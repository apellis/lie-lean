/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TensorProduct
import LieLean.Algebra.Lie.KacMoody.CharacterDenominator

/-!
# Translation functors on the category `𝒪`

Let `A` be a symmetrizable generalized Cartan matrix and `K` a field of characteristic zero. For
`V` in `𝒪` let `V^c` be its Casimir block for the eigenvalue `c` (`KacMoody/Blocks.lean`). For a
module `Z` in `𝒪` and `c, c' ∈ K` we define

  `T V = (Z ⊗ V^c)^{c'}`,

which lies in `𝒪` by `KacMoody/TensorProduct.lean`. With `Z = L(ν)` for a dominant integral `ν`
and `c = (λ + 2ρ | λ)`, `c' = (μ + 2ρ | μ)`, this is the Kac–Moody version of the translation
functor `T_λ^μ = pr_μ (L(ν) ⊗ pr_λ (-))` of [HumO] §7.1 (check). (In [HumO], `𝔤` is finite
dimensional, `ν` is the dominant `W`-conjugate of `μ - λ`, `L(ν)` is finite-dimensional, and
`pr_λ` is the projection onto a block for the action of the centre `Z(𝔤)`; here `L(ν)` is in
general infinite-dimensional but lies in `𝒪`, only the Casimir operator is available, so the
blocks are unions of linkage classes, and we leave `ν` as a parameter: in Kac–Moody generality
`μ - λ` need not be `W`-conjugate to a dominant weight.)

We prove that `T` is exact in the sense of characters: if `ch V = ch V' + ch V''` (for instance
for a short exact sequence `0 → V' → V → V'' → 0`), then `ch T V = ch T V' + ch T V''`
([HumO] §7.1 (check)). On Verma modules we only record the character form of [HumO] Thm. 3.6
(check): `R · ch (Z ⊗ M(λ)) = e^λ ch Z`, i.e. `Z ⊗ M(λ)` has the character of
`⊕_ξ M(λ + ξ)^{dim Z_ξ}`. The computation of `T_λ^μ M(w·λ)` ([HumO] Thm. 7.6 (check)) needs
the finer linkage principle (blocks for the full centre, or the Kac–Kazhdan criterion) and is not
attempted.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.translation`: `T V = (Z ⊗ V^c)^{c'}`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.character_eq_add_iff`:
  `ch V = ch V' + ch V''` iff `[V : L(μ)] = [V' : L(μ)] + [V'' : L(μ)]` for all `μ`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.character_casimirBlock_eq_add`: the block
  projections `V ↦ V^c` are exact on characters.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.denominator_mul_character_tensorProduct_verma`:
  `R · ch (Z ⊗ M(λ)) = e^λ ch Z`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.character_translation_eq_add`,
  `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.character_translation_eq_add_quotient`:
  **exactness of translation functors** on characters.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category `𝒪`*,
  GSM 94, AMS 2008, §7.1–7.6.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.
-/

open Module LieModule TensorProduct

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {V V' V'' Z : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [AddCommGroup V'] [Module K V']
  [LieRingModule P.KacMoodyAlgebra V'] [LieModule K P.KacMoodyAlgebra V'] [AddCommGroup V'']
  [Module K V''] [LieRingModule P.KacMoodyAlgebra V''] [LieModule K P.KacMoodyAlgebra V'']
  [AddCommGroup Z] [Module K Z] [LieRingModule P.KacMoodyAlgebra Z]
  [LieModule K P.KacMoodyAlgebra Z]

/-- In `𝒪`, `ch V = ch V' + ch V''` iff `[V : L(μ)] = [V' : L(μ)] + [V'' : L(μ)]` for all `μ`
(the characters `ch L(μ)` are linearly independent, `sumIrreducibleCharacter_injective`). -/
theorem IsCategoryO.character_eq_add_iff (hV : IsCategoryO P V) (hV' : IsCategoryO P V')
    (hV'' : IsCategoryO P V'') :
    hV.character = hV'.character + hV''.character ↔
      ∀ μ, hV.multiplicity μ = hV'.multiplicity μ + hV''.multiplicity μ := by
  rw [hV.character_eq_sumIrreducibleCharacter, hV'.character_eq_sumIrreducibleCharacter,
    hV''.character_eq_sumIrreducibleCharacter, ← map_add,
    sumIrreducibleCharacter_injective.eq_iff]
  refine ⟨fun h μ ↦ ?_, fun h ↦ CharacterRing.ext fun μ ↦ ?_⟩
  · have := congrArg (fun c ↦ c.coeffAt μ) h
    simp only [IsCategoryO.coeffAt_multiplicities, CharacterRing.coeffAt,
      HahnSeries.coeff_add] at this
    exact_mod_cast this
  · simp only [IsCategoryO.coeffAt_multiplicities, CharacterRing.coeffAt, HahnSeries.coeff_add]
    exact_mod_cast h μ

/-- **Tensoring a Verma module** ([HumO] Thm. 3.6 (check), character form): for `Z` in `𝒪`,
`R · ch (Z ⊗ M(λ)) = e^λ ch Z`, where `R = ∏_{α > 0} (1 - e^{-α})^{mult α}` is the denominator;
thus `Z ⊗ M(λ)` has the character of `⊕_ξ M(λ + ξ)^{dim Z_ξ}`. -/
theorem IsCategoryO.denominator_mul_character_tensorProduct_verma (hZ : IsCategoryO P Z)
    (Λ : Dual K H) :
    denominator P * (hZ.tensorProduct (VermaModule.isCategoryO P Λ)).character =
      CharacterRing.exp P ℤ Λ * hZ.character := by
  rw [hZ.character_tensorProduct (VermaModule.isCategoryO P Λ), mul_left_comm,
    VermaModule.denominator_mul_character, mul_comm]

variable [FiniteDimensional K H] {S : A.Symmetrization}
  {B : LinearMap.BilinForm K P.KacMoodyAlgebra}

namespace IsStandardForm

variable (hB : IsStandardForm P S B) (hA : A.IsGeneralizedCartan)
include hB hA

/-- **The block projections are exact** (on characters): if `ch V = ch V' + ch V''`, then
`ch V^c = ch V'^c + ch V''^c`. -/
theorem character_casimirBlock_eq_add (hV : IsCategoryO P V) (hV' : IsCategoryO P V')
    (hV'' : IsCategoryO P V'') (h : hV.character = hV'.character + hV''.character) (c : K) :
    (hV.lieSubmodule (hB.casimirBlock hA hV.isPosFinite c)).character =
      (hV'.lieSubmodule (hB.casimirBlock hA hV'.isPosFinite c)).character +
        (hV''.lieSubmodule (hB.casimirBlock hA hV''.isPosFinite c)).character := by
  classical
  rw [IsCategoryO.character_eq_add_iff] at h ⊢
  intro μ
  rw [hB.multiplicity_casimirBlock hA hV, hB.multiplicity_casimirBlock hA hV',
    hB.multiplicity_casimirBlock hA hV'']
  split_ifs
  · exact h μ
  · rfl

/-- The *translation functor* `T V = (Z ⊗ V^c)^{c'}` on `𝒪`, for a module `Z` in `𝒪` and
`c, c' ∈ K`. For `Z = L(ν)` with `ν` dominant integral, `c = (λ + 2ρ | λ)` and
`c' = (μ + 2ρ | μ)` this is the translation functor `T_λ^μ` of [HumO] §7.1 (check), with Casimir
blocks in place of blocks for the centre of `U(𝔤)` (see the module docstring). -/
def translation (hZ : IsCategoryO P Z) (hV : IsCategoryO P V) (c c' : K) :
    LieSubmodule K P.KacMoodyAlgebra (Z ⊗[K] hB.casimirBlock hA hV.isPosFinite c) :=
  hB.casimirBlock hA (hZ.tensorProduct (hV.lieSubmodule _)).isPosFinite c'

/-- The translation functor preserves `𝒪`. -/
theorem isCategoryO_translation (hZ : IsCategoryO P Z) (hV : IsCategoryO P V) (c c' : K) :
    IsCategoryO P (hB.translation hA hZ hV c c') :=
  (hZ.tensorProduct (hV.lieSubmodule _)).lieSubmodule _

/-- **Exactness of translation functors** ([HumO] §7.1 (check)), on characters: if
`ch V = ch V' + ch V''`, e.g. for a short exact sequence `0 → V' → V → V'' → 0` in `𝒪`, then
`ch T V = ch T V' + ch T V''` for `T V = (Z ⊗ V^c)^{c'}`. -/
theorem character_translation_eq_add (hZ : IsCategoryO P Z) (hV : IsCategoryO P V)
    (hV' : IsCategoryO P V') (hV'' : IsCategoryO P V'')
    (h : hV.character = hV'.character + hV''.character) (c c' : K) :
    (hB.isCategoryO_translation hA hZ hV c c').character =
      (hB.isCategoryO_translation hA hZ hV' c c').character +
        (hB.isCategoryO_translation hA hZ hV'' c c').character := by
  have h1 := hB.character_casimirBlock_eq_add hA hV hV' hV'' h c
  have h2 : (hZ.tensorProduct (hV.lieSubmodule (hB.casimirBlock hA hV.isPosFinite c))).character =
      (hZ.tensorProduct (hV'.lieSubmodule (hB.casimirBlock hA hV'.isPosFinite c))).character +
        (hZ.tensorProduct
          (hV''.lieSubmodule (hB.casimirBlock hA hV''.isPosFinite c))).character := by
    rw [hZ.character_tensorProduct (hV.lieSubmodule _),
      hZ.character_tensorProduct (hV'.lieSubmodule _),
      hZ.character_tensorProduct (hV''.lieSubmodule _), h1, mul_add]
  exact hB.character_casimirBlock_eq_add hA (hZ.tensorProduct (hV.lieSubmodule _))
    (hZ.tensorProduct (hV'.lieSubmodule _)) (hZ.tensorProduct (hV''.lieSubmodule _)) h2 c'

/-- **Exactness of translation functors** ([HumO] §7.1 (check)), on characters, for the short
exact sequence `0 → N → V → V / N → 0`: `ch T V = ch T N + ch T (V / N)`. -/
theorem character_translation_eq_add_quotient (hZ : IsCategoryO P Z) (hV : IsCategoryO P V)
    (N : LieSubmodule K P.KacMoodyAlgebra V) (c c' : K) :
    (hB.isCategoryO_translation hA hZ hV c c').character =
      (hB.isCategoryO_translation hA hZ (hV.lieSubmodule N) c c').character +
        (hB.isCategoryO_translation hA hZ (hV.quotient N) c c').character :=
  hB.character_translation_eq_add hA hZ hV _ _ (hV.character_eq_add N _ _) c c'

end IsStandardForm

end Matrix.Realization.KacMoodyAlgebra

end
