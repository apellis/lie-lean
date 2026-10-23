/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BlockProjectiveFunctorComposition
import LieLean.Algebra.Lie.KacMoody.CentralTensorFiltration
import LieLean.Algebra.Lie.KacMoody.TranslationProjective
import LieLean.Algebra.Lie.KacMoody.BGGReciprocity
import LieLean.Algebra.Lie.KacMoody.FiniteDimensional

/-!
# Projective functors and the Weyl group: Verma multiplicities

Bernstein–Gelfand's Theorem 3.4 (iv) says that the action `F^K` of a projective functor on the
Grothendieck group commutes with the action of the Weyl group `W` that sends the class of `M(ν)`
to the class of `M(w·ν)`. On the block of a dominant weight `λ` the Verma modules are the
`M(w·λ)`, `w ∈ W_[λ]`, and the values `F(M(w·λ))` have standard filtrations. The statement is
that the multiplicities in these filtrations are related by the dot action:
`(F(M(w·λ)) : M(w·ν)) = (F(M(λ)) : M(ν))` (`BlockProjectiveFunctor.CommutesWithWeyl`). The
multiplicities are taken as `dim Hom(F(M), M(ν)^∨)`, which is the number of factors `M(ν)` in any
standard filtration of `F(M)` (Humphreys, Theorem 3.7; `BlockProjectiveFunctor.count_eq_vermaMult`).

This file proves the statement for the projective functors `pr_χ(− ⊗ V)` given by a block of a
tensoring functor (`BlockProjectiveFunctor.tensorBlock`), from the explicit form of their values
on Verma modules: `pr_χ(M(Λ) ⊗ V)` has a standard filtration in which `M(ξ)` occurs
`dim V_{ξ - Λ}` times if `ξ` has central character `χ`, and not otherwise
(`BlockProjectiveFunctor.vermaMult_tensorBlock`). Weight multiplicities of finite-dimensional
modules and central characters are invariant under the dot action, so these functors commute with
`W` (`BlockProjectiveFunctor.commutesWithWeyl_tensorBlock`). These are the functors `G_V` of
Bernstein–Gelfand's proof (§3.9 (d)).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.BlockProjectiveFunctor.vermaMult`: the multiplicity of
  `M(ν)` in `F(M)`.
* `Matrix.Realization.KacMoodyAlgebra.BlockProjectiveFunctor.CommutesWithWeyl`.
* `Matrix.Realization.KacMoodyAlgebra.BlockProjectiveFunctor.tensorBlock`: `pr_χ(− ⊗ V)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.count_range_eq_finrank_hom`.
* `BlockProjectiveFunctor.count_eq_vermaMult`.
* `BlockProjectiveFunctor.exists_isStdFiltered_tensorBlock_verma`,
  `BlockProjectiveFunctor.vermaMult_tensorBlock`.
* `BlockProjectiveFunctor.commutesWithWeyl_tensorBlock`.

## References

* J. N. Bernstein, S. I. Gelfand, *Tensor products of finite and infinite dimensional
  representations of semisimple Lie algebras*, Compositio Math. **41** (1980), 245–285,
  Thm. 3.4 (iv) and §3.9 (c), (d).
* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Thm. 3.6, Thm. 3.7, §10.8.
-/

noncomputable section

open Module UniversalEnvelopingAlgebra TensorProduct

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Range

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)
  {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]

local notation "𝔤" => KacMoodyAlgebra P

/-- The multiplicity of `M(ν)` in a standard filtration of the image of an idempotent is
`dim Hom(e(X), M(ν)^∨)` (Humphreys, GSM 94, Theorem 3.7). -/
theorem IsStdFiltered.count_range_eq_finrank_hom [CharZero K] [DecidableEq (Dual K H)]
    {e : X →ₗ⁅K,𝔤⁆ X} (he : e.comp e = e) (hX : IsCategoryO P e.range)
    {s : Multiset (Dual K H)} (hs : IsStdFiltered P e.range s) (ν : Dual K H) :
    s.count ν = finrank K (e.range →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P ν)) :=
  (isStdFiltered_top_range P he hs).count_eq_finrank_hom hX ν

end Range

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ}

namespace BlockProjectiveFunctor

variable {P : Realization A K H} {hA : A.IsFiniteCartan}

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

variable {lam : Dual K H} {V : Type (max u₁ u₂)} [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
  (F : BlockProjectiveFunctor P hA lam V)

/-! ### Verma multiplicities -/

/-- The multiplicity of `M(ν)` in `F(M)`, as `dim Hom(F(M), M(ν)^∨)`. If `F(M)` has a standard
filtration, it is the number of factors `M(ν)` (`count_eq_vermaMult`). -/
def vermaMult (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M] (ν : Dual K H) : ℕ :=
  finrank K ((F.idem M).range →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P ν))

/-- The multiplicity of `M(ν)` in a standard filtration of `F(M)` is `vermaMult`. -/
theorem count_eq_vermaMult [DecidableEq (Dual K H)] {M : Type (max u₁ u₂)} [AddCommGroup M]
    [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsInBlock P hA lam M)
    (hFM : IsCategoryO P (F.idem M).range) {s : Multiset (Dual K H)}
    (hs : IsStdFiltered P (F.idem M).range s) (ν : Dual K H) :
    s.count ν = F.vermaMult M ν :=
  hs.count_range_eq_finrank_hom P (LieModuleHom.ext (F.idem_idem M hM)) hFM ν

/-- **`F` commutes with the Weyl group on Verma multiplicities** (the statement of
Bernstein–Gelfand's Thm. 3.4 (iv) on the block of `λ`): for `w ∈ W_[λ]` and every `ν`, the
multiplicity of `M(w·ν)` in `F(M(w·λ))` is the multiplicity of `M(ν)` in `F(M(λ))`. -/
def CommutesWithWeyl : Prop :=
  ∀ w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam, ∀ ν : Dual K H,
    F.vermaMult (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam))
        (P.weylDot hA.isGeneralizedCartan w ν) =
      F.vermaMult (VermaModule P lam) ν

/-! ### Blocks of tensoring functors -/

variable [IsAlgClosed K] [FiniteDimensional K H]

omit [IsAlgClosed K] in
include hA in
/-- A finite-dimensional module lies in `𝒪` (finite type). -/
theorem isCategoryO_of_finiteDimensional (V : Type*) [AddCommGroup V] [Module K V]
    [LieRingModule 𝔤 V] [LieModule K 𝔤 V] [FiniteDimensional K V] : IsCategoryO P V :=
  IsHDiagonalizable.isCategoryO_of_finite P (isHDiagonalizable_of_finiteDimensional hA)

open Classical in
variable (P hA lam V) in
/-- The projective functor `pr_χ(− ⊗ V)` on the block of `λ` (`V` finite-dimensional, `χ` a
central character): its idempotent at `M ∈ 𝒪` is the projection of `M ⊗ V` onto the block `χ`. -/
def tensorBlock [FiniteDimensional K V] (χ : 𝓩 →ₐ[K] K) : BlockProjectiveFunctor P hA lam V where
  idem M _ _ _ _ := if hM : IsCategoryO P M then
      (hM.tensorProduct
        (isCategoryO_of_finiteDimensional (P := P) (hA := hA) V)).centralBlockProjection P χ
    else 0
  idem_idem M _ _ _ _ hM x := by
    simp only [hM.isCategoryO, ↓reduceDIte]
    exact centralBlockProjection_self P _ χ (centralBlockProjection_mem P _ χ x)
  exists_tensorNatTrans M N _ _ _ _ _ _ _ _ hM hN := by
    have hVO := isCategoryO_of_finiteDimensional (P := P) (hA := hA) V
    obtain ⟨s, hs⟩ := hM.exists_finset
    obtain ⟨t, ht⟩ := hN.exists_finset
    obtain ⟨s', hs'⟩ := LieSubmodule.exists_finset_lieSpan_tmul_eq_top (W := V) hs
    obtain ⟨t', ht'⟩ := LieSubmodule.exists_finset_lieSpan_tmul_eq_top (W := V) ht
    obtain ⟨z, hzM, hzN⟩ := exists_rep_eq_centralBlockProjection₂ P
      ((hM.isCategoryO.tensorProduct hVO).isCentralLocallyFinite P) hs'
      ((hN.isCategoryO.tensorProduct hVO).isCentralLocallyFinite P) ht' χ
    refine ⟨TensorNatTrans.ofCentral V (z : 𝓤) z.property, ?_, ?_⟩
    · simp only [hM.isCategoryO, ↓reduceDIte]
      exact LieModuleHom.ext hzM
    · simp only [hN.isCategoryO, ↓reduceDIte]
      exact LieModuleHom.ext hzN

theorem tensorBlock_idem [FiniteDimensional K V] (χ : 𝓩 →ₐ[K] K) {M : Type (max u₁ u₂)}
    [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsCategoryO P M) :
    (tensorBlock P hA lam V χ).idem M =
      (hM.tensorProduct
        (isCategoryO_of_finiteDimensional (P := P) (hA := hA) V)).centralBlockProjection P χ := by
  classical
  simp only [tensorBlock, hM, ↓reduceDIte]

/-- The image of `pr_χ` on `M ⊗ V` is the block `χ` of `M ⊗ V`. -/
theorem range_tensorBlock_idem [FiniteDimensional K V] (χ : 𝓩 →ₐ[K] K) {M : Type (max u₁ u₂)}
    [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsCategoryO P M) :
    ((tensorBlock P hA lam V χ).idem M).range = centralBlock P (M ⊗[K] V) χ := by
  rw [tensorBlock_idem χ hM, ← LieModuleHom.map_top, IsCategoryO.centralBlockProjection,
    map_centralBlockProjection_eq_inf P
      (hM.tensorProduct (isCategoryO_of_finiteDimensional (P := P) (hA := hA) V)), top_inf_eq]

open Classical in
/-- **`pr_χ(M(Λ) ⊗ V)` has a standard filtration** in which `M(ξ)` occurs `dim V_{ξ - Λ}` times if
`ξ` has central character `χ`, and not otherwise (Humphreys, GSM 94, Theorem 3.6, projected to a
block). -/
theorem exists_isStdFiltered_tensorBlock_verma [FiniteDimensional K V] (χ : 𝓩 →ₐ[K] K)
    (Λ : Dual K H) :
    ∃ s, IsStdFiltered P ((tensorBlock P hA lam V χ).idem (VermaModule P Λ)).range s ∧
      ∀ ξ, s.count ξ = if centralCharacter P ξ = χ then finrank K (weightSpace P V (ξ - Λ))
        else 0 := by
  obtain ⟨N, wt, -, -, -, -, -, hmono, h0, hlast, -, hstep, hcount⟩ :=
    exists_centralTensorVermaFiltration P (isHDiagonalizable_of_finiteDimensional (V := V) hA)
      Λ χ
  set S : Set (Fin (finrank K V)) := {j | centralCharacter P (Λ + wt j) = χ}
  have h1 := isStdFiltered_of_fin_of_zero P _ (fun j ↦ Λ + wt j) S hmono h0
    (fun j hj ↦ (hstep j).1 hj) (fun j hj ↦ (hstep j).2 hj)
  refine ⟨(Finset.univ.filter (· ∈ S)).val.map (fun j ↦ Λ + wt j), ?_, fun ξ ↦ ?_⟩
  · rw [range_tensorBlock_idem χ (VermaModule.isCategoryO P Λ)]
    exact hlast ▸ h1
  · have hc := hcount (ξ - Λ)
    rw [add_sub_cancel] at hc
    rw [← hc, Nat.card_eq_fintype_card, Fintype.card_subtype, Multiset.count_map,
      ← Finset.filter_val, Finset.filter_filter, Finset.card_val]
    congr 1
    refine Finset.filter_congr fun j _ ↦ ?_
    simp only [S, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h2]; abel, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by rw [h1]; abel⟩

open Classical in
/-- **The Verma multiplicities of `pr_χ(M(Λ) ⊗ V)`**: `M(ξ)` occurs `dim V_{ξ - Λ}` times if `ξ`
has central character `χ`, and not otherwise. -/
theorem vermaMult_tensorBlock [FiniteDimensional K V] (χ : 𝓩 →ₐ[K] K) (Λ ξ : Dual K H) :
    (tensorBlock P hA lam V χ).vermaMult (VermaModule P Λ) ξ =
      if centralCharacter P ξ = χ then finrank K (weightSpace P V (ξ - Λ)) else 0 := by
  have hVO := isCategoryO_of_finiteDimensional (P := P) (hA := hA) V
  have hO := (VermaModule.isCategoryO P Λ).tensorProduct hVO
  obtain ⟨s, hs, hcount⟩ :=
    exists_isStdFiltered_tensorBlock_verma (P := P) (hA := hA) (lam := lam) (V := V) χ Λ
  have he : ((tensorBlock P hA lam V χ).idem (VermaModule P Λ)).comp
      ((tensorBlock P hA lam V χ).idem (VermaModule P Λ)) =
      (tensorBlock P hA lam V χ).idem (VermaModule P Λ) := by
    ext x
    simp only [LieModuleHom.coe_comp, Function.comp_apply,
      tensorBlock_idem χ (VermaModule.isCategoryO P Λ), IsCategoryO.centralBlockProjection]
    exact centralBlockProjection_self P _ χ (centralBlockProjection_mem P _ χ x)
  have hX : IsCategoryO P ((tensorBlock P hA lam V χ).idem (VermaModule P Λ)).range :=
    hO.lieSubmodule _
  rw [vermaMult, ← hs.count_range_eq_finrank_hom P he hX ξ, hcount ξ]

/-- **Tensoring functors commute with the Weyl group** (Bernstein–Gelfand, Thm. 3.4 (iv), for
the functors `pr_χ(− ⊗ V)`): `w · ν - w · λ = w (ν - λ)`, weight multiplicities of the
finite-dimensional module `V` are `W`-invariant, and `w · ν` has the central character of `ν`. -/
theorem commutesWithWeyl_tensorBlock [FiniteDimensional K V] (χ : 𝓩 →ₐ[K] K) :
    (tensorBlock P hA lam V χ).CommutesWithWeyl := by
  classical
  intro w _ ν
  rw [vermaMult_tensorBlock, vermaMult_tensorBlock]
  have hc : centralCharacter P (P.weylDot hA.isGeneralizedCartan w ν) = centralCharacter P ν :=
    VermaModule.centralCharacter_weyl P hA.isGeneralizedCartan w.property ν
  have hsub : P.weylDot hA.isGeneralizedCartan w ν - P.weylDot hA.isGeneralizedCartan w lam =
      (w : Dual K H ≃ₗ[K] Dual K H) (ν - lam) := by
    simp only [weylDot, map_sub, map_add]
    abel
  rw [hc, hsub, ((nonempty_weightSpace_weylGroup_equiv hA.isGeneralizedCartan
    (isIntegrable_of_finiteDimensional hA (V := V)) w.property (ν - lam)).some.finrank_eq)]

end BlockProjectiveFunctor

end Matrix.Realization.KacMoodyAlgebra
