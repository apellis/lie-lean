/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaTorsionFree
import LieLean.Algebra.Lie.KacMoody.VermaHomGeneralFiniteType
import LieLean.Algebra.Lie.KacMoody.ProjectiveSocle
import LieLean.Algebra.Lie.KacMoody.VermaSocle

/-!
# Multiplicities of antidominant simple modules in Verma modules

Humphreys, GSM 94, Theorem 7.16 (b): for `λ` antidominant, `[M(w·λ) : L(λ)] = 1` for every
`w ∈ W_[λ]`, so (BGG reciprocity) every standard filtration of `P(λ)` contains each `M(w·λ)`
exactly once. This holds for all antidominant `λ`, integral or not; the integral case is part of
Theorem 4.10.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.ProjectiveCover.ker_π_le_of_isAntidominant`: every
  morphism `P(λ) → M(ξ)` factors through `P(λ) → L(λ)`.
* `Matrix.Realization.KacMoodyAlgebra.multiplicity_verma_le_one_of_isAntidominant`:
  `[M(ξ) : L(λ)] ≤ 1` for every `ξ`.
* `Matrix.Realization.KacMoodyAlgebra.multiplicity_verma_weylDot_of_isAntidominant`,
  `Matrix.Realization.KacMoodyAlgebra.count_projectiveCover_of_isAntidominant`: Theorem 7.16 (b).
* `Matrix.Realization.KacMoodyAlgebra.multiplicity_verma_weylDot_of_integral`: Theorem 4.10,
  multiplicities.

## Proof

`M(λ) = L(λ)` is simple (Theorem 4.8). A nonzero `f : P(λ) → M(ξ)` has kernel in the unique
maximal submodule `ker π` of `P(λ)`; since Verma modules are torsion-free over `U(𝔫⁻)`
(`VermaModule.eq_zero_or_ker_le`), applied to `f` and `P(λ) → L(λ) ≅ M(λ)`, the two kernels
agree. So `f` is determined by the primitive vector `f(p)` of weight `λ`, `p` a generator, and
`[M(ξ) : L(λ)] = dim Hom(P(λ), M(ξ)) ≤ dim Hom(M(λ), M(ξ)) ≤ 1` (Theorems 3.9 (c), 4.2 (b)).
The socle of `M(w·λ)` is `L(ξ)` with `ξ` antidominant and linked to `λ`, hence `ξ = λ`
(Corollary 4.8 and its proof), so the multiplicity is nonzero. Reconstructed.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §4.1–§4.2, §4.10, §7.16.
-/

open Module LieModule

universe u₁ u₂

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA

omit hA [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] in
/-- `ker (e⁻¹ ∘ π) = ker π` for an isomorphism `e`. -/
lemma ker_comp_equiv {X Y Z : Type*} [AddCommGroup X] [Module K X] [LieRingModule 𝔤 X]
    [LieModule K 𝔤 X] [AddCommGroup Y] [Module K Y] [LieRingModule 𝔤 Y] [LieModule K 𝔤 Y]
    [AddCommGroup Z] [Module K Z] [LieRingModule 𝔤 Z] [LieModule K 𝔤 Z]
    (e : Y ≃ₗ⁅K,𝔤⁆ Z) (π : X →ₗ⁅K,𝔤⁆ Y) :
    ((e : Y →ₗ⁅K,𝔤⁆ Z).comp π).ker = π.ker := by
  ext x
  simp only [LieModuleHom.mem_ker, LieModuleHom.coe_comp, Function.comp_apply]
  refine ⟨fun h ↦ e.injective ?_, fun h ↦ by rw [h, map_zero]⟩
  rw [map_zero]
  exact h

/-- Every morphism `P(λ) → M(ξ)`, `λ` antidominant, kills `ker (P(λ) → L(λ))`. -/
theorem ProjectiveCover.ker_π_le_of_isAntidominant {lam ξ : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (f : ProjectiveCover P hA lam →ₗ⁅K,𝔤⁆ VermaModule P ξ) :
    (ProjectiveCover.π P hA lam).ker ≤ f.ker := by
  by_cases hf : f = 0
  · intro x _
    rw [LieModuleHom.mem_ker, hf]
    rfl
  have h1 : f.ker ≤ (ProjectiveCover.π P hA lam).ker := by
    by_contra h
    refine hf (LieModuleHom.ext fun x ↦ ?_)
    have hx : x ∈ f.ker := (ProjectiveCover.eq_top_of_not_le_ker P hA lam _ h) ▸ trivial
    exact hx
  obtain ⟨e⟩ := VermaModule.nonempty_equiv_irreducible_of_isAntidominant P hA hlam
  have hgker := ker_comp_equiv P e.symm (ProjectiveCover.π P hA lam)
  rcases VermaModule.eq_zero_or_ker_le P hA f _ (hgker ▸ h1) with h | h
  · exfalso
    refine ProjectiveCover.π_ne_zero P hA lam (LieModuleHom.ext fun x ↦ ?_)
    have hx : ((e.symm : IrreducibleModule P lam →ₗ⁅K,𝔤⁆ VermaModule P lam).comp
        (ProjectiveCover.π P hA lam)) x = 0 := by rw [h]; rfl
    rw [LieModuleHom.coe_comp, Function.comp_apply] at hx
    exact e.symm.injective (hx.trans (map_zero _).symm)
  · exact hgker ▸ h

/-- **Humphreys, GSM 94, Theorem 7.16 (b), multiplicity bound**: for `λ` antidominant,
`[M(ξ) : L(λ)] ≤ 1` for every `ξ`. -/
theorem multiplicity_verma_le_one_of_isAntidominant {lam : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam) (ξ : Dual K H) :
    (VermaModule.isCategoryO P ξ).multiplicity lam ≤ 1 := by
  obtain ⟨d, hdpos, hposDef⟩ := hA.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hposDef.isHermitian
  set S := Symmetrization.ofDiagonal d hdpos hsymm
  have hπ := ProjectiveCover.isProjectiveCover P lam hA
  obtain ⟨p, hpw, hπp, hp⟩ := hπ.exists_generator
  rw [← ProjectiveCover.finrank_hom_eq_multiplicity P lam hA (VermaModule.isCategoryO P ξ)]
  have hprim : ∀ f : ProjectiveCover P hA lam →ₗ⁅K,𝔤⁆ VermaModule P ξ,
      f p ∈ primitiveVectors P (VermaModule P ξ) lam := fun f ↦ by
    refine mem_primitiveVectors.mpr ⟨map_mem_weightSpaceOfMap P f hpw, fun i ↦ ?_⟩
    rw [← LieModuleHom.map_lie]
    refine ProjectiveCover.ker_π_le_of_isAntidominant P hA hlam f ?_
    rw [LieModuleHom.mem_ker, LieModuleHom.map_lie, hπp, IrreducibleModule.hwv,
      ← LieModuleHom.map_lie, VermaModule.lie_e_hwv,
      map_zero]
  let Φ : (ProjectiveCover P hA lam →ₗ⁅K,𝔤⁆ VermaModule P ξ) →ₗ[K]
      primitiveVectors P (VermaModule P ξ) lam :=
    { toFun f := ⟨f p, hprim f⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have : FiniteDimensional K (primitiveVectors P (VermaModule P ξ) lam) :=
    have := VermaModule.finiteDimensional_weightSpace P ξ lam
    Submodule.finiteDimensional_of_le inf_le_left
  refine (LinearMap.finrank_le_finrank_of_injective (f := Φ) fun f g hfg ↦ ?_).trans ?_
  · rw [← sub_eq_zero]
    refine IsProjectiveCover.eq_zero_of_apply_eq_zero hp ?_
    have := congrArg Subtype.val hfg
    simpa [Φ, sub_eq_zero] using this
  · rw [← (homEquiv P (VermaModule P ξ) lam).finrank_eq]
    exact finrank_hom_le_one_of_finite_type P hA S ξ lam

/-- **Humphreys, GSM 94, Theorem 7.16 (b)**: for `λ` antidominant and `w ∈ W_[λ]`,
`[M(w·λ) : L(λ)] = 1`. -/
theorem multiplicity_verma_weylDot_of_isAntidominant {lam : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam) {w : P.weylGroup hA.isGeneralizedCartan}
    (hw : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam) :
    (VermaModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan w lam)).multiplicity lam = 1 := by
  set μ := P.weylDot hA.isGeneralizedCartan w lam
  refine le_antisymm (multiplicity_verma_le_one_of_isAntidominant P hA hlam μ) ?_
  obtain ⟨S, hS, -⟩ := VermaModule.exists_isAtom_le P hA μ
  obtain ⟨ξ, hξ, hmξ, -⟩ := exists_isAntidominant_of_isAtom_of_injective P hA
    (VermaModule.isCategoryO P μ) hS (f := S.incl) Subtype.val_injective
  have hmμ : (VermaModule.isCategoryO P μ).multiplicity μ ≠ 0 := by
    rw [VermaModule.multiplicity_self]
    exact one_ne_zero
  obtain rfl := eq_of_multiplicity_ne_zero_of_isAntidominant P hA hlam hξ hw hmξ hmμ
  exact Nat.one_le_iff_ne_zero.mpr hmξ

/-- **Humphreys, GSM 94, Theorem 7.16 (b)**: for `λ` antidominant, every standard filtration of
`P(λ)` contains each `M(w·λ)`, `w ∈ W_[λ]`, exactly once (BGG reciprocity). -/
theorem count_projectiveCover_of_isAntidominant [DecidableEq (Dual K H)] {lam : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam) {t : Multiset (Dual K H)}
    (ht : IsStdFiltered P (⊤ : LieSubmodule K 𝔤 (ProjectiveCover P hA lam)) t)
    {w : P.weylGroup hA.isGeneralizedCartan}
    (hw : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam) :
    t.count (P.weylDot hA.isGeneralizedCartan w lam) = 1 := by
  rw [ProjectiveCover.count_eq_multiplicity P lam hA ht]
  exact multiplicity_verma_weylDot_of_isAntidominant P hA hlam hw

/-- **Humphreys, GSM 94, Theorem 4.10**, multiplicities: for `λ` antidominant with `λ + ρ`
integral, `[M(w·λ) : L(λ)] = 1` for every `w ∈ W`. -/
theorem multiplicity_verma_weylDot_of_integral {lam : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hint : ∀ j, ∃ n : ℤ, (lam + P.rho) (P.coroot j) = n) (w : P.weylGroup hA.isGeneralizedCartan) :
    (VermaModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan w lam)).multiplicity lam = 1 := by
  refine multiplicity_verma_weylDot_of_isAntidominant P hA hlam ?_
  rw [P.integralWeylGroup_eq_of_integral hA.isGeneralizedCartan (μ' := lam + P.rho)
    fun j ↦ ⟨-1, by simp⟩, mem_integralWeylGroup, mem_rootLattice]
  obtain ⟨k, hk⟩ := P.exists_apply_eq_add_rootOf hA.isGeneralizedCartan w.2 hint
  exact ⟨k, by rw [hk, add_sub_cancel_left]⟩

end Matrix.Realization.KacMoodyAlgebra
