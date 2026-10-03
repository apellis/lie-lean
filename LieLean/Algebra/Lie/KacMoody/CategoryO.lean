/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaIrreducible

/-!
# The category `𝒪` for `𝔤(A)`

A module `V` over the Kac–Moody algebra `𝔤(A)` lies in the category `𝒪` ([Kac] §9.1) if it is
`𝔥`-diagonalizable with finite-dimensional weight spaces, and its weights lie in a finite union
of cones `D(λ) = λ - Q₊`. Every quotient of a Verma module lies in `𝒪`; in particular `M(Λ)` and
`L(Λ)` do.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.cone`: the cone `D(λ) = {λ - β | β ∈ Q₊}`.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO`: the property of lying in the category `𝒪`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.of_surjective`: a quotient of `M(Λ)` lies in
  `𝒪`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.isCategoryO`,
  `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.isCategoryO`: `M(Λ)` and `L(Λ)` lie in
  `𝒪`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.1–9.3.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- The cone `D(λ) = {λ - β | β ∈ Q₊}` ([Kac] §9.1). -/
def cone (Λ : Dual K H) : Set (Dual K H) := {μ | ∃ k : ι → ℤ, 0 ≤ k ∧ μ = Λ - P.rootOf k}

variable (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-- A `𝔤(A)`-module `V` lies in the category `𝒪` ([Kac] §9.1) if it is `𝔥`-diagonalizable, its
weight spaces are finite-dimensional, and its weights lie in a finite union of cones
`D(λ) = λ - Q₊`. -/
structure IsCategoryO : Prop where
  /-- `V` is the sum of its weight spaces. -/
  iSup_weightSpaceOfMap_eq_top : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤
  /-- The weight spaces of `V` are finite-dimensional. -/
  finiteDimensional_weightSpaceOfMap : ∀ μ, FiniteDimensional K (weightSpaceOfMap V (h P) μ)
  /-- The weights of `V` lie in a finite union of cones `λ - Q₊`. -/
  exists_finset : ∃ s : Finset (Dual K H),
    ∀ μ, weightSpaceOfMap V (h P) μ ≠ ⊥ → ∃ Λ ∈ s, μ ∈ cone P Λ

namespace IsCategoryO

variable [CharZero K] {P V} {Λ : Dual K H}

/-- Every quotient of the Verma module `M(Λ)` lies in the category `𝒪` ([Kac] §9.2). -/
theorem of_surjective (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V)
    (hφ : Function.Surjective φ) : IsCategoryO P V := by
  have hmap : ∀ μ, (VermaModule.weightSpace P Λ μ).map (φ : VermaModule P Λ →ₗ[K] V) ≤
      weightSpaceOfMap V (h P) μ := fun μ ↦ by
    rintro _ ⟨m, hm, rfl⟩
    exact map_mem_weightSpaceOfMap P φ hm
  have htop : ⨆ μ, (VermaModule.weightSpace P Λ μ).map (φ : VermaModule P Λ →ₗ[K] V) = ⊤ := by
    rw [← Submodule.map_iSup, eq_top_iff]
    rintro x -
    obtain ⟨m, rfl⟩ := hφ x
    refine Submodule.mem_map_of_mem ?_
    have hm : m ∈ ⨆ (k : ι → ℤ) (_ : 0 ≤ k), VermaModule.weightSpace P Λ (Λ - P.rootOf k) := by
      rw [VermaModule.iSup_weightSpace_eq_top]; trivial
    exact (iSup₂_le fun k _ ↦ le_iSup (VermaModule.weightSpace P Λ) _ :
      _ ≤ ⨆ μ, VermaModule.weightSpace P Λ μ) hm
  have hle : ∀ μ, weightSpaceOfMap V (h P) μ ≤
      (VermaModule.weightSpace P Λ μ).map (φ : VermaModule P Λ →ₗ[K] V) := fun μ x hx ↦
    mem_of_mem_iSup_of_le (h P) _ hmap hx (htop ▸ Submodule.mem_top)
  refine ⟨eq_top_iff.mpr (htop ▸ iSup_mono hmap), fun μ ↦ ?_, ⟨{Λ}, fun μ hμ ↦ ?_⟩⟩
  · have := VermaModule.finiteDimensional_weightSpace P Λ μ
    exact Submodule.finiteDimensional_of_le (hle μ)
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
    exact ⟨Λ, Finset.mem_singleton_self Λ,
      VermaModule.exists_eq_sub_of_mem_weightSpace P Λ φ hφ hx hx0⟩

end IsCategoryO

variable [CharZero K]

/-- The Verma module `M(Λ)` lies in the category `𝒪` ([Kac] §9.2). -/
theorem VermaModule.isCategoryO (Λ : Dual K H) : IsCategoryO P (VermaModule P Λ) :=
  .of_surjective LieModuleHom.id Function.surjective_id

/-- The irreducible module `L(Λ)` lies in the category `𝒪` ([Kac] §9.3). -/
theorem IrreducibleModule.isCategoryO (Λ : Dual K H) : IsCategoryO P (IrreducibleModule P Λ) :=
  .of_surjective (LieSubmodule.Quotient.mk' _) (LieSubmodule.Quotient.surjective_mk' _)

end Matrix.Realization.KacMoodyAlgebra

end
