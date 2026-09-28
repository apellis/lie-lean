/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryO
import LieLean.Algebra.Lie.KacMoody.Integrable

/-!
# Bases of weight vectors

Collect bases of weight spaces using the internal weight-space decomposition. The same
construction serves arbitrary `𝔥`-diagonalizable modules and modules in category `𝒪`.
The latter retain their finite `Fin (finrank ...)` indices for character computations.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsHDiagonalizable.weightBasis`: collect any chosen family
  of weight-space bases.
* `Matrix.Realization.KacMoodyAlgebra.diagWeightBasis`: use `Basis.ofVectorSpace` in each weight.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.weightBasis`: use `Module.finBasis` in each
  finite-dimensional weight space.

## Main results

The corresponding `weightBasis_mem` lemmas place each basis vector in its indexed weight space.

## References

This construction is an application of Mathlib's `DirectSum.IsInternal.collectedBasis`.
It consolidates the constructions previously in `TensorProduct.lean` and `Kostant/Euler.lean`;
no new external theorem is assumed.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H}
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

open Classical in
/-- Collect chosen weight-space bases into a basis of an `𝔥`-diagonalizable module. -/
def IsHDiagonalizable.weightBasis {κ : Dual K H → Type*} (hV : IsHDiagonalizable P V)
    (b : ∀ μ, Basis (κ μ) K (weightSpace P V μ)) : Basis (Σ μ, κ μ) K V :=
  hV.isInternal_weightSpace.collectedBasis b

open Classical in
/-- Each collected basis vector belongs to the weight space indexing it. -/
theorem IsHDiagonalizable.weightBasis_mem {κ : Dual K H → Type*}
    (hV : IsHDiagonalizable P V) (b : ∀ μ, Basis (κ μ) K (weightSpace P V μ)) (j : Σ μ, κ μ) :
    hV.weightBasis b j ∈ weightSpace P V j.1 :=
  hV.isInternal_weightSpace.collectedBasis_mem b j

variable (P V) in
/-- The index type of `diagWeightBasis`. -/
abbrev DiagWeightBasisIndex : Type _ :=
  Σ μ : Dual K H, Basis.ofVectorSpaceIndex K (weightSpace P V μ)

/-- A basis of weight vectors of an `𝔥`-diagonalizable module. -/
def diagWeightBasis (hV : IsHDiagonalizable P V) : Basis (DiagWeightBasisIndex P V) K V :=
  hV.weightBasis fun μ ↦ Basis.ofVectorSpace K (weightSpace P V μ)

theorem diagWeightBasis_mem (hV : IsHDiagonalizable P V) (j : DiagWeightBasisIndex P V) :
    diagWeightBasis hV j ∈ weightSpace P V j.1 :=
  hV.weightBasis_mem _ j

variable (P V) in
/-- Finite indices within each weight space of a module in category `𝒪`. -/
abbrev WeightBasisIndex : Type _ :=
  Σ μ : Dual K H, Fin (finrank K (weightSpace P V μ))

open Classical in
/-- A module in category `𝒪` is the internal direct sum of its weight spaces. -/
theorem IsCategoryO.isInternal_weightSpace (hV : IsCategoryO P V) :
    DirectSum.IsInternal (weightSpace P V) :=
  (show IsHDiagonalizable P V from hV.iSup_weightSpaceOfMap_eq_top).isInternal_weightSpace

/-- A weight-vector basis of a module in category `𝒪`, with finite indices at each weight. -/
def IsCategoryO.weightBasis (hV : IsCategoryO P V) : Basis (WeightBasisIndex P V) K V :=
  (show IsHDiagonalizable P V from hV.iSup_weightSpaceOfMap_eq_top).weightBasis fun μ ↦
    haveI := hV.finiteDimensional_weightSpaceOfMap μ
    Module.finBasis K (weightSpace P V μ)

/-- Each category-`𝒪` basis vector has the weight indexing it. -/
theorem IsCategoryO.weightBasis_mem (hV : IsCategoryO P V) (j : WeightBasisIndex P V) :
    hV.weightBasis j ∈ weightSpace P V j.1 :=
  (show IsHDiagonalizable P V from hV.iSup_weightSpaceOfMap_eq_top).weightBasis_mem _ j

end Matrix.Realization.KacMoodyAlgebra
