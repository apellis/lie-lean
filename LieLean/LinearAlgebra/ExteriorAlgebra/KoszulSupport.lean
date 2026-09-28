/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.ExteriorAlgebra.Koszul
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Finite supports for homogeneous exterior-polynomial tensors

## Main results

Every tensor in the span of exterior-degree `q` and polynomial-degree `n` pure tensors
belongs to `homogeneousTensors b s n q` for some finite set `s`. Thus the finite-support
Koszul identities apply to the entire homogeneous tensor space, with no finite-dimensionality
assumption. This does not yet identify any CE associated-graded quotient.

## References

Reconstructed from Mathlib's spanning theorem for exterior powers; no external source consulted.
-/

open scoped TensorProduct
noncomputable section
namespace ExteriorAlgebra.Koszul
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Enlarging the coordinate support enlarges the homogeneous tensor submodule. -/
theorem homogeneousTensors_mono (b : Module.Basis I R M) (n q : ℕ)
    {s t : Finset I} (hst : s ⊆ t) :
    homogeneousTensors b s n q ≤ homogeneousTensors b t n q := by
  apply Submodule.span_mono
  rintro z ⟨l, p, hl, hs, hp, hv, hz⟩
  exact ⟨l, p, hl, fun i hi => hst (hs i hi), hp, hv.trans hst, hz⟩

/-- A basis word has its stated exterior degree, even when repetitions make it zero. -/
theorem basisWord_mem_exteriorPower (b : Module.Basis I R M) (l : List I) :
    basisWord b l ∈ ⋀[R]^l.length M := by
  induction l with
  | nil =>
    simp [basisWord, exteriorPower]
  | cons i l ih =>
    simpa [basisWord, exteriorPower, pow_succ'] using
      Submodule.mul_mem_mul (LinearMap.mem_range_self (ι R) (b i)) ih

/-- Finite-support homogeneous spans exhaust the usual span of pure tensors of fixed bidegree.
The right side uses all exterior-degree `q` elements and all homogeneous degree-`n` polynomials,
not merely basis words. -/
theorem iSup_homogeneousTensors (b : Module.Basis I R M) (n q : ℕ) :
    (⨆ s : Finset I, homogeneousTensors b s n q) =
      Submodule.span R {z | ∃ (e : ExteriorAlgebra R M) (p : MvPolynomial I R),
        e ∈ ⋀[R]^q M ∧ p.IsHomogeneous n ∧ z = e ⊗ₜ[R] p} := by
  classical
  apply le_antisymm
  · refine iSup_le fun s => Submodule.span_le.mpr ?_
    rintro z ⟨l, p, hl, _, hp, _, rfl⟩
    exact Submodule.subset_span ⟨basisWord b l, p,
      hl ▸ basisWord_mem_exteriorPower b l, hp, rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro z ⟨e, p, he, hp, rfl⟩
    rw [← exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top R q M b.span_eq] at he
    induction he using Submodule.span_induction with
    | mem e he =>
      obtain ⟨v, hv, rfl⟩ := he
      have hv' : ∀ j, ∃ i, b i = v j := fun j => hv ⟨j, rfl⟩
      choose f hf using hv'
      let l := List.ofFn f
      have heq : ExteriorAlgebra.ιMulti R q v = basisWord b l := by
        simp only [ExteriorAlgebra.ιMulti_apply, basisWord, l, List.map_ofFn]
        congr 2
        funext j
        exact congrArg (ι R) (hf j).symm
      rw [heq]
      apply Submodule.mem_iSup_of_mem (l.toFinset ∪ p.vars)
      apply Submodule.subset_span
      exact ⟨l, p, by simp [l], fun i hi => Finset.mem_union_left _ (by simpa),
        hp, Finset.subset_union_right, rfl⟩
    | zero => simp
    | add e f _ _ he hf =>
      rw [TensorProduct.add_tmul]
      exact add_mem he hf
    | smul r e _ he =>
      rw [← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ r he

/-- Every homogeneous exterior-polynomial tensor admits a common finite coordinate support. -/
theorem exists_support_of_mem_homogeneous_span (b : Module.Basis I R M) (n q : ℕ)
    {z : ExteriorAlgebra R M ⊗[R] MvPolynomial I R}
    (hz : z ∈ Submodule.span R {z | ∃ (e : ExteriorAlgebra R M) (p : MvPolynomial I R),
      e ∈ ⋀[R]^q M ∧ p.IsHomogeneous n ∧ z = e ⊗ₜ[R] p}) :
    ∃ s : Finset I, z ∈ homogeneousTensors b s n q := by
  classical
  rw [← iSup_homogeneousTensors b n q] at hz
  apply (Submodule.mem_iSup_of_directed _ ?_).mp hz
  intro s t
  exact ⟨s ∪ t, homogeneousTensors_mono b n q Finset.subset_union_left,
    homogeneousTensors_mono b n q Finset.subset_union_right⟩

end ExteriorAlgebra.Koszul
