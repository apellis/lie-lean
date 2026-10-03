/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.Vanishing
import Mathlib.Algebra.Lie.DirectSum
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Acyclicity of direct sums of CE coefficient modules

## Main results

* `subsingleton_homology_directSum`: arbitrary direct sums preserve CE homology vanishing
  in any fixed degree, over any commutative ring.

## References

The finite-support argument is reconstructed from Mathlib's tensor/direct-sum equivalence
and the proved naturality of the actual CE differential.
-/

noncomputable section
open scoped TensorProduct DirectSum BigOperators
open TensorProduct

namespace LieModule.ChevalleyEilenberg

variable {R L I : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : I → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, LieRingModule L (M i)] [∀ i, LieModule R L (M i)]

omit [∀ i, LieModule R L (M i)] in
/-- The tensor/direct-sum equivalence computes the actual coefficient projection. -/
theorem directSum_tensor_component [DecidableEq I]
    (z : ExteriorAlgebra R L ⊗[R] (⨁ i, M i)) (i : I) :
    directSumRight R R (ExteriorAlgebra R L) M z i =
      ((DirectSum.lieModuleComponent R I L M i).toLinearMap).lTensor _ z := by
  induction z with
  | tmul e m => exact directSumRight_tmul R R e m i
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy]

omit [∀ i, LieModule R L (M i)] in
/-- The inverse tensor/direct-sum equivalence computes the actual coefficient inclusion. -/
theorem directSum_tensor_symm_of [DecidableEq I] (i : I)
    (z : ExteriorAlgebra R L ⊗[R] M i) :
    (directSumRight R R (ExteriorAlgebra R L) M).symm (DirectSum.of _ i z) =
      ((DirectSum.lieModuleOf R I L M i).toLinearMap).lTensor _ z := by
  induction z with
  | tmul e m =>
    change (directSumRight R R (ExteriorAlgebra R L) M).symm
      (DirectSum.lof R _ _ i (e ⊗ₜ[R] m)) = e ⊗ₜ[R] DirectSum.lof R _ _ i m
    exact directSumRight_symm_lof_tmul R R e i m
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A cycle with arbitrary direct-sum coefficients is a boundary when each coordinate
homology vanishes. Naturality here is for the actual CE differential and Lie actions. -/
theorem directSum_cycle_boundary (q : ℕ)
    (h : ∀ i, Subsingleton (homology R L (M i) q))
    {z : ExteriorAlgebra R L ⊗[R] (⨁ i, M i)}
    (hz : z ∈ cycles R L (⨁ i, M i) q) :
    z ∈ boundaries R L (⨁ i, M i) q := by
  classical
  let e := directSumRight R R (ExteriorAlgebra R L) M
  have hc (i : I) : e z i ∈ boundaries R L (M i) q := by
    rw [(subsingleton_homology_iff R L (M i) q).mp (h i)]
    rw [directSum_tensor_component]
    exact lTensor_mem_cycles (DirectSum.lieModuleComponent R I L M i) hz
  have he : z = ∑ i ∈ (e z).support,
      ((DirectSum.lieModuleOf R I L M i).toLinearMap).lTensor _ (e z i) := by
    conv_lhs => rw [← e.symm_apply_apply z, ← DirectSum.sum_support_of (e z)]
    simp only [map_sum, e, directSum_tensor_symm_of]
  rw [he]
  exact Submodule.sum_mem _ fun i _ =>
    lTensor_mem_boundaries (DirectSum.lieModuleOf R I L M i) (hc i)

/-- Vanishing of constituent CE homology implies vanishing for their arbitrary direct sum,
over any commutative ring. There is no finiteness assumption on the index or modules. -/
theorem subsingleton_homology_directSum (q : ℕ)
    (h : ∀ i, Subsingleton (homology R L (M i) q)) :
    Subsingleton (homology R L (⨁ i, M i) q) := by
  apply (subsingleton_homology_iff R L (⨁ i, M i) q).mpr
  exact le_antisymm (boundaries_le_cycles q) (fun _ hz => directSum_cycle_boundary M q h hz)

end LieModule.ChevalleyEilenberg

