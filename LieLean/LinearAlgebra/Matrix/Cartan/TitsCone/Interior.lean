/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.Matrix.Cartan.TitsCone
import LieLean.LinearAlgebra.Matrix.Cartan.Symmetrizable
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite stabilizers give interior points of the Tits cone

## Main results

* `Matrix.Realization.mem_interior_titsCone_of_finite_stabilizer`: for a point of the
  actual Tits cone, finiteness of its Weyl stabilizer implies interior membership.

The dual is equipped with a Hausdorff real vector-space topology and `H` is
finite-dimensional. These hypotheses specify the usual finite-dimensional topology;
no norm or inner product is chosen, and no symmetrizability is assumed.

## References

Kac, *Infinite dimensional Lie algebras*, third edition, Proposition 3.12(f).
The primary text was not consulted in this investigation; the argument is reconstructed.
It maximizes a linear functional over the actual finite stabilizer, not over the Weyl group.
The essential domain hypothesis is membership in the Tits cone.
-/

open Module

namespace Matrix.Realization

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  [FiniteDimensional ℝ H] [TopologicalSpace (Dual ℝ H)]
  [IsTopologicalAddGroup (Dual ℝ H)] [ContinuousSMul ℝ (Dual ℝ H)]
  [T2Space (Dual ℝ H)] {A : Matrix ι ι ℤ} (P : Realization A ℝ H)
  (hA : A.IsGeneralizedCartan)

/-- A dominant point with finite Weyl stabilizer is interior to the actual Tits cone.
This is the chamber case of Kac, third edition, Proposition 3.12(f), reconstructed. -/
theorem mem_interior_titsCone_of_dominant_of_finite_stabilizer {μ : Dual ℝ H}
    (hμ : μ ∈ P.dominantChamber)
    [Finite (MulAction.stabilizer (P.weylGroup hA) μ)] :
    μ ∈ interior (P.titsCone hA) := by
  classical
  let S := MulAction.stabilizer (P.weylGroup hA) μ
  let _ := Fintype.ofFinite S
  let U : Set (Dual ℝ H) := {ν | ∀ w : S, ∀ i : {i // μ (P.coroot i) ≠ 0},
    0 < (w.val : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) ν (P.coroot i.val)}
  have hU : IsOpen U := by
    change IsOpen {ν | ∀ w : S, ∀ i : {i // μ (P.coroot i) ≠ 0},
      0 < (w.val : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) ν (P.coroot i.val)}
    simp only [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun w ↦ isOpen_iInter_of_finite fun i ↦ ?_
    exact isOpen_lt continuous_const (LinearMap.continuous_of_finiteDimensional
      ((Dual.eval ℝ H (P.coroot i.val)).comp w.val.val.toLinearMap))
  have hμU : μ ∈ U := by
    intro w i
    have hw : (w.val : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) μ = μ := w.property
    rw [hw]
    exact lt_of_le_of_ne (hμ i.val) (Ne.symm i.property)
  have hUX : U ⊆ P.titsCone hA := by
    intro ν hν
    obtain ⟨w, -, hw⟩ := Finset.exists_max_image Finset.univ
      (fun w : S ↦ (w.val : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) ν P.rhoCheck)
      Finset.univ_nonempty
    have hC : (w.val : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) ν ∈ P.dominantChamber := by
      intro i
      by_cases hi : μ (P.coroot i) = 0
      · let r : S := ⟨⟨P.reflection hA i, P.reflection_mem_weylGroup hA i⟩, by
          change P.reflection hA i μ = μ
          rw [reflection_apply, hi, zero_smul, sub_zero]⟩
        have h := hw (r * w) (Finset.mem_univ _)
        change (P.reflection hA i ((w.val : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) ν))
          P.rhoCheck ≤ (w.val : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) ν P.rhoCheck at h
        rw [reflection_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          P.root_rhoCheck, smul_eq_mul, mul_one] at h
        linarith
      · exact (hν w ⟨i, hi⟩).le
    exact ⟨w.val.val⁻¹, inv_mem w.val.property, w.val.val ν, hC,
      w.val.val.symm_apply_apply ν⟩
  exact interior_mono hUX (hU.interior_eq.symm ▸ hμU)

/-- Finite Weyl stabilizer implies interior membership for a point of the actual Tits cone.
This is one direction of Kac, third edition, Proposition 3.12(f), reconstructed. -/
theorem mem_interior_titsCone_of_finite_stabilizer {μ : Dual ℝ H}
    (hμ : μ ∈ P.titsCone hA)
    [Finite (MulAction.stabilizer (P.weylGroup hA) μ)] :
    μ ∈ interior (P.titsCone hA) := by
  obtain ⟨v, hv, ν, hν, rfl⟩ := hμ
  let w : P.weylGroup hA := ⟨v, hv⟩
  let e := MulAction.stabilizerEquivStabilizer (G := P.weylGroup hA)
    (g := w) (a := ν) (b := v ν) rfl
  let _ : Finite (MulAction.stabilizer (P.weylGroup hA) ν) :=
    Finite.of_injective e e.injective
  have hνint := P.mem_interior_titsCone_of_dominant_of_finite_stabilizer hA hν
  have himage : v '' P.titsCone hA ⊆ P.titsCone hA := by
    rintro _ ⟨x, hx, rfl⟩
    exact P.apply_mem_titsCone hA hv hx
  apply interior_mono himage
  change v ν ∈ interior (v.toContinuousLinearEquiv.toHomeomorph '' P.titsCone hA)
  rw [← v.toContinuousLinearEquiv.toHomeomorph.image_interior]
  exact ⟨ν, hνint, rfl⟩

end Matrix.Realization
