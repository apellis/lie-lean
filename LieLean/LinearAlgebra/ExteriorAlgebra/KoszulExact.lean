/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.ExteriorAlgebra.Koszul

/-!
# Homogeneous finite-support Koszul exactness

## Main results

* `homotopy_mem_homogeneousTensors`: the concrete homotopy retains the finite coordinate
  support and shifts polynomial/exterior degrees by `(-1, +1)`.
* `homotopy_eq_zero_of_polynomial_degree_zero`: the homotopy vanishes in polynomial degree zero.
* `exists_homogeneous_primitive`: every positive-total-degree homogeneous cycle admits a
  homogeneous primitive with the same finite coordinate support.

## References

Reconstructed from the concrete anticommutator and Mathlib's homogeneous derivative API;
no external reference was consulted. No CE identification or BGG result is asserted.
-/

open scoped TensorProduct BigOperators

noncomputable section

namespace MvPolynomial

variable {R I : Type*} [CommSemiring R]

/-- Partial differentiation introduces no new polynomial variables. -/
theorem vars_pderiv_subset (p : MvPolynomial I R) (i : I) :
    (pderiv i p).vars ⊆ p.vars := by
  classical
  intro j hj
  obtain ⟨d, hd, hjd⟩ := (mem_vars_iff_mem_support j).mp hj
  refine (mem_vars_iff_mem_support j).mpr ⟨d + Finsupp.single i 1, ?_, ?_⟩
  · apply mem_support_iff.mpr
    exact left_ne_zero_of_mul (by simpa only [coeff_pderiv] using mem_support_iff.mp hd)
  · apply Finsupp.mem_support_iff.mpr
    intro hz
    apply Finsupp.mem_support_iff.mp hjd
    exact Nat.eq_zero_of_add_eq_zero_right (by simpa only [Finsupp.add_apply] using hz)

end MvPolynomial

namespace ExteriorAlgebra.Koszul

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The concrete derivative homotopy has bidegree `(-1,+1)` and retains both supports.
At polynomial degree zero, subtraction is truncated; the stronger vanishing result is below. -/
theorem homotopy_mem_homogeneousTensors (b : Module.Basis I R M) (s : Finset I)
    (n q : ℕ) (z : ExteriorAlgebra R M ⊗[R] MvPolynomial I R)
    (hz : z ∈ homogeneousTensors b s n q) :
    homotopy b s z ∈ homogeneousTensors b s (n - 1) (q + 1) := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, p, hlq, hl, hp, hs, rfl⟩ := hz
    simp only [homotopy, LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro i hi
    rw [homotopyTerm_tmul]
    apply Submodule.subset_span
    refine ⟨i :: l, MvPolynomial.pderiv i p, ?_, ?_, hp.pderiv,
      (MvPolynomial.vars_pderiv_subset p i).trans hs, ?_⟩
    · simp only [List.length_cons, hlq]
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hl j hj
    · rfl
  | zero => simpa only [map_zero] using
      (homogeneousTensors b s (n - 1) (q + 1)).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using
      (homogeneousTensors b s (n - 1) (q + 1)).add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using
      (homogeneousTensors b s (n - 1) (q + 1)).smul_mem a hx

/-- The derivative homotopy vanishes on polynomial-degree-zero homogeneous tensors. -/
theorem homotopy_eq_zero_of_polynomial_degree_zero (b : Module.Basis I R M) (s : Finset I)
    (q : ℕ) (z : ExteriorAlgebra R M ⊗[R] MvPolynomial I R)
    (hz : z ∈ homogeneousTensors b s 0 q) : homotopy b s z = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, p, _, _, hp, _, rfl⟩ := hz
    rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous,
      MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hp
    rw [hp]
    simp [homotopy, homotopyTerm_tmul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
  | smul a x _ hx => simp only [map_smul, hx, smul_zero]

section Field

variable {K : Type*} [Field K] [CharZero K] [Module K M]

/-- An explicit, support-preserving homogeneous primitive, obtained by dividing the concrete
homotopy by the positive total degree. -/
theorem normalized_homotopy_primitive (b : Module.Basis I K M) (s : Finset I) (n q : ℕ)
    (z : ExteriorAlgebra K M ⊗[K] MvPolynomial I K)
    (hz : z ∈ homogeneousTensors b s n q) (hcycle : delta b s z = 0)
    (hpos : 0 < n + q) :
    ((n + q : ℕ) : K)⁻¹ • homotopy b s z ∈ homogeneousTensors b s (n - 1) (q + 1) ∧
      delta b s (((n + q : ℕ) : K)⁻¹ • homotopy b s z) = z := by
  refine ⟨(homogeneousTensors b s (n - 1) (q + 1)).smul_mem _
    (homotopy_mem_homogeneousTensors b s n q z hz), ?_⟩
  have heq := anticommutator_homogeneous b s n q z hz
  rw [hcycle, map_zero, add_zero] at heq
  rw [map_smul, heq, ← Nat.cast_smul_eq_nsmul K, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos)), one_smul]

/-- Positive-exterior-degree cycles in polynomial degree zero vanish. This explicitly handles
that boundary rather than treating a truncated negative polynomial degree as nonzero. -/
theorem eq_zero_of_cycle_polynomial_degree_zero (b : Module.Basis I K M) (s : Finset I)
    (q : ℕ) (z : ExteriorAlgebra K M ⊗[K] MvPolynomial I K)
    (hz : z ∈ homogeneousTensors b s 0 q) (hcycle : delta b s z = 0)
    (hq : 0 < q) : z = 0 := by
  have h := (normalized_homotopy_primitive b s 0 q z hz hcycle (by simpa using hq)).2
  rw [homotopy_eq_zero_of_polynomial_degree_zero b s q z hz, smul_zero, map_zero] at h
  exact h.symm

/-- Homogeneous finite-support Koszul exactness in positive total degree: the primitive has
polynomial degree `n - 1`, exterior degree `q + 1`, and both supports still contained in `s`.
When `n = 0`, every such cycle vanishes and the primitive is zero. The basis index type is
arbitrary; there is no global finiteness assumption. -/
theorem exists_homogeneous_primitive (b : Module.Basis I K M) (s : Finset I) (n q : ℕ)
    (z : ExteriorAlgebra K M ⊗[K] MvPolynomial I K)
    (hz : z ∈ homogeneousTensors b s n q) (hcycle : delta b s z = 0)
    (hpos : 0 < n + q) :
    ∃ y ∈ homogeneousTensors b s (n - 1) (q + 1), delta b s y = z := by
  exact ⟨((n + q : ℕ) : K)⁻¹ • homotopy b s z,
    normalized_homotopy_primitive b s n q z hz hcycle hpos⟩

end Field

end ExteriorAlgebra.Koszul

