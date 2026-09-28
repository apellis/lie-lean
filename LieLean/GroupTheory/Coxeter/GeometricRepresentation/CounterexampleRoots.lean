/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Explicit primitive roots for the (5,10,2) reflection coefficients

## Main results
* `exists_primitive_roots_with_coefficients`: simultaneous roots of exact orders 4, 10, 20
  with inverse sums 0, (1 + sqrt 5)/2, sqrt (3 - (1 + sqrt 5)/2).
* `half_coefficients`: the corresponding half-sums, in the `geomCoeff` convention.

## References and boundary
The arguments are reconstructed using Mathlib's exact trigonometric identities, not
transcribed from an external reference. In the repository, `geomCoeff` is the HALF-sum;
`geomReflection_single` uses twice that coefficient. Thus our inverse sums, not our
half-sums, are the off-diagonal entries of the explicit reflection matrices.
This artifact concerns explicit roots, not `CoxeterMatrix.geomRoot`'s opaque choice.
-/


namespace GeometricRootBridge

/-- The order-four root for the exponent-two edge. -/
noncomputable def root4 : ℂ := Complex.I

/-- The usual order-ten root for the exponent-five edge. -/
noncomputable def root10 : ℂ := Complex.exp ((Real.pi / 5 : ℝ) * Complex.I)

/-- The nonstandard order-twenty root for the exponent-ten edge. -/
noncomputable def root20 : ℂ := Complex.exp ((3 * Real.pi / 10 : ℝ) * Complex.I)

/-- This explicit root is primitive of order four (Mathlib). -/
theorem primitive_root4 : IsPrimitiveRoot root4 4 := Complex.isPrimitiveRoot_I

/-- This explicit root is primitive of order ten (Mathlib's exponential criterion). -/
theorem primitive_root10 : IsPrimitiveRoot root10 10 := by
  convert Complex.isPrimitiveRoot_exp 10 (by norm_num) using 1
  simp only [root10, Complex.ofReal_div, Complex.ofReal_ofNat]
  congr 1
  ring

/-- Coprimality of 3 and 20 gives exact order twenty, not merely a power relation. -/
theorem primitive_root20 : IsPrimitiveRoot root20 20 := by
  convert Complex.isPrimitiveRoot_exp_of_coprime 3 20 (by norm_num) (by norm_num) using 1
  simp only [root20, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Nat.cast_ofNat]
  congr 1
  ring

/-- Euler's identity gives the doubled geometric coefficient. -/
theorem exp_add_inv (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) + (Complex.exp ((t : ℂ) * Complex.I))⁻¹ =
      ((2 * Real.cos t : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos,
    Complex.cos, ← Complex.exp_neg]
  ring

/-- Exact positive value of twice the cosine at the nonstandard order-twenty root. -/
theorem two_cos_three_pi_div_ten :
    2 * Real.cos (3 * Real.pi / 10) = Real.sqrt (3 - (1 + Real.sqrt 5) / 2) := by
  have hc : 0 ≤ Real.cos (3 * Real.pi / 10) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hdouble := Real.cos_two_mul (3 * Real.pi / 10)
  have hcomp : Real.cos (2 * (3 * Real.pi / 10)) =
      -Real.cos (2 * (Real.pi / 5)) := by
    rw [show 2 * (3 * Real.pi / 10) = Real.pi - 2 * (Real.pi / 5) by ring,
      Real.cos_pi_sub]
  rw [hcomp, Real.cos_two_mul, Real.cos_pi_div_five] at hdouble
  have hs : (2 * Real.cos (3 * Real.pi / 10)) ^ 2 =
      3 - (1 + Real.sqrt 5) / 2 := by nlinarith
  have hnonneg := sq_nonneg (2 * Real.cos (3 * Real.pi / 10))
  apply Eq.symm
  apply (Real.sqrt_eq_iff_mul_self_eq (by nlinarith) (by positivity)).2
  nlinarith

/-- The exponent-two doubled coefficient is zero. -/
theorem root4_add_inv : root4 + root4⁻¹ = 0 := by
  simp [root4, Complex.inv_I]

/-- The exponent-five doubled coefficient is the positive golden ratio. -/
theorem root10_add_inv :
    root10 + root10⁻¹ = (((1 + Real.sqrt 5) / 2 : ℝ) : ℂ) := by
  rw [root10, exp_add_inv, Real.cos_pi_div_five]
  congr 1
  ring

/-- The exponent-ten doubled coefficient is the bad square-root coefficient. -/
theorem root20_add_inv :
    root20 + root20⁻¹ = ((Real.sqrt (3 - (1 + Real.sqrt 5) / 2) : ℝ) : ℂ) := by
  rw [root20, exp_add_inv, two_cos_three_pi_div_ten]

/-- Explicit simultaneous primitive-root witnesses for all three off-diagonal coefficients.
This is reconstructed from exact trigonometry; no claim about opaque chosen roots is made. -/
theorem exists_primitive_roots_with_coefficients :
    ∃ z4 z10 z20 : ℂ,
      IsPrimitiveRoot z4 4 ∧ IsPrimitiveRoot z10 10 ∧ IsPrimitiveRoot z20 20 ∧
      z4 + z4⁻¹ = 0 ∧
      z10 + z10⁻¹ = (((1 + Real.sqrt 5) / 2 : ℝ) : ℂ) ∧
      z20 + z20⁻¹ = ((Real.sqrt (3 - (1 + Real.sqrt 5) / 2) : ℝ) : ℂ) :=
  ⟨root4, root10, root20, primitive_root4, primitive_root10, primitive_root20,
    root4_add_inv, root10_add_inv, root20_add_inv⟩

/-- Exact half-sums in the repository's `geomCoeff` convention (not matrix entries). -/
theorem half_coefficients :
    (root4 + root4⁻¹) / 2 = 0 ∧
    (root10 + root10⁻¹) / 2 = (((1 + Real.sqrt 5) / 4 : ℝ) : ℂ) ∧
    (root20 + root20⁻¹) / 2 =
      ((Real.sqrt (3 - (1 + Real.sqrt 5) / 2) / 2 : ℝ) : ℂ) := by
  rw [root4_add_inv, root10_add_inv, root20_add_inv]
  push_cast
  constructor
  · simp
  constructor <;> ring

/-- The exact multiplicative orders expected by `orderOf_geomRoot`. -/
theorem root_orders : orderOf root4 = 2 * 2 ∧ orderOf root10 = 2 * 5 ∧
    orderOf root20 = 2 * 10 :=
  ⟨primitive_root4.eq_orderOf.symm, primitive_root10.eq_orderOf.symm,
    primitive_root20.eq_orderOf.symm⟩


end GeometricRootBridge
