/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import LieLean.Algebra.QuantumGroup.BraidCoproduct.RightStringComparison.Compatibility

/-!
# Original skew-generator norms

The original right derivative and bilinear form give the skew-generator norm recurrence.
-/

noncomputable section
open LieLean LieLean.QuantumGroup
namespace RestrictedBraidIsometry
open LusztigF
variable {k I : Type*} [Field k] [DecidableEq I]
  (D : LusztigCartanDatum I) (v : k) (i : I)

/-- Coefficient of the original right derivative of an adjoint string. -/
def derivativeCoefficient (q t : k) : ℕ → k
  | 0 => 0
  | n + 1 => 1 - ((q ^ 2) ^ n * t) ^ 2 + q ^ 2 * derivativeCoefficient q t n

lemma rDeriv_skewAdjoint (x : LusztigF k I) :
    rDeriv D v i (skewAdjoint D v i x) =
      x - twist D v i (twist D v i x) +
        v ^ D.dot i i • skewAdjoint D v i (rDeriv D v i x) := by
  simp only [skewAdjoint_apply, map_sub, rDeriv_mul_θ, rDeriv_θ_mul,
    ite_true, rDeriv_twist, smul_sub, mul_smul_comm]
  module

lemma rDeriv_skewGenerator_succ {j : I} (hij : i ≠ j) (n : ℕ) :
    rDeriv D v i (skewGenerator D v i j (n + 1)) =
      derivativeCoefficient (v ^ D.d i) (v ^ D.dot i j) (n + 1) •
        skewGenerator D v i j n := by
  induction n with
  | zero =>
    simp only [skewGenerator_succ, rDeriv_skewAdjoint, skewGenerator_zero,
      rDeriv_θ, hij, ite_false, map_zero, smul_zero, add_zero, twist_θ,
      map_smul, derivativeCoefficient, pow_zero, one_mul, mul_zero]
    module
  | succ n ih =>
    rw [skewGenerator_succ, rDeriv_skewAdjoint, ih, map_smul,
      ← skewGenerator_succ, twist_skewGenerator, map_smul, twist_skewGenerator,
      smul_smul, smul_smul, zpow_dot_self]
    simp only [derivativeCoefficient]
    module

/-- Norm recurrence in the original free form, hence also its radical quotient. -/
theorem form_skewGenerator_succ {j : I} (hij : i ≠ j) (n : ℕ) :
    form D v (skewGenerator D v i j (n + 1)) (skewGenerator D v i j (n + 1)) =
      thetaNorm D v i * derivativeCoefficient (v ^ D.d i) (v ^ D.dot i j) (n + 1) *
        form D v (skewGenerator D v i j n) (skewGenerator D v i j n) := by
  conv_lhs => arg 1; rw [skewGenerator_succ, skewAdjoint_apply]
  rw [map_sub, LinearMap.sub_apply, form_mul_θ, form_θ_mul,
    lDeriv_skewGenerator D v i hij, map_zero, mul_zero, sub_zero,
    rDeriv_skewGenerator_succ D v i hij, map_smul, smul_eq_mul, mul_assoc]

omit [DecidableEq I] in
lemma derivativeCoefficient_closed (q t : k) (hq : q ≠ 0) (n : ℕ) :
    derivativeCoefficient q t (n + 1) =
      q ^ n * qInt q (n + 1) * (1 - q ^ (2 * n) * t ^ 2) := by
  induction n with
  | zero => simp [derivativeCoefficient, qInt]
  | succ n ih =>
    rw [derivativeCoefficient, ih, qInt_succ (n + 1)]
    have he : q ^ n * qInt q (n + 1) * (q ^ 2 - 1) = q ^ (2 * (n + 1)) - 1 := by
      have h := qInt_mul_sub (v := q) (n + 1)
      have h' := congrArg (fun z : k ↦ q ^ (n + 1) * z) h
      rw [mul_sub, ← mul_pow, ← mul_pow, mul_inv_cancel₀ hq, one_pow] at h'
      simp only [pow_mul, pow_succ, mul_pow] at h' ⊢
      field_simp at h' ⊢
      linear_combination h'
    simp only [pow_mul, pow_succ] at he ⊢
    field_simp
    linear_combination he

end RestrictedBraidIsometry
