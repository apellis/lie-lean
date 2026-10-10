/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.G2SquareDivisibility

/-!
# First-order recurrence for the G₂ Newton polynomials

The cubic Newton recurrence also satisfies a first-order dilation equation. This is the
coefficient recurrence used to compare the integral polynomial kernel with the sparse
square recurrence. The comparison with `squareCoeff` is not asserted here.
-/

open Polynomial

noncomputable section

namespace LieLean.QuantumGroup.G2Integral.SquareCancellation

variable {R : Type*} [CommRing R]

lemma shift_pow_mul_X (x : R) (n : ℕ) (F : R[X]) :
    (shift x ^ n) (X * F) = x ^ n • (X * (shift x ^ n) F) := by
  simp only [shift_pow_apply, mul_comp, X_comp, smul_eq_C_mul]
  ring

lemma shift_newtonOp (x : R) (j n : ℕ) (F : R[X]) :
    shift x (newtonOp x j n F) = newtonOp x j n (shift x F) := by
  have hc (H : R[X]) : shift x ((shift x ^ 3) H) = (shift x ^ 3) (shift x H) :=
    congrArg (fun T : Module.End R R[X] ↦ T H) (Commute.self_pow (shift x) 3).eq
  induction n with
  | zero => simp [newtonOp_zero]
  | succ n ih =>
    simp only [newtonOp_succ, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hc, ih]

lemma shift_pow_newtonOp (x : R) (j n k : ℕ) (F : R[X]) :
    (shift x ^ k) (newtonOp x j n F) = newtonOp x j n ((shift x ^ k) F) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, shift_newtonOp]

/-- Moving one polynomial variable past a shifted interval of Newton factors. -/
lemma newtonOp_succ_start_mul_X (x : R) (j t : ℕ) (F : R[X]) :
    newtonOp x (j + 1) t (X * F) = x ^ (3 * t) • (X * newtonOp x j t F) := by
  induction t with
  | zero => simp [newtonOp_zero]
  | succ t ih =>
    simp only [newtonOp_succ, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, ih, map_smul, shift_pow_mul_X]
    simp only [smul_eq_C_mul, show 3 * (t + 1) = 3 * t + 3 by omega,
      show 3 * (j + 1 + t) = 3 * (j + t) + 3 by omega, pow_add, map_mul]
    ring

lemma newtonOp_mul_X (x : R) (t : ℕ) (F : R[X]) :
    newtonOp x 0 (t + 1) (X * F) =
      x ^ (3 * t) • (X * (x ^ 3 • ((shift x ^ 3) (newtonOp x 0 t F)) -
        newtonOp x 0 t F)) := by
  rw [show t + 1 = 1 + t by omega, newtonOp_add]
  simp only [zero_add, Module.End.mul_apply]
  have hfirst : newtonOp x 0 1 (X * F) = X * (x ^ 3 • ((shift x ^ 3) F) - F) := by
    rw [show 1 = 0 + 1 from rfl, newtonOp_succ, newtonOp_zero]
    simp only [Module.End.mul_apply, Module.End.one_apply, LinearMap.sub_apply,
      zero_add, mul_zero, pow_zero, one_smul, shift_pow_mul_X,
      smul_eq_C_mul]
    ring
  rw [hfirst, newtonOp_succ_start_mul_X x 0 t]
  simp only [map_sub, map_smul, ← shift_pow_newtonOp]

/-- The first-order, division-free dilation equation on the Newton polynomials.
Unlike the cubic definition, this equation relates neighboring coefficients in `n`. -/
theorem newtonPolynomial_dilation (t : ℕ) :
    (1 + X) * (newtonPolynomial (t + 1)).comp (C (X : ℤ[X]) * X) =
      (1 + C ((X : ℤ[X]) ^ (3 * (t + 1))) * X) * newtonPolynomial (t + 1) +
        C ((X : ℤ[X]) ^ (3 * t)) *
          (C ((X : ℤ[X]) ^ (3 * (t + 1))) - 1) * X * newtonPolynomial t := by
  change shift (X : ℤ[X]) (newtonOp (X : ℤ[X]) 0 (t + 1) 1) = _
  rw [shift_newtonOp]
  simp only [shift_apply, one_comp, mul_one, map_add]
  have hx := newtonOp_mul_X (X : ℤ[X]) t (1 : ℤ[X][X])
  rw [mul_one] at hx
  rw [hx]
  have hs : (shift (X : ℤ[X]) ^ 3) (newtonPolynomial t) =
      newtonPolynomial (t + 1) + (X : ℤ[X]) ^ (3 * t) • newtonPolynomial t := by
    simp only [newtonPolynomial, newtonOp_succ, Module.End.mul_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, zero_add]
    abel
  change newtonPolynomial (t + 1) +
    (X : ℤ[X]) ^ (3 * t) • (X * ((X : ℤ[X]) ^ 3 •
      ((shift (X : ℤ[X]) ^ 3) (newtonPolynomial t)) - newtonPolynomial t)) = _
  rw [hs]
  simp only [smul_eq_C_mul, show 3 * (t + 1) = 3 * t + 3 by omega, pow_add, map_mul]
  ring

/-- The scalar coefficient recurrence extracted from first-order dilation. -/
theorem newtonCoeff_recurrence (n t : ℕ) :
    ((X : ℤ[X]) ^ (n + 1) - 1) * newtonCoeff (n + 1) (t + 1) =
      ((X : ℤ[X]) ^ (3 * (t + 1)) - (X : ℤ[X]) ^ n) * newtonCoeff n (t + 1) +
        (X : ℤ[X]) ^ (3 * t) * ((X : ℤ[X]) ^ (3 * (t + 1)) - 1) * newtonCoeff n t := by
  have hc := congrArg (fun F : ℤ[X][X] ↦ F.coeff (n + 1)) (newtonPolynomial_dilation t)
  simp only [add_mul, sub_mul, one_mul, coeff_add, coeff_sub, coeff_X_mul,
    comp_C_mul_X_coeff, mul_assoc, coeff_C_mul] at hc
  unfold newtonCoeff
  linear_combination hc

/-- Ordinary Gaussian integers remove the common polynomial factor `x - 1`.
This cancellation takes place in `ℤ[x]`, before any specialization of the parameter. -/
theorem newtonCoeff_gaussian_recurrence (n t : ℕ) (hn : n ≤ 3 * (t + 1)) :
    gaussian (n + 1) * newtonCoeff (n + 1) (t + 1) =
      (X : ℤ[X]) ^ n * gaussian (3 * (t + 1) - n) * newtonCoeff n (t + 1) +
        (X : ℤ[X]) ^ (3 * t) * gaussian (3 * (t + 1)) * newtonCoeff n t := by
  have hg (m : ℕ) : gaussian m * ((X : ℤ[X]) - 1) = X ^ m - 1 :=
    geom_sum_mul X m
  have he : (X : ℤ[X]) ^ (3 * (t + 1)) =
      X ^ n * X ^ (3 * (t + 1) - n) := by
    rw [← pow_add, Nat.add_sub_of_le hn]
  have hz : (X : ℤ[X]) - 1 ≠ 0 := by
    simpa using (X_sub_C_ne_zero (1 : ℤ))
  apply mul_right_cancel₀ hz
  have hrec := newtonCoeff_recurrence n t
  rw [← hg (n + 1), ← hg (3 * (t + 1))] at hrec
  have hd : (X : ℤ[X]) ^ (3 * (t + 1)) - X ^ n =
      X ^ n * (gaussian (3 * (t + 1) - n) * (X - 1)) := by
    rw [hg, he]
    ring
  rw [hd] at hrec
  linear_combination hrec

end LieLean.QuantumGroup.G2Integral.SquareCancellation
