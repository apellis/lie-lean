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
square recurrence. Factorial cancellation then yields the integral quotient recurrence,
with support and base values. `G2SquareIntegral` compares its Laurent specialization with
`squareCoeff`.
-/

open Polynomial Finset

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

lemma progressionProduct_zero (k : ℕ) : progressionProduct k 0 = 1 := by
  simp [progressionProduct]

lemma progressionProduct_succ (k n : ℕ) :
    progressionProduct k (n + 1) = progressionProduct k n * gaussian (k * (n + 1)) := by
  simp [progressionProduct, prod_range_succ]

lemma newtonCoeff_zero_succ (t : ℕ) : newtonCoeff 0 (t + 1) = 0 := by
  induction t with
  | zero => simp [newtonCoeff, newtonPolynomial_succ, newtonPolynomial_zero]
  | succ t ih =>
    simp only [newtonCoeff, newtonPolynomial_succ, coeff_sub, mul_coeff_zero,
      coeff_add, coeff_one_zero, coeff_X_zero, coeff_C_zero, comp_C_mul_X_coeff,
      pow_zero, mul_one, add_zero] at *
    rw [ih]
    ring

lemma newtonCoeff_eq_zero_of_lt (n t : ℕ) (h : n < t) : newtonCoeff n t = 0 := by
  induction n generalizing t with
  | zero => obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
            exact newtonCoeff_zero_succ t
  | succ n ih =>
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    have hr := newtonCoeff_gaussian_recurrence n t (by omega)
    rw [ih (t + 1) (by omega), ih t (by omega), mul_zero, mul_zero, add_zero] at hr
    exact (mul_eq_zero.mp hr).resolve_left (gaussian_ne_zero (n + 1) (by omega))

lemma newtonCoeff_eq_zero_of_gt (n t : ℕ) (h : 3 * t < n) : newtonCoeff n t = 0 := by
  induction n generalizing t with
  | zero => omega
  | succ n ih =>
    cases t with
    | zero => simp [newtonCoeff, newtonPolynomial_zero, coeff_one]
    | succ t =>
      have hr := newtonCoeff_recurrence n t
      rw [ih t (by omega), mul_zero, add_zero] at hr
      have hz : ((X : ℤ[X]) ^ (3 * (t + 1)) - X ^ n) * newtonCoeff n (t + 1) = 0 := by
        by_cases he : n = 3 * (t + 1)
        · rw [he, sub_self, zero_mul]
        · rw [ih (t + 1) (by omega), mul_zero]
      rw [hz] at hr
      have hn : (X : ℤ[X]) ^ (n + 1) - 1 ≠ 0 := by
        intro he
        have hc := congrArg (fun p : ℤ[X] ↦ p.coeff (n + 1)) he
        simp [coeff_one] at hc
      exact (mul_eq_zero.mp hr).resolve_left hn

lemma squarePolynomial_eq_zero (n t : ℕ) (h : ¬ (t ≤ n ∧ n ≤ 3 * t)) :
    squarePolynomial n t = 0 := by
  simp [squarePolynomial, h]

lemma squarePolynomial_spec_all (n t : ℕ) :
    progressionProduct 3 t * squarePolynomial n t =
      progressionProduct 1 (3 * t - n) * progressionProduct 3 (n - t) * newtonCoeff n t := by
  by_cases h : t ≤ n ∧ n ≤ 3 * t
  · exact squarePolynomial_spec n t h.1 h.2
  · rw [squarePolynomial_eq_zero n t h]
    have hz : newtonCoeff n t = 0 := by
      by_cases hnt : n < t
      · exact newtonCoeff_eq_zero_of_lt n t hnt
      · exact newtonCoeff_eq_zero_of_gt n t (by omega)
    rw [hz, mul_zero, mul_zero]

lemma squarePolynomial_zero_zero : squarePolynomial 0 0 = 1 := by
  symm
  apply squarePolynomial_unique 0 0 (by omega) (by omega)
  simp [progressionProduct_zero, newtonCoeff, newtonPolynomial_zero]

lemma squarePolynomial_recurrence_first (n t : ℕ) (htn : t ≤ n)
    (hnt : n ≤ 3 * t + 2) :
    progressionProduct 1 (3 * t + 2 - n) * progressionProduct 3 (n - t) *
        gaussian (3 * (t + 1) - n) * newtonCoeff n (t + 1) =
      progressionProduct 3 (t + 1) * gaussian (3 * (n - t)) *
        squarePolynomial n (t + 1) := by
  by_cases he : n = t
  · subst n
    rw [newtonCoeff_eq_zero_of_lt t (t + 1) (by omega)]
    simp [gaussian]
  · have ha : n - t = (n - (t + 1)) + 1 := by omega
    have hb : 3 * (t + 1) - n = (3 * t + 2 - n) + 1 := by omega
    have hs := squarePolynomial_spec_all n (t + 1)
    rw [hb, progressionProduct_succ 1, one_mul] at hs
    rw [ha, progressionProduct_succ 3 (n - (t + 1))]
    rw [hb]
    linear_combination -gaussian (3 * (n - (t + 1) + 1)) * hs

lemma squarePolynomial_recurrence_second (n t : ℕ) (htn : t ≤ n) :
    progressionProduct 1 (3 * t + 2 - n) * progressionProduct 3 (n - t) *
        gaussian (3 * (t + 1)) * newtonCoeff n t =
      progressionProduct 3 (t + 1) * gaussian (3 * t + 2 - n) *
        gaussian (3 * t + 1 - n) * squarePolynomial n t := by
  by_cases he : n ≤ 3 * t
  · have hb : 3 * t + 2 - n = (3 * t - n) + 1 + 1 := by omega
    have hb' : 3 * t + 1 - n = (3 * t - n) + 1 := by omega
    have hs := squarePolynomial_spec n t htn he
    rw [hb, hb', progressionProduct_succ, progressionProduct_succ,
      progressionProduct_succ]
    simp only [one_mul]
    linear_combination -gaussian (3 * (t + 1)) * gaussian (3 * t - n + 1 + 1) *
      gaussian (3 * t - n + 1) * hs
  · rw [newtonCoeff_eq_zero_of_gt n t (by omega),
      squarePolynomial_eq_zero n t (by omega), mul_zero, mul_zero]

/-- The integral quotient satisfies the normalized first-order square recurrence.
The successor support range is essential at its upper endpoint. -/
theorem squarePolynomial_recurrence (n t : ℕ) (htn : t ≤ n)
    (hnt : n ≤ 3 * t + 2) :
    gaussian (n + 1) * squarePolynomial (n + 1) (t + 1) =
      (X : ℤ[X]) ^ n * gaussian (3 * (n - t)) * squarePolynomial n (t + 1) +
        X ^ (3 * t) * gaussian (3 * t + 2 - n) * gaussian (3 * t + 1 - n) *
          squarePolynomial n t := by
  apply mul_left_cancel₀ (progressionProduct_ne_zero 3 (t + 1) (by decide))
  have hs := squarePolynomial_spec (n + 1) (t + 1) (by omega) (by omega)
  rw [show 3 * (t + 1) - (n + 1) = 3 * t + 2 - n by omega,
    show n + 1 - (t + 1) = n - t by omega] at hs
  have hr := newtonCoeff_gaussian_recurrence n t (by omega)
  have h₁ := squarePolynomial_recurrence_first n t htn hnt
  have h₂ := squarePolynomial_recurrence_second n t htn
  linear_combination gaussian (n + 1) * hs +
    progressionProduct 1 (3 * t + 2 - n) * progressionProduct 3 (n - t) * hr +
    X ^ n * h₁ + X ^ (3 * t) * h₂

end LieLean.QuantumGroup.G2Integral.SquareCancellation
