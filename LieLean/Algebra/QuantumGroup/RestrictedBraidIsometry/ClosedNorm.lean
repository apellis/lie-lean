/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import LieLean.Algebra.QuantumGroup.RestrictedBraidIsometry.GeneratorNorm

/-!
# Closed skew-generator norms

Closed norms of bounded divided generators and invariance under complementation.
-/

noncomputable section
open LieLean LieLean.QuantumGroup LusztigF
namespace RestrictedBraidIsometry
variable {k : Type*} [Field k]

lemma closedNorm_geometric (q : k) (hq : q ≠ 0) (m : ℕ) :
    1 - q⁻¹ ^ (2 * (m + 1)) =
      (1 - q⁻¹ ^ 2) * q⁻¹ ^ m * qInt q (m + 1) := by
  calc
    _ = q⁻¹ ^ (m + 1) * (q ^ (m + 1) - q⁻¹ ^ (m + 1)) := by
      rw [mul_sub, ← mul_pow, inv_mul_cancel₀ hq, one_pow]
      ring
    _ = _ := by
      rw [← qInt_mul_sub, pow_succ]
      have hc := inv_mul_cancel₀ hq
      linear_combination (q⁻¹ ^ m * qInt q (m + 1)) * hc

lemma closedNorm_coefficient (q : k) (hq : q ≠ 0)
    (hd : 1 - q⁻¹ ^ 2 ≠ 0) (n m : ℕ) :
    (1 - q⁻¹ ^ 2)⁻¹ * derivativeCoefficient q (q⁻¹ ^ (n + m + 1)) (n + 1) =
      q ^ n * q⁻¹ ^ m * qInt q (n + 1) * qInt q (m + 1) := by
  rw [derivativeCoefficient_closed q _ hq]
  have hp : q ^ (2 * n) * (q⁻¹ ^ (n + m + 1)) ^ 2 = q⁻¹ ^ (2 * (m + 1)) := by
    rw [show n + m + 1 = n + (m + 1) by omega, pow_add, mul_pow,
      ← pow_mul, Nat.mul_comm n 2, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq, one_pow, one_mul]
    ring
  rw [hp, closedNorm_geometric q hq]
  have hc := inv_mul_cancel₀ hd
  linear_combination q ^ n * q⁻¹ ^ m * qInt q (n + 1) * qInt q (m + 1) * hc

lemma closedNorm_binomial_step (q : k) (hq : q - q⁻¹ ≠ 0) (A n : ℕ) :
    qInt q (n + 1) * qBinomial q A (n + 1) =
      qInt q (A - n) * qBinomial q A n := by
  apply mul_left_cancel₀ hq
  have h := qBinomial_mul_sub q A n
  simpa only [← qInt_mul_sub, mul_assoc] using h.symm

variable {I : Type*} [DecidableEq I] (D : LusztigCartanDatum I) (v : k)

theorem form_skewGenerator_closed (hv : v ≠ 0)
    (hroot : ∀ r : ℕ, 0 < r → v ^ r ≠ 1) {i j : I} (hij : i ≠ j)
    (n : ℕ) (hn : n ≤ negA D i j) :
    form D v (skewGenerator D v i j n) (skewGenerator D v i j n) =
      thetaNorm D v j * (v ^ D.d i)⁻¹ ^ (n * (negA D i j - n)) *
        qBinomial (v ^ D.d i) (negA D i j) n * qFactorial (v ^ D.d i) n ^ 2 := by
  let q := v ^ D.d i
  have hq : q ≠ 0 := pow_ne_zero _ hv
  have hr : ∀ r : ℕ, 0 < r → q ^ r ≠ 1 := fun r hr ↦ by
    dsimp [q]
    rw [← pow_mul]
    exact hroot _ (Nat.mul_pos (D.d_pos i) hr)
  have hdiff : q - q⁻¹ ≠ 0 := sub_inv_ne_zero_of_pow_ne_one hq hr
  have hd : 1 - q⁻¹ ^ 2 ≠ 0 := by
    intro h
    have he : q⁻¹ ^ 2 = 1 := (sub_eq_zero.mp h).symm
    have := congrArg (fun z : k ↦ z⁻¹) he
    simp only [← inv_pow, inv_inv, inv_one] at this
    exact hr 2 (by omega) this
  have ht : v ^ D.dot i j = q⁻¹ ^ negA D i j := by
    apply zpow_dot_eq hij
    rw [cartanMatrix_eq_neg_negA hij]
    omega
  induction n with
  | zero => simp [skewGenerator_zero, form_θ_θ]
  | succ n ih =>
    obtain ⟨m, hm⟩ : ∃ m, negA D i j = n + m + 1 := ⟨negA D i j - n - 1, by omega⟩
    have hprev : negA D i j - n = m + 1 := by omega
    have hnext : negA D i j - (n + 1) = m := by omega
    rw [form_skewGenerator_succ D v i hij, ih (by omega)]
    change (1 - q⁻¹ ^ 2)⁻¹ * derivativeCoefficient q (v ^ D.dot i j) (n + 1) *
      (thetaNorm D v j * q⁻¹ ^ (n * (negA D i j - n)) *
        qBinomial q (negA D i j) n * qFactorial q n ^ 2) = _
    rw [ht, hm, closedNorm_coefficient q hq hd]
    rw [← hm]
    change _ = thetaNorm D v j * q⁻¹ ^ ((n + 1) * (negA D i j - (n + 1))) *
      qBinomial q (negA D i j) (n + 1) * qFactorial q (n + 1) ^ 2
    rw [hprev, hnext, qFactorial_succ]
    have hp : q ^ n * q⁻¹ ^ m * q⁻¹ ^ (n * (m + 1)) = q⁻¹ ^ ((n + 1) * m) := by
      rw [mul_assoc, ← pow_add, show m + n * (m + 1) = n + (n + 1) * m by ring,
        pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq, one_pow, one_mul]
    have hb := closedNorm_binomial_step q hdiff (negA D i j) n
    rw [hprev] at hb
    calc
      _ = thetaNorm D v j * (q ^ n * q⁻¹ ^ m * q⁻¹ ^ (n * (m + 1))) *
          qInt q (n + 1) * (qInt q (m + 1) * qBinomial q (negA D i j) n) *
          qFactorial q n ^ 2 := by ring
      _ = _ := by rw [hp, ← hb]; ring

/-- The bounded divided-generator norm in the original form. -/
theorem form_skewDividedGenerator_closed (hv : v ≠ 0)
    (hroot : ∀ r : ℕ, 0 < r → v ^ r ≠ 1) {i j : I} (hij : i ≠ j)
    (n : ℕ) (hn : n ≤ negA D i j) :
    form D v (skewDividedGenerator D v i j n) (skewDividedGenerator D v i j n) =
      thetaNorm D v j * (v ^ D.d i)⁻¹ ^ (n * (negA D i j - n)) *
        qBinomial (v ^ D.d i) (negA D i j) n := by
  have hf := qFactorial_ne_zero_of_not_root (D := D) hv hroot i n
  simp only [skewDividedGenerator, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [form_skewGenerator_closed D v hv hroot hij n hn]
  field_simp

/-- Complementary bounded divided generators have the same original norm. -/
theorem form_skewDividedGenerator_complement (hv : v ≠ 0)
    (hroot : ∀ r : ℕ, 0 < r → v ^ r ≠ 1) {i j : I} (hij : i ≠ j)
    (n : ℕ) (hn : n ≤ negA D i j) :
    form D v (skewDividedGenerator D v i j n) (skewDividedGenerator D v i j n) =
      form D v (skewDividedGenerator D v i j (negA D i j - n))
        (skewDividedGenerator D v i j (negA D i j - n)) := by
  rw [form_skewDividedGenerator_closed D v hv hroot hij n hn,
    form_skewDividedGenerator_closed D v hv hroot hij _ (Nat.sub_le _ _),
    Nat.sub_sub_self hn, qBinomial_symm _ hn, Nat.mul_comm (negA D i j - n) n]

/-- The closed norm on the actual radical quotient, at the original parameter `X`. -/
theorem quotientForm_skewDividedGenerator_closed [Finite I] {i j : I} (hij : i ≠ j)
    (n : ℕ) (hn : n ≤ negA D i j) :
    quotientForm D
        (toQuotient D (RatFunc.X : RatFunc ℚ) (skewDividedGenerator D RatFunc.X i j n))
        (toQuotient D (RatFunc.X : RatFunc ℚ) (skewDividedGenerator D RatFunc.X i j n)) =
      thetaNorm D (RatFunc.X : RatFunc ℚ) j *
        (RatFunc.X ^ D.d i)⁻¹ ^ (n * (negA D i j - n)) *
        qBinomial (RatFunc.X ^ D.d i) (negA D i j) n := by
  rw [quotientForm_toQuotient]
  exact form_skewDividedGenerator_closed D RatFunc.X RatFunc.X_ne_zero
    ratFunc_X_not_root hij n hn

/-- Complementary bounded generators have equal norms in the original radical quotient. -/
theorem quotientForm_skewDividedGenerator_complement [Finite I] {i j : I} (hij : i ≠ j)
    (n : ℕ) (hn : n ≤ negA D i j) :
    quotientForm D
        (toQuotient D (RatFunc.X : RatFunc ℚ) (skewDividedGenerator D RatFunc.X i j n))
        (toQuotient D (RatFunc.X : RatFunc ℚ) (skewDividedGenerator D RatFunc.X i j n)) =
      quotientForm D
        (toQuotient D (RatFunc.X : RatFunc ℚ)
          (skewDividedGenerator D RatFunc.X i j (negA D i j - n)))
        (toQuotient D (RatFunc.X : RatFunc ℚ)
          (skewDividedGenerator D RatFunc.X i j (negA D i j - n))) := by
  rw [quotientForm_toQuotient, quotientForm_toQuotient]
  exact form_skewDividedGenerator_complement D RatFunc.X RatFunc.X_ne_zero
    ratFunc_X_not_root hij n hn

end RestrictedBraidIsometry
