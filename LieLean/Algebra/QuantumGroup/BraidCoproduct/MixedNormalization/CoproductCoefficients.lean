/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.MixedNormalization.Convolution

/-!
# Coproduct coefficient products

Products and top coefficients in the finite mixed-root coproduct row.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994),
37.3.1–37.3.2 and the proof of 38.1.8 (printed pp. 293, 297–299).
The finite-cutoff argument uses the actual quantum group and original Verma modules.
No restricted braid isometry or PBW norm conclusion is asserted here.
-/

open LieLean
noncomputable section
namespace MixedNormalization
open QuantumGroup MixedIntertwining
variable {k : Type*} [Field k]

def gaussianCoeff (q : k) (m t : ℕ) : k :=
  q ^ (t * (m - t)) * qBinomial q m t

lemma gaussianCoeff_pascal {q : k} (hq : q ≠ 0) (m t : ℕ) (ht : t < m) :
    gaussianCoeff q (m + 1) (t + 1) = gaussianCoeff q m (t + 1) +
      q ^ (2 * (m - t)) * gaussianCoeff q m t := by
  obtain ⟨b, rfl⟩ : ∃ b, m = t + 1 + b := ⟨m - (t + 1), by omega⟩
  simp only [gaussianCoeff, qBinomial_succ_succ,
    show t + 1 + b + 1 - (t + 1) = b + 1 by omega,
    show t + 1 + b - t = b + 1 by omega,
    show t + 1 + b - (t + 1) = b by omega, inv_pow]
  field_simp
  ring

lemma gaussianCoeff_pascal' {q : k} (hq : q ≠ 0) (m t : ℕ) (ht : t < m) :
    gaussianCoeff q (m + 1) (t + 1) = q ^ (2 * (t + 1)) * gaussianCoeff q m (t + 1) +
      gaussianCoeff q m t := by
  have h := qBinomial_succ_succ q⁻¹ m t
  simp only [qBinomial_inv, inv_inv] at h
  obtain ⟨b, rfl⟩ : ∃ b, m = t + 1 + b := ⟨m - (t + 1), by omega⟩
  simp only [gaussianCoeff, h,
    show t + 1 + b + 1 - (t + 1) = b + 1 by omega,
    show t + 1 + b - t = b + 1 by omega,
    show t + 1 + b - (t + 1) = b by omega, inv_pow]
  field_simp
  ring

/-- Closed product formula for the entire previously verified coproduct row. -/
theorem coproductCoeff_product {q : k} (hq : q ≠ 0) (Q : k) (m t : ℕ) :
    coproductCoeff q Q m t = gaussianCoeff q m t *
      ∏ h ∈ Finset.Ico t m, (1 - q ^ (2 * h) * Q⁻¹ ^ 2) := by
  induction m generalizing t with
  | zero =>
    cases t <;> simp [coproductCoeff, gaussianCoeff]
  | succ m ih =>
    rcases lt_trichotomy t (m + 1) with ht | rfl | ht
    · cases t with
      | zero =>
        rw [coproductCoeff, ih, Finset.prod_Ico_succ_top (Nat.zero_le m)]
        simp only [gaussianCoeff, Nat.zero_mul, Nat.sub_zero, pow_zero,
          qBinomial_zero_right, mul_one, one_mul]
        ring
      | succ t =>
        have htm : t < m := by omega
        rw [coproductCoeff, ih, ih,
          Finset.prod_Ico_succ_top (by omega : t + 1 ≤ m),
          Finset.prod_eq_prod_Ico_succ_bot htm]
        have h1 := gaussianCoeff_pascal hq m t htm
        have h2 := gaussianCoeff_pascal' hq m t htm
        have hp : q ^ (2 * (m + t + 1)) = q ^ (2 * m) * q ^ (2 * (t + 1)) := by
          rw [← pow_add]
          congr 1
          omega
        have hp2 : q ^ (2 * t) * q ^ (2 * (m - t)) = q ^ (2 * m) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hp]
        linear_combination
          (∏ h ∈ Finset.Ico (t + 1) m, (1 - q ^ (2 * h) * Q⁻¹ ^ 2)) *
            (-h1 + q ^ (2 * m) * Q⁻¹ ^ 2 * h2 - Q⁻¹ ^ 2 * gaussianCoeff q m t * hp2)
    · simp [coproductCoeff_diag, gaussianCoeff]
    · rw [coproductCoeff_above q Q ht]
      simp [gaussianCoeff, qBinomial_eq_zero_of_lt q ht]

lemma rootProduct {q : k} (hq : q ≠ 0) (a t : ℕ) :
    (∏ h ∈ Finset.Ico t (t + a), (1 - q ^ (2 * h) * (q ^ (t + a))⁻¹ ^ 2)) =
      (q - q⁻¹) ^ a * qFactorial q a * q⁻¹ ^ ((∑ h ∈ Finset.range a, h) + a) := by
  have hprod : (∏ h ∈ Finset.Ico t (t + a),
      (1 - q ^ (2 * h) * (q ^ (t + a))⁻¹ ^ 2)) =
      ∏ h ∈ Finset.range a, (1 - q⁻¹ ^ (2 * (h + 1))) := by
    rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel_left,
      ← Finset.prod_range_reflect]
    apply Finset.prod_congr rfl
    intro h hh
    have hh' := Finset.mem_range.mp hh
    obtain ⟨b, hb⟩ : ∃ b, a = h + 1 + b := ⟨a - (h + 1), by omega⟩
    rw [hb, show h + 1 + b - 1 - h = b by omega]
    simp only [inv_pow]
    field_simp
    ring
  rw [hprod]
  clear hprod
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.prod_range_succ, ih, Finset.sum_range_succ, qFactorial_succ, pow_succ]
    have hfactor : 1 - q⁻¹ ^ (2 * (a + 1)) =
        (q - q⁻¹) * qInt q (a + 1) * q⁻¹ ^ (a + 1) := by
      rw [qInt_mul_sub]
      simp only [inv_pow]
      field_simp
      ring
    rw [hfactor]
    simp only [pow_add]
    ring

/-- Exact all-index top-row coefficient, with no rank restriction. -/
theorem coproductCoeff_top {q : k} (hq : q ≠ 0)
    (hf : ∀ n, qFactorial q n ≠ 0) (a t : ℕ) :
    coproductCoeff q (q ^ (t + a)) (t + a) t =
      (qFactorial q (t + a) / qFactorial q t) * (q - q⁻¹) ^ a *
        q ^ (t * a) * q⁻¹ ^ ((∑ h ∈ Finset.range a, h) + a) := by
  rw [coproductCoeff_product hq, rootProduct hq]
  have hb := qBinomial_mul_qFactorial_mul_qFactorial (v := q)
    (n := t + a) (j := t) (Nat.le_add_right t a)
  simp only [Nat.add_sub_cancel_left] at hb
  have hb' : qBinomial q (t + a) t =
      qFactorial q (t + a) / (qFactorial q t * qFactorial q a) := by
    apply (eq_div_iff (mul_ne_zero (hf t) (hf a))).mpr
    simpa only [mul_assoc] using hb
  simp only [gaussianCoeff, Nat.add_sub_cancel_left, hb']
  field_simp [hf]

end MixedNormalization
