/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.MixedNormalization.Normalization

/-!
# Mixed-root coefficient convolution

Normal ordering and the coefficient convolution, with Serre truncation.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994),
37.3.1–37.3.2 and the proof of 38.1.8 (printed pp. 293, 297–299).
The finite-cutoff argument uses the actual quantum group and original Verma modules.
No restricted braid isometry or PBW norm conclusion is asserted here.
-/

open LieLean
noncomputable section
namespace MixedNormalization
open QuantumGroup BraidDiagonal FiniteIntertwining
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- The ordinary-power root-string normal-order coefficient. -/
def normalCoeff (q Q : k) (m a : ℕ) : k :=
  qBinomial q m a * q⁻¹ ^ (a * (m - a)) * Q ^ (m - a)

lemma normalCoeff_zero (q Q : k) (m : ℕ) : normalCoeff q Q m 0 = Q ^ m := by
  simp [normalCoeff]

lemma normalCoeff_diag (q Q : k) (m : ℕ) : normalCoeff q Q m m = 1 := by
  simp [normalCoeff]

lemma normalCoeff_above (q Q : k) {m a : ℕ} (h : m < a) :
    normalCoeff q Q m a = 0 := by
  simp [normalCoeff, qBinomial_eq_zero_of_lt q h]

lemma normalCoeff_step {q : k} (hq : q ≠ 0) (Q : k) (m a : ℕ) (ha : a ≤ m) :
    normalCoeff q Q (m + 1) (a + 1) = normalCoeff q Q m a +
      (q⁻¹ ^ (2 * (a + 1)) * Q) * normalCoeff q Q m (a + 1) := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simp [normalCoeff_diag, normalCoeff_above q Q (Nat.lt_succ_self a)]
  · obtain ⟨b, hb⟩ : ∃ b, m = a + 1 + b := ⟨m - (a + 1), by omega⟩
    subst m
    simp only [normalCoeff, qBinomial_succ_succ,
      show a + 1 + b + 1 - (a + 1) = b + 1 by omega,
      show a + 1 + b - a = b + 1 by omega,
      show a + 1 + b - (a + 1) = b by omega, inv_pow]
    field_simp
    ring

/-- Reconstructed normal ordering in an arbitrary associative algebra. -/
theorem normal_order {q : k} (hq : q ≠ 0) (Q : k) (E x : B) (m : ℕ) :
    E ^ m * x = ∑ a ∈ Finset.range (m + 1), normalCoeff q Q m a •
      (X q⁻¹ Q⁻¹ E x a * E ^ (m - a)) := by
  induction m with
  | zero => simp [normalCoeff, X]
  | succ m ih =>
    have hterm (a : ℕ) (ha : a ≤ m) :
        E * (X q⁻¹ Q⁻¹ E x a * E ^ (m - a)) =
          X q⁻¹ Q⁻¹ E x (a + 1) * E ^ (m - a) +
          (q⁻¹ ^ (2 * a) * Q) • (X q⁻¹ Q⁻¹ E x a * E ^ (m + 1 - a)) := by
      rw [X_succ]
      simp only [BraidDiagonal.shift, inv_inv, sub_mul, smul_mul_assoc,
        mul_assoc, ← pow_succ', show m - a + 1 = m + 1 - a by omega]
      abel
    rw [pow_succ', mul_assoc, ih, Finset.mul_sum]
    simp only [mul_smul_comm]
    rw [Finset.sum_congr rfl (fun a ha ↦ congrArg (fun z ↦ normalCoeff q Q m a • z)
      (hterm a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))))]
    simp only [smul_add, smul_smul, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' _ (m + 1)]
    have hsecond :
        (∑ a ∈ Finset.range (m + 1),
          (normalCoeff q Q m a * (q⁻¹ ^ (2 * a) * Q)) •
            (X q⁻¹ Q⁻¹ E x a * E ^ (m + 1 - a))) =
        (∑ a ∈ Finset.range (m + 1),
          ((q⁻¹ ^ (2 * (a + 1)) * Q) * normalCoeff q Q m (a + 1)) •
            (X q⁻¹ Q⁻¹ E x (a + 1) * E ^ (m - a))) +
          Q ^ (m + 1) • (x * E ^ (m + 1)) := by
      have h := Finset.sum_range_succ'
        (fun a ↦ (normalCoeff q Q m a * (q⁻¹ ^ (2 * a) * Q)) •
          (X q⁻¹ Q⁻¹ E x a * E ^ (m + 1 - a))) (m + 1)
      rw [Finset.sum_range_succ, normalCoeff_above q Q (Nat.lt_succ_self m)] at h
      simp only [zero_mul, zero_smul, add_zero, normalCoeff_zero, mul_zero, pow_zero,
        one_mul, show X q⁻¹ Q⁻¹ E x 0 = x from rfl,
        Nat.sub_zero, ← pow_succ, Nat.add_sub_add_right] at h
      simpa only [mul_comm] using h
    rw [hsecond, ← add_assoc, ← Finset.sum_add_distrib]
    simp only [normalCoeff_zero, show X q⁻¹ Q⁻¹ E x 0 = x from rfl,
      Nat.sub_zero, Nat.add_sub_add_right]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    rw [← add_smul, normalCoeff_step hq Q m a
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))]

lemma triangle_add (a b : ℕ) :
    (∑ t ∈ Finset.range (a + b), t) =
      (∑ t ∈ Finset.range a, t) + (∑ t ∈ Finset.range b, t) + a * b := by
  rw [Finset.sum_range_add, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

lemma coeff_normalCoeff {q : k} (hq : q ≠ 0)
    (hf : ∀ n, qFactorial q n ≠ 0) (Q : k) (m a : ℕ) (ha : a ≤ m) :
    coeff q m * normalCoeff q Q m a = coeff q a * coeff q (m - a) * Q ^ (m - a) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hb := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (n := a + b) (j := a)
    (Nat.le_add_right a b)
  simp only [Nat.add_sub_cancel_left] at hb ⊢
  have hb' : qBinomial q (a + b) a =
      qFactorial q (a + b) / (qFactorial q a * qFactorial q b) := by
    apply (eq_div_iff (mul_ne_zero (hf a) (hf b))).mpr
    simpa only [mul_assoc] using hb
  simp only [normalCoeff, Nat.add_sub_cancel_left, hb', coeff_closed, triangle_add,
    pow_add, inv_pow]
  field_simp [hf]

/-- Exact convolution with the exponential coefficients, before Serre truncation. -/
theorem coefficient_convolution {q : k} (hq : q ≠ 0)
    (hf : ∀ n, qFactorial q n ≠ 0) (Q : k) (E x : B) (m : ℕ) :
    coeff q m • (E ^ m * x) = ∑ a ∈ Finset.range (m + 1),
      (coeff q a * coeff q (m - a) * Q ^ (m - a)) •
        (X q⁻¹ Q⁻¹ E x a * E ^ (m - a)) := by
  rw [normal_order hq Q E x m, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [smul_smul, coeff_normalCoeff hq hf Q m a
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))]

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]

/-- Unrestricted actual root-string convolution in the original quantum group. -/
theorem rankTwoXm_convolution (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    (i j : I) (m : ℕ) :
    coeff (v ^ D.d i) m • (E R v i ^ m * E R v j) =
      ∑ a ∈ Finset.range (m + 1),
        (coeff (v ^ D.d i) a * coeff (v ^ D.d i) (m - a) *
          (v ^ D.d i) ^ (negA D i j * (m - a))) •
            (rankTwoXm R v i j a * E R v i ^ (m - a)) := by
  simpa only [rankTwoXm, inv_pow, pow_mul] using
    coefficient_convolution (pow_ne_zero _ (NeZero.ne v))
      (fun n ↦ LusztigF.qFactorial_ne_zero_of_not_root (NeZero.ne v) hv i n)
      ((v ^ D.d i) ^ negA D i j) (E R v i) (E R v j) m

/-- Termination of the actual inverse-parameter string is the defining Serre relation. -/
lemma rankTwoXm_serre {i j : I} (hij : i ≠ j) :
    rankTwoXm R v i j (negA D i j + 1) = 0 := by
  have hq : (v ^ D.d i)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (NeZero.ne v))
  rw [rankTwoXm, X_eq_serreAux hq (pow_ne_zero _ hq)]
  rw [pow_succ', mul_inv_cancel₀ (mul_ne_zero hq (pow_ne_zero _ hq)), serreAux_one]
  simp only [qSerre, qBinomial_inv]
  simpa only [qSerre, one_sub_cartanMatrix_toNat hij] using
    (serre_E (R := R) (v := v) hij)

lemma rankTwoXm_above {i j : I} (hij : i ≠ j) (a : ℕ) (ha : negA D i j < a) :
    rankTwoXm R v i j a = 0 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  induction b with
  | zero => simpa using rankTwoXm_serre R v hij
  | succ b ih =>
    rw [← Nat.add_assoc, rankTwoXm_succ, ih (by omega)]
    simp

/-- The exact coefficient convolution, truncated only by the proved quantum Serre relation. -/
theorem rankTwoXm_convolution_truncated (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) (m : ℕ) :
    coeff (v ^ D.d i) m • (E R v i ^ m * E R v j) =
      ∑ a ∈ Finset.range (min (negA D i j) m + 1),
        (coeff (v ^ D.d i) a * coeff (v ^ D.d i) (m - a) *
          (v ^ D.d i) ^ (negA D i j * (m - a))) •
            (rankTwoXm R v i j a * E R v i ^ (m - a)) := by
  rw [rankTwoXm_convolution R v hv i j m]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro a ha hnot
  have ha' := Finset.mem_range.mp ha
  have hnot' : ¬a < min (negA D i j) m + 1 := by simpa using hnot
  rw [rankTwoXm_above R v hij a (by omega), zero_mul, smul_zero]

end MixedNormalization
