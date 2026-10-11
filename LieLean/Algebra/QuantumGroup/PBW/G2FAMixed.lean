/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2Span

/-!
# A normalized mixed long-root G₂ product

The reconstructed identity `qDivPow_f_two_mul_qDivPow_A_two` checks the first product
with both mixed exponents greater than one. Its eight ordered coefficients are Laurent
polynomials, including the two cubic short-root corrections. The membership corollary
uses the existing six-root ordered span and supplies a normalization check for an
unrestricted mixed kernel. Arbitrary `f^{(s)} A^{(r)}` membership remains unproved.
-/

noncomputable section
namespace LieLean.QuantumGroup.G2Integral
open Finset
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]
variable {q : k} {e A b C D f : B}

private lemma fa_two_A (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) :
    qDivPow (q ^ 3) 2 f * A =
      q ^ 6 • (A * qDivPow (q ^ 3) 2 f) +
      (q ^ 4 + q ^ 2 - 1) • (C * f) -
      (q ^ 2 * (q ^ 2 - 1)) • (b * D * f) +
      (q * (q ^ 2 - 1) ^ 2 * qInt q 2) • qDivPow q 3 D := by
  have hh := qDivPow_f_mul_A hq (hqi 2 (by omega)) (hqi 3 (by omega)) hpi H 2
  rw [hh]
  simp only [Nat.reduceAdd, B2Integral.sCoef, mul_one, inv_pow, mul_assoc,
    reverseLongMixedAdjoint, sum_range_succ, range_one, sum_singleton, pow_zero, tsub_zero,
    zero_mul, inv_one, one_mul, pow_one, Nat.add_one_sub_one, neg_mul,
    A2Integral.qDivPow_one', sub_mul, Algebra.smul_mul_assoc, smul_sub, smul_smul,
    neg_smul, sub_neg_eq_add, even_two, Even.neg_pow, one_pow, tsub_self, mul_zero,
    qDivPow_zero', add_left_inj]
  match_scalars <;> field_simp

/-- The mixed long-root product at exponents `(2,2)`, derived from normalized relations. -/
theorem qDivPow_f_two_mul_qDivPow_A_two (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) :
    qDivPow (q ^ 3) 2 f * qDivPow (q ^ 3) 2 A =
      q ^ 12 • (qDivPow (q ^ 3) 2 A * qDivPow (q ^ 3) 2 f) +
      (q ^ 3 * (q ^ 4 + q ^ 2 - 1)) • (A * C * f) -
      (q ^ 5 * (q ^ 2 - 1)) • (A * b * D * f) +
      (q ^ 3 * (q ^ 2 - 1) ^ 2 * (q ^ 2 + 1)) •
        (A * qDivPow q 3 D + qDivPow q 3 b * f) +
      ((q ^ 2 - 1) ^ 2 * (q ^ 2 + 1)) • (qDivPow q 2 b * qDivPow q 2 D) -
      ((q ^ 2 - 1) * (q ^ 8 + q ^ 4 - 1) * q⁻¹ ^ 4) • (b * C * D) +
      ((q ^ 14 + q ^ 12 - q ^ 8 + q ^ 6 - q ^ 4 - q ^ 2 + 1) * q⁻¹ ^ 6) •
        qDivPow (q ^ 3) 2 C := by
  have h2 := hqi 2 (by omega)
  have h3 := hqi 3 (by omega)
  have hp2 := hpi 2 (by omega)
  have hD := qDivPow_D_mul_A hq hqi H 3
  have hA : qInt (q ^ 3) 2 • qDivPow (q ^ 3) 2 A = A * A := by
    rw [← mul_qDivPow (q ^ 3) A 1 hp2, A2Integral.qDivPow_one']
  apply smul_right_injective B hp2
  simp only
  rw [← mul_smul_comm, hA, ← mul_assoc, fa_two_A hq hqi hpi H]
  simp only [add_mul, sub_mul, smul_mul_assoc]
  rw [mul_assoc A (qDivPow (q ^ 3) 2 f) A, fa_two_A hq hqi hpi H,
    mul_assoc C f A, H.fA, mul_assoc (b * D) f A, H.fA, hD]
  simp only [mul_add, mul_sub, mul_smul_comm, smul_add, smul_sub, smul_smul]
  rw [← mul_assoc C A, H.CA, ← mul_assoc (b * D) A, mul_assoc b D A, H.DA]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul]
  rw [← mul_assoc b A, H.BA, mul_assoc b D C, H.DC,
    mul_assoc b D (b * D), ← mul_assoc D b D, H.DB]
  simp only [sum_range_succ, reverseSquareMixedAdjoint, B2Integral.sCoef,
    qDivPow, qFactorial, qInt, sum_range_succ]
  norm_num
  simp only [mul_sub, mul_add, add_mul, sub_mul, mul_smul_comm, smul_mul_assoc,
    smul_sub, smul_smul, pow_succ, pow_zero, mul_one, one_mul, mul_assoc]
  rw [← mul_assoc C b, H.CB]
  simp only [smul_mul_assoc, smul_smul, mul_assoc]
  have hn2 : 1 + q ^ 2 ≠ 0 := by
    intro hz
    apply h2
    rw [qInt_two]
    field_simp
    linear_combination hz
  have hn3 : 1 + q ^ 2 + q ^ 4 ≠ 0 := by
    intro hz
    apply h3
    rw [qInt_three hq]
    field_simp
    linear_combination hz
  have hnp2 : 1 + q ^ 6 ≠ 0 := by
    intro hz
    apply hp2
    rw [qInt_two]
    field_simp
    linear_combination hz
  have hn23 : 1 + q ^ 2 * 2 + q ^ 4 * 2 + q ^ 6 ≠ 0 := by
    convert mul_ne_zero hn2 hn3 using 1
    ring
  match_scalars <;> field_simp
  all_goals ring_nf
  all_goals field_simp [hn2, hn3, hnp2, hn23]
  all_goals ring

/-- All eight coefficients belong to the Laurent coefficient subring. -/
theorem qDivPow_f_two_mul_qDivPow_A_two_mem (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) (Λ : Subring k) (hqΛ : q ∈ Λ) (hiΛ : q⁻¹ ∈ Λ) :
    qDivPow (q ^ 3) 2 f * qDivPow (q ^ 3) 2 A ∈ orderedSpan q Λ e A b C D f := by
  have hm := M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b)
    (C := C) (D := D) (f := f)
  have hδ : q ^ 2 - 1 ∈ Λ := sub_mem (pow_mem hqΛ _) (one_mem _)
  have hα : q ^ 4 + q ^ 2 - 1 ∈ Λ :=
    sub_mem (add_mem (pow_mem hqΛ _) (pow_mem hqΛ _)) (one_mem _)
  have hplus : q ^ 2 + 1 ∈ Λ := add_mem (pow_mem hqΛ _) (one_mem _)
  rw [qDivPow_f_two_mul_qDivPow_A_two hq hqi hpi H]
  refine add_mem (sub_mem (add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · apply smul_mem_orderedSpan (pow_mem hqΛ 12)
    simpa [M6, M5, P3, qDivPow_zero'] using hm 0 2 0 0 0 2
  · apply smul_mem_orderedSpan (mul_mem (pow_mem hqΛ _) hα)
    simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using hm 0 1 0 1 0 1
  · apply smul_mem_orderedSpan (mul_mem (pow_mem hqΛ _) hδ)
    simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using hm 0 1 1 0 1 1
  · apply smul_mem_orderedSpan (mul_mem (mul_mem (pow_mem hqΛ _) (pow_mem hδ _)) hplus)
    apply add_mem
    · simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using hm 0 1 0 0 3 0
    · simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using hm 0 0 3 0 0 1
  · apply smul_mem_orderedSpan (mul_mem (pow_mem hδ _) hplus)
    simpa [M6, M5, P3, qDivPow_zero'] using hm 0 0 2 0 2 0
  · apply smul_mem_orderedSpan (mul_mem (mul_mem hδ
      (sub_mem (add_mem (pow_mem hqΛ _) (pow_mem hqΛ _)) (one_mem _))) (pow_mem hiΛ _))
    simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using hm 0 0 1 1 1 0
  · apply smul_mem_orderedSpan (mul_mem (add_mem (sub_mem (sub_mem (add_mem
      (sub_mem (add_mem (pow_mem hqΛ _) (pow_mem hqΛ _)) (pow_mem hqΛ _))
      (pow_mem hqΛ _)) (pow_mem hqΛ _)) (pow_mem hqΛ _)) (one_mem _)) (pow_mem hiΛ _))
    simpa [M6, M5, P3, qDivPow_zero'] using hm 0 0 0 2 0 0

end LieLean.QuantumGroup.G2Integral
