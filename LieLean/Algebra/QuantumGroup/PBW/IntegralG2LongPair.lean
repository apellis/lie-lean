/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2ShortPair

/-!
# Integral straightening for long G₂ root pairs

The pairs `C,A` and `f,C` have a cubic correction in a short root. The apparent denominator
`[3]` in their degree-one relation cancels in divided powers. The resulting coefficients are
products of Laurent polynomials, including `[3j+1][3j+2]`.
-/

open Finset

noncomputable section

namespace LieLean.QuantumGroup.G2Integral

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- A divided-power identity for a cubic-weight correction. -/
lemma cubic_div_mul {t c : k} {x z y : B} (ht : t ≠ 0)
    (hti : ∀ n : ℕ, 0 < n → qInt t n ≠ 0)
    (hyx : y * x = t⁻¹ • (x * y) - c • z)
    (hyz : y * z = (t ^ 3)⁻¹ • (z * y)) (n : ℕ) :
    qDivPow t (n + 1) y * x = t⁻¹ ^ (n + 1) • (x * qDivPow t (n + 1) y) -
      (t⁻¹ ^ (2 * n) * c) • (z * qDivPow t n y) := by
  induction n with
  | zero => simpa [A2Integral.qDivPow_one', qDivPow_zero'] using hyx
  | succ n ih =>
    have hc : qInt t (n + 1 + 1) ≠ 0 := hti _ (by omega)
    have hc' : qInt t (n + 1) ≠ 0 := hti _ (by omega)
    refine smul_right_injective B hc ?_
    simp only
    rw [← smul_mul_assoc, ← mul_qDivPow t y (n + 1) hc, mul_assoc, ih, mul_sub,
      mul_smul_comm, mul_smul_comm, ← mul_assoc y x, hyx, ← mul_assoc y z, hyz]
    simp only [sub_mul, smul_mul_assoc, mul_assoc, mul_qDivPow t y (n + 1) hc,
      mul_qDivPow t y n hc', mul_smul_comm, smul_sub, smul_smul]
    rw [qInt_succ (v := t) (n + 1)]
    match_scalars
    all_goals (try simp only [inv_pow])
    all_goals (try field_simp)
    all_goals (try ring)

/-- Multiplication by a cube in divided-power coordinates. -/
lemma qDivPow_mul_cube (q : k) (z : B)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0) (n : ℕ) :
    qDivPow q n z * z ^ 3 =
      (qInt q (n + 1) * qInt q (n + 2) * qInt q (n + 3)) • qDivPow q (n + 3) z := by
  rw [pow_succ, pow_two, ← mul_assoc, ← mul_assoc,
    A2Integral.qDivPow_mul_self z n (hqi _ (by omega)), smul_mul_assoc,
    A2Integral.qDivPow_mul_self z (n + 1) (hqi _ (by omega)), smul_smul,
    smul_mul_assoc, A2Integral.qDivPow_mul_self z (n + 2) (hqi _ (by omega)), smul_smul]

/-- The Laurent factor at step `n` for the long-long pair. -/
def longStep (q : k) (s n : ℕ) : k :=
  ((q ^ 2 - 1) ^ 2 * q⁻¹ ^ 2) * (q ^ 3)⁻¹ ^ (2 * (s - 1 - n)) *
    qInt q (3 * n + 1) * qInt q (3 * n + 2)

def longCoeff (q : k) (s n : ℕ) : k := ∏ j ∈ range n, longStep q s j

def longW (q : k) (z y : B) (s n : ℕ) : B :=
  if n ≤ s then longCoeff q s n • (qDivPow q (3 * n) z * qDivPow (q ^ 3) (s - n) y)
  else 0

variable {q : k} {x z y : B}
  (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0)
  (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
  (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
  (hyx : y * x = (q ^ 3)⁻¹ • (x * y) -
    ((q ^ 2 - 1) ^ 2 / (q ^ 2 * qInt q 3)) • z ^ 3)
  (hzx : z * x = (q ^ 3)⁻¹ • (x * z))
  (hyz : y * z = (q ^ 3)⁻¹ • (z * y))

include hq hd hqi in
lemma longCoeff_step (n d : ℕ) :
    qInt (q ^ 3) (n + 1) * longCoeff q (n + 1 + d) (n + 1) =
      longCoeff q (n + 1 + d) n * (q ^ 3)⁻¹ ^ (2 * d) *
        ((q ^ 2 - 1) ^ 2 / (q ^ 2 * qInt q 3)) *
        (qInt q (3 * n + 1) * qInt q (3 * n + 2) * qInt q (3 * n + 3)) := by
  have h3 := hqi 3 (by omega)
  have hp := qInt_three_mul hd (n + 1)
  rw [show 3 * (n + 1) = 3 * n + 3 by omega] at hp
  simp only [longCoeff, prod_range_succ, longStep, show n + 1 + d - 1 - n = d by omega]
  rw [← hp]
  field_simp

include hq hd hqi hpi hyx hzx hyz in
lemma longW_mul (s n : ℕ) :
    longW q z y s n * x = ((q ^ 3)⁻¹ ^ s * (q ^ 3)⁻¹ ^ (2 * n)) •
      (x * longW q z y s n) - qInt (q ^ 3) (n + 1) • longW q z y s (n + 1) := by
  have hz (a : ℕ) : qDivPow q a z * x =
      (q ^ 3)⁻¹ ^ a • (x * qDivPow q a z) := by
    simpa only [A2Integral.qDivPow_one', mul_one] using
      B2Integral.qDivPow_mul_qDivPow_comm (u := q) (u' := q ^ 3) hzx a 1
  have hyz3 : y * z ^ 3 = ((q ^ 3) ^ 3)⁻¹ • (z ^ 3 * y) := by
    rw [show z ^ 3 = z * z * z by noncomm_ring]
    rw [← mul_assoc, ← mul_assoc, hyz, smul_mul_assoc, mul_assoc z y, hyz,
      mul_smul_comm, smul_smul, smul_mul_assoc, ← mul_assoc z z y, mul_assoc _ y, hyz,
      mul_smul_comm,
      smul_smul]
    simp only [mul_assoc]
    congr 1
    ring
  rcases Nat.lt_trichotomy n s with h | rfl | h
  · obtain ⟨d, rfl⟩ : ∃ d, s = n + 1 + d := ⟨s - n - 1, by omega⟩
    have hsn : n + 1 + d - n = d + 1 := by omega
    have hsn' : n + 1 + d - (n + 1) = d := by omega
    simp only [longW, show n ≤ n + 1 + d by omega, show n + 1 ≤ n + 1 + d by omega,
      ite_true, hsn, hsn', smul_mul_assoc, mul_assoc]
    rw [cubic_div_mul (pow_ne_zero _ hq) hpi hyx hyz3 d, mul_sub, mul_smul_comm,
      mul_smul_comm, ← mul_assoc _ x, hz, smul_mul_assoc, ← mul_assoc _ (z ^ 3),
      qDivPow_mul_cube q z hqi]
    simp only [smul_mul_assoc, smul_sub, smul_smul, mul_assoc, mul_smul_comm,
      show 3 * (n + 1) = 3 * n + 3 by omega]
    have hc := longCoeff_step hq hd hqi n d
    match_scalars
    · simp only [inv_pow]
      ring
    · linear_combination hc
  · simp only [longW, le_refl, ite_true, Nat.sub_self, qDivPow_zero', mul_one,
      show ¬ n + 1 ≤ n by omega, ite_false, smul_zero, sub_zero, smul_mul_assoc, hz,
      mul_smul_comm, smul_smul]
    congr 1
    simp only [inv_pow]
    ring
  · simp [longW, show ¬ n ≤ s by omega, show ¬ n + 1 ≤ s by omega]

lemma longW_zero (s : ℕ) : longW q z y s 0 = qDivPow (q ^ 3) s y := by
  simp [longW, longCoeff, qDivPow_zero']

include hq hd hqi hpi hyx hzx hyz in
/-- Arbitrary divided-power straightening for a long-long G₂ pair. -/
theorem qDivPow_long_pair (s r : ℕ) :
    qDivPow (q ^ 3) s y * qDivPow (q ^ 3) r x =
      ∑ n ∈ range (r + 1), B2Integral.sCoefParam (q ^ 3) ((q ^ 3)⁻¹ ^ s) r n •
        (qDivPow (q ^ 3) (r - n) x * longW q z y s n) := by
  simpa only [longW_zero] using B2Integral.straighten_param (pow_ne_zero _ hq) hpi
    ((q ^ 3)⁻¹ ^ s) (longW_mul hq hd hqi hpi hyx hzx hyz s) r

lemma longCoeff_mem (Λ : Subring k) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ) (s n : ℕ) :
    longCoeff q s n ∈ Λ := by
  apply Λ.prod_mem
  intro j _
  have hInv : (q ^ 3)⁻¹ ∈ Λ := by simpa only [inv_pow] using Λ.pow_mem hqiΛ 3
  exact Λ.mul_mem (Λ.mul_mem
    (Λ.mul_mem (Λ.mul_mem (Λ.pow_mem (Λ.sub_mem (Λ.pow_mem hqΛ 2) Λ.one_mem) 2)
      (Λ.pow_mem hqiΛ 2)) (Λ.pow_mem hInv _))
    (B2Integral.qInt_mem hqΛ hqiΛ _)) (B2Integral.qInt_mem hqΛ hqiΛ _)

/-- The full coefficient has no denominator outside the Laurent coefficient subring. -/
lemma long_pair_coeff_mem (Λ : Subring k) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ) (s r n : ℕ) :
    B2Integral.sCoefParam (q ^ 3) ((q ^ 3)⁻¹ ^ s) r n * longCoeff q s n ∈ Λ := by
  have hInv : (q ^ 3)⁻¹ ∈ Λ := by simpa only [inv_pow] using Λ.pow_mem hqiΛ 3
  exact Λ.mul_mem
    (Λ.mul_mem (Λ.mul_mem (Λ.pow_mem (Λ.neg_mem Λ.one_mem) _)
      (Λ.pow_mem (Λ.pow_mem hInv _) _)) (Λ.pow_mem hInv _))
    (longCoeff_mem Λ hqΛ hqiΛ s n)

variable {e A b C D f : B} (H : Rel q e A b C D f)

include hq hd hqi hpi H in
/-- The long pair `C,A` straightens through cubic divided powers of `B`. -/
theorem qDivPow_C_mul_qDivPow_A (s r : ℕ) :
    qDivPow (q ^ 3) s C * qDivPow (q ^ 3) r A =
      ∑ n ∈ range (r + 1), B2Integral.sCoefParam (q ^ 3) ((q ^ 3)⁻¹ ^ s) r n •
        (qDivPow (q ^ 3) (r - n) A * longW q b C s n) :=
  qDivPow_long_pair hq hd hqi hpi H.CA H.BA H.CB s r

include hq hd hqi hpi H in
/-- The long pair `f,C` straightens through cubic divided powers of `D`. -/
theorem qDivPow_f_mul_qDivPow_C (s r : ℕ) :
    qDivPow (q ^ 3) s f * qDivPow (q ^ 3) r C =
      ∑ n ∈ range (r + 1), B2Integral.sCoefParam (q ^ 3) ((q ^ 3)⁻¹ ^ s) r n •
        (qDivPow (q ^ 3) (r - n) C * longW q D f s n) :=
  qDivPow_long_pair hq hd hqi hpi H.fC H.DC H.fD s r

end LieLean.QuantumGroup.G2Integral
