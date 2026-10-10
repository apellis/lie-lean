/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2Divided

/-!
# G₂ straightening for two short root vectors

For `yx = q⁻¹xy - q⁻¹[3]z`, `zx = q⁻³xz`, `yz = q⁻³zy`, with `x,y` short and `z` long,
we prove divided-power straightening with Laurent coefficients. The only non-monomial factor
is `∏_{j=1}^n (q^{2j} + 1 + q^{-2j})`. This applies to the pairs `B,e` and `D,B` in the
normalized G₂ order.
-/

open Finset

noncomputable section

namespace LieLean.QuantumGroup.G2Integral

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- The Laurent factor `[3n]_q/[n]_q`, without division. -/
def tripleFactor (q : k) (n : ℕ) : k := q ^ (2 * n) + 1 + q⁻¹ ^ (2 * n)

lemma tripleFactor_mul_qInt {q : k} (hq : q ≠ 0) (n : ℕ) :
    tripleFactor q n * qInt q n = qInt q (3 * n) := by
  rw [show 3 * n = n + n + n by omega, qInt_add, qInt_add]
  have hcancel : q⁻¹ ^ n * q ^ n = 1 := by rw [← mul_pow, inv_mul_cancel₀ hq, one_pow]
  simp only [tripleFactor, two_mul, pow_add]
  linear_combination -(qInt q n) * hcancel

lemma qInt_three_mul {q : k} (hd : q - q⁻¹ ≠ 0) (n : ℕ) :
    qInt q 3 * qInt (q ^ 3) n = qInt q (3 * n) := by
  apply mul_left_cancel₀ hd
  rw [← mul_assoc, qInt_mul_sub, inv_pow, qInt_mul_sub, qInt_mul_sub]
  simp only [inv_pow, ← pow_mul, Nat.mul_comm]

/-- Product of the Laurent factors arising when short divided powers produce long ones. -/
def shortFactor (q : k) (n : ℕ) : k := ∏ j ∈ range n, tripleFactor q (j + 1)

lemma shortFactor_succ (q : k) (n : ℕ) :
    shortFactor q (n + 1) = shortFactor q n * tripleFactor q (n + 1) := prod_range_succ _ _

/-- Coefficient of `z^{(n)} y^{(s-n)}` in the q-adjoint family. -/
def shortCoeff (q : k) (s n : ℕ) : k :=
  q ^ (n * n) * q⁻¹ ^ (2 * s * n) * shortFactor q n

lemma shortCoeff_step {q : k} (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0) (n d : ℕ) :
    qInt q (n + 1) * shortCoeff q (n + 1 + d) (n + 1) =
      shortCoeff q (n + 1 + d) n * q⁻¹ ^ (2 * d + 1) * qInt q 3 *
        qInt (q ^ 3) (n + 1) := by
  have hf := tripleFactor_mul_qInt hq (n + 1)
  rw [← qInt_three_mul hd] at hf
  have hp : q ^ (2 * n + 1) * q⁻¹ ^ (2 * (n + 1 + d)) = q⁻¹ ^ (2 * d + 1) := by
    rw [show 2 * (n + 1 + d) = (2 * n + 1) + (2 * d + 1) by omega, pow_add q⁻¹,
      ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq, one_pow, one_mul]
  have hc : shortCoeff q (n + 1 + d) (n + 1) =
      shortCoeff q (n + 1 + d) n * q⁻¹ ^ (2 * d + 1) * tripleFactor q (n + 1) := by
    simp only [shortCoeff, shortFactor_succ,
      show (n + 1) * (n + 1) = n * n + (2 * n + 1) by ring,
      show 2 * (n + 1 + d) * (n + 1) = 2 * (n + 1 + d) * n + 2 * (n + 1 + d) by ring,
      pow_add]
    linear_combination q ^ (n * n) * q⁻¹ ^ (2 * (n + 1 + d) * n) *
      shortFactor q n * tripleFactor q (n + 1) * hp
  rw [hc]
  linear_combination shortCoeff q (n + 1 + d) n * q⁻¹ ^ (2 * d + 1) * hf

variable {q : k} {x z y : B}
  (hq : q ≠ 0) (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
  (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
  (hyx : y * x = q⁻¹ • (x * y) - (q⁻¹ * qInt q 3) • z)
  (hzx : z * x = (q ^ 3)⁻¹ • (x * z))
  (hyz : y * z = (q ^ 3)⁻¹ • (z * y))

include hq hqi hyx hyz in
lemma short_div_mul (n : ℕ) : qDivPow q (n + 1) y * x =
    q⁻¹ ^ (n + 1) • (x * qDivPow q (n + 1) y) -
      (q⁻¹ ^ (2 * n + 1) * qInt q 3) • (z * qDivPow q n y) := by
  induction n with
  | zero => simpa [A2Integral.qDivPow_one', qDivPow_zero'] using hyx
  | succ n ih =>
    have hc : qInt q (n + 1 + 1) ≠ 0 := hqi _ (by omega)
    have hc' : qInt q (n + 1) ≠ 0 := hqi _ (by omega)
    refine smul_right_injective B hc ?_
    simp only
    rw [← smul_mul_assoc, ← mul_qDivPow q y (n + 1) hc, mul_assoc, ih, mul_sub,
      mul_smul_comm, mul_smul_comm, ← mul_assoc y x, hyx, ← mul_assoc y z, hyz]
    simp only [sub_mul, smul_mul_assoc, mul_assoc, mul_qDivPow q y (n + 1) hc,
      mul_qDivPow q y n hc', mul_smul_comm, smul_sub, smul_smul]
    rw [qInt_succ (v := q) (n + 1)]
    match_scalars
    all_goals (try simp only [inv_pow])
    all_goals (try field_simp)
    all_goals (try ring)

/-- The finite q-adjoint family for the short pair. -/
def shortW (q : k) (z y : B) (s n : ℕ) : B :=
  if n ≤ s then shortCoeff q s n • (qDivPow (q ^ 3) n z * qDivPow q (s - n) y) else 0

lemma shortW_zero (s : ℕ) : shortW q z y s 0 = qDivPow q s y := by
  simp [shortW, shortCoeff, shortFactor, qDivPow_zero']

include hq hqi hpi hyx hzx hyz in
lemma shortW_mul (hd : q - q⁻¹ ≠ 0) (s n : ℕ) :
    shortW q z y s n * x = (q⁻¹ ^ s * q⁻¹ ^ (2 * n)) • (x * shortW q z y s n) -
      qInt q (n + 1) • shortW q z y s (n + 1) := by
  have hz (a : ℕ) : qDivPow (q ^ 3) a z * x =
      (q ^ 3)⁻¹ ^ a • (x * qDivPow (q ^ 3) a z) := by
    simpa only [A2Integral.qDivPow_one', mul_one] using
      B2Integral.qDivPow_mul_qDivPow_comm (u := q ^ 3) (u' := q) hzx a 1
  rcases Nat.lt_trichotomy n s with h | rfl | h
  · obtain ⟨d, rfl⟩ : ∃ d, s = n + 1 + d := ⟨s - n - 1, by omega⟩
    have hsn : n + 1 + d - n = d + 1 := by omega
    have hsn' : n + 1 + d - (n + 1) = d := by omega
    simp only [shortW, show n ≤ n + 1 + d by omega, show n + 1 ≤ n + 1 + d by omega,
      ite_true, hsn, hsn', smul_mul_assoc, mul_assoc]
    rw [short_div_mul hq hqi hyx hyz d, mul_sub, mul_smul_comm, mul_smul_comm,
      ← mul_assoc _ x, hz, smul_mul_assoc, ← mul_assoc _ z,
      A2Integral.qDivPow_mul_self z n (hpi _ (by omega))]
    simp only [smul_mul_assoc, smul_sub, smul_smul, mul_assoc, mul_smul_comm]
    have hc := shortCoeff_step hq hd n d
    match_scalars
    · simp only [inv_pow]
      ring
    · linear_combination hc
  · simp only [shortW, le_refl, ite_true, Nat.sub_self, qDivPow_zero', mul_one,
      show ¬ n + 1 ≤ n by omega, ite_false, smul_zero, sub_zero, smul_mul_assoc, hz,
      mul_smul_comm, smul_smul]
    congr 1
    simp only [inv_pow]
    ring
  · simp [shortW, show ¬ n ≤ s by omega, show ¬ n + 1 ≤ s by omega]

include hq hqi hpi hyx hzx hyz in
/-- Divided-power straightening for a short-short pair with a long middle root. -/
theorem qDivPow_short_pair (hd : q - q⁻¹ ≠ 0) (s r : ℕ) :
    qDivPow q s y * qDivPow q r x =
      ∑ n ∈ range (r + 1), B2Integral.sCoefParam q (q⁻¹ ^ s) r n •
        (qDivPow q (r - n) x * shortW q z y s n) := by
  simpa only [shortW_zero] using B2Integral.straighten_param hq hqi (q⁻¹ ^ s)
    (shortW_mul hq hqi hpi hyx hzx hyz hd s) r

/-- Every factor of the short-pair formula is Laurent integral. -/
lemma tripleFactor_mem (Λ : Subring k) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ) (n : ℕ) :
    tripleFactor q n ∈ Λ :=
  Λ.add_mem (Λ.add_mem (Λ.pow_mem hqΛ _) Λ.one_mem) (Λ.pow_mem hqiΛ _)

lemma shortFactor_mem (Λ : Subring k) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ) (n : ℕ) :
    shortFactor q n ∈ Λ := by
  exact Λ.prod_mem fun j _ ↦ tripleFactor_mem Λ hqΛ hqiΛ (j + 1)

lemma shortCoeff_mem (Λ : Subring k) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ) (s n : ℕ) :
    shortCoeff q s n ∈ Λ :=
  Λ.mul_mem (Λ.mul_mem (Λ.pow_mem hqΛ _) (Λ.pow_mem hqiΛ _))
    (shortFactor_mem Λ hqΛ hqiΛ n)

/-- The complete coefficient of each nonzero ordered term lies in every subring containing
`q` and `q⁻¹`; no quantum integer is inverted in this coefficient. -/
lemma short_pair_coeff_mem (Λ : Subring k) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ) (s r n : ℕ) :
    B2Integral.sCoefParam q (q⁻¹ ^ s) r n * shortCoeff q s n ∈ Λ := by
  exact Λ.mul_mem
    (Λ.mul_mem (Λ.mul_mem (Λ.pow_mem (Λ.neg_mem Λ.one_mem) _)
      (Λ.pow_mem (Λ.pow_mem hqiΛ _) _)) (Λ.pow_mem hqiΛ _))
    (shortCoeff_mem Λ hqΛ hqiΛ s n)

variable {e A b C D f : B} (H : Rel q e A b C D f)

include hq hqi hpi H in
/-- The divided-power pair `B,e` straightens through the long root `A`. -/
theorem qDivPow_b_mul_qDivPow_e (hd : q - q⁻¹ ≠ 0) (s r : ℕ) :
    qDivPow q s b * qDivPow q r e =
      ∑ n ∈ range (r + 1), B2Integral.sCoefParam q (q⁻¹ ^ s) r n •
        (qDivPow q (r - n) e * shortW q A b s n) :=
  qDivPow_short_pair hq hqi hpi H.Be H.Ae H.BA hd s r

include hq hqi hpi H in
/-- The divided-power pair `D,B` straightens through the long root `C`. -/
theorem qDivPow_D_mul_qDivPow_b (hd : q - q⁻¹ ≠ 0) (s r : ℕ) :
    qDivPow q s D * qDivPow q r b =
      ∑ n ∈ range (r + 1), B2Integral.sCoefParam q (q⁻¹ ^ s) r n •
        (qDivPow q (r - n) b * shortW q C D s n) :=
  qDivPow_short_pair hq hqi hpi H.DB H.CB H.DC hd s r

end LieLean.QuantumGroup.G2Integral
