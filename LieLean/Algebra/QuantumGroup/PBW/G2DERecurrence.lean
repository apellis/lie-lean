/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.G2SquareTransports

/-!
# The four-term G₂ D,e adjoint recurrence

`deMonomial_e` specializes the ordered-tail recurrence to the four intervening roots.
`qDivPow_D_two_mul_qDivPow_e_two_mem` verifies the normalized pair at exponents `(2,2)`
with Laurent-integral coefficients. Both are derived from the normalized relations.

`deScalar` records a field-valued scalar recurrence. Its Laurent integrality and its
identification with arbitrary divided-adjoint coefficients are not proved here.
In particular, this module does not prove unrestricted D,e ordered-span membership.
-/

noncomputable section
namespace LieLean.QuantumGroup.G2Integral
open Finset
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]
variable {q : k} {e A b C D f : B}

/-- The ordered four-root tail needed for the `D,e` divided adjoint. -/
def deMonomial (q : k) (A b C D : B) (a b' c d : ℕ) : B :=
  P3 q A b C a b' c * qDivPow q d D

/-- Four corrections, with the quadratic `D` correction carrying the opposite sign. -/
theorem deMonomial_e (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) (a b' c d : ℕ) :
    deMonomial q A b C D a b' c d * e =
      (q ^ d * q⁻¹ ^ b' * (q ^ 3)⁻¹ ^ a) •
        (e * deMonomial q A b C D a b' c d) -
      (if b' = 0 then 0 else
        (q ^ d * q⁻¹ ^ (2 * (b' - 1) + 1) * qInt q 3 * qInt (q ^ 3) (a + 1)) •
          deMonomial q A b C D (a + 1) (b' - 1) c d) -
      (if c = 0 then 0 else
        (q ^ d * (q ^ 2 - 1) * (q ^ 3)⁻¹ ^ (c - 1) *
          qInt q (b' + 1) * qInt q (b' + 2)) •
          deMonomial q A b C D a (b' + 2) (c - 1) d) -
      (if d = 0 then 0 else
        (q * qInt q 2 * (q ^ 3)⁻¹ ^ c * qInt q (b' + 1)) •
          deMonomial q A b C D a (b' + 1) c (d - 1)) +
      (if d ≤ 1 then 0 else
        (q⁻¹ ^ (d - 2) * qInt q 3 * qInt (q ^ 3) (c + 1)) •
          deMonomial q A b C D a b' (c + 1) (d - 2)) := by
  simpa only [M5, deMonomial, pow_zero, one_mul, qDivPow_zero', mul_one,
    ite_true, sub_zero] using M5_e hq hqi hpi H a b' c d 0

/-- The normalized scalar recurrence after removing the `D`-exponent Laurent monomial.
This definition involves a field inverse; it does not assert coefficient integrality. -/
def deScalar (q : k) : ℕ → ℕ → ℕ → k
  | a, b, c =>
    if a = 0 ∧ b = 0 ∧ c = 0 then 1 else
      (qInt q (2 * a + b + c))⁻¹ *
        ((if a = 0 then 0 else
          q⁻¹ ^ (2 * b + 1) * qInt q 3 * qInt (q ^ 3) a *
            deScalar q (a - 1) (b + 1) c) +
        (if b < 2 then 0 else
          (q ^ 2 - 1) * q⁻¹ ^ (3 * c) * qInt q (b - 1) * qInt q b *
            deScalar q a (b - 2) (c + 1)) +
        (if b = 0 then 0 else
          q ^ (a + 1) * q⁻¹ ^ (4 * c) * qInt q 2 * qInt q b *
            deScalar q a (b - 1) c) -
        (if c = 0 then 0 else
          q ^ (2 * a + 2) * q⁻¹ ^ (2 * c) * qInt q 3 * qInt (q ^ 3) c *
            deScalar q a b (c - 1)))
termination_by a b c => 2 * a + b + c
decreasing_by all_goals omega

@[simp] lemma deScalar_zero : deScalar q 0 0 0 = 1 := by
  rw [deScalar]
  simp

lemma deScalar_recurrence (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (a b c : ℕ) (hn : 0 < 2 * a + b + c) :
    qInt q (2 * a + b + c) * deScalar q a b c =
      (if a = 0 then 0 else
        q⁻¹ ^ (2 * b + 1) * qInt q 3 * qInt (q ^ 3) a * deScalar q (a - 1) (b + 1) c) +
      (if b < 2 then 0 else
        (q ^ 2 - 1) * q⁻¹ ^ (3 * c) * qInt q (b - 1) * qInt q b *
          deScalar q a (b - 2) (c + 1)) +
      (if b = 0 then 0 else
        q ^ (a + 1) * q⁻¹ ^ (4 * c) * qInt q 2 * qInt q b * deScalar q a (b - 1) c) -
      (if c = 0 then 0 else
        q ^ (2 * a + 2) * q⁻¹ ^ (2 * c) * qInt q 3 * qInt (q ^ 3) c *
          deScalar q a b (c - 1)) := by
  rw [deScalar, ite_eq_right (by omega), ← mul_assoc, mul_inv_cancel₀ (hqi _ hn), one_mul]

/-- An explicit low-exponent check of the normalized mixed pair. -/
theorem qDivPow_D_two_mul_qDivPow_e_two (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0) (H : Rel q e A b C D f) :
    qDivPow q 2 D * qDivPow q 2 e =
      q ^ 4 • (qDivPow q 2 e * qDivPow q 2 D) -
      (q ^ 2 * qInt q 2) • (e * b * D) +
      (q * qInt q 3) • (e * C) +
      (q * qInt q 3) • (A * D) +
      (2 * q ^ 2 + 1 + q⁻¹ ^ 2) • qDivPow q 2 b := by
  have h2 := hqi 2 (by decide)
  have he : qInt q 2 • qDivPow q 2 e = e * e := by
    rw [← mul_qDivPow q e 1 h2, A2Integral.qDivPow_one']
  have hb : qInt q 2 • qDivPow q 2 b = b * b := by
    rw [← mul_qDivPow q b 1 h2, A2Integral.qDivPow_one']
  have hDe := Dd_e hq hqi H 0
  simp only [Nat.zero_add, A2Integral.qDivPow_one', qDivPow_zero', pow_zero,
    one_mul, mul_one] at hDe
  apply smul_right_injective B h2
  simp only
  rw [← mul_smul_comm, he]
  simp only [smul_add, smul_sub]
  rw [smul_comm (qInt q 2) (q ^ 4), ← smul_mul_assoc, he,
    smul_comm (qInt q 2) (2 * q ^ 2 + 1 + q⁻¹ ^ 2), hb]
  rw [← mul_assoc, hDe]
  simp only [add_mul, sub_mul, smul_mul_assoc]
  rw [mul_assoc e (qDivPow q 2 D) e, hDe,
    mul_assoc b D e, H.De, H.Ce]
  simp only [mul_add, mul_sub, mul_smul_comm, smul_add, smul_sub, smul_smul]
  rw [← mul_assoc b e D, H.Be]
  simp only [sub_mul, smul_mul_assoc, smul_sub, smul_smul, pow_two, mul_assoc]
  rw [qInt_two, qInt_three hq]
  match_scalars <;> field_simp <;> ring

/-- The `(s,r)=(2,2)` product has genuinely integral ordered coefficients. -/
theorem qDivPow_D_two_mul_qDivPow_e_two_mem (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0) (H : Rel q e A b C D f)
    (Λ : Subring k) (hqΛ : q ∈ Λ) (hiΛ : q⁻¹ ∈ Λ) :
    qDivPow q 2 D * qDivPow q 2 e ∈ orderedSpan q Λ e A b C D f := by
  have hm := M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b)
    (C := C) (D := D) (f := f)
  have h3 : q * qInt q 3 ∈ Λ := mul_mem hqΛ (B2Integral.qInt_mem hqΛ hiΛ _)
  rw [qDivPow_D_two_mul_qDivPow_e_two hq hqi H]
  refine add_mem (add_mem (add_mem (sub_mem ?_ ?_) ?_) ?_) ?_
  · apply smul_mem_orderedSpan (pow_mem hqΛ 4)
    simpa [M6, M5, P3, qDivPow_zero'] using hm 2 0 0 0 2 0
  · apply smul_mem_orderedSpan
      (mul_mem (pow_mem hqΛ 2) (B2Integral.qInt_mem hqΛ hiΛ _))
    simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one', mul_assoc] using
      hm 1 0 1 0 1 0
  · apply smul_mem_orderedSpan h3
    simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using hm 1 0 0 1 0 0
  · apply smul_mem_orderedSpan h3
    simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using hm 0 1 0 0 1 0
  · apply smul_mem_orderedSpan
      (add_mem (add_mem (mul_mem (by norm_num : (2 : k) ∈ Λ) (pow_mem hqΛ 2)) (one_mem Λ))
        (pow_mem hiΛ 2))
    simpa [M6, M5, P3, qDivPow_zero'] using hm 0 0 2 0 0 0

end LieLean.QuantumGroup.G2Integral
