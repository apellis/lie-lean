/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2Adjoint

/-!
# First-root multiplication of ordered G₂ monomials

The five correction terms of the divided q-adjoint recurrence, including the boundary cases
of zero exponents. This is an identity in the quantum Serre algebra, not an integral-span claim.
-/

noncomputable section

namespace LieLean.QuantumGroup.G2Integral

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- The first three factors in the five-root tail. -/
def P3 (q : k) (A b C : B) (a b' c : ℕ) : B :=
  qDivPow (q ^ 3) a A * qDivPow q b' b * qDivPow (q ^ 3) c C

/-- The five-root ordered tail. -/
def M5 (q : k) (A b C D f : B) (a b' c d l : ℕ) : B :=
  P3 q A b C a b' c * qDivPow q d D * qDivPow (q ^ 3) l f

variable {q : k} {e A b C D f : B}
  (hq : q ≠ 0) (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
  (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0) (H : Rel q e A b C D f)

include hqi H in
lemma P3_b (a b' c : ℕ) : P3 q A b C a b' c * b =
    ((q ^ 3)⁻¹ ^ c * qInt q (b' + 1)) • P3 q A b C a (b' + 1) c := by
  have hc : qDivPow (q ^ 3) c C * b = (q ^ 3)⁻¹ ^ c • (b * qDivPow (q ^ 3) c C) := by
    simpa only [A2Integral.qDivPow_one', mul_one] using Cd_bd H c 1
  rw [P3, mul_assoc _ _ b, hc, mul_smul_comm, ← mul_assoc, mul_assoc _ _ b,
    A2Integral.qDivPow_mul_self b b' (hqi _ (by omega)), mul_smul_comm, smul_mul_assoc,
    smul_smul]
  rfl

include hpi in
lemma P3_C (a b' c : ℕ) : P3 q A b C a b' c * C =
    qInt (q ^ 3) (c + 1) • P3 q A b C a b' (c + 1) := by
  rw [P3, mul_assoc, A2Integral.qDivPow_mul_self C c (hpi _ (by omega)), mul_smul_comm]
  rfl

include hq hqi hpi H in
lemma P3_e (a b' c : ℕ) : P3 q A b C a b' c * e =
    (q⁻¹ ^ b' * (q ^ 3)⁻¹ ^ a) • (e * P3 q A b C a b' c) -
      (if b' = 0 then 0 else
        (q⁻¹ ^ (2 * (b' - 1) + 1) * qInt q 3 * qInt (q ^ 3) (a + 1)) •
          P3 q A b C (a + 1) (b' - 1) c) -
      (if c = 0 then 0 else
        ((q ^ 2 - 1) * (q ^ 3)⁻¹ ^ (c - 1) * qInt q (b' + 1) * qInt q (b' + 2)) •
          P3 q A b C a (b' + 2) (c - 1)) := by
  have hAA := A2Integral.qDivPow_mul_self A a (hpi _ (by omega))
  have hbb : qDivPow q b' b * b ^ 2 =
      (qInt q (b' + 1) * qInt q (b' + 2)) • qDivPow q (b' + 2) b := by
    rw [pow_two, ← mul_assoc, A2Integral.qDivPow_mul_self b b' (hqi _ (by omega)),
      smul_mul_assoc, A2Integral.qDivPow_mul_self b (b' + 1) (hqi _ (by omega)), smul_smul]
  have hBe : qDivPow q b' b * e = q⁻¹ ^ b' • (e * qDivPow q b' b) -
      (if b' = 0 then 0 else (q⁻¹ ^ (2 * (b' - 1) + 1) * qInt q 3) •
        (A * qDivPow q (b' - 1) b)) := by
    cases b' with
    | zero => simp [qDivPow_zero']
    | succ n =>
      simpa only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] using bd_e hq hqi H n
  have hCe : qDivPow (q ^ 3) c C * e = e * qDivPow (q ^ 3) c C -
      (if c = 0 then 0 else ((q ^ 2 - 1) * (q ^ 3)⁻¹ ^ (c - 1)) •
        (b ^ 2 * qDivPow (q ^ 3) (c - 1) C)) := by
    cases c with
    | zero => simp [qDivPow_zero']
    | succ n =>
      simpa only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] using Cd_e hq hpi H n
  set P := qDivPow (q ^ 3) a A
  set Q := qDivPow q b' b
  set S := qDivPow (q ^ 3) c C
  have h1 : P * Q * S * e = P * (Q * e) * S - P * Q *
      (if c = 0 then 0 else ((q ^ 2 - 1) * (q ^ 3)⁻¹ ^ (c - 1)) •
        (b ^ 2 * qDivPow (q ^ 3) (c - 1) C)) := by
    rw [mul_assoc (P * Q) S e, hCe, mul_sub, ← mul_assoc (P * Q) e S, mul_assoc P Q e]
  have h2 : P * (Q * e) * S = (q⁻¹ ^ b' * (q ^ 3)⁻¹ ^ a) • (e * (P * Q * S)) -
      (if b' = 0 then 0 else
        (q⁻¹ ^ (2 * (b' - 1) + 1) * qInt q 3 * qInt (q ^ 3) (a + 1)) •
          P3 q A b C (a + 1) (b' - 1) c) := by
    rw [hBe, mul_sub, mul_smul_comm, sub_mul, smul_mul_assoc,
      ← mul_assoc P e, Ad_e H a, smul_mul_assoc, smul_mul_assoc, smul_smul]
    split_ifs
    · simp only [mul_zero, zero_mul, sub_zero, mul_assoc]
      rfl
    · rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc P A, hAA, smul_mul_assoc,
        smul_mul_assoc, smul_smul]
      simp only [P3, mul_assoc]
      rfl
  have h3 : P * Q *
      (if c = 0 then 0 else ((q ^ 2 - 1) * (q ^ 3)⁻¹ ^ (c - 1)) •
        (b ^ 2 * qDivPow (q ^ 3) (c - 1) C)) =
      if c = 0 then 0 else
        ((q ^ 2 - 1) * (q ^ 3)⁻¹ ^ (c - 1) * qInt q (b' + 1) * qInt q (b' + 2)) •
          P3 q A b C a (b' + 2) (c - 1) := by
    split_ifs
    · simp
    · rw [mul_smul_comm, ← mul_assoc, mul_assoc P Q, hbb, mul_smul_comm,
        smul_mul_assoc, smul_smul]
      simp only [P3, mul_assoc]
      rfl
  exact h1.trans (by rw [h2, h3]; rfl)

include hq hqi hpi H in
/-- The five-term correction formula for an arbitrary ordered tail monomial. -/
lemma M5_e (a b' c d l : ℕ) : M5 q A b C D f a b' c d l * e =
    ((q ^ 3) ^ l * q ^ d * q⁻¹ ^ b' * (q ^ 3)⁻¹ ^ a) •
      (e * M5 q A b C D f a b' c d l) -
      (if b' = 0 then 0 else
        ((q ^ 3) ^ l * q ^ d * q⁻¹ ^ (2 * (b' - 1) + 1) *
          qInt q 3 * qInt (q ^ 3) (a + 1)) • M5 q A b C D f (a + 1) (b' - 1) c d l) -
      (if c = 0 then 0 else
        ((q ^ 3) ^ l * q ^ d * (q ^ 2 - 1) * (q ^ 3)⁻¹ ^ (c - 1) *
          qInt q (b' + 1) * qInt q (b' + 2)) • M5 q A b C D f a (b' + 2) (c - 1) d l) -
      (if d = 0 then 0 else
        ((q ^ 3) ^ l * q * qInt q 2 * (q ^ 3)⁻¹ ^ c * qInt q (b' + 1)) •
          M5 q A b C D f a (b' + 1) c (d - 1) l) +
      (if d ≤ 1 then 0 else
        ((q ^ 3) ^ l * q⁻¹ ^ (d - 2) * qInt q 3 * qInt (q ^ 3) (c + 1)) •
          M5 q A b C D f a b' (c + 1) (d - 2) l) -
      (if l = 0 then 0 else (q ^ 3 * qInt q (d + 1)) •
        M5 q A b C D f a b' c (d + 1) (l - 1)) := by
  have hDD := A2Integral.qDivPow_mul_self D d (hqi _ (by omega))
  have hDe : qDivPow q d D * e = q ^ d • (e * qDivPow q d D) -
      (if d = 0 then 0 else (q * qInt q 2) • (b * qDivPow q (d - 1) D)) +
      (if d ≤ 1 then 0 else (q⁻¹ ^ (d - 2) * qInt q 3) •
        (C * qDivPow q (d - 2) D)) := by
    rcases d with _ | (_ | n)
    · simp [qDivPow_zero']
    · simpa [A2Integral.qDivPow_one', qDivPow_zero'] using H.De
    · simpa only [show n + 1 + 1 = n + 2 by omega, show ¬ n + 2 = 0 by omega,
        show ¬ n + 2 ≤ 1 by omega, ite_false,
        show n + 2 - 1 = n + 1 by omega, Nat.add_sub_cancel] using Dd_e hq hqi H n
  have hFe : qDivPow (q ^ 3) l f * e = (q ^ 3) ^ l • (e * qDivPow (q ^ 3) l f) -
      (if l = 0 then 0 else q ^ 3 • (D * qDivPow (q ^ 3) (l - 1) f)) := by
    cases l with
    | zero => simp [qDivPow_zero']
    | succ n =>
      simpa only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] using fd_e hq hpi H n
  set P := P3 q A b C a b' c
  set V := qDivPow q d D
  set F := qDivPow (q ^ 3) l f
  have hPb : P * b = ((q ^ 3)⁻¹ ^ c * qInt q (b' + 1)) •
      P3 q A b C a (b' + 1) c := P3_b hqi H a b' c
  have hPC : P * C = qInt (q ^ 3) (c + 1) •
      P3 q A b C a b' (c + 1) := P3_C hpi a b' c
  have h1 : P * V * F * e = (q ^ 3) ^ l • (P * (V * e) * F) -
      (if l = 0 then 0 else (q ^ 3 * qInt q (d + 1)) •
        M5 q A b C D f a b' c (d + 1) (l - 1)) := by
    rw [mul_assoc (P * V) F e, hFe, mul_sub, mul_smul_comm,
      ← mul_assoc (P * V) e F, mul_assoc P V e]
    split_ifs
    · simp
    · rw [mul_smul_comm, ← mul_assoc (P * V) D, mul_assoc P V D, hDD,
        mul_smul_comm, smul_mul_assoc, smul_smul]
      rfl
  have h2 : P * (V * e) * F = q ^ d • ((P * e) * V * F) -
      P * (if d = 0 then 0 else (q * qInt q 2) • (b * qDivPow q (d - 1) D)) * F +
      P * (if d ≤ 1 then 0 else (q⁻¹ ^ (d - 2) * qInt q 3) •
        (C * qDivPow q (d - 2) D)) * F := by
    rw [hDe, mul_add, mul_sub, add_mul, sub_mul, mul_smul_comm,
      smul_mul_assoc, ← mul_assoc P e]
  change P * V * F * e = _
  rw [h1, h2, P3_e hq hqi hpi H]
  split_ifs <;>
    simp only [M5, mul_zero, zero_mul, sub_zero, add_zero, mul_sub,
      sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_add, smul_smul,
      ← mul_assoc P b, ← mul_assoc P C, hPb, hPC]
  all_goals
    simp only [V, F, mul_assoc]

end LieLean.QuantumGroup.G2Integral
