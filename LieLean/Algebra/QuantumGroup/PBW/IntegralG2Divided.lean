/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2Relations
import LieLean.Algebra.QuantumGroup.PBW.IntegralB2

/-!
# Divided-power commutation with the first G₂ root

Elementary divided-power consequences of the normalized G₂ relations. The three long-root
parameters are `q³`; the other three are `q`. These identities are the input for the iterated
q-adjoint recurrence underlying `f^{(s)} e^{(r)}` straightening.
-/

open Finset

noncomputable section

namespace LieLean.QuantumGroup.G2Integral

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]
  {q : k} {e A b C D f : B}
  (hq : q ≠ 0) (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
  (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0) (H : Rel q e A b C D f)

lemma SquareRel.Ad_ed (H : SquareRel q e A b C) (a r : ℕ) : qDivPow (q ^ 3) a A * qDivPow q r e =
    (q ^ 3)⁻¹ ^ (a * r) • (qDivPow q r e * qDivPow (q ^ 3) a A) :=
  B2Integral.qDivPow_mul_qDivPow_comm H.Ae a r

include H in
lemma Ad_ed (a r : ℕ) : qDivPow (q ^ 3) a A * qDivPow q r e =
    (q ^ 3)⁻¹ ^ (a * r) • (qDivPow q r e * qDivPow (q ^ 3) a A) :=
  SquareRel.Ad_ed H.squareRel a r

include H in
lemma bd_Ad (b' a : ℕ) : qDivPow q b' b * qDivPow (q ^ 3) a A =
    (q ^ 3)⁻¹ ^ (b' * a) • (qDivPow (q ^ 3) a A * qDivPow q b' b) :=
  B2Integral.qDivPow_mul_qDivPow_comm H.BA b' a

include H in
lemma Cd_bd (c b' : ℕ) : qDivPow (q ^ 3) c C * qDivPow q b' b =
    (q ^ 3)⁻¹ ^ (c * b') • (qDivPow q b' b * qDivPow (q ^ 3) c C) :=
  B2Integral.qDivPow_mul_qDivPow_comm H.CB c b'

include H in
lemma Dd_Cd (d c : ℕ) : qDivPow q d D * qDivPow (q ^ 3) c C =
    (q ^ 3)⁻¹ ^ (d * c) • (qDivPow (q ^ 3) c C * qDivPow q d D) :=
  B2Integral.qDivPow_mul_qDivPow_comm H.DC d c

include H in
lemma fd_Dd (s d : ℕ) : qDivPow (q ^ 3) s f * qDivPow q d D =
    (q ^ 3)⁻¹ ^ (s * d) • (qDivPow q d D * qDivPow (q ^ 3) s f) :=
  B2Integral.qDivPow_mul_qDivPow_comm H.fD s d

lemma SquareRel.Ad_e (H : SquareRel q e A b C) (a : ℕ) : qDivPow (q ^ 3) a A * e =
    (q ^ 3)⁻¹ ^ a • (e * qDivPow (q ^ 3) a A) := by
  simpa only [A2Integral.qDivPow_one', mul_one] using SquareRel.Ad_ed H a 1

include H in
lemma Ad_e (a : ℕ) : qDivPow (q ^ 3) a A * e =
    (q ^ 3)⁻¹ ^ a • (e * qDivPow (q ^ 3) a A) :=
  SquareRel.Ad_e H.squareRel a

include hq hqi in
lemma SquareRel.bd_e (H : SquareRel q e A b C) (n : ℕ) : qDivPow q (n + 1) b * e =
    q⁻¹ ^ (n + 1) • (e * qDivPow q (n + 1) b) -
      (q⁻¹ ^ (2 * n + 1) * qInt q 3) • (A * qDivPow q n b) := by
  induction n with
  | zero => simpa [A2Integral.qDivPow_one', qDivPow_zero'] using H.Be
  | succ n ih =>
    have hc : qInt q (n + 1 + 1) ≠ 0 := hqi _ (by omega)
    have hc' : qInt q (n + 1) ≠ 0 := hqi _ (by omega)
    refine smul_right_injective B hc ?_
    simp only
    rw [← smul_mul_assoc, ← mul_qDivPow q b (n + 1) hc, mul_assoc, ih, mul_sub,
      mul_smul_comm, mul_smul_comm, ← mul_assoc b e, H.Be, ← mul_assoc b A, H.BA]
    simp only [sub_mul, smul_mul_assoc, mul_assoc, mul_qDivPow q b (n + 1) hc,
      mul_qDivPow q b n hc', mul_smul_comm, smul_sub, smul_smul]
    rw [qInt_succ (v := q) (n + 1)]
    match_scalars
    all_goals (try simp only [inv_pow])
    all_goals (try field_simp)
    all_goals (try ring)

include hq hqi H in
lemma bd_e (n : ℕ) : qDivPow q (n + 1) b * e =
    q⁻¹ ^ (n + 1) • (e * qDivPow q (n + 1) b) -
      (q⁻¹ ^ (2 * n + 1) * qInt q 3) • (A * qDivPow q n b) :=
  SquareRel.bd_e hq hqi H.squareRel n

include hq hpi in
lemma SquareRel.Cd_e (H : SquareRel q e A b C) (n : ℕ) : qDivPow (q ^ 3) (n + 1) C * e =
    e * qDivPow (q ^ 3) (n + 1) C -
      ((q ^ 2 - 1) * (q ^ 3)⁻¹ ^ n) • (b ^ 2 * qDivPow (q ^ 3) n C) := by
  induction n with
  | zero => simpa [A2Integral.qDivPow_one', qDivPow_zero'] using H.Ce
  | succ n ih =>
    have hc : qInt (q ^ 3) (n + 1 + 1) ≠ 0 := hpi _ (by omega)
    have hc' : qInt (q ^ 3) (n + 1) ≠ 0 := hpi _ (by omega)
    have hCb : C * b ^ 2 = (q ^ 3)⁻¹ ^ 2 • (b ^ 2 * C) :=
      mul_pow_of_mul_eq_smul H.CB 2
    refine smul_right_injective B hc ?_
    simp only
    rw [← smul_mul_assoc, ← mul_qDivPow (q ^ 3) C (n + 1) hc, mul_assoc, ih, mul_sub,
      mul_smul_comm, ← mul_assoc C e, H.Ce, ← mul_assoc C, hCb]
    simp only [sub_mul, smul_mul_assoc, mul_assoc, mul_qDivPow (q ^ 3) C (n + 1) hc,
      mul_qDivPow (q ^ 3) C n hc', mul_smul_comm, smul_sub, smul_smul]
    rw [qInt_succ (v := q ^ 3) (n + 1)]
    match_scalars
    all_goals (try simp only [inv_pow])
    all_goals (try field_simp)
    all_goals (try ring)

include hq hpi H in
lemma Cd_e (n : ℕ) : qDivPow (q ^ 3) (n + 1) C * e =
    e * qDivPow (q ^ 3) (n + 1) C -
      ((q ^ 2 - 1) * (q ^ 3)⁻¹ ^ n) • (b ^ 2 * qDivPow (q ^ 3) n C) :=
  SquareRel.Cd_e hq hpi H.squareRel n

include hq hpi H in
lemma fd_e (n : ℕ) : qDivPow (q ^ 3) (n + 1) f * e =
    (q ^ 3) ^ (n + 1) • (e * qDivPow (q ^ 3) (n + 1) f) -
      q ^ 3 • (D * qDivPow (q ^ 3) n f) := by
  induction n with
  | zero => simpa [A2Integral.qDivPow_one', qDivPow_zero'] using H.fe
  | succ n ih =>
    have hc : qInt (q ^ 3) (n + 1 + 1) ≠ 0 := hpi _ (by omega)
    have hc' : qInt (q ^ 3) (n + 1) ≠ 0 := hpi _ (by omega)
    refine smul_right_injective B hc ?_
    simp only
    rw [← smul_mul_assoc, ← mul_qDivPow (q ^ 3) f (n + 1) hc, mul_assoc, ih, mul_sub,
      mul_smul_comm, mul_smul_comm, ← mul_assoc f e, H.fe, ← mul_assoc f D, H.fD]
    simp only [sub_mul, smul_mul_assoc, mul_assoc, mul_qDivPow (q ^ 3) f (n + 1) hc,
      mul_qDivPow (q ^ 3) f n hc', mul_smul_comm, smul_sub, smul_smul]
    rw [qInt_succ (v := q ^ 3) (n + 1)]
    match_scalars <;> (field_simp; ring)

include hq hqi H in
lemma Dd_e (n : ℕ) : qDivPow q (n + 2) D * e =
    q ^ (n + 2) • (e * qDivPow q (n + 2) D) -
      (q * qInt q 2) • (b * qDivPow q (n + 1) D) +
      (q⁻¹ ^ n * qInt q 3) • (C * qDivPow q n D) := by
  induction n with
  | zero =>
    have hc : qInt q 2 ≠ 0 := hqi 2 (by decide)
    have hDD : qInt q 2 • qDivPow q 2 D = D * D := by
      rw [← mul_qDivPow q D 1 hc, A2Integral.qDivPow_one']
    refine smul_right_injective B hc ?_
    simp only [Nat.zero_add, A2Integral.qDivPow_one', qDivPow_zero', pow_zero, one_mul,
      mul_one, smul_add, smul_sub]
    rw [← smul_mul_assoc, hDD,
      smul_comm (qInt q 2) (q ^ 2) (e * qDivPow q 2 D),
      ← mul_smul_comm (qInt q 2) e (qDivPow q 2 D), hDD]
    rw [mul_assoc, H.De, mul_sub, mul_smul_comm, mul_smul_comm, ← mul_assoc D e, H.De, H.DB]
    simp only [sub_mul, smul_mul_assoc, smul_sub, smul_smul, mul_assoc,
      qInt_two, qInt_three hq]
    match_scalars <;> (field_simp; try ring)
  | succ n ih =>
    have hc : qInt q (n + 2 + 1) ≠ 0 := hqi _ (by omega)
    have hc' : qInt q (n + 1 + 1) ≠ 0 := hqi _ (by omega)
    have hc'' : qInt q (n + 1) ≠ 0 := hqi _ (by omega)
    refine smul_right_injective B hc ?_
    simp only
    rw [show n + 1 + 2 = n + 2 + 1 by omega, ← smul_mul_assoc,
      ← mul_qDivPow q D (n + 2) hc, mul_assoc, ih, mul_add, mul_sub,
      mul_smul_comm, mul_smul_comm, mul_smul_comm, ← mul_assoc D e, H.De,
      ← mul_assoc D b, H.DB, ← mul_assoc D C, H.DC]
    simp only [sub_mul, smul_mul_assoc, mul_assoc, mul_qDivPow q D (n + 2) hc,
      mul_qDivPow q D (n + 1) hc', mul_qDivPow q D n hc'', mul_smul_comm,
      smul_add, smul_sub, smul_smul]
    rw [qInt_succ (v := q) (n + 2), qInt_succ (v := q) (n + 1), qInt_two]
    match_scalars
    all_goals (try simp only [inv_pow])
    all_goals (try field_simp)
    all_goals (try ring)

end LieLean.QuantumGroup.G2Integral
