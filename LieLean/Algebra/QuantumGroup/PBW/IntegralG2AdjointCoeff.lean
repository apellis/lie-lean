/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2AdjointMonomial

/-!
# Coefficient recurrence for the finite G₂ adjoint family
-/

noncomputable section

namespace LieLean.QuantumGroup.G2Integral

variable {k : Type*} [Field k] {q : k}

lemma adjointCoeff_f_step (a b c d l : ℕ) :
    q ^ 3 * adjointCoeff q a b c d (l + 1) =
      adjointCoeff q a b c (d + 1) l * q ^ (3 * a + 2 * b + 3 * c) := by
  simp only [adjointCoeff, adjointExponent, pow_add, pow_mul, pow_one]
  ring

lemma adjointCoeff_D_step (hq : q ≠ 0) (a b c d l : ℕ) :
    q ^ (3 * l + 1) * q⁻¹ ^ (3 * c) * adjointCoeff q a b c (d + 1) l =
      adjointCoeff q a (b + 1) c d l * q ^ (3 * a + (b + 1)) *
        q⁻¹ ^ (3 * c + d + 1) := by
  simp only [adjointCoeff, adjointExponent, pow_add, pow_mul, mul_pow, pow_one]
  simp only [inv_pow]
  field_simp

lemma adjointCoeff_DC_step (hq : q ≠ 0) (a b c d l : ℕ) :
    -(q ^ (3 * l) * q⁻¹ ^ d * adjointCoeff q a b c (d + 2) l) =
      adjointCoeff q a b (c + 1) d l * q ^ (3 * a + 2 * b) * q⁻¹ ^ d := by
  simp only [adjointCoeff, adjointExponent, pow_add, pow_mul, mul_pow, pow_one]
  simp only [inv_pow]
  field_simp
  ring

lemma adjointCoeff_C_step (hq : q ≠ 0) (a b c d l : ℕ) :
    q ^ (3 * l + d) * q⁻¹ ^ (3 * c) * adjointCoeff q a b (c + 1) d l =
      -(adjointCoeff q a (b + 2) c d l * q ^ (3 * a) * q⁻¹ ^ (3 * c + d + 2)) := by
  simp only [adjointCoeff, adjointExponent, pow_add, pow_mul, mul_pow, pow_one]
  simp only [inv_pow]
  field_simp
  ring

lemma adjointCoeff_B_step (hq : q ≠ 0) (a b c d l : ℕ) :
    q ^ (3 * l + d) * q⁻¹ ^ (2 * b + 1) * adjointCoeff q a (b + 1) c d l =
      adjointCoeff q (a + 1) b c d l * q⁻¹ ^ (2 * b + 3 * c + d) := by
  simp only [adjointCoeff, adjointExponent, pow_add, pow_mul, mul_pow, pow_one]
  simp only [inv_pow]
  field_simp
  ring

/-- The coefficient recurrence, including every missing-predecessor boundary. -/
lemma adjointCoeff_recurrence (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0) (a b c d l : ℕ) :
    qInt q (3 * a + 2 * b + 3 * c + d) * adjointCoeff q a b c d l =
      (if d = 0 then 0 else
        q ^ 3 * adjointCoeff q a b c (d - 1) (l + 1) * qInt q d) +
      (if b = 0 then 0 else
        q ^ (3 * l + 1) * q⁻¹ ^ (3 * c) * adjointCoeff q a (b - 1) c (d + 1) l *
          qInt q 2 * qInt q b) +
      (if c = 0 then 0 else
        -(q ^ (3 * l) * q⁻¹ ^ d * adjointCoeff q a b (c - 1) (d + 2) l) *
          qInt q 3 * qInt (q ^ 3) c) +
      (if b ≤ 1 then 0 else
        (q ^ 2 - 1) * (q ^ (3 * l + d) * q⁻¹ ^ (3 * c) *
          adjointCoeff q a (b - 2) (c + 1) d l) * qInt q (b - 1) * qInt q b) +
      (if a = 0 then 0 else
        q ^ (3 * l + d) * q⁻¹ ^ (2 * b + 1) * adjointCoeff q (a - 1) (b + 1) c d l *
          qInt q 3 * qInt (q ^ 3) a) := by
  have hF : (if d = 0 then 0 else
      q ^ 3 * adjointCoeff q a b c (d - 1) (l + 1) * qInt q d) =
      adjointCoeff q a b c d l * q ^ (3 * a + 2 * b + 3 * c) * qInt q d := by
    cases d with
    | zero => simp [qInt]
    | succ d => simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
        adjointCoeff_f_step]
  have hD : (if b = 0 then 0 else
      q ^ (3 * l + 1) * q⁻¹ ^ (3 * c) * adjointCoeff q a (b - 1) c (d + 1) l *
        qInt q 2 * qInt q b) =
      adjointCoeff q a b c d l * q ^ (3 * a + b) * q⁻¹ ^ (3 * c + d + 1) *
        qInt q 2 * qInt q b := by
    cases b with
    | zero => simp [qInt]
    | succ b => simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
        adjointCoeff_D_step hq]
  have hDC : (if c = 0 then 0 else
      -(q ^ (3 * l) * q⁻¹ ^ d * adjointCoeff q a b (c - 1) (d + 2) l) *
        qInt q 3 * qInt (q ^ 3) c) =
      adjointCoeff q a b c d l * q ^ (3 * a + 2 * b) * q⁻¹ ^ d *
        qInt q 3 * qInt (q ^ 3) c := by
    cases c with
    | zero => simp [qInt]
    | succ c => simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
        adjointCoeff_DC_step hq]
  have hC : (if b ≤ 1 then 0 else
      (q ^ 2 - 1) * (q ^ (3 * l + d) * q⁻¹ ^ (3 * c) *
        adjointCoeff q a (b - 2) (c + 1) d l) * qInt q (b - 1) * qInt q b) =
      -(adjointCoeff q a b c d l * (q ^ 2 - 1) * q ^ (3 * a) *
        q⁻¹ ^ (3 * c + d + 2) * qInt q (b - 1) * qInt q b) := by
    rcases b with _ | (_ | b)
    · simp [qInt]
    · simp [qInt]
    · simp only [show b + 1 + 1 = b + 2 by omega, show ¬ b + 2 ≤ 1 by omega, ite_false,
        Nat.add_sub_cancel, show b + 2 - 1 = b + 1 by omega, adjointCoeff_C_step hq]
      ring
  have hB : (if a = 0 then 0 else
      q ^ (3 * l + d) * q⁻¹ ^ (2 * b + 1) * adjointCoeff q (a - 1) (b + 1) c d l *
        qInt q 3 * qInt (q ^ 3) a) =
      adjointCoeff q a b c d l * q⁻¹ ^ (2 * b + 3 * c + d) *
        qInt q 3 * qInt (q ^ 3) a := by
    cases a with
    | zero => simp [qInt]
    | succ a => simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
        adjointCoeff_B_step hq]
  rw [hF, hD, hDC, hC, hB]
  linear_combination adjointCoeff q a b c d l * adjoint_scalar hq hd a b c d

end LieLean.QuantumGroup.G2Integral
