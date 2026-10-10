/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2LongPair

/-!
# Scalar identities for the G₂ divided q-adjoint recurrence

The five incoming coefficients in the first-root adjoint recurrence sum to a quantum integer.
These scalar identities are independent of noncommutative straightening or summation bounds.
-/

noncomputable section

namespace LieLean.QuantumGroup.G2Integral

variable {k : Type*} [Field k] {q : k}

lemma qInt_double_decomp (hq : q ≠ 0) (b : ℕ) :
    qInt q (2 * b) = q ^ (b - 1) * qInt q 2 * qInt q b -
      (q ^ 2 - 1) * q⁻¹ ^ 2 * qInt q (b - 1) * qInt q b := by
  cases b with
  | zero => simp [qInt]
  | succ b =>
    have hh := qInt_mul_sub (v := q) b
    rw [show 2 * (b + 1) = (b + 1) + (b + 1) by omega, qInt_add]
    simp only [Nat.add_sub_cancel, qInt_two, pow_add, pow_one]
    linear_combination (norm := (field_simp; ring)) q⁻¹ * qInt q (b + 1) * hh

/-- The five incoming scalar coefficients for an ordered G₂ adjoint monomial. -/
lemma adjoint_scalar (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0) (a b c d : ℕ) :
    qInt q (3 * a + 2 * b + 3 * c + d) =
      q ^ (3 * a + 2 * b + 3 * c) * qInt q d +
      q ^ (3 * a + b) * q⁻¹ ^ (3 * c + d + 1) * qInt q 2 * qInt q b +
      q ^ (3 * a + 2 * b) * q⁻¹ ^ d * qInt q 3 * qInt (q ^ 3) c -
      (q ^ 2 - 1) * q ^ (3 * a) * q⁻¹ ^ (3 * c + d + 2) *
        qInt q (b - 1) * qInt q b +
      q⁻¹ ^ (2 * b + 3 * c + d) * qInt q 3 * qInt (q ^ 3) a := by
  have ha := qInt_three_mul hd a
  have hc := qInt_three_mul hd c
  have hb := qInt_double_decomp hq b
  rw [qInt_add]
  rw [show 3 * a + 2 * b + 3 * c = 3 * a + (2 * b + 3 * c) by omega]
  rw [qInt_add, qInt_add, ← ha, ← hc, hb]
  cases b with
  | zero => simp [qInt, pow_add]; ring
  | succ b =>
    simp only [Nat.add_sub_cancel, pow_add, pow_one]
    field_simp
    ring

/-- Nonnegative exponent of the Laurent coefficient in the five-root adjoint family. -/
def adjointExponent (a b c d l : ℕ) : ℕ :=
  3 * a * c + 3 * a * d + 6 * a * l + 3 * a + b * d + 3 * b * l + 4 * b +
    3 * c * l + 6 * c + 3 * d

def adjointCoeff (q : k) (a b c d l : ℕ) : k :=
  (-1) ^ c * q ^ adjointExponent a b c d l

lemma adjointCoeff_mem (Λ : Subring k) (hqΛ : q ∈ Λ) (a b c d l : ℕ) :
    adjointCoeff q a b c d l ∈ Λ :=
  Λ.mul_mem (Λ.pow_mem (Λ.neg_mem Λ.one_mem) _) (Λ.pow_mem hqΛ _)

end LieLean.QuantumGroup.G2Integral
