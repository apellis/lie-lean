/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.G2SquareRecurrence
import LieLean.Algebra.QuantumGroup.PBW.G2SquareKernel
/-!
# Laurent specialization of the G₂ square polynomial

The polynomial quotient evaluated at `q⁻²` satisfies the normalized scalar recurrence.
Its Laurent integrality uses no division by quantum integers or by `q² - 1`.
-/

open Polynomial Finset
noncomputable section
namespace LieLean.QuantumGroup.G2Integral
open SquareCancellation
variable {k : Type*} [Field k] {q : k}

lemma qInt_gaussian (hq : q ≠ 0) (m : ℕ) :
    qInt q m = q ^ ((m : ℤ) - 1) *
      (gaussian m).eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ)) := by
  simp only [qInt, gaussian, eval₂_finsetSum, eval₂_pow, eval₂_X, mul_sum]
  apply sum_congr rfl
  intro i hi
  have hi : i < m := mem_range.mp hi
  rw [← zpow_natCast q (m - 1 - i), ← zpow_natCast q⁻¹ i, inv_zpow,
    ← zpow_neg, ← zpow_natCast (q ^ (-2 : ℤ)) i, ← zpow_mul, ← zpow_add₀ hq, ← zpow_add₀ hq]
  congr 1
  have hm : (m - 1 - i : ℕ) = (m : ℤ) - 1 - i := by omega
  rw [hm]
  ring

lemma qInt_three_mul_all (n : ℕ) : qInt q 3 * qInt (q ^ 3) n = qInt q (3 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qInt_succ (v := q ^ 3) n, mul_add, mul_left_comm, ih,
      show 3 * (n + 1) = 3 * n + 3 by omega, qInt_add, inv_pow, pow_mul]
    ring

/-- Laurent normalization of the integral Newton quotient. -/
def squareScalar (q : k) (n t : ℕ) : k :=
  (q ^ 2 - 1) ^ t * q ^ (3 * (n : ℤ) ^ 2 - 9 * n * t + 9 * t ^ 2 - 2 * t) *
    (squarePolynomial n t).eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ))

lemma squareScalar_eq_zero (n t : ℕ) (h : ¬ (t ≤ n ∧ n ≤ 3 * t)) :
    squareScalar q n t = 0 := by
  simp [squareScalar, squarePolynomial_eq_zero n t h]

lemma squareScalar_zero_zero : squareScalar q 0 0 = 1 := by
  simp [squareScalar, squarePolynomial_zero_zero]

lemma squareScalar_recurrence (hq : q ≠ 0) (n t : ℕ) (htn : t ≤ n)
    (hnt : n ≤ 3 * t + 2) :
    qInt q (n + 1) * squareScalar q (n + 1) (t + 1) =
      q ^ (-(2 * (3 * t + 2 - n : ℕ) + 1 : ℤ)) *
        (qInt q 3 * qInt (q ^ 3) (n - t)) * squareScalar q n (t + 1) +
      (q ^ 2 - 1) * q ^ (-3 * (t : ℤ)) * qInt q (3 * t + 1 - n) *
        qInt q (3 * t + 2 - n) * squareScalar q n t := by
  have hr := congrArg (fun p : ℤ[X] ↦ p.eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ)))
    (squarePolynomial_recurrence n t htn hnt)
  simp only [eval₂_mul, eval₂_add, eval₂_pow, eval₂_X] at hr
  have ha : ((n - t : ℕ) : ℤ) = (n : ℤ) - t := by omega
  have hb : ((3 * t + 2 - n : ℕ) : ℤ) = 3 * (t : ℤ) + 2 - n := by omega
  rw [qInt_three_mul_all]
  simp only [squareScalar, qInt_gaussian hq]
  have hfirst :
      q ^ (-(2 * (3 * t + 2 - n : ℕ) + 1 : ℤ)) *
          q ^ ((3 * (n - t : ℕ) : ℕ) - 1 : ℤ) *
          q ^ (3 * (n : ℤ) ^ 2 - 9 * n * (t + 1) + 9 * (t + 1) ^ 2 - 2 * (t + 1)) =
        q ^ ((n : ℤ) + (3 * (n + 1) ^ 2 - 9 * (n + 1) * (t + 1) +
          9 * (t + 1) ^ 2 - 2 * (t + 1))) * (q ^ (-2 : ℤ)) ^ n := by
    rw [← zpow_natCast (q ^ (-2 : ℤ)), ← zpow_mul]
    simp only [← zpow_add₀ hq]
    congr 1
    push_cast
    rw [ha, hb]
    ring
  have hleft : q ^ (n : ℤ) *
      q ^ (3 * ((n : ℤ) + 1) ^ 2 - 9 * (n + 1) * (t + 1) +
        9 * (t + 1) ^ 2 - 2 * (t + 1)) =
      q ^ ((n : ℤ) + (3 * (n + 1) ^ 2 - 9 * (n + 1) * (t + 1) +
        9 * (t + 1) ^ 2 - 2 * (t + 1))) := (zpow_add₀ hq _ _).symm
  by_cases he : n ≤ 3 * t
  · have hb' : ((3 * t + 1 - n : ℕ) : ℤ) = 3 * (t : ℤ) + 1 - n := by omega
    have hsecond :
        q ^ (-3 * (t : ℤ)) * q ^ ((3 * t + 1 - n : ℕ) - 1 : ℤ) *
          q ^ ((3 * t + 2 - n : ℕ) - 1 : ℤ) *
          q ^ (3 * (n : ℤ) ^ 2 - 9 * n * t + 9 * t ^ 2 - 2 * t) =
        q ^ ((n : ℤ) + (3 * (n + 1) ^ 2 - 9 * (n + 1) * (t + 1) +
          9 * (t + 1) ^ 2 - 2 * (t + 1))) * (q ^ (-2 : ℤ)) ^ (3 * t) := by
      rw [← zpow_natCast (q ^ (-2 : ℤ)), ← zpow_mul]
      simp only [← zpow_add₀ hq]
      congr 1
      push_cast
      rw [hb', hb]
      ring
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, pow_succ (q ^ 2 - 1) t]
    linear_combination
      (q ^ 2 - 1) ^ t * (q ^ 2 - 1) *
        q ^ ((n : ℤ) + (3 * (n + 1) ^ 2 - 9 * (n + 1) * (t + 1) +
          9 * (t + 1) ^ 2 - 2 * (t + 1))) * hr +
      (q ^ 2 - 1) ^ t * (q ^ 2 - 1) *
        (gaussian (n + 1)).eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ)) *
        (squarePolynomial (n + 1) (t + 1)).eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ)) * hleft -
      (q ^ 2 - 1) ^ t * (q ^ 2 - 1) *
        (gaussian (3 * (n - t))).eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ)) *
        (squarePolynomial n (t + 1)).eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ)) * hfirst -
      (q ^ 2 - 1) ^ t * (q ^ 2 - 1) *
        (gaussian (3 * t + 2 - n)).eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ)) *
        (gaussian (3 * t + 1 - n)).eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ)) *
        (squarePolynomial n t).eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ)) * hsecond
  · have hz := squarePolynomial_eq_zero n t (by omega)
    simp only [hz, eval₂_zero, mul_zero, add_zero] at hr ⊢
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    linear_combination
      (q ^ 2 - 1) ^ (t + 1) *
        q ^ ((n : ℤ) + (3 * (n + 1) ^ 2 - 9 * (n + 1) * (t + 1) +
          9 * (t + 1) ^ 2 - 2 * (t + 1))) * hr +
      (q ^ 2 - 1) ^ (t + 1) *
        (gaussian (n + 1)).eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ)) *
        (squarePolynomial (n + 1) (t + 1)).eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ)) * hleft -
      (q ^ 2 - 1) ^ (t + 1) *
        (gaussian (3 * (n - t))).eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ)) *
        (squarePolynomial n (t + 1)).eval₂ (Int.castRingHom k) (q ^ (-2 : ℤ)) * hfirst

lemma laurent_zpow_mem (Λ : Subring k) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ) (z : ℤ) :
    q ^ z ∈ Λ := by
  cases z with
  | ofNat n => simpa using Λ.pow_mem hqΛ n
  | negSucc n => simpa [zpow_negSucc, inv_pow] using Λ.pow_mem hqiΛ (n + 1)

lemma intPolynomial_eval_mem (Λ : Subring k) {x : k} (hx : x ∈ Λ) (p : ℤ[X]) :
    p.eval₂ (Int.castRingHom k) x ∈ Λ := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simpa only [eval₂_add] using Λ.add_mem hp hr
  | monomial n a =>
    simpa only [eval₂_monomial, Int.coe_castRingHom] using
      Λ.mul_mem (intCast_mem Λ a) (Λ.pow_mem hx n)

/-- The normalized polynomial formula is Laurent integral before sparse identification. -/
lemma squareScalar_mem (Λ : Subring k) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ) (n t : ℕ) :
    squareScalar q n t ∈ Λ := by
  exact Λ.mul_mem
    (Λ.mul_mem (Λ.pow_mem (Λ.sub_mem (Λ.pow_mem hqΛ 2) Λ.one_mem) t)
      (laurent_zpow_mem Λ hqΛ hqiΛ _))
    (intPolynomial_eval_mem Λ (laurent_zpow_mem Λ hqΛ hqiΛ _) _)

end LieLean.QuantumGroup.G2Integral
