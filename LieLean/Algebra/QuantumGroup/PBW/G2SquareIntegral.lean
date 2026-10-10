/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.G2SquareLaurent
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2Span
/-!
# Integral G₂ square straightening

The polynomial cancellation formula is identified with the actual normalized sparse
coefficients. This proves their Laurent integrality and the unrestricted ordered-span
membership of `C^(s) e^(r)` under the normalized G₂ relations.
-/

open Finset
noncomputable section
namespace LieLean.QuantumGroup.G2Integral
variable {k : Type*} [Field k] {q : k}

lemma squareStepTerm_apply (i : SquareIndex) (a b c : ℕ) :
    squareStepTerm q i (a, b, c) =
      (if a = 0 then 0 else if i = (a - 1, b + 1, c) then
        q⁻¹ ^ (2 * b + 1) * qInt q 3 * qInt (q ^ 3) a else 0) +
      (if b < 2 then 0 else if i = (a, b - 2, c + 1) then
        (q ^ 2 - 1) * (q ^ 3)⁻¹ ^ c * qInt q (b - 1) * qInt q b else 0) := by
  rcases i with ⟨u, v, w⟩
  simp only [squareStepTerm, Finsupp.add_apply]
  congr 1
  · split_ifs <;> simp_all [Finsupp.single_apply, Prod.mk.injEq]
    all_goals omega
  · split_ifs <;> simp_all only [Order.lt_two_iff, Finsupp.coe_zero, Pi.zero_apply,
      not_le, Prod.mk.injEq, Nat.right_eq_add, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, not_false_eq_true, inv_pow, Finsupp.single_apply, ite_eq_right_iff,
      mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', ne_eq, OfNat.ofNat_ne_zero,
      and_imp, add_tsub_cancel_right, and_true, true_and, not_and]
    all_goals first | omega |
      (rw [ite_eq_left (by omega : b - 2 + 2 = b), show b - 2 + 1 = b - 1 by omega])

lemma squareStep_apply (F : SquareIndex →₀ k) (a b c : ℕ) :
    squareStep q F (a, b, c) =
      (if a = 0 then 0 else
        F (a - 1, b + 1, c) * (q⁻¹ ^ (2 * b + 1) * qInt q 3 * qInt (q ^ 3) a)) +
      (if b < 2 then 0 else
        F (a, b - 2, c + 1) *
          ((q ^ 2 - 1) * (q ^ 3)⁻¹ ^ c * qInt q (b - 1) * qInt q b)) := by
  classical
  simp only [squareStep, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, squareStepTerm_apply,
    mul_add, sum_add_distrib]
  congr 1
  · split_ifs with ha
    · simp
    · simp only [mul_ite, mul_zero, sum_ite_eq']
      split_ifs with hs
      · rfl
      · rw [Finsupp.notMem_support_iff.mp hs, zero_mul]
  · split_ifs with hb
    · simp
    · simp only [mul_ite, mul_zero, sum_ite_eq']
      split_ifs with hs
      · rfl
      · rw [Finsupp.notMem_support_iff.mp hs, zero_mul]

lemma squareCoeff_recurrence (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (s n a b c : ℕ) :
    qInt q (n + 1) * squareCoeff q s (n + 1) (a, b, c) =
      (if a = 0 then 0 else
        squareCoeff q s n (a - 1, b + 1, c) *
          (q⁻¹ ^ (2 * b + 1) * qInt q 3 * qInt (q ^ 3) a)) +
      (if b < 2 then 0 else
        squareCoeff q s n (a, b - 2, c + 1) *
          ((q ^ 2 - 1) * (q ^ 3)⁻¹ ^ c * qInt q (b - 1) * qInt q b)) := by
  have hn := hqi (n + 1) (by omega)
  simp only [squareCoeff, squareNumerator, squareStep_apply, qFactorial_succ, mul_inv_rev]
  split_ifs <;> field_simp <;> ring

lemma squareCoeff_eq_zero_of_grade (s n : ℕ) (a b c : ℕ)
    (h : ¬ (3 * a + b = 2 * n ∧ a + b + 2 * c = 2 * s)) :
    squareCoeff q s n (a, b, c) = 0 := by
  have hz : squareNumerator q s n (a, b, c) = 0 := by
    by_contra hn
    exact h (squareNumerator_grade q s n (a, b, c) hn)
  simp [squareCoeff, hz]

/-- The integral Laurent expression is the actual normalized sparse coefficient. -/
theorem squareCoeff_eq_squareScalar (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (s n t : ℕ) (hts : t ≤ s) (htn : t ≤ n) (hnt : n ≤ 3 * t) :
    squareCoeff q s n (n - t, 3 * t - n, s - t) =
      q ^ (-3 * (s - t : ℕ) * (t : ℤ)) * squareScalar q n t := by
  induction n generalizing t with
  | zero =>
    have ht : t = 0 := by omega
    subst t
    simp [squareCoeff, squareNumerator, qFactorial, squareScalar_zero_zero]
  | succ n ih =>
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    have ha : n + 1 - (t + 1) = n - t := by omega
    have hb : 3 * (t + 1) - (n + 1) = 3 * t + 2 - n := by omega
    rw [ha, hb]
    apply mul_left_cancel₀ (hqi (n + 1) (by omega))
    rw [squareCoeff_recurrence hqi]
    have hfirst :
        (if n - t = 0 then 0 else
          squareCoeff q s n (n - t - 1, 3 * t + 2 - n + 1, s - (t + 1)) *
            (q⁻¹ ^ (2 * (3 * t + 2 - n) + 1) * qInt q 3 * qInt (q ^ 3) (n - t))) =
        q ^ (-3 * (s - (t + 1) : ℕ) * ((t : ℤ) + 1)) *
          (q ^ (-(2 * (3 * t + 2 - n : ℕ) + 1 : ℤ)) *
            (qInt q 3 * qInt (q ^ 3) (n - t)) * squareScalar q n (t + 1)) := by
      split_ifs with he
      · rw [squareScalar_eq_zero n (t + 1) (by omega)]
        ring
      · rw [show n - t - 1 = n - (t + 1) by omega,
          show 3 * t + 2 - n + 1 = 3 * (t + 1) - n by omega,
          ih (t + 1) hts (by omega) (by omega)]
        rw [← zpow_natCast q⁻¹ (2 * (3 * t + 2 - n) + 1), inv_zpow, ← zpow_neg]
        push_cast
        ring
    have hsecond :
        (if 3 * t + 2 - n < 2 then 0 else
          squareCoeff q s n (n - t, 3 * t + 2 - n - 2, s - (t + 1) + 1) *
            ((q ^ 2 - 1) * (q ^ 3)⁻¹ ^ (s - (t + 1)) *
              qInt q (3 * t + 2 - n - 1) * qInt q (3 * t + 2 - n))) =
        q ^ (-3 * (s - (t + 1) : ℕ) * ((t : ℤ) + 1)) *
          ((q ^ 2 - 1) * q ^ (-3 * (t : ℤ)) * qInt q (3 * t + 1 - n) *
            qInt q (3 * t + 2 - n) * squareScalar q n t) := by
      split_ifs with he
      · rw [squareScalar_eq_zero n t (by omega)]
        ring
      · rw [show 3 * t + 2 - n - 2 = 3 * t - n by omega,
          show s - (t + 1) + 1 = s - t by omega,
          show 3 * t + 2 - n - 1 = 3 * t + 1 - n by omega,
          ih t (by omega) (by omega) (by omega)]
        have hp : q ^ (-3 * (s - t : ℕ) * (t : ℤ)) * (q ^ 3)⁻¹ ^ (s - (t + 1)) =
            q ^ (-3 * (s - (t + 1) : ℕ) * ((t : ℤ) + 1)) * q ^ (-3 * (t : ℤ)) := by
          rw [← zpow_natCast (q ^ 3)⁻¹, inv_zpow, ← zpow_neg,
            ← zpow_natCast q 3, ← zpow_mul]
          simp only [← zpow_add₀ hq]
          congr 1
          have hc : ((s - t : ℕ) : ℤ) = (s - (t + 1) : ℕ) + 1 := by omega
          rw [hc]
          ring
        linear_combination
          (q ^ 2 - 1) * qInt q (3 * t + 1 - n) * qInt q (3 * t + 2 - n) *
            squareScalar q n t * hp
    rw [hfirst, hsecond]
    have hr := squareScalar_recurrence hq n t (by omega) (by omega)
    push_cast
    linear_combination -q ^ (-3 * (s - (t + 1) : ℕ) * ((t : ℤ) + 1)) * hr

/-- All normalized sparse square coefficients lie in every coefficient subring containing
`q` and `q⁻¹`. Quantum-integer inverses are used only in the ambient field. -/
theorem squareCoeff_mem (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (Λ : Subring k) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ) (s n : ℕ) (i : SquareIndex) :
    squareCoeff q s n i ∈ Λ := by
  rcases i with ⟨a, b, c⟩
  by_cases hg : 3 * a + b = 2 * n ∧ a + b + 2 * c = 2 * s
  · have hi : (a, b, c) = (n - (n - a), 3 * (n - a) - n, s - (n - a)) := by
      ext <;> dsimp <;> omega
    rw [hi, squareCoeff_eq_squareScalar hq hqi s n (n - a) (by omega) (by omega) (by omega)]
    exact Λ.mul_mem (laurent_zpow_mem Λ hqΛ hqiΛ _) (squareScalar_mem Λ hqΛ hqiΛ _ _)
  · rw [squareCoeff_eq_zero_of_grade s n a b c hg]
    exact Λ.zero_mem

variable {B : Type*} [Ring B] [Algebra k B] {e A b C D f : B} {Λ : Subring k}

/-- Arbitrary divided powers of `C` and `e` straighten into the ordered integral span.
This uses the polynomial cancellation of the collected coefficients, not closure of the span. -/
theorem qDivPow_C_mul_qDivPow_e_mem (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ) (s r : ℕ) :
    qDivPow (q ^ 3) s C * qDivPow q r e ∈ orderedSpan q Λ e A b C D f := by
  rw [qDivPow_C_mul_qDivPow_e_field_sum hq hqi hpi H]
  refine AddSubgroup.sum_mem _ fun n _ ↦ AddSubgroup.sum_mem _ fun i _ ↦ ?_
  have hscoef : B2Integral.sCoefParam q 1 r n ∈ Λ := by
    simpa only [B2Integral.sCoefParam, one_pow, mul_one] using
      Λ.mul_mem (Λ.pow_mem (Λ.neg_mem Λ.one_mem) n) (Λ.pow_mem hqiΛ (n * (r - n)))
  apply smul_mem_orderedSpan
    (Λ.mul_mem hscoef (squareCoeff_mem hq hqi Λ hqΛ hqiΛ s n i))
  simpa [M6, M5, P3, qDivPow_zero', mul_assoc] using
    M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
      (D := D) (f := f) (r - n) i.1 i.2.1 i.2.2 0 0

end LieLean.QuantumGroup.G2Integral
