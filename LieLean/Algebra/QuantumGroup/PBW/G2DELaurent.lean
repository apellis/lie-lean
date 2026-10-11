/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.G2DECancellation
import LieLean.Algebra.QuantumGroup.PBW.G2DERecurrence
/-!
# Laurent integrality of the G₂ D,e scalar recurrence

The polynomial evaluator agrees with `deScalar` at every index. Its membership
in every subring containing q and q⁻¹ does not require inverses of quantum
integers or of q² - 1 in that subring. Actual arbitrary divided-adjoint
coefficient identification and unrestricted D,e membership remain separate.
-/

open Polynomial Finset
noncomputable section
namespace LieLean.QuantumGroup.G2Integral
namespace DECancellation
open SquareCancellation
variable {k : Type*} [Field k] {q : k}

lemma qInt_gaussian_pos (hq : q ≠ 0) (n : ℕ) :
    qInt q n = q ^ (1 - (n : ℤ)) *
      (gaussian n).eval₂ (Int.castRingHom k) (q ^ 2) := by
  have h := qInt_gaussian (inv_ne_zero hq) n
  rw [A2Integral.qInt_inv', inv_zpow, ← zpow_neg] at h
  simpa only [neg_sub, inv_zpow, zpow_neg, inv_pow, inv_inv, zpow_ofNat] using h

/-- The Laurent exponent for the integral polynomial evaluator. -/
def weight (a b c : ℤ) : ℤ :=
  -2 * a ^ 2 - 2 * c ^ 2 - 2 * a * c - b * (b - 1) - 3 * b * (a + c)

/-- The division-free Laurent evaluator of the scalar polynomial. -/
def laurentScalar (q : k) (a b c : ℕ) : k :=
  (-1) ^ c * q ^ weight a b c *
    (scalarPolynomial a b c).eval₂ (Int.castRingHom k) (q ^ 2)

def scale (q : k) (a b c : ℕ) : k :=
  (-1) ^ c * q ^ (1 - (2 * (a : ℤ) + b + c) + weight a b c)

lemma normalize_a (hq : q ≠ 0) (a b c : ℕ) :
    (if a = 0 then 0 else q⁻¹ ^ (2 * b + 1) * qInt q 3 * qInt (q ^ 3) a *
      laurentScalar q (a - 1) (b + 1) c) =
    scale q a b c * (gaussian (3 * a)).eval₂ (Int.castRingHom k) (q ^ 2) *
      (scalarPolynomial (a - 1) (b + 1) c).eval₂ (Int.castRingHom k) (q ^ 2) := by
  rcases a with _ | a
  · simp [gaussian]
  · simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel]
    rw [show q⁻¹ ^ (2 * b + 1) * qInt q 3 * qInt (q ^ 3) (a + 1) =
      q⁻¹ ^ (2 * b + 1) * qInt q (3 * (a + 1)) by
        rw [mul_assoc, qInt_three_mul_all]]
    simp only [qInt_gaussian_pos hq, laurentScalar, scale]
    have hp : q⁻¹ ^ (2 * b + 1) * q ^ (1 - (3 * (a + 1) : ℕ) : ℤ) *
        q ^ weight a (b + 1) c =
        q ^ (1 - (2 * ((a + 1 : ℕ) : ℤ) + b + c) + weight (a + 1) b c) := by
      rw [← zpow_natCast q⁻¹, inv_zpow, ← zpow_neg]
      simp only [← zpow_add₀ hq]
      congr 1
      push_cast
      unfold weight
      ring
    push_cast at hp ⊢
    linear_combination (-1 : k) ^ c *
      (gaussian (3 * (a + 1))).eval₂ (Int.castRingHom k) (q ^ 2) *
      (scalarPolynomial a (b + 1) c).eval₂ (Int.castRingHom k) (q ^ 2) * hp

lemma normalize_btwo (hq : q ≠ 0) (a b c : ℕ) :
    (if b < 2 then 0 else (q ^ 2 - 1) * q⁻¹ ^ (3 * c) *
      qInt q (b - 1) * qInt q b * laurentScalar q a (b - 2) (c + 1)) =
    scale q a b c * (1 - q ^ 2) * (q ^ 2) ^ (3 * a) *
      (gaussian (b - 1)).eval₂ (Int.castRingHom k) (q ^ 2) *
      (gaussian b).eval₂ (Int.castRingHom k) (q ^ 2) *
      (scalarPolynomial a (b - 2) (c + 1)).eval₂ (Int.castRingHom k) (q ^ 2) := by
  rcases b with _ | _ | b
  · simp [gaussian]
  · simp [gaussian]
  · simp only [show ¬b + 1 + 1 < 2 by omega, ↓reduceIte,
      show b + 1 + 1 - 1 = b + 1 by omega, show b + 1 + 1 - 2 = b by omega]
    simp only [qInt_gaussian_pos hq, laurentScalar, scale, pow_succ (-1 : k) c]
    have hp : q⁻¹ ^ (3 * c) * q ^ (1 - (b + 1 : ℕ) : ℤ) *
        q ^ (1 - (b + 1 + 1 : ℕ) : ℤ) * q ^ weight a b (c + 1) =
        q ^ (1 - (2 * (a : ℤ) + (b + 1 + 1 : ℕ) + c) + weight a (b + 1 + 1) c) *
          (q ^ 2) ^ (3 * a) := by
      rw [← zpow_natCast q⁻¹, inv_zpow, ← zpow_neg,
        ← zpow_natCast (q ^ 2), ← zpow_natCast q 2, ← zpow_mul]
      simp only [← zpow_add₀ hq]
      congr 1
      push_cast
      unfold weight
      ring
    push_cast at hp ⊢
    linear_combination (-1 : k) ^ c * (1 - q ^ 2) *
      (gaussian (b + 1)).eval₂ (Int.castRingHom k) (q ^ 2) *
      (gaussian (b + 1 + 1)).eval₂ (Int.castRingHom k) (q ^ 2) *
      (scalarPolynomial a b (c + 1)).eval₂ (Int.castRingHom k) (q ^ 2) * hp

lemma normalize_bone (hq : q ≠ 0) (a b c : ℕ) :
    (if b = 0 then 0 else q ^ (a + 1) * q⁻¹ ^ (4 * c) * qInt q 2 * qInt q b *
      laurentScalar q a (b - 1) c) =
    scale q a b c * (q ^ 2) ^ (3 * a + b - 1) * (1 + q ^ 2) *
      (gaussian b).eval₂ (Int.castRingHom k) (q ^ 2) *
      (scalarPolynomial a (b - 1) c).eval₂ (Int.castRingHom k) (q ^ 2) := by
  rcases b with _ | b
  · simp [gaussian]
  · simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel]
    have hg : (gaussian 2).eval₂ (Int.castRingHom k) (q ^ 2) = 1 + q ^ 2 := by
      simp [gaussian, Finset.sum_range_succ]
    simp only [qInt_gaussian_pos hq, hg, laurentScalar, scale]
    have hp : q ^ (a + 1) * q⁻¹ ^ (4 * c) * q ^ (1 - (2 : ℕ) : ℤ) *
        q ^ (1 - (b + 1 : ℕ) : ℤ) * q ^ weight a b c =
        q ^ (1 - (2 * (a : ℤ) + (b + 1 : ℕ) + c) + weight a (b + 1) c) *
          (q ^ 2) ^ (3 * a + (b + 1) - 1) := by
      rw [show 3 * a + (b + 1) - 1 = 3 * a + b by omega,
        ← zpow_natCast q⁻¹, inv_zpow, ← zpow_neg,
        ← zpow_natCast q (a + 1), ← zpow_natCast (q ^ 2),
        ← zpow_natCast q 2, ← zpow_mul]
      simp only [← zpow_add₀ hq]
      congr 1
      push_cast
      unfold weight
      ring
    push_cast at hp ⊢
    linear_combination (-1 : k) ^ c * (1 + q ^ 2) *
      (gaussian (b + 1)).eval₂ (Int.castRingHom k) (q ^ 2) *
      (scalarPolynomial a b c).eval₂ (Int.castRingHom k) (q ^ 2) * hp

lemma normalize_c (hq : q ≠ 0) (a b c : ℕ) :
    -(if c = 0 then 0 else q ^ (2 * a + 2) * q⁻¹ ^ (2 * c) *
      qInt q 3 * qInt (q ^ 3) c * laurentScalar q a b (c - 1)) =
    scale q a b c * (q ^ 2) ^ (3 * a + 2 * b) *
      (gaussian (3 * c)).eval₂ (Int.castRingHom k) (q ^ 2) *
      (scalarPolynomial a b (c - 1)).eval₂ (Int.castRingHom k) (q ^ 2) := by
  rcases c with _ | c
  · simp [gaussian]
  · simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel]
    rw [show q ^ (2 * a + 2) * q⁻¹ ^ (2 * (c + 1)) * qInt q 3 *
      qInt (q ^ 3) (c + 1) = q ^ (2 * a + 2) * q⁻¹ ^ (2 * (c + 1)) *
      qInt q (3 * (c + 1)) by rw [mul_assoc _ (qInt q 3), qInt_three_mul_all]]
    simp only [qInt_gaussian_pos hq, laurentScalar, scale, pow_succ (-1 : k) c]
    have hp : q ^ (2 * a + 2) * q⁻¹ ^ (2 * (c + 1)) *
        q ^ (1 - (3 * (c + 1) : ℕ) : ℤ) * q ^ weight a b c =
        q ^ (1 - (2 * (a : ℤ) + b + (c + 1 : ℕ)) + weight a b (c + 1)) *
          (q ^ 2) ^ (3 * a + 2 * b) := by
      rw [← zpow_natCast q⁻¹, inv_zpow, ← zpow_neg,
        ← zpow_natCast q (2 * a + 2), ← zpow_natCast (q ^ 2),
        ← zpow_natCast q 2, ← zpow_mul]
      simp only [← zpow_add₀ hq]
      congr 1
      push_cast
      unfold weight
      ring
    push_cast at hp ⊢
    linear_combination -(-1 : k) ^ c *
      (gaussian (3 * (c + 1))).eval₂ (Int.castRingHom k) (q ^ 2) *
      (scalarPolynomial a b c).eval₂ (Int.castRingHom k) (q ^ 2) * hp

lemma laurentScalar_recurrence (hq : q ≠ 0) (a b c : ℕ) :
    qInt q (2 * a + b + c) * laurentScalar q a b c =
      (if a = 0 then 0 else q⁻¹ ^ (2 * b + 1) * qInt q 3 * qInt (q ^ 3) a *
        laurentScalar q (a - 1) (b + 1) c) +
      (if b < 2 then 0 else (q ^ 2 - 1) * q⁻¹ ^ (3 * c) *
        qInt q (b - 1) * qInt q b * laurentScalar q a (b - 2) (c + 1)) +
      (if b = 0 then 0 else q ^ (a + 1) * q⁻¹ ^ (4 * c) * qInt q 2 * qInt q b *
        laurentScalar q a (b - 1) c) -
      (if c = 0 then 0 else q ^ (2 * a + 2) * q⁻¹ ^ (2 * c) * qInt q 3 *
        qInt (q ^ 3) c * laurentScalar q a b (c - 1)) := by
  rw [sub_eq_add_neg, normalize_a hq, normalize_btwo hq, normalize_bone hq, normalize_c hq]
  have hr := congrArg (fun p : ℤ[X] ↦ p.eval₂ (Int.castRingHom k) (q ^ 2))
    (scalarPolynomial_recurrence a b c)
  simp only [eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one] at hr
  have hl : qInt q (2 * a + b + c) * laurentScalar q a b c =
      scale q a b c * (gaussian (2 * a + b + c)).eval₂ (Int.castRingHom k) (q ^ 2) *
        (scalarPolynomial a b c).eval₂ (Int.castRingHom k) (q ^ 2) := by
    simp only [qInt_gaussian_pos hq, laurentScalar, scale]
    have hp : q ^ (1 - (2 * a + b + c : ℕ) : ℤ) * q ^ weight a b c =
        q ^ (1 - (2 * (a : ℤ) + b + c) + weight a b c) := by
      rw [← zpow_add₀ hq]
      push_cast
      rfl
    linear_combination (-1 : k) ^ c *
      (gaussian (2 * a + b + c)).eval₂ (Int.castRingHom k) (q ^ 2) *
      (scalarPolynomial a b c).eval₂ (Int.castRingHom k) (q ^ 2) * hp
  rw [hl]
  linear_combination scale q a b c * hr

lemma laurentScalar_zero : laurentScalar q 0 0 0 = 1 := by
  simp [laurentScalar, scalarPolynomial_zero, weight]

/-- The field recurrence equals a Laurent-polynomial evaluator at every index. -/
theorem deScalar_eq_laurentScalar (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0) (a b c : ℕ) :
    deScalar q a b c = laurentScalar q a b c := by
  generalize hn : 2 * a + b + c = n
  induction n using Nat.strong_induction_on generalizing a b c with
  | h n ih =>
    by_cases hzero : n = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      have hc : c = 0 := by omega
      subst a; subst b; subst c
      rw [deScalar_zero, laurentScalar_zero]
    have hpos : 0 < 2 * a + b + c := by omega
    apply mul_left_cancel₀ (hqi _ hpos)
    rw [deScalar_recurrence hqi a b c hpos, laurentScalar_recurrence hq]
    congr 1
    · congr 1
      · congr 1
        · split_ifs with ha
          · rfl
          · rw [ih (2 * (a - 1) + (b + 1) + c) (by omega) (a - 1) (b + 1) c rfl]
        · split_ifs with hb
          · rfl
          · rw [ih (2 * a + (b - 2) + (c + 1)) (by omega) a (b - 2) (c + 1) rfl]
      · split_ifs with hb
        · rfl
        · rw [ih (2 * a + (b - 1) + c) (by omega) a (b - 1) c rfl]
    · split_ifs with hc
      · rfl
      · rw [ih (2 * a + b + (c - 1)) (by omega) a b (c - 1) rfl]

/-- The division-free evaluator lies in every coefficient subring containing q and q⁻¹. -/
lemma laurentScalar_mem (Λ : Subring k) (hqΛ : q ∈ Λ) (hiΛ : q⁻¹ ∈ Λ)
    (a b c : ℕ) : laurentScalar q a b c ∈ Λ := by
  exact Λ.mul_mem (Λ.mul_mem (Λ.pow_mem (Λ.neg_mem Λ.one_mem) c)
    (laurent_zpow_mem Λ hqΛ hiΛ _))
    (intPolynomial_eval_mem Λ (Λ.pow_mem hqΛ 2) _)

end DECancellation

variable {k : Type*} [Field k] {q : k}

/-- Uniform Laurent cancellation for the four-correction D,e scalar recurrence.
No quantum integer or q² - 1 is inverted inside the coefficient subring. This
statement concerns the scalar recurrence; its identification with actual divided-adjoint
coefficients and unrestricted D,e ordered-span membership are proved in `G2DEIntegral`. -/
theorem deScalar_mem (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (Λ : Subring k) (hqΛ : q ∈ Λ) (hiΛ : q⁻¹ ∈ Λ) (a b c : ℕ) :
    deScalar q a b c ∈ Λ := by
  rw [DECancellation.deScalar_eq_laurentScalar hq hqi]
  exact DECancellation.laurentScalar_mem Λ hqΛ hiΛ a b c

end LieLean.QuantumGroup.G2Integral
