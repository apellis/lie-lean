/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.G2DELaurent

/-!
# Unrestricted integral G₂ D,e straightening

The four correction transitions are evaluated in the actual normalized root vectors.
Their normalized coefficients are identified with `q^(d(a-c)) deScalar q a b c`
on the weights `n = 2a+b+c` and `s = a+b+2c+d`, and vanish off those weights.
This direct recurrence argument does not require PBW linear independence.

## Main results

* `deCoeff_eq_deScalar`: all-index coefficient identification, including natural boundaries.
* `deW_eq_sum`, `deW_mul`: finite ambient divided-adjoint expansion and its recurrence.
* `qDivPow_D_mul_qDivPow_e_mem`: arbitrary D^(s)e^(r) belongs to the ordered integral span.

The proofs are direct derivations from the normalized relations and scalar cancellation.
-/

open Finset
noncomputable section
namespace LieLean.QuantumGroup.G2Integral
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- Exponents of the four-root ordered tail. -/
abbrev DEIndex := ℕ × ℕ × ℕ × ℕ

/-- The four corrections in the right-e recurrence, before factorial normalization. -/
def deStepTerm (q : k) (i : DEIndex) : DEIndex →₀ k :=
  (if i.2.1 = 0 then 0 else
    Finsupp.single (i.1 + 1, i.2.1 - 1, i.2.2.1, i.2.2.2)
      (q ^ i.2.2.2 * q⁻¹ ^ (2 * (i.2.1 - 1) + 1) *
        qInt q 3 * qInt (q ^ 3) (i.1 + 1))) +
  (if i.2.2.1 = 0 then 0 else
    Finsupp.single (i.1, i.2.1 + 2, i.2.2.1 - 1, i.2.2.2)
      (q ^ i.2.2.2 * (q ^ 2 - 1) * (q ^ 3)⁻¹ ^ (i.2.2.1 - 1) *
        qInt q (i.2.1 + 1) * qInt q (i.2.1 + 2))) +
  (if i.2.2.2 = 0 then 0 else
    Finsupp.single (i.1, i.2.1 + 1, i.2.2.1, i.2.2.2 - 1)
      (q * qInt q 2 * (q ^ 3)⁻¹ ^ i.2.2.1 * qInt q (i.2.1 + 1))) -
  (if i.2.2.2 ≤ 1 then 0 else
    Finsupp.single (i.1, i.2.1, i.2.2.1 + 1, i.2.2.2 - 2)
      (q⁻¹ ^ (i.2.2.2 - 2) * qInt q 3 * qInt (q ^ 3) (i.2.2.1 + 1)))

/-- Linear extension of the four transitions. -/
def deStep (q : k) : (DEIndex →₀ k) →ₗ[k] (DEIndex →₀ k) :=
  Finsupp.linearCombination k (deStepTerm q)

/-- The actual factorial-cleared adjoint coefficients. -/
def deNumerator (q : k) (s : ℕ) : ℕ → DEIndex →₀ k
  | 0 => Finsupp.single (0, 0, 0, s) 1
  | n + 1 => deStep q (deNumerator q s n)

/-- Evaluation in the actual four normalized root vectors. -/
def deEval (q : k) (A b C D : B) : (DEIndex →₀ k) →ₗ[k] B :=
  Finsupp.linearCombination k (fun i ↦ deMonomial q A b C D i.1 i.2.1 i.2.2.1 i.2.2.2)

variable {q : k}

lemma deStepTerm_apply (i : DEIndex) (a b c d : ℕ) :
    deStepTerm q i (a, b, c, d) =
      (if a = 0 then 0 else if i = (a - 1, b + 1, c, d) then
        q ^ d * q⁻¹ ^ (2 * b + 1) * qInt q 3 * qInt (q ^ 3) a else 0) +
      (if b < 2 then 0 else if i = (a, b - 2, c + 1, d) then
        q ^ d * (q ^ 2 - 1) * (q ^ 3)⁻¹ ^ c * qInt q (b - 1) * qInt q b else 0) +
      (if b = 0 then 0 else if i = (a, b - 1, c, d + 1) then
        q * qInt q 2 * (q ^ 3)⁻¹ ^ c * qInt q b else 0) -
      (if c = 0 then 0 else if i = (a, b, c - 1, d + 2) then
        q⁻¹ ^ d * qInt q 3 * qInt (q ^ 3) c else 0) := by
  rcases i with ⟨u, v, w, z⟩
  simp only [deStepTerm, Finsupp.add_apply, Finsupp.sub_apply]
  congr 1
  · congr 1
    · congr 1
      · split_ifs <;> simp_all [Finsupp.single_apply, Prod.mk.injEq] <;> omega
      · split_ifs <;> simp_all only [Finsupp.coe_zero, Pi.zero_apply,
          Finsupp.single_apply, Prod.mk.injEq]
        all_goals
          (try split_ifs) <;> simp_all <;> try omega
        all_goals rw [show b - 2 + 1 = b - 1 by omega]; simp
    · split_ifs <;> simp_all [Finsupp.single_apply, Prod.mk.injEq] <;> omega
  · split_ifs <;> simp_all only [Finsupp.coe_zero, Pi.zero_apply,
      Finsupp.single_apply, Prod.mk.injEq]
    all_goals
      (try split_ifs) <;> simp_all <;> try omega

lemma deStep_apply (F : DEIndex →₀ k) (a b c d : ℕ) :
    deStep q F (a, b, c, d) =
      (if a = 0 then 0 else F (a - 1, b + 1, c, d) *
        (q ^ d * q⁻¹ ^ (2 * b + 1) * qInt q 3 * qInt (q ^ 3) a)) +
      (if b < 2 then 0 else F (a, b - 2, c + 1, d) *
        (q ^ d * (q ^ 2 - 1) * (q ^ 3)⁻¹ ^ c * qInt q (b - 1) * qInt q b)) +
      (if b = 0 then 0 else F (a, b - 1, c, d + 1) *
        (q * qInt q 2 * (q ^ 3)⁻¹ ^ c * qInt q b)) -
      (if c = 0 then 0 else F (a, b, c - 1, d + 2) *
        (q⁻¹ ^ d * qInt q 3 * qInt (q ^ 3) c)) := by
  classical
  simp only [deStep, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, deStepTerm_apply,
    mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  congr 1
  · congr 1
    · congr 1
      all_goals
        split_ifs
        · simp
        · simp only [mul_ite, mul_zero, sum_ite_eq']
          split_ifs with hs
          · rfl
          · rw [Finsupp.notMem_support_iff.mp hs, zero_mul]
    · split_ifs
      · simp
      · simp only [mul_ite, mul_zero, sum_ite_eq']
        split_ifs with hs
        · rfl
        · rw [Finsupp.notMem_support_iff.mp hs, zero_mul]
  · split_ifs
    · simp
    · simp only [mul_ite, mul_zero, sum_ite_eq']
      split_ifs with hs
      · rfl
      · rw [Finsupp.notMem_support_iff.mp hs, zero_mul]

lemma deNumerator_eq_zero_of_grade (s n a b c d : ℕ)
    (h : ¬ (2 * a + b + c = n ∧ a + b + 2 * c + d = s)) :
    deNumerator q s n (a, b, c, d) = 0 := by
  induction n generalizing a b c d with
  | zero =>
    simp only [deNumerator, Finsupp.single_apply]
    rw [ite_eq_right (by simp only [Prod.mk.injEq]; omega)]
  | succ n ih =>
    rw [deNumerator, deStep_apply]
    have h₁ : a ≠ 0 → deNumerator q s n (a - 1, b + 1, c, d) = 0 :=
      fun ha ↦ ih _ _ _ _ (by omega)
    have h₂ : ¬ b < 2 → deNumerator q s n (a, b - 2, c + 1, d) = 0 :=
      fun hb ↦ ih _ _ _ _ (by omega)
    have h₃ : b ≠ 0 → deNumerator q s n (a, b - 1, c, d + 1) = 0 :=
      fun hb ↦ ih _ _ _ _ (by omega)
    have h₄ : c ≠ 0 → deNumerator q s n (a, b, c - 1, d + 2) = 0 :=
      fun hc ↦ ih _ _ _ _ (by omega)
    split_ifs <;> simp_all

/-- The normalized sparse coefficient of the actual divided adjoint. -/
def deCoeff (q : k) (s n : ℕ) (i : DEIndex) : k :=
  (qFactorial q n)⁻¹ * deNumerator q s n i

lemma deCoeff_recurrence (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (s n a b c d : ℕ) :
    qInt q (n + 1) * deCoeff q s (n + 1) (a, b, c, d) =
      (if a = 0 then 0 else deCoeff q s n (a - 1, b + 1, c, d) *
        (q ^ d * q⁻¹ ^ (2 * b + 1) * qInt q 3 * qInt (q ^ 3) a)) +
      (if b < 2 then 0 else deCoeff q s n (a, b - 2, c + 1, d) *
        (q ^ d * (q ^ 2 - 1) * (q ^ 3)⁻¹ ^ c * qInt q (b - 1) * qInt q b)) +
      (if b = 0 then 0 else deCoeff q s n (a, b - 1, c, d + 1) *
        (q * qInt q 2 * (q ^ 3)⁻¹ ^ c * qInt q b)) -
      (if c = 0 then 0 else deCoeff q s n (a, b, c - 1, d + 2) *
        (q⁻¹ ^ d * qInt q 3 * qInt (q ^ 3) c)) := by
  have hn := hqi (n + 1) (by omega)
  simp only [deCoeff, deNumerator, deStep_apply, qFactorial_succ, mul_inv_rev]
  split_ifs <;> field_simp <;> ring

lemma deCoeff_eq_zero_of_grade (s n a b c d : ℕ)
    (h : ¬ (2 * a + b + c = n ∧ a + b + 2 * c + d = s)) :
    deCoeff q s n (a, b, c, d) = 0 := by
  simp [deCoeff, deNumerator_eq_zero_of_grade s n a b c d h]

/-- The Laurent monomial separating the final D exponent. -/
def deScale (q : k) (a c d : ℕ) : k := q ^ ((d : ℤ) * ((a : ℤ) - c))

lemma deScale_A (hq : q ≠ 0) (a b c d : ℕ) (ha : a ≠ 0) :
    deScale q (a - 1) c d * (q ^ d * q⁻¹ ^ (2 * b + 1)) =
      deScale q a c d * q⁻¹ ^ (2 * b + 1) := by
  unfold deScale
  have hp : q ^ ((d : ℤ) * ((a - 1 : ℕ) - c)) * q ^ d =
      q ^ ((d : ℤ) * ((a : ℤ) - c)) := by
    rw [← zpow_natCast q d, ← zpow_add₀ hq]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    push_cast
    ring
  rw [← mul_assoc, hp]

lemma deScale_BB (hq : q ≠ 0) (a c d : ℕ) :
    deScale q a (c + 1) d * (q ^ d * (q ^ 3)⁻¹ ^ c) =
      deScale q a c d * q⁻¹ ^ (3 * c) := by
  simp only [deScale, ← inv_pow, ← pow_mul]
  have hp : q ^ ((d : ℤ) * ((a : ℤ) - (c + 1 : ℕ))) * q ^ d =
      q ^ ((d : ℤ) * ((a : ℤ) - c)) := by
    rw [← zpow_natCast q d, ← zpow_add₀ hq]
    congr 1
    push_cast
    ring
  rw [← mul_assoc, hp]

lemma deScale_B (hq : q ≠ 0) (a c d : ℕ) :
    deScale q a c (d + 1) * (q * (q ^ 3)⁻¹ ^ c) =
      deScale q a c d * (q ^ (a + 1) * q⁻¹ ^ (4 * c)) := by
  rw [show q * (q ^ 3)⁻¹ ^ c = q ^ (1 : ℤ) * (q ^ 3)⁻¹ ^ c by rw [zpow_one]]
  simp only [deScale, ← zpow_natCast, inv_zpow, ← zpow_neg, ← zpow_mul]
  simp only [← zpow_add₀ hq]
  congr 1
  push_cast
  ring

lemma deScale_C (hq : q ≠ 0) (a c d : ℕ) (hc : c ≠ 0) :
    deScale q a (c - 1) (d + 2) * q⁻¹ ^ d =
      deScale q a c d * (q ^ (2 * a + 2) * q⁻¹ ^ (2 * c)) := by
  simp only [deScale, ← zpow_natCast, inv_zpow, ← zpow_neg]
  simp only [← zpow_add₀ hq]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ c)]
  push_cast
  ring

/-- Identification of every actual divided-adjoint coefficient on the two root weights. -/
theorem deCoeff_eq_deScalar (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (s n a b c d : ℕ) (hn : 2 * a + b + c = n) (hs : a + b + 2 * c + d = s) :
    deCoeff q s n (a, b, c, d) = deScale q a c d * deScalar q a b c := by
  induction n generalizing a b c d with
  | zero =>
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    have hc : c = 0 := by omega
    subst a; subst b; subst c
    have hd : d = s := by omega
    subst d
    simp [deCoeff, deNumerator, qFactorial, deScale]
  | succ n ih =>
    apply mul_left_cancel₀ (hqi (n + 1) (by omega))
    rw [deCoeff_recurrence hqi]
    have hr := deScalar_recurrence hqi a b c (by omega)
    rw [hn] at hr
    have h₁ :
        (if a = 0 then 0 else deCoeff q s n (a - 1, b + 1, c, d) *
          (q ^ d * q⁻¹ ^ (2 * b + 1) * qInt q 3 * qInt (q ^ 3) a)) =
        deScale q a c d * (if a = 0 then 0 else
          q⁻¹ ^ (2 * b + 1) * qInt q 3 * qInt (q ^ 3) a *
            deScalar q (a - 1) (b + 1) c) := by
      split_ifs with ha
      · ring
      · rw [ih _ _ _ _ (by omega) (by omega)]
        linear_combination
          deScalar q (a - 1) (b + 1) c * qInt q 3 * qInt (q ^ 3) a *
            deScale_A hq a b c d ha
    have h₂ :
        (if b < 2 then 0 else deCoeff q s n (a, b - 2, c + 1, d) *
          (q ^ d * (q ^ 2 - 1) * (q ^ 3)⁻¹ ^ c * qInt q (b - 1) * qInt q b)) =
        deScale q a c d * (if b < 2 then 0 else
          (q ^ 2 - 1) * q⁻¹ ^ (3 * c) * qInt q (b - 1) * qInt q b *
            deScalar q a (b - 2) (c + 1)) := by
      split_ifs with hb
      · ring
      · rw [ih _ _ _ _ (by omega) (by omega)]
        linear_combination
          (q ^ 2 - 1) * qInt q (b - 1) * qInt q b * deScalar q a (b - 2) (c + 1) *
            deScale_BB hq a c d
    have h₃ :
        (if b = 0 then 0 else deCoeff q s n (a, b - 1, c, d + 1) *
          (q * qInt q 2 * (q ^ 3)⁻¹ ^ c * qInt q b)) =
        deScale q a c d * (if b = 0 then 0 else
          q ^ (a + 1) * q⁻¹ ^ (4 * c) * qInt q 2 * qInt q b * deScalar q a (b - 1) c) := by
      split_ifs with hb
      · ring
      · rw [ih _ _ _ _ (by omega) (by omega)]
        linear_combination
          qInt q 2 * qInt q b * deScalar q a (b - 1) c * deScale_B hq a c d
    have h₄ :
        (if c = 0 then 0 else deCoeff q s n (a, b, c - 1, d + 2) *
          (q⁻¹ ^ d * qInt q 3 * qInt (q ^ 3) c)) =
        deScale q a c d * (if c = 0 then 0 else
          q ^ (2 * a + 2) * q⁻¹ ^ (2 * c) * qInt q 3 * qInt (q ^ 3) c *
            deScalar q a b (c - 1)) := by
      split_ifs with hc
      · ring
      · rw [ih _ _ _ _ (by omega) (by omega)]
        linear_combination
          qInt q 3 * qInt (q ^ 3) c * deScalar q a b (c - 1) * deScale_C hq a c d hc
    rw [h₁, h₂, h₃, h₄]
    linear_combination -deScale q a c d * hr

/-- Every normalized coefficient is integral in any Laurent coefficient subring. -/
theorem deCoeff_mem (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (Λ : Subring k) (hqΛ : q ∈ Λ) (hiΛ : q⁻¹ ∈ Λ) (s n : ℕ) (i : DEIndex) :
    deCoeff q s n i ∈ Λ := by
  rcases i with ⟨a, b, c, d⟩
  by_cases hg : 2 * a + b + c = n ∧ a + b + 2 * c + d = s
  · rw [deCoeff_eq_deScalar hq hqi s n a b c d hg.1 hg.2]
    exact Λ.mul_mem (laurent_zpow_mem Λ hqΛ hiΛ _) (deScalar_mem hq hqi Λ hqΛ hiΛ _ _ _)
  · rw [deCoeff_eq_zero_of_grade s n a b c d hg]
    exact Λ.zero_mem

lemma deNumerator_grade (s n : ℕ) (i : DEIndex) (hi : deNumerator q s n i ≠ 0) :
    2 * i.1 + i.2.1 + i.2.2.1 = n ∧ i.1 + i.2.1 + 2 * i.2.2.1 + i.2.2.2 = s := by
  by_contra hn
  exact hi (deNumerator_eq_zero_of_grade s n i.1 i.2.1 i.2.2.1 i.2.2.2 hn)

variable {e A b C D f : B}

lemma deStepTerm_eval (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) (i : DEIndex) :
    deEval q A b C D (deStepTerm q i) =
      (q ^ i.2.2.2 * q⁻¹ ^ i.2.1 * (q ^ 3)⁻¹ ^ i.1) •
        (e * deMonomial q A b C D i.1 i.2.1 i.2.2.1 i.2.2.2) -
      deMonomial q A b C D i.1 i.2.1 i.2.2.1 i.2.2.2 * e := by
  have hm := deMonomial_e hq hqi hpi H i.1 i.2.1 i.2.2.1 i.2.2.2
  simp only [deStepTerm, map_add, map_sub, deEval]
  split_ifs <;> simp only [map_zero, Finsupp.linearCombination_single] <;>
    simp_all only [ite_true, ite_false] <;> abel

lemma deNumerator_eval_mul (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) (s n : ℕ) :
    deEval q A b C D (deNumerator q s n) * e =
      (q ^ s * q⁻¹ ^ (2 * n)) • (e * deEval q A b C D (deNumerator q s n)) -
        deEval q A b C D (deNumerator q s (n + 1)) := by
  classical
  have ht (i : DEIndex) (hi : i ∈ (deNumerator q s n).support) :
      deEval q A b C D (deStepTerm q i) =
        (q ^ s * q⁻¹ ^ (2 * n)) •
          (e * deMonomial q A b C D i.1 i.2.1 i.2.2.1 i.2.2.2) -
        deMonomial q A b C D i.1 i.2.1 i.2.2.1 i.2.2.2 * e := by
    rw [deStepTerm_eval hq hqi hpi H]
    have hg := deNumerator_grade s n i (Finsupp.mem_support_iff.mp hi)
    have hp : q ^ i.2.2.2 * q⁻¹ ^ i.2.1 * (q ^ 3)⁻¹ ^ i.1 =
        q ^ s * q⁻¹ ^ (2 * n) := by
      simp only [← zpow_natCast, inv_zpow, ← zpow_neg, ← zpow_mul, ← zpow_add₀ hq]
      congr 1
      push_cast
      omega
    rw [hp]
  simp only [deNumerator, deStep, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul]
  simp only [deEval, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have h := ht i hi
  simp only [deEval, Finsupp.linearCombination_apply, Finsupp.sum] at h
  rw [← Finset.smul_sum, h, smul_sub]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  module

/-- The normalized, finite divided e-adjoint of D^(s) in the ambient algebra. -/
def deW (q : k) (A b C D : B) (s n : ℕ) : B :=
  (qFactorial q n)⁻¹ • deEval q A b C D (deNumerator q s n)

lemma deW_zero (s : ℕ) : deW q A b C D s 0 = qDivPow q s D := by
  simp [deW, deNumerator, deEval, deMonomial, P3, qFactorial, qDivPow_zero']

lemma deW_mul (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) (s n : ℕ) :
    deW q A b C D s n * e = (q ^ s * q⁻¹ ^ (2 * n)) • (e * deW q A b C D s n) -
      qInt q (n + 1) • deW q A b C D s (n + 1) := by
  have hn := hqi (n + 1) (by omega)
  simp only [deW, smul_mul_assoc, deNumerator_eval_mul hq hqi hpi H,
    smul_sub, mul_smul_comm, smul_smul, qFactorial_succ, mul_inv_rev]
  congr 1
  · congr 1
    ring
  · congr 1
    field_simp

lemma deW_sum (s n : ℕ) : deW q A b C D s n =
    ∑ i ∈ (deNumerator q s n).support,
      deCoeff q s n i • deMonomial q A b C D i.1 i.2.1 i.2.2.1 i.2.2.2 := by
  simp only [deW, deEval, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.smul_sum, smul_smul, deCoeff]

/-- Actual finite-sum expansion of every divided e-adjoint, with Laurent scalar coefficients. -/
theorem deW_eq_sum (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0) (s n : ℕ) :
    deW q A b C D s n = ∑ i ∈ (deNumerator q s n).support,
      (q ^ ((i.2.2.2 : ℤ) * ((i.1 : ℤ) - i.2.2.1)) *
        deScalar q i.1 i.2.1 i.2.2.1) •
          deMonomial q A b C D i.1 i.2.1 i.2.2.1 i.2.2.2 := by
  rw [deW_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hg := deNumerator_grade s n i (Finsupp.mem_support_iff.mp hi)
  rw [deCoeff_eq_deScalar hq hqi s n i.1 i.2.1 i.2.2.1 i.2.2.2 hg.1 hg.2, deScale]

/-- Unrestricted D,e straightening in the actual normalized root vectors. -/
theorem qDivPow_D_mul_qDivPow_e (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) (s r : ℕ) :
    qDivPow q s D * qDivPow q r e =
      ∑ n ∈ range (r + 1), B2Integral.sCoef q s r n •
        (qDivPow q (r - n) e * deW q A b C D s n) := by
  rw [← deW_zero (q := q) (A := A) (b := b) (C := C) s]
  exact B2Integral.straighten hq hqi s (deW_mul hq hqi hpi H s) r

/-- Arbitrary divided powers of D and e lie in the existing ordered integral span.
No closure or linear independence of that span is assumed. -/
theorem qDivPow_D_mul_qDivPow_e_mem (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) {Λ : Subring k} (hqΛ : q ∈ Λ) (hiΛ : q⁻¹ ∈ Λ)
    (s r : ℕ) : qDivPow q s D * qDivPow q r e ∈ orderedSpan q Λ e A b C D f := by
  rw [qDivPow_D_mul_qDivPow_e hq hqi hpi H]
  refine AddSubgroup.sum_mem _ fun n _ ↦ ?_
  apply smul_mem_orderedSpan (B2Integral.sCoef_mem hqΛ hiΛ s r n)
  rw [deW_sum, Finset.mul_sum]
  refine AddSubgroup.sum_mem _ fun i _ ↦ ?_
  rw [mul_smul_comm]
  apply smul_mem_orderedSpan (deCoeff_mem hq hqi Λ hqΛ hiΛ s n i)
  simpa [M6, M5, deMonomial, qDivPow_zero', mul_assoc] using
    M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
      (D := D) (f := f) (r - n) i.1 i.2.1 i.2.2.1 i.2.2.2 0

end LieLean.QuantumGroup.G2Integral
