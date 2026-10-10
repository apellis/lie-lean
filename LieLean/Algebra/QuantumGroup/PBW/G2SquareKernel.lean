/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2AdjointMonomial
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# A finite ordered recurrence for the G₂ pair C,e

This is an arbitrary-two-exponent identity over the coefficient field. The sparse numerator
recurrence has Laurent coefficients, and its normalization divides by `[n]_q!`.
`G2SquareIntegral` proves the cancellation of this factorial in the collected coefficients
and derives unrestricted integral ordered-span membership.
-/

open Finset

noncomputable section

namespace LieLean.QuantumGroup.G2Integral

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- Exponents of the ordered three-root monomial `A^(a) B^(b) C^(c)`. -/
abbrev SquareIndex := ℕ × ℕ × ℕ

/-- The two corrections when a three-root monomial is multiplied on the right by `e`. -/
def squareStepTerm (q : k) (i : SquareIndex) : SquareIndex →₀ k :=
  (if i.2.1 = 0 then 0 else
    Finsupp.single (i.1 + 1, i.2.1 - 1, i.2.2)
      (q⁻¹ ^ (2 * (i.2.1 - 1) + 1) * qInt q 3 * qInt (q ^ 3) (i.1 + 1))) +
  (if i.2.2 = 0 then 0 else
    Finsupp.single (i.1, i.2.1 + 2, i.2.2 - 1)
      ((q ^ 2 - 1) * (q ^ 3)⁻¹ ^ (i.2.2 - 1) *
        qInt q (i.2.1 + 1) * qInt q (i.2.1 + 2)))

/-- Linear extension of the two correction transitions. -/
def squareStep (q : k) : (SquareIndex →₀ k) →ₗ[k] (SquareIndex →₀ k) :=
  Finsupp.linearCombination k (squareStepTerm q)

/-- Sparse, factorial-cleared coefficients of the iterated adjoint of `C^(s)`. -/
def squareNumerator (q : k) (s : ℕ) : ℕ → SquareIndex →₀ k
  | 0 => Finsupp.single (0, 0, s) 1
  | n + 1 => squareStep q (squareNumerator q s n)

/-- Evaluate sparse coefficients in the actual normalized root vectors. -/
def squareEval (q : k) (A b C : B) : (SquareIndex →₀ k) →ₗ[k] B :=
  Finsupp.linearCombination k (fun i ↦ P3 q A b C i.1 i.2.1 i.2.2)

lemma squareStepTerm_grade (q : k) (i j : SquareIndex) (n s : ℕ)
    (hi : 3 * i.1 + i.2.1 = 2 * n ∧ i.1 + i.2.1 + 2 * i.2.2 = 2 * s)
    (hj : ¬ (3 * j.1 + j.2.1 = 2 * (n + 1) ∧
      j.1 + j.2.1 + 2 * j.2.2 = 2 * s)) : squareStepTerm q i j = 0 := by
  classical
  simp only [squareStepTerm, Finsupp.add_apply]
  have h₁ : (if i.2.1 = 0 then 0 else
      Finsupp.single (i.1 + 1, i.2.1 - 1, i.2.2)
        (q⁻¹ ^ (2 * (i.2.1 - 1) + 1) * qInt q 3 * qInt (q ^ 3) (i.1 + 1))) j = 0 := by
    split_ifs with h
    · rfl
    · apply Finsupp.single_eq_of_ne
      intro he
      subst j
      apply hj
      dsimp
      omega
  have h₂ : (if i.2.2 = 0 then 0 else
      Finsupp.single (i.1, i.2.1 + 2, i.2.2 - 1)
        ((q ^ 2 - 1) * (q ^ 3)⁻¹ ^ (i.2.2 - 1) *
          qInt q (i.2.1 + 1) * qInt q (i.2.1 + 2))) j = 0 := by
    split_ifs with h
    · rfl
    · apply Finsupp.single_eq_of_ne
      intro he
      subst j
      apply hj
      dsimp
      omega
  rw [h₁, h₂, add_zero]

/-- Every nonzero coefficient has the required two root weights. -/
lemma squareNumerator_grade (q : k) (s n : ℕ) (i : SquareIndex)
    (hi : squareNumerator q s n i ≠ 0) :
    3 * i.1 + i.2.1 = 2 * n ∧ i.1 + i.2.1 + 2 * i.2.2 = 2 * s := by
  classical
  induction n generalizing i with
  | zero =>
    have he : (0, 0, s) = i := by
      by_contra hn
      exact hi (Finsupp.single_eq_of_ne (Ne.symm hn))
    subst i
    simp
  | succ n ih =>
    by_contra hn
    apply hi
    simp only [squareNumerator, squareStep, Finsupp.linearCombination_apply,
      Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j hj
    rw [squareStepTerm_grade q j i n s (ih j (Finsupp.mem_support_iff.mp hj)) hn,
      mul_zero]

lemma squareNumerator_eq_zero (q : k) (s n : ℕ) (hn : 3 * s < n) :
    squareNumerator q s n = 0 := by
  ext i
  by_contra hi
  have hg := squareNumerator_grade q s n i hi
  omega

variable {q : k} {e A b C D f : B}
  (hq : q ≠ 0) (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
  (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0) (H : Rel q e A b C D f)

include hq hqi hpi in
lemma SquareRel.squareStepTerm_eval (H : SquareRel q e A b C) (i : SquareIndex) :
    squareEval q A b C (squareStepTerm q i) =
      (q⁻¹ ^ i.2.1 * (q ^ 3)⁻¹ ^ i.1) • (e * P3 q A b C i.1 i.2.1 i.2.2) -
        P3 q A b C i.1 i.2.1 i.2.2 * e := by
  have hm := SquareRel.P3_e hq hqi hpi H i.1 i.2.1 i.2.2
  simp only [squareStepTerm, map_add, squareEval]
  split_ifs <;> simp only [map_zero, Finsupp.linearCombination_single] <;>
    simp_all only [ite_true, ite_false] <;> abel

include hq hqi hpi H in
lemma squareStepTerm_eval (i : SquareIndex) :
    squareEval q A b C (squareStepTerm q i) =
      (q⁻¹ ^ i.2.1 * (q ^ 3)⁻¹ ^ i.1) • (e * P3 q A b C i.1 i.2.1 i.2.2) -
        P3 q A b C i.1 i.2.1 i.2.2 * e :=
  SquareRel.squareStepTerm_eval hq hqi hpi H.squareRel i

include hq hqi hpi in
lemma SquareRel.squareNumerator_eval_mul (H : SquareRel q e A b C) (s n : ℕ) :
    squareEval q A b C (squareNumerator q s n) * e =
      q⁻¹ ^ (2 * n) • (e * squareEval q A b C (squareNumerator q s n)) -
        squareEval q A b C (squareNumerator q s (n + 1)) := by
  classical
  have ht (i : SquareIndex) (hi : i ∈ (squareNumerator q s n).support) :
      squareEval q A b C (squareStepTerm q i) =
        q⁻¹ ^ (2 * n) • (e * P3 q A b C i.1 i.2.1 i.2.2) -
          P3 q A b C i.1 i.2.1 i.2.2 * e := by
    rw [SquareRel.squareStepTerm_eval hq hqi hpi H]
    have hg := (squareNumerator_grade q s n i (Finsupp.mem_support_iff.mp hi)).1
    rw [← inv_pow q 3, ← pow_mul, ← pow_add,
      show i.2.1 + 3 * i.1 = 2 * n by omega]
  simp only [squareNumerator, squareStep, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul]
  simp only [squareEval, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have h := ht i hi
  simp only [squareEval, Finsupp.linearCombination_apply, Finsupp.sum] at h
  rw [← Finset.smul_sum, h, smul_sub]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  module

include hq hqi hpi H in
lemma squareNumerator_eval_mul (s n : ℕ) :
    squareEval q A b C (squareNumerator q s n) * e =
      q⁻¹ ^ (2 * n) • (e * squareEval q A b C (squareNumerator q s n)) -
        squareEval q A b C (squareNumerator q s (n + 1)) :=
  SquareRel.squareNumerator_eval_mul hq hqi hpi H.squareRel s n

/-- The unnormalized transition coefficients are Laurent integral. Normalization is not
covered by this statement. -/
lemma squareStepTerm_mem (q : k) (Λ : Subring k) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ)
    (i j : SquareIndex) : squareStepTerm q i j ∈ Λ := by
  classical
  have hp : (q ^ 3)⁻¹ ∈ Λ := by simpa only [← inv_pow] using Λ.pow_mem hqiΛ 3
  have h₁ : q⁻¹ ^ (2 * (i.2.1 - 1) + 1) * qInt q 3 * qInt (q ^ 3) (i.1 + 1) ∈ Λ :=
    Λ.mul_mem (Λ.mul_mem (Λ.pow_mem hqiΛ _) (B2Integral.qInt_mem hqΛ hqiΛ _))
      (B2Integral.qInt_mem (Λ.pow_mem hqΛ 3) hp _)
  have h₂ : (q ^ 2 - 1) * (q ^ 3)⁻¹ ^ (i.2.2 - 1) *
      qInt q (i.2.1 + 1) * qInt q (i.2.1 + 2) ∈ Λ :=
    Λ.mul_mem (Λ.mul_mem
      (Λ.mul_mem (Λ.sub_mem (Λ.pow_mem hqΛ 2) Λ.one_mem) (Λ.pow_mem hp _))
      (B2Integral.qInt_mem hqΛ hqiΛ _)) (B2Integral.qInt_mem hqΛ hqiΛ _)
  simp only [squareStepTerm, Finsupp.add_apply]
  apply Λ.add_mem
  · split_ifs <;> simp only [Finsupp.zero_apply, Finsupp.single_apply]
    · exact Λ.zero_mem
    · split_ifs <;> first | assumption | exact Λ.zero_mem
  · split_ifs <;> simp only [Finsupp.zero_apply, Finsupp.single_apply]
    · exact Λ.zero_mem
    · split_ifs <;> first | assumption | exact Λ.zero_mem

/-- Laurent integrality before division by the adjoint factorial. -/
lemma squareNumerator_mem (q : k) (Λ : Subring k) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ)
    (s n : ℕ) (i : SquareIndex) : squareNumerator q s n i ∈ Λ := by
  classical
  induction n generalizing i with
  | zero =>
    simp only [squareNumerator, Finsupp.single_apply]
    split_ifs
    · exact Λ.one_mem
    · exact Λ.zero_mem
  | succ n ih =>
    simp only [squareNumerator, squareStep, Finsupp.linearCombination_apply,
      Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Λ.sum_mem fun j _ ↦ Λ.mul_mem (ih j) (squareStepTerm_mem q Λ hqΛ hqiΛ j i)

/-- The collected normalized coefficient.
Its Laurent integrality is proved in `G2SquareIntegral`. -/
def squareCoeff (q : k) (s n : ℕ) (i : SquareIndex) : k :=
  (qFactorial q n)⁻¹ * squareNumerator q s n i

/-- The normalized sparse adjoint; its coefficient integrality is proved in `G2SquareIntegral`. -/
def squareW (q : k) (A b C : B) (s n : ℕ) : B :=
  (qFactorial q n)⁻¹ • squareEval q A b C (squareNumerator q s n)

lemma squareW_sum (s n : ℕ) : squareW q A b C s n =
    ∑ i ∈ (squareNumerator q s n).support,
      squareCoeff q s n i • P3 q A b C i.1 i.2.1 i.2.2 := by
  simp only [squareW, squareEval, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.smul_sum, smul_smul, squareCoeff]

lemma squareW_zero (s : ℕ) : squareW q A b C s 0 = qDivPow (q ^ 3) s C := by
  simp [squareW, squareNumerator, squareEval, P3, qFactorial, qDivPow_zero']

include hq hqi hpi in
lemma SquareRel.squareW_mul (H : SquareRel q e A b C) (s n : ℕ) :
    squareW q A b C s n * e = q⁻¹ ^ (2 * n) • (e * squareW q A b C s n) -
      qInt q (n + 1) • squareW q A b C s (n + 1) := by
  have hn := hqi (n + 1) (by omega)
  simp only [squareW, smul_mul_assoc, SquareRel.squareNumerator_eval_mul hq hqi hpi H,
    smul_sub, mul_smul_comm, smul_smul, qFactorial_succ, mul_inv_rev]
  congr 1
  · congr 1
    ring
  · congr 1
    field_simp

include hq hqi hpi H in
lemma squareW_mul (s n : ℕ) :
    squareW q A b C s n * e = q⁻¹ ^ (2 * n) • (e * squareW q A b C s n) -
      qInt q (n + 1) • squareW q A b C s (n + 1) :=
  SquareRel.squareW_mul hq hqi hpi H.squareRel s n

lemma squareW_eq_zero (s n : ℕ) (hn : 3 * s < n) : squareW q A b C s n = 0 := by
  simp [squareW, squareNumerator_eq_zero q s n hn]

include hq hqi hpi in
/-- Arbitrary C,e straightening over the coefficient field. This does not assert Laurent
integrality of the normalized sparse coefficients. -/
theorem SquareRel.qDivPow_C_mul_qDivPow_e_field (H : SquareRel q e A b C) (s r : ℕ) :
    qDivPow (q ^ 3) s C * qDivPow q r e =
      ∑ n ∈ range (r + 1), B2Integral.sCoefParam q 1 r n •
        (qDivPow q (r - n) e * squareW q A b C s n) := by
  rw [← squareW_zero (q := q) (A := A) (b := b) s]
  exact B2Integral.straighten_param hq hqi 1
    (fun n ↦ by simpa only [one_mul] using SquareRel.squareW_mul hq hqi hpi H s n) r

include hq hqi hpi H in
/-- Arbitrary C,e straightening over the coefficient field. This does not assert Laurent
integrality of the normalized sparse coefficients. -/
theorem qDivPow_C_mul_qDivPow_e_field (s r : ℕ) :
    qDivPow (q ^ 3) s C * qDivPow q r e =
      ∑ n ∈ range (r + 1), B2Integral.sCoefParam q 1 r n •
        (qDivPow q (r - n) e * squareW q A b C s n) :=
  SquareRel.qDivPow_C_mul_qDivPow_e_field hq hqi hpi H.squareRel s r

include hq hqi hpi in
/-- The same field identity as a finite sum of ordered four-root divided monomials.
The two exponents are unrestricted. Laurent integrality is proved in `G2SquareIntegral`. -/
theorem SquareRel.qDivPow_C_mul_qDivPow_e_field_sum (H : SquareRel q e A b C) (s r : ℕ) :
    qDivPow (q ^ 3) s C * qDivPow q r e =
      ∑ n ∈ range (r + 1), ∑ i ∈ (squareNumerator q s n).support,
        (B2Integral.sCoefParam q 1 r n * squareCoeff q s n i) •
          (qDivPow q (r - n) e * qDivPow (q ^ 3) i.1 A *
            qDivPow q i.2.1 b * qDivPow (q ^ 3) i.2.2 C) := by
  rw [SquareRel.qDivPow_C_mul_qDivPow_e_field hq hqi hpi H]
  apply Finset.sum_congr rfl
  intro n _
  rw [squareW_sum, Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [P3, mul_smul_comm, smul_smul, mul_assoc]

include hq hqi hpi H in
/-- The same field identity as a finite sum of ordered four-root divided monomials.
The two exponents are unrestricted. Laurent integrality is proved in `G2SquareIntegral`. -/
theorem qDivPow_C_mul_qDivPow_e_field_sum (s r : ℕ) :
    qDivPow (q ^ 3) s C * qDivPow q r e =
      ∑ n ∈ range (r + 1), ∑ i ∈ (squareNumerator q s n).support,
        (B2Integral.sCoefParam q 1 r n * squareCoeff q s n i) •
          (qDivPow q (r - n) e * qDivPow (q ^ 3) i.1 A *
            qDivPow q i.2.1 b * qDivPow (q ^ 3) i.2.2 C) :=
  SquareRel.qDivPow_C_mul_qDivPow_e_field_sum hq hqi hpi H.squareRel s r

end LieLean.QuantumGroup.G2Integral
