/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2AdjointCoeff

/-!
# Finite G₂ adjoint sums

The finite five-root sum and its right-multiplication recurrence are derived from the
normalized G₂ relations. The proof uses the five incoming coefficient identities.
-/

noncomputable section

namespace LieLean.QuantumGroup.G2Integral

open Finset

/-- Exponents of the five-root tail `A, B, C, D, f`. -/
abbrev AdjointIndex := ℕ × ℕ × ℕ × ℕ × ℕ

/-- Indices of weight `(n,s)` in the five-root tail. -/
def adjointIndices (n s : ℕ) : Finset AdjointIndex :=
  ((range (s + 1)) ×ˢ (range (s + 1)) ×ˢ (range (s + 1)) ×ˢ
    (range (s + 1)) ×ˢ (range (s + 1))).filter fun ⟨a, b, c, d, l⟩ =>
      a + b + 2 * c + d + l = s ∧ 3 * a + 2 * b + 3 * c + d = n

@[simp] lemma mem_adjointIndices (n s a b c d l : ℕ) :
    (a, b, c, d, l) ∈ adjointIndices n s ↔
      a + b + 2 * c + d + l = s ∧ 3 * a + 2 * b + 3 * c + d = n := by
  simp only [adjointIndices, mem_filter, mem_product, mem_range]
  omega

lemma adjointIndices_zero (s : ℕ) : adjointIndices 0 s = {(0, 0, 0, 0, s)} := by
  ext ⟨a, b, c, d, l⟩
  simp only [mem_adjointIndices, mem_singleton, Prod.mk.injEq]
  omega

lemma adjointIndices_eq_empty {n s : ℕ} (h : 3 * s < n) :
    adjointIndices n s = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro ⟨a, b, c, d, l⟩ hi
  simp only [mem_adjointIndices] at hi
  omega

private lemma sum_transport {V : Type*} [AddCommMonoid V]
    (S T : Finset AdjointIndex) (P Q : AdjointIndex → Prop)
    [DecidablePred P] [DecidablePred Q]
    (i j : AdjointIndex → AdjointIndex)
    (hi : ∀ x ∈ S, P x → i x ∈ T ∧ Q (i x))
    (hj : ∀ x ∈ T, Q x → j x ∈ S ∧ P (j x))
    (hji : ∀ x ∈ S, P x → j (i x) = x)
    (hij : ∀ x ∈ T, Q x → i (j x) = x)
    (F : AdjointIndex → AdjointIndex → V) :
    (∑ x ∈ S, if P x then F x (i x) else 0) =
      ∑ x ∈ T, if Q x then F (j x) x else 0 := by
  rw [← sum_filter, ← sum_filter]
  apply sum_nbij' i j
  · intro x hx
    rcases mem_filter.mp hx with ⟨hx, hp⟩
    exact mem_filter.mpr (hi x hx hp)
  · intro x hx
    rcases mem_filter.mp hx with ⟨hx, hp⟩
    exact mem_filter.mpr (hj x hx hp)
  · intro x hx
    rcases mem_filter.mp hx with ⟨hx, hp⟩
    exact hji x hx hp
  · intro x hx
    rcases mem_filter.mp hx with ⟨hx, hp⟩
    exact hij x hx hp
  · intro x hx
    rcases mem_filter.mp hx with ⟨hx, hp⟩
    rw [hji x hx hp]

variable {V : Type*} [AddCommMonoid V]

lemma sum_adjoint_shift_f (n s : ℕ) (F : AdjointIndex → AdjointIndex → V) :
    (∑ x ∈ adjointIndices n s, if x.2.2.2.2 ≠ 0 then
      F x (x.1, x.2.1, x.2.2.1, x.2.2.2.1 + 1, x.2.2.2.2 - 1) else 0) =
      ∑ x ∈ adjointIndices (n + 1) s, if x.2.2.2.1 ≠ 0 then
        F (x.1, x.2.1, x.2.2.1, x.2.2.2.1 - 1, x.2.2.2.2 + 1) x else 0 := by
  apply sum_transport _ _ _ _
    (fun ⟨a, b, c, d, l⟩ => (a, b, c, d + 1, l - 1))
    (fun ⟨a, b, c, d, l⟩ => (a, b, c, d - 1, l + 1))
  all_goals
    rintro ⟨a, b, c, d, l⟩ hx hp
    simp only [mem_adjointIndices] at hx
    simp only [mem_adjointIndices, Prod.mk.injEq, true_and]
    dsimp only at hp ⊢
    omega

lemma sum_adjoint_shift_D (n s : ℕ) (F : AdjointIndex → AdjointIndex → V) :
    (∑ x ∈ adjointIndices n s, if x.2.2.2.1 ≠ 0 then
      F x (x.1, x.2.1 + 1, x.2.2.1, x.2.2.2.1 - 1, x.2.2.2.2) else 0) =
      ∑ x ∈ adjointIndices (n + 1) s, if x.2.1 ≠ 0 then
        F (x.1, x.2.1 - 1, x.2.2.1, x.2.2.2.1 + 1, x.2.2.2.2) x else 0 := by
  apply sum_transport _ _ _ _
    (fun ⟨a, b, c, d, l⟩ => (a, b + 1, c, d - 1, l))
    (fun ⟨a, b, c, d, l⟩ => (a, b - 1, c, d + 1, l))
  all_goals
    rintro ⟨a, b, c, d, l⟩ hx hp
    simp only [mem_adjointIndices] at hx
    simp only [mem_adjointIndices, Prod.mk.injEq, true_and, and_true]
    dsimp only at hp ⊢
    omega

lemma sum_adjoint_shift_DC (n s : ℕ) (F : AdjointIndex → AdjointIndex → V) :
    (∑ x ∈ adjointIndices n s, if 1 < x.2.2.2.1 then
      F x (x.1, x.2.1, x.2.2.1 + 1, x.2.2.2.1 - 2, x.2.2.2.2) else 0) =
      ∑ x ∈ adjointIndices (n + 1) s, if x.2.2.1 ≠ 0 then
        F (x.1, x.2.1, x.2.2.1 - 1, x.2.2.2.1 + 2, x.2.2.2.2) x else 0 := by
  apply sum_transport _ _ _ _
    (fun ⟨a, b, c, d, l⟩ => (a, b, c + 1, d - 2, l))
    (fun ⟨a, b, c, d, l⟩ => (a, b, c - 1, d + 2, l))
  all_goals
    rintro ⟨a, b, c, d, l⟩ hx hp
    simp only [mem_adjointIndices] at hx
    simp only [mem_adjointIndices, Prod.mk.injEq, true_and, and_true]
    dsimp only at hp ⊢
    omega

lemma sum_adjoint_shift_C (n s : ℕ) (F : AdjointIndex → AdjointIndex → V) :
    (∑ x ∈ adjointIndices n s, if x.2.2.1 ≠ 0 then
      F x (x.1, x.2.1 + 2, x.2.2.1 - 1, x.2.2.2.1, x.2.2.2.2) else 0) =
      ∑ x ∈ adjointIndices (n + 1) s, if 1 < x.2.1 then
        F (x.1, x.2.1 - 2, x.2.2.1 + 1, x.2.2.2.1, x.2.2.2.2) x else 0 := by
  apply sum_transport _ _ _ _
    (fun ⟨a, b, c, d, l⟩ => (a, b + 2, c - 1, d, l))
    (fun ⟨a, b, c, d, l⟩ => (a, b - 2, c + 1, d, l))
  all_goals
    rintro ⟨a, b, c, d, l⟩ hx hp
    simp only [mem_adjointIndices] at hx
    simp only [mem_adjointIndices, Prod.mk.injEq, true_and, and_true]
    dsimp only at hp ⊢
    omega

lemma sum_adjoint_shift_B (n s : ℕ) (F : AdjointIndex → AdjointIndex → V) :
    (∑ x ∈ adjointIndices n s, if x.2.1 ≠ 0 then
      F x (x.1 + 1, x.2.1 - 1, x.2.2.1, x.2.2.2.1, x.2.2.2.2) else 0) =
      ∑ x ∈ adjointIndices (n + 1) s, if x.1 ≠ 0 then
        F (x.1 - 1, x.2.1 + 1, x.2.2.1, x.2.2.2.1, x.2.2.2.2) x else 0 := by
  apply sum_transport _ _ _ _
    (fun ⟨a, b, c, d, l⟩ => (a + 1, b - 1, c, d, l))
    (fun ⟨a, b, c, d, l⟩ => (a - 1, b + 1, c, d, l))
  all_goals
    rintro ⟨a, b, c, d, l⟩ hx hp
    simp only [mem_adjointIndices] at hx
    simp only [mem_adjointIndices, Prod.mk.injEq, and_true]
    dsimp only at hp ⊢
    omega

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- The finite divided q-adjoint family of the last root vector. -/
def adjointSum (q : k) (A b C D f : B) (n s : ℕ) : B :=
  ∑ x ∈ adjointIndices n s,
    adjointCoeff q x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 •
      M5 q A b C D f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

@[simp] lemma adjointSum_zero (q : k) (A b C D f : B) (s : ℕ) :
    adjointSum q A b C D f 0 s = qDivPow (q ^ 3) s f := by
  simp [adjointSum, adjointIndices_zero, adjointCoeff, adjointExponent, M5, P3,
    qDivPow_zero']

lemma adjointSum_eq_zero (q : k) (A b C D f : B) {n s : ℕ} (h : 3 * s < n) :
    adjointSum q A b C D f n s = 0 := by
  simp [adjointSum, adjointIndices_eq_empty h]

private lemma adjoint_lead {q : k} (hq : q ≠ 0) (n s a b c d l : ℕ)
    (h : (a, b, c, d, l) ∈ adjointIndices n s) :
    (q ^ 3) ^ l * q ^ d * q⁻¹ ^ b * (q ^ 3)⁻¹ ^ a =
      q ^ (3 * s) * q⁻¹ ^ (2 * n) := by
  have hi := (mem_adjointIndices n s a b c d l).mp h
  simp only [inv_pow, ← pow_mul]
  field_simp
  simp only [← pow_add]
  congr 1
  omega

variable {q : k} {e A b C D f : B}

/-- The two-term right-`e` recurrence for the finite G₂ adjoint sum. -/
lemma adjointSum_e (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) (n s : ℕ) :
    adjointSum q A b C D f n s * e =
      (q ^ (3 * s) * q⁻¹ ^ (2 * n)) • (e * adjointSum q A b C D f n s) -
        qInt q (n + 1) • adjointSum q A b C D f (n + 1) s := by
  let coeff : AdjointIndex → k := fun ⟨a, b', c, d, l⟩ => adjointCoeff q a b' c d l
  let M : AdjointIndex → B := fun ⟨a, b', c, d, l⟩ => M5 q A b C D f a b' c d l
  let Ff : AdjointIndex → AdjointIndex → B := fun x y =>
    (q ^ 3 * coeff x * qInt q y.2.2.2.1) • M y
  let FD : AdjointIndex → AdjointIndex → B := fun x y =>
    (q ^ (3 * y.2.2.2.2 + 1) * q⁻¹ ^ (3 * y.2.2.1) * coeff x *
      qInt q 2 * qInt q y.2.1) • M y
  let FDC : AdjointIndex → AdjointIndex → B := fun x y =>
    (-(q ^ (3 * y.2.2.2.2) * q⁻¹ ^ y.2.2.2.1 * coeff x) *
      qInt q 3 * qInt (q ^ 3) y.2.2.1) • M y
  let FC : AdjointIndex → AdjointIndex → B := fun x y =>
    ((q ^ 2 - 1) * (q ^ (3 * y.2.2.2.2 + y.2.2.2.1) *
      q⁻¹ ^ (3 * y.2.2.1) * coeff x) * qInt q (y.2.1 - 1) * qInt q y.2.1) • M y
  let FB : AdjointIndex → AdjointIndex → B := fun x y =>
    (q ^ (3 * y.2.2.2.2 + y.2.2.2.1) * q⁻¹ ^ (2 * y.2.1 + 1) * coeff x *
      qInt q 3 * qInt (q ^ 3) y.1) • M y
  have step (x : AdjointIndex) (hx : x ∈ adjointIndices n s) :
      (coeff x • M x) * e =
        (q ^ (3 * s) * q⁻¹ ^ (2 * n)) • (e * (coeff x • M x)) -
        (if x.2.2.2.2 ≠ 0 then
          Ff x (x.1, x.2.1, x.2.2.1, x.2.2.2.1 + 1, x.2.2.2.2 - 1) else 0) -
        (if x.2.2.2.1 ≠ 0 then
          FD x (x.1, x.2.1 + 1, x.2.2.1, x.2.2.2.1 - 1, x.2.2.2.2) else 0) -
        (if 1 < x.2.2.2.1 then
          FDC x (x.1, x.2.1, x.2.2.1 + 1, x.2.2.2.1 - 2, x.2.2.2.2) else 0) -
        (if x.2.2.1 ≠ 0 then
          FC x (x.1, x.2.1 + 2, x.2.2.1 - 1, x.2.2.2.1, x.2.2.2.2) else 0) -
        (if x.2.1 ≠ 0 then
          FB x (x.1 + 1, x.2.1 - 1, x.2.2.1, x.2.2.2.1, x.2.2.2.2) else 0) := by
    rcases x with ⟨a, b', c, d, l⟩
    dsimp only [coeff, M, Ff, FD, FDC, FC, FB]
    rw [smul_mul_assoc, M5_e hq hqi hpi H,
      ← adjoint_lead hq n s a b' c d l hx]
    simp only [show b' + 2 - 1 = b' + 1 by omega,
      show (1 < d) ↔ ¬ d ≤ 1 by omega, ite_not]
    split_ifs <;>
      simp only [mul_smul_comm, smul_add, smul_sub, smul_zero, smul_smul,
        pow_add, pow_one, pow_mul, inv_pow] <;> module
  have incoming (x : AdjointIndex) (hx : x ∈ adjointIndices (n + 1) s) :
      qInt q (n + 1) • (coeff x • M x) =
        (if x.2.2.2.1 ≠ 0 then
          Ff (x.1, x.2.1, x.2.2.1, x.2.2.2.1 - 1, x.2.2.2.2 + 1) x else 0) +
        (if x.2.1 ≠ 0 then
          FD (x.1, x.2.1 - 1, x.2.2.1, x.2.2.2.1 + 1, x.2.2.2.2) x else 0) +
        (if x.2.2.1 ≠ 0 then
          FDC (x.1, x.2.1, x.2.2.1 - 1, x.2.2.2.1 + 2, x.2.2.2.2) x else 0) +
        (if 1 < x.2.1 then
          FC (x.1, x.2.1 - 2, x.2.2.1 + 1, x.2.2.2.1, x.2.2.2.2) x else 0) +
        (if x.1 ≠ 0 then
          FB (x.1 - 1, x.2.1 + 1, x.2.2.1, x.2.2.2.1, x.2.2.2.2) x else 0) := by
    rcases x with ⟨a, b', c, d, l⟩
    have hn := ((mem_adjointIndices (n + 1) s a b' c d l).mp hx).2
    dsimp only [coeff, M, Ff, FD, FDC, FC, FB]
    rw [smul_smul, ← hn, adjointCoeff_recurrence hq hd]
    simp only [add_smul, ite_not, show (1 < b') ↔ ¬ b' ≤ 1 by omega,
      ite_smul, zero_smul]
  change (∑ x ∈ adjointIndices n s, coeff x • M x) * e =
    (q ^ (3 * s) * q⁻¹ ^ (2 * n)) •
      (e * ∑ x ∈ adjointIndices n s, coeff x • M x) -
    qInt q (n + 1) • ∑ x ∈ adjointIndices (n + 1) s, coeff x • M x
  rw [sum_mul]
  simp_rw [sum_congr rfl step]
  simp only [sum_sub_distrib]
  rw [sum_adjoint_shift_f n s Ff, sum_adjoint_shift_D n s FD,
    sum_adjoint_shift_DC n s FDC, sum_adjoint_shift_C n s FC,
    sum_adjoint_shift_B n s FB]
  simp only [mul_sum, smul_sum]
  rw [sum_congr rfl incoming]
  simp only [sum_add_distrib]
  abel

/-- Integral-coefficient straightening of arbitrary last-root and first-root divided powers.
The finite adjoint sum is explicit; this does not assert closure of the full ordered span. -/
theorem qDivPow_f_mul_qDivPow_e (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) (r s : ℕ) :
    qDivPow (q ^ 3) s f * qDivPow q r e =
      ∑ n ∈ range (r + 1), B2Integral.sCoef q (3 * s) r n •
        (qDivPow q (r - n) e * adjointSum q A b C D f n s) := by
  simpa only [adjointSum_zero] using
    B2Integral.straighten hq hqi (3 * s) (fun n => adjointSum_e hq hd hqi hpi H n s) r

/-- The straightening identity with both finite sums displayed. -/
theorem qDivPow_f_mul_qDivPow_e_sum (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) (r s : ℕ) :
    qDivPow (q ^ 3) s f * qDivPow q r e =
      ∑ n ∈ range (r + 1), ∑ x ∈ adjointIndices n s,
        (B2Integral.sCoef q (3 * s) r n *
          adjointCoeff q x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) •
        (qDivPow q (r - n) e *
          M5 q A b C D f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  rw [qDivPow_f_mul_qDivPow_e hq hd hqi hpi H]
  simp only [adjointSum, mul_sum, smul_sum, mul_smul_comm, smul_smul]

/-- Every coefficient in the double-sum straightening belongs to any subring containing
`q` and `q⁻¹`; no quantum-integer denominators remain. -/
lemma adjoint_straightening_coeff_mem (Λ : Subring k) (hqΛ : q ∈ Λ) (hqΛ' : q⁻¹ ∈ Λ)
    (r s n a b c d l : ℕ) :
    B2Integral.sCoef q (3 * s) r n * adjointCoeff q a b c d l ∈ Λ :=
  Λ.mul_mem (B2Integral.sCoef_mem hqΛ hqΛ' _ _ _) (adjointCoeff_mem Λ hqΛ _ _ _ _ _)

end LieLean.QuantumGroup.G2Integral
