/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Strings
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Orders of quantum integers at `q = 0`

Let `A` be a local ring, `k` an `A`-algebra and `ϖ ∈ A` a non-unit, and put `q = ϖ` in `k`
(for crystal bases, `A = A₀` is the ring of rational functions regular at `q = 0` and `ϖ = q`).
We record when an element `κ ∈ k` lies in `qᵉ A` (`QuantumGroup.InPow`) and when it is of the
form `qᵉ (1 + ϖ a)` (`QuantumGroup.IsOnePow`), and show that the quantum integers and binomial
coefficients are of the latter form:
`[n] = q^{1-n} (1 + q² + ⋯ + q^{2(n-1)})` (`QuantumGroup.isOnePow_qInt`) and
`[n, m] ∈ q^{-m(n-m)} (1 + ϖ A)` (`QuantumGroup.isOnePow_qBinomial`).
These are used to compute crystal limits of explicit vectors.
-/

namespace LieLean.QuantumGroup

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra A k] (ϖ : A)

/-- `κ ∈ qᵉ A`, where `q` is the image of `ϖ`. -/
def InPow (e : ℤ) (κ : k) : Prop := ∃ a : A, κ = algebraMap A k ϖ ^ e * algebraMap A k a

/-- `κ ∈ qᵉ (1 + ϖ A)`, where `q` is the image of `ϖ`. -/
def IsOnePow (e : ℤ) (κ : k) : Prop :=
  ∃ a : A, κ = algebraMap A k ϖ ^ e * algebraMap A k (1 + ϖ * a)

/-- `κ ∈ qᵉ A×`, where `q` is the image of `ϖ`. -/
def IsUnitPow (e : ℤ) (κ : k) : Prop :=
  ∃ u : A, IsUnit u ∧ κ = algebraMap A k ϖ ^ e * algebraMap A k u

variable {ϖ}

section Basic

lemma IsUnitPow.inPow {e : ℤ} {κ : k} (h : IsUnitPow ϖ e κ) : InPow ϖ e κ := by
  obtain ⟨u, -, rfl⟩ := h
  exact ⟨u, rfl⟩

lemma IsUnitPow.mul {e e' : ℤ} {κ κ' : k} (hq : algebraMap A k ϖ ≠ 0) (h : IsUnitPow ϖ e κ)
    (h' : IsUnitPow ϖ e' κ') : IsUnitPow ϖ (e + e') (κ * κ') := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  exact ⟨u * u', hu.mul hu', by rw [zpow_add₀ hq, map_mul]; ring⟩

lemma IsUnitPow.neg {e : ℤ} {κ : k} (h : IsUnitPow ϖ e κ) : IsUnitPow ϖ e (-κ) := by
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨-u, hu.neg, by rw [map_neg, mul_neg]⟩

lemma IsUnitPow.inv {e : ℤ} {κ : k} (h : IsUnitPow ϖ e κ) : IsUnitPow ϖ (-e) κ⁻¹ := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨v, rfl⟩ := hu
  refine ⟨↑v⁻¹, v⁻¹.isUnit, ?_⟩
  rw [mul_inv, zpow_neg]
  congr 1
  exact (eq_inv_of_mul_eq_one_left (by rw [← map_mul, v.inv_mul, map_one])).symm

lemma IsUnitPow.div {e e' : ℤ} {κ κ' : k} (hq : algebraMap A k ϖ ≠ 0) (h : IsUnitPow ϖ e κ)
    (h' : IsUnitPow ϖ e' κ') : IsUnitPow ϖ (e - e') (κ / κ') := by
  rw [div_eq_mul_inv, sub_eq_add_neg]
  exact h.mul hq h'.inv

lemma isUnitPow_zpow (e : ℤ) : IsUnitPow ϖ e (algebraMap A k ϖ ^ e) :=
  ⟨1, isUnit_one, by simp⟩

lemma isUnitPow_one : IsUnitPow ϖ 0 (1 : k) := ⟨1, isUnit_one, by simp⟩

lemma InPow.add {e : ℤ} {κ κ' : k} (h : InPow ϖ e κ) (h' : InPow ϖ e κ') :
    InPow ϖ e (κ + κ') := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨a', rfl⟩ := h'
  exact ⟨a + a', by rw [map_add, mul_add]⟩

lemma InPow.neg {e : ℤ} {κ : k} (h : InPow ϖ e κ) : InPow ϖ e (-κ) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨-a, by rw [map_neg, mul_neg]⟩

lemma InPow.sub {e : ℤ} {κ κ' : k} (h : InPow ϖ e κ) (h' : InPow ϖ e κ') :
    InPow ϖ e (κ - κ') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

lemma inPow_zero (e : ℤ) : InPow ϖ e (0 : k) := ⟨0, by simp⟩

lemma InPow.congr_right {e : ℤ} {κ κ' : k} (h : InPow ϖ e κ) (hκ : κ = κ') : InPow ϖ e κ' :=
  hκ ▸ h

lemma InPow.mul {e e' : ℤ} {κ κ' : k} (hq : algebraMap A k ϖ ≠ 0) (h : InPow ϖ e κ)
    (h' : InPow ϖ e' κ') : InPow ϖ (e + e') (κ * κ') := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨a', rfl⟩ := h'
  exact ⟨a * a', by rw [zpow_add₀ hq, map_mul]; ring⟩

lemma InPow.mono {e e' : ℤ} {κ : k} (hq : algebraMap A k ϖ ≠ 0) (hee' : e ≤ e')
    (h : InPow ϖ e' κ) : InPow ϖ e κ := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨d, hd⟩ : ∃ d : ℕ, e' = e + d := ⟨(e' - e).toNat, by omega⟩
  exact ⟨ϖ ^ d * a, by rw [hd, zpow_add₀ hq, map_mul, map_pow, zpow_natCast]; ring⟩

lemma InPow.sum {ι : Type*} (s : Finset ι) {e : ℤ} {f : ι → k} (h : ∀ i ∈ s, InPow ϖ e (f i)) :
    InPow ϖ e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inPow_zero e
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

lemma inPow_algebraMap (a : A) : InPow ϖ 0 (algebraMap A k a) := ⟨a, by simp⟩

lemma IsOnePow.inPow {e : ℤ} {κ : k} (h : IsOnePow ϖ e κ) : InPow ϖ e κ := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨_, rfl⟩

lemma isOnePow_zpow (e : ℤ) : IsOnePow ϖ e (algebraMap A k ϖ ^ e) := ⟨0, by simp⟩

lemma isOnePow_one : IsOnePow ϖ 0 (1 : k) := ⟨0, by simp⟩

lemma IsOnePow.mul {e e' : ℤ} {κ κ' : k} (hq : algebraMap A k ϖ ≠ 0) (h : IsOnePow ϖ e κ)
    (h' : IsOnePow ϖ e' κ') : IsOnePow ϖ (e + e') (κ * κ') := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨a', rfl⟩ := h'
  refine ⟨a + a' + ϖ * a * a', ?_⟩
  rw [zpow_add₀ hq]
  simp only [map_add, map_mul, map_one]
  ring

/-- `κ ∈ 1 + ϖ A` implies `κ - 1 ∈ ϖ A`. -/
lemma IsOnePow.sub_one {κ : k} (h : IsOnePow ϖ 0 κ) : InPow ϖ 1 (κ - 1) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨a, by simp [map_add, map_mul]⟩

variable [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
include hϖ

lemma isUnit_one_add_mul (a : A) : IsUnit (1 + ϖ * a) := by
  have h : -(ϖ * a) ∈ nonunits A :=
    (IsLocalRing.mem_maximalIdeal _).1 ((Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right a _ hϖ))
  simpa using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h

lemma IsOnePow.isUnitPow {e : ℤ} {κ : k} (h : IsOnePow ϖ e κ) : IsUnitPow ϖ e κ := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨_, isUnit_one_add_mul hϖ a, rfl⟩

lemma IsOnePow.inv {e : ℤ} {κ : k} (h : IsOnePow ϖ e κ) :
    IsOnePow ϖ (-e) κ⁻¹ := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨u, hu⟩ := isUnit_one_add_mul hϖ a
  refine ⟨-(a * ↑u⁻¹), ?_⟩
  have h0 : (↑u⁻¹ : A) * (1 + ϖ * a) = 1 := by rw [← hu]; exact u.inv_mul
  have h1 : (1 + ϖ * -(a * ↑u⁻¹)) * (1 + ϖ * a) = 1 := by
    have e : (1 + ϖ * -(a * ↑u⁻¹)) = ↑u⁻¹ := by linear_combination (-1 : A) * h0
    rw [e, h0]
  have h2 : algebraMap A k (1 + ϖ * -(a * ↑u⁻¹)) = (algebraMap A k (1 + ϖ * a))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, h1, map_one])
  rw [h2, mul_inv, zpow_neg]

lemma IsOnePow.div {e e' : ℤ} {κ κ' : k} (hq : algebraMap A k ϖ ≠ 0) (h : IsOnePow ϖ e κ)
    (h' : IsOnePow ϖ e' κ') : IsOnePow ϖ (e - e') (κ / κ') := by
  rw [div_eq_mul_inv, sub_eq_add_neg]
  exact h.mul hq (h'.inv hϖ)

end Basic

/-! ### Quantum integers -/

section QInt

variable [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hq : algebraMap A k ϖ ≠ 0)
include hq

omit [IsLocalRing A] in
/-- `[n] = q^{1-n} (1 + q² + ⋯ + q^{2(n-1)})` lies in `q^{1-n} (1 + ϖ A)` for `n ≥ 1`. -/
lemma isOnePow_qInt {n : ℕ} (hn : 0 < n) :
    IsOnePow ϖ (1 - n) (qInt (algebraMap A k ϖ) n) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  -- `[n+1] = Σ_{s ≤ n} q^{n-2s} = q^{-n} Σ_{s ≤ n} q^{2(n-s)}`
  refine ⟨∑ s ∈ Finset.range n, ϖ ^ (2 * (n - s) - 1), ?_⟩
  set q := algebraMap A k ϖ
  have hsum : (1 : A) + ϖ * ∑ s ∈ Finset.range n, ϖ ^ (2 * (n - s) - 1) =
      ∑ s ∈ Finset.range (n + 1), ϖ ^ (2 * (n - s)) := by
    rw [Finset.sum_range_succ, Nat.sub_self, mul_zero, pow_zero, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    rw [← pow_succ']
    congr 1
    have := Finset.mem_range.1 hs
    omega
  rw [hsum, map_sum, qInt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hs := Finset.mem_range.1 hs
  rw [map_pow, inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_neg,
    ← zpow_add₀ hq, ← zpow_add₀ hq]
  congr 1
  push_cast [show s ≤ n by omega, show 2 * (n - s) = 2 * n - 2 * s by omega]
  omega

omit [IsLocalRing A] in
/-- `[n, m] ∈ q^{-m(n-m)} (1 + ϖ A)` for `m ≤ n`. -/
lemma isOnePow_qBinomial {n m : ℕ} (hmn : m ≤ n) :
    IsOnePow ϖ (-(m * (n - m) : ℕ)) (qBinomial (algebraMap A k ϖ) n m) := by
  induction n generalizing m with
  | zero => obtain rfl : m = 0 := by omega
            simpa using isOnePow_one
  | succ n ih =>
    rcases m with _ | m
    · simpa using isOnePow_one
    set q := algebraMap A k ϖ
    rw [qBinomial_succ_succ]
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · -- `m = n`
      obtain rfl : m = n := by omega
      simpa [qBinomial_eq_zero_of_lt q (Nat.lt_succ_self m)] using isOnePow_one
    · -- `[n+1, m+1] = q^{-(m+1)} [n, m+1] + q^{n-m} [n, m]`
      obtain ⟨a₁, h₁⟩ := ih hge
      obtain ⟨a₂, h₂⟩ := ih (show m ≤ n by omega)
      refine ⟨a₁ + ϖ ^ (2 * (n - m) - 1) * (1 + ϖ * a₂), ?_⟩
      rw [h₁, h₂, inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_natCast q (n - m)]
      have e₁ : (-((m + 1 : ℕ) : ℤ)) + (-((m + 1) * (n - (m + 1)) : ℕ) : ℤ) =
          -((m + 1) * (n + 1 - (m + 1)) : ℕ) := by
        push_cast [show m + 1 ≤ n by omega, show m ≤ n by omega]; ring
      have e₂ : ((n - m : ℕ) : ℤ) + (-(m * (n - m) : ℕ) : ℤ) =
          -((m + 1) * (n + 1 - (m + 1)) : ℕ) + ((2 * (n - m) - 1 : ℕ) + 1 : ℕ) := by
        push_cast [show m + 1 ≤ n by omega, show m ≤ n by omega,
          show 1 ≤ 2 * (n - m) by omega]
        ring
      rw [← mul_assoc, ← zpow_add₀ hq, e₁, ← mul_assoc, ← zpow_add₀ hq, e₂, zpow_add₀ hq,
        zpow_natCast, ← map_pow]
      simp only [map_add, map_mul, map_pow, map_one]
      ring

end QInt

end LieLean.QuantumGroup
