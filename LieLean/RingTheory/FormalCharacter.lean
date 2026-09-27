/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# A sign-reversing involution for the identity `∏ (1 - xᵢ) · ∏ (1 - xᵢ)⁻¹ = 1`

Let `σ` be a linearly ordered set of "variables" with weights `w : σ → M` in an additive
commutative monoid. Consider pairs `(S, s)` of a finite set `S ⊆ σ` (a monomial of
`∏ᵢ (1 - xᵢ)`, with sign `(-1)^|S|`) and a finitely supported `s : σ →₀ ℕ` (a monomial of
`∏ᵢ (1 - xᵢ)⁻¹ = ∏ᵢ ∑ₙ xᵢⁿ`), of total weight `∑_{i ∈ S} wᵢ + ∑ᵢ sᵢ wᵢ`. Then for every `β` the
signed number of pairs of weight `β` (when finite) is `1` if `β = 0` and `0` otherwise; this is
the coefficient form of `∏ᵢ (1 - e^{wᵢ}) · ∏ᵢ (1 - e^{wᵢ})⁻¹ = 1` for infinitely many variables.
It is used to prove that the Kac–Moody denominator is the inverse of the character of the Verma
module `M(0)`.

The proof is the standard sign-reversing involution: let `x` be the least index occurring in
`S` or in the support of `s`; if `x ∈ S`, move it from `S` to `s`, otherwise move one copy of
`x` from `s` to `S`. Its only fixed point is `(∅, 0)`.

## Main definitions

* `FormalCharacter.pairWt`: the weight of a pair `(S, s)`.
* `FormalCharacter.signInv`: the sign-reversing involution.

## Main results

* `FormalCharacter.sum_neg_one_pow_card_eq_ite`: the signed count of the pairs of weight `β`
  is `if β = 0 then 1 else 0`.
-/

open Finsupp

noncomputable section

namespace FormalCharacter

variable {σ M : Type*} [LinearOrder σ] [AddCommMonoid M]

/-- The weight `∑_{i ∈ S} wᵢ + ∑ᵢ sᵢ wᵢ` of a pair `(S, s)`. -/
def pairWt (w : σ → M) (p : Finset σ × (σ →₀ ℕ)) : M :=
  ∑ x ∈ p.1, w x + p.2.sum fun x n ↦ n • w x

/-- The set of indices occurring in a pair `(S, s)`: `S ∪ supp s`. -/
def indices (p : Finset σ × (σ →₀ ℕ)) : Finset σ := p.1 ∪ p.2.support

/-- Move the index `x` from `S` to `s` if `x ∈ S`, and one copy of `x` from `s` to `S`
otherwise. -/
def toggle (x : σ) (p : Finset σ × (σ →₀ ℕ)) : Finset σ × (σ →₀ ℕ) :=
  if x ∈ p.1 then (p.1.erase x, p.2 + single x 1) else (insert x p.1, p.2 - single x 1)

/-- The sign-reversing involution: toggle the least index occurring in the pair. -/
def signInv (p : Finset σ × (σ →₀ ℕ)) : Finset σ × (σ →₀ ℕ) :=
  if h : (indices p).Nonempty then toggle ((indices p).min' h) p else p

variable {x : σ} {p : Finset σ × (σ →₀ ℕ)}

lemma single_le_of_mem_indices (hx : x ∈ indices p) (hxS : x ∉ p.1) : single x 1 ≤ p.2 := by
  rw [single_le_iff, Nat.one_le_iff_ne_zero, ← mem_support_iff]
  simpa [indices, hxS] using hx

lemma indices_toggle (hx : x ∈ indices p) : indices (toggle x p) = indices p := by
  unfold toggle
  split_ifs with hxS
  · ext y
    simp only [indices, Finset.mem_union, Finset.mem_erase, mem_support_iff, add_apply,
      single_apply]
    by_cases hy : x = y
    · subst hy; simp [hxS]
    · simp [hy, Ne.symm hy]
  · have hle := single_le_of_mem_indices hx hxS
    have hx1 : 1 ≤ p.2 x := by simpa using hle x
    ext y
    simp only [indices, Finset.mem_union, Finset.mem_insert, mem_support_iff, tsub_apply,
      single_apply]
    by_cases hy : x = y
    · subst hy; simp only [true_or, true_iff]; right; omega
    · simp [hy, Ne.symm hy]

lemma toggle_toggle (hx : x ∈ indices p) : toggle x (toggle x p) = p := by
  unfold toggle
  by_cases hxS : x ∈ p.1
  · rw [ite_eq_left hxS, ite_eq_right (Finset.notMem_erase x p.1), Finset.insert_erase hxS,
      add_tsub_cancel_right]
  · rw [ite_eq_right hxS, ite_eq_left (Finset.mem_insert_self x p.1), Finset.erase_insert hxS,
      tsub_add_cancel_of_le (single_le_of_mem_indices hx hxS)]

lemma toggle_ne (x : σ) (p : Finset σ × (σ →₀ ℕ)) : toggle x p ≠ p := by
  unfold toggle
  split_ifs with hxS
  · intro h
    have := congrArg Prod.fst h
    simp only at this
    have h2 : x ∈ p.1.erase x := by rw [this]; exact hxS
    exact Finset.notMem_erase x p.1 h2
  · intro h
    have := congrArg Prod.fst h
    simp only at this
    exact hxS (this ▸ Finset.mem_insert_self x p.1)

lemma neg_one_pow_card_toggle (x : σ) (p : Finset σ × (σ →₀ ℕ)) :
    (-1 : ℤ) ^ (toggle x p).1.card = -(-1) ^ p.1.card := by
  unfold toggle
  split_ifs with hxS <;> dsimp only
  · rw [← Finset.card_erase_add_one hxS, pow_succ]
    ring
  · rw [Finset.card_insert_of_notMem hxS, pow_succ]
    ring

lemma pairWt_toggle (w : σ → M) (hx : x ∈ indices p) : pairWt w (toggle x p) = pairWt w p := by
  unfold toggle pairWt
  split_ifs with hxS <;> dsimp only
  · rw [sum_add_index' (h := fun x n ↦ n • w x) (fun _ ↦ zero_nsmul _)
      (fun _ _ _ ↦ add_nsmul _ _ _),
      sum_single_index (h := fun x n ↦ n • w x) (zero_nsmul _), one_nsmul,
      ← Finset.sum_erase_add _ _ hxS]
    abel
  · conv_rhs => rw [← tsub_add_cancel_of_le (single_le_of_mem_indices hx hxS)]
    rw [Finset.sum_insert hxS, sum_add_index' (h := fun x n ↦ n • w x) (fun _ ↦ zero_nsmul _)
      (fun _ _ _ ↦ add_nsmul _ _ _),
      sum_single_index (h := fun x n ↦ n • w x) (zero_nsmul _), one_nsmul]
    abel

lemma min'_indices_signInv (h : (indices p).Nonempty) :
    ∃ h' : (indices (signInv p)).Nonempty,
      (indices (signInv p)).min' h' = (indices p).min' h := by
  have hmem := (indices p).min'_mem h
  have hI : indices (signInv p) = indices p := by
    rw [signInv, dite_eq_left h, indices_toggle hmem]
  exact ⟨hI ▸ h, by simp_rw [hI]⟩

lemma signInv_signInv (p : Finset σ × (σ →₀ ℕ)) : signInv (signInv p) = p := by
  by_cases h : (indices p).Nonempty
  · obtain ⟨h', hmin⟩ := min'_indices_signInv h
    rw [signInv, dite_eq_left h', hmin, signInv, dite_eq_left h,
      toggle_toggle ((indices p).min'_mem h)]
  · have hp : signInv p = p := dite_eq_right h
    rw [hp, hp]

lemma eq_of_not_nonempty_indices (h : ¬ (indices p).Nonempty) : p = (∅, 0) := by
  rw [Finset.not_nonempty_iff_eq_empty, indices, Finset.union_eq_empty,
    support_eq_empty] at h
  exact Prod.ext h.1 h.2

lemma signInv_ne (hp : p ≠ (∅, 0)) : signInv p ≠ p := by
  have h : (indices p).Nonempty := by
    by_contra h
    exact hp (eq_of_not_nonempty_indices h)
  rw [signInv, dite_eq_left h]
  exact toggle_ne _ _

lemma neg_one_pow_card_signInv (hp : p ≠ (∅, 0)) :
    (-1 : ℤ) ^ (signInv p).1.card = -(-1) ^ p.1.card := by
  have h : (indices p).Nonempty := by
    by_contra h
    exact hp (eq_of_not_nonempty_indices h)
  rw [signInv, dite_eq_left h, neg_one_pow_card_toggle]

lemma pairWt_signInv (w : σ → M) (p : Finset σ × (σ →₀ ℕ)) :
    pairWt w (signInv p) = pairWt w p := by
  unfold signInv
  split_ifs with h
  · exact pairWt_toggle w ((indices p).min'_mem h)
  · rfl

/-- **The identity `∏ (1 - e^{wᵢ}) · ∏ (1 - e^{wᵢ})⁻¹ = 1`, coefficientwise**: if the set of
pairs `(S, s)` of weight `β` is finite, their signed count `∑ (-1)^|S|` is `1` if `β = 0` and `0`
otherwise. -/
theorem sum_neg_one_pow_card_eq_ite [DecidableEq M] (w : σ → M) (β : M)
    {T : Finset (Finset σ × (σ →₀ ℕ))}
    (hT : ∀ p, p ∈ T ↔ pairWt w p = β) :
    ∑ p ∈ T, (-1 : ℤ) ^ p.1.card = if β = 0 then 1 else 0 := by
  classical
  have h0 : ∑ p ∈ T.erase (∅, 0), (-1 : ℤ) ^ p.1.card = 0 := by
    refine Finset.sum_involution (fun p _ ↦ signInv p) (fun p hp ↦ ?_) (fun p hp _ ↦ ?_)
      (fun p hp ↦ ?_) (fun p _ ↦ signInv_signInv p)
    · rw [neg_one_pow_card_signInv (Finset.ne_of_mem_erase hp), add_neg_cancel]
    · exact signInv_ne (Finset.ne_of_mem_erase hp)
    · obtain ⟨hp0, hpT⟩ := Finset.mem_erase.mp hp
      refine Finset.mem_erase.mpr ⟨fun h ↦ hp0 ?_, (hT _).mpr ?_⟩
      · rw [← signInv_signInv p, h]
        rfl
      · rw [pairWt_signInv]
        exact (hT p).mp hpT
  have hwt0 : pairWt w ((∅ : Finset σ), (0 : σ →₀ ℕ)) = 0 := by simp [pairWt]
  split_ifs with hβ
  · have hmem : ((∅ : Finset σ), (0 : σ →₀ ℕ)) ∈ T := (hT _).mpr (hwt0.trans hβ.symm)
    rw [← Finset.add_sum_erase _ _ hmem, h0]
    simp
  · have hmem : ((∅ : Finset σ), (0 : σ →₀ ℕ)) ∉ T := fun h ↦ hβ (((hT _).mp h).symm.trans hwt0)
    rwa [← Finset.erase_eq_of_notMem hmem]

end FormalCharacter

end
