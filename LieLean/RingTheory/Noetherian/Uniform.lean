/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Left ideals of noetherian rings without zero-divisors

Let `R` be a left noetherian ring and `x ∈ R` an element which is not a right zero-divisor
(`IsRightRegular x`). Then the left ideal `R x` meets every nonzero left ideal of `R`
nontrivially. In particular, in a left noetherian ring without zero-divisors any two nonzero left
ideals intersect nontrivially.

## Main results

* `Submodule.inf_span_singleton_ne_bot`: `I ⊓ R x ≠ ⊥` for `I ≠ ⊥` and `x` right regular.
* `Submodule.inf_ne_bot_of_noZeroDivisors`: two nonzero left ideals of a left noetherian ring
  without zero-divisors meet nontrivially.

## Proof

As in Humphreys: if `I ∩ R x = 0`, the left ideals `I + I x + ⋯ + I xⁿ⁻¹` form an ascending chain,
and every sum `a₀ + a₁ x + ⋯ + aₙ xⁿ` with `aₖ ∈ I` vanishing has all `aₖ = 0`, by induction on
`n` (`a₀ = -(a₁ + ⋯ + aₙ xⁿ⁻¹) x ∈ I ∩ R x`, then cancel `x` on the right). The chain stabilizes,
which is impossible.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, Lemma 4.1.
-/

open Finset

namespace Submodule

variable {R : Type*} [Ring R]

/-- The left ideal `I + I x + ⋯ + I xⁿ⁻¹`. -/
def powSumIdeal (I : Submodule R R) (x : R) (n : ℕ) : Submodule R R where
  carrier := {y | ∃ c : ℕ → R, (∀ k, c k ∈ I) ∧ y = ∑ k ∈ range n, c k * x ^ k}
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c + d, fun k ↦ I.add_mem (hc k) (hd k), by simp [add_mul, sum_add_distrib]⟩
  zero_mem' := ⟨0, fun _ ↦ I.zero_mem, by simp⟩
  smul_mem' := by
    rintro r _ ⟨c, hc, rfl⟩
    exact ⟨fun k ↦ r * c k, fun k ↦ I.smul_mem r (hc k), by simp [mul_sum, mul_assoc]⟩

lemma powSumIdeal_mono (I : Submodule R R) (x : R) : Monotone (powSumIdeal I x) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨fun k ↦ if k = n then 0 else c k, fun k ↦ ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact I.zero_mem
    · exact hc k
  · rw [sum_range_succ]
    simp only [ite_true, zero_mul, add_zero]
    exact sum_congr rfl fun k hk ↦ by simp [(mem_range.mp hk).ne]

/-- The sum `I + I x + I x² + ⋯` is direct when `I ∩ R x = 0` and `x` is right regular. -/
lemma eq_zero_of_sum_mul_pow_eq_zero {I : Submodule R R} {x : R} (hx : IsRightRegular x)
    (hI : I ⊓ span R {x} = ⊥) :
    ∀ (n : ℕ) (c : ℕ → R), (∀ k, c k ∈ I) → ∑ k ∈ range (n + 1), c k * x ^ k = 0 →
      ∀ k ≤ n, c k = 0 := by
  intro n
  induction n with
  | zero =>
    intro c _ h k hk
    rw [Nat.le_zero.mp hk]
    simpa using h
  | succ n ih =>
    intro c hc h
    set S := ∑ k ∈ range (n + 1), c (k + 1) * x ^ k
    have hsplit : ∑ k ∈ range (n + 1 + 1), c k * x ^ k = c 0 + S * x := by
      rw [sum_range_succ', sum_mul, pow_zero, mul_one, add_comm]
      congr 1
      exact sum_congr rfl fun k _ ↦ by rw [pow_succ, mul_assoc]
    rw [hsplit] at h
    have h0 : c 0 = 0 := by
      have hmem : c 0 ∈ I ⊓ span R {x} := by
        refine ⟨hc 0, ?_⟩
        rw [eq_neg_of_add_eq_zero_left h]
        exact mem_span_singleton.mpr ⟨-S, by rw [smul_eq_mul, neg_mul]⟩
      rw [hI] at hmem
      exact (mem_bot R).mp hmem
    rw [h0, zero_add] at h
    have hS : S = 0 := hx (show S * x = 0 * x by rw [h, zero_mul])
    intro k hk
    rcases k with _ | k
    · exact h0
    · exact ih (fun k ↦ c (k + 1)) (fun k ↦ hc (k + 1)) hS k (by omega)

/-- **Humphreys, GSM 94, Lemma 4.1.** In a left noetherian ring `R`, if `x` is not a right
zero-divisor, the left ideal `R x` meets every nonzero left ideal `I` nontrivially. -/
theorem inf_span_singleton_ne_bot [IsNoetherian R R] {x : R} (hx : IsRightRegular x)
    {I : Submodule R R} (hI : I ≠ ⊥) : I ⊓ span R {x} ≠ ⊥ := by
  intro hinf
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance
    ⟨powSumIdeal I x, powSumIdeal_mono I x⟩
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff I).mp hI
  have hmem : a * x ^ N ∈ powSumIdeal I x (N + 1) := by
    refine ⟨fun k ↦ if k = N then a else 0, fun k ↦ ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact ha
      · exact I.zero_mem
    · rw [sum_range_succ, sum_eq_zero fun k hk ↦ by simp [(mem_range.mp hk).ne]]
      simp
  have hNN : powSumIdeal I x N = powSumIdeal I x (N + 1) := hN (N + 1) (Nat.le_succ N)
  rw [← hNN] at hmem
  obtain ⟨c, hc, hac⟩ := hmem
  have := eq_zero_of_sum_mul_pow_eq_zero hx hinf N (fun k ↦ if k = N then a else -c k)
    (fun k ↦ by
      split_ifs
      · exact ha
      · exact I.neg_mem (hc k))
    (by
      have hs : ∑ k ∈ range N, (if k = N then a else -c k) * x ^ k =
          -∑ k ∈ range N, c k * x ^ k := by
        rw [← sum_neg_distrib]
        exact sum_congr rfl fun k hk ↦ by simp [(mem_range.mp hk).ne]
      rw [sum_range_succ, hs]
      simp only [↓reduceIte]
      rw [hac, neg_add_cancel]) N le_rfl
  exact ha0 (by simpa using this)

/-- **Humphreys, GSM 94, Lemma 4.1**, second assertion: in a left noetherian ring without
zero-divisors, any two nonzero left ideals intersect nontrivially. -/
theorem inf_ne_bot_of_noZeroDivisors [IsNoetherian R R] [NoZeroDivisors R] {I J : Submodule R R}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : I ⊓ J ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff J).mp hJ
  have hreg : IsRightRegular x := fun a b hab ↦ mul_right_cancel₀ hx0 hab
  refine fun h ↦ inf_span_singleton_ne_bot hreg hI (eq_bot_iff.mpr ?_)
  rw [← h]
  exact inf_le_inf_left I ((span_singleton_le_iff_mem x J).mpr hx)

end Submodule
