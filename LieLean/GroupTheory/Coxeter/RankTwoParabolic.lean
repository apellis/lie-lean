/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.GeometricRepresentation
import LieLean.GroupTheory.Coxeter.Matsumoto
import LieLean.GroupTheory.Coxeter.Parabolic.CoxeterSystem

/-!
# Rank-two parabolic subgroups of Coxeter groups

For two distinct simple reflections `sᵢ`, `sₖ` of a Coxeter system, we describe the elements `u`
of the parabolic subgroup `W_{i,k} = ⟨sᵢ, sₖ⟩` with `ℓ(u sᵢ) > ℓ(u)`: they are the products of the
alternating words `⋯ sᵢ sₖ` of length `n < mᵢₖ`
(`CoxeterSystem.exists_eq_wordProd_alternatingWord`).
Among them, `u sᵢ u⁻¹` is a simple reflection `sₗ` only for `n = 0` (`l = i`) and for
`n = mᵢₖ - 1` (`CoxeterSystem.eq_of_alternatingWord_mul_simple_eq`); in the second case `l` is the
letter not at the beginning of the alternating word, i.e. `u αᵢ = αₗ` for the corresponding root.

These are the rank-two inputs of the inductive proof that Lusztig's braid group operators map
simple root vectors to `U⁺` (`LieLean/Algebra/QuantumGroup/PBW/RootVectors.lean`).

## Main results

* `CoxeterSystem.mem_of_simple_mem_parabolicSubgroup`: `sₗ ∈ W_J` implies `l ∈ J`.
* `CoxeterSystem.exists_eq_wordProd_alternatingWord`: elements `u ∈ W_{i,k}` without right
  descent `i` are alternating products of length `< mᵢₖ`.
* `CoxeterSystem.eq_of_alternatingWord_mul_simple_eq`: the conjugation criterion above.

## References

Standard facts about dihedral groups, e.g. [HumC] §1.1, §5.4 (check); the proofs are ours and use
`CoxeterSystem.orderOf_simple_mul_simple` and `CoxeterSystem.isReduced_alternatingWord`.
-/

namespace CoxeterSystem

open List

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} {cs : CoxeterSystem M W}

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd
local prefix:100 "ℓ " => cs.length

/-- A simple reflection lying in `W_J` has its index in `J`. -/
theorem mem_of_simple_mem_parabolicSubgroup {J : Set B} {l : B}
    (h : s l ∈ cs.parabolicSubgroup J) : l ∈ J := by
  obtain ⟨ω, hred, hJ, he⟩ := exists_isReduced_of_mem_parabolicSubgroup h
  have hlen : ω.length = 1 := by rw [← hred.eq, he, length_simple]
  obtain ⟨l', rfl⟩ := List.length_eq_one_iff.mp hlen
  rw [wordProd_singleton] at he
  rw [← cs.simple_injective he]
  exact hJ l' (by simp)

/-- An element of `W_{i,k}` without right descent `i` is the product of an alternating word
`⋯ sᵢ sₖ` of length `n < mᵢₖ` (any `n` if `mᵢₖ = ∞`). -/
theorem exists_eq_wordProd_alternatingWord {i k : B} (hik : i ≠ k) {u : W}
    (hu : u ∈ cs.parabolicSubgroup {i, k}) (hui : ¬cs.IsRightDescent u i) :
    ∃ n, (M i k = 0 ∨ n < M i k) ∧ u = π (alternatingWord i k n) := by
  have hM1 : M i k ≠ 1 := M.off_diagonal i k hik
  obtain ⟨ω, hred, hJ, rfl⟩ := exists_isReduced_of_mem_parabolicSubgroup hu
  rcases ω.eq_nil_or_concat with rfl | ⟨ω', c, rfl⟩
  · exact ⟨0, by omega, rfl⟩
  -- the last letter is `k`
  have hc : c = k := by
    rcases hJ c (by simp) with hc | hc
    · subst hc
      exfalso
      apply hui
      have h1 := hred.eq
      rw [IsRightDescent, wordProd_concat, simple_mul_simple_cancel_right]
      rw [wordProd_concat] at h1
      rw [h1]
      have := cs.length_wordProd_le ω'
      simp only [concat_eq_append, length_append, length_singleton]
      omega
    · exact hc
  subst hc
  -- a reduced word in `{i, k}` ending with `k` is alternating
  have hrev : cs.IsReduced (ω'.concat c).reverse := (cs.isReduced_reverse_iff _).mpr hred
  have halt := hrev.eq_reverse_alternatingWord (a := c) (b := i)
    (fun d hd ↦ by
      rcases hJ d (mem_reverse.mp hd) with h | h
      · exact Or.inr h
      · exact Or.inl h)
    (by simp)
  rw [length_reverse, reverse_inj] at halt
  set n := (ω'.concat c).length with hn
  rw [halt] at hred hui ⊢
  refine ⟨n, ?_, rfl⟩
  by_cases hM : M i c = 0
  · exact Or.inl hM
  refine Or.inr ?_
  have hle : n ≤ M i c := by
    by_contra hlt
    exact cs.not_isReduced_alternatingWord i c hM (by omega) hred
  refine lt_of_le_of_ne hle fun heq ↦ hui ?_
  -- the alternating word of length `mᵢₖ` also ends with `i`
  have e := cs.prod_alternatingWord_eq_prod_alternatingWord_sub i c n (by omega)
  rw [show M i c * 2 - n = (M i c - 1) + 1 by omega, alternatingWord_succ,
    wordProd_concat] at e
  rw [e, IsRightDescent, mul_assoc, simple_mul_simple_self, mul_one]
  have := cs.length_wordProd_le (alternatingWord i c (M i c - 1))
  have h2 : ℓ (π (alternatingWord i c (M i c - 1)) * s i) = M i c := by
    rw [← e, hred.eq, length_alternatingWord, heq]
  rw [length_alternatingWord] at this
  omega

/-- The two alternating words of length `r` define the same element only if `mᵢₖ ∣ r`. -/
theorem dvd_of_wordProd_alternatingWord_eq {i k : B} {r : ℕ}
    (h : π (alternatingWord i k r) = π (alternatingWord k i r)) : M i k ∣ r := by
  rw [← cs.orderOf_simple_mul_simple i k]
  apply orderOf_dvd_of_pow_eq_one
  rw [prod_alternatingWord_eq_mul_pow, prod_alternatingWord_eq_mul_pow] at h
  have hinv : s k * s i = (s i * s k)⁻¹ := by simp [mul_inv_rev]
  rw [hinv, inv_pow] at h
  obtain ⟨t, ht | ht⟩ := Nat.even_or_odd' r
  · have he : Even r := ⟨t, by omega⟩
    simp only [he, ↓reduceIte, one_mul] at h
    have : t = r / 2 := by omega
    subst this
    rw [ht, pow_mul', sq]
    nth_rw 1 [h]
    exact inv_mul_cancel _
  · have he : ¬Even r := by rw [Nat.not_even_iff_odd]; exact ⟨t, ht⟩
    simp only [he, ↓reduceIte] at h
    have ht2 : r / 2 = t := by omega
    rw [ht2] at h
    -- `sₖ xᵗ = sᵢ x⁻ᵗ` with `x = sᵢ sₖ`
    have h' : (s i * s k) ^ (t + 1) = ((s i * s k) ^ t)⁻¹ := by
      rw [pow_succ', mul_assoc, h, ← mul_assoc, simple_mul_simple_self, one_mul]
    rw [ht, pow_succ, show 2 * t = t + t by ring, pow_add, mul_assoc, ← pow_succ, h',
      mul_inv_cancel]

/-- **Conjugation in rank two**: if `u = ⋯ sᵢ sₖ` is alternating of length `n < mᵢₖ` and
`u sᵢ = sₗ u`, then `n = 0` and `l = i`, or `n = mᵢₖ - 1` and `sₗ` is the simple reflection not at
the start of `u`. -/
theorem eq_of_alternatingWord_mul_simple_eq {i k : B} (hik : i ≠ k) {n : ℕ}
    (hn : M i k = 0 ∨ n < M i k) {l : B}
    (h : π (alternatingWord i k n) * s i = s l * π (alternatingWord i k n)) :
    (n = 0 ∧ l = i) ∨ (n + 1 = M i k ∧ l = if Even n then k else i) := by
  rcases n with _ | n
  · left
    simp only [alternatingWord, wordProd_nil, one_mul, mul_one] at h
    exact ⟨rfl, (cs.simple_injective h).symm⟩
  right
  have hMs : M k i = M i k := M.symmetric k i
  -- `l ∈ {i, k}`
  have hl : l ∈ ({i, k} : Set B) := by
    apply mem_of_simple_mem_parabolicSubgroup (cs := cs)
    have hu : π (alternatingWord i k (n + 1)) ∈ cs.parabolicSubgroup {i, k} :=
      wordProd_mem_parabolicSubgroup fun c hc ↦ by
        rcases eq_or_eq_of_mem_alternatingWord hc with rfl | rfl <;> simp
    have : s l = π (alternatingWord i k (n + 1)) * s i * (π (alternatingWord i k (n + 1)))⁻¹ := by
      rw [h, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu (simple_mem_parabolicSubgroup (by simp)))
      (Subgroup.inv_mem _ hu)
  -- `u sᵢ` is the reduced alternating word `⋯ sₖ sᵢ` of length `n + 2`
  have hus : π (alternatingWord i k (n + 1)) * s i = π (alternatingWord k i (n + 2)) := by
    rw [alternatingWord_succ k i (n + 1), wordProd_concat]
  have hlen : ℓ (π (alternatingWord k i (n + 2))) = n + 2 :=
    cs.length_wordProd_alternatingWord k i (by rw [hMs]; omega)
  -- `l` is not the first letter of `u`
  have hfirst := alternatingWord_succ' i k n
  have hne : l ≠ if Even n then k else i := by
    intro hl'
    rw [hl', hus, hfirst, wordProd_cons, simple_mul_simple_cancel_left] at h
    have := cs.length_wordProd_le (alternatingWord i k n)
    rw [length_alternatingWord, ← h, hlen] at this
    omega
  have hl2 : l = if Even (n + 1) then k else i := by
    rcases hl with rfl | hl
    · by_cases he : Even n
      · simp [he, Nat.even_add_one]
      · simp [he] at hne
    · rw [Set.mem_singleton_iff] at hl
      subst hl
      by_cases he : Even n
      · simp [he] at hne
      · simp [he, Nat.even_add_one]
  refine ⟨?_, hl2⟩
  -- the two alternating words of length `n + 2` coincide, so `mᵢₖ ∣ n + 2`
  have heq : π (alternatingWord i k (n + 2)) = π (alternatingWord k i (n + 2)) := by
    rw [← hus, h, alternatingWord_succ' i k (n + 1), wordProd_cons, hl2]
  have hdvd := dvd_of_wordProd_alternatingWord_eq heq
  rcases hn with h0 | hlt
  · rw [h0, zero_dvd_iff] at hdvd
    omega
  · have := Nat.le_of_dvd (by omega) hdvd
    omega

end CoxeterSystem
