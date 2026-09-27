/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Exchange

/-!
# The strong exchange condition for arbitrary words; the deletion condition

Let `cs : CoxeterSystem M W` be a Coxeter system. `LieLean.GroupTheory.Coxeter.Exchange` proves,
via the reflection representation of [BB] §1.4, that for a *reduced* word `ω` the right inversions
of `π ω` are the entries of the right inversion sequence of `ω`. Here we extend this to arbitrary
words: a reflection `t` is a right inversion of `π ω` if and only if it occurs an odd number of
times in the right inversion sequence of `ω`. This gives the strong exchange condition in the
generality of [HumC] §5.8 and [BB] Thm. 1.4.3 (the word need not be reduced), its left-handed
version, the deletion condition, and the facts that a word is reduced if and only if its
inversion sequence has no repetitions and that `w` has exactly `ℓ(w)` right inversions.

## Main results

* `CoxeterSystem.isRightInversion_iff_inversionParity_eq_one`: `ℓ(w t) < ℓ(w) ↔ η(w, t) = 1` for
  a reflection `t` and any `w`.
* `CoxeterSystem.isRightInversion_wordProd_iff`: `t` is a right inversion of `π ω` if and only if
  it occurs an odd number of times in the right inversion sequence of `ω`.
* `CoxeterSystem.IsRightInversion.exists_wordProd_mul_eq`,
  `CoxeterSystem.IsLeftInversion.exists_mul_wordProd_eq`: the strong exchange condition for
  arbitrary words.
* `CoxeterSystem.exists_sublist_isReduced`: the deletion condition.
* `CoxeterSystem.isReduced_iff_nodup_rightInvSeq`, `CoxeterSystem.isReduced_iff_nodup_leftInvSeq`:
  a word is reduced if and only if its inversion sequence has no repetitions.
* `CoxeterSystem.ncard_setOf_isRightInversion`: `w` has exactly `ℓ(w)` right inversions.

## References

* [BB] A. Björner, F. Brenti, *Combinatorics of Coxeter groups*, GTM 231, Springer 2005, §1.4.
* [HumC] J. E. Humphreys, *Reflection groups and Coxeter groups*, CUP 1990, §5.8.
-/

open List

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd
local prefix:100 "ℓ " => cs.length
local prefix:100 "ris " => cs.rightInvSeq
local prefix:100 "lis " => cs.leftInvSeq

/-- A reflection `t` is a right inversion of `w` (`ℓ(w t) < ℓ(w)`) if and only if
`η(w, t) = 1`, for any `w` ([BB] §1.4, proof of Thm. 1.4.3 (check); right-handed version). -/
theorem isRightInversion_iff_inversionParity_eq_one [DecidableEq W] {w t : W} :
    cs.IsRightInversion w t ↔ cs.inversionParity w t = 1 := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [inversionParity_eq_one_iff cs hω, mem_rightInvSeq_iff cs hω]

/-- A reflection `t` is a right inversion of `π ω` if and only if it occurs an odd number of
times in the right inversion sequence of `ω`; here `ω` is any word. -/
theorem isRightInversion_wordProd_iff [DecidableEq W] {ω : List B} {t : W} :
    cs.IsRightInversion (π ω) t ↔ Odd ((ris ω).count t) := by
  rw [isRightInversion_iff_inversionParity_eq_one, inversionParity_wordProd,
    ZMod.natCast_eq_one_iff_odd]

/-- A right inversion of `π ω` occurs in the right inversion sequence of `ω`, for any word `ω`. -/
theorem IsRightInversion.mem_rightInvSeq {ω : List B} {t : W}
    (h : cs.IsRightInversion (π ω) t) : t ∈ ris ω := by
  classical
  rw [isRightInversion_wordProd_iff] at h
  exact count_pos_iff.mp h.pos

/-- A left inversion of `π ω` occurs in the left inversion sequence of `ω`, for any word `ω`. -/
theorem IsLeftInversion.mem_leftInvSeq {ω : List B} {t : W}
    (h : cs.IsLeftInversion (π ω) t) : t ∈ lis ω := by
  rw [← isRightInversion_inv_iff, ← wordProd_reverse] at h
  simpa [rightInvSeq_reverse] using h.mem_rightInvSeq

/-- For a reduced word `ω`, the left inversions of `π ω` are exactly the entries of the left
inversion sequence of `ω`. -/
theorem IsReduced.isLeftInversion_iff {ω : List B} (hω : cs.IsReduced ω) {t : W} :
    cs.IsLeftInversion (π ω) t ↔ t ∈ lis ω :=
  ⟨fun h ↦ h.mem_leftInvSeq, cs.isLeftInversion_of_mem_leftInvSeq hω⟩

/-- **The strong exchange condition** ([HumC] Thm. 5.8, [BB] Thm. 1.4.3), right-handed version:
if `ω` is any word and `t` is a reflection with `ℓ(π ω * t) < ℓ(π ω)`, then `π ω * t` is obtained
from `ω` by deleting one letter. -/
theorem IsRightInversion.exists_wordProd_mul_eq {ω : List B} {t : W}
    (h : cs.IsRightInversion (π ω) t) : ∃ j < ω.length, π ω * t = π (ω.eraseIdx j) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h.mem_rightInvSeq
  rw [length_rightInvSeq] at hj
  refine ⟨j, hj, ?_⟩
  rw [← wordProd_mul_getD_rightInvSeq, List.getD_eq_getElem]

/-- **The strong exchange condition** ([HumC] Thm. 5.8, [BB] Thm. 1.4.3): if `ω` is any word
and `t` is a reflection with `ℓ(t * π ω) < ℓ(π ω)`, then `t * π ω` is obtained from `ω` by
deleting one letter. -/
theorem IsLeftInversion.exists_mul_wordProd_eq {ω : List B} {t : W}
    (h : cs.IsLeftInversion (π ω) t) : ∃ j < ω.length, t * π ω = π (ω.eraseIdx j) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h.mem_leftInvSeq
  rw [length_leftInvSeq] at hj
  refine ⟨j, hj, ?_⟩
  rw [← getD_leftInvSeq_mul_wordProd, List.getD_eq_getElem]

/-- **The exchange condition**, right-handed version ([BB] Thm. 1.5.1 (check), [HumC] §5.8
(check)). -/
theorem IsRightDescent.exists_wordProd_mul_eq {ω : List B} {i : B}
    (h : cs.IsRightDescent (π ω) i) : ∃ j < ω.length, π ω * s i = π (ω.eraseIdx j) :=
  IsRightInversion.exists_wordProd_mul_eq cs
    ((cs.isRightInversion_simple_iff_isRightDescent _ _).mpr h)

/-- **The exchange condition** ([BB] Thm. 1.5.1 (check), [HumC] §5.8 (check)). -/
theorem IsLeftDescent.exists_mul_wordProd_eq {ω : List B} {i : B}
    (h : cs.IsLeftDescent (π ω) i) : ∃ j < ω.length, s i * π ω = π (ω.eraseIdx j) :=
  IsLeftInversion.exists_mul_wordProd_eq cs
    ((cs.isLeftInversion_simple_iff_isLeftDescent _ _).mpr h)

/-- **The deletion condition**: every word contains a reduced subword with the same product
([HumC] §5.8 Cor. (check), [BB] Cor. 1.4.8 (check)). -/
theorem exists_sublist_isReduced (ω : List B) :
    ∃ ω' : List B, ω' <+ ω ∧ cs.IsReduced ω' ∧ π ω' = π ω := by
  induction ω with
  | nil => exact ⟨[], Sublist.slnil, by simp [IsReduced], rfl⟩
  | cons i ω ih =>
    obtain ⟨ω', hsub, hred, hprod⟩ := ih
    by_cases hi : cs.IsLeftDescent (π ω') i
    · obtain ⟨j, hjlt, hj⟩ := IsLeftDescent.exists_mul_wordProd_eq cs hi
      refine ⟨ω'.eraseIdx j, (eraseIdx_sublist _ _).trans (hsub.trans (sublist_cons_self _ _)),
        ?_, by rw [← hj, hprod, wordProd_cons]⟩
      have h1 := (cs.isLeftDescent_iff).mp hi
      have h2 := cs.length_wordProd_le (ω'.eraseIdx j)
      have h3 := List.length_eraseIdx_add_one hjlt
      unfold IsReduced
      rw [← hj]
      rw [hred.eq] at h1
      omega
    · refine ⟨i :: ω', hsub.cons_cons i, ?_, by rw [wordProd_cons, wordProd_cons, hprod]⟩
      have := (cs.not_isLeftDescent_iff).mp hi
      unfold IsReduced
      rw [wordProd_cons, this, hred.eq, length_cons]

/-- A word is reduced if and only if its right inversion sequence has no repetitions. -/
theorem isReduced_iff_nodup_rightInvSeq {ω : List B} : cs.IsReduced ω ↔ (ris ω).Nodup := by
  classical
  refine ⟨IsReduced.nodup_rightInvSeq cs, fun hnd ↦ ?_⟩
  obtain ⟨ω₀, hω₀, he⟩ := cs.exists_isReduced (π ω)
  have hsub : (ris ω).toFinset ⊆ (ris ω₀).toFinset := by
    intro t ht
    rw [List.mem_toFinset] at ht ⊢
    have : cs.IsRightInversion (π ω) t := by
      rw [isRightInversion_wordProd_iff, List.count_eq_one_of_mem hnd ht]
      exact odd_one
    rw [he] at this
    exact this.mem_rightInvSeq
  have h1 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.toFinset_card_of_nodup hω₀.nodup_rightInvSeq,
    length_rightInvSeq, length_rightInvSeq] at h1
  have h2 := cs.length_wordProd_le ω
  unfold IsReduced
  rw [he, hω₀.eq] at h2 ⊢
  omega

/-- A word is reduced if and only if its left inversion sequence has no repetitions. -/
theorem isReduced_iff_nodup_leftInvSeq {ω : List B} : cs.IsReduced ω ↔ (lis ω).Nodup := by
  rw [← isReduced_reverse_iff, isReduced_iff_nodup_rightInvSeq, rightInvSeq_reverse,
    nodup_reverse]

/-- The number of right inversions of `w` is `ℓ(w)` ([BB] Cor. 1.4.5 (check)). -/
theorem ncard_setOf_isRightInversion (w : W) : {t | cs.IsRightInversion w t}.ncard = ℓ w := by
  classical
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have : {t | cs.IsRightInversion (π ω) t} = ↑(ris ω).toFinset := by
    ext t
    simp [(cs.mem_rightInvSeq_iff hω).symm]
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hω.nodup_rightInvSeq,
    length_rightInvSeq, hω.eq]

/-- The number of left inversions of `w` is `ℓ(w)` ([BB] Cor. 1.4.5 (check)). -/
theorem ncard_setOf_isLeftInversion (w : W) : {t | cs.IsLeftInversion w t}.ncard = ℓ w := by
  simp_rw [← isRightInversion_inv_iff, ncard_setOf_isRightInversion, length_inv]

/-- An element has finitely many right inversions. -/
theorem finite_setOf_isRightInversion (w : W) : {t | cs.IsRightInversion w t}.Finite := by
  classical
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  exact (ris ω).finite_toSet.subset fun t ht ↦ IsRightInversion.mem_rightInvSeq cs ht

/-- An element has finitely many left inversions. -/
theorem finite_setOf_isLeftInversion (w : W) : {t | cs.IsLeftInversion w t}.Finite := by
  simp_rw [← isRightInversion_inv_iff]
  exact cs.finite_setOf_isRightInversion w⁻¹

end CoxeterSystem
