/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.GroupTheory.Coxeter.Inversion

/-!
# The strong exchange condition

Let `cs : CoxeterSystem M W` be a Coxeter system (possibly infinite). Following [BB] §1.4 we
construct the permutation representation of `W` on `W × ZMod 2` in which the simple reflection
`sᵢ` acts by `(t, ε) ↦ (sᵢ t sᵢ, ε + δ(t = sᵢ))` ([BB] use `T × {±1}`; allowing all `t ∈ W`
changes nothing and avoids a subtype). For a word `ω` with product `w`, the element `π ω` acts by
`(t, ε) ↦ (w t w⁻¹, ε + n(ω, t))`, where `n(ω, t)` is the number of occurrences of `t` in the right
inversion sequence of `ω`. Hence the parity `η(w, t) = n(ω, t) mod 2` depends only on `w`
(`CoxeterSystem.inversionParity`), and one shows that a reflection `t` is a right inversion of
`w` if and only if `η(w, t) = 1`. This gives the strong exchange condition for arbitrary (not
necessarily reduced) words, the deletion condition, and the fact that the right (left) inversion
sequence of a reduced word lists every right (left) inversion exactly once.

Mathlib's `Mathlib/GroupTheory/Coxeter/Inversion.lean` provides the inversion sequences and the
fact that their entries are inversions; the converse proved here is the new ingredient.

## Main definitions

* `CoxeterSystem.simplePerm`, `CoxeterSystem.permRep`: the permutation representation of `W` on
  `W × ZMod 2`.
* `CoxeterSystem.inversionParity`: the function `η(w, t) ∈ ZMod 2`.

## Main results

* `CoxeterSystem.isRightInversion_iff_inversionParity_eq_one`: `ℓ(w t) < ℓ(w) ↔ η(w, t) = 1` for a
  reflection `t`.
* `CoxeterSystem.isRightInversion_wordProd_iff`: `t` is a right inversion of `π ω` if and only if
  it occurs an odd number of times in the right inversion sequence of `ω`.
* `CoxeterSystem.IsRightInversion.exists_wordProd_mul_eq`,
  `CoxeterSystem.IsLeftInversion.exists_mul_wordProd_eq`: the strong exchange condition.
* `CoxeterSystem.exists_sublist_isReduced`: the deletion condition.
* `CoxeterSystem.isReduced_iff_nodup_rightInvSeq`: a word is reduced if and only if its right
  inversion sequence has no repetitions.
* `CoxeterSystem.ncard_setOf_isRightInversion`: `w` has exactly `ℓ(w)` right inversions.

## References

* [BB] A. Björner, F. Brenti, *Combinatorics of Coxeter groups*, GTM 231, Springer 2005, §1.3–1.4
  (Thm. 1.4.3, the strong exchange property).
* [HumC] J. E. Humphreys, *Reflection groups and Coxeter groups*, CUP 1990, §5.8 (proved there via
  the geometric representation).
-/

open List

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd
local prefix:100 "ℓ " => cs.length
local prefix:100 "ris " => cs.rightInvSeq
local prefix:100 "lis " => cs.leftInvSeq

/-- Conjugation by `sᵢ` fixes only `sᵢ` among the elements it maps to `sᵢ`. -/
theorem simple_mul_mul_simple_eq_simple_iff {t : W} {i : B} :
    s i * t * s i = s i ↔ t = s i := by
  constructor
  · intro h
    simpa [mul_assoc] using congrArg (fun x ↦ s i * x * s i) h
  · rintro rfl
    simp

open scoped Classical in
/-- The permutation of `W × ZMod 2` attached to the simple reflection `sᵢ`:
`(t, ε) ↦ (sᵢ t sᵢ, ε + δ(t = sᵢ))` ([BB] §1.4). -/
noncomputable def simplePerm (i : B) : Equiv.Perm (W × ZMod 2) :=
  Function.Involutive.toPerm (fun p ↦ (s i * p.1 * s i, p.2 + if p.1 = s i then 1 else 0))
    (by
      rintro ⟨t, ε⟩
      simp only [cs.simple_mul_mul_simple_eq_simple_iff, Prod.mk.injEq]
      refine ⟨by simp [mul_assoc], ?_⟩
      split_ifs <;> [rw [add_assoc, (by decide : (1 : ZMod 2) + 1 = 0), add_zero]; simp])

open scoped Classical in
/-- The formula defining `CoxeterSystem.simplePerm`. -/
theorem simplePerm_apply (i : B) (p : W × ZMod 2) :
    cs.simplePerm i p = (s i * p.1 * s i, p.2 + if p.1 = s i then 1 else 0) := rfl

/-- The action of a word: `sᵢ₁ ⋯ sᵢₖ` acts by `(t, ε) ↦ (w t w⁻¹, ε + n(ω, t))`, where `w = π ω`
and `n(ω, t)` is the number of occurrences of `t` in the right inversion sequence of `ω`. -/
theorem prod_map_simplePerm_apply [DecidableEq W] (ω : List B) (p : W × ZMod 2) :
    (ω.map cs.simplePerm).prod p =
      (π ω * p.1 * (π ω)⁻¹, p.2 + ((ris ω).count p.1 : ZMod 2)) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih, simplePerm_apply]
    simp only [rightInvSeq, List.count_cons, wordProd_cons, Prod.mk.injEq]
    refine ⟨by simp [mul_assoc], ?_⟩
    have : π ω * p.1 * (π ω)⁻¹ = s i ↔ (π ω)⁻¹ * s i * π ω = p.1 := by
      constructor <;> intro h
      · rw [← h]; group
      · rw [← h]; group
    by_cases h : (π ω)⁻¹ * s i * π ω = p.1
    · simp [h, this.mpr h, add_assoc]
    · simp [this, h]

/-- The image of the alternating word `sᵢ sⱼ ⋯ sᵢ sⱼ` of length `2k` under any map to a monoid. -/
theorem prod_map_alternatingWord_two_mul {G : Type*} [Monoid G] (f : B → G) (i j : B) (k : ℕ) :
    ((alternatingWord i j (2 * k)).map f).prod = (f i * f j) ^ k := by
  induction k with
  | zero => simp [alternatingWord]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, alternatingWord_succ', alternatingWord_succ']
    simp [ih, pow_succ', mul_assoc]

/-- Appending `[i, j]` to an alternating word ending in `j`. -/
theorem alternatingWord_add_two (i j : B) (n : ℕ) :
    alternatingWord i j (n + 2) = alternatingWord i j n ++ [i, j] := by
  simp [alternatingWord_succ]

/-- The reverse of the word `i j ⋯ i j` is `j i ⋯ j i`. -/
theorem reverse_alternatingWord_two_mul (i j : B) (k : ℕ) :
    (alternatingWord i j (2 * k)).reverse = alternatingWord j i (2 * k) := by
  induction k with
  | zero => simp [alternatingWord]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, alternatingWord_succ', alternatingWord_succ',
      alternatingWord_add_two]
    simp [ih]

/-- The left inversion sequence of the word `(sⱼ sᵢ)^{mᵢⱼ}` is periodic with period `mᵢⱼ`. -/
theorem leftInvSeq_alternatingWord_two_mul_eq_append (i j : B) :
    lis (alternatingWord j i (2 * M i j)) =
      (lis (alternatingWord j i (2 * M i j))).take (M i j) ++
        (lis (alternatingWord j i (2 * M i j))).take (M i j) := by
  set m := M i j
  apply List.ext_getElem (by simp; omega)
  intro n h₁ h₂
  simp only [length_leftInvSeq, length_alternatingWord] at h₁
  rw [getElem_leftInvSeq_alternatingWord cs j i m n h₁]
  by_cases hn : n < m
  · rw [List.getElem_append_left (by simp; omega), List.getElem_take,
      getElem_leftInvSeq_alternatingWord cs j i m n h₁]
  · rw [List.getElem_append_right (by simp; omega), List.getElem_take]
    simp only [length_take, length_leftInvSeq, length_alternatingWord]
    rw [getElem_leftInvSeq_alternatingWord cs j i m _ (by omega)]
    simp only [prod_alternatingWord_eq_mul_pow, Nat.not_even_two_mul_add_one, ite_false]
    have e1 : (2 * n + 1) / 2 = n - min m (2 * m) + m := by omega
    have e2 : (2 * (n - min m (2 * m)) + 1) / 2 = n - min m (2 * m) := by omega
    rw [e1, e2, pow_add, simple_mul_simple_pow, mul_one]

/-- Every element occurs an even number of times in the right inversion sequence of the word
`(sᵢ sⱼ)^{mᵢⱼ}`. -/
theorem even_count_rightInvSeq_alternatingWord [DecidableEq W] (i j : B) (t : W) :
    Even ((ris (alternatingWord i j (2 * M i j))).count t) := by
  rw [← reverse_reverse (alternatingWord i j (2 * M i j)), reverse_alternatingWord_two_mul,
    rightInvSeq_reverse, count_reverse, leftInvSeq_alternatingWord_two_mul_eq_append,
    count_append]
  exact ⟨_, rfl⟩

/-- The permutations `CoxeterSystem.simplePerm` satisfy the Coxeter relations. -/
theorem isLiftable_simplePerm : M.IsLiftable cs.simplePerm := by
  classical
  intro i j
  rw [← prod_map_alternatingWord_two_mul]
  ext p
  · simp only [prod_map_simplePerm_apply, Equiv.Perm.one_apply]
    have : π (alternatingWord i j (2 * M i j)) = 1 := by
      rw [wordProd, prod_map_alternatingWord_two_mul, simple_mul_simple_pow]
    simp [this]
  · simp only [prod_map_simplePerm_apply, Equiv.Perm.one_apply]
    obtain ⟨c, hc⟩ := cs.even_count_rightInvSeq_alternatingWord i j p.1
    rw [hc, Nat.cast_add, ← two_mul, (by decide : (2 : ZMod 2) = 0), zero_mul, add_zero]

/-- The permutation representation of `W` on `W × ZMod 2`, sending `sᵢ` to
`CoxeterSystem.simplePerm cs i` ([BB] §1.4 (check)). -/
noncomputable def permRep : W →* Equiv.Perm (W × ZMod 2) :=
  cs.lift ⟨cs.simplePerm, cs.isLiftable_simplePerm⟩

/-- `CoxeterSystem.permRep` on a simple reflection. -/
theorem permRep_simple (i : B) : cs.permRep (s i) = cs.simplePerm i :=
  cs.lift_apply_simple _ i

/-- `CoxeterSystem.permRep` on the product of a word. -/
theorem permRep_wordProd (ω : List B) : cs.permRep (π ω) = (ω.map cs.simplePerm).prod := by
  rw [wordProd, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ cs.permRep_simple i

/-- The parity `η(w, t) ∈ ZMod 2` of the number of occurrences of `t` in the right inversion
sequence of any word for `w` (see `CoxeterSystem.inversionParity_wordProd`). -/
noncomputable def inversionParity (w t : W) : ZMod 2 := (cs.permRep w (t, 0)).2

/-- `η(π ω, t)` is the number of occurrences of `t` in the right inversion sequence of `ω`,
modulo `2`. -/
theorem inversionParity_wordProd [DecidableEq W] (ω : List B) (t : W) :
    cs.inversionParity (π ω) t = (ris ω).count t := by
  simp [inversionParity, permRep_wordProd, prod_map_simplePerm_apply]

/-- The permutation representation in terms of `η`: `w · (t, ε) = (w t w⁻¹, ε + η(w, t))`. -/
theorem permRep_apply (w : W) (p : W × ZMod 2) :
    cs.permRep w p = (w * p.1 * w⁻¹, p.2 + cs.inversionParity w p.1) := by
  classical
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  rw [inversionParity_wordProd, permRep_wordProd, prod_map_simplePerm_apply]

/-- `η(1, t) = 0`. -/
theorem inversionParity_one (t : W) : cs.inversionParity 1 t = 0 := by
  simp [inversionParity]

/-- The cocycle identity `η(u v, t) = η(v, t) + η(u, v t v⁻¹)`. -/
theorem inversionParity_mul (u v t : W) :
    cs.inversionParity (u * v) t = cs.inversionParity v t + cs.inversionParity u (v * t * v⁻¹) := by
  have h : cs.permRep (u * v) (t, 0) = cs.permRep u (cs.permRep v (t, 0)) := by
    rw [map_mul, Equiv.Perm.mul_apply]
  simp only [permRep_apply] at h
  simpa using congrArg Prod.snd h

/-- `η(sᵢ, sᵢ) = 1`. -/
theorem inversionParity_simple_self (i : B) : cs.inversionParity (s i) (s i) = 1 := by
  classical
  rw [← wordProd_singleton, inversionParity_wordProd]
  simp

/-- `η(t, t) = 1` for every reflection `t`. -/
theorem IsReflection.inversionParity_self {t : W} (ht : cs.IsReflection t) :
    cs.inversionParity t t = 1 := by
  obtain ⟨u, i, rfl⟩ := ht
  have h1 := cs.inversionParity_mul u u⁻¹ (u * s i * u⁻¹)
  have h2 := cs.inversionParity_mul (u * s i) u⁻¹ (u * s i * u⁻¹)
  have h3 := cs.inversionParity_mul u (s i) (s i)
  simp only [mul_inv_cancel, inversionParity_one, inv_inv] at h1 h2 h3
  have e : u⁻¹ * (u * s i * u⁻¹) * u = s i := by group
  have e' : s i * s i * (s i)⁻¹ = s i := by simp
  rw [e] at h1 h2
  rw [e', inversionParity_simple_self] at h3
  rw [h2, h3, add_left_comm, ← h1, add_zero]

private theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem isRightInversion_of_inversionParity_eq_one {w t : W}
    (h : cs.inversionParity w t = 1) : cs.IsRightInversion w t := by
  classical
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [inversionParity_wordProd] at h
  have : (ris ω).count t ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at h
    exact zero_ne_one h
  exact cs.isRightInversion_of_mem_rightInvSeq hω (count_pos_iff.mp (Nat.pos_of_ne_zero this))

/-- A reflection `t` is a right inversion of `w` (`ℓ(w t) < ℓ(w)`) if and only if
`η(w, t) = 1` ([BB] §1.4, proof of Thm. 1.4.3 (check); right-handed version). -/
theorem isRightInversion_iff_inversionParity_eq_one {w t : W} :
    cs.IsRightInversion w t ↔ cs.inversionParity w t = 1 := by
  refine ⟨fun h ↦ ?_, cs.isRightInversion_of_inversionParity_eq_one⟩
  rcases zmod_two_eq_zero_or_one (cs.inversionParity w t) with h0 | h1
  · have := cs.inversionParity_mul w t t
    rw [h.1.inversionParity_self, mul_assoc, mul_inv_cancel, mul_one, h0, add_zero] at this
    have h' := (cs.isRightInversion_of_inversionParity_eq_one this).2
    rw [mul_assoc, h.1.mul_self, mul_one] at h'
    exact absurd h.2 (lt_asymm h')
  · exact h1

/-- A reflection `t` is a right inversion of `π ω` if and only if it occurs an odd number of
times in the right inversion sequence of `ω`. -/
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

/-- For a reduced word `ω`, the right inversions of `π ω` are exactly the entries of the right
inversion sequence of `ω`. -/
theorem IsReduced.isRightInversion_iff {ω : List B} (hω : cs.IsReduced ω) {t : W} :
    cs.IsRightInversion (π ω) t ↔ t ∈ ris ω :=
  ⟨fun h ↦ h.mem_rightInvSeq, cs.isRightInversion_of_mem_rightInvSeq hω⟩

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

/-- **The exchange condition**, right-handed version. -/
theorem IsRightDescent.exists_wordProd_mul_eq {ω : List B} {i : B}
    (h : cs.IsRightDescent (π ω) i) : ∃ j < ω.length, π ω * s i = π (ω.eraseIdx j) :=
  IsRightInversion.exists_wordProd_mul_eq cs
    ((cs.isRightInversion_simple_iff_isRightDescent _ _).mpr h)

/-- **The exchange condition**. -/
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
    simp [hω.isRightInversion_iff]
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
