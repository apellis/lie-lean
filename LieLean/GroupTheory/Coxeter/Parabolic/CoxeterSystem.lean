/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Matsumoto

/-!
# Standard parabolic subgroups are Coxeter groups

Let `cs : CoxeterSystem M W` be a Coxeter system and `J` a set of indices. We show that the
standard parabolic subgroup `W_J` (`CoxeterSystem.parabolicSubgroup`) is a Coxeter group with
Coxeter matrix `M|_J` (`CoxeterMatrix.restrict`), with simple reflections `sⱼ`, `j ∈ J`, and that
its length function is the restriction of that of `W` ([HumC] §5.5, [BB] §2.4).

The homomorphism from the Coxeter group of `M|_J` to `W` is injective because a reduced word
for `M|_J` stays reduced in `W`: otherwise, by the exchange condition, some `J`-word would have two
reduced expressions in `W` of which only one is reduced for `M|_J`; by Matsumoto's theorem they
are connected by braid moves, which only involve letters of `J` and relations of `M|_J`. (This
argument was reconstructed by us; [HumC] §5.5 uses the geometric representation instead.)

## Main definitions

* `CoxeterMatrix.restrict`: the restriction `M|_J` of a Coxeter matrix.
* `CoxeterSystem.restrictHom`: the homomorphism from the Coxeter group of `M|_J` to `W`.
* `CoxeterSystem.parabolicCoxeterSystem`: the Coxeter system `(W_J, {sⱼ : j ∈ J})`.

## Main results

* `CoxeterSystem.isReduced_map_val_iff`: a `J`-word is reduced for `M|_J` iff it is reduced in
  `W`.
* `CoxeterSystem.restrictHom_injective`, `CoxeterSystem.range_restrictHom`.
* `CoxeterSystem.coe_parabolicCoxeterSystem_simple`,
  `CoxeterSystem.length_parabolicCoxeterSystem`: the simple reflections and the length function
  of `W_J`.

## References

* [HumC] J. E. Humphreys, *Reflection groups and Coxeter groups*, CUP 1990, §5.5.
* [BB] A. Björner, F. Brenti, *Combinatorics of Coxeter groups*, GTM 231, Springer 2005, §2.4.
-/

open List

namespace CoxeterMatrix

variable {B : Type*} (M : CoxeterMatrix B)

/-- The restriction of a Coxeter matrix to a subset `J` of the index set. -/
protected def restrict (J : Set B) : CoxeterMatrix J where
  M := M.M.submatrix Subtype.val Subtype.val
  isSymm := M.isSymm.submatrix _
  diagonal i := M.diagonal i
  off_diagonal i i' h := M.off_diagonal i i' (Subtype.val_injective.ne h)

/-- The entries of `M|_J`. -/
@[simp]
theorem restrict_apply (J : Set B) (i j : J) : M.restrict J i j = M i j := rfl

end CoxeterMatrix

namespace CoxeterSystem

variable {B B' : Type*}

/-- The image of an alternating word under a map of index sets. -/
theorem map_alternatingWord (f : B → B') (i j : B) (m : ℕ) :
    (alternatingWord i j m).map f = alternatingWord (f i) (f j) m := by
  induction m generalizing i j with
  | zero => rfl
  | succ m ih => rw [alternatingWord_succ, alternatingWord_succ, map_concat, ih]

/-- The letters of an alternating word in `i, j` are `i` and `j`. -/
theorem eq_or_eq_of_mem_alternatingWord {i j c : B} {m : ℕ} (h : c ∈ alternatingWord i j m) :
    c = i ∨ c = j := by
  induction m generalizing i j with
  | zero => simp [alternatingWord] at h
  | succ m ih =>
    rw [alternatingWord_succ, concat_eq_append, mem_append, mem_singleton] at h
    rcases h with h | rfl
    · exact (ih h).symm
    · exact .inr rfl

/-- An alternating word in `i, j` of length at least `2` contains both `i` and `j`. -/
theorem mem_alternatingWord_of_two_le {i j : B} {m : ℕ} (hm : 2 ≤ m) :
    i ∈ alternatingWord i j m ∧ j ∈ alternatingWord i j m := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have : alternatingWord i j (m + 2) = alternatingWord i j m ++ [i, j] := by
    simp [alternatingWord_succ]
  simp [this]

variable {W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd
local prefix:100 "ℓ " => cs.length

variable (J : Set B)

open scoped Classical in
/-- Sends a word with letters in `J` to the corresponding element of the Coxeter group of the
restricted matrix (letters outside `J` are sent to `1`). -/
private noncomputable def toRestrict (M : CoxeterMatrix B) (J : Set B)
    (ω : List B) : (M.restrict J).Group :=
  (ω.map fun i ↦ if h : i ∈ J then (M.restrict J).simple ⟨i, h⟩ else 1).prod

private theorem toRestrict_append (ω ω' : List B) :
    toRestrict M J (ω ++ ω') = toRestrict M J ω * toRestrict M J ω' := by
  simp [toRestrict]

private theorem toRestrict_map_val (η : List J) :
    toRestrict M J (η.map Subtype.val) = (M.restrict J).toCoxeterSystem.wordProd η := by
  unfold toRestrict wordProd
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun j _ ↦ ?_
  simp [j.2]

private theorem length_toRestrict_le (ω : List B) :
    (M.restrict J).toCoxeterSystem.length (toRestrict M J ω) ≤ ω.length := by
  classical
  induction ω with
  | nil => simp [toRestrict]
  | cons i ω ih =>
    have h1 := (M.restrict J).toCoxeterSystem.length_mul_le
      (if h : i ∈ J then (M.restrict J).simple ⟨i, h⟩ else 1) (toRestrict M J ω)
    have h2 : (M.restrict J).toCoxeterSystem.length
        (if h : i ∈ J then (M.restrict J).simple ⟨i, h⟩ else 1) ≤ 1 := by
      split_ifs
      · rw [← CoxeterMatrix.toCoxeterSystem_simple, length_simple]
      · simp
    have : toRestrict M J (i :: ω) =
        (if h : i ∈ J then (M.restrict J).simple ⟨i, h⟩ else 1) * toRestrict M J ω := by
      simp [toRestrict]
    rw [this, length_cons]
    omega

variable {J} in
/-- A braid move applied to a word with letters in `J` gives a word with letters in `J` with the
same image in the Coxeter group of the restricted matrix. -/
private theorem toRestrict_braidMove {ω ω' : List B} (h : M.BraidMove ω ω')
    (hω : ∀ i ∈ ω, i ∈ J) : toRestrict M J ω = toRestrict M J ω' ∧ ∀ i ∈ ω', i ∈ J := by
  obtain ⟨l, r, i, j, hij, hm, rfl, rfl⟩ := h
  have hm2 : 2 ≤ M i j := by have := M.off_diagonal i j hij; omega
  have hiJ : i ∈ J := hω i (by simp [(mem_alternatingWord_of_two_le hm2).1])
  have hjJ : j ∈ J := hω j (by simp [(mem_alternatingWord_of_two_le hm2).2])
  refine ⟨?_, ?_⟩
  · simp only [toRestrict_append]
    congr 2
    have e1 : braidWord M i j = (alternatingWord (⟨i, hiJ⟩ : J) ⟨j, hjJ⟩
        (M.restrict J ⟨i, hiJ⟩ ⟨j, hjJ⟩)).map Subtype.val := by
      rw [map_alternatingWord]; rfl
    have e2 : braidWord M j i = (alternatingWord (⟨j, hjJ⟩ : J) ⟨i, hiJ⟩
        (M.restrict J ⟨j, hjJ⟩ ⟨i, hiJ⟩)).map Subtype.val := by
      rw [map_alternatingWord]; rfl
    rw [e1, e2, toRestrict_map_val, toRestrict_map_val]
    exact (M.restrict J).toCoxeterSystem.wordProd_braidWord_eq _ _
  · intro c hc
    simp only [mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact hω c (by simp [hc])
    · rcases eq_or_eq_of_mem_alternatingWord hc with rfl | rfl
      · exact hjJ
      · exact hiJ
    · exact hω c (by simp [hc])

variable {J} in
private theorem toRestrict_reflTransGen {ω ω' : List B}
    (h : Relation.ReflTransGen M.BraidMove ω ω') (hω : ∀ i ∈ ω, i ∈ J) :
    toRestrict M J ω = toRestrict M J ω' := by
  suffices toRestrict M J ω = toRestrict M J ω' ∧ ∀ i ∈ ω', i ∈ J from this.1
  induction h with
  | refl => exact ⟨rfl, hω⟩
  | tail _ hs ih =>
    obtain ⟨h1, h2⟩ := toRestrict_braidMove hs ih.2
    exact ⟨ih.1.trans h1, h2⟩

/-- A reduced word for the Coxeter group of the restricted matrix is reduced in `W`. This is the
key to the fact that `W_J` is a Coxeter group; the proof uses Matsumoto's theorem. -/
theorem isReduced_map_val {η : List J} (hη : (M.restrict J).toCoxeterSystem.IsReduced η) :
    cs.IsReduced (η.map Subtype.val) := by
  induction η using List.reverseRecOn with
  | nil => simp [IsReduced]
  | append_singleton η j ih =>
    have hη' : (M.restrict J).toCoxeterSystem.IsReduced η := by simpa using hη.take η.length
    have ih := ih hη'
    by_contra hcon
    set ν := η.map Subtype.val
    have hdesc : cs.IsRightDescent (π ν) j := by
      rw [map_append, map_singleton] at hcon
      unfold IsReduced at hcon
      rw [wordProd_append, wordProd_singleton] at hcon
      rcases cs.length_mul_simple (π ν) j with h | h
      · exact absurd (by rw [h, ih.eq, length_append, length_singleton]) hcon
      · rw [isRightDescent_iff]; exact h
    obtain ⟨p, hp, hpe⟩ := hdesc.exists_wordProd_mul_eq
    have hν'red : cs.IsReduced (ν.eraseIdx p ++ [(j : B)]) := by
      unfold IsReduced
      rw [wordProd_append, ← hpe, wordProd_singleton, simple_mul_simple_cancel_right, ih.eq,
        length_append, length_eraseIdx_of_lt hp, length_singleton]
      have : 0 < ν.length := by omega
      omega
    have hchain := reflTransGen_braidMove_of_isReduced ih hν'red (by
      rw [wordProd_append, ← hpe, wordProd_singleton, simple_mul_simple_cancel_right])
    have hνJ : ∀ i ∈ ν, i ∈ J := by
      intro i hi
      obtain ⟨k, -, rfl⟩ := mem_map.mp hi
      exact k.2
    have heq := toRestrict_reflTransGen hchain hνJ
    rw [toRestrict_map_val, toRestrict_append] at heq
    have hj : toRestrict M J [(j : B)] = (M.restrict J).toCoxeterSystem.simple j := by
      simp [toRestrict]
    rw [hj] at heq
    have h1 : (M.restrict J).toCoxeterSystem.wordProd (η ++ [j]) =
        toRestrict M J (ν.eraseIdx p) := by
      rw [wordProd_append, wordProd_singleton, heq, simple_mul_simple_cancel_right]
    have h2 := length_toRestrict_le (M := M) J (ν.eraseIdx p)
    rw [← h1, hη.eq, length_eraseIdx_of_lt hp] at h2
    simp [ν] at h2
    omega

/-- The simple reflections `sⱼ`, `j ∈ J`, satisfy the relations of `M|_J`. -/
theorem isLiftable_restrict : (M.restrict J).IsLiftable (fun j : J ↦ s (j : B)) :=
  fun i j ↦ cs.simple_mul_simple_pow i j

/-- The homomorphism from the Coxeter group of the restricted matrix `M|_J` to `W`,
`sⱼ ↦ sⱼ`. -/
noncomputable def restrictHom : (M.restrict J).Group →* W :=
  (M.restrict J).toCoxeterSystem.lift ⟨_, cs.isLiftable_restrict J⟩

/-- `restrictHom` maps `sⱼ` to `sⱼ`. -/
theorem restrictHom_simple (j : J) : cs.restrictHom J ((M.restrict J).simple j) = s j :=
  (M.restrict J).toCoxeterSystem.lift_apply_simple (cs.isLiftable_restrict J) j

/-- `restrictHom` on the product of a word. -/
theorem restrictHom_wordProd (η : List J) :
    cs.restrictHom J ((M.restrict J).toCoxeterSystem.wordProd η) = π (η.map Subtype.val) := by
  rw [wordProd, map_list_prod, wordProd, map_map, map_map]
  congr 1
  refine map_congr_left fun j _ ↦ ?_
  simp [restrictHom_simple]

/-- `restrictHom` is injective. -/
theorem restrictHom_injective : Function.Injective (cs.restrictHom J) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨η, hη, rfl⟩ := (M.restrict J).toCoxeterSystem.exists_isReduced g
  rw [restrictHom_wordProd] at hg
  have := (cs.isReduced_map_val J hη).eq
  rw [hg, length_one, length_map] at this
  rw [List.eq_nil_of_length_eq_zero this.symm, wordProd_nil]

/-- The image of `restrictHom` is `W_J`. -/
theorem range_restrictHom : (cs.restrictHom J).range = cs.parabolicSubgroup J := by
  rw [MonoidHom.range_eq_map, ← (M.restrict J).toCoxeterSystem.subgroup_closure_range_simple,
    MonoidHom.map_closure, parabolicSubgroup]
  congr 1
  ext w
  simp [restrictHom_simple]

/-- A word in `J` is reduced for the Coxeter group of `M|_J` if and only if it is reduced
in `W`. -/
theorem isReduced_map_val_iff {η : List J} :
    (M.restrict J).toCoxeterSystem.IsReduced η ↔ cs.IsReduced (η.map Subtype.val) := by
  refine ⟨cs.isReduced_map_val J, fun h ↦ ?_⟩
  unfold IsReduced
  apply le_antisymm ((M.restrict J).toCoxeterSystem.length_wordProd_le η)
  obtain ⟨η', hη', he⟩ := (M.restrict J).toCoxeterSystem.exists_isReduced
    ((M.restrict J).toCoxeterSystem.wordProd η)
  have := congrArg (cs.restrictHom J) he
  rw [restrictHom_wordProd, restrictHom_wordProd] at this
  have h1 := cs.length_wordProd_le (η'.map Subtype.val)
  rw [← this, h.eq, length_map] at h1
  rw [he, hη'.eq]
  simpa using h1

/-- **The standard parabolic subgroup `W_J` is a Coxeter group** with Coxeter matrix `M|_J` and
simple reflections `sⱼ`, `j ∈ J` ([HumC] §5.5 Thm., [BB] Prop. 2.4.1(i)). -/
noncomputable def parabolicCoxeterSystem :
    CoxeterSystem (M.restrict J) (cs.parabolicSubgroup J) :=
  ⟨(MulEquiv.subgroupCongr (cs.range_restrictHom J)).symm.trans
    (MulEquiv.ofBijective (cs.restrictHom J).rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr (cs.restrictHom_injective J),
        MonoidHom.rangeRestrict_surjective _⟩).symm⟩

/-- The simple reflections of `W_J` are the `sⱼ`, `j ∈ J`. -/
@[simp]
theorem coe_parabolicCoxeterSystem_simple (j : J) :
    ((cs.parabolicCoxeterSystem J).simple j : W) = s j :=
  cs.restrictHom_simple J j

/-- Products of words in `W_J`. -/
theorem coe_parabolicCoxeterSystem_wordProd (η : List J) :
    ((cs.parabolicCoxeterSystem J).wordProd η : W) = π (η.map Subtype.val) := by
  rw [wordProd, ← (cs.parabolicSubgroup J).subtype_apply, map_list_prod, wordProd, map_map,
    map_map]
  congr 1
  refine map_congr_left fun j _ ↦ ?_
  simp

/-- The length function of `W_J` (as a Coxeter group) is the restriction of that of `W`
([HumC] §5.5). -/
theorem length_parabolicCoxeterSystem (w : cs.parabolicSubgroup J) :
    (cs.parabolicCoxeterSystem J).length w = ℓ (w : W) := by
  apply le_antisymm
  · obtain ⟨ω, hω, hωJ, he⟩ := exists_isReduced_of_mem_parabolicSubgroup w.2
    lift ω to List J using hωJ
    have : (cs.parabolicCoxeterSystem J).wordProd ω = w :=
      Subtype.ext (by rw [coe_parabolicCoxeterSystem_wordProd, he])
    rw [← this, coe_parabolicCoxeterSystem_wordProd, hω.eq, length_map]
    exact (cs.parabolicCoxeterSystem J).length_wordProd_le ω
  · obtain ⟨η, hη, rfl⟩ := (cs.parabolicCoxeterSystem J).exists_isReduced w
    rw [coe_parabolicCoxeterSystem_wordProd, hη.eq]
    simpa using cs.length_wordProd_le (η.map Subtype.val)

end CoxeterSystem
