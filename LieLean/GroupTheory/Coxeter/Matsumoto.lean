/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.GeometricRepresentation
import LieLean.GroupTheory.Coxeter.Parabolic

/-!
# Matsumoto's theorem

Let `cs : CoxeterSystem M W` be a Coxeter system. A *braid move* on a word replaces a factor
`i j i ⋯` (alternating, of length `mᵢⱼ < ∞`, `i ≠ j`) by `j i j ⋯` (of the same length). Braid moves
do not change the product. **Matsumoto's theorem** states that any two reduced words for the same
element are connected by braid moves ([BB] Thm. 3.3.1; H. Matsumoto, C. R. Acad. Sci. Paris 258
(1964); J. Tits, 1969). Consequently, a function on reduced words that is invariant under braid
moves descends to `W`; in particular, if elements `g i` of a monoid satisfy the braid relations,
then `w ↦ g(i₁) ⋯ g(iₖ)` for a reduced word `i₁ ⋯ iₖ` of `w` is well defined
(`CoxeterSystem.braidLift`), which is how the standard basis of an Iwahori–Hecke algebra and
Lusztig's braid group operators are defined.

## Main definitions

* `CoxeterMatrix.BraidMove`: the braid move relation on words.
* `CoxeterMatrix.IsBraidLiftable`: elements of a monoid satisfying the braid relations.
* `CoxeterSystem.braidLift`: the induced map `W → G`.

## Main results

* `CoxeterSystem.exists_braidMove_of_isLeftDescent`: if `a ≠ b` are left descents of `w`, then
  `mₐᵦ < ∞` and `w` has reduced words beginning with `a` and with `b` that differ by one braid move.
* `CoxeterSystem.reflTransGen_braidMove_of_isReduced`: **Matsumoto's theorem**.
* `CoxeterSystem.exists_eq_of_braidMove`: a braid-invariant function on reduced words descends
  to `W`.
* `CoxeterSystem.braidLift_wordProd`, `CoxeterSystem.braidLift_mul`: properties of `braidLift`.

## Implementation notes

The proof is the standard induction on the length ([BB] §3.3): if two reduced words for `w`
start with different letters `a ≠ b`, both are left descents of `w`. Writing `w = x u` with
`x ∈ W_{a,b}` and `u` without left descents in `{a, b}` (the parabolic decomposition,
`LieLean.GroupTheory.Coxeter.Parabolic`), `x` has both `a` and `b` as left descents; reduced words
in two letters are alternating, and since alternating words of length `≤ mₐᵦ` are reduced
(`CoxeterSystem.isReduced_alternatingWord`, which relies on the geometric representation) while
longer ones are not, `ℓ(x) = mₐᵦ`. We reconstructed this argument; [BB] phrase the key step via
the "longest element of a dihedral parabolic subgroup".

## References

* [BB] A. Björner, F. Brenti, *Combinatorics of Coxeter groups*, GTM 231, Springer 2005, §3.3.
* H. Matsumoto, *Générateurs et relations des groupes de Weyl généralisés*, C. R. Acad. Sci.
  Paris **258** (1964), 3419–3422.
-/

open List

namespace CoxeterMatrix

variable {B : Type*} (M : CoxeterMatrix B)

/-- A **braid move** replaces a factor `CoxeterSystem.braidWord M i j` of a word (the
alternating word `⋯ i j` of length `mᵢⱼ`) by `CoxeterSystem.braidWord M j i`, for `i ≠ j` with
`mᵢⱼ < ∞` ([BB] §3.3). -/
def BraidMove (ω ω' : List B) : Prop :=
  ∃ (l r : List B) (i j : B), i ≠ j ∧ M i j ≠ 0 ∧
    ω = l ++ CoxeterSystem.braidWord M i j ++ r ∧ ω' = l ++ CoxeterSystem.braidWord M j i ++ r

variable {M}

/-- The braid move relation is symmetric. -/
theorem BraidMove.symm {ω ω' : List B} (h : M.BraidMove ω ω') : M.BraidMove ω' ω := by
  obtain ⟨l, r, i, j, hij, hm, h₁, h₂⟩ := h
  exact ⟨l, r, j, i, hij.symm, by rwa [M.symmetric], h₂, h₁⟩

/-- Braid moves can be performed after a prefix. -/
theorem BraidMove.cons {ω ω' : List B} (h : M.BraidMove ω ω') (a : B) :
    M.BraidMove (a :: ω) (a :: ω') := by
  obtain ⟨l, r, i, j, hij, hm, rfl, rfl⟩ := h
  exact ⟨a :: l, r, i, j, hij, hm, rfl, rfl⟩

/-- Braid moves can be performed before a suffix. -/
theorem BraidMove.append_right {ω ω' : List B} (h : M.BraidMove ω ω') (γ : List B) :
    M.BraidMove (ω ++ γ) (ω' ++ γ) := by
  obtain ⟨l, r, i, j, hij, hm, rfl, rfl⟩ := h
  exact ⟨l, r ++ γ, i, j, hij, hm, by simp, by simp⟩

/-- The basic braid move `braidWord M i j ++ γ → braidWord M j i ++ γ`. -/
theorem braidMove_braidWord {i j : B} (hij : i ≠ j) (hm : M i j ≠ 0) (γ : List B) :
    M.BraidMove (CoxeterSystem.braidWord M i j ++ γ) (CoxeterSystem.braidWord M j i ++ γ) :=
  ⟨[], γ, i, j, hij, hm, rfl, rfl⟩

/-- Braid moves preserve the length of a word. -/
theorem BraidMove.length_eq {ω ω' : List B} (h : M.BraidMove ω ω') : ω.length = ω'.length := by
  obtain ⟨l, r, i, j, hij, hm, rfl, rfl⟩ := h
  simp [M.symmetric i j]

/-- Being connected by braid moves is a symmetric relation. -/
theorem reflTransGen_braidMove_symm {ω ω' : List B}
    (h : Relation.ReflTransGen M.BraidMove ω ω') : Relation.ReflTransGen M.BraidMove ω' ω :=
  by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact .head hs.symm ih

end CoxeterMatrix

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd
local prefix:100 "ℓ " => cs.length

/-- The reverse of an alternating word. -/
theorem reverse_alternatingWord (i j : B) (k : ℕ) :
    (alternatingWord i j k).reverse =
      if Even k then alternatingWord j i k else alternatingWord i j k := by
  induction k generalizing i j with
  | zero => simp [alternatingWord]
  | succ k ih =>
    have e : (alternatingWord i j (k + 1)).reverse = j :: (alternatingWord j i k).reverse := by
      rw [alternatingWord_succ, concat_eq_append, reverse_append]
      simp
    rw [e, ih]
    by_cases hk : Even k
    · have hk' : ¬Even (k + 1) := by simp [Nat.even_add_one, hk]
      simp only [hk, hk', ↓reduceIte, alternatingWord_succ' i j k]
    · have hk' : Even (k + 1) := by simp [Nat.even_add_one, hk]
      simp only [hk, hk', ↓reduceIte, alternatingWord_succ' j i k]

variable {cs}

/-- Braid moves do not change the product of a word. -/
theorem wordProd_eq_of_braidMove {ω ω' : List B} (h : M.BraidMove ω ω') : π ω = π ω' := by
  obtain ⟨l, r, i, j, -, -, rfl, rfl⟩ := h
  simp only [wordProd_append, wordProd_braidWord_eq]

/-- Braid moves preserve reducedness. -/
theorem IsReduced.of_braidMove {ω ω' : List B} (hω : cs.IsReduced ω) (h : M.BraidMove ω ω') :
    cs.IsReduced ω' := by
  unfold IsReduced
  rw [← wordProd_eq_of_braidMove h, hω.eq, h.length_eq]

/-- A reduced word with letters in `{a, b}` starting with `a` is alternating. -/
theorem IsReduced.eq_reverse_alternatingWord {a b : B} {ω : List B} (hω : cs.IsReduced ω)
    (hab : ∀ c ∈ ω, c = a ∨ c = b) (hhead : ω.head? = some a) :
    ω = (alternatingWord b a ω.length).reverse := by
  induction ω generalizing a b with
  | nil => simp at hhead
  | cons x ω ih =>
    simp only [head?_cons, Option.some.injEq] at hhead
    subst hhead
    rcases ω with _ | ⟨y, ω⟩
    · simp [alternatingWord]
    have hy : y = b := by
      rcases hab y (by simp) with h | h
      · exfalso
        subst h
        have := hω.take 2
        simp [IsReduced, wordProd] at this
      · exact h
    subst hy
    have hω' : cs.IsReduced (y :: ω) := by simpa using hω.drop 1
    have := ih hω' (fun c hc ↦ (hab c (mem_cons_of_mem _ hc)).symm) rfl
    rw [this, length_cons, length_cons, length_reverse, length_alternatingWord,
      alternatingWord_succ y x (ω.length + 1), concat_eq_append, reverse_append]
    simp

/-- A reduced word `c :: η` has `c` as a left descent. -/
theorem IsReduced.isLeftDescent_cons {c : B} {η : List B} (h : cs.IsReduced (c :: η)) :
    cs.IsLeftDescent (π (c :: η)) c := by
  unfold IsLeftDescent
  rw [wordProd_cons, simple_mul_simple_cancel_left, ← wordProd_cons, h.eq]
  have := cs.length_wordProd_le η
  simp only [length_cons]
  omega

/-- The key step of Matsumoto's theorem ([BB] proof of Thm. 3.3.1(ii)): if `a ≠ b` are both left
descents of `w`, then `mₐᵦ < ∞` and `w` has reduced words `a ⋯ γ` and `b ⋯ γ` that differ by one
braid move (they begin with the two alternating words of length `mₐᵦ`). -/
theorem exists_braidMove_of_isLeftDescent {w : W} {a b : B} (hab : a ≠ b)
    (ha : cs.IsLeftDescent w a) (hb : cs.IsLeftDescent w b) :
    ∃ P₀ Q₀ γ : List B, M.BraidMove (a :: (P₀ ++ γ)) (b :: (Q₀ ++ γ)) ∧
      cs.IsReduced (a :: (P₀ ++ γ)) ∧ π (a :: (P₀ ++ γ)) = w ∧ π (b :: (Q₀ ++ γ)) = w := by
  set J : Set B := {a, b} with hJ
  obtain ⟨x, hx, u, hu, rfl⟩ := cs.exists_mul_eq_of_forall_not_isLeftDescent J w
  have hlen := length_mul_of_forall_not_isLeftDescent hu hx
  have hdesc : ∀ c ∈ J, cs.IsLeftDescent (x * u) c → cs.IsLeftDescent x c := by
    intro c hc h
    have h' := length_mul_of_forall_not_isLeftDescent hu
      (Subgroup.mul_mem _ (simple_mem_parabolicSubgroup hc) hx)
    unfold IsLeftDescent at h ⊢
    rw [← mul_assoc, h', hlen] at h
    omega
  have hxa := hdesc a (by simp [hJ]) ha
  have hxb := hdesc b (by simp [hJ]) hb
  -- reduced words for `x` starting with `a`, resp. `b`
  have hword : ∀ c ∈ J, cs.IsLeftDescent x c →
      ∃ η, cs.IsReduced (c :: η) ∧ (∀ d ∈ c :: η, d ∈ J) ∧ π (c :: η) = x := by
    intro c hc hxc
    obtain ⟨η, hη, hηJ, hηe⟩ := exists_isReduced_of_mem_parabolicSubgroup
      (Subgroup.mul_mem _ (simple_mem_parabolicSubgroup hc) hx)
    refine ⟨η, ?_, ?_, by rw [wordProd_cons, hηe, simple_mul_simple_cancel_left]⟩
    · unfold IsReduced
      rw [wordProd_cons, hηe, simple_mul_simple_cancel_left, length_cons, ← hη.eq, hηe]
      rw [isLeftDescent_iff] at hxc
      omega
    · intro d hd
      rcases mem_cons.mp hd with rfl | hd
      · exact hc
      · exact hηJ d hd
  obtain ⟨ηa, hηa, hηaJ, hηae⟩ := hword a (by simp [hJ]) hxa
  obtain ⟨ηb, hηb, hηbJ, hηbe⟩ := hword b (by simp [hJ]) hxb
  have hka : (a :: ηa).length = ℓ x := by rw [← hηa.eq, hηae]
  have hkb : (b :: ηb).length = ℓ x := by rw [← hηb.eq, hηbe]
  have hPa := hηa.eq_reverse_alternatingWord (a := a) (b := b)
    (fun c hc ↦ by simpa [hJ] using hηaJ c hc) rfl
  have hPb := hηb.eq_reverse_alternatingWord (a := b) (b := a)
    (fun c hc ↦ by simpa [hJ, or_comm] using hηbJ c hc) rfl
  rw [hka] at hPa
  rw [hkb] at hPb
  -- `ℓ(x) = mₐᵦ`
  have hm0 : M a b ≠ 0 ∧ M a b ≤ ℓ x := by
    by_contra hcon
    have hred := cs.isReduced_alternatingWord a b (k := ℓ x + 1) (by omega)
    have e : (alternatingWord a b (ℓ x + 1)).reverse = b :: (a :: ηa) := by
      rw [hPa, alternatingWord_succ, concat_eq_append, reverse_append]
      simp
    have h2 := hred.reverse
    rw [e] at h2
    unfold IsReduced at h2
    rw [wordProd_cons, hηae, length_cons, hka] at h2
    rw [isLeftDescent_iff] at hxb
    omega
  have hkm : ℓ x = M a b := by
    refine le_antisymm ?_ hm0.2
    by_contra hlt
    apply cs.not_isReduced_alternatingWord b a (m := ℓ x) (by rw [M.symmetric]; exact hm0.1)
      (by rw [M.symmetric]; omega)
    have := hηa.reverse
    rwa [hPa, reverse_reverse] at this
  -- the braid move
  obtain ⟨γ, hγ, rfl⟩ := cs.exists_isReduced u
  refine ⟨ηa, ηb, γ, ?_, ?_, by rw [← cons_append, wordProd_append, hηae],
    by rw [← cons_append, wordProd_append, hηbe]⟩
  · rw [← cons_append, ← cons_append, hPa, hPb, hkm, reverse_alternatingWord,
      reverse_alternatingWord]
    have hm : M b a = M a b := M.symmetric b a
    by_cases he : Even (M a b)
    · simp only [he, ↓reduceIte]
      have := CoxeterMatrix.braidMove_braidWord (M := M) hab hm0.1 γ
      rwa [braidWord, braidWord, hm] at this
    · simp only [he, ↓reduceIte]
      have := CoxeterMatrix.braidMove_braidWord (M := M) hab.symm (by rw [hm]; exact hm0.1) γ
      rwa [braidWord, braidWord, hm] at this
  · unfold IsReduced
    rw [← cons_append, wordProd_append, hηae, hlen, hγ.eq, length_append, hka]

/-- **Matsumoto's theorem** ([BB] Thm. 3.3.1, Matsumoto 1964, Tits 1969):
any two reduced words for the same element of `W` are connected by a sequence of braid moves. -/
theorem reflTransGen_braidMove_of_isReduced {ω ω' : List B} (hω : cs.IsReduced ω)
    (hω' : cs.IsReduced ω') (h : π ω = π ω') : Relation.ReflTransGen M.BraidMove ω ω' := by
  induction hn : ω.length generalizing ω ω' with
  | zero =>
    have h1 : ω = [] := List.length_eq_zero_iff.mp hn
    have h2 : ω' = [] := by
      rw [← List.length_eq_zero_iff, ← hω'.eq, ← h, hω.eq, hn]
    rw [h1, h2]
  | succ n ih =>
    obtain ⟨a, α, rfl⟩ := exists_cons_of_length_eq_add_one hn
    have hlen' : ω'.length = n + 1 := by rw [← hω'.eq, ← h, hω.eq, hn]
    obtain ⟨b, β, rfl⟩ := exists_cons_of_length_eq_add_one hlen'
    have hα : cs.IsReduced α := by simpa using hω.drop 1
    have hβ : cs.IsReduced β := by simpa using hω'.drop 1
    have hlα : α.length = n := by simpa using hn
    by_cases hab : a = b
    · subst hab
      have : π α = π β := by
        rw [wordProd_cons, wordProd_cons] at h
        exact mul_left_cancel h
      exact Relation.ReflTransGen.lift (List.cons a) (fun _ _ hm ↦ hm.cons a) _ _
        (ih hα hβ this hlα)
    · obtain ⟨P₀, Q₀, γ, hmove, hPred, hPe, hQe⟩ :=
        exists_braidMove_of_isLeftDescent hab hω.isLeftDescent_cons
          (h ▸ hω'.isLeftDescent_cons)
      have hQred := hPred.of_braidMove hmove
      have h1 : Relation.ReflTransGen M.BraidMove (a :: α) (a :: (P₀ ++ γ)) := by
        have hP : cs.IsReduced (P₀ ++ γ) := by simpa using hPred.drop 1
        have : π α = π (P₀ ++ γ) := by
          rw [wordProd_cons] at hPe
          rw [wordProd_cons] at hPe
          exact (mul_left_cancel hPe).symm
        exact Relation.ReflTransGen.lift (List.cons a) (fun _ _ hm ↦ hm.cons a) _ _
          (ih hα hP this hlα)
      have h2 : Relation.ReflTransGen M.BraidMove (b :: β) (b :: (Q₀ ++ γ)) := by
        have hQ : cs.IsReduced (Q₀ ++ γ) := by simpa using hQred.drop 1
        have : π β = π (Q₀ ++ γ) := by
          rw [h, wordProd_cons] at hQe
          rw [wordProd_cons] at hQe
          exact (mul_left_cancel hQe).symm
        have hlβ : β.length = n := by simpa using hlen'
        exact Relation.ReflTransGen.lift (List.cons b) (fun _ _ hm ↦ hm.cons b) _ _
          (ih hβ hQ this (by rw [hlβ]))
      exact (h1.tail hmove).trans (CoxeterMatrix.reflTransGen_braidMove_symm h2)

/-- Braid moves connect reduced words to reduced words. -/
theorem IsReduced.of_reflTransGen_braidMove {ω ω' : List B} (hω : cs.IsReduced ω)
    (h : Relation.ReflTransGen M.BraidMove ω ω') : cs.IsReduced ω' := by
  induction h with
  | refl => exact hω
  | tail _ hs ih => exact ih.of_braidMove hs

/-- A function on reduced words that is invariant under braid moves is constant on braid
classes of reduced words. -/
theorem eq_of_reflTransGen_braidMove {α : Sort*} {f : List B → α}
    (hf : ∀ ω ω', cs.IsReduced ω → M.BraidMove ω ω' → f ω = f ω') {ω ω' : List B}
    (hω : cs.IsReduced ω) (h : Relation.ReflTransGen M.BraidMove ω ω') : f ω = f ω' := by
  induction h with
  | refl => rfl
  | tail hab hs ih => exact ih.trans (hf _ _ (hω.of_reflTransGen_braidMove hab) hs)

/-- **Matsumoto's theorem**, functional form: a function on reduced words that is invariant under
braid moves descends to a function on `W`. -/
theorem exists_eq_of_braidMove {α : Sort*} (f : List B → α)
    (hf : ∀ ω ω', cs.IsReduced ω → M.BraidMove ω ω' → f ω = f ω') :
    ∃ F : W → α, ∀ ω, cs.IsReduced ω → F (π ω) = f ω := by
  refine ⟨fun w ↦ f (cs.exists_isReduced w).choose, fun ω hω ↦ ?_⟩
  obtain ⟨hω₀, he⟩ := (cs.exists_isReduced (π ω)).choose_spec
  exact eq_of_reflTransGen_braidMove hf hω₀ (reflTransGen_braidMove_of_isReduced hω₀ hω he.symm)

end CoxeterSystem

namespace CoxeterMatrix

variable {B : Type*} (M : CoxeterMatrix B)

/-- The elements `g i` of a monoid satisfy the braid relations of `M`:
`g i g j g i ⋯ = g j g i g j ⋯` (`mᵢⱼ` factors on each side) whenever `i ≠ j` and `mᵢⱼ < ∞`. -/
def IsBraidLiftable {G : Type*} [Monoid G] (g : B → G) : Prop :=
  ∀ i j, i ≠ j → M i j ≠ 0 →
    ((CoxeterSystem.braidWord M i j).map g).prod = ((CoxeterSystem.braidWord M j i).map g).prod

end CoxeterMatrix

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd
local prefix:100 "ℓ " => cs.length

section braidLift

variable {G : Type*} [Monoid G]

/-- The map `W → G`, `w ↦ g(i₁) ⋯ g(iₖ)` for a (chosen) reduced word `i₁ ⋯ iₖ` of `w`. If the
`g i` satisfy the braid relations, this does not depend on the reduced word
(`CoxeterSystem.braidLift_wordProd`, by Matsumoto's theorem). This is how, e.g., the elements
`T_w` of an Iwahori–Hecke algebra or Lusztig's braid group operators `T_w` are defined. -/
noncomputable def braidLift (g : B → G) (w : W) : G :=
  ((cs.exists_isReduced w).choose.map g).prod

variable {cs} {g : B → G}

/-- If the `g i` satisfy the braid relations, then `braidLift g (π ω) = g(i₁) ⋯ g(iₖ)` for every
reduced word `ω = i₁ ⋯ iₖ` (Matsumoto's theorem). -/
theorem braidLift_wordProd (hg : M.IsBraidLiftable g) {ω : List B} (hω : cs.IsReduced ω) :
    cs.braidLift g (π ω) = (ω.map g).prod := by
  obtain ⟨hω₀, he⟩ := (cs.exists_isReduced (π ω)).choose_spec
  refine eq_of_reflTransGen_braidMove (f := fun ω ↦ (ω.map g).prod) ?_ hω₀
    (reflTransGen_braidMove_of_isReduced hω₀ hω he.symm)
  rintro _ _ - ⟨l, r, i, j, hij, hm, rfl, rfl⟩
  simp only [map_append, prod_append, hg i j hij hm]

variable (cs g) in
/-- `braidLift g 1 = 1`. -/
theorem braidLift_one : cs.braidLift g 1 = 1 := by
  obtain ⟨hω, he⟩ := (cs.exists_isReduced (1 : W)).choose_spec
  have : (cs.exists_isReduced (1 : W)).choose = [] := by
    rw [← List.length_eq_zero_iff, ← hω.eq, ← he, length_one]
  rw [braidLift, this, map_nil, prod_nil]

variable (cs g) in
/-- `braidLift g sᵢ = g i`. -/
theorem braidLift_simple (i : B) : cs.braidLift g (s i) = g i := by
  obtain ⟨hω, he⟩ := (cs.exists_isReduced (s i)).choose_spec
  obtain ⟨j, hj⟩ : ∃ j, (cs.exists_isReduced (s i)).choose = [j] := by
    apply List.length_eq_one_iff.mp
    rw [← hω.eq, ← he, length_simple]
  rw [hj, wordProd_singleton] at he
  rw [braidLift, hj, cs.simple_injective he]
  simp

/-- If lengths add, `braidLift` is multiplicative. -/
theorem braidLift_mul (hg : M.IsBraidLiftable g) {u v : W} (h : ℓ (u * v) = ℓ u + ℓ v) :
    cs.braidLift g (u * v) = cs.braidLift g u * cs.braidLift g v := by
  obtain ⟨ωu, hu, rfl⟩ := cs.exists_isReduced u
  obtain ⟨ωv, hv, rfl⟩ := cs.exists_isReduced v
  have huv : cs.IsReduced (ωu ++ ωv) := by
    unfold IsReduced
    rw [wordProd_append, h, hu.eq, hv.eq, length_append]
  rw [← wordProd_append, braidLift_wordProd hg huv, braidLift_wordProd hg hu,
    braidLift_wordProd hg hv, map_append, prod_append]

/-- `braidLift g (w sᵢ) = braidLift g w * g i` if `ℓ(w sᵢ) > ℓ(w)`. -/
theorem braidLift_mul_simple (hg : M.IsBraidLiftable g) {w : W} {i : B}
    (h : ¬cs.IsRightDescent w i) : cs.braidLift g (w * s i) = cs.braidLift g w * g i := by
  rw [braidLift_mul hg (by rw [(cs.not_isRightDescent_iff).mp h, length_simple]),
    braidLift_simple]

/-- `braidLift g (sᵢ w) = g i * braidLift g w` if `ℓ(sᵢ w) > ℓ(w)`. -/
theorem braidLift_simple_mul (hg : M.IsBraidLiftable g) {w : W} {i : B}
    (h : ¬cs.IsLeftDescent w i) : cs.braidLift g (s i * w) = g i * cs.braidLift g w := by
  rw [braidLift_mul hg (by rw [(cs.not_isLeftDescent_iff).mp h, length_simple, add_comm]),
    braidLift_simple]

end braidLift

end CoxeterSystem
