/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingComponent

/-!
# Component isomorphisms from mixed root words

A connected component of the crystal of paths is the set of values of mixed root words
(`mem_component_iff_rootWord`). This file shows that two components are isomorphic, with
`π ↦ π'`, as soon as the same words vanish on `π` and `π'` and the same pairs of words agree
on `π` and `π'`. This is the form in which Littelmann proves Theorem 6.3: the map
`a(π_λ * π_μ) ↦ a(π_ν)` is well defined and injective by (6.1).

## Main results

* `rootWord_wt_sub_eq`: a mixed root word changes the weight of every path by the same
  amount.
* `invWord`, `rootWord_invWord_eq_some_iff`: the inverse of a mixed word (reverse it and
  exchange raising with lowering) undoes it.
* `componentIso_of_rootWord`: the word-relation criterion for `ComponentIso`.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), proof of Theorem 6.3, pp. 517–518 (the equivalences (6.1) and (6.2)). The
crystal-isomorphism packaging (including `ε`, via seminormality) is reconstructed.
-/

open Set

namespace LittelmannPath

variable {ι X V : Type*} [AddCommGroup X] [AddCommGroup V] [Module ℝ V]
  {D : CartanDatum ι X} {S : D.PathSpace ℝ V}

/-- A mixed root word changes the weight of every path by the same amount. -/
theorem rootWord_wt_sub_eq {l : List (ι ⊕ ι)} {π π' η η' : LittelmannPath S}
    (h : rootWord l π = some η) (h' : rootWord l π' = some η') :
    η.wt - π.wt = η'.wt - π'.wt := by
  induction l generalizing π π' with
  | nil =>
    cases h
    cases h'
    simp
  | cons a l ih =>
    obtain ⟨ρ, ha, hl⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ρ', ha', hl'⟩ := Option.bind_eq_some_iff.mp h'
    have hstep : ρ.wt - π.wt = ρ'.wt - π'.wt := by
      cases a with
      | inl i =>
        rw [wt_of_e_eq_some ha, wt_of_e_eq_some ha']
        abel
      | inr i =>
        have h1 : ρ.wt = π.wt - D.root i := (crystal S).wt_f ha
        have h2 : ρ'.wt = π'.wt - D.root i := (crystal S).wt_f ha'
        rw [h1, h2]
        abel
    calc η.wt - π.wt = (η.wt - ρ.wt) + (ρ.wt - π.wt) := by abel
      _ = (η'.wt - ρ'.wt) + (ρ'.wt - π'.wt) := by rw [ih hl hl', hstep]
      _ = η'.wt - π'.wt := by abel

/-- Mixed words compose in their left-to-right order, for an arbitrary path space. -/
theorem rootWord_append_eq_bind (u v : List (ι ⊕ ι)) (π : LittelmannPath S) :
    rootWord (u ++ v) π = (rootWord u π).bind (rootWord v) := by
  induction u generalizing π with
  | nil => rfl
  | cons a u ih =>
    simp only [List.cons_append, rootWord]
    cases rootStep a π with
    | none => rfl
    | some ρ => exact ih ρ

/-- Appending one letter applies one more root operator. -/
theorem rootWord_append_singleton (u : List (ι ⊕ ι)) (a : ι ⊕ ι) (π : LittelmannPath S) :
    rootWord (u ++ [a]) π = (rootWord u π).bind (rootStep a) := by
  rw [rootWord_append_eq_bind]
  congr 1
  funext ρ
  change (rootStep a ρ).bind (rootWord []) = rootStep a ρ
  cases rootStep a ρ <;> rfl

/-- The crystal iterate `ẽᵢⁿ` is the mixed word consisting of `n` raising letters. -/
theorem eIter_eq_rootWord (i : ι) (n : ℕ) (π : LittelmannPath S) :
    (crystal S).eIter i n π = rootWord (List.replicate n (.inl i)) π := by
  induction n generalizing π with
  | zero => rfl
  | succ n ih =>
    change ((crystal S).e i π).bind ((crystal S).eIter i n) =
      (rootStep (.inl i) π).bind (rootWord (List.replicate n (.inl i)))
    congr 1
    funext ρ
    exact ih ρ

/-- Raising and lowering the same color are inverse letters. -/
theorem rootStep_eq_some_iff_swap (a : ι ⊕ ι) {π η : LittelmannPath S} :
    rootStep a π = some η ↔ rootStep a.swap η = some π := by
  cases a with
  | inl i => exact f_eq_some_iff.symm
  | inr i => exact f_eq_some_iff

/-- The inverse of a mixed root word: reverse it and exchange raising with lowering. -/
def invWord (l : List (ι ⊕ ι)) : List (ι ⊕ ι) := (l.map Sum.swap).reverse

/-- The inverse word undoes the word, in both directions. -/
theorem rootWord_invWord_eq_some_iff (l : List (ι ⊕ ι)) {π η : LittelmannPath S} :
    rootWord l π = some η ↔ rootWord (invWord l) η = some π := by
  induction l generalizing π with
  | nil =>
    change some π = some η ↔ some η = some π
    exact eq_comm
  | cons a l ih =>
    have hinv : invWord (a :: l) = invWord l ++ [a.swap] := by
      simp [invWord]
    rw [hinv, rootWord_append_singleton]
    constructor
    · intro h
      obtain ⟨ρ, ha, hl⟩ := Option.bind_eq_some_iff.mp h
      exact Option.bind_eq_some_iff.mpr ⟨ρ, ih.mp hl, (rootStep_eq_some_iff_swap a).mp ha⟩
    · intro h
      obtain ⟨ρ, hl, ha⟩ := Option.bind_eq_some_iff.mp h
      exact Option.bind_eq_some_iff.mpr ⟨ρ, (rootStep_eq_some_iff_swap a).mpr ha, ih.mpr hl⟩

/-- Two nonnegative values of `WithBot ℤ` with the same natural lower bounds are equal. -/
theorem withBot_eq_of_natCast_le_iff {x y : WithBot ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ∀ n : ℕ, (n : WithBot ℤ) ≤ x ↔ (n : WithBot ℤ) ≤ y) : x = y := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd hx (by simp)
  | coe a =>
    induction y using WithBot.recBotCoe with
    | bot => exact absurd hy (by simp)
    | coe b =>
      have ha : 0 ≤ a := by exact_mod_cast hx
      have hb : 0 ≤ b := by exact_mod_cast hy
      have h1 := (h a.toNat).mp (by rw [← WithBot.coe_natCast, Int.toNat_of_nonneg ha])
      have h2 := (h b.toNat).mpr (by rw [← WithBot.coe_natCast, Int.toNat_of_nonneg hb])
      rw [← WithBot.coe_natCast, Int.toNat_of_nonneg ha, WithBot.coe_le_coe] at h1
      rw [← WithBot.coe_natCast, Int.toNat_of_nonneg hb, WithBot.coe_le_coe] at h2
      rw [le_antisymm h2 h1]

end LittelmannPath

namespace Matrix.Realization.LSGeneralClass

open LittelmannPath

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- **Word-relation criterion for component isomorphisms.** If `π` and `π'` have the same
weight, the same mixed words vanish on them, and the same pairs of words agree on them, then
`B(π) ≅ B(π')` with `π ↦ π'`. The isomorphism sends `D π` to `D π'`. -/
theorem componentIso_of_rootWord {π π' : LittelmannPath (P.pathSpace hA)}
    (hwt : π.wt = π'.wt)
    (hnone : ∀ u, rootWord u π = none ↔ rootWord u π' = none)
    (heq : ∀ u v, rootWord u π = rootWord v π ↔ rootWord u π' = rootWord v π') :
    ComponentIso π π' := by
  classical
  let g : LittelmannPath (P.pathSpace hA) → LittelmannPath (P.pathSpace hA) := fun η =>
    if h : ∃ u, rootWord u π = some η then (rootWord h.choose π').getD η else η
  have key : ∀ u η, rootWord u π = some η → rootWord u π' = some (g η) := by
    intro u η hu
    have h : ∃ u, rootWord u π = some η := ⟨u, hu⟩
    have h1 := (heq _ _).mp (h.choose_spec.trans hu.symm)
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp (fun hn => by
      rw [(hnone u).mpr hn] at hu
      cases hu)
    simp only [g, h, ↓reduceDIte, h1, hx, Option.getD_some]
  have hmaps : MapsTo g π.component π'.component := by
    intro η hη
    obtain ⟨u, hu⟩ := (mem_component_iff_rootWord _ _).mp hη
    exact (mem_component_iff_rootWord _ _).mpr ⟨u, key u η hu⟩
  have hinj : InjOn g π.component := by
    intro η₁ h₁ η₂ h₂ hg
    obtain ⟨u₁, hu₁⟩ := (mem_component_iff_rootWord _ _).mp h₁
    obtain ⟨u₂, hu₂⟩ := (mem_component_iff_rootWord _ _).mp h₂
    have h := (heq u₁ u₂).mpr (by rw [key u₁ η₁ hu₁, key u₂ η₂ hu₂, hg])
    rw [hu₁, hu₂] at h
    exact Option.some_injective _ h
  have hsurj : SurjOn g π.component π'.component := by
    intro y hy
    obtain ⟨v, hv⟩ := (mem_component_iff_rootWord _ _).mp hy
    obtain ⟨η, hη⟩ := Option.ne_none_iff_exists'.mp (fun hn => by
      rw [(hnone v).mp hn] at hv
      cases hv)
    refine ⟨η, (mem_component_iff_rootWord _ _).mpr ⟨v, hη⟩, ?_⟩
    have h := key v η hη
    rw [hv] at h
    exact (Option.some_injective _ h).symm
  have hb : BijOn g π.component π'.component := ⟨hmaps, hinj, hsurj⟩
  have hstep : ∀ η ∈ π.component, ∀ a : ι ⊕ ι, rootStep a (g η) = (rootStep a η).map g := by
    intro η hη a
    obtain ⟨u, hu⟩ := (mem_component_iff_rootWord _ _).mp hη
    have hu' := key u η hu
    cases ha : rootStep a η with
    | none =>
      have h1 : rootWord (u ++ [a]) π = none := by
        rw [rootWord_append_singleton, hu]
        exact ha
      have h2 := (hnone _).mp h1
      rw [rootWord_append_singleton, hu'] at h2
      exact h2
    | some η'' =>
      have h1 : rootWord (u ++ [a]) π = some η'' := by
        rw [rootWord_append_singleton, hu]
        exact ha
      have h2 := key _ _ h1
      rw [rootWord_append_singleton, hu'] at h2
      exact h2
  have hwtg : ∀ η ∈ π.component, (g η).wt = η.wt := by
    intro η hη
    obtain ⟨u, hu⟩ := (mem_component_iff_rootWord _ _).mp hη
    have h := rootWord_wt_sub_eq (key u η hu) hu
    rw [hwt] at h
    exact sub_left_injective h
  have hεg : ∀ η ∈ π.component, ∀ i, ε i (g η) = ε i η := by
    intro η hη i
    obtain ⟨u, hu⟩ := (mem_component_iff_rootWord _ _).mp hη
    have hu' := key u η hu
    have hiter : ∀ n : ℕ, ((crystal (P.pathSpace hA)).eIter i n (g η)).isSome ↔
        ((crystal (P.pathSpace hA)).eIter i n η).isSome := by
      intro n
      have h := hnone (u ++ List.replicate n (.inl i))
      rw [rootWord_append_eq_bind, rootWord_append_eq_bind, hu, hu'] at h
      simp only [Option.bind_some] at h
      rw [eIter_eq_rootWord, eIter_eq_rootWord, Option.isSome_iff_ne_none,
        Option.isSome_iff_ne_none]
      exact not_congr h.symm
    have hsn := isSeminormal_crystal (P.pathSpace hA)
    have h0 : ∀ ζ : LittelmannPath (P.pathSpace hA), (0 : WithBot ℤ) ≤ ε i ζ := by
      intro ζ
      have := ((hsn i ζ 0).1).mp rfl
      exact_mod_cast this
    exact withBot_eq_of_natCast_le_iff (h0 _) (h0 _) fun n =>
      ((hsn i (g η) n).1.symm.trans (hiter n)).trans ((hsn i η n).1)
  refine ⟨{
    toEquiv := hb.equiv g
    wt_map := fun b => hwtg b.1 b.2
    ε_map := fun i b => hεg b.1 b.2 i
    e_map := ?_
    f_map := ?_ }, ?_⟩
  · intro i b
    apply Option.map_injective Subtype.val_injective
    simp only [componentCrystal, Crystal.restrict_e, Option.map_map]
    change e i (g b.1) = Option.map (g ∘ Subtype.val) (π.componentCrystal.e i b)
    rw [← Option.map_map, componentCrystal, Crystal.restrict_e]
    exact hstep b.1 b.2 (.inl i)
  · intro i b
    apply Option.map_injective Subtype.val_injective
    simp only [componentCrystal, Crystal.restrict_f, Option.map_map]
    change f i (g b.1) = Option.map (g ∘ Subtype.val) (π.componentCrystal.f i b)
    rw [← Option.map_map, componentCrystal, Crystal.restrict_f]
    exact hstep b.1 b.2 (.inr i)
  · have h := key [] π rfl
    exact (Option.some_injective _ h).symm

end Matrix.Realization.LSGeneralClass
