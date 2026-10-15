/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.CrystalBaseIsomorphism
import LieLean.Algebra.QuantumGroup.CompleteReducibility
import Mathlib.Data.Finsupp.Interval

/-!
# Uniqueness of crystal bases

This file proves the uniqueness theorem for crystal bases ([HK] Thm. 5.2.1): if `M` is a module in
`𝒪_int` and `(L, B)` is a crystal base of `M`, there is an isomorphism `Φ : ⊕ⱼ V(λⱼ) ≃ M` of
`U`-modules from a direct sum of irreducible highest weight modules with dominant highest weights
which maps `⊕ⱼ L(λⱼ)` onto `L` and induces a bijection `⊔ⱼ B(λⱼ) ≃ B`.

## Main definitions

* `GrandLoop.summandsAbove Λ j`: the summands `j'` with `λ_{j'} ∈ λⱼ + Q₊`.
* `GrandLoop.SplitStage L B`: a set `U` of summands together with an automorphism `Φ` of
  `⊕ⱼ V(λⱼ)`, acting only on the summands in `U`, such that the pullback of `(L, B)` along `Φ`
  agrees with `(⊕ⱼ L(λⱼ), ⊔ⱼ B(λⱼ))` on the summands in `U`.

## Main results

* `GrandLoop.exists_isLatticeIso`: if every summand lies below only finitely many summands, every
  crystal base of `⊕ⱼ V(λⱼ)` is the image of `(⊕ⱼ L(λⱼ), ⊔ⱼ B(λⱼ))` under an automorphism.
* `GrandLoop.exists_equiv_of_isCrystalBase`: the same for a module `M` with a given isomorphism
  `⊕ⱼ V(λⱼ) ≃ M`.
* `GrandLoop.exists_equiv_of_isCategoryOInt`: **[HK] Thm. 5.2.1**, for every `M` in `𝒪_int`.

## Implementation notes

[HK] split off the summands of a maximal highest weight and repeat. With infinitely many summands
the repetition is a limit construction: the stages `SplitStage L B` are ordered by extension, a
chain of stages has an upper bound (the automorphisms agree on the summands where they are
defined), and a maximal stage (Zorn's lemma) covers all summands, since a stage missing a summand
can be extended by one more step (`GrandLoop.IsSplit.exists_pullback`). One step needs a maximal
weight among the remaining summands and a finite-dimensional weight space there; both follow from
the hypothesis that every summand lies below only finitely many summands, which holds in `𝒪_int`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.2.
-/

open Pointwise

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}
  {J : Type*} [DecidableEq J] {Λ : J → Dom R}

/-! ### Summands above a summand -/

section Above

variable (Λ) in
/-- The summands `j'` whose highest weight lies in `λⱼ + Q₊`. -/
def summandsAbove (j : J) : Set J :=
  {j' | ∃ ν : I →₀ ℕ, (Λ j').1 = (Λ j).1 + R.rootSum ν}

omit [DecidableEq I] [DecidableEq J] in
lemma mem_summandsAbove_self (j : J) : j ∈ summandsAbove Λ j :=
  ⟨0, by rw [R.rootSum_zero, add_zero]⟩

omit [DecidableEq I] [DecidableEq J] in
lemma summandsAbove_subset {j j' : J} (h : j' ∈ summandsAbove Λ j) :
    summandsAbove Λ j' ⊆ summandsAbove Λ j := by
  rintro l ⟨ν', hν'⟩
  obtain ⟨ν, hν⟩ := h
  exact ⟨ν + ν', by rw [hν', hν, R.rootSum_add, add_assoc]⟩

omit [DecidableEq J] in
include hvt hR in
/-- The weight space of `⊕ⱼ V(λⱼ)` of weight `λⱼ` is finite-dimensional if only finitely many
summands lie above `j`. -/
lemma finiteDimensional_weightSpace_of_finite (j : J) (hfin : (summandsAbove Λ j).Finite) :
    FiniteDimensional k (weightSpace R v (Π₀ j, IrreducibleModule R v (Λ j).1) (Λ j).1) := by
  have := hfin.to_subtype
  have hfd : ∀ j', FiniteDimensional k
      (weightSpace R v (IrreducibleModule R v (Λ j').1) (Λ j).1) :=
    fun j' ↦ IrreducibleModule.finiteDimensional_weightSpace hR
      (pow_ne_one_of_transcendental' hvt) _
  have h0 : ∀ x ∈ weightSpace R v (Π₀ j, IrreducibleModule R v (Λ j).1) (Λ j).1,
      ∀ j' ∉ summandsAbove Λ j, x j' = 0 := fun x hx j' hj' ↦ by
    by_contra hne
    obtain ⟨ν, hν⟩ := IrreducibleModule.exists_eq_sub_rootSum (pow_ne_one_of_transcendental' hvt)
      (map_mem_weightSpace (DFinsupp.lapply (R := QuantumGroup R v) j') hx) hne
    exact hj' ⟨ν, by rw [hν, sub_add_cancel]⟩
  let f : weightSpace R v (Π₀ j, IrreducibleModule R v (Λ j).1) (Λ j).1 →ₗ[k]
      ∀ j' : summandsAbove Λ j, weightSpace R v (IrreducibleModule R v (Λ j').1) (Λ j).1 :=
    LinearMap.pi fun j' ↦ ((DFinsupp.lapply (R := QuantumGroup R v)
      (M := fun j ↦ IrreducibleModule R v (Λ j).1) j').restrictScalars k).restrict
        fun x hx ↦ map_mem_weightSpace (DFinsupp.lapply (R := QuantumGroup R v)
          (M := fun j ↦ IrreducibleModule R v (Λ j).1) j'.1) hx
  refine Module.Finite.of_injective f fun x y h ↦ Subtype.ext (DFinsupp.ext fun j' ↦ ?_)
  by_cases hj' : j' ∈ summandsAbove Λ j
  · exact congrArg Subtype.val (congrFun h ⟨j', hj'⟩)
  · rw [h0 _ x.2 j' hj', h0 _ y.2 j' hj']

omit [DecidableEq I] [DecidableEq J] in
include hR in
/-- If only finitely many summands lie above `j ∈ S`, some summand in `S` above `j` has a maximal
highest weight among the summands in `S`. -/
lemma exists_maximal_of_finite {S : Set J} {j : J} (hj : j ∈ S)
    (hfin : (summandsAbove Λ j).Finite) :
    ∃ j₀ ∈ S, ∀ j' ∈ S, ∀ ν : I →₀ ℕ, (Λ j').1 = (Λ j₀).1 + R.rootSum ν → ν = 0 := by
  have hF : (summandsAbove Λ j ∩ S).Finite := hfin.subset Set.inter_subset_left
  obtain ⟨j₀, ⟨hj₀a, hj₀S⟩, hmin⟩ := Set.exists_min_image (summandsAbove Λ j ∩ S)
    (fun j' ↦ (summandsAbove Λ j' ∩ S).ncard) hF ⟨j, mem_summandsAbove_self j, hj⟩
  refine ⟨j₀, hj₀S, fun j' hj'S ν hν ↦ by_contra fun hν0 ↦ ?_⟩
  have hj'a : j' ∈ summandsAbove Λ j₀ := ⟨ν, hν⟩
  have hsub : summandsAbove Λ j' ∩ S ⊂ summandsAbove Λ j₀ ∩ S := by
    refine ⟨Set.inter_subset_inter_left _ (summandsAbove_subset hj'a), fun h ↦ hν0 ?_⟩
    obtain ⟨ν', hν'⟩ := (h ⟨mem_summandsAbove_self j₀, hj₀S⟩).1
    have h0 : R.rootSum (ν + ν') = R.rootSum 0 := by
      rw [R.rootSum_add, R.rootSum_zero]
      calc R.rootSum ν + R.rootSum ν' = ((Λ j₀).1 + R.rootSum ν + R.rootSum ν') - (Λ j₀).1 := by
            abel
        _ = 0 := by rw [← hν, ← hν', sub_self]
    exact (add_eq_zero.1 (LusztigCartanDatum.RootDatum.rootSum_injective hR h0)).1
  have hlt := Set.ncard_lt_ncard hsub
    (hF.subset (Set.inter_subset_inter_left _ (summandsAbove_subset hj₀a)))
  exact absurd (hmin j' ⟨summandsAbove_subset hj₀a hj'a, hj'S⟩) (not_le.2 hlt)

end Above

/-! ### Auxiliary lemmas -/

section Aux

omit [NeZero v] [CharZero k] in
/-- Two `U`-linear endomorphisms of `⊕ⱼ V(λⱼ)` agree on the vectors whose nonzero components are
all in summands where they agree. -/
lemma ds_apply_eq_of_single {F G : (Π₀ j, IrreducibleModule R v (Λ j).1) →ₗ[QuantumGroup R v]
      Π₀ j, IrreducibleModule R v (Λ j).1} {P : J → Prop}
    (h : ∀ j, P j → ∀ y, F (DFinsupp.single j y) = G (DFinsupp.single j y))
    {x : Π₀ j, IrreducibleModule R v (Λ j).1} (hx : ∀ j, x j ≠ 0 → P j) : F x = G x := by
  induction x using DFinsupp.induction with
  | h0 => rw [map_zero, map_zero]
  | ha j b f hf hb ih =>
    have hfP : ∀ l, f l ≠ 0 → P l := fun l hl ↦ by
      by_cases hlj : l = j
      · subst hlj
        exact absurd hf hl
      · exact hx l (by rwa [DFinsupp.add_apply, DFinsupp.single_eq_of_ne hlj, zero_add])
    rw [map_add, map_add, ih hfP,
      h j (hx j (by rwa [DFinsupp.add_apply, DFinsupp.single_eq_same, hf, add_zero])) b]

omit [DecidableEq J] [NeZero v] [CharZero k] in
lemma projDS_eq_self {p : J → Prop} [DecidablePred p] {x : Π₀ j, IrreducibleModule R v (Λ j).1}
    (hx : ∀ j, ¬p j → x j = 0) : projDS Λ p x = x := by
  ext j
  rw [projDS_apply]
  split_ifs with h
  · rfl
  · exact (hx j h).symm

variable [Finite I] {T : Finset J} {μ : Y →+ ℤ} (hT : ∀ j ∈ T, (Λ j).1 = μ)

/-- The automorphism `autEquiv g` fixes the vectors with no components in `T`. -/
lemma autEquiv_eq_self (g : hwSpan v Λ T ≃ₗ[k] hwSpan v Λ T)
    {x : Π₀ j, IrreducibleModule R v (Λ j).1} (hx : ∀ j ∈ T, x j = 0) :
    autEquiv hvt hR Λ hT g x = x := by
  have h := autMap_projDS_of_notMem (hvt := hvt) (hR := hR) hT g.toLinearMap (fun j ↦ j ∉ T)
    (fun j hj h ↦ h hj) x
  rwa [projDS_eq_self fun j hj ↦ hx j (not_not.1 hj)] at h

/-- The inverse of `autEquiv g` preserves the vectors supported in a set containing `T`. -/
lemma autEquiv_symm_apply_eq_zero (g : hwSpan v Λ T ≃ₗ[k] hwSpan v Λ T) (p : J → Prop)
    (hp : ∀ j ∈ T, p j) {x : Π₀ j, IrreducibleModule R v (Λ j).1}
    (hx : ∀ j, ¬p j → x j = 0) {j : J} (hj : ¬p j) :
    (autEquiv hvt hR Λ hT g).symm x j = 0 := by
  classical
  have h := projDS_autMap (hvt := hvt) (hR := hR) hT g.symm.toLinearMap p hp x
  rw [projDS_eq_self hx, ← autEquiv_symm_apply] at h
  rw [← h, projDS_apply]
  simp [hj]

end Aux

/-! ### Transport of `IsSplit` -/

section Transport

/-- `IsSplit` depends only on the set of summands, not on the decidability instance. -/
lemma IsSplit.congr {S S' : Set J} {_ : DecidablePred (· ∈ S)} {_ : DecidablePred (· ∈ S')}
    (hSS' : S = S') {L : Submodule A (Π₀ j, IrreducibleModule R v (Λ j).1)} {B : Set (QDS L ϖ)}
    (h : IsSplit hvt hR S L B) : IsSplit hvt hR S' L B := by
  subst hSS'
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun x hx ↦ by convert h1 x hx, h2, h3, h4⟩

omit [NeZero v] [CharZero k] [DecidableEq J] in
lemma mem_pullback_trans {L : Submodule A (Π₀ j, IrreducibleModule R v (Λ j).1)}
    {Φ ψ : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v]
      Π₀ j, IrreducibleModule R v (Λ j).1} {x : Π₀ j, IrreducibleModule R v (Λ j).1} :
    x ∈ pullback L (ψ.trans Φ) ↔ x ∈ pullback (pullback L Φ) ψ :=
  Iff.rfl

/-- Pulling back along `Φ` and then along `ψ` is pulling back along `ψ.trans Φ`. -/
lemma IsSplit.of_pullback_pullback {S : Set J} {_ : DecidablePred (· ∈ S)}
    {L : Submodule A (Π₀ j, IrreducibleModule R v (Λ j).1)} {B : Set (QDS L ϖ)}
    {Φ ψ : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v]
      Π₀ j, IrreducibleModule R v (Λ j).1}
    (h : IsSplit hvt hR S (pullback (pullback L Φ) ψ)
      (pullbackBase (pullback L Φ) ψ (pullbackBase L Φ B))) :
    IsSplit hvt hR S (pullback L (ψ.trans Φ)) (pullbackBase L (ψ.trans Φ) B) where
  projDS_mem x hx := mem_pullback_trans.2 (h.projDS_mem x (mem_pullback_trans.1 hx))
  mem_iff x hx := mem_pullback_trans.trans (h.mem_iff x hx)
  hwv_mem j hj := (h.hwv_mem j hj).elim fun h1 h2 ↦
    ⟨mem_pullback_trans.2 h1, (mk_mem_pullbackBase_iff (ψ.trans Φ) _).2
      ((mk_mem_pullbackBase_iff Φ h1).1 ((mk_mem_pullbackBase_iff ψ h1).1 h2))⟩
  ne := h.ne

end Transport

/-! ### Stages of the splitting -/

section Stage

variable (hvt hR) in
/-- A stage of the proof of [HK] Thm. 5.2.1: a set `U` of summands and an automorphism `Φ` of
`⊕ⱼ V(λⱼ)` which fixes the vectors with no components in `U`, preserves (through `Φ⁻¹`) the vectors
supported in `U`, and such that the pullback of `(L, B)` along `Φ` agrees with
`(⊕ⱼ L(λⱼ), ⊔ⱼ B(λⱼ))` outside the complement of `U`. -/
structure SplitStage (L : Submodule A (Π₀ j, IrreducibleModule R v (Λ j).1))
    (B : Set (QDS L ϖ)) where
  /-- The summands already split off. -/
  U : Set J
  /-- The automorphism. -/
  Φ : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v]
    Π₀ j, IrreducibleModule R v (Λ j).1
  map_eq_self : ∀ x : Π₀ j, IrreducibleModule R v (Λ j).1, (∀ j ∈ U, x j = 0) → Φ x = x
  symm_apply_eq_zero : ∀ x : Π₀ j, IrreducibleModule R v (Λ j).1, (∀ j ∉ U, x j = 0) →
    ∀ j ∉ U, Φ.symm x j = 0
  isSplit : ∀ [DecidablePred (· ∈ Uᶜ)], IsSplit hvt hR Uᶜ (pullback L Φ) (pullbackBase L Φ B)

variable {L : Submodule A (Π₀ j, IrreducibleModule R v (Λ j).1)} {B : Set (QDS L ϖ)}

/-- The extension order on stages: `b` extends `a` if `a.U ⊆ b.U` and `b.Φ` agrees with `a.Φ` on
the vectors supported in `a.U`. -/
def SplitStage.Le (a b : SplitStage hvt hR L B) : Prop :=
  a.U ⊆ b.U ∧ ∀ x : Π₀ j, IrreducibleModule R v (Λ j).1, (∀ j ∉ a.U, x j = 0) → b.Φ x = a.Φ x

lemma SplitStage.Le.trans {a b c : SplitStage hvt hR L B} (hab : a.Le b) (hbc : b.Le c) :
    a.Le c :=
  ⟨hab.1.trans hbc.1, fun x hx ↦ (hbc.2 x fun j hj ↦ hx j fun h ↦ hj (hab.1 h)).trans
    (hab.2 x hx)⟩

/-- The stage with no summand split off. -/
lemma SplitStage.nonempty : Nonempty (SplitStage hvt hR L B) := by
  refine ⟨⟨∅, LinearEquiv.refl _ _, fun _ _ ↦ rfl, fun x hx j hj ↦ hx j hj,
    ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun j hj ↦ absurd (Set.mem_compl (Set.notMem_empty j)) hj,
      fun j hj ↦ absurd (Set.mem_compl (Set.notMem_empty j)) hj⟩⟩⟩
  · rwa [projDS_eq_self fun j hj ↦ absurd (Set.mem_compl (Set.notMem_empty j)) hj]
  · have hx0 : x = 0 := DFinsupp.ext fun j ↦ hx j (Set.mem_compl (Set.notMem_empty j))
    subst hx0
    exact ⟨fun _ ↦ zero_mem _, fun _ ↦ zero_mem _⟩

section Chain

variable (c : Set (SplitStage hvt hR L B)) (hc : IsChain SplitStage.Le c)

include hc in
/-- A finite set of summands split off in a nonempty chain of stages is split off in one stage. -/
lemma SplitStage.exists_mem_chain (hne : c.Nonempty) (s : Finset J)
    (hs : ∀ j ∈ s, ∃ a ∈ c, j ∈ a.U) : ∃ a ∈ c, ∀ j ∈ s, j ∈ a.U := by
  induction s using Finset.induction_on with
  | empty => exact hne.elim fun a ha ↦ ⟨a, ha, fun j hj ↦ absurd hj (Finset.notMem_empty j)⟩
  | insert j s _ ih =>
    obtain ⟨a, ha, has⟩ := ih fun l hl ↦ hs l (Finset.mem_insert_of_mem hl)
    obtain ⟨b, hb, hjb⟩ := hs j (Finset.mem_insert_self j s)
    by_cases hab : a = b
    · subst hab
      exact ⟨a, ha, fun l hl ↦ (Finset.mem_insert.1 hl).elim (fun h ↦ h ▸ hjb) (has l)⟩
    · rcases hc ha hb hab with h | h
      · exact ⟨b, hb, fun l hl ↦ (Finset.mem_insert.1 hl).elim (fun h ↦ h ▸ hjb)
          fun hl ↦ h.1 (has l hl)⟩
      · exact ⟨a, ha, fun l hl ↦ (Finset.mem_insert.1 hl).elim (fun h' ↦ h' ▸ h.1 hjb) (has l)⟩

include hc in
/-- For every vector, some stage of a nonempty chain contains the components of the vector in
summands split off in the chain. -/
lemma SplitStage.exists_mem_chain_vec (hne : c.Nonempty) (x : Π₀ j, IrreducibleModule R v (Λ j).1) :
    ∃ a ∈ c, ∀ j, x j ≠ 0 → (∃ b ∈ c, j ∈ b.U) → j ∈ a.U := by
  classical
  obtain ⟨a, ha, has⟩ := SplitStage.exists_mem_chain c hc hne
    (x.support.filter fun j ↦ ∃ b ∈ c, j ∈ b.U) fun j hj ↦ (Finset.mem_filter.1 hj).2
  exact ⟨a, ha, fun j hj hjc ↦ has j (Finset.mem_filter.2 ⟨DFinsupp.mem_support_iff.2 hj, hjc⟩)⟩

open scoped Classical in
/-- The automorphism of the limit stage of a chain, as a linear map: on the summands split off in
the chain it is given by any stage splitting them off. -/
def SplitStage.limMap : (Π₀ j, IrreducibleModule R v (Λ j).1) →ₗ[QuantumGroup R v]
    Π₀ j, IrreducibleModule R v (Λ j).1 :=
  DFinsupp.lsum ℕ fun j ↦ if h : ∃ a ∈ c, j ∈ a.U then
    (h.choose.Φ : (Π₀ j, IrreducibleModule R v (Λ j).1) →ₗ[QuantumGroup R v]
      Π₀ j, IrreducibleModule R v (Λ j).1) ∘ₗ
        DFinsupp.lsingle (R := QuantumGroup R v) (M := fun j ↦ IrreducibleModule R v (Λ j).1) j
  else DFinsupp.lsingle (R := QuantumGroup R v) (M := fun j ↦ IrreducibleModule R v (Λ j).1) j

include hc in
lemma SplitStage.limMap_eq {a : SplitStage hvt hR L B} (ha : a ∈ c)
    {x : Π₀ j, IrreducibleModule R v (Λ j).1} (hx : ∀ j, x j ≠ 0 → (∃ b ∈ c, j ∈ b.U) → j ∈ a.U) :
    SplitStage.limMap c x = a.Φ x := by
  classical
  refine ds_apply_eq_of_single
    (G := (a.Φ : (Π₀ j, IrreducibleModule R v (Λ j).1) →ₗ[QuantumGroup R v]
      Π₀ j, IrreducibleModule R v (Λ j).1)) (P := fun j ↦ (∃ b ∈ c, j ∈ b.U) → j ∈ a.U)
    (fun j hj y ↦ ?_) hx
  simp only [SplitStage.limMap, DFinsupp.lsum_single]
  split_ifs with h
  · obtain ⟨hb, hjb⟩ := h.choose_spec
    have hja := hj h
    have hsupp : ∀ (d : SplitStage hvt hR L B), j ∈ d.U →
        ∀ l ∉ d.U, (DFinsupp.single j y : Π₀ j, IrreducibleModule R v (Λ j).1) l = 0 :=
      fun d hjd l hl ↦ DFinsupp.single_eq_of_ne (by rintro rfl; exact hl hjd)
    change h.choose.Φ (DFinsupp.single j y) = a.Φ (DFinsupp.single j y)
    by_cases hab : a = h.choose
    · rw [← hab]
    · rcases hc ha hb hab with h' | h'
      · exact h'.2 _ (hsupp a hja)
      · exact (h'.2 _ (hsupp _ hjb)).symm
  · have hja : j ∉ a.U := fun hja ↦ h ⟨a, ha, hja⟩
    exact (a.map_eq_self _ fun l hl ↦ DFinsupp.single_eq_of_ne (by rintro rfl; exact hja hl)).symm

include hc in
lemma SplitStage.limMap_bijective (hne : c.Nonempty) :
    Function.Bijective (SplitStage.limMap c) := by
  classical
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨a, ha, hax⟩ := SplitStage.exists_mem_chain_vec c hc hne x
    rw [SplitStage.limMap_eq c hc ha hax] at hx
    exact (map_eq_zero_iff _ a.Φ.injective).1 hx
  · obtain ⟨a, ha, hay⟩ := SplitStage.exists_mem_chain_vec c hc hne y
    set y₁ := projDS Λ (· ∈ a.U) y
    set y₂ := projDS Λ (fun j ↦ j ∉ a.U) y
    have hy₁ : ∀ j ∉ a.U, y₁ j = 0 := fun j hj ↦ by simp [y₁, hj]
    have hy₂ : ∀ j ∈ a.U, y₂ j = 0 := fun j hj ↦ by simp [y₂, hj]
    refine ⟨a.Φ.symm y₁ + y₂, ?_⟩
    rw [SplitStage.limMap_eq c hc ha, map_add, LinearEquiv.apply_symm_apply,
      a.map_eq_self _ hy₂, projDS_add_projDS_not]
    intro j hj hjc
    by_contra hja
    rw [DFinsupp.add_apply, a.symm_apply_eq_zero _ hy₁ j hja, zero_add] at hj
    have hj' : y j ≠ 0 := by simpa [y₂, hja] using hj
    exact hja (hay j hj' hjc)

/-- The automorphism of the limit stage of a nonempty chain. -/
def SplitStage.limEquiv (hne : c.Nonempty) :
    (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v]
      Π₀ j, IrreducibleModule R v (Λ j).1 :=
  LinearEquiv.ofBijective (SplitStage.limMap c) (SplitStage.limMap_bijective c hc hne)

include hc in
/-- A nonempty chain of stages has an upper bound. -/
lemma SplitStage.exists_le (hne : c.Nonempty) : ∃ ub : SplitStage hvt hR L B, ∀ a ∈ c, a.Le ub := by
  classical
  set U' : Set J := {j | ∃ b ∈ c, j ∈ b.U}
  set Φ := SplitStage.limEquiv c hc hne
  have hΦ : ∀ x, Φ x = SplitStage.limMap c x := fun _ ↦ rfl
  have key : ∀ x, ∃ a ∈ c, Φ x = a.Φ x ∧ ∀ j ∈ U', x j ≠ 0 → j ∈ a.U := fun x ↦ by
    obtain ⟨a, ha, hax⟩ := SplitStage.exists_mem_chain_vec c hc hne x
    exact ⟨a, ha, SplitStage.limMap_eq c hc ha hax, fun j hj hx ↦ hax j hx hj⟩
  -- vectors without components in `U'` are fixed
  have hfix : ∀ x : Π₀ j, IrreducibleModule R v (Λ j).1, (∀ j ∈ U', x j = 0) → Φ x = x :=
    fun x hx ↦ hne.elim fun a ha ↦ by
      rw [hΦ, SplitStage.limMap_eq c hc ha fun j hj hjc ↦ absurd (hx j hjc) hj]
      exact a.map_eq_self x fun j hj ↦ hx j ⟨a, ha, hj⟩
  refine ⟨⟨U', Φ, hfix, fun x hx j hj ↦ ?_, ⟨fun x hx ↦ ?_, fun x hx ↦ ?_,
    fun j hj ↦ ?_, fun j hj j' hj' ↦ ?_⟩⟩, fun a ha ↦ ⟨fun j hj ↦ ⟨a, ha, hj⟩, fun x hx ↦ ?_⟩⟩
  · -- `Φ⁻¹` preserves the vectors supported in `U'`
    obtain ⟨a, ha, -, hax⟩ := key x
    have hxa : ∀ l ∉ a.U, x l = 0 := fun l hl ↦ by
      by_contra h
      exact hl (hax l (by_contra fun h' ↦ h (hx l h')) h)
    have hz := a.symm_apply_eq_zero x hxa
    have hΦz : Φ (a.Φ.symm x) = x := by
      rw [hΦ, SplitStage.limMap_eq c hc ha fun l hl _ ↦ by_contra fun h ↦ hl (hz l h),
        LinearEquiv.apply_symm_apply]
    rw [Φ.symm_apply_eq.2 hΦz.symm]
    exact hz j fun h ↦ hj ⟨a, ha, h⟩
  · -- stability under the projection onto the summands outside `U'`
    obtain ⟨a, ha, hΦx, hax⟩ := key x
    have hxa : x ∈ pullback L a.Φ := by rw [mem_pullback, ← hΦx]; exact hx
    have hp := a.isSplit.projDS_mem x hxa
    have he : projDS Λ (· ∈ U'ᶜ) x = projDS Λ (· ∈ a.Uᶜ) x := by
      ext j
      simp only [projDS_apply, Set.mem_compl_iff]
      by_cases hja : j ∈ a.U
      · simp [hja, show j ∈ U' from ⟨a, ha, hja⟩]
      · by_cases hjU : j ∈ U'
        · simp only [hjU, not_true_eq_false, ↓reduceIte, hja, not_false_eq_true]
          by_contra h
          exact hja (hax j hjU (Ne.symm h))
        · simp [hjU, hja]
    rw [mem_pullback, he, hΦ, SplitStage.limMap_eq c hc ha]
    · exact hp
    · intro j hj hjc
      have hj' : j ∉ a.U ∧ x j ≠ 0 := by simpa using hj
      exact absurd (hax j hjc hj'.2) hj'.1
  · -- vectors supported in `U'`
    obtain ⟨a, ha, hΦx, hax⟩ := key x
    rw [mem_pullback, hΦx]
    refine a.isSplit.mem_iff x fun j hj ↦ ?_
    by_contra h
    by_cases hjU : j ∈ U'
    · exact hj (hax j hjU h)
    · exact h (hx j hjU)
  · -- the highest weight vectors of the summands in `U'`
    obtain ⟨a, ha, hja⟩ : j ∈ U' := not_not.1 hj
    obtain ⟨h1, h2⟩ := a.isSplit.hwv_mem j (not_not.2 hja)
    have he : Φ (DFinsupp.single j (IrreducibleModule.hwv R v (Λ j).1)) =
        a.Φ (DFinsupp.single j (IrreducibleModule.hwv R v (Λ j).1)) := by
      rw [hΦ, SplitStage.limMap_eq c hc ha]
      intro l hl _
      by_contra hla
      exact hl (DFinsupp.single_eq_of_ne (by rintro rfl; exact hla hja))
    obtain ⟨h1', h2'⟩ := exists_mem_mk_mem he h1 ((mk_mem_pullbackBase_iff a.Φ h1).1 h2)
    exact ⟨h1', (mk_mem_pullbackBase_iff Φ h1').2 h2'⟩
  · obtain ⟨a, ha, hja⟩ : j ∈ U' := not_not.1 hj
    exact a.isSplit.ne j (not_not.2 hja) j' fun h ↦ hj' ⟨a, ha, h⟩
  · rw [hΦ, SplitStage.limMap_eq c hc ha]
    intro j hj _
    by_contra h
    exact hj (hx j h)

end Chain

/-- A stage missing a summand can be extended: split off the summands of a maximal highest weight
among the remaining ones. -/
lemma SplitStage.exists_lt [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
    (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖv : algebraMap A k ϖ = v⁻¹)
    (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
    (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
    {hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) (isIntDS hvt hR Λ) L}
    (hB : IsCrystalBase hL ϖ B)
    (hup : ∀ j, (summandsAbove Λ j).Finite) (a : SplitStage hvt hR L B) {j : J} (hj : j ∉ a.U) :
    ∃ b : SplitStage hvt hR L B, a.Le b ∧ ¬b.U ⊆ a.U := by
  classical
  obtain ⟨j₀, hj₀S, hmax⟩ := exists_maximal_of_finite (hR := hR) (S := a.Uᶜ) hj (hup j)
  set T : Finset J := (hup j₀).toFinset.filter fun j' ↦ j' ∉ a.U ∧ (Λ j').1 = (Λ j₀).1
  have hT : ∀ j' ∈ T, (Λ j').1 = (Λ j₀).1 := fun j' h ↦ (Finset.mem_filter.1 h).2.2
  have hTS : ∀ j' ∈ a.Uᶜ, (Λ j').1 = (Λ j₀).1 → j' ∈ T := fun j' hj' h ↦
    Finset.mem_filter.2 ⟨(hup j₀).mem_toFinset.2 ⟨0, by rw [R.rootSum_zero, add_zero, h]⟩, hj', h⟩
  have hTsub : ∀ j' ∈ T, j' ∈ a.Uᶜ := fun j' h ↦ (Finset.mem_filter.1 h).2.1
  have := finiteDimensional_weightSpace_of_finite (hvt := hvt) (hR := hR) j₀ (hup j₀)
  obtain ⟨g, hg⟩ := a.isSplit.exists_pullback hinj hϖ hϖv hk hfund
    (isCrystalBase_pullback (hvt := hvt) (hR := hR) a.Φ hB) hj₀S hmax hT hTS hTsub
  set ψ := autEquiv hvt hR Λ hT g
  have hψ : ∀ x : Π₀ j, IrreducibleModule R v (Λ j).1, (∀ j ∉ a.U, x j = 0) → ψ x = x :=
    fun x hx ↦ autEquiv_eq_self hT g fun l hl ↦ hx l (hTsub l hl)
  have hfix : ∀ x : Π₀ j, IrreducibleModule R v (Λ j).1, (∀ j ∈ a.U ∪ T, x j = 0) →
      (ψ.trans a.Φ) x = x := fun x hx ↦ by
    rw [LinearEquiv.trans_apply, autEquiv_eq_self hT g fun l hl ↦ hx l (Or.inr hl)]
    exact a.map_eq_self x fun l hl ↦ hx l (Or.inl hl)
  have hsymm : ∀ x : Π₀ j, IrreducibleModule R v (Λ j).1, (∀ j ∉ a.U ∪ T, x j = 0) →
      ∀ j ∉ a.U ∪ T, (ψ.trans a.Φ).symm x j = 0 := fun x hx l hl ↦ by
    rw [LinearEquiv.symm_trans_apply]
    refine autEquiv_symm_apply_eq_zero hT g (· ∈ a.U ∪ T) (fun l hl ↦ Or.inr hl) (fun l hl ↦ ?_) hl
    -- the components of `a.Φ⁻¹ x` outside `a.U ∪ T` vanish
    have hx₂ : a.Φ.symm (projDS Λ (fun j ↦ j ∉ a.U) x) = projDS Λ (fun j ↦ j ∉ a.U) x :=
      a.Φ.symm_apply_eq.2 (a.map_eq_self _ fun j hj ↦ by simp [hj]).symm
    have hlU : l ∉ a.U := fun h ↦ hl (Or.inl h)
    rw [← projDS_add_projDS_not Λ (· ∈ a.U) x, map_add, hx₂, DFinsupp.add_apply,
      a.symm_apply_eq_zero _ (fun j hj ↦ by simp [hj]) l hlU, zero_add]
    simp [hlU, hx l hl]
  have hset : a.Uᶜ \ (T : Set J) = (a.U ∪ T)ᶜ := by
    ext l
    simp
  refine ⟨⟨a.U ∪ T, ψ.trans a.Φ, hfix, hsymm, IsSplit.congr hset hg.of_pullback_pullback⟩,
    ⟨Set.subset_union_left, fun x hx ↦ ?_⟩, fun h ↦ ?_⟩
  · rw [LinearEquiv.trans_apply, hψ x hx]
  · exact hTsub j₀ (hTS j₀ hj₀S rfl) (h (Or.inr (hTS j₀ hj₀S rfl)))

end Stage

/-! ### The uniqueness theorem -/

section Theorem

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
  {L : Submodule A (Π₀ j, IrreducibleModule R v (Λ j).1)}
  {hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) (isIntDS hvt hR Λ) L}
  {B : Set (QDS L ϖ)}

include hinj hϖ hϖv hk hfund in
/-- If every summand lies below only finitely many summands, every crystal base `(L, B)` of
`⊕ⱼ V(λⱼ)` is the image of `(⊕ⱼ L(λⱼ), ⊔ⱼ B(λⱼ))` under an automorphism, in the sense of
`GrandLoop.IsLatticeIso`. -/
theorem exists_isLatticeIso (hup : ∀ j, (summandsAbove Λ j).Finite) (hB : IsCrystalBase hL ϖ B) :
    ∃ Φ, IsLatticeIso hvt hR L B Φ := by
  classical
  have hch : ∀ c : Set (SplitStage hvt hR L B), IsChain SplitStage.Le c →
      ∃ ub, ∀ a ∈ c, a.Le ub := fun c hc ↦ c.eq_empty_or_nonempty.elim
    (fun h ↦ SplitStage.nonempty.elim fun a ↦
      ⟨a, fun b hb ↦ (Set.notMem_empty b (h ▸ hb)).elim⟩)
    (SplitStage.exists_le c hc)
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hch SplitStage.Le.trans
  have hU : ∀ j, j ∈ m.U := fun j ↦ by_contra fun hj ↦
    (SplitStage.exists_lt hinj hϖ hϖv hk hfund hB hup m hj).elim fun b hb ↦
      hb.2 (hm b hb.1).1
  refine ⟨m.Φ, fun x ↦ (m.isSplit.mem_iff x fun j hj ↦ absurd (hU j) hj).symm, fun j ↦ ?_⟩
  obtain ⟨h1, h2⟩ := m.isSplit.hwv_mem j (not_not.2 (hU j))
  exact ⟨h1, (mk_mem_pullbackBase_iff m.Φ h1).1 h2⟩

include hinj hϖ hϖv hk hfund in
/-- If every summand lies below only finitely many summands (for example, if there are finitely
many summands), every crystal base `(L, B)` of `⊕ⱼ V(λⱼ)` is the image of
`(⊕ⱼ L(λⱼ), ⊔ⱼ B(λⱼ))` under an automorphism `Φ` of `⊕ⱼ V(λⱼ)` (the case `M = ⊕ⱼ V(λⱼ)` of
`exists_equiv_of_isCrystalBase`). -/
theorem exists_autEquiv_of_isCrystalBase (hup : ∀ j, (summandsAbove Λ j).Finite)
    (hB : IsCrystalBase hL ϖ B) :
    ∃ (Φ : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v]
        Π₀ j, IrreducibleModule R v (Λ j).1) (hΦ : ∀ x, x ∈ dsSum hvt hR A Λ ↔ Φ x ∈ L),
      ∀ b, b ∈ dsBase hvt hR A ϖ Λ ↔ IntegrableSl2.quotEquiv (Φ.restrictScalars k) hΦ ϖ b ∈ B :=
  (exists_isLatticeIso hinj hϖ hϖv hk hfund hup hB).elim fun Φ h ↦
    ⟨Φ, h.1, h.mem_dsBase_iff hinj hϖ hϖv hk hfund hB⟩

end Theorem

section Module

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] [Module A M] [IsScalarTower A k M]
  {hM : IsIntegrable R v M} {L : Submodule A M}
  {hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) hM L}
  {B : Set (L ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L))}

include hinj hϖ hϖv hk hfund in
/-- **Uniqueness of crystal bases** (cf. [HK] Thm. 5.2.1), for a module `M` with an isomorphism
`ψ : ⊕ⱼ V(λⱼ) ≃ M` such that every summand lies below only finitely many summands: for every
crystal base `(L, B)` of `M` there is an isomorphism `Φ : ⊕ⱼ V(λⱼ) ≃ M` of `U`-modules mapping
`⊕ⱼ L(λⱼ)` onto `L` such that the induced isomorphism `(⊕ⱼ L(λⱼ)) / ϖ ≃ L / ϖL` maps `⊔ⱼ B(λⱼ)`
onto `B`. -/
theorem exists_equiv_of_isCrystalBase (hup : ∀ j, (summandsAbove Λ j).Finite)
    (ψ : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v] M)
    (hB : IsCrystalBase hL ϖ B) :
    ∃ (Φ : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v] M)
      (hΦ : ∀ x, x ∈ dsSum hvt hR A Λ ↔ Φ x ∈ L),
      ∀ b, b ∈ dsBase hvt hR A ϖ Λ ↔ IntegrableSl2.quotEquiv (Φ.restrictScalars k) hΦ ϖ b ∈ B := by
  let L₀ : Submodule A (Π₀ j, IrreducibleModule R v (Λ j).1) :=
    L.comap (((ψ : (Π₀ j, IrreducibleModule R v (Λ j).1) →ₗ[QuantumGroup R v] M).restrictScalars
      k).restrictScalars A)
  have hLL₀ : ∀ m, m ∈ L ↔ ψ.symm m ∈ L₀ := fun m ↦ by
    change _ ↔ ψ (ψ.symm m) ∈ L
    rw [ψ.apply_symm_apply]
  set Qψ := IntegrableSl2.quotEquiv (ψ.symm.restrictScalars k) hLL₀ ϖ
  have hB₀ := hB.of_equiv (isIntDS hvt hR Λ) ψ.symm hLL₀ (B' := Qψ '' B)
    fun _ ↦ (Qψ.injective.mem_set_image).symm
  refine (exists_autEquiv_of_isCrystalBase hinj hϖ hϖv hk hfund hup hB₀).elim fun Φ₀ h ↦
    h.elim fun hΦ₀ hb₀ ↦ ⟨Φ₀.trans ψ, hΦ₀, fun b ↦ ?_⟩
  rw [hb₀ b]
  have e : IntegrableSl2.quotEquiv (Φ₀.restrictScalars k) hΦ₀ ϖ b =
      Qψ (IntegrableSl2.quotEquiv ((Φ₀.trans ψ).restrictScalars k) hΦ₀ ϖ b) := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    exact congrArg Submodule.Quotient.mk (Subtype.ext (ψ.symm_apply_apply _).symm)
  rw [e, Qψ.injective.mem_set_image]

omit [DecidableEq J] [Finite I] in
include hvt hR in
/-- If `M ≃ ⊕ⱼ V(λⱼ)` lies in `𝒪_int`, every summand lies below only finitely many summands: the
weights of `M` above a given weight are finitely many, and each weight space of `M` is
finite-dimensional. -/
lemma finite_summandsAbove_of_isCategoryOInt (hO : IsCategoryOInt R v M)
    (ψ : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v] M) (j : J) :
    (summandsAbove Λ j).Finite := by
  classical
  have hv' := pow_ne_one_of_transcendental' hvt
  obtain ⟨s₀, hs₀⟩ := hO.exists_finset
  -- the image of the highest weight vector of each summand
  have hmem : ∀ j', ψ (DFinsupp.single j' (IrreducibleModule.hwv R v (Λ j').1)) ∈
      weightSpace R v M (Λ j').1 := fun j' ↦
    map_mem_weightSpace (ψ : (Π₀ j, IrreducibleModule R v (Λ j).1) →ₗ[QuantumGroup R v] M)
      (map_mem_weightSpace (DFinsupp.lsingle (R := QuantumGroup R v)
        (M := fun j ↦ IrreducibleModule R v (Λ j).1) j') IrreducibleModule.hwv_mem_weightSpace)
  have hne : ∀ j', ψ (DFinsupp.single j' (IrreducibleModule.hwv R v (Λ j').1)) ≠ 0 := fun j' h ↦ by
    rw [map_eq_zero_iff _ ψ.injective, DFinsupp.single_eq_zero] at h
    exact hwv_ne_zero hR hv' _ h
  -- the possible differences `λ_{j'} - λⱼ`
  set N : Set (I →₀ ℕ) := ⋃ μ ∈ (s₀ : Set (Y →+ ℤ)),
    ⋃ σ ∈ {σ : I →₀ ℕ | R.rootSum σ = μ - (Λ j).1}, Set.Icc 0 σ
  have hN : N.Finite := Set.Finite.biUnion s₀.finite_toSet fun μ _ ↦
    Set.Finite.biUnion (Set.Subsingleton.finite fun σ hσ σ' hσ' ↦
      LusztigCartanDatum.RootDatum.rootSum_injective hR (hσ.trans hσ'.symm))
      fun σ _ ↦ Set.finite_Icc 0 σ
  -- each weight has finitely many summands
  have hfib : ∀ μ, {j' | (Λ j').1 = μ}.Finite := fun μ ↦ by
    have := hO.finiteDimensional_weightSpace μ
    let f : {j' | (Λ j').1 = μ} → weightSpace R v M μ := fun j' ↦
      ⟨ψ (DFinsupp.single j'.1 (IrreducibleModule.hwv R v (Λ j'.1).1)), by
        convert hmem j'.1
        exact (show (Λ j'.1).1 = μ from j'.2).symm⟩
    have hli : LinearIndependent k fun j' : {j' | (Λ j').1 = μ} ↦
        ψ (DFinsupp.single j'.1 (IrreducibleModule.hwv R v (Λ j'.1).1)) :=
      (linearIndependent_dfinsuppSingle (fun j ↦ IrreducibleModule.hwv R v (Λ j).1)
        (fun j ↦ hwv_ne_zero hR hv' _) _).map'
        ((ψ : (Π₀ j, IrreducibleModule R v (Λ j).1) →ₗ[QuantumGroup R v] M).restrictScalars k)
        (LinearMap.ker_eq_bot.2 ψ.injective)
    have hf : LinearIndependent k f := LinearIndependent.of_comp (weightSpace R v M μ).subtype hli
    exact Set.finite_coe_iff.1 hf.finite
  refine (hN.biUnion fun ν _ ↦ hfib ((Λ j).1 + R.rootSum ν)).subset fun j' ⟨ν, hν⟩ ↦ ?_
  obtain ⟨μ, hμ, ρ, hρ⟩ := hs₀ _ ((Submodule.ne_bot_iff _).2 ⟨_, hmem j', hne j'⟩)
  refine Set.mem_biUnion (x := ν) (Set.mem_biUnion hμ (Set.mem_biUnion (x := ν + ρ) ?_ ?_)) hν
  · change R.rootSum (ν + ρ) = μ - (Λ j).1
    rw [R.rootSum_add]
    calc R.rootSum ν + R.rootSum ρ = ((Λ j).1 + R.rootSum ν) - (Λ j).1 + R.rootSum ρ := by abel
      _ = μ - (Λ j).1 := by rw [← hν, hρ]; abel
  · exact ⟨zero_le, le_self_add⟩

open scoped Classical in
include hinj hϖ hϖv hk hfund in
/-- **[HK] Thm. 5.2.1 (uniqueness of crystal bases).** Let `M` be a module in `𝒪_int` and `(L, B)`
a crystal base of `M`. Then `M ≃ ⊕ⱼ V(λⱼ)` for dominant weights `λⱼ` by an isomorphism `Φ` of
`U`-modules mapping `⊕ⱼ L(λⱼ)` onto `L`, such that the induced isomorphism
`(⊕ⱼ L(λⱼ)) / ϖ ≃ L / ϖL` maps `⊔ⱼ B(λⱼ)` onto `B`. The summands are indexed by a set of
submodules of `M`. -/
theorem exists_equiv_of_isCategoryOInt (hO : IsCategoryOInt R v M) (hB : IsCrystalBase hL ϖ B) :
    ∃ (s : Set (Submodule (QuantumGroup R v) M)) (Λ : s → Dom R)
      (Φ : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v] M)
      (hΦ : ∀ x, x ∈ dsSum hvt hR A Λ ↔ Φ x ∈ L),
      ∀ b, b ∈ dsBase hvt hR A ϖ Λ ↔ IntegrableSl2.quotEquiv (Φ.restrictScalars k) hΦ ϖ b ∈ B := by
  obtain ⟨s, Λ₀, hdom, ⟨ψ⟩⟩ :=
    hO.exists_linearEquiv_dfinsupp (pow_ne_one_of_transcendental' hvt) hvt hR
  let Λ : s → Dom R := fun j ↦ ⟨Λ₀ j, hdom j⟩
  let ψ' : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v] M := ψ
  exact ⟨s, Λ, exists_equiv_of_isCrystalBase hinj hϖ hϖv hk hfund
    (finite_summandsAbove_of_isCategoryOInt (hvt := hvt) (hR := hR) hO ψ') ψ' hB⟩

end Module

end GrandLoop

end LieLean.QuantumGroup
