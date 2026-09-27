/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.HighestWeight
import LieLean.RepresentationTheory.Crystal.Path.Character
import LieLean.RepresentationTheory.Crystal.Realization

/-!
# Littelmann paths for a realization

Let `(𝔥, Π, Π^∨)` be a realization of a generalized Cartan matrix `A` over a conditionally complete
ordered field `K` (i.e. over `ℝ`). Littelmann paths for the Cartan datum of integral weights
(`Matrix.Realization.cartanDatum`) take values in `𝔥*` itself. For a dominant integral weight `Λ`
we obtain Littelmann's crystal `B(Λ)`, the connected component of the straight line path
`π_Λ(t) = tΛ` ([Lit95] §2 (check)).

## Main definitions

* `Matrix.Realization.pathSpace`: `𝔥*` as the space of Littelmann paths for the Cartan datum of
  integral weights.
* `Matrix.Realization.pathCrystal`: Littelmann's crystal `B(Λ)` of a dominant integral weight.

## Main results

* `Matrix.Realization.isSeminormal_pathCrystal`: `B(Λ)` is seminormal.
* `Matrix.Realization.e_straightLine`, `Matrix.Realization.φ_straightLine`: `π_Λ` is a highest
  weight element of `B(Λ)` with `φᵢ(π_Λ) = ⟨Λ, αᵢ^∨⟩`.
* `Matrix.Realization.card_wt_weylGroup_pathCrystal`: the number of paths in `B(Λ)` of weight
  `w μ` equals the number of paths of weight `μ`, for every `w` in the Weyl group.
* `Matrix.Realization.finite_wt_pathCrystal`: *if* the set of paths `f_{i₁} ⋯ f_{iₖ} π_Λ` is stable
  under all `eⱼ` (Littelmann's theorem, not formalized here), then each weight occurs only
  finitely often in `B(Λ)`, and all weights lie in `Λ - Q₊`
  (`Matrix.Realization.exists_wt_eq_pathCrystal`).

Littelmann's character formula `ch B(Λ) = ch L(Λ)` ([Lit95] Thm. 9.1 (check)) is not proved.

## References

* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
-/

open Module Set

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [ConditionallyCompleteLinearOrder K]
  [IsStrictOrderedRing K] [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsGeneralizedCartan)

/-- The dual `𝔥*` of the Cartan subalgebra, as the space in which Littelmann paths for the Cartan
datum of integral weights take values; the coroots act by evaluation. -/
noncomputable def pathSpace : (P.cartanDatum hA).PathSpace K (Dual K H) where
  embed := P.integralWeights.subtype
  embed_injective := Subtype.val_injective
  coroot i := Dual.eval K H (P.coroot i)
  coroot_embed i x := by simp

@[simp] lemma pathSpace_embed (x : P.integralWeights) : (P.pathSpace hA).embed x = x := rfl

@[simp] lemma pathSpace_coroot (i : ι) (μ : Dual K H) :
    (P.pathSpace hA).coroot i μ = μ (P.coroot i) := rfl

variable {P}

lemma IsDominantIntegral.mem_integralWeights {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ) :
    Λ ∈ P.integralWeights := fun i ↦ by
  obtain ⟨n, hn⟩ := hΛ i
  exact ⟨n, by rw [hn]; norm_cast⟩

lemma IsDominantIntegral.coroot_nonneg {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ) (i : ι) :
    0 ≤ (P.cartanDatum hA).coroot i ⟨Λ, hΛ.mem_integralWeights⟩ := by
  obtain ⟨n, hn⟩ := hΛ i
  have h := coroot_cartanDatum_cast P hA i ⟨Λ, hΛ.mem_integralWeights⟩
  rw [hn] at h
  have : (P.cartanDatum hA).coroot i ⟨Λ, hΛ.mem_integralWeights⟩ = n := by exact_mod_cast h
  rw [this]
  exact Int.natCast_nonneg n

omit [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K] in
lemma sum_count_smul_root [DecidableEq ι] (s : Multiset ι) :
    ∑ m ∈ s.toFinset, s.count m • P.root m = ∑ i, ((s.count i : ℤ) : K) • P.root i := by
  have h : ∑ m ∈ s.toFinset, s.count m • P.root m = ∑ m, s.count m • P.root m :=
    Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ by
      rw [Multiset.count_eq_zero_of_notMem (Multiset.mem_toFinset.not.mp hi), zero_smul]
  rw [h]
  simp [← Nat.cast_smul_eq_nsmul K]

/-- The sum `∑_{i ∈ s} αᵢ` over a multiset `s` determines `s` (the simple roots are linearly
independent). -/
theorem injective_sum_map_root :
    Function.Injective fun s : Multiset ι ↦ (s.map (P.cartanDatum hA).root).sum := by
  classical
  have key : ∀ s : Multiset ι, (((s.map (P.cartanDatum hA).root).sum : P.integralWeights) :
      Dual K H) = P.rootOf fun i ↦ (s.count i : ℤ) := fun s ↦ by
    rw [rootOf_apply, AddSubgroup.val_multiset_sum, Multiset.map_map, Function.comp_def]
    simp only [coe_root_cartanDatum]
    rw [Finset.sum_multiset_map_count, P.sum_count_smul_root s]
  intro s t hst
  have h := P.rootOf_injective ((key s).symm.trans ((congrArg Subtype.val hst).trans (key t)))
  ext i
  exact_mod_cast congrFun h i

variable [TopologicalSpace K] [OrderTopology K] [FloorRing K] {Λ : Dual K H}

variable (P) in
/-- Littelmann's crystal `B(Λ)` of a dominant integral weight `Λ` ([Lit95] §2 (check)): the
connected component of the straight line path `π_Λ(t) = tΛ` in the crystal of Littelmann paths in
`𝔥*`. -/
noncomputable def pathCrystal (hΛ : P.IsDominantIntegral Λ) :
    Crystal (P.cartanDatum hA)
      (LittelmannPath.straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component :=
  LittelmannPath.componentCrystal _

/-- `B(Λ)` is seminormal. -/
theorem isSeminormal_pathCrystal (hΛ : P.IsDominantIntegral Λ) :
    (P.pathCrystal hA hΛ).IsSeminormal :=
  LittelmannPath.isSeminormal_componentCrystal _

omit [FloorRing K] in
/-- `π_Λ` is a highest weight element: `eᵢ π_Λ = 0`. -/
theorem e_straightLine (hΛ : P.IsDominantIntegral Λ) (i : ι) :
    LittelmannPath.e i (LittelmannPath.straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩)
      = none :=
  LittelmannPath.e_straightLine (hΛ.coroot_nonneg hA i)

/-- `φᵢ(π_Λ) = ⟨Λ, αᵢ^∨⟩`. -/
theorem φ_straightLine (hΛ : P.IsDominantIntegral Λ) (i : ι) :
    LittelmannPath.φ i (LittelmannPath.straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩)
      = (P.cartanDatum hA).coroot i ⟨Λ, hΛ.mem_integralWeights⟩ :=
  LittelmannPath.φ_straightLine (hΛ.coroot_nonneg hA i)

omit [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] in
private lemma card_reflection_aux {B : Type*} (C : Crystal (P.cartanDatum hA) B)
    (hC : C.IsSeminormal) (i : ι) (μ : Dual K H) :
    Nat.card {b // (C.wt b : Dual K H) = P.reflection hA i μ} =
      Nat.card {b // (C.wt b : Dual K H) = μ} := by
  by_cases hμ : μ ∈ P.integralWeights
  · lift μ to P.integralWeights using hμ
    rw [← coe_reflection_cartanDatum,
      Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ Subtype.coe_inj),
      Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ Subtype.coe_inj), hC.card_wt_reflection]
  · have h₁ : IsEmpty {b // (C.wt b : Dual K H) = μ} :=
      ⟨fun ⟨b, hb⟩ ↦ hμ (hb ▸ (C.wt b).2)⟩
    have h₂ : IsEmpty {b // (C.wt b : Dual K H) = P.reflection hA i μ} := by
      refine ⟨fun ⟨b, hb⟩ ↦ hμ ?_⟩
      rw [← P.reflection_reflection hA i μ, ← hb, ← coe_reflection_cartanDatum]
      exact ((P.cartanDatum hA).reflection i (C.wt b)).2
    simp [Nat.card_of_isEmpty]

/-- The number of paths in `B(Λ)` of weight `w μ` equals the number of paths of weight `μ`, for
every element `w` of the Weyl group: the crystal analogue of the `W`-invariance of weight
multiplicities of `L(Λ)` ([Kac] Prop. 3.7, Prop. 10.1 (check)). -/
theorem card_wt_weylGroup_pathCrystal (hΛ : P.IsDominantIntegral Λ) {w : Dual K H ≃ₗ[K] Dual K H}
    (hw : w ∈ P.weylGroup hA) (μ : Dual K H) :
    Nat.card {b // ((P.pathCrystal hA hΛ).wt b : Dual K H) = w μ} =
      Nat.card {b // ((P.pathCrystal hA hΛ).wt b : Dual K H) = μ} := by
  refine P.weylGroup_induction hA (p := fun w ↦ ∀ μ, Nat.card {b //
    ((P.pathCrystal hA hΛ).wt b : Dual K H) = w μ} = Nat.card {b //
      ((P.pathCrystal hA hΛ).wt b : Dual K H) = μ}) (fun _ ↦ rfl) (fun i w ih μ ↦ ?_) hw μ
  rw [LinearEquiv.mul_apply, card_reflection_aux hA _ (isSeminormal_pathCrystal hA hΛ), ih]

/-- The stability hypothesis of Littelmann's theorem for `B(Λ)`: the set of paths
`f_{i₁} ⋯ f_{iₖ} π_Λ` is stable under all root operators `eⱼ` ([Lit95] §5–7 (check); not
formalized here). -/
def FOrbitStable (hΛ : P.IsDominantIntegral Λ) : Prop :=
  ∀ π' ∈ (LittelmannPath.straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).fOrbit,
    ∀ j π'', LittelmannPath.e j π' = some π'' →
      π'' ∈ (LittelmannPath.straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).fOrbit

/-- Assuming Littelmann's stability theorem (`Matrix.Realization.FOrbitStable`), the weights of
`B(Λ)` lie in `Λ - Q₊`. -/
theorem exists_wt_eq_pathCrystal (hΛ : P.IsDominantIntegral Λ) (h : FOrbitStable hA hΛ)
    (b : (LittelmannPath.straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    ∃ k : ι → ℤ, 0 ≤ k ∧ ((P.pathCrystal hA hΛ).wt b : Dual K H) = Λ - P.rootOf k := by
  classical
  obtain ⟨s, hs⟩ := LittelmannPath.exists_wt_eq_of_mem_component h b.2
  refine ⟨fun i ↦ (s.count i : ℤ), fun i ↦ Int.natCast_nonneg _, ?_⟩
  change (b.1.wt : Dual K H) = _
  rw [hs, AddSubgroup.coe_sub, rootOf_apply, AddSubgroup.val_multiset_sum, Multiset.map_map,
    Function.comp_def]
  simp only [coe_root_cartanDatum, LittelmannPath.wt_straightLine]
  rw [Finset.sum_multiset_map_count, P.sum_count_smul_root s]

/-- Assuming Littelmann's stability theorem (`Matrix.Realization.FOrbitStable`), every weight
occurs only finitely often in `B(Λ)`. -/
theorem finite_wt_pathCrystal (hΛ : P.IsDominantIntegral Λ) (h : FOrbitStable hA hΛ)
    (μ : P.integralWeights) :
    {π ∈ (LittelmannPath.straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component |
      π.wt = μ}.Finite :=
  LittelmannPath.finite_wt_component (injective_sum_map_root hA) h μ

end Matrix.Realization
