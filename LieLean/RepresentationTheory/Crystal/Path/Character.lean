/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.RootOperators

/-!
# The path crystals `B(π)` and `B(λ)`

For a Littelmann path `π`, let `B(π)` be the connected component of `π` in the crystal of all
paths, i.e. the smallest set of paths containing `π` and stable under all root operators `eᵢ`,
`fᵢ` ([Lit95] §2 (check)). For a dominant weight `λ` and the straight line path `π_λ(t) = tλ`,
Littelmann's theorem ([Lit95] Thm. 9.1, [Lit94] (check)) states that the character of
`B(λ) := B(π_λ)` is the character of the irreducible integrable highest-weight module `L(λ)`.

## Main definitions

* `LittelmannPath.straightLine S λ`: the path `π_λ(t) = tλ`.
* `LittelmannPath.component π`: the connected component `B(π)` of `π`.
* `LittelmannPath.componentCrystal π`: the crystal structure on `B(π)`.
* `LittelmannPath.fWord`, `LittelmannPath.fOrbit π`: the paths `f_{i₁} ⋯ f_{iₖ} π`.

## Main results

* `LittelmannPath.e_straightLine`, `LittelmannPath.φ_straightLine`: for dominant `λ`, `π_λ` is a
  highest weight element: `eᵢ π_λ = 0` and `φᵢ(π_λ) = ⟨λ, αᵢ^∨⟩`.
* `LittelmannPath.isSeminormal_componentCrystal`: `B(π)` is seminormal.
* `LittelmannPath.card_wt_reflection_component`: the number of paths of weight `rᵢ μ` in `B(π)`
  equals the number of paths of weight `μ` (Kashiwara's `Sᵢ`).
* `LittelmannPath.component_eq_fOrbit`, `LittelmannPath.exists_wt_eq_of_mem_component`,
  `LittelmannPath.finite_wt_component`: *if* the set `{f_{i₁} ⋯ f_{iₖ} π}` is stable under the
  `eⱼ`, then `B(π)` is this set, its weights lie in `wt π - Q₊`, and (for linearly independent
  simple roots and finitely many indices) each weight occurs finitely often.

## What remains

Littelmann's theorem that for `π` with image in the dominant chamber (e.g. `π = π_λ`) the set
`{f_{i₁} ⋯ f_{iₖ} π}` is stable under all `eⱼ` ([Lit95] §5–7 (check); in [Lit94] via
Lakshmibai–Seshadri paths) is not proved here; it is the hypothesis of
`LittelmannPath.component_eq_fOrbit`. Nor is the character formula `ch B(λ) = ch L(λ)`.

## References

* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
* [Lit94] P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*,
  Invent. Math. **116** (1994), 329–346.
-/

open Set

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {D : CartanDatum ι X}
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

/-! ### Straight line paths -/

variable (S) in
/-- The straight line path `π_λ(t) = tλ` ([Lit95] §1 (check)). -/
def straightLine (μ : X) : LittelmannPath S where
  toFun t := max 0 (min 1 t) • S.embed μ
  wt := μ
  toFun_of_nonpos' t ht := by
    rw [min_eq_right (ht.trans zero_le_one), max_eq_left ht, zero_smul]
  toFun_of_one_le' t ht := by rw [min_eq_left ht, max_eq_right zero_le_one, one_smul]
  continuous_coroot' i := by
    simp only [map_smul, smul_eq_mul]
    exact (continuous_const.max (continuous_const.min continuous_id)).mul continuous_const

variable {i : ι} {μ : X}

@[simp] lemma wt_straightLine : (straightLine S μ).wt = μ := rfl

lemma straightLine_apply (t : 𝕜) : straightLine S μ t = max 0 (min 1 t) • S.embed μ := rfl

lemma pairing_straightLine (t : 𝕜) :
    (straightLine S μ).pairing i t = max 0 (min 1 t) * D.coroot i μ := by
  rw [pairing, straightLine_apply, map_smul, smul_eq_mul, S.coroot_embed]

/-- For `⟨λ, αᵢ^∨⟩ ≥ 0` the function `hᵢ` of `π_λ` is nonnegative, so its minimum is `0`. -/
lemma minPairing_straightLine (hμ : 0 ≤ D.coroot i μ) : (straightLine S μ).minPairing i = 0 :=
  le_antisymm ((straightLine S μ).minPairing_nonpos i)
    ((straightLine S μ).le_runningMin zero_le_one fun t _ ↦ by
      rw [pairing_straightLine]
      exact mul_nonneg (le_max_left _ _) (by exact_mod_cast hμ))

lemma e_straightLine (hμ : 0 ≤ D.coroot i μ) : e i (straightLine S μ) = none := by
  rw [e_eq_none_iff, minPairing_straightLine hμ]
  norm_num

variable [FloorRing 𝕜]

lemma ε_straightLine (hμ : 0 ≤ D.coroot i μ) : ε i (straightLine S μ) = 0 := by
  rw [ε, minPairing_straightLine hμ, neg_zero, Int.floor_zero]
  rfl

lemma φ_straightLine (hμ : 0 ≤ D.coroot i μ) : φ i (straightLine S μ) = D.coroot i μ := by
  rw [φ, minPairing_straightLine hμ, sub_zero, pairing_one, Int.floor_intCast, wt_straightLine]

/-! ### Connected components -/

/-- The connected component `B(π)` of a path `π` in the path crystal: the smallest set of paths
containing `π` and stable under all root operators ([Lit95] §2 (check)). -/
def component (π : LittelmannPath S) : Set (LittelmannPath S) := (crystal S).closure {π}

variable (π : LittelmannPath S)

lemma mem_component_self : π ∈ π.component := (crystal S).subset_closure {π} rfl

lemma isStable_component : (crystal S).IsStable π.component := Crystal.isStable_closure _

/-- The crystal structure on the connected component `B(π)`. For the straight line path `π_λ` of
a dominant weight this is Littelmann's crystal `B(λ)`. -/
noncomputable def componentCrystal : Crystal D π.component :=
  Crystal.restrict π.isStable_component

/-- The crystal `B(π)` is seminormal. -/
theorem isSeminormal_componentCrystal : π.componentCrystal.IsSeminormal :=
  (isSeminormal_crystal S).restrict π.isStable_component

/-- The number of paths of weight `rᵢ μ` in `B(π)` equals the number of paths of weight `μ` (both
possibly infinite, in which case `Nat.card` is `0`); a bijection is given by Kashiwara's `Sᵢ`. -/
theorem card_wt_reflection_component (i : ι) (μ : X) :
    Nat.card {b : π.component // b.1.wt = D.reflection i μ} =
      Nat.card {b : π.component // b.1.wt = μ} :=
  π.isSeminormal_componentCrystal.card_wt_reflection i μ

/-! ### The paths `f_{i₁} ⋯ f_{iₖ} π` -/

/-- `fWord [i₁, …, iₖ] π = f_{i₁} ⋯ f_{iₖ} π` (`none` if some step gives `0`). -/
noncomputable def fWord : List ι → LittelmannPath S → Option (LittelmannPath S)
  | [], π => some π
  | i :: l, π => (fWord l π).bind (f i)

/-- The set of paths `f_{i₁} ⋯ f_{iₖ} π`. -/
def fOrbit : Set (LittelmannPath S) := {π' | ∃ l, fWord l π = some π'}

variable {π}

lemma wt_of_fWord {l : List ι} {π' : LittelmannPath S} (h : fWord l π = some π') :
    π'.wt = π.wt - (l.map D.root).sum := by
  induction l generalizing π' with
  | nil =>
    cases h
    simp
  | cons i l ih =>
    obtain ⟨ρ, hρ, hf⟩ := Option.bind_eq_some_iff.mp h
    have := (crystal S).wt_f hf
    simp only [crystal_wt] at this
    rw [this, ih hρ, List.map_cons, List.sum_cons]
    abel

lemma fOrbit_subset_component : π.fOrbit ⊆ π.component := by
  rintro π' ⟨l, hl⟩
  induction l generalizing π' with
  | nil =>
    cases hl
    exact π.mem_component_self
  | cons i l ih =>
    obtain ⟨ρ, hρ, hf⟩ := Option.bind_eq_some_iff.mp hl
    exact π.isStable_component.f_mem i ρ π' (ih hρ) hf

/-- If the set `{f_{i₁} ⋯ f_{iₖ} π}` is stable under all `eⱼ`, then it is the connected component
`B(π)`. (Littelmann proves the hypothesis for paths `π` in the dominant chamber, [Lit95] §5–7
(check); this is not formalized here.) -/
theorem component_eq_fOrbit
    (h : ∀ π' ∈ π.fOrbit, ∀ j π'', e j π' = some π'' → π'' ∈ π.fOrbit) :
    π.component = π.fOrbit := by
  refine subset_antisymm (Crystal.closure_subset ⟨fun j π' π'' hπ' he ↦ h π' hπ' j π'' he,
    fun j π' π'' ⟨l, hl⟩ hf ↦ ⟨j :: l, by rw [fWord, hl, Option.bind_some]; exact hf⟩⟩
    (singleton_subset_iff.mpr ⟨[], rfl⟩)) fOrbit_subset_component

/-- If the set `{f_{i₁} ⋯ f_{iₖ} π}` is stable under all `eⱼ`, then the weights of `B(π)` lie in
`wt π - Q₊`. -/
theorem exists_wt_eq_of_mem_component
    (h : ∀ π' ∈ π.fOrbit, ∀ j π'', e j π' = some π'' → π'' ∈ π.fOrbit)
    {π' : LittelmannPath S} (hπ' : π' ∈ π.component) :
    ∃ s : Multiset ι, π'.wt = π.wt - (s.map D.root).sum := by
  rw [component_eq_fOrbit h] at hπ'
  obtain ⟨l, hl⟩ := hπ'
  exact ⟨l, by rw [wt_of_fWord hl, Multiset.map_coe, Multiset.sum_coe]⟩

/-- If the set `{f_{i₁} ⋯ f_{iₖ} π}` is stable under all `eⱼ` and the simple roots are linearly
independent (in the sense that `s ↦ ∑_{i ∈ s} αᵢ` is injective on multisets), then every weight
occurs only finitely often in `B(π)`. -/
theorem finite_wt_component
    (hroot : Function.Injective fun s : Multiset ι ↦ (s.map D.root).sum)
    (h : ∀ π' ∈ π.fOrbit, ∀ j π'', e j π' = some π'' → π'' ∈ π.fOrbit) (μ : X) :
    {π' ∈ π.component | π'.wt = μ}.Finite := by
  rw [component_eq_fOrbit h]
  rcases eq_empty_or_nonempty {π' ∈ π.fOrbit | π'.wt = μ} with h0 | ⟨π₀, ⟨l₀, hl₀⟩, hπ₀⟩
  · rw [h0]
    exact finite_empty
  refine ((List.finite_toSet l₀.permutations).image fun l ↦ (fWord l π).getD π).subset ?_
  rintro π' ⟨⟨l, hl⟩, hπ'⟩
  refine ⟨l, List.mem_permutations.mpr (Multiset.coe_eq_coe.mp (hroot ?_)), by simp [hl]⟩
  have h₁ := wt_of_fWord hl
  have h₂ := wt_of_fWord hl₀
  simp only [Multiset.map_coe, Multiset.sum_coe]
  rw [hπ', hπ₀] at *
  rw [h₁] at h₂
  exact sub_right_inj.mp h₂

end LittelmannPath
