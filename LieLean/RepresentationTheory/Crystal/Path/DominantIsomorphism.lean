/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Isomorphism

/-!
# Lowering words from arbitrary dominant paths

## Main results

* `pairing_le_of_fWord_not_mem`: lowering in colors other than `j` cannot decrease the
  `j`-height, provided the Cartan matrix has nonpositive off-diagonal entries.
* `e_eq_none_of_fWord_not_mem`: a raising color at a descendant of a dominant path must
  occur in its lowering word.
* `e_mem_fOrbit_of_fWord_replicate`: every raising operator preserves the lowering orbit
  at a monochromatic descendant of an arbitrary dominant path.
* `component_eq_fOrbit_of_subsingleton`: in rank at most one, the component of any
  dominant path is its lowering orbit, without an LS or straight-line hypothesis.

## Scope and references

These are direct proofs from the closed root-operator formula, reconstructed here, not
claims of the full isomorphism theorem. They apply to the repository's continuous,
parametrized paths. Littelmann, *Paths and root operators in representation theory*,
Ann. of Math. 142 (1995), 499–525, Section 1 and Theorem 7.1. The source's Theorem 7.1
concerns piecewise-linear rational paths, modulo reparametrization, in the dominant chamber
with integral endpoint, for a symmetrizable Kac–Moody algebra. Extending it to all continuous
paths in the current interface is a further assertion, not something justified by that citation.

For higher rank, raising in a color already present in a mixed lowering word is still open
here. Even full lowering-orbit stability would leave the independence of word relations
from the choice of dominant path to prove; `LRIsomorphismHypothesis` is not discharged.
-/

open Set

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜]
  [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {D : CartanDatum ι X} {V : Type*} [AddCommGroup V] [Module 𝕜 V]
  {S : D.PathSpace 𝕜 V} {π η : LittelmannPath S}

/-- The coefficient subtracted by a lowering operator lies in `[0,1]` at every time.
Direct consequence of the closed formula `f_apply` (reconstructed proof). -/
lemma loweringCoeff_mem_Icc (π : LittelmannPath S) (i : ι) {t : 𝕜}
    (ht : t ∈ Icc (0 : 𝕜) 1) :
    min (π.rightMin i t) (π.minPairing i + 1) - π.minPairing i ∈ Icc (0 : 𝕜) 1 := by
  have hm : π.minPairing i ≤ π.rightMin i t :=
    π.le_rightMin ht.2 fun s hs ↦ π.minPairing_le ⟨ht.1.trans hs.1, hs.2⟩
  constructor
  · exact sub_nonneg.mpr (le_min hm (by linarith))
  · have := min_le_right (π.rightMin i t) (π.minPairing i + 1)
    linarith

/-- Lowering in a color with nonpositive `j`-Cartan entry increases the `j`-height
pointwise. Direct calculation from `f_apply` (reconstructed proof). -/
lemma pairing_le_of_f {i j : ι} (hji : D.cartanMatrix j i ≤ 0)
    (hf : f i π = some η) {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) :
    π.pairing j t ≤ η.pairing j t := by
  have ha : (D.cartanMatrix j i : 𝕜) ≤ 0 := by exact_mod_cast hji
  have hc := (loweringCoeff_mem_Icc π i ht).1
  rw [pairing, pairing, f_apply hf ht, map_sub, map_smul,
    CartanDatum.PathSpace.coroot_root]
  change π.pairing j t ≤ π.pairing j t - _ * (D.cartanMatrix j i : 𝕜)
  have := mul_nonpos_of_nonneg_of_nonpos hc ha
  linarith

/-- A lowering word avoiding `j` cannot decrease the `j`-height. Only off-diagonal
nonpositivity is used; this is a direct induction, not an isomorphism hypothesis. -/
theorem pairing_le_of_fWord_not_mem
    (hA : ∀ i j, i ≠ j → D.cartanMatrix i j ≤ 0)
    {l : List ι} {j : ι} (hj : j ∉ l) (hf : fWord l π = some η)
    {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) : π.pairing j t ≤ η.pairing j t := by
  induction l generalizing η with
  | nil =>
    have : π = η := Option.some.inj hf
    subst η
    exact le_rfl
  | cons i l ih =>
    obtain ⟨ρ, hρ, hη⟩ := Option.bind_eq_some_iff.mp hf
    have hji : j ≠ i := fun h ↦ hj (by simp [h])
    have hjl : j ∉ l := fun h ↦ hj (List.mem_cons_of_mem i h)
    exact (ih hjl hρ).trans (pairing_le_of_f (hA j i hji) hη ht)

/-- Nonnegative `j`-height rules out `e_j`, directly by the minimum criterion. -/
lemma e_eq_none_of_pairing_nonneg {j : ι}
    (hπ : ∀ t ∈ Icc (0 : 𝕜) 1, 0 ≤ π.pairing j t) : e j π = none := by
  obtain ⟨t, ht, heq⟩ := π.exists_minPairing j
  apply e_eq_none_iff.mpr
  have := hπ t ht
  rw [heq] at this
  linarith

/-- At a descendant of a dominant path, a raising color must have occurred in the
lowering word. Reconstructed from off-diagonal nonpositivity and `f_apply`. -/
theorem e_eq_none_of_fWord_not_mem
    (hA : ∀ i j, i ≠ j → D.cartanMatrix i j ≤ 0)
    (hπ : ∀ i t, t ∈ Icc (0 : 𝕜) 1 → 0 ≤ π.pairing i t)
    {l : List ι} {j : ι} (hj : j ∉ l) (hf : fWord l π = some η) : e j η = none := by
  apply e_eq_none_of_pairing_nonneg
  intro t ht
  exact (hπ j t ht).trans (pairing_le_of_fWord_not_mem hA hj hf ht)

/-- At a monochromatic descendant of a dominant path, every successful raising operation
removes one letter of that word. Other colors cannot raise. This proves the monochromatic
case of arbitrary-dominant-path lowering-orbit stability, by a direct reconstructed proof. -/
theorem e_fWord_replicate
    (hA : ∀ i j, i ≠ j → D.cartanMatrix i j ≤ 0)
    (hπ : ∀ i t, t ∈ Icc (0 : 𝕜) 1 → 0 ≤ π.pairing i t)
    {i j : ι} {n : ℕ} {ζ : LittelmannPath S}
    (hf : fWord (List.replicate n i) π = some η) (he : e j η = some ζ) :
    j = i ∧ ∃ m, n = m + 1 ∧ fWord (List.replicate m i) π = some ζ := by
  have hji : j = i := by
    by_contra h
    have hj : j ∉ List.replicate n i := by simp [h]
    rw [e_eq_none_of_fWord_not_mem hA hπ hj hf] at he
    contradiction
  subst j
  cases n with
  | zero =>
    have hπη : π = η := Option.some.inj hf
    subst η
    rw [e_eq_none_of_pairing_nonneg (hπ i)] at he
    contradiction
  | succ m =>
    obtain ⟨ρ, hρ, hη⟩ := Option.bind_eq_some_iff.mp hf
    have hρζ : ρ = ζ := Option.some.inj ((f_eq_some_iff.mp hη).symm.trans he)
    exact ⟨rfl, m, rfl, hρζ ▸ hρ⟩

/-- Raising at a monochromatic descendant of any dominant path stays in its lowering
orbit. This does not assert stability at mixed-color descendants. -/
theorem e_mem_fOrbit_of_fWord_replicate
    (hA : ∀ i j, i ≠ j → D.cartanMatrix i j ≤ 0)
    (hπ : ∀ i t, t ∈ Icc (0 : 𝕜) 1 → 0 ≤ π.pairing i t)
    {i j : ι} {n : ℕ} {ζ : LittelmannPath S}
    (hf : fWord (List.replicate n i) π = some η) (he : e j η = some ζ) :
    ζ ∈ π.fOrbit := by
  obtain ⟨_, m, _, hm⟩ := e_fWord_replicate hA hπ hf he
  exact ⟨List.replicate m i, hm⟩

variable [FloorRing 𝕜]

/-- Rank-at-most-one stability for arbitrary dominant paths. Reconstructed using cancellation
of `e_i f_i`; no LS, piecewise-linearity, or isomorphism hypothesis is imposed. -/
theorem component_eq_fOrbit_of_subsingleton [Subsingleton ι]
    (hπ : ∀ i t, t ∈ Icc (0 : 𝕜) 1 → 0 ≤ π.pairing i t) :
    π.component = π.fOrbit := by
  apply component_eq_fOrbit
  rintro η ⟨l, hl⟩ j ζ he
  cases l with
  | nil =>
    have hπη : π = η := Option.some.inj hl
    subst η
    rw [e_eq_none_of_pairing_nonneg (hπ j)] at he
    contradiction
  | cons i l =>
    obtain ⟨ρ, hρ, hη⟩ := Option.bind_eq_some_iff.mp hl
    have hij : i = j := Subsingleton.elim _ _
    subst i
    have hρζ : ρ = ζ := Option.some.inj ((f_eq_some_iff.mp hη).symm.trans he)
    exact ⟨l, hρζ ▸ hρ⟩

end LittelmannPath
