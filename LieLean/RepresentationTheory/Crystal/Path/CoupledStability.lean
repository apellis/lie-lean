/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.DominantIsomorphism

/-!
# A coupled two-color stability step for dominant continuous paths

## Main results

* `pairing_nonneg_of_f_f_coupled`: if both directed Cartan entries are negative, then
  `f_j (f_i π)` has nonnegative `i`-height for every dominant continuous path `π`.
* `e_mem_fOrbit_of_fWord_pair_coupled`: every raising operation at this genuinely
  mixed, coupled two-letter descendant stays in the lowering orbit.

## Scope and references

The proofs below are reconstructed directly from the closed running-minimum formula.
They do not assume LS data, integrality of intermediate minima, piecewise linearity,
symmetrizability, or a component isomorphism. They prove only a two-letter step.
Littelmann, Paths and root operators in representation theory, Ann. Math. 142 (1995),
499–525, Sections 1 and 7, Theorem 7.1 and Corollary 1, was consulted at
https://www.mi.uni-koeln.de/~littelma/papers/RootOperator.pdf . Its full isomorphism
statement concerns rational piecewise-linear paths modulo reparametrization, in the
symmetrizable setting; no full continuous-path isomorphism is asserted here.
-/

open Set

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜]
  [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {D : CartanDatum ι X} {V : Type*} [AddCommGroup V] [Module 𝕜 V]
  {S : D.PathSpace 𝕜 V} {π ρ η ζ : LittelmannPath S}

/-- A pointwise nonnegative height has minimum zero, since paths start at zero. -/
lemma minPairing_eq_zero_of_pairing_nonneg {i : ι}
    (hπ : ∀ t ∈ Icc (0 : 𝕜) 1, 0 ≤ π.pairing i t) : π.minPairing i = 0 := by
  obtain ⟨t, ht, heq⟩ := π.exists_minPairing i
  exact le_antisymm (π.minPairing_nonpos i) (heq ▸ hπ t ht)

/-- The closed lowering formula after applying an arbitrary simple coroot. -/
lemma pairing_of_f_eq_some {i j : ι} (hf : f i π = some ρ)
    {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) :
    ρ.pairing j t = π.pairing j t -
      (min (π.rightMin i t) (π.minPairing i + 1) - π.minPairing i) *
        (D.cartanMatrix j i : 𝕜) := by
  rw [pairing, f_apply hf ht, map_sub, map_smul, CartanDatum.PathSpace.coroot_root]
  rfl

/-- A first lowering in `i` followed by one in a coupled color `j` restores nonnegative
`i`-height. Both directed entries must be at most `-1`; no rank or edge-multiplicity
restriction is imposed. Direct running-minimum calculation, reconstructed here. -/
theorem pairing_nonneg_of_f_f_coupled {i j : ι}
    (hij : D.cartanMatrix i j ≤ -1) (hji : D.cartanMatrix j i ≤ -1)
    (hi : ∀ t ∈ Icc (0 : 𝕜) 1, 0 ≤ π.pairing i t)
    (hj : ∀ t ∈ Icc (0 : 𝕜) 1, 0 ≤ π.pairing j t)
    (hfi : f i π = some ρ) (hfj : f j ρ = some η)
    {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) : 0 ≤ η.pairing i t := by
  have hmi : π.minPairing i = 0 := minPairing_eq_zero_of_pairing_nonneg hi
  have hρj : ∀ s ∈ Icc (0 : 𝕜) 1, 0 ≤ ρ.pairing j s := fun s hs ↦
    (hj s hs).trans (pairing_le_of_f (hji.trans (by norm_num)) hfi hs)
  have hmj : ρ.minPairing j = 0 := minPairing_eq_zero_of_pairing_nonneg hρj
  let c := min (π.rightMin i t) 1
  have hc0 : 0 ≤ c := by
    have h := (loweringCoeff_mem_Icc π i ht).1
    simpa [hmi, c] using h
  have hc1 : c ≤ 1 := min_le_right _ _
  have hct : c ≤ π.pairing i t :=
    (min_le_left _ _).trans (π.rightMin_le ⟨le_rfl, ht.2⟩)
  have hcji : (D.cartanMatrix j i : 𝕜) ≤ -1 := by exact_mod_cast hji
  have hcij : (D.cartanMatrix i j : 𝕜) ≤ -1 := by exact_mod_cast hij
  have hcr : c ≤ ρ.rightMin j t := by
    apply ρ.le_rightMin ht.2
    intro s hs
    have hs' : s ∈ Icc (0 : 𝕜) 1 := ⟨ht.1.trans hs.1, hs.2⟩
    have hcs : c ≤ min (π.rightMin i s) 1 := by
      apply le_min _ hc1
      apply π.le_rightMin hs.2
      intro u hu
      exact (min_le_left _ _).trans (π.rightMin_le ⟨hs.1.trans hu.1, hu.2⟩)
    rw [pairing_of_f_eq_some hfi hs', hmi]
    simp only [zero_add, sub_zero]
    have hcprod := mul_nonpos_of_nonneg_of_nonpos
      (hc0.trans hcs) (show (D.cartanMatrix j i : 𝕜) + 1 ≤ 0 by linarith)
    have hjs := hj s hs'
    nlinarith
  have hcd : c ≤ min (ρ.rightMin j t) 1 := le_min hcr hc1
  have hdprod := mul_nonpos_of_nonneg_of_nonpos
    (hc0.trans hcd) (show (D.cartanMatrix i j : 𝕜) + 1 ≤ 0 by linarith)
  rw [pairing_of_f_eq_some hfj ht, pairing_of_f_eq_some hfi ht, hmi, hmj]
  simp only [zero_add, sub_zero, CartanDatum.cartanMatrix_self, Int.cast_ofNat]
  change 0 ≤ π.pairing i t - c * 2 - min (ρ.rightMin j t) 1 * _
  nlinarith

/-- On a coupled two-letter lowering word from a dominant path, raising in the first
applied color is impossible. This is not cancellation in the last applied color. -/
theorem e_eq_none_of_f_f_coupled {i j : ι}
    (hij : D.cartanMatrix i j ≤ -1) (hji : D.cartanMatrix j i ≤ -1)
    (hi : ∀ t ∈ Icc (0 : 𝕜) 1, 0 ≤ π.pairing i t)
    (hj : ∀ t ∈ Icc (0 : 𝕜) 1, 0 ≤ π.pairing j t)
    (hfi : f i π = some ρ) (hfj : f j ρ = some η) : e i η = none :=
  e_eq_none_of_pairing_nonneg fun _ ht ↦
    pairing_nonneg_of_f_f_coupled hij hji hi hj hfi hfj ht

/-- Genuine coupled two-color lowering-orbit stability: a successful raising operation
at `f_j f_i π` must be `e_j`, and returns exactly `f_i π`. The proof handles the
non-cancellation color using height restoration, not a stability hypothesis. -/
theorem e_f_f_coupled
    (hA : ∀ i j, i ≠ j → D.cartanMatrix i j ≤ 0)
    (hπ : ∀ i t, t ∈ Icc (0 : 𝕜) 1 → 0 ≤ π.pairing i t)
    {i j k : ι} (hij : D.cartanMatrix i j ≤ -1) (hji : D.cartanMatrix j i ≤ -1)
    (hfi : f i π = some ρ) (hfj : f j ρ = some η) (he : e k η = some ζ) :
    k = j ∧ ζ = ρ := by
  have hword : fWord [j, i] π = some η := by simp [fWord, hfi, hfj]
  have hkj : k = j := by
    by_contra hkj
    by_cases hki : k = i
    · subst k
      rw [e_eq_none_of_f_f_coupled hij hji (hπ i) (hπ j) hfi hfj] at he
      contradiction
    · have hkn : k ∉ [j, i] := by simp [hkj, hki]
      rw [e_eq_none_of_fWord_not_mem hA hπ hkn hword] at he
      contradiction
  subst k
  exact ⟨rfl, Option.some.inj (he.symm.trans (f_eq_some_iff.mp hfj))⟩

/-- All raising operators preserve the lowering orbit at a two-letter descendant whose
two colors are coupled. No assumption equivalent to the desired stability is used. -/
theorem e_mem_fOrbit_of_fWord_pair_coupled
    (hA : ∀ i j, i ≠ j → D.cartanMatrix i j ≤ 0)
    (hπ : ∀ i t, t ∈ Icc (0 : 𝕜) 1 → 0 ≤ π.pairing i t)
    {i j k : ι} (hij : D.cartanMatrix i j ≤ -1) (hji : D.cartanMatrix j i ≤ -1)
    (hf : fWord [j, i] π = some η) (he : e k η = some ζ) : ζ ∈ π.fOrbit := by
  obtain ⟨ρ, hρ, hfj⟩ := Option.bind_eq_some_iff.mp hf
  have hfi : f i π = some ρ := by simpa [fWord] using hρ
  obtain ⟨_, rfl⟩ := e_f_f_coupled hA hπ hij hji hfi hfj he
  exact ⟨[i], by simpa [fWord] using hfi⟩

/-- The coupled two-letter situation is nonvacuous whenever the initial `i`-height at
one is at least one. Lowering in `i` creates enough `j`-height for the second step. -/
theorem exists_f_f_coupled {i j : ι} (hji : D.cartanMatrix j i ≤ -1)
    (hi : ∀ t ∈ Icc (0 : 𝕜) 1, 0 ≤ π.pairing i t)
    (hj : ∀ t ∈ Icc (0 : 𝕜) 1, 0 ≤ π.pairing j t)
    (hi1 : 1 ≤ π.pairing i 1) :
    ∃ ρ η, f i π = some ρ ∧ f j ρ = some η := by
  have hmi : π.minPairing i = 0 := minPairing_eq_zero_of_pairing_nonneg hi
  have hfi : f i π ≠ none := by
    intro h
    have := f_eq_none_iff.mp h
    rw [hmi] at this
    linarith
  obtain ⟨ρ, hρ⟩ := Option.ne_none_iff_exists'.mp hfi
  have hr : π.rightMin i 1 = π.pairing i 1 := by
    apply le_antisymm (π.rightMin_le ⟨le_rfl, le_rfl⟩)
    apply π.le_rightMin le_rfl
    intro s hs
    have : s = 1 := le_antisymm hs.2 hs.1
    subst s
    exact le_rfl
  have hρ1 : 1 ≤ ρ.pairing j 1 := by
    rw [pairing_of_f_eq_some hρ ⟨zero_le_one, le_rfl⟩, hmi, hr]
    simp only [zero_add, sub_zero, min_eq_right hi1, one_mul]
    have ha : (D.cartanMatrix j i : 𝕜) ≤ -1 := by exact_mod_cast hji
    have := hj 1 ⟨zero_le_one, le_rfl⟩
    linarith
  have hfj : f j ρ ≠ none := by
    intro h
    have := f_eq_none_iff.mp h
    have := ρ.minPairing_nonpos j
    linarith
  obtain ⟨η, hη⟩ := Option.ne_none_iff_exists'.mp hfj
  exact ⟨ρ, η, hρ, hη⟩

end LittelmannPath
