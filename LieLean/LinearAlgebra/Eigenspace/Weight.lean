/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Finsupp.Span

/-!
# Weight spaces for a linear family of endomorphisms

Let `T : H →ₗ[K] End K M` be a linear family of endomorphisms of a vector space `M` (for instance
the action of a Cartan subalgebra `𝔥` on a Chevalley–Eilenberg complex). For `μ ∈ H*`, the weight
space is `M_μ = {m | T a m = μ(a) m for all a}`. This file contains the basic linear algebra of
such weight spaces; `LieLean.Algebra.Lie.Weights.OfMap` specializes it to Lie modules (the family
`a ↦ ⁅φ a, ·⁆`). Unlike for Mathlib's simultaneous generalized eigenspaces
(`Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`), no commutativity of the
family is needed.

## Main definitions

* `Module.End.weightSpaceOf`: the weight space `M_μ`.

## Main results

* `iSupIndep.mem_of_mem_iSup_of_le`: if `N i ≤ M i` for an independent family `M` and
  `x ∈ M i ∩ ⨆ j, N j`, then `x ∈ N i`.
* `Module.End.iSupIndep_weightSpaceOf`: weight spaces for distinct weights are independent.
* `Module.End.inf_iSup_weightSpaceOf_le`: a subspace stable under the family meets the sum of the
  weight spaces in the sum of its intersections with the weight spaces.
* `Module.End.mem_of_mem_iSup_of_le`: if `N ν ⊆ M_ν` for all `ν`, then `M_μ ∩ ⨆ ν, N ν ⊆ N μ`.

## References

Elementary linear algebra (the usual argument that eigenvectors for distinct eigenvalues are
linearly independent); no specific reference.
-/

open Module

/-- If `N i ≤ M i` for an independent family `M`, and `x ∈ M i` lies in `⨆ j, N j`, then
`x ∈ N i`. -/
theorem iSupIndep.mem_of_mem_iSup_of_le {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {F G : ι → Submodule R M} (hG : iSupIndep G) (hFG : ∀ j, F j ≤ G j) {i : ι} {x : M}
    (hx : x ∈ G i) (hx' : x ∈ ⨆ j, F j) : x ∈ F i := by
  classical
  rw [iSup_split_single F i, Submodule.mem_sup] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  have hb' : b ∈ G i := by
    have := Submodule.sub_mem _ hx (hFG i ha)
    rwa [add_sub_cancel_left] at this
  have hb'' : b ∈ ⨆ (j) (_ : j ≠ i), G j := (iSup₂_mono fun j _ ↦ hFG j) hb
  have := Submodule.disjoint_def.mp (hG i) b hb' hb''
  rwa [this, add_zero]

namespace Module.End

variable {K H M : Type*} [Field K] [AddCommGroup H] [Module K H] [AddCommGroup M] [Module K M]
  (T : H →ₗ[K] Module.End K M)

/-- The weight space `M_μ = {m | T a m = μ(a) m for all a}`. -/
def weightSpaceOf (μ : Dual K H) : Submodule K M where
  carrier := {m | ∀ a, T a m = μ a • m}
  add_mem' hx hy a := by simp [map_add, hx a, hy a, smul_add]
  zero_mem' a := by simp
  smul_mem' c x hx a := by simp [map_smul, hx a, smul_comm c]

variable {T}

lemma mem_weightSpaceOf {μ : Dual K H} {m : M} :
    m ∈ weightSpaceOf T μ ↔ ∀ a, T a m = μ a • m := Iff.rfl

variable (T)

/-- If a finite sum of weight vectors of distinct weights lies in a subspace `N` stable under the
family, then so does each summand. -/
theorem mem_of_sum_mem (N : Submodule K M) (hN : ∀ a, ∀ m ∈ N, T a m ∈ N)
    (s : Finset (Dual K H)) (x : Dual K H → M) (hx : ∀ μ ∈ s, x μ ∈ weightSpaceOf T μ)
    (hsum : ∑ μ ∈ s, x μ ∈ N) : ∀ μ ∈ s, x μ ∈ N := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert β s hβ ih =>
    rw [Finset.sum_insert hβ] at hsum
    have hs : ∀ γ ∈ s, x γ ∈ N := by
      intro γ hγ
      have hne : γ ≠ β := fun h ↦ hβ (h ▸ hγ)
      obtain ⟨a, ha⟩ : ∃ a, γ a ≠ β a := by
        by_contra! h'; exact hne (LinearMap.ext h')
      let y : Dual K H → M := fun μ ↦ (μ a - β a) • x μ
      have hy : ∀ μ ∈ s, y μ ∈ weightSpaceOf T μ := fun μ hμ ↦
        Submodule.smul_mem _ _ (hx μ (Finset.mem_insert_of_mem hμ))
      have hysum : ∑ μ ∈ s, y μ ∈ N := by
        have h1 := N.sub_mem (hN a _ hsum) (N.smul_mem (β a) hsum)
        convert h1 using 1
        simp only [map_add, map_sum, smul_add, Finset.smul_sum, y, sub_smul]
        rw [(hx β (Finset.mem_insert_self β s)) a, Finset.sum_sub_distrib]
        rw [Finset.sum_congr rfl fun μ hμ ↦ (hx μ (Finset.mem_insert_of_mem hμ)) a]
        abel
      have := ih y hy hysum γ hγ
      have hc : γ a - β a ≠ 0 := sub_ne_zero.mpr ha
      simpa [y, hc] using N.smul_mem (γ a - β a)⁻¹ this
    intro μ hμ
    rcases Finset.mem_insert.mp hμ with rfl | hμ
    · have := N.sub_mem hsum (N.sum_mem hs)
      simpa using this
    · exact hs μ hμ

/-- A subspace stable under the family meets the sum of the weight spaces in the sum of its
intersections with the weight spaces. -/
theorem inf_iSup_weightSpaceOf_le (N : Submodule K M) (hN : ∀ a, ∀ m ∈ N, T a m ∈ N) :
    N ⊓ ⨆ μ, weightSpaceOf T μ ≤ ⨆ μ, (N ⊓ weightSpaceOf T μ) := by
  classical
  intro m hm
  obtain ⟨hmN, hm⟩ := Submodule.mem_inf.mp hm
  rw [Submodule.mem_iSup_iff_exists_finset] at hm
  obtain ⟨s, hs⟩ := hm
  rw [Submodule.mem_iSup_finset_iff_exists_sum] at hs
  obtain ⟨x, rfl⟩ := hs
  have hmem := mem_of_sum_mem T N hN s (fun μ ↦ x μ) (fun μ _ ↦ (x μ).2) hmN
  exact Submodule.sum_mem _ fun μ hμ ↦ Submodule.mem_iSup_of_mem μ ⟨hmem μ hμ, (x μ).2⟩

/-- Weight spaces for distinct weights are independent. -/
theorem iSupIndep_weightSpaceOf : iSupIndep fun μ : Dual K H ↦ weightSpaceOf T μ := by
  classical
  intro μ
  rw [Submodule.disjoint_def]
  intro m hm hm'
  have hm'' : m ∈ ⨆ ν ∈ {ν | ν ≠ μ}, weightSpaceOf T ν := by simpa using hm'
  rw [← iSup_subtype'', Submodule.mem_iSup_iff_exists_finset] at hm''
  obtain ⟨s, hs⟩ := hm''
  rw [Submodule.mem_iSup_finset_iff_exists_sum] at hs
  obtain ⟨x, hx⟩ := hs
  let s' : Finset (Dual K H) := insert μ (s.map (Function.Embedding.subtype _))
  have hμs : μ ∉ s.map (Function.Embedding.subtype _) := by simp
  let x' : Dual K H → M := fun ν ↦
    if h : ν = μ then -m else if h' : ν ≠ μ then (x ⟨ν, h'⟩ : M) else 0
  have hx' : ∀ ν ∈ s', x' ν ∈ weightSpaceOf T ν := by
    intro ν hν
    by_cases h : ν = μ
    · subst h; simpa [x'] using Submodule.neg_mem _ hm
    · simp [x', h]
  have hsum : ∑ ν ∈ s', x' ν = 0 := by
    rw [Finset.sum_insert hμs, Finset.sum_map]
    have h1 : ∀ ν ∈ s, x' ((Function.Embedding.subtype _) ν) = (x ν : M) := by
      intro ν _
      have hν : (ν : Dual K H) ≠ μ := ν.2
      simp [x', hν]
      rfl
    rw [Finset.sum_congr rfl h1, hx]
    simp [x']
  have := mem_of_sum_mem T ⊥ (by simp) s' x' hx' (hsum ▸ Submodule.zero_mem _)
    μ (Finset.mem_insert_self _ _)
  simpa [x'] using this

/-- If `N ν ≤ M_ν` for all `ν` and a weight vector `x ∈ M_μ` lies in `⨆ ν, N ν`, then `x ∈ N μ`. -/
theorem mem_of_mem_iSup_of_le (N : Dual K H → Submodule K M)
    (hN : ∀ ν, N ν ≤ weightSpaceOf T ν) {μ : Dual K H} {x : M}
    (hx : x ∈ weightSpaceOf T μ) (hx' : x ∈ ⨆ ν, N ν) : x ∈ N μ :=
  (iSupIndep_weightSpaceOf T).mem_of_mem_iSup_of_le hN hx hx'

end Module.End
