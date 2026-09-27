/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.OfAssociative
import LieLean.LinearAlgebra.Eigenspace.Weight

/-!
# Weight spaces with respect to a linear map into a Lie algebra

Let `L` be a Lie algebra over a field `K`, `H` a `K`-vector space and `φ : H →ₗ[K] L` a linear
map (typically the inclusion of a Cartan subalgebra `𝔥`, which in Kac–Moody theory is a vector
space given in advance rather than a Lie subalgebra). For an `L`-module `M` and `μ ∈ H*`, the
weight space `M_μ` is the space of `m ∈ M` with `φ(a) • m = μ(a) m` for all `a ∈ H`. It is the
weight space `Module.End.weightSpaceOf` of the linear family `a ↦ ⁅φ a, ·⁆`
(`LieModule.weightSpaceOfMap_eq_weightSpaceOf`), and the results below are specializations of
those of `LieLean.LinearAlgebra.Eigenspace.Weight`.

## Main definitions

* `LieModule.weightSpaceOfMap`: the weight space `M_μ`.

## Main results

* `LieModule.iSupIndep_weightSpaceOfMap`: weight spaces for distinct weights are independent.
* `LieModule.mem_weightSpaceOfMap_of_sum_mem`, `LieModule.inf_iSup_weightSpaceOfMap_le`: a
  subspace stable under `φ(H)` which is contained in a sum of weight spaces is the sum of its
  intersections with the weight spaces.
* `LieModule.mem_of_mem_iSup_of_le`: if `N ν ⊆ M_ν` for all `ν`, then
  `M_μ ∩ ⨆ ν, N ν ⊆ N μ`.
* `LieModule.lie_mem_weightSpaceOfMap`: `L_μ • M_ν ⊆ M_{μ+ν}`.

## References

Elementary linear algebra; see `LieLean.LinearAlgebra.Eigenspace.Weight`.
-/

open Module

namespace LieModule

variable {K H L M : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  (φ : H →ₗ[K] L)

variable (M) in
/-- The weight space `M_μ = {m | ∀ a, φ(a) • m = μ(a) m}`. -/
def weightSpaceOfMap (μ : Dual K H) : Submodule K M where
  carrier := {m | ∀ a, ⁅φ a, m⁆ = μ a • m}
  add_mem' hx hy a := by simp [lie_add, hx a, hy a, smul_add]
  zero_mem' a := by simp
  smul_mem' c x hx a := by simp [lie_smul, hx a, smul_comm c]

lemma mem_weightSpaceOfMap {μ : Dual K H} {m : M} :
    m ∈ weightSpaceOfMap M φ μ ↔ ∀ a, ⁅φ a, m⁆ = μ a • m := Iff.rfl

variable (M) in
/-- `M_μ` is the weight space of the linear family `a ↦ ⁅φ a, ·⁆` of endomorphisms of `M`. -/
theorem weightSpaceOfMap_eq_weightSpaceOf (μ : Dual K H) :
    weightSpaceOfMap M φ μ =
      Module.End.weightSpaceOf ((toEnd K L M : L →ₗ[K] Module.End K M) ∘ₗ φ) μ :=
  rfl

/-- If a finite sum of weight vectors of distinct weights lies in a subspace `N` stable under
`φ(H)`, then so does each summand. -/
theorem mem_weightSpaceOfMap_of_sum_mem (N : Submodule K M) (hN : ∀ a, ∀ m ∈ N, ⁅φ a, m⁆ ∈ N)
    (s : Finset (Dual K H)) (x : Dual K H → M) (hx : ∀ μ ∈ s, x μ ∈ weightSpaceOfMap M φ μ)
    (hsum : ∑ μ ∈ s, x μ ∈ N) : ∀ μ ∈ s, x μ ∈ N :=
  Module.End.mem_of_sum_mem ((toEnd K L M : L →ₗ[K] Module.End K M) ∘ₗ φ) N hN s x hx hsum

/-- A subspace stable under `φ(H)` meets the sum of the weight spaces in the sum of its
intersections with the weight spaces. -/
theorem inf_iSup_weightSpaceOfMap_le (N : Submodule K M) (hN : ∀ a, ∀ m ∈ N, ⁅φ a, m⁆ ∈ N)
    (S : Set (Dual K H)) :
    N ⊓ ⨆ μ ∈ S, weightSpaceOfMap M φ μ ≤ ⨆ μ ∈ S, (N ⊓ weightSpaceOfMap M φ μ) := by
  classical
  intro m hm
  obtain ⟨hmN, hm⟩ := Submodule.mem_inf.mp hm
  rw [← iSup_subtype'', Submodule.mem_iSup_iff_exists_finset] at hm
  obtain ⟨s, hs⟩ := hm
  rw [Submodule.mem_iSup_finset_iff_exists_sum] at hs
  obtain ⟨x, rfl⟩ := hs
  let s' : Finset (Dual K H) := s.map (Function.Embedding.subtype _)
  let x' : Dual K H → M := fun μ ↦ if h : μ ∈ S then (x ⟨μ, h⟩ : M) else 0
  have hx' : ∀ μ ∈ s', x' μ ∈ weightSpaceOfMap M φ μ := by
    intro μ hμ
    obtain ⟨⟨μ, hμS⟩, -, rfl⟩ := Finset.mem_map.mp hμ
    simp [x', hμS]
  have hsum : ∑ μ ∈ s', x' μ = ∑ i ∈ s, (x i : M) := by
    simp [s', x']
  have hmem := mem_weightSpaceOfMap_of_sum_mem φ N hN s' x' hx' (hsum ▸ hmN)
  rw [← hsum]
  refine Submodule.sum_mem _ fun μ hμ ↦ ?_
  obtain ⟨⟨μ, hμS⟩, -, rfl⟩ := Finset.mem_map.mp hμ
  exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμS ⟨hmem _ hμ, hx' _ hμ⟩)

/-- Weight spaces for distinct weights are independent. -/
theorem iSupIndep_weightSpaceOfMap :
    iSupIndep fun μ : Dual K H ↦ weightSpaceOfMap M φ μ :=
  Module.End.iSupIndep_weightSpaceOf ((toEnd K L M : L →ₗ[K] Module.End K M) ∘ₗ φ)

/-- If `N ν ≤ M_ν` for all `ν` and a weight vector `x ∈ M_μ` lies in `⨆ ν, N ν`, then `x ∈ N μ`. -/
theorem mem_of_mem_iSup_of_le (N : Dual K H → Submodule K M)
    (hN : ∀ ν, N ν ≤ weightSpaceOfMap M φ ν) {μ : Dual K H} {x : M}
    (hx : x ∈ weightSpaceOfMap M φ μ) (hx' : x ∈ ⨆ ν, N ν) : x ∈ N μ :=
  (iSupIndep_weightSpaceOfMap (M := M) φ).mem_of_mem_iSup_of_le hN hx hx'

/-- `L_μ • M_ν ⊆ M_{μ+ν}`. -/
theorem lie_mem_weightSpaceOfMap {μ ν : Dual K H} {x : L} {m : M}
    (hx : x ∈ weightSpaceOfMap L φ μ) (hm : m ∈ weightSpaceOfMap M φ ν) :
    ⁅x, m⁆ ∈ weightSpaceOfMap M φ (μ + ν) := by
  intro a
  rw [leibniz_lie, hx a, hm a, smul_lie, lie_smul, LinearMap.add_apply, add_smul]

end LieModule
