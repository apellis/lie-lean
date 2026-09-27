/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.SerrePresented.Homology

/-!
# Lowest weight vectors of `𝔯̂₋` are dominant

Let `A` be a generalized Cartan matrix, `K` of characteristic zero, and `𝔤̂ = 𝔤̂(A)` the
Serre-presented algebra with radical `𝔯̂ = 𝔯̂₋ ⊕ 𝔯̂₊`. Let `x ∈ 𝔯̂₋` be a nonzero weight vector of
weight `-β`, `β = ∑ kⱼ αⱼ ∈ Q₊ \ {0}`, such that `𝔯̂₋` has no nonzero weight vectors of weight `-γ`
with `ht γ < ht β`. Then `[eᵢ, x] = 0` for all `i` (by minimality, since `[eᵢ, x] ∈ 𝔯̂` has weight
`αᵢ - β`), hence by `𝔰𝔩₂`-theory in the integrable algebra `𝔤̂` we get `⟨β, αᵢ^∨⟩ ≤ 0`, i.e.
`∑ⱼ aᵢⱼ kⱼ ≤ 0` for all `i`. This is the first step of the proof of the Gabber–Kac theorem
([Kac] §9.11 (check), [GK]); the argument is reconstructed.

## Main results

* `Matrix.Realization.SerrePresentedAlgebra.rootSpace_eq_bot_of_notMem`: `𝔤̂_μ = 0` unless
  `μ ∈ -(Q₊ \ {0}) ∪ {0} ∪ (Q₊ \ {0})`.
* `Matrix.Realization.SerrePresentedAlgebra.lie_e_eq_zero_of_minimal`: `[eᵢ, x] = 0`.
* `Matrix.Realization.SerrePresentedAlgebra.sum_mul_le_zero_of_minimal`: `∑ⱼ aᵢⱼ kⱼ ≤ 0`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.11 (check).
* [GK] O. Gabber, V. G. Kac, *On defining relations of certain infinite-dimensional Lie
  algebras*, Bull. Amer. Math. Soc. (N.S.) **5** (1981), 185–189.
-/

open FreeLieAlgebra Module LieModule LieAlgebra

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

omit [DecidableEq ι] in
lemma rootOf_apply_coroot (k : ι → ℤ) (i : ι) :
    P.rootOf k (P.coroot i) = ((∑ j, A i j * k j : ℤ) : K) := by
  simp [rootOf_apply, P.root_coroot, mul_comm]

namespace SerrePresentedAlgebra

/-- `𝔤̂_μ = 0` unless `μ` is `0` or `±α` for some `α ∈ Q₊ \ {0}`. -/
theorem rootSpace_eq_bot_of_notMem {μ : Dual K H} (hμ : μ ∉ AuxLieAlgebra.allWeights P) :
    rootSpace P μ = ⊥ := by
  have hdisj :=
    (iSupIndep_weightSpaceOfMap (M := P.SerrePresentedAlgebra) (h P)).disjoint_biSup hμ
  rwa [iSup_rootSpace_eq_top, disjoint_top] at hdisj

variable [CharZero K] (hA : A.IsGeneralizedCartan)

lemma sub_single_mem_posCone_or {k : ι → ℤ} (hk : k ∈ posCone ι) (i : ι) :
    k - Pi.single i 1 = 0 ∨ k - Pi.single i 1 ∈ posCone ι ∨
      -P.rootOf (k - Pi.single i 1) ∉ AuxLieAlgebra.allWeights P := by
  have hl : ∀ j, (k - Pi.single i 1 : ι → ℤ) j = k j - (Pi.single i 1 : ι → ℤ) j :=
    fun j ↦ rfl
  by_cases hl0 : k - Pi.single i 1 = 0
  · exact Or.inl hl0
  by_cases hlpos : 0 ≤ k - Pi.single i 1
  · exact Or.inr (Or.inl ⟨hlpos, hl0⟩)
  refine Or.inr (Or.inr ?_)
  rintro ((⟨m, hm, hml⟩ | hml) | ⟨m, hm, hml⟩)
  · rw [neg_inj, P.rootOf_injective.eq_iff] at hml
    exact hlpos (hml ▸ hm.1)
  · rw [Set.mem_singleton_iff, neg_eq_zero, ← map_zero P.rootOf,
      P.rootOf_injective.eq_iff] at hml
    exact hl0 hml
  · have hlm : k - Pi.single i 1 = -m := by
      apply P.rootOf_injective
      rw [map_neg, hml, neg_neg]
    obtain ⟨j', hj'⟩ : ∃ j', (k - Pi.single i 1 : ι → ℤ) j' < 0 := by
      by_contra! h; exact hlpos h
    have hki : k i = 0 := by
      by_cases hj'i : j' = i
      · subst hj'i
        rw [hl, Pi.single_eq_same] at hj'
        have := hk.1 j'
        simp only [Pi.zero_apply] at this
        omega
      · rw [hl, Pi.single_eq_of_ne hj'i, sub_zero] at hj'
        have := hk.1 j'
        simp only [Pi.zero_apply] at this
        omega
    apply hk.2
    funext j
    by_cases hji : j = i
    · subst hji; exact hki
    · have h1 := hl j
      rw [hlm, Pi.single_eq_of_ne hji, sub_zero] at h1
      have h2 := hk.1 j
      have h3 := hm.1 j
      simp only [Pi.neg_apply, Pi.zero_apply] at h1 h2 h3 ⊢
      omega

include hA in
/-- Let `x ∈ 𝔯̂₋` be a weight vector of weight `-β`, `β = ∑ kⱼ αⱼ ∈ Q₊ \ {0}`, such that `𝔯̂₋` has
no nonzero weight vectors of weight `-γ` with `ht γ < ht β`. Then `[eᵢ, x] = 0` for all `i`
([Kac] §9.11 (check); reconstructed argument). -/
theorem lie_e_eq_zero_of_minimal {k : ι → ℤ} (hk : k ∈ posCone ι)
    (hmin : ∀ l ∈ posCone ι, height l < height k →
      (radicalNeg P).toSubmodule ⊓ rootSpace P (-P.rootOf l) = ⊥)
    {x : P.SerrePresentedAlgebra} (hx : x ∈ radicalNeg P) (hxk : x ∈ rootSpace P (-P.rootOf k))
    (i : ι) : ⁅e P i, x⁆ = 0 := by
  have hyr : ⁅e P i, x⁆ ∈ radical P hA := (radical P hA).lie_mem (radicalNeg_le_radical P hA hx)
  have hyk : ⁅e P i, x⁆ ∈ rootSpace P (-P.rootOf (k - Pi.single i 1)) := by
    have := lie_mem_rootSpace P (e_mem_rootSpace P i) hxk
    rwa [map_sub, rootOf_single, neg_sub, sub_eq_add_neg]
  rcases sub_single_mem_posCone_or P hk i with hl | hl | hl
  · -- `β = αᵢ`
    have hki : k = Pi.single i 1 := sub_eq_zero.mp hl
    rw [hki, rootOf_single] at hxk
    have := (Submodule.eq_bot_iff _).mp (radical_inf_rootSpace_neg_root P hA i) x
      ⟨radicalNeg_le_radical P hA hx, hxk⟩
    rw [this, lie_zero]
  · -- `β - αᵢ ∈ Q₊ \ {0}`: use minimality
    have hyN : ⁅e P i, x⁆ ∈ (radicalNeg P).toSubmodule := by
      rw [radicalNeg_toSubmodule P hA]
      exact ⟨hyr, rootSpace_neg_le P ⟨_, hl, rfl⟩ hyk⟩
    have hlt : height (k - Pi.single i 1) < height k := by
      have := height_add (k - Pi.single i 1) (Pi.single i 1)
      rw [sub_add_cancel] at this
      have h1 : height (Pi.single i 1 : ι → ℤ) = 1 := by simp [height]
      omega
    exact (Submodule.eq_bot_iff _).mp (hmin _ hl hlt) _ ⟨hyN, hyk⟩
  · -- `αᵢ - β` is not a weight
    rw [rootSpace_eq_bot_of_notMem P hl] at hyk
    exact hyk

include hA in
/-- Under the hypotheses of `lie_e_eq_zero_of_minimal`, if `x ≠ 0` then `⟨β, αᵢ^∨⟩ ≤ 0` for all
`i`, i.e. `∑ⱼ aᵢⱼ kⱼ ≤ 0` ([Kac] §9.11 (check); reconstructed argument). -/
theorem sum_mul_le_zero_of_minimal {k : ι → ℤ} (hk : k ∈ posCone ι)
    (hmin : ∀ l ∈ posCone ι, height l < height k →
      (radicalNeg P).toSubmodule ⊓ rootSpace P (-P.rootOf l) = ⊥)
    {x : P.SerrePresentedAlgebra} (hx : x ∈ radicalNeg P) (hxk : x ∈ rootSpace P (-P.rootOf k))
    (hx0 : x ≠ 0) (i : ι) : ∑ j, A i j * k j ≤ 0 := by
  obtain ⟨n, hn⟩ := exists_nat_of_lie_e_eq_zero P hA i hxk hx0
    (lie_e_eq_zero_of_minimal P hA hk hmin hx hxk i)
  rw [LinearMap.neg_apply, rootOf_apply_coroot, neg_eq_iff_eq_neg] at hn
  have : (∑ j, A i j * k j : ℤ) = -n := by exact_mod_cast hn
  omega

end SerrePresentedAlgebra

end Matrix.Realization

end
