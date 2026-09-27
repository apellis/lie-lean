/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterVerma
import LieLean.Algebra.Lie.KacMoody.InvariantForm

/-!
# The nilradical `𝔲ᵢ⁻` of the opposite minimal parabolic subalgebra

Let `𝔤 = 𝔤(A)` be a Kac–Moody algebra and `i` a simple index. The subspace
`𝔲ᵢ⁻ = ⊕_{α ∈ Q₊ \ {0, αᵢ}} 𝔤_{-α}` of `𝔫₋` is a Lie subalgebra, stable under `ad eᵢ`, `ad fᵢ` and
`ad 𝔥`, and `𝔫₋ = K fᵢ ⊕ 𝔲ᵢ⁻` ([Kac] §3.? (check); [Kum] §1.? (check)). By PBW,
`U(𝔫₋) = K[fᵢ] ⊗ U(𝔲ᵢ⁻)`; this is used to show that Verma modules are projective "in the direction
of the `𝔰𝔩₂`-subalgebra `⟨eᵢ, fᵢ, αᵢ^∨⟩`".

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.nilradNeg`: the subspace `𝔲ᵢ⁻` of `𝔤(A)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.nilradNeg_le_nNeg`,
  `Matrix.Realization.KacMoodyAlgebra.nNeg_eq_span_f_sup_nilradNeg`,
  `Matrix.Realization.KacMoodyAlgebra.disjoint_span_f_nilradNeg`: `𝔫₋ = K fᵢ ⊕ 𝔲ᵢ⁻`.
* `Matrix.Realization.KacMoodyAlgebra.lie_mem_nilradNeg`, `lie_e_mem_nilradNeg`,
  `lie_f_mem_nilradNeg`, `lie_h_mem_nilradNeg`: `𝔲ᵢ⁻` is a subalgebra, stable under
  `ad eᵢ`, `ad fᵢ`, `ad 𝔥`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §1.3, §3.6 (check).
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-! ### Weights of `𝔤(A)` -/

/-- A weight `∑ kⱼ αⱼ` of `𝔤(A)` has all `kⱼ ≥ 0` or all `kⱼ ≤ 0`. -/
lemma nonneg_or_nonpos_of_rootSpace_ne_bot {k : ι → ℤ} (hk : rootSpace P (P.rootOf k) ≠ ⊥) :
    0 ≤ k ∨ k ≤ 0 := by
  by_contra hcon
  push Not at hcon
  refine hk ?_
  rw [rootSpace_eq_map, AuxLieAlgebra.rootSpace_eq_bot, Submodule.map_bot]
  rintro ((⟨l, hl, hkl⟩ | hk0) | ⟨l, hl, hkl⟩)
  · have : k = -l := P.rootOf_injective (by rw [map_neg]; exact hkl.symm)
    exact hcon.2 (by rw [this]; exact neg_nonpos.mpr hl.1)
  · have : k = 0 := P.rootOf_injective (by rw [map_zero]; exact hk0)
    exact hcon.1 (le_of_eq this.symm)
  · have : k = l := P.rootOf_injective hkl.symm
    exact hcon.1 (this ▸ hl.1)

/-- `𝔤_{-2αᵢ} = 0`. -/
lemma rootSpace_neg_two_smul_root_eq_bot (i : ι) : rootSpace P (-(2 • P.root i)) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  have h1 := chevalleyInvolution_mem_rootSpace P hx
  rw [neg_neg, rootSpace_nsmul_root_eq_bot P i le_rfl, Submodule.mem_bot] at h1
  rw [Submodule.mem_bot]
  have := congrArg (chevalleyInvolution P) h1
  rwa [chevalleyInvolution_chevalleyInvolution, map_zero] at this

omit [CharZero K] in
/-- `x ∈ ⨆_{μ ∈ S} 𝔤_μ` and `y ∈ ⨆_{ν ∈ T} 𝔤_ν` give `[x, y] ∈ ⨆_{ρ ∈ R} 𝔤_ρ` if every sum
`μ + ν` of weights `μ ∈ S`, `ν ∈ T` with nonzero root spaces `𝔤_μ, 𝔤_ν, 𝔤_{μ+ν}` lies in `R`. -/
lemma lie_mem_iSup_rootSpace {S T R : Set (Dual K H)}
    (hST : ∀ μ ∈ S, ∀ ν ∈ T, rootSpace P μ ≠ ⊥ → rootSpace P ν ≠ ⊥ →
      rootSpace P (μ + ν) ≠ ⊥ → μ + ν ∈ R)
    {x y : P.KacMoodyAlgebra} (hx : x ∈ ⨆ μ ∈ S, rootSpace P μ)
    (hy : y ∈ ⨆ ν ∈ T, rootSpace P ν) : ⁅x, y⁆ ∈ ⨆ ρ ∈ R, rootSpace P ρ := by
  rw [← iSup_subtype''] at hx hy
  induction hx using Submodule.iSup_induction' with
  | zero => rw [zero_lie]; exact zero_mem _
  | add x x' _ _ hx hx' => rw [add_lie]; exact add_mem hx hx'
  | mem μ x hx =>
    induction hy using Submodule.iSup_induction' with
    | zero => rw [lie_zero]; exact zero_mem _
    | add y y' _ _ hy hy' => rw [lie_add]; exact add_mem hy hy'
    | mem ν y hy =>
      have hxy := lie_mem_weightSpaceOfMap (h P) hx hy
      by_cases h0 : ⁅x, y⁆ = 0
      · rw [h0]; exact zero_mem _
      have hx0 : rootSpace P μ ≠ ⊥ := fun hb ↦ h0 (by
        rw [hb, Submodule.mem_bot] at hx; rw [hx, zero_lie])
      have hy0 : rootSpace P ν ≠ ⊥ := fun hb ↦ h0 (by
        rw [hb, Submodule.mem_bot] at hy; rw [hy, lie_zero])
      have hxy0 : rootSpace P (μ + ν) ≠ ⊥ := fun hb ↦ h0 (by
        have hxy' : ⁅x, y⁆ ∈ rootSpace P (μ + ν) := hxy
        rwa [hb, Submodule.mem_bot] at hxy')
      exact Submodule.mem_iSup_of_mem _
        (Submodule.mem_iSup_of_mem (hST μ μ.2 ν ν.2 hx0 hy0 hxy0) hxy)

/-! ### The subspace `𝔲ᵢ⁻` -/

variable (i : ι)

/-- The subspace `𝔲ᵢ⁻ = ⊕_{α ∈ Q₊ \ {0, αᵢ}} 𝔤_{-α}` of `𝔫₋`. -/
def nilradNeg : Submodule K P.KacMoodyAlgebra :=
  ⨆ μ ∈ P.negWeights \ {-P.root i}, rootSpace P μ

variable {P}

omit [DecidableEq ι] in
lemma sum_pos_of_mem_posCone {k : ι → ℤ} (hk : k ∈ posCone ι) : 0 < ∑ j, k j := by
  obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
    by_contra! h
    exact hk.2 (funext h)
  have hj' : 0 < k j := lt_of_le_of_ne (hk.1 j) (Ne.symm hj)
  calc 0 < k j := hj'
    _ ≤ ∑ j, k j := Finset.single_le_sum (fun j _ ↦ hk.1 j) (Finset.mem_univ j)

omit [CharZero K] in
lemma neg_root_eq_neg_rootOf : -P.root i = -P.rootOf (Pi.single i 1) := by
  rw [rootOf_single]

omit [DecidableEq ι] in
/-- The weights `μ + ν`, `μ, ν ∈ -(Q₊ \ {0, αᵢ})`, lie in `-(Q₊ \ {0, αᵢ})`. -/
lemma add_mem_negWeights_diff {μ ν : Dual K H} (hμ : μ ∈ P.negWeights \ {-P.root i})
    (hν : ν ∈ P.negWeights \ {-P.root i}) :
    μ + ν ∈ P.negWeights \ {-P.root i} := by
  classical
  refine ⟨negWeights_add P hμ.1 hν.1, fun h ↦ ?_⟩
  obtain ⟨⟨k, hk, rfl⟩, -⟩ := hμ
  obtain ⟨⟨l, hl, rfl⟩, -⟩ := hν
  rw [Set.mem_singleton_iff, neg_root_eq_neg_rootOf, ← neg_add, neg_inj, ← map_add] at h
  have hkl := P.rootOf_injective h
  have h1 := sum_pos_of_mem_posCone hk
  have h2 := sum_pos_of_mem_posCone hl
  have h3 : ∑ j, (k + l) j = ∑ j, (Pi.single i 1 : ι → ℤ) j := by rw [hkl]
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true] at h3
  omega

lemma nilradNeg_le_nNeg : nilradNeg P i ≤ (nNeg P).toSubmodule := by
  rw [nNeg_toSubmodule_eq]
  exact iSup₂_mono' fun μ hμ ↦ ⟨μ, hμ.1, le_rfl⟩

/-- `𝔲ᵢ⁻` is a Lie subalgebra. -/
lemma lie_mem_nilradNeg {x y : P.KacMoodyAlgebra} (hx : x ∈ nilradNeg P i)
    (hy : y ∈ nilradNeg P i) : ⁅x, y⁆ ∈ nilradNeg P i :=
  lie_mem_iSup_rootSpace P (fun _ hμ _ hν _ _ _ ↦ add_mem_negWeights_diff i hμ hν) hx hy

omit [CharZero K] in
/-- `𝔲ᵢ⁻` is stable under `ad 𝔥`. -/
lemma lie_h_mem_nilradNeg (a : H) {x : P.KacMoodyAlgebra} (hx : x ∈ nilradNeg P i) :
    ⁅h P a, x⁆ ∈ nilradNeg P i := by
  have ha : h P a ∈ ⨆ μ ∈ ({0} : Set (Dual K H)), rootSpace P μ :=
    Submodule.mem_iSup_of_mem 0 (Submodule.mem_iSup_of_mem rfl fun b ↦ by
      rw [lie_h_h, LinearMap.zero_apply, zero_smul])
  exact lie_mem_iSup_rootSpace P (fun μ hμ ν hν _ _ _ ↦ by
    rw [Set.mem_singleton_iff.mp hμ, zero_add]; exact hν) ha hx

/-- `𝔲ᵢ⁻` is stable under `ad fᵢ`. -/
lemma lie_f_mem_nilradNeg {x : P.KacMoodyAlgebra} (hx : x ∈ nilradNeg P i) :
    ⁅f P i, x⁆ ∈ nilradNeg P i := by
  have hf : f P i ∈ ⨆ μ ∈ ({-P.root i} : Set (Dual K H)), rootSpace P μ :=
    Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem rfl (by
      rw [rootSpace_neg_root]; exact Submodule.mem_span_singleton_self _))
  refine lie_mem_iSup_rootSpace P (fun μ hμ ν hν _ _ _ ↦ ?_) hf hx
  rw [Set.mem_singleton_iff.mp hμ]
  refine ⟨negWeights_add P (neg_root_mem_negWeights P i) hν.1, fun h ↦ ?_⟩
  rw [Set.mem_singleton_iff, add_eq_left] at h
  exact zero_notMem_negWeights P (h ▸ hν.1)

/-- `𝔲ᵢ⁻` is stable under `ad eᵢ`. -/
lemma lie_e_mem_nilradNeg {x : P.KacMoodyAlgebra} (hx : x ∈ nilradNeg P i) :
    ⁅e P i, x⁆ ∈ nilradNeg P i := by
  have he : e P i ∈ ⨆ μ ∈ ({P.root i} : Set (Dual K H)), rootSpace P μ :=
    Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem rfl (by
      rw [rootSpace_root]; exact Submodule.mem_span_singleton_self _))
  refine lie_mem_iSup_rootSpace P (fun μ hμ ν hν _ hν0 hμν0 ↦ ?_) he hx
  obtain rfl := Set.mem_singleton_iff.mp hμ
  obtain ⟨⟨k, hk, rfl⟩, hki⟩ := hν
  beta_reduce at *
  have hki' : k ≠ Pi.single i 1 := by
    rintro rfl
    exact hki (by rw [Set.mem_singleton_iff, rootOf_single])
  have hsum : P.root i + -P.rootOf k = P.rootOf (Pi.single i 1 - k) := by
    rw [map_sub, rootOf_single]; abel
  rw [hsum] at hμν0 ⊢
  have hk2 : k ≠ 2 • Pi.single i 1 := by
    rintro rfl
    apply hν0
    rw [map_nsmul, rootOf_single]
    exact rootSpace_neg_two_smul_root_eq_bot P i
  rcases nonneg_or_nonpos_of_rootSpace_ne_bot P hμν0 with h | h
  · -- `0 ≤ αᵢ - k` is impossible
    exfalso
    have hk0 := hk.2
    apply hk0
    by_cases hki0 : k i = 0
    · funext j
      have := h j; have := hk.1 j
      by_cases hj : j = i
      · subst hj; simpa using hki0
      · simp only [Pi.sub_apply, Pi.single_eq_of_ne hj, Pi.zero_apply] at *; omega
    · exfalso
      apply hki'
      funext j
      have := h j; have := hk.1 j
      by_cases hj : j = i
      · subst hj; simp only [Pi.sub_apply, Pi.single_eq_same, Pi.zero_apply] at *; omega
      · simp only [Pi.sub_apply, Pi.single_eq_of_ne hj, Pi.zero_apply] at *; omega
  · refine ⟨⟨k - Pi.single i 1, ⟨fun j ↦ ?_, sub_ne_zero.mpr hki'⟩, ?_⟩, ?_⟩
    · have := h j; simp only [Pi.sub_apply, Pi.zero_apply] at *; omega
    · simp only [map_sub]; abel
    · rw [Set.mem_singleton_iff, neg_root_eq_neg_rootOf, ← map_neg]
      intro h'
      have := P.rootOf_injective h'
      apply hk2
      rw [two_nsmul]
      funext j
      have := congr_fun this j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.sub_apply, Pi.neg_apply, Pi.single_eq_same, Pi.add_apply] at this ⊢
        omega
      · simp only [Pi.sub_apply, Pi.neg_apply, Pi.single_eq_of_ne hj, Pi.add_apply] at this ⊢
        omega

/-- `𝔫₋ = K fᵢ ⊕ 𝔲ᵢ⁻`: the sum. -/
lemma nNeg_eq_span_f_sup_nilradNeg : (nNeg P).toSubmodule = (K ∙ f P i) ⊔ nilradNeg P i := by
  have hS : P.negWeights = insert (-P.root i) (P.negWeights \ {-P.root i}) := by
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem (neg_root_mem_negWeights P i)]
  rw [nNeg_toSubmodule_eq, hS, iSup_insert, rootSpace_neg_root]
  rfl

/-- `𝔫₋ = K fᵢ ⊕ 𝔲ᵢ⁻`: the sum is direct. -/
lemma disjoint_span_f_nilradNeg : Disjoint (K ∙ f P i) (nilradNeg P i) := by
  rw [← rootSpace_neg_root]
  exact (iSupIndep_weightSpaceOfMap (h P)).disjoint_biSup fun h ↦ h.2 rfl

end Matrix.Realization.KacMoodyAlgebra
