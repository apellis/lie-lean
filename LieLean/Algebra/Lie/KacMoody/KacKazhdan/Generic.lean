/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Grothendieck
import LieLean.Algebra.Lie.KacMoody.Jantzen.Weight
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Criterion

/-!
# Verma modules at generic points of a Kac–Kazhdan hyperplane

Let `A` be a symmetrizable generalized Cartan matrix. For `γ ∈ Q₊ \ {0}` let `H_γ` be the
hyperplane `2 (λ + ρ | γ) = (γ | γ)` in `𝔥*`. Fix `η ∈ Q₊` and a point `λ₀` which is *generic* on
`H_{γ₀}` up to depth `η`, in the sense that

* `λ₀` lies on no other hyperplane `H_γ` with `0 < γ ≤ η`, and
* `2 (λ₀ - γ₀ + ρ | γ) ≠ (γ | γ)` for all `0 < γ ≤ η` (so that `M'(λ₀ - γ₀)` has no nonzero
  vectors of weights `λ₀ - γ₀ - β` with `β ≤ η`, by
  `VermaModule.exists_of_maxSubmodule_inf_weightSpace_ne_bot`).

Then every composition factor `L(μ)` of `M'(λ₀)` that contributes to a weight `λ₀ - β` with
`β ≤ η` is `L(λ₀ - γ₀)`, whose weight spaces there agree with those of `M(λ₀ - γ₀)`. Hence
for every submodule `N ⊆ M'(λ₀)`,

`dim N_{λ₀ - β} = [N : L(λ₀ - γ₀)] · P(β - γ₀)`

(`VermaModule.finrank_inf_weightSpace_of_generic`). Applied to the Jantzen filtration along any
line `λ₀ + t δ`, the order formula gives

`ord_{t=0} D_β(λ₀ + t δ) = ord_{t=0} D_{γ₀}(λ₀ + t δ) · P(β - γ₀)`

for the Shapovalov determinants `D_β` (`VermaModule.natTrailingDegree_eq_mul_of_generic`). This is
the step in the proof of the Kac–Kazhdan determinant formula that identifies the multiplicity of
a non-isotropic hyperplane `H_γ` in `D_β` as `P(β - γ)` times a constant (cf. [KK];
[Kum] Thm. 2.3.4, proof, Step 4 and its conclusion; [Jantzen, *Kontravariante Formen auf induzierten
Darstellungen halbeinfacher Lie-Algebren*, Math. Ann. 226 (1977), 53–65], where such a filtration is
used for the parabolic determinant ([HumO] §9.17, Remark); the argument here was reconstructed by
us).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.finrank_inf_weightSpace_of_generic`,
  `Matrix.Realization.KacMoodyAlgebra.VermaModule.natTrailingDegree_eq_mul_of_generic`.

## Proof

`dim N_ξ = ∑_μ [N : L(μ)] dim L(μ)_ξ` (`IsCategoryO.finrank_weightSpace_eq_finsum`). If
`[N : L(μ)] ≠ 0` then `[M(λ₀) : L(μ)] ≠ 0`, so `μ = λ₀ - γ` with `γ ∈ Q₊` and
`2 (λ₀ + ρ | γ) = (γ | γ)` ([Kac] Lemma 9.8 and the proof of Prop. 9.8); `γ ≠ 0` since
`N_{λ₀} = 0`; and if `dim L(μ)_{λ₀ - β} ≠ 0` then `γ ≤ β ≤ η`. By genericity `γ = γ₀`. Finally
`dim L(λ₀ - γ₀)_{λ₀ - β} = dim M(λ₀ - γ₀)_{λ₀ - β} = P(β - γ₀)`, since `M'(λ₀ - γ₀)` has no
vector of that weight.

## References

* [KK] V. G. Kac, D. A. Kazhdan, *Structure of representations with highest weight of
  infinite-dimensional Lie algebras*, Adv. Math. 34 (1979), 97–108.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §2.3.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.8.
* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, §5.6–5.7.
-/

open Module LieModule Polynomial

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (S : A.Symmetrization) (hA : A.IsGeneralizedCartan)

namespace VermaModule

include hA

/-- If `2 (μ + ρ | γ) ≠ (γ | γ)` for all `0 < γ ≤ η`, then `L(μ)` and `M(μ)` have the same weight
spaces of weights `μ - β` with `β ≤ η`: `dim L(μ)_{μ - β} = P(β)`. -/
theorem finrank_weightSpace_irreducibleModule_of_forall {μ : Dual K H} {η : ι → ℤ}
    (h : ∀ γ : ι → ℤ, 0 ≤ γ → γ ≠ 0 → γ ≤ η →
      2 * P.dualBilinForm S (μ + P.rho) (P.rootOf γ) ≠
        P.dualBilinForm S (P.rootOf γ) (P.rootOf γ))
    {β : ι → ℤ} (hβ : β ≤ η) :
    finrank K (KacMoodyAlgebra.weightSpace P (IrreducibleModule P μ) (μ - P.rootOf β)) =
      kostantPartition P (P.rootOf β) := by
  have hbot : (maxSubmodule P μ).toSubmodule ⊓ weightSpace P μ (μ - P.rootOf β) = ⊥ := by
    by_contra hne
    obtain ⟨γ, hγ0, hγne, hγβ, hγ, -⟩ :=
      exists_of_maxSubmodule_inf_weightSpace_ne_bot P S hA hne
    exact h γ hγ0 hγne (hγβ.trans hβ) hγ
  have := (isCategoryO P μ).finiteDimensional_weightSpaceOfMap (μ - P.rootOf β)
  have := finrank_weightSpaceOfMap_eq_add P (maxSubmodule P μ)
    (isCategoryO P μ).iSup_weightSpaceOfMap_eq_top (μ - P.rootOf β)
  rw [finrank_weightSpaceOfMap_lieSubmodule, hbot, finrank_bot, zero_add] at this
  rw [← finrank_weightSpace_sub P μ (P.rootOf β)]
  exact this.symm

/-- **Weight spaces of submodules of `M'(λ₀)` at a generic point of a Kac–Kazhdan
hyperplane.** Suppose that `λ₀` lies on no hyperplane `2 (λ + ρ | γ) = (γ | γ)` with `0 < γ ≤ η`
other than possibly the one for `γ₀`, and that `2 (λ₀ - γ₀ + ρ | γ) ≠ (γ | γ)` for all
`0 < γ ≤ η`. Then for every submodule `N ⊆ M'(λ₀)` and `β ≤ η`,
`dim N_{λ₀ - β} = [N : L(λ₀ - γ₀)] · P(β - γ₀)`. -/
theorem finrank_inf_weightSpace_of_generic {Λ₀ : Dual K H} {γ₀ η : ι → ℤ} (hγ₀ : 0 ≤ γ₀)
    (hgen : ∀ γ : ι → ℤ, 0 ≤ γ → γ ≠ 0 → γ ≤ η →
      2 * P.dualBilinForm S (Λ₀ + P.rho) (P.rootOf γ) =
        P.dualBilinForm S (P.rootOf γ) (P.rootOf γ) → γ = γ₀)
    (hirr : ∀ γ : ι → ℤ, 0 ≤ γ → γ ≠ 0 → γ ≤ η →
      2 * P.dualBilinForm S (Λ₀ - P.rootOf γ₀ + P.rho) (P.rootOf γ) ≠
        P.dualBilinForm S (P.rootOf γ) (P.rootOf γ))
    {N : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ₀)} (hN : N ≤ maxSubmodule P Λ₀)
    {β : ι → ℤ} (hβ : β ≤ η) :
    finrank K ↥(N.toSubmodule ⊓ weightSpace P Λ₀ (Λ₀ - P.rootOf β)) =
      ((isCategoryO P Λ₀).lieSubmodule N).multiplicity (Λ₀ - P.rootOf γ₀) *
        kostantPartition P (P.rootOf β - P.rootOf γ₀) := by
  set hN' := (isCategoryO P Λ₀).lieSubmodule N
  rw [← finrank_weightSpaceOfMap_lieSubmodule, hN'.finrank_weightSpace_eq_finsum,
    finsum_eq_single _ (Λ₀ - P.rootOf γ₀) fun μ hμ ↦ ?_]
  · congr 1
    have hξ : Λ₀ - P.rootOf β = Λ₀ - P.rootOf γ₀ - P.rootOf (β - γ₀) := by
      rw [map_sub]; abel
    rw [hξ, finrank_weightSpace_irreducibleModule_of_forall P S hA hirr
      ((sub_le_self_iff _).mpr hγ₀ |>.trans hβ), map_sub]
  by_contra hne
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
  have hM : (isCategoryO P Λ₀).multiplicity μ ≠ 0 := by
    rw [(isCategoryO P Λ₀).multiplicity_eq_add N μ]
    omega
  obtain ⟨⟨γ, hγ0, rfl⟩, hnorm⟩ := mem_cone_and_eq_of_multiplicity_ne_zero hA S
    LieModuleHom.id Function.surjective_id (isCategoryO P Λ₀) hM
  obtain ⟨γ', hγ'0, hγ'⟩ := IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero h2
  have hβγ : β = γ + γ' := P.rootOf_injective (by
    rw [map_add]
    linear_combination (norm := abel_nf) -hγ')
  have hγne : γ ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero] at h1
    have := hN'.multiplicity_le_finrank Λ₀
    rw [finrank_weightSpaceOfMap_lieSubmodule,
      (hwv_notMem_iff_inf_weightSpace_eq_bot P Λ₀ N).mp
        fun h ↦ hwv_notMem_maxSubmodule P Λ₀ (hN h), finrank_bot] at this
    omega
  rw [dualBilinForm_add_rho_add_rho_eq_iff, dualBilinForm_add_two_rho_eq_iff] at hnorm
  exact hμ (by rw [hgen γ hγ0 hγne (le_trans (by rw [hβγ]; exact le_add_of_nonneg_right hγ'0) hβ)
    hnorm])

/-- **The order of the Shapovalov determinants along a transversal line at a generic point of a
Kac–Kazhdan hyperplane.** Under the genericity assumptions of `finrank_inf_weightSpace_of_generic`,
for any direction `δ` and `β ≤ η`, if `d_β(t) = D_β(λ₀ + t δ)` and `d_{γ₀}(t) = D_{γ₀}(λ₀ + t δ)`
are nonzero, then `ord_{t=0} d_β = ord_{t=0} d_{γ₀} · P(β - γ₀)`. -/
theorem natTrailingDegree_eq_mul_of_generic {Λ₀ δ : Dual K H} {γ₀ η : ι → ℤ} (hγ₀ : 0 ≤ γ₀)
    (hγ₀η : γ₀ ≤ η)
    (hgen : ∀ γ : ι → ℤ, 0 ≤ γ → γ ≠ 0 → γ ≤ η →
      2 * P.dualBilinForm S (Λ₀ + P.rho) (P.rootOf γ) =
        P.dualBilinForm S (P.rootOf γ) (P.rootOf γ) → γ = γ₀)
    (hirr : ∀ γ : ι → ℤ, 0 ≤ γ → γ ≠ 0 → γ ≤ η →
      2 * P.dualBilinForm S (Λ₀ - P.rootOf γ₀ + P.rho) (P.rootOf γ) ≠
        P.dualBilinForm S (P.rootOf γ) (P.rootOf γ))
    {β : ι → ℤ} (hβ : β ≤ η) {d d₀ : K[X]} (hd : d ≠ 0) (hd₀ : d₀ ≠ 0)
    (hdet : ∀ t, d.eval t =
      (LinearMap.BilinForm.toMatrix (pbwWeightBasis P (Λ₀ + t • δ) (P.rootOf β))
        (weightSpaceForm P (Λ₀ + t • δ) (Λ₀ + t • δ - P.rootOf β))).det)
    (hdet₀ : ∀ t, d₀.eval t =
      (LinearMap.BilinForm.toMatrix (pbwWeightBasis P (Λ₀ + t • δ) (P.rootOf γ₀))
        (weightSpaceForm P (Λ₀ + t • δ) (Λ₀ + t • δ - P.rootOf γ₀))).det) :
    d.natTrailingDegree = d₀.natTrailingDegree * kostantPartition P (P.rootOf β - P.rootOf γ₀) := by
  set c : ℕ → ℕ := fun i ↦ ((isCategoryO P Λ₀).lieSubmodule (jantzen P Λ₀ δ (i + 1))).multiplicity
    (Λ₀ - P.rootOf γ₀)
  have hle (i : ℕ) : jantzen P Λ₀ δ (i + 1) ≤ maxSubmodule P Λ₀ := by
    rw [← jantzen_one P S Λ₀ δ]
    exact antitone_nat_of_succ_le (jantzen_antitone P Λ₀ δ) (Nat.le_add_left 1 i)
  have hform {β' : ι → ℤ} (hβ' : β' ≤ η) (i : ℕ) :
      finrank K ((jantzen P Λ₀ δ (i + 1)).toSubmodule ⊓ weightSpace P Λ₀ (Λ₀ - P.rootOf β') :
        Submodule K _) = c i * kostantPartition P (P.rootOf β' - P.rootOf γ₀) :=
    finrank_inf_weightSpace_of_generic P S hA hγ₀ hgen hirr (hle i) hβ'
  have hP0 : kostantPartition P 0 = 1 := by
    rw [← finrank_weightSpace_sub P 0 0, sub_zero]
    exact finrank_weightSpace_self P 0
  have hsum := sum_finrank_jantzen_inf_weightSpace S Λ₀ δ (P.rootOf β) d hd hdet
  have hsum₀ := sum_finrank_jantzen_inf_weightSpace S Λ₀ δ (P.rootOf γ₀) d₀ hd₀ hdet₀
  simp only [hform hβ, hform hγ₀η, sub_self, hP0, mul_one] at hsum hsum₀
  have hz {i : ℕ} (hi : d.natTrailingDegree ≤ i) :
      c i * kostantPartition P (P.rootOf β - P.rootOf γ₀) = 0 := by
    rw [← hform hβ]
    exact finrank_jantzen_inf_weightSpace_eq_zero S Λ₀ δ _ d hd hdet (by omega)
  have hz₀ {i : ℕ} (hi : d₀.natTrailingDegree ≤ i) : c i = 0 := by
    have := hform hγ₀η i
    rw [sub_self, hP0, mul_one] at this
    rw [← this]
    exact finrank_jantzen_inf_weightSpace_eq_zero S Λ₀ δ _ d₀ hd₀ hdet₀ (by omega)
  set R := d.natTrailingDegree + d₀.natTrailingDegree
  have h1 : ∑ i ∈ Finset.range R, c i * kostantPartition P (P.rootOf β - P.rootOf γ₀) =
      d.natTrailingDegree := by
    rw [← hsum]
    refine (Finset.sum_subset (Finset.range_subset_range.mpr (Nat.le_add_right _ _))
      fun i _ hi ↦ hz (by simpa using hi)).symm
  have h2 : ∑ i ∈ Finset.range R, c i = d₀.natTrailingDegree := by
    rw [← hsum₀]
    refine (Finset.sum_subset (Finset.range_subset_range.mpr (Nat.le_add_left _ _))
      fun i _ hi ↦ hz₀ (by simpa using hi)).symm
  rw [← h1, ← Finset.sum_mul, h2]

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
