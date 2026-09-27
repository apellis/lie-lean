/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Casimir
import LieLean.Algebra.Lie.KacMoody.WeylLength

/-!
# Sums over dual bases of positive root spaces

Let `𝔤 = 𝔤(A)` be a Kac–Moody algebra with a standard invariant form (`IsStandardForm`), and
let `{e_α^{(k)}}`, `{e_{-α}^{(k)}}` be dual bases of `𝔤_α`, `𝔤_{-α}`. Kostant's identity for
`𝔫₋`-homology is proved by manipulating sums `∑_{α > 0} ∑ₖ Φ(e_{-α}^{(k)}, [e_α^{(k)}, y])` for
root vectors `y ∈ 𝔤_{-β}`. This file provides the tools:
* the projection `π : 𝔤 → 𝔫₋` along the Borel subalgebra (`nNegProj`), which on a root vector
  `x ∈ 𝔤_γ` is `x` or `0` according as `γ < 0` or not;
* the finiteness of `{α > 0 | β - α > 0}` (`finite_window`) and reindexing of sums over the
  positive weights by `α ↦ α + β` and `α ↦ β - α`;
* the evaluation of the `α = β` term (`IsStandardForm.casimirSum_lie_self`, via [Kac] Thm. 2.2 e)),
  the antisymmetry `α ↔ β - α` (`IsStandardForm.casimirSum_lie_swap`, via [Kac] Lemma 2.4), and
  the decomposition of a sum along the root string through `β`
  (`IsStandardForm.finsum_casimirSum_lie_eq`).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.nNegProj`: the projection `π : 𝔤 → 𝔫₋`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.dualBasisBasis`: the dual basis of `𝔤_{-μ}`
  as a basis.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.finite_window`,
  `Matrix.Realization.KacMoodyAlgebra.finsum_posWeights_add`,
  `Matrix.Realization.KacMoodyAlgebra.finsum_posWeights_sub`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.casimirSum_lie_self`,
  `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.casimirSum_lie_swap`,
  `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.finsum_casimirSum_lie_eq`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.2–2.4.
* The lemmas are reconstructed by us for the proof of Kostant's identity.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}

/-! ### The projection onto `𝔫₋` -/

variable (P) in
/-- The projection `π : 𝔤 → 𝔫₋` along the Borel subalgebra `𝔟 = 𝔥 ⊕ 𝔫₊`. -/
def nNegProj : P.KacMoodyAlgebra →ₗ[K] nNeg P :=
  Submodule.projectionOnto _ _ (isCompl_nNeg_borel P)

lemma nNegProj_of_mem {x : P.KacMoodyAlgebra} (hx : x ∈ nNeg P) : nNegProj P x = ⟨x, hx⟩ :=
  Submodule.projectionOnto_apply_of_mem_left _ hx

@[simp] lemma nNegProj_coe (x : nNeg P) : nNegProj P x = x :=
  Submodule.projectionOnto_apply_left _ x

lemma nNegProj_of_mem_borel {x : P.KacMoodyAlgebra} (hx : x ∈ borel P) : nNegProj P x = 0 :=
  Submodule.projectionOnto_apply_of_mem_right _ hx

lemma rootSpace_le_nNeg {γ : Dual K H} (hγ : γ ∈ P.negWeights) :
    rootSpace P γ ≤ (nNeg P).toSubmodule := by
  rw [nNeg_toSubmodule_eq]
  exact le_iSup₂ (f := fun μ (_ : μ ∈ P.negWeights) ↦ rootSpace P μ) γ hγ

lemma rootSpace_le_borel {γ : Dual K H} (hγ : γ ∉ P.negWeights) :
    rootSpace P γ ≤ (borel P).toSubmodule := by
  by_cases hne : rootSpace P γ = ⊥
  · rw [hne]; exact bot_le
  rcases mem_allWeights_of_rootSpace_ne_bot P hne with (hneg | h0) | hpos
  · exact absurd hneg hγ
  · rw [Set.mem_singleton_iff.mp h0, rootSpace_zero]
    exact fun x hx ↦ Submodule.mem_sup_left hx
  · intro x hx
    refine Submodule.mem_sup_right ?_
    rw [nPos_toSubmodule_eq]
    exact Submodule.mem_iSup_of_mem γ (Submodule.mem_iSup_of_mem hpos hx)

/-- `π x = x` for a root vector `x ∈ 𝔤_γ`, `γ < 0`. -/
lemma coe_nNegProj_of_mem_rootSpace {γ : Dual K H} {x : P.KacMoodyAlgebra}
    (hx : x ∈ rootSpace P γ) (hγ : γ ∈ P.negWeights) :
    (nNegProj P x : P.KacMoodyAlgebra) = x := by
  rw [nNegProj_of_mem (rootSpace_le_nNeg hγ hx)]

/-- `π x = 0` for a root vector `x ∈ 𝔤_γ`, `γ ≮ 0`. -/
lemma nNegProj_eq_zero_of_mem_rootSpace {γ : Dual K H} {x : P.KacMoodyAlgebra}
    (hx : x ∈ rootSpace P γ) (hγ : γ ∉ P.negWeights) : nNegProj P x = 0 :=
  nNegProj_of_mem_borel (rootSpace_le_borel hγ hx)


/-! ### Positive weights below a given one -/

omit [DecidableEq ι] in
/-- There are only finitely many `α ∈ Q₊ \ 0` with `β - α ∈ Q₊ \ 0`. -/
lemma finite_window (β : Dual K H) :
    {α | α ∈ P.posWeights ∧ β - α ∈ P.posWeights}.Finite := by
  classical
  let c : ι → ℤ := if hc : ∃ c, P.rootOf c = β then hc.choose else 0
  refine ((Set.Finite.pi (t := fun i ↦ Set.Icc 0 (c i)) fun i ↦ Set.finite_Icc _ _).image
    P.rootOf).subset ?_
  rintro _ ⟨⟨k, hk, rfl⟩, l, hl, hlk⟩
  have hkl : P.rootOf (k + l) = β := by rw [map_add, hlk]; abel
  have hex : ∃ c, P.rootOf c = β := ⟨_, hkl⟩
  have hc : c = k + l := P.rootOf_injective (by
    simp only [c, hex, ↓reduceDIte]; rw [hex.choose_spec, hkl])
  refine ⟨k, fun i _ ↦ ⟨hk.1 i, ?_⟩, rfl⟩
  rw [hc, Pi.add_apply, le_add_iff_nonneg_right]
  exact hl.1 i

omit [DecidableEq ι] [CharZero K] in
lemma sub_mem_negWeights_iff {α β : Dual K H} :
    α - β ∈ P.negWeights ↔ β - α ∈ P.posWeights := by
  rw [← neg_sub, neg_mem_negWeights_iff]

omit [DecidableEq ι] [CharZero K] in
lemma mem_posWeights_of_sub_mem {α β : Dual K H} (hβ : β ∈ P.posWeights)
    (h : α - β ∈ P.posWeights) : α ∈ P.posWeights := by
  simpa using P.posWeights_add h hβ

/-! ### Reindexing sums over the positive weights -/

section Reindex

variable {M : Type*} [AddCommGroup M]

omit [DecidableEq ι] [CharZero K] in
/-- Shifting a sum over `Q₊ \ 0` by `β`: `∑_{α > 0} F(α + β) = ∑_{α - β > 0} F(α)`. -/
lemma finsum_posWeights_add (F : Dual K H → M) (β : Dual K H) :
    ∑ᶠ α ∈ P.posWeights, F (α + β) = ∑ᶠ α ∈ {α | α - β ∈ P.posWeights}, F α := by
  rw [finsum_mem_def, finsum_mem_def, ← finsum_comp_equiv (Equiv.subRight β)]
  refine finsum_congr fun α ↦ ?_
  by_cases h : α - β ∈ P.posWeights
  · rw [Equiv.subRight_apply, Set.indicator_of_mem h, Set.indicator_of_mem (by exact h),
      sub_add_cancel]
  · rw [Equiv.subRight_apply, Set.indicator_of_notMem h,
      Set.indicator_of_notMem (by exact h)]

omit [DecidableEq ι] [CharZero K] in
/-- Reflecting a sum over `Q₊ \ 0` in `β / 2`: if `F` vanishes outside
`{α > 0 | β - α > 0}`, then `∑_{α > 0} F(β - α) = ∑_{α > 0} F(α)`. -/
lemma finsum_posWeights_sub (F : Dual K H → M) (β : Dual K H)
    (hF : ∀ α, F α ≠ 0 → α ∈ P.posWeights ∧ β - α ∈ P.posWeights) :
    ∑ᶠ α ∈ P.posWeights, F (β - α) = ∑ᶠ α ∈ P.posWeights, F α := by
  classical
  rw [finsum_mem_def, finsum_mem_def, ← finsum_comp_equiv (Equiv.subLeft β)]
  refine finsum_congr fun α ↦ ?_
  rw [Equiv.subLeft_apply]
  by_cases h0 : F α = 0
  · rw [Set.indicator_apply, Set.indicator_apply, sub_sub_cancel, h0]
    simp
  · obtain ⟨h1, h2⟩ := hF α h0
    rw [Set.indicator_of_mem h2, Set.indicator_of_mem h1, sub_sub_cancel]

omit [Fintype ι] [DecidableEq ι] [CharZero K] in
lemma finsum_mem_neg (s : Set (Dual K H)) (F : Dual K H → M) :
    ∑ᶠ α ∈ s, -F α = -∑ᶠ α ∈ s, F α := by
  rw [finsum_mem_def, finsum_mem_def, ← finsum_neg_distrib]
  exact finsum_congr fun α ↦ by
    classical
    simp only [Set.indicator_apply]
    split_ifs <;> simp

end Reindex

/-! ### Sums over dual bases -/

omit [CharZero K] in
lemma lie_mem_rootSpace_sub {α β : Dual K H} {e y : P.KacMoodyAlgebra} (he : e ∈ rootSpace P α)
    (hy : y ∈ rootSpace P (-β)) : ⁅e, y⁆ ∈ rootSpace P (α - β) := by
  have := lie_mem_weightSpaceOfMap (h P) he hy
  rwa [← sub_eq_add_neg] at this

namespace IsStandardForm

variable [FiniteDimensional K H] {S : A.Symmetrization}
  {B : LinearMap.BilinForm K P.KacMoodyAlgebra} (hB : IsStandardForm P S B)
include hB

/-- The dual basis `{e_{-μ}^{(k)}}` as a basis of `𝔤_{-μ}`. -/
def dualBasisBasis (μ : Dual K H) :
    Basis (Fin (finrank K (rootSpace P μ))) K (rootSpace P (-μ)) :=
  (rootSpaceBasis P μ).dualBasis.map (hB.pairingEquiv μ).symm

lemma coe_dualBasisBasis (μ : Dual K H) (k : Fin (finrank K (rootSpace P μ))) :
    (hB.dualBasisBasis μ k : P.KacMoodyAlgebra) = hB.dualBasis μ k := by
  rw [dualBasisBasis, Basis.map_apply, Basis.coe_dualBasis]
  rfl

/-- `∑ₖ Φ(e_{-β}^{(k)}, [e_β^{(k)}, y]) = Φ(y, ν⁻¹(β))` for `y ∈ 𝔤_{-β}` ([Kac] Thm. 2.2 e)). -/
lemma casimirSum_lie_self {M : Type*} [AddCommGroup M] [Module K M]
    (Ψ : P.KacMoodyAlgebra →ₗ[K] P.KacMoodyAlgebra →ₗ[K] M) {β : Dual K H}
    {y : P.KacMoodyAlgebra} (hy : y ∈ rootSpace P (-β)) :
    hB.casimirSum (fun f e ↦ Ψ f ⁅e, y⁆) β = Ψ y (h P ((P.toDual S).symm β)) := by
  conv_rhs => rw [← hB.sum_smul_dualBasis β hy]
  rw [casimirSum_def, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [hB.lie_eq_smul (rootSpaceBasis_mem P β k) hy, map_smul, map_smul, LinearMap.smul_apply]

/-- The antisymmetry of `∑ₖ e_{-α}^{(k)} ⊗ [e_α^{(k)}, y]` under reflection of the root string:
`∑ₖ Ψ([e_α^{(k)}, y], e_{-α}^{(k)}) = -∑ₖ Ψ(e_{-(β-α)}^{(k)}, [e_{β-α}^{(k)}, y])` for
`y ∈ 𝔤_{-β}`. This follows from [Kac] Lemma 2.4 (`casimirSum_lie_left`). -/
lemma casimirSum_lie_swap {M : Type*} [AddCommGroup M] [Module K M]
    (Ψ : P.KacMoodyAlgebra →ₗ[K] P.KacMoodyAlgebra →ₗ[K] M) {β : Dual K H}
    {y : P.KacMoodyAlgebra} (hy : y ∈ rootSpace P (-β)) (α : Dual K H) :
    hB.casimirSum (fun f e ↦ Ψ ⁅e, y⁆ f) α = -hB.casimirSum (fun f e ↦ Ψ f ⁅e, y⁆) (β - α) := by
  let Ψ' : P.KacMoodyAlgebra →ₗ[K] P.KacMoodyAlgebra →ₗ[K] M :=
    LinearMap.mk₂ K (fun a b ↦ Ψ ⁅a, y⁆ b) (fun a a' b ↦ by rw [add_lie, map_add,
      LinearMap.add_apply]) (fun c a b ↦ by rw [smul_lie, map_smul, LinearMap.smul_apply])
      (fun a b b' ↦ map_add _ _ _) (fun c a b ↦ map_smul _ _ _)
  have h1 := hB.casimirSum_eq_of_basis Ψ' (μ := -α) (hB.dualBasisBasis α)
    (fun k ↦ (rootSpaceBasis P α k : P.KacMoodyAlgebra))
    (fun k ↦ by rw [neg_neg]; exact rootSpaceBasis_mem P α k)
    (fun j k ↦ by rw [coe_dualBasisBasis, hB.symm, basis_dualBasis]; simp [eq_comm])
  have h2 := hB.casimirSum_lie_left Ψ (γ := -β) hy (-α)
  simp only [Ψ', LinearMap.mk₂_apply, coe_dualBasisBasis] at h1
  rw [sub_neg_eq_add, neg_add_eq_sub] at h2
  rw [casimirSum_def, h1, h2, casimirSum_def, casimirSum_def, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← lie_skew, map_neg]

variable {M : Type*} [AddCommGroup M] (Φ : P.KacMoodyAlgebra → P.KacMoodyAlgebra → M)
  {β : Dual K H} {y : P.KacMoodyAlgebra}

lemma casimirSum_nNegProj_lie_of_mem (hy : y ∈ rootSpace P (-β)) {α : Dual K H}
    (h : α - β ∈ P.negWeights) :
    hB.casimirSum (fun f e ↦ Φ f (nNegProj P ⁅e, y⁆ : P.KacMoodyAlgebra)) α =
      hB.casimirSum (fun f e ↦ Φ f ⁅e, y⁆) α :=
  Finset.sum_congr rfl fun k _ ↦ by
    dsimp only
    rw [coe_nNegProj_of_mem_rootSpace (lie_mem_rootSpace_sub (rootSpaceBasis_mem P α k) hy) h]

lemma casimirSum_nNegProj_lie_of_notMem (hΦ : ∀ f, Φ f 0 = 0) (hy : y ∈ rootSpace P (-β))
    {α : Dual K H} (h : α - β ∉ P.negWeights) :
    hB.casimirSum (fun f e ↦ Φ f (nNegProj P ⁅e, y⁆ : P.KacMoodyAlgebra)) α = 0 :=
  Finset.sum_eq_zero fun k _ ↦ by
    dsimp only
    rw [nNegProj_eq_zero_of_mem_rootSpace (lie_mem_rootSpace_sub (rootSpaceBasis_mem P α k) hy)
      h, ZeroMemClass.coe_zero, hΦ]

lemma casimirSum_lie_of_eq_bot (hΦ : ∀ f, Φ f 0 = 0) (hy : y ∈ rootSpace P (-β))
    {α : Dual K H} (h : rootSpace P (α - β) = ⊥) :
    hB.casimirSum (fun f e ↦ Φ f ⁅e, y⁆) α = 0 :=
  Finset.sum_eq_zero fun k _ ↦ by
    have := lie_mem_rootSpace_sub (rootSpaceBasis_mem P α k) hy
    rw [h, Submodule.mem_bot] at this
    dsimp only
    rw [this, hΦ]

/-- The terms `∑ₖ Φ(e_{-α}^{(k)}, π[e_α^{(k)}, y])`, `y ∈ 𝔤_{-β}`, vanish unless
`0 < α < β`. -/
lemma mem_window_of_casimirSum_nNegProj_ne_zero (hΦ : ∀ f, Φ f 0 = 0)
    (hy : y ∈ rootSpace P (-β)) {α : Dual K H} (hα : α ∈ P.posWeights)
    (h : hB.casimirSum (fun f e ↦ Φ f (nNegProj P ⁅e, y⁆ : P.KacMoodyAlgebra)) α ≠ 0) :
    α ∈ {α | α ∈ P.posWeights ∧ β - α ∈ P.posWeights} :=
  ⟨hα, sub_mem_negWeights_iff.mp (by_contra fun h' ↦
    h (hB.casimirSum_nNegProj_lie_of_notMem Φ hΦ hy h'))⟩

/-- **Splitting a sum over the positive roots according to the root string through `β`**: for
`y ∈ 𝔤_{-β}`, the sum `∑_{α > 0} ∑ₖ Φ(e_{-α}^{(k)}, [e_α^{(k)}, y])` is the sum of the term
`α = β`, the terms `α > β` (reindexed as `α + β`, `α > 0`) and the terms `0 < α < β`, in which
`[e_α^{(k)}, y] = π[e_α^{(k)}, y] ∈ 𝔫₋`. -/
theorem finsum_casimirSum_lie_eq (hΦ : ∀ f, Φ f 0 = 0) (hβ : β ∈ P.posWeights)
    (hy : y ∈ rootSpace P (-β))
    (hfin : (P.posWeights ∩ Function.support fun α ↦
      hB.casimirSum (fun f e ↦ Φ f ⁅e, y⁆) α).Finite) :
    ∑ᶠ α ∈ P.posWeights, hB.casimirSum (fun f e ↦ Φ f ⁅e, y⁆) α =
      hB.casimirSum (fun f e ↦ Φ f ⁅e, y⁆) β +
        ∑ᶠ α ∈ P.posWeights, hB.casimirSum (fun f e ↦ Φ f ⁅e, y⁆) (α + β) +
        ∑ᶠ α ∈ P.posWeights,
          hB.casimirSum (fun f e ↦ Φ f (nNegProj P ⁅e, y⁆ : P.KacMoodyAlgebra)) α := by
  set F : Dual K H → M := fun α ↦ hB.casimirSum (fun f e ↦ Φ f ⁅e, y⁆) α
  set Fπ : Dual K H → M := fun α ↦
    hB.casimirSum (fun f e ↦ Φ f (nNegProj P ⁅e, y⁆ : P.KacMoodyAlgebra)) α
  change ∑ᶠ α ∈ P.posWeights, F α = F β + ∑ᶠ α ∈ P.posWeights, F (α + β) +
    ∑ᶠ α ∈ P.posWeights, Fπ α
  rw [finsum_posWeights_add, ← finsum_mem_singleton (f := F) (a := β), finsum_mem_def,
    finsum_mem_def, finsum_mem_def, finsum_mem_def]
  have hfin2 : (Function.support ({α | α - β ∈ P.posWeights}.indicator F)).Finite :=
    hfin.subset fun α hα ↦ by
      rw [Set.support_indicator] at hα
      exact ⟨mem_posWeights_of_sub_mem hβ hα.1, hα.2⟩
  have hfin3 : (Function.support (P.posWeights.indicator Fπ)).Finite :=
    (finite_window β).subset fun α hα ↦ by
      rw [Set.support_indicator] at hα
      exact hB.mem_window_of_casimirSum_nNegProj_ne_zero Φ hΦ hy hα.1 hα.2
  have hfin1 : (Function.support (({β} : Set (Dual K H)).indicator F)).Finite :=
    (Set.finite_singleton β).subset fun α hα ↦ by
      rw [Set.support_indicator] at hα
      exact hα.1
  rw [← finsum_add_distrib hfin1 hfin2, ← finsum_add_distrib (hfin1.union hfin2 |>.subset
    (Function.support_add _ _)) hfin3]
  refine finsum_congr fun α ↦ ?_
  by_cases hα : α ∈ P.posWeights
  · rw [Set.indicator_of_mem hα, Set.indicator_of_mem hα]
    by_cases h2 : α - β ∈ P.posWeights
    · have hne : α ∉ ({β} : Set (Dual K H)) := fun h ↦
        P.zero_notMem_posWeights (by rwa [Set.mem_singleton_iff.mp h, sub_self] at h2)
      have h3 : α - β ∉ P.negWeights := fun h3 ↦
        Set.disjoint_left.mp P.disjoint_posWeights_negWeights h2 h3
      rw [Set.indicator_of_notMem hne, Set.indicator_of_mem (show α ∈ {α | α - β ∈ P.posWeights}
        from h2), show Fπ α = 0 from hB.casimirSum_nNegProj_lie_of_notMem Φ hΦ hy h3]
      simp
    have h2' : α ∉ {α | α - β ∈ P.posWeights} := h2
    by_cases h0 : α = β
    · subst h0
      rw [Set.indicator_of_mem (Set.mem_singleton α), Set.indicator_of_notMem h2',
        show Fπ α = 0 from hB.casimirSum_nNegProj_lie_of_notMem Φ hΦ hy
          (by rw [sub_self]; exact P.zero_notMem_negWeights)]
      simp
    rw [Set.indicator_of_notMem (show α ∉ ({β} : Set (Dual K H)) from h0),
      Set.indicator_of_notMem h2', zero_add, zero_add]
    by_cases h3 : α - β ∈ P.negWeights
    · exact (hB.casimirSum_nNegProj_lie_of_mem Φ hy h3).symm
    · change F α = Fπ α
      rw [show Fπ α = 0 from hB.casimirSum_nNegProj_lie_of_notMem Φ hΦ hy h3]
      refine hB.casimirSum_lie_of_eq_bot Φ hΦ hy (by_contra fun hne ↦ ?_)
      rcases mem_allWeights_of_rootSpace_ne_bot P hne with (hneg | h0') | hpos
      · exact h3 hneg
      · exact h0 (sub_eq_zero.mp h0')
      · exact h2 hpos
  · have hne : α ∉ ({β} : Set (Dual K H)) := fun h ↦ hα (Set.mem_singleton_iff.mp h ▸ hβ)
    have h2 : α ∉ {α | α - β ∈ P.posWeights} := fun h ↦ hα (mem_posWeights_of_sub_mem hβ h)
    rw [Set.indicator_of_notMem hα, Set.indicator_of_notMem hα, Set.indicator_of_notMem hne,
      Set.indicator_of_notMem h2]
    simp

end IsStandardForm

end Matrix.Realization.KacMoodyAlgebra
