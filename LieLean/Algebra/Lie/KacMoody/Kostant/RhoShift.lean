/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Kostant.RootSums

/-!
# The `ρ`-shift identity for `𝔫₋`

Let `A` be a generalized Cartan matrix with a symmetrization, `𝔤 = 𝔤(A)` with a standard
invariant form and dual bases `{e_α^{(k)}}`, `{e_{-α}^{(k)}}` of the root spaces. For a positive
root `β` and `y ∈ 𝔤_{-β}` we prove
`∑_{0 < α < β} ∑ₖ [e_{-α}^{(k)}, [e_α^{(k)}, y]] = (2(ρ | β) - (β | β)) y`
(`IsStandardForm.coe_rhoShiftSum`). This is the degree-one input of Kostant's identity for the
Laplacian on `𝔫₋`-chains (`KacMoody/Kostant/Identity.lean`).

## Proof

The following argument for this step is our own. Let `v₀` be the
highest-weight vector of the Verma module `M(0)`. The Casimir operator `Ω` acts on `M(0)` by
`(0 + 2ρ | 0) = 0` ([Kac] Cor. 2.6). Expanding `Ω (y v₀)` with `Ω = 2ν⁻¹(ρ) + Ω₀ + 2Ω₊`, the
first two terms give `(-2(ρ|β) + (β|β)) y v₀`, and in `Ω₊ (y v₀) = ∑_α ∑ₖ e_{-α} [e_α, y] v₀` only
the roots `0 < α < β` contribute. Writing `e_{-α}[e_α, y] v₀ = [e_{-α}, [e_α, y]] v₀ +
[e_α, y] e_{-α} v₀`, the antisymmetry of [Kac] Lemma 2.4 under `α ↦ β - α` identifies the sum of
the second terms with minus the whole sum, so `2 Ω₊ (y v₀) = ∑_{0<α<β} ∑ₖ [e_{-α}, [e_α, y]] v₀`.
Finally `x ↦ x v₀` is injective on `𝔫₋` (PBW).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.rhoShiftSum`: the element
  `∑_{α > 0} ∑ₖ [π e_{-α}^{(k)}, π[e_α^{(k)}, y]]` of `𝔫₋`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.coe_rhoShiftSum`: the `ρ`-shift identity.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.eq_zero_of_lie_hwv_eq_zero`: `x ↦ x v_Λ` is
  injective on `𝔫₋`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.4–2.6, §9.2
  (stated over `ℂ`).
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- The map `𝔫₋ → M(Λ)`, `x ↦ x v_Λ`, is injective (by PBW). -/
lemma VermaModule.eq_zero_of_lie_hwv_eq_zero {Λ : Dual K H} {x : P.KacMoodyAlgebra}
    (hx : x ∈ nNeg P) (h0 : ⁅x, VermaModule.hwv P Λ⁆ = 0) : x = 0 := by
  have h1 : VermaModule.equivEnvNNeg P Λ (UniversalEnvelopingAlgebra.ι K (⟨x, hx⟩ : nNeg P)) =
      0 := by
    rw [VermaModule.equivEnvNNeg_apply, UniversalEnvelopingAlgebra.map_ι]
    exact h0
  rw [LinearEquiv.map_eq_zero_iff, ← map_zero (UniversalEnvelopingAlgebra.ι K)] at h1
  exact congrArg Subtype.val (UniversalEnvelopingAlgebra.ι_injective K (nNeg P) h1)

omit [CharZero K] in
/-- The Borel subalgebra kills the highest-weight vector of `M(0)`. -/
lemma VermaModule.lie_hwv_zero_of_mem_borel {x : P.KacMoodyAlgebra} (hx : x ∈ borel P) :
    ⁅x, VermaModule.hwv P 0⁆ = 0 := by
  obtain ⟨a, n, hn, rfl⟩ := (mem_borel P).mp hx
  rw [add_lie, VermaModule.lie_h_hwv, VermaModule.lie_hwv_of_mem_nPos P 0 hn, LinearMap.zero_apply,
    zero_smul, add_zero]

namespace IsStandardForm

variable [FiniteDimensional K H] {S : A.Symmetrization}
  {B : LinearMap.BilinForm K P.KacMoodyAlgebra} (hB : IsStandardForm P S B)
include hB

/-- `∑ₖ e_0^{(k)} e_0^{(k)}` (dual bases of `𝔥`) acts on a vector of weight `λ` as `ν⁻¹(λ)`. -/
lemma casimirTerm_zero_apply {V : Type*} [AddCommGroup V] [Module K V]
    [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] {Λ : Dual K H} {v : V}
    (hv : v ∈ weightSpace P V Λ) :
    hB.casimirTerm V 0 v = ⁅h P ((P.toDual S).symm Λ), v⁆ := by
  have hH : h P ((P.toDual S).symm Λ) ∈ rootSpace P (-0) := by
    rw [neg_zero, rootSpace_zero]; exact ⟨_, rfl⟩
  conv_rhs => rw [← hB.sum_smul_dualBasis 0 hH]
  rw [casimirTerm_apply, casimirSum_def, sum_lie]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [hB.lie_of_mem_rootSpace_zero (rootSpaceBasis_mem P 0 k) hv, lie_smul, smul_lie, hB.symm]

/-- The element `∑_{α > 0} ∑ₖ [π e_{-α}^{(k)}, π [e_α^{(k)}, y]]` of `𝔫₋`; for `y ∈ 𝔤_{-β}` only
the roots `0 < α < β` contribute. -/
def rhoShiftSum (y : P.KacMoodyAlgebra) : nNeg P :=
  ∑ᶠ α ∈ P.posWeights, hB.casimirSum (fun f e ↦ ⁅nNegProj P f, nNegProj P ⁅e, y⁆⁆) α

lemma casimirSum_nNegProj_ne_zero_mem_window {β : Dual K H} {y : P.KacMoodyAlgebra}
    (hy : y ∈ rootSpace P (-β)) {α : Dual K H} (hα : α ∈ P.posWeights)
    (h : hB.casimirSum (fun f e ↦ ⁅nNegProj P f, nNegProj P ⁅e, y⁆⁆) α ≠ 0) :
    α ∈ {α | α ∈ P.posWeights ∧ β - α ∈ P.posWeights} := by
  refine ⟨hα, sub_mem_negWeights_iff.mp (by_contra fun h' ↦ h (Finset.sum_eq_zero fun k _ ↦ ?_))⟩
  dsimp only
  rw [nNegProj_eq_zero_of_mem_rootSpace (lie_mem_rootSpace_sub (rootSpaceBasis_mem P α k) hy) h',
    lie_zero]

/-- **The `ρ`-shift identity** (reconstructed; it is the adjoint-representation shadow of
[Kac] Cor. 2.6): for `β ∈ Q₊ \ 0` and `y ∈ 𝔤_{-β}`,
`∑_{0 < α < β} ∑ₖ [e_{-α}^{(k)}, [e_α^{(k)}, y]] = (2(ρ | β) - (β | β)) y`.
Proof: apply the Casimir operator, which vanishes on `M(0)`, to `y v₀ ∈ M(0)`, and use that
`𝔫₋ → M(0)`, `x ↦ x v₀`, is injective. -/
theorem coe_rhoShiftSum (hA : A.IsGeneralizedCartan) {β : Dual K H} (hβ : β ∈ P.posWeights)
    {y : P.KacMoodyAlgebra} (hy : y ∈ rootSpace P (-β)) :
    (hB.rhoShiftSum y : P.KacMoodyAlgebra) =
      (2 * P.dualBilinForm S P.rho β - P.dualBilinForm S β β) • y := by
  set V := VermaModule P 0
  set v₀ := VermaModule.hwv P 0
  have hV : IsPosFinite P V := (VermaModule.isCategoryO P 0).isPosFinite
  have hyn : y ∈ nNeg P := rootSpace_le_nNeg ((neg_mem_negWeights_iff P).mpr hβ) hy
  set w : V := ⁅y, v₀⁆ with hwdef
  have hw : w ∈ weightSpace P V (-β) := by
    have := lie_mem_weightSpaceOfMap (h P) hy (VermaModule.hwv_mem_weightSpace P 0)
    rwa [add_zero] at this
  have hΩ : hB.casimir V hV w = 0 := by
    rw [hB.casimir_eq_smul_of_surjective hA hV LieModuleHom.id (fun x ↦ ⟨x, rfl⟩) w]
    simp
  have hkill (γ : Dual K H) (hγ : γ ∉ P.negWeights) (x : P.KacMoodyAlgebra)
      (hx : x ∈ rootSpace P γ) : ⁅x, v₀⁆ = 0 :=
    VermaModule.lie_hwv_zero_of_mem_borel (rootSpace_le_borel hγ hx)
  have hnotneg {α : Dual K H} (hα : α ∈ P.posWeights) : α ∉ P.negWeights := fun h ↦
    Set.disjoint_left.mp P.disjoint_posWeights_negWeights hα h
  -- the positive part of the Casimir operator on `w`
  set Φ : P.KacMoodyAlgebra → P.KacMoodyAlgebra → V := fun f x ↦ ⁅f, ⁅x, v₀⁆⁆
  have hT3 (α : Dual K H) (hα : α ∈ P.posWeights) :
      hB.casimirTerm V α w = hB.casimirSum (fun f e ↦ Φ f ⁅e, y⁆) α := by
    rw [casimirTerm_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Φ, w]
    rw [leibniz_lie (rootSpaceBasis P α k : P.KacMoodyAlgebra) y v₀,
      hkill α (hnotneg hα) _ (rootSpaceBasis_mem P α k), lie_zero, add_zero]
  have hfin : (P.posWeights ∩ Function.support fun α ↦
      hB.casimirSum (fun f e ↦ Φ f ⁅e, y⁆) α).Finite :=
    (hB.finite_casimirTerm hV w).subset fun α ⟨hα, hne⟩ ↦ ⟨hα, by rwa [Function.mem_support,
      hT3 α hα]⟩
  have hSL := hB.finsum_casimirSum_lie_eq Φ (fun f ↦ by simp [Φ]) hβ hy hfin
  have hβterm : hB.casimirSum (fun f e ↦ Φ f ⁅e, y⁆) β = 0 :=
    Finset.sum_eq_zero fun k _ ↦ by
      simp only [Φ]
      rw [hkill (β - β) (by rw [sub_self]; exact P.zero_notMem_negWeights) _
        (lie_mem_rootSpace_sub (rootSpaceBasis_mem P β k) hy), lie_zero]
  have hshift : ∑ᶠ α ∈ P.posWeights, hB.casimirSum (fun f e ↦ Φ f ⁅e, y⁆) (α + β) = 0 :=
    finsum_mem_eq_zero_of_forall_eq_zero fun α hα ↦ Finset.sum_eq_zero fun k _ ↦ by
      simp only [Φ]
      rw [hkill (α + β - β) (by rw [add_sub_cancel_right]; exact hnotneg hα) _
        (lie_mem_rootSpace_sub (rootSpaceBasis_mem P (α + β) k) hy), lie_zero]
  rw [hβterm, hshift, zero_add, zero_add] at hSL
  -- split `Φ f (π x) = [[f, π x], v₀] + [π x, [f, v₀]]`
  set N : Dual K H → V := fun α ↦
    hB.casimirSum (fun f e ↦ Φ f (nNegProj P ⁅e, y⁆ : P.KacMoodyAlgebra)) α
  set Y' : Dual K H → V := fun α ↦
    hB.casimirSum (fun f e ↦ ⁅⁅f, (nNegProj P ⁅e, y⁆ : P.KacMoodyAlgebra)⁆, v₀⁆) α
  set Mt : Dual K H → V := fun α ↦
    hB.casimirSum (fun f e ↦ ⁅(nNegProj P ⁅e, y⁆ : P.KacMoodyAlgebra), ⁅f, v₀⁆⁆) α
  have hNYM (α : Dual K H) : N α = Y' α + Mt α := by
    simp only [N, Y', Mt, casimirSum_def, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ leibniz_lie _ _ _
  -- the terms vanish outside `0 < α < β`
  have hwin {F : P.KacMoodyAlgebra → P.KacMoodyAlgebra → V} (hF : ∀ f, F f 0 = 0)
      (α : Dual K H) (hα : α ∈ P.posWeights)
      (hne : hB.casimirSum (fun f e ↦ F f (nNegProj P ⁅e, y⁆ : P.KacMoodyAlgebra)) α ≠ 0) :
      α ∈ {α | α ∈ P.posWeights ∧ β - α ∈ P.posWeights} :=
    hB.mem_window_of_casimirSum_nNegProj_ne_zero F hF hy hα hne
  have hfinY : (P.posWeights ∩ Function.support Y').Finite :=
    (finite_window β).subset fun α ⟨hα, hne⟩ ↦ hwin (F := fun f x ↦ ⁅⁅f, x⁆, v₀⁆)
      (fun f ↦ by simp) α hα hne
  have hfinM : (P.posWeights ∩ Function.support Mt).Finite :=
    (finite_window β).subset fun α ⟨hα, hne⟩ ↦ hwin (F := fun f x ↦ ⁅x, ⁅f, v₀⁆⁆)
      (fun f ↦ by simp) α hα hne
  -- antisymmetry: `∑ M = -∑ N`
  let Ψ2 : P.KacMoodyAlgebra →ₗ[K] P.KacMoodyAlgebra →ₗ[K] V :=
    LinearMap.mk₂ K (fun a b ↦ ⁅(nNegProj P a : P.KacMoodyAlgebra), ⁅b, v₀⁆⁆)
      (fun a a' b ↦ by rw [map_add, Submodule.coe_add, add_lie])
      (fun c a b ↦ by rw [map_smul, Submodule.coe_smul, smul_lie])
      (fun a b b' ↦ by rw [add_lie, lie_add]) (fun c a b ↦ by rw [smul_lie, lie_smul])
  set G : Dual K H → V := fun γ ↦ hB.casimirSum (fun f e ↦ Ψ2 f ⁅e, y⁆) γ
  have hMG (α : Dual K H) : Mt α = -G (β - α) := hB.casimirSum_lie_swap Ψ2 hy α
  have hGwin (γ : Dual K H) (hγ : G γ ≠ 0) : γ ∈ P.posWeights ∧ β - γ ∈ P.posWeights := by
    by_contra hc
    refine hγ (Finset.sum_eq_zero fun k _ ↦ ?_)
    simp only [Ψ2, LinearMap.mk₂_apply]
    by_cases hγp : γ ∈ P.posWeights
    · have h' : γ - β ∉ P.negWeights := fun h' ↦ hc ⟨hγp, sub_mem_negWeights_iff.mp h'⟩
      rw [hkill _ h' _ (lie_mem_rootSpace_sub (rootSpaceBasis_mem P γ k) hy), lie_zero]
    · rw [nNegProj_eq_zero_of_mem_rootSpace (hB.dualBasis_mem γ k)
        (by rwa [neg_mem_negWeights_iff]), ZeroMemClass.coe_zero, zero_lie]
  have hGN (α : Dual K H) (hα : α ∈ P.posWeights) : G α = N α := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Ψ2, LinearMap.mk₂_apply, Φ]
    have hf : (nNegProj P (hB.dualBasis α k) : P.KacMoodyAlgebra) = hB.dualBasis α k :=
      coe_nNegProj_of_mem_rootSpace (hB.dualBasis_mem α k) ((neg_mem_negWeights_iff P).mpr hα)
    have hey := lie_mem_rootSpace_sub (rootSpaceBasis_mem P α k) hy
    rw [hf]
    by_cases h' : α - β ∈ P.negWeights
    · rw [coe_nNegProj_of_mem_rootSpace hey h']
    · rw [nNegProj_eq_zero_of_mem_rootSpace hey h', hkill _ h' _ hey, ZeroMemClass.coe_zero,
        zero_lie]
  have hsumM : ∑ᶠ α ∈ P.posWeights, Mt α = -∑ᶠ α ∈ P.posWeights, N α := by
    rw [finsum_mem_congr rfl fun α _ ↦ hMG α, finsum_mem_neg, finsum_posWeights_sub G β hGwin,
      finsum_mem_congr rfl hGN]
  have hsumN : ∑ᶠ α ∈ P.posWeights, N α =
      ∑ᶠ α ∈ P.posWeights, Y' α + ∑ᶠ α ∈ P.posWeights, Mt α := by
    rw [← finsum_mem_add_distrib' hfinY hfinM]
    exact finsum_mem_congr rfl fun α _ ↦ hNYM α
  -- `∑ Y' = [Y, v₀]`
  let T : nNeg P →ₗ[K] V :=
    { toFun := fun x ↦ ⁅(x : P.KacMoodyAlgebra), v₀⁆
      map_add' := fun x x' ↦ by rw [Submodule.coe_add, add_lie]
      map_smul' := fun c x ↦ by rw [Submodule.coe_smul, smul_lie]; rfl }
  have hfinR : (P.posWeights ∩ Function.support fun α ↦
      hB.casimirSum (fun f e ↦ ⁅nNegProj P f, nNegProj P ⁅e, y⁆⁆) α).Finite :=
    (finite_window β).subset fun α ⟨hα, hne⟩ ↦ hB.casimirSum_nNegProj_ne_zero_mem_window hy hα hne
  have hY : T (hB.rhoShiftSum y) = ∑ᶠ α ∈ P.posWeights, Y' α := by
    rw [rhoShiftSum, ← LinearMap.toAddMonoidHom_coe, AddMonoidHom.map_finsum_mem' _ hfinR]
    refine finsum_mem_congr rfl fun α hα ↦ ?_
    simp only [LinearMap.toAddMonoidHom_coe, casimirSum_def, map_sum, Y']
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, LieSubalgebra.coe_bracket]
    rw [coe_nNegProj_of_mem_rootSpace (hB.dualBasis_mem α k) ((neg_mem_negWeights_iff P).mpr hα)]
  -- assemble
  have hpos : ∑ᶠ α ∈ P.posWeights, hB.casimirTerm V α w = (1 / 2 : K) • T (hB.rhoShiftSum y) := by
    rw [finsum_mem_congr rfl hT3, hSL]
    change ∑ᶠ α ∈ P.posWeights, N α = _
    rw [hY]
    have h2 : (2 : K) • ∑ᶠ α ∈ P.posWeights, N α = ∑ᶠ α ∈ P.posWeights, Y' α := by
      rw [two_smul]
      nth_rewrite 2 [hsumN]
      rw [hsumM]
      abel
    rw [← h2, smul_smul]
    norm_num
  rw [casimir_apply, hB.casimirTerm_zero_apply hw, hpos, hw, hw] at hΩ
  have key : T (hB.rhoShiftSum y - (2 * P.dualBilinForm S P.rho β - P.dualBilinForm S β β) •
      ⟨y, hyn⟩) = 0 := by
    have hTy : T ⟨y, hyn⟩ = w := rfl
    rw [map_sub, map_smul, hTy]
    have e1 : (-β) ((P.toDual S).symm P.rho) = -P.dualBilinForm S P.rho β := by
      rw [LinearMap.neg_apply, ← dualBilinForm_apply_eq, (P.isSymm_dualBilinForm S).eq]
    have e2 : (-β) ((P.toDual S).symm (-β)) = P.dualBilinForm S β β := by
      rw [map_neg, map_neg, LinearMap.neg_apply, neg_neg, dualBilinForm_apply_eq]
    rw [e1, e2] at hΩ
    linear_combination (norm := module) hΩ
  have hmem : ((hB.rhoShiftSum y - (2 * P.dualBilinForm S P.rho β - P.dualBilinForm S β β) •
      ⟨y, hyn⟩ : nNeg P) : P.KacMoodyAlgebra) ∈ nNeg P := Subtype.property _
  have := VermaModule.eq_zero_of_lie_hwv_eq_zero hmem key
  rw [Submodule.coe_sub, Submodule.coe_smul, sub_eq_zero] at this
  exact this

end IsStandardForm

end Matrix.Realization.KacMoodyAlgebra
