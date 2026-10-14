/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.ExtProjective
import LieLean.Algebra.Lie.KacMoody.CategoryOSubmodule

/-!
# `Ext¹` between highest weight modules

Humphreys, GSM 94, Proposition 3.1, for the relative `Ext¹` `ExtOne (h P)` (the Yoneda `Ext¹` of
`𝒪`, see `KacMoody/ExtProjective.lean`):

* (a) `Ext¹(M(λ), M) = 0` for a highest weight module `M` of weight `μ` with `λ ≮ μ`;
* (b) `Ext¹(M(λ), L(μ)) = 0` for `μ ≤ λ`;
* (c) `Hom(N(λ), L(μ)) ≅ Ext¹(L(λ), L(μ))` for `μ < λ`, `N(λ)` the maximal submodule of `M(λ)`;
* (d) `Ext¹(L(λ), L(λ)) = 0`.

Here `μ ≤ λ` is `μ ∈ cone P λ` (`λ - μ ∈ Q₊`).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.extOne_verma_eq_zero`: (a).
* `Matrix.Realization.KacMoodyAlgebra.extOne_verma_irreducibleModule_eq_zero`: (b).
* `Matrix.Realization.KacMoodyAlgebra.nonempty_hom_maxSubmodule_equiv_extOne`: (c).
* `Matrix.Realization.KacMoodyAlgebra.extOne_irreducibleModule_self_eq_zero`: (d).

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.1.
-/

noncomputable section

open Module LieModule

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝔤" => KacMoodyAlgebra P

/-- **Humphreys, GSM 94, Proposition 3.1 (a).** If `M` is a highest weight module of weight `μ`
(a quotient of `M(μ)`) and `λ ≮ μ`, then `Ext¹(M(λ), M) = 0`: every extension of `M(λ)` by `M`
splits. Humphreys states this for `𝔤` semisimple over `ℂ`. -/
theorem extOne_verma_eq_zero {M : Type*} [AddCommGroup M] [Module K M]
    [LieRingModule P.KacMoodyAlgebra M] [LieModule K P.KacMoodyAlgebra M] {Λ μ : Dual K H}
    (φ : VermaModule P μ →ₗ⁅K,𝔤⁆ M) (hφ : Function.Surjective φ)
    (hΛμ : ¬ (Λ ∈ cone P μ ∧ Λ ≠ μ)) (y : ExtOne (h P) (VermaModule P Λ) M) : y = 0 := by
  obtain ⟨c, rfl⟩ := ExtOne.mk_surjective y
  set E := ExtOne.Extension c
  have hM : IsCategoryO P M := IsCategoryO.of_surjective φ hφ
  have hE : ⨆ ν, weightSpaceOfMap E (h P) ν = ⊤ :=
    ExtOne.Extension.iSup_weightSpaceOfMap_eq_top c hM.1 (VermaModule.isCategoryO P Λ).1
  -- a preimage of `v_λ` of weight `λ`
  obtain ⟨v, hv, hvv⟩ := ExtOne.exists_mem_weightSpaceOfMap_of_surjective (h P) hE
    (ExtOne.Extension.surjective_snd c) (hwv_mem_weightSpace P Λ)
  -- it is a maximal vector
  have he (i : ι) : ⁅e P i, v⁆ = 0 := by
    have hsnd : ExtOne.Extension.snd c ⁅e P i, v⁆ = 0 := by
      rw [LieModuleHom.map_lie, hvv]
      exact lie_e_hwv P Λ i
    obtain ⟨n, hn⟩ := ExtOne.Extension.exists_inl_eq_of_snd_eq_zero c hsnd
    have hvi : ⁅e P i, v⁆ ∈ weightSpaceOfMap E (h P) (Λ + P.root i) :=
      toEnd_e_mem_weightSpace (P := P) i hv
    have hnw : n ∈ weightSpaceOfMap M (h P) (Λ + P.root i) := by
      rw [← hn, ExtOne.Extension.mem_weightSpaceOfMap_iff] at hvi
      exact hvi.1
    by_contra hne
    have hn0 : n ≠ 0 := fun h0 ↦ hne (by rw [← hn, h0, map_zero])
    obtain ⟨k, hk, hkμ⟩ := VermaModule.exists_eq_sub_of_mem_weightSpace P μ φ hφ hnw hn0
    refine hΛμ ⟨⟨k + Pi.single i 1, add_nonneg hk (Pi.single_nonneg.mpr zero_le_one), ?_⟩,
      fun hΛ ↦ ?_⟩
    · rw [map_add, rootOf_single, sub_add_eq_sub_sub, ← hkμ]
      abel
    · have h0 : P.rootOf (k + Pi.single i 1) = P.rootOf 0 := by
        rw [map_add, rootOf_single, map_zero]
        calc P.rootOf k + P.root i = (μ + P.root i) - (μ - P.rootOf k) := by abel
          _ = 0 := by rw [← hkμ, hΛ, sub_self]
      have := congrFun (P.rootOf_injective h0) i
      simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at this
      have := hk i
      simp only [Pi.zero_apply] at this
      omega
  set σ := VermaModule.lift P v (fun _ hx ↦ lie_eq_zero_of_mem_nPos he hx) (fun a ↦ hv a)
  refine (ExtOne.mk_eq_zero_iff c).mpr ⟨σ, fun m ↦ ?_⟩
  have : (ExtOne.Extension.snd c).comp σ = LieModuleHom.id :=
    VermaModule.hom_ext P Λ (by rw [LieModuleHom.comp_apply, VermaModule.lift_hwv, hvv]; rfl)
  exact LieModuleHom.congr_fun this m

/-- **Humphreys, GSM 94, Proposition 3.1 (b).** If `μ ≤ λ`, then `Ext¹(M(λ), L(μ)) = 0`. -/
theorem extOne_verma_irreducibleModule_eq_zero {Λ μ : Dual K H} (hμΛ : μ ∈ cone P Λ)
    (y : ExtOne (h P) (VermaModule P Λ) (IrreducibleModule P μ)) : y = 0 :=
  extOne_verma_eq_zero P (LieSubmodule.Quotient.mk' (maxSubmodule P μ))
    (LieSubmodule.Quotient.surjective_mk' _)
    (fun h ↦ h.2 (eq_of_mem_cone_of_mem_cone h.1 hμΛ)) y

/-- The extension `0 → N(λ) → M(λ) → L(λ) → 0`. -/
theorem nonempty_splitData_maxSubmodule (Λ : Dual K H) :
    Nonempty (ExtOne.SplitData (h P) (maxSubmodule P Λ).incl
      (LieSubmodule.Quotient.mk' (maxSubmodule P Λ))) :=
  ExtOne.exists_splitData (h P) (VermaModule.isCategoryO P Λ).1
    (IrreducibleModule.isCategoryO P Λ).1 Subtype.val_injective
    (LieSubmodule.Quotient.surjective_mk' _) fun b ↦ by
      rw [LieSubmodule.Quotient.mk_eq_zero]
      exact ⟨fun hb ↦ ⟨⟨b, hb⟩, rfl⟩, fun ⟨a, ha⟩ ↦ ha ▸ a.2⟩

/-- **Humphreys, GSM 94, Proposition 3.1 (c).** If `μ < λ` and `N(λ)` is the maximal submodule of
`M(λ)`, then `Hom(N(λ), L(μ)) ≅ Ext¹(L(λ), L(μ))`, via the connecting map. -/
theorem nonempty_hom_maxSubmodule_equiv_extOne {Λ μ : Dual K H} (hμΛ : μ ∈ cone P Λ)
    (hne : μ ≠ Λ) :
    Nonempty ((maxSubmodule P Λ →ₗ⁅K,𝔤⁆ IrreducibleModule P μ) ≃ₗ[K]
      ExtOne (h P) (IrreducibleModule P Λ) (IrreducibleModule P μ)) := by
  obtain ⟨D⟩ := nonempty_splitData_maxSubmodule P Λ
  refine ⟨D.connectingEquiv (fun g ↦ ?_) (extOne_verma_irreducibleModule_eq_zero P hμΛ)⟩
  -- `Hom(M(λ), L(μ)) = 0`: the image of `v_λ` would be a nonzero vector of weight `λ` in `L(μ)`
  by_contra hg
  have hg0 : g (hwv P Λ) ≠ 0 := fun h0 ↦ hg (VermaModule.hom_ext P Λ (by rw [h0]; rfl))
  have hw : g (hwv P Λ) ∈ weightSpaceOfMap (IrreducibleModule P μ) (h P) Λ :=
    map_mem_weightSpaceOfMap P g (hwv_mem_weightSpace P Λ)
  obtain ⟨k, hk, hkΛ⟩ := VermaModule.exists_eq_sub_of_mem_weightSpace P μ
    (LieSubmodule.Quotient.mk' (maxSubmodule P μ)) (LieSubmodule.Quotient.surjective_mk' _) hw hg0
  exact hne (eq_of_mem_cone_of_mem_cone hμΛ ⟨k, hk, hkΛ⟩)

/-- **Humphreys, GSM 94, Proposition 3.1 (d).** `Ext¹(L(λ), L(λ)) = 0`. -/
theorem extOne_irreducibleModule_self_eq_zero (Λ : Dual K H)
    (y : ExtOne (h P) (IrreducibleModule P Λ) (IrreducibleModule P Λ)) : y = 0 := by
  obtain ⟨D⟩ := nonempty_splitData_maxSubmodule P Λ
  obtain ⟨f, rfl⟩ := D.exists_connecting_eq (y := y)
    (extOne_verma_eq_zero P (LieSubmodule.Quotient.mk' (maxSubmodule P Λ))
      (LieSubmodule.Quotient.surjective_mk' _) (fun h ↦ h.2 rfl) _)
  -- `Hom(N(λ), L(λ)) = 0`: `N(λ)` has no vectors of weight `λ`
  suffices hf : f = 0 by rw [hf, map_zero]
  by_contra hf
  have := IrreducibleModule.isIrreducible P Λ
  have hsurj : Function.Surjective f := by
    rw [← LieModuleHom.range_eq_top]
    refine (IsSimpleOrder.eq_bot_or_eq_top f.range).resolve_left fun h0 ↦ hf ?_
    ext y
    have : f y ∈ f.range := (LieModuleHom.mem_range _ _).mpr ⟨y, rfl⟩
    rw [h0, LieSubmodule.mem_bot] at this
    exact this
  have hN : IsCategoryO P (maxSubmodule P Λ) :=
    (VermaModule.isCategoryO P Λ).lieSubmodule (maxSubmodule P Λ)
  obtain ⟨n, hn, hnf⟩ := ExtOne.exists_mem_weightSpaceOfMap_of_surjective (h P) hN.1 hsurj
    (IrreducibleModule.hwv_mem_weightSpace P Λ)
  have hn0 : (n : VermaModule P Λ) ∈ (maxSubmodule P Λ).toSubmodule ⊓
      weightSpaceOfMap (VermaModule P Λ) (h P) Λ :=
    ⟨n.2, mem_weightSpaceOfMap_lieSubmodule_iff.mp hn⟩
  rw [inf_weightSpace_self_eq_bot P Λ (hwv_notMem_maxSubmodule P Λ), Submodule.mem_bot] at hn0
  have : n = 0 := Subtype.ext hn0
  rw [this, map_zero] at hnf
  exact IrreducibleModule.hwv_ne_zero P Λ hnf.symm

end Matrix.Realization.KacMoodyAlgebra
