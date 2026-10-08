/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationDuality
import LieLean.Algebra.Lie.KacMoody.TranslationSameFacet

/-!
# Self-duality of simple modules and of their translates

For every highest weight `Λ`, the simple module `L(Λ)` is self-dual for the duality `M ↦ M^∨`
of category `𝒪`: the contravariant form of `L(Λ)` gives `L(Λ) ≅ L(Λ)^∨`
(`Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.equivRestrictedDual`; Humphreys, GSM 94,
§3.2). Since translation commutes with duality (Proposition 7.1,
`restrictedDualCentralTranslationEquiv`), every translate `T L(Λ) = pr_{χ₂}(pr_{χ₁} L(Λ) ⊗ L(ν))`
is self-dual
(`Matrix.Realization.KacMoodyAlgebra.nonempty_equiv_restrictedDual_centralTranslation`).
In particular `T_μ^λ L(w·μ)` is self-dual, the first assertion of Humphreys, GSM 94,
Theorem 7.14 (c).

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.2, §7.1, §7.14.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open TwistedDual

section SelfDual

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (Λ : Dual K H)

local notation "𝔤" => KacMoodyAlgebra P

/-- Distinct weight spaces of `L(Λ)` are orthogonal for the contravariant form. -/
theorem IrreducibleModule.contravariantForm_eq_zero_of_ne {μ ν : Dual K H}
    {u w : IrreducibleModule P Λ} (hu : u ∈ weightSpaceOfMap (IrreducibleModule P Λ) (h P) μ)
    (hw : w ∈ weightSpaceOfMap (IrreducibleModule P Λ) (h P) ν) (hne : μ ≠ ν) :
    IrreducibleModule.contravariantForm P Λ u w = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := by
    by_contra hc
    push Not at hc
    exact hne (LinearMap.ext hc)
  have h1 := IrreducibleModule.contravariantForm_lie_left P Λ (h P a) u w
  rw [transpose_h, hu a, hw a, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul,
    smul_eq_mul] at h1
  have h2 : (μ a - ν a) * IrreducibleModule.contravariantForm P Λ u w = 0 := by
    linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)

/-- The morphism `L(Λ) → L(Λ)^∨`, `u ↦ B(u, −)`, given by the contravariant form. -/
def IrreducibleModule.toRestrictedDualSelf :
    IrreducibleModule P Λ →ₗ⁅K,𝔤⁆ restrictedDual P (IrreducibleModule P Λ) :=
  (homOfForm P _ (IrreducibleModule.contravariantForm P Λ)
    (IrreducibleModule.contravariantForm_lie_left P Λ)).codRestrict _ fun _ ↦
    map_mem_iSup_weightSpaceOfMap P _
      ((IrreducibleModule.isCategoryO P Λ).iSup_weightSpaceOfMap_eq_top ▸ Submodule.mem_top)

@[simp] lemma IrreducibleModule.toDual_toRestrictedDualSelf (u w : IrreducibleModule P Λ) :
    TwistedDual.toDual P _ (IrreducibleModule.toRestrictedDualSelf P Λ u).val w =
      IrreducibleModule.contravariantForm P Λ u w := rfl

/-- **`L(Λ)` is self-dual** (Humphreys, GSM 94, §3.2): the contravariant form gives an
isomorphism `L(Λ) ≅ L(Λ)^∨`. -/
def IrreducibleModule.equivRestrictedDual :
    IrreducibleModule P Λ ≃ₗ⁅K,𝔤⁆ restrictedDual P (IrreducibleModule P Λ) := by
  classical
  refine LieModuleEquiv.ofBijective (IrreducibleModule.toRestrictedDualSelf P Λ) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro u hu
    refine (IrreducibleModule.nondegenerate_contravariantForm P Λ).1 u fun w ↦ ?_
    have := congrArg
      (fun φ : restrictedDual P (IrreducibleModule P Λ) ↦ TwistedDual.toDual P _ φ.val w) hu
    simpa using this
  · rintro ⟨φ, hφ⟩
    have hL := (IrreducibleModule.isCategoryO P Λ).iSup_weightSpaceOfMap_eq_top
    -- functionals of weight `μ` are represented by vectors of weight `μ`
    have key : ∀ ψ ∈ ⨆ μ, weightSpaceOfMap (TwistedDual P (IrreducibleModule P Λ)) (h P) μ,
        ∃ u, (IrreducibleModule.toRestrictedDualSelf P Λ u).val = ψ := by
      intro ψ hψ
      induction hψ using Submodule.iSup_induction' with
      | mem μ ψ hψ =>
        let Lμ := weightSpaceOfMap (IrreducibleModule P Λ) (h P) μ
        have := (IrreducibleModule.isCategoryO P Λ).finiteDimensional_weightSpaceOfMap μ
        let Bμ := (IrreducibleModule.contravariantForm P Λ).restrict Lμ
        have hsep : ∀ u : Lμ, (∀ w : Lμ, Bμ u w = 0) → u = 0 := by
          intro u hu
          refine Subtype.ext ((IrreducibleModule.nondegenerate_contravariantForm P Λ).1 u
            fun w ↦ ?_)
          -- `w` is a sum of weight vectors; only its `μ`-component pairs with `u`
          have hw : w ∈ ⨆ ν, weightSpaceOfMap (IrreducibleModule P Λ) (h P) ν :=
            hL ▸ Submodule.mem_top
          induction hw using Submodule.iSup_induction' with
          | mem ν w hw =>
            by_cases hνμ : ν = μ
            · subst hνμ
              exact hu ⟨w, hw⟩
            · exact IrreducibleModule.contravariantForm_eq_zero_of_ne P Λ u.2 hw (Ne.symm hνμ)
          | zero => simp
          | add w₁ w₂ _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
        have hBμ : Bμ.Nondegenerate := by
          refine ⟨hsep, fun w hw ↦ hsep w fun u ↦ ?_⟩
          change IrreducibleModule.contravariantForm P Λ w u = 0
          rw [(IrreducibleModule.isSymm_contravariantForm P Λ).eq]
          exact hw u
        let f : Module.Dual K Lμ := (TwistedDual.toDual P _ ψ).comp Lμ.subtype
        refine ⟨((Bμ.toDual hBμ).symm f : Lμ), TwistedDual.ext fun w ↦ ?_⟩
        rw [IrreducibleModule.toDual_toRestrictedDualSelf]
        have hw : w ∈ ⨆ ν, weightSpaceOfMap (IrreducibleModule P Λ) (h P) ν :=
          hL ▸ Submodule.mem_top
        induction hw using Submodule.iSup_induction' with
        | mem ν w hw =>
          by_cases hνμ : ν = μ
          · subst hνμ
            have := LinearMap.BilinForm.apply_toDual_symm_apply (B := Bμ) (hB := hBμ) f ⟨w, hw⟩
            exact this
          · rw [IrreducibleModule.contravariantForm_eq_zero_of_ne P Λ
              ((Bμ.toDual hBμ).symm f).2 hw (Ne.symm hνμ),
              apply_eq_zero_of_ne hψ hw (Ne.symm hνμ)]
        | zero => simp
        | add w₁ w₂ _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
      | zero => exact ⟨0, by simp⟩
      | add ψ₁ ψ₂ _ _ h₁ h₂ =>
        obtain ⟨u₁, hu₁⟩ := h₁
        obtain ⟨u₂, hu₂⟩ := h₂
        exact ⟨u₁ + u₂, by rw [map_add, LieSubmodule.coe_add, hu₁, hu₂]⟩
    obtain ⟨u, hu⟩ := key φ hφ
    exact ⟨u, Subtype.ext hu⟩

end SelfDual

section Translation

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

include hA in
/-- **Translates of simple modules are self-dual** (Humphreys, GSM 94, Theorem 7.14 (c),
self-duality, in general form): for `ν` dominant integral, `T = pr_{χ₂}(pr_{χ₁}(−) ⊗ L(ν))` and
any `Λ`, `T L(Λ) ≅ (T L(Λ))^∨`. Combined with
`exists_hom_translation_irreducible_ne_zero_iff` and
`exists_hom_irreducible_translation_ne_zero_iff`, `T_μ^λ L(w·μ)` is self-dual with head and socle
`L(w·λ)` in the setting of Theorem 7.14. -/
theorem nonempty_equiv_restrictedDual_centralTranslation {ν : Dual K H}
    (hν : P.IsDominantIntegral ν) (χ₁ χ₂ : 𝓩 →ₐ[K] K) (Λ : Dual K H) :
    Nonempty (centralTranslation P (IrreducibleModule P ν) χ₁ χ₂ (IrreducibleModule P Λ) ≃ₗ⁅K,𝔤⁆
      restrictedDual P (centralTranslation P (IrreducibleModule P ν) χ₁ χ₂
        (IrreducibleModule P Λ))) :=
  ⟨((restrictedDualCentralTranslationEquiv P hA hν (IrreducibleModule.isCategoryO P Λ) χ₁
    χ₂).trans (centralTranslationEquiv P (IrreducibleModule P ν) χ₁ χ₂
      (IrreducibleModule.equivRestrictedDual P Λ).symm)).symm⟩

end Translation

end Matrix.Realization.KacMoodyAlgebra
