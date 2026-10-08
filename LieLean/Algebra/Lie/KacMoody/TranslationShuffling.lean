/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationWallExt

/-!
# The adjunction morphism `M → Θ_s M` and shuffling

For translation functors `T = pr_{χ₂}(pr_{χ₁}(−) ⊗ L)` and `T' = pr_{χ₁}(pr_{χ₂}(−) ⊗ L^*)` with
the adjunction `Hom(T M, N) ≅ Hom(M, T' N)` (`translationAdjunction`), the identity of `T M`
corresponds to the **adjunction morphism** `M → T' T M` (Humphreys, GSM 94, §7.15). For
`λ` regular antidominant and `μ♮` on a single wall `s` of the chamber of `λ♮`, with
`T = T_λ^μ` (`L = L(ν)`) and `T' = T_μ^λ` (`L(ν)^* ≅ L(-w₀ν)`), `T' T = Θ_s` is the wall-crossing
functor and this is the morphism `M → Θ_s M` of §7.15; its cokernel is the shuffling
`Sh_s M`:
`M → Θ_s M → Sh_s M → 0`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.translationUnit`: the adjunction morphism `M → T' T M`.
* `Matrix.Realization.KacMoodyAlgebra.shuffling`: its cokernel `T' T M ⧸ im(M)`.
* `Matrix.Realization.KacMoodyAlgebra.shufflingMap`: the action of shuffling on morphisms.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.translationAdjunction_comp_left`: naturality of the
  adjunction in the first variable (`translationAdjunction_comp` is the second).
* `Matrix.Realization.KacMoodyAlgebra.translationAdjunction_eq_comp_translationUnit`: every
  `M → T' N` is `T'(f) ∘ η_M` for the adjoint `f : T M → N` (universal property of the unit).
* `Matrix.Realization.KacMoodyAlgebra.translationUnit_naturality`: `η` is natural,
  `η_{M'} ∘ g = T' T(g) ∘ η_M`.
* `Matrix.Realization.KacMoodyAlgebra.translationUnit_eq_zero_of_subsingleton`,
  `Matrix.Realization.KacMoodyAlgebra.not_injective_translationUnit`: `η_M = 0` if `T M = 0`, so
  it is not injective when moreover `M ≠ 0` (Humphreys' remark in §7.15).
* `Matrix.Realization.KacMoodyAlgebra.shuffling_exact`: `M → Θ M → Sh M → 0` is exact;
  `shufflingMap_id`, `shufflingMap_comp`: functoriality.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.2, §7.15. Shuffling functors are studied further in Chapter 12 of the book.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {M M' M'' N L : Type*}
  [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M]
  [AddCommGroup M'] [Module K M'] [LieRingModule P.KacMoodyAlgebra M']
  [LieModule K P.KacMoodyAlgebra M']
  [AddCommGroup M''] [Module K M''] [LieRingModule P.KacMoodyAlgebra M'']
  [LieModule K P.KacMoodyAlgebra M'']
  [AddCommGroup N] [Module K N] [LieRingModule P.KacMoodyAlgebra N]
  [LieModule K P.KacMoodyAlgebra N]
  [AddCommGroup L] [Module K L] [LieRingModule P.KacMoodyAlgebra L]
  [LieModule K P.KacMoodyAlgebra L]

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

/-- A translated module lies in its target block. -/
theorem centralBlock_centralTranslation_eq_top (χ₁ χ₂ : 𝓩 →ₐ[K] K) :
    centralBlock P (centralTranslation P L χ₁ χ₂ M) χ₂ = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  exact mem_centralBlock_of_injective P (centralTranslation P L χ₁ χ₂ M).incl
    Subtype.val_injective χ₂ v.property

variable [FiniteDimensional K L] [CharZero K] [IsAlgClosed K]

/-- **Naturality of the translation adjunction** in the first variable:
`adj f ∘ g = adj (f ∘ T g)` (Humphreys, GSM 94, §7.2). -/
theorem translationAdjunction_comp_left (hM : IsCategoryO P M) (hM' : IsCategoryO P M')
    (hL : IsCategoryO P L) {χ₁ χ₂ : 𝓩 →ₐ[K] K} (hMχ : centralBlock P M χ₁ = ⊤)
    (hM'χ : centralBlock P M' χ₁ = ⊤) (hNχ : centralBlock P N χ₂ = ⊤) (g : M →ₗ⁅K,𝔤⁆ M')
    (f : centralTranslation P L χ₁ χ₂ M' →ₗ⁅K,𝔤⁆ N) :
    (translationAdjunction P hM' hL hM'χ hNχ f).comp g =
      translationAdjunction P hM hL hMχ hNχ (f.comp (centralTranslationMap P L χ₁ χ₂ g)) := by
  ext m
  apply (rTensorEquiv P (Module.Dual K L) (equivCentralBlockOfEqTop P hNχ)).injective
  apply (tensorDualEquivHom P N L).injective
  change tensorDualEquivHom P N L (rTensorEquiv P (Module.Dual K L)
      (equivCentralBlockOfEqTop P hNχ)
        (rTensorEquiv P (Module.Dual K L) (equivCentralBlockOfEqTop P hNχ).symm _)) =
    tensorDualEquivHom P N L (rTensorEquiv P (Module.Dual K L) (equivCentralBlockOfEqTop P hNχ)
        (rTensorEquiv P (Module.Dual K L) (equivCentralBlockOfEqTop P hNχ).symm _))
  rw [rTensorEquiv_apply_symm_apply, rTensorEquiv_apply_symm_apply]
  change tensorDualEquivHom P N L ((tensorDualEquivHom P N L).symm _) =
    tensorDualEquivHom P N L ((tensorDualEquivHom P N L).symm _)
  rw [LieModuleEquiv.apply_symm_apply, LieModuleEquiv.apply_symm_apply]
  ext l
  change f _ = f _
  congr 1
  apply Subtype.ext
  have hX := ((hM.centralBlock P χ₁).tensorProduct hL).isCentralLocallyFinite P
  have hX' := ((hM'.centralBlock P χ₁).tensorProduct hL).isCentralLocallyFinite P
  have hx : (equivCentralBlockOfEqTop P hM'χ).symm (g m) =
      centralBlockMap P g χ₁ ((equivCentralBlockOfEqTop P hMχ).symm m) := by
    apply (equivCentralBlockOfEqTop P hM'χ).injective
    rw [LieModuleEquiv.apply_symm_apply]
    change g m = g ((equivCentralBlockOfEqTop P hMχ) ((equivCentralBlockOfEqTop P hMχ).symm m))
    rw [LieModuleEquiv.apply_symm_apply]
  change centralBlockProjection P hX' χ₂ ((equivCentralBlockOfEqTop P hM'χ).symm (g m) ⊗ₜ l) =
    TensorProduct.LieModule.map (centralBlockMap P g χ₁) (LieModuleHom.id : L →ₗ⁅K,𝔤⁆ L)
      (centralBlockProjection P hX χ₂ ((equivCentralBlockOfEqTop P hMχ).symm m ⊗ₜ l))
  rw [hx]
  exact (LieModuleHom.congr_fun (centralBlockProjection_natural P hX hX'
    (TensorProduct.LieModule.map (centralBlockMap P g χ₁)
      (LieModuleHom.id : L →ₗ⁅K,𝔤⁆ L)) χ₂)
    ((equivCentralBlockOfEqTop P hMχ).symm m ⊗ₜ l)).symm

section Unit

variable {X X' X'' : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]
  [AddCommGroup X'] [Module K X'] [LieRingModule P.KacMoodyAlgebra X']
  [LieModule K P.KacMoodyAlgebra X']
  [AddCommGroup X''] [Module K X''] [LieRingModule P.KacMoodyAlgebra X'']
  [LieModule K P.KacMoodyAlgebra X'']

/-- **The adjunction morphism** `η_M : M → T' T M` (Humphreys, GSM 94, §7.15): the adjoint of
the identity of `T M`, stated with a module `X ≅ T M` (take `X = T M`) as `M → T' X`. For
`T = T_λ^μ` translation to a wall, `T' T = Θ_s`. -/
def translationUnit (hM : IsCategoryO P M) (hL : IsCategoryO P L) {χ₁ χ₂ : 𝓩 →ₐ[K] K}
    (hMχ : centralBlock P M χ₁ = ⊤) (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M)
    (hXχ : centralBlock P X χ₂ = ⊤) :
    M →ₗ⁅K,𝔤⁆ centralTranslation P (Module.Dual K L) χ₂ χ₁ X :=
  translationAdjunction P hM hL hMχ hXχ eX.symm.toLieModuleHom

/-- **Universal property of the unit**: the adjoint of `f : T M → N` is `T'(f) ∘ η_M`. -/
theorem translationAdjunction_eq_comp_translationUnit (hM : IsCategoryO P M)
    (hL : IsCategoryO P L) {χ₁ χ₂ : 𝓩 →ₐ[K] K} (hMχ : centralBlock P M χ₁ = ⊤)
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M) (hXχ : centralBlock P X χ₂ = ⊤)
    (hNχ : centralBlock P N χ₂ = ⊤) (f : centralTranslation P L χ₁ χ₂ M →ₗ⁅K,𝔤⁆ N) :
    translationAdjunction P hM hL hMχ hNχ f =
      (centralTranslationMap P (Module.Dual K L) χ₂ χ₁ (f.comp eX.toLieModuleHom)).comp
        (translationUnit P hM hL hMχ eX hXχ) := by
  refine Eq.trans ?_ (translationAdjunction_comp P hM hL hMχ hXχ hNχ (f.comp eX.toLieModuleHom)
    eX.symm.toLieModuleHom)
  congr 1
  ext x
  simp

/-- **Naturality of the unit**: `η_{M'} ∘ g = T' T(g) ∘ η_M`, stated for `X ≅ T M`,
`X' ≅ T M'` and `g_X : X → X'` corresponding to `T(g)`. -/
theorem translationUnit_naturality (hM : IsCategoryO P M) (hL : IsCategoryO P L)
    {χ₁ χ₂ : 𝓩 →ₐ[K] K} (hMχ : centralBlock P M χ₁ = ⊤)
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M) (hXχ : centralBlock P X χ₂ = ⊤)
    (hM' : IsCategoryO P M') (hM'χ : centralBlock P M' χ₁ = ⊤)
    (eX' : X' ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M') (hX'χ : centralBlock P X' χ₂ = ⊤)
    (g : M →ₗ⁅K,𝔤⁆ M') (gX : X →ₗ⁅K,𝔤⁆ X')
    (hg : ∀ x, eX' (gX x) = centralTranslationMap P L χ₁ χ₂ g (eX x)) :
    (translationUnit P hM' hL hM'χ eX' hX'χ).comp g =
      (centralTranslationMap P (Module.Dual K L) χ₂ χ₁ gX).comp
        (translationUnit P hM hL hMχ eX hXχ) := by
  have key : eX'.symm.toLieModuleHom.comp (centralTranslationMap P L χ₁ χ₂ g) =
      gX.comp eX.symm.toLieModuleHom := by
    refine LieModuleHom.ext fun y ↦ ?_
    obtain ⟨x, rfl⟩ := eX.surjective y
    apply eX'.injective
    rw [LieModuleHom.comp_apply, LieModuleHom.comp_apply, LieModuleEquiv.coe_toLieModuleHom,
      LieModuleEquiv.coe_toLieModuleHom, LieModuleEquiv.symm_apply_apply,
      LieModuleEquiv.apply_symm_apply, hg]
  exact (translationAdjunction_comp_left P hM hM' hL hMχ hM'χ hX'χ g
    eX'.symm.toLieModuleHom).trans ((congrArg _ key).trans
      (translationAdjunction_comp P hM hL hMχ hXχ hX'χ gX eX.symm.toLieModuleHom))

/-- `η_M = 0` if `T M = 0`. -/
theorem translationUnit_eq_zero_of_subsingleton (hM : IsCategoryO P M) (hL : IsCategoryO P L)
    {χ₁ χ₂ : 𝓩 →ₐ[K] K} (hMχ : centralBlock P M χ₁ = ⊤)
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M) (hXχ : centralBlock P X χ₂ = ⊤)
    [Subsingleton X] : translationUnit P hM hL hMχ eX hXχ = 0 := by
  have : eX.symm.toLieModuleHom = 0 := LieModuleHom.ext fun _ ↦ Subsingleton.elim _ _
  rw [translationUnit, this, map_zero]

/-- The adjunction morphism is not injective when `M ≠ 0` and `T M = 0` (Humphreys, GSM 94,
§7.15). -/
theorem not_injective_translationUnit (hM : IsCategoryO P M) (hL : IsCategoryO P L)
    {χ₁ χ₂ : 𝓩 →ₐ[K] K} (hMχ : centralBlock P M χ₁ = ⊤)
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M) (hXχ : centralBlock P X χ₂ = ⊤)
    [Nontrivial M] [Subsingleton X] :
    ¬Function.Injective (translationUnit P hM hL hMχ eX hXχ) := by
  intro hinj
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  refine hm (hinj ?_)
  rw [translationUnit_eq_zero_of_subsingleton P hM hL hMχ eX hXχ, map_zero]
  rfl

/-- **Shuffling** (Humphreys, GSM 94, §7.15): the cokernel `T' T M ⧸ η_M(M)` of the adjunction
morphism, `Sh_s M` for `T' T = Θ_s` (with `X ≅ T M`). -/
abbrev shuffling (hM : IsCategoryO P M) (hL : IsCategoryO P L) {χ₁ χ₂ : 𝓩 →ₐ[K] K}
    (hMχ : centralBlock P M χ₁ = ⊤) (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M)
    (hXχ : centralBlock P X χ₂ = ⊤) : Type _ :=
  centralTranslation P (Module.Dual K L) χ₂ χ₁ X ⧸ (translationUnit P hM hL hMχ eX hXχ).range

/-- The projection `T' T M → Sh M`. -/
def shufflingProj (hM : IsCategoryO P M) (hL : IsCategoryO P L) {χ₁ χ₂ : 𝓩 →ₐ[K] K}
    (hMχ : centralBlock P M χ₁ = ⊤) (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M)
    (hXχ : centralBlock P X χ₂ = ⊤) :
    centralTranslation P (Module.Dual K L) χ₂ χ₁ X →ₗ⁅K,𝔤⁆ shuffling P hM hL hMχ eX hXχ :=
  LieSubmodule.Quotient.mk' _

/-- **`M → Θ M → Sh M → 0` is exact** (Humphreys, GSM 94, §7.15). -/
theorem shuffling_exact (hM : IsCategoryO P M) (hL : IsCategoryO P L) {χ₁ χ₂ : 𝓩 →ₐ[K] K}
    (hMχ : centralBlock P M χ₁ = ⊤) (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M)
    (hXχ : centralBlock P X χ₂ = ⊤) :
    (shufflingProj P hM hL hMχ eX hXχ).ker = (translationUnit P hM hL hMχ eX hXχ).range ∧
      Function.Surjective (shufflingProj P hM hL hMχ eX hXχ) :=
  ⟨LieSubmodule.Quotient.mk'_ker _, LieSubmodule.Quotient.surjective_mk' _⟩

/-- The action of shuffling on a morphism `g : M → M'` (with `g_X : X → X'` corresponding to
`T(g)`): the map induced by `T'(g_X)`. -/
def shufflingMap (hM : IsCategoryO P M) (hL : IsCategoryO P L) {χ₁ χ₂ : 𝓩 →ₐ[K] K}
    (hMχ : centralBlock P M χ₁ = ⊤) (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M)
    (hXχ : centralBlock P X χ₂ = ⊤) (hM' : IsCategoryO P M') (hM'χ : centralBlock P M' χ₁ = ⊤)
    (eX' : X' ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M') (hX'χ : centralBlock P X' χ₂ = ⊤)
    (g : M →ₗ⁅K,𝔤⁆ M') (gX : X →ₗ⁅K,𝔤⁆ X')
    (hg : ∀ x, eX' (gX x) = centralTranslationMap P L χ₁ χ₂ g (eX x)) :
    shuffling P hM hL hMχ eX hXχ →ₗ⁅K,𝔤⁆ shuffling P hM' hL hM'χ eX' hX'χ :=
  LieSubmodule.Quotient.lift _ ((shufflingProj P hM' hL hM'χ eX' hX'χ).comp
    (centralTranslationMap P (Module.Dual K L) χ₂ χ₁ gX)) (by
      rintro _ ⟨m, rfl⟩
      have h := LieModuleHom.congr_fun
        (translationUnit_naturality P hM hL hMχ eX hXχ hM' hM'χ eX' hX'χ g gX hg) m
      rw [LieModuleHom.mem_ker, LieModuleHom.comp_apply]
      change shufflingProj P hM' hL hM'χ eX' hX'χ
        ((centralTranslationMap P (Module.Dual K L) χ₂ χ₁ gX).comp
          (translationUnit P hM hL hMχ eX hXχ) m) = 0
      rw [← h, shufflingProj, LieSubmodule.Quotient.mk_eq_zero]
      exact (LieModuleHom.mem_range _ _).mpr ⟨g m, rfl⟩)

theorem shufflingMap_shufflingProj (hM : IsCategoryO P M) (hL : IsCategoryO P L)
    {χ₁ χ₂ : 𝓩 →ₐ[K] K} (hMχ : centralBlock P M χ₁ = ⊤)
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M) (hXχ : centralBlock P X χ₂ = ⊤)
    (hM' : IsCategoryO P M') (hM'χ : centralBlock P M' χ₁ = ⊤)
    (eX' : X' ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M') (hX'χ : centralBlock P X' χ₂ = ⊤)
    (g : M →ₗ⁅K,𝔤⁆ M') (gX : X →ₗ⁅K,𝔤⁆ X')
    (hg : ∀ x, eX' (gX x) = centralTranslationMap P L χ₁ χ₂ g (eX x))
    (y : centralTranslation P (Module.Dual K L) χ₂ χ₁ X) :
    shufflingMap P hM hL hMχ eX hXχ hM' hM'χ eX' hX'χ g gX hg
        (shufflingProj P hM hL hMχ eX hXχ y) =
      shufflingProj P hM' hL hM'χ eX' hX'χ
        (centralTranslationMap P (Module.Dual K L) χ₂ χ₁ gX y) :=
  rfl

/-- Shuffling preserves identities. -/
theorem shufflingMap_id (hM : IsCategoryO P M) (hL : IsCategoryO P L) {χ₁ χ₂ : 𝓩 →ₐ[K] K}
    (hMχ : centralBlock P M χ₁ = ⊤) (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M)
    (hXχ : centralBlock P X χ₂ = ⊤)
    (hg : ∀ x, eX (LieModuleHom.id x) = centralTranslationMap P L χ₁ χ₂ LieModuleHom.id (eX x)) :
    shufflingMap P hM hL hMχ eX hXχ hM hMχ eX hXχ LieModuleHom.id LieModuleHom.id hg =
      LieModuleHom.id := by
  refine LieModuleHom.ext fun y ↦ ?_
  obtain ⟨y, rfl⟩ := (shuffling_exact P hM hL hMχ eX hXχ).2 y
  rw [shufflingMap_shufflingProj, centralTranslationMap_id]
  rfl

/-- Shuffling preserves composition. -/
theorem shufflingMap_comp (hM : IsCategoryO P M) (hL : IsCategoryO P L) {χ₁ χ₂ : 𝓩 →ₐ[K] K}
    (hMχ : centralBlock P M χ₁ = ⊤) (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M)
    (hXχ : centralBlock P X χ₂ = ⊤) (hM' : IsCategoryO P M') (hM'χ : centralBlock P M' χ₁ = ⊤)
    (eX' : X' ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M') (hX'χ : centralBlock P X' χ₂ = ⊤)
    (hM'' : IsCategoryO P M'') (hM''χ : centralBlock P M'' χ₁ = ⊤)
    (eX'' : X'' ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M'') (hX''χ : centralBlock P X'' χ₂ = ⊤)
    (g : M →ₗ⁅K,𝔤⁆ M') (g' : M' →ₗ⁅K,𝔤⁆ M'') (gX : X →ₗ⁅K,𝔤⁆ X') (gX' : X' →ₗ⁅K,𝔤⁆ X'')
    (hg : ∀ x, eX' (gX x) = centralTranslationMap P L χ₁ χ₂ g (eX x))
    (hg' : ∀ x, eX'' (gX' x) = centralTranslationMap P L χ₁ χ₂ g' (eX' x))
    (hgg : ∀ x, eX'' (gX'.comp gX x) = centralTranslationMap P L χ₁ χ₂ (g'.comp g) (eX x)) :
    shufflingMap P hM hL hMχ eX hXχ hM'' hM''χ eX'' hX''χ (g'.comp g) (gX'.comp gX) hgg =
      (shufflingMap P hM' hL hM'χ eX' hX'χ hM'' hM''χ eX'' hX''χ g' gX' hg').comp
        (shufflingMap P hM hL hMχ eX hXχ hM' hM'χ eX' hX'χ g gX hg) := by
  refine LieModuleHom.ext fun y ↦ ?_
  obtain ⟨y, rfl⟩ := (shuffling_exact P hM hL hMχ eX hXχ).2 y
  rw [LieModuleHom.comp_apply, shufflingMap_shufflingProj, shufflingMap_shufflingProj,
    shufflingMap_shufflingProj, centralTranslationMap_comp]
  rfl

end Unit

end Matrix.Realization.KacMoodyAlgebra
