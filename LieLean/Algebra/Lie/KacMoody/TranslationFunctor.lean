/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationVerma

/-!
# Translation functors on category `𝒪`

For a `𝔤(A)`-module `Z` and central characters `χ₁, χ₂`, the translation of a module `V` is
`T V = pr_{χ₂}(pr_{χ₁} V ⊗ Z)`, with `pr_χ` the generalized central block. It acts on morphisms
by restriction of `(pr_{χ₁} f) ⊗ id_Z`. (It uses full-central blocks; the older
`IsStandardForm.translation` uses Casimir eigenspaces.)

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.centralTranslation`: the object `pr_{χ₂}(pr_{χ₁} V ⊗ Z)`.
* `Matrix.Realization.KacMoodyAlgebra.centralTranslationMap`: its action on Lie-module maps.

## Main results

* `centralTranslationMap_id`, `centralTranslationMap_comp`: functoriality.
* `centralTranslationMap_shortExact`: over an algebraically closed field, translation preserves
  short exact sequences whose middle term is in `𝒪`, when `Z` is in `𝒪` (Humphreys, GSM 94, §7.1
  (check)).
* `translation_verma_equiv`: the translation `T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν))` sends
  `M(w·λ)` to `M(w·μ)` under the facet hypotheses of `translation_verma` (Humphreys, GSM 94,
  Theorem 7.6 (check), Verma part, integral weights, finite type).

Exactness combines exactness of block restriction (`IsCategoryO.shortExact_centralBlockMap`)
with exactness of `− ⊗ Z` over a field. The tensor factor is written on the right.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {U V W Z : Type*}
  [AddCommGroup U] [Module K U] [LieRingModule P.KacMoodyAlgebra U]
  [LieModule K P.KacMoodyAlgebra U]
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]
  [AddCommGroup Z] [Module K Z] [LieRingModule P.KacMoodyAlgebra Z]
  [LieModule K P.KacMoodyAlgebra Z]

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

variable (Z) in
/-- The translation `pr_{χ₂}(pr_{χ₁} V ⊗ Z)` of a module `V`. -/
abbrev centralTranslation (χ₁ χ₂ : 𝓩 →ₐ[K] K) (V : Type*) [AddCommGroup V] [Module K V]
    [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] :
    LieSubmodule K 𝔤 (centralBlock P V χ₁ ⊗[K] Z) :=
  centralBlock P (centralBlock P V χ₁ ⊗[K] Z) χ₂

variable (Z) in
/-- The action of translation on Lie-module maps. -/
def centralTranslationMap (χ₁ χ₂ : 𝓩 →ₐ[K] K) (f : V →ₗ⁅K,𝔤⁆ W) :
    centralTranslation P Z χ₁ χ₂ V →ₗ⁅K,𝔤⁆ centralTranslation P Z χ₁ χ₂ W :=
  centralBlockMap P (TensorProduct.LieModule.map (centralBlockMap P f χ₁) LieModuleHom.id) χ₂

variable (Z) in
theorem centralTranslationMap_id (χ₁ χ₂ : 𝓩 →ₐ[K] K) :
    centralTranslationMap P Z χ₁ χ₂ (LieModuleHom.id : V →ₗ⁅K,𝔤⁆ V) = LieModuleHom.id := by
  ext x
  change (TensorProduct.map _ _ x.val : _) = x.val
  rw [centralBlockMap_id]
  exact congrFun (congrArg DFunLike.coe TensorProduct.map_id) x.val

variable (Z) in
theorem centralTranslationMap_comp (χ₁ χ₂ : 𝓩 →ₐ[K] K) (f : U →ₗ⁅K,𝔤⁆ V) (g : V →ₗ⁅K,𝔤⁆ W) :
    centralTranslationMap P Z χ₁ χ₂ (g.comp f) =
      (centralTranslationMap P Z χ₁ χ₂ g).comp (centralTranslationMap P Z χ₁ χ₂ f) := by
  ext x
  change (TensorProduct.map _ _ x.val : _) = TensorProduct.map _ _ (TensorProduct.map _ _ x.val)
  rw [centralBlockMap_comp, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  rfl

omit [LieModule K 𝔤 U] [LieModule K 𝔤 V] [LieModule K 𝔤 W] in
/-- Equality of the kernel and range of Lie-module maps is exactness of the underlying maps. -/
theorem exact_iff_ker_eq_range (f : U →ₗ⁅K,𝔤⁆ V) (g : V →ₗ⁅K,𝔤⁆ W) :
    Function.Exact f g ↔ g.ker = f.range := by
  constructor
  · intro h
    ext y
    rw [LieModuleHom.mem_ker, LieModuleHom.mem_range]
    exact h y
  · intro h y
    have := congrArg (fun S : LieSubmodule K 𝔤 V => y ∈ S) h
    simpa only [LieModuleHom.mem_ker, LieModuleHom.mem_range, eq_iff_iff, Set.mem_range] using this

variable (Z) in
/-- **Translation is exact** (Humphreys, GSM 94, §7.1 (check)): over an algebraically closed
field, translation preserves short exact sequences whose middle term is in `𝒪`, for `Z` in
`𝒪`. -/
theorem centralTranslationMap_shortExact [CharZero K] [IsAlgClosed K] (hV : IsCategoryO P V)
    (hZ : IsCategoryO P Z)
    (f : U →ₗ⁅K,𝔤⁆ V) (g : V →ₗ⁅K,𝔤⁆ W) (hf : Function.Injective f) (hex : g.ker = f.range)
    (hg : Function.Surjective g) (χ₁ χ₂ : 𝓩 →ₐ[K] K) :
    Function.Injective (centralTranslationMap P Z χ₁ χ₂ f) ∧
      (centralTranslationMap P Z χ₁ χ₂ g).ker = (centralTranslationMap P Z χ₁ χ₂ f).range ∧
      Function.Surjective (centralTranslationMap P Z χ₁ χ₂ g) := by
  obtain ⟨hf₁, hex₁, hg₁⟩ := hV.shortExact_centralBlockMap P f g hf hex hg χ₁
  set f₁ := centralBlockMap P f χ₁
  set g₁ := centralBlockMap P g χ₁
  let F := TensorProduct.LieModule.map f₁ (LieModuleHom.id : Z →ₗ⁅K,𝔤⁆ Z)
  let G := TensorProduct.LieModule.map g₁ (LieModuleHom.id : Z →ₗ⁅K,𝔤⁆ Z)
  have eF : F.toLinearMap = LinearMap.rTensor Z f₁.toLinearMap := by
    rw [TensorProduct.LieModule.toLinearMap_map]
    rfl
  have eG : G.toLinearMap = LinearMap.rTensor Z g₁.toLinearMap := by
    rw [TensorProduct.LieModule.toLinearMap_map]
    rfl
  have hF : Function.Injective F := by
    rw [← LieModuleHom.coe_toLinearMap, eF]
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := Z) _ hf₁
  have hG : Function.Surjective G := by
    rw [← LieModuleHom.coe_toLinearMap, eG]
    exact LinearMap.rTensor_surjective Z hg₁
  have hFG : G.ker = F.range := by
    rw [← exact_iff_ker_eq_range, ← LieModuleHom.coe_toLinearMap,
      ← LieModuleHom.coe_toLinearMap G, eF, eG]
    exact rTensor_exact Z ((exact_iff_ker_eq_range P f₁ g₁).mpr hex₁) hg₁
  have hmid : IsCategoryO P (centralBlock P V χ₁ ⊗[K] Z) :=
    (hV.centralBlock P χ₁).tensorProduct hZ
  exact hmid.shortExact_centralBlockMap P F G hF hFG hG χ₂

/-- Isomorphic modules have isomorphic central blocks. -/
def centralBlockEquiv (e : V ≃ₗ⁅K,𝔤⁆ W) (χ : 𝓩 →ₐ[K] K) :
    centralBlock P V χ ≃ₗ⁅K,𝔤⁆ centralBlock P W χ :=
  LieModuleEquiv.ofBijective (centralBlockMap P e.toLieModuleHom χ)
    ⟨injective_centralBlockMap P _ e.injective χ, fun y =>
      ⟨⟨e.symm y.val, map_mem_centralBlock P e.symm.toLieModuleHom χ y.property⟩,
        Subtype.ext (e.apply_symm_apply y.val)⟩⟩

variable (Z) in
/-- Tensoring an isomorphism on the right with `Z`. -/
def rTensorEquiv (e : V ≃ₗ⁅K,𝔤⁆ W) : V ⊗[K] Z ≃ₗ⁅K,𝔤⁆ W ⊗[K] Z :=
  LieModuleEquiv.ofBijective
    (TensorProduct.LieModule.map e.toLieModuleHom (LieModuleHom.id : Z →ₗ⁅K,𝔤⁆ Z)) (by
      have h : (TensorProduct.LieModule.map e.toLieModuleHom
          (LieModuleHom.id : Z →ₗ⁅K,𝔤⁆ Z)).toLinearMap =
          (LinearEquiv.rTensor Z e.toLinearEquiv).toLinearMap := by
        rw [TensorProduct.LieModule.toLinearMap_map]
        rfl
      rw [← LieModuleHom.coe_toLinearMap, h]
      exact (LinearEquiv.rTensor Z e.toLinearEquiv).bijective)

/-- A module equal to its own block is isomorphic to that block. -/
def equivCentralBlockOfEqTop {χ : 𝓩 →ₐ[K] K} (h : centralBlock P V χ = ⊤) :
    centralBlock P V χ ≃ₗ⁅K,𝔤⁆ V :=
  LieModuleEquiv.ofBijective (centralBlock P V χ).incl
    ⟨Subtype.val_injective, fun v => ⟨⟨v, h ▸ LieSubmodule.mem_top v⟩, rfl⟩⟩

section Verma

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] {H : Type*} [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsFiniteCartan)

include hA in
/-- **Translation functors on Verma modules** (Humphreys, GSM 94, Theorem 7.6 (check), Verma
part, integral weights, finite type): with `T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν))` and the
hypotheses of `translation_verma`, `T_λ^μ M(w·λ) ≅ M(w·μ)` for every `w ∈ W`. -/
theorem translation_verma_equiv {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    Nonempty (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,KacMoodyAlgebra P⁆
      centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam) (centralCharacter P μ)
        (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam))) := by
  obtain ⟨e⟩ := translation_verma P hA hlam hμ hfacet hν hz hzν w
  have hχ : centralCharacter P (P.weylDot hA.isGeneralizedCartan w lam) =
      centralCharacter P lam := centralCharacter_weyl P hA.isGeneralizedCartan w.property lam
  have htop : centralBlock P (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam))
      (centralCharacter P lam) = ⊤ := hχ ▸ centralBlock_verma P _
  exact ⟨e.trans (centralBlockEquiv P (rTensorEquiv P (IrreducibleModule P ν)
    (equivCentralBlockOfEqTop P htop)).symm (centralCharacter P μ))⟩

end Verma

end Matrix.Realization.KacMoodyAlgebra
