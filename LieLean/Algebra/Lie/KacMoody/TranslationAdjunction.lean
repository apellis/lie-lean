/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationDuality
import Mathlib.LinearAlgebra.Contraction

/-!
# Adjointness of translation functors

For a finite-dimensional module `L` in `𝒪` with dual `L^*` (the contragredient module
`Module.Dual K L`, `⁅x, f⁆ = -f ∘ x`), the translation functors
`T = pr_{χ₂}(pr_{χ₁}(−) ⊗ L)` and `T' = pr_{χ₁}(pr_{χ₂}(−) ⊗ L^*)` are adjoint on the blocks:
`Hom(T M, N) ≅ Hom(M, T' N)` for `M` in the `χ₁`-block and `N` in the `χ₂`-block
(Humphreys, GSM 94, §7.2). With `L = L(ν)` this is the adjunction between `T_λ^μ` and
`T_μ^λ`, where `L(ν)^*` plays the role of `L(-w₀ν)`; the identification `L(ν)^* ≅ L(-w₀ν)` is
not needed and not formalized here.

## Main definitions

* `lieModuleHomCongr`: Hom-space equivalence induced by equivalences of source and target.
* `homCentralBlockSourceEquiv`: `Hom(pr_χ X, N) ≅ Hom(X, N)` for `N` in the `χ`-block.
* `homCentralBlockTargetEquiv`: `Hom(M, pr_χ Y) ≅ Hom(M, Y)` for `M` in the `χ`-block.
* `tensorDualEquivHom`: `N ⊗ L^* ≅ Hom_K(L, N)` as `𝔤(A)`-modules, `L` finite-dimensional.
* `tensorHomAdjunction`: `Hom(M ⊗ L, N) ≅ Hom(M, N ⊗ L^*)`.
* `translationAdjunction`: `Hom(T M, N) ≅ Hom(M, T' N)`.
* `translationAdjunction_irreducible`: the case `L = L(ν)`, `ν` dominant integral, finite type.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {M M' N N' L : Type*}
  [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M]
  [AddCommGroup M'] [Module K M'] [LieRingModule P.KacMoodyAlgebra M']
  [LieModule K P.KacMoodyAlgebra M']
  [AddCommGroup N] [Module K N] [LieRingModule P.KacMoodyAlgebra N]
  [LieModule K P.KacMoodyAlgebra N]
  [AddCommGroup N'] [Module K N'] [LieRingModule P.KacMoodyAlgebra N']
  [LieModule K P.KacMoodyAlgebra N']
  [AddCommGroup L] [Module K L] [LieRingModule P.KacMoodyAlgebra L]
  [LieModule K P.KacMoodyAlgebra L]

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

/-- Equivalences of source and target induce a linear equivalence of Hom spaces. -/
def lieModuleHomCongr (e₁ : M ≃ₗ⁅K,𝔤⁆ M') (e₂ : N ≃ₗ⁅K,𝔤⁆ N') :
    (M →ₗ⁅K,𝔤⁆ N) ≃ₗ[K] (M' →ₗ⁅K,𝔤⁆ N') where
  toFun f := e₂.toLieModuleHom.comp (f.comp e₁.symm.toLieModuleHom)
  invFun g := e₂.symm.toLieModuleHom.comp (g.comp e₁.toLieModuleHom)
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  left_inv f := by ext; simp
  right_inv g := by ext; simp

/-- Maps from a module lying in one block into a module land in that block. -/
def homCentralBlockTargetEquiv {χ : 𝓩 →ₐ[K] K} (hM : centralBlock P M χ = ⊤) :
    (M →ₗ⁅K,𝔤⁆ centralBlock P N χ) ≃ₗ[K] (M →ₗ⁅K,𝔤⁆ N) where
  toFun g := (centralBlock P N χ).incl.comp g
  invFun f := f.codRestrict (centralBlock P N χ) fun m ↦
    map_mem_centralBlock P f χ (hM ▸ LieSubmodule.mem_top m)
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  left_inv g := by ext; rfl
  right_inv f := by ext; rfl

section Source

variable [IsAlgClosed K]

/-- Maps into a module lying in the block `χ` factor through the projection onto the `χ`-block:
`Hom(pr_χ X, N) ≅ Hom(X, N)` for `X` locally finite under the centre. -/
def homCentralBlockSourceEquiv (hX : IsCentralLocallyFinite P M) {χ : 𝓩 →ₐ[K] K}
    (hN : centralBlock P N χ = ⊤) :
    (centralBlock P M χ →ₗ⁅K,𝔤⁆ N) ≃ₗ[K] (M →ₗ⁅K,𝔤⁆ N) where
  toFun g := g.comp ((centralBlockProjection P hX χ).codRestrict _
    (centralBlockProjection_mem P hX χ))
  invFun f := f.comp (centralBlock P M χ).incl
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  left_inv g := by
    ext v
    exact congrArg g (Subtype.ext (centralBlockProjection_self P hX χ v.property))
  right_inv f := by
    ext v
    change f (centralBlockProjection P hX χ v) = f v
    have hv : v ∈ ⨆ θ, (centralBlock P M θ).toSubmodule := by
      rw [iSup_centralBlock_eq_top P hX]; trivial
    induction hv using Submodule.iSup_induction' with
    | mem θ v hv =>
      by_cases hθ : θ = χ
      · subst hθ
        rw [centralBlockProjection_self P hX θ hv]
      · rw [centralBlockProjection_other P hX hθ hv, map_zero]
        have h1 : f v ∈ centralBlock P N θ := map_mem_centralBlock P f θ hv
        have h2 : f v ∈ centralBlock P N χ := hN ▸ LieSubmodule.mem_top _
        exact ((LieSubmodule.mem_bot _).mp ((disjoint_centralBlock P hθ).le_bot
          ((LieSubmodule.mem_inf _ _ _).mpr ⟨h1, h2⟩))).symm
    | zero => simp
    | add v w _ _ hv hw => rw [map_add, map_add, map_add, hv, hw]

end Source

section Tensor

variable [FiniteDimensional K L]

variable (N L) in
/-- `N ⊗ L^* ≅ Hom_K(L, N)` as `𝔤(A)`-modules, `n ⊗ f ↦ (l ↦ f(l) n)`, for `L`
finite-dimensional. -/
def tensorDualEquivHom : N ⊗[K] Module.Dual K L ≃ₗ⁅K,𝔤⁆ (L →ₗ[K] N) :=
  let e : N ⊗[K] Module.Dual K L ≃ₗ[K] (L →ₗ[K] N) :=
    (TensorProduct.comm K N (Module.Dual K L)).trans (dualTensorHomEquiv K L N)
  LieModuleEquiv.ofBijective
    { toLinearMap := e.toLinearMap
      map_lie' := fun {x t} ↦ by
        change e ⁅x, t⁆ = ⁅x, e t⁆
        induction t with
        | add s t hs ht => rw [lie_add, map_add, hs, ht, map_add, lie_add]
        | tmul n f =>
          ext l
          simp [e, TensorProduct.LieModule.lie_tmul_right, lie_smul, sub_eq_add_neg] }
    e.bijective

/-- **Tensor–Hom adjunction** for a finite-dimensional module `L`:
`Hom(M ⊗ L, N) ≅ Hom(M, N ⊗ L^*)`. -/
def tensorHomAdjunction :
    (M ⊗[K] L →ₗ⁅K,𝔤⁆ N) ≃ₗ[K] (M →ₗ⁅K,𝔤⁆ N ⊗[K] Module.Dual K L) :=
  (TensorProduct.LieModule.liftLie K 𝔤 M L N).symm.trans
    (lieModuleHomCongr P LieModuleEquiv.refl (tensorDualEquivHom P N L).symm)

variable [CharZero K] [IsAlgClosed K]

/-- **Adjointness of translation functors** (Humphreys, GSM 94, §7.2): for `M` in `𝒪`
lying in the block `χ₁`, `N` lying in the block `χ₂`, and a finite-dimensional `L` in `𝒪`,
`Hom(pr_{χ₂}(pr_{χ₁} M ⊗ L), N) ≅ Hom(M, pr_{χ₁}(pr_{χ₂} N ⊗ L^*))`, `K`-linearly. -/
def translationAdjunction (hM : IsCategoryO P M) (hL : IsCategoryO P L) {χ₁ χ₂ : 𝓩 →ₐ[K] K}
    (hMχ : centralBlock P M χ₁ = ⊤) (hNχ : centralBlock P N χ₂ = ⊤) :
    (centralTranslation P L χ₁ χ₂ M →ₗ⁅K,𝔤⁆ N) ≃ₗ[K]
      (M →ₗ⁅K,𝔤⁆ centralTranslation P (Module.Dual K L) χ₂ χ₁ N) :=
  (homCentralBlockSourceEquiv P
      (((hM.centralBlock P χ₁).tensorProduct hL).isCentralLocallyFinite P) hNχ).trans <|
    (tensorHomAdjunction P).trans <|
      (lieModuleHomCongr P (equivCentralBlockOfEqTop P hMχ) LieModuleEquiv.refl).trans <|
        (homCentralBlockTargetEquiv P hMχ).symm.trans <|
          lieModuleHomCongr P LieModuleEquiv.refl
            (centralBlockEquiv P (rTensorEquiv P (Module.Dual K L)
              (equivCentralBlockOfEqTop P hNχ).symm) χ₁)

end Tensor

section Irreducible

variable {ι' H' : Type*} {K' : Type} [Fintype ι'] [DecidableEq ι'] [Field K'] [CharZero K']
  [IsAlgClosed K'] [AddCommGroup H'] [Module K' H'] [FiniteDimensional K' H']
  {A' : Matrix ι' ι' ℤ} (P' : Realization A' K' H') (hA : A'.IsFiniteCartan)
  {M₁ N₁ : Type*}
  [AddCommGroup M₁] [Module K' M₁] [LieRingModule P'.KacMoodyAlgebra M₁]
  [LieModule K' P'.KacMoodyAlgebra M₁]
  [AddCommGroup N₁] [Module K' N₁] [LieRingModule P'.KacMoodyAlgebra N₁]
  [LieModule K' P'.KacMoodyAlgebra N₁]

include hA in
/-- **Adjointness of `T_λ^μ` and `T_μ^λ`** (Humphreys, GSM 94, §7.2), finite type: for
`ν` dominant integral, `T = pr_{χ₂}(pr_{χ₁}(−) ⊗ L(ν))` and
`T' = pr_{χ₁}(pr_{χ₂}(−) ⊗ L(ν)^*)`, `Hom(T M, N) ≅ Hom(M, T' N)` for `M ∈ 𝒪` in the block `χ₁`
and `N` in the block `χ₂`. -/
def translationAdjunction_irreducible {ν : Dual K' H'} (hν : P'.IsDominantIntegral ν)
    (hM : IsCategoryO P' M₁)
    {χ₁ χ₂ : Subalgebra.center K' (UniversalEnvelopingAlgebra K' P'.KacMoodyAlgebra) →ₐ[K'] K'}
    (hMχ : centralBlock P' M₁ χ₁ = ⊤) (hNχ : centralBlock P' N₁ χ₂ = ⊤) :
    (centralTranslation P' (IrreducibleModule P' ν) χ₁ χ₂ M₁ →ₗ⁅K',P'.KacMoodyAlgebra⁆ N₁)
      ≃ₗ[K'] (M₁ →ₗ⁅K',P'.KacMoodyAlgebra⁆
        centralTranslation P' (Module.Dual K' (IrreducibleModule P' ν)) χ₂ χ₁ N₁) :=
  have := IrreducibleModule.finiteDimensional (P := P') hA hν
  translationAdjunction P' hM (IrreducibleModule.isCategoryO P' ν) hMχ hNχ

end Irreducible

end Matrix.Realization.KacMoodyAlgebra
