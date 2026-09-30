/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.DualIrreducible
import LieLean.Algebra.Lie.KacMoody.TranslationAdjunction
import LieLean.Algebra.Lie.KacMoody.TranslationSimple

/-!
# Translation within a facet

Let `λ + ρ`, `μ + ρ` be antidominant integral with the same simple walls (`λ` and `μ` lie in the
same facet), `ν = z(μ - λ)` dominant, and `T = T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν))`,
`T' = T_μ^λ = pr_{χ_λ}(pr_{χ_μ}(−) ⊗ L(ν)^*)` its adjoint (`translationAdjunction`). Then
(finite type, algebraically closed field of characteristic zero; Humphreys, GSM 94, Theorem 7.9
(check) and §7.8 (check)):

* `translation_irreducible_of_sameFacet`: `T L(w·λ) ≅ L(w·μ)`;
* `translation_translation_verma_of_sameFacet`: `T' T M(w·λ) ≅ M(w·λ)`;
* `translation_translation_irreducible_of_sameFacet`: `T' T L(w·λ) ≅ L(w·λ)`.

The first is proved (reconstructed) by adjunction: `Hom(M(w·μ), T L(w·λ)) ≅ Hom(T'' M(w·μ), L(w·λ))`
with `T''` the translation by `L(ν)^* ≅ L(ν')`, `ν'` dominant in `W(-ν)`
(`IrreducibleModule.exists_equiv_dual`); `T'' M(w·μ) ≅ M(w·λ)` by the Verma part applied with the
roles of `λ, μ` exchanged, so the quotient map `M(w·λ) → L(w·λ)` gives a nonzero element and
`T L(w·λ) ≠ 0`; the dichotomy `translation_irreducible` then gives `T L(w·λ) ≅ L(w·μ)`.

Isomorphisms of functors (natural in all modules of the block) are not formalized; the
statements are on Verma and simple modules. The general upper-closure criterion of Thm. 7.9
(walls of `μ` not walls of `λ`) is not formalized.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Equivs

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V W Z Z' : Type*}
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]
  [AddCommGroup Z] [Module K Z] [LieRingModule P.KacMoodyAlgebra Z]
  [LieModule K P.KacMoodyAlgebra Z]
  [AddCommGroup Z'] [Module K Z'] [LieRingModule P.KacMoodyAlgebra Z']
  [LieModule K P.KacMoodyAlgebra Z']

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

variable (V) in
/-- `id_V ⊗ e : V ⊗ Z ≃ V ⊗ Z'` as `𝔤(A)`-modules. -/
def lTensorEquiv (e : Z ≃ₗ⁅K,𝔤⁆ Z') : V ⊗[K] Z ≃ₗ⁅K,𝔤⁆ V ⊗[K] Z' :=
  LieModuleEquiv.ofBijective
    (TensorProduct.LieModule.map (LieModuleHom.id : V →ₗ⁅K,𝔤⁆ V) e.toLieModuleHom) (by
      have h : (TensorProduct.LieModule.map (LieModuleHom.id : V →ₗ⁅K,𝔤⁆ V)
          e.toLieModuleHom).toLinearMap = (LinearEquiv.lTensor V e.toLinearEquiv).toLinearMap := by
        rw [TensorProduct.LieModule.toLinearMap_map]
        rfl
      rw [← LieModuleHom.coe_toLinearMap, h]
      exact (LinearEquiv.lTensor V e.toLinearEquiv).bijective)

variable (Z) in
/-- Translation of an equivalence of modules. -/
def centralTranslationEquiv (χ₁ χ₂ : 𝓩 →ₐ[K] K) (e : V ≃ₗ⁅K,𝔤⁆ W) :
    centralTranslation P Z χ₁ χ₂ V ≃ₗ⁅K,𝔤⁆ centralTranslation P Z χ₁ χ₂ W :=
  centralBlockEquiv P (rTensorEquiv P Z (centralBlockEquiv P e χ₁)) χ₂

variable (V) in
/-- Translation functors with equivalent coefficient modules agree. -/
def centralTranslationCoeffEquiv (χ₁ χ₂ : 𝓩 →ₐ[K] K) (e : Z ≃ₗ⁅K,𝔤⁆ Z') :
    centralTranslation P Z χ₁ χ₂ V ≃ₗ⁅K,𝔤⁆ centralTranslation P Z' χ₁ χ₂ V :=
  centralBlockEquiv P (lTensorEquiv P (centralBlock P V χ₁) e) χ₂

end Equivs

section SameFacet

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- The Verma part of Humphreys, GSM 94, Thm. 7.6 (check) with the roles of `λ` and `μ`
exchanged, when `λ` and `μ` lie in the same facet: translation back by the dual `L(ν)^*`
(realized as `L(ν')`, `ν'` dominant in `W(-ν)`) sends `M(w·μ)` to `M(w·λ)`. -/
theorem exists_translation_verma_back {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet' : ∀ i, (μ + P.rho) (P.coroot i) = 0 → (lam + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    ∃ ν' : Dual K H, ∃ z' ∈ P.weylGroup hA.isGeneralizedCartan,
      P.IsDominantIntegral ν' ∧ z' (lam - μ) = ν' ∧
      Nonempty (Module.Dual K (IrreducibleModule P ν) ≃ₗ⁅K,𝔤⁆ IrreducibleModule P ν') ∧
      Nonempty (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam) ≃ₗ⁅K,𝔤⁆
        centralTranslation P (IrreducibleModule P ν') (centralCharacter P μ)
          (centralCharacter P lam) (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ))) := by
  obtain ⟨z', hz', hν', ⟨eν⟩⟩ := IrreducibleModule.exists_equiv_dual P hA hν
  have hzz : z' * z ∈ P.weylGroup hA.isGeneralizedCartan := mul_mem hz' hz
  have hzν' : (z' * z) (lam - μ) = z' (-ν) := by
    change z' (z (lam - μ)) = z' (-ν)
    rw [← hzν, ← map_neg, neg_sub]
  exact ⟨z' (-ν), z' * z, hzz, hν', hzν', ⟨eν⟩,
    translation_verma_equiv P hA hμ hlam hfacet' hν' hzz hzν' w⟩

include hA in
/-- **Translation of simple modules within a facet** (Humphreys, GSM 94, Theorem 7.9 (check),
case `λ`, `μ` in the same facet; integral weights, finite type, algebraically closed field of
characteristic zero): with the hypotheses of `translation_verma` and the reverse wall
inclusion, `T_λ^μ L(w·λ) ≅ L(w·μ)`. -/
theorem translation_irreducible_of_sameFacet {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hfacet' : ∀ i, (μ + P.rho) (P.coroot i) = 0 → (lam + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    Nonempty (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) := by
  classical
  have hA' := hA.isGeneralizedCartan
  obtain ⟨ν', -, -, hν', -, ⟨eν⟩, ⟨eV⟩⟩ :=
    exists_translation_verma_back P hA hlam hμ hfacet' hν hz hzν w
  have := IrreducibleModule.finiteDimensional (P := P) hA hν'
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  set x := P.weylDot hA' w lam
  set y := P.weylDot hA' w μ
  have hMχ : centralBlock P (VermaModule P y) (centralCharacter P μ) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' w.property μ) ▸ centralBlock_verma P y
  have hNχ : centralBlock P (IrreducibleModule P x) (centralCharacter P lam) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' w.property lam) ▸ centralBlock_irreducible P x
  let adj := translationAdjunction P (VermaModule.isCategoryO P y)
    (IrreducibleModule.isCategoryO P ν') hMχ hNχ
  let π : VermaModule P x →ₗ⁅K,𝔤⁆ IrreducibleModule P x := LieSubmodule.Quotient.mk' _
  let f₀ := π.comp eV.symm.toLieModuleHom
  have hf₀ : f₀ ≠ 0 := by
    intro h
    have h1 := LieModuleHom.congr_fun h (eV (hwv P x))
    change π (eV.symm (eV (hwv P x))) = 0 at h1
    rw [LieModuleEquiv.symm_apply_apply] at h1
    exact IrreducibleModule.hwv_ne_zero P x h1
  have hg : adj f₀ ≠ 0 := (LinearEquiv.map_ne_zero_iff adj).mpr hf₀
  let eD : Module.Dual K (IrreducibleModule P ν') ≃ₗ⁅K,𝔤⁆ IrreducibleModule P ν :=
    (dualEquiv eν).trans evalEquiv.symm
  let E := centralTranslationCoeffEquiv P (IrreducibleModule P x) (centralCharacter P lam)
    (centralCharacter P μ) eD
  have hnt : ¬ Subsingleton (centralTranslation P (IrreducibleModule P ν)
      (centralCharacter P lam) (centralCharacter P μ) (IrreducibleModule P x)) := by
    intro hs
    exact hg (LieModuleHom.ext fun u ↦ E.injective (Subsingleton.elim _ _))
  rcases translation_irreducible P hA hlam hμ hfacet hν hz hzν w with h | h
  · exact absurd h hnt
  · exact h

include hA in
/-- **`T_μ^λ T_λ^μ M(w·λ) ≅ M(w·λ)`** when `λ` and `μ` lie in the same facet (Humphreys, GSM 94,
§7.8 (check)), with `T_μ^λ = pr_{χ_λ}(pr_{χ_μ}(−) ⊗ L(ν)^*)` the adjoint of
`T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν))`. -/
theorem translation_translation_verma_of_sameFacet {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hfacet' : ∀ i, (μ + P.rho) (P.coroot i) = 0 → (lam + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    Nonempty (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (Module.Dual K (IrreducibleModule P ν)) (centralCharacter P μ)
        (centralCharacter P lam) (centralTranslation P (IrreducibleModule P ν)
          (centralCharacter P lam) (centralCharacter P μ)
          (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam)))) := by
  have h := exists_translation_verma_back P hA hlam hμ hfacet' hν hz hzν w
  obtain ⟨ν', h⟩ := h
  obtain ⟨z', h⟩ := h
  obtain ⟨hz', h⟩ := h
  have eν := h.2.2.1.some
  have eV := h.2.2.2.some
  have e₁ := (translation_verma_equiv P hA hlam hμ hfacet hν hz hzν w).some
  have E₂ := centralTranslationCoeffEquiv P (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ))
    (centralCharacter P μ) (centralCharacter P lam) eν.symm
  have E₃ := centralTranslationEquiv P (Module.Dual K (IrreducibleModule P ν))
    (centralCharacter P μ) (centralCharacter P lam) e₁
  have E := (eV.trans E₂).trans E₃
  exact ⟨E⟩

include hA in
/-- **`T_μ^λ T_λ^μ L(w·λ) ≅ L(w·λ)`** when `λ` and `μ` lie in the same facet (Humphreys, GSM 94,
§7.8 and Theorem 7.9 (check)). -/
theorem translation_translation_irreducible_of_sameFacet {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hfacet' : ∀ i, (μ + P.rho) (P.coroot i) = 0 → (lam + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    Nonempty (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (Module.Dual K (IrreducibleModule P ν)) (centralCharacter P μ)
        (centralCharacter P lam) (centralTranslation P (IrreducibleModule P ν)
          (centralCharacter P lam) (centralCharacter P μ)
          (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam)))) := by
  have h := exists_translation_verma_back P hA hlam hμ hfacet' hν hz hzν w
  obtain ⟨ν', h⟩ := h
  obtain ⟨z', h⟩ := h
  obtain ⟨hz', h⟩ := h
  have eν := h.2.2.1.some
  have e₁ := (translation_irreducible_of_sameFacet P hA hlam hμ hfacet hfacet' hν hz hzν w).some
  have e₂ := (translation_irreducible_of_sameFacet P hA hμ hlam hfacet' hfacet h.1 hz' h.2.1
    w).some
  have E₂ := centralTranslationCoeffEquiv P
    (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ))
    (centralCharacter P μ) (centralCharacter P lam) eν.symm
  have E₃ := centralTranslationEquiv P (Module.Dual K (IrreducibleModule P ν))
    (centralCharacter P μ) (centralCharacter P lam) e₁
  have E := (e₂.trans E₂).trans E₃
  exact ⟨E⟩

end SameFacet

end Matrix.Realization.KacMoodyAlgebra
