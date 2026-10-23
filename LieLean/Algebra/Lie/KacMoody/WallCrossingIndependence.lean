/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.ProjectiveFunctorIso
import LieLean.Algebra.Lie.KacMoody.CategoryOTranslation
import LieLean.Algebra.Lie.KacMoody.ProjectiveCharacter
import LieLean.Algebra.Lie.KacMoody.TranslationFacetClosureNonintegral
import LieLean.Algebra.Lie.KacMoody.TranslationSameFacet
import LieLean.Algebra.Lie.KacMoody.TranslationProjectiveLongest

/-!
# The composite `T_μ^λ T_λ^μ` depends only on the stabilizer of `μ`

Let `λ` be antidominant and `μ`, `μ'` antidominant weights in the closure of the facet of `λ`
with the same stabilizer under the dot action, for instance two weights on the wall of a simple
reflection `s` and on no other wall, as in the definition of the wall-crossing functor
`Θ_s = T_μ^λ T_λ^μ` (Humphreys, §7.15). Then `T_μ^λ T_λ^μ ≅ T_{μ'}^λ T_λ^{μ'}` on the block of `λ`
(Humphreys, §10.8, the independence of `Θ_s` from `μ`), assuming Duflo's theorem and Kostant's
multiplicity formula at the dominant weight of the block, the inputs of Theorem 10.7
(`exists_bijOn_translationIdem`).

Both composites are summands of tensoring functors. At the dominant Verma module `M(λ♮)` of the
block both values are projective with the same character (Theorem 7.6 and Theorem 7.12), hence
isomorphic (Corollary 3.10), and Theorem 10.7 extends the isomorphism to the block.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.translationIdemRangeEquiv`: the image of
  `translationIdem` is the composite `pr_{χ₂}(pr_{χ₁}(M ⊗ L) ⊗ L')`.
* `Matrix.Realization.exists_isDominant_weylDot`: every block contains a dominant weight.
* `Matrix.Realization.KacMoodyAlgebra.nonempty_equiv_translation_translation_verma`: the two
  composites agree on the dominant Verma module of the block.
* `Matrix.Realization.KacMoodyAlgebra.exists_bijOn_translationIdem_of_stabilizer`: the two
  composites are isomorphic on the block, by one natural transformation.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §7.15, §10.8.
-/

noncomputable section

open Module UniversalEnvelopingAlgebra
open scoped TensorProduct

namespace Matrix.Realization

section Dominant

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (hF : A.IsFiniteCartan)

include hF in
/-- Every integral dot orbit `W_[λ]·λ` contains a dominant weight (Humphreys, GSM 94, §3.5, the
statement dual to Prop. 3.5 (b)): apply `exists_isAntidominant_weylDot` to `-λ - 2ρ`. -/
theorem exists_isDominant_weylDot (lam : Dual K H) :
    ∃ w ∈ P.integralWeylGroup hF.isGeneralizedCartan lam,
      P.IsDominant hF.isGeneralizedCartan
        (P.weylDot hF.isGeneralizedCartan w lam) := by
  obtain ⟨w, hw, hanti⟩ := P.exists_isAntidominant_weylDot hF (-(lam + P.rho) - P.rho)
  have hW : P.integralWeylGroup hF.isGeneralizedCartan (-(lam + P.rho) - P.rho) =
      P.integralWeylGroup hF.isGeneralizedCartan lam := by
    rw [P.integralWeylGroup_eq_of_integral hF.isGeneralizedCartan
      (μ' := -(lam + P.rho)) fun j ↦ ⟨-1, by simp⟩, integralWeylGroup_neg,
      ← P.integralWeylGroup_eq_of_integral hF.isGeneralizedCartan (μ := lam) fun j ↦ ⟨-1, by simp⟩]
  refine ⟨w, hW ▸ hw, fun v i hv n hn ↦ ?_⟩
  have h2 := hanti v i hv (-n) (by
    rw [sub_add_cancel, sub_add_cancel, map_neg, corootPairing_neg, ← weylDot_add_rho, hn]
    push_cast; ring)
  omega

end Dominant

namespace KacMoodyAlgebra

section Comparison

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {L L' : Type*} [AddCommGroup L] [Module K L] [LieRingModule P.KacMoodyAlgebra L]
  [LieModule K P.KacMoodyAlgebra L] [AddCommGroup L'] [Module K L']
  [LieRingModule P.KacMoodyAlgebra L'] [LieModule K P.KacMoodyAlgebra L']
  {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M]

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

/-- The inclusion of `pr_{χ₂}(pr_{χ₁}(M ⊗ L) ⊗ L')` into `M ⊗ (L ⊗ L')`. -/
def translationIncl (χ₁ χ₂ : 𝓩 →ₐ[K] K) :
    centralTranslation P L' χ₁ χ₂ (M ⊗[K] L) →ₗ⁅K,𝔤⁆ M ⊗[K] (L ⊗[K] L') :=
  (LieModuleEquiv.tensorAssoc K 𝔤 M L L' : (M ⊗[K] L) ⊗[K] L' →ₗ⁅K,𝔤⁆ _).comp
    ((TensorProduct.LieModule.map (centralBlock P (M ⊗[K] L) χ₁).incl
      (LieModuleHom.id : L' →ₗ⁅K,𝔤⁆ L')).comp
      (centralTranslation P L' χ₁ χ₂ (M ⊗[K] L)).incl)

omit [CharZero K] [IsAlgClosed K] in
theorem translationIncl_injective (χ₁ χ₂ : 𝓩 →ₐ[K] K) :
    Function.Injective (translationIncl P (L := L) (L' := L') (M := M) χ₁ χ₂) := by
  intro y y' h
  apply Subtype.val_injective
  refine Module.Flat.rTensor_preserves_injective_linearMap (M := L')
    ((centralBlock P (M ⊗[K] L) χ₁).incl : _ →ₗ[K] M ⊗[K] L) Subtype.val_injective ?_
  exact (LieModuleEquiv.tensorAssoc K 𝔤 M L L').injective h

theorem range_translationIdem (hL : IsCategoryO P L) (hL' : IsCategoryO P L')
    (χ₁ χ₂ : 𝓩 →ₐ[K] K) (hM : IsCategoryO P M) :
    (translationIdem P hL hL' χ₁ χ₂ M hM).range =
      (translationIncl P (L := L) (L' := L') (M := M) χ₁ χ₂).range := by
  set hML := hM.tensorProduct hL
  set hMLL := hML.tensorProduct hL'
  set B := centralBlock P (M ⊗[K] L) χ₁
  have hB : IsCategoryO P B := hML.centralBlock P χ₁
  have hBL := hB.tensorProduct hL'
  set j := TensorProduct.LieModule.map B.incl (LieModuleHom.id : L' →ₗ⁅K,𝔤⁆ L')
  set p₁ := TensorProduct.LieModule.map (hML.centralBlockProjection P χ₁)
    (LieModuleHom.id : L' →ₗ⁅K,𝔤⁆ L')
  set p₂ := hMLL.centralBlockProjection P χ₂
  have hj₁ : ∀ t, p₁ (j t) = j t := by
    intro t
    induction t with
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul b l =>
      change hML.centralBlockProjection P χ₁ (b : M ⊗[K] L) ⊗ₜ l = (b : M ⊗[K] L) ⊗ₜ l
      exact congrArg (· ⊗ₜ l) (centralBlockProjection_self P _ χ₁ b.property)
  have hj₂ : ∀ t, p₂ (j t) = j (hBL.centralBlockProjection P χ₂ t) := fun t ↦
    (DFunLike.congr_fun (IsCategoryO.centralBlockProjection_natural P hBL hMLL j χ₂) t).symm
  have hp₁ : ∀ u, ∃ t, p₁ u = j t := by
    intro u
    induction u with
    | add a b ha hb =>
      obtain ⟨t, ht⟩ := ha
      obtain ⟨t', ht'⟩ := hb
      exact ⟨t + t', by rw [map_add, map_add, ht, ht']⟩
    | tmul m l =>
      exact ⟨(⟨hML.centralBlockProjection P χ₁ m, centralBlockProjection_mem P _ χ₁ m⟩ : B) ⊗ₜ l,
        rfl⟩
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨t, ht⟩ := hp₁ ((LieModuleEquiv.tensorAssoc K 𝔤 M L L').symm x)
    refine ⟨⟨hBL.centralBlockProjection P χ₂ t, centralBlockProjection_mem P _ χ₂ t⟩, ?_⟩
    change LieModuleEquiv.tensorAssoc K 𝔤 M L L' (j _) =
      LieModuleEquiv.tensorAssoc K 𝔤 M L L' (p₂ (p₁ _))
    erw [ht, hj₂]
    rfl
  · rintro _ ⟨y, rfl⟩
    refine ⟨translationIncl P χ₁ χ₂ y, ?_⟩
    change LieModuleEquiv.tensorAssoc K 𝔤 M L L' (p₂ (p₁
      ((LieModuleEquiv.tensorAssoc K 𝔤 M L L').symm
        (LieModuleEquiv.tensorAssoc K 𝔤 M L L' (j y))))) =
      LieModuleEquiv.tensorAssoc K 𝔤 M L L' (j y)
    rw [LieModuleEquiv.symm_apply_apply, hj₁, hj₂,
      show hBL.centralBlockProjection P χ₂ y = y from centralBlockProjection_self P _ χ₂ y.property]

/-- The image of `translationIdem` is the composite of translation functors
`pr_{χ₂}(pr_{χ₁}(M ⊗ L) ⊗ L')`. -/
def translationIdemRangeEquiv (hL : IsCategoryO P L) (hL' : IsCategoryO P L')
    (χ₁ χ₂ : 𝓩 →ₐ[K] K) (hM : IsCategoryO P M) :
    centralTranslation P L' χ₁ χ₂ (M ⊗[K] L) ≃ₗ⁅K,𝔤⁆
      (translationIdem P hL hL' χ₁ χ₂ M hM).range :=
  LieModuleEquiv.ofBijective (LieModuleHom.codRestrict (translationIdem P hL hL' χ₁ χ₂ M hM).range
      (translationIncl P χ₁ χ₂) fun y ↦ by
        rw [range_translationIdem]; exact ⟨y, rfl⟩)
    ⟨fun y y' h ↦ translationIncl_injective P χ₁ χ₂ (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      rw [range_translationIdem] at hx
      obtain ⟨y, rfl⟩ := hx
      exact ⟨y, rfl⟩⟩

/-- For `M` in the block `χ`, the composite `pr_{χ₂}(pr_{χ₁}(pr_χ M ⊗ L) ⊗ L')` of two translation
functors is `pr_{χ₂}(pr_{χ₁}(M ⊗ L) ⊗ L')`. -/
def translationTranslationEquiv {χ : 𝓩 →ₐ[K] K} (h : centralBlock P M χ = ⊤)
    (χ₁ χ₂ : 𝓩 →ₐ[K] K) :
    centralTranslation P L' χ₁ χ₂ (centralTranslation P L χ χ₁ M) ≃ₗ⁅K,𝔤⁆
      centralTranslation P L' χ₁ χ₂ (M ⊗[K] L) :=
  (centralTranslationEquiv P L' χ₁ χ₂
    (centralBlockEquiv P (rTensorEquiv P L (equivCentralBlockOfEqTop P h)) χ₁)).trans
    (centralBlockEquiv P (rTensorEquiv P L'
      (equivCentralBlockOfEqTop P (centralBlock_centralBlock_eq_top P χ₁))) χ₂)

end Comparison

section Independence

universe u₁ u₂

open VermaModule

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

include hA in
/-- Translation by a finite-dimensional simple module preserves projectives of `𝒪`. -/
theorem isProjectiveO_centralTranslation {V : Type (max u₁ u₂)} [AddCommGroup V] [Module K V]
    [LieRingModule 𝔤 V] [LieModule K 𝔤 V] (hV : IsCategoryO P V)
    (hVp : IsProjectiveO.{max u₁ u₂} P V) {ν : Dual K H} (hν : P.IsDominantIntegral ν)
    (χ₁ χ₂ : 𝓩 →ₐ[K] K) :
    IsProjectiveO.{max u₁ u₂} P (centralTranslation P (IrreducibleModule P ν) χ₁ χ₂ V) := by
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  obtain ⟨z', -, -, ⟨eν⟩⟩ := IrreducibleModule.exists_equiv_dual P hA hν
  have hL'O : IsCategoryO P (Module.Dual K (IrreducibleModule P ν)) :=
    IsCategoryO.of_equiv (IrreducibleModule.isCategoryO P _) eν.symm
  exact isProjectiveO_centralBlock P
    (hV := (hV.centralBlock P χ₁).tensorProduct (IrreducibleModule.isCategoryO P ν))
    ((isProjectiveO_centralBlock P (hV := hV) hVp χ₁).tensorProduct P hL'O) χ₂

include hA in
/-- The character of `T_μ^λ T_λ^μ M(w·λ)` for antidominant `λ, μ` with `μ♮` in the closure of the
facet of `λ♮` (Humphreys, GSM 94, Thm. 7.6 and Thm. 7.12): with `T_λ^μ` and `T_μ^λ` given by
`L(ν)`, `ν ∈ W(μ - λ)`, and `L(ν')`, `ν' ∈ W(λ - μ)`, it is `∑ ch M((w w')·λ)` over the cosets
of the stabilizer of `μ`. -/
theorem character_translation_translation_verma {lam μ ν ν' : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (hν' : P.IsDominantIntegral ν') {z' : Dual K H ≃ₗ[K] Dual K H}
    (hz' : z' ∈ P.weylGroup hA.isGeneralizedCartan) (hzν' : z' (lam - μ) = ν')
    (w : P.weylGroup hA.isGeneralizedCartan) :
    ∃ T : Finset (Dual K H), (T : Set (Dual K H)) = {y | ∃ w' : P.weylGroup hA.isGeneralizedCartan,
        P.weylDot hA.isGeneralizedCartan w' μ = μ ∧
          y = P.weylDot hA.isGeneralizedCartan (w * w') lam} ∧
      (((VermaModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan w lam)).centralTranslation P
        (IrreducibleModule.isCategoryO P ν) (centralCharacter P lam) (centralCharacter P μ)
        ).centralTranslation P (IrreducibleModule.isCategoryO P ν') (centralCharacter P μ)
          (centralCharacter P lam)).character =
        ∑ y ∈ T, (VermaModule.isCategoryO P y).character := by
  have hA' := hA.isGeneralizedCartan
  have e := (translation_verma_equiv_of_isAntidominant P hA hlam hμ hfacet hν hz hzν w).some
  have hMχ : centralBlock P (VermaModule P (P.weylDot hA' w μ)) (centralCharacter P μ) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' w.property μ) ▸ centralBlock_verma P _
  have hc := character_translation_verma_of_isAntidominant (P := P) hA hlam hμ hν' hz' hzν' w
  refine ⟨hc.choose, hc.choose_spec.1, ?_⟩
  refine (IsCategoryO.character_congr _ _
    ((centralTranslationEquiv P (IrreducibleModule P ν') (centralCharacter P μ)
      (centralCharacter P lam) e).symm.trans
      (centralBlockEquiv P (rTensorEquiv P (IrreducibleModule P ν')
        (equivCentralBlockOfEqTop P hMχ)) (centralCharacter P lam)))).trans hc.choose_spec.2

/-- Two elements equal to the values of one function at equal arguments are equal. -/
private theorem eq_of_eq_of_eq_of_eq {α β : Type*} {f : α → β} {a b : β} {T T' : α}
    (ha : a = f T) (hb : b = f T') (h : T = T') : a = b := by
  subst h
  exact ha.trans hb.symm

include hA in
/-- **`T_μ^λ T_λ^μ` at the dominant Verma module of the block** (Humphreys, GSM 94, §10.8):
for antidominant `λ` and antidominant `μ`, `μ'` in the closure of the facet of `λ` with the same
stabilizer under the dot action, `T_μ^λ T_λ^μ M(w·λ) ≅ T_{μ'}^λ T_λ^{μ'} M(w·λ)` when `w·λ` is
dominant: both are projective (Prop. 3.8 and Prop. 7.2) with the same character (Thm. 7.6 and
Thm. 7.12), hence isomorphic (Cor. 3.10). -/
theorem nonempty_equiv_translation_translation_verma {lam μ μ' ν ν' η η' : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hμ' : P.IsAntidominant hA.isGeneralizedCartan μ')
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hfacet' : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ' + P.rho) v i = 0)
    (hstab : ∀ w' : P.weylGroup hA.isGeneralizedCartan,
      P.weylDot hA.isGeneralizedCartan w' μ = μ ↔ P.weylDot hA.isGeneralizedCartan w' μ' = μ')
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (hν' : P.IsDominantIntegral ν') {z' : Dual K H ≃ₗ[K] Dual K H}
    (hz' : z' ∈ P.weylGroup hA.isGeneralizedCartan) (hzν' : z' (lam - μ) = ν')
    (hη : P.IsDominantIntegral η) {y : Dual K H ≃ₗ[K] Dual K H}
    (hy : y ∈ P.weylGroup hA.isGeneralizedCartan) (hyη : y (μ' - lam) = η)
    (hη' : P.IsDominantIntegral η') {y' : Dual K H ≃ₗ[K] Dual K H}
    (hy' : y' ∈ P.weylGroup hA.isGeneralizedCartan) (hyη' : y' (lam - μ') = η')
    {w : P.weylGroup hA.isGeneralizedCartan}
    (hdom : P.IsDominant hA.isGeneralizedCartan (P.weylDot hA.isGeneralizedCartan w lam)) :
    Nonempty (centralTranslation P (IrreducibleModule P ν') (centralCharacter P μ)
        (centralCharacter P lam) (centralTranslation P (IrreducibleModule P ν)
          (centralCharacter P lam) (centralCharacter P μ)
          (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam))) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (IrreducibleModule P η') (centralCharacter P μ')
        (centralCharacter P lam) (centralTranslation P (IrreducibleModule P η)
          (centralCharacter P lam) (centralCharacter P μ')
          (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam)))) := by
  classical
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν'
  have := IrreducibleModule.finiteDimensional (P := P) hA hη
  have := IrreducibleModule.finiteDimensional (P := P) hA hη'
  have hV := VermaModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan w lam)
  have hVp : IsProjectiveO.{max u₁ u₂} P (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam)) :=
    VermaModule.isProjectiveO P hA hdom
  have hsV : LieSubmodule.lieSpan K 𝔤
      (({VermaModule.hwv P (P.weylDot hA.isGeneralizedCartan w lam)} : Finset (VermaModule P _)) :
        Set (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam))) = ⊤ := by
    rw [Finset.coe_singleton]
    exact VermaModule.lieSpan_map_hwv_eq_top LieModuleHom.id Function.surjective_id
  have hc := character_translation_translation_verma P hA hlam hμ hfacet hν hz hzν hν' hz' hzν' w
  have hc' := character_translation_translation_verma P hA hlam hμ' hfacet' hη hy hyη hη' hy'
    hyη' w
  have hTT : hc.choose = hc'.choose := by
    have hset : {y | ∃ w' : P.weylGroup hA.isGeneralizedCartan,
          P.weylDot hA.isGeneralizedCartan w' μ = μ ∧
          y = P.weylDot hA.isGeneralizedCartan (w * w') lam} =
        {y | ∃ w' : P.weylGroup hA.isGeneralizedCartan,
          P.weylDot hA.isGeneralizedCartan w' μ' = μ' ∧
          y = P.weylDot hA.isGeneralizedCartan (w * w') lam} := Set.ext fun x ↦
      ⟨fun ⟨w', h, hx⟩ ↦ ⟨w', (hstab w').mp h, hx⟩, fun ⟨w', h, hx⟩ ↦ ⟨w', (hstab w').mpr h, hx⟩⟩
    exact Finset.coe_injective (hc.choose_spec.1.trans (hset.trans hc'.choose_spec.1.symm))
  have hLν := IrreducibleModule.isCategoryO P ν
  have hLν' := IrreducibleModule.isCategoryO P ν'
  have hLη := IrreducibleModule.isCategoryO P η
  have hLη' := IrreducibleModule.isCategoryO P η'
  have hS₁ := exists_finset_lieSpan_centralTranslation_eq_top_of_fg P
    (centralCharacter P lam) (centralCharacter P μ) hV hLν hsV
  have hS₂ := exists_finset_lieSpan_centralTranslation_eq_top_of_fg P
    (centralCharacter P μ) (centralCharacter P lam)
    (hV.centralTranslation P hLν (centralCharacter P lam) (centralCharacter P μ)) hLν'
    hS₁.choose_spec
  have hS₁' := exists_finset_lieSpan_centralTranslation_eq_top_of_fg P
    (centralCharacter P lam) (centralCharacter P μ') hV hLη hsV
  have hS₂' := exists_finset_lieSpan_centralTranslation_eq_top_of_fg P
    (centralCharacter P μ') (centralCharacter P lam)
    (hV.centralTranslation P hLη (centralCharacter P lam) (centralCharacter P μ')) hLη'
    hS₁'.choose_spec
  have hX := (hV.centralTranslation P hLν (centralCharacter P lam) (centralCharacter P μ)
    ).centralTranslation P hLν' (centralCharacter P μ) (centralCharacter P lam)
  have hX' := (hV.centralTranslation P hLη (centralCharacter P lam) (centralCharacter P μ')
    ).centralTranslation P hLη' (centralCharacter P μ') (centralCharacter P lam)
  have h1 : hX.character = ∑ y ∈ hc.choose, (VermaModule.isCategoryO P y).character :=
    hc.choose_spec.2
  have h2 : hX'.character = ∑ y ∈ hc'.choose, (VermaModule.isCategoryO P y).character :=
    hc'.choose_spec.2
  have hP := isProjectiveO_centralTranslation P hA
      (hV.centralTranslation P hLν (centralCharacter P lam) (centralCharacter P μ))
      (isProjectiveO_centralTranslation P hA hV hVp hν (centralCharacter P lam)
        (centralCharacter P μ)) hν' (centralCharacter P μ)
        (centralCharacter P lam)
  have hP' := isProjectiveO_centralTranslation P hA
      (hV.centralTranslation P hLη (centralCharacter P lam) (centralCharacter P μ'))
      (isProjectiveO_centralTranslation P hA hV hVp hη (centralCharacter P lam)
        (centralCharacter P μ')) hη' (centralCharacter P μ')
        (centralCharacter P lam)
  have hch : hX.character = hX'.character :=
    eq_of_eq_of_eq_of_eq (f := fun T ↦ ∑ y ∈ T, (VermaModule.isCategoryO P y).character) h1 h2
      hTT
  have key := IsProjectiveO.nonempty_equiv_of_character_eq P hA hP hX hS₂.choose_spec hP' hX'
    hS₂'.choose_spec hch
  exact key

include hA in
/-- **Independence of `T_μ^λ T_λ^μ` from `μ`** (Humphreys, GSM 94, §7.15, by §10.8): for
antidominant `λ` and antidominant `μ`, `μ'` in the closure of the facet of `λ` with the same
stabilizer under the dot action, one natural transformation `− ⊗ (L(ν) ⊗ L(ν')) →
− ⊗ (L(η) ⊗ L(η'))` induces, after the central projections, a bijection
`T_μ^λ T_λ^μ M → T_{μ'}^λ T_λ^{μ'} M` for every finitely generated `M ∈ 𝒪` in the block of `λ`.
The two functors are written as `pr_λ(pr_μ(M ⊗ L(ν)) ⊗ L(ν'))` (`translationIdem`), which is
`T_μ^λ T_λ^μ M` for `M` in the block of `λ` (`translationTranslationEquiv`).

Here `w·λ` is the dominant weight of the block. Duflo's theorem and Kostant's theorem enter as
hypotheses at `M(w·λ)`: `I` is the annihilator of `M(w·λ)` (`hM₀`, `hI`) and `U(𝔤)/I` has
Kostant's multiplicities (`hK`); see `exists_tensorNatTrans_app_verma`. -/
theorem exists_bijOn_translationIdem_of_stabilizer {lam μ μ' ν ν' η η' : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hμ' : P.IsAntidominant hA.isGeneralizedCartan μ')
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hfacet' : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ' + P.rho) v i = 0)
    (hstab : ∀ w' : P.weylGroup hA.isGeneralizedCartan,
      P.weylDot hA.isGeneralizedCartan w' μ = μ ↔ P.weylDot hA.isGeneralizedCartan w' μ' = μ')
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (hν' : P.IsDominantIntegral ν') {z' : Dual K H ≃ₗ[K] Dual K H}
    (hz' : z' ∈ P.weylGroup hA.isGeneralizedCartan) (hzν' : z' (lam - μ) = ν')
    (hη : P.IsDominantIntegral η) {y : Dual K H ≃ₗ[K] Dual K H}
    (hy : y ∈ P.weylGroup hA.isGeneralizedCartan) (hyη : y (μ' - lam) = η)
    (hη' : P.IsDominantIntegral η') {y' : Dual K H ≃ₗ[K] Dual K H}
    (hy' : y' ∈ P.weylGroup hA.isGeneralizedCartan) (hyη' : y' (lam - μ') = η')
    {w : P.weylGroup hA.isGeneralizedCartan}
    (hw : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    (hdom : P.IsDominant hA.isGeneralizedCartan (P.weylDot hA.isGeneralizedCartan w lam))
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)}
    (hM₀ : IsKilledBy I (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam)))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤)
      (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam)) a = 0 → a ∈ I)
    (hK : KostantMultiplicity P (AdQuotient K 𝔤 I)) :
    ∃ φ : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤
        (IrreducibleModule P ν ⊗[K] IrreducibleModule P ν')
        (IrreducibleModule P η ⊗[K] IrreducibleModule P η'),
      ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
        [LieModule K 𝔤 M] (hM : IsCategoryO P M) (s : Finset M),
        LieSubmodule.lieSpan K 𝔤 (s : Set M) = ⊤ →
        (∀ ξ, hM.multiplicity ξ ≠ 0 → ∃ x ∈ P.integralWeylGroup hA.isGeneralizedCartan lam,
          ξ = P.weylDot hA.isGeneralizedCartan x lam) →
        Set.BijOn (fun x ↦ translationIdem P (IrreducibleModule.isCategoryO P η)
            (IrreducibleModule.isCategoryO P η') (centralCharacter P μ') (centralCharacter P lam)
            M hM (φ.app M x))
          (Set.range (translationIdem P (IrreducibleModule.isCategoryO P ν)
            (IrreducibleModule.isCategoryO P ν') (centralCharacter P μ) (centralCharacter P lam)
            M hM))
          (Set.range (translationIdem P (IrreducibleModule.isCategoryO P η)
            (IrreducibleModule.isCategoryO P η') (centralCharacter P μ') (centralCharacter P lam)
            M hM)) := by
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν'
  have := IrreducibleModule.finiteDimensional (P := P) hA hη
  have := IrreducibleModule.finiteDimensional (P := P) hA hη'
  have hV := VermaModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan w lam)
  have htop : centralBlock P (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam))
      (centralCharacter P lam) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA.isGeneralizedCartan w.property lam) ▸
      centralBlock_verma P _
  have e₀ := (nonempty_equiv_translation_translation_verma P hA hlam hμ hμ' hfacet hfacet' hstab
    hν hz hzν hν' hz' hzν' hη hy hyη hη' hy' hyη' hdom).some
  have hLν := IrreducibleModule.isCategoryO P ν
  have hLν' := IrreducibleModule.isCategoryO P ν'
  have hLη := IrreducibleModule.isCategoryO P η
  have hLη' := IrreducibleModule.isCategoryO P η'
  have E : (translationIdem P hLν hLν' (centralCharacter P μ) (centralCharacter P lam) _ hV).range
      ≃ₗ⁅K,𝔤⁆
      (translationIdem P hLη hLη' (centralCharacter P μ') (centralCharacter P lam) _ hV).range :=
    (((translationIdemRangeEquiv P hLν hLν' (centralCharacter P μ) (centralCharacter P lam)
      hV).symm.trans (translationTranslationEquiv P (L := IrreducibleModule P ν)
        (L' := IrreducibleModule P ν') htop (centralCharacter P μ)
        (centralCharacter P lam)).symm).trans e₀).trans
      ((translationTranslationEquiv P (L := IrreducibleModule P η)
        (L' := IrreducibleModule P η') htop (centralCharacter P μ')
        (centralCharacter P lam)).trans
        (translationIdemRangeEquiv P hLη hLη' (centralCharacter P μ') (centralCharacter P lam)
          hV))
  have h0 := exists_bijOn_translationIdem P hA hdom hM₀ hI hK hLν hLν' hLη hLη'
    (centralCharacter P μ) (centralCharacter P lam) (centralCharacter P μ')
    (centralCharacter P lam) hV
  obtain ⟨φ, hφ⟩ := h0 E
  refine ⟨φ, fun M _ _ _ _ hM s hs hblock ↦ hφ M hM s hs fun ξ hξ ↦ ?_⟩
  obtain ⟨x, hx, rfl⟩ := hblock ξ hξ
  have hint : ∀ j, ∃ k : ℤ, (P.weylDot hA.isGeneralizedCartan w lam - lam) (P.coroot j) = k :=
    P.exists_int_of_mem_rootLattice ((P.mem_integralWeylGroup_iff_dot _).mp hw)
  refine ⟨x * w⁻¹, ?_, ?_⟩
  · rw [P.integralWeylGroup_eq_of_integral _ hint]
    exact mul_mem hx (inv_mem hw)
  · rw [← weylDot_mul, mul_assoc, inv_mul_cancel, mul_one]

end Independence

end KacMoodyAlgebra

end Matrix.Realization
