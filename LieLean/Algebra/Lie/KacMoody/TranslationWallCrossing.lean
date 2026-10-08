/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationWallHead

/-!
# Wall-crossing functors

Let `A` be of finite type, `λ`, `μ` antidominant with every positive root orthogonal to `λ + ρ`
orthogonal to `μ + ρ`, `±α` (`α = v αᵢ > 0`) the only roots orthogonal to `μ + ρ` and
`⟨λ + ρ, α^∨⟩ ≠ 0`, and `s = s_α`. With `T_μ^λ = pr_{χ_λ}(pr_{χ_μ}(−) ⊗ L(ν))` and
`T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν'))` (`ν`, `ν'` dominant integral in `W (λ - μ)`,
`W (μ - λ)`), the **wall-crossing functor** is `Θ_s = T_μ^λ T_λ^μ` (Humphreys, GSM 94, §7.15).
The composite is not packaged as a functor here: the statements are about `T_μ^λ X` for a
module `X ≅ T_λ^μ V`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.wallCrossing_verma_shortExact`: for `w α > 0`, `Θ_s M(w·λ)`
  is an extension `0 → M(ws·λ) → Θ_s M(w·λ) → M(w·λ) → 0` (Humphreys, GSM 94, §7.16, step (3),
  from Theorems 7.6 and 7.14 (a)).
* `Matrix.Realization.KacMoodyAlgebra.wallCrossing_irreducible_of_isPosRoot`: for `w α > 0`,
  `Θ_s L(w·λ) ≅ T_μ^λ L(w·μ)`, the module of Theorem 7.14 (b)–(g) (§7.15).
* `Matrix.Realization.KacMoodyAlgebra.wallCrossing_irreducible_of_not_isPosRoot`: for `w ∈ W_[λ]`
  with `w α < 0`, `Θ_s L(w·λ) = 0` (Theorem 7.9).

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.15–7.16.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Generic

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V Y Z W : Type*}
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup Y] [Module K Y] [LieRingModule P.KacMoodyAlgebra Y]
  [LieModule K P.KacMoodyAlgebra Y]
  [AddCommGroup Z] [Module K Z] [LieRingModule P.KacMoodyAlgebra Z]
  [LieModule K P.KacMoodyAlgebra Z]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

omit [LieModule K P.KacMoodyAlgebra Y] in
/-- A submodule `S ≤ T` with `S ≅ U` and `T/S ≅ U'`, transported along `Y ≅ T`, gives a short
exact sequence `0 → U → Y → U' → 0` of morphisms. -/
theorem exists_shortExact_of_lieSubmodule {U U' : Type*} [AddCommGroup U] [Module K U]
    [LieRingModule P.KacMoodyAlgebra U] [LieModule K P.KacMoodyAlgebra U] [AddCommGroup U']
    [Module K U'] [LieRingModule P.KacMoodyAlgebra U'] [LieModule K P.KacMoodyAlgebra U']
    {S T : LieSubmodule K 𝔤 W} (hS : S ≤ T) (eS : U ≃ₗ⁅K,𝔤⁆ S)
    (eQ : U' ≃ₗ⁅K,𝔤⁆ T.map (LieSubmodule.Quotient.mk' S)) (e : Y ≃ₗ⁅K,𝔤⁆ T) :
    ∃ (f : U →ₗ⁅K,𝔤⁆ Y) (g : Y →ₗ⁅K,𝔤⁆ U'), Function.Injective f ∧ Function.Surjective g ∧
      ∀ y, g y = 0 ↔ ∃ u, f u = y := by
  let qT : T →ₗ⁅K,𝔤⁆ T.map (LieSubmodule.Quotient.mk' S) :=
    LieModuleHom.codRestrict _ ((LieSubmodule.Quotient.mk' S).comp T.incl)
      (fun t ↦ (LieSubmodule.mem_map _).mpr ⟨t, t.2, rfl⟩)
  let f : U →ₗ⁅K,𝔤⁆ Y :=
    e.symm.toLieModuleHom.comp ((LieSubmodule.inclusion hS).comp eS.toLieModuleHom)
  let g : Y →ₗ⁅K,𝔤⁆ U' := eQ.symm.toLieModuleHom.comp (qT.comp e.toLieModuleHom)
  refine ⟨f, g, fun u u' huu ↦ ?_, fun u' ↦ ?_, fun y ↦ ⟨fun hy ↦ ?_, ?_⟩⟩
  · have h1 := congrArg e huu
    simp only [f, LieModuleHom.comp_apply, LieModuleEquiv.coe_toLieModuleHom,
      LieModuleEquiv.apply_symm_apply] at h1
    exact eS.injective (LieSubmodule.inclusion_injective hS h1)
  · obtain ⟨t, ht, hte⟩ := (LieSubmodule.mem_map _).mp (eQ u').2
    refine ⟨e.symm ⟨t, ht⟩, ?_⟩
    simp only [g, LieModuleHom.comp_apply, LieModuleEquiv.coe_toLieModuleHom,
      LieModuleEquiv.apply_symm_apply]
    rw [LieModuleEquiv.symm_apply_eq]
    exact Subtype.ext hte
  · have h1 : qT (e y) = 0 := by
      have := congrArg eQ hy
      simp only [g, LieModuleHom.comp_apply, LieModuleEquiv.coe_toLieModuleHom,
        LieModuleEquiv.apply_symm_apply, map_zero] at this
      exact this
    have h2 : (e y).1 ∈ S := (LieSubmodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val h1)
    refine ⟨eS.symm ⟨(e y).1, h2⟩, ?_⟩
    simp only [f, LieModuleHom.comp_apply, LieModuleEquiv.coe_toLieModuleHom,
      LieModuleEquiv.apply_symm_apply]
    exact e.symm_apply_eq.mpr (Subtype.ext rfl)
  · rintro ⟨u, rfl⟩
    have h1 : qT (LieSubmodule.inclusion hS (eS u)) = 0 :=
      Subtype.ext ((LieSubmodule.Quotient.mk_eq_zero _).mpr (eS u).2)
    simp only [g, f, LieModuleHom.comp_apply, LieModuleEquiv.coe_toLieModuleHom,
      LieModuleEquiv.apply_symm_apply, h1, map_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- The tensor product with a zero module is zero. -/
theorem subsingleton_tensorProduct_left [Subsingleton V] : Subsingleton (V ⊗[K] Z) := by
  refine ⟨fun x y ↦ ?_⟩
  have h0 : ∀ t : V ⊗[K] Z, t = 0 := fun t ↦ by
    induction t using TensorProduct.inductionOn with
    | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [h0 x, h0 y]

/-- Translation of a zero module is zero. -/
theorem subsingleton_centralTranslation [Subsingleton V] (χ₁ χ₂ : 𝓩 →ₐ[K] K) :
    Subsingleton (centralTranslation P Z χ₁ χ₂ V) := by
  have : Subsingleton (centralBlock P V χ₁) := inferInstance
  have : Subsingleton (centralBlock P V χ₁ ⊗[K] Z) := subsingleton_tensorProduct_left
  exact inferInstance

end Generic

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- **Wall-crossing on Verma modules** (Humphreys, GSM 94, §7.16, step (3); arbitrary weights).
Under the hypotheses above, for `w ∈ W` with `w α > 0` and `X ≅ T_λ^μ M(w·λ)`, the module
`Θ_s M(w·λ) = T_μ^λ X` is an extension `0 → M(ws·λ) → T_μ^λ X → M(w·λ) → 0`. -/
theorem wallCrossing_verma_shortExact {lam μ ν ν' : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    (hν' : P.IsDominantIntegral ν') {z' : Dual K H ≃ₗ[K] Dual K H}
    (hz' : z' ∈ P.weylGroup hA.isGeneralizedCartan) (hzν' : z' (μ - lam) = ν')
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    {w : P.weylGroup hA.isGeneralizedCartan} (hw : P.IsPosRoot hA.isGeneralizedCartan (w * v) i)
    {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
    [LieModule K P.KacMoodyAlgebra X]
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P (IrreducibleModule P ν') (centralCharacter P lam)
      (centralCharacter P μ) (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam))) :
    ∃ (f : VermaModule P (P.weylDot hA.isGeneralizedCartan
        (w * P.reflectionOf hA.isGeneralizedCartan v i) lam) →ₗ⁅K,𝔤⁆
        centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
          (centralCharacter P lam) X)
      (g : centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
          (centralCharacter P lam) X →ₗ⁅K,𝔤⁆
        VermaModule P (P.weylDot hA.isGeneralizedCartan w lam)),
      Function.Injective f ∧ Function.Surjective g ∧ ∀ y, g y = 0 ↔ ∃ u, f u = y := by
  have hA' := hA.isGeneralizedCartan
  -- `X ≅ M(w·μ)` (Theorem 7.6)
  obtain ⟨e₁⟩ := translation_verma_equiv_of_isAntidominant P hA hlam hμ hfacet hν' hz' hzν' w
  let eXM := eX.trans e₁.symm
  -- `T_μ^λ X ≅ T_μ^λ M(w·μ) ≅ pr_{χ_λ}(M(w·μ) ⊗ L(ν))`
  have hMχ : centralBlock P (VermaModule P (P.weylDot hA' w μ)) (centralCharacter P μ) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' w.property μ) ▸
      centralBlock_verma P (P.weylDot hA' w μ)
  let e := (centralTranslationEquiv P (IrreducibleModule P ν) (centralCharacter P μ)
    (centralCharacter P lam) eXM).trans (centralBlockEquiv P (rTensorEquiv P
      (IrreducibleModule P ν) (equivCentralBlockOfEqTop P hMχ)) (centralCharacter P lam))
  -- Theorem 7.14 (a)
  obtain ⟨S, hS, ⟨eS⟩, ⟨eQ⟩⟩ := translation_verma_shortExact_of_isAntidominant hA hlam hμ hν hz
    hzν hv hμα hwall hlamα hw
  exact exists_shortExact_of_lieSubmodule P hS eS eQ e

include hA in
/-- **Wall-crossing on simple modules, `w α > 0`** (Humphreys, GSM 94, §7.15; arbitrary weights).
For `w ∈ W` with `w α > 0` and `X ≅ T_λ^μ L(w·λ)`: `Θ_s L(w·λ) = T_μ^λ X ≅ T_μ^λ L(w·μ)`, the
module studied in Theorem 7.14. -/
theorem wallCrossing_irreducible_of_isPosRoot {lam μ ν' : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν' : P.IsDominantIntegral ν') {z' : Dual K H ≃ₗ[K] Dual K H}
    (hz' : z' ∈ P.weylGroup hA.isGeneralizedCartan) (hzν' : z' (μ - lam) = ν')
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    {w : P.weylGroup hA.isGeneralizedCartan} (hw : P.IsPosRoot hA.isGeneralizedCartan (w * v) i)
    (hwint : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
    [LieModule K P.KacMoodyAlgebra X]
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P (IrreducibleModule P ν') (centralCharacter P lam)
      (centralCharacter P μ) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam)))
    (ν : Dual K H) :
    Nonempty (centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
        (centralCharacter P lam) X ≃ₗ⁅K,𝔤⁆
      centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
        (centralCharacter P lam) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ))) := by
  obtain ⟨e⟩ := (translation_irreducible_wall P hA hlam hμ hfacet hν' hz' hzν' hv hμα hwall hlamα
    hw hwint w).1 rfl
  exact ⟨centralTranslationEquiv P (IrreducibleModule P ν) _ _ (eX.trans e.symm)⟩

include hA in
/-- **Wall-crossing on simple modules, `w α < 0`** (Humphreys, GSM 94, §7.15 with Theorem 7.9;
arbitrary weights). For `w ∈ W_[λ]` with `w α < 0` and `X ≅ T_λ^μ L(w·λ)`:
`Θ_s L(w·λ) = T_μ^λ X = 0`. -/
theorem wallCrossing_irreducible_of_not_isPosRoot {lam μ ν' : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν' : P.IsDominantIntegral ν') {z' : Dual K H ≃ₗ[K] Dual K H}
    (hz' : z' ∈ P.weylGroup hA.isGeneralizedCartan) (hzν' : z' (μ - lam) = ν')
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    {w : P.weylGroup hA.isGeneralizedCartan} (hw : ¬P.IsPosRoot hA.isGeneralizedCartan (w * v) i)
    (hwint : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
    [LieModule K P.KacMoodyAlgebra X]
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P (IrreducibleModule P ν') (centralCharacter P lam)
      (centralCharacter P μ) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam)))
    (ν : Dual K H) :
    Subsingleton (centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
      (centralCharacter P lam) X) := by
  have hA' := hA.isGeneralizedCartan
  set s := P.reflectionOf hA' v i with hs
  have hint := sub_rho_integral P hA hν' hz' hzν'
  obtain ⟨n, hn⟩ := (P.isIntegralRoot_congr _ hint v i).mpr ⟨0, by rw [Int.cast_zero]; exact hμα⟩
  change P.corootPairing _ (lam + P.rho) v i = n at hn
  have hn0 : n < 0 := lt_of_le_of_ne (hlam v i hv n hn)
    (by rintro rfl; exact hlamα (by simp [hn]))
  -- `w = w' s` with `w' α > 0`
  have hss : s * s = 1 := reflectionOf_mul_self v i
  have hw' : P.IsPosRoot hA' ((w * s) * v) i := by
    have hsv : s * v = v * (P.coxeterSystem hA').simple i := by
      have hsimp : (⟨P.reflection hA' i, P.reflection_mem_weylGroup hA' i⟩ : P.weylGroup hA') =
          (P.coxeterSystem hA').simple i := by
        ext1
        simp
      rw [hs, reflectionOf, ← hsimp]
      group
    rw [mul_assoc, hsv, ← mul_assoc]
    exact (isPosRoot_or (w * v) i).resolve_left hw
  have hww : (w * s) * s = w := by rw [mul_assoc, hss, mul_one]
  have hnotU := not_upperClosureCondition_of_wall hA hμα hn0 hn hw'
  rw [hww] at hnotU
  have hsub := translation_irreducible_of_not_memUpperClosure_of_isAntidominant P hA hlam hμ
    hfacet hν' hz' hzν' w hwint (fun hU ↦ hnotU ((memUpperClosure_weylDot_iff_of_isAntidominant
      hA hlam hμ hint hfacet w).mp hU))
  have : Subsingleton X := @Equiv.subsingleton _ _ eX.toEquiv hsub
  exact subsingleton_centralTranslation P _ _

end Matrix.Realization.KacMoodyAlgebra
