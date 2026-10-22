/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOProjDimensionEq
import LieLean.Algebra.Lie.KacMoody.CategoryOStdFilteredCriterion
import LieLean.Algebra.Lie.KacMoody.SelfDualProjective
import LieLean.Algebra.Lie.KacMoody.TranslationShuffling

/-!
# Projective dimensions of simple modules in `𝒪`: Prop. 6.9 (b)

For `𝔤` of finite type over an algebraically closed field of characteristic zero and `Λ`
dominant integral, `CategoryOProjDimension.lean` gives `pd L(w·Λ) ≤ 2ℓ(w₀) - ℓ(w)`. This file
proves equality for every `w ∈ W`, so the block of `Λ` has global dimension `2ℓ(w₀)`.

## Main results

* `CategoryO.projectiveDimension_simple_weylDot`: [HumO] Prop. 6.9 (b),
  `pd L(w·Λ) = 2ℓ(w₀) - ℓ(w)`.
* `CategoryO.projectiveDimension_simple`: the case `w = 1`, `pd L(Λ) = 2ℓ(w₀)`.

## Proof

The lower bound is a nonzero class in `Ext^{2ℓ(w₀) - ℓ(w)}(L(w·Λ), L(Λ))`, built by descending
induction on `ℓ(w)`. For `w = w₀` the module `L(w₀·Λ) = M(w₀·Λ)` is a Verma module and
Prop. 6.9 (a) applies. For the step, let `u > u sᵢ` with a nonzero class in
`Extⁿ(L(u·Λ), L(Λ))`, and let `Θ = T' T` be wall-crossing through the wall of `sᵢ`. Since
`T L(u·Λ) ≠ 0`, the adjunction morphism `L(u·Λ) → Θ L(u·Λ)` is injective; let `Q` be its
cokernel. As `T L(Λ) = 0`, `Ext(Θ L(u·Λ), L(Λ)) = 0`, so the long exact sequence gives a nonzero
class in `Extⁿ⁺¹(Q, L(Λ))`. The composition factors of `Q` are factors of `Θ M(u·Λ)`, an
extension of `M(u·Λ)` by `M(u sᵢ·Λ)`, so each is `L(z·Λ)` with `z = u sᵢ` or `ℓ(z) ≥ ℓ(u)`; the
upper bound kills `Extⁿ⁺¹(L(z·Λ), L(Λ))` for the latter, which leaves a nonzero class in
`Extⁿ⁺¹(L(u sᵢ·Λ), L(Λ))`.

Humphreys indicates a proof through twisting functors (or Kazhdan–Lusztig theory); the
wall-crossing argument above is reconstructed and needs neither.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, §6.9.
-/
noncomputable section

universe u

open Module

namespace Matrix.Realization.KacMoodyAlgebra

namespace CategoryO

open CategoryTheory VermaModule

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
/-- A nonzero morphism out of an irreducible module is injective. -/
theorem injective_of_isIrreducible_of_ne_zero {M N : Type*} [AddCommGroup M] [Module K M]
    [LieRingModule 𝔤 M] [LieModule K 𝔤 M] [AddCommGroup N] [Module K N] [LieRingModule 𝔤 N]
    [LieModule K 𝔤 N] [LieModule.IsIrreducible K 𝔤 M] (f : M →ₗ⁅K,𝔤⁆ N) (hf : f ≠ 0) :
    Function.Injective f := by
  rcases IsSimpleOrder.eq_bot_or_eq_top f.ker with h' | h'
  · exact (LieModuleHom.ker_eq_bot f).mp h'
  · exact (hf (LieModuleHom.ext fun a ↦
      (LieModuleHom.mem_ker).mp (h' ▸ LieSubmodule.mem_top a))).elim

omit [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
/-- Multiplicities do not increase along surjections. -/
theorem multiplicity_le_of_surjective {X Y : CategoryO.{u} P} (φ : X.obj →ₗ⁅K,𝔤⁆ Y.obj)
    (hφ : Function.Surjective φ) (ν : Dual K H) :
    Y.property.1.multiplicity ν ≤ X.property.1.multiplicity ν := by
  have := IsCategoryO.multiplicity_eq_add_of_exact (X.property.1.lieSubmodule φ.ker)
    X.property.1 Y.property.1 φ.ker.incl φ Subtype.val_injective φ.ker.range_incl.symm hφ ν
  omega

omit [IsAlgClosed K] in
/-- The object of `𝒪` underlying a translation is the translated module. -/
def translationObjEquiv (L : Type u) [AddCommGroup L] [Module K L]
    [LieRingModule 𝔤 L] [LieModule K 𝔤 L] [FiniteDimensional K L]
    (χ₁ χ₂ : Subalgebra.center K (UniversalEnvelopingAlgebra K 𝔤) →ₐ[K] K)
    (X : CategoryO.{u} P) :
    centralTranslation P L χ₁ χ₂ X.obj ≃ₗ⁅K,𝔤⁆ ((translationFunctor L χ₁ χ₂).obj X).obj :=
  ofLieEquiv (P := P) _

/-- Translation functors preserve surjections. -/
theorem surjective_translationFunctor_map (L : Type u) [AddCommGroup L] [Module K L]
    [LieRingModule 𝔤 L] [LieModule K 𝔤 L] [FiniteDimensional K L]
    (χ₁ χ₂ : Subalgebra.center K (UniversalEnvelopingAlgebra K 𝔤) →ₐ[K] K)
    {X Y : CategoryO.{u} P} (f : X ⟶ Y) (hf : Function.Surjective f.hom.hom) :
    Function.Surjective ((translationFunctor L χ₁ χ₂).map f).hom.hom :=
  (ofLieEquiv (P := P) (centralTranslation P L χ₁ χ₂ Y.obj)).surjective.comp
    ((centralTranslationMap_surjective P X.property.1
    (isCategoryO_of_finiteDimensional' L) χ₁ χ₂ (toLieModuleHom f.hom) hf).comp
      (ofLieEquiv (P := P) (centralTranslation P L χ₁ χ₂ X.obj)).symm.surjective)

/-- The adjunction morphism `X → T'(T X)` for an irreducible `X` with `T X ≠ 0`, where `T'` is
translation by a module `L'` isomorphic to the dual of the coefficient module `L` of `T`, is
injective. -/
theorem exists_injective_translation_translation (L L' : Type u) [AddCommGroup L] [Module K L]
    [LieRingModule 𝔤 L] [LieModule K 𝔤 L] [FiniteDimensional K L] [AddCommGroup L']
    [Module K L'] [LieRingModule 𝔤 L'] [LieModule K 𝔤 L'] [FiniteDimensional K L']
    (eD : Module.Dual K L ≃ₗ⁅K,𝔤⁆ L')
    (χ₁ χ₂ : Subalgebra.center K (UniversalEnvelopingAlgebra K 𝔤) →ₐ[K] K)
    (X : CategoryO.{u} P) {M : Type u} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M] [LieModule.IsIrreducible K 𝔤 M] (e : X.obj ≃ₗ⁅K,𝔤⁆ M)
    (hM : IsCategoryO P M) (hX : centralBlock P M χ₁ = ⊤)
    [Nontrivial (centralTranslation P L χ₁ χ₂ M)] :
    ∃ φ : X.obj →ₗ⁅K,𝔤⁆
        ((translationFunctor L' χ₂ χ₁).obj ((translationFunctor L χ₁ χ₂).obj X)).obj,
      Function.Injective φ := by
  let N := centralTranslation P L χ₁ χ₂ M
  have adj := translationAdjunction P hM (isCategoryO_of_finiteDimensional' L) hX
    (centralBlock_centralTranslation_eq_top P (L := L) (M := M) χ₁ χ₂)
  let η₀ := adj (LieModuleHom.id : N →ₗ⁅K,𝔤⁆ N)
  have hη₀ : η₀ ≠ 0 := by
    intro h0
    have h0' : (LieModuleHom.id : N →ₗ⁅K,𝔤⁆ N) = 0 := (LinearEquiv.map_eq_zero_iff adj).mp h0
    obtain ⟨b, hb⟩ := exists_ne (0 : N)
    exact hb (LieModuleHom.congr_fun h0' b)
  let E := ((centralTranslationCoeffEquiv P N χ₂ χ₁ eD).trans
    (centralTranslationEquiv P L' χ₂ χ₁ ((centralTranslationEquiv P L χ₁ χ₂ e.symm).trans
      (translationObjEquiv L χ₁ χ₂ X)))).trans
    (translationObjEquiv L' χ₂ χ₁ ((translationFunctor L χ₁ χ₂).obj X))
  exact ⟨E.toLieModuleHom.comp (η₀.comp e.toLieModuleHom),
    E.injective.comp ((injective_of_isIrreducible_of_ne_zero η₀ hη₀).comp e.injective)⟩

/-- For an injection `φ : X → Y` with `Extⁿ(Y, T) = 0`, a nonzero class in `Extⁿ(X, T)` gives
a nonzero class in `Extⁿ⁺¹(W, T)` for the cokernel `W`, whose multiplicities are bounded by those
of `Y`. -/
theorem exists_ext_quotient_ne_zero {X Y : CategoryO.{u} P} (φ : X.obj →ₗ⁅K,𝔤⁆ Y.obj)
    (hφ : Function.Injective φ) {T : CategoryO.{u} P} {n : ℕ}
    (hY : ∀ x : Abelian.Ext.{u} Y T n, x = 0) (hX : ∃ x : Abelian.Ext.{u} X T n, x ≠ 0) :
    ∃ W : CategoryO.{u} P, (∀ κ, W.property.1.multiplicity κ ≤ Y.property.1.multiplicity κ) ∧
      ∃ x : Abelian.Ext.{u} W T (n + 1), x ≠ 0 := by
  obtain ⟨x₁, hx₁⟩ := hX
  let F : X ⟶ Y := (IsObj.{u} P).homMk (ofLieModuleHom φ)
  let G : Y ⟶ ofQuotient Y φ.range :=
    (IsObj.{u} P).homMk (ofLieModuleHom (toQuotient Y φ.range))
  have hFG : F ≫ G = 0 := by
    ext a
    exact (toQuotient_eq_zero_iff Y φ.range _).mpr ⟨a, rfl⟩
  let S := ShortComplex.mk F G hFG
  have hS : S.ShortExact := shortExact_of_lie (fun a b hab ↦ hφ hab)
    (fun b ↦ surjective_toQuotient Y φ.range b)
    (fun b hb ↦ (LieModuleHom.mem_range φ b).mp ((toQuotient_eq_zero_iff Y φ.range b).mp hb))
  exact ⟨ofQuotient Y φ.range, fun κ ↦ multiplicity_le_of_surjective (toQuotient Y φ.range)
    (surjective_toQuotient _ _) κ, _, Abelian.Ext.extClass_comp_ne_zero hS hY hx₁⟩

theorem _root_.Nat.ne_zero_or_ne_zero_of_le_add {a b c : ℕ} (ha : a ≠ 0) (h : a ≤ b + c) :
    b ≠ 0 ∨ c ≠ 0 := by
  omega

variable (hA : A.IsFiniteCartan) {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)

include hΛ in
/-- With `λ = y·Λ` regular antidominant and `μ` on the wall of `y αᵢ`, the wall-crossing functor
kills `Ext(−, L(Λ))`: `Extⁿ(T' X, L(Λ)) ≅ Extⁿ(X, T L(Λ))` and `T L(Λ) = 0`. -/
theorem ext_translation_wall_simple_eq_zero {y : P.weylGroup hA.isGeneralizedCartan}
    (hy : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      ¬P.IsPosRoot hA.isGeneralizedCartan (y * v) i) (i : ι)
    [FiniteDimensional K (IrreducibleModule P (Λ + P.rho - P.wallWeight i))]
    (X : CategoryO.{u} P) (n : ℕ)
    (x : Abelian.Ext.{u} ((translationFunctor (IrreducibleModule P (Λ + P.rho - P.wallWeight i))
      (centralCharacter P ((y : Dual K H ≃ₗ[K] Dual K H) (P.wallWeight i) - P.rho))
      (centralCharacter P (P.weylDot hA.isGeneralizedCartan y Λ))).obj X) (simple P Λ) n) :
    x = 0 := by
  have hA' := hA.isGeneralizedCartan
  let s := (P.coxeterSystem hA').simple i
  let lam := P.weylDot hA' y Λ
  let μ := (y : Dual K H ≃ₗ[K] Dual K H) (P.wallWeight i) - P.rho
  let ν := Λ + P.rho - P.wallWeight i
  let v₀ := y * s
  have hlam := isAntidominant_weylDot hA hy hΛ
  have hμ := isAntidominant_wall hA hy i
  have hfacet : ∀ v j, P.IsPosRoot hA' v j → P.corootPairing hA' (lam + P.rho) v j = 0 →
      P.corootPairing hA' (μ + P.rho) v j = 0 := fun v j hv h0 ↦ by
    obtain ⟨m, hm⟩ := exists_corootPairing_weylDot_eq_neg hA hy hΛ hv
    rw [hm] at h0
    exact (Nat.cast_add_one_ne_zero m (neg_eq_zero.mp h0)).elim
  have hν := isDominantIntegral_sub_wallWeight hΛ i
  have hzν : ((y⁻¹ : P.weylGroup hA') : Dual K H ≃ₗ[K] Dual K H) (lam - μ) = ν :=
    inv_apply_weylDot_sub_wall (hF := hA) (y := y) i
  have hμα := corootPairing_wall_mul_simple (hF := hA) (y := y) i
  obtain ⟨m, hm⟩ := hΛ i
  let chiL := centralCharacter P lam
  let chiM := centralCharacter P μ
  obtain ⟨z'', hz'', hdom, ⟨eD⟩⟩ := IrreducibleModule.exists_equiv_dual (P := P) hA hν
  have hint : ∀ j, ∃ z : ℤ, lam (P.coroot j) = z := fun j ↦ by
    obtain ⟨k, hk⟩ := exists_corootPairing_weylDot_eq_neg hA hy hΛ (isPosRoot_one hA' j)
    rw [corootPairing_one, LinearMap.add_apply, rho_coroot] at hk
    exact ⟨-(k + 2 : ℤ), by push_cast; linear_combination hk⟩
  have hsimp : (⟨P.reflection hA' i, P.reflection_mem_weylGroup hA' i⟩ :
      P.weylGroup hA') = s := Subtype.ext (coxeterSystem_simple P hA' i).symm
  have hC : ¬P.UpperClosureCondition hA'
      (((y⁻¹ : P.weylGroup hA') : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho))
      (((y⁻¹ : P.weylGroup hA') : Dual K H ≃ₗ[K] Dual K H) (μ + P.rho)) := by
    have key := not_upperClosureCondition_of_wall (P := P) hA (a := lam + P.rho) (b := μ + P.rho)
      (v := v₀) (w := s * y⁻¹) (i := i) hμα (n := -((m : ℤ) + 1)) (by omega) (by
        rw [corootPairing_weylDot_mul_simple (hF := hA) (y := y) (Λ := Λ) i, hm]; push_cast; ring)
      (by
        rw [show s * y⁻¹ * v₀ = 1 by simp [v₀, s, mul_assoc]]
        exact isPosRoot_one hA' i)
    rwa [show s * y⁻¹ * P.reflectionOf hA' v₀ i = y⁻¹ by
      simp [reflectionOf, hsimp, v₀, s, mul_assoc]] at key
  have hsub := translation_irreducible_of_not_upperClosureCondition_of_isAntidominant P hA
    hlam hμ hfacet hdom (z := z'' * ((y⁻¹ : P.weylGroup hA') : Dual K H ≃ₗ[K] Dual K H))
    (mul_mem hz'' (y⁻¹).2) (by
      rw [LinearEquiv.mul_apply, show μ - lam = -(lam - μ) by abel, map_neg, hzν])
    y⁻¹ (by rw [P.integralWeylGroup_eq_top hA' hint]; trivial) hC
  have hΛ' : P.weylDot hA' y⁻¹ lam = Λ := by
    rw [← weylDot_mul, inv_mul_cancel, weylDot_one]
  rw [hΛ'] at hsub
  let T' := (translationFunctor (Module.Dual K (IrreducibleModule P ν)) chiL chiM).obj
    (simple P Λ)
  have : Subsingleton T'.obj := (((ofLieEquiv (P := P) _).symm.trans
    ((centralTranslationEquiv P _ chiL chiM
      (ofLieEquiv (P := P) (IrreducibleModule P Λ)).symm).trans
      (centralTranslationCoeffEquiv P (IrreducibleModule P Λ) chiL chiM eD))).toEquiv
    ).subsingleton
  have hz := Abelian.Ext.eq_zero_of_isZero_right (isZero_of_subsingleton T')
    (extTranslationEquiv (IrreducibleModule P ν) chiM chiL X (simple P Λ) n x)
  exact (LinearEquiv.map_eq_zero_iff _).mp hz

include hΛ in
/-- If the composition factors of `W` are among those of `M(u sᵢ·Λ)` and `M(u·Λ)`, and
`Extⁿ⁺¹(L(z·Λ), L(Λ)) = 0` for `z = u sᵢ` and for `ℓ(z) ≥ ℓ(u)`, then `Extⁿ⁺¹(W, L(Λ)) = 0`. -/
theorem ext_eq_zero_of_multiplicity_le_verma {u v : P.weylGroup hA.isGeneralizedCartan}
    (hlen : (P.coxeterSystem hA.isGeneralizedCartan).length v + 1 =
      (P.coxeterSystem hA.isGeneralizedCartan).length u) {n : ℕ}
    (hvan : ∀ z : P.weylGroup hA.isGeneralizedCartan,
      (P.coxeterSystem hA.isGeneralizedCartan).length u ≤
        (P.coxeterSystem hA.isGeneralizedCartan).length z → ∀ Z : CategoryO.{u} P,
      (Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P (P.weylDot hA.isGeneralizedCartan z Λ)) →
      ∀ x : Abelian.Ext.{u} Z (simple P Λ) (n + 1), x = 0)
    (hv : ∀ x : Abelian.Ext.{u} (simple P (P.weylDot hA.isGeneralizedCartan v Λ)) (simple P Λ)
      (n + 1), x = 0)
    (W : CategoryO.{u} P)
    (hW : ∀ κ, W.property.1.multiplicity κ ≤
      (VermaModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan v Λ)).multiplicity κ +
        (VermaModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan u Λ)).multiplicity κ)
    (x : Abelian.Ext.{u} W (simple P Λ) (n + 1)) : x = 0 := by
  refine ext_eq_zero_of_multiplicity_left W _ (n + 1) (fun κ hκ Z eZ e₀ ↦ ?_) x
  rcases Nat.ne_zero_or_ne_zero_of_le_add hκ (hW κ) with hk | hk
  · obtain ⟨z, hz, rfl⟩ := IsStronglyLinked.exists_bruhatLE_weylDot P hA hΛ
      (VermaModule.isStronglyLinked_of_multiplicity_ne_zero P hA hk)
    rcases hz.eq_or_length_lt with rfl | hlt
    · exact ext_eq_zero_of_equiv_left ((ofLieEquiv (P := P) _).symm.trans eZ.symm) hv e₀
    · exact hvan z (hlen.symm.trans_le hlt) Z eZ e₀
  · obtain ⟨z, hz, rfl⟩ := IsStronglyLinked.exists_bruhatLE_weylDot P hA hΛ
      (VermaModule.isStronglyLinked_of_multiplicity_ne_zero P hA hk)
    rcases hz.eq_or_length_lt with rfl | hlt
    · exact hvan u le_rfl Z eZ e₀
    · exact hvan z hlt.le Z eZ e₀

include hΛ in
/-- The step of [HumO] Prop. 6.9 (b): for `ℓ(u sᵢ) < ℓ(u)`, a nonzero class in
`Extⁿ(L(u·Λ), L(Λ))` gives a nonzero class in `Extⁿ⁺¹(L(u sᵢ·Λ), L(Λ))`, provided
`Extⁿ⁺¹(L(z·Λ), L(Λ)) = 0` whenever `ℓ(z) ≥ ℓ(u)`. The adjunction morphism
`L(u·Λ) → Θ L(u·Λ)` is injective, and `Extⁿ(Θ L(u·Λ), L(Λ)) = 0`; the composition factors of the
cokernel `Q` are factors of `Θ M(u·Λ)`, an extension of `M(u·Λ)` by `M(u sᵢ·Λ)`, so each is
`L(z·Λ)` with `z = u sᵢ` or `ℓ(z) ≥ ℓ(u)`. -/
theorem exists_ext_simple_ne_zero_succ (i : ι) {u : P.weylGroup hA.isGeneralizedCartan}
    (hu : P.IsPosRoot hA.isGeneralizedCartan
      (u * (P.coxeterSystem hA.isGeneralizedCartan).simple i) i) {n : ℕ}
    (hvan : ∀ z : P.weylGroup hA.isGeneralizedCartan,
      (P.coxeterSystem hA.isGeneralizedCartan).length u ≤
        (P.coxeterSystem hA.isGeneralizedCartan).length z → ∀ Z : CategoryO.{u} P,
      (Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P (P.weylDot hA.isGeneralizedCartan z Λ)) →
      ∀ x : Abelian.Ext.{u} Z (simple P Λ) (n + 1), x = 0)
    (h : ∃ x : Abelian.Ext.{u} (simple P (P.weylDot hA.isGeneralizedCartan u Λ)) (simple P Λ) n,
      x ≠ 0) :
    ∃ x : Abelian.Ext.{u} (simple P (P.weylDot hA.isGeneralizedCartan
      (u * (P.coxeterSystem hA.isGeneralizedCartan).simple i) Λ)) (simple P Λ) (n + 1),
      x ≠ 0 := by
  have hA' := hA.isGeneralizedCartan
  have hlen : (P.coxeterSystem hA').length (u * (P.coxeterSystem hA').simple i) + 1 =
      (P.coxeterSystem hA').length u := by
    have hnd := hu
    rw [isPosRoot_iff_not_isRightDescent, (P.coxeterSystem hA').isRightDescent_iff,
      (P.coxeterSystem hA').simple_mul_simple_cancel_right] at hnd
    rcases (P.coxeterSystem hA').length_mul_simple u i with h' | h' <;> omega
  obtain ⟨y, hy⟩ := exists_forall_not_isPosRoot_mul (P := P) hA
  let s := (P.coxeterSystem hA').simple i
  let lam := P.weylDot hA' y Λ
  let μ := (y : Dual K H ≃ₗ[K] Dual K H) (P.wallWeight i) - P.rho
  let ν := Λ + P.rho - P.wallWeight i
  let ν' := μ - lam
  let v₀ := y * s
  let w := u * y⁻¹
  have hlen' : (P.coxeterSystem hA').length (u * s) + 1 = (P.coxeterSystem hA').length u := hlen
  have hlam := isAntidominant_weylDot hA hy hΛ
  have hμ := isAntidominant_wall hA hy i
  have hfacet : ∀ v j, P.IsPosRoot hA' v j → P.corootPairing hA' (lam + P.rho) v j = 0 →
      P.corootPairing hA' (μ + P.rho) v j = 0 := fun v j hv h0 ↦ by
    obtain ⟨m, hm⟩ := exists_corootPairing_weylDot_eq_neg hA hy hΛ hv
    rw [hm] at h0
    exact (Nat.cast_add_one_ne_zero m (neg_eq_zero.mp h0)).elim
  have hν := isDominantIntegral_sub_wallWeight hΛ i
  have hν' := isDominantIntegral_wall_sub_weylDot hA hy hΛ i
  have hzν : ((y⁻¹ : P.weylGroup hA') : Dual K H ≃ₗ[K] Dual K H) (lam - μ) = ν :=
    inv_apply_weylDot_sub_wall (hF := hA) (y := y) i
  have hv₀ : P.IsPosRoot hA' v₀ i := isPosRoot_mul_simple hA hy i
  have hμα := corootPairing_wall_mul_simple (hF := hA) (y := y) i
  have hwall := fun v' i' (h0 : P.corootPairing hA' (μ + P.rho) v' i' = 0) ↦
    apply_root_eq_or_of_corootPairing_wall hA i h0
  obtain ⟨m, hm⟩ := hΛ i
  have hlamα : P.corootPairing hA' (lam + P.rho) v₀ i ≠ 0 := by
    rw [corootPairing_weylDot_mul_simple (hF := hA) (y := y) (Λ := Λ) i, hm]
    intro h0
    exact Nat.cast_add_one_ne_zero m (neg_eq_zero.mp h0)
  have hw : P.IsPosRoot hA' (w * v₀) i := by
    rwa [show w * v₀ = u * s by simp only [w, v₀]; group]
  have hint : ∀ j, ∃ z : ℤ, lam (P.coroot j) = z := fun j ↦ by
    obtain ⟨k, hk⟩ := exists_corootPairing_weylDot_eq_neg hA hy hΛ (isPosRoot_one hA' j)
    rw [corootPairing_one, LinearMap.add_apply, rho_coroot] at hk
    exact ⟨-(k + 2 : ℤ), by push_cast; linear_combination hk⟩
  have hwint : w ∈ P.integralWeylGroup hA' lam := by
    rw [P.integralWeylGroup_eq_top hA' hint]; trivial
  let chiL := centralCharacter P lam
  let chiM := centralCharacter P μ
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν'
  have h1 : P.weylDot hA' (w * P.reflectionOf hA' v₀ i) lam = P.weylDot hA' (u * s) Λ := by
    have hsimp : (⟨P.reflection hA' i, P.reflection_mem_weylGroup hA' i⟩ :
        P.weylGroup hA') = s := Subtype.ext (coxeterSystem_simple P hA' i).symm
    rw [← weylDot_mul]
    congr 1
    simp [reflectionOf, hsimp, w, v₀, s, mul_assoc]
  have h3 : P.weylDot hA' w lam = P.weylDot hA' u Λ := by
    rw [← weylDot_mul]
    simp [w]
  let x₀ := P.weylDot hA' w lam
  -- the wall-crossing sequence `0 → M(u sᵢ·Λ) → Θ M(u·Λ) → M(u·Λ) → 0`
  let Xv := (translationFunctor (IrreducibleModule P ν') chiL chiM).obj (verma P x₀)
  let eXv : Xv.obj ≃ₗ⁅K,𝔤⁆ centralTranslation P (IrreducibleModule P ν') chiL chiM
      (VermaModule P x₀) :=
    (ofLieEquiv (P := P) (centralTranslation P (IrreducibleModule P ν') chiL chiM
      (verma P x₀).obj)).symm.trans
      (centralTranslationEquiv P (IrreducibleModule P ν') chiL chiM
        (ofLieEquiv (P := P) (VermaModule P x₀)).symm)
  obtain ⟨f, g, hf, hg, hfg⟩ := wallCrossing_verma_shortExact P hA hlam hμ hfacet hν
    (y⁻¹).2 hzν hν' (1 : P.weylGroup hA').2 rfl hv₀ hμα hwall hlamα hw eXv
  let Θv := (translationFunctor (IrreducibleModule P ν) chiM chiL).obj Xv
  let CTv := centralTranslation P (IrreducibleModule P ν) chiM chiL Xv.obj
  have hexact : LieModuleHom.ker (g.comp (ofLieEquiv (P := P) CTv).symm.toLieModuleHom) =
      LieModuleHom.range ((ofLieEquiv (P := P) CTv).toLieModuleHom.comp f) :=
    LieSubmodule.ext _ _ fun b ↦ (hfg _).trans
      (exists_congr fun a ↦ (ofLieEquiv (P := P) CTv).toEquiv.eq_symm_apply)
  have hmultv₀ : ∀ κ, Θv.property.1.multiplicity κ =
      (VermaModule.isCategoryO P (P.weylDot hA' (w * P.reflectionOf hA' v₀ i) lam)).multiplicity κ +
        (VermaModule.isCategoryO P x₀).multiplicity κ := fun κ ↦
    IsCategoryO.multiplicity_eq_add_of_exact (VermaModule.isCategoryO P _) Θv.property.1
      (VermaModule.isCategoryO P _) ((ofLieEquiv (P := P) CTv).toLieModuleHom.comp f)
      (g.comp (ofLieEquiv (P := P) CTv).symm.toLieModuleHom)
      ((ofLieEquiv (P := P) CTv).injective.comp hf) hexact
      (hg.comp (ofLieEquiv (P := P) CTv).symm.surjective) κ
  have hmultv : ∀ κ, Θv.property.1.multiplicity κ =
      (VermaModule.isCategoryO P (P.weylDot hA' (u * s) Λ)).multiplicity κ +
        (VermaModule.isCategoryO P (P.weylDot hA' u Λ)).multiplicity κ := by
    have hv : ∀ a b, a = b → ∀ κ, (VermaModule.isCategoryO P a).multiplicity κ =
        (VermaModule.isCategoryO P b).multiplicity κ := by
      rintro a b rfl κ; rfl
    exact fun κ ↦ (hmultv₀ κ).trans (congrArg₂ (· + ·) (hv _ _ h1 κ) (hv _ _ h3 κ))
  -- `Θ L(u·Λ)` is a quotient of `Θ M(u·Λ)`
  let π : verma P x₀ ⟶ simple P x₀ := (IsObj.{u} P).homMk (ofLieModuleHom
    (toSimple P x₀ (simple P x₀) (ofLieEquiv (P := P) (IrreducibleModule P x₀)).symm))
  have hπ : Function.Surjective π.hom.hom := fun z ↦
    surjective_toSimple x₀ (simple P x₀) (ofLieEquiv (P := P) (IrreducibleModule P x₀)).symm z
  let Xo := (translationFunctor (IrreducibleModule P ν') chiL chiM).obj (simple P x₀)
  let Θo := (translationFunctor (IrreducibleModule P ν) chiM chiL).obj Xo
  have hmultΘ : ∀ κ, Θo.property.1.multiplicity κ ≤ Θv.property.1.multiplicity κ :=
    multiplicity_le_of_surjective (toLieModuleHom ((translationFunctor (IrreducibleModule P ν)
      chiM chiL).map ((translationFunctor (IrreducibleModule P ν') chiL chiM).map π)).hom)
      (surjective_translationFunctor_map _ _ _ _
        (surjective_translationFunctor_map _ _ _ _ hπ))
  -- the adjunction morphism `η : L(u·Λ) → Θ L(u·Λ)`
  have hMχ : centralBlock P (IrreducibleModule P (P.weylDot hA' w lam))
      (centralCharacter P lam) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' w.property lam) ▸ centralBlock_irreducible P _
  obtain ⟨eW⟩ := (translation_irreducible_wall P hA hlam hμ hfacet hν' (1 : P.weylGroup hA').2
    rfl hv₀ hμα hwall hlamα hw hwint w).1 rfl
  have := IrreducibleModule.isIrreducible P (P.weylDot hA' w μ)
  have : Nontrivial (centralTranslation P (IrreducibleModule P ν') chiL chiM
      (IrreducibleModule P x₀)) := eW.symm.toEquiv.nontrivial
  have := IrreducibleModule.isIrreducible P x₀
  obtain ⟨z₁, hz₁, hdom₁, ⟨eD⟩⟩ := IrreducibleModule.exists_equiv_dual (P := P) hA hν'
  have hyν : (y : Dual K H ≃ₗ[K] Dual K H) ν = -ν' := by
    rw [← hzν, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
    change lam - μ = -(μ - lam)
    abel
  have hz₁ν : z₁ (-ν') = ν := by
    rw [← hyν, ← LinearEquiv.mul_apply]
    exact P.apply_eq_self_of_dominant hA' hν (mul_mem hz₁ y.2)
      (by rwa [LinearEquiv.mul_apply, hyν])
  rw [hz₁ν] at eD
  obtain ⟨φ, hφ⟩ := exists_injective_translation_translation (IrreducibleModule P ν')
    (IrreducibleModule P ν) eD chiL chiM (simple P x₀)
    (ofLieEquiv (P := P) (IrreducibleModule P x₀)).symm (IrreducibleModule.isCategoryO P x₀) hMχ
  have h₂ : ∀ x : Abelian.Ext.{u} Θo (simple P Λ) n, x = 0 :=
    fun x ↦ ext_translation_wall_simple_eq_zero hA hΛ hy i Xo n x
  obtain ⟨x₁, hx₁⟩ : ∃ x : Abelian.Ext.{u} (simple P (P.weylDot hA' w lam)) (simple P Λ) n,
      x ≠ 0 := by
    rw [h3]; exact h
  -- `0 → L(u·Λ) → Θ L(u·Λ) → Q → 0`
  obtain ⟨W, hW, xq, hne⟩ := exists_ext_quotient_ne_zero φ hφ h₂ ⟨x₁, hx₁⟩
  by_contra hcon
  push Not at hcon
  refine hne (ext_eq_zero_of_multiplicity_le_verma hA hΛ hlen' hvan hcon W (fun κ ↦ ?_) _)
  have hle₁ : W.property.1.multiplicity κ ≤ Θo.property.1.multiplicity κ := hW κ
  have hle₂ : Θo.property.1.multiplicity κ ≤ Θv.property.1.multiplicity κ := hmultΘ κ
  have hle₃ := (hmultv κ).le
  have hle₄ := hle₂.trans hle₃
  exact hle₁.trans hle₄

include hΛ in
/-- **[HumO] Proposition 6.9 (b), lower bound**: `Ext^{2m - ℓ(w)}(L(w·Λ), L(Λ)) ≠ 0` for `Λ`
dominant integral, `w ∈ W` and `m = ℓ(w₀)`. Descending induction on `ℓ(w)`, starting from
`L(w₀·Λ) = M(w₀·Λ)`. -/
theorem exists_ext_simple_weylDot_ne_zero : ∀ (d : ℕ) (w : P.weylGroup hA.isGeneralizedCartan),
    (P.coxeterSystem hA.isGeneralizedCartan).length
        (P.coxeterSystem hA.isGeneralizedCartan).longestElement -
      (P.coxeterSystem hA.isGeneralizedCartan).length w = d →
    ∃ x : Abelian.Ext.{u} (simple P (P.weylDot hA.isGeneralizedCartan w Λ)) (simple P Λ)
      (2 * (P.coxeterSystem hA.isGeneralizedCartan).length
          (P.coxeterSystem hA.isGeneralizedCartan).longestElement -
        (P.coxeterSystem hA.isGeneralizedCartan).length w), x ≠ 0 := by
  have hA' := hA.isGeneralizedCartan
  intro d
  induction d with
  | zero =>
    intro w hw
    have hwm := (P.coxeterSystem hA').length_le_length_longestElement w
    obtain ⟨y, hy⟩ := exists_forall_not_isPosRoot_mul (P := P) hA
    have hyw : y = w := by
      have hy₀ : y = (P.coxeterSystem hA').longestElement :=
        (P.coxeterSystem hA').eq_longestElement_iff_forall_isRightDescent.mpr fun j ↦ by
          have := hy 1 j (isPosRoot_one hA' j)
          rwa [mul_one, isPosRoot_iff_not_isRightDescent, not_not] at this
      have hw₀ : w = (P.coxeterSystem hA').longestElement :=
        (P.coxeterSystem hA').eq_longestElement_of_forall_length_le fun v ↦ by
          have := (P.coxeterSystem hA').length_le_length_longestElement v
          omega
      rw [hy₀, hw₀]
    subst hyw
    obtain ⟨x, hx⟩ := exists_ext_verma_weylDot_simple_ne_zero hA hΛ _ y rfl
    obtain ⟨e⟩ := VermaModule.nonempty_equiv_irreducible_of_isAntidominant P hA
      (isAntidominant_weylDot hA hy hΛ)
    rw [show 2 * (P.coxeterSystem hA').length (P.coxeterSystem hA').longestElement -
      (P.coxeterSystem hA').length y = (P.coxeterSystem hA').length y by omega]
    by_contra hcon
    push Not at hcon
    exact hx (ext_eq_zero_of_equiv_left ((ofLieEquiv (P := P) _).symm.trans
      (e.symm.trans (ofLieEquiv (P := P) _))) hcon x)
  | succ d ih =>
    intro w hw
    have hwm := (P.coxeterSystem hA').length_le_length_longestElement w
    obtain ⟨i, hi⟩ : ∃ i, ¬(P.coxeterSystem hA').IsRightDescent w i := by
      by_contra hc
      push Not at hc
      rw [(P.coxeterSystem hA').eq_longestElement_iff_forall_isRightDescent.mpr hc] at hw
      omega
    have hl : (P.coxeterSystem hA').length (w * (P.coxeterSystem hA').simple i) =
        (P.coxeterSystem hA').length w + 1 := by
      rw [(P.coxeterSystem hA').isRightDescent_iff] at hi
      rcases (P.coxeterSystem hA').length_mul_simple w i with h' | h' <;> omega
    have hum := (P.coxeterSystem hA').length_le_length_longestElement
      (w * (P.coxeterSystem hA').simple i)
    obtain ⟨x, hx⟩ := ih (w * (P.coxeterSystem hA').simple i) (by omega)
    have hws : w * (P.coxeterSystem hA').simple i * (P.coxeterSystem hA').simple i = w :=
      (P.coxeterSystem hA').simple_mul_simple_cancel_right i
    have hu : P.IsPosRoot hA' (w * (P.coxeterSystem hA').simple i *
        (P.coxeterSystem hA').simple i) i := by
      rwa [hws, isPosRoot_iff_not_isRightDescent]
    have key := exists_ext_simple_ne_zero_succ hA hΛ i hu (fun z hz Z e x ↦
      ext_simple_weylDot_eq_zero hA hΛ _ z rfl Z e _ (by
        have := (P.coxeterSystem hA').length_le_length_longestElement z
        omega) (simple P Λ) x) ⟨x, hx⟩
    rw [hws] at key
    rwa [show 2 * (P.coxeterSystem hA').length (P.coxeterSystem hA').longestElement -
      (P.coxeterSystem hA').length w = 2 * (P.coxeterSystem hA').length
        (P.coxeterSystem hA').longestElement - (P.coxeterSystem hA').length
          (w * (P.coxeterSystem hA').simple i) + 1 by omega]

include hΛ in
/-- **[HumO] Proposition 6.9 (b)**: `pd L(w·Λ) = 2m - ℓ(w)` for `Λ` dominant integral, `w ∈ W`
and `m = ℓ(w₀)`. -/
theorem projectiveDimension_simple_weylDot (w : P.weylGroup hA.isGeneralizedCartan) :
    projectiveDimension (simple.{u} P (P.weylDot hA.isGeneralizedCartan w Λ)) =
      ((2 * (P.coxeterSystem hA.isGeneralizedCartan).length
          (P.coxeterSystem hA.isGeneralizedCartan).longestElement -
        (P.coxeterSystem hA.isGeneralizedCartan).length w : ℕ) : WithBot ℕ∞) := by
  refine le_antisymm ?_ ?_
  · exact (projectiveDimension_le_iff _ _).mpr (hasProjectiveDimensionLT_simple_weylDot hA hΛ w)
  · rw [projectiveDimension_ge_iff]
    intro h
    obtain ⟨x, hx⟩ := exists_ext_simple_weylDot_ne_zero hA hΛ _ w rfl
    exact hx (x.eq_zero_of_hasProjectiveDimensionLT _ le_rfl)

include hΛ in
/-- `pd L(Λ) = 2ℓ(w₀)` for `Λ` dominant integral: the case `w = 1` of
`projectiveDimension_simple_weylDot`. With `pd M(w·Λ) = ℓ(w)` and `pd L(w·Λ) ≤ 2ℓ(w₀)`, the
block of `Λ` has global dimension `2ℓ(w₀)` ([HumO] §6.9). -/
theorem projectiveDimension_simple :
    projectiveDimension (simple.{u} P Λ) =
      ((2 * (P.coxeterSystem hA.isGeneralizedCartan).length
        (P.coxeterSystem hA.isGeneralizedCartan).longestElement : ℕ) : WithBot ℕ∞) := by
  have h := projectiveDimension_simple_weylDot hA hΛ 1
  rwa [weylDot_one, (P.coxeterSystem _).length_one, Nat.sub_zero] at h

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
