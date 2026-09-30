/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationDuality

/-!
# Translation of simple modules: the dichotomy `T_λ^μ L(w·λ) ∈ {0, L(w·μ)}`

Under the hypotheses of `translation_verma` (integral weights, finite type, algebraically closed
field of characteristic zero), the translation `T_λ^μ L(w·λ)` of a simple module is either zero
or isomorphic to `L(w·μ)` (Humphreys, GSM 94, Theorem 7.9 (check), first assertion).

The argument (Humphreys' proof, reconstructed): `L(x)` is a quotient of `M(x)` and a submodule
of `M(x)^∨`. Since `T_λ^μ` is exact, `T_λ^μ L(w·λ)` is a quotient of `T_λ^μ M(w·λ) ≅ M(w·μ)`
and a submodule of `T_λ^μ M(w·λ)^∨ ≅ M(w·μ)^∨`. Every morphism `M(y) → M(y)^∨` is a scalar
multiple of the Shapovalov map, whose kernel is the maximal submodule; so such a module is `0`
or `L(y)`.

## Main results

* `IrreducibleModule.toRestrictedDual`: the embedding `L(x) ↪ M(x)^∨`.
* `centralTranslationMap_surjective`, `centralTranslationMap_injective`: `T` preserves
  surjections (in `𝒪`) and injections.
* `subsingleton_or_nonempty_equiv_irreducible`: a quotient of `M(y)` embedding in `M(y)^∨` is
  `0` or `≅ L(y)`.
* `translation_irreducible`: `T_λ^μ L(w·λ) = 0` or `T_λ^μ L(w·λ) ≅ L(w·μ)`.

Which alternative occurs (the upper-closure criterion of Humphreys Thm. 7.9) is not formalized.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule TwistedDual

section General

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V W X Z : Type*}
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]
  [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]
  [AddCommGroup Z] [Module K Z] [LieRingModule P.KacMoodyAlgebra Z]
  [LieModule K P.KacMoodyAlgebra Z]

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

omit [LieModule K P.KacMoodyAlgebra X] in
/-- The induced map on a quotient is injective when the kernel is exactly the submodule. -/
lemma quotient_lift_injective (N : LieSubmodule K 𝔤 V) (p : V →ₗ⁅K,𝔤⁆ X) (hN : N ≤ p.ker)
    (hker : ∀ v, p v = 0 → v ∈ N) :
    Function.Injective (LieSubmodule.Quotient.lift N p hN) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨v, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N q
  rw [LieSubmodule.Quotient.lift_mk] at hq
  exact LieSubmodule.Quotient.mk_eq_zero'.mpr (hker v hq)

/-- Translation preserves injections. -/
theorem centralTranslationMap_injective (χ₁ χ₂ : 𝓩 →ₐ[K] K) (f : V →ₗ⁅K,𝔤⁆ W)
    (hf : Function.Injective f) : Function.Injective (centralTranslationMap P Z χ₁ χ₂ f) := by
  have hf₁ := injective_centralBlockMap P f hf χ₁
  let F := TensorProduct.LieModule.map (centralBlockMap P f χ₁) (LieModuleHom.id : Z →ₗ⁅K,𝔤⁆ Z)
  have eF : F.toLinearMap = LinearMap.rTensor Z (centralBlockMap P f χ₁).toLinearMap := by
    rw [TensorProduct.LieModule.toLinearMap_map]
    rfl
  have hF : Function.Injective F := by
    rw [← LieModuleHom.coe_toLinearMap, eF]
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := Z) _ hf₁
  exact injective_centralBlockMap P F hF χ₂

/-- Translation preserves surjections out of modules in `𝒪`, when `Z ∈ 𝒪`. -/
theorem centralTranslationMap_surjective [CharZero K] [IsAlgClosed K] (hV : IsCategoryO P V)
    (hZ : IsCategoryO P Z) (χ₁ χ₂ : 𝓩 →ₐ[K] K) (g : V →ₗ⁅K,𝔤⁆ W)
    (hg : Function.Surjective g) :
    Function.Surjective (centralTranslationMap P Z χ₁ χ₂ g) := by
  have hg₁ := hV.surjective_centralBlockMap P g hg χ₁
  let G := TensorProduct.LieModule.map (centralBlockMap P g χ₁) (LieModuleHom.id : Z →ₗ⁅K,𝔤⁆ Z)
  have eG : G.toLinearMap = LinearMap.rTensor Z (centralBlockMap P g χ₁).toLinearMap := by
    rw [TensorProduct.LieModule.toLinearMap_map]
    rfl
  have hG : Function.Surjective G := by
    rw [← LieModuleHom.coe_toLinearMap, eG]
    exact LinearMap.rTensor_surjective Z hg₁
  exact ((hV.centralBlock P χ₁).tensorProduct hZ).surjective_centralBlockMap P G hG χ₂

end General

section Verma

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]

local notation "𝔤" => KacMoodyAlgebra P

/-- The Shapovalov map `M(x) → M(x)^∨`, `u ↦ B(u, −)`. -/
def VermaModule.toRestrictedDual (x : Dual K H) :
    VermaModule P x →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P x) :=
  (toTwistedDual P x).codRestrict _ fun _ ↦ map_mem_iSup_weightSpaceOfMap P _
    ((VermaModule.isCategoryO P x).iSup_weightSpaceOfMap_eq_top ▸ Submodule.mem_top)

lemma VermaModule.toRestrictedDual_eq_zero_iff (x : Dual K H) (u : VermaModule P x) :
    VermaModule.toRestrictedDual P x u = 0 ↔ u ∈ maxSubmodule P x := by
  rw [mem_maxSubmodule_iff]
  constructor
  · intro h w
    exact congrArg (fun φ : restrictedDual P (VermaModule P x) ↦ TwistedDual.toDual P _ φ.val w) h
  · intro h
    exact restrictedDual_ext P fun w ↦ h w

/-- The embedding `L(x) ↪ M(x)^∨` induced by the Shapovalov form. -/
def IrreducibleModule.toRestrictedDual (x : Dual K H) :
    IrreducibleModule P x →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P x) :=
  LieSubmodule.Quotient.lift (maxSubmodule P x) (VermaModule.toRestrictedDual P x) fun u hu ↦ by
    rw [LieModuleHom.mem_ker]
    exact (VermaModule.toRestrictedDual_eq_zero_iff P x u).mpr hu

lemma IrreducibleModule.toRestrictedDual_injective (x : Dual K H) :
    Function.Injective (IrreducibleModule.toRestrictedDual P x) :=
  quotient_lift_injective P _ _ _ fun u hu ↦ (VermaModule.toRestrictedDual_eq_zero_iff P x u).mp hu

/-- Every morphism `M(y) → M(y)^{*σ}` is a scalar multiple of the Shapovalov map. -/
theorem VermaModule.eq_smul_toTwistedDual (y : Dual K H)
    (φ : VermaModule P y →ₗ⁅K,𝔤⁆ TwistedDual P (VermaModule P y)) :
    φ = TwistedDual.toDual P _ (φ (hwv P y)) (hwv P y) • toTwistedDual P y := by
  set c := TwistedDual.toDual P _ (φ (hwv P y)) (hwv P y)
  apply hom_ext
  change φ (hwv P y) = c • toTwistedDual P y (hwv P y)
  have hφ : φ (hwv P y) ∈ weightSpaceOfMap (TwistedDual P (VermaModule P y)) (h P) y :=
    map_mem_weightSpaceOfMap P φ (VermaModule.hwv_mem_weightSpace P y)
  apply TwistedDual.ext
  intro w
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  change _ = c * contravariantForm P y (hwv P y) w
  have hw : w ∈ ⨆ ν, weightSpaceOfMap (VermaModule P y) (h P) ν :=
    (VermaModule.isCategoryO P y).iSup_weightSpaceOfMap_eq_top ▸ Submodule.mem_top
  induction hw using Submodule.iSup_induction' with
  | mem ν w hw =>
    by_cases hν : y = ν
    · subst hν
      have hw' : w ∈ weightSpace P y y := hw
      rw [weightSpace_self, Submodule.mem_span_singleton] at hw'
      obtain ⟨a, rfl⟩ := hw'
      rw [map_smul, map_smul, contravariantForm_hwv_hwv, smul_eq_mul, smul_eq_mul]
      ring
    · rw [apply_eq_zero_of_ne hφ hw hν,
        contravariantForm_eq_zero_of_ne P y (VermaModule.hwv_mem_weightSpace P y) hw hν,
        mul_zero]
  | zero => simp
  | add u v _ _ hu hv => rw [map_add, map_add, hu, hv, mul_add]

omit [LieModule K P.KacMoodyAlgebra X] in
/-- A module which is a quotient of `M(y)` and embeds into `M(y)^∨` is zero or isomorphic to
`L(y)` (the argument of Humphreys, GSM 94, Theorem 7.9 (check)). -/
theorem subsingleton_or_nonempty_equiv_irreducible {y : Dual K H}
    (p : VermaModule P y →ₗ⁅K,𝔤⁆ X) (hp : Function.Surjective p)
    (i : X →ₗ⁅K,𝔤⁆ restrictedDual P (VermaModule P y)) (hi : Function.Injective i) :
    Subsingleton X ∨ Nonempty (IrreducibleModule P y ≃ₗ⁅K,𝔤⁆ X) := by
  let φ := (restrictedDual P (VermaModule P y)).incl.comp (i.comp p)
  have hφ := VermaModule.eq_smul_toTwistedDual P y φ
  set c := TwistedDual.toDual P _ (φ (hwv P y)) (hwv P y)
  have hker : ∀ u, p u = 0 ↔ c • toTwistedDual P y u = 0 := fun u ↦ by
    have hφu : φ u = c • toTwistedDual P y u := by rw [hφ]; rfl
    rw [← hφu]
    constructor
    · intro h
      change (restrictedDual P (VermaModule P y)).incl (i (p u)) = 0
      rw [h, map_zero, map_zero]
    · intro h
      exact hi (by rw [map_zero]; exact Subtype.ext h)
  by_cases hc : c = 0
  · left
    refine ⟨fun a b ↦ ?_⟩
    obtain ⟨u, rfl⟩ := hp a
    obtain ⟨v, rfl⟩ := hp b
    rw [(hker u).mpr (by rw [hc, zero_smul]), (hker v).mpr (by rw [hc, zero_smul])]
  · right
    have hker' : ∀ u, p u = 0 ↔ u ∈ maxSubmodule P y := fun u ↦ by
      rw [hker, smul_eq_zero, or_iff_right hc, ← VermaModule.toRestrictedDual_eq_zero_iff P y u]
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    exact ⟨LieModuleEquiv.ofBijective (LieSubmodule.Quotient.lift (maxSubmodule P y) p
      fun u hu ↦ by rw [LieModuleHom.mem_ker]; exact (hker' u).mpr hu)
      ⟨quotient_lift_injective P _ _ _ fun u hu ↦ (hker' u).mp hu,
        LieSubmodule.Quotient.lift_surjective _ _ _ hp⟩⟩

end Verma

section Translation

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

include hA in
/-- **Translation of simple modules, dichotomy** (Humphreys, GSM 94, Theorem 7.9 (check), first
assertion; integral weights, finite type, algebraically closed field of characteristic zero).
Under the hypotheses of `translation_verma`, with `T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν))`, the
module `T_λ^μ L(w·λ)` is either zero or isomorphic to `L(w·μ)`. -/
theorem translation_irreducible {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    Subsingleton (centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) ∨
      Nonempty (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,KacMoodyAlgebra P⁆
        centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
          (centralCharacter P μ)
          (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) := by
  set x := P.weylDot hA.isGeneralizedCartan w lam
  obtain ⟨e₁⟩ := translation_verma_equiv P hA hlam hμ hfacet hν hz hzν w
  obtain ⟨e₂⟩ := translation_dualVerma P hA hlam hμ hfacet hν hz hzν w
  let π : VermaModule P x →ₗ⁅K,KacMoodyAlgebra P⁆ IrreducibleModule P x :=
    LieSubmodule.Quotient.mk' (maxSubmodule P x)
  have hπ : Function.Surjective π := LieSubmodule.Quotient.surjective_mk' _
  have hTπ : Function.Surjective (centralTranslationMap P (IrreducibleModule P ν)
      (centralCharacter P lam) (centralCharacter P μ) π) := centralTranslationMap_surjective P
    (VermaModule.isCategoryO P x) (IrreducibleModule.isCategoryO P ν) _ _ π hπ
  have hTι : Function.Injective (centralTranslationMap P (IrreducibleModule P ν)
      (centralCharacter P lam) (centralCharacter P μ) (IrreducibleModule.toRestrictedDual P x)) :=
    centralTranslationMap_injective P _ _ _ (IrreducibleModule.toRestrictedDual_injective P x)
  exact subsingleton_or_nonempty_equiv_irreducible P
    ((centralTranslationMap P (IrreducibleModule P ν) (centralCharacter P lam)
      (centralCharacter P μ) π).comp e₁.toLieModuleHom) (hTπ.comp e₁.surjective)
    (e₂.symm.toLieModuleHom.comp (centralTranslationMap P (IrreducibleModule P ν)
      (centralCharacter P lam) (centralCharacter P μ) (IrreducibleModule.toRestrictedDual P x)))
    (e₂.symm.injective.comp hTι)

end Translation

end Matrix.Realization.KacMoodyAlgebra
