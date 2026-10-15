/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.Verma
import LieLean.Algebra.Lie.KacMoody.VermaHomSingularReduction
import LieLean.Algebra.Lie.KacMoody.TensorVerma
import LieLean.LinearAlgebra.LinearMap.IntegralPoints
import LieLean.LinearAlgebra.Matrix.Cartan.AffineWeylGroup

/-!
# Verma's theorem for an arbitrary positive root

For `A` of finite type, `β` a positive root and `λ` a weight with `⟨λ + ρ, β^∨⟩ = n ∈ ℕ`, there is
an embedding `M(s_β · λ) = M(λ - nβ) ↪ M(λ)` ([HumO] Thm. 4.6, proved for integral weights in
§4.6 and for arbitrary weights in §4.7).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_affine_lie`: under the identification
  `U(𝔫₋) ≃ M(λ)`, `u ↦ u v_λ`, the action of `x ∈ 𝔤` on `M(λ)` depends affinely on `λ`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_injective_iff_not_injective_primMap`:
  an embedding `M(λ - ν) ↪ M(λ)` exists iff the linear map `u ↦ (eⱼ u v_λ)ⱼ` on `U(𝔫₋)_{-ν}`
  (`primMap`) is not injective.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_injective_reflectionOf_of_regular`:
  the integral regular case.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_injective_reflectionOf`:
  **Verma's theorem** ([HumO] Thm. 4.6) for arbitrary weights.

## Proof

Integral regular case: write `λ = w · Λ` with `Λ` dominant integral. Then `β' = w⁻¹ β` is a
positive root with `w β' > 0`, so `w ≤ w s_{β'}` in the Bruhat order, and Verma's theorem along
the Bruhat order (`exists_injective_of_bruhatLE`) gives `M(w s_{β'} · Λ) ↪ M(w · Λ)`, where
`w s_{β'} · Λ = s_β · λ`. This replaces the bookkeeping of [HumO] §4.6 (reconstructed).

General case ([HumO] §4.7): the weights `λ` with `⟨λ + ρ, β^∨⟩ = n` form an affine hyperplane,
parametrized affinely by `y ∈ K^{ι}` with `y_i` fixed. The map `primMap` depends affinely on `λ`
(`exists_affine_lie`), it is not injective at the integral points where `λ + ρ` is regular, and
these are the integral points outside the zero set of a nonzero polynomial, so it is not
injective anywhere (`LinearMap.not_injective_add_sum_smul_of_forall_int`).

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §4.6, §4.7.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra.VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝓤₋" => UniversalEnvelopingAlgebra K (nNeg P)
local notation "ιₙ" => UniversalEnvelopingAlgebra.ι K (L := nNeg P)

/-! ### Affine dependence on the highest weight -/

lemma equivEnvNNeg_one (Λ : Dual K H) : equivEnvNNeg P Λ 1 = hwv P Λ := by
  simp

lemma equivEnvNNeg_ι_mul (Λ : Dual K H) (y : nNeg P) (u : 𝓤₋) :
    equivEnvNNeg P Λ (ιₙ y * u) = ⁅(y : P.KacMoodyAlgebra), equivEnvNNeg P Λ u⁆ := by
  rw [equivEnvNNeg_mul, UniversalEnvelopingAlgebra.map_ι, lie_eq_smul]
  rfl

lemma equivEnvNNeg_symm_lie (Λ : Dual K H) (y : nNeg P) (u : 𝓤₋) :
    (equivEnvNNeg P Λ).symm ⁅(y : P.KacMoodyAlgebra), equivEnvNNeg P Λ u⁆ = ιₙ y * u := by
  rw [← equivEnvNNeg_ι_mul, LinearEquiv.symm_apply_apply]

/-- Under `U(𝔫₋) ≃ M(λ)`, the action of `x ∈ 𝔤` on `u v_λ` depends affinely on `λ`. -/
theorem exists_affine_lie (x : P.KacMoodyAlgebra) (u : 𝓤₋) :
    ∃ (a : 𝓤₋) (ℓ : Dual K H →ₗ[K] 𝓤₋), ∀ Λ,
      (equivEnvNNeg P Λ).symm ⁅x, equivEnvNNeg P Λ u⁆ = a + ℓ Λ := by
  induction u using UniversalEnvelopingAlgebra.TensorIdentity.induction_left generalizing x with
  | hone =>
    have hx : x ∈ (nNeg P).toSubmodule ⊔ (borel P).toSubmodule := by
      rw [(isCompl_nNeg_borel P).sup_eq_top]; trivial
    obtain ⟨y, hy, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, hc, z, hz, rfl⟩ := Submodule.mem_sup.mp hb
    obtain ⟨a, rfl⟩ := (mem_cartan P).mp hc
    refine ⟨ιₙ ⟨y, hy⟩, (LinearMap.applyₗ a).smulRight 1, fun Λ ↦ ?_⟩
    have hy' := equivEnvNNeg_symm_lie P Λ ⟨y, hy⟩ 1
    simp only [mul_one] at hy'
    rw [equivEnvNNeg_one, add_lie, add_lie, lie_h_hwv, lie_hwv_of_mem_nPos P Λ hz, add_zero,
      map_add, ← equivEnvNNeg_one, hy', map_smul, LinearEquiv.symm_apply_apply]
    rfl
  | hadd u u' hu hu' =>
    obtain ⟨a, ℓ, h⟩ := hu x
    obtain ⟨a', ℓ', h'⟩ := hu' x
    refine ⟨a + a', ℓ + ℓ', fun Λ ↦ ?_⟩
    rw [map_add, lie_add, map_add, h, h', LinearMap.add_apply]
    abel
  | hsmul r u hu =>
    obtain ⟨a, ℓ, h⟩ := hu x
    refine ⟨r • a, r • ℓ, fun Λ ↦ ?_⟩
    rw [map_smul, lie_smul, map_smul, h, LinearMap.smul_apply, smul_add]
  | hι y u hu =>
    obtain ⟨a, ℓ, h⟩ := hu x
    obtain ⟨a₁, ℓ₁, h₁⟩ := hu ⁅x, (y : P.KacMoodyAlgebra)⁆
    refine ⟨a₁ + ιₙ y * a, ℓ₁ + LinearMap.mulLeft K (ιₙ y) ∘ₗ ℓ, fun Λ ↦ ?_⟩
    rw [equivEnvNNeg_ι_mul, leibniz_lie, map_add, h₁,
      ← LinearEquiv.apply_symm_apply (equivEnvNNeg P Λ) ⁅x, equivEnvNNeg P Λ u⁆,
      equivEnvNNeg_symm_lie, h, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, mul_add]
    abel

/-- The Cartan part acts on `u v_λ` by `λ` plus a term independent of `λ`. -/
theorem exists_lie_h (a : H) (u : 𝓤₋) :
    ∃ c : 𝓤₋, ∀ Λ, (equivEnvNNeg P Λ).symm ⁅h P a, equivEnvNNeg P Λ u⁆ = c + Λ a • u := by
  induction u using UniversalEnvelopingAlgebra.TensorIdentity.induction_left with
  | hone =>
    refine ⟨0, fun Λ ↦ ?_⟩
    rw [equivEnvNNeg_one, lie_h_hwv, ← equivEnvNNeg_one, ← map_smul,
      LinearEquiv.symm_apply_apply, zero_add]
  | hadd u u' hu hu' =>
    obtain ⟨c, h⟩ := hu
    obtain ⟨c', h'⟩ := hu'
    refine ⟨c + c', fun Λ ↦ ?_⟩
    rw [map_add, lie_add, map_add, h, h', smul_add]
    abel
  | hsmul r u hu =>
    obtain ⟨c, h⟩ := hu
    refine ⟨r • c, fun Λ ↦ ?_⟩
    rw [map_smul, lie_smul, map_smul, h, smul_add, smul_comm]
  | hι y u hu =>
    obtain ⟨c, hc⟩ := hu
    have hy : ⁅h P a, (y : P.KacMoodyAlgebra)⁆ ∈ nNeg P := lie_h_mem_nNeg P a y.2
    refine ⟨ιₙ ⟨_, hy⟩ * u + ιₙ y * c, fun Λ ↦ ?_⟩
    have hy' := equivEnvNNeg_symm_lie P Λ ⟨_, hy⟩ u
    simp only at hy'
    rw [equivEnvNNeg_ι_mul, leibniz_lie, map_add, hy',
      ← LinearEquiv.apply_symm_apply (equivEnvNNeg P Λ) ⁅h P a, equivEnvNNeg P Λ u⁆,
      equivEnvNNeg_symm_lie, hc, mul_add, mul_smul_comm]
    abel

/-! ### Weight spaces of `U(𝔫₋)` -/

/-- The elements `u ∈ U(𝔫₋)` of weight `-ν`, i.e. with `u v_0 ∈ M(0)_{-ν}`. -/
def negWeightSpace (ν : Dual K H) : Submodule K 𝓤₋ :=
  (weightSpace P 0 (-ν)).comap (equivEnvNNeg P 0).toLinearMap

theorem equivEnvNNeg_mem_weightSpace_iff (Λ ν : Dual K H) (u : 𝓤₋) :
    equivEnvNNeg P Λ u ∈ weightSpace P Λ (Λ - ν) ↔ u ∈ negWeightSpace P ν := by
  have key : ∀ Λ', equivEnvNNeg P Λ' u ∈ weightSpace P Λ' (Λ' - ν) ↔
      ∀ a, ∀ c : 𝓤₋, (∀ Λ, (equivEnvNNeg P Λ).symm ⁅h P a, equivEnvNNeg P Λ u⁆ =
        c + Λ a • u) → c = -ν a • u := by
    intro Λ'
    refine ⟨fun hu a c hc ↦ ?_, fun H a ↦ ?_⟩
    · have := hc Λ'
      rw [hu a, map_smul, LinearEquiv.symm_apply_apply, LinearMap.sub_apply, sub_smul] at this
      rw [neg_smul]
      linear_combination (norm := module) -this
    · obtain ⟨c, hc⟩ := exists_lie_h P a u
      have hc' := H a c hc
      apply (equivEnvNNeg P Λ').symm.injective
      rw [hc Λ', map_smul, LinearEquiv.symm_apply_apply, hc', LinearMap.sub_apply, sub_smul,
        neg_smul]
      abel
  rw [key, negWeightSpace, Submodule.mem_comap, LinearEquiv.coe_coe,
    show (-ν) = (0 : Dual K H) - ν by simp, key]

instance (ν : Dual K H) : FiniteDimensional K (negWeightSpace P ν) := by
  have := finiteDimensional_weightSpace P 0 (-ν)
  let f : negWeightSpace P ν →ₗ[K] weightSpace P 0 (-ν) :=
    ((equivEnvNNeg P 0).toLinearMap ∘ₗ (negWeightSpace P ν).subtype).codRestrict _
      fun u ↦ u.2
  refine Module.Finite.of_injective f fun u u' huu ↦ ?_
  have := congrArg Subtype.val huu
  exact Subtype.ext ((equivEnvNNeg P 0).injective this)

/-! ### Primitive vectors -/

/-- The map `u ↦ (eⱼ u v_λ)ⱼ` on `U(𝔫₋)_{-ν}`, through `U(𝔫₋) ≃ M(λ)`. Its kernel corresponds to
the primitive vectors of weight `λ - ν` of `M(λ)`. -/
def primMap (Λ ν : Dual K H) : negWeightSpace P ν →ₗ[K] (ι → 𝓤₋) :=
  LinearMap.pi fun j ↦ (equivEnvNNeg P Λ).symm.toLinearMap ∘ₗ
    (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (e P j)) ∘ₗ
      (equivEnvNNeg P Λ).toLinearMap ∘ₗ (negWeightSpace P ν).subtype

lemma primMap_apply (Λ ν : Dual K H) (u : negWeightSpace P ν) (j : ι) :
    primMap P Λ ν u j = (equivEnvNNeg P Λ).symm ⁅e P j, equivEnvNNeg P Λ u⁆ :=
  rfl

/-- An embedding `M(λ - ν) ↪ M(λ)` exists iff `primMap` is not injective. -/
theorem exists_injective_iff_not_injective_primMap (Λ ν : Dual K H) :
    (∃ φ : VermaModule P (Λ - ν) →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ,
      Function.Injective φ) ↔ ¬Function.Injective (primMap P Λ ν) := by
  rw [exists_injective_iff, injective_iff_map_eq_zero, not_forall]
  constructor
  · rintro ⟨v, hv, hv0, he⟩
    obtain ⟨u, rfl⟩ := (equivEnvNNeg P Λ).surjective v
    have hu := (equivEnvNNeg_mem_weightSpace_iff P Λ ν u).mp hv
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [not_imp]
    refine ⟨funext fun j ↦ ?_, fun h0 ↦ hv0 ?_⟩
    · rw [primMap_apply, he, map_zero, Pi.zero_apply]
    · rw [show u = 0 from congrArg Subtype.val h0, map_zero]
  · rintro ⟨u, hu⟩
    rw [not_imp] at hu
    refine ⟨equivEnvNNeg P Λ u, (equivEnvNNeg_mem_weightSpace_iff P Λ ν u).mpr u.2,
      fun h0 ↦ hu.2 (Subtype.ext ((equivEnvNNeg P Λ).map_eq_zero_iff.mp h0)), fun j ↦ ?_⟩
    have := congrFun hu.1 j
    rw [primMap_apply, Pi.zero_apply] at this
    simpa using congrArg (equivEnvNNeg P Λ) this

/-- `primMap` depends affinely on `λ`. -/
theorem exists_primMap_eq_add (ν : Dual K H) (u : negWeightSpace P ν) :
    ∃ ℓ : Dual K H →ₗ[K] (ι → 𝓤₋), ∀ Λ, primMap P Λ ν u = primMap P 0 ν u + ℓ Λ := by
  choose a ℓ h using fun j ↦ exists_affine_lie P (e P j) (u : 𝓤₋)
  refine ⟨LinearMap.pi ℓ, fun Λ ↦ funext fun j ↦ ?_⟩
  rw [Pi.add_apply, primMap_apply, primMap_apply, h, h, LinearMap.pi_apply, map_zero, add_zero]

/-- `primMap` along an affine family of weights. -/
theorem primMap_add_sum_smul (ν μ₀ : Dual K H) (μ : ι → Dual K H) (y : ι → K) :
    primMap P (∑ j, y j • μ j + μ₀) ν =
      primMap P μ₀ ν + ∑ j, y j • (primMap P (μ j) ν - primMap P 0 ν) := by
  ext u : 1
  obtain ⟨ℓ, hℓ⟩ := exists_primMap_eq_add P ν u
  have hj : ∀ j, (primMap P (μ j) ν - primMap P 0 ν) u = ℓ (μ j) := fun j ↦ by
    rw [LinearMap.sub_apply, hℓ (μ j), add_sub_cancel_left]
  rw [LinearMap.add_apply, LinearMap.sum_apply, hℓ, hℓ μ₀]
  simp only [LinearMap.smul_apply, hj, map_add, map_sum, map_smul]
  abel


/-! ### The integral regular case -/

omit [DecidableEq ι] in
/-- A weight `x` with `⟨x, αⱼ^∨⟩ ∈ ℤ_{>0}` for all `j` is regular: `⟨x, β^∨⟩ ≠ 0` for every real
root `β`. -/
theorem corootPairing_ne_zero_of_regular (hA : A.IsGeneralizedCartan) {x : Dual K H}
    (hx : ∀ j, ∃ m : ℕ, x (P.coroot j) = m + 1) (u : P.weylGroup hA) (j : ι) :
    P.corootPairing hA x u j ≠ 0 := by
  classical
  rcases isPosRoot_or u j with hu | hu
  · have hu' : ¬(P.coxeterSystem hA).IsLeftDescent u⁻¹ j := by
      rw [CoxeterSystem.isLeftDescent_inv_iff]
      exact isPosRoot_iff_not_isRightDescent.mp hu
    obtain ⟨m, hm0, hm⟩ := P.exists_apply_coroot_eq_of_not_isLeftDescent hA hx hu'
    rw [corootPairing, hm]
    exact_mod_cast hm0.ne'
  · have hu' : ¬(P.coxeterSystem hA).IsLeftDescent (u * (P.coxeterSystem hA).simple j)⁻¹ j := by
      rw [CoxeterSystem.isLeftDescent_inv_iff]
      exact isPosRoot_iff_not_isRightDescent.mp hu
    obtain ⟨m, hm0, hm⟩ := P.exists_apply_coroot_eq_of_not_isLeftDescent hA hx hu'
    have h := corootPairing_mul_simple (P := P) (hA := hA) x u j
    rw [corootPairing, hm] at h
    intro h0
    rw [h0, neg_zero] at h
    exact hm0.ne' (by exact_mod_cast h)

lemma reflectionOf_mul_self_eq (hA : A.IsGeneralizedCartan) (u : P.weylGroup hA) (i : ι) :
    P.reflectionOf hA u i * u = u * (P.coxeterSystem hA).simple i := by
  have hs : (⟨P.reflection hA i, P.reflection_mem_weylGroup hA i⟩ : P.weylGroup hA) =
      (P.coxeterSystem hA).simple i := Subtype.ext (P.coxeterSystem_simple hA i).symm
  rw [reflectionOf, hs]
  group

omit [DecidableEq ι] [CharZero K] in
lemma reflectionOf_mul (hA : A.IsGeneralizedCartan) (v w : P.weylGroup hA) (i : ι) :
    P.reflectionOf hA v i * w = w * P.reflectionOf hA (w⁻¹ * v) i := by
  simp only [reflectionOf]
  group

/-- **Verma's theorem for integral regular weights** ([HumO] §4.6): if `λ + ρ` is integral and
regular, `β` is a positive root and `⟨λ + ρ, β^∨⟩ = n ∈ ℕ`, then `M(λ - nβ) ↪ M(λ)`. Write
`λ = w · Λ` with `Λ` dominant integral; then `s_β w = w s_{β'}` with `β' = w⁻¹β > 0`, `w β' > 0`,
so `w < w s_{β'}` and `exists_injective_of_bruhatLE` applies (reconstructed). -/
theorem exists_injective_reflectionOf_of_regular (hA : A.IsGeneralizedCartan)
    [Finite (P.weylGroup hA)] {Λ : Dual K H}
    (hint : ∀ j, ∃ z : ℤ, (Λ + P.rho) (P.coroot j) = z)
    (hreg : ∀ u j, P.corootPairing hA (Λ + P.rho) u j ≠ 0)
    {v : P.weylGroup hA} {i : ι} (hv : P.IsPosRoot hA v i) {n : ℕ}
    (hn : P.corootPairing hA (Λ + P.rho) v i = n) :
    ∃ φ : VermaModule P (Λ - n • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) →ₗ⁅K,
      P.KacMoodyAlgebra⁆ VermaModule P Λ, Function.Injective φ := by
  classical
  set cs := P.coxeterSystem hA
  obtain ⟨w₀, hw₀⟩ := P.exists_dominantIntegral_weylGroup hA hint
  set Λ₀ := w₀.val (Λ + P.rho) - P.rho with hΛ₀def
  have hΛ₀ : P.IsDominantIntegral Λ₀ := by
    intro j
    obtain ⟨m, hm⟩ := hw₀ j
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hreg w₀⁻¹ j
      rw [corootPairing, inv_inv]
      exact_mod_cast hm
    refine ⟨m - 1, ?_⟩
    rw [hΛ₀def, LinearMap.sub_apply, hm, rho_coroot,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm0), Nat.cast_one]
  set w := w₀⁻¹
  have hΛw : P.weylDot hA w Λ₀ = Λ := by
    rw [weylDot, hΛ₀def, sub_add_cancel, inv_apply_apply, add_sub_cancel_right]
  set u := w⁻¹ * v
  have hpair : ∀ y : P.weylGroup hA, P.corootPairing hA (w₀.val (Λ + P.rho)) (w₀ * y) i =
      P.corootPairing hA (Λ + P.rho) y i := fun y ↦ by
    rw [corootPairing_apply, ← mul_assoc, inv_mul_cancel, one_mul]
  have hu : P.IsPosRoot hA u i := by
    refine (isPosRoot_or u i).resolve_right fun hneg ↦ ?_
    have hneg' : ¬cs.IsLeftDescent (u * cs.simple i)⁻¹ i := by
      rw [CoxeterSystem.isLeftDescent_inv_iff]
      exact isPosRoot_iff_not_isRightDescent.mp hneg
    obtain ⟨m, hm⟩ := P.exists_apply_coroot_nat_of_not_isLeftDescent hA hw₀ hneg'
    have h1 : P.corootPairing hA (w₀.val (Λ + P.rho)) (u * cs.simple i) i = m := hm
    rw [show u = w₀ * v by simp [u, w], mul_assoc, hpair, corootPairing_mul_simple, hn] at h1
    have h2 : (n : K) = 0 := by
      have : ((n + m : ℕ) : K) = 0 := by push_cast; linear_combination -h1
      exact_mod_cast (Nat.add_eq_zero_iff.mp (by exact_mod_cast this)).1
    exact hreg v i (by rw [hn, h2])
  have hwu : w * u = v := by simp [u]
  have hlen : cs.length w < cs.length (w * P.reflectionOf hA u i) := by
    have hneg : ¬P.IsPosRoot hA (w * P.reflectionOf hA u i * u) i := by
      rw [mul_assoc, reflectionOf_mul_self_eq, ← mul_assoc, hwu]
      exact fun h ↦ not_isPosRoot_and hv h
    have := length_mul_reflectionOf_lt hu hneg
    rwa [mul_assoc, reflectionOf_mul_self, mul_one] at this
  have hbr : cs.BruhatLE w (w * P.reflectionOf hA u i) := by
    refine CoxeterSystem.BruhatStep.bruhatLE ⟨?_, hlen⟩
    have hs : (⟨P.reflection hA i, P.reflection_mem_weylGroup hA i⟩ : P.weylGroup hA) =
        cs.simple i := Subtype.ext (P.coxeterSystem_simple hA i).symm
    exact ⟨u, i, by rw [← mul_assoc, inv_mul_cancel, one_mul, reflectionOf, hs]⟩
  have hdot : P.weylDot hA (w * P.reflectionOf hA u i) Λ₀ =
      Λ - n • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) := by
    rw [show u = w⁻¹ * v from rfl, ← reflectionOf_mul, weylDot_mul, hΛw, weylDot,
      reflectionOf_apply', hn, ← Nat.cast_smul_eq_nsmul K]
    abel
  have := exists_injective_of_bruhatLE hA hΛ₀ hbr
  rwa [hdot, hΛw] at this

/-! ### Arbitrary weights -/

/-- Verma's theorem `M(λ - nβ) ↪ M(λ)` for `⟨λ + ρ, β^∨⟩ = n ∈ ℕ`, assuming that `W` is finite
and `dim 𝔥 = |ι|` (both hold in finite type, `exists_injective_reflectionOf`). Proof as in
[HumO] §4.7: the weights `λ'` with `⟨λ' + ρ, β^∨⟩ = n` are parametrized affinely by `K^ι`, the
integral regular ones (`exists_injective_reflectionOf_of_regular`) are the integral points outside
the zero set of a nonzero polynomial, and non-injectivity of `primMap` is a closed condition
(`LinearMap.not_injective_add_sum_smul_of_forall_int`). -/
theorem exists_injective_reflectionOf_of_finrank (hA : A.IsGeneralizedCartan)
    [Finite (P.weylGroup hA)] [FiniteDimensional K H] (hH : finrank K H = Fintype.card ι)
    {Λ : Dual K H} {v : P.weylGroup hA} {i : ι} (hv : P.IsPosRoot hA v i) {n : ℕ}
    (hn : P.corootPairing hA (Λ + P.rho) v i = n) :
    ∃ φ : VermaModule P (Λ - n • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) →ₗ⁅K,
      P.KacMoodyAlgebra⁆ VermaModule P Λ, Function.Injective φ := by
  classical
  have : Fintype (P.weylGroup hA) := Fintype.ofFinite _
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [zero_smul, sub_zero]
    exact ⟨LieModuleHom.id, Function.injective_id⟩
  set ν := n • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i)
  let b : Basis ι K H := basisOfLinearIndependentOfCardEqFinrank' P.coroot
    P.linearIndependent_coroot hH.symm
  have hb : ∀ j, b j = P.coroot j := fun j ↦ by simp [b]
  have hϖ : ∀ j k, b.dualBasis j (P.coroot k) = if k = j then 1 else 0 := fun j k ↦ by
    rw [← hb, Basis.dualBasis_apply_self]
  -- the points `x(y) = n ϖᵢ + ∑_{j ≠ i} yⱼ ϖⱼ` of the hyperplane `⟨x, αᵢ^∨⟩ = n`
  let x : (ι → K) → Dual K H := fun y ↦
    (n : K) • b.dualBasis i + ∑ j, (if j = i then 0 else y j) • b.dualBasis j
  have hx : ∀ y k, x y (P.coroot k) = if k = i then (n : K) else y k := fun y k ↦ by
    simp only [x, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, hϖ,
      smul_eq_mul]
    by_cases hk : k = i <;> simp [hk]
  let μ : ι → Dual K H := fun j ↦ if j = i then 0 else (v : Dual K H ≃ₗ[K] Dual K H) (b.dualBasis j)
  let μ₀ : Dual K H := (v : Dual K H ≃ₗ[K] Dual K H) ((n : K) • b.dualBasis i) - P.rho
  have hfam : ∀ y, ∑ j, y j • μ j + μ₀ + P.rho = (v : Dual K H ≃ₗ[K] Dual K H) (x y) := by
    intro y
    have hj : ∀ j, y j • μ j =
        (v : Dual K H ≃ₗ[K] Dual K H) ((if j = i then 0 else y j) • b.dualBasis j) := by
      intro j
      by_cases h : j = i <;> simp [μ, h]
    rw [Finset.sum_congr rfl fun j _ ↦ hj j, ← map_sum]
    simp only [μ₀, x, map_add]
    abel
  have hpair : ∀ y, P.corootPairing hA ((v : Dual K H ≃ₗ[K] Dual K H) (x y)) v i = n := by
    intro y
    rw [corootPairing, inv_apply_apply, hx, ite_eq_left rfl]
  have hint : ∀ y : ι → ℤ, ∀ k, ∃ z : ℤ,
      (v : Dual K H ≃ₗ[K] Dual K H) (x fun j ↦ (y j : K)) (P.coroot k) = z := by
    intro y k
    have hxint : ∀ j, ∃ z : ℤ, x (fun j ↦ (y j : K)) (P.coroot j) = z := fun j ↦
      ⟨if j = i then n else y j, by rw [hx]; split_ifs <;> simp⟩
    obtain ⟨z, hz⟩ := P.exists_int_of_mem_rootLattice
      (P.apply_sub_mem_rootLattice_of_integral hA v.2 hxint) k
    obtain ⟨z', hz'⟩ := hxint k
    refine ⟨z + z', ?_⟩
    rw [LinearMap.sub_apply, hz'] at hz
    push_cast
    linear_combination hz
  -- the regularity polynomial `∏_{u, j} ⟨λ(y) + ρ, (u αⱼ)^∨⟩`
  let L : P.weylGroup hA → ι → MvPolynomial ι K := fun u j ↦
    MvPolynomial.C (P.corootPairing hA (μ₀ + P.rho) u j) +
      ∑ l, MvPolynomial.X l * MvPolynomial.C (P.corootPairing hA (μ l) u j)
  let D : MvPolynomial ι K := ∏ u, ∏ j, L u j
  have hL : ∀ y u j, MvPolynomial.eval y (L u j) =
      P.corootPairing hA ((v : Dual K H ≃ₗ[K] Dual K H) (x y)) u j := by
    intro y u j
    rw [← hfam]
    simp only [L, corootPairing, map_add, map_sum, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    ring
  have hD : D ≠ 0 := by
    intro h0
    have h1 := congrArg (MvPolynomial.eval fun _ ↦ (1 : K)) h0
    simp only [D, map_prod, hL, map_zero, Finset.prod_eq_zero_iff, Finset.mem_univ,
      true_and] at h1
    obtain ⟨u, j, hj⟩ := h1
    rw [corootPairing_apply] at hj
    refine corootPairing_ne_zero_of_regular P hA (fun k ↦ ?_) _ j hj
    refine ⟨if k = i then n - 1 else 0, ?_⟩
    rw [hx]
    split_ifs
    · rw [Nat.cast_sub hn0, Nat.cast_one, sub_add_cancel]
    · simp
  have hnot : ∀ y : ι → ℤ, MvPolynomial.eval (fun j ↦ (y j : K)) D ≠ 0 →
      ¬Function.Injective (primMap P μ₀ ν +
        ∑ j, (y j : K) • (primMap P (μ j) ν - primMap P 0 ν)) := by
    intro y hy
    rw [← primMap_add_sum_smul, ← exists_injective_iff_not_injective_primMap]
    have hΛy := hfam fun j ↦ (y j : K)
    simp only [D, map_prod, Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const] at hy
    refine exists_injective_reflectionOf_of_regular P hA ?_ ?_ hv ?_
    · intro k
      rw [hΛy]
      exact hint y k
    · intro u j
      rw [hΛy, ← hL]
      exact hy u j
    · rw [hΛy, hpair]
  let ystar : ι → K := fun j ↦
    ((v⁻¹ : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) (P.coroot j)
  have hxs : x ystar = ((v⁻¹ : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) := by
    refine b.ext fun k ↦ ?_
    rw [hb, hx]
    split_ifs with hk
    · subst hk
      rw [← hn]
      rfl
    · rfl
  have hstar : ∑ j, ystar j • μ j + μ₀ = Λ := by
    have h1 := hfam ystar
    rw [hxs, apply_inv_apply] at h1
    exact add_right_cancel h1
  have key := LinearMap.not_injective_add_sum_smul_of_forall_int _ _ hD hnot ystar
  rw [← primMap_add_sum_smul, hstar] at key
  exact (exists_injective_iff_not_injective_primMap P Λ ν).mpr key


/-- **Verma's theorem** ([HumO] Thm. 4.6): for `A` of finite type, a positive root `β` and a
weight `λ` with `⟨λ + ρ, β^∨⟩ = n ∈ ℕ`, there is an embedding `M(s_β · λ) = M(λ - nβ) ↪ M(λ)`.
Humphreys works with a finite-dimensional semisimple Lie algebra over `ℂ`; here `K` is any field
of characteristic zero. The positive root `β = v αᵢ` is given by `v ∈ W` and `i`. -/
theorem exists_injective_reflectionOf (hA : A.IsFiniteCartan) [FiniteDimensional K H]
    {Λ : Dual K H} {v : P.weylGroup hA.isGeneralizedCartan} {i : ι}
    (hv : P.IsPosRoot hA.isGeneralizedCartan v i) {n : ℕ}
    (hn : P.corootPairing hA.isGeneralizedCartan (Λ + P.rho) v i = n) :
    ∃ φ : VermaModule P (Λ - n • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) →ₗ⁅K,
      P.KacMoodyAlgebra⁆ VermaModule P Λ, Function.Injective φ :=
  have := P.finite_weylGroup hA
  exists_injective_reflectionOf_of_finrank P hA.isGeneralizedCartan
    (P.finrank_eq_card_of_isFiniteCartan hA) hv hn

end Matrix.Realization.KacMoodyAlgebra.VermaModule
