/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaHomFiniteType

/-!
# Singular integral reduction to dot-dominant targets

The arguments are reconstructed from the existing BGG.Verma proofs, not transcribed
from a consulted textbook. Here dot dominance means `IsDominantIntegral (Λ + rho)`;
ordinary dominance of `Λ` is NOT assumed. Zero coroot pairings are allowed.

Main results: every Weyl translate of a dot-dominant integral weight embeds into its
Verma module, and every integral target for a finite Weyl group embeds into such a
Verma module. Postcomposition gives an actual injective map on Hom spaces and a
dimension inequality. This is a reduction, not a proof of singular-block uniqueness.
-/

open Module LieModule CoxeterSystem
noncomputable section
namespace Matrix.Realization
variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- Reconstructed weak-dominance version of the positive-coroot lemma: along a
Coxeter ascent the coroot pairing is a natural number, possibly zero. -/
theorem exists_apply_coroot_nat_of_not_isLeftDescent
    (hA : A.IsGeneralizedCartan) {μ : Dual K H} (hμ : P.IsDominantIntegral μ)
    {w : P.weylGroup hA} {i : ι}
    (hw : ¬(P.coxeterSystem hA).IsLeftDescent w i) :
    ∃ n : ℕ, w.val μ (P.coroot i) = n := by
  classical
  set cs := P.coxeterSystem hA
  obtain ⟨k, hk⟩ := P.exists_apply_eq_add_rootOf hA w.2 (μ := μ) fun j ↦ by
    obtain ⟨n, hn⟩ := hμ j
    exact ⟨n, by rw [hn]; norm_cast⟩
  obtain ⟨nᵢ, hnᵢ⟩ := hμ i
  set z : ℤ := nᵢ + (A *ᵥ k) i
  have hc : w.val μ (P.coroot i) = z := by
    rw [hk, LinearMap.add_apply, hnᵢ, rootOf_apply_coroot]
    push_cast [z]
    rfl
  have hw' : ¬cs.IsRightDescent w⁻¹ i := by rwa [cs.isRightDescent_inv_iff]
  obtain ⟨l, hl, hwl⟩ := (P.not_isRightDescent_coxeterSystem_iff hA).mp hw'
  set v := w⁻¹ * cs.simple i * w
  obtain ⟨m, hm, hvm⟩ := P.exists_sub_apply_eq_rootOf hA hμ v
  have hv : v.val μ = μ - (z : K) • P.rootOf l := by
    simp only [v, Subgroup.coe_mul, LinearEquiv.mul_apply, coxeterSystem_simple, cs]
    rw [reflection_apply, hc, map_sub, map_smul, hwl]
    congr 1
    exact w.val.symm_apply_apply μ
  have h2 : P.rootOf (z • l) = (z : K) • P.rootOf l := by
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul K]
  rw [hv, sub_sub_cancel, ← h2] at hvm
  have hml : z • l = m := P.rootOf_injective hvm
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero, LinearEquiv.map_eq_zero_iff] at hwl
    exact P.linearIndependent_root.ne_zero i hwl
  obtain ⟨j, hj⟩ : ∃ j, l j ≠ 0 := by
    by_contra! h
    exact hl0 (funext h)
  have hlj : 0 < l j := lt_of_le_of_ne (hl j) (Ne.symm hj)
  have hz0 : 0 ≤ z := by
    have h1 := congrFun hml j
    have h2 := hm j
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2
    nlinarith
  refine ⟨z.toNat, hc.trans ?_⟩
  exact_mod_cast (Int.toNat_of_nonneg hz0).symm

omit [DecidableEq ι] in
/-- Reconstructed finite-Weyl-group reduction. The representative is dot-dominant,
not necessarily ordinarily dominant, so singular integral weights are included. -/
theorem exists_dotDominantIntegral_weylDot
    (hA : A.IsGeneralizedCartan) [Finite (P.weylGroup hA)]
    {Λ : Dual K H} (hΛ : ∀ i, ∃ z : ℤ, (Λ + P.rho) (P.coroot i) = z) :
    ∃ Λ', P.IsDominantIntegral (Λ' + P.rho) ∧
      ∃ w : P.weylGroup hA, Λ = P.weylDot hA w Λ' := by
  obtain ⟨w, hw⟩ := P.exists_dominantIntegral_weylGroup hA hΛ
  refine ⟨w.val (Λ + P.rho) - P.rho, ?_, w⁻¹, ?_⟩
  · simpa only [sub_add_cancel] using hw
  · simp [weylDot]

namespace KacMoodyAlgebra.VermaModule

set_option maxHeartbeats 1000000 in
-- The Coxeter-length induction elaborates dependent Verma-module maps in both pairing cases.
/-- Reconstructed weak-dominant Verma embedding. Zero pairings give identity maps;
positive pairings give the existing rank-one reflection embeddings. -/
theorem exists_injective_weylDot_of_dotDominant
    (hA : A.IsGeneralizedCartan) {Λ : Dual K H}
    (hΛ : P.IsDominantIntegral (Λ + P.rho)) (w : P.weylGroup hA) :
    ∃ φ : VermaModule P (P.weylDot hA w Λ) →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ,
      Function.Injective φ := by
  set cs := P.coxeterSystem hA
  induction hl : cs.length w using Nat.strong_induction_on generalizing w with
  | _ l ih =>
    subst hl
    by_cases hw1 : w = 1
    · subst hw1
      rw [weylDot_one]
      exact ⟨LieModuleHom.id, Function.injective_id⟩
    obtain ⟨s, hs⟩ := cs.exists_leftDescent_of_ne_one hw1
    have hsl := (cs.isLeftDescent_iff).mp hs
    set w' := cs.simple s * w
    have hww' : w = cs.simple s * w' := (cs.simple_mul_simple_cancel_left s).symm
    have hw' : ¬cs.IsLeftDescent w' s := by
      rwa [← cs.isLeftDescent_iff_not_isLeftDescent_mul]
    obtain ⟨φ, hφ⟩ := ih _ (by omega) w' rfl
    obtain ⟨n, hn⟩ := P.exists_apply_coroot_nat_of_not_isLeftDescent hA hΛ hw'
    have hn' : (P.weylDot hA w' Λ + P.rho) (P.coroot s) = n := by
      rwa [weylDot_add_rho]
    rw [hww', weylDot_simple_mul]
    by_cases hn0 : n = 0
    · have heq : P.reflection hA s (P.weylDot hA w' Λ + P.rho) - P.rho =
          P.weylDot hA w' Λ := by
        rw [P.reflection_add_rho_sub_rho hA hn', hn0, zero_nsmul, sub_zero]
      rw [heq]
      exact ⟨φ, hφ⟩
    · obtain ⟨ψ, hψ, -⟩ := exists_injective_reflection P hA (Nat.pos_of_ne_zero hn0) hn'
      exact ⟨φ.comp ψ, hφ.comp hψ⟩

/-- A genuine embedding into a dot-dominant Verma module for every integral weight
when the Weyl group is finite. This reconstructed reduction includes singular targets. -/
theorem exists_injective_dotDominant_of_integral
    (hA : A.IsGeneralizedCartan) [Finite (P.weylGroup hA)]
    (Λ : Dual K H) (hΛ : ∀ i, ∃ z : ℤ, (Λ + P.rho) (P.coroot i) = z) :
    ∃ Λ', P.IsDominantIntegral (Λ' + P.rho) ∧
      (∃ w : P.weylGroup hA, Λ = P.weylDot hA w Λ') ∧
      ∃ φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ',
        Function.Injective φ := by
  obtain ⟨Λ', hΛ', w, hw⟩ := P.exists_dotDominantIntegral_weylDot hA hΛ
  refine ⟨Λ', hΛ', ⟨w, hw⟩, ?_⟩
  rw [hw]
  exact exists_injective_weylDot_of_dotDominant P hA hΛ' w

/-- Reconstructed dimension monotonicity under an actual Verma embedding.
Finite-dimensionality is the existing primitive-vector theorem, not a premise. -/
theorem finrank_hom_le_of_injective {Λ Λ' : Dual K H} (μ : Dual K H)
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ')
    (hφ : Function.Injective φ) :
    finrank K (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) ≤
      finrank K (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ') := by
  let Φ : (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) →ₗ[K]
      (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ') :=
    { toFun := fun ψ ↦ φ.comp ψ
      map_add' := fun _ _ ↦ LieModuleHom.ext fun _ ↦ map_add φ _ _
      map_smul' := fun _ _ ↦ LieModuleHom.ext fun _ ↦ map_smul φ _ _ }
  exact LinearMap.finrank_le_finrank_of_injective
    (show Function.Injective Φ from fun ψ ψ' h ↦
      LieModuleHom.ext fun m ↦ hφ (LieModuleHom.congr_fun h m))

/-- Necessary singular-integral reduction: there is a single dot-dominant target
in the same orbit that bounds Hom dimensions from EVERY source weight. -/
theorem exists_dotDominant_hom_bound_of_finite_type_integral
    (hA : A.IsFiniteCartan) (Λ : Dual K H)
    (hΛ : ∀ i, ∃ z : ℤ, (Λ + P.rho) (P.coroot i) = z) :
    ∃ Λ', P.IsDominantIntegral (Λ' + P.rho) ∧
      (∃ w : P.weylGroup hA.isGeneralizedCartan,
        Λ = P.weylDot hA.isGeneralizedCartan w Λ') ∧
      ∀ μ : Dual K H,
        finrank K (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) ≤
          finrank K (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ') := by
  have := P.finite_weylGroup hA
  obtain ⟨Λ', hΛ', hw, φ, hφ⟩ :=
    exists_injective_dotDominant_of_integral P hA.isGeneralizedCartan Λ hΛ
  exact ⟨Λ', hΛ', hw, fun μ ↦ finrank_hom_le_of_injective P μ φ hφ⟩

end KacMoodyAlgebra.VermaModule
end Matrix.Realization
