/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Hyperplane
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Polynomials vanishing only on finitely many hyperplanes

Let `H` be a finite-dimensional vector space over an algebraically closed field `K`. A nonzero
polynomial function on `H*` whose zero set is contained in a finite union of affine hyperplanes
`λ(a_k) + c_k = 0` is, up to a nonzero scalar, a product of powers of the equations
`λ(a_k) + c_k` (`Module.Dual.exists_eq_C_mul_prod_affPoly_pow`).

## Proof

It suffices to show that some `λ(a_k) + c_k` divides `F` when `F` is not constant
(`Module.Dual.exists_affPoly_dvd_of_forall`); then induct on the degree. If no `λ(a_k) + c_k`
divides `F`, then `F` is nonzero somewhere on each hyperplane. Choose `δ` with `F_d(δ) ≠ 0`
(`F_d` the top homogeneous component of `F`) and `δ(a_k) ≠ 0` for all `k`, and choose `λ₁` such
that for every `k`, `F` is nonzero at the point where the line `λ₁ + t δ` meets the `k`-th
hyperplane (these are finitely many nonzero polynomial conditions on `λ₁`). The polynomial
`t ↦ F(λ₁ + t δ)` has degree `d > 0` (its leading coefficient is `F_d(δ)`), so it has a root `t₀`
since `K` is algebraically closed. The point `λ₁ + t₀ δ` then lies on some hyperplane, where `F`
does not vanish by the choice of `λ₁`: a contradiction. (This replaces an appeal to the
Nullstellensatz.)
-/

open Polynomial

noncomputable section

namespace Module.Dual

variable {K H : Type*} [Field K] [IsAlgClosed K] [AddCommGroup H] [Module K H]

/-- Over an algebraically closed field, a nonconstant polynomial whose zeros all lie on finitely
many affine hyperplanes is divisible by the equation of one of them. -/
theorem exists_affPoly_dvd_of_forall {F : MvPolynomial (PolyIdx K H) K}
    (hF : 0 < F.totalDegree) {κ : Type*} (s : Finset κ) (a : κ → H) (c : κ → K)
    (ha : ∀ k ∈ s, a k ≠ 0)
    (hz : ∀ Λ : Dual K H, evalPoly K H F Λ = 0 → ∃ k ∈ s, Λ (a k) + c k = 0) :
    ∃ k ∈ s, affPoly K H (a k) (c k) ∣ F := by
  by_contra! hnd
  have hF0 : F ≠ 0 := by rintro rfl; simp at hF
  set d := F.totalDegree
  -- the direction `δ`
  obtain ⟨δ, hδ⟩ := exists_evalPoly_ne_zero (K := K) (H := H)
    (F := MvPolynomial.homogeneousComponent d F * ∏ k ∈ s, linPoly K H (a k))
    (mul_ne_zero (MvPolynomial.homogeneousComponent_totalDegree_ne_zero hF0)
      (Finset.prod_ne_zero_iff.mpr fun k hk ↦ linPoly_ne_zero (ha k hk)))
  rw [map_mul, map_prod, Pi.mul_apply, Finset.prod_apply] at hδ
  have hδd := left_ne_zero_of_mul hδ
  have hδa (k : κ) (hk : k ∈ s) : δ (a k) ≠ 0 := by
    have := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hδ) k hk
    rwa [evalPoly_linPoly] at this
  -- the base point `λ₁`
  obtain ⟨Λ₁, hΛ₁⟩ := exists_forall_evalPoly_ne_zero s
    (fun k ↦ projSubst K H (a k) (c k) ((δ (a k))⁻¹ • δ) F) fun k hk h0 ↦ by
      obtain ⟨Λ, hΛ, hne⟩ := exists_eval_ne_zero_of_not_dvd (ha k hk) (c k) (hnd k hk)
      have := congrFun (congrArg (evalPoly K H) h0) Λ
      rw [evalPoly_projSubst, hΛ, zero_smul, sub_zero, map_zero, Pi.zero_apply] at this
      exact hne this
  -- the restriction to the line `λ₁ + t δ` has a root
  obtain ⟨hdeg, hcoeff⟩ := natDegree_linePoly_le_and_coeff Λ₁ δ (F := F) le_rfl
  set r := linePoly K H Λ₁ δ F
  have hr0 : r ≠ 0 := fun h ↦ hδd (by rw [← hcoeff, h, coeff_zero])
  have hrdeg : r.natDegree = d := le_antisymm hdeg (le_natDegree_of_ne_zero (by rwa [hcoeff]))
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root r (by
    rw [degree_eq_natDegree hr0, hrdeg]
    exact_mod_cast hF.ne')
  rw [IsRoot, eval_linePoly] at ht
  obtain ⟨k, hk, hkz⟩ := hz _ ht
  apply hΛ₁ k hk
  rw [evalPoly_projSubst]
  convert ht using 2
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hkz
  have hx : (Λ₁ (a k) + c k) * (δ (a k))⁻¹ = -t := by
    rw [show Λ₁ (a k) + c k = -(t * δ (a k)) by linear_combination hkz, neg_mul, mul_assoc,
      mul_inv_cancel₀ (hδa k hk), mul_one]
  rw [smul_smul, hx, neg_smul, sub_neg_eq_add]

/-- **Polynomials vanishing only on finitely many hyperplanes.** Over an algebraically closed
field, a nonzero polynomial whose zeros all lie on the affine hyperplanes `λ(a_k) + c_k = 0`
(`k ∈ s`) is a nonzero scalar times `∏_k (λ(a_k) + c_k)^{e_k}` for some exponents `e_k`. -/
theorem exists_eq_C_mul_prod_affPoly_pow {F : MvPolynomial (PolyIdx K H) K} (hF : F ≠ 0)
    {κ : Type*} (s : Finset κ) (a : κ → H) (c : κ → K) (ha : ∀ k ∈ s, a k ≠ 0)
    (hz : ∀ Λ : Dual K H, evalPoly K H F Λ = 0 → ∃ k ∈ s, Λ (a k) + c k = 0) :
    ∃ c₀ : K, c₀ ≠ 0 ∧ ∃ e : κ → ℕ,
      F = MvPolynomial.C c₀ * ∏ k ∈ s, affPoly K H (a k) (c k) ^ e k := by
  classical
  induction hn : F.totalDegree using Nat.strong_induction_on generalizing F with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (hn.trans h0)
    refine ⟨F.coeff 0, fun h ↦ hF (by rw [hC, h, map_zero]), 0, ?_⟩
    simpa using hC
  · obtain ⟨k, hk, G, rfl⟩ := exists_affPoly_dvd_of_forall (hn ▸ hpos) s a c ha hz
    have hG : G ≠ 0 := right_ne_zero_of_mul hF
    have hdeg : G.totalDegree < n := by
      rw [← hn, MvPolynomial.totalDegree_mul_eq_add (affPoly_ne_zero (ha k hk) _) hG,
        totalDegree_affPoly (ha k hk)]
      omega
    obtain ⟨c₀, hc₀, e, he⟩ := ih _ hdeg hG (fun Λ hΛ ↦ hz Λ (by
      rw [map_mul, Pi.mul_apply, hΛ, mul_zero])) rfl
    refine ⟨c₀, hc₀, Function.update e k (e k + 1), ?_⟩
    have hprod : ∏ k' ∈ s.erase k, affPoly K H (a k') (c k') ^ Function.update e k (e k + 1) k' =
        ∏ k' ∈ s.erase k, affPoly K H (a k') (c k') ^ e k' :=
      Finset.prod_congr rfl fun k' hk' ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
    rw [he, ← Finset.mul_prod_erase _ _ hk, ← Finset.mul_prod_erase _ _ hk,
      Function.update_self, pow_succ, hprod]
    ring

end Module.Dual
