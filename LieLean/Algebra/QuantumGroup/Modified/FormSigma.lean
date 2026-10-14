/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.FormRight
import LieLean.Algebra.QuantumGroup.BraidAction.A2

/-!
# The form on `U̇` is invariant under `σ`

The anti-automorphism `σ` of `U` (`braidReversal`: `Eᵢ ↦ Eᵢ`, `Fᵢ ↦ Fᵢ`, `K_μ ↦ K_{-μ}`,
[Lus] 3.1.3) maps `U_{λ'-λ''}` to itself and `N(λ', λ'')` to `N(-λ'', -λ')`, so it induces
`σ : U̇ → U̇`, `π_{λ',λ''}(u) ↦ π_{-λ'',-λ'}(σ u)` ([Lus] 23.1.6), with `σ(u x) = σ(x) σ(u)`.

## Main definitions and results

* `QuantumGroup.Modified.sigma`: the map `σ : U̇ → U̇` of [Lus] 23.1.6.
* `QuantumGroup.braidReversal_rho`: `σ ρ = ρ̄ σ` on `U`.
* `QuantumGroup.Modified.form_sigma_sigma`: [Lus] 26.1.4, `(σ(x), σ(y)) = (x, y)`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 3.1.3, 23.1.6, 26.1.4.
-/

open LieLean LusztigF

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]

@[simp] lemma braidReversal_algebraMap (c : k) :
    braidReversal (algebraMap k (QuantumGroup R v) c) = algebraMap k _ c := by
  simp [braidReversal]

lemma braidReversal_mem_adWeightSpace {χ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v χ) : braidReversal x ∈ adWeightSpace R v χ := fun μ ↦ by
  have h := congrArg braidReversal (hx (-μ))
  rw [braidReversal_mul, map_smul, braidReversal_mul, braidReversal_K, neg_neg] at h
  rw [h, smul_smul, map_neg, ← zpow_add₀ (NeZero.ne v), add_neg_cancel, zpow_zero, one_smul]

lemma braidReversal_mem_adWeightSpace_sub {l₁ l₂ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v (l₁ - l₂)) :
    braidReversal x ∈ adWeightSpace R v (-l₂ - -l₁) := by
  rw [neg_sub_neg]; exact braidReversal_mem_adWeightSpace hx

lemma braidReversal_mem_modRel {l₁ l₂ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ modRel R v l₁ l₂) : braidReversal x ∈ modRel R v (-l₂) (-l₁) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨μ, u, hu, rfl⟩ | ⟨μ, u, hu, rfl⟩
    · refine Submodule.subset_span
        (Or.inr ⟨-μ, braidReversal u, braidReversal_mem_adWeightSpace_sub hu, ?_⟩)
      rw [braidReversal_mul, map_sub, braidReversal_K, braidReversal_algebraMap, map_neg,
        AddMonoidHom.neg_apply, neg_neg]
    · refine Submodule.subset_span
        (Or.inl ⟨-μ, braidReversal u, braidReversal_mem_adWeightSpace_sub hu, ?_⟩)
      rw [braidReversal_mul, map_sub, braidReversal_K, braidReversal_algebraMap, map_neg,
        AddMonoidHom.neg_apply, neg_neg]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- `σ ρ = ρ̄ σ` on `U` ([Lus] 26.1.4). -/
theorem braidReversal_rho (u : QuantumGroup R v) :
    braidReversal (rho R v u) = rhoBar R v (braidReversal u) := by
  have hv := NeZero.ne v
  have hc : ∀ i : I, v ^ D.d i * v ^ (-D.dot i i) = (v ^ D.d i)⁻¹ := fun i ↦
    eq_inv_of_mul_eq_one_left (by rw [mul_right_comm]; exact zpow_dot_mul hv i)
  induction u using QuantumGroup.induction_on with
  | algebraMap c => simp
  | E i =>
    rw [rho_E, rhoE, map_smul, braidReversal_mul, braidReversal_F, Kt, braidReversal_K,
      braidReversal_E, rhoBar_E, rhoBarE, F_mul_K hv, smul_smul, map_neg, root_ktilde_eq_dot, hc]
  | F i =>
    rw [rho_F, rhoF, map_smul, braidReversal_mul, braidReversal_E, braidReversal_K, neg_neg,
      braidReversal_F, rhoBar_F, rhoBarF, Kt, E_mul_K hv, smul_smul, root_ktilde_eq_dot, hc]
  | K μ => rw [rho_K, braidReversal_K, rhoBar_K]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | mul x y hx hy =>
    rw [rho_mul, braidReversal_mul, hx, hy, braidReversal_mul x y, rhoBar_mul]

lemma braidReversal_minusHom (x : LusztigF k I) :
    braidReversal (minusHom R v x) = minusHom R v (rev k I x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes, rev_algebraMap, AlgHom.commutes, braidReversal_algebraMap]
  | grade1 i =>
    rw [show FreeAlgebra.ι k i = θ k i from rfl, minusHom_θ, rev_θ, minusHom_θ, braidReversal_F]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | mul a b ha hb => rw [map_mul, braidReversal_mul, ha, hb, rev_mul, map_mul]

namespace Modified

attribute [local instance] decEqIdx

/-- The map `ₗU_λ'' → _{-λ''}U_{-λ'}` induced by `σ`. -/
def sigmaComp (p : (Y →+ ℤ) × (Y →+ ℤ)) : Comp R v p →ₗ[k] Comp R v (-p.2, -p.1) :=
  Submodule.mapQ _ _
    (braidReversal.restrict fun _ hx ↦ braidReversal_mem_adWeightSpace_sub hx)
    (fun _ hx ↦ braidReversal_mem_modRel hx)

/-- **The map `σ : U̇ → U̇`** ([Lus] 23.1.6): `π_{λ',λ''}(u) ↦ π_{-λ'',-λ'}(σ u)`. -/
def sigma : Modified R v →ₗ[k] Modified R v :=
  DirectSum.toModule k _ _ fun p ↦ (DirectSum.lof k _ (Comp R v) (-p.2, -p.1)).comp (sigmaComp p)

lemma sigma_elt (l₁ l₂ : Y →+ ℤ) {u : QuantumGroup R v} (hu : u ∈ adWeightSpace R v (l₁ - l₂)) :
    sigma (elt l₁ l₂ u hu) =
      elt (-l₂) (-l₁) (braidReversal u) (braidReversal_mem_adWeightSpace_sub hu) := by
  rw [sigma, elt, DirectSum.toModule_lof]
  rfl

variable (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv

/-- `σ(u x) = σ(x) σ(u)` for `u ∈ U`, `x ∈ U̇`. -/
theorem sigma_leftAct (u : QuantumGroup R v) (x : Modified R v) :
    sigma (leftAct R v hv u x) = rightAct R v hv (braidReversal u) (sigma x) := by
  induction u using induction_adWeightSpace with
  | h0 => simp
  | hadd u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']
  | hhom χ u hu =>
  induction x using induction_on with
  | h0 => simp
  | hadd x x' hx hx' => simp only [map_add, hx, hx']
  | helt l₁ l₂ t ht =>
    rw [leftAct_elt hv hu, sigma_elt, sigma_elt,
      rightAct_elt hv (braidReversal_mem_adWeightSpace hu)]
    exact elt_index rfl (by abel) (braidReversal_mul _ _) _ _

omit hv in
/-- A bilinear form on `U̇` for which different components are orthogonal has
property (a) of [Lus] 26.1.2. -/
lemma one_mul_mul_one_eq_zero_of_elt {B : Modified R v →ₗ[k] Modified R v →ₗ[k] k}
    (h : ∀ l₁ l₂ m₁ m₂ a b (ha : a ∈ adWeightSpace R v (l₁ - l₂))
      (hb : b ∈ adWeightSpace R v (m₁ - m₂)), (l₁, l₂) ≠ (m₁, m₂) →
        B (elt l₁ l₂ a ha) (elt m₁ m₂ b hb) = 0)
    {l₁ l₂ m₁ m₂ : Y →+ ℤ} (hne : (l₁, l₂) ≠ (m₁, m₂)) (x y : Modified R v) :
    B (one l₁ * x * one l₂) (one m₁ * y * one m₂) = 0 := by
  induction x using induction_on with
  | h0 => simp
  | hadd x x' hx hx' => rw [mul_add, add_mul, map_add, LinearMap.add_apply, hx, hx', add_zero]
  | helt a₁ a₂ a ha =>
  rw [one_mul_mul_one]
  split_ifs with h₁
  swap; · simp
  induction y using induction_on with
  | h0 => simp
  | hadd y y' hy hy' => rw [mul_add, add_mul, map_add, hy, hy', add_zero]
  | helt b₁ b₂ b hb =>
    rw [one_mul_mul_one]
    split_ifs with h₂
    · exact h _ _ _ _ _ _ _ _ (by rw [← h₁, ← h₂]; exact hne)
    · simp

/-- **[Lus] 26.1.4**: `(σ(x), σ(y)) = (x, y)` for `x, y ∈ U̇`. -/
theorem form_sigma_sigma (x y : Modified R v) :
    form R v hv (sigma x) (sigma y) = form R v hv x y := by
  have h := eq_form hv (B := (form R v hv).compl₁₂ sigma sigma)
    (fun _ _ _ _ hne ↦ one_mul_mul_one_eq_zero_of_elt (fun l₁ l₂ m₁ m₂ a b ha hb hne ↦ by
      rw [LinearMap.compl₁₂_apply, sigma_elt, sigma_elt]
      refine form_elt_elt_of_ne hv (fun h ↦ hne ?_) _ _
      simp only [Prod.mk.injEq, neg_inj] at h ⊢
      exact ⟨h.2, h.1⟩) hne)
    (fun u x y ↦ by
      rw [LinearMap.compl₁₂_apply, LinearMap.compl₁₂_apply, sigma_leftAct, form_rightAct_left,
        ← braidReversal_rho, ← sigma_leftAct])
    (fun l x y ↦ by
      have h : ((form R v hv).compl₁₂
          (sigma ∘ₗ (leftAct R v hv ∘ₗ (minusHom R v).toLinearMap).flip (one l))
          (sigma ∘ₗ (leftAct R v hv ∘ₗ (minusHom R v).toLinearMap).flip (one l))) =
            LusztigF.form D v :=
        LinearMap.ext_basis (FreeAlgebra.wordBasis k I) (FreeAlgebra.wordBasis k I) fun w w' ↦ by
          simp only [LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearMap.flip_apply,
            AlgHom.toLinearMap_apply, wordBasis_eq_monomial]
          rw [one, leftAct_elt hv (minusHom_monomial_mem_adWeightSpace w),
            leftAct_elt hv (minusHom_monomial_mem_adWeightSpace w'), sigma_elt, sigma_elt,
            form_elt_elt]
          have h1 : braidReversal (1 : QuantumGroup R v) = 1 := by simp [braidReversal]
          split_ifs with h
          · rw [braidReversal_mul, braidReversal_mul, h1, one_mul, one_mul,
              braidReversal_minusHom, braidReversal_minusHom,
              ← mul_one (minusHom R v (rev k I (monomial k w'))), ← K_zero R v, ← mul_assoc,
              formFunctional_rho_minusHom, map_zero, zpow_zero, one_mul, LusztigF.form_rev]
          · refine (LusztigF.form_eq_zero_of_ne D v (fun hw ↦ h ?_) (monomial_mem_weightSpace w)
              (monomial_mem_weightSpace w')).symm
            rw [wordChar_eq_rootSum, wordChar_eq_rootSum, hw]
      exact LinearMap.congr_fun₂ h x y)
  exact LinearMap.congr_fun₂ h x y

end Modified

end LieLean.QuantumGroup
