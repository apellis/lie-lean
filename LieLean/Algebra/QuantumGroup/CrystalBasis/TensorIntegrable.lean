/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.TensorModule
import LieLean.Algebra.QuantumGroup.CrystalBasis.Integrable
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorSl2

/-!
# Kashiwara operators on tensor products of integrable `U_q(𝔤)`-modules

The library's coproduct is Lusztig's: `Δ Eᵢ = Eᵢ ⊗ 1 + K̃ᵢ ⊗ Eᵢ`, `Δ Fᵢ = Fᵢ ⊗ K̃ᵢ⁻¹ + 1 ⊗ Fᵢ`.
The tensor product rule for crystal bases (`QuantumGroup.IntegrableSl2.tensor`) is stated with
Kashiwara's coproduct `E ⊗ K⁻¹ + 1 ⊗ E`, `F ⊗ 1 + K ⊗ F`. The two are related by exchanging the
factors and replacing `q` by `q⁻¹`: at a node `i`, the flip `x ⊗ y ↦ y ⊗ x` identifies
`M₁ ⊗ M₂` (`QuantumGroup.TensorModule`) as a `U_{vᵢ}(𝔰𝔩₂)`-module with Kashiwara's tensor
product of `M₂` and `M₁` regarded as `U_{vᵢ⁻¹}(𝔰𝔩₂)`-modules.

## Main definitions and results

* `QuantumGroup.IntegrableSl2.inv`: an integrable `U_q(𝔰𝔩₂)`-module is an integrable
  `U_{q⁻¹}(𝔰𝔩₂)`-module with the same `E`, `F` and grading; its Kashiwara operators are the same
  (`QuantumGroup.IntegrableSl2.inv_eTilde`, `QuantumGroup.IntegrableSl2.inv_fTilde`).
* `QuantumGroup.TensorModule.comm_kashiwaraE`, `QuantumGroup.TensorModule.comm_kashiwaraF`: under
  the flip, `ẽᵢ`, `f̃ᵢ` on `M₁ ⊗ M₂` are the Kashiwara operators of
  `IntegrableSl2.tensor (M₂ at vᵢ⁻¹) (M₁ at vᵢ⁻¹)`.
-/

open TensorProduct

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  (V : IntegrableSl2 q M)

omit [AddCommGroup M] [Module k M] in
lemma qInt_inv (n : ℕ) : qInt q⁻¹ n = qInt q n := by
  rw [qInt, qInt, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [Finset.mem_range] at hs
  rw [inv_inv, mul_comm]
  congr 2
  omega

omit [AddCommGroup M] [Module k M] in
lemma qFactorial_inv (n : ℕ) : qFactorial q⁻¹ n = qFactorial q n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [qFactorial, qFactorial, ih, qInt_inv]

omit [AddCommGroup M] [Module k M] in
lemma qIntZ_inv (n : ℤ) : qIntZ q⁻¹ n = qIntZ q n := by
  simp only [qIntZ, inv_zpow', neg_neg, inv_inv]
  rw [← neg_sub, ← neg_sub q, neg_div_neg_eq]

/-- An integrable `U_q(𝔰𝔩₂)`-module as an integrable `U_{q⁻¹}(𝔰𝔩₂)`-module (same `E`, `F` and
grading; the relation `EF - FE = [n]` is symmetric in `q ↔ q⁻¹`). -/
def inv : IntegrableSl2 q⁻¹ M where
  E := V.E
  F := V.F
  wt := V.wt
  iSupIndep_wt := V.iSupIndep_wt
  iSup_wt := V.iSup_wt
  E_mem := V.E_mem
  F_mem := V.F_mem
  E_F_sub h := by rw [qIntZ_inv]; exact V.E_F_sub h
  exists_E_pow_eq_zero := V.exists_E_pow_eq_zero
  exists_F_pow_eq_zero := V.exists_F_pow_eq_zero

@[simp] lemma inv_E : V.inv.E = V.E := rfl

@[simp] lemma inv_F : V.inv.F = V.F := rfl

@[simp] lemma inv_wt : V.inv.wt = V.wt := rfl

lemma inv_dF (a : ℕ) : V.inv.dF a = V.dF a := by
  simp only [dF, qDivPow, qFactorial_inv, inv_F]

variable {V} (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)

omit hq0 in
include hq in
lemma inv_pow_ne_one : ∀ n : ℕ, 0 < n → q⁻¹ ^ n ≠ 1 := fun n hn h ↦
  hq n hn (by rwa [inv_pow, inv_eq_one] at h)

/-- The Kashiwara operator `ẽ` does not change when `q` is replaced by `q⁻¹`. -/
theorem inv_eTilde : V.inv.eTilde (inv_ne_zero hq0) (inv_pow_ne_one hq) = V.eTilde hq0 hq := by
  refine V.ext_wt fun n m hm ↦ ?_
  refine eq_on_wt (V := V) hq0 hq (V.inv.eTilde (inv_ne_zero hq0) (inv_pow_ne_one hq))
    (V.eTilde hq0 hq) ?_ hm
  intro p j η hjp _ hη hEη
  rcases j with _ | j
  · rw [dF_zero, eTilde_of_primitive hq0 hq hEη hη,
      eTilde_of_primitive (V := V.inv) (inv_ne_zero hq0) (inv_pow_ne_one hq) hEη hη]
  · rw [← inv_dF, eTilde_dF_succ (V := V.inv) (inv_ne_zero hq0) (inv_pow_ne_one hq) hEη hη
      (by omega)]
    simp only [inv_dF]
    rw [eTilde_dF_succ hq0 hq hEη hη (by omega)]

/-- The Kashiwara operator `f̃` does not change when `q` is replaced by `q⁻¹`. -/
theorem inv_fTilde : V.inv.fTilde (inv_ne_zero hq0) (inv_pow_ne_one hq) = V.fTilde hq0 hq := by
  refine V.ext_wt fun n m hm ↦ ?_
  refine eq_on_wt (V := V) hq0 hq (V.inv.fTilde (inv_ne_zero hq0) (inv_pow_ne_one hq))
    (V.fTilde hq0 hq) ?_ hm
  intro p j η hjp _ hη hEη
  rw [← inv_dF, fTilde_dF (V := V.inv) (inv_ne_zero hq0) (inv_pow_ne_one hq) hEη hη]
  simp only [inv_dF]
  rw [fTilde_dF hq0 hq hEη hη]

end IntegrableSl2

namespace TensorModule

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁]
  [AddCommGroup M₂] [Module k M₂] [Module (QuantumGroup R v) M₂]
  [IsScalarTower k (QuantumGroup R v) M₂]
  (h₁ : IsIntegrable R v M₁) (h₂ : IsIntegrable R v M₂) (i : I)

variable (M₁ M₂) in
/-- The flip `M₁ ⊗ M₂ → M₂ ⊗ M₁`, `x ⊗ y ↦ y ⊗ x`. -/
noncomputable def flip : TensorModule k M₁ M₂ ≃ₗ[k] M₂ ⊗[k] M₁ :=
  (mk M₁ M₂).symm.trans (TensorProduct.comm k M₁ M₂)

lemma flip_mk_tmul (x : M₁) (y : M₂) : flip M₁ M₂ (mk M₁ M₂ (x ⊗ₜ[k] y)) = y ⊗ₜ[k] x := rfl

/-- Kashiwara's tensor product of `M₂` and `M₁` at the node `i`, as `U_{vᵢ⁻¹}(𝔰𝔩₂)`-modules. -/
noncomputable abbrev flipSl2 : IntegrableSl2 (v ^ D.d i)⁻¹ (M₂ ⊗[k] M₁) :=
  IntegrableSl2.tensor (nodeSl2 R v M₂ hv h₂ i).inv (nodeSl2 R v M₁ hv h₁ i).inv
    (inv_ne_zero (pow_d_ne_zero i)) (IntegrableSl2.inv_pow_ne_one (pow_d_ne_one hv i))

lemma flip_E (z : TensorModule k M₁ M₂) :
    flip M₁ M₂ (E R v i • z) = (flipSl2 hv h₁ h₂ i).E (flip M₁ M₂ z) := by
  obtain ⟨z, rfl⟩ := (mk M₁ M₂).surjective z
  have := IntegrableSl2.ext_tensor (V₁ := nodeSl2 R v M₁ hv h₁ i) (V₂ := nodeSl2 R v M₂ hv h₂ i)
    (f := (flip M₁ M₂).toLinearMap ∘ₗ
      LieLean.QuantumGroup.act R v (TensorModule k M₁ M₂) (E R v i) ∘ₗ (mk M₁ M₂).toLinearMap)
    (g := (flipSl2 hv h₁ h₂ i).E ∘ₗ (flip M₁ M₂).toLinearMap ∘ₗ (mk M₁ M₂).toLinearMap)
    (fun a b x y hx hy ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Algebra.lsmul_coe, E_smul_tmul,
        map_add, flip_mk_tmul]
      rw [IntegrableSl2.tensor_E, IntegrableSl2.tensorE_tmul (V₁ := (nodeSl2 R v M₂ hv h₂ i).inv)
        (V₂ := (nodeSl2 R v M₁ hv h₁ i).inv) y (b := a) hx, Kt_smul_of_mem_nodeWt hx]
      simp only [IntegrableSl2.inv_E, nodeSl2_E, Algebra.lsmul_coe, tmul_smul, inv_zpow',
        neg_neg]
      exact add_comm _ _)
  exact LinearMap.congr_fun this z

lemma flip_F (z : TensorModule k M₁ M₂) :
    flip M₁ M₂ (F R v i • z) = (flipSl2 hv h₁ h₂ i).F (flip M₁ M₂ z) := by
  obtain ⟨z, rfl⟩ := (mk M₁ M₂).surjective z
  have := IntegrableSl2.ext_tensor (V₁ := nodeSl2 R v M₁ hv h₁ i) (V₂ := nodeSl2 R v M₂ hv h₂ i)
    (f := (flip M₁ M₂).toLinearMap ∘ₗ
      LieLean.QuantumGroup.act R v (TensorModule k M₁ M₂) (F R v i) ∘ₗ (mk M₁ M₂).toLinearMap)
    (g := (flipSl2 hv h₁ h₂ i).F ∘ₗ (flip M₁ M₂).toLinearMap ∘ₗ (mk M₁ M₂).toLinearMap)
    (fun a b x y hx hy ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Algebra.lsmul_coe, F_smul_tmul,
        map_add, flip_mk_tmul]
      rw [IntegrableSl2.tensor_F, IntegrableSl2.tensorF_tmul (V₁ := (nodeSl2 R v M₂ hv h₂ i).inv)
        (V₂ := (nodeSl2 R v M₁ hv h₁ i).inv) (a := b) hy x, K_neg_ktilde_smul_of_mem_nodeWt hy]
      simp only [IntegrableSl2.inv_F, nodeSl2_F, Algebra.lsmul_coe, smul_tmul', inv_zpow']
      exact add_comm _ _)
  exact LinearMap.congr_fun this z

lemma flip_mem_wt {n : ℤ} {z : TensorModule k M₁ M₂}
    (hz : z ∈ nodeWt R v (TensorModule k M₁ M₂) i n) :
    flip M₁ M₂ z ∈ (flipSl2 hv h₁ h₂ i).wt n := by
  rw [IntegrableSl2.mem_tensor_wt]
  have := IntegrableSl2.ext_tensor (V₁ := nodeSl2 R v M₁ hv h₁ i) (V₂ := nodeSl2 R v M₂ hv h₂ i)
    (f := (flip M₁ M₂).toLinearMap ∘ₗ
      LieLean.QuantumGroup.act R v (TensorModule k M₁ M₂) (K R v (-ktilde R i)) ∘ₗ
      (mk M₁ M₂).toLinearMap)
    (g := IntegrableSl2.tensorK (nodeSl2 R v M₂ hv h₂ i).inv (nodeSl2 R v M₁ hv h₁ i).inv ∘ₗ
      (flip M₁ M₂).toLinearMap ∘ₗ (mk M₁ M₂).toLinearMap)
    (fun a b x y hx hy ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Algebra.lsmul_coe, K_smul_tmul,
        flip_mk_tmul]
      rw [IntegrableSl2.tensorK_tmul (V₁ := (nodeSl2 R v M₂ hv h₂ i).inv)
        (V₂ := (nodeSl2 R v M₁ hv h₁ i).inv) hy hx (inv_ne_zero (pow_d_ne_zero i)),
        K_neg_ktilde_smul_of_mem_nodeWt hx, K_neg_ktilde_smul_of_mem_nodeWt hy, smul_tmul_smul,
        ← zpow_add₀ (pow_d_ne_zero i), inv_zpow', neg_add, add_comm])
  obtain ⟨w, rfl⟩ := (mk M₁ M₂).surjective z
  have h := LinearMap.congr_fun this w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Algebra.lsmul_coe] at h
  rw [← h, K_neg_ktilde_smul_of_mem_nodeWt hz, map_smul, inv_zpow']

/-- Under the flip, `ẽᵢ` on `M₁ ⊗ M₂` is Kashiwara's `ẽ` on `M₂ ⊗ M₁` at `vᵢ⁻¹`. -/
theorem flip_kashiwaraE (z : TensorModule k M₁ M₂) :
    flip M₁ M₂ (kashiwaraE R v (TensorModule k M₁ M₂) hv (isIntegrable h₁ h₂) i z) =
      (flipSl2 hv h₁ h₂ i).eTilde (inv_ne_zero (pow_d_ne_zero i))
        (IntegrableSl2.inv_pow_ne_one (pow_d_ne_one hv i)) (flip M₁ M₂ z) := by
  rw [kashiwaraE, ← IntegrableSl2.inv_eTilde]
  exact IntegrableSl2.map_eTilde _ _ _ (flip M₁ M₂).toLinearMap (flip_E hv h₁ h₂ i)
    (flip_F hv h₁ h₂ i) (fun n m hm ↦ flip_mem_wt hv h₁ h₂ i hm) z

/-- Under the flip, `f̃ᵢ` on `M₁ ⊗ M₂` is Kashiwara's `f̃` on `M₂ ⊗ M₁` at `vᵢ⁻¹`. -/
theorem flip_kashiwaraF (z : TensorModule k M₁ M₂) :
    flip M₁ M₂ (kashiwaraF R v (TensorModule k M₁ M₂) hv (isIntegrable h₁ h₂) i z) =
      (flipSl2 hv h₁ h₂ i).fTilde (inv_ne_zero (pow_d_ne_zero i))
        (IntegrableSl2.inv_pow_ne_one (pow_d_ne_one hv i)) (flip M₁ M₂ z) := by
  rw [kashiwaraF, ← IntegrableSl2.inv_fTilde]
  exact IntegrableSl2.map_fTilde _ _ _ (flip M₁ M₂).toLinearMap (flip_E hv h₁ h₂ i)
    (flip_F hv h₁ h₂ i) (fun n m hm ↦ flip_mem_wt hv h₁ h₂ i hm) z

end TensorModule

end LieLean.QuantumGroup
