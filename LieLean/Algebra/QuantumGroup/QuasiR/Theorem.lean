/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.QuasiR.Basic

/-!
# The quasi-R-matrix

Lusztig's quasi-R-matrix ([Lus] Theorem 4.1.2) over `𝕂 = ℚ(v)`, built weight by weight.
For `ν ∈ ℕ[I]` let `Θ_ν = c_ν Σ_b b⁻ ⊗ (b*)⁺ ∈ U⁻_ν ⊗ U⁺_ν`, where `b` runs over a basis of
`f_ν`, `b*` is the dual basis for the form `( , )`, and
`c_ν = ∏ᵢ (-vᵢ)^{νᵢ} = (-1)^{tr ν} v_ν`. This is the formula of [Lus] 4.1.2 (b). The element
`Θ = Σ_ν Θ_ν` of the completion of `U ⊗ U` is not formalized; its defining property
`Δ(u) Θ = Θ Δ̄(u)` ([Lus] 4.1.2 (a)) is stated on the generators `u = Eᵢ, Fᵢ, K_μ`, component by
component, where `Δ̄ = (¯ ⊗ ¯) ∘ Δ ∘ ¯` has `Δ̄(Eᵢ) = Eᵢ ⊗ 1 + K̃₋ᵢ ⊗ Eᵢ`,
`Δ̄(Fᵢ) = Fᵢ ⊗ K̃ᵢ + 1 ⊗ Fᵢ` and `Δ̄(K_μ) = K_μ ⊗ K_μ`.

## Main definitions

* `QuantumGroup.quasiRTensor`: the canonical element `Σ_b b ⊗ b*` of `f_ν ⊗ f_ν`.
* `QuantumGroup.quasiRCoeff`: the scalar `c_ν = ∏ᵢ (-vᵢ)^{νᵢ}`.
* `QuantumGroup.quasiR`: the component `Θ_ν ∈ U ⊗ U`.

## Main results

* `QuantumGroup.quasiR_eq_sum`: [Lus] 4.1.2 (b), for every basis of `f_ν`.
* `QuantumGroup.quasiR_zero`: `Θ_0 = 1 ⊗ 1`.
* `QuantumGroup.quasiR_E`, `quasiR_E_of_eq_zero`, `quasiR_F`, `quasiR_F_of_eq_zero`,
  `quasiR_K`: the components of `Δ(u) Θ = Θ Δ̄(u)` for `u = Eᵢ, Fᵢ, K_μ` ([Lus] 4.1.2 (a),
  existence). For `Eᵢ`, the component of weight `ν` in the second factor reads
  `(Eᵢ ⊗ 1) Θ_ν + (K̃ᵢ ⊗ Eᵢ) Θ_{ν-i} = Θ_ν (Eᵢ ⊗ 1) + Θ_{ν-i} (K̃₋ᵢ ⊗ Eᵢ)`.

The proof is our own and does not follow [Lus]: the identities are reduced, through the
commutators of [Lus] 3.1.6, to the adjointness of the skew derivations and multiplication by
`θᵢ` ([Lus] 1.2.13) and an exchange identity for dual bases
(`sum_tmul_dualBasis_of_adjoint`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.2.13, 3.1.6, 4.1.2.
-/

open LieLean TensorProduct

noncomputable section

/-! ### Multiplying pure tensors into `map f g` -/

namespace TensorProduct

variable {K A B M N : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

lemma tmul_mul_map (a : A) (b : B) (f : M →ₗ[K] A) (g : N →ₗ[K] B) (t : M ⊗[K] N) :
    (a ⊗ₜ[K] b) * map f g t =
      map (LinearMap.mulLeft K a ∘ₗ f) (LinearMap.mulLeft K b ∘ₗ g) t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp [mul_add, hx, hy]

lemma map_mul_tmul (a : A) (b : B) (f : M →ₗ[K] A) (g : N →ₗ[K] B) (t : M ⊗[K] N) :
    map f g t * (a ⊗ₜ[K] b) =
      map (LinearMap.mulRight K a ∘ₗ f) (LinearMap.mulRight K b ∘ₗ g) t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp [add_mul, hx, hy]

variable {P Q : Type*} [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]

lemma map_sub_left' (f₁ f₂ : M →ₗ[K] P) (g : N →ₗ[K] Q) :
    map (f₁ - f₂) g = map f₁ g - map f₂ g := by
  ext x y
  simp [sub_tmul]

lemma map_sub_right' (f : M →ₗ[K] P) (g₁ g₂ : N →ₗ[K] Q) :
    map f (g₁ - g₂) = map f g₁ - map f g₂ := by
  ext x y
  simp [tmul_sub]

lemma map_comp_apply_rTensor {S : Type*} [AddCommGroup S] [Module K S] (f : M →ₗ[K] P)
    (g : N →ₗ[K] Q) (f' : S →ₗ[K] M) (t : S ⊗[K] N) :
    map (f ∘ₗ f') g t = map f g (f'.rTensor N t) := by
  rw [← LinearMap.map_comp_rTensor]; rfl

lemma map_comp_apply_lTensor {S : Type*} [AddCommGroup S] [Module K S] (f : M →ₗ[K] P)
    (g : N →ₗ[K] Q) (g' : S →ₗ[K] N) (t : M ⊗[K] S) :
    map f (g ∘ₗ g') t = map f g (g'.lTensor M t) := by
  rw [← LinearMap.map_comp_lTensor]; rfl

end TensorProduct

namespace LieLean.QuantumGroup

open LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]

/-! ### The canonical element of `f_ν ⊗ f_ν` -/

section Tensor

variable (D : LusztigCartanDatum I)

/-- The canonical element `Σ_b b ⊗ b*` of `f_ν ⊗ f_ν ⊆ f ⊗ f`, for `b` running over a basis of
`f_ν` and `b*` the dual basis; it does not depend on the basis (`quasiRTensor_eq_sum`). -/
def quasiRTensor (ν : I →₀ ℕ) : Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧 :=
  ∑ s, (Module.finBasis 𝕂 (quotientWeightSpace D ν) s : Quotient D 𝕧) ⊗ₜ[𝕂]
    (quotientDualBasis (Module.finBasis 𝕂 (quotientWeightSpace D ν)) s : Quotient D 𝕧)

variable {D}

theorem quasiRTensor_eq_sum {ν : I →₀ ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝕂 (quotientWeightSpace D ν)) :
    quasiRTensor D ν = ∑ s, (b s : Quotient D 𝕧) ⊗ₜ[𝕂] (quotientDualBasis b s : Quotient D 𝕧) :=
  sum_tmul_dualBasis_of_adjoint _ b LinearMap.id LinearMap.id (fun _ hx ↦ hx) (fun _ hy ↦ hy)
    (fun x y ↦ quotientForm_comm D x y)

theorem quasiRTensor_zero : quasiRTensor D 0 = 1 ⊗ₜ[𝕂] 1 := by
  set b := Module.finBasis 𝕂 (quotientWeightSpace D 0)
  calc quasiRTensor D 0
      = ∑ s, quotientForm D 1 (b s) • ((1 : Quotient D 𝕧) ⊗ₜ[𝕂]
          (quotientDualBasis b s : Quotient D 𝕧)) := by
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        conv_lhs => rw [eq_smul_one_of_mem_zero (b s).2]
        rw [smul_tmul', quotientForm_comm]
    _ = 1 ⊗ₜ[𝕂] 1 := by
        simp_rw [← tmul_smul, ← tmul_sum]
        rw [← eq_sum_dualBasis_right b one_mem_quotientWeightSpace_zero]

variable (i : I)

/-- `Σ_b ᵢr(b) ⊗ b* = (θᵢ, θᵢ)⁻¹ Σ_c c ⊗ θᵢ c*`, for bases `b` of `f_{μ+i}` and `c` of `f_μ`. -/
theorem rTensor_quotientLDeriv_quasiRTensor (μ : I →₀ ℕ) :
    (quotientLDeriv D i).rTensor _ (quasiRTensor D (μ + Finsupp.single i 1)) =
      (thetaNorm D 𝕧 i)⁻¹ •
        (LinearMap.mulLeft 𝕂 (toQuotient D 𝕧 (θ 𝕂 i))).lTensor _ (quasiRTensor D μ) := by
  have h := sum_tmul_dualBasis_of_adjoint
    (Module.finBasis 𝕂 (quotientWeightSpace D (μ + Finsupp.single i 1)))
    (Module.finBasis 𝕂 (quotientWeightSpace D μ)) (quotientLDeriv D i)
    ((thetaNorm D 𝕧 i)⁻¹ • LinearMap.mulLeft 𝕂 (toQuotient D 𝕧 (θ 𝕂 i)))
    (fun _ hx ↦ quotientLDeriv_mem i hx)
    (fun _ hy ↦ Submodule.smul_mem _ _ (θ_mul_mem_quotientWeightSpace i hy))
    (fun x y ↦ quotientForm_lDeriv_eq i x y)
  simp only [quasiRTensor, map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    Finset.smul_sum, ← tmul_smul]
  simpa only [LinearMap.smul_apply, LinearMap.mulLeft_apply] using h

/-- `Σ_b rᵢ(b) ⊗ b* = (θᵢ, θᵢ)⁻¹ Σ_c c ⊗ c* θᵢ`. -/
theorem rTensor_quotientRDeriv_quasiRTensor (μ : I →₀ ℕ) :
    (quotientRDeriv D i).rTensor _ (quasiRTensor D (μ + Finsupp.single i 1)) =
      (thetaNorm D 𝕧 i)⁻¹ •
        (LinearMap.mulRight 𝕂 (toQuotient D 𝕧 (θ 𝕂 i))).lTensor _ (quasiRTensor D μ) := by
  have h := sum_tmul_dualBasis_of_adjoint
    (Module.finBasis 𝕂 (quotientWeightSpace D (μ + Finsupp.single i 1)))
    (Module.finBasis 𝕂 (quotientWeightSpace D μ)) (quotientRDeriv D i)
    ((thetaNorm D 𝕧 i)⁻¹ • LinearMap.mulRight 𝕂 (toQuotient D 𝕧 (θ 𝕂 i)))
    (fun _ hx ↦ quotientRDeriv_mem i hx)
    (fun _ hy ↦ Submodule.smul_mem _ _ (mul_θ_mem_quotientWeightSpace i hy))
    (fun x y ↦ quotientForm_rDeriv_eq i x y)
  simp only [quasiRTensor, map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    Finset.smul_sum, ← tmul_smul]
  simpa only [LinearMap.smul_apply, LinearMap.mulRight_apply] using h

/-- `Σ_b b ⊗ ᵢr(b*) = (θᵢ, θᵢ)⁻¹ Σ_c θᵢ c ⊗ c*`. -/
theorem lTensor_quotientLDeriv_quasiRTensor (μ : I →₀ ℕ) :
    (quotientLDeriv D i).lTensor _ (quasiRTensor D (μ + Finsupp.single i 1)) =
      (thetaNorm D 𝕧 i)⁻¹ •
        (LinearMap.mulLeft 𝕂 (toQuotient D 𝕧 (θ 𝕂 i))).rTensor _ (quasiRTensor D μ) := by
  have h := sum_tmul_dualBasis_of_adjoint'
    (Module.finBasis 𝕂 (quotientWeightSpace D (μ + Finsupp.single i 1)))
    (Module.finBasis 𝕂 (quotientWeightSpace D μ)) (quotientLDeriv D i)
    ((thetaNorm D 𝕧 i)⁻¹ • LinearMap.mulLeft 𝕂 (toQuotient D 𝕧 (θ 𝕂 i)))
    (fun _ hx ↦ quotientLDeriv_mem i hx)
    (fun _ hy ↦ Submodule.smul_mem _ _ (θ_mul_mem_quotientWeightSpace i hy))
    (fun x y ↦ quotientForm_lDeriv_eq i x y)
  simp only [quasiRTensor, map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    Finset.smul_sum, smul_tmul']
  simpa only [LinearMap.smul_apply, LinearMap.mulLeft_apply] using h

/-- `Σ_b b ⊗ rᵢ(b*) = (θᵢ, θᵢ)⁻¹ Σ_c c θᵢ ⊗ c*`. -/
theorem lTensor_quotientRDeriv_quasiRTensor (μ : I →₀ ℕ) :
    (quotientRDeriv D i).lTensor _ (quasiRTensor D (μ + Finsupp.single i 1)) =
      (thetaNorm D 𝕧 i)⁻¹ •
        (LinearMap.mulRight 𝕂 (toQuotient D 𝕧 (θ 𝕂 i))).rTensor _ (quasiRTensor D μ) := by
  have h := sum_tmul_dualBasis_of_adjoint'
    (Module.finBasis 𝕂 (quotientWeightSpace D (μ + Finsupp.single i 1)))
    (Module.finBasis 𝕂 (quotientWeightSpace D μ)) (quotientRDeriv D i)
    ((thetaNorm D 𝕧 i)⁻¹ • LinearMap.mulRight 𝕂 (toQuotient D 𝕧 (θ 𝕂 i)))
    (fun _ hx ↦ quotientRDeriv_mem i hx)
    (fun _ hy ↦ Submodule.smul_mem _ _ (mul_θ_mem_quotientWeightSpace i hy))
    (fun x y ↦ quotientForm_rDeriv_eq i x y)
  simp only [quasiRTensor, map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    Finset.smul_sum, smul_tmul']
  simpa only [LinearMap.smul_apply, LinearMap.mulRight_apply] using h

variable {i}

theorem rTensor_quotientLDeriv_quasiRTensor_of_eq_zero {ν : I →₀ ℕ} (hν : ν i = 0) :
    (quotientLDeriv D i).rTensor _ (quasiRTensor D ν) = 0 := by
  simp only [quasiRTensor, map_sum, LinearMap.rTensor_tmul]
  exact Finset.sum_eq_zero fun s _ ↦ by rw [quotientLDeriv_eq_zero i hν (Subtype.prop _),
    zero_tmul]

theorem rTensor_quotientRDeriv_quasiRTensor_of_eq_zero {ν : I →₀ ℕ} (hν : ν i = 0) :
    (quotientRDeriv D i).rTensor _ (quasiRTensor D ν) = 0 := by
  simp only [quasiRTensor, map_sum, LinearMap.rTensor_tmul]
  exact Finset.sum_eq_zero fun s _ ↦ by rw [quotientRDeriv_eq_zero i hν (Subtype.prop _),
    zero_tmul]

theorem lTensor_quotientLDeriv_quasiRTensor_of_eq_zero {ν : I →₀ ℕ} (hν : ν i = 0) :
    (quotientLDeriv D i).lTensor _ (quasiRTensor D ν) = 0 := by
  simp only [quasiRTensor, map_sum, LinearMap.lTensor_tmul]
  exact Finset.sum_eq_zero fun s _ ↦ by rw [quotientLDeriv_eq_zero i hν (Subtype.prop _),
    tmul_zero]

theorem lTensor_quotientRDeriv_quasiRTensor_of_eq_zero {ν : I →₀ ℕ} (hν : ν i = 0) :
    (quotientRDeriv D i).lTensor _ (quasiRTensor D ν) = 0 := by
  simp only [quasiRTensor, map_sum, LinearMap.lTensor_tmul]
  exact Finset.sum_eq_zero fun s _ ↦ by rw [quotientRDeriv_eq_zero i hν (Subtype.prop _),
    tmul_zero]

end Tensor

/-! ### The components `Θ_ν` -/

section QuasiR

variable (D : LusztigCartanDatum I)

/-- The scalar `c_ν = ∏ᵢ (-vᵢ)^{νᵢ} = (-1)^{tr ν} v_ν` of [Lus] 4.1.2 (b). -/
def quasiRCoeff (ν : I →₀ ℕ) : 𝕂 := ν.prod fun i n ↦ (-(𝕧 ^ D.d i)) ^ n

omit [Finite I] [DecidableEq I] in
@[simp] lemma quasiRCoeff_zero : quasiRCoeff D 0 = 1 := Finsupp.prod_zero_index

omit [Finite I] [DecidableEq I] in
lemma quasiRCoeff_add_single (μ : I →₀ ℕ) (i : I) :
    quasiRCoeff D (μ + Finsupp.single i 1) = -(𝕧 ^ D.d i) * quasiRCoeff D μ := by
  unfold quasiRCoeff
  rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ ↦ by rw [pow_add]), mul_comm]
  congr 1
  rw [Finsupp.prod_single_index (by simp), pow_one]

omit [Finite I] [DecidableEq I] in
/-- `(vᵢ - vᵢ⁻¹)⁻¹ (θᵢ, θᵢ)⁻¹ = vᵢ⁻¹`. -/
lemma inv_sub_inv_mul_thetaNorm_inv (i : I) :
    (𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹)⁻¹ * (thetaNorm D 𝕧 i)⁻¹ = (𝕧 ^ D.d i)⁻¹ := by
  set w : 𝕂 := 𝕧 ^ D.d i
  have hw : w ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  have hw2 : w - w⁻¹ ≠ 0 := by
    intro h
    apply ratFunc_X_not_root (D.d i * 2) (Nat.mul_pos (D.d_pos i) (by decide))
    rw [pow_mul, sq]
    change w * w = 1
    have h' : w = w⁻¹ := sub_eq_zero.mp h
    nth_rewrite 2 [h']
    exact mul_inv_cancel₀ hw
  rw [thetaNorm, inv_inv]
  have : 1 - w⁻¹ ^ 2 = w⁻¹ * (w - w⁻¹) := by field_simp
  rw [this, ← mul_assoc, mul_comm _ w⁻¹, mul_assoc, inv_mul_cancel₀ hw2, mul_one]

omit [Finite I] [DecidableEq I] in
/-- The scalar identity behind [Lus] 4.1.2 (a): `c_{μ+i} (vᵢ - vᵢ⁻¹)⁻¹ (θᵢ, θᵢ)⁻¹ + c_μ = 0`. -/
lemma quasiRCoeff_add_single_mul_add (μ : I →₀ ℕ) (i : I) :
    quasiRCoeff D (μ + Finsupp.single i 1) *
        ((𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹)⁻¹ * (thetaNorm D 𝕧 i)⁻¹) + quasiRCoeff D μ = 0 := by
  rw [inv_sub_inv_mul_thetaNorm_inv, quasiRCoeff_add_single]
  have hw : (𝕧 ^ D.d i : 𝕂) ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  field_simp
  ring

variable {D} (R : D.RootDatum Y)

/-- The component `Θ_ν = c_ν Σ_b b⁻ ⊗ (b*)⁺ ∈ U⁻_ν ⊗ U⁺_ν` of Lusztig's quasi-R-matrix
([Lus] 4.1.2). -/
def quasiR (ν : I →₀ ℕ) : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧 :=
  quasiRCoeff D ν • map (quotientMinus R).toLinearMap (quotientPlus R).toLinearMap
    (quasiRTensor D ν)

/-- [Lus] 4.1.2 (b): `Θ_ν = (-1)^{tr ν} v_ν Σ_b b⁻ ⊗ (b*)⁺` for any basis `b` of `f_ν`. -/
theorem quasiR_eq_sum {ν : I →₀ ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝕂 (quotientWeightSpace D ν)) :
    quasiR R ν = quasiRCoeff D ν •
      ∑ s, quotientMinus R (b s) ⊗ₜ[𝕂] quotientPlus R (quotientDualBasis b s) := by
  rw [quasiR, quasiRTensor_eq_sum b, map_sum]
  rfl

/-- `Θ_ν` lies in `U⁻_ν ⊗ U⁺_ν`. -/
theorem quasiR_mem_range (ν : I →₀ ℕ) :
    quasiR R ν ∈ LinearMap.range (map
      ((quotientMinus R).toLinearMap ∘ₗ (quotientWeightSpace D ν).subtype)
      ((quotientPlus R).toLinearMap ∘ₗ (quotientWeightSpace D ν).subtype)) := by
  set b := Module.finBasis 𝕂 (quotientWeightSpace D ν)
  refine ⟨quasiRCoeff D ν • ∑ s, b s ⊗ₜ[𝕂] quotientDualBasis b s, ?_⟩
  simp [quasiR, quasiRTensor, b, map_sum]

@[simp] theorem quasiR_zero : quasiR R 0 = 1 := by
  rw [quasiR, quasiRTensor_zero, quasiRCoeff_zero, one_smul, map_tmul]
  simp [Algebra.TensorProduct.one_def]

variable (i : I)

private lemma quotientPlus_comp_mulLeft :
    (quotientPlus R).toLinearMap ∘ₗ LinearMap.mulLeft 𝕂 (toQuotient D 𝕧 (θ 𝕂 i)) =
      LinearMap.mulLeft 𝕂 (E R 𝕧 i) ∘ₗ (quotientPlus R).toLinearMap := by
  ext x; simp

private lemma quotientPlus_comp_mulRight :
    (quotientPlus R).toLinearMap ∘ₗ LinearMap.mulRight 𝕂 (toQuotient D 𝕧 (θ 𝕂 i)) =
      LinearMap.mulRight 𝕂 (E R 𝕧 i) ∘ₗ (quotientPlus R).toLinearMap := by
  ext x; simp

private lemma quotientMinus_comp_mulLeft :
    (quotientMinus R).toLinearMap ∘ₗ LinearMap.mulLeft 𝕂 (toQuotient D 𝕧 (θ 𝕂 i)) =
      LinearMap.mulLeft 𝕂 (F R 𝕧 i) ∘ₗ (quotientMinus R).toLinearMap := by
  ext x; simp

private lemma quotientMinus_comp_mulRight :
    (quotientMinus R).toLinearMap ∘ₗ LinearMap.mulRight 𝕂 (toQuotient D 𝕧 (θ 𝕂 i)) =
      LinearMap.mulRight 𝕂 (F R 𝕧 i) ∘ₗ (quotientMinus R).toLinearMap := by
  ext x; simp

/-- The commutator with `Eᵢ ⊗ 1`, as an identity of linear maps `f → U` ([Lus] 3.1.6). -/
private lemma commE :
    LinearMap.mulLeft 𝕂 (E R 𝕧 i) ∘ₗ (quotientMinus R).toLinearMap -
        LinearMap.mulRight 𝕂 (E R 𝕧 i) ∘ₗ (quotientMinus R).toLinearMap =
      (𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹)⁻¹ •
        ((LinearMap.mulLeft 𝕂 (K R 𝕧 (ktilde R i)) ∘ₗ (quotientMinus R).toLinearMap) ∘ₗ
            quotientLDeriv D i -
          (LinearMap.mulRight 𝕂 (K R 𝕧 (-ktilde R i)) ∘ₗ (quotientMinus R).toLinearMap) ∘ₗ
            quotientRDeriv D i) := by
  ext y
  simpa using E_mul_quotientMinus_sub R i y

/-- The commutator with `1 ⊗ Fᵢ`, as an identity of linear maps `f → U` ([Lus] 3.1.6). -/
private lemma commF :
    LinearMap.mulLeft 𝕂 (F R 𝕧 i) ∘ₗ (quotientPlus R).toLinearMap -
        LinearMap.mulRight 𝕂 (F R 𝕧 i) ∘ₗ (quotientPlus R).toLinearMap =
      (𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹)⁻¹ •
        ((LinearMap.mulLeft 𝕂 (K R 𝕧 (-ktilde R i)) ∘ₗ (quotientPlus R).toLinearMap) ∘ₗ
            quotientLDeriv D i -
          (LinearMap.mulRight 𝕂 (K R 𝕧 (ktilde R i)) ∘ₗ (quotientPlus R).toLinearMap) ∘ₗ
            quotientRDeriv D i) := by
  ext x
  have h := F_mul_quotientPlus_sub R i x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply] at h ⊢
  rw [h, ← smul_neg, neg_sub]

/-- The commutator of `Eᵢ ⊗ 1` with `Σ_b b⁻ ⊗ (b*)⁺` over `f_{μ+i}`. -/
private lemma commE_quasiRTensor (μ : I →₀ ℕ) :
    (E R 𝕧 i ⊗ₜ[𝕂] 1) * map (quotientMinus R).toLinearMap (quotientPlus R).toLinearMap
        (quasiRTensor D (μ + Finsupp.single i 1)) -
      map (quotientMinus R).toLinearMap (quotientPlus R).toLinearMap
          (quasiRTensor D (μ + Finsupp.single i 1)) * (E R 𝕧 i ⊗ₜ[𝕂] 1) =
      ((𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹)⁻¹ * (thetaNorm D 𝕧 i)⁻¹) •
        ((K R 𝕧 (ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i) *
            map (quotientMinus R).toLinearMap (quotientPlus R).toLinearMap (quasiRTensor D μ) -
          map (quotientMinus R).toLinearMap (quotientPlus R).toLinearMap (quasiRTensor D μ) *
            (K R 𝕧 (-ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i)) := by
  rw [tmul_mul_map, map_mul_tmul, tmul_mul_map, map_mul_tmul, LinearMap.mulLeft_one,
    LinearMap.mulRight_one, LinearMap.id_comp, ← LinearMap.sub_apply, ← map_sub_left', commE,
    map_smul_left, map_sub_left', LinearMap.smul_apply, LinearMap.sub_apply,
    map_comp_apply_rTensor _ _ (quotientLDeriv D i),
    map_comp_apply_rTensor _ _ (quotientRDeriv D i),
    rTensor_quotientLDeriv_quasiRTensor, rTensor_quotientRDeriv_quasiRTensor, map_smul,
    map_smul, ← map_comp_apply_lTensor, ← map_comp_apply_lTensor, quotientPlus_comp_mulLeft,
    quotientPlus_comp_mulRight]
  simp only [smul_sub, smul_smul]

/-- The commutator of `1 ⊗ Fᵢ` with `Σ_b b⁻ ⊗ (b*)⁺` over `f_{μ+i}`. -/
private lemma commF_quasiRTensor (μ : I →₀ ℕ) :
    (1 ⊗ₜ[𝕂] F R 𝕧 i) * map (quotientMinus R).toLinearMap (quotientPlus R).toLinearMap
        (quasiRTensor D (μ + Finsupp.single i 1)) -
      map (quotientMinus R).toLinearMap (quotientPlus R).toLinearMap
          (quasiRTensor D (μ + Finsupp.single i 1)) * (1 ⊗ₜ[𝕂] F R 𝕧 i) =
      ((𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹)⁻¹ * (thetaNorm D 𝕧 i)⁻¹) •
        ((F R 𝕧 i ⊗ₜ[𝕂] K R 𝕧 (-ktilde R i)) *
            map (quotientMinus R).toLinearMap (quotientPlus R).toLinearMap (quasiRTensor D μ) -
          map (quotientMinus R).toLinearMap (quotientPlus R).toLinearMap (quasiRTensor D μ) *
            (F R 𝕧 i ⊗ₜ[𝕂] K R 𝕧 (ktilde R i))) := by
  rw [tmul_mul_map, map_mul_tmul, tmul_mul_map, map_mul_tmul, LinearMap.mulLeft_one,
    LinearMap.mulRight_one, LinearMap.id_comp, ← LinearMap.sub_apply, ← map_sub_right', commF,
    map_smul_right, map_sub_right', LinearMap.smul_apply, LinearMap.sub_apply,
    map_comp_apply_lTensor _ _ (quotientLDeriv D i),
    map_comp_apply_lTensor _ _ (quotientRDeriv D i),
    lTensor_quotientLDeriv_quasiRTensor, lTensor_quotientRDeriv_quasiRTensor, map_smul,
    map_smul, ← map_comp_apply_rTensor, ← map_comp_apply_rTensor, quotientMinus_comp_mulLeft,
    quotientMinus_comp_mulRight]
  simp only [smul_sub, smul_smul]

/-- [Lus] 4.1.2 (a) for `u = Eᵢ`, component of weight `ν = μ + i` in the second factor:
`(Eᵢ ⊗ 1) Θ_ν + (K̃ᵢ ⊗ Eᵢ) Θ_μ = Θ_ν (Eᵢ ⊗ 1) + Θ_μ (K̃₋ᵢ ⊗ Eᵢ)`. -/
theorem quasiR_E (μ : I →₀ ℕ) :
    (E R 𝕧 i ⊗ₜ[𝕂] 1) * quasiR R (μ + Finsupp.single i 1) +
        (K R 𝕧 (ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i) * quasiR R μ =
      quasiR R (μ + Finsupp.single i 1) * (E R 𝕧 i ⊗ₜ[𝕂] 1) +
        quasiR R μ * (K R 𝕧 (-ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i) := by
  rw [← sub_eq_zero]
  simp only [quasiR, mul_smul_comm, smul_mul_assoc]
  have h := commE_quasiRTensor R i μ
  set A := map (quotientMinus R).toLinearMap (quotientPlus R).toLinearMap
    (quasiRTensor D (μ + Finsupp.single i 1))
  set B := map (quotientMinus R).toLinearMap (quotientPlus R).toLinearMap (quasiRTensor D μ)
  calc _ = quasiRCoeff D (μ + Finsupp.single i 1) •
        ((E R 𝕧 i ⊗ₜ[𝕂] 1) * A - A * (E R 𝕧 i ⊗ₜ[𝕂] 1)) + quasiRCoeff D μ •
          ((K R 𝕧 (ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i) * B - B * (K R 𝕧 (-ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i)) := by
        simp only [smul_sub]; abel
    _ = 0 := by
        rw [h, smul_smul, ← add_smul, quasiRCoeff_add_single_mul_add, zero_smul]

/-- [Lus] 4.1.2 (a) for `u = Eᵢ`, component of weight `ν` with `νᵢ = 0`:
`(Eᵢ ⊗ 1) Θ_ν = Θ_ν (Eᵢ ⊗ 1)`. -/
theorem quasiR_E_of_eq_zero {ν : I →₀ ℕ} (hν : ν i = 0) :
    (E R 𝕧 i ⊗ₜ[𝕂] 1) * quasiR R ν = quasiR R ν * (E R 𝕧 i ⊗ₜ[𝕂] 1) := by
  rw [← sub_eq_zero]
  simp only [quasiR, mul_smul_comm, smul_mul_assoc, ← smul_sub]
  rw [tmul_mul_map, map_mul_tmul, LinearMap.mulLeft_one, LinearMap.mulRight_one,
    LinearMap.id_comp, ← LinearMap.sub_apply, ← map_sub_left', commE, map_smul_left,
    map_sub_left', LinearMap.smul_apply, LinearMap.sub_apply,
    map_comp_apply_rTensor _ _ (quotientLDeriv D i),
    map_comp_apply_rTensor _ _ (quotientRDeriv D i),
    rTensor_quotientLDeriv_quasiRTensor_of_eq_zero hν,
    rTensor_quotientRDeriv_quasiRTensor_of_eq_zero hν]
  simp

/-- [Lus] 4.1.2 (a) for `u = Fᵢ`, component of weight `ν = μ + i` in the first factor:
`(1 ⊗ Fᵢ) Θ_ν + (Fᵢ ⊗ K̃₋ᵢ) Θ_μ = Θ_ν (1 ⊗ Fᵢ) + Θ_μ (Fᵢ ⊗ K̃ᵢ)`. -/
theorem quasiR_F (μ : I →₀ ℕ) :
    (1 ⊗ₜ[𝕂] F R 𝕧 i) * quasiR R (μ + Finsupp.single i 1) +
        (F R 𝕧 i ⊗ₜ[𝕂] K R 𝕧 (-ktilde R i)) * quasiR R μ =
      quasiR R (μ + Finsupp.single i 1) * (1 ⊗ₜ[𝕂] F R 𝕧 i) +
        quasiR R μ * (F R 𝕧 i ⊗ₜ[𝕂] K R 𝕧 (ktilde R i)) := by
  rw [← sub_eq_zero]
  simp only [quasiR, mul_smul_comm, smul_mul_assoc]
  have h := commF_quasiRTensor R i μ
  set A := map (quotientMinus R).toLinearMap (quotientPlus R).toLinearMap
    (quasiRTensor D (μ + Finsupp.single i 1))
  set B := map (quotientMinus R).toLinearMap (quotientPlus R).toLinearMap (quasiRTensor D μ)
  calc _ = quasiRCoeff D (μ + Finsupp.single i 1) •
        ((1 ⊗ₜ[𝕂] F R 𝕧 i) * A - A * (1 ⊗ₜ[𝕂] F R 𝕧 i)) + quasiRCoeff D μ •
          ((F R 𝕧 i ⊗ₜ[𝕂] K R 𝕧 (-ktilde R i)) * B - B * (F R 𝕧 i ⊗ₜ[𝕂] K R 𝕧 (ktilde R i))) := by
        simp only [smul_sub]; abel
    _ = 0 := by
        rw [h, smul_smul, ← add_smul, quasiRCoeff_add_single_mul_add, zero_smul]

/-- [Lus] 4.1.2 (a) for `u = Fᵢ`, component of weight `ν` with `νᵢ = 0`:
`(1 ⊗ Fᵢ) Θ_ν = Θ_ν (1 ⊗ Fᵢ)`. -/
theorem quasiR_F_of_eq_zero {ν : I →₀ ℕ} (hν : ν i = 0) :
    (1 ⊗ₜ[𝕂] F R 𝕧 i) * quasiR R ν = quasiR R ν * (1 ⊗ₜ[𝕂] F R 𝕧 i) := by
  rw [← sub_eq_zero]
  simp only [quasiR, mul_smul_comm, smul_mul_assoc, ← smul_sub]
  rw [tmul_mul_map, map_mul_tmul, LinearMap.mulLeft_one, LinearMap.mulRight_one,
    LinearMap.id_comp, ← LinearMap.sub_apply, ← map_sub_right', commF, map_smul_right,
    map_sub_right', LinearMap.smul_apply, LinearMap.sub_apply,
    map_comp_apply_lTensor _ _ (quotientLDeriv D i),
    map_comp_apply_lTensor _ _ (quotientRDeriv D i),
    lTensor_quotientLDeriv_quasiRTensor_of_eq_zero hν,
    lTensor_quotientRDeriv_quasiRTensor_of_eq_zero hν]
  simp

/-- [Lus] 4.1.2 (a) for `u = K_λ`: `(K_λ ⊗ K_λ) Θ_ν = Θ_ν (K_λ ⊗ K_λ)`. -/
theorem quasiR_K (l : Y) (ν : I →₀ ℕ) :
    (K R 𝕧 l ⊗ₜ[𝕂] K R 𝕧 l) * quasiR R ν = quasiR R ν * (K R 𝕧 l ⊗ₜ[𝕂] K R 𝕧 l) := by
  rw [quasiR, mul_smul_comm, smul_mul_assoc]
  congr 1
  simp only [quasiRTensor, map_sum, Finset.mul_sum, Finset.sum_mul, map_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, AlgHom.toLinearMap_apply]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [K_mul_quotientMinus_of_mem R l (Subtype.prop _),
    K_mul_quotientPlus_of_mem R l (Subtype.prop _), smul_tmul_smul, ← zpow_add₀
      RatFunc.X_ne_zero, map_neg, neg_add_cancel, zpow_zero, one_smul]

end QuasiR

end LieLean.QuantumGroup
