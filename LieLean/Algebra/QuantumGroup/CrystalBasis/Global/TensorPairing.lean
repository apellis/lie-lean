/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.HighestWeightInnerProduct

/-!
# The pairing `δ_λ : ʷΛ_λ ⊗ Λ_λ → ℚ(v)`

For dominant `λ`, [Lus] Prop. 25.1.4 states that there is a unique homomorphism of `U`-modules
`δ_λ : ʷΛ_λ ⊗ Λ_λ → ℚ(v)`, where `U` acts on `ℚ(v)` through the counit, with
`δ_λ(ξ_{-λ} ⊗ η_λ) = 1` (a); and that for `b, b' ∈ B(λ)`, `δ_λ(b⁺ξ_{-λ} ⊗ b'⁻η_λ)` is `1` if
`b = b' = 1` and lies in `v⁻¹ℤ[v⁻¹]` otherwise (b).

Lusztig obtains `δ_λ(x ⊗ y) = [x, y)` from a pairing `[ , )` on `Λ_λ` and shows
`[x, y) = c_ν (x, y)` on `(Λ_λ)_{λ-ν}`, where `( , )` is the contravariant form of 19.1.2 and
`c_ν = ∏ᵢ (-vᵢ⁻¹)^{νᵢ}` (the sign `(-1)^{tr ν}` times a power of `v`). Here we define `δ_λ`
by this formula, `δ_λ(ξ ⊗ y) = (ξ, Ω y)` with `Ω = c_ν` on `(Λ_λ)_{λ-ν}`, and check
equivariance on the generators of `U`. Then (b) follows from [Lus] Prop. 19.3.3
(`isNegLaurent_formL_evq_sub`) and `c_ν ∈ v⁻¹ℤ[v⁻¹]` for `ν ≠ 0`, as in Lusztig's proof.

## Main definitions

* `tensorPairingCoef`: `c_ν = ∏ᵢ (-vᵢ⁻¹)^{νᵢ}`;
* `tensorPairingOp`: the operator `Ω` of `Λ_λ`, equal to `c_ν` on `(Λ_λ)_{λ-ν}`;
* `tensorPairing`: `δ_λ`.

## Main results

* `tensorPairing_act`, `tensorPairing_hwv`, `eq_tensorPairing`: **[Lus] Prop. 25.1.4 (a)**;
* `tensorPairing_tensorBasis_one`, `isNegLaurent_tensorPairing_tensorBasis`:
  **[Lus] Prop. 25.1.4 (b)**.

## Implementation notes

The uniqueness in (a) is proved directly (our own route): a counit-equivariant form vanishing
at `ξ_{-λ} ⊗ η_λ` vanishes on `ξ_{-λ}⁺ ⊗ η_λ` (apply the `Eᵢ`), then on everything (apply the
`Fᵢ` and the `K_μ`), instead of through the surjectivity in [Lus] 23.3.6. The root datum is
`X`-regular, where Lusztig assumes it `Y`-regular.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 19.1.2, 19.3.3, 25.1.4.
-/

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop LusztigF TensorProduct

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular)

/-! ### The scalars `c_ν` -/

section Coef

variable (D) in
/-- `c_ν = ∏ᵢ (-vᵢ⁻¹)^{νᵢ}`, `vᵢ = v^{dᵢ}`. -/
def tensorPairingCoef (ν : I →₀ ℕ) : 𝕂 := ν.prod fun i n ↦ (-(𝕧 ^ D.d i)⁻¹) ^ n

omit [Finite I] [DecidableEq I] in
@[simp] lemma tensorPairingCoef_zero : tensorPairingCoef D 0 = 1 := Finsupp.prod_zero_index

omit [Finite I] [DecidableEq I] in
lemma tensorPairingCoef_add (ν ν' : I →₀ ℕ) :
    tensorPairingCoef D (ν + ν') = tensorPairingCoef D ν * tensorPairingCoef D ν' :=
  Finsupp.prod_add_index' (fun _ ↦ pow_zero _) fun _ _ _ ↦ pow_add _ _ _

omit [Finite I] [DecidableEq I] in
lemma tensorPairingCoef_single (i : I) (n : ℕ) :
    tensorPairingCoef D (Finsupp.single i n) = (-(𝕧 ^ D.d i)⁻¹) ^ n :=
  Finsupp.prod_single_index (pow_zero _)

omit [Finite I] [DecidableEq I] in
/-- `c_{ν + i} = c_ν · (-vᵢ⁻¹)`. -/
lemma tensorPairingCoef_add_single (ν : I →₀ ℕ) (i : I) :
    tensorPairingCoef D (ν + Finsupp.single i 1) = tensorPairingCoef D ν * -(𝕧 ^ D.d i)⁻¹ := by
  rw [tensorPairingCoef_add, tensorPairingCoef_single, pow_one]

lemma IsIntInv.pow {c : 𝕂} (hc : IsIntInv c) (n : ℕ) : IsIntInv (c ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact isIntInv_one
  | succ n ih => rw [pow_succ]; exact ih.mul hc

omit [Finite I] [DecidableEq I] in
lemma isNegLaurent_neg_inv_pow (i : I) {n : ℕ} (hn : n ≠ 0) :
    IsNegLaurent ((-(𝕧 ^ D.d i)⁻¹) ^ n) := by
  have hd : IsNegLaurent (-(𝕧 ^ D.d i)⁻¹) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_one_of_ne_zero (D.d_pos i).ne'
    rw [hd, ← inv_pow, pow_succ']
    exact (isNegLaurent_inv_X.mul_isIntInv (isNegLaurent_inv_X.isIntInv.pow d)).neg
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [pow_succ']
  exact hd.mul_isIntInv (hd.isIntInv.pow n)

omit [Finite I] [DecidableEq I] in
/-- `c_ν ∈ ℤ[v⁻¹]`. -/
lemma isIntInv_tensorPairingCoef (ν : I →₀ ℕ) : IsIntInv (tensorPairingCoef D ν) := by
  rw [tensorPairingCoef, Finsupp.prod]
  refine Finset.prod_induction _ IsIntInv (fun _ _ ha hb ↦ ha.mul hb) isIntInv_one fun i _ ↦ ?_
  by_cases hn : ν i = 0
  · rw [hn, pow_zero]; exact isIntInv_one
  · exact (isNegLaurent_neg_inv_pow i hn).isIntInv

omit [Finite I] [DecidableEq I] in
/-- `c_ν ∈ v⁻¹ℤ[v⁻¹]` for `ν ≠ 0`. -/
lemma isNegLaurent_tensorPairingCoef {ν : I →₀ ℕ} (hν : ν ≠ 0) :
    IsNegLaurent (tensorPairingCoef D ν) := by
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hν
  rw [← Finsupp.single_add_erase i ν, tensorPairingCoef_add, tensorPairingCoef_single]
  exact (isNegLaurent_neg_inv_pow i hi).mul_isIntInv (isIntInv_tensorPairingCoef _)

end Coef

/-! ### The operator `Ω` -/

section Op

variable (Λ : Dom R)

/-- The operator of `Λ_λ` equal to `c_ν` on `(Λ_λ)_{λ-ν}`. -/
def tensorPairingOp : IrreducibleModule R 𝕧 Λ.1 →ₗ[𝕂] IrreducibleModule R 𝕧 Λ.1 :=
  (canonicalBasisHWBasis Λ hR).constr 𝕂 fun b ↦ tensorPairingCoef D (hwbWt Λ b) • evq hvt Λ b

lemma tensorPairingOp_of_mem {μ : I →₀ ℕ} {y : IrreducibleModule R 𝕧 Λ.1} (hy : y ∈ hwWt Λ μ) :
    tensorPairingOp hR Λ y = tensorPairingCoef D μ • y := by
  set B := canonicalBasisHWBasis Λ hR
  conv_rhs => rw [← B.linearCombination_repr y]
  rw [tensorPairingOp, Module.Basis.constr_apply, Finsupp.linearCombination_apply,
    Finsupp.smul_sum]
  refine Finsupp.sum_congr fun b _ ↦ ?_
  by_cases hb : hwbWt Λ b = μ
  · rw [hb, canonicalBasisHWBasis_apply, smul_comm]
  · rw [repr_eq_zero_of_mem_hwWt hR Λ hy b hb, zero_smul, zero_smul, smul_zero]

end Op

/-! ### The pairing `δ_λ` -/

section Pairing

variable (Λ : Dom R)

/-- `δ_λ(x ⊗ y) = (x, Ω y)`, where `x ∈ ʷΛ_λ` is viewed in `Λ_λ` ([Lus] 25.1.4). -/
def tensorPairing : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ.1 →ₗ[𝕂] 𝕂 :=
  TensorProduct.lift ((formL hvt hR Λ).compl₁₂
    (ChevalleyTwist.toTwist R 𝕧 (IrreducibleModule R 𝕧 Λ.1)).symm.toLinearMap
    (tensorPairingOp hR Λ))

lemma tensorPairing_tmul (m y : IrreducibleModule R 𝕧 Λ.1) :
    tensorPairing hR Λ (ChevalleyTwist.toTwist R 𝕧 _ m ⊗ₜ[𝕂] y) =
      formL hvt hR Λ m (tensorPairingOp hR Λ y) := by
  simp [tensorPairing]

include hR in
/-- Two forms on `ʷΛ_λ ⊗ Λ_λ` agree if they agree on `x ⊗ y`, `y` a weight vector. -/
lemma tensor_ext_hwWt {φ ψ : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ.1 →ₗ[𝕂] 𝕂}
    (h : ∀ (m : IrreducibleModule R 𝕧 Λ.1) (μ : I →₀ ℕ) (y : IrreducibleModule R 𝕧 Λ.1),
      y ∈ hwWt Λ μ → φ (ChevalleyTwist.toTwist R 𝕧 _ m ⊗ₜ[𝕂] y) =
        ψ (ChevalleyTwist.toTwist R 𝕧 _ m ⊗ₜ[𝕂] y)) : φ = ψ := by
  refine TensorProduct.ext' fun x y ↦ ?_
  obtain ⟨m, rfl⟩ := (ChevalleyTwist.toTwist R 𝕧 (IrreducibleModule R 𝕧 Λ.1)).surjective x
  have hy : y ∈ Submodule.span 𝕂 (Set.range (canonicalBasisHWBasis Λ hR)) := by
    rw [Module.Basis.span_eq]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    rw [canonicalBasisHWBasis_apply]
    exact h m _ _ (evq_mem_hwWt hR Λ b)
  | zero => rw [tmul_zero, map_zero, map_zero]
  | add a b _ _ ha hb => rw [tmul_add, map_add, map_add, ha, hb]
  | smul c a _ ha => rw [tmul_smul, map_smul, map_smul, ha]

omit [Finite I] in
lemma TensorModule.act_E_tmul {M₁ M₂ : Type*} [AddCommGroup M₁] [Module 𝕂 M₁]
    [Module (QuantumGroup R 𝕧) M₁]
    [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₁] [AddCommGroup M₂] [Module 𝕂 M₂]
    [Module (QuantumGroup R 𝕧) M₂] [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂] (i : I)
    (x : M₁) (y : M₂) :
    TensorModule.act R 𝕧 M₁ M₂ (E R 𝕧 i) (x ⊗ₜ[𝕂] y) =
      (E R 𝕧 i • x) ⊗ₜ[𝕂] y + (Kt R 𝕧 i • x) ⊗ₜ[𝕂] (E R 𝕧 i • y) :=
  TensorModule.E_smul_tmul i x y

omit [Finite I] in
lemma TensorModule.act_F_tmul {M₁ M₂ : Type*} [AddCommGroup M₁] [Module 𝕂 M₁]
    [Module (QuantumGroup R 𝕧) M₁]
    [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₁] [AddCommGroup M₂] [Module 𝕂 M₂]
    [Module (QuantumGroup R 𝕧) M₂] [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂] (i : I)
    (x : M₁) (y : M₂) :
    TensorModule.act R 𝕧 M₁ M₂ (F R 𝕧 i) (x ⊗ₜ[𝕂] y) =
      (F R 𝕧 i • x) ⊗ₜ[𝕂] (K R 𝕧 (-ktilde R i) • y) + x ⊗ₜ[𝕂] (F R 𝕧 i • y) :=
  TensorModule.F_smul_tmul i x y

omit [Finite I] in
lemma TensorModule.act_K_tmul {M₁ M₂ : Type*} [AddCommGroup M₁] [Module 𝕂 M₁]
    [Module (QuantumGroup R 𝕧) M₁]
    [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₁] [AddCommGroup M₂] [Module 𝕂 M₂]
    [Module (QuantumGroup R 𝕧) M₂] [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂] (μ : Y)
    (x : M₁) (y : M₂) :
    TensorModule.act R 𝕧 M₁ M₂ (K R 𝕧 μ) (x ⊗ₜ[𝕂] y) = (K R 𝕧 μ • x) ⊗ₜ[𝕂] (K R 𝕧 μ • y) :=
  TensorModule.K_smul_tmul μ x y

omit [Finite I] [DecidableEq I] in
private lemma inv_pow_d_mul (i : I) : (𝕧 ^ D.d i)⁻¹ * 𝕧 ^ D.d i = 1 :=
  inv_mul_cancel₀ (pow_ne_zero _ (NeZero.ne 𝕧))

omit [Finite I] in
lemma formL_K_smul_left (μ : Y) (a w : IrreducibleModule R 𝕧 Λ.1) :
    formL hvt hR Λ (K R 𝕧 μ • a) w = formL hvt hR Λ a (K R 𝕧 μ • w) := by
  rw [IrreducibleModule.isContravariant_form hR (pow_ne_one_of_transcendental' hvt), rho_K]

omit [Finite I] in
lemma formL_F_smul_left (i : I) (a w : IrreducibleModule R 𝕧 Λ.1) :
    formL hvt hR Λ (F R 𝕧 i • a) w =
      𝕧 ^ D.d i * formL hvt hR Λ a (K R 𝕧 (-ktilde R i) • E R 𝕧 i • w) := by
  rw [IrreducibleModule.isContravariant_form hR (pow_ne_one_of_transcendental' hvt), rho_F,
    rhoF, smul_assoc, mul_smul, map_smul, smul_eq_mul]

/-- `δ_λ ∘ Eᵢ = 0`. -/
lemma tensorPairing_comp_act_E (i : I) :
    tensorPairing hR Λ ∘ₗ TensorModule.act R 𝕧 _ _ (E R 𝕧 i) =
      counit R 𝕧 (E R 𝕧 i) • tensorPairing hR Λ := by
  refine tensor_ext_hwWt hR Λ fun m μ y hy ↦ ?_
  rw [LinearMap.comp_apply, TensorModule.act_E_tmul, ChevalleyTwist.smul_toTwist,
    ChevalleyTwist.smul_toTwist, chevalley_E, chevalley_K, map_add, tensorPairing_tmul,
    tensorPairing_tmul, counit_E, zero_smul, LinearMap.zero_apply, tensorPairingOp_of_mem hR Λ hy,
    LinearMap.map_smul _ (tensorPairingCoef D μ), formL_F_smul_left, smul_eq_mul]
  have hE : plusHom R 𝕧 (θ 𝕂 i) = E R 𝕧 i := by simp
  by_cases hμ : Finsupp.single i 1 ≤ μ
  · have hEy : E R 𝕧 i • y ∈ hwWt Λ (μ - Finsupp.single i 1) := by
      rw [← hE]; exact plusHom_smul_mem_hwWt Λ hμ (θ_mem_weightSpace i) hy
    rw [tensorPairingOp_of_mem hR Λ hEy,
      LinearMap.map_smul _ (tensorPairingCoef D (μ - Finsupp.single i 1)), formL_K_smul_left,
      smul_eq_mul,
      ← tsub_add_cancel_of_le hμ, tensorPairingCoef_add_single, add_tsub_cancel_right]
    linear_combination (-(tensorPairingCoef D (μ - Finsupp.single i 1) *
      (formL hvt hR Λ) m (K R 𝕧 (-ktilde R i) • E R 𝕧 i • y))) * inv_pow_d_mul i
  · have hEy : E R 𝕧 i • y = 0 := by
      rw [← hE]; exact plusHom_smul_hwWt_eq_zero hR Λ hμ (θ_mem_weightSpace i) hy
    simp [hEy]

/-- `δ_λ ∘ Fᵢ = 0`. -/
lemma tensorPairing_comp_act_F (i : I) :
    tensorPairing hR Λ ∘ₗ TensorModule.act R 𝕧 _ _ (F R 𝕧 i) =
      counit R 𝕧 (F R 𝕧 i) • tensorPairing hR Λ := by
  refine tensor_ext_hwWt hR Λ fun m μ y hy ↦ ?_
  have hs := IrreducibleModule.form_comm hR (pow_ne_one_of_transcendental' hvt) (Λ := Λ.1)
  have hFy : F R 𝕧 i • y ∈ hwWt Λ (μ + Finsupp.single i 1) := by
    have h := F_smul_mem_weightSpace hy i
    rw [hwWt, R.rootSum_add, R.rootSum_single, one_smul, ← sub_sub]
    exact h
  have hFm : formL hvt hR Λ m (F R 𝕧 i • y) =
      𝕧 ^ D.d i * formL hvt hR Λ (E R 𝕧 i • m) (K R 𝕧 (-ktilde R i) • y) := by
    rw [hs, formL_F_smul_left, ← formL_K_smul_left, hs]
  rw [LinearMap.comp_apply, TensorModule.act_F_tmul, ChevalleyTwist.smul_toTwist, chevalley_F,
    map_add, tensorPairing_tmul, tensorPairing_tmul, counit_F, zero_smul, LinearMap.zero_apply,
    tensorPairingOp_of_mem hR Λ (K_smul_mem_weightSpace hy _), tensorPairingOp_of_mem hR Λ hFy,
    tensorPairingCoef_add_single, LinearMap.map_smul _ (tensorPairingCoef D μ),
    LinearMap.map_smul _ (tensorPairingCoef D μ * -(𝕧 ^ D.d i)⁻¹), hFm, smul_eq_mul, smul_eq_mul]
  linear_combination (-(tensorPairingCoef D μ *
    (formL hvt hR Λ) (E R 𝕧 i • m) (K R 𝕧 (-ktilde R i) • y))) * inv_pow_d_mul i

/-- `δ_λ ∘ K_ν = δ_λ`. -/
lemma tensorPairing_comp_act_K (ν : Y) :
    tensorPairing hR Λ ∘ₗ TensorModule.act R 𝕧 _ _ (K R 𝕧 ν) =
      counit R 𝕧 (K R 𝕧 ν) • tensorPairing hR Λ := by
  refine tensor_ext_hwWt hR Λ fun m μ y hy ↦ ?_
  rw [LinearMap.comp_apply, TensorModule.act_K_tmul, ChevalleyTwist.smul_toTwist, chevalley_K,
    tensorPairing_tmul, LinearMap.smul_apply, tensorPairing_tmul, counit_K, one_smul,
    tensorPairingOp_of_mem hR Λ (K_smul_mem_weightSpace hy _), tensorPairingOp_of_mem hR Λ hy,
    LinearMap.map_smul _ (tensorPairingCoef D μ), LinearMap.map_smul _ (tensorPairingCoef D μ),
    formL_K_smul_left, ← mul_smul, K_add, neg_add_cancel, K_zero, one_smul]

/-- **[Lus] Prop. 25.1.4 (a)**, existence: `δ_λ` is a homomorphism of `U`-modules, `U` acting on
`ℚ(v)` through the counit. -/
theorem tensorPairing_act (u : QuantumGroup R 𝕧) (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ.1) :
    tensorPairing hR Λ (TensorModule.act R 𝕧 _ _ u z) = counit R 𝕧 u * tensorPairing hR Λ z := by
  suffices h : tensorPairing hR Λ ∘ₗ TensorModule.act R 𝕧 _ _ u =
      counit R 𝕧 u • tensorPairing hR Λ from LinearMap.congr_fun h z
  induction u using QuantumGroup.induction_on with
  | algebraMap c =>
    refine LinearMap.ext fun z ↦ ?_
    rw [LinearMap.comp_apply, AlgHom.commutes, Module.algebraMap_end_apply, map_smul,
      AlgHom.commutes, LinearMap.smul_apply, Algebra.algebraMap_self, RingHom.id_apply]
  | E i => exact tensorPairing_comp_act_E hR Λ i
  | F i => exact tensorPairing_comp_act_F hR Λ i
  | K ν => exact tensorPairing_comp_act_K hR Λ ν
  | add x y hx hy => rw [map_add, LinearMap.comp_add, hx, hy, map_add, add_smul]
  | mul x y hx hy =>
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hx, LinearMap.smul_comp, hy,
      smul_smul, map_mul]

/-- **[Lus] Prop. 25.1.4 (a)**: `δ_λ(ξ_{-λ} ⊗ η_λ) = 1`. -/
theorem tensorPairing_hwv :
    tensorPairing hR Λ (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
      IrreducibleModule.hwv R 𝕧 Λ.1) = 1 := by
  have h : IrreducibleModule.hwv R 𝕧 Λ.1 ∈ hwWt Λ 0 := by
    rw [hwWt, R.rootSum_zero, sub_zero]
    exact IrreducibleModule.hwv_mem_weightSpace
  rw [tensorPairing_tmul, tensorPairingOp_of_mem hR Λ h, tensorPairingCoef_zero, one_smul,
    IrreducibleModule.form_hwv]

omit [Finite I] in
/-- A counit-equivariant form on `ʷΛ_λ ⊗ Λ_λ` vanishing at `ξ_{-λ} ⊗ η_λ` is zero. -/
lemma eq_zero_of_counit_equivariant {φ : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ.1 →ₗ[𝕂] 𝕂}
    (hφ : ∀ u z, φ (TensorModule.act R 𝕧 _ _ u z) = counit R 𝕧 u * φ z)
    (h₁ : φ (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
      IrreducibleModule.hwv R 𝕧 Λ.1) = 0) : φ = 0 := by
  have hη : ∀ m, φ (ChevalleyTwist.toTwist R 𝕧 _ m ⊗ₜ[𝕂] IrreducibleModule.hwv R 𝕧 Λ.1) = 0 := by
    intro m
    induction m using hw_induction with
    | zero => rw [map_zero, zero_tmul, map_zero]
    | add a b ha hb => rw [map_add, add_tmul, map_add, ha, hb, add_zero]
    | smul c a ha => rw [map_smul, ← smul_tmul', map_smul, ha, smul_zero]
    | hwv => exact h₁
    | F i a _ =>
      have h := hφ (E R 𝕧 i) (ChevalleyTwist.toTwist R 𝕧 _ a ⊗ₜ[𝕂] IrreducibleModule.hwv R 𝕧 Λ.1)
      rwa [TensorModule.act_E_tmul, IrreducibleModule.E_smul_hwv, tmul_zero, add_zero,
        ChevalleyTwist.smul_toTwist, chevalley_E,
        counit_E, zero_mul] at h
  have hall : ∀ y (x : TwL Λ), φ (x ⊗ₜ[𝕂] y) = 0 := by
    intro y
    induction y using hw_induction with
    | zero => intro x; rw [tmul_zero, map_zero]
    | add a b ha hb => intro x; rw [tmul_add, map_add, ha, hb, add_zero]
    | smul c a ha => intro x; rw [tmul_smul, map_smul, ha, smul_zero]
    | hwv =>
      intro x
      obtain ⟨m, rfl⟩ := (ChevalleyTwist.toTwist R 𝕧 (IrreducibleModule R 𝕧 Λ.1)).surjective x
      exact hη m
    | F i a ha =>
      intro x
      have hF := hφ (F R 𝕧 i) (x ⊗ₜ[𝕂] a)
      have hK := hφ (K R 𝕧 (-ktilde R i)) ((K R 𝕧 (ktilde R i) • F R 𝕧 i • x) ⊗ₜ[𝕂] a)
      rw [TensorModule.act_K_tmul, ← mul_smul, K_add, neg_add_cancel, K_zero, one_smul, ha,
        mul_zero] at hK
      rwa [TensorModule.act_F_tmul, map_add, hK, zero_add, counit_F, zero_mul] at hF
  exact TensorProduct.ext' fun x y ↦ hall y x

/-- **[Lus] Prop. 25.1.4 (a)**, uniqueness. -/
theorem eq_tensorPairing {φ : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ.1 →ₗ[𝕂] 𝕂}
    (hφ : ∀ u z, φ (TensorModule.act R 𝕧 _ _ u z) = counit R 𝕧 u * φ z)
    (h₁ : φ (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
      IrreducibleModule.hwv R 𝕧 Λ.1) = 1) : φ = tensorPairing hR Λ := by
  refine sub_eq_zero.1 (eq_zero_of_counit_equivariant Λ (fun u z ↦ ?_) ?_)
  · rw [LinearMap.sub_apply, LinearMap.sub_apply, hφ, tensorPairing_act, mul_sub]
  · rw [LinearMap.sub_apply, h₁, tensorPairing_hwv, sub_self]

end Pairing

/-! ### [Lus] Prop. 25.1.4 (b) -/

section Basis

variable (Λ : Dom R)

/-- The only element of `B(λ)` of weight `0` is `1`. -/
lemma eq_hwOne_of_hwbWt_eq_zero {b : canonicalBasisHW D Λ} (hb : hwbWt Λ b = 0) :
    b = hwOne Λ := by
  have hs := ((mem_canonicalBasis_iff D).1 (canonicalBasisHW_subset D Λ b.2)).choose_spec
  have hb' : ((mem_canonicalBasis_iff D).1 (canonicalBasisHW_subset D Λ b.2)).choose = 0 := hb
  generalize ((mem_canonicalBasis_iff D).1 (canonicalBasisHW_subset D Λ b.2)).choose = ν at hs hb'
  subst hb'
  obtain ⟨b', hb'⟩ := hs
  exact Subtype.ext (hb'.trans (negGlobal_zero D b'))

lemma tensorPairing_tensorBasis (b b' : canonicalBasisHW D Λ) :
    tensorPairing hR Λ (tensorBasis hR Λ Λ (b, b')) =
      tensorPairingCoef D (hwbWt Λ b') * formL hvt hR Λ (evq hvt Λ b) (evq hvt Λ b') := by
  rw [tensorBasis_apply, tensorPairing_tmul, tensorPairingOp_of_mem hR Λ (evq_mem_hwWt hR Λ b'),
    map_smul, smul_eq_mul]

/-- **[Lus] Prop. 25.1.4 (b)**: `δ_λ(1⁺ξ_{-λ} ⊗ 1⁻η_λ) = 1`. -/
theorem tensorPairing_tensorBasis_one :
    tensorPairing hR Λ (tensorBasis hR Λ Λ (hwOne Λ, hwOne Λ)) = 1 := by
  have h : evq hvt Λ (hwOne Λ : Um D 𝕧) = IrreducibleModule.hwv R 𝕧 Λ.1 := ev_one Λ.1
  rw [tensorBasis_apply]
  dsimp only
  rw [h]
  exact tensorPairing_hwv hR Λ

open Classical in
/-- **[Lus] Prop. 25.1.4 (b)**: `δ_λ(b⁺ξ_{-λ} ⊗ b'⁻η_λ) ∈ v⁻¹ℤ[v⁻¹]` unless `b = b' = 1`. -/
theorem isNegLaurent_tensorPairing_tensorBasis {b b' : canonicalBasisHW D Λ}
    (h : (b, b') ≠ (hwOne Λ, hwOne Λ)) :
    IsNegLaurent (tensorPairing hR Λ (tensorBasis hR Λ Λ (b, b'))) := by
  have hf := isNegLaurent_formL_evq_sub hR Λ b b'
  rw [tensorPairing_tensorBasis]
  by_cases hbb : b = b'
  · subst hbb
    simp only [↓reduceIte] at hf
    have hw : hwbWt Λ b ≠ 0 := fun hw ↦ h (by rw [eq_hwOne_of_hwbWt_eq_zero Λ hw])
    have hi : IsIntInv (formL hvt hR Λ (evq hvt Λ b) (evq hvt Λ b)) := by
      simpa using hf.isIntInv.add isIntInv_one
    exact (isNegLaurent_tensorPairingCoef hw).mul_isIntInv hi
  · simp only [hbb, ↓reduceIte, sub_zero] at hf
    rw [mul_comm]
    exact hf.mul_isIntInv (isIntInv_tensorPairingCoef _)

end Basis

end LieLean.QuantumGroup
