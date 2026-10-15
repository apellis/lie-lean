/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorPairing

/-!
# The map `χ' : ʷΛ_{λ+λ'} → ʷΛ_{λ'} ⊗ ʷΛ_λ`

For dominant `λ, λ'`, [Lus] Prop. 25.1.3 states that there is a unique homomorphism of
`U`-modules `χ' : ʷΛ_{λ+λ'} → ʷΛ_{λ'} ⊗ ʷΛ_λ` with `χ'(ξ_{-λ-λ'}) = ξ_{-λ'} ⊗ ξ_{-λ}` (a), and
that `χ'(b⁺ξ_{-λ-λ'}) = Σ f(b; b₁, b₂) b₂⁺ξ_{-λ'} ⊗ b₁⁺ξ_{-λ}` with the coefficients
`f(b; b₁, b₂)` of [Lus] 25.1.2 (b). Lusztig deduces it from 25.1.2 and the identity
`Δ ∘ ω = ᵗ(ω ⊗ ω) ∘ Δ`; here `χ'` is defined as `χ` followed by the flip and the twists, and
its equivariance is checked on the generators of `U`.

In `ʷΛ_λ` we write `b⁺ξ_{-λ}` for the image of `b⁻η_λ` (the twist by the Chevalley involution
`ω` exchanges `b⁺` and `b⁻`).

## Main definitions

* `tensorTwistEquiv`: `Λ_λ ⊗ Λ_{λ'} ≅ ʷΛ_{λ'} ⊗ ʷΛ_λ`, `x ⊗ y ↦ ʷy ⊗ ʷx`;
* `tensorEmbTw`: `χ'`;
* `twTensorBasis`: the basis `b₂⁺ξ_{-λ'} ⊗ b₁⁺ξ_{-λ}` of `ʷΛ_{λ'} ⊗ ʷΛ_λ`.

## Main results

* `tensorEmbTw_act`, `tensorEmbTw_hwv`, `eq_tensorEmbTw`: **[Lus] Prop. 25.1.3 (a)**;
* `repr_tensorEmbTw`, `isIntInv_repr_tensorEmbTw_evq`, `repr_tensorEmbTw_evq_one`:
  **[Lus] Prop. 25.1.3 (b)**.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 25.1.2, 25.1.3.
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

section Twist

variable (Λ Λ' : Dom R)

/-- `Λ_λ ⊗ Λ_{λ'} ≅ ʷΛ_{λ'} ⊗ ʷΛ_λ`, `x ⊗ y ↦ ʷy ⊗ ʷx`. -/
def tensorTwistEquiv : (IrreducibleModule R 𝕧 Λ.1 ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) ≃ₗ[𝕂]
    TwL Λ' ⊗[𝕂] TwL Λ :=
  (TensorProduct.comm 𝕂 _ _).trans
    (TensorProduct.congr (ChevalleyTwist.toTwist R 𝕧 _) (ChevalleyTwist.toTwist R 𝕧 _))

omit [Finite I] in
@[simp] lemma tensorTwistEquiv_tmul (x : IrreducibleModule R 𝕧 Λ.1)
    (y : IrreducibleModule R 𝕧 Λ'.1) :
    tensorTwistEquiv Λ Λ' (x ⊗ₜ y) =
      ChevalleyTwist.toTwist R 𝕧 _ y ⊗ₜ ChevalleyTwist.toTwist R 𝕧 _ x := rfl

omit [Finite I] in
/-- The flip intertwines `ω(u)` on `Λ_λ ⊗ Λ_{λ'}` with `u` on `ʷΛ_{λ'} ⊗ ʷΛ_λ`
(`Δ ∘ ω = ᵗ(ω ⊗ ω) ∘ Δ`). -/
lemma tensorTwistEquiv_act (u : QuantumGroup R 𝕧)
    (z : IrreducibleModule R 𝕧 Λ.1 ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) :
    tensorTwistEquiv Λ Λ' (TensorModule.act R 𝕧 (IrreducibleModule R 𝕧 Λ.1)
      (IrreducibleModule R 𝕧 Λ'.1) (chevalley R 𝕧 u) z) =
      TensorModule.act R 𝕧 (TwL Λ') (TwL Λ) u (tensorTwistEquiv Λ Λ' z) := by
  induction u using QuantumGroup.induction_on generalizing z with
  | algebraMap c => simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | E i =>
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      simp only [chevalley_E, TensorModule.act_F_tmul, TensorModule.act_E_tmul, map_add,
        tensorTwistEquiv_tmul, ChevalleyTwist.smul_toTwist, chevalley_K]
      exact add_comm _ _
  | F i =>
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      simp only [chevalley_F, TensorModule.act_F_tmul, TensorModule.act_E_tmul, map_add,
        tensorTwistEquiv_tmul, ChevalleyTwist.smul_toTwist, chevalley_K, neg_neg]
      exact add_comm _ _
  | K μ =>
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      simp only [chevalley_K, TensorModule.act_K_tmul, tensorTwistEquiv_tmul,
        ChevalleyTwist.smul_toTwist]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | mul x y hx hy => simp only [map_mul, Module.End.mul_apply, hx, hy]

/-- The basis `b₂⁺ξ_{-λ'} ⊗ b₁⁺ξ_{-λ}` of `ʷΛ_{λ'} ⊗ ʷΛ_λ`, indexed by `B(λ') × B(λ)`. -/
def twTensorBasis : Module.Basis (canonicalBasisHW D Λ' × canonicalBasisHW D Λ) 𝕂
    (TwL Λ' ⊗[𝕂] TwL Λ) :=
  ((canonicalBasisHWBasis Λ' hR).map (ChevalleyTwist.toTwist R 𝕧 _)).tensorProduct
    ((canonicalBasisHWBasis Λ hR).map (ChevalleyTwist.toTwist R 𝕧 _))

lemma twTensorBasis_apply (p : canonicalBasisHW D Λ' × canonicalBasisHW D Λ) :
    twTensorBasis hR Λ Λ' p = ChevalleyTwist.toTwist R 𝕧 _ (evq hvt Λ' p.1) ⊗ₜ[𝕂]
      ChevalleyTwist.toTwist R 𝕧 _ (evq hvt Λ p.2) := by
  rw [twTensorBasis, Module.Basis.tensorProduct_apply', Module.Basis.map_apply,
    Module.Basis.map_apply, canonicalBasisHWBasis_apply, canonicalBasisHWBasis_apply]

/-- The coordinates of `ʷy ⊗ ʷx` at `(b₂, b₁)` are those of `x ⊗ y` at `(b₁, b₂)`. -/
lemma repr_tensorTwistEquiv
    (z : TensorModule 𝕂 (IrreducibleModule R 𝕧 Λ.1) (IrreducibleModule R 𝕧 Λ'.1))
    (p : canonicalBasisHW D Λ' × canonicalBasisHW D Λ) :
    (twTensorBasis hR Λ Λ').repr (tensorTwistEquiv Λ Λ' ((TensorModule.mk _ _).symm z)) p =
      (tensorHWBasis hR Λ Λ').repr z p.swap := by
  have h : (twTensorBasis hR Λ Λ').coord p ∘ₗ (tensorTwistEquiv Λ Λ').toLinearMap ∘ₗ
      (TensorModule.mk _ _).symm.toLinearMap = (tensorHWBasis hR Λ Λ').coord p.swap :=
    (tensorHWBasis hR Λ Λ').ext fun q ↦ by
      classical
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Module.Basis.coord_apply,
        Module.Basis.coord_apply, Module.Basis.repr_self, tensorHWBasis_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, tensorTwistEquiv_tmul]
      rw [show ChevalleyTwist.toTwist R 𝕧 _ (evq hvt Λ' q.2) ⊗ₜ[𝕂]
          ChevalleyTwist.toTwist R 𝕧 _ (evq hvt Λ q.1) = twTensorBasis hR Λ Λ' q.swap from
          (twTensorBasis_apply hR Λ Λ' q.swap).symm, Module.Basis.repr_self,
        Finsupp.single_apply, Finsupp.single_apply]
      exact if_congr ⟨fun h ↦ by rw [← h, Prod.swap_swap], fun h ↦ by rw [h, Prod.swap_swap]⟩
        rfl rfl
  exact LinearMap.congr_fun h z

end Twist

section Emb

variable (Λ Λ' : Dom R)

/-- **[Lus] Prop. 25.1.3** `χ' : ʷΛ_{λ+λ'} → ʷΛ_{λ'} ⊗ ʷΛ_λ`: `χ` followed by the flip and
the twists. -/
def tensorEmbTw : TwL (Λ + Λ') →ₗ[𝕂] TwL Λ' ⊗[𝕂] TwL Λ :=
  (tensorTwistEquiv Λ Λ').toLinearMap ∘ₗ (TensorModule.mk _ _).symm.toLinearMap ∘ₗ
    (tensorEmb hvt hR Λ.2 Λ'.2).restrictScalars 𝕂 ∘ₗ
      (ChevalleyTwist.toTwist R 𝕧 (IrreducibleModule R 𝕧 (Λ + Λ').1)).symm.toLinearMap

lemma tensorEmbTw_toTwist (m : IrreducibleModule R 𝕧 (Λ + Λ').1) :
    tensorEmbTw hR Λ Λ' (ChevalleyTwist.toTwist R 𝕧 _ m) =
      tensorTwistEquiv Λ Λ' ((TensorModule.mk _ _).symm (tensorEmb hvt hR Λ.2 Λ'.2 m)) := by
  simp [tensorEmbTw]

/-- **[Lus] Prop. 25.1.3 (a)**: `χ'` is a homomorphism of `U`-modules. -/
theorem tensorEmbTw_act (u : QuantumGroup R 𝕧) (x : TwL (Λ + Λ')) :
    tensorEmbTw hR Λ Λ' (u • x) = TensorModule.act R 𝕧 _ _ u (tensorEmbTw hR Λ Λ' x) := by
  obtain ⟨m, rfl⟩ := (ChevalleyTwist.toTwist R 𝕧 (IrreducibleModule R 𝕧 (Λ + Λ').1)).surjective x
  rw [ChevalleyTwist.smul_toTwist, tensorEmbTw_toTwist, tensorEmbTw_toTwist, map_smul,
    ← tensorTwistEquiv_act]
  rfl

/-- **[Lus] Prop. 25.1.3 (a)**: `χ'(ξ_{-λ-λ'}) = ξ_{-λ'} ⊗ ξ_{-λ}`. -/
theorem tensorEmbTw_hwv :
    tensorEmbTw hR Λ Λ' (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 (Λ + Λ').1)) =
      ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ'.1) ⊗ₜ[𝕂]
        ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) := by
  rw [tensorEmbTw_toTwist]
  erw [tensorEmb_hwv hvt hR Λ.2 Λ'.2]
  rfl

omit [Finite I] in
/-- A homomorphism of `U`-modules out of `ʷΛ_λ` vanishing at `ξ_{-λ}` is zero. -/
lemma eq_zero_of_twist_equivariant {M : Type*} [AddCommGroup M] [Module 𝕂 M] (Λ : Dom R)
    (ψ : TwL Λ →ₗ[𝕂] M) (act : QuantumGroup R 𝕧 → Module.End 𝕂 M)
    (hψ : ∀ u x, ψ (u • x) = act u (ψ x))
    (h₀ : ψ (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1)) = 0) : ψ = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨m, rfl⟩ := (ChevalleyTwist.toTwist R 𝕧 (IrreducibleModule R 𝕧 Λ.1)).surjective x
  induction m using hw_induction with
  | zero => simp
  | add a b ha hb =>
    rw [LinearMap.zero_apply] at ha hb ⊢
    rw [map_add, map_add, ha, hb, add_zero]
  | smul c a ha =>
    rw [LinearMap.zero_apply] at ha ⊢
    rw [map_smul, map_smul, ha, smul_zero]
  | hwv => exact h₀
  | F i b hb =>
    rw [LinearMap.zero_apply] at hb ⊢
    have h := hψ (E R 𝕧 i) (ChevalleyTwist.toTwist R 𝕧 _ b)
    rw [ChevalleyTwist.smul_toTwist, chevalley_E] at h
    rw [h, hb, map_zero]

/-- **[Lus] Prop. 25.1.3 (a)**, uniqueness. -/
theorem eq_tensorEmbTw (ψ : TwL (Λ + Λ') →ₗ[𝕂] TwL Λ' ⊗[𝕂] TwL Λ)
    (hψ : ∀ u x, ψ (u • x) = TensorModule.act R 𝕧 _ _ u (ψ x))
    (h₁ : ψ (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 (Λ + Λ').1)) =
      ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ'.1) ⊗ₜ[𝕂]
        ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1)) :
    ψ = tensorEmbTw hR Λ Λ' := by
  refine sub_eq_zero.1 (eq_zero_of_twist_equivariant (Λ + Λ') _
    (fun u ↦ TensorModule.act R 𝕧 _ _ u) (fun u x ↦ ?_) ?_)
  · rw [LinearMap.sub_apply, LinearMap.sub_apply, hψ, tensorEmbTw_act, map_sub]
  · rw [LinearMap.sub_apply, h₁, tensorEmbTw_hwv, sub_self]

/-- The coordinates of `χ'(b⁺ξ_{-λ-λ'})` at `(b₂, b₁)` are the coordinates `f(b; b₁, b₂)` of
`χ(b⁻η_{λ+λ'})`. -/
theorem repr_tensorEmbTw (m : IrreducibleModule R 𝕧 (Λ + Λ').1)
    (p : canonicalBasisHW D Λ' × canonicalBasisHW D Λ) :
    (twTensorBasis hR Λ Λ').repr (tensorEmbTw hR Λ Λ' (ChevalleyTwist.toTwist R 𝕧 _ m)) p =
      (tensorHWBasis hR Λ Λ').repr (tensorEmb hvt hR Λ.2 Λ'.2 m) p.swap := by
  rw [tensorEmbTw_toTwist, repr_tensorTwistEquiv]

/-- **[Lus] Prop. 25.1.3 (b)**: the coordinates of `χ'(b⁺ξ_{-λ-λ'})` lie in `ℤ[v⁻¹]`. -/
theorem isIntInv_repr_tensorEmbTw_evq {x : Um D 𝕧} (hx : x ∈ canonicalBasis D)
    (p : canonicalBasisHW D Λ' × canonicalBasisHW D Λ) :
    IsIntInv ((twTensorBasis hR Λ Λ').repr
      (tensorEmbTw hR Λ Λ' (ChevalleyTwist.toTwist R 𝕧 _ (evq hvt (Λ + Λ') x))) p) := by
  rw [repr_tensorEmbTw]
  exact isIntInv_repr_tensorEmb_evq hR Λ Λ' hx p.swap

open Classical in
/-- **[Lus] Prop. 25.1.3 (b)**: `f(b; 1, b₂) = δ_{b,b₂}`. -/
theorem repr_tensorEmbTw_evq_one {x : Um D 𝕧} (hx : x ∈ canonicalBasis D)
    (b₂ : canonicalBasisHW D Λ') :
    (twTensorBasis hR Λ Λ').repr
      (tensorEmbTw hR Λ Λ' (ChevalleyTwist.toTwist R 𝕧 _ (evq hvt (Λ + Λ') x))) (b₂, hwOne Λ) =
      if (b₂ : Um D 𝕧) = x then 1 else 0 := by
  rw [repr_tensorEmbTw]
  exact repr_tensorEmb_evq_one hR Λ Λ' hx b₂

end Emb

end LieLean.QuantumGroup
