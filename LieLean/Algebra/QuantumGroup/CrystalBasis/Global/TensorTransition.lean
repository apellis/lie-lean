/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorEmbTwist

/-!
# The transition maps `t : ʷΛ_{λ+λ'} ⊗ Λ_{λ'+λ''} → ʷΛ_λ ⊗ Λ_{λ''}`

For dominant `λ, λ', λ''`, [Lus] 25.1.5 defines a homomorphism of `U`-modules
`t : ʷΛ_{λ+λ'} ⊗ Λ_{λ'+λ''} → ʷΛ_λ ⊗ Λ_{λ''}` as the composition of `χ' ⊗ χ` (25.1.3, 25.1.2)
with `1 ⊗ δ_{λ'} ⊗ 1` (25.1.4). Here the source is `ʷΛ_{λ'+λ} ⊗ Λ_{λ'+λ''}`, since `χ'` of
`TensorEmbTwist` maps `ʷΛ_{λ'+λ}` to `ʷΛ_λ ⊗ ʷΛ_{λ'}`.

[Lus] Lemma 25.1.6 states that, modulo `v⁻¹ℒ_{λ,λ''}`, `t` maps `b⁺ξ_{-λ-λ'} ⊗ b''⁻η_{λ'+λ''}` to
`b⁺ξ_{-λ} ⊗ b''⁻η_{λ''}` when `b ∈ B(λ)`, `b'' ∈ B(λ'')`, and to `0` otherwise, and that `t` is
surjective. The surjectivity uses that `ξ_{-λ} ⊗ η_{λ'}` generates `ʷΛ_λ ⊗ Λ_{λ'}`, which is
part of [Lus] Prop. 23.3.6; we prove this generation directly by applying the `Eᵢ`, `Fᵢ` and
`K_μ` (our own route; Lusztig deduces it from the description of `U̇1_ζ`).

## Main definitions

* `tensorContract`: `(a ⊗ b) ⊗ (c ⊗ d) ↦ δ_{λ'}(b ⊗ c) a ⊗ d`;
* `tensorTransition`: the map `t`.

## Main results

* `exists_act_tmul_hwv_eq`: `ξ_{-λ} ⊗ η_{λ'}` generates `ʷΛ_λ ⊗ Λ_{λ'}` (cf. [Lus] 23.3.6);
* `tensorTransition_act`: `t` is a homomorphism of `U`-modules ([Lus] 25.1.5);
* `tensorTransition_hwv`: `t(ξ_{-λ'-λ} ⊗ η_{λ'+λ''}) = ξ_{-λ} ⊗ η_{λ''}`;
* `repr_tensorTransition_sub`, `tensorTransition_sub_mem_tensorLatNeg`,
  `tensorTransition_mem_tensorLatNeg`, `surjective_tensorTransition`:
  **[Lus] Lemma 25.1.6 (a), (b), (c)**.

As for 25.1.2 and 25.1.4, the root datum is assumed `X`-regular, where Lusztig assumes it
`Y`-regular.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.3.6, 25.1.5, 25.1.6.
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

/-! ### Generation by `ξ ⊗ η` -/

section Generation

variable (Λ Λ' : Dom R)

omit [Finite I] in
/-- `ξ_{-λ} ⊗ η_{λ'}` generates `ʷΛ_λ ⊗ Λ_{λ'}` as a `U`-module (the surjectivity in
[Lus] Prop. 23.3.6; our own proof, by applying the generators). -/
theorem exists_act_tmul_hwv_eq (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) :
    ∃ u, TensorModule.act R 𝕧 _ _ u
      (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
        IrreducibleModule.hwv R 𝕧 Λ'.1) = z := by
  set z₀ := ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
    IrreducibleModule.hwv R 𝕧 Λ'.1
  set S : Submodule 𝕂 (TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) :=
    LinearMap.range ((LinearMap.applyₗ z₀) ∘ₗ
      (TensorModule.act R 𝕧 (TwL Λ) (IrreducibleModule R 𝕧 Λ'.1)).toLinearMap)
  have hS : ∀ w, w ∈ S ↔ ∃ u, TensorModule.act R 𝕧 _ _ u z₀ = w := fun w ↦ by
    simp [S]
  have hact : ∀ u w, w ∈ S → TensorModule.act R 𝕧 _ _ u w ∈ S := by
    rintro u w hw
    obtain ⟨u', rfl⟩ := (hS w).1 hw
    exact (hS _).2 ⟨u * u', by rw [map_mul, Module.End.mul_apply]⟩
  have hη : ∀ y, ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂] y ∈ S := by
    intro y
    induction y using hw_induction with
    | zero => rw [tmul_zero]; exact S.zero_mem
    | add a b ha hb => rw [tmul_add]; exact S.add_mem ha hb
    | smul c a ha => rw [tmul_smul]; exact S.smul_mem c ha
    | hwv => exact (hS _).2 ⟨1, by rw [map_one, Module.End.one_apply]⟩
    | F i b hb =>
      have h := hact (F R 𝕧 i) _ hb
      rwa [TensorModule.act_F_tmul, ChevalleyTwist.smul_toTwist, chevalley_F,
        IrreducibleModule.E_smul_hwv, map_zero, zero_tmul, zero_add] at h
  have hm : ∀ m y, ChevalleyTwist.toTwist R 𝕧 _ m ⊗ₜ[𝕂] y ∈ S := by
    intro m
    induction m using hw_induction with
    | zero => intro y; rw [map_zero, zero_tmul]; exact S.zero_mem
    | add a b ha hb => intro y; rw [map_add, add_tmul]; exact S.add_mem (ha y) (hb y)
    | smul c a ha => intro y; rw [LinearEquiv.map_smul, ← smul_tmul']; exact S.smul_mem c (ha y)
    | hwv => exact hη
    | F i b hb =>
      intro y
      have h₁ := hact (E R 𝕧 i) _ (hb y)
      have h₂ := hact (Kt R 𝕧 i) _ (hb (K R 𝕧 (-ktilde R i) • E R 𝕧 i • y))
      rw [TensorModule.act_E_tmul] at h₁
      rw [TensorModule.act_K_tmul, ← mul_smul, K_add, add_neg_cancel, K_zero,
        one_smul] at h₂
      have h := S.sub_mem h₁ h₂
      rwa [add_sub_cancel_right, ChevalleyTwist.smul_toTwist, chevalley_E] at h
  refine (hS z).1 ?_
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => exact S.add_mem ha hb
  | tmul x y =>
    obtain ⟨m, rfl⟩ := (ChevalleyTwist.toTwist R 𝕧 (IrreducibleModule R 𝕧 Λ.1)).surjective x
    exact hm m y

end Generation


/-! ### The contraction `1 ⊗ δ ⊗ 1` -/

section Contract

variable {M₁ M₂ M₃ M₄ : Type*} [AddCommGroup M₁] [Module 𝕂 M₁] [Module (QuantumGroup R 𝕧) M₁]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₁] [AddCommGroup M₂] [Module 𝕂 M₂]
  [Module (QuantumGroup R 𝕧) M₂] [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂] [AddCommGroup M₃]
  [Module 𝕂 M₃] [Module (QuantumGroup R 𝕧) M₃] [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₃]
  [AddCommGroup M₄] [Module 𝕂 M₄] [Module (QuantumGroup R 𝕧) M₄]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₄]

variable (M₁ M₄) in
/-- `(a ⊗ b) ⊗ (c ⊗ d) ↦ δ(b ⊗ c) a ⊗ d`; for `δ = δ_{λ'}` this is the map `1 ⊗ δ_{λ'} ⊗ 1`
of [Lus] 25.1.5. -/
def tensorContract (δ : M₂ ⊗[𝕂] M₃ →ₗ[𝕂] 𝕂) :
    (M₁ ⊗[𝕂] M₂) ⊗[𝕂] (M₃ ⊗[𝕂] M₄) →ₗ[𝕂] M₁ ⊗[𝕂] M₄ :=
  TensorProduct.map ((TensorProduct.rid 𝕂 M₁).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id δ) LinearMap.id ∘ₗ
    (TensorProduct.tensorTensorTensorAssoc 𝕂 _ _ _ _).toLinearMap

omit [Finite I] [DecidableEq I] [Module (QuantumGroup R 𝕧) M₁]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₁] [Module (QuantumGroup R 𝕧) M₂]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂] [Module (QuantumGroup R 𝕧) M₃]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₃] [Module (QuantumGroup R 𝕧) M₄]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₄] in
lemma tensorContract_tmul (δ : M₂ ⊗[𝕂] M₃ →ₗ[𝕂] 𝕂) (a : M₁) (b : M₂) (c : M₃) (d : M₄) :
    tensorContract M₁ M₄ δ ((a ⊗ₜ[𝕂] b) ⊗ₜ[𝕂] (c ⊗ₜ[𝕂] d)) = δ (b ⊗ₜ[𝕂] c) • (a ⊗ₜ[𝕂] d) := by
  simp [tensorContract, tensorTensorTensorAssoc_tmul, smul_tmul']

variable {δ : M₂ ⊗[𝕂] M₃ →ₗ[𝕂] 𝕂}
  (hδ : ∀ u w, δ (TensorModule.act R 𝕧 M₂ M₃ u w) = counit R 𝕧 u * δ w)
include hδ

omit [Finite I] in
/-- The contraction intertwines `Eᵢ`. -/
lemma tensorContract_E (i : I) (P : M₁ ⊗[𝕂] M₂) (Q : M₃ ⊗[𝕂] M₄) :
    tensorContract M₁ M₄ δ (TensorModule.act R 𝕧 _ _ (E R 𝕧 i) P ⊗ₜ[𝕂] Q +
      TensorModule.act R 𝕧 _ _ (Kt R 𝕧 i) P ⊗ₜ[𝕂] TensorModule.act R 𝕧 _ _ (E R 𝕧 i) Q) =
      TensorModule.act R 𝕧 _ _ (E R 𝕧 i) (tensorContract M₁ M₄ δ (P ⊗ₜ[𝕂] Q)) := by
  induction P using TensorProduct.inductionOn with
  | add P P' hP hP' =>
    simp only [map_add, add_tmul] at hP hP' ⊢
    rw [← hP, ← hP']
    abel
  | tmul a b =>
    induction Q using TensorProduct.inductionOn with
    | add Q Q' hQ hQ' =>
      simp only [map_add, tmul_add] at hQ hQ' ⊢
      rw [← hQ, ← hQ']
      abel
    | tmul c d =>
      have hE := hδ (E R 𝕧 i) (b ⊗ₜ[𝕂] c)
      have hK := hδ (Kt R 𝕧 i) (b ⊗ₜ[𝕂] c)
      rw [TensorModule.act_E_tmul, map_add, counit_E, zero_mul] at hE
      rw [TensorModule.act_K_tmul, counit_K, one_mul] at hK
      rw [TensorModule.act_E_tmul, TensorModule.act_K_tmul, TensorModule.act_E_tmul, add_tmul,
        tmul_add, map_add, map_add, map_add, tensorContract_tmul, tensorContract_tmul,
        tensorContract_tmul, tensorContract_tmul, tensorContract_tmul, map_smul,
        TensorModule.act_E_tmul, hK, eq_neg_of_add_eq_zero_right hE, neg_smul, smul_add]
      abel

omit [Finite I] in
/-- The contraction intertwines `Fᵢ`. -/
lemma tensorContract_F (i : I) (P : M₁ ⊗[𝕂] M₂) (Q : M₃ ⊗[𝕂] M₄) :
    tensorContract M₁ M₄ δ (TensorModule.act R 𝕧 _ _ (F R 𝕧 i) P ⊗ₜ[𝕂]
      TensorModule.act R 𝕧 _ _ (K R 𝕧 (-ktilde R i)) Q +
        P ⊗ₜ[𝕂] TensorModule.act R 𝕧 _ _ (F R 𝕧 i) Q) =
      TensorModule.act R 𝕧 _ _ (F R 𝕧 i) (tensorContract M₁ M₄ δ (P ⊗ₜ[𝕂] Q)) := by
  induction P using TensorProduct.inductionOn with
  | add P P' hP hP' =>
    simp only [map_add, add_tmul] at hP hP' ⊢
    rw [← hP, ← hP']
    abel
  | tmul a b =>
    induction Q using TensorProduct.inductionOn with
    | add Q Q' hQ hQ' =>
      simp only [map_add, tmul_add] at hQ hQ' ⊢
      rw [← hQ, ← hQ']
      abel
    | tmul c d =>
      have hF := hδ (F R 𝕧 i) (b ⊗ₜ[𝕂] c)
      have hK := hδ (K R 𝕧 (-ktilde R i)) (b ⊗ₜ[𝕂] c)
      rw [TensorModule.act_F_tmul, map_add, counit_F, zero_mul] at hF
      rw [TensorModule.act_K_tmul, counit_K, one_mul] at hK
      rw [TensorModule.act_F_tmul, TensorModule.act_K_tmul, TensorModule.act_F_tmul, add_tmul,
        tmul_add, map_add, map_add, map_add, tensorContract_tmul, tensorContract_tmul,
        tensorContract_tmul, tensorContract_tmul, tensorContract_tmul, map_smul,
        TensorModule.act_F_tmul, hK, eq_neg_of_add_eq_zero_left hF, neg_smul, smul_add]
      abel

omit [Finite I] in
/-- The contraction intertwines `K_μ`. -/
lemma tensorContract_K (μ : Y) (P : M₁ ⊗[𝕂] M₂) (Q : M₃ ⊗[𝕂] M₄) :
    tensorContract M₁ M₄ δ (TensorModule.act R 𝕧 _ _ (K R 𝕧 μ) P ⊗ₜ[𝕂]
      TensorModule.act R 𝕧 _ _ (K R 𝕧 μ) Q) =
      TensorModule.act R 𝕧 _ _ (K R 𝕧 μ) (tensorContract M₁ M₄ δ (P ⊗ₜ[𝕂] Q)) := by
  induction P using TensorProduct.inductionOn with
  | add P P' hP hP' => simp only [map_add, add_tmul, hP, hP']
  | tmul a b =>
    induction Q using TensorProduct.inductionOn with
    | add Q Q' hQ hQ' => simp only [map_add, tmul_add, hQ, hQ']
    | tmul c d =>
      have hK := hδ (K R 𝕧 μ) (b ⊗ₜ[𝕂] c)
      rw [TensorModule.act_K_tmul, counit_K, one_mul] at hK
      rw [TensorModule.act_K_tmul, TensorModule.act_K_tmul, tensorContract_tmul,
        tensorContract_tmul, map_smul, TensorModule.act_K_tmul, hK]

end Contract

/-! ### The map `t` -/

section Transition

variable (Λ Λ' Λ'' : Dom R)

/-- **[Lus] 25.1.5**: `t : ʷΛ_{λ'+λ} ⊗ Λ_{λ'+λ''} → ʷΛ_λ ⊗ Λ_{λ''}`, the composition of
`χ' ⊗ χ` with `1 ⊗ δ_{λ'} ⊗ 1`. -/
def tensorTransition : TwL (Λ' + Λ) ⊗[𝕂] IrreducibleModule R 𝕧 (Λ' + Λ'').1 →ₗ[𝕂]
    TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ''.1 :=
  tensorContract (TwL Λ) (IrreducibleModule R 𝕧 Λ''.1) (tensorPairing hR Λ') ∘ₗ
    TensorProduct.map (tensorEmbTw hR Λ' Λ)
    ((TensorModule.mk _ _).symm.toLinearMap ∘ₗ (tensorEmb hvt hR Λ'.2 Λ''.2).restrictScalars 𝕂)

lemma tensorTransition_tmul (x : TwL (Λ' + Λ)) (y : IrreducibleModule R 𝕧 (Λ' + Λ'').1) :
    tensorTransition hR Λ Λ' Λ'' (x ⊗ₜ[𝕂] y) =
      tensorContract (TwL Λ) (IrreducibleModule R 𝕧 Λ''.1) (tensorPairing hR Λ')
      (tensorEmbTw hR Λ' Λ x ⊗ₜ[𝕂] (TensorModule.mk _ _).symm (tensorEmb hvt hR Λ'.2 Λ''.2 y)) :=
  rfl

variable {Λ Λ' Λ''} in
lemma tensorEmb_act (u : QuantumGroup R 𝕧) (y : IrreducibleModule R 𝕧 (Λ' + Λ'').1) :
    (TensorModule.mk _ _).symm (tensorEmb hvt hR Λ'.2 Λ''.2 (u • y)) =
      TensorModule.act R 𝕧 _ _ u ((TensorModule.mk _ _).symm (tensorEmb hvt hR Λ'.2 Λ''.2 y)) := by
  rw [map_smul]
  rfl

lemma tensorTransition_comp_act_E (i : I) :
    tensorTransition hR Λ Λ' Λ'' ∘ₗ TensorModule.act R 𝕧 _ _ (E R 𝕧 i) =
      TensorModule.act R 𝕧 _ _ (E R 𝕧 i) ∘ₗ tensorTransition hR Λ Λ' Λ'' := by
  refine TensorProduct.ext' fun x y ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, TensorModule.act_E_tmul, LinearMap.map_add,
    tensorTransition_tmul, tensorTransition_tmul, tensorTransition_tmul,
    tensorEmbTw_act hR Λ' Λ (E R 𝕧 i) x, tensorEmbTw_act hR Λ' Λ (Kt R 𝕧 i) x,
    tensorEmb_act hR (E R 𝕧 i) y, ← LinearMap.map_add]
  exact tensorContract_E (tensorPairing_act hR Λ') i _ _

lemma tensorTransition_comp_act_F (i : I) :
    tensorTransition hR Λ Λ' Λ'' ∘ₗ TensorModule.act R 𝕧 _ _ (F R 𝕧 i) =
      TensorModule.act R 𝕧 _ _ (F R 𝕧 i) ∘ₗ tensorTransition hR Λ Λ' Λ'' := by
  refine TensorProduct.ext' fun x y ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, TensorModule.act_F_tmul, LinearMap.map_add,
    tensorTransition_tmul, tensorTransition_tmul, tensorTransition_tmul,
    tensorEmbTw_act hR Λ' Λ (F R 𝕧 i) x, tensorEmb_act hR (K R 𝕧 (-ktilde R i)) y,
    tensorEmb_act hR (F R 𝕧 i) y, ← LinearMap.map_add]
  exact tensorContract_F (tensorPairing_act hR Λ') i _ _

lemma tensorTransition_comp_act_K (μ : Y) :
    tensorTransition hR Λ Λ' Λ'' ∘ₗ TensorModule.act R 𝕧 _ _ (K R 𝕧 μ) =
      TensorModule.act R 𝕧 _ _ (K R 𝕧 μ) ∘ₗ tensorTransition hR Λ Λ' Λ'' := by
  refine TensorProduct.ext' fun x y ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, TensorModule.act_K_tmul,
    tensorTransition_tmul, tensorTransition_tmul, tensorEmbTw_act hR Λ' Λ (K R 𝕧 μ) x,
    tensorEmb_act hR (K R 𝕧 μ) y]
  exact tensorContract_K (tensorPairing_act hR Λ') μ _ _

/-- **[Lus] 25.1.5**: `t` is a homomorphism of `U`-modules. -/
theorem tensorTransition_act (u : QuantumGroup R 𝕧)
    (z : TwL (Λ' + Λ) ⊗[𝕂] IrreducibleModule R 𝕧 (Λ' + Λ'').1) :
    tensorTransition hR Λ Λ' Λ'' (TensorModule.act R 𝕧 _ _ u z) =
      TensorModule.act R 𝕧 _ _ u (tensorTransition hR Λ Λ' Λ'' z) := by
  suffices h : tensorTransition hR Λ Λ' Λ'' ∘ₗ TensorModule.act R 𝕧 _ _ u =
      TensorModule.act R 𝕧 _ _ u ∘ₗ tensorTransition hR Λ Λ' Λ'' from LinearMap.congr_fun h z
  induction u using QuantumGroup.induction_on with
  | algebraMap c =>
    refine LinearMap.ext fun z ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.commutes, AlgHom.commutes,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | E i => exact tensorTransition_comp_act_E hR Λ Λ' Λ'' i
  | F i => exact tensorTransition_comp_act_F hR Λ Λ' Λ'' i
  | K μ => exact tensorTransition_comp_act_K hR Λ Λ' Λ'' μ
  | add x y hx hy => rw [map_add, LinearMap.comp_add, hx, hy, map_add, LinearMap.add_comp]
  | mul x y hx hy =>
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hx, LinearMap.comp_assoc, hy,
      ← LinearMap.comp_assoc, map_mul, Module.End.mul_eq_comp]

/-- `t(ξ_{-λ'-λ} ⊗ η_{λ'+λ''}) = ξ_{-λ} ⊗ η_{λ''}`. -/
theorem tensorTransition_hwv :
    tensorTransition hR Λ Λ' Λ''
      (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 (Λ' + Λ).1) ⊗ₜ[𝕂]
        IrreducibleModule.hwv R 𝕧 (Λ' + Λ'').1) =
      ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
        IrreducibleModule.hwv R 𝕧 Λ''.1 := by
  rw [tensorTransition_tmul, tensorEmbTw_hwv]
  erw [tensorEmb_hwv hvt hR Λ'.2 Λ''.2]
  erw [tensorContract_tmul, tensorPairing_hwv, one_smul]

/-- **[Lus] Lemma 25.1.6 (c)**: `t` is surjective. -/
theorem surjective_tensorTransition : Function.Surjective (tensorTransition hR Λ Λ' Λ'') := by
  intro z
  obtain ⟨u, rfl⟩ := exists_act_tmul_hwv_eq Λ Λ'' z
  exact ⟨_, by rw [tensorTransition_act, tensorTransition_hwv]⟩

end Transition

/-! ### [Lus] Lemma 25.1.6 -/

section Congruence

omit [Finite I] [DecidableEq I] in
lemma isNegLaurent_finsuppSum {ι : Type*} (f : ι →₀ 𝕂) {g : ι → 𝕂 → 𝕂}
    (h : ∀ i ∈ f.support, IsNegLaurent (g i (f i))) : IsNegLaurent (f.sum g) :=
  Finset.sum_induction _ IsNegLaurent (fun _ _ ↦ IsNegLaurent.add) isNegLaurent_zero h

variable (Λ Λ' Λ'' : Dom R)

open Classical in
/-- **[Lus] Lemma 25.1.6 (a), (b)** in coordinates: the coefficient of
`b₁⁺ξ_{-λ} ⊗ b₂⁻η_{λ''}` in `t(b⁺ξ_{-λ'-λ} ⊗ b''⁻η_{λ'+λ''})` is congruent modulo `v⁻¹ℤ[v⁻¹]`
to `1` if `(b₁, b₂) = (b, b'')` and to `0` otherwise. -/
theorem repr_tensorTransition_sub {x x'' : Um D 𝕧} (hx : x ∈ canonicalBasis D)
    (hx'' : x'' ∈ canonicalBasis D) (p : canonicalBasisHW D Λ × canonicalBasisHW D Λ'') :
    IsNegLaurent ((tensorBasis hR Λ Λ'').repr (tensorTransition hR Λ Λ' Λ''
      (ChevalleyTwist.toTwist R 𝕧 _ (evq hvt (Λ' + Λ) x) ⊗ₜ[𝕂] evq hvt (Λ' + Λ'') x'')) p -
        if (p.1 : Um D 𝕧) = x ∧ (p.2 : Um D 𝕧) = x'' then 1 else 0) := by
  set B₁ := twTensorBasis hR Λ' Λ
  set B₂ := tensorHWBasis hR Λ' Λ''
  set q₀ : canonicalBasisHW D Λ × canonicalBasisHW D Λ' := (p.1, hwOne Λ')
  set r₀ : canonicalBasisHW D Λ' × canonicalBasisHW D Λ'' := (hwOne Λ', p.2)
  set Bf : (TwL Λ ⊗[𝕂] TwL Λ') →ₗ[𝕂]
      TensorModule 𝕂 (IrreducibleModule R 𝕧 Λ'.1) (IrreducibleModule R 𝕧 Λ''.1) →ₗ[𝕂] 𝕂 :=
    (((TensorProduct.mk 𝕂 _ _).compr₂ ((tensorBasis hR Λ Λ'').coord p ∘ₗ
      tensorContract (TwL Λ) (IrreducibleModule R 𝕧 Λ''.1) (tensorPairing hR Λ'))).compl₂
        (TensorModule.mk _ _).symm.toLinearMap) -
      (LinearMap.mul 𝕂 𝕂).compl₁₂ (B₁.coord q₀) (B₂.coord r₀)
  have hval : ∀ q r, Bf (B₁ q) (B₂ r) =
      tensorPairing hR Λ' (tensorBasis hR Λ' Λ' (q.2, r.1)) * (if (q.1, r.2) = p then 1 else 0) -
        (if q = q₀ then 1 else 0) * (if r = r₀ then 1 else 0) := by
    intro q r
    simp only [Bf, LinearMap.sub_apply, LinearMap.compl₂_apply, LinearMap.compr₂_apply,
      LinearMap.compl₁₂_apply, LinearMap.mul_apply', Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply, LinearMap.comp_apply, mk_apply,
      LinearEquiv.coe_coe]
    rw [twTensorBasis_apply, tensorHWBasis_apply]
    erw [LinearEquiv.symm_apply_apply]
    rw [tensorContract_tmul, map_smul, ← tensorBasis_apply hR Λ Λ'' (q.1, r.2),
      Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      ← tensorBasis_apply hR Λ' Λ' (q.2, r.1)]
  have hX := isIntInv_repr_tensorEmbTw_evq hR Λ' Λ hx
  have hY := isIntInv_repr_tensorEmb_evq hR Λ' Λ'' hx''
  have hX₀ := repr_tensorEmbTw_evq_one hR Λ' Λ hx p.1
  have hY₀ := repr_tensorEmb_evq_one hR Λ' Λ'' hx'' p.2
  have key : Bf (tensorEmbTw hR Λ' Λ (ChevalleyTwist.toTwist R 𝕧 _ (evq hvt (Λ' + Λ) x)))
      (tensorEmb hvt hR Λ'.2 Λ''.2 (evq hvt (Λ' + Λ'') x'')) =
      (tensorBasis hR Λ Λ'').repr (tensorTransition hR Λ Λ' Λ''
        (ChevalleyTwist.toTwist R 𝕧 _ (evq hvt (Λ' + Λ) x) ⊗ₜ[𝕂] evq hvt (Λ' + Λ'') x'')) p -
        if (p.1 : Um D 𝕧) = x ∧ (p.2 : Um D 𝕧) = x'' then 1 else 0 := by
    simp only [Bf, LinearMap.sub_apply, LinearMap.compl₂_apply, LinearMap.compr₂_apply,
      LinearMap.compl₁₂_apply, LinearMap.mul_apply', Module.Basis.coord_apply, mk_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, B₁, B₂, q₀, r₀]
    rw [hX₀, hY₀, tensorTransition_tmul, ite_zero_mul_ite_zero, one_mul]
  rw [← key, ← LinearMap.sum_repr_mul_repr_mul B₁ B₂ (B := Bf)]
  refine isNegLaurent_finsuppSum _ fun q _ ↦ isNegLaurent_finsuppSum _ fun r _ ↦ ?_
  rw [smul_eq_mul, smul_eq_mul, hval, ← mul_assoc, mul_comm (_ * _) (_ - _)]
  refine IsNegLaurent.mul_isIntInv ?_ ((hX q).mul (hY r))
  by_cases hqr : q = q₀ ∧ r = r₀
  · obtain ⟨rfl, rfl⟩ := hqr
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, tensorPairing_tensorBasis_one]
    simp only [mul_one, sub_self, isNegLaurent_zero]
  · rw [show ((if q = q₀ then (1 : 𝕂) else 0) * if r = r₀ then 1 else 0) = 0 by
      rw [ite_zero_mul_ite_zero, ite_eq_right hqr], sub_zero]
    by_cases hp : (q.1, r.2) = p
    · rw [ite_eq_left hp, mul_one]
      refine isNegLaurent_tensorPairing_tensorBasis hR Λ' fun h ↦ hqr ⟨?_, ?_⟩
      · exact Prod.ext_iff.2 ⟨(Prod.ext_iff.1 hp).1, (Prod.ext_iff.1 h).1⟩
      · exact Prod.ext_iff.2 ⟨(Prod.ext_iff.1 h).2, (Prod.ext_iff.1 hp).2⟩
    · rw [ite_eq_right hp, mul_zero]
      exact isNegLaurent_zero

/-- **[Lus] Lemma 25.1.6 (a)**: for `b ∈ B(λ)`, `b'' ∈ B(λ'')`,
`t(b⁺ξ_{-λ'-λ} ⊗ b''⁻η_{λ'+λ''}) ≡ b⁺ξ_{-λ} ⊗ b''⁻η_{λ''}` modulo `v⁻¹ℒ_{λ,λ''}`. -/
theorem tensorTransition_sub_mem_tensorLatNeg (b : canonicalBasisHW D Λ)
    (b'' : canonicalBasisHW D Λ'') :
    tensorTransition hR Λ Λ' Λ'' (ChevalleyTwist.toTwist R 𝕧 _ (evq hvt (Λ' + Λ) b) ⊗ₜ[𝕂]
      evq hvt (Λ' + Λ'') b'') - tensorBasis hR Λ Λ'' (b, b'') ∈ tensorLatNeg hR Λ Λ'' := by
  classical
  intro h
  have := repr_tensorTransition_sub hR Λ Λ' Λ'' (canonicalBasisHW_subset D Λ b.2)
    (canonicalBasisHW_subset D Λ'' b''.2) h
  have e : (tensorBasisIdx hR Λ Λ'').repr (tensorBasis hR Λ Λ'' (b, b'')) h =
      if (show TensorIdx Λ Λ'' from (b, b'')) = h then 1 else 0 := by
    rw [← tensorBasisIdx_apply hR Λ Λ'' (show TensorIdx Λ Λ'' from (b, b'')),
      Module.Basis.repr_self, Finsupp.single_apply]
  change IsNegLaurent ((tensorBasisIdx hR Λ Λ'').repr (_ - tensorBasis hR Λ Λ'' (b, b'')) h)
  rw [map_sub, Finsupp.sub_apply, e]
  obtain ⟨h₁, h₂⟩ := h
  have hc : (show TensorIdx Λ Λ'' from (b, b'')) = (h₁, h₂) ↔
      (h₁ : Um D 𝕧) = b ∧ (h₂ : Um D 𝕧) = b'' := by
    refine ⟨fun e ↦ ?_, fun e ↦ ?_⟩
    · have e' : (b, b'') = (h₁, h₂) := e
      rw [Prod.mk.injEq] at e'
      exact ⟨congrArg Subtype.val e'.1.symm, congrArg Subtype.val e'.2.symm⟩
    · change (b, b'') = (h₁, h₂)
      rw [Subtype.ext e.1, Subtype.ext e.2]
  convert this using 2
  · rfl
  · exact if_congr hc rfl rfl

/-- **[Lus] Lemma 25.1.6 (b)**: for `b ∈ B(λ'+λ)`, `b'' ∈ B(λ'+λ'')` with `b ∉ B(λ)` or
`b'' ∉ B(λ'')`, `t(b⁺ξ_{-λ'-λ} ⊗ b''⁻η_{λ'+λ''}) ≡ 0` modulo `v⁻¹ℒ_{λ,λ''}`. -/
theorem tensorTransition_mem_tensorLatNeg (b : canonicalBasisHW D (Λ' + Λ))
    (b'' : canonicalBasisHW D (Λ' + Λ''))
    (h : (b : Um D 𝕧) ∉ canonicalBasisHW D Λ ∨ (b'' : Um D 𝕧) ∉ canonicalBasisHW D Λ'') :
    tensorTransition hR Λ Λ' Λ'' (ChevalleyTwist.toTwist R 𝕧 _ (evq hvt (Λ' + Λ) b) ⊗ₜ[𝕂]
      evq hvt (Λ' + Λ'') b'') ∈ tensorLatNeg hR Λ Λ'' := by
  classical
  intro p
  have := repr_tensorTransition_sub hR Λ Λ' Λ'' (canonicalBasisHW_subset D _ b.2)
    (canonicalBasisHW_subset D _ b''.2) p
  have hne : ¬((p.1 : Um D 𝕧) = b ∧ (p.2 : Um D 𝕧) = b'') := by
    rintro ⟨e₁, e₂⟩
    rcases h with h | h
    · exact h (e₁ ▸ p.1.2)
    · exact h (e₂ ▸ p.2.2)
  rwa [ite_eq_right hne, sub_zero] at this

end Congruence

end LieLean.QuantumGroup
