/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import LieLean.Algebra.QuantumGroup.LusztigF.Basic

/-!
# The twisted coproduct `r : 'f → 'f ⊗ 'f`

Following [Lus] 1.2.2 (check), `'f ⊗ 'f` carries the *twisted* multiplication
`(x₁ ⊗ x₂)(x₁' ⊗ x₂') = v^{|x₂|·|x₁'|} x₁x₁' ⊗ x₂x₂'` (`x₂, x₁'` homogeneous), and
`r : 'f → 'f ⊗ 'f` is the unique algebra homomorphism for this multiplication with
`r(θᵢ) = θᵢ ⊗ 1 + 1 ⊗ θᵢ`.

We avoid choosing homogeneous components: the twisted product is
`twistedMul (a ⊗ b) Z = (a · ⊗ id)(ρ(b) Z)`, where `ρ : 'f → End('f ⊗ 'f)` is the algebra
homomorphism `θᵢ ↦ σᵢ ⊗ (θᵢ ·)` (`twistAct`), so `ρ(b)(c ⊗ d) = σ_{|b|}(c) ⊗ bd` for homogeneous
`b`; associativity (`twistedMul_assoc`) is proved without the grading. Then `r` is obtained by
letting `'f` act on `'f ⊗ 'f` by `θᵢ ↦` twisted left multiplication by `θᵢ ⊗ 1 + 1 ⊗ θᵢ`
(`rEnd`), and `r(x) = rEnd x (1 ⊗ 1)` (`comul`); `comul_mul` shows that `r` is multiplicative for
the twisted product. This construction is our own; it is equivalent to Lusztig's definition.

We also prove the compatibilities of `r` with the counit, the twists and the skew derivations that
are needed for Lusztig's bilinear form ([Lus] 1.2.3, 1.2.13 (check)).

## Main definitions

* `LusztigF.twistAct`: `ρ : 'f → End('f ⊗ 'f)`, `θᵢ ↦ σᵢ ⊗ (θᵢ ·)`.
* `LusztigF.twistedMul`: the twisted multiplication on `'f ⊗ 'f`.
* `LusztigF.comul`: Lusztig's `r : 'f → 'f ⊗ 'f`.

## Main results

* `LusztigF.twistedMul_assoc`, `LusztigF.twistedMul_one_left`, `LusztigF.twistedMul_one_right`.
* `LusztigF.comul_θ`, `LusztigF.comul_one`, `LusztigF.comul_mul`: `r` is the twisted algebra
  homomorphism with `r(θᵢ) = θᵢ ⊗ 1 + 1 ⊗ θᵢ`.
* `LusztigF.rid_lTensor_counit_comul`, `LusztigF.lid_rTensor_counit_comul`: counit laws.
* `LusztigF.comul_twist`: `r ∘ σⱼ = (σⱼ ⊗ σⱼ) ∘ r`.
* `LusztigF.lTensor_rDeriv_comul`: `(1 ⊗ rⱼ) ∘ r = r ∘ rⱼ`.
* `LusztigF.lid_rTensor_counit_rDeriv_comul`: `(ε ∘ rᵢ ⊗ 1) ∘ r = ᵢr`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §1.2.
-/

noncomputable section

open TensorProduct

namespace LusztigF

variable {k I : Type*} [Field k] (D : CartanDatum I) (v : k)

/-- The algebra homomorphism `ρ : 'f → End('f ⊗ 'f)`, `θᵢ ↦ σᵢ ⊗ (θᵢ ·)`; for homogeneous `b`,
`ρ(b)(c ⊗ d) = v^{|b|·|c|} c ⊗ bd`. -/
def twistAct : LusztigF k I →ₐ[k] Module.End k (LusztigF k I ⊗[k] LusztigF k I) :=
  FreeAlgebra.lift k fun i ↦ TensorProduct.map (twist D v i).toLinearMap
    (LinearMap.mulLeft k (θ k i))

lemma twistAct_θ (i : I) : twistAct D v (θ k i) =
    TensorProduct.map (twist D v i).toLinearMap (LinearMap.mulLeft k (θ k i)) := by
  simp [twistAct]

lemma twistAct_one_tmul (b d : LusztigF k I) : twistAct D v b (1 ⊗ₜ d) = 1 ⊗ₜ (b * d) := by
  induction b using FreeAlgebra.induction generalizing d with
  | grade0 c =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    rw [← Algebra.smul_def, TensorProduct.tmul_smul]
  | grade1 i => simp [twistAct_θ]
  | mul a b ha hb => rw [map_mul, Module.End.mul_apply, hb, ha, mul_assoc]
  | add a b ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_mul, tmul_add]

variable {D v} in
/-- For homogeneous `b ∈ 'f_β` and `c ∈ 'f_γ`, `ρ(b)(c ⊗ d) = v^{β·γ} c ⊗ bd`. -/
theorem twistAct_tmul_of_mem (hv : v ≠ 0) {β γ : I →₀ ℕ} {b c : LusztigF k I}
    (hb : b ∈ weightSpace k β) (hc : c ∈ weightSpace k γ) (d : LusztigF k I) :
    twistAct D v b (c ⊗ₜ d) = v ^ D.weightDot β γ • (c ⊗ₜ (b * d)) := by
  induction hb using Submodule.span_induction generalizing d with
  | mem y hy =>
    obtain ⟨w, rfl, rfl⟩ := hy
    induction w generalizing d with
    | nil => simp [Module.End.one_apply]
    | cons l w ih =>
      rw [monomial_cons, map_mul, Module.End.mul_apply, ih, map_smul, twistAct_θ, map_tmul,
        AlgHom.toLinearMap_apply, twist_of_mem hv l hc, LinearMap.mulLeft_apply, smul_tmul',
        smul_smul, wordWeight_cons, D.weightDot_add_left, zpow_add₀ hv, mul_assoc, mul_comm,
        smul_tmul']
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, LinearMap.add_apply, hy, hz, add_mul, tmul_add, smul_add]
  | smul a y _ hy => rw [map_smul, LinearMap.smul_apply, hy, smul_mul_assoc, tmul_smul, smul_comm]

/-- The bilinear map `a, b ↦ (a · ⊗ id) ∘ ρ(b)`. -/
def twistedMulAux :
    LusztigF k I →ₗ[k] LusztigF k I →ₗ[k] Module.End k (LusztigF k I ⊗[k] LusztigF k I) :=
  LinearMap.mk₂ k (fun a b ↦ (LinearMap.mulLeft k a).rTensor _ ∘ₗ twistAct D v b)
    (fun a a' b ↦ by
      rw [show LinearMap.mulLeft k (a + a') = LinearMap.mulLeft k a + LinearMap.mulLeft k a' from
        LinearMap.ext fun x ↦ add_mul _ _ _, LinearMap.rTensor_add, LinearMap.add_comp])
    (fun c a b ↦ by
      rw [show LinearMap.mulLeft k (c • a) = c • LinearMap.mulLeft k a from
        LinearMap.ext fun x ↦ smul_mul_assoc _ _ _, LinearMap.rTensor_smul, LinearMap.smul_comp])
    (fun a b b' ↦ by rw [map_add, LinearMap.comp_add])
    (fun c a b ↦ by rw [map_smul, LinearMap.comp_smul])

/-- Lusztig's twisted multiplication on `'f ⊗ 'f` ([Lus] 1.2.2 (check)): for homogeneous `x₂`,
`x₁'`, `(x₁ ⊗ x₂)(x₁' ⊗ x₂') = v^{|x₂|·|x₁'|} x₁x₁' ⊗ x₂x₂'`. -/
def twistedMul :
    LusztigF k I ⊗[k] LusztigF k I →ₗ[k] LusztigF k I ⊗[k] LusztigF k I →ₗ[k]
      LusztigF k I ⊗[k] LusztigF k I :=
  TensorProduct.lift (twistedMulAux D v)

lemma twistedMul_tmul (a b : LusztigF k I) (Z : LusztigF k I ⊗[k] LusztigF k I) :
    twistedMul D v (a ⊗ₜ b) Z = (LinearMap.mulLeft k a).rTensor _ (twistAct D v b Z) := by
  simp [twistedMul, twistedMulAux]

lemma twistedMul_tmul_tmul_θ (a c d : LusztigF k I) (i : I) :
    twistedMul D v (a ⊗ₜ θ k i) (c ⊗ₜ d) = (a * twist D v i c) ⊗ₜ (θ k i * d) := by
  simp [twistedMul_tmul, twistAct_θ]

/-- The twisted multiplication on homogeneous elements ([Lus] 1.2.2 (check)):
`(x₁ ⊗ x₂)(x₁' ⊗ x₂') = v^{|x₂|·|x₁'|} x₁x₁' ⊗ x₂x₂'`. -/
theorem twistedMul_tmul_tmul (hv : v ≠ 0) {β γ : I →₀ ℕ} {x₂ x₁' : LusztigF k I}
    (h₂ : x₂ ∈ weightSpace k β) (h₁ : x₁' ∈ weightSpace k γ) (x₁ x₂' : LusztigF k I) :
    twistedMul D v (x₁ ⊗ₜ x₂) (x₁' ⊗ₜ x₂') =
      v ^ D.weightDot β γ • ((x₁ * x₁') ⊗ₜ (x₂ * x₂')) := by
  rw [twistedMul_tmul, twistAct_tmul_of_mem hv h₂ h₁, map_smul, LinearMap.rTensor_tmul,
    LinearMap.mulLeft_apply]

@[simp] lemma twistedMul_one_left (Z : LusztigF k I ⊗[k] LusztigF k I) :
    twistedMul D v (1 ⊗ₜ 1) Z = Z := by
  rw [twistedMul_tmul, map_one, show LinearMap.mulLeft k (1 : LusztigF k I) = LinearMap.id from
    LinearMap.ext fun x ↦ one_mul x, LinearMap.rTensor_id]
  rfl

@[simp] lemma twistedMul_one_right (X : LusztigF k I ⊗[k] LusztigF k I) :
    twistedMul D v X (1 ⊗ₜ 1) = X := by
  induction X with
  | tmul a b => simp [twistedMul_tmul, twistAct_one_tmul]
  | add X Y hX hY => rw [map_add, LinearMap.add_apply, hX, hY]

lemma twistedMul_rTensor_mulLeft (a : LusztigF k I) (W : LusztigF k I ⊗[k] LusztigF k I) :
    twistedMul D v ((LinearMap.mulLeft k a).rTensor _ W) =
      (LinearMap.mulLeft k a).rTensor _ ∘ₗ twistedMul D v W := by
  induction W with
  | tmul c d =>
    refine LinearMap.ext fun Z ↦ ?_
    simp only [LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, twistedMul_tmul,
      LinearMap.coe_comp, Function.comp_apply]
    rw [show LinearMap.mulLeft k (a * c) = LinearMap.mulLeft k a ∘ₗ LinearMap.mulLeft k c from
      LinearMap.ext fun x ↦ mul_assoc _ _ _, LinearMap.rTensor_comp, LinearMap.comp_apply]
  | add X Y hX hY => simp only [map_add, hX, hY, LinearMap.comp_add]

lemma twistedMul_twistAct (b : LusztigF k I) (W : LusztigF k I ⊗[k] LusztigF k I) :
    twistedMul D v (twistAct D v b W) = twistAct D v b ∘ₗ twistedMul D v W := by
  induction b using FreeAlgebra.induction generalizing W with
  | grade0 c =>
    simp only [AlgHom.commutes, Module.algebraMap_end_eq_smul_id, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul, LinearMap.smul_comp, LinearMap.id_comp]
  | grade1 i =>
    induction W with
    | tmul c d =>
      refine LinearMap.ext fun Z ↦ ?_
      simp only [twistAct_θ, map_tmul, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
        twistedMul_tmul, map_mul, LinearMap.coe_comp, Function.comp_apply, Module.End.mul_apply]
      generalize twistAct D v d Z = W
      induction W with
      | tmul e f => simp
      | add X Y hX hY => simp only [map_add, hX, hY]
    | add X Y hX hY => simp only [map_add, hX, hY, LinearMap.comp_add]
  | mul a b ha hb =>
    rw [map_mul, Module.End.mul_apply, ha, hb, Module.End.mul_eq_comp, LinearMap.comp_assoc]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, LinearMap.add_comp]

/-- The twisted multiplication is associative. -/
theorem twistedMul_assoc (X Y Z : LusztigF k I ⊗[k] LusztigF k I) :
    twistedMul D v (twistedMul D v X Y) Z = twistedMul D v X (twistedMul D v Y Z) := by
  induction X generalizing Z with
  | tmul a b =>
    rw [twistedMul_tmul, twistedMul_rTensor_mulLeft, LinearMap.comp_apply, twistedMul_twistAct,
      LinearMap.comp_apply, twistedMul_tmul]
  | add X X' hX hX' => simp only [map_add, LinearMap.add_apply, hX, hX']

/-- The action of `'f` on `'f ⊗ 'f` by twisted left multiplication, `θᵢ ↦ (θᵢ ⊗ 1 + 1 ⊗ θᵢ) ·`. -/
def rEnd : LusztigF k I →ₐ[k] Module.End k (LusztigF k I ⊗[k] LusztigF k I) :=
  FreeAlgebra.lift k fun i ↦ twistedMul D v (θ k i ⊗ₜ 1 + 1 ⊗ₜ θ k i)

/-- Lusztig's twisted coproduct `r : 'f → 'f ⊗ 'f` ([Lus] 1.2.2 (check)), `r(x) = x · (1 ⊗ 1)`
for the action `rEnd`; see `comul_θ` and `comul_mul`. -/
def comul : LusztigF k I →ₗ[k] LusztigF k I ⊗[k] LusztigF k I :=
  LinearMap.applyₗ (1 ⊗ₜ 1) ∘ₗ (rEnd D v).toLinearMap

lemma comul_apply (x : LusztigF k I) : comul D v x = rEnd D v x (1 ⊗ₜ 1) := rfl

lemma rEnd_θ_apply (i : I) (W : LusztigF k I ⊗[k] LusztigF k I) :
    rEnd D v (θ k i) W = (LinearMap.mulLeft k (θ k i)).rTensor _ W +
      TensorProduct.map (twist D v i).toLinearMap (LinearMap.mulLeft k (θ k i)) W := by
  simp only [rEnd, FreeAlgebra.lift_ι_apply, map_add, LinearMap.add_apply, twistedMul_tmul,
    map_one, Module.End.one_apply, twistAct_θ]
  congr 1
  rw [show LinearMap.mulLeft k (1 : LusztigF k I) = LinearMap.id from
    LinearMap.ext fun x ↦ one_mul x, LinearMap.rTensor_id, LinearMap.id_apply]

@[simp] lemma comul_one : comul D v (1 : LusztigF k I) = 1 ⊗ₜ 1 := by
  simp [comul_apply]

@[simp] lemma comul_algebraMap (c : k) :
    comul D v (algebraMap k (LusztigF k I) c) = c • ((1 : LusztigF k I) ⊗ₜ 1) := by
  simp [comul_apply, Module.algebraMap_end_apply]

/-- `r(θᵢ) = θᵢ ⊗ 1 + 1 ⊗ θᵢ`. -/
@[simp] theorem comul_θ (i : I) : comul D v (θ k i) = θ k i ⊗ₜ 1 + 1 ⊗ₜ θ k i := by
  simp [comul_apply, rEnd_θ_apply]

lemma comul_θ_mul (i : I) (x : LusztigF k I) :
    comul D v (θ k i * x) = (LinearMap.mulLeft k (θ k i)).rTensor _ (comul D v x) +
      TensorProduct.map (twist D v i).toLinearMap (LinearMap.mulLeft k (θ k i)) (comul D v x) := by
  rw [comul_apply, map_mul, Module.End.mul_apply, rEnd_θ_apply, ← comul_apply]

lemma twistedMul_comul (x : LusztigF k I) : twistedMul D v (comul D v x) = rEnd D v x := by
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    refine LinearMap.ext fun Z ↦ ?_
    simp [Module.algebraMap_end_apply]
  | grade1 i =>
    rw [comul_apply]
    simp only [rEnd, FreeAlgebra.lift_ι_apply, twistedMul_one_right]
  | mul a b ha hb =>
    have : comul D v (a * b) = rEnd D v a (comul D v b) := by
      rw [comul_apply, map_mul, Module.End.mul_apply, ← comul_apply]
    rw [this, map_mul, ← ha, ← hb]
    refine LinearMap.ext fun Z ↦ ?_
    rw [Module.End.mul_apply, twistedMul_assoc]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- `r` is multiplicative for the twisted multiplication ([Lus] 1.2.2 (check)). -/
theorem comul_mul (x y : LusztigF k I) :
    comul D v (x * y) = twistedMul D v (comul D v x) (comul D v y) := by
  rw [twistedMul_comul, comul_apply, map_mul, Module.End.mul_apply, ← comul_apply]

/-! ### Counit, twists and skew derivations -/

/-- The counit law `(1 ⊗ ε) ∘ r = id`. -/
theorem rid_lTensor_counit_comul (x : LusztigF k I) :
    TensorProduct.rid k _ ((counit (k := k) (I := I)).toLinearMap.lTensor _ (comul D v x)) = x := by
  induction x using induction_left with
  | algebraMap c => simp [Algebra.algebraMap_eq_smul_one]
  | smul c x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | θ_mul i x hx =>
    rw [comul_θ_mul, map_add, map_add]
    generalize comul D v x = W at hx
    have h1 : ∀ W : LusztigF k I ⊗[k] LusztigF k I,
        TensorProduct.rid k _ ((counit (k := k) (I := I)).toLinearMap.lTensor _
          ((LinearMap.mulLeft k (θ k i)).rTensor _ W)) =
        θ k i * TensorProduct.rid k _ ((counit (k := k) (I := I)).toLinearMap.lTensor _ W) := by
      intro W
      induction W with
      | tmul e f => simp
      | add X Y hX hY => simp only [map_add, hX, hY, mul_add]
    have h2 : ∀ W : LusztigF k I ⊗[k] LusztigF k I,
        (counit (k := k) (I := I)).toLinearMap.lTensor _
          (TensorProduct.map (twist D v i).toLinearMap (LinearMap.mulLeft k (θ k i)) W) = 0 := by
      intro W
      induction W with
      | tmul e f => simp
      | add X Y hX hY => simp only [map_add, hX, hY, add_zero]
    rw [h1, hx, h2, map_zero, add_zero]

/-- The counit law `(ε ⊗ 1) ∘ r = id`. -/
theorem lid_rTensor_counit_comul (x : LusztigF k I) :
    TensorProduct.lid k _ ((counit (k := k) (I := I)).toLinearMap.rTensor _ (comul D v x)) = x := by
  induction x using induction_left with
  | algebraMap c => simp [Algebra.algebraMap_eq_smul_one]
  | smul c x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | θ_mul i x hx =>
    rw [comul_θ_mul, map_add, map_add]
    generalize comul D v x = W at hx
    have h1 : ∀ W : LusztigF k I ⊗[k] LusztigF k I,
        (counit (k := k) (I := I)).toLinearMap.rTensor _
          ((LinearMap.mulLeft k (θ k i)).rTensor _ W) = 0 := by
      intro W
      induction W with
      | tmul e f => simp
      | add X Y hX hY => simp only [map_add, hX, hY, add_zero]
    have h2 : ∀ W : LusztigF k I ⊗[k] LusztigF k I,
        TensorProduct.lid k _ ((counit (k := k) (I := I)).toLinearMap.rTensor _
          (TensorProduct.map (twist D v i).toLinearMap (LinearMap.mulLeft k (θ k i)) W)) =
        θ k i * TensorProduct.lid k _ ((counit (k := k) (I := I)).toLinearMap.rTensor _ W) := by
      intro W
      induction W with
      | tmul e f => simp
      | add X Y hX hY => simp only [map_add, hX, hY, mul_add]
    rw [h1, h2, hx, map_zero, zero_add]

/-- `r ∘ σⱼ = (σⱼ ⊗ σⱼ) ∘ r`. -/
theorem comul_twist (j : I) (x : LusztigF k I) :
    comul D v (twist D v j x) =
      TensorProduct.map (twist D v j).toLinearMap (twist D v j).toLinearMap (comul D v x) := by
  induction x using induction_left with
  | algebraMap c => simp [Algebra.algebraMap_eq_smul_one]
  | smul c x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | θ_mul i x hx =>
    rw [map_mul, twist_θ, smul_mul_assoc, map_smul, comul_θ_mul, comul_θ_mul, hx]
    have e1 : ∀ W : LusztigF k I ⊗[k] LusztigF k I,
        TensorProduct.map (twist D v j).toLinearMap (twist D v j).toLinearMap
          ((LinearMap.mulLeft k (θ k i)).rTensor _ W) = v ^ D.dot j i •
          (LinearMap.mulLeft k (θ k i)).rTensor _
            (TensorProduct.map (twist D v j).toLinearMap (twist D v j).toLinearMap W) := by
      intro W
      induction W with
      | tmul e f => simp [TensorProduct.smul_tmul']
      | add X Y hX hY => simp only [map_add, smul_add, hX, hY]
    have e2 : ∀ W : LusztigF k I ⊗[k] LusztigF k I,
        TensorProduct.map (twist D v j).toLinearMap (twist D v j).toLinearMap
          (TensorProduct.map (twist D v i).toLinearMap (LinearMap.mulLeft k (θ k i)) W) =
        v ^ D.dot j i • TensorProduct.map (twist D v i).toLinearMap (LinearMap.mulLeft k (θ k i))
            (TensorProduct.map (twist D v j).toLinearMap (twist D v j).toLinearMap W) := by
      intro W
      induction W with
      | tmul e f => simp [twist_comm D v i j, TensorProduct.tmul_smul]
      | add X Y hX hY => simp only [map_add, smul_add, hX, hY]
    rw [map_add, e1, e2, smul_add]

/-- `(1 ⊗ rⱼ) ∘ r = r ∘ rⱼ` (a form of [Lus] 1.2.13 (check)). -/
theorem lTensor_rDeriv_comul [DecidableEq I] (j : I) (x : LusztigF k I) :
    (rDeriv D v j).lTensor _ (comul D v x) = comul D v (rDeriv D v j x) := by
  induction x using induction_left with
  | algebraMap c => simp [Algebra.algebraMap_eq_smul_one]
  | smul c x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | θ_mul i x hx =>
    rw [comul_θ_mul, rDeriv_θ_mul, map_add, map_add, comul_θ_mul, ← hx]
    have key : ∀ W : LusztigF k I ⊗[k] LusztigF k I,
        (rDeriv D v j).lTensor _ ((LinearMap.mulLeft k (θ k i)).rTensor _ W) +
          (rDeriv D v j).lTensor _
            (TensorProduct.map (twist D v i).toLinearMap (LinearMap.mulLeft k (θ k i)) W) =
        (LinearMap.mulLeft k (θ k i)).rTensor _ ((rDeriv D v j).lTensor _ W) +
          TensorProduct.map (twist D v i).toLinearMap (LinearMap.mulLeft k (θ k i))
            ((rDeriv D v j).lTensor _ W) +
          if j = i then TensorProduct.map (twist D v j).toLinearMap (twist D v j).toLinearMap W
          else 0 := by
      intro W
      induction W with
      | tmul e f =>
        simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_tmul,
          LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, rDeriv_θ_mul]
        split_ifs with h
        · subst h; rw [tmul_add]; abel
        · simp
      | add X Y hX hY =>
        simp only [map_add] at hX hY ⊢
        split_ifs at hX hY ⊢ <;> [rw [← add_add_add_comm, hX, hY]; rw [← add_add_add_comm, hX, hY]]
        <;> abel
    rw [key]
    split_ifs with h
    · subst h; rw [comul_twist]
    · simp

/-- `(ε ∘ rᵢ ⊗ 1) ∘ r = ᵢr` (a form of [Lus] 1.2.13 (check)). -/
theorem lid_rTensor_counit_rDeriv_comul [DecidableEq I] (i : I) (y : LusztigF k I) :
    TensorProduct.lid k _ (((counit (k := k) (I := I)).toLinearMap ∘ₗ rDeriv D v i).rTensor _
      (comul D v y)) = lDeriv D v i y := by
  induction y using induction_left with
  | algebraMap c => simp [Algebra.algebraMap_eq_smul_one]
  | smul c x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | θ_mul j y hy =>
    rw [comul_θ_mul, map_add, map_add, lDeriv_θ_mul]
    have e1 : ∀ W : LusztigF k I ⊗[k] LusztigF k I,
        TensorProduct.lid k _ (((counit (k := k) (I := I)).toLinearMap ∘ₗ rDeriv D v i).rTensor _
          ((LinearMap.mulLeft k (θ k j)).rTensor _ W)) = (if i = j then (1 : k) else 0) •
          TensorProduct.lid k _ ((counit (k := k) (I := I)).toLinearMap.rTensor _ W) := by
      intro W
      induction W with
      | tmul e f =>
        simp only [LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, LinearMap.coe_comp,
          Function.comp_apply, AlgHom.toLinearMap_apply, counit_rDeriv_θ_mul, lid_tmul]
        split_ifs <;> simp
      | add X Y hX hY => simp only [map_add, smul_add, hX, hY]
    have e2 : ∀ W : LusztigF k I ⊗[k] LusztigF k I,
        TensorProduct.lid k _ (((counit (k := k) (I := I)).toLinearMap ∘ₗ rDeriv D v i).rTensor _
          (TensorProduct.map (twist D v j).toLinearMap (LinearMap.mulLeft k (θ k j)) W)) =
        v ^ D.dot i j • (θ k j * TensorProduct.lid k _
          (((counit (k := k) (I := I)).toLinearMap ∘ₗ rDeriv D v i).rTensor _ W)) := by
      intro W
      induction W with
      | tmul e f =>
        simp only [map_tmul, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, LinearMap.coe_comp,
          Function.comp_apply, AlgHom.toLinearMap_apply, lid_tmul, rDeriv_twist, map_smul,
          counit_twist, smul_eq_mul, mul_smul_comm, smul_smul]
      | add X Y hX hY => simp only [map_add, smul_add, mul_add, hX, hY]
    rw [e1, e2, hy, lid_rTensor_counit_comul]
    split_ifs <;> simp

end LusztigF
