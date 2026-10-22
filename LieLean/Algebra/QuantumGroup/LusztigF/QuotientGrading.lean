/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.LusztigF.QuotientComul
import LieLean.Algebra.QuantumGroup.Faithful

/-!
# Weight grading, twists and the coproduct on `f`

Lusztig's coproduct `r : 'f → 'f ⊗ 'f` ([Lus] 1.2.2) is a twisted algebra homomorphism. For the
tensor product decomposition of [Lus] 35.4.2 we need three consequences, which we prove on `'f`
and on the radical quotient `f` over `ℚ(v)`:

* right multiplication by a generator: `r(xθᵢ) = (·θᵢ ⊗ σᵢ)(r x) + (1 ⊗ ·θᵢ)(r x)`;
* weight support: for `x ∈ 'f_β`, the component of `r(x)` in `'f_α ⊗ 'f_γ` vanishes unless
  `α + γ = β`;
* the top component: the component of `r(x)` in `'f ⊗ 'f_β` is `1 ⊗ x`.

## Main definitions

* `LieLean.QuantumGroup.quotientWeightProj`: the projection of `f` onto `f_ν`.
* `LieLean.QuantumGroup.quotientTwist`: the twist `σᵢ` on `f`.

## Main results

* `LusztigF.comul_mul_θ`, `LieLean.QuantumGroup.quotientComul_mul_θ`.
* `LusztigF.map_weightProj_comul_of_ne`, `LieLean.QuantumGroup.map_quotientWeightProj_comul_of_ne`.
* `LusztigF.lTensor_weightProj_comul`, `LieLean.QuantumGroup.lTensor_quotientWeightProj_comul`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.2.2, 35.4.2.
-/

open LieLean TensorProduct
noncomputable section

namespace LusztigF

variable {k I : Type*} [Field k] (D : LusztigCartanDatum I) (v : k)

lemma twistAct_θ_tmul (i : I) (b d : LusztigF k I) :
    twistAct D v b (θ k i ⊗ₜ d) = θ k i ⊗ₜ (twist D v i b * d) := by
  induction b using FreeAlgebra.induction generalizing d with
  | grade0 c =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    rw [← Algebra.smul_def, tmul_smul]
  | grade1 j =>
    change twistAct D v (θ k j) _ = θ k i ⊗ₜ (twist D v i (θ k j) * d)
    simp [twistAct_θ, D.dot_comm i j, TensorProduct.smul_tmul]
  | mul a b ha hb => rw [map_mul, Module.End.mul_apply, hb, ha, map_mul, mul_assoc]
  | add a b ha hb => rw [map_add, LinearMap.add_apply, ha, hb, map_add, add_mul, tmul_add]

/-- Right multiplication by a generator: `r(xθᵢ) = (·θᵢ ⊗ σᵢ)(r x) + (1 ⊗ ·θᵢ)(r x)`. -/
theorem comul_mul_θ (i : I) (x : LusztigF k I) :
    comul D v (x * θ k i) =
      TensorProduct.map (LinearMap.mulRight k (θ k i)) (twist D v i).toLinearMap (comul D v x) +
        (LinearMap.mulRight k (θ k i)).lTensor _ (comul D v x) := by
  rw [comul_mul, comul_θ, map_add]
  congr 1
  · induction comul D v x with
    | tmul a b => simp [twistedMul_tmul, twistAct_θ_tmul]
    | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY]
  · induction comul D v x with
    | tmul a b => simp [twistedMul_tmul, twistAct_one_tmul]
    | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY]

variable [DecidableEq I]

/-- The tensors whose components lie in `'f_α ⊗ 'f_γ` with `α + γ = β`. -/
def comulSupport (β : I →₀ ℕ) : Submodule k (LusztigF k I ⊗[k] LusztigF k I) :=
  Submodule.span k {z | ∃ α γ a c, α + γ = β ∧ a ∈ weightSpace k α ∧ c ∈ weightSpace k γ ∧
    z = a ⊗ₜ c}

omit [DecidableEq I] in
lemma comul_mem_comulSupport {β : I →₀ ℕ} {x : LusztigF k I} (hx : x ∈ weightSpace k β) :
    comul D v x ∈ comulSupport β := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl, rfl⟩ := hy
    induction w with
    | nil =>
      refine Submodule.subset_span ⟨0, 0, 1, 1, by simp [wordWeight], one_mem_weightSpace,
        one_mem_weightSpace, ?_⟩
      simp [monomial]
    | cons l w ih =>
      rw [monomial_cons, comul_θ_mul]
      refine Submodule.add_mem _ ?_ ?_
      · refine Submodule.span_induction (p := fun z _ ↦
          (LinearMap.mulLeft k (θ k l)).rTensor _ z ∈ comulSupport (wordWeight (l :: w)))
          ?_ (by simp) (fun _ _ _ _ h₁ h₂ ↦ by rw [map_add]; exact Submodule.add_mem _ h₁ h₂)
          (fun c _ _ h ↦ by rw [map_smul]; exact Submodule.smul_mem _ _ h) ih
        rintro _ ⟨α, γ, a, c, hαγ, ha, hc, rfl⟩
        refine Submodule.subset_span ⟨Finsupp.single l 1 + α, γ, θ k l * a, c, ?_,
          mul_mem_weightSpace (θ_mem_weightSpace l) ha, hc, rfl⟩
        rw [wordWeight_cons, ← hαγ, add_assoc]
      · refine Submodule.span_induction (p := fun z _ ↦
          TensorProduct.map (twist D v l).toLinearMap (LinearMap.mulLeft k (θ k l)) z ∈
            comulSupport (wordWeight (l :: w)))
          ?_ (by simp) (fun _ _ _ _ h₁ h₂ ↦ by rw [map_add]; exact Submodule.add_mem _ h₁ h₂)
          (fun c _ _ h ↦ by rw [map_smul]; exact Submodule.smul_mem _ _ h) ih
        rintro _ ⟨α, γ, a, c, hαγ, ha, hc, rfl⟩
        refine Submodule.subset_span ⟨α, Finsupp.single l 1 + γ, twist D v l a, θ k l * c, ?_,
          twist_mem_weightSpace D v l ha, mul_mem_weightSpace (θ_mem_weightSpace l) hc, rfl⟩
        rw [wordWeight_cons, ← hαγ]; abel
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

lemma map_weightProj_of_mem_comulSupport {α γ β : I →₀ ℕ} (h : α + γ ≠ β)
    {z : LusztigF k I ⊗[k] LusztigF k I} (hz : z ∈ comulSupport β) :
    TensorProduct.map (weightProj α) (weightProj γ) z = 0 := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨α', γ', a, c, hαγ, ha, hc, rfl⟩ := hz
    rw [map_tmul, weightProj_of_mem ha, weightProj_of_mem hc]
    by_cases h₁ : α' = α
    · by_cases h₂ : γ' = γ
      · exact absurd (h₁ ▸ h₂ ▸ hαγ) h
      · simp [h₂]
    · simp [h₁]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]

/-- Weight support of the coproduct: for `x ∈ 'f_β`, the component of `r(x)` in
`'f_α ⊗ 'f_γ` vanishes unless `α + γ = β`. -/
theorem map_weightProj_comul_of_ne {α γ β : I →₀ ℕ} (h : α + γ ≠ β) {x : LusztigF k I}
    (hx : x ∈ weightSpace k β) :
    TensorProduct.map (weightProj α) (weightProj γ) (comul D v x) = 0 :=
  map_weightProj_of_mem_comulSupport h (comul_mem_comulSupport D v hx)

/-- The top component of the coproduct: for `x ∈ 'f_β`, `(1 ⊗ P_β)(r x) = 1 ⊗ x`. -/
theorem lTensor_weightProj_comul {β : I →₀ ℕ} {x : LusztigF k I} (hx : x ∈ weightSpace k β) :
    (weightProj β).lTensor _ (comul D v x) = 1 ⊗ₜ x := by
  classical
  -- On `comulSupport β`, `1 ⊗ P_β` agrees with `P_0 ⊗ 1`, which is `z ↦ 1 ⊗ (ε ⊗ 1) z`.
  have key : ∀ z ∈ comulSupport (k := k) β, (weightProj β).lTensor _ z =
      1 ⊗ₜ TensorProduct.lid k _ ((counit (k := k) (I := I)).toLinearMap.rTensor _ z) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨α, γ, a, c, hαγ, ha, hc, rfl⟩ := hz
      rw [LinearMap.lTensor_tmul, weightProj_of_mem hc, LinearMap.rTensor_tmul,
        TensorProduct.lid_tmul, AlgHom.toLinearMap_apply]
      by_cases hγ : γ = β
      · subst hγ
        have hα : α = 0 := by simpa using hαγ
        subst hα
        simp only [↓reduceIte]
        rw [eq_algebraMap_of_mem_weightSpace_zero ha, Algebra.algebraMap_eq_smul_one,
          map_smul, map_one, smul_eq_mul, mul_one, smul_tmul]
      · simp only [hγ, ↓reduceIte, tmul_zero]
        have hα : α ≠ 0 := by rintro rfl; exact hγ (by simpa using hαγ)
        have : counit (k := k) a = 0 := by
          rw [← counit_weightProj_zero, weightProj_of_mem ha]
          simp [hα]
        rw [this, zero_smul, tmul_zero]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, hy, hz, map_add, map_add, tmul_add]
    | smul c y _ hy => rw [map_smul, hy, map_smul, map_smul, tmul_smul]
  rw [key _ (comul_mem_comulSupport D v hx), lid_rTensor_counit_comul]

end LusztigF

namespace LieLean.QuantumGroup
open LusztigF
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- The weight space `f_ν` of the radical quotient. -/
def quotientWeightSpace (ν : I →₀ ℕ) : Submodule 𝕂 (Quotient D 𝕧) :=
  (LusztigF.weightSpace 𝕂 ν).map (toQuotient D 𝕧).toLinearMap

/-- The projection of `f` onto `f_ν`, descended from `'f`. -/
def quotientWeightProj (ν : I →₀ ℕ) : Module.End 𝕂 (Quotient D 𝕧) :=
  ((serreSubmodule D 𝕧).liftQ ((toQuotient D 𝕧).toLinearMap ∘ₗ LusztigF.weightProj ν) (by
      intro x hx
      change toQuotient D 𝕧 (LusztigF.weightProj ν x) = 0
      rw [toQuotient_eq_zero_iff, radical_eq_serreIdeal_ratFunc]
      exact weightProj_mem_serreIdeal (mem_serreSubmodule.mp hx) ν)).comp
    (negativeQuotientEquiv D).symm.toLinearMap

@[simp] lemma quotientWeightProj_toQuotient (ν : I →₀ ℕ) (x : LusztigF 𝕂 I) :
    quotientWeightProj D ν (toQuotient D 𝕧 x) = toQuotient D 𝕧 (LusztigF.weightProj ν x) := by
  simp [quotientWeightProj]

lemma quotientWeightProj_mem (ν : I →₀ ℕ) (x : Quotient D 𝕧) :
    quotientWeightProj D ν x ∈ quotientWeightSpace D ν := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  rw [quotientWeightProj_toQuotient]
  exact Submodule.mem_map_of_mem (weightProj_mem ν x)

lemma quotientWeightProj_of_mem {ν μ : I →₀ ℕ} {x : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D μ) :
    quotientWeightProj D ν x = if μ = ν then x else 0 := by
  classical
  obtain ⟨x, hx, rfl⟩ := hx
  rw [AlgHom.toLinearMap_apply, quotientWeightProj_toQuotient, weightProj_of_mem hx]
  split_ifs <;> simp

/-- The twist `σᵢ` (`θⱼ ↦ v^{i·j} θⱼ`) on `f`. -/
def quotientTwist (i : I) : Quotient D 𝕧 →ₐ[𝕂] Quotient D 𝕧 :=
  (radical D 𝕧).ringCon.liftₐ ((toQuotient D 𝕧).comp (twist D 𝕧 i)) fun x y h ↦ by
    apply sub_eq_zero.mp
    rw [← map_sub]
    change toQuotient D 𝕧 (twist D 𝕧 i (x - y)) = 0
    rw [toQuotient_eq_zero_iff,
      radical_eq_serreIdeal_ratFunc]
    have hxy := ((radical D 𝕧).rel_iff x y).mp h
    rw [radical_eq_serreIdeal_ratFunc] at hxy
    exact twist_mem_serreIdeal i hxy

@[simp] lemma quotientTwist_toQuotient (i : I) (x : LusztigF 𝕂 I) :
    quotientTwist D i (toQuotient D 𝕧 x) = toQuotient D 𝕧 (twist D 𝕧 i x) := rfl

/-- `r(xθᵢ) = (·θᵢ ⊗ σᵢ)(r x) + (1 ⊗ ·θᵢ)(r x)` on `f`. -/
theorem quotientComul_mul_θ (i : I) (x : Quotient D 𝕧) :
    quotientComul D (x * toQuotient D 𝕧 (θ 𝕂 i)) =
      TensorProduct.map (LinearMap.mulRight 𝕂 (toQuotient D 𝕧 (θ 𝕂 i)))
          (quotientTwist D i).toLinearMap (quotientComul D x) +
        (LinearMap.mulRight 𝕂 (toQuotient D 𝕧 (θ 𝕂 i))).lTensor _ (quotientComul D x) := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  rw [← map_mul, quotientComul_toQuotient, quotientComul_toQuotient, comul_mul_θ, map_add]
  congr 1
  · induction LusztigF.comul D 𝕧 x with
    | tmul a b => simp
    | add X Y hX hY => simp only [map_add, hX, hY]
  · induction LusztigF.comul D 𝕧 x with
    | tmul a b => simp
    | add X Y hX hY => simp only [map_add, hX, hY]

lemma map_quotientWeightProj_quotientTensorMap (α γ : I →₀ ℕ)
    (z : LusztigF 𝕂 I ⊗[𝕂] LusztigF 𝕂 I) :
    TensorProduct.map (quotientWeightProj D α) (quotientWeightProj D γ) (quotientTensorMap D z) =
      quotientTensorMap D (TensorProduct.map (LusztigF.weightProj α) (LusztigF.weightProj γ) z) := by
  induction z with
  | tmul a b => simp
  | add X Y hX hY => simp only [map_add, hX, hY]

/-- Weight support of the coproduct of `f`. -/
theorem map_quotientWeightProj_comul_of_ne {α γ β : I →₀ ℕ} (h : α + γ ≠ β)
    {x : Quotient D 𝕧} (hx : x ∈ quotientWeightSpace D β) :
    TensorProduct.map (quotientWeightProj D α) (quotientWeightProj D γ) (quotientComul D x) = 0 := by
  obtain ⟨x, hx, rfl⟩ := hx
  rw [AlgHom.toLinearMap_apply, quotientComul_toQuotient,
    map_quotientWeightProj_quotientTensorMap, map_weightProj_comul_of_ne D 𝕧 h hx, map_zero]

/-- The top component of the coproduct of `f`: `(1 ⊗ P_β)(r x) = 1 ⊗ x` for `x ∈ f_β`. -/
theorem lTensor_quotientWeightProj_comul {β : I →₀ ℕ} {x : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D β) :
    (quotientWeightProj D β).lTensor _ (quotientComul D x) = 1 ⊗ₜ x := by
  obtain ⟨x, hx, rfl⟩ := hx
  rw [AlgHom.toLinearMap_apply, quotientComul_toQuotient]
  have : (quotientWeightProj D β).lTensor _ (quotientTensorMap D (LusztigF.comul D 𝕧 x)) =
      quotientTensorMap D ((LusztigF.weightProj β).lTensor _ (LusztigF.comul D 𝕧 x)) := by
    induction LusztigF.comul D 𝕧 x with
    | tmul a b => simp
    | add X Y hX hY => simp only [map_add, hX, hY]
  rw [this, lTensor_weightProj_comul D 𝕧 hx]
  simp

end LieLean.QuantumGroup
