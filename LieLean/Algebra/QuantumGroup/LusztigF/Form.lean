/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import LieLean.Algebra.QuantumGroup.LusztigF.Comul

/-!
# Lusztig's bilinear form on `'f` and the algebra `f`

By [Lus] Prop. 1.2.3 (check) there is a unique bilinear form `(·, ·)` on `'f` with values in
`k = ℚ(v)` such that `(1, 1) = 1` and
* (a) `(θᵢ, θⱼ) = δᵢⱼ (1 - vᵢ⁻²)⁻¹`;
* (b) `(x, y'y'') = (r(x), y' ⊗ y'')`;
* (c) `(x'x'', y) = (x' ⊗ x'', r(y))`,
where `(x₁ ⊗ x₂, y₁ ⊗ y₂) = (x₁, y₁)(x₂, y₂)` on `'f ⊗ 'f`; it is symmetric.

We construct the form directly as `(x, y) = ε(Ψ(x) y)`, where `ε` is the counit and
`Ψ : 'f → End('f)` is the algebra homomorphism `θᵢ ↦ (θᵢ, θᵢ) rᵢ` (`formEnd`); thus
`(x θᵢ, y) = (θᵢ, θᵢ)(x, rᵢ(y))` holds by construction ([Lus] 1.2.13 (a) (check)). We then prove
`(x, y θⱼ) = (θⱼ, θⱼ)(rⱼ(x), y)` (`form_mul_θ_right`), symmetry (`form_comm`), (b)
(`form_mul_right`, using `(1 ⊗ rⱼ) ∘ r = r ∘ rⱼ`), (c) (`form_mul_left`), and
`(θᵢ x, y) = (θᵢ, θᵢ)(x, ᵢr(y))` (`form_θ_mul`). This route (rather than Lusztig's, via the
graded dual of `'f`) is our own.

The radical `I = {x | ∀ y, (x, y) = 0}` of the form is a two-sided ideal (by (c)), and
`f = 'f / I` ([Lus] 1.2.5 (check)).

## Main definitions

* `LusztigF.thetaNorm D v i`: `(θᵢ, θᵢ) = (1 - vᵢ⁻²)⁻¹` with `vᵢ = v^{dᵢ}`.
* `LusztigF.form D v`: Lusztig's bilinear form on `'f`.
* `LusztigF.formTensor D v`: the induced form on `'f ⊗ 'f`.
* `LusztigF.radical D v`: the radical, as a two-sided ideal.
* `LusztigF.Quotient D v`: Lusztig's algebra `f = 'f / radical`, with `LusztigF.toQuotient`.

## Main results

* `LusztigF.form_one_one`, `LusztigF.form_θ_θ`: normalization.
* `LusztigF.form_mul_right` (b), `LusztigF.form_mul_left` (c), `LusztigF.form_comm`.
* `LusztigF.form_mul_θ`, `LusztigF.form_θ_mul`: the adjunction with `rᵢ`, `ᵢr`.
* `LusztigF.form_eq_zero_of_ne`: distinct weight spaces are orthogonal.
* `LusztigF.mem_radical_iff`, `LusztigF.ker_toQuotient`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §1.2.
-/

noncomputable section

open TensorProduct

namespace LusztigF

variable {k I : Type*} [Field k] [DecidableEq I] (D : CartanDatum I) (v : k)

/-- `(θᵢ, θᵢ) = (1 - vᵢ⁻²)⁻¹`, `vᵢ = v^{dᵢ}` ([Lus] 1.2.3 (a) (check)). -/
def thetaNorm (i : I) : k := (1 - (v ^ D.d i)⁻¹ ^ 2)⁻¹

/-- The algebra homomorphism `Ψ : 'f → End('f)`, `θᵢ ↦ (θᵢ, θᵢ) rᵢ`. -/
def formEnd : LusztigF k I →ₐ[k] Module.End k (LusztigF k I) :=
  FreeAlgebra.lift k fun i ↦ thetaNorm D v i • rDeriv D v i

/-- Lusztig's bilinear form `(·, ·)` on `'f` ([Lus] 1.2.3 (check)), `(x, y) = ε(Ψ(x) y)`. -/
def form : LinearMap.BilinForm k (LusztigF k I) :=
  (formEnd D v).toLinearMap.compr₂ (counit (k := k) (I := I)).toLinearMap

lemma form_apply (x y : LusztigF k I) : form D v x y = counit (formEnd D v x y) := rfl

lemma formEnd_apply_one (x : LusztigF k I) :
    formEnd D v x 1 = algebraMap k _ (counit x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp [Algebra.algebraMap_eq_smul_one]
  | grade1 i => simp [formEnd]
  | mul a b ha hb =>
    rw [map_mul, Module.End.mul_apply, hb, Algebra.algebraMap_eq_smul_one, map_smul, ha,
      map_mul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul,
      mul_comm]
  | add a b ha hb => simp [ha, hb]

@[simp] lemma form_algebraMap_left (c : k) (y : LusztigF k I) :
    form D v (algebraMap k _ c) y = c * counit y := by
  simp [form_apply, Module.algebraMap_end_apply]

@[simp] lemma form_algebraMap_right (x : LusztigF k I) (c : k) :
    form D v x (algebraMap k _ c) = c * counit x := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, form_apply, formEnd_apply_one]
  simp

@[simp] lemma form_one_left (y : LusztigF k I) : form D v 1 y = counit y := by
  simpa using form_algebraMap_left D v 1 y

@[simp] lemma form_one_right (x : LusztigF k I) : form D v x 1 = counit x := by
  simpa using form_algebraMap_right D v x 1

/-- `(1, 1) = 1`. -/
theorem form_one_one : form D v (1 : LusztigF k I) 1 = 1 := by simp

/-- `(x θᵢ, y) = (θᵢ, θᵢ)(x, rᵢ(y))` ([Lus] 1.2.13 (a) (check)). -/
theorem form_mul_θ (x : LusztigF k I) (i : I) (y : LusztigF k I) :
    form D v (x * θ k i) y = thetaNorm D v i * form D v x (rDeriv D v i y) := by
  simp [form_apply, formEnd]

/-- `(θᵢ, θⱼ) = δᵢⱼ (1 - vᵢ⁻²)⁻¹` ([Lus] 1.2.3 (a) (check)). -/
theorem form_θ_θ (i j : I) :
    form D v (θ k i) (θ k j) = if i = j then thetaNorm D v i else 0 := by
  have := form_mul_θ D v 1 i (θ k j)
  rw [one_mul] at this
  rw [this, rDeriv_θ]
  split_ifs <;> simp

/-- `(x, y θⱼ) = (θⱼ, θⱼ)(rⱼ(x), y)`. -/
theorem form_mul_θ_right (x y : LusztigF k I) (j : I) :
    form D v x (y * θ k j) = thetaNorm D v j * form D v (rDeriv D v j x) y := by
  induction x using induction_right generalizing y with
  | algebraMap c => simp
  | smul c x hx => simp [hx, mul_left_comm]
  | add x x' hx hx' => simp [hx, hx', mul_add]
  | mul_θ x i hx =>
    rw [form_mul_θ, rDeriv_mul_θ, map_add, map_smul, hx, rDeriv_mul_θ]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, form_mul_θ,
      smul_eq_mul]
    by_cases h : i = j
    · subst h; simp only [ite_true]
    · simp only [h, Ne.symm h, ite_false, map_zero, LinearMap.zero_apply, D.dot_comm]
      ring

/-- Lusztig's form is symmetric ([Lus] 1.2.3 (check)). -/
theorem form_comm (x y : LusztigF k I) : form D v x y = form D v y x := by
  induction y using induction_right generalizing x with
  | algebraMap c => simp
  | smul c y hy => simp [hy]
  | add y y' hy hy' => simp [hy, hy']
  | mul_θ y j hy => rw [form_mul_θ_right, hy, form_mul_θ]

theorem isSymm_form : LinearMap.IsSymm (form D v) :=
  LinearMap.isSymm_def.2 fun x y ↦ by simpa using form_comm D v x y

/-- The bilinear form `(x₁ ⊗ x₂, y₁ ⊗ y₂) = (x₁, y₁)(x₂, y₂)` on `'f ⊗ 'f`. -/
def formTensor : LinearMap.BilinForm k (LusztigF k I ⊗[k] LusztigF k I) :=
  (form D v).tmul (form D v)

@[simp] lemma formTensor_tmul (x₁ x₂ y₁ y₂ : LusztigF k I) :
    formTensor D v (x₁ ⊗ₜ x₂) (y₁ ⊗ₜ y₂) = form D v x₁ y₁ * form D v x₂ y₂ := by
  simp [formTensor, mul_comm]

lemma formTensor_comm (X Y : LusztigF k I ⊗[k] LusztigF k I) :
    formTensor D v X Y = formTensor D v Y X := by
  induction X generalizing Y with
  | tmul a b =>
    induction Y with
    | tmul c d => simp [form_comm D v a, form_comm D v b]
    | add Y Z hY hZ => simp [hY, hZ]
  | add X X' hX hX' => simp [hX, hX']

lemma formTensor_tmul_one (W : LusztigF k I ⊗[k] LusztigF k I) (y : LusztigF k I) :
    formTensor D v W (y ⊗ₜ 1) =
      form D v (TensorProduct.rid k _ ((counit (k := k) (I := I)).toLinearMap.lTensor _ W)) y := by
  induction W with
  | tmul a b => simp [mul_comm]
  | add X Y hX hY => simp [hX, hY]

lemma formTensor_tmul_mul_θ (W : LusztigF k I ⊗[k] LusztigF k I) (y z : LusztigF k I) (j : I) :
    formTensor D v W (y ⊗ₜ (z * θ k j)) =
      thetaNorm D v j * formTensor D v ((rDeriv D v j).lTensor _ W) (y ⊗ₜ z) := by
  induction W with
  | tmul a b => simp [form_mul_θ_right, mul_left_comm]
  | add X Y hX hY => simp [hX, hY, mul_add]

/-- Lusztig's property (b): `(x, y'y'') = (r(x), y' ⊗ y'')` ([Lus] 1.2.3 (b) (check)). -/
theorem form_mul_right (x y' y'' : LusztigF k I) :
    form D v x (y' * y'') = formTensor D v (comul D v x) (y' ⊗ₜ y'') := by
  induction y'' using induction_right generalizing x with
  | algebraMap c =>
    rw [← Algebra.commutes, ← Algebra.smul_def, map_smul, Algebra.algebraMap_eq_smul_one,
      tmul_smul, map_smul, formTensor_tmul_one, rid_lTensor_counit_comul]
  | smul c y hy => rw [mul_smul_comm, map_smul, hy, tmul_smul, map_smul]
  | add y z hy hz => rw [mul_add, map_add, hy, hz, tmul_add, map_add]
  | mul_θ y j hy =>
    rw [← mul_assoc, form_mul_θ_right, hy, formTensor_tmul_mul_θ, lTensor_rDeriv_comul]

/-- Lusztig's property (c): `(x'x'', y) = (x' ⊗ x'', r(y))` ([Lus] 1.2.3 (c) (check)). -/
theorem form_mul_left (x' x'' y : LusztigF k I) :
    form D v (x' * x'') y = formTensor D v (x' ⊗ₜ x'') (comul D v y) := by
  rw [form_comm, form_mul_right, formTensor_comm]

lemma formTensor_θ_tmul (i : I) (x : LusztigF k I) (W : LusztigF k I ⊗[k] LusztigF k I) :
    formTensor D v (θ k i ⊗ₜ x) W = thetaNorm D v i * form D v x (TensorProduct.lid k _
      (((counit (k := k) (I := I)).toLinearMap ∘ₗ rDeriv D v i).rTensor _ W)) := by
  induction W with
  | tmul a b =>
    have := form_mul_θ D v 1 i a
    rw [one_mul] at this
    simp [this, mul_assoc]
  | add X Y hX hY => simp [hX, hY, mul_add]

/-- `(θᵢ x, y) = (θᵢ, θᵢ)(x, ᵢr(y))` ([Lus] 1.2.13 (a) (check)). -/
theorem form_θ_mul (i : I) (x y : LusztigF k I) :
    form D v (θ k i * x) y = thetaNorm D v i * form D v x (lDeriv D v i y) := by
  rw [form_mul_left, formTensor_θ_tmul, lid_rTensor_counit_rDeriv_comul]

/-! ### Orthogonality of weight spaces -/

omit [DecidableEq I] in
lemma twist_mem_weightSpace (i : I) {ν : I →₀ ℕ} {x : LusztigF k I}
    (hx : x ∈ weightSpace k ν) : twist D v i x ∈ weightSpace k ν := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl, rfl⟩ := hy
    induction w with
    | nil => simpa [monomial] using one_mem_weightSpace
    | cons l w ih =>
      rw [monomial_cons, map_mul, twist_θ, smul_mul_assoc, wordWeight_cons]
      exact Submodule.smul_mem _ _ (mul_mem_weightSpace (θ_mem_weightSpace l) ih)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

omit [DecidableEq I] in
lemma counit_eq_zero_of_mem {ν : I →₀ ℕ} (hν : ν ≠ 0) {x : LusztigF k I}
    (hx : x ∈ weightSpace k ν) : counit x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    cases w with
    | nil => exact absurd hw.symm hν
    | cons l w => simp
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

lemma rDeriv_monomial_eq_zero (i : I) (w : List I) (hw : wordWeight w i = 0) :
    rDeriv D v i (monomial k w) = 0 := by
  induction w with
  | nil => simp
  | cons l w ih =>
    have hl : l ≠ i := by
      rintro rfl; simp at hw
    have hw' : wordWeight w i = 0 := by
      simp only [wordWeight_cons, Finsupp.add_apply] at hw; omega
    rw [monomial_cons, rDeriv_θ_mul, ih hw']
    simp [Ne.symm hl]

lemma rDeriv_monomial_mem (i : I) (w : List I) :
    ∀ μ, wordWeight w = μ + Finsupp.single i 1 →
      rDeriv D v i (monomial k w) ∈ weightSpace k μ := by
  induction w with
  | nil =>
    intro μ h
    have := congr($h i)
    simp at this
  | cons l w ih =>
    intro μ h
    rw [monomial_cons, rDeriv_θ_mul]
    rw [wordWeight_cons] at h
    -- the term `θₗ rᵢ(m)`
    have h1 : θ k l * rDeriv D v i (monomial k w) ∈ weightSpace k μ := by
      by_cases hwi : wordWeight w i = 0
      · rw [rDeriv_monomial_eq_zero D v i w hwi, mul_zero]; exact Submodule.zero_mem _
      · have hw : wordWeight w = (wordWeight w - Finsupp.single i 1) + Finsupp.single i 1 := by
          ext j
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          split_ifs with hij
          · subst hij; omega
          · omega
        have hμ : μ = Finsupp.single l 1 + (wordWeight w - Finsupp.single i 1) := by
          ext j
          have := congr($h j)
          simp only [Finsupp.add_apply, Finsupp.tsub_apply] at this ⊢
          by_cases hij : i = j
          · subst hij
            simp only [Finsupp.single_eq_same] at this ⊢
            omega
          · rw [Finsupp.single_eq_of_ne (Ne.symm hij)] at this ⊢
            omega
        rw [hμ]
        exact mul_mem_weightSpace (θ_mem_weightSpace l) (ih _ hw)
    split_ifs with hil
    · subst hil
      have : wordWeight w = μ := by
        rw [add_comm] at h; exact add_right_cancel h
      exact Submodule.add_mem _ h1
        (this ▸ twist_mem_weightSpace D v i (monomial_mem_weightSpace w))
    · rw [add_zero]; exact h1

lemma rDeriv_mem_weightSpace (i : I) {μ : I →₀ ℕ} {y : LusztigF k I}
    (hy : y ∈ weightSpace k (μ + Finsupp.single i 1)) : rDeriv D v i y ∈ weightSpace k μ := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    exact rDeriv_monomial_mem D v i w μ hw
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

lemma rDeriv_eq_zero_of_mem (i : I) {μ : I →₀ ℕ} (hμ : μ i = 0) {y : LusztigF k I}
    (hy : y ∈ weightSpace k μ) : rDeriv D v i y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl, rfl⟩ := hy
    exact rDeriv_monomial_eq_zero D v i w hμ
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]

lemma form_monomial_eq_zero (w : List I) :
    ∀ μ y, y ∈ weightSpace k μ → wordWeight w ≠ μ → form D v (monomial k w) y = 0 := by
  induction w using List.reverseRecOn with
  | nil =>
    intro μ y hy hμ
    rw [monomial_nil, form_one_left, counit_eq_zero_of_mem (Ne.symm hμ) hy]
  | append_singleton w i ih =>
    intro μ y hy hμ
    rw [monomial_append, show monomial k [i] = θ k i by simp [monomial], form_mul_θ]
    by_cases hμi : μ i = 0
    · rw [rDeriv_eq_zero_of_mem D v i hμi hy, map_zero, mul_zero]
    · have hμ' : μ = (μ - Finsupp.single i 1) + Finsupp.single i 1 := by
        ext j
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with hij
        · subst hij; omega
        · omega
      rw [hμ'] at hy
      rw [ih _ _ (rDeriv_mem_weightSpace D v i hy), mul_zero]
      intro h
      apply hμ
      rw [wordWeight_append, h, hμ']
      simp

/-- Distinct weight spaces are orthogonal for Lusztig's form ([Lus] 1.2.3 (check)). -/
theorem form_eq_zero_of_ne {ν μ : I →₀ ℕ} (hνμ : ν ≠ μ) {x y : LusztigF k I}
    (hx : x ∈ weightSpace k ν) (hy : y ∈ weightSpace k μ) : form D v x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact form_monomial_eq_zero D v w μ y hy (hw ▸ hνμ)
  | zero => simp
  | add x z _ _ hx hz => simp [hx, hz]
  | smul c x _ hx => simp [hx]

/-! ### The radical and the algebra `f` -/

lemma formTensor_tmul_eq_zero_left {x : LusztigF k I} (hx : ∀ y, form D v x y = 0)
    (z : LusztigF k I) (W : LusztigF k I ⊗[k] LusztigF k I) : formTensor D v (x ⊗ₜ z) W = 0 := by
  induction W with
  | tmul a b => simp [hx]
  | add X Y hX hY => simp [hX, hY]

lemma formTensor_tmul_eq_zero_right {x : LusztigF k I} (hx : ∀ y, form D v x y = 0)
    (z : LusztigF k I) (W : LusztigF k I ⊗[k] LusztigF k I) : formTensor D v (z ⊗ₜ x) W = 0 := by
  induction W with
  | tmul a b => simp [hx]
  | add X Y hX hY => simp [hX, hY]

/-- The radical `{x | ∀ y, (x, y) = 0}` of Lusztig's form, a two-sided ideal of `'f`
([Lus] 1.2.4 (check)). -/
def radical : TwoSidedIdeal (LusztigF k I) :=
  TwoSidedIdeal.mk' {x | ∀ y, form D v x y = 0} (by simp) (fun hx hy z ↦ by simp [hx z, hy z])
    (fun hx z ↦ by simp [hx z])
    (fun hy z ↦ by rw [form_mul_left, formTensor_tmul_eq_zero_right D v hy])
    (fun hx z ↦ by rw [form_mul_left, formTensor_tmul_eq_zero_left D v hx])

theorem mem_radical_iff {x : LusztigF k I} : x ∈ radical D v ↔ ∀ y, form D v x y = 0 := by
  simp [radical, TwoSidedIdeal.mem_mk']

theorem mem_radical_iff' {x : LusztigF k I} : x ∈ radical D v ↔ ∀ y, form D v y x = 0 := by
  simp only [mem_radical_iff, form_comm D v x]

/-- Lusztig's algebra `f = 'f / I`, the quotient of `'f` by the radical of its bilinear form
([Lus] 1.2.5 (check)). -/
abbrev Quotient := (radical D v).ringCon.Quotient

/-- The projection `'f → f`. -/
def toQuotient : LusztigF k I →ₐ[k] Quotient D v := RingCon.mkₐ k (radical D v).ringCon

theorem toQuotient_surjective : Function.Surjective (toQuotient D v) :=
  RingCon.mkₐ_surjective _

theorem toQuotient_eq_zero_iff {x : LusztigF k I} : toQuotient D v x = 0 ↔ x ∈ radical D v := by
  rw [TwoSidedIdeal.mem_iff, ← RingCon.eq]
  rfl

end LusztigF
