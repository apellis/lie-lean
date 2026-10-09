/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.LusztigF.Serre
import LieLean.Algebra.QuantumGroup.GabberKac.MapCoeffs

/-!
# The anti-automorphism `σ` of `'f`

Let `σ : 'f → 'f` be the algebra anti-automorphism fixing every `θᵢ` (word reversal; [Lus] 1.1.3).
We show `σ² = 1`, `rᵢ ∘ σ = σ ∘ ᵢr` (`LusztigF.rDeriv_rev`), `(σ x, σ y) = (x, y)` for Lusztig's
form (`LusztigF.form_rev`; [Lus] 1.2.8) and that `σ` preserves the Serre ideal
(`LusztigF.rev_mem_serreIdeal`). Under `'f ⧸ J = U⁻`, `σ` is Kashiwara's anti-automorphism `*`
restricted to `U⁻` ([Kas91] §1.3).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.1.3, 1.2.8, 1.2.13.
* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516.
-/

open Finset LieLean.QuantumGroup

noncomputable section

namespace LusztigF

variable {k I : Type*} [Field k]

variable (k I) in
/-- `σ` as an algebra map to the opposite algebra. -/
def revHom : LusztigF k I →ₐ[k] (LusztigF k I)ᵐᵒᵖ :=
  FreeAlgebra.lift k fun i ↦ MulOpposite.op (θ k i)

variable (k I) in
/-- The anti-automorphism `σ` of `'f` fixing the `θᵢ`, as a linear map. -/
def rev : LusztigF k I →ₗ[k] LusztigF k I :=
  (MulOpposite.opLinearEquiv k).symm.toLinearMap ∘ₗ (revHom k I).toLinearMap

lemma rev_apply (x : LusztigF k I) : rev k I x = MulOpposite.unop (revHom k I x) := rfl

@[simp] lemma rev_θ (i : I) : rev k I (θ k i) = θ k i := by
  simp [rev_apply, revHom]

@[simp] lemma rev_one : rev k I (1 : LusztigF k I) = 1 := by
  simp [rev_apply]

@[simp] lemma rev_algebraMap (c : k) : rev k I (algebraMap k (LusztigF k I) c) =
    algebraMap k _ c := by
  simp [rev_apply]

lemma rev_mul (x y : LusztigF k I) : rev k I (x * y) = rev k I y * rev k I x := by
  simp [rev_apply]

lemma rev_rev (x : LusztigF k I) : rev k I (rev k I x) = x := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 i => exact (congrArg _ (rev_θ i)).trans (rev_θ i)
  | mul a b ha hb => rw [rev_mul, rev_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

lemma rev_monomial (w : List I) : rev k I (monomial k w) = monomial k w.reverse := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [monomial_cons, rev_mul, ih, rev_θ, List.reverse_cons]
    simp [monomial, List.map_append, List.prod_append]

lemma rev_mem_weightSpace {ν : I →₀ ℕ} {x : LusztigF k I} (hx : x ∈ weightSpace k ν) :
    rev k I x ∈ weightSpace k ν := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl, rfl⟩ := hy
    rw [rev_monomial]
    convert monomial_mem_weightSpace w.reverse using 2
    induction w with
    | nil => simp
    | cons i w ih =>
      rw [List.reverse_cons, wordWeight_append, ← ih, wordWeight_cons, add_comm]
      simp [wordWeight]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

lemma diagTwist_rev (c : I → k) (x : LusztigF k I) :
    diagTwist c (rev k I x) = rev k I (diagTwist c x) := by
  induction x using FreeAlgebra.induction with
  | grade0 a => simp
  | grade1 i => simp
  | mul a b ha hb => rw [rev_mul, map_mul, ha, hb, map_mul, rev_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

@[simp] lemma counit_rev (x : LusztigF k I) : counit (rev k I x) = counit x := by
  induction x using FreeAlgebra.induction with
  | grade0 a => simp
  | grade1 i => simp
  | mul a b ha hb => rw [rev_mul, map_mul, ha, hb, map_mul, mul_comm]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

variable [DecidableEq I] (D : LusztigCartanDatum I) (v : k)

/-- `rᵢ ∘ σ = σ ∘ ᵢr`. -/
theorem rDeriv_rev (i : I) (x : LusztigF k I) :
    rDeriv D v i (rev k I x) = rev k I (lDeriv D v i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 j => simp [apply_ite]
  | mul a b ha hb =>
    rw [rev_mul, rDeriv_mul, lDeriv_mul, map_add, rev_mul, rev_mul, ha, hb, twist_eq_diagTwist,
      diagTwist_rev]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- `ᵢr ∘ σ = σ ∘ rᵢ`. -/
theorem lDeriv_rev (i : I) (x : LusztigF k I) :
    lDeriv D v i (rev k I x) = rev k I (rDeriv D v i x) := by
  have := congrArg (rev k I) (rDeriv_rev D v i (rev k I x))
  rw [rev_rev, rev_rev] at this
  exact this.symm

/-- **`(σ x, σ y) = (x, y)`** for Lusztig's form ([Lus] 1.2.8). -/
theorem form_rev (x y : LusztigF k I) : form D v (rev k I x) (rev k I y) = form D v x y := by
  induction x using FreeAlgebra.induction_wordBasis generalizing y with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | smul c a ha => simp only [map_smul, LinearMap.smul_apply, ha]
  | word w =>
    induction w generalizing y with
    | nil =>
      rw [FreeAlgebra.wordBasis_nil, rev_one, form_one_left, form_one_left, counit_rev]
    | cons j w ih =>
      rw [← FreeAlgebra.ι_mul_wordBasis, rev_mul, show FreeAlgebra.ι k j = θ k j from rfl, rev_θ,
        form_mul_θ, form_θ_mul, rDeriv_rev, ih]

omit [DecidableEq I] in
lemma rev_qDivPow (q : k) (n : ℕ) (i : I) :
    rev k I (qDivPow q n (θ k i)) = qDivPow q n (θ k i) := by
  have : ∀ m : ℕ, rev k I (θ k i ^ m) = θ k i ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, rev_mul, ih, rev_θ, ← pow_succ', pow_succ]
  rw [qDivPow, map_smul, this]

omit [DecidableEq I] in
/-- `σ` maps the quantum Serre element `S_{ij}` to `±S_{ij}`. -/
lemma rev_serreElement (i j : I) :
    rev k I (serreElement D v i j) =
      (-1 : k) ^ (1 - D.cartanMatrix i j).toNat • serreElement D v i j := by
  set m := (1 - D.cartanMatrix i j).toNat
  rw [serreElement]
  unfold qSerreDiv
  rw [map_sum, Finset.smul_sum]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hr := Finset.mem_range.1 hr
  rw [map_smul, rev_mul, rev_mul, rev_qDivPow, rev_qDivPow, rev_θ, smul_smul, ← mul_assoc,
    show m - (m + 1 - 1 - r) = r by omega, show m + 1 - 1 - r = m - r by omega]
  congr 1
  rw [← pow_add, show m + r = (m - r) + 2 * r by omega, pow_add, pow_mul]
  simp

omit [DecidableEq I] in
/-- `σ` preserves the Serre ideal. -/
theorem rev_mem_serreIdeal {x : LusztigF k I} (hx : x ∈ serreIdeal D v) :
    rev k I x ∈ serreIdeal D v := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨i, j, hij, rfl⟩ := hx
    rw [rev_serreElement]
    exact smul_mem_serreIdeal _ (serreElement_mem_serreIdeal hij)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact TwoSidedIdeal.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact TwoSidedIdeal.neg_mem _ hx
  | left_absorb a x _ hx => rw [rev_mul]; exact TwoSidedIdeal.mul_mem_right _ _ _ hx
  | right_absorb b x _ hx => rw [rev_mul]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx

end LusztigF
