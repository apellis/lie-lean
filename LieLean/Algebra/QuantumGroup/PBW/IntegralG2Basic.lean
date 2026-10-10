/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.RankTwoG2Relations
import LieLean.Algebra.QuantumGroup.PBW.IntegralA2

/-!
# Normalized root vectors for integral G₂ straightening

Normalize the six ordered root vectors as `e, X3, X2, Z, x1, f`, where
`X3 = x3/[3]!`, `X2 = x2/[2]`, and `Z = z/[3]!`. This module supplies the relations
with the simple generators in the normalization needed for divided-power straightening.
The proofs use only the two quantum Serre relations, including their opposite-algebra images.

## Main results

* `G2Integral.X3_mul_e`, `X2_mul_e`, `Z_mul_e`, `x1_mul_e`, `f_mul_e`.
* `G2Integral.f_mul_X3`, `f_mul_X2`, `f_mul_Z`, `f_mul_x1`.
-/

open Finset MulOpposite

noncomputable section

namespace LieLean.QuantumGroup.G2Integral

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- The long root vector of weight `3α + β`. -/
def X3 (q : k) (e f : B) : B := (qFactorial q 3)⁻¹ • G2PBW.x3 q e f

/-- The short root vector of weight `2α + β`. -/
def X2 (q : k) (e f : B) : B := (qInt q 2)⁻¹ • G2PBW.x2 q e f

/-- The long root vector of weight `3α + 2β`. -/
def Z (q : k) (e f : B) : B := (qFactorial q 3)⁻¹ • G2PBW.z q e f

variable {q : k} {e f : B}

lemma qFactorial_three : qFactorial q 3 = qInt q 2 * qInt q 3 := by
  simp [qFactorial, qInt, mul_comm]

lemma qInt_two : qInt q 2 = q + q⁻¹ := by
  simp [qInt, sum_range_succ]

lemma qInt_three (hq : q ≠ 0) : qInt q 3 = q ^ 2 + 1 + q⁻¹ ^ 2 := by
  simp [qInt, sum_range_succ, hq]

variable (hq : q ≠ 0) (h2 : qInt q 2 ≠ 0) (h3 : qInt q 3 ≠ 0)

include h2 h3 in
lemma qFactorial_three_ne_zero : qFactorial q 3 ≠ 0 := by
  rw [qFactorial_three]
  exact mul_ne_zero h2 h3

include hq h2 in
lemma square_add_one_ne_zero : q ^ 2 + 1 ≠ 0 := by
  have h : q * qInt q 2 = q ^ 2 + 1 := by rw [qInt_two, mul_add]; field_simp
  rw [← h]
  exact mul_ne_zero hq h2

include h2 in
lemma x2_eq : G2PBW.x2 q e f = qInt q 2 • X2 q e f := by
  rw [X2, smul_smul, mul_inv_cancel₀ h2, one_smul]

include h2 h3 in
lemma x3_eq : G2PBW.x3 q e f = qFactorial q 3 • X3 q e f := by
  rw [X3, smul_smul, mul_inv_cancel₀ (qFactorial_three_ne_zero h2 h3), one_smul]

include h2 h3 in
lemma z_eq : G2PBW.z q e f = qFactorial q 3 • Z q e f := by
  rw [Z, smul_smul, mul_inv_cancel₀ (qFactorial_three_ne_zero h2 h3), one_smul]

include hq in
lemma f_mul_e : f * e = q ^ 3 • (e * f) - q ^ 3 • G2PBW.x1 q e f := by
  simp only [G2PBW.x1, smul_sub, smul_smul, mul_inv_cancel₀ (pow_ne_zero 3 hq), one_smul]
  abel

include hq h2 in
lemma x1_mul_e : G2PBW.x1 q e f * e =
    q • (e * G2PBW.x1 q e f) - (q * qInt q 2) • X2 q e f := by
  rw [← smul_smul, ← x2_eq h2, G2PBW.x2]
  simp only [smul_sub, smul_smul, mul_inv_cancel₀ hq, one_smul]
  abel

include hq h2 h3 in
lemma X2_mul_e : X2 q e f * e =
    q⁻¹ • (e * X2 q e f) - (q⁻¹ * qInt q 3) • X3 q e f := by
  rw [X2, X3, qFactorial_three, G2PBW.x3]
  simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
  match_scalars <;> (field_simp; try ring)

include hq h2 h3 in
lemma x1_mul_X2 : G2PBW.x1 q e f * X2 q e f =
    q⁻¹ • (X2 q e f * G2PBW.x1 q e f) - (q⁻¹ * qInt q 3) • Z q e f := by
  rw [X2, Z, qFactorial_three, G2PBW.z]
  simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
  match_scalars <;> (field_simp; try ring)

variable (hS4 : qSerre q 4 e f = 0) (hS2 : qSerre (q ^ 3) 2 f e = 0)

include hq hS4 in
lemma X3_mul_e : X3 q e f * e = (q ^ 3)⁻¹ • (e * X3 q e f) := by
  rw [X3, smul_mul_assoc, G2PBW.x3_mul_e hq hS4, mul_smul_comm, smul_comm]

include hq h2 h3 hS4 hS2 in
lemma Z_mul_e : Z q e f * e = e * Z q e f - (q ^ 2 - 1) • (X2 q e f ^ 2) := by
  rw [Z, X2, smul_mul_assoc, G2PBW.z_mul_e hq hS4 hS2 (square_add_one_ne_zero hq h2),
    mul_smul_comm, smul_add, qFactorial_three, smul_pow]
  simp only [smul_smul, sub_eq_add_neg, pow_two]
  match_scalars <;> field_simp [square_add_one_ne_zero hq h2]
  simp only [qInt_two, qInt_three hq]
  field_simp
  ring

include hS2 in
private lemma serre_op : qSerre (q ^ 3) 2 (op f) (op e) = 0 := by
  rw [qSerre_op, hS2, op_zero, smul_zero]

private lemma unop_y1 : unop (G2PBW.y1 q (op e) (op f)) = G2PBW.x1 q e f := by
  simp [G2PBW.y1, G2PBW.x1]

private lemma unop_y2 : unop (G2PBW.y2 q (op e) (op f)) = G2PBW.x2 q e f := by
  simp [G2PBW.y2, G2PBW.x2, unop_y1]

private lemma unop_y3 : unop (G2PBW.y3 q (op e) (op f)) = G2PBW.z q e f := by
  simp [G2PBW.y3, G2PBW.z, unop_y1, unop_y2]

private lemma unop_w : unop (G2PBW.w q (op e) (op f)) = G2PBW.x3 q e f := by
  simp [G2PBW.w, G2PBW.x3, unop_y2]

include hq hS2 in
lemma f_mul_x1 : f * G2PBW.x1 q e f = (q ^ 3)⁻¹ • (G2PBW.x1 q e f * f) := by
  simpa only [unop_mul, unop_smul, unop_op, unop_y1] using
    congrArg unop (G2PBW.y1_mul_f hq (serre_op hS2))

include hq h2 hS2 in
lemma f_mul_X2 : f * X2 q e f = X2 q e f * f - (q ^ 2 - 1) • (G2PBW.x1 q e f ^ 2) := by
  have h := congrArg unop (G2PBW.y2_mul_f hq (serre_op hS2))
  simp only [unop_mul, unop_add, unop_smul, unop_op, unop_y1, unop_y2] at h
  rw [X2, mul_smul_comm, h, smul_add, smul_mul_assoc, smul_smul]
  simp only [sub_eq_add_neg, pow_two]
  match_scalars <;> field_simp
  rw [qInt_two]
  field_simp
  ring

include hq h2 h3 hS2 in
lemma f_mul_Z : f * Z q e f = (q ^ 3)⁻¹ • (Z q e f * f) -
    ((q ^ 2 - 1) ^ 2 / (q ^ 2 * qInt q 3)) • (G2PBW.x1 q e f ^ 3) := by
  have h := congrArg unop (G2PBW.y3_mul_f hq (serre_op hS2))
  simp only [unop_mul, unop_add, unop_smul, unop_op, unop_y1, unop_y3] at h
  rw [Z, mul_smul_comm, h, smul_add, smul_mul_assoc, smul_comm, smul_smul,
    qFactorial_three]
  simp only [sub_eq_add_neg, pow_succ, pow_zero, one_mul, smul_smul, mul_assoc]
  match_scalars <;> field_simp
  rw [qInt_two]
  field_simp

include hq h2 h3 hS2 in
lemma f_mul_X3 : f * X3 q e f = q ^ 3 • (X3 q e f * f) +
    (q ^ 4 + q ^ 2 - 1) • Z q e f - (q ^ 2 * (q ^ 2 - 1)) •
      (X2 q e f * G2PBW.x1 q e f) := by
  have h := congrArg unop (G2PBW.w_mul_f hq (serre_op hS2))
  simp only [unop_mul, unop_add, unop_smul, unop_op, unop_y1, unop_y2, unop_y3, unop_w] at h
  rw [X3, Z, X2, mul_smul_comm, h]
  simp only [smul_add, smul_mul_assoc, smul_smul, sub_eq_add_neg, neg_smul]
  rw [qFactorial_three]
  match_scalars <;> field_simp
  rw [qInt_three hq]
  field_simp
  ring

include hq h2 h3 hS4 hS2 in
lemma x1_mul_X3 : G2PBW.x1 q e f * X3 q e f =
    X3 q e f * G2PBW.x1 q e f - (q ^ 2 - 1) • (X2 q e f ^ 2) := by
  have h : G2PBW.x1 q e f * G2PBW.x3 q e f =
      G2PBW.x3 q e f * G2PBW.x1 q e f +
        (G2PBW.z q e f * e - e * G2PBW.z q e f) := by
    simp only [G2PBW.x3, G2PBW.z, G2PBW.x2, mul_sub, sub_mul, smul_mul_assoc,
      mul_smul_comm, smul_sub, smul_smul, mul_assoc]
    match_scalars <;> (field_simp; try ring)
  calc
    G2PBW.x1 q e f * X3 q e f =
        X3 q e f * G2PBW.x1 q e f + (Z q e f * e - e * Z q e f) := by
      simp only [X3, Z, mul_smul_comm, h, smul_add, smul_sub, smul_mul_assoc]
    _ = _ := by rw [Z_mul_e hq h2 h3 hS4 hS2]; abel

end LieLean.QuantumGroup.G2Integral
