/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ContravariantForm

/-!
# The anti-automorphism `ρ̄` of `U`

Lusztig's anti-automorphism `ρ̄` of `U` ([Lus] 26.1.1) is `ρ̄(u) = \overline{ρ(ū)}`, the
conjugate of `ρ` (19.1.1) by the bar involution. On the generators,
`ρ̄(Eᵢ) = vᵢ⁻¹ K̃ᵢ⁻¹ Fᵢ`, `ρ̄(Fᵢ) = vᵢ⁻¹ K̃ᵢ Eᵢ`, `ρ̄(K_μ) = K_μ`.
Since `ρ̄` is linear over the ground field, we define it directly by these values, as a linear
anti-automorphism of `U` over any field `k` (`v ≠ 0`); over `ℚ(v)` it is Lusztig's `ρ̄`.

## Main definitions and results

* `QuantumGroup.rhoBarOp`, `QuantumGroup.rhoBar`: the anti-automorphism `ρ̄`.
* `QuantumGroup.rhoBar_mul`, `QuantumGroup.rhoBar_rhoBar`: `ρ̄` reverses products and is an
  involution.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 19.1.1, 26.1.1.
-/

open LieLean MulOpposite

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k)

/-- `ρ̄(Eᵢ) = vᵢ⁻¹ K̃ᵢ⁻¹ Fᵢ`. -/
def rhoBarE (i : I) : QuantumGroup R v := (v ^ D.d i)⁻¹ • (K R v (-ktilde R i) * F R v i)

/-- `ρ̄(Fᵢ) = vᵢ⁻¹ K̃ᵢ Eᵢ`. -/
def rhoBarF (i : I) : QuantumGroup R v := (v ^ D.d i)⁻¹ • (Kt R v i * E R v i)

variable {R v} [NeZero v]

lemma rhoBarE_mul_K (i : I) (μ : Y) :
    rhoBarE R v i * K R v μ = v ^ R.root i μ • (K R v μ * rhoBarE R v i) := by
  rw [rhoBarE, smul_mul_assoc, mul_assoc, F_mul_K (NeZero.ne v), mul_smul_comm, ← mul_assoc,
    K_comm, mul_assoc, smul_comm, mul_smul_comm]

lemma rhoBarF_mul_K (i : I) (μ : Y) :
    rhoBarF R v i * K R v μ = v ^ (-R.root i μ) • (K R v μ * rhoBarF R v i) := by
  rw [rhoBarF, smul_mul_assoc, mul_assoc, E_mul_K (NeZero.ne v), mul_smul_comm, ← mul_assoc,
    K_comm, mul_assoc, smul_comm, mul_smul_comm]

omit [DecidableEq I] in
lemma inv_zpow_dot_mul (hv : v ≠ 0) (i : I) :
    (v ^ D.d i)⁻¹ * (v ^ D.d i)⁻¹ * v ^ D.dot i i = 1 := by
  have h := zpow_dot_mul (D := D) hv i
  rw [zpow_neg] at h
  rw [← inv_inv (v ^ D.dot i i), ← mul_inv, ← mul_inv, h, inv_one]

lemma rhoBarF_mul_rhoBarE_sub (i j : I) :
    rhoBarF R v j * rhoBarE R v i - rhoBarE R v i * rhoBarF R v j = if i = j then
      (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (Kt R v i - K R v (-ktilde R i)) else 0 := by
  have hv := NeZero.ne v
  have e1 : rhoBarF R v j * rhoBarE R v i = (((v ^ D.d j)⁻¹ * (v ^ D.d i)⁻¹) * v ^ D.dot i j) •
      (Kt R v j * K R v (-ktilde R i) * (E R v j * F R v i)) := by
    rw [rhoBarF, rhoBarE, smul_mul_smul_comm, mul_assoc, ← mul_assoc (E R v j), E_mul_K hv,
      map_neg, root_ktilde_eq_dot, neg_neg]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  have e2 : rhoBarE R v i * rhoBarF R v j = (((v ^ D.d j)⁻¹ * (v ^ D.d i)⁻¹) * v ^ D.dot i j) •
      (Kt R v j * K R v (-ktilde R i) * (F R v i * E R v j)) := by
    rw [rhoBarE, rhoBarF, smul_mul_smul_comm, mul_assoc, ← mul_assoc (F R v i), F_mul_K hv,
      root_ktilde_eq_dot, D.dot_comm j i]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    congr 1
    · ring
    · rw [← mul_assoc, K_comm, mul_assoc]
  rw [e1, e2, ← smul_sub, ← mul_sub, E_mul_F_sub]
  by_cases h : i = j
  · subst h
    simp only [ite_true]
    rw [mul_smul_comm, Kt, K_add, add_neg_cancel, K_zero, one_mul, inv_zpow_dot_mul hv,
      one_smul]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, mul_zero, smul_zero]

theorem rhoBar_relations :
    Relations R v (fun i ↦ op (rhoBarE R v i)) (fun i ↦ op (rhoBarF R v i)) (rhoK R v) where
  K_mul_E μ i := by
    apply unop_injective
    simp only [rhoK, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, unop_mul, unop_op,
      unop_smul]
    exact rhoBarE_mul_K i μ
  K_mul_F μ i := by
    apply unop_injective
    simp only [rhoK, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, unop_mul, unop_op,
      unop_smul]
    exact rhoBarF_mul_K i μ
  E_mul_F i j := by
    apply unop_injective
    simp only [unop_sub, unop_mul, unop_op]
    rw [rhoBarF_mul_rhoBarE_sub]
    split_ifs
    · simp [rhoK, Kt]
    · simp
  serre_E i j hij := by
    have hv := NeZero.ne v
    rw [qSerre_op, rhoBarE, rhoBarE, qSerre_smul_smul,
      qSerre_mul_mul (t := v ^ (-R.root i (-ktilde R i))) (s := v ^ R.root i (-ktilde R j))
        (zpow_ne_zero _ hv) (K_mul_F R v _ i) (F_mul_K hv _ i)
        (by rw [F_mul_K hv, map_neg, map_neg, root_ktilde_eq_dot, root_ktilde_eq_dot,
          D.dot_comm]) (K_comm R v _ _),
      serre_F R v hij]
    simp
  serre_F i j hij := by
    have hv := NeZero.ne v
    rw [qSerre_op, rhoBarF, rhoBarF, qSerre_smul_smul,
      qSerre_mul_mul (t := v ^ R.root i (ktilde R i)) (s := v ^ (-R.root i (ktilde R j)))
        (zpow_ne_zero _ hv) (K_mul_E R v _ i) (E_mul_K hv _ i)
        (by rw [E_mul_K hv, root_ktilde_eq_dot, root_ktilde_eq_dot, D.dot_comm])
        (K_comm R v _ _),
      serre_E R v hij]
    simp

variable (R v) in
/-- Lusztig's anti-automorphism `ρ̄` as an algebra map to the opposite algebra ([Lus] 26.1.1). -/
def rhoBarOp : QuantumGroup R v →ₐ[k] (QuantumGroup R v)ᵐᵒᵖ := lift rhoBar_relations

variable (R v) in
/-- Lusztig's anti-automorphism `ρ̄` ([Lus] 26.1.1): `ρ̄(Eᵢ) = vᵢ⁻¹ K̃ᵢ⁻¹ Fᵢ`,
`ρ̄(Fᵢ) = vᵢ⁻¹ K̃ᵢ Eᵢ`, `ρ̄(K_μ) = K_μ`. -/
def rhoBar : QuantumGroup R v →ₗ[k] QuantumGroup R v :=
  (opLinearEquiv k).symm.toLinearMap.comp (rhoBarOp R v).toLinearMap

@[simp] lemma rhoBar_E (i : I) : rhoBar R v (E R v i) = rhoBarE R v i := by
  simp [rhoBar, rhoBarOp]

@[simp] lemma rhoBar_F (i : I) : rhoBar R v (F R v i) = rhoBarF R v i := by
  simp [rhoBar, rhoBarOp]

@[simp] lemma rhoBar_K (μ : Y) : rhoBar R v (K R v μ) = K R v μ := by
  simp [rhoBar, rhoBarOp, rhoK]

@[simp] lemma rhoBar_algebraMap (c : k) : rhoBar R v (algebraMap k _ c) = algebraMap k _ c := by
  simp [rhoBar]

/-- `ρ̄` reverses products. -/
theorem rhoBar_mul (x y : QuantumGroup R v) :
    rhoBar R v (x * y) = rhoBar R v y * rhoBar R v x := by
  simp [rhoBar]

@[simp] lemma rhoBar_one : rhoBar R v 1 = 1 := by simp [rhoBar]

lemma rhoBar_rhoBarE (i : I) : rhoBar R v (rhoBarE R v i) = E R v i := by
  have hv := NeZero.ne v
  rw [rhoBarE, map_smul, rhoBar_mul, rhoBar_F, rhoBar_K, rhoBarF, smul_mul_assoc, mul_assoc,
    E_mul_K hv, map_neg, root_ktilde_eq_dot, neg_neg, mul_smul_comm, ← mul_assoc, Kt, K_add,
    add_neg_cancel, K_zero, one_mul, smul_smul, smul_smul, inv_zpow_dot_mul hv, one_smul]

lemma rhoBar_rhoBarF (i : I) : rhoBar R v (rhoBarF R v i) = F R v i := by
  have hv := NeZero.ne v
  rw [rhoBarF, map_smul, rhoBar_mul, rhoBar_E, rhoBar_K, rhoBarE, smul_mul_assoc, mul_assoc,
    F_mul_K hv, root_ktilde_eq_dot, mul_smul_comm, ← mul_assoc, K_add, neg_add_cancel, K_zero,
    one_mul, smul_smul, smul_smul, inv_zpow_dot_mul hv, one_smul]

/-- `ρ̄` is an involution. -/
theorem rhoBar_rhoBar (x : QuantumGroup R v) : rhoBar R v (rhoBar R v x) = x := by
  induction x using QuantumGroup.induction_on with
  | algebraMap c => simp
  | E i => rw [rhoBar_E, rhoBar_rhoBarE]
  | F i => rw [rhoBar_F, rhoBar_rhoBarF]
  | K μ => rw [rhoBar_K, rhoBar_K]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | mul x y hx hy => rw [rhoBar_mul, rhoBar_mul, hx, hy]

end LieLean.QuantumGroup
