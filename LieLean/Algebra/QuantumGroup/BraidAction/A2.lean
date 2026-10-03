/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.CoupledSerreNegativeReverse

/-!
# A coupled A2 quantum braid equivalence

## Main definitions

* `QuantumGroup.a2Braid` lifts the existing braid candidates through all defining relations.
* `QuantumGroup.a2BraidInv` is the explicit inverse, built using actual product reversal.
* `QuantumGroup.a2BraidEquiv` is the resulting algebra equivalence.

## Main results

Both composites are proved to be the identity. The neighboring generator composites
reduce to the coupled lowering commutator and its coefficient-correct Chevalley image.

## References

Reconstructed from the quotient presentation and the published coupled relation proofs.
The index type has exactly the two distinct nodes `i,j`, both Cartan entries are `-1`, and the
root datum lattice is arbitrary.
-/

noncomputable section
namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  (i j : I) (hij : i ≠ j) (hall : ∀ l, l = i ∨ l = j)
  (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)

include hij hall h h' hq in
/-- All defining relations for the actual coupled A2 braid images, not an assumption.
Reconstructed by exhaustive two-node cases from the published relation theorems. -/
theorem a2Braid_relations :
    Relations R v (fun l ↦ if l = i then braidEi R i else braidEj R v i l)
      (fun l ↦ if l = i then braidFi R i else braidFj R v i l) (braidK R v i) where
  K_mul_E μ l := by
    rcases hall l with rfl | rfl
    · simpa only [↓reduceIte] using braidK_mul_braidEi (R := R) (v := v) _ μ
    · simpa only [hij.symm, ↓reduceIte] using braidK_mul_braidEj (R := R) (NeZero.ne v) hij μ
  K_mul_F μ l := by
    rcases hall l with rfl | rfl
    · simpa only [↓reduceIte] using braidK_mul_braidFi (R := R) (v := v) _ μ
    · simpa only [hij.symm, ↓reduceIte] using braidK_mul_braidFj (R := R) (NeZero.ne v) hij μ
  E_mul_F l m := by
    rcases hall l with rfl | rfl <;> rcases hall m with rfl | rfl
    · simpa only [↓reduceIte] using braidEi_mul_braidFi_sub (R := R) (v := v) _
    · simpa only [hij, hij.symm, ↓reduceIte] using braidEi_mul_braidFj_sub (R := R) (v := v) hij
    · simpa only [hij.symm, ↓reduceIte] using braidEj_mul_braidFi_sub (R := R) (v := v) hij
    · simpa only [hij.symm, ↓reduceIte] using
        braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_one (R := R) (NeZero.ne v) h hq
  serre_E l m hlm := by
    rcases hall l with rfl | rfl <;> rcases hall m with rfl | rfl
    · exact (hlm rfl).elim
    · simpa only [hij.symm, ↓reduceIte] using
        qSerre_braidEi_braidEj_of_cartanMatrix_eq_neg_one (R := R) h hq
    · simpa only [hij.symm, ↓reduceIte] using
        qSerre_braidEj_braidEi_of_simply_laced_edge (R := R) h h' hq
    · exact (hlm rfl).elim
  serre_F l m hlm := by
    rcases hall l with rfl | rfl <;> rcases hall m with rfl | rfl
    · exact (hlm rfl).elim
    · simpa only [hij.symm, ↓reduceIte] using
        qSerre_braidFi_braidFj_of_cartanMatrix_eq_neg_one (R := R) h hq
    · simpa only [hij.symm, ↓reduceIte] using
        qSerre_braidFj_braidFi_of_simply_laced_edge (R := R) h h' hq
    · exact (hlm rfl).elim

/-- The genuine A2 braid algebra homomorphism on the quotient presentation.
No relation package or faithful action is assumed. Reconstructed proof. -/
def a2Braid : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  lift (a2Braid_relations i j hij hall h h' hq)

@[simp] theorem a2Braid_E (l : I) :
    a2Braid i j hij hall h h' hq (E R v l) =
      if l = i then braidEi R i else braidEj R v i l := lift_E _ l

@[simp] theorem a2Braid_F (l : I) :
    a2Braid i j hij hall h h' hq (F R v l) =
      if l = i then braidFi R i else braidFj R v i l := lift_F _ l

@[simp] theorem a2Braid_K (μ : Y) :
    a2Braid i j hij hall h h' hq (K R v μ) = K R v (reflY R i μ) := lift_K _ μ


/-! ### Product reversal and the explicit inverse candidate -/

open MulOpposite

/-- Product reversal fixing `E,F` and negating the toral lattice preserves the
presentation. This auxiliary anti-homomorphism works in arbitrary rank. -/
theorem braidReversal_relations :
    Relations R v (fun l ↦ op (E R v l)) (fun l ↦ op (F R v l)) (antipodeK R v) where
  K_mul_E μ l := by
    apply unop_injective
    simpa [antipodeK] using E_mul_K (R := R) (NeZero.ne v) (-μ) l
  K_mul_F μ l := by
    apply unop_injective
    simpa [antipodeK] using F_mul_K (R := R) (NeZero.ne v) (-μ) l
  E_mul_F l m := by
    apply unop_injective
    by_cases hlm : l = m
    · subst m
      simpa [antipodeK, neg_sub, smul_sub] using
        congrArg Neg.neg (E_mul_F_sub R v l l)
    · simpa [antipodeK, hlm, neg_sub] using
        congrArg Neg.neg (E_mul_F_sub R v l m)
  serre_E l m hlm := by rw [qSerre_op, serre_E R v hlm, op_zero, smul_zero]
  serre_F l m hlm := by rw [qSerre_op, serre_F R v hlm, op_zero, smul_zero]

/-- The actual quotient anti-homomorphism, reconstructed from the presentation. -/
def braidReversalOp : QuantumGroup R v →ₐ[k] (QuantumGroup R v)ᵐᵒᵖ :=
  lift braidReversal_relations

/-- Product reversal viewed as a coefficient-linear map. -/
def braidReversal : QuantumGroup R v →ₗ[k] QuantumGroup R v :=
  (opLinearEquiv k).symm.toLinearMap.comp (braidReversalOp (R := R) (v := v)).toLinearMap

@[simp] theorem braidReversal_E (l : I) : braidReversal (E R v l) = E R v l := by
  simp [braidReversal, braidReversalOp]

@[simp] theorem braidReversal_F (l : I) : braidReversal (F R v l) = F R v l := by
  simp [braidReversal, braidReversalOp]

@[simp] theorem braidReversal_K (μ : Y) : braidReversal (K R v μ) = K R v (-μ) := by
  simp [braidReversal, braidReversalOp, antipodeK]

/-- Product reversal reverses multiplication. -/
theorem braidReversal_mul (x y : QuantumGroup R v) :
    braidReversal (x * y) = braidReversal y * braidReversal x := by
  simp [braidReversal]

/-- Reversal squares to the identity, proved on the quotient generators. -/
theorem braidReversal_involutive :
    Function.Involutive (braidReversal (R := R) (v := v)) := by
  have hh : (AlgHom.opComm (braidReversalOp (R := R) (v := v))).comp
      braidReversalOp = AlgHom.id k (QuantumGroup R v) := by
    apply hom_ext <;> intro x <;>
      simp [braidReversalOp, antipodeK]
  intro x
  exact DFunLike.congr_fun hh x

/-- Explicit inverse candidate obtained by conjugating the proved braid homomorphism
by the proved product-reversal anti-homomorphism. No extra relations are assumed. -/
def a2BraidInv : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  (AlgHom.opComm braidReversalOp).comp
    ((a2Braid i j hij hall h h' hq).op.comp braidReversalOp)

/-- The inverse candidate is reversal-conjugation on every element. -/
theorem a2BraidInv_apply (x : QuantumGroup R v) :
    a2BraidInv i j hij hall h h' hq x =
      braidReversal (a2Braid i j hij hall h h' hq (braidReversal x)) := rfl

@[simp] theorem a2BraidInv_Ei :
    a2BraidInv i j hij hall h h' hq (E R v i) = braidInvEi R i := by
  simp [a2BraidInv_apply, braidEi, braidInvEi, braidReversal_mul, Kt]

@[simp] theorem a2BraidInv_Fi :
    a2BraidInv i j hij hall h h' hq (F R v i) = braidInvFi R i := by
  simp [a2BraidInv_apply, braidFi, braidInvFi, braidReversal_mul, Kt]

@[simp] theorem a2BraidInv_Ej :
    a2BraidInv i j hij hall h h' hq (E R v j) =
      E R v j * E R v i - (v ^ D.d i)⁻¹ • (E R v i * E R v j) := by
  simp [a2BraidInv_apply, hij.symm, braidEj_eq_of_cartanMatrix_eq_neg_one h,
    braidReversal_mul]

@[simp] theorem a2BraidInv_Fj :
    a2BraidInv i j hij hall h h' hq (F R v j) =
      F R v i * F R v j - (v ^ D.d i) • (F R v j * F R v i) := by
  simp [a2BraidInv_apply, hij.symm,
    braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h, braidReversal_mul]

@[simp] theorem a2BraidInv_K (μ : Y) :
    a2BraidInv i j hij hall h h' hq (K R v μ) = K R v (reflY R i μ) := by
  simp [a2BraidInv_apply]


include h hq in
/-- The neighboring positive generator is recovered by the inverse polynomial
in the actual forward images. Reconstructed from the coupled lowering commutator. -/
theorem a2Braid_recover_Ej :
    braidEj R v i j * braidEi R i -
      (v ^ D.d i)⁻¹ • (braidEi R i * braidEj R v i j) = E R v j := by
  have hne : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have ht := braidK_mul_braidEj (R := R) (NeZero.ne v) hne (-ktilde R i)
  rw [braidK_apply, reflY_neg_ktilde, map_neg, root_ktilde, h,
    mul_neg_one, neg_neg, zpow_natCast] at ht
  have hc := congrArg (fun z : QuantumGroup R v ↦ z * Kt R v i)
    (braidEj_mul_Fi_sub_of_cartanMatrix_eq_neg_one (R := R) h hq)
  simp only [sub_mul, neg_mul, mul_assoc, K_neg_mul_Kt, mul_one] at hc
  simp only [braidEi, mul_neg, neg_mul, mul_assoc]
  rw [ht, mul_smul_comm, smul_neg, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ (NeZero.ne v)), one_smul]
  linear_combination (norm := module) -hc

include h hq in
/-- The neighboring negative generator is recovered by the inverse polynomial.
The scalar cancellation is derived with the genuine Chevalley involution. -/
theorem a2Braid_recover_Fj :
    braidFi R i * braidFj R v i j -
      (v ^ D.d i) • (braidFj R v i j * braidFi R i) = F R v j := by
  have hc := congrArg (chevalley R v) (a2Braid_recover_Ej i j h hq)
  rw [map_sub, map_mul, map_smul, map_mul,
    chevalley_braidEj_of_cartanMatrix_eq_neg_one (NeZero.ne v) h,
    chevalley_braidEi (NeZero.ne v), chevalley_E] at hc
  have hq0 := pow_ne_zero (D.d i) (NeZero.ne v)
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul] at hc
  have c1 : (v ^ D.d i) ^ 2 * -(v ^ D.d i)⁻¹ = -(v ^ D.d i) := by
    field_simp
  have c2 : (v ^ D.d i)⁻¹ * (-(v ^ D.d i)⁻¹ * (v ^ D.d i) ^ 2) = -1 := by
    field_simp
  rw [c1, c2] at hc
  simpa [neg_smul, sub_eq_add_neg, add_comm] using hc

/-- The candidate is a right inverse, checked on both Chevalley colors and all toral
lattice generators, not inferred from a surjectivity assertion. -/
theorem a2Braid_comp_a2BraidInv :
    (a2Braid (R := R) i j hij hall h h' hq).comp
      (a2BraidInv i j hij hall h h' hq) = AlgHom.id k (QuantumGroup R v) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · rcases hall l with hl | hl
    · subst l
      simp only [AlgHom.comp_apply, a2BraidInv_Ei, braidInvEi, map_neg, map_mul,
        a2Braid_F, ↓reduceIte, braidFi, a2Braid_K, reflY_ktilde,
        mul_neg, neg_neg, AlgHom.id_apply, ← mul_assoc, K_mul_K_neg, one_mul]
    · subst l
      simpa only [AlgHom.comp_apply, a2BraidInv_Ej, map_sub, map_mul, map_smul,
        a2Braid_E, hij.symm, ↓reduceIte, AlgHom.id_apply] using a2Braid_recover_Ej i j h hq
  · rcases hall l with hl | hl
    · subst l
      simp only [AlgHom.comp_apply, a2BraidInv_Fi, braidInvFi, map_neg, map_mul,
        a2Braid_E, ↓reduceIte, braidEi, Kt, a2Braid_K, reflY_ktilde,
        neg_mul, neg_neg, AlgHom.id_apply, mul_assoc, K_mul_K_neg, mul_one]
    · subst l
      simpa only [AlgHom.comp_apply, a2BraidInv_Fj, map_sub, map_mul, map_smul,
        a2Braid_F, hij.symm, ↓reduceIte, AlgHom.id_apply] using a2Braid_recover_Fj i j h hq
  · simp

/-- The candidate is also a left inverse. Conjugating the proved generator-level
right-inverse identity by the involutive product reversal gives this identity. -/
theorem a2BraidInv_comp_a2Braid :
    (a2BraidInv (R := R) i j hij hall h h' hq).comp
      (a2Braid i j hij hall h h' hq) = AlgHom.id k (QuantumGroup R v) := by
  apply DFunLike.ext
  intro x
  have hc := congrArg braidReversal
    (DFunLike.congr_fun (a2Braid_comp_a2BraidInv (R := R) i j hij hall h h' hq)
      (braidReversal x))
  simpa only [AlgHom.comp_apply, a2BraidInv_apply, braidReversal_involutive x,
    AlgHom.id_apply] using hc

/-- Lusztig's actual coupled A2 braid algebra equivalence, with explicit two-sided inverse.
Assumptions: exactly two distinct nodes, mutual Cartan entries `-1`, arbitrary root datum
lattice and field, `v ≠ 0`, and `vᵢ - vᵢ⁻¹ ≠ 0`. Reconstructed from the presentation. -/
def a2BraidEquiv : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  AlgEquiv.ofAlgHom (a2Braid i j hij hall h h' hq) (a2BraidInv i j hij hall h h' hq)
    (a2Braid_comp_a2BraidInv i j hij hall h h' hq)
    (a2BraidInv_comp_a2Braid i j hij hall h h' hq)

end QuantumGroup
