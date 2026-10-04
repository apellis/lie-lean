/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.DoubleEdge

/-!
# The simple-side double-edge quantum braid map

## Main results
Neighbor-first cubic relations and the second exact-two-node automorphism.

## References
Reconstructed from the defining presentation.
-/

open LieLean

noncomputable section
namespace LieLean.QuantumGroup
variable {k : Type*} [Field k]
section Ring
variable {B : Type*} [Ring B] [Algebra k B]

set_option maxHeartbeats 4000000 in
-- Expanding the two-relation polynomial certificate needs additional scalar normalization.
private lemma other_positive (a b : B) (q : k) (hq : q ≠ 0)
    (hs : qSerre q 3 b a = 0) (ht : qSerre (q ^ 2) 2 a b = 0) :
    let X := a * b - q⁻¹ ^ 2 • (b * a)
    b * X ^ 2 - (1 + q⁻¹ ^ 2) • (X * b * X) + q⁻¹ ^ 2 • (X ^ 2 * b) = 0 := by
  dsimp only
  have he :
      b * (a * b - q⁻¹ ^ 2 • (b * a)) ^ 2 -
        (1 + q⁻¹ ^ 2) • ((a * b - q⁻¹ ^ 2 • (b * a)) * b *
          (a * b - q⁻¹ ^ 2 • (b * a))) +
        q⁻¹ ^ 2 • ((a * b - q⁻¹ ^ 2 • (b * a)) ^ 2 * b) =
      q⁻¹ ^ 2 • (a * qSerre q 3 b a) -
        q⁻¹ ^ 4 • (qSerre q 3 b a * a) +
        q⁻¹ ^ 4 • (b ^ 2 * qSerre (q ^ 2) 2 a b) -
        (q⁻¹ ^ 2 + q⁻¹ ^ 4) • (b * qSerre (q ^ 2) 2 a b * b) +
        q⁻¹ ^ 2 • (qSerre (q ^ 2) 2 a b * b ^ 2) := by
    simp only [qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial,
      Nat.reduceSub, pow_succ, pow_zero, mul_one, one_mul, mul_zero, add_zero,
      zero_add, one_smul, mul_neg, neg_mul, neg_neg, mul_sub, sub_mul, mul_add,
      add_mul, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, mul_assoc]
    match_scalars <;> field_simp [hq] <;> ring
  rw [he, hs, ht]
  simp

private lemma other_serre (X A b : B) (q : k) (hq : q ≠ 0)
    (hAX : A * X - q ^ 2 • (X * A) = -(q ^ 2) • b)
    (hb : b * X ^ 2 - (1 + q⁻¹ ^ 2) • (X * b * X) +
      q⁻¹ ^ 2 • (X ^ 2 * b) = 0) :
    qSerre q 3 X A = 0 := by
  apply neg_eq_zero.mp
  have he : -qSerre q 3 X A =
      (A * X - q ^ 2 • (X * A)) * X ^ 2 -
        (1 + q⁻¹ ^ 2) • (X * (A * X - q ^ 2 • (X * A)) * X) +
        q⁻¹ ^ 2 • (X ^ 2 * (A * X - q ^ 2 • (X * A))) := by
    simp only [qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial,
      Nat.reduceSub, pow_succ, pow_zero, mul_one, one_mul, mul_zero, add_zero,
      zero_add, one_smul, mul_neg, neg_mul, neg_neg, mul_sub, sub_mul, mul_add,
      mul_smul_comm, smul_mul_assoc, smul_sub, mul_assoc]
    match_scalars <;> field_simp [hq] <;> ring
  rw [he, hAX]
  calc
    _ = -(q ^ 2) • (b * X ^ 2 - (1 + q⁻¹ ^ 2) • (X * b * X) +
        q⁻¹ ^ 2 • (X ^ 2 * b)) := by
      simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, smul_smul]
      module
    _ = 0 := by rw [hb, smul_zero]
end Ring

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j : I}

/-- Neighbor-first cubic relation at the simple side of a double edge.
Reconstructed polynomial certificate from both original Serre relations.
Ambient rank and toral lattice are unrestricted. -/
theorem qSerre_braidEj_braidEi_of_double_edge_other [NeZero v]
    (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -2)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j i).toNat
      (braidEj R v i j) (braidEi R i) = 0 := by
  have hv := NeZero.ne v
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have hp := parameter_eq_square_of_double_edge (v := v) h' h
  let q := v ^ D.d j
  let A := braidEi (v := v) R i
  let X := braidEj R v i j
  let b := E R v j
  have hq0 : q ≠ 0 := pow_ne_zero _ hv
  have hKX : Kt R v i * X = q ^ 2 • (X * Kt R v i) := by
    have ht := braidK_mul_braidEj (R := R) hv hij (-ktilde R i)
    rw [braidK_apply, reflY_neg_ktilde, map_neg, root_ktilde, h,
      mul_neg_one, neg_neg, zpow_natCast, hp] at ht
    exact ht
  have hAX : A * X - q ^ 2 • (X * A) = -(q ^ 2) • b := by
    have hc := congrArg (fun z : QuantumGroup R v ↦ z * Kt R v i)
      (braidEj_mul_Fi_sub_of_cartanMatrix_eq_neg_one (R := R) h hq)
    change (X * F R v i - F R v i * X) * Kt R v i =
      -(b * K R v (-ktilde R i)) * Kt R v i at hc
    simp only [sub_mul, neg_mul, mul_assoc, K_neg_mul_Kt, mul_one] at hc
    dsimp [A, braidEi]
    simp only [neg_mul, mul_neg, mul_assoc]
    rw [hKX, mul_smul_comm]
    linear_combination (norm := module)
      congrArg (fun z : QuantumGroup R v ↦ q ^ 2 • z) hc
  have hs : qSerre q 3 b (E R v i) = 0 := by
    simpa only [h', Int.reduceSub, Int.reduceToNat] using serre_E R v hij.symm
  have ht : qSerre (q ^ 2) 2 (E R v i) b = 0 := by
    simpa only [h, hp, Int.reduceSub, Int.reduceToNat] using serre_E R v hij
  have hb := other_positive (E R v i) b q hq0 hs ht
  have hX : X = E R v i * b - q⁻¹ ^ 2 • (b * E R v i) := by
    simp only [X, braidEj_eq_of_cartanMatrix_eq_neg_one h, hp, inv_pow]
    rfl
  rw [h']
  change qSerre q 3 X A = 0
  apply other_serre X A b q hq0 hAX
  simpa only [hX] using hb

/-- The corresponding negative cubic relation, via the actual Chevalley involution.
Reconstructed; no braid automorphism or transformed relation is assumed. -/
theorem qSerre_braidFj_braidFi_of_double_edge_other [NeZero v]
    (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -2)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j i).toNat
      (braidFj R v i j) (braidFi R i) = 0 := by
  have hv := NeZero.ne v
  have hc := congrArg (chevalley R v)
    (qSerre_braidEj_braidEi_of_double_edge_other (R := R) h h' hq)
  rw [map_qSerre, map_zero, chevalley_braidEi hv,
    chevalley_braidEj_of_cartanMatrix_eq_neg_one hv h, qSerre_smul_smul] at hc
  exact (smul_eq_zero.mp hc).resolve_left
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hv))))
      (pow_ne_zero _ (pow_ne_zero _ hv)))

omit [DecidableEq I] in
/-- The second node's denominator follows from the first node's quantum sum and
 difference. Reconstructed using the symmetrizer-derived square relation. -/
theorem parameter_sub_inv_ne_zero_of_double_edge (hv : v ≠ 0)
    (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1)
    (hd : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0) :
    v ^ D.d j - (v ^ D.d j)⁻¹ ≠ 0 := by
  rw [parameter_eq_square_of_double_edge (v := v) h h']
  have he : (v ^ D.d i) ^ 2 - ((v ^ D.d i) ^ 2)⁻¹ =
      (v ^ D.d i - (v ^ D.d i)⁻¹) * (v ^ D.d i + (v ^ D.d i)⁻¹) := by
    field_simp [pow_ne_zero (D.d i) hv]
    ring
  rw [he]
  exact mul_ne_zero hd hs

variable [NeZero v]
  (i j : I) (hij : i ≠ j) (hall : ∀ l, l = i ∨ l = j)
  (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -2)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)

include hij hall h h' hq in
/-- All defining relations for the actual simple-side double-edge braid images, not an assumption.
Reconstructed by exhaustive two-node cases from the published relation theorems. -/
theorem doubleEdgeOtherBraid_relations :
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
        qSerre_braidEj_braidEi_of_double_edge_other (R := R) h h' hq
    · exact (hlm rfl).elim
  serre_F l m hlm := by
    rcases hall l with rfl | rfl <;> rcases hall m with rfl | rfl
    · exact (hlm rfl).elim
    · simpa only [hij.symm, ↓reduceIte] using
        qSerre_braidFi_braidFj_of_cartanMatrix_eq_neg_one (R := R) h hq
    · simpa only [hij.symm, ↓reduceIte] using
        qSerre_braidFj_braidFi_of_double_edge_other (R := R) h h' hq
    · exact (hlm rfl).elim

/-- The genuine simple-side double-edge braid algebra homomorphism on the quotient presentation.
No relation package or faithful action is assumed. Reconstructed proof. -/
def doubleEdgeOtherBraid : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  lift (doubleEdgeOtherBraid_relations i j hij hall h h' hq)

@[simp] theorem doubleEdgeOtherBraid_E (l : I) :
    doubleEdgeOtherBraid i j hij hall h h' hq (E R v l) =
      if l = i then braidEi R i else braidEj R v i l := lift_E _ l

@[simp] theorem doubleEdgeOtherBraid_F (l : I) :
    doubleEdgeOtherBraid i j hij hall h h' hq (F R v l) =
      if l = i then braidFi R i else braidFj R v i l := lift_F _ l

@[simp] theorem doubleEdgeOtherBraid_K (μ : Y) :
    doubleEdgeOtherBraid i j hij hall h h' hq (K R v μ) = K R v (reflY R i μ) := lift_K _ μ
/-- Explicit inverse candidate obtained by conjugating the proved braid homomorphism
by the proved product-reversal anti-homomorphism. No extra relations are assumed. -/
def doubleEdgeOtherBraidInv : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  (AlgHom.opComm braidReversalOp).comp
    ((doubleEdgeOtherBraid i j hij hall h h' hq).op.comp braidReversalOp)

/-- The inverse candidate is reversal-conjugation on every element. -/
theorem doubleEdgeOtherBraidInv_apply (x : QuantumGroup R v) :
    doubleEdgeOtherBraidInv i j hij hall h h' hq x =
      braidReversal (doubleEdgeOtherBraid i j hij hall h h' hq (braidReversal x)) := rfl

@[simp] theorem doubleEdgeOtherBraidInv_Ei :
    doubleEdgeOtherBraidInv i j hij hall h h' hq (E R v i) = braidInvEi R i := by
  simp [doubleEdgeOtherBraidInv_apply, braidEi, braidInvEi, braidReversal_mul, Kt]

@[simp] theorem doubleEdgeOtherBraidInv_Fi :
    doubleEdgeOtherBraidInv i j hij hall h h' hq (F R v i) = braidInvFi R i := by
  simp [doubleEdgeOtherBraidInv_apply, braidFi, braidInvFi, braidReversal_mul, Kt]

@[simp] theorem doubleEdgeOtherBraidInv_Ej :
    doubleEdgeOtherBraidInv i j hij hall h h' hq (E R v j) =
      E R v j * E R v i - (v ^ D.d i)⁻¹ • (E R v i * E R v j) := by
  simp [doubleEdgeOtherBraidInv_apply, hij.symm, braidEj_eq_of_cartanMatrix_eq_neg_one h,
    braidReversal_mul]

@[simp] theorem doubleEdgeOtherBraidInv_Fj :
    doubleEdgeOtherBraidInv i j hij hall h h' hq (F R v j) =
      F R v i * F R v j - (v ^ D.d i) • (F R v j * F R v i) := by
  simp [doubleEdgeOtherBraidInv_apply, hij.symm,
    braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h, braidReversal_mul]

@[simp] theorem doubleEdgeOtherBraidInv_K (μ : Y) :
    doubleEdgeOtherBraidInv i j hij hall h h' hq (K R v μ) = K R v (reflY R i μ) := by
  simp [doubleEdgeOtherBraidInv_apply]

/-- The candidate is a right inverse, checked on both Chevalley colors and all toral
lattice generators, not inferred from a surjectivity assertion. -/
theorem doubleEdgeOtherBraid_comp_doubleEdgeOtherBraidInv :
    (doubleEdgeOtherBraid (R := R) i j hij hall h h' hq).comp
      (doubleEdgeOtherBraidInv i j hij hall h h' hq) = AlgHom.id k (QuantumGroup R v) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · rcases hall l with hl | hl
    · subst l
      simp only [AlgHom.comp_apply, doubleEdgeOtherBraidInv_Ei, braidInvEi, map_neg, map_mul,
        doubleEdgeOtherBraid_F, ↓reduceIte, braidFi, doubleEdgeOtherBraid_K, reflY_ktilde,
        mul_neg, neg_neg, AlgHom.id_apply, ← mul_assoc, K_mul_K_neg, one_mul]
    · subst l
      simpa only [AlgHom.comp_apply, doubleEdgeOtherBraidInv_Ej, map_sub, map_mul, map_smul,
        doubleEdgeOtherBraid_E, hij.symm, ↓reduceIte, AlgHom.id_apply] using
        a2Braid_recover_Ej i j h hq
  · rcases hall l with hl | hl
    · subst l
      simp only [AlgHom.comp_apply, doubleEdgeOtherBraidInv_Fi, braidInvFi, map_neg, map_mul,
        doubleEdgeOtherBraid_E, ↓reduceIte, braidEi, Kt, doubleEdgeOtherBraid_K, reflY_ktilde,
        neg_mul, neg_neg, AlgHom.id_apply, mul_assoc, K_mul_K_neg, mul_one]
    · subst l
      simpa only [AlgHom.comp_apply, doubleEdgeOtherBraidInv_Fj, map_sub, map_mul, map_smul,
        doubleEdgeOtherBraid_F, hij.symm, ↓reduceIte, AlgHom.id_apply] using
        a2Braid_recover_Fj i j h hq
  · simp

/-- The candidate is also a left inverse. Conjugating the proved generator-level
right-inverse identity by the involutive product reversal gives this identity. -/
theorem doubleEdgeOtherBraidInv_comp_doubleEdgeOtherBraid :
    (doubleEdgeOtherBraidInv (R := R) i j hij hall h h' hq).comp
      (doubleEdgeOtherBraid i j hij hall h h' hq) = AlgHom.id k (QuantumGroup R v) := by
  apply DFunLike.ext
  intro x
  have hc := congrArg braidReversal
    (DFunLike.congr_fun
      (doubleEdgeOtherBraid_comp_doubleEdgeOtherBraidInv (R := R) i j hij hall h h' hq)
      (braidReversal x))
  simpa only [AlgHom.comp_apply, doubleEdgeOtherBraidInv_apply, braidReversal_involutive x,
    AlgHom.id_apply] using hc

/-- Lusztig's simple-side double-edge algebra equivalence, with explicit two-sided inverse.
Assumptions: exactly two distinct nodes, Cartan entries `(-1,-2)`, arbitrary root datum
lattice and field, `v ≠ 0`, and `vᵢ - vᵢ⁻¹ ≠ 0`. Reconstructed from the presentation. -/
def doubleEdgeOtherBraidEquiv : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  AlgEquiv.ofAlgHom (doubleEdgeOtherBraid i j hij hall h h' hq)
    (doubleEdgeOtherBraidInv i j hij hall h h' hq)
    (doubleEdgeOtherBraid_comp_doubleEdgeOtherBraidInv i j hij hall h h' hq)
    (doubleEdgeOtherBraidInv_comp_doubleEdgeOtherBraid i j hij hall h h' hq)

end LieLean.QuantumGroup
