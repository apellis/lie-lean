/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.DoubleEdgeRelation
import LieLean.Algebra.QuantumGroup.BraidAction.SimplyLaced
import LieLean.Algebra.QuantumGroup.BraidAction.HigherMixed

/-!
# A double-edge path's transformed Serre relations

## Main results
Positive and negative relations between the degree-two image at an outgoing double
edge and an untouched node. The forward relation covers a connected three-node
B/C path, not merely the rank-two diagram.

## References
Builds on the repository's `PathSerre`, `HigherSerreReverse`, `HigherMixed`, `DoubleEdge`,
`DoubleEdgeOther` and `DoubleEdgeRelation`. The degree-seven polynomial certificate is
reconstructed by exact rational-function elimination and checked by Lean.
-/

open LieLean
noncomputable section
namespace LieLean.QuantumGroup
variable {k : Type*} [Field k]
section Ring
variable {B : Type*} [Ring B] [Algebra k B]

set_option maxHeartbeats 8000000 in
-- Expansion of the degree-seven certificate requires scalar normalization.
private theorem double_path_positive (a b c : B) (q : k) (hq : q ≠ 0)
    (hS : qSerre q 3 a b = 0) (hU : qSerre (q ^ 2) 2 b c = 0)
    (hac : Commute a c)
    (hn : (1 + q⁻¹ ^ 4) * (1 + q⁻¹ ^ 2 + q⁻¹ ^ 4) ≠ 0) :
    qSerre (q ^ 2) 2
      (a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) + q⁻¹ ^ 2 • (b * a ^ 2))
      c = 0 := by
  have h0 := congrArg (fun z : B ↦ (z) * (a * b * c)) hS
  have h1 := congrArg (fun z : B ↦ (a) * (z) * (b * c)) hS
  have h2 := congrArg (fun z : B ↦ (a * b) * (z) * (c)) hS
  have h3 := congrArg (fun z : B ↦ (a * b * c) * (z)) hS
  have h4 := congrArg (fun z : B ↦ (z) * (a * c * b)) hS
  have h5 := congrArg (fun z : B ↦ (a) * (z) * (c * b)) hS
  have h6 := congrArg (fun z : B ↦ (a * c) * (z) * (b)) hS
  have h7 := congrArg (fun z : B ↦ (a * c * b) * (z)) hS
  have h8 := congrArg (fun z : B ↦ (z) * (b * a * c)) hS
  have h9 := congrArg (fun z : B ↦ (b) * (z) * (a * c)) hS
  have h10 := congrArg (fun z : B ↦ (b * a) * (z) * (c)) hS
  have h11 := congrArg (fun z : B ↦ (b * a * c) * (z)) hS
  have h12 := congrArg (fun z : B ↦ (b * c) * (z) * (a)) hS
  have h13 := congrArg (fun z : B ↦ (c) * (z) * (a * b)) hS
  have h14 := congrArg (fun z : B ↦ (z) * (c * b * a)) hS
  have h15 := congrArg (fun z : B ↦ (c) * (z) * (b * a)) hS
  have h16 := congrArg (fun z : B ↦ (c * b) * (z) * (a)) hS
  have h17 := congrArg (fun z : B ↦ (c * b * a) * (z)) hS
  have h26 := congrArg (fun z : B ↦ (z) * (a * a * a * a)) hU
  have h27 := congrArg (fun z : B ↦ (a) * (z) * (a * a * a)) hU
  have h28 := congrArg (fun z : B ↦ (a * a) * (z) * (a * a)) hU
  have h29 := congrArg (fun z : B ↦ (a * a * a) * (z) * (a)) hU
  have h30 := congrArg (fun z : B ↦ (a * a * a * a) * (z)) hU
  have hca (z : B) : c * (a * z) = a * (c * z) := by
    rw [← mul_assoc, hac.symm.eq, mul_assoc]
  apply (smul_eq_zero.mp (show
    ((1 + q⁻¹ ^ 4) * (1 + q⁻¹ ^ 2 + q⁻¹ ^ 4)) •
      qSerre (q ^ 2) 2
        (a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) +
          q⁻¹ ^ 2 • (b * a ^ 2)) c = 0 from ?_)).resolve_left hn
  simp only [qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial,
    Nat.reduceSub, pow_succ, pow_zero, mul_one, one_mul, mul_zero, zero_mul, add_zero,
    zero_add, one_smul, mul_neg, neg_mul, neg_neg, mul_sub, sub_mul, mul_add,
    add_mul, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_smul,
    mul_assoc, hac.symm.eq, hca]
    at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h26 h27 h28 h29 h30 ⊢
  linear_combination (norm := (match_scalars <;> field_simp [hq] <;> ring))
    (-(q⁻¹ ^ 2) + -(q⁻¹ ^ 4) + -(q⁻¹ ^ 6)) • h0 +
      (-(q⁻¹ ^ 4)) • h1 +
      (-(q⁻¹ ^ 4) + -(q⁻¹ ^ 6) + -(q⁻¹ ^ 8) + -(q⁻¹ ^ 10)) • h2 +
      (q⁻¹ ^ 2 + q⁻¹ ^ 4 + 2 * q⁻¹ ^ 6 + 2 * q⁻¹ ^ 8 + q⁻¹ ^ 10 + q⁻¹ ^ 12) • h3 +
      (1 + q⁻¹ ^ 2 + 2 * q⁻¹ ^ 4 + q⁻¹ ^ 6 + q⁻¹ ^ 8) • h4 +
      (q⁻¹ ^ 2 + q⁻¹ ^ 6) • h5 +
      (-(q⁻¹ ^ 4)) • h6 +
      (-(q⁻¹ ^ 4) + -(q⁻¹ ^ 6) + -(q⁻¹ ^ 8) + -(q⁻¹ ^ 10)) • h7 +
      (q⁻¹ ^ 2 + q⁻¹ ^ 4 + q⁻¹ ^ 6 + q⁻¹ ^ 8) • h8 +
      (q⁻¹ ^ 8) • h9 +
      (q⁻¹ ^ 6 + q⁻¹ ^ 8 + q⁻¹ ^ 10) • h10 +
      (-(q⁻¹ ^ 4) + -(q⁻¹ ^ 6) + -(2 * q⁻¹ ^ 8) + -(q⁻¹ ^ 10) + -(q⁻¹ ^ 12)) • h11 +
      (-(q⁻¹ ^ 6) + -(q⁻¹ ^ 10)) • h12 +
      (-(q⁻¹ ^ 2) + -(q⁻¹ ^ 4) + -(q⁻¹ ^ 6)) • h13 +
      (-(1) + -(q⁻¹ ^ 2) + -(2 * q⁻¹ ^ 4) + -(2 * q⁻¹ ^ 6) + -(q⁻¹ ^ 8) + -(q⁻¹ ^ 10)) • h14 +
      (q⁻¹ ^ 2 + q⁻¹ ^ 4 + q⁻¹ ^ 6 + q⁻¹ ^ 8) • h15 +
      (q⁻¹ ^ 8) • h16 +
      (q⁻¹ ^ 6 + q⁻¹ ^ 8 + q⁻¹ ^ 10) • h17 +
      (q⁻¹ ^ 8) • h26 +
      (-(q⁻¹ ^ 4) + -(q⁻¹ ^ 6) + -(q⁻¹ ^ 8) + -(q⁻¹ ^ 10)) • h27 +
      (q⁻¹ ^ 2 + q⁻¹ ^ 4 + 2 * q⁻¹ ^ 6 + q⁻¹ ^ 8 + q⁻¹ ^ 10) • h28 +
      (-(q⁻¹ ^ 2) + -(q⁻¹ ^ 4) + -(q⁻¹ ^ 6) + -(q⁻¹ ^ 8)) • h29 +
      (q⁻¹ ^ 4) • h30

end Ring

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j l : I}

/-- Forward Serre relation at a double-edge path `i => j - l`.
Reconstructed degree-seven certificate. The reverse entry `a_li` follows by
symmetry of zero entries; `a_lj` and all other entries are unrestricted.
The extra explicit cyclotomic nonvanishing is a parameter boundary of this proof,
not a claim that the generic classical braid automorphism fails there. -/
theorem qSerre_braidEj_braidEj_of_double_path
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -2)
    (hji : D.cartanMatrix j i = -1) (hjl : D.cartanMatrix j l = -1)
    (hil : D.cartanMatrix i l = 0)
    (hn : (1 + (v ^ D.d i)⁻¹ ^ 4) *
      (1 + (v ^ D.d i)⁻¹ ^ 2 + (v ^ D.d i)⁻¹ ^ 4) ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j l).toNat
      (braidEj R v i j) (braidEj R v i l) = 0 := by
  have hij' : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at hij
    norm_num at hij
  have hjl' : j ≠ l := by
    rintro rfl
    rw [D.cartanMatrix_self] at hjl
    norm_num at hjl
  have hp := parameter_eq_square_of_double_edge (v := v) hij hji
  have hS : qSerre (v ^ D.d i) 3 (E R v i) (E R v j) = 0 := by
    simpa only [hij, Int.reduceSub, Int.reduceToNat] using serre_E R v hij'
  have hU : qSerre ((v ^ D.d i) ^ 2) 2 (E R v j) (E R v l) = 0 := by
    simpa only [hjl, hp, Int.reduceSub, Int.reduceToNat] using serre_E R v hjl'
  rw [braidEj_eq_of_cartanMatrix_eq_neg_two hij,
    braidEj_eq_of_cartanMatrix_eq_zero hil, hp, hjl]
  change qSerre ((v ^ D.d i) ^ 2) 2 (_ • _) (E R v l) = 0
  rw [← one_smul k (E R v l), qSerre_smul_smul]
  exact smul_eq_zero.mpr (Or.inr (double_path_positive _ _ _ _
    (pow_ne_zero _ hv) hS hU (E_commute_E_of_cartanMatrix_eq_zero hil) hn))

/-- Negative forward double-path Serre relation, transported through the genuine
Chevalley involution. Only its actual nonzero `q_i^{-2}` factor is cancelled. -/
theorem qSerre_braidFj_braidFj_of_double_path
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -2)
    (hji : D.cartanMatrix j i = -1) (hjl : D.cartanMatrix j l = -1)
    (hil : D.cartanMatrix i l = 0)
    (hn : (1 + (v ^ D.d i)⁻¹ ^ 4) *
      (1 + (v ^ D.d i)⁻¹ ^ 2 + (v ^ D.d i)⁻¹ ^ 4) ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j l).toNat
      (braidFj R v i j) (braidFj R v i l) = 0 := by
  have h := congrArg (chevalley R v)
    (qSerre_braidEj_braidEj_of_double_path (R := R) hv hij hji hjl hil hn)
  rw [map_qSerre, map_zero,
    chevalley_braidEj_of_cartanMatrix_eq_neg_two hv hij,
    braidEj_eq_of_cartanMatrix_eq_zero hil, chevalley_E] at h
  rw [braidFj_eq_of_cartanMatrix_eq_zero hil]
  have h' := qSerre_smul_smul (v := v ^ D.d j) (1 - D.cartanMatrix j l).toNat
    (braidFj R v i j) (F R v l) ((v ^ D.d i)⁻¹ ^ 2) 1
  simp only [one_smul, mul_one] at h'
  rw [h'] at h
  exact (smul_eq_zero.mp h).resolve_left
    (pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hv))))

/-- Reverse positive relation at a degree-two path. Reconstructed by applying
linearity in the Serre polynomial's second argument twice. The reverse double-edge
entry and parameter sum/difference are unrestricted. -/
theorem qSerre_braidEj_braidEj_of_double_path_reverse
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -2)
    (hlj : D.cartanMatrix l j = -1) (hil : D.cartanMatrix i l = 0) :
    qSerre (v ^ D.d l) (1 - D.cartanMatrix l j).toNat
      (braidEj R v i l) (braidEj R v i j) = 0 := by
  have hlj' : l ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at hlj
    norm_num at hlj
  have hcb : qSerre (v ^ D.d l) 2 (E R v l) (E R v j) = 0 := by
    simpa only [hlj, Int.reduceSub, Int.reduceToNat] using serre_E R v hlj'
  have hac := E_commute_E_of_cartanMatrix_eq_zero (R := R) (v := v) hil
  have hY := qSerre_quantumCommutator_of_path_reverse
    (r := (v ^ D.d i)⁻¹ ^ 2) hcb hac
  have hX := qSerre_quantumCommutator_of_path_reverse (r := (1 : k)) hY hac
  have he :
      E R v i * (E R v i * E R v j - (v ^ D.d i)⁻¹ ^ 2 • (E R v j * E R v i)) -
        (1 : k) • ((E R v i * E R v j - (v ^ D.d i)⁻¹ ^ 2 • (E R v j * E R v i)) *
          E R v i) =
      E R v i ^ 2 * E R v j -
        ((v ^ D.d i + (v ^ D.d i)⁻¹) * (v ^ D.d i)⁻¹) •
          (E R v i * E R v j * E R v i) +
        (v ^ D.d i)⁻¹ ^ 2 • (E R v j * E R v i ^ 2) := by
    simp only [one_smul, pow_two, mul_sub, sub_mul, mul_smul_comm,
      smul_mul_assoc, mul_assoc]
    match_scalars <;> field_simp [pow_ne_zero (D.d i) hv]
    ring
  rw [he] at hX
  rw [braidEj_eq_of_cartanMatrix_eq_zero hil,
    braidEj_eq_of_cartanMatrix_eq_neg_two hij, hlj]
  change qSerre (v ^ D.d l) 2 (E R v l) (_ • _) = 0
  rw [← one_smul k (E R v l), qSerre_smul_smul, hX, smul_zero]

/-- Negative reverse double-path relation via the genuine Chevalley involution.
Reconstructed from the proved positive relation; no transformed relation is assumed. -/
theorem qSerre_braidFj_braidFj_of_double_path_reverse
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -2)
    (hlj : D.cartanMatrix l j = -1) (hil : D.cartanMatrix i l = 0) :
    qSerre (v ^ D.d l) (1 - D.cartanMatrix l j).toNat
      (braidFj R v i l) (braidFj R v i j) = 0 := by
  have h := congrArg (chevalley R v)
    (qSerre_braidEj_braidEj_of_double_path_reverse (R := R) hv hij hlj hil)
  rw [map_qSerre, map_zero,
    chevalley_braidEj_of_cartanMatrix_eq_neg_two hv hij,
    braidEj_eq_of_cartanMatrix_eq_zero hil, chevalley_E] at h
  rw [braidFj_eq_of_cartanMatrix_eq_zero hil]
  have h' := qSerre_smul_smul (v := v ^ D.d l) (1 - D.cartanMatrix l j).toNat
    (F R v l) (braidFj R v i j) 1 ((v ^ D.d i)⁻¹ ^ 2)
  simp only [one_smul, one_pow, one_mul] at h'
  rw [h'] at h
  exact (smul_eq_zero.mp h).resolve_left
    (pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hv)))

end LieLean.QuantumGroup
