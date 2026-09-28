/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.HigherSerre

/-!
# Neighbor-first transformed Serre relations at a double edge

## Main results
The actual positive and negative candidates satisfy the neighbor-first quadratic
Serre relation at mutual Cartan entries `(-2,-1)`. The parameter is `q_j = q_i^2`.
Only `v ≠ 0` is needed; no quantum sum or difference is cancelled.

## References
Reconstructed from the defining quotient presentation; no external source consulted.
These are automorphism prerequisites, not an automorphism or length-four braid relation.
-/

noncomputable section
namespace QuantumGroup
variable {k : Type*} [Field k]
section Ring
variable {B : Type*} [Ring B] [Algebra k B]

set_option maxHeartbeats 4000000 in
-- The polynomial certificate is an explicit combination of the two original Serre relations.
private lemma reverse_two_positive (a b : B) (q : k) (hq : q ≠ 0)
    (hs : qSerre q 3 a b = 0) (ht : qSerre (q ^ 2) 2 b a = 0) :
    let X := a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) +
      q⁻¹ ^ 2 • (b * a ^ 2)
    let Y := a * b - q⁻¹ ^ 2 • (b * a)
    Y * X - q⁻¹ ^ 2 • (X * Y) = 0 := by
  dsimp only
  have he :
      (a * b - q⁻¹ ^ 2 • (b * a)) *
          (a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) +
            q⁻¹ ^ 2 • (b * a ^ 2)) -
        q⁻¹ ^ 2 • ((a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) +
          q⁻¹ ^ 2 • (b * a ^ 2)) * (a * b - q⁻¹ ^ 2 • (b * a))) =
      -(q⁻¹ ^ 4) • (b * qSerre q 3 a b) +
        q⁻¹ ^ 2 • (qSerre q 3 a b * b) -
        q⁻¹ ^ 2 • (a ^ 2 * qSerre (q ^ 2) 2 b a) +
        (q⁻¹ ^ 4 + q⁻¹ ^ 2) • (a * qSerre (q ^ 2) 2 b a * a) -
        q⁻¹ ^ 4 • (qSerre (q ^ 2) 2 b a * a ^ 2) := by
    simp only [qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial,
      Nat.reduceSub, pow_succ, pow_zero, mul_one, one_mul, mul_zero, add_zero,
      zero_add, one_smul, mul_neg, neg_mul, neg_neg, mul_sub, sub_mul, mul_add,
      add_mul, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, mul_assoc]
    match_scalars <;> field_simp [hq] <;> ring
  rw [he, hs, ht]
  simp

set_option maxHeartbeats 4000000 in
-- Normal ordering uses the totalized commutator coefficient without cancellation.
private lemma reverse_two_lowering (a b c u u' : B) (q t : k) (hq : q ≠ 0)
    (hca : c * a = a * c - t • (u - u')) (hcb : c * b = b * c)
    (hua : u * a = q ^ 2 • (a * u))
    (hub : u * b = q⁻¹ ^ 2 • (b * u))
    (hu'a : u' * a = q⁻¹ ^ 2 • (a * u'))
    (hu'b : u' * b = q ^ 2 • (b * u')) (hu'u : u' * u = 1) :
    let X := a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) +
      q⁻¹ ^ 2 • (b * a ^ 2);
    -(c * u) * X - q ^ 2 • (X * -(c * u)) =
      (t * (1 - q ^ 4)) • (a * b - q⁻¹ ^ 2 • (b * a)) := by
  have hca_assoc (z : B) := congrArg (fun x : B ↦ x * z) hca
  have hcb_assoc (z : B) := congrArg (fun x : B ↦ x * z) hcb
  have hua_assoc (z : B) := congrArg (fun x : B ↦ x * z) hua
  have hub_assoc (z : B) := congrArg (fun x : B ↦ x * z) hub
  have hu'a_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'a
  have hu'b_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'b
  simp only [mul_assoc, sub_mul, smul_mul_assoc] at *
  simp only [pow_two, mul_sub, sub_mul, mul_add, add_mul, mul_neg, neg_mul,
    mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_neg, mul_assoc,
    hua, hub, hca_assoc, hcb_assoc, hua_assoc, hub_assoc, hu'a_assoc, hu'b_assoc,
    hu'u, mul_one]
  match_scalars <;> field_simp [hq] <;> ring

private lemma reverse_two_serre (X A Y : B) (q t : k) (hq : q ≠ 0)
    (hAX : A * X - q ^ 2 • (X * A) = t • Y)
    (hYX : Y * X - q⁻¹ ^ 2 • (X * Y) = 0) :
    qSerre (q ^ 2) 2 X A = 0 := by
  have he : qSerre (q ^ 2) 2 X A =
      (A * X - q ^ 2 • (X * A)) * X -
        q⁻¹ ^ 2 • (X * (A * X - q ^ 2 • (X * A))) := by
    simp [qSerre, Finset.sum_range_succ, qBinomial, pow_two, mul_assoc,
      mul_sub, sub_mul, smul_sub, smul_smul, hq, add_smul]
    module
  rw [he, hAX]
  rw [smul_mul_assoc, mul_smul_comm, smul_comm, ← smul_sub, hYX, smul_zero]

end Ring

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j : I}

omit [DecidableEq I] in
/-- The symmetrizer gives `q_j = q_i^2` at mutual entries `(-2,-1)`.
Reconstructed directly from symmetrizer compatibility. -/
theorem parameter_eq_square_of_double_edge
    (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1) :
    v ^ D.d j = (v ^ D.d i) ^ 2 := by
  have hd : D.d j = D.d i * 2 := by
    have hs := D.d_mul_cartanMatrix_comm i j
    rw [h, h'] at hs
    omega
  rw [hd, pow_mul]

set_option maxHeartbeats 1000000 in
-- Applying the normal-ordering certificate in the quotient needs a larger budget.
/-- Neighbor-first positive Serre relation for the actual degree-two braid candidate.
Reconstructed from the quotient presentation at mutual entries `(-2,-1)`.
Rank, characteristic and toral lattice are unrestricted. The inverse quantum sum in
`braidEj` and inverse quantum difference in the presentation remain totalized: neither
must be nonzero here. This does not assert an automorphism at singular parameters. -/
theorem qSerre_braidEj_braidEi_of_double_edge (hv : v ≠ 0)
    (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j i).toNat
      (braidEj R v i j) (braidEi R i) = 0 := by
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have hp := parameter_eq_square_of_double_edge (v := v) h h'
  have hca : F R v i * E R v i = E R v i * F R v i -
      (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (Kt R v i - K R v (-ktilde R i)) := by
    have hc := E_mul_F_sub R v i i
    simp only [ite_true] at hc
    linear_combination (norm := module) -hc
  have hub : Kt R v i * E R v j =
      (v ^ D.d i)⁻¹ ^ 2 • (E R v j * Kt R v i) := by
    rw [Kt, K_mul_E, root_ktilde, h, mul_neg, zpow_neg, zpow_mul,
      zpow_natCast, zpow_ofNat, inv_pow]
  have hu'b : K R v (-ktilde R i) * E R v j =
      (v ^ D.d i) ^ 2 • (E R v j * K R v (-ktilde R i)) := by
    rw [K_mul_E, map_neg, root_ktilde, h, mul_neg, neg_neg, zpow_mul,
      zpow_natCast, zpow_ofNat]
  have hAX := reverse_two_lowering (E R v i) (E R v j) (F R v i)
    (Kt R v i) (K R v (-ktilde R i)) (v ^ D.d i)
    (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ (pow_ne_zero _ hv) hca
    (E_mul_F_of_ne hij.symm).symm (Kt_mul_E i) hub
    (by simpa only [inv_pow] using K_neg_ktilde_mul_E (R := R) (v := v) i)
    hu'b (K_neg_mul_Kt i)
  have hs : qSerre (v ^ D.d i) 3 (E R v i) (E R v j) = 0 := by
    simpa only [h, Int.reduceSub, Int.reduceToNat] using serre_E R v hij
  have ht : qSerre ((v ^ D.d i) ^ 2) 2 (E R v j) (E R v i) = 0 := by
    simpa only [h', hp, Int.reduceSub, Int.reduceToNat] using serre_E R v hij.symm
  have hYX := reverse_two_positive (E R v i) (E R v j) (v ^ D.d i)
    (pow_ne_zero _ hv) hs ht
  have H := reverse_two_serre _ _ _ (v ^ D.d i) _ (pow_ne_zero _ hv) hAX hYX
  rw [h', hp, braidEj_eq_of_cartanMatrix_eq_neg_two h]
  change qSerre ((v ^ D.d i) ^ 2) 2 (_ • _) (braidEi R i) = 0
  rw [← one_smul k (braidEi (v := v) R i), qSerre_smul_smul]
  exact (smul_eq_zero.mpr (Or.inr H))

/-- Neighbor-first negative Serre relation at mutual entries `(-2,-1)`.
Reconstructed via the proved quotient Chevalley map and its actual scalar factors;
no automorphism or transformed-relation hypothesis is assumed. -/
theorem qSerre_braidFj_braidFi_of_double_edge (hv : v ≠ 0)
    (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j i).toNat
      (braidFj R v i j) (braidFi R i) = 0 := by
  have hs := congrArg (chevalley R v)
    (qSerre_braidEj_braidEi_of_double_edge (R := R) hv h h')
  rw [map_qSerre, map_zero, chevalley_braidEi hv,
    chevalley_braidEj_of_cartanMatrix_eq_neg_two hv h, qSerre_smul_smul] at hs
  exact (smul_eq_zero.mp hs).resolve_left
    (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hv))))
      (pow_ne_zero _ (pow_ne_zero _ hv)))

end QuantumGroup
