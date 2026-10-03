/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.DegreeTwo
import LieLean.Algebra.QuantumGroup.BraidAction.CoupledSerreNegative

/-!
# Centre-first transformed Serre relations at a double edge

## Main results

The actual positive and negative braid candidates satisfy the centre-first cubic
quantum Serre relation when the directed Cartan entry is `-2`.

## References

Reconstructed from the defining quotient presentation.
-/

noncomputable section
namespace QuantumGroup

variable {k : Type*} [Field k]

section Ring
variable {B : Type*} [Ring B] [Algebra k B]

set_option maxHeartbeats 4000000 in
-- Normal ordering the cubic identity produces many scalar coefficients.
private lemma centre_two (a b c u u' : B) (q t : k) (hq : q ≠ 0)
    (hca : c * a = a * c - t • (u - u'))
    (hcb : c * b = b * c)
    (hua : u * a = q ^ 2 • (a * u))
    (hub : u * b = q⁻¹ ^ 2 • (b * u))
    (huc : u * c = q⁻¹ ^ 2 • (c * u))
    (hu'a : u' * a = q⁻¹ ^ 2 • (a * u'))
    (hu'b : u' * b = q ^ 2 • (b * u'))
    (hu'c : u' * c = q ^ 2 • (c * u'))
    (hu'u : u' * u = 1) (huu' : u * u' = 1) :
    qSerre q 3 (-(c * u))
      (a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) +
        q⁻¹ ^ 2 • (b * a ^ 2)) = 0 := by
  have hca_assoc (z : B) := congrArg (fun x : B ↦ x * z) hca
  have hcb_assoc (z : B) := congrArg (fun x : B ↦ x * z) hcb
  have hua_assoc (z : B) := congrArg (fun x : B ↦ x * z) hua
  have hub_assoc (z : B) := congrArg (fun x : B ↦ x * z) hub
  have huc_assoc (z : B) := congrArg (fun x : B ↦ x * z) huc
  have hu'a_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'a
  have hu'b_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'b
  have hu'c_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'c
  have hu'u_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'u
  have huu'_assoc (z : B) := congrArg (fun x : B ↦ x * z) huu'
  simp only [mul_assoc, sub_mul, smul_mul_assoc, one_mul] at *
  simp only [qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial,
    Nat.reduceSub, pow_succ, pow_zero,
    mul_one, one_mul, mul_zero, add_zero, zero_add, one_smul,
    mul_neg, neg_mul, neg_neg, mul_sub, sub_mul, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_neg, mul_assoc,
    hua, hub, hca_assoc, hcb_assoc, hua_assoc, hub_assoc, huc_assoc, hu'a_assoc,
    hu'b_assoc, hu'c_assoc, hu'u_assoc]
  match_scalars <;> field_simp [hq] <;> ring

end Ring

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j : I}

set_option maxHeartbeats 1000000 in
-- Elaborating the normal-ordering lemma in the quotient needs a larger budget.
/-- The centre-first positive cubic Serre relation for the actual degree-two candidate.
Reconstructed from the quotient relations. Only `v ≠ 0` is needed: no nonvanishing
quantum sum, difference or factorial is assumed. The reverse entry is unrestricted. -/
theorem qSerre_braidEi_braidEj_of_cartanMatrix_eq_neg_two (hv : v ≠ 0)
    (h : D.cartanMatrix i j = -2) :
    qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat
      (braidEi R i) (braidEj R v i j) = 0 := by
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
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
  have hs := centre_two (E R v i) (E R v j) (F R v i)
    (Kt R v i) (K R v (-ktilde R i)) (v ^ D.d i)
    (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ (pow_ne_zero _ hv) hca
    (E_mul_F_of_ne hij.symm).symm (Kt_mul_E i) hub (Kt_mul_F i)
    (by simpa only [inv_pow] using K_neg_ktilde_mul_E (R := R) (v := v) i)
    hu'b (K_neg_ktilde_mul_F i) (K_neg_mul_Kt i) (Kt_mul_K_neg i)
  rw [h, braidEj_eq_of_cartanMatrix_eq_neg_two h]
  change qSerre (v ^ D.d i) 3 (braidEi R i) (_ • _) = 0
  have he := qSerre_smul_smul (v := v ^ D.d i) 3
    (braidEi (v := v) R i)
    (E R v i ^ 2 * E R v j -
      ((v ^ D.d i + (v ^ D.d i)⁻¹) * (v ^ D.d i)⁻¹) •
        (E R v i * E R v j * E R v i) +
      (v ^ D.d i)⁻¹ ^ 2 • (E R v j * E R v i ^ 2))
    1 (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹
  rw [one_smul, one_pow, one_mul, hs, smul_zero] at he
  exact he

/-- The Chevalley factor for the actual degree-two neighbor is `qᵢ⁻²`.
Reconstructed directly from the candidate definitions. -/
theorem chevalley_braidEj_of_cartanMatrix_eq_neg_two (hv : v ≠ 0)
    (h : D.cartanMatrix i j = -2) :
    chevalley R v (braidEj R v i j) = (v ^ D.d i)⁻¹ ^ 2 • braidFj R v i j := by
  rw [braidEj_eq_of_cartanMatrix_eq_neg_two h,
    braidFj_eq_of_cartanMatrix_eq_neg_two hv h]
  simp only [map_smul, map_add, map_sub, map_mul, map_pow, chevalley_E,
    smul_add, smul_sub, smul_smul]
  match_scalars <;> field_simp [pow_ne_zero (D.d i) hv]

/-- The centre-first negative cubic Serre relation for the actual degree-two candidate.
Reconstructed via the proved quotient Chevalley map. No relation package or braid
automorphism is assumed; ambient rank, toral lattice and reverse entry are unrestricted. -/
theorem qSerre_braidFi_braidFj_of_cartanMatrix_eq_neg_two (hv : v ≠ 0)
    (h : D.cartanMatrix i j = -2) :
    qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat
      (braidFi R i) (braidFj R v i j) = 0 := by
  have hs := congrArg (chevalley R v)
    (qSerre_braidEi_braidEj_of_cartanMatrix_eq_neg_two (R := R) hv h)
  rw [map_qSerre, map_zero, chevalley_braidEi hv,
    chevalley_braidEj_of_cartanMatrix_eq_neg_two hv h, qSerre_smul_smul] at hs
  exact (smul_eq_zero.mp hs).resolve_left
    (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ hv)))
      (pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hv))))

end QuantumGroup
