/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.Mixed

/-!
# Degree-two diagonal mixed braid relation

## Main results

* `QuantumGroup.braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_two`: the diagonal mixed
  relation for the existing degree-two braid candidates, in the actual quantum quotient.
* `QuantumGroup.braidEj_eq_of_cartanMatrix_eq_neg_two` and the negative analogue:
  degree-two expansions in the repository's convention.
* `QuantumGroup.reflY_ktilde_of_cartanMatrix_eq_neg_two`: the symmetrizer-correct toral
  exponent, with no condition on the reverse Cartan entry.

The ambient rank and toral lattice are unrestricted. Explicit parameter assumptions are
`v ≠ 0`, `q_i - q_i⁻¹ ≠ 0`, and `q_i + q_i⁻¹ ≠ 0`, where `q_i = v ^ D.d i`.
No nonvanishing condition at node `j`, characteristic-zero hypothesis, or relation
package is assumed. This is one prerequisite for higher-edge automorphisms, not the
full automorphism or a length-four braid relation.

## References

Reconstructed from the defining quotient relations and the repository's `T''` convention;
no external primary source was consulted.
-/

noncomputable section
namespace QuantumGroup

variable {k : Type*} [Field k]

section Ring
variable {B : Type*} [Ring B] [Algebra k B]

set_option maxHeartbeats 4000000 in
-- Normal ordering produces many scalar coefficients, all checked by field normalization.
private lemma degree_two_diagonal (a b c d u u' w w' : B) (q p : k)
    (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0) (hs : q + q⁻¹ ≠ 0)
    (hac : a * c = c * a + (q - q⁻¹)⁻¹ • (u - u'))
    (hbd : b * d = d * b + p • (w - w'))
    (had : a * d = d * a) (hbc : b * c = c * b)
    (hua : u * a = q ^ 2 • (a * u))
    (hub : u * b = q⁻¹ ^ 2 • (b * u))
    (huc : u * c = q⁻¹ ^ 2 • (c * u))
    (hud : u * d = q ^ 2 • (d * u))
    (hu'a : u' * a = q⁻¹ ^ 2 • (a * u'))
    (hu'b : u' * b = q ^ 2 • (b * u'))
    (hu'c : u' * c = q ^ 2 • (c * u'))
    (hu'd : u' * d = q⁻¹ ^ 2 • (d * u'))
    (hwa : w * a = q⁻¹ ^ 2 • (a * w))
    (hwc : w * c = q ^ 2 • (c * w))
    (hw'a : w' * a = q ^ 2 • (a * w'))
    (hw'c : w' * c = q⁻¹ ^ 2 • (c * w'))
    (hu'u : u' * u = 1) (huu' : u * u' = 1)
    (hwu : w * u = u * w) (hwu' : w * u' = u' * w)
    (hw'u : w' * u = u * w') (hw'u' : w' * u' = u' * w') :
    let X := (q + q⁻¹)⁻¹ • (a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) +
      q⁻¹ ^ 2 • (b * a ^ 2))
    let Z := (q + q⁻¹)⁻¹ • (q ^ 2 • (c ^ 2 * d) -
      ((q + q⁻¹) * q) • (c * d * c) + d * c ^ 2)
    X * Z - Z * X = p • (u ^ 2 * w - u' ^ 2 * w') := by
  have hac_assoc (z : B) := congrArg (fun t : B ↦ t * z) hac
  have hbd_assoc (z : B) := congrArg (fun t : B ↦ t * z) hbd
  have had_assoc (z : B) := congrArg (fun t : B ↦ t * z) had
  have hbc_assoc (z : B) := congrArg (fun t : B ↦ t * z) hbc
  have hua_assoc (z : B) := congrArg (fun t : B ↦ t * z) hua
  have hub_assoc (z : B) := congrArg (fun t : B ↦ t * z) hub
  have huc_assoc (z : B) := congrArg (fun t : B ↦ t * z) huc
  have hud_assoc (z : B) := congrArg (fun t : B ↦ t * z) hud
  have hu'a_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'a
  have hu'b_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'b
  have hu'c_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'c
  have hu'd_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'd
  have hwa_assoc (z : B) := congrArg (fun t : B ↦ t * z) hwa
  have hwc_assoc (z : B) := congrArg (fun t : B ↦ t * z) hwc
  have hw'a_assoc (z : B) := congrArg (fun t : B ↦ t * z) hw'a
  have hw'c_assoc (z : B) := congrArg (fun t : B ↦ t * z) hw'c
  have hu'u_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'u
  have huu'_assoc (z : B) := congrArg (fun t : B ↦ t * z) huu'
  have hwu_assoc (z : B) := congrArg (fun t : B ↦ t * z) hwu
  have hwu'_assoc (z : B) := congrArg (fun t : B ↦ t * z) hwu'
  have hw'u_assoc (z : B) := congrArg (fun t : B ↦ t * z) hw'u
  have hw'u'_assoc (z : B) := congrArg (fun t : B ↦ t * z) hw'u'
  simp only [mul_assoc, add_mul, sub_mul, smul_mul_assoc, one_mul] at *
  simp only [pow_two, mul_sub, mul_add,
    mul_smul_comm, smul_add, smul_sub, mul_assoc, mul_one,
    hac, hbd, had, hbc, hua, hub, huc, hud, hu'a, hu'b, hu'c, hu'd, hwa, hwc, hw'a, hw'c, hu'u,
    huu', hwu, hwu', hw'u, hw'u', hac_assoc, hbd_assoc, had_assoc, hbc_assoc, hua_assoc,
    hub_assoc, huc_assoc, hud_assoc, hu'a_assoc, hu'b_assoc, hu'c_assoc, hu'd_assoc, hwa_assoc,
    hwc_assoc, hw'a_assoc, hw'c_assoc, hu'u_assoc, huu'_assoc, hwu_assoc, hwu'_assoc, hw'u_assoc,
    hw'u'_assoc]
  have hd2 : q ^ 2 - 1 ≠ 0 := by
    have he : q ^ 2 - 1 = q * (q - q⁻¹) := by field_simp
    rw [he]
    exact mul_ne_zero hq hd
  have hs2 : q ^ 2 + 1 ≠ 0 := by
    have he : q ^ 2 + 1 = q * (q + q⁻¹) := by field_simp
    rw [he]
    exact mul_ne_zero hq hs
  match_scalars <;> field_simp [hq, hd2, hs2] <;> ring

end Ring

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j : I}

/-- Degree-two positive candidate, expanded from the defining Serre sum. -/
theorem braidEj_eq_of_cartanMatrix_eq_neg_two (h : D.cartanMatrix i j = -2) :
    braidEj R v i j =
      (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ •
        (E R v i ^ 2 * E R v j -
          ((v ^ D.d i + (v ^ D.d i)⁻¹) * (v ^ D.d i)⁻¹) •
            (E R v i * E R v j * E R v i) +
          (v ^ D.d i)⁻¹ ^ 2 • (E R v j * E R v i ^ 2)) := by
  simp only [braidEj, negA, h, Int.reduceNeg, neg_neg, Int.reduceToNat, qFactorial, qInt,
    Nat.reduceAdd, Nat.add_one_sub_one, inv_pow, mul_comm, Finset.sum_range_succ,
    Finset.range_one, Finset.sum_singleton, pow_zero, inv_one, tsub_zero, pow_one, mul_one,
    tsub_self, zero_add, zero_tsub, serreAux, add_comm, qBinomial, one_smul, mul_zero,
    mul_neg, neg_add_rev, even_two, Even.neg_pow, one_pow, zero_mul, add_zero, one_mul,
    smul_add, sub_eq_add_neg, smul_neg]
  module

/-- Degree-two negative candidate, with the existing `T''` convention. -/
theorem braidFj_eq_of_cartanMatrix_eq_neg_two (hv : v ≠ 0)
    (h : D.cartanMatrix i j = -2) :
    braidFj R v i j =
      (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ •
        ((v ^ D.d i) ^ 2 • (F R v i ^ 2 * F R v j) -
          ((v ^ D.d i + (v ^ D.d i)⁻¹) * v ^ D.d i) •
            (F R v i * F R v j * F R v i) + F R v j * F R v i ^ 2) := by
  simp only [braidFj, negA, h, Int.reduceNeg, neg_neg, Int.reduceToNat, qFactorial, qInt,
    Nat.reduceAdd, Nat.add_one_sub_one, inv_pow, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, tsub_zero, pow_one, pow_zero, inv_one, mul_one, tsub_self,
    one_mul, zero_add, zero_tsub, even_two, Even.neg_pow, one_pow, serreAux, qBinomial,
    one_smul, mul_zero, neg_mul, neg_add_rev, add_zero, smul_add, smul_smul,
    sub_eq_add_neg, smul_neg]
  match_scalars <;> field_simp [pow_ne_zero (D.d i) hv]
  ring

omit [DecidableEq I] in
/-- Symmetrizer-correct reflection of the neighboring toral exponent at a double edge. -/
lemma reflY_ktilde_of_cartanMatrix_eq_neg_two (h : D.cartanMatrix i j = -2) :
    reflY R i (ktilde R j) = ktilde R j + 2 • ktilde R i := by
  have hr : R.root i (ktilde R j) = -((D.d i : ℤ) * 2) := by
    rw [root_ktilde, ← D.d_mul_cartanMatrix_comm i j, h]
    ring
  rw [reflY_apply, hr, neg_smul, sub_neg_eq_add, mul_smul, natCast_zsmul]
  simp only [ktilde, two_smul, smul_add]

/-- The actual diagonal mixed relation for the degree-two braid images in arbitrary
ambient rank. The reverse Cartan entry is unrestricted: the toral calculation uses the
symmetrizer, not equality of the two node parameters. Reconstructed from the quotient
presentation. The extra parameter conditions exclude precisely the denominators used
here; no automorphism, transformed relation package, or faithfulness is assumed. -/
theorem braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_two
    (hv : v ≠ 0) (h : D.cartanMatrix i j = -2)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0) :
    braidEj R v i j * braidFj R v i j - braidFj R v i j * braidEj R v i j =
      (v ^ D.d j - (v ^ D.d j)⁻¹)⁻¹ •
        (braidK R v i (.ofAdd (ktilde R j)) -
          braidK R v i (.ofAdd (-ktilde R j))) := by
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have hr : R.root i (ktilde R j) = -((D.d i : ℤ) * 2) := by
    rw [root_ktilde, ← D.d_mul_cartanMatrix_comm i j, h]
    ring
  have he : v ^ ((D.d i : ℤ) * 2) = (v ^ D.d i) ^ 2 := by
    rw [zpow_mul, zpow_natCast, zpow_ofNat]
  have H := degree_two_diagonal
    (E R v i) (E R v j) (F R v i) (F R v j)
    (Kt R v i) (K R v (-ktilde R i)) (Kt R v j) (K R v (-ktilde R j))
    (v ^ D.d i) (v ^ D.d j - (v ^ D.d j)⁻¹)⁻¹ (pow_ne_zero _ hv) hq hs
    (by simpa only [↓reduceIte] using
      (sub_eq_iff_eq_add'.mp (E_mul_F_sub R v i i)))
    (by simpa only [↓reduceIte] using
      (sub_eq_iff_eq_add'.mp (E_mul_F_sub R v j j)))
    (E_mul_F_of_ne hij) (E_mul_F_of_ne hij.symm)
    (by rw [Kt, K_mul_E, root_ktilde, D.cartanMatrix_self, he])
    (by rw [Kt, K_mul_E, root_ktilde, h, mul_neg, zpow_neg, he, inv_pow])
    (by rw [Kt, K_mul_F, root_ktilde, D.cartanMatrix_self, zpow_neg, he, inv_pow])
    (by rw [Kt, K_mul_F, root_ktilde, h, mul_neg, neg_neg, he])
    (by rw [K_mul_E, map_neg, root_ktilde, D.cartanMatrix_self, zpow_neg, he, inv_pow])
    (by rw [K_mul_E, map_neg, root_ktilde, h, mul_neg, neg_neg, he])
    (by rw [K_mul_F, map_neg, neg_neg, root_ktilde, D.cartanMatrix_self, he])
    (by rw [K_mul_F, map_neg, neg_neg, root_ktilde, h, mul_neg, zpow_neg, he, inv_pow])
    (by rw [Kt, K_mul_E, hr, zpow_neg, he, inv_pow])
    (by rw [Kt, K_mul_F, hr, neg_neg, he])
    (by rw [K_mul_E, map_neg, hr, neg_neg, he])
    (by rw [K_mul_F, map_neg, neg_neg, hr, zpow_neg, he, inv_pow])
    (by simp [Kt, K_add]) (by simp [Kt, K_add])
    (K_comm (R := R) (v := v) _ _) (K_comm (R := R) (v := v) _ _)
    (K_comm (R := R) (v := v) _ _) (K_comm (R := R) (v := v) _ _)
  rw [braidEj_eq_of_cartanMatrix_eq_neg_two h,
    braidFj_eq_of_cartanMatrix_eq_neg_two hv h]
  rw [H]
  rw [braidK_apply, braidK_apply, map_neg, reflY_ktilde_of_cartanMatrix_eq_neg_two h]
  simp only [Kt, pow_two, K_add, two_smul, neg_add_rev]
  congr 2
  congr 1
  abel

end QuantumGroup
