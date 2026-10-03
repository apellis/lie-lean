/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.CoupledSerre

/-!
# Reversed positive transformed quantum Serre relation

## Main results

`QuantumGroup.qSerre_braidEj_braidEi_of_simply_laced_edge` proves the opposite
positive ordering at an edge with both Cartan entries equal to `-1`.

## References

Reconstructed from the defining presentation and the lowering commutator in
`BraidAction/Coupled.lean`. No symmetry or braid automorphism is assumed. Negative images and
other ordered pairs are not claimed.
-/

noncomputable section
namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j : I}

/-- The reversed positive Serre relation for the actual braid candidates at a
simply-laced edge. Reconstructed directly from the presentation. Both directed
Cartan entries are `-1`; ambient rank, characteristic, and all other entries are
unrestricted. This is one ordered relation, not a braid automorphism. -/
theorem qSerre_braidEj_braidEi_of_simply_laced_edge [NeZero v]
    (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j i).toNat
      (braidEj R v i j) (braidEi R i) = 0 := by
  have hv := NeZero.ne v
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have hd : D.d i = D.d j := by
    have hs := D.d_mul_cartanMatrix_comm i j
    rw [h, h', mul_neg_one, mul_neg_one] at hs
    exact_mod_cast neg_injective hs
  let q := v ^ D.d i
  let A := braidEi (v := v) R i
  let X := braidEj R v i j
  let b := E R v j
  have hq0 : q ≠ 0 := pow_ne_zero _ hv
  have hKX : Kt R v i * X = q • (X * Kt R v i) := by
    have ht := braidK_mul_braidEj (R := R) hv hij (-ktilde R i)
    rw [braidK_apply, reflY_neg_ktilde, map_neg, root_ktilde, h,
      mul_neg_one, neg_neg, zpow_natCast] at ht
    exact ht
  have hAX : A * X - q • (X * A) = -q • b := by
    have hc := congrArg (fun z : QuantumGroup R v ↦ z * Kt R v i)
      (braidEj_mul_Fi_sub_of_cartanMatrix_eq_neg_one (R := R) h hq)
    change (X * F R v i - F R v i * X) * Kt R v i =
      -(b * K R v (-ktilde R i)) * Kt R v i at hc
    simp only [sub_mul, neg_mul, mul_assoc, K_neg_mul_Kt, mul_one] at hc
    dsimp [A, braidEi]
    simp only [neg_mul, mul_neg, mul_assoc]
    rw [hKX, mul_smul_comm]
    linear_combination (norm := module) congrArg (fun z : QuantumGroup R v ↦ q • z) hc
  have hXA : X * A - q⁻¹ • (A * X) = b := by
    have hc := congrArg (fun z : QuantumGroup R v ↦ -q⁻¹ • z) hAX
    simpa [smul_sub, smul_smul, hq0, neg_sub, sub_eq_add_neg, add_comm] using hc
  have hXb : X * b - q • (b * X) = 0 := by
    have hs := serre_E R v hij.symm
    rw [h', ← hd] at hs
    change qSerre q 2 b (E R v i) = 0 at hs
    dsimp [X]
    rw [braidEj_eq_of_cartanMatrix_eq_neg_one h]
    change (E R v i * b - q⁻¹ • (b * E R v i)) * b -
      q • (b * (E R v i * b - q⁻¹ • (b * E R v i))) = 0
    simp [qSerre, Finset.sum_range_succ, qBinomial, pow_two, mul_assoc] at hs
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub,
      smul_smul, mul_inv_cancel₀ hq0, one_smul, mul_assoc]
    linear_combination (norm := module) hs
  have he : qSerre q 2 X A = X * (X * A - q⁻¹ • (A * X)) -
      q • ((X * A - q⁻¹ • (A * X)) * X) := by
    simp [qSerre, Finset.sum_range_succ, qBinomial, pow_two, mul_assoc,
      mul_sub, sub_mul, smul_sub, smul_smul, hq0, add_smul]
    module
  rw [h', ← hd]
  change qSerre q 2 X A = 0
  rw [he, hXA]
  exact hXb

end QuantumGroup
