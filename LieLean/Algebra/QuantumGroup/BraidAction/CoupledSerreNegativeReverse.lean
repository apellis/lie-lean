/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.CoupledSerreNegative
import LieLean.Algebra.QuantumGroup.BraidAction.CoupledSerreReverse

/-!
# Reversed negative transformed Serre relation

## Main results

The actual negative images satisfy the opposite ordered relation at a mutual `-1` edge.
This uses the independently proved positive companion and the genuine quotient involution.

## References

Reconstructed from the quotient presentation and the positive companion proof.
-/

open LieLean

noncomputable section
namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j : I}

/-- Reversed negative Serre relation for the actual braid candidates. Both directed
Cartan entries must be `-1`; the parameter and degree are those of the outer node `j`.
No rank, characteristic, finite-type, or general braid-automorphism assumption is used. -/
theorem qSerre_braidFj_braidFi_of_simply_laced_edge [NeZero v]
    (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j i).toNat
      (braidFj R v i j) (braidFi R i) = 0 := by
  have hs := congrArg (chevalley R v)
    (qSerre_braidEj_braidEi_of_simply_laced_edge (R := R) h h' hq)
  rw [map_qSerre, map_zero,
    chevalley_braidEj_of_cartanMatrix_eq_neg_one (NeZero.ne v) h,
    chevalley_braidEi (NeZero.ne v), qSerre_smul_smul] at hs
  exact (smul_eq_zero.mp hs).resolve_left
    (mul_ne_zero
      (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ (NeZero.ne v)))))
      (pow_ne_zero _ (pow_ne_zero _ (NeZero.ne v))))

end LieLean.QuantumGroup
