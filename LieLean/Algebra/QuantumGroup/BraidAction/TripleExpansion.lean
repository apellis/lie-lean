/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.TripleEdge

/-!
# Degree-three negative candidate and factorial

## Main results
The negative candidate's odd-degree sign and the expanded third quantum factorial.

## References
Reconstructed from the original quotient presentation; no external primary source consulted.
-/

noncomputable section
namespace QuantumGroup
variable {k : Type*} [Field k]
/-- Expanded third quantum factorial; reconstructed from its defining recursion. -/
lemma qFactorial_three_eq (q : k) (hq : q ≠ 0) :
    qFactorial q 3 = (q + q⁻¹) * (q ^ 2 + 1 + q⁻¹ ^ 2) := by
  simp only [qFactorial, qInt, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, mul_one, one_mul, zero_add]
  field_simp

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j : I}

/-- Degree-three negative candidate with the repository's odd-degree sign convention.
Reconstructed from the defining sum; the inverse factorial remains totalized. -/
theorem braidFj_eq_of_cartanMatrix_eq_neg_three (hv : v ≠ 0)
    (h : D.cartanMatrix i j = -3) :
    braidFj R v i j = (qFactorial (v ^ D.d i) 3)⁻¹ •
      (-((v ^ D.d i) ^ 3) • (F R v i ^ 3 * F R v j) +
        (((v ^ D.d i) ^ 2 + 1 + (v ^ D.d i)⁻¹ ^ 2) * (v ^ D.d i) ^ 2) •
          (F R v i ^ 2 * F R v j * F R v i) -
        (((v ^ D.d i) ^ 2 + 1 + (v ^ D.d i)⁻¹ ^ 2) * v ^ D.d i) •
          (F R v i * F R v j * F R v i ^ 2) +
        F R v j * F R v i ^ 3) := by
  simp only [braidFj, negA, h, Int.reduceNeg, neg_neg, Int.reduceToNat,
    serreAux, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial,
    Nat.reduceSub, pow_succ, pow_zero, mul_one, one_mul, mul_zero, add_zero,
    zero_add, one_smul, mul_neg, neg_mul, neg_neg, mul_add, add_mul,
    smul_add, smul_sub, smul_smul]
  match_scalars <;> field_simp [pow_ne_zero (D.d i) hv] <;> ring

end QuantumGroup
