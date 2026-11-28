/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.Diagonal

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

Reconstructed from the defining quotient relations and the repository's `T''` convention.
-/

open LieLean

noncomputable section
namespace LieLean.QuantumGroup

variable {k : Type*} [Field k]

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
  refine braidEj_mul_braidFj_sub hv hij hq ?_
  have hn : negA D i j = 2 := by simp [negA, h]
  rw [hn]
  simpa [qFactorial, qInt, Finset.sum_range_succ] using hs

end LieLean.QuantumGroup
