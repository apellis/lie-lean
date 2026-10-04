/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.Star

/-!
# Mixed neighbour/non-neighbour quantum Serre relations

## Main results

The quantum commutator at the first edge of a three-vertex path satisfies
both quadratic Serre relations with the untouched last vertex. These are
relations missing from the whole-star braid construction.

## References

Reconstructed directly from the defining Serre polynomials. This is a dependency of the
simply-laced braid automorphism theorem, not an assertion of the full theorem.
-/

open LieLean

noncomputable section
namespace LieLean.QuantumGroup

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B]

private lemma path_qSerre_two (q : k) (a b : B) :
    qSerre q 2 a b = a * (a * b) - (q + q⁻¹) • (a * (b * a)) + b * (a * a) := by
  simp [qSerre, Finset.sum_range_succ, qBinomial, pow_two, mul_assoc]
  module

/-- The forward mixed Serre polynomial along a path. Reconstructed polynomial
identity; division is only by `q` and `q + q⁻¹`. -/
theorem qSerre_quantumCommutator_of_path {q : k} {a b c : B}
    (hq : q ≠ 0) (hs : q + q⁻¹ ≠ 0)
    (hab : qSerre q 2 a b = 0) (hbc : qSerre q 2 b c = 0)
    (hac : Commute a c) :
    qSerre q 2 (a * b - q⁻¹ • (b * a)) c = 0 := by
  have h1 := congrArg (fun x : B ↦ x * (b * c)) hab
  have h2 := congrArg (fun x : B ↦ b * (x * c)) hab
  have h3 := congrArg (fun x : B ↦ b * (c * x)) hab
  have h4 := congrArg (fun x : B ↦ x * (c * b)) hab
  have h5 := congrArg (fun x : B ↦ c * (x * b)) hab
  have h6 := congrArg (fun x : B ↦ c * (b * x)) hab
  have h7 := congrArg (fun x : B ↦ x * (a * a)) hbc
  have h8 := congrArg (fun x : B ↦ a * (x * a)) hbc
  have h9 := congrArg (fun x : B ↦ a * (a * x)) hbc
  have hca (x : B) : c * (a * x) = a * (c * x) := by
    rw [← mul_assoc, hac.symm.eq, mul_assoc]
  apply (smul_eq_zero.mp (show (q + q⁻¹) •
    qSerre q 2 (a * b - q⁻¹ • (b * a)) c = 0 from ?_)).resolve_left hs
  simp only [path_qSerre_two, mul_add, add_mul, mul_sub, sub_mul,
    mul_smul_comm, smul_mul_assoc, smul_sub, smul_add, smul_smul,
    mul_zero, zero_mul, mul_assoc, hac.symm.eq, hca] at h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
  linear_combination (norm := (match_scalars <;> field_simp <;> ring))
    -h1 - q⁻¹ ^ 2 • h2 + (q⁻¹ ^ 3 + q⁻¹) • h3 + (q⁻¹ + q) • h4 -
      h5 - q⁻¹ ^ 2 • h6 + q⁻¹ ^ 2 • h7 - (q⁻¹ ^ 2 + 1) • h8 + h9

/-- The reverse mixed Serre relation is linear in the quantum commutator.
The Serre parameter `q` and commutator coefficient `r` can be independent. -/
theorem qSerre_quantumCommutator_of_path_reverse {q r : k} {a b c : B}
    (hcb : qSerre q 2 c b = 0) (hac : Commute a c) :
    qSerre q 2 c (a * b - r • (b * a)) = 0 := by
  have h1 := congrArg (fun x : B ↦ a * x) hcb
  have h2 := congrArg (fun x : B ↦ x * a) hcb
  have hca (x : B) : c * (a * x) = a * (c * x) := by
    rw [← mul_assoc, hac.symm.eq, mul_assoc]
  simp only [path_qSerre_two, mul_add, add_mul, mul_sub, sub_mul,
    mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul,
    mul_zero, zero_mul, mul_assoc, hac.symm.eq, hca] at h1 h2 ⊢
  linear_combination (norm := module) h1 - r • h2

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j l : I}

/-- The actual positive braid images satisfy the forward Serre relation between
an `i`-neighbour `j` and an `i`-non-neighbour `l` joined to `j`.
Ambient rank and entries not displayed are unrestricted. Reconstructed proof. -/
theorem qSerre_braidEj_braidEj_of_path
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -1)
    (hji : D.cartanMatrix j i = -1) (hjl : D.cartanMatrix j l = -1)
    (hil : D.cartanMatrix i l = 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j l).toNat
      (braidEj R v i j) (braidEj R v i l) = 0 := by
  have hd : D.d i = D.d j := by
    have h := D.d_mul_cartanMatrix_comm i j
    rw [hij, hji, mul_neg_one, mul_neg_one] at h
    exact_mod_cast neg_injective h
  have hij' : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at hij
    norm_num at hij
  have hjl' : j ≠ l := by
    rintro rfl
    rw [D.cartanMatrix_self] at hjl
    norm_num at hjl
  have hab : qSerre (v ^ D.d i) 2 (E R v i) (E R v j) = 0 := by
    simpa [hij] using serre_E R v hij'
  have hbc : qSerre (v ^ D.d i) 2 (E R v j) (E R v l) = 0 := by
    simpa [hjl, hd] using serre_E R v hjl'
  rw [braidEj_eq_of_cartanMatrix_eq_neg_one hij,
    braidEj_eq_of_cartanMatrix_eq_zero hil, hjl, ← hd]
  exact qSerre_quantumCommutator_of_path (pow_ne_zero _ hv) hs hab hbc
    (E_commute_E_of_cartanMatrix_eq_zero hil)

/-- The opposite ordered positive relation for a transformed neighbour and an
untouched non-neighbour. No parameter nonvanishing is needed for this direction. -/
theorem qSerre_braidEj_braidEj_of_path_reverse
    (hij : D.cartanMatrix i j = -1) (hlj : D.cartanMatrix l j = -1)
    (hil : D.cartanMatrix i l = 0) :
    qSerre (v ^ D.d l) (1 - D.cartanMatrix l j).toNat
      (braidEj R v i l) (braidEj R v i j) = 0 := by
  have hlj' : l ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at hlj
    norm_num at hlj
  have hcb : qSerre (v ^ D.d l) 2 (E R v l) (E R v j) = 0 := by
    simpa [hlj] using serre_E R v hlj'
  rw [braidEj_eq_of_cartanMatrix_eq_neg_one hij,
    braidEj_eq_of_cartanMatrix_eq_zero hil, hlj]
  exact qSerre_quantumCommutator_of_path_reverse hcb
    (E_commute_E_of_cartanMatrix_eq_zero hil)

/-- The forward negative path relation follows by the actual Chevalley involution,
not an assumed relation package. Reconstructed proof. -/
theorem qSerre_braidFj_braidFj_of_path
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -1)
    (hji : D.cartanMatrix j i = -1) (hjl : D.cartanMatrix j l = -1)
    (hil : D.cartanMatrix i l = 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j l).toNat
      (braidFj R v i j) (braidFj R v i l) = 0 := by
  have h := congrArg (chevalley R v)
    (qSerre_braidEj_braidEj_of_path (R := R) hv hij hji hjl hil hs)
  rw [map_qSerre, map_zero,
    chevalley_braidEj_of_cartanMatrix_eq_neg_one hv hij,
    braidEj_eq_of_cartanMatrix_eq_zero hil, chevalley_E] at h
  rw [braidFj_eq_of_cartanMatrix_eq_zero hil]
  have h' := qSerre_smul_smul (v := v ^ D.d j) (1 - D.cartanMatrix j l).toNat
    (braidFj R v i j) (F R v l) (-(v ^ D.d i)⁻¹) 1
  simp only [one_smul, mul_one] at h'
  rw [h'] at h
  exact (smul_eq_zero.mp h).resolve_left
    (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hv))))

/-- The reverse negative path relation, obtained from its proved positive
companion by Chevalley and cancellation of a nonzero scalar. -/
theorem qSerre_braidFj_braidFj_of_path_reverse
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -1)
    (hlj : D.cartanMatrix l j = -1) (hil : D.cartanMatrix i l = 0) :
    qSerre (v ^ D.d l) (1 - D.cartanMatrix l j).toNat
      (braidFj R v i l) (braidFj R v i j) = 0 := by
  have h := congrArg (chevalley R v)
    (qSerre_braidEj_braidEj_of_path_reverse (R := R) hij hlj hil)
  rw [map_qSerre, map_zero,
    chevalley_braidEj_of_cartanMatrix_eq_neg_one hv hij,
    braidEj_eq_of_cartanMatrix_eq_zero hil, chevalley_E] at h
  rw [braidFj_eq_of_cartanMatrix_eq_zero hil]
  have h' := qSerre_smul_smul (v := v ^ D.d l) (1 - D.cartanMatrix l j).toNat
    (F R v l) (braidFj R v i j) 1 (-(v ^ D.d i)⁻¹)
  simp only [one_smul, one_pow, one_mul] at h'
  rw [h'] at h
  exact (smul_eq_zero.mp h).resolve_left
    (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hv)))

end LieLean.QuantumGroup
