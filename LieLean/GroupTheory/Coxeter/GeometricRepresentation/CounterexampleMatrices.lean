/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Mathlib.GroupTheory.Coxeter.Basic

/-!
# A nonfaithful representation of the (5,10,2) Coxeter presentation

## Main definitions and results
* `GeometricCounterexample.triangle`: the actual Mathlib Coxeter matrix.
* `GeometricCounterexample.badRepresentation`: its presented group maps to the group
  of invertible real matrices, with explicit square-root coefficients.
* `GeometricCounterexample.w_ne_one`: the commutator word is nontrivial, witnessed by
  a second representation; no faithfulness theorem is assumed for that comparison.
* `GeometricCounterexample.w_mem_badRepresentation_ker`: the same word is killed.
* `GeometricCounterexample.badRepresentation_not_injective`: unconditional nonfaithfulness.
* `GeometricCounterexample.badRepresentation_ker_ne_bot`: a genuine nontrivial group kernel.

## References and formal boundary
The proof is reconstructed, not transcribed from an external source. The first namespace
reproduces the previously verified `GeometricFaithfulScope.lean` matrix certificates
(SHA256 427fc1988559b20093a501a435d3a93e1af637f18c4d3cc47d6ccd71206297b9).
Exact polynomial calculations verify all Coxeter relations, and `CoxeterSystem.lift`
provides the presentation link. The square-root coefficients are explicit; identifying
these with the real parts of primitive complex roots of orders 10 and 20 is still a
separate, unformalized step. This file does not assert noninjectivity of the repository's
fixed opaque `Classical.choose` representation. See `geometric-counterexample-state.md`.
-/


namespace GeometricFaithfulScope

/-- The three-by-three matrices in the simple-root basis. -/
abbrev Mat (K : Type*) := Matrix (Fin 3) (Fin 3) K

/-- The first simple reflection, with adjacent coefficient `x`. -/
def A {K : Type*} [CommRing K] (x : K) : Mat K :=
  !![-1, x, 0; 0, 1, 0; 0, 0, 1]
/-- The second simple reflection, with adjacent coefficients `x` and `y`. -/
def B {K : Type*} [CommRing K] (x y : K) : Mat K :=
  !![1, 0, 0; x, -1, y; 0, 0, 1]
/-- The third simple reflection, with adjacent coefficient `y`. -/
def C {K : Type*} [CommRing K] (y : K) : Mat K :=
  !![1, 0, 0; 0, 1, 0; 0, y, -1]
/-- The matrix word `(A x * B x y * C y) ^ 2`. -/
def U {K : Type*} [CommRing K] (x y : K) : Mat K :=
  (A x * B x y * C y) ^ 2
/-- The conjugate of `U x y` by the first simple reflection. -/
def V {K : Type*} [CommRing K] (x y : K) : Mat K :=
  A x * U x y * A x


theorem U_eq {K : Type*} [CommRing K] (x y : K) :
    U x y = !![1 -3 * x ^ 2 + x ^ 2 * y ^ 2 + x ^ 4,
      2 * x -4 * x * y ^ 2 + x * y ^ 4 -x ^ 3 + x ^ 3 * y ^ 2,
      3 * x * y -x * y ^ 3 -x ^ 3 * y;
    -2 * x + x * y ^ 2 + x ^ 3, 1 -3 * y ^ 2 + y ^ 4 -x ^ 2 + x ^ 2 * y ^ 2,
      2 * y -y ^ 3 -x ^ 2 * y;
    x * y, -2 * y + y ^ 3, 1 -y ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, A, B, C, pow_two, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem V_eq {K : Type*} [CommRing K] (x y : K) :
    V x y = !![1 -x ^ 2, -2 * x + x * y ^ 2 + x ^ 3, -x * y;
    2 * x -x * y ^ 2 -x ^ 3, 1 -3 * y ^ 2 + y ^ 4 -3 * x ^ 2 + 2 * x ^ 2 * y ^ 2 + x ^ 4,
      2 * y -y ^ 3 -x ^ 2 * y;
    -x * y, -2 * y + y ^ 3 + x ^ 2 * y, 1 -y ^ 2] := by
  rw [V, U_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- Reconstructed exact algebra: degenerate (2,5,10) choice kills this commutator. -/
theorem bad_commute {K : Type*} [CommRing K] (x y : K) (h : x ^ 2 + y ^ 2 = 4) :
    U x y * V x y = V x y * U x y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [U_eq, neg_mul, V_eq, Fin.zero_eta, Fin.isValue, Matrix.mul_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
      Fin.sum_univ_succ, Matrix.cons_val_succ, Finset.univ_unique, Fin.default_eq_zero, mul_neg,
      Finset.sum_neg_distrib, Finset.sum_const, Finset.card_singleton, one_smul, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
  all_goals solve
    | ring
    | linear_combination (2 * x ^ 2 * y ^ 2 -x ^ 2 * y ^ 4 -x ^ 4 * y ^ 2) * h
    | linear_combination
        (5 * x * y ^ 2 -5 * x * y ^ 4 + x * y ^ 6 -4 * x ^ 3 * y ^ 2 +
          2 * x ^ 3 * y ^ 4 + x ^ 5 * y ^ 2) * h
    | linear_combination (-2 * x * y + 4 * x * y ^ 3 -x * y ^ 5 -x ^ 3 * y ^ 3) * h
    | linear_combination (4 * x * y ^ 2 -2 * x * y ^ 4 -2 * x ^ 3 * y ^ 2) * h
    | linear_combination (-2 * x ^ 2 * y ^ 2 + x ^ 2 * y ^ 4 + x ^ 4 * y ^ 2) * h
    | linear_combination (2 * x * y -2 * x * y ^ 3) * h
    | linear_combination (-x ^ 2 * y + x ^ 2 * y ^ 3) * h


/-- The corresponding canonical coefficients distinguish the same two words. -/
theorem good_difference {K : Type*} [CommRing K] (x y : K)
    (hx : x ^ 2 = x + 1) (hy : y ^ 2 = x + 2) :
    (U x y * V x y) 0 0 - (V x y * U x y) 0 0 = -40 * x-25 := by
  simp [U_eq, V_eq, Matrix.mul_apply, Fin.sum_univ_succ]
  linear_combination
    (-25 -15 * x -10 * x ^ 2 -9 * x ^ 3 -5 * x ^ 4 -x ^ 5) * hx +
      (4 * x ^ 2 * y ^ 2 -x ^ 2 * y ^ 4 + 2 * x ^ 3 -x ^ 3 * y ^ 2 + x ^ 4 -
        2 * x ^ 4 * y ^ 2 -2 * x ^ 5 -x ^ 6) * hy

/-- This does not invoke faithfulness of the canonical representation. -/
theorem good_not_commute (x y : ℝ) (hx : x ^ 2 = x + 1) (hy : y ^ 2 = x + 2)
    (hpos : 0 < x) : U x y * V x y ≠ V x y * U x y := by
  intro h
  have hd := good_difference x y hx hy
  rw [h, sub_self] at hd
  linarith

/-- Concrete real coefficients show that the algebraic hypotheses are jointly inhabited. -/
theorem explicit_coefficients : ∃ x y z : ℝ,
    0 < x ∧ x ^ 2 = x + 1 ∧ y ^ 2 = 3-x ∧ z ^ 2 = x + 2 ∧
    U x y * V x y = V x y * U x y ∧
    U x z * V x z ≠ V x z * U x z := by
  let x : ℝ := (1 + Real.sqrt 5) / 2
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  have hx : x ^ 2 = x + 1 := by dsimp [x]; nlinarith
  have hp : 0 < x := by dsimp [x]; positivity
  have hb : x < 3 := by dsimp [x]; nlinarith
  have hy : (Real.sqrt (3-x)) ^ 2 = 3-x := Real.sq_sqrt (by linarith)
  have hz : (Real.sqrt (x + 2)) ^ 2 = x + 2 := Real.sq_sqrt (by linarith)
  refine ⟨x, Real.sqrt (3-x), Real.sqrt (x + 2), hp, hx, hy, hz, ?_, ?_⟩
  · apply bad_commute
    linarith
  · exact good_not_commute x _ hx hz hp


end GeometricFaithfulScope

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

/-!
# Exact Coxeter pair relations for the (5,10,2) matrices

The arguments are reconstructed exact polynomial certificates, over arbitrary
commutative rings. Both coefficient choices satisfy the same quartic equation.
-/


namespace GeometricCounterexampleRelations

open GeometricFaithfulScope

/-- The first reflection is an involution (direct reconstructed calculation). -/
theorem A_sq {K : Type*} [CommRing K] (x : K) : A x ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The second reflection is an involution (direct reconstructed calculation). -/
theorem B_sq {K : Type*} [CommRing K] (x t : K) : B x t ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The third reflection is an involution (direct reconstructed calculation). -/
theorem C_sq {K : Type*} [CommRing K] (t : K) : C t ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The nonadjacent reflections satisfy the exponent-two relation. -/
theorem AC_sq {K : Type*} [CommRing K] (x t : K) : (A x * C t) ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, C, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem AB_sq_nf {K : Type*} [CommRing K] (x t : K) (hx : x ^ 2 = x + 1) :
    (A x * B x t) ^ 2 = !![0, -1, x * t + t;
    1, -x, x * t + t;
    0, 0, 1] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [A, B, Matrix.cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.vecMul_cons,
      Matrix.head_cons, neg_smul, one_smul, Matrix.neg_cons, neg_zero, Matrix.neg_empty,
      Matrix.tail_cons, Matrix.smul_cons, smul_eq_mul, mul_neg, mul_one, Matrix.smul_empty,
      zero_smul, Matrix.empty_vecMul, add_zero, Matrix.add_cons, zero_add,
      Matrix.empty_add_empty, Matrix.empty_mul, Equiv.symm_apply_apply, Fin.zero_eta,
      Fin.isValue, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
      Matrix.cons_val_zero, Fin.sum_univ_succ, Matrix.cons_val_succ, neg_mul,
      Finset.univ_unique, Fin.default_eq_zero, mul_zero, Finset.sum_const_zero, Fin.mk_one,
      Matrix.cons_val_one, neg_neg, Fin.reduceFinMk, Matrix.cons_val, Finset.sum_const,
      Finset.card_singleton, neg_add_cancel, one_mul, zero_mul]
  all_goals solve
    | ring
    | linear_combination (x ^ 2 + x - 1) * hx
    | linear_combination (-x - 1) * hx
    | linear_combination (x * t + t) * hx
    | linear_combination (x + 1) * hx
    | linear_combination (-1) * hx
    | linear_combination (t) * hx

private theorem AB_four_nf {K : Type*} [CommRing K] (x t : K)
    (hx : x ^ 2 = x + 1) :
    (A x * B x t) ^ 4 = !![-1, x, 0;
    -x, x, t;
    0, 0, 1] := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, AB_sq_nf x t hx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, Fin.sum_univ_succ, mul_zero,
      Matrix.cons_val_succ, mul_one, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_const_zero, add_zero, zero_add, Fin.mk_one, Matrix.cons_val_one, mul_neg,
      neg_zero, neg_mul, one_mul, neg_neg, Fin.reduceFinMk, Matrix.cons_val, zero_mul,
      neg_add_rev, Finset.sum_const, Finset.card_singleton, smul_add, one_smul,
      add_neg_add_add_cancel, neg_add_cancel]
  all_goals solve
    | ring
    | linear_combination (1) * hx
    | linear_combination (-t) * hx

/-- Reconstructed exact exponent-five relation for the first adjacent pair. -/
theorem AB_pow_five {K : Type*} [CommRing K] (x t : K) (hx : x ^ 2 = x + 1) :
    (A x * B x t) ^ 5 = 1 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_add, pow_one, AB_four_nf x t hx]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [A, B, Matrix.cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.vecMul_cons,
      Matrix.head_cons, neg_smul, one_smul, Matrix.neg_cons, neg_zero, Matrix.neg_empty,
      Matrix.tail_cons, Matrix.smul_cons, smul_eq_mul, mul_neg, mul_one, Matrix.smul_empty,
      zero_smul, Matrix.empty_vecMul, add_zero, Matrix.add_cons, zero_add,
      Matrix.empty_add_empty, Matrix.empty_mul, Equiv.symm_apply_apply, Fin.zero_eta,
      Fin.isValue, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
      Matrix.cons_val_zero, Fin.sum_univ_succ, neg_mul, one_mul, neg_add_rev, neg_neg,
      Matrix.cons_val_succ, Finset.univ_unique, Fin.default_eq_zero, mul_zero,
      Finset.sum_const_zero, neg_add_cancel_comm, Matrix.one_apply_eq, Fin.mk_one,
      Matrix.cons_val_one, add_neg_cancel, ne_eq, zero_ne_one, not_false_eq_true,
      Matrix.one_apply_ne, Fin.reduceFinMk, Matrix.cons_val, neg_add_cancel, Fin.reduceEq,
      one_ne_zero, Finset.sum_const, Finset.card_singleton, zero_mul]
  all_goals solve
    | ring
    | linear_combination (-x) * hx
    | linear_combination (1) * hx
    | linear_combination (-t) * hx

private theorem BC_sq_nf {K : Type*} [CommRing K] (x t : K) :
    (B x t * C t) ^ 2 = !![1, 0, 0;
    x * t ^ 2, t ^ 4 - 3 * t ^ 2 + 1, -t ^ 3 + 2 * t;
    x * t, t ^ 3 - 2 * t, -t ^ 2 + 1] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [B, C, Matrix.cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.vecMul_cons,
      Matrix.head_cons, one_smul, Matrix.tail_cons, zero_smul, Matrix.empty_vecMul, add_zero,
      Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty, neg_smul,
      Matrix.neg_cons, neg_zero, Matrix.neg_empty, mul_neg, Matrix.add_cons, zero_add,
      Matrix.empty_add_empty, Matrix.empty_mul, Equiv.symm_apply_apply, Fin.zero_eta,
      Fin.isValue, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
      Matrix.cons_val_zero, Fin.sum_univ_succ, Matrix.cons_val_succ, zero_mul,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_const_zero, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, neg_mul, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_singleton, neg_neg, one_mul, add_left_inj, neg_inj]
  all_goals solve
    | ring

private theorem BC_four_nf {K : Type*} [CommRing K] (x t : K)
    (ht : t ^ 4 = 5 * t ^ 2 - 5) :
    (B x t * C t) ^ 4 = !![1, 0, 0;
    4 * x * t ^ 2 - 5 * x, 1, -t;
    2 * x * t ^ 3 - 3 * x * t, t, -t ^ 2 + 1] := by
  rw [show (B x t * C t) ^ 4 = (B x t * C t) ^ 2 * (B x t * C t) ^ 2 by
    rw [← pow_add], BC_sq_nf]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, Fin.sum_univ_succ, mul_one,
      Matrix.cons_val_succ, zero_mul, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_const_zero, add_zero, Fin.mk_one, Matrix.cons_val_one, mul_zero,
      Fin.reduceFinMk, Matrix.cons_val, Finset.sum_const, Finset.card_singleton, one_smul,
      zero_add]
  all_goals solve
    | ring
    | linear_combination (x * t ^ 2 + x) * ht
    | linear_combination (t ^ 4 - 2 * t ^ 2) * ht
    | linear_combination (-t ^ 3 + t) * ht
    | linear_combination (x * t) * ht
    | linear_combination (t ^ 3 - t) * ht
    | linear_combination (-t ^ 2) * ht

private theorem BC_five_nf {K : Type*} [CommRing K] (x t : K)
    (ht : t ^ 4 = 5 * t ^ 2 - 5) :
    (B x t * C t) ^ 5 = !![1, 0, 0;
    4 * x * t ^ 2 - 4 * x, -1, 0;
    2 * x * t ^ 3 - 2 * x * t, 0, -1] := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_add, pow_one, BC_four_nf x t ht]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [B, C, Matrix.cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.vecMul_cons,
      Matrix.head_cons, one_smul, Matrix.tail_cons, zero_smul, Matrix.empty_vecMul, add_zero,
      Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty, neg_smul,
      Matrix.neg_cons, neg_zero, Matrix.neg_empty, mul_neg, Matrix.add_cons, zero_add,
      Matrix.empty_add_empty, Matrix.empty_mul, Equiv.symm_apply_apply, Fin.zero_eta,
      Fin.isValue, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
      Matrix.cons_val_zero, Fin.sum_univ_succ, Matrix.cons_val_succ, zero_mul,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_const_zero, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, one_mul, neg_mul,
      Finset.sum_neg_distrib, Finset.sum_const, Finset.card_singleton, add_neg_cancel_right,
      neg_neg, neg_add_cancel, neg_add_rev, smul_add, smul_neg]
  all_goals solve
    | ring

/-- The quartic relation alone implies the exponent-ten Coxeter relation. -/
theorem BC_pow_ten {K : Type*} [CommRing K] (x t : K)
    (ht : t ^ 4 = 5 * t ^ 2 - 5) : (B x t * C t) ^ 10 = 1 := by
  rw [show (10 : ℕ) = 5 + 5 from rfl, pow_add, BC_five_nf x t ht]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The incompatible coefficient choice satisfies the shared quartic. -/
theorem quartic_bad {K : Type*} [CommRing K] (x t : K)
    (hx : x ^ 2 = x + 1) (ht : t ^ 2 = 3 - x) : t ^ 4 = 5 * t ^ 2 - 5 := by
  linear_combination hx + (t ^ 2 - x - 2) * ht

/-- The canonical coefficient choice satisfies the shared quartic. -/
theorem quartic_good {K : Type*} [CommRing K] (x t : K)
    (hx : x ^ 2 = x + 1) (ht : t ^ 2 = x + 2) : t ^ 4 = 5 * t ^ 2 - 5 := by
  linear_combination hx + (t ^ 2 + x - 3) * ht

/-- The exponent-ten relation for the incompatible coefficient choice. -/
theorem BC_pow_ten_bad {K : Type*} [CommRing K] (x t : K)
    (hx : x ^ 2 = x + 1) (ht : t ^ 2 = 3 - x) : (B x t * C t) ^ 10 = 1 :=
  BC_pow_ten x t (quartic_bad x t hx ht)

/-- The exponent-ten relation for the canonical coefficient choice. -/
theorem BC_pow_ten_good {K : Type*} [CommRing K] (x t : K)
    (hx : x ^ 2 = x + 1) (ht : t ^ 2 = x + 2) : (B x t * C t) ^ 10 = 1 :=
  BC_pow_ten x t (quartic_good x t hx ht)


end GeometricCounterexampleRelations


namespace GeometricCounterexample

open GeometricFaithfulScope GeometricCounterexampleRelations

/-- The actual Mathlib Coxeter matrix of the triangle (5,10,2). -/
def triangle : CoxeterMatrix (Fin 3) where
  M := !![1, 5, 2; 5, 1, 10; 2, 10, 1]
  isSymm := by decide
  diagonal := by decide
  off_diagonal := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

/-- The presented Coxeter group, not a matrix-defined quotient. -/
abbrev W := triangle.Group

/-- Three explicit reflections in the given simple-root basis. -/
def generators (x t : ℝ) : Fin 3 → Mat ℝ := ![A x, B x t, C t]

private theorem reverse_relation {M : Type*} [Monoid M] (a b : M) (n : ℕ)
    (ha : a * a = 1) (hab : (a * b) ^ n = 1) : (b * a) ^ n = 1 := by
  have h : a * (b * a) ^ n = (a * b) ^ n * a :=
    (show SemiconjBy a (b * a) (a * b) from (mul_assoc a b a).symm).pow_right n
  calc
    (b * a) ^ n = a * (a * (b * a) ^ n) := by rw [← mul_assoc, ha, one_mul]
    _ = a * ((a * b) ^ n * a) := congrArg (a * ·) h
    _ = 1 := by rw [hab, one_mul, ha]

/-- Polynomial equations suffice for every relation of the actual presentation. -/
theorem generators_liftable (x t : ℝ) (hx : x ^ 2 = x + 1)
    (ht : t ^ 4 = 5 * t ^ 2 - 5) : triangle.IsLiftable (generators x t) := by
  have ha : A x * A x = 1 := by simpa [pow_two] using A_sq x
  have hb : B x t * B x t = 1 := by simpa [pow_two] using B_sq x t
  have hc : C t * C t = 1 := by simpa [pow_two] using C_sq t
  have hab := AB_pow_five x t hx
  have hbc := BC_pow_ten x t ht
  have hac := AC_sq x t
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [generators, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, triangle,
      CoxeterMatrix.diagonal, pow_one, Fin.mk_one, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Fin.reduceFinMk, Matrix.cons_val]
  · exact ha
  · exact hab
  · exact hac
  · exact reverse_relation _ _ _ ha hab
  · exact hb
  · exact hbc
  · exact reverse_relation _ _ _ ha hac
  · exact reverse_relation _ _ _ hb hbc
  · exact hc

/-- Representation obtained using Mathlib's Coxeter universal property. -/
noncomputable def representation (x t : ℝ) (hx : x ^ 2 = x + 1)
    (ht : t ^ 4 = 5 * t ^ 2 - 5) : W →* Mat ℝ :=
  triangle.toCoxeterSystem.lift ⟨generators x t, generators_liftable x t hx ht⟩

/-- The value on each simple generator is exactly the declared reflection. -/
@[simp] theorem representation_simple (x t : ℝ) (hx : x ^ 2 = x + 1)
    (ht : t ^ 4 = 5 * t ^ 2 - 5) (i : Fin 3) :
    representation x t hx ht (triangle.simple i) = generators x t i :=
  triangle.toCoxeterSystem.lift_apply_simple (generators_liftable x t hx ht) i

/-- The first fixed word (abc)² in the presented group. -/
def u : W := (triangle.simple 0 * triangle.simple 1 * triangle.simple 2) ^ 2

/-- The conjugate a u a (the first generator is an involution). -/
def v : W := triangle.simple 0 * u * triangle.simple 0

/-- A fixed potential kernel witness, independent of all coefficient choices. -/
def w : W := (u * v) * (v * u)⁻¹

@[simp] theorem representation_u (x t : ℝ) (hx : x ^ 2 = x + 1)
    (ht : t ^ 4 = 5 * t ^ 2 - 5) : representation x t hx ht u = U x t := by
  simp [u, generators, U]

@[simp] theorem representation_v (x t : ℝ) (hx : x ^ 2 = x + 1)
    (ht : t ^ 4 = 5 * t ^ 2 - 5) : representation x t hx ht v = V x t := by
  simp [v, generators, V]

/-- The bad coefficient choice kills the fixed word in the actual Coxeter group. -/
theorem bad_kills_w (x y : ℝ) (hx : x ^ 2 = x + 1) (hy : y ^ 2 = 3 - x) :
    representation x y hx (quartic_bad x y hx hy) w = 1 := by
  let ρ := representation x y hx (quartic_bad x y hx hy)
  have heq : ρ (u * v) = ρ (v * u) := by
    simpa [ρ] using bad_commute x y (by linarith : x ^ 2 + y ^ 2 = 4)
  change ρ ((u * v) * (v * u)⁻¹) = 1
  rw [map_mul, heq, ← map_mul, mul_inv_cancel, map_one]

/-- The comparison representation certifies noncommutation without a faithfulness premise. -/
theorem words_not_commute (x z : ℝ) (hx : x ^ 2 = x + 1)
    (hz : z ^ 2 = x + 2) (hp : 0 < x) : u * v ≠ v * u := by
  intro h
  have hm := congrArg (representation x z hx (quartic_good x z hx hz)) h
  exact good_not_commute x z hx hz hp (by simpa using hm)

/-- Explicit coefficients prove that the fixed word is nontrivial in Mathlib's Coxeter group. -/
theorem w_ne_one : w ≠ 1 := by
  obtain ⟨x, y, z, hp, hx, hy, hz, _, _⟩ := explicit_coefficients
  intro h
  have heq : u * v = v * u := mul_inv_eq_one.mp h
  exact words_not_commute x z hx hz hp heq

/-- Presentation-level nonfaithfulness, with explicit algebraic coefficient hypotheses. -/
theorem bad_not_injective (x y : ℝ) (hx : x ^ 2 = x + 1)
    (hy : y ^ 2 = 3 - x) :
    ¬ Function.Injective (representation x y hx (quartic_bad x y hx hy)) := by
  intro hinj
  apply w_ne_one
  apply hinj
  rw [bad_kills_w x y hx hy, map_one]

/-- An inhabited, unconditional group-level counterexample; no faithfulness hypotheses. -/
theorem exists_nonfaithful_representation :
    ∃ (x y : ℝ) (hx : x ^ 2 = x + 1) (hy : y ^ 2 = 3 - x),
      w ≠ 1 ∧ representation x y hx (quartic_bad x y hx hy) w = 1 ∧
      ¬ Function.Injective (representation x y hx (quartic_bad x y hx hy)) := by
  obtain ⟨x, y, z, hp, hx, hy, hz, _, _⟩ := explicit_coefficients
  exact ⟨x, y, hx, hy, w_ne_one, bad_kills_w x y hx hy, bad_not_injective x y hx hy⟩

/-- The same representation with a genuine group codomain: invertible real matrices. -/
noncomputable def groupRepresentation (x t : ℝ) (hx : x ^ 2 = x + 1)
    (ht : t ^ 4 = 5 * t ^ 2 - 5) : W →* (Mat ℝ)ˣ :=
  (representation x t hx ht).toHomUnits

/-- The explicit positive golden-ratio coefficient. -/
noncomputable def golden : ℝ := (1 + Real.sqrt 5) / 2

/-- The incompatible adjacent coefficient, specified without opaque choices. -/
noncomputable def badCoefficient : ℝ := Real.sqrt (3 - golden)

/-- Direct square-root calculation for the explicit coefficient. -/
theorem golden_sq : golden ^ 2 = golden + 1 := by
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  dsimp [golden]
  nlinarith

/-- Direct square-root calculation for the incompatible coefficient. -/
theorem badCoefficient_sq : badCoefficient ^ 2 = 3 - golden := by
  apply Real.sq_sqrt
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  dsimp [golden]
  nlinarith

/-- The positive golden coefficient, needed to distinguish the comparison images. -/
theorem golden_pos : 0 < golden := by
  dsimp [golden]
  positivity

/-- The canonical comparison coefficient, again specified by an explicit square root. -/
noncomputable def goodCoefficient : ℝ := Real.sqrt (golden + 2)

/-- Direct square-root calculation for the comparison coefficient. -/
theorem goodCoefficient_sq : goodCoefficient ^ 2 = golden + 2 :=
  Real.sq_sqrt (by linarith [golden_pos])

/-- A second explicit group representation; its faithfulness is neither assumed nor needed. -/
noncomputable def goodRepresentation : W →* (Mat ℝ)ˣ :=
  groupRepresentation golden goodCoefficient golden_sq
    (quartic_good golden goodCoefficient golden_sq goodCoefficient_sq)

/-- The comparison representation separates the same two group words. -/
theorem goodRepresentation_words_not_commute :
    goodRepresentation (u * v) ≠ goodRepresentation (v * u) := by
  intro h
  have hm := congrArg (fun g : (Mat ℝ)ˣ => (g : Mat ℝ)) h
  change representation golden goodCoefficient golden_sq
    (quartic_good golden goodCoefficient golden_sq goodCoefficient_sq) (u * v) =
    representation golden goodCoefficient golden_sq
    (quartic_good golden goodCoefficient golden_sq goodCoefficient_sq) (v * u) at hm
  exact good_not_commute golden goodCoefficient golden_sq goodCoefficient_sq golden_pos
    (by simpa using hm)

/-- A fully specified group homomorphism out of the (5,10,2) Coxeter presentation. -/
noncomputable def badRepresentation : W →* (Mat ℝ)ˣ :=
  groupRepresentation golden badCoefficient golden_sq
    (quartic_bad golden badCoefficient golden_sq badCoefficient_sq)

/-- On simple generators, the group-valued representation has the advertised matrix. -/
theorem badRepresentation_simple (i : Fin 3) :
    (badRepresentation (triangle.simple i) : Mat ℝ) =
      generators golden badCoefficient i := by
  exact representation_simple golden badCoefficient golden_sq
    (quartic_bad golden badCoefficient golden_sq badCoefficient_sq) i

/-- The fixed nontrivial word belongs to the kernel of the concrete group homomorphism. -/
theorem w_mem_badRepresentation_ker : w ∈ badRepresentation.ker := by
  change badRepresentation w = 1
  apply Units.ext
  exact bad_kills_w golden badCoefficient golden_sq badCoefficient_sq

/-- Unconditional nonfaithfulness of the explicitly specified group representation.
This is not a claim about the repository's opaque `Classical.choose` representation. -/
theorem badRepresentation_not_injective : ¬ Function.Injective badRepresentation := by
  intro hinj
  apply w_ne_one
  apply hinj
  rw [map_one]
  exact w_mem_badRepresentation_ker

/-- Nontriviality of the kernel, as an equality statement about actual subgroups. -/
theorem badRepresentation_ker_ne_bot : badRepresentation.ker ≠ ⊥ := by
  intro h
  have hw := w_mem_badRepresentation_ker
  rw [h, Subgroup.mem_bot] at hw
  exact w_ne_one hw


end GeometricCounterexample
