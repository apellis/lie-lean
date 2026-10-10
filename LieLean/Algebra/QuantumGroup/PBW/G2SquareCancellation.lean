/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic

/-!
# Coefficient cancellation for filtered polynomial operators

The reconstructed cancellation argument for the G₂ square kernel uses blocks which,
modulo a cyclotomic polynomial, increase the polynomial degree filtration by the block
width. The main result `coeff_dvd_pow_of_blocks` proves the resulting power divisibility
without any commutativity hypothesis on the blocks or their error operators.

This file does not yet identify these blocks with the G₂ Newton operator or prove
integrality of `G2Integral.squareCoeff`.
-/

open Finset Polynomial

noncomputable section

namespace LieLean.QuantumGroup.G2Integral.SquareCancellation

variable {R : Type*} [CommRing R]

/-- A block preserves the degree filtration and raises it by `d` modulo `π`.
Only matrix coefficients on monomials are needed. -/
structure Block (π : R) (d : ℕ) where
  /-- The underlying coefficient-linear operator. -/
  toLinearMap : R[X] →ₗ[R] R[X]
  /-- The operator never lowers degree. -/
  triangular : ∀ j n, n < j → (toLinearMap (X ^ j)).coeff n = 0
  /-- Modulo `π`, the operator raises degree by at least `d`. -/
  raises : ∀ j n, n < j + d → π ∣ (toLinearMap (X ^ j)).coeff n

/-- The coefficientwise divisibility filtration for a sequence of blocks. -/
def Filtered (π : R) (d r : ℕ) (F : R[X]) : Prop :=
  ∀ n, π ^ (r - n / d) ∣ F.coeff n

lemma filtered_zero (π : R) (d : ℕ) (F : R[X]) : Filtered π d 0 F := by
  intro n
  simp

/-- One block gains one power of `π`, except when crossing a block-width boundary. -/
theorem Block.filtered {π : R} {d r : ℕ} (T : Block π d) (hd : 0 < d)
    {F : R[X]} (hF : Filtered π d r F) : Filtered π d (r + 1) (T.toLinearMap F) := by
  intro n
  conv_rhs => rw [F.as_sum_range_C_mul_X_pow]
  simp only [← smul_eq_C_mul, map_sum, map_smul, finsetSum_coeff, coeff_smul,
    smul_eq_mul]
  apply Finset.dvd_sum
  intro j _
  by_cases hj : n < j
  · rw [T.triangular j n hj, mul_zero]
    exact dvd_zero _
  · have hjn : j / d ≤ n / d := Nat.div_le_div_right (by omega : j ≤ n)
    by_cases he : j / d = n / d
    · have hlt : n < j + d := by
        have hn := Nat.mod_lt n hd
        have hj' := Nat.mod_add_div j d
        have hn' := Nat.mod_add_div n d
        rw [← he] at hn'
        omega
      have hm := mul_dvd_mul (hF j) (T.raises j n hlt)
      rw [← pow_succ] at hm
      exact (pow_dvd_pow π (by omega : r + 1 - n / d ≤ r - j / d + 1)).trans hm
    · exact dvd_mul_of_dvd_left
        ((pow_dvd_pow π (by omega : r + 1 - n / d ≤ r - j / d)).trans (hF j)) _

/-- Apply an ordered sequence of blocks. No pairwise commutation is imposed. -/
def applyBlocks {π : R} {d : ℕ} (T : ℕ → Block π d) (F : R[X]) : ℕ → R[X]
  | 0 => F
  | r + 1 => (T r).toLinearMap (applyBlocks T F r)

/-- Arbitrary-index power cancellation for filtered blocks, proved coefficientwise.
In the G₂ application `R = ℤ[x]`, `π = Φ_(3h)` and `d = 3h`. -/
theorem coeff_dvd_pow_of_blocks {π : R} {d : ℕ} (T : ℕ → Block π d)
    (hd : 0 < d) (F : R[X]) (r n : ℕ) :
    π ^ (r - n / d) ∣ (applyBlocks T F r).coeff n := by
  have hf : Filtered π d r (applyBlocks T F r) := by
    induction r with
    | zero => exact filtered_zero π d F
    | succ r ih => exact (T r).filtered hd ih
  exact hf n

/-- The floor inequality needed to compare the G₂ cyclotomic exponents.
It includes `a = b = n = 0`. -/
theorem square_floor_comparison (a b n h : ℕ) (hh : 0 < h)
    (hw : 3 * a + b = 2 * n) :
    n / (3 * h) ≤ a / h + b / (3 * h) := by
  have ha := Nat.mod_lt a hh
  have hb := Nat.mod_lt b (by omega : 0 < 3 * h)
  have ea := Nat.mod_add_div a h
  have eb := Nat.mod_add_div b (3 * h)
  have en := Nat.mod_add_div n (3 * h)
  by_contra hn
  have hc : a / h + b / (3 * h) + 1 ≤ n / (3 * h) := by omega
  have hm := Nat.mul_le_mul_left (3 * h) hc
  have hz : 0 ≤ h * (a / h) + h * (b / (3 * h)) := Nat.zero_le _
  nlinarith only [hw, ha, hb, ea, eb, en, hm, hz,
    Nat.zero_le (n % (3 * h))]

/-- The block valuation dominates the possible denominator deficit. -/
theorem square_deficit_le (a b n t h : ℕ) (hh : 0 < h)
    (hw : 3 * a + b = 2 * n) :
    t / h - a / h - b / (3 * h) ≤ t / h - n / (3 * h) := by
  have := square_floor_comparison a b n h hh hw
  omega

end LieLean.QuantumGroup.G2Integral.SquareCancellation
