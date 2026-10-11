/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2AdjointSum

/-!
# The extreme G₂ divided adjoint

The last nonzero first-root adjoint of `f^{(r)}` is `q^{3r} A^{(r)}`.
Expanding its normalized recurrence gives `qDivPow_A_eq_sum`, an integral
simple-root sandwich expression for every divided power of `A`. This supplies
an input for direct mixed-pair straightening, without a coefficient-faithfulness
hypothesis. No ordered-span multiplicative closure is asserted.

The derivation uses only the normalized relations, `q ≠ 0`, and nonvanishing
positive quantum integers at `q` and `q³`; it includes `q = ±1`.
-/

open Finset
noncomputable section
namespace LieLean.QuantumGroup.G2Integral
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]
  {q : k} {e A b C D f : B}

private def adjExpCoeff (q : k) (N n j : ℕ) : k :=
  (-1) ^ j * q ^ (((n : ℤ) - j) * ((N : ℤ) - n + 1))

private lemma adjExpCoeff_left (hq : q ≠ 0) (N n j : ℕ) :
    q ^ ((N : ℤ) - 2 * n) * adjExpCoeff q N n j =
      adjExpCoeff q N (n + 1) j * q ^ (-(j : ℤ)) := by
  simp only [adjExpCoeff, Nat.cast_add, Nat.cast_one]
  rw [mul_left_comm]
  simp only [mul_assoc, ← zpow_add₀ hq]
  congr 2
  ring

private lemma adjExpCoeff_right (hq : q ≠ 0) (N n j : ℕ) :
    -adjExpCoeff q N n j =
      adjExpCoeff q N (n + 1) (j + 1) * q ^ ((n : ℤ) - j) := by
  simp only [adjExpCoeff, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [mul_assoc, ← zpow_add₀ hq]
  have hh : ((n : ℤ) + 1 - (j + 1)) * ((N : ℤ) - (n + 1) + 1) + (n - j) =
      ((n : ℤ) - j) * ((N : ℤ) - n + 1) := by ring
  rw [hh]
  ring

private theorem adjointExpansion (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0) (N : ℕ) (x : B) (W : ℕ → B)
    (hW : ∀ n, qInt q (n + 1) • W (n + 1) =
      q ^ ((N : ℤ) - 2 * n) • (x * W n) - W n * x) (n : ℕ) :
    W n = ∑ j ∈ range (n + 1), adjExpCoeff q N n j •
      (qDivPow q (n - j) x * W 0 * qDivPow q j x) := by
  induction n with
  | zero => simp only [Nat.zero_add, sum_range_one, adjExpCoeff, pow_zero,
      Nat.cast_zero, Nat.sub_self, sub_self, zero_mul, zpow_zero, one_mul, qDivPow_zero', mul_one,
      one_smul]
  | succ n ih =>
    let X : ℕ → B := fun j => qDivPow q (n + 1 - j) x * W 0 * qDivPow q j x
    let L : ℕ → B := fun j =>
      (adjExpCoeff q N (n + 1) j * q ^ (-(j : ℤ)) * qInt q (n + 1 - j)) • X j
    let R : ℕ → B := fun j =>
      (adjExpCoeff q N (n + 1) (j + 1) * q ^ ((n : ℤ) - j) * qInt q (j + 1)) • X (j + 1)
    have hL (j : ℕ) (hj : j ∈ range (n + 1)) :
        q ^ ((N : ℤ) - 2 * n) • (x * (adjExpCoeff q N n j •
          (qDivPow q (n - j) x * W 0 * qDivPow q j x))) = L j := by
      have hnj : n - j + 1 = n + 1 - j := by have := mem_range.mp hj; omega
      simp only [L, X, mul_smul_comm, ← mul_assoc,
        mul_qDivPow q x (n - j) (hqi _ (by omega)), smul_mul_assoc, smul_smul]
      rw [adjExpCoeff_left hq, hnj]
    have hR (j : ℕ) (_hj : j ∈ range (n + 1)) :
        -((adjExpCoeff q N n j •
          (qDivPow q (n - j) x * W 0 * qDivPow q j x)) * x) = R j := by
      have hnj : n + 1 - (j + 1) = n - j := by omega
      simp only [R, X, smul_mul_assoc, mul_assoc,
        A2Integral.qDivPow_mul_self x j (hqi _ (by omega)), mul_smul_comm,
        smul_smul, ← neg_smul, hnj]
      rw [← neg_mul, adjExpCoeff_right hq, mul_assoc]
    refine smul_right_injective B (hqi (n + 1) (by omega)) ?_
    simp only
    rw [hW, ih]
    simp only [mul_sum, sum_mul, smul_sum]
    rw [sub_eq_add_neg, ← sum_neg_distrib]
    rw [sum_congr rfl hL, sum_congr rfl hR]
    change (∑ j ∈ range (n + 1), L j) + (∑ j ∈ range (n + 1), R j) =
      ∑ j ∈ range (n + 1 + 1), qInt q (n + 1) •
        (adjExpCoeff q N (n + 1) j • X j)
    rw [sum_range_succ' L n, sum_range_succ R n,
      sum_range_succ' _ (n + 1), sum_range_succ _ n]
    have hmid (j : ℕ) (hj : j ∈ range n) :
        L (j + 1) + R j = qInt q (n + 1) • (adjExpCoeff q N (n + 1) (j + 1) • X (j + 1)) := by
      have hjn : j < n := mem_range.mp hj
      have hn : n + 1 - (j + 1) + (j + 1) = n + 1 := by omega
      have hz : ((n : ℤ) - j) = (n + 1 - (j + 1) : ℕ) := by omega
      simp only [L, R, smul_smul, ← add_smul]
      congr 1
      rw [hz, zpow_natCast, zpow_neg, zpow_natCast]
      have hh := B2Integral.qInt_add (t := q) (n + 1 - (j + 1)) (j + 1)
      rw [hn] at hh
      linear_combination adjExpCoeff q N (n + 1) (j + 1) * hh
    have hfirst : L 0 = qInt q (n + 1) • (adjExpCoeff q N (n + 1) 0 • X 0) := by
      simp only [L, Nat.cast_zero, neg_zero, zpow_zero, mul_one, Nat.sub_zero, smul_smul]
      rw [mul_comm]
    have hlast : R n = qInt q (n + 1) •
        (adjExpCoeff q N (n + 1) (n + 1) • X (n + 1)) := by
      simp only [R, sub_self, zpow_zero, mul_one, smul_smul]
      rw [mul_comm]
    have hs := sum_congr rfl hmid
    rw [sum_add_distrib] at hs
    rw [hfirst, hlast, ← hs]
    abel

/-- Only the first long root occurs at the extreme adjoint weight. -/
lemma adjointIndices_extreme (s : ℕ) : adjointIndices (3 * s) s = {(s, 0, 0, 0, 0)} := by
  ext ⟨a, b, c, d, l⟩
  simp only [mem_adjointIndices, mem_singleton, Prod.mk.injEq]
  omega

/-- Evaluation of the extreme finite adjoint sum. -/
lemma adjointSum_extreme (q : k) (A b C D f : B) (s : ℕ) :
    adjointSum q A b C D f (3 * s) s = q ^ (3 * s) • qDivPow (q ^ 3) s A := by
  simp only [adjointSum, adjointIndices_extreme, sum_singleton, adjointCoeff,
    adjointExponent, Nat.mul_zero, Nat.add_zero, Nat.zero_add, pow_zero, one_mul, M5, P3,
    qDivPow_zero', mul_one]

/-- The extreme divided adjoint writes every `A` divided power as an integral
linear combination of simple-root sandwiches. The proof uses only the normalized relations. -/
theorem qDivPow_A_eq_sum (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) (r : ℕ) :
    qDivPow (q ^ 3) r A = ∑ j ∈ range (3 * r + 1),
      ((-1 : k) ^ j * q⁻¹ ^ j) •
        (qDivPow q (3 * r - j) e * qDivPow (q ^ 3) r f * qDivPow q j e) := by
  have hlead (n : ℕ) : q ^ (((3 * r : ℕ) : ℤ) - 2 * n) =
      q ^ (3 * r) * q⁻¹ ^ (2 * n) := by
    simp only [← zpow_natCast q, ← zpow_natCast q⁻¹, inv_zpow,
      ← zpow_neg, ← zpow_add₀ hq]
    congr 1
  have hW (n : ℕ) : qInt q (n + 1) • adjointSum q A b C D f (n + 1) r =
      q ^ (((3 * r : ℕ) : ℤ) - 2 * n) • (e * adjointSum q A b C D f n r) -
        adjointSum q A b C D f n r * e := by
    rw [hlead]
    have hh := adjointSum_e_all hq hqi hpi H n r
    rw [hh]
    abel
  have hh := adjointExpansion hq hqi (3 * r) e
    (fun n => adjointSum q A b C D f n r) hW (3 * r)
  rw [adjointSum_extreme, adjointSum_zero] at hh
  refine smul_right_injective B (pow_ne_zero (3 * r) hq) ?_
  simp only
  rw [hh, smul_sum]
  apply sum_congr rfl
  intro j _
  rw [smul_smul]
  congr 1
  simp only [adjExpCoeff, sub_self, zero_add, mul_one,
    ← zpow_natCast q, ← zpow_natCast q⁻¹, inv_zpow, ← zpow_neg]
  rw [mul_left_comm]
  simp only [← zpow_add₀ hq, sub_eq_add_neg]

end LieLean.QuantumGroup.G2Integral
