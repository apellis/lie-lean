/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Finite-support Euler identities for arbitrary variable types

## Main results

The pinned Mathlib Euler identities require `Fintype σ`. Here the sum ranges over any finite
set containing the variables of the polynomial, with no finiteness assumption on `σ`.
The weighted identity also allows an additional exterior-degree contribution.

## References

Reconstructed directly from Mathlib's monomial derivative and homogeneous support APIs;
no external reference was consulted.
-/

open scoped BigOperators

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R]

/-- Finite-support weighted Euler identity for a monomial, with extra zero coordinates allowed. -/
theorem sum_weight_X_mul_pderiv_monomial_of_support_subset
    (w : σ → ℕ) (s : Finset σ) (m : σ →₀ ℕ) (r : R) (hs : m.support ⊆ s) :
    (∑ i ∈ s, w i • (X i * pderiv i (monomial m r))) =
      Finsupp.weight w m • monomial m r := by
  classical
  simp only [X_mul_pderiv_monomial, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Finsupp.weight_apply, Finsupp.sum]
  simp only [smul_eq_mul]
  rw [Finset.sum_subset hs]
  · apply Finset.sum_congr rfl
    intro i _
    exact Nat.mul_comm _ _
  · intro i _ hi
    simp [Finsupp.notMem_support_iff.mp hi]

/-- Weighted Euler identity on a finite set containing all occurring variables, for arbitrary
variable types. This removes the `Fintype` restriction in the pinned Mathlib theorem. -/
theorem IsWeightedHomogeneous.sum_weight_X_mul_pderiv_of_vars_subset
    {p : MvPolynomial σ R} {w : σ → ℕ} {n : ℕ}
    (hp : p.IsWeightedHomogeneous w n) (s : Finset σ) (hs : p.vars ⊆ s) :
    (∑ i ∈ s, w i • (X i * pderiv i p)) = n • p := by
  classical
  calc
    _ = ∑ i ∈ s, w i •
        (X i * pderiv i (∑ m ∈ p.support, monomial m (p.coeff m))) := by
      rw [support_sum_monomial_coeff]
    _ = ∑ m ∈ p.support, ∑ i ∈ s,
        w i • (X i * pderiv i (monomial m (p.coeff m))) := by
      simp only [map_sum, Finset.mul_sum, Finset.smul_sum]
      rw [Finset.sum_comm]
    _ = ∑ m ∈ p.support, n • monomial m (p.coeff m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [sum_weight_X_mul_pderiv_monomial_of_support_subset w s m (p.coeff m)
        ((support_subset_vars_of_mem_support hm).trans hs)]
      rw [hp (mem_support_iff.mp hm)]
    _ = n • p := by rw [← Finset.smul_sum, support_sum_monomial_coeff]

/-- Euler identity for arbitrary-variable homogeneous polynomials, over any commutative semiring. -/
theorem IsHomogeneous.sum_X_mul_pderiv_of_vars_subset
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (s : Finset σ) (hs : p.vars ⊆ s) :
    (∑ i ∈ s, X i * pderiv i p) = n • p := by
  simpa only [Pi.one_apply, one_smul] using
    hp.sum_weight_X_mul_pderiv_of_vars_subset s hs

/-- The diagonal scalar needed after adding the exterior-degree contribution in a weighted
Koszul calculation. This is only the Euler scalar identity, not a construction of a homotopy. -/
theorem IsWeightedHomogeneous.sum_weight_X_mul_pderiv_add_exteriorDegree
    {p : MvPolynomial σ R} {w : σ → ℕ} {n : ℕ}
    (hp : p.IsWeightedHomogeneous w n) (s : Finset σ) (hs : p.vars ⊆ s) (q : ℕ) :
    (∑ i ∈ s, w i • (X i * pderiv i p)) + q • p = (n + q) • p := by
  rw [hp.sum_weight_X_mul_pderiv_of_vars_subset s hs, add_smul]

/-- In characteristic zero, the positive polynomial-plus-exterior degree scalar can be inverted.
This supplies the normalization factor for a Koszul contraction, without asserting its existence. -/
theorem IsWeightedHomogeneous.inv_degree_smul_euler_add_exteriorDegree
    {K : Type*} [Field K] [CharZero K] {p : MvPolynomial σ K} {w : σ → ℕ} {n : ℕ}
    (hp : p.IsWeightedHomogeneous w n) (s : Finset σ) (hs : p.vars ⊆ s)
    (q : ℕ) (hpos : 0 < n + q) :
    ((n + q : ℕ) : K)⁻¹ • ((∑ i ∈ s, w i • (X i * pderiv i p)) + q • p) = p := by
  rw [hp.sum_weight_X_mul_pderiv_add_exteriorDegree s hs q,
    ← Nat.cast_smul_eq_nsmul K, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos)), one_smul]

end MvPolynomial
