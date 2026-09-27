/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Algebraic.Basic
import LieLean.Algebra.QuantumGroup.QBinomial

/-!
# Specialization tools for the quantum Gabber–Kac theorem

The proof of the quantum Gabber–Kac theorem (`LieLean.Algebra.QuantumGroup.GabberKac`) compares
Lusztig's algebra over a field `k ∋ v` with its classical limit `v = 1` over `ℚ`, through the ring
`ℚ[T, T⁻¹]` of Laurent polynomials, which maps to `k` (`T ↦ v`) and to `ℚ` (`T ↦ 1`). This file
contains the generic ingredients.

* A **specialization lemma** for linear independence
  (`LinearIndependent.of_comp_ratHom`): if vectors with entries in a commutative ring `R` become
  linearly independent over `ℚ` under a ring homomorphism `φ₁ : R → ℚ`, then they are linearly
  independent over any field `F` under an *injective* ring homomorphism `φ₂ : R → F`. The proof
  uses the Gram determinant `det(Mᵀ M)`, which is nonzero over `ℚ` since `ℚ` is ordered.
* `LaurentPolynomial.eval₂_injective_of_transcendental`: evaluation of `ℚ[T, T⁻¹]` at a
  transcendental element is injective.
* Quantum integers, binomial coefficients and Serre elements with respect to a unit `q` of a
  commutative ring (`QuantumGroup.qIntU`, `QuantumGroup.qBinomialU`, `QuantumGroup.qSerreU`), and
  their images under ring homomorphisms to fields (`QuantumGroup.map_qBinomialU`, …).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §1.3.
-/

noncomputable section

open Finset Matrix

/-! ### The specialization lemma -/

private lemma mulVec_map_of_eq {R K ι n : Type*} [CommRing R] [Field K] [Fintype ι]
    (φ : R →+* K) (p : ι → n → R) (c : ι → K) :
    ((Matrix.of fun x a ↦ p a x).map φ) *ᵥ c = ∑ a, c a • (φ ∘ p a) := by
  ext x
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- **Specialization of linear independence.** Let `p a` (`a ∈ ι`) be vectors in `Rⁿ` for a
commutative ring `R`, and let `φ₁ : R → ℚ`, `φ₂ : R → F` be ring homomorphisms, `F` a field and
`φ₂` injective. If the vectors `φ₁ ∘ p a` are linearly independent over `ℚ`, then the vectors
`φ₂ ∘ p a` are linearly independent over `F`. (The Gram determinant `det(Mᵀ M) ∈ R` of the matrix
of the `p a` is nonzero after `φ₁`, hence nonzero, hence nonzero after `φ₂`.) -/
theorem LinearIndependent.of_comp_ratHom {R F ι n : Type*} [CommRing R] [Field F] [Finite ι]
    [Finite n] (φ₁ : R →+* ℚ) (φ₂ : R →+* F) (hφ₂ : Function.Injective φ₂)
    (p : ι → n → R) (h : LinearIndependent ℚ fun a ↦ φ₁ ∘ p a) :
    LinearIndependent F fun a ↦ φ₂ ∘ p a := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite n
  set M : Matrix n ι R := Matrix.of fun x a ↦ p a x
  -- the Gram determinant is nonzero over `ℚ`
  have h₁ : ((M.map φ₁)ᵀ * M.map φ₁).det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hMc : M.map φ₁ *ᵥ c = 0 := by
      have : (M.map φ₁ *ᵥ c) ⬝ᵥ (M.map φ₁ *ᵥ c) = 0 := by
        have e : (M.map φ₁ *ᵥ c) ⬝ᵥ (M.map φ₁ *ᵥ c) =
            c ⬝ᵥ (((M.map φ₁)ᵀ * M.map φ₁) *ᵥ c) := by
          rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec c, Matrix.vecMul_transpose]
        rw [e, hc0, dotProduct_zero]
      exact dotProduct_self_eq_zero.1 this
    rw [mulVec_map_of_eq] at hMc
    exact hc (funext (Fintype.linearIndependent_iff.1 h c hMc))
  have hR : (Mᵀ * M).det ≠ 0 := by
    intro h0
    apply h₁
    have := RingHom.map_det φ₁ (Mᵀ * M)
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map, h0, map_zero] at this
    exact this.symm
  have h₂ : ((M.map φ₂)ᵀ * M.map φ₂).det ≠ 0 := by
    have := RingHom.map_det φ₂ (Mᵀ * M)
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at this
    rw [← this]
    exact fun h0 ↦ hR (hφ₂ (h0.trans (map_zero φ₂).symm))
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨a, ha⟩ := hne
  apply h₂
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, fun h0 ↦ ha (by simp [h0]), ?_⟩
  rw [← Matrix.mulVec_mulVec, mulVec_map_of_eq, hc, Matrix.mulVec_zero]

/-! ### Evaluation of Laurent polynomials at a transcendental element -/

/-- Evaluation of `ℚ[T, T⁻¹]` at a transcendental element `v` of a field `k` is injective. -/
theorem LaurentPolynomial.eval₂_injective_of_transcendental {k : Type*} [Field k] [CharZero k]
    {v : k} (hv : Transcendental ℚ v) (hv0 : v ≠ 0) :
    Function.Injective (LaurentPolynomial.eval₂ (algebraMap ℚ k) (Units.mk0 v hv0)) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  obtain ⟨n, f', hf'⟩ := LaurentPolynomial.exists_T_pow f
  have h1 : LaurentPolynomial.eval₂ (algebraMap ℚ k) (Units.mk0 v hv0) (Polynomial.toLaurent f')
      = 0 := by
    rw [hf', map_mul, hf, zero_mul]
  rw [LaurentPolynomial.eval₂_toLaurent] at h1
  have h2 : f' = 0 := (transcendental_iff.1 hv) f' (by rwa [Polynomial.aeval_def])
  have h3 : f * LaurentPolynomial.T n = 0 := by rw [← hf', h2, map_zero]
  have hu : IsUnit (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial ℚ) :=
    LaurentPolynomial.isUnit_T _
  exact (hu.mul_left_eq_zero).1 h3

namespace QuantumGroup

/-! ### Quantum integers and binomial coefficients with respect to a unit -/

variable {R : Type*} [CommRing R] (q : Rˣ)

/-- The quantum integer `[n]_q = Σ_{s < n} q^{n-1-2s}` for a unit `q` of a commutative ring. -/
def qNatU (n : ℕ) : R := ∑ s ∈ range n, ((q ^ (n - 1 - s) * q⁻¹ ^ s : Rˣ) : R)

/-- The quantum integer `[n]_q` for `n ∈ ℤ`, with `[-n]_q = -[n]_q`. -/
def qIntU : ℤ → R
  | .ofNat n => qNatU q n
  | .negSucc n => -qNatU q (n + 1)

/-- The quantum binomial coefficient `[n j]_q` for a unit `q` of a commutative ring, by the Pascal
rule of `QuantumGroup.qBinomial`. -/
def qBinomialU : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, j + 1 => ((q⁻¹ ^ (j + 1) : Rˣ) : R) * qBinomialU n (j + 1) +
      ((q ^ (n - j) : Rˣ) : R) * qBinomialU n j

variable {B : Type*} [Ring B] [Algebra R B]

/-- The quantum Serre element `Σ_{r=0}^{m} (-1)^r [m r]_q a^{m-r} b a^r` for a unit `q`. -/
def qSerreU (m : ℕ) (a b : B) : B :=
  ∑ r ∈ range (m + 1), ((-1) ^ r * qBinomialU q m r) • (a ^ (m - r) * b * a ^ r)

variable {k : Type*} [Field k] (φ : R →+* k)

lemma map_units_inv' : φ ((q⁻¹ : Rˣ) : R) = (φ q)⁻¹ := by
  refine (eq_inv_of_mul_eq_one_right ?_)
  rw [← map_mul, Units.mul_inv, map_one]

lemma map_units_val_pow_inv (a b : ℕ) :
    φ ((q ^ a * q⁻¹ ^ b : Rˣ) : R) = φ q ^ a * (φ q)⁻¹ ^ b := by
  rw [Units.val_mul, map_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    map_pow, map_units_inv']

lemma map_qNatU (n : ℕ) : φ (qNatU q n) = qInt (φ q) n := by
  simp only [qNatU, map_sum, map_units_val_pow_inv, qInt]

lemma map_qBinomialU (n j : ℕ) : φ (qBinomialU q n j) = qBinomial (φ q) n j := by
  induction n generalizing j with
  | zero => cases j <;> simp [qBinomialU, qBinomial]
  | succ n ih =>
    cases j with
    | zero => simp [qBinomialU]
    | succ j =>
      rw [qBinomialU, qBinomial_succ_succ, map_add, map_mul, map_mul, ih, ih,
        Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow, map_units_inv']

/-- `(q - q⁻¹) [n]_q = qⁿ - q⁻ⁿ` after mapping to a field, for `n ∈ ℤ`. -/
lemma sub_mul_map_qIntU (n : ℤ) :
    (φ q - (φ q)⁻¹) * φ (qIntU q n) = φ q ^ n - φ q ^ (-n) := by
  cases n with
  | ofNat n =>
    rw [qIntU, map_qNatU, qInt_mul_sub]
    simp [zpow_neg]
  | negSucc n =>
    rw [qIntU, map_neg, map_qNatU, mul_neg, qInt_mul_sub, Int.neg_negSucc, zpow_natCast,
      zpow_negSucc, inv_pow]
    ring

/-- At `q ↦ 1` the quantum integer `[n]_q` becomes `n`. -/
lemma map_qIntU_of_eq_one (hφ : φ q = 1) (n : ℤ) : φ (qIntU q n) = n := by
  cases n with
  | ofNat n => simp [qIntU, map_qNatU, hφ, qInt]
  | negSucc n =>
    rw [qIntU, map_neg, map_qNatU, hφ]
    simp [qInt, Int.negSucc_eq]

end QuantumGroup
