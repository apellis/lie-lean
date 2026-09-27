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

## Main results

* A **specialization lemma** for linear independence
  (`LinearIndependent.of_comp_ratHom`): if vectors with entries in a commutative ring `R` become
  linearly independent over `ℚ` under a ring homomorphism `φ₁ : R → ℚ`, then they are linearly
  independent over any field `F` under an *injective* ring homomorphism `φ₂ : R → F`. The proof
  uses the Gram determinant `det(Mᵀ M)`, which is nonzero over `ℚ` since `ℚ` is ordered.
* `LaurentPolynomial.eval₂_injective_of_transcendental`: evaluation of `ℚ[T, T⁻¹]` at a
  transcendental element is injective.

The quantum integers and binomial coefficients with respect to a unit of a commutative ring
(`QuantumGroup.qIntU`, `QuantumGroup.qBinomialU`) are in `LieLean.Algebra.QuantumGroup.QBinomial`.

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

