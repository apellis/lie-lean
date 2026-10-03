/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.Parabolic

/-!
# Parabolic Kazhdan–Lusztig μ-coefficients

## Main definitions

* `IwahoriHeckeAlgebra.parabolicKLMu`: the top coefficient selected by an odd length difference.

## Main results

* `IwahoriHeckeAlgebra.parabolicKLMu_eq_coeff_neg_one`: the coefficient of `v⁻¹` in the
  normalized-basis coordinate of a parabolic Kazhdan–Lusztig element.
* `IwahoriHeckeAlgebra.parabolicKLMu_eq_coeff_of_odd`: the explicit polynomial coefficient.
* `IwahoriHeckeAlgebra.parabolicKLMu_eq_zero_of_not_bruhatLE` and
  `IwahoriHeckeAlgebra.parabolicKLMu_self`: support and diagonal vanishing.

## References

These statements and proofs are reconstructed from the polynomial normalization in
`KazhdanLusztig.Parabolic` and the definition `muCoeff`.
No finiteness hypothesis on the Coxeter group or its parabolic subgroup is needed.
-/

open LaurentPolynomial Polynomial

namespace IwahoriHeckeAlgebra

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} {cs : CoxeterSystem M W}
variable {J : Set B} {χ : IwahoriHeckeAlgebra (cs.parabolicCoxeterSystem J)
  (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) →ₐ[ℤ[T;T⁻¹]] ℤ[T;T⁻¹]}
variable (hχ : IsBarCompatible (cs.parabolicCoxeterSystem J) χ)

local prefix:100 "ℓ " => cs.length

/-- The parabolic μ-coefficient, using the ordinary `muCoeff` convention.
Reconstructed from the definition of the parabolic Kazhdan–Lusztig polynomials. -/
noncomputable def parabolicKLMu (x w : cs.minCosetReps J) : ℤ :=
  muCoeff (parabolicKLPoly hχ x w) (ℓ w - ℓ x)

/-- The explicit odd-length coefficient formula, reconstructed from `muCoeff`. -/
theorem parabolicKLMu_eq_coeff_of_odd (x w : cs.minCosetReps J)
    (hodd : Odd (ℓ w - ℓ x)) :
    parabolicKLMu hχ x w = (parabolicKLPoly hχ x w).coeff ((ℓ w - ℓ x - 1) / 2) := by
  rw [parabolicKLMu, muCoeff, ite_eq_left hodd]
  congr 1
  have := Nat.odd_iff.mp hodd
  omega

/-- An even length difference gives zero, reconstructed from `muCoeff`. -/
theorem parabolicKLMu_eq_zero_of_not_odd (x w : cs.minCosetReps J)
    (hodd : ¬Odd (ℓ w - ℓ x)) : parabolicKLMu hχ x w = 0 := by
  simp [parabolicKLMu, muCoeff, hodd]

/-- The parabolic μ-coefficient is the coefficient of `v⁻¹` in the normalized-basis
coordinate. Reconstructed from `coeff_parabolicKLPoly` and `repr_parabolicKLBasis`. -/
theorem parabolicKLMu_eq_coeff_neg_one (x w : cs.minCosetReps J) :
    parabolicKLMu hχ x w =
      ((normalizedBasis cs χ).repr (parabolicKLBasis hχ w) x).coeff (-1) := by
  by_cases hodd : Odd (ℓ w - ℓ x)
  · rw [parabolicKLMu, muCoeff, ite_eq_left hodd, coeff_parabolicKLPoly,
      normalizedBasis_repr_apply, coeff_T_mul]
    congr 1
    have := Nat.odd_iff.mp hodd
    omega
  · rw [parabolicKLMu, muCoeff, ite_eq_right hodd, normalizedBasis_repr_apply,
      repr_parabolicKLBasis, ← mul_assoc, ← T_add]
    symm
    apply coeff_T_mul_aeval_T_two_eq_zero
    intro k hk
    exfalso
    apply hodd
    apply Nat.odd_iff.mpr
    omega

/-- The μ-coefficient vanishes outside Bruhat support, reconstructed from polynomial support. -/
theorem parabolicKLMu_eq_zero_of_not_bruhatLE {x w : cs.minCosetReps J}
    (h : ¬cs.BruhatLE x w) : parabolicKLMu hχ x w = 0 := by
  simp [parabolicKLMu, muCoeff, parabolicKLPoly_eq_zero_of_not_bruhatLE hχ h]

/-- The diagonal μ-coefficient vanishes, reconstructed from the even length difference. -/
@[simp]
theorem parabolicKLMu_self (w : cs.minCosetReps J) : parabolicKLMu hχ w w = 0 := by
  simp [parabolicKLMu, muCoeff]

end IwahoriHeckeAlgebra
