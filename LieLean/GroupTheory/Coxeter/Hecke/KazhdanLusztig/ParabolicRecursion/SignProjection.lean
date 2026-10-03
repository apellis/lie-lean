/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.ParabolicRecursion.Mu
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.ParabolicRelations
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.Inverse

/-!
# Sign projection and parabolic μ-coefficients

## Main results

* `IwahoriHeckeAlgebra.mk_klBasis_eq_zero_sgn_of_not_mem_minCosetReps`: nonminimal
  ordinary Kazhdan–Lusztig elements vanish in the sign quotient.
* `IwahoriHeckeAlgebra.parabolicKLMu_sgn`: sign parabolic and ordinary μ-coefficients agree.

## References

The proofs are reconstructed from the right-descent eigenvalue relation and the alternating
sum `parabolicKLPoly_sgn`. No finiteness is assumed.
-/

open LaurentPolynomial Polynomial CoxeterSystem

namespace IwahoriHeckeAlgebra

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {J : Set B}

local prefix:100 "ℓ " => cs.length

/-- The right-descent eigenvalue relation, reconstructed by applying the anti-involution
 to the left-descent relation `T_simple_mul_klBasis`. -/
theorem klBasis_mul_T_simple {w : W} {i : B}
    (hw : ℓ (w * cs.simple i) < ℓ w) :
    klBasis cs w * T cs (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) (cs.simple i) =
      (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) • klBasis cs w := by
  have hi : ℓ (cs.simple i * w⁻¹) < ℓ w⁻¹ := by
    rwa [← cs.inv_simple i, ← mul_inv_rev, cs.length_inv, cs.length_inv]
  have h := congrArg (antiInvolutionSelf cs _) (T_simple_mul_klBasis cs hi)
  simpa only [antiInvolutionSelf_mul, antiInvolutionSelf_T, antiInvolutionSelf_klBasis,
    cs.inv_simple, inv_inv, map_smul] using h

/-- A nonminimal ordinary KL element vanishes in the sign quotient. Reconstructed from
its right-descent eigenvalue and the torsion-free standard coordinates of the quotient. -/
theorem mk_klBasis_eq_zero_sgn_of_not_mem_minCosetReps {w : W}
    (hw : w ∉ cs.minCosetReps J) :
    (Submodule.Quotient.mk (klBasis cs w) :
      InducedModule (sgn (cs.parabolicCoxeterSystem J) (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]))) =
      0 := by
  classical
  obtain ⟨i, hi, hdesc⟩ : ∃ i ∈ J, cs.IsRightDescent w i := by
    simpa only [minCosetReps, Set.mem_ofPred_eq, not_forall, not_not, exists_prop] using hw
  let χ := sgn (cs.parabolicCoxeterSystem J) (LaurentPolynomial.T 2 : ℤ[T;T⁻¹])
  apply (inducedModuleEquiv χ).injective
  rw [inducedModuleEquiv_mk, map_zero]
  have h := inducedCoeff_mul_parabolicHom χ (klBasis cs w)
    (T (cs.parabolicCoxeterSystem J) _ ((cs.parabolicCoxeterSystem J).simple ⟨i, hi⟩))
  rw [parabolicHom_T, coe_parabolicCoxeterSystem_simple,
    klBasis_mul_T_simple cs hdesc, map_smul, sgn_T_simple] at h
  apply Finsupp.ext
  intro d
  have hd := congrArg (fun f => f d) h
  simp only [Finsupp.smul_apply, smul_eq_mul, neg_one_mul] at hd
  have hzero : (LaurentPolynomial.T 2 + 1 : ℤ[T;T⁻¹]) * inducedCoeff χ (klBasis cs w) d = 0 := by
    rw [add_mul, one_mul, hd, neg_add_cancel]
  have hne : (LaurentPolynomial.T 2 + 1 : ℤ[T;T⁻¹]) ≠ 0 := by
    intro he
    have he' := congrArg (fun p : ℤ[T;T⁻¹] => p.coeff 2) he
    have hone : (1 : ℤ[T;T⁻¹]).coeff 2 = 0 := by
      change (LaurentPolynomial.T 0 : ℤ[T;T⁻¹]).coeff 2 = 0
      rw [T_apply]
      norm_num
    norm_num [AddMonoidAlgebra.coeff_add, hone] at he'
  exact (mul_eq_zero.mp hzero).resolve_left hne

/-- Sign parabolic μ-coefficients agree with ordinary ones for minimal representatives.
Reconstructed from `parabolicKLPoly_sgn`: every nonidentity parabolic summand has too small
a degree to contribute to the selected top coefficient. -/
theorem parabolicKLMu_sgn (x w : cs.minCosetReps J) :
    parabolicKLMu (isBarCompatible_sgn (cs.parabolicCoxeterSystem J)) x w =
      klMu cs x w := by
  classical
  by_cases hle : cs.BruhatLE x w
  · by_cases hodd : Odd (ℓ w - ℓ x)
    · have hlen := hle.length_le
      have hpar := Nat.odd_iff.mp hodd
      rw [parabolicKLMu, klMu, muCoeff, muCoeff, ite_eq_left hodd, ite_eq_left hodd,
        parabolicKLPoly_sgn, finsetSum_coeff]
      rw [Finset.sum_eq_single_of_mem (x : W)]
      · rw [parabolicComponent_of_mem x.2, cs.length_one, pow_zero, one_mul]
      · simp [minCosetRep_of_mem x.2, hle]
      · intro y hy hyx
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hy
        have hyw : y ≠ w := by
          intro he
          have he' : (x : W) = w := by
            simpa only [he, minCosetRep_of_mem w.2] using hy.2.symm
          have : ℓ x = ℓ w := congrArg cs.length he'
          omega
        have hl := length_eq_length_minCosetRep_add (cs := cs) (J := J) y
        rw [hy.2] at hl
        have hp : ℓ (cs.parabolicComponent J y) ≠ 0 := by
          intro hp
          have he := minCosetRep_mul_parabolicComponent (cs := cs) (J := J) y
          rw [hy.2, cs.length_eq_zero_iff.mp hp, mul_one] at he
          exact hyx he.symm
        rw [show ((-1 : ℤ[X]) ^ ℓ (cs.parabolicComponent J y)) =
          Polynomial.C ((-1) ^ ℓ (cs.parabolicComponent J y)) by simp,
          coeff_C_mul, coeff_klPoly_eq_zero cs hyw (by omega), mul_zero]
    · simp [parabolicKLMu, klMu, muCoeff, hodd]
  · rw [parabolicKLMu_eq_zero_of_not_bruhatLE _ hle,
      klMu_eq_zero_of_not_bruhatLE cs hle]

end IwahoriHeckeAlgebra
