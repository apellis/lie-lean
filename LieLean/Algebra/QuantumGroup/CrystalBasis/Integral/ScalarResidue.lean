/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Integral.Intersection

/-! Integer residues for the actual Laurent embedding and infinity local ring. -/
open LieLean LusztigF
noncomputable section
namespace LieLean.QuantumGroup
open Sl2.RankOne GrandLoop

/-- Integer polynomials evaluated at the genuine local parameter. -/
def integerLocalPolynomial : Polynomial ℤ →+* LocalRing :=
  Polynomial.eval₂RingHom (Int.castRingHom LocalRing) localX

lemma residue_integerLocalPolynomial (p : Polynomial ℤ) :
    residue (integerLocalPolynomial p) = (p.coeff 0 : ℚ) := by
  change residue (p.eval₂ (Int.castRingHom LocalRing) localX) = _
  rw [Polynomial.hom_eval₂]
  simp

lemma map_integerLocalPolynomial (p : Polynomial ℤ) :
    algebraMap LocalRing (RatFunc ℚ) (integerLocalPolynomial p) =
      integralLaurentEval (Polynomial.toLaurent p) := by
  change algebraMap LocalRing (RatFunc ℚ)
    (p.eval₂ (Int.castRingHom LocalRing) localX) = _
  rw [Polynomial.hom_eval₂]
  simp only [integralLaurentEval, LaurentPolynomial.eval₂_toLaurent]
  congr 1
  · ext z
    simp

/-- Clearing a power of the parameter cannot introduce nonintegral residues. -/
theorem residue_integer_of_local_power (a : LocalRing) (n : ℕ) (p : Polynomial ℤ)
    (h : a * localX ^ n = integerLocalPolynomial p) :
    ∃ z : ℤ, residue a = z := by
  induction n generalizing p with
  | zero =>
    refine ⟨p.coeff 0, ?_⟩
    simpa only [pow_zero, mul_one] using
      (congrArg residue h).trans (residue_integerLocalPolynomial p)
  | succ n ih =>
    have hz : p.coeff 0 = 0 := by
      have hh := congrArg residue h
      rw [map_mul, map_pow, residue_localX, zero_pow (Nat.succ_ne_zero n),
        mul_zero, residue_integerLocalPolynomial] at hh
      exact_mod_cast hh.symm
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr hz
    apply ih q
    apply mul_right_cancel₀ irreducible_localX.ne_zero
    rw [mul_assoc, ← pow_succ, h, hq, map_mul]
    simp [integerLocalPolynomial, mul_comm]

/-- A Laurent-integer rational function regular at zero has integer residue. -/
theorem residue_integer_of_laurent_at_zero (a : LocalRing) (f : LaurentPolynomial ℤ)
    (h : algebraMap LocalRing (RatFunc ℚ) a = integralLaurentEval f) :
    ∃ z : ℤ, residue a = z := by
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow f
  apply residue_integer_of_local_power a n p
  apply injective_algebraMap_localRing
  rw [map_mul, map_pow, algebraMap_localX, map_integerLocalPolynomial, hp, map_mul,
    integralLaurentEval_T, h]
  simp

/-- The actual bar-twisted infinity embedding of a Laurent integer has integer residue. -/
theorem InfinityLocalRing.residue_integer_of_laurent (a : InfinityLocalRing)
    (f : LaurentPolynomial ℤ)
    (h : algebraMap InfinityLocalRing (RatFunc ℚ) a = integralLaurentEval f) :
    ∃ z : ℤ, residue a = z := by
  apply residue_integer_of_laurent_at_zero a (LaurentPolynomial.invert f)
  have hh := congrArg RatFunc.bar h
  change RatFunc.bar (RatFunc.bar (algebraMap LocalRing (RatFunc ℚ) a)) = _ at hh
  simpa only [RatFunc.bar_bar, bar_integralLaurentEval] using hh

end LieLean.QuantumGroup
