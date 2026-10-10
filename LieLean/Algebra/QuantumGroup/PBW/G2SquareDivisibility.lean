/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.G2SquareNewton
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Factorial cancellation for the G₂ Newton coefficients

The Gaussian integers in this file are the ordinary polynomials `1 + x + ... + x^(m-1)`,
not the symmetric quantum integers. The argument is reconstructed from cyclotomic
factorization and the block valuation estimate.
-/

open Finset Polynomial UniqueFactorizationMonoid

noncomputable section

namespace LieLean.QuantumGroup.G2Integral.SquareCancellation

/-- An ordinary Gaussian integer over `ℤ`. -/
def gaussian (m : ℕ) : ℤ[X] := ∑ i ∈ range m, X ^ i

/-- Factorials along a positive arithmetic progression. -/
def progressionProduct (k n : ℕ) : ℤ[X] :=
  ∏ i ∈ range n, gaussian (k * (i + 1))

lemma gaussian_ne_zero (m : ℕ) (hm : 0 < m) : gaussian m ≠ 0 := by
  rw [gaussian, ← prod_cyclotomic_eq_geom_sum hm]
  exact prod_ne_zero_iff.mpr fun i _ ↦ cyclotomic_ne_zero i ℤ

lemma progressionProduct_ne_zero (k n : ℕ) (hk : 0 < k) :
    progressionProduct k n ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro i _
  exact gaussian_ne_zero _ (by positivity)

lemma cyclotomic_emultiplicity (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    emultiplicity (cyclotomic d ℤ) (cyclotomic e ℤ) = if d = e then 1 else 0 := by
  split_ifs with h
  · subst e
    simpa using emultiplicity_pow_self_of_prime (cyclotomic.irreducible hd).prime 1
  · apply emultiplicity_eq_zero.mpr
    intro hdiv
    apply h
    apply cyclotomic_injective (R := ℤ)
    exact eq_of_monic_of_associated (cyclotomic.monic d ℤ) (cyclotomic.monic e ℤ)
      ((cyclotomic.irreducible hd).associated_of_dvd (cyclotomic.irreducible he) hdiv)

lemma gaussian_emultiplicity (d m : ℕ) (hd : 1 < d) (hm : 0 < m) :
    emultiplicity (cyclotomic d ℤ) (gaussian m) = if d ∣ m then 1 else 0 := by
  classical
  rw [gaussian, ← prod_cyclotomic_eq_geom_sum hm,
    Finset.emultiplicity_prod (cyclotomic.irreducible (by omega : 0 < d)).prime]
  have he (e : ℕ) (he : e ∈ m.divisors.erase 1) : 0 < e :=
    Nat.pos_of_mem_divisors (mem_of_mem_erase he)
  simp_rw [sum_congr rfl (fun e he' ↦ cyclotomic_emultiplicity d e (by omega) (he e he'))]
  simp [Nat.mem_divisors, hm.ne', show d ≠ 1 by omega]

lemma progressionProduct_emultiplicity (k n d : ℕ) (hk : 0 < k) (hd : 1 < d) :
    emultiplicity (cyclotomic d ℤ) (progressionProduct k n) =
      (#{i ∈ range n | d ∣ k * (i + 1)} : ℕ∞) := by
  classical
  rw [progressionProduct,
    Finset.emultiplicity_prod (cyclotomic.irreducible (by omega : 0 < d)).prime]
  rw [sum_congr rfl (fun i _ ↦ gaussian_emultiplicity d (k * (i + 1)) hd
    (by positivity))]
  simp

lemma factorial_emultiplicity (n d : ℕ) (hd : 1 < d) :
    emultiplicity (cyclotomic d ℤ) (progressionProduct 1 n) = (n / d : ℕ) := by
  rw [progressionProduct_emultiplicity 1 n d (by decide) hd]
  simp only [one_mul, Nat.card_multiples]

lemma tripleProduct_emultiplicity (n h : ℕ) (hh : 0 < h) :
    emultiplicity (cyclotomic (3 * h) ℤ) (progressionProduct 3 n) = (n / h : ℕ) := by
  rw [progressionProduct_emultiplicity 3 n (3 * h) (by decide) (by omega)]
  simp only [Nat.mul_dvd_mul_iff_left (by decide : 0 < 3), Nat.card_multiples]

lemma tripleProduct_emultiplicity_of_not_dvd (n d : ℕ) (hd : 1 < d) (h3 : ¬3 ∣ d) :
    emultiplicity (cyclotomic d ℤ) (progressionProduct 3 n) = (n / d : ℕ) := by
  have hc : d.Coprime 3 := ((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm
  rw [progressionProduct_emultiplicity 3 n d (by decide) hd]
  simp only [hc.dvd_mul_left, Nat.card_multiples]

lemma prime_dvd_progressionProduct (k t : ℕ) (hk : 0 < k) {p : ℤ[X]}
    (hp : Prime p) (hdiv : p ∣ progressionProduct k t) :
    ∃ d : ℕ, 1 < d ∧ Associated p (cyclotomic d ℤ) := by
  classical
  obtain ⟨i, _, hi⟩ := (hp.dvd_finsetProd_iff _).mp hdiv
  change p ∣ gaussian (k * (i + 1)) at hi
  rw [gaussian, ← prod_cyclotomic_eq_geom_sum (by positivity : 0 < k * (i + 1))] at hi
  obtain ⟨d, hd, hpd⟩ := (hp.dvd_finsetProd_iff _).mp hi
  have hd0 := Nat.pos_of_mem_divisors (mem_of_mem_erase hd)
  have hd1 := ne_of_mem_erase hd
  exact ⟨d, by omega,
    hp.irreducible.associated_of_dvd (cyclotomic.irreducible hd0) hpd⟩

/-- Full polynomial denominator cancellation for the G₂ Newton coefficients.
For `a = n-t`, `b = 3t-n`, this is `P_t ∣ [b]! P_a d(n,t)` in `ℤ[x]`.
The proof uses the all-index cyclotomic block estimate, not termwise cancellation
in a Newton expansion. -/
theorem newtonCoeff_factorial_dvd (n t : ℕ) (htn : t ≤ n) (hnt : n ≤ 3 * t) :
    progressionProduct 3 t ∣ progressionProduct 1 (3 * t - n) *
      progressionProduct 3 (n - t) * newtonCoeff n t := by
  apply (dvd_iff_emultiplicity_le (progressionProduct_ne_zero 3 t (by decide))).mpr
  intro p hp
  by_cases hpd : p ∣ progressionProduct 3 t
  · obtain ⟨d, hd, hassoc⟩ := prime_dvd_progressionProduct 3 t (by decide) hp hpd
    rw [← emultiplicity_eq_of_associated_left hassoc,
      ← emultiplicity_eq_of_associated_left hassoc]
    have hprime := (cyclotomic.irreducible (show 0 < d by omega)).prime
    rw [emultiplicity_mul hprime, emultiplicity_mul hprime,
      factorial_emultiplicity _ d hd]
    by_cases h3 : 3 ∣ d
    · obtain ⟨h, rfl⟩ := h3
      have hh : 0 < h := by omega
      rw [tripleProduct_emultiplicity t h hh, tripleProduct_emultiplicity (n - t) h hh]
      have hv := le_emultiplicity_of_pow_dvd (cyclotomic_pow_dvd_newtonCoeff h hh n t)
      have hf := square_floor_comparison (n - t) (3 * t - n) n h hh (by omega)
      have hb : t / h ≤ (3 * t - n) / (3 * h) + (n - t) / h +
          (t / h - n / (3 * h)) := by omega
      have hb' : (t / h : ℕ∞) ≤ ((3 * t - n) / (3 * h) : ℕ) +
          ((n - t) / h : ℕ) + (t / h - n / (3 * h) : ℕ) := by exact_mod_cast hb
      exact hb'.trans (add_le_add le_rfl hv)
    · rw [tripleProduct_emultiplicity_of_not_dvd t d hd h3,
        tripleProduct_emultiplicity_of_not_dvd (n - t) d hd h3]
      have hb : t / d ≤ (3 * t - n) / d + (n - t) / d := by
        by_cases ha : t ≤ n - t
        · exact (Nat.div_le_div_right (c := d) ha).trans (Nat.le_add_left _ _)
        · exact (Nat.div_le_div_right (c := d) (show t ≤ 3 * t - n by omega)).trans
            (Nat.le_add_right _ _)
      have hb' : (t / d : ℕ∞) ≤ ((3 * t - n) / d : ℕ) + ((n - t) / d : ℕ) := by
        exact_mod_cast hb
      exact hb'.trans (le_add_of_nonneg_right bot_le)
  · rw [emultiplicity_eq_zero.mpr hpd]
    exact bot_le

/-- The integral polynomial obtained after the factorial cancellation.
It is defined as zero outside the Newton support range. -/
def squarePolynomial (n t : ℕ) : ℤ[X] :=
  if h : t ≤ n ∧ n ≤ 3 * t then
    Classical.choose (newtonCoeff_factorial_dvd n t h.1 h.2)
  else 0

/-- The exact, division-free identity defining the integral square polynomial. -/
theorem squarePolynomial_spec (n t : ℕ) (htn : t ≤ n) (hnt : n ≤ 3 * t) :
    progressionProduct 3 t * squarePolynomial n t =
      progressionProduct 1 (3 * t - n) * progressionProduct 3 (n - t) * newtonCoeff n t := by
  rw [squarePolynomial, dite_eq_left ⟨htn, hnt⟩]
  exact (Classical.choose_spec (newtonCoeff_factorial_dvd n t htn hnt)).symm

/-- The polynomial witness is unique; no inverse in `ℤ[x]` is used. -/
theorem squarePolynomial_unique (n t : ℕ) (htn : t ≤ n) (hnt : n ≤ 3 * t)
    (H : ℤ[X]) (hH : progressionProduct 3 t * H =
      progressionProduct 1 (3 * t - n) * progressionProduct 3 (n - t) * newtonCoeff n t) :
    H = squarePolynomial n t := by
  apply mul_left_cancel₀ (progressionProduct_ne_zero 3 t (by decide))
  exact hH.trans (squarePolynomial_spec n t htn hnt).symm

end LieLean.QuantumGroup.G2Integral.SquareCancellation
