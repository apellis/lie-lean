/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.G2SquareCancellation
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The polynomial Newton operator for the G₂ square kernel

The operator used here is `(1 + z) F(xz)`, cubed. Its Newton factors have eigenvalues
`x^(3i)`. The proofs are reconstructed polynomial arguments; no specialization
inverts `x - 1` or a quantum integer.
-/

open Finset Polynomial

noncomputable section

namespace LieLean.QuantumGroup.G2Integral.SquareCancellation

variable {R : Type*} [CommRing R]

/-- The one-step dilation and multiplication operator. Its cube is the G₂ operator. -/
def shift (x : R) : Module.End R R[X] where
  toFun F := (1 + X) * F.comp (C x * X)
  map_add' F H := by simp [add_comp, mul_add]
  map_smul' c F := by simp [smul_eq_C_mul, mul_comp, mul_left_comm]

lemma shift_apply (x : R) (F : R[X]) :
    shift x F = (1 + X) * F.comp (C x * X) := rfl

/-- The accumulated linear factors of the dilation operator. -/
def linearFactors (x : R) (n : ℕ) : R[X] :=
  ∏ i ∈ range n, (1 + C (x ^ i) * X)

lemma shift_pow_apply (x : R) (n : ℕ) (F : R[X]) :
    (shift x ^ n) F = linearFactors x n * F.comp (C (x ^ n) * X) := by
  induction n with
  | zero => simp [linearFactors]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, shift_apply, ih]
    simp only [mul_comp, comp_assoc, mul_comp, C_comp, X_comp]
    have hc : C (x ^ n) * (C x * X) = C (x ^ (n + 1)) * X := by
      rw [pow_succ, map_mul]
      ring
    rw [hc]
    have hp : (1 + X) * (linearFactors x n).comp (C x * X) =
        linearFactors x (n + 1) := by
      simp only [linearFactors, Polynomial.prod_comp, add_comp, one_comp, mul_comp, C_comp, X_comp]
      rw [prod_range_succ']
      simp only [pow_zero, map_one, one_mul]
      rw [mul_comm (1 + X)]
      congr 1
      apply prod_congr rfl
      intro i _
      rw [pow_succ, map_mul]
      ring
    rw [← mul_assoc, hp]

/-- The cube is precisely multiplication by the three G₂ linear factors followed by dilation. -/
lemma shift_cube_apply (x : R) (F : R[X]) :
    (shift x ^ 3) F = (1 + X) * (1 + C x * X) * (1 + C (x ^ 2) * X) *
      F.comp (C (x ^ 3) * X) := by
  rw [shift_pow_apply]
  simp [linearFactors, prod_range_succ]

/-- Polynomial Newton factors, before evaluation at the G₂ operator. -/
def newtonFactors (x : R) (j n : ℕ) : R[X] :=
  ∏ i ∈ range n, (X - C (x ^ (3 * (j + i))))

/-- An arbitrary consecutive interval of Newton factors, acting on polynomials. -/
def newtonOp (x : R) (j n : ℕ) : Module.End R R[X] :=
  aeval (shift x ^ 3) (newtonFactors x j n)

lemma newtonOp_zero (x : R) (j : ℕ) : newtonOp x j 0 = 1 := by
  simp [newtonOp, newtonFactors]

lemma newtonOp_succ (x : R) (j n : ℕ) :
    newtonOp x j (n + 1) =
      (shift x ^ 3 - x ^ (3 * (j + n)) • 1) * newtonOp x j n := by
  unfold newtonOp newtonFactors
  rw [prod_range_succ, mul_comm]
  simp only [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

lemma newtonOp_add (x : R) (j n m : ℕ) :
    newtonOp x j (n + m) = newtonOp x (j + n) m * newtonOp x j n := by
  unfold newtonOp newtonFactors
  rw [prod_range_add, mul_comm, map_mul]
  congr 2
  apply prod_congr rfl
  intro i _
  congr 3
  omega

lemma shift_pow_map {S : Type*} [CommRing S] (f : R →+* S) (x : R)
    (n : ℕ) (F : R[X]) :
    ((shift x ^ n) F).map f = (shift (f x) ^ n) (F.map f) := by
  rw [shift_pow_apply, shift_pow_apply]
  simp [linearFactors, Polynomial.map_comp, Polynomial.map_prod]

lemma newtonOp_map {S : Type*} [CommRing S] (f : R →+* S) (x : R)
    (j n : ℕ) (F : R[X]) :
    (newtonOp x j n F).map f = newtonOp (f x) j n (F.map f) := by
  induction n with
  | zero => simp [newtonOp_zero]
  | succ n ih =>
    simp only [newtonOp_succ, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, smul_eq_C_mul, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, map_C, map_pow, shift_pow_map, ih]

lemma shift_pow_preserves_X_dvd (x : R) (n m : ℕ) (F : R[X])
    (hF : X ^ m ∣ F) : X ^ m ∣ (shift x ^ n) F := by
  obtain ⟨H, rfl⟩ := hF
  refine ⟨linearFactors x n * C (x ^ n) ^ m * H.comp (C (x ^ n) * X), ?_⟩
  simp only [shift_pow_apply, mul_comp, pow_comp, X_comp, mul_pow]
  ring

lemma newtonOp_preserves_X_dvd (x : R) (j n m : ℕ) (F : R[X])
    (hF : X ^ m ∣ F) : X ^ m ∣ newtonOp x j n F := by
  induction n with
  | zero => simpa [newtonOp_zero] using hF
  | succ n ih =>
    simp only [newtonOp_succ, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, smul_eq_C_mul]
    exact dvd_sub (shift_pow_preserves_X_dvd x 3 m _ ih) (dvd_mul_of_dvd_right ih _)

section Domain

variable [IsDomain R]

/-- The root-of-unity product identity, without any inversion of the polynomial variable. -/
theorem linearFactors_eq (x : R) (n : ℕ) (hn : 0 < n) (hx : IsPrimitiveRoot x n) :
    linearFactors x n = 1 - (-X) ^ n := by
  have hc : IsPrimitiveRoot (C x : R[X]) n :=
    hx.map_of_injective (Polynomial.C_injective)
  have hp := X_pow_sub_C_eq_prod hc hn (rfl : (-X : R[X]) ^ n = (-X) ^ n)
  have he := congrArg (Polynomial.eval (1 : R[X])) hp
  simpa [linearFactors, eval_prod, mul_neg, sub_neg_eq_add] using he.symm

omit [IsDomain R] in
/-- A primitive cubic multiple gives a primitive root for the Newton eigenvalues. -/
lemma primitive_cube {x : R} {h : ℕ} (hx : IsPrimitiveRoot x (3 * h)) :
    IsPrimitiveRoot (x ^ 3) h := by
  have hp := hx.pow_of_dvd (by decide : 3 ≠ 0) (dvd_mul_right 3 h)
  simpa using hp

/-- Each full block of Newton factors is `T^h - 1` at a primitive `3h`-th root. -/
theorem newtonFactors_block {x : R} {h : ℕ} (hh : 0 < h)
    (hx : IsPrimitiveRoot x (3 * h)) (j : ℕ) :
    newtonFactors x j h = X ^ h - 1 := by
  have hq := primitive_cube hx
  have ha : (x ^ (3 * j)) ^ h = 1 := by
    rw [← pow_mul, show 3 * j * h = 3 * h * j by ring, pow_mul, hx.pow_eq_one, one_pow]
  have hp := X_pow_sub_C_eq_prod hq hh ha
  rw [C_1] at hp
  rw [hp]
  apply prod_congr rfl
  intro i _
  congr 2
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

/-- Exact block cancellation on every polynomial at a primitive root.
This is not a statement only about the constant input polynomial. -/
theorem newtonOp_block {x : R} {h : ℕ} (hh : 0 < h)
    (hx : IsPrimitiveRoot x (3 * h)) (j : ℕ) (F : R[X]) :
    newtonOp x j h F = -((-X) ^ (3 * h)) * F := by
  rw [newtonOp, newtonFactors_block hh hx]
  simp only [map_sub, map_pow, aeval_X, map_one, ← pow_mul, LinearMap.sub_apply,
    Module.End.one_apply]
  rw [shift_pow_apply, linearFactors_eq x (3 * h) (by omega) hx, hx.pow_eq_one]
  simp only [map_one, one_mul, comp_X]
  ring

end Domain

/-- Integral coefficient divisibility for a single Newton block. The proof specializes at a
complex primitive root and uses its minimal polynomial over `ℤ`. -/
theorem cyclotomic_dvd_newtonOp_coeff (h : ℕ) (hh : 0 < h) (j m n : ℕ)
    (hn : n < m + 3 * h) :
    cyclotomic (3 * h) ℤ ∣ (newtonOp (X : ℤ[X]) j h (X ^ m)).coeff n := by
  have hd : 0 < 3 * h := by omega
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (↑(3 * h) : ℂ))
  have hζ : IsPrimitiveRoot ζ (3 * h) := Complex.isPrimitiveRoot_exp (3 * h) hd.ne'
  rw [cyclotomic_eq_minpoly hζ hd]
  apply minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hd)
  have he := newtonOp_map (aeval ζ).toRingHom (X : ℤ[X]) j h (X ^ m)
  have he' := congrArg (fun P : ℂ[X] ↦ P.coeff n) he
  simp only [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
    Polynomial.map_pow, map_X] at he'
  rw [he', newtonOp_block hh hζ]
  apply (X_pow_dvd_iff (n := m + 3 * h)).mp ?_ n hn
  refine ⟨-((-1 : ℂ[X]) ^ (3 * h)), ?_⟩
  rw [neg_pow, pow_add]
  ring

/-- A full Newton block over `ℤ[x]`, with its integral cyclotomic filtration. -/
def cyclotomicBlock (h : ℕ) (hh : 0 < h) (j : ℕ) :
    Block (cyclotomic (3 * h) ℤ) (3 * h) where
  toLinearMap := newtonOp (X : ℤ[X]) j h
  triangular m n hn := X_pow_dvd_iff.mp
    (newtonOp_preserves_X_dvd (X : ℤ[X]) j h m (X ^ m) dvd_rfl) n hn
  raises m n hn := cyclotomic_dvd_newtonOp_coeff h hh j m n hn

lemma apply_cyclotomicBlocks (h : ℕ) (hh : 0 < h) (u r : ℕ) (F : ℤ[X][X]) :
    applyBlocks (fun j ↦ cyclotomicBlock h hh (u + j * h))
      (newtonOp (X : ℤ[X]) 0 u F) r =
        newtonOp (X : ℤ[X]) 0 (u + r * h) F := by
  induction r with
  | zero => simp [applyBlocks]
  | succ r ih =>
    rw [applyBlocks, ih]
    change newtonOp (X : ℤ[X]) (u + r * h) h
      (newtonOp (X : ℤ[X]) 0 (u + r * h) F) = _
    rw [show u + (r + 1) * h = (u + r * h) + h by ring,
      newtonOp_add _ 0 (u + r * h) h]
    simp only [zero_add, Module.End.mul_apply]

/-- Cyclotomic cancellation for every Newton coefficient, with no bounds on `n` or `t`.
This is the block valuation estimate in `ℤ[x]`; natural subtraction encodes the maximum
with zero. The input polynomial is arbitrary. -/
theorem cyclotomic_pow_dvd_newtonOp_coeff (h : ℕ) (hh : 0 < h) (t n : ℕ)
    (F : ℤ[X][X]) :
    cyclotomic (3 * h) ℤ ^ (t / h - n / (3 * h)) ∣
      (newtonOp (X : ℤ[X]) 0 t F).coeff n := by
  have hv := coeff_dvd_pow_of_blocks
    (fun j ↦ cyclotomicBlock h hh (t % h + j * h)) (by omega : 0 < 3 * h)
    (newtonOp (X : ℤ[X]) 0 (t % h) F) (t / h) n
  rw [apply_cyclotomicBlocks] at hv
  simpa only [Nat.mod_add_div', Nat.add_comm] using hv

/-- The polynomial `D_t(z)` of the integral Newton recurrence. -/
def newtonPolynomial (t : ℕ) : ℤ[X][X] := newtonOp (X : ℤ[X]) 0 t 1

lemma newtonPolynomial_zero : newtonPolynomial 0 = 1 := by
  simp [newtonPolynomial, newtonOp_zero]

/-- The defining integral recurrence, in the original three-factor convention. -/
lemma newtonPolynomial_succ (t : ℕ) :
    newtonPolynomial (t + 1) =
      (1 + X) * (1 + C (X : ℤ[X]) * X) * (1 + C ((X : ℤ[X]) ^ 2) * X) *
        (newtonPolynomial t).comp (C ((X : ℤ[X]) ^ 3) * X) -
          C ((X : ℤ[X]) ^ (3 * t)) * newtonPolynomial t := by
  simp only [newtonPolynomial, newtonOp_succ, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, smul_eq_C_mul, zero_add, shift_cube_apply]

/-- The integral coefficient `d(n,t;x)`, before the factorial prefactor. -/
def newtonCoeff (n t : ℕ) : ℤ[X] := (newtonPolynomial t).coeff n

/-- The unrestricted cyclotomic valuation estimate for the G₂ Newton coefficients. -/
theorem cyclotomic_pow_dvd_newtonCoeff (h : ℕ) (hh : 0 < h) (n t : ℕ) :
    cyclotomic (3 * h) ℤ ^ (t / h - n / (3 * h)) ∣ newtonCoeff n t :=
  cyclotomic_pow_dvd_newtonOp_coeff h hh t n 1

end LieLean.QuantumGroup.G2Integral.SquareCancellation
