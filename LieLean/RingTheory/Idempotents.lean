/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Lifting an element that is idempotent modulo a nilpotent element

If `x - x ^ 2` is nilpotent, then `1 - (1 - x ^ n) ^ n` is idempotent for every `n` with
`(x - x ^ 2) ^ n = 0` (`isIdempotentElem_one_sub_one_sub_pow_pow`). This file shows that this
idempotent does not depend on `n`, so it defines a canonical idempotent `idempotentLift x`, a
polynomial in `x` without constant term. The polynomial is the same for all `n` large enough,
so the lift commutes with every map intertwining two such elements; this is what makes the lift
natural when `x` is the component of a natural transformation.

## Main definitions

* `idempotentLiftPow n x`: the element `1 - (1 - x ^ n) ^ n`.
* `idempotentLift x`: `idempotentLiftPow n x` for `n` the nilpotency class of `x - x ^ 2`.

## Main results

* `idempotentLiftPow_eq_idempotentLiftPow`: `1 - (1 - x ^ n) ^ n` is independent of `n` once
  `(x - x ^ 2) ^ n = 0`.
* `isIdempotentElem_idempotentLift`: `idempotentLift x` is idempotent if `x - x ^ 2` is
  nilpotent.
* `LinearMap.comp_idempotentLiftPow`: a linear map intertwining `u` and `v` intertwines the
  lifts.
-/

open Polynomial

variable {R : Type*} [Ring R]

/-- The element `1 - (1 - x ^ n) ^ n`. It is idempotent once `(x - x ^ 2) ^ n = 0`. -/
def idempotentLiftPow (n : ℕ) (x : R) : R := 1 - (1 - x ^ n) ^ n

/-- The idempotent lift of `x`: `1 - (1 - x ^ n) ^ n` for `n` the nilpotency class of
`x - x ^ 2`. If `x - x ^ 2` is nilpotent it is idempotent and agrees with
`idempotentLiftPow n x` for every `n` with `(x - x ^ 2) ^ n = 0`. -/
noncomputable def idempotentLift (x : R) : R := idempotentLiftPow (nilpotencyClass (x - x ^ 2)) x

theorem aeval_idempotentLiftPow (n : ℕ) (x : R) :
    aeval x (idempotentLiftPow n (X : ℤ[X])) = idempotentLiftPow n x := by
  simp [idempotentLiftPow]

theorem map_idempotentLiftPow {S F : Type*} [Ring S] [FunLike F R S] [RingHomClass F R S] (g : F)
    (n : ℕ) (x : R) : g (idempotentLiftPow n x) = idempotentLiftPow n (g x) := by
  simp [idempotentLiftPow]

/-- For `n ≠ 0`, `X - X ^ 2` divides `1 - (1 - X ^ n) ^ n - X` in `ℤ[X]`. -/
theorem X_sub_X_sq_dvd_idempotentLiftPow_sub {n : ℕ} (hn : n ≠ 0) :
    (X - X ^ 2 : ℤ[X]) ∣ idempotentLiftPow n X - X := by
  have h0 : (X : ℤ[X]) ∣ idempotentLiftPow n X - X := by
    rw [X_dvd_iff, coeff_zero_eq_eval_zero]
    simp [idempotentLiftPow, zero_pow hn]
  have h1 : (X - C 1 : ℤ[X]) ∣ idempotentLiftPow n X - X := by
    rw [dvd_iff_isRoot]
    simp [idempotentLiftPow, zero_pow hn]
  have hc : IsCoprime (X : ℤ[X]) (X - C 1) := ⟨1, -1, by simp⟩
  have h := hc.mul_dvd h0 h1
  have he : (X - X ^ 2 : ℤ[X]) = -(X * (X - C 1)) := by simp; ring
  rw [he, neg_dvd]
  exact h

/-- `X` divides `1 - (1 - X ^ n) ^ n` in `ℤ[X]` for `n ≠ 0`. -/
theorem X_dvd_idempotentLiftPow {n : ℕ} (hn : n ≠ 0) : (X : ℤ[X]) ∣ idempotentLiftPow n X := by
  rw [X_dvd_iff, coeff_zero_eq_eval_zero]
  simp [idempotentLiftPow, zero_pow hn]

theorem isIdempotentElem_idempotentLiftPow {x : R} {n : ℕ} (h : (x - x ^ 2) ^ n = 0) :
    IsIdempotentElem (idempotentLiftPow n x) :=
  isIdempotentElem_one_sub_one_sub_pow_pow x n h

/-- `1 - (1 - x ^ n) ^ n` does not depend on `n` once `(x - x ^ 2) ^ n = 0`. -/
theorem idempotentLiftPow_eq_idempotentLiftPow {x : R} {k n m : ℕ} (hk : (x - x ^ 2) ^ k = 0)
    (hn : k ≤ n) (hm : k ≤ m) : idempotentLiftPow n x = idempotentLiftPow m x := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have : Subsingleton R := subsingleton_of_zero_eq_one (by simpa using hk.symm)
    exact Subsingleton.elim _ _
  have hn0 : n ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  obtain ⟨a, ha⟩ := X_sub_X_sq_dvd_idempotentLiftPow_sub (n := n) hn0
  obtain ⟨b, hb⟩ := X_sub_X_sq_dvd_idempotentLiftPow_sub (n := m) hm0
  have hcomm : ∀ p q : ℤ[X], Commute (aeval x p) (aeval x q) := fun p q ↦ by
    change _ * _ = _ * _
    rw [← map_mul, mul_comm, map_mul]
  refine eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute
    (isIdempotentElem_idempotentLiftPow (pow_eq_zero_of_le hn hk))
    (isIdempotentElem_idempotentLiftPow (pow_eq_zero_of_le hm hk)) ?_ ?_
  · have he : idempotentLiftPow n x - idempotentLiftPow m x =
        aeval x (X - X ^ 2 : ℤ[X]) * aeval x (a - b) := by
      rw [← aeval_idempotentLiftPow n x, ← aeval_idempotentLiftPow m x, ← map_mul, mul_sub, ← ha,
        ← hb]
      simp
    rw [he]
    refine Commute.isNilpotent_mul_right (hcomm (X - X ^ 2) (a - b)) ⟨k, ?_⟩
    simpa using hk
  · rw [← aeval_idempotentLiftPow n x, ← aeval_idempotentLiftPow m x]
    exact hcomm _ _

theorem nilpotencyClass_le_of_pow_eq_zero {x : R} {k : ℕ} (hk : x ^ k = 0) :
    nilpotencyClass x ≤ k :=
  Nat.sInf_le hk

/-- `idempotentLift x = 1 - (1 - x ^ n) ^ n` whenever `(x - x ^ 2) ^ n = 0`. -/
theorem idempotentLift_eq {x : R} {n : ℕ} (h : (x - x ^ 2) ^ n = 0) :
    idempotentLift x = idempotentLiftPow n x :=
  idempotentLiftPow_eq_idempotentLiftPow (k := nilpotencyClass (x - x ^ 2))
    (pow_nilpotencyClass ⟨n, h⟩) le_rfl (nilpotencyClass_le_of_pow_eq_zero h)

theorem isIdempotentElem_idempotentLift {x : R} (h : IsNilpotent (x - x ^ 2)) :
    IsIdempotentElem (idempotentLift x) :=
  isIdempotentElem_idempotentLiftPow (pow_nilpotencyClass h)

/-- An idempotent is its own lift. -/
theorem IsIdempotentElem.idempotentLift_eq {e : R} (he : IsIdempotentElem e) :
    idempotentLift e = e := by
  have h0 : e - e ^ 2 = 0 := by rw [sq, he.eq, sub_self]
  rw [_root_.idempotentLift_eq (n := 1) (by rw [pow_one, h0])]
  simp [idempotentLiftPow]

/-- If `x` is fixed by `e` on both sides, so is every `1 - (1 - x ^ n) ^ n`, `n ≠ 0`. -/
theorem idempotentLiftPow_mul_eq {x e : R} {n : ℕ} (hn : n ≠ 0) (hx : x * e = x) :
    idempotentLiftPow n x * e = idempotentLiftPow n x := by
  obtain ⟨a, ha⟩ := X_dvd_idempotentLiftPow hn
  have hcomm : Commute (aeval x a) x := by
    change _ * _ = _ * _
    nth_rw 2 [← aeval_X (R := ℤ) x]
    nth_rw 3 [← aeval_X (R := ℤ) x]
    rw [← map_mul, mul_comm, map_mul]
  rw [← aeval_idempotentLiftPow n x, ha, map_mul, aeval_X, ← hcomm.eq, mul_assoc, hx]

theorem mul_idempotentLiftPow_eq {x e : R} {n : ℕ} (hn : n ≠ 0) (hx : e * x = x) :
    e * idempotentLiftPow n x = idempotentLiftPow n x := by
  obtain ⟨a, ha⟩ := X_dvd_idempotentLiftPow hn
  rw [← aeval_idempotentLiftPow n x, ha, map_mul, aeval_X, ← mul_assoc, hx]

namespace LinearMap

variable {S M N : Type*} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]

theorem comp_pow_of_comp_eq {f : M →ₗ[S] N} {u : Module.End S M} {v : Module.End S N}
    (h : f ∘ₗ u = v ∘ₗ f) (k : ℕ) : f ∘ₗ (u ^ k) = (v ^ k) ∘ₗ f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← comp_assoc, ih,
      comp_assoc, h, comp_assoc]

theorem comp_one_sub_of_comp_eq {f : M →ₗ[S] N} {u : Module.End S M} {v : Module.End S N}
    (h : f ∘ₗ u = v ∘ₗ f) : f ∘ₗ (1 - u) = (1 - v) ∘ₗ f := by
  rw [comp_sub, sub_comp, h]
  rfl

/-- A linear map intertwining `u` and `v` intertwines `1 - (1 - u ^ n) ^ n` and
`1 - (1 - v ^ n) ^ n`. -/
theorem comp_idempotentLiftPow {f : M →ₗ[S] N} {u : Module.End S M} {v : Module.End S N}
    (h : f ∘ₗ u = v ∘ₗ f) (n : ℕ) :
    f ∘ₗ (idempotentLiftPow n u) = (idempotentLiftPow n v) ∘ₗ f :=
  comp_one_sub_of_comp_eq (comp_pow_of_comp_eq (comp_one_sub_of_comp_eq
    (comp_pow_of_comp_eq h n)) n)

/-- A linear map intertwining `u` and `v`, with `u - u ^ 2` and `v - v ^ 2` nilpotent,
intertwines the idempotent lifts. -/
theorem comp_idempotentLift {f : M →ₗ[S] N} {u : Module.End S M} {v : Module.End S N}
    (h : f ∘ₗ u = v ∘ₗ f) (hu : IsNilpotent (u - u ^ 2)) (hv : IsNilpotent (v - v ^ 2)) :
    f ∘ₗ (idempotentLift u) = (idempotentLift v) ∘ₗ f := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  rw [_root_.idempotentLift_eq (pow_eq_zero_of_le (le_max_left a b) ha),
    _root_.idempotentLift_eq (pow_eq_zero_of_le (le_max_right a b) hb)]
  exact comp_idempotentLiftPow h _

end LinearMap
