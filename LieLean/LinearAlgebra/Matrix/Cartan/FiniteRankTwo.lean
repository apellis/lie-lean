/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Rank-two subdiagrams of finite-type Cartan matrices

For a Cartan matrix of finite type (Mathlib's `Matrix.IsFiniteCartan`), every pair of distinct
indices satisfies `aᵢⱼ aⱼᵢ ≤ 3`, i.e. every rank-two subdiagram is of type `A₁ × A₁`, `A₂`, `B₂`
or `G₂` (`Matrix.IsFiniteCartan.mul_le_three`).

## Main results

* `Matrix.IsFiniteCartan.mul_le_three`: `aᵢⱼ aⱼᵢ ≤ 3` for `i ≠ j`.

## References

Standard, e.g. V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., §4.8 (check). The proof
evaluates the positive definite form `diag(d) A` at `x = -2 eᵢ + aⱼᵢ eⱼ`, which gives
`2 dᵢ (4 - aᵢⱼ aⱼᵢ) > 0`.
-/

namespace Matrix.IsFiniteCartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ}

/-- In finite type, `aᵢⱼ aⱼᵢ ≤ 3` for `i ≠ j`: the rank-two subdiagrams are of finite type. -/
theorem mul_le_three (hA : A.IsFiniteCartan) {i j : ι} (hij : i ≠ j) :
    A i j * A j i ≤ 3 := by
  obtain ⟨d, hd, hS⟩ := hA.exists_posDef
  set x : ι → ℤ := Pi.single i (-2) + Pi.single j (A j i) with hx
  have hx0 : x ≠ 0 := by
    intro h
    have := congrFun h i
    simp [hx, hij] at this
  have hpos := hS.dotProduct_mulVec_pos hx0
  have key : star x ⬝ᵥ ((diagonal d * A) *ᵥ x) = 2 * d i * (4 - A i j * A j i) := by
    simp only [hx, star_trivial, mulVec_add, add_dotProduct, dotProduct_add, mulVec_single,
      single_dotProduct]
    simp [diagonal_mul, hA.diag]
    ring
  rw [key] at hpos
  have := hd i
  have : 0 < 4 - A i j * A j i := pos_of_mul_pos_right hpos (by positivity)
  omega

end Matrix.IsFiniteCartan
