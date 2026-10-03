/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.Matrix.Cartan.BraidOuter

/-!
# Rank-two and rank-three subdiagrams of finite-type Cartan matrices

For a Cartan matrix of finite type (Mathlib's `Matrix.IsFiniteCartan`), every pair of distinct
indices satisfies `aᵢⱼ aⱼᵢ ≤ 3`, i.e. every rank-two subdiagram is of type `A₁ × A₁`, `A₂`, `B₂`
or `G₂` (`Matrix.IsFiniteCartan.mul_le_three`). The rank-three subdiagrams have no triangles
(`Matrix.IsFiniteCartan.eq_zero_or_eq_zero_of_ne_zero`) and at a node `i` with two neighbours
`j`, `l` that are not joined, `aᵢⱼ aⱼᵢ + aᵢₗ aₗᵢ ≤ 3`
(`Matrix.IsFiniteCartan.mul_add_mul_le_three`). Hence the third-node condition of the braid
relations holds in finite type (`Matrix.IsFiniteCartan.braidOuterCondition`).

## Main results

* `Matrix.IsFiniteCartan.mul_le_three`: `aᵢⱼ aⱼᵢ ≤ 3` for `i ≠ j`.
* `Matrix.IsFiniteCartan.det_three_pos`: the principal `3 × 3` minors of `A` are positive.
* `Matrix.IsFiniteCartan.braidOuterCondition`: `A.IsFiniteCartan → A.BraidOuterCondition`.

## References

Standard, e.g. V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., §4.7–4.8. The
proofs use the positive definite form `diag(d) A`: for `mul_le_three` its value at
`x = -2 eᵢ + aⱼᵢ eⱼ`, which is `2 dᵢ (4 - aᵢⱼ aⱼᵢ) > 0`; in rank three the positivity of the
principal `3 × 3` minors of `diag(d) A`, which are `dᵢ dⱼ dₗ` times those of `A`.
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

/-- The principal `3 × 3` minors of a finite-type Cartan matrix are positive:
`det A_{ijl} = 8 - 2 (aᵢⱼ aⱼᵢ + aᵢₗ aₗᵢ + aⱼₗ aₗⱼ) + aᵢⱼ aⱼₗ aₗᵢ + aᵢₗ aₗⱼ aⱼᵢ > 0`. -/
theorem det_three_pos (hA : A.IsFiniteCartan) {i j l : ι} (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) :
    0 < 8 - 2 * (A i j * A j i) - 2 * (A i l * A l i) - 2 * (A j l * A l j) +
      A i j * A j l * A l i + A i l * A l j * A j i := by
  obtain ⟨d, hd, hS⟩ := hA.exists_posDef
  have he : Function.Injective ![i, j, l] := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have h := (hS.submatrix he).det_pos
  rw [det_fin_three] at h
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, submatrix_apply, cons_val_zero,
    diagonal_mul, hA.diag, cons_val_one, cons_val, Int.sub_pos] at h
  have hdi := hd i
  have hdj := hd j
  have hdl := hd l
  have hpos : 0 < d i * d j * d l := by positivity
  refine pos_of_mul_pos_right (a := d i * d j * d l) ?_ hpos.le
  linear_combination h

/-- An off-diagonal entry of a finite-type Cartan matrix is `0` or at most `-1`, and the entries
`aᵢⱼ`, `aⱼᵢ` vanish together. -/
lemma le_neg_one_of_ne_zero (hA : A.IsFiniteCartan) {i j : ι} (hij : i ≠ j) (h : A i j ≠ 0) :
    A i j ≤ -1 ∧ A j i ≤ -1 := by
  have h1 := hA.offDiag_nonpos i j hij
  have h2 := hA.offDiag_nonpos j i hij.symm
  have h' : A j i ≠ 0 := fun h0 ↦ h ((hA.zero_comm i j).2 h0)
  omega

/-- **No triangles in finite type**: three distinct nodes are not pairwise joined. -/
theorem eq_zero_or_eq_zero_of_ne_zero (hA : A.IsFiniteCartan) {i j l : ι} (hij : i ≠ j)
    (hil : i ≠ l) (hjl : j ≠ l) (h : A i j ≠ 0) : A i l = 0 ∨ A j l = 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨a1, a2⟩ := hA.le_neg_one_of_ne_zero hij h
  obtain ⟨b1, b2⟩ := hA.le_neg_one_of_ne_zero hil hc.1
  obtain ⟨c1, c2⟩ := hA.le_neg_one_of_ne_zero hjl hc.2
  have hdet := hA.det_three_pos hij hil hjl
  have p1 : 1 ≤ A i j * A j i := by nlinarith
  have p2 : 1 ≤ A i l * A l i := by nlinarith
  have p3 : 1 ≤ A j l * A l j := by nlinarith
  have q1 : 1 ≤ A i j * A j l := by nlinarith
  have q2 : 1 ≤ A i l * A l j := by nlinarith
  have r1 : A i j * A j l * A l i ≤ -1 := by nlinarith
  have r2 : A i l * A l j * A j i ≤ -1 := by nlinarith
  linarith

/-- At a node `i` with two neighbours `j`, `l` that are not joined, `aᵢⱼ aⱼᵢ + aᵢₗ aₗᵢ ≤ 3`: a
finite-type diagram has no two multiple edges at a node, and no neighbours of a triple edge. -/
theorem mul_add_mul_le_three (hA : A.IsFiniteCartan) {i j l : ι} (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) (h : A j l = 0) : A i j * A j i + A i l * A l i ≤ 3 := by
  have h' : A l j = 0 := (hA.zero_comm j l).1 h
  have hdet := hA.det_three_pos hij hil hjl
  rw [h, h'] at hdet
  linarith

/-- If `aᵢⱼ aⱼᵢ ≤ 1` then `aᵢⱼ ∈ {0, -1}`. -/
lemma eq_zero_or_eq_neg_one (hA : A.IsFiniteCartan) {i j : ι} (hij : i ≠ j)
    (h : A i j * A j i ≤ 1) : A i j = 0 ∨ A i j = -1 := by
  by_cases h0 : A i j = 0
  · exact Or.inl h0
  obtain ⟨a1, a2⟩ := hA.le_neg_one_of_ne_zero hij h0
  right
  nlinarith

/-- **The third-node condition holds in finite type**: every Cartan matrix of finite type
satisfies `Matrix.BraidOuterCondition` (in fact with no triangles). -/
theorem braidOuterCondition (hA : A.IsFiniteCartan) : A.BraidOuterCondition where
  simple i j l h h' hli hlj := by
    have hij : i ≠ j := by rintro rfl; rw [hA.diag] at h; omega
    rcases hA.eq_zero_or_eq_zero_of_ne_zero hij (Ne.symm hli) (Ne.symm hlj) (by omega) with
      h0 | h0
    · exact Or.inl h0
    · exact Or.inr (Or.inl h0)
  double i j l h h' hli hlj := by
    have hij : i ≠ j := by rintro rfl; rw [hA.diag] at h; omega
    rcases hA.eq_zero_or_eq_zero_of_ne_zero hij (Ne.symm hli) (Ne.symm hlj) (by omega) with
      h0 | h0
    · have hb := hA.mul_add_mul_le_three hij.symm (Ne.symm hlj) (Ne.symm hli) h0
      rw [h, h'] at hb
      rcases hA.eq_zero_or_eq_neg_one (Ne.symm hlj) (by linarith) with h1 | h1
      · exact Or.inl ⟨h0, h1⟩
      · exact Or.inr (Or.inr ⟨h0, h1⟩)
    · have hb := hA.mul_add_mul_le_three hij (Ne.symm hli) hlj.symm h0
      rw [h, h'] at hb
      rcases hA.eq_zero_or_eq_neg_one (Ne.symm hli) (by linarith) with h1 | h1
      · exact Or.inl ⟨h1, h0⟩
      · exact Or.inr (Or.inl ⟨h1, h0⟩)
  triple i j l h h' hli hlj := by
    have hij : i ≠ j := by rintro rfl; rw [hA.diag] at h; omega
    rcases hA.eq_zero_or_eq_zero_of_ne_zero hij (Ne.symm hli) (Ne.symm hlj) (by omega) with
      h0 | h0
    · have hb := hA.mul_add_mul_le_three hij.symm (Ne.symm hlj) (Ne.symm hli) h0
      rw [h, h'] at hb
      refine ⟨h0, ?_⟩
      by_contra h1
      obtain ⟨a1, a2⟩ := hA.le_neg_one_of_ne_zero (Ne.symm hlj) h1
      nlinarith
    · have hb := hA.mul_add_mul_le_three hij (Ne.symm hli) hlj.symm h0
      rw [h, h'] at hb
      refine ⟨?_, h0⟩
      by_contra h1
      obtain ⟨a1, a2⟩ := hA.le_neg_one_of_ne_zero (Ne.symm hli) h1
      nlinarith

end Matrix.IsFiniteCartan
