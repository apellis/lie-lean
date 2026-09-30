/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# The third-node condition for braid relations

`Matrix.BraidOuterCondition A` is a condition on the Dynkin diagram of an integer matrix `A`,
used for the braid relations of Lusztig's automorphisms `Tᵢ` of the quantum group
(`LusztigCartanDatum.BraidOuterCondition` in
`LieLean/Algebra/QuantumGroup/BraidAction/GeneralArtin.lean`):

* a third node `l` meeting both ends of a simple edge `aᵢⱼ = aⱼᵢ = -1` has `aᵢₗ = aⱼₗ = -1`;
* at a double edge `aᵢⱼ = -2`, `aⱼᵢ = -1`, every third node `l` has
  `(aᵢₗ, aⱼₗ) ∈ {(0, 0), (-1, 0), (0, -1)}`;
* at a triple edge `aᵢⱼ = -3`, `aⱼᵢ = -1`, every third node is orthogonal to both ends.

## Main results

The condition holds for all of Mathlib's Cartan matrices of finite type, at every rank:
`CartanMatrix.braidOuterCondition_A`, `_B`, `_C`, `_D`, `_E` (the families `A n`, ..., `E n`,
including the degenerate small ranks), `CartanMatrix.braidOuterCondition_F₄`, `_G₂`; and for
every simply-laced matrix (`Matrix.IsSimplyLaced.braidOuterCondition`).

## References

The Cartan matrices are those of Mathlib (Bourbaki, *Lie groups and Lie algebras*, Ch. VI,
Plates I–IX). The proofs are direct computations on the explicit entries.
-/

namespace Matrix

variable {I : Type*} (A : Matrix I I ℤ)

/-- The third-node condition on the Dynkin diagram of `A` under which the braid relations of
Lusztig's `Tᵢ` are proved (see the module docstring). -/
structure BraidOuterCondition : Prop where
  simple : ∀ i j l, A i j = -1 → A j i = -1 → l ≠ i → l ≠ j →
    A i l = 0 ∨ A j l = 0 ∨ (A i l = -1 ∧ A j l = -1)
  double : ∀ i j l, A i j = -2 → A j i = -1 → l ≠ i → l ≠ j →
    (A i l = 0 ∧ A j l = 0) ∨ (A i l = -1 ∧ A j l = 0) ∨ (A i l = 0 ∧ A j l = -1)
  triple : ∀ i j l, A i j = -3 → A j i = -1 → l ≠ i → l ≠ j → A i l = 0 ∧ A j l = 0

variable {A}

/-- Every simply-laced matrix satisfies the third-node condition (for instance affine `Ãₙ`,
including the triangle `Ã₂`, and all simply-laced Kac–Moody types). -/
theorem IsSimplyLaced.braidOuterCondition (hA : A.IsSimplyLaced) : A.BraidOuterCondition where
  simple i j l _ _ hli hlj := by
    rcases hA hli.symm with h1 | h1 <;> rcases hA hlj.symm with h2 | h2 <;> simp [h1, h2]
  double i j l h h' _ _ := by
    have hij : i ≠ j := by rintro rfl; omega
    rcases hA hij with h1 | h1 <;> omega
  triple i j l h h' _ _ := by
    have hij : i ≠ j := by rintro rfl; omega
    rcases hA hij with h1 | h1 <;> omega

end Matrix

namespace CartanMatrix

/-- The third-node condition for Mathlib's `CartanMatrix.A n` (type `Aₙ₋₁`), at every rank. -/
theorem braidOuterCondition_A (n : ℕ) : (A n).BraidOuterCondition := by
  constructor <;> intro i j l h1 h2 hli hlj <;>
    simp only [A, Matrix.of_apply, Fin.ext_iff, ne_eq] at h1 h2 hli hlj ⊢ <;>
    split_ifs at h1 <;> omega

/-- The third-node condition for the Cartan matrix of type `Bₙ`, at every rank. -/
theorem braidOuterCondition_B (n : ℕ) : (B n).BraidOuterCondition := by
  constructor <;> intro i j l h1 h2 hli hlj <;>
    simp only [B, Matrix.of_apply, Fin.ext_iff, ne_eq] at h1 h2 hli hlj ⊢ <;>
    split_ifs at h1 <;> omega

/-- The third-node condition for the Cartan matrix of type `Cₙ`, at every rank. -/
theorem braidOuterCondition_C (n : ℕ) : (C n).BraidOuterCondition := by
  constructor <;> intro i j l h1 h2 hli hlj <;>
    simp only [C, Matrix.of_apply, Fin.ext_iff, ne_eq] at h1 h2 hli hlj ⊢ <;>
    split_ifs at h1 <;> omega

/-- The third-node condition for the Cartan matrix of type `Dₙ`, at every rank. -/
theorem braidOuterCondition_D (n : ℕ) : (D n).BraidOuterCondition := by
  constructor <;> intro i j l h1 h2 hli hlj <;>
    simp only [D, Matrix.of_apply, Fin.ext_iff, ne_eq] at h1 h2 hli hlj ⊢ <;>
    split_ifs at h1 <;> omega

/-- The third-node condition for Mathlib's `CartanMatrix.E n` (types `E₆`, `E₇`, `E₈`, and the
same diagram pattern at every `n`). -/
theorem braidOuterCondition_E (n : ℕ) : (E n).BraidOuterCondition := by
  constructor <;> intro i j l h1 h2 hli hlj <;>
    simp only [E, Matrix.of_apply, Fin.ext_iff, ne_eq] at h1 h2 hli hlj ⊢ <;>
    split_ifs at h1 <;> omega

/-- The third-node condition for the Cartan matrix of type `F₄`. -/
theorem braidOuterCondition_F₄ : F₄.BraidOuterCondition := by
  constructor <;> simp [F₄, Fin.forall_fin_succ]

/-- The third-node condition for the Cartan matrix of type `G₂`. -/
theorem braidOuterCondition_G₂ : G₂.BraidOuterCondition := by
  constructor <;> simp [G₂, Fin.forall_fin_succ]

end CartanMatrix
