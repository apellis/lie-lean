/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.ThreeLocalArtin
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Named simple/double Cartan families

## Main definitions and results
Graph-only contracts for the two established local constructors, and their
instantiation for the literal pinned Mathlib B, C and F₄ matrices. B and C cover
every natural rank (including the empty and rank-one degeneracies). Infinite
multiplicative order discharges all scalar cancellations in every field. The
named homomorphisms and actions use the actual quantum quotient, with arbitrary
compatible Cartan datum, symmetrizer and root-datum toral lattice.

These are length-two/three/four Artin actions, not Coxeter actions. Neither
triple-edge relations nor faithfulness of the quantum action is asserted.

## References
Reconstructed from the pinned matrix definitions and the repository's proved
local-class Artin theorem. No external primary source was consulted.
-/

namespace QuantumGroup

/-- Literal B has its directed -2 entry from the penultimate to the last node. -/
theorem cartanMatrix_B_eq_neg_two_iff {n : ℕ} (i j : Fin n) :
    CartanMatrix.B n i j = -2 ↔ i.val + 1 = j.val ∧ j.val + 1 = n := by
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> constructor <;> intro h <;> first | contradiction | omega

/-- Literal C reverses the directed double edge, without changing node labels. -/
theorem cartanMatrix_C_eq_neg_two_iff {n : ℕ} (i j : Fin n) :
    CartanMatrix.C n i j = -2 ↔ j.val + 1 = i.val ∧ i.val + 1 = n := by
  simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> constructor <;> intro h <;> first | contradiction | omega

/-- Literal F₄ has directed -2 entry at the zero-based pair (1,2). -/
theorem cartanMatrix_F₄_eq_neg_two_iff (i j : Fin 4) :
    CartanMatrix.F₄ i j = -2 ↔ i = 1 ∧ j = 2 := by
  fin_cases i <;> fin_cases j <;> norm_num [CartanMatrix.F₄]

/-- Graph-only contract of the next-edge constructor. -/
structure ThreeNextGraph {I : Type*} (A : Matrix I I ℤ) (i : I) : Prop where
  edge : ∀ j, j ≠ i → A i j = 0 ∨ (A i j = -1 ∧ A j i = -1)
  leaf : ∀ j l, A i j = -1 → A i l = -1 → j ≠ l → A j l = 0
  path : ∀ j l, A i j = -1 → A i l = 0 → A j l = 0 ∨ A j l = -1 ∨ A j l = -2

/-- Graph-only contract of the higher-double constructor. -/
structure HigherDoubleGraph {I : Type*} (A : Matrix I I ℤ) (i : I) : Prop where
  edge : ∀ j, j ≠ i → A i j = 0 ∨
    (A i j = -1 ∧ (A j i = -1 ∨ A j i = -2)) ∨ (A i j = -2 ∧ A j i = -1)
  leaf : ∀ j l, j ≠ i → l ≠ i → A i j ≠ 0 → A i l ≠ 0 → j ≠ l → A j l = 0
  unique : ∀ j l, A i j = -2 → A i l = -2 → j = l
  path : ∀ j l, A i j ≠ 0 → A i l = 0 → A j l = 0 ∨ (A j l = -1 ∧ A l j = -1)

set_option maxHeartbeats 2000000 in
-- Exhaustive conditional expansion of the symbolic-rank matrix uses arithmetic case splits.
/-- All non-double-incident nodes of literal B are next-edge nodes. -/
theorem threeNextGraph_B {n : ℕ} (i : Fin n) (hi : i.val + 2 < n) :
    ThreeNextGraph (CartanMatrix.B n) i := by
  constructor <;> intros
  all_goals
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff] at *
    split_ifs at * <;> omega

set_option maxHeartbeats 2000000 in
-- Exhaustive conditional expansion of the symbolic-rank matrix uses arithmetic case splits.
/-- The final two nodes of literal B satisfy the higher-double graph contract. -/
theorem higherDoubleGraph_B {n : ℕ} (i : Fin n) (hi : n ≤ i.val + 2) :
    HigherDoubleGraph (CartanMatrix.B n) i := by
  constructor <;> intros
  all_goals
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff] at *
    split_ifs at * <;> omega

set_option maxHeartbeats 2000000 in
-- Exhaustive conditional expansion of the symbolic-rank matrix uses arithmetic case splits.
/-- All non-double-incident nodes of literal C are next-edge nodes. -/
theorem threeNextGraph_C {n : ℕ} (i : Fin n) (hi : i.val + 2 < n) :
    ThreeNextGraph (CartanMatrix.C n) i := by
  constructor <;> intros
  all_goals
    simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff] at *
    split_ifs at * <;> omega

set_option maxHeartbeats 2000000 in
-- Exhaustive conditional expansion of the symbolic-rank matrix uses arithmetic case splits.
/-- The final two nodes of literal C satisfy the higher-double graph contract. -/
theorem higherDoubleGraph_C {n : ℕ} (i : Fin n) (hi : n ≤ i.val + 2) :
    HigherDoubleGraph (CartanMatrix.C n) i := by
  constructor <;> intros
  all_goals
    simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff] at *
    split_ifs at * <;> omega

/-- Every literal B node belongs to the proved local graph union, even in ranks 0 and 1. -/
theorem threeLocalGraph_B (n : ℕ) (i : Fin n) :
    ThreeNextGraph (CartanMatrix.B n) i ∨ HigherDoubleGraph (CartanMatrix.B n) i := by
  by_cases hi : i.val + 2 < n
  · exact Or.inl (threeNextGraph_B i hi)
  · exact Or.inr (higherDoubleGraph_B i (by omega))

/-- Every literal C node belongs to the proved local graph union, even in ranks 0 and 1. -/
theorem threeLocalGraph_C (n : ℕ) (i : Fin n) :
    ThreeNextGraph (CartanMatrix.C n) i ∨ HigherDoubleGraph (CartanMatrix.C n) i := by
  by_cases hi : i.val + 2 < n
  · exact Or.inl (threeNextGraph_C i hi)
  · exact Or.inr (higherDoubleGraph_C i (by omega))

/-- The two endpoints of literal F₄ satisfy the next-edge graph contract. -/
theorem threeNextGraph_F₄ (i : Fin 4) (hi : i = 0 ∨ i = 3) :
    ThreeNextGraph CartanMatrix.F₄ i := by
  rcases hi with rfl | rfl <;> constructor <;>
    norm_num [CartanMatrix.F₄, Fin.forall_fin_succ]

/-- The two double-incident nodes of literal F₄ satisfy the higher-double contract. -/
theorem higherDoubleGraph_F₄ (i : Fin 4) (hi : i = 1 ∨ i = 2) :
    HigherDoubleGraph CartanMatrix.F₄ i := by
  rcases hi with rfl | rfl <;> constructor <;>
    norm_num [CartanMatrix.F₄, Fin.forall_fin_succ]

/-- Every literal F₄ node belongs to the proved local graph union. -/
theorem threeLocalGraph_F₄ (i : Fin 4) :
    ThreeNextGraph CartanMatrix.F₄ i ∨ HigherDoubleGraph CartanMatrix.F₄ i := by
  fin_cases i
  · exact Or.inl (threeNextGraph_F₄ 0 (Or.inl rfl))
  · exact Or.inr (higherDoubleGraph_F₄ 1 (Or.inl rfl))
  · exact Or.inr (higherDoubleGraph_F₄ 2 (Or.inr rfl))
  · exact Or.inl (threeNextGraph_F₄ 3 (Or.inr rfl))

section Scalars
variable {k : Type*} [Field k] {q : k}

/-- All scalar cancellations of the local-class constructors. -/
structure ThreeLocalScalars (q : k) : Prop where
  diff : q - q⁻¹ ≠ 0
  sum : q + q⁻¹ ≠ 0
  cycl : (1 + q⁻¹ ^ 4) * (1 + q⁻¹ ^ 2 + q⁻¹ ^ 4) ≠ 0
  cube : q ^ 4 + q ^ 2 + 1 ≠ 0

/-- Infinite multiplicative order discharges every local scalar restriction.
The argument uses only the powers 2, 4, 6 and 8, and works in any field. -/
theorem threeLocalScalars_of_not_root (hq : q ≠ 0)
    (hpow : ∀ m : ℕ, 0 < m → q ^ m ≠ 1) : ThreeLocalScalars q := by
  constructor
  · intro h
    apply hpow 2 (by decide)
    linear_combination (norm := (field_simp [hq]; ring)) q * h
  · intro h
    apply hpow 4 (by decide)
    linear_combination (norm := (field_simp [hq]; ring)) (q ^ 3 - q) * h
  · apply mul_ne_zero
    · intro h
      apply hpow 8 (by decide)
      linear_combination (norm := (field_simp [hq]; ring)) (q ^ 8 - q ^ 4) * h
    · intro h
      apply hpow 6 (by decide)
      linear_combination (norm := (field_simp [hq]; ring)) (q ^ 6 - q ^ 4) * h
  · intro h
    apply hpow 6 (by decide)
    linear_combination (q ^ 2 - 1) * h

/-- Genericity at the global parameter implies all required local cancellations,
with the original positive symmetrizer left unchanged. -/
theorem threeLocalScalars_pow {I : Type*} (D : LusztigCartanDatum I) {v : k}
    (hv : v ≠ 0) (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) (i : I) :
    ThreeLocalScalars (v ^ D.d i) := by
  apply threeLocalScalars_of_not_root (pow_ne_zero _ hv)
  intro m hm
  rw [← pow_mul]
  exact hpow _ (Nat.mul_pos (D.d_pos i) hm)

end Scalars

/-- The graph union plus scalar nonvanishing supplies the exact existing local data. -/
theorem threeLocalData_of_graph {k I : Type*} [Field k] (D : LusztigCartanDatum I)
    {v : k} (i : I)
    (H : ThreeNextGraph D.cartanMatrix i ∨ HigherDoubleGraph D.cartanMatrix i)
    (hs : ThreeLocalScalars (v ^ D.d i)) : ThreeLocalData D v i := by
  rcases H with H | H
  · exact Or.inl ⟨H.edge, H.leaf, H.path, hs.diff, hs.sum, hs.cube⟩
  · exact Or.inr ⟨H.edge, H.leaf, H.unique, H.path, hs.diff, hs.sum, hs.cycl, hs.cube⟩

noncomputable section Families
variable {k Y : Type*} [Field k] [AddCommGroup Y] {v : k} [NeZero v]

/-- Actual all-node local data for literal B, with arbitrary compatible symmetrizer.
Only nonzero parameter and absence of positive roots of unity are needed. -/
theorem threeLocalData_B {n : ℕ} (D : LusztigCartanDatum (Fin n))
    (hD : D.cartanMatrix = (CartanMatrix.B n))
    (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) (i : Fin n) : ThreeLocalData D v i := by
  apply threeLocalData_of_graph D i
  · rw [hD]
    exact threeLocalGraph_B n i
  · exact threeLocalScalars_pow D (NeZero.ne v) hpow i

/-- The actual algebra-automorphism-valued Artin representation for literal B.
The compatible root datum and its entire toral lattice are arbitrary. -/
def artinHom_B {n : ℕ} {D : LusztigCartanDatum (Fin n)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = (CartanMatrix.B n))
    (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) :
    SimpleDoubleArtinGroup D →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  threeLocalArtinHom (R := R) (threeLocalData_B D hD hpow)

/-- Evaluation gives the genuine literal B Artin action on the quantum quotient. -/
abbrev artinAction_B {n : ℕ} {D : LusztigCartanDatum (Fin n)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = (CartanMatrix.B n))
    (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) :
    MulSemiringAction (SimpleDoubleArtinGroup D) (QuantumGroup R v) :=
  MulSemiringAction.compHom (QuantumGroup R v) (artinHom_B R hD hpow)

/-- All Chevalley and arbitrary toral generator formulas for the literal B action. -/
theorem artinHom_B_images {n : ℕ} {D : LusztigCartanDatum (Fin n)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = (CartanMatrix.B n))
    (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) (i : Fin n) :
    HasBraidGeneratorImages i
      (artinHom_B R hD hpow (SimpleDoubleArtinGroup.generator i)).toAlgHom :=
  threeLocalArtinHom_images (threeLocalData_B D hD hpow) i

/-- Actual all-node local data for literal C, with arbitrary compatible symmetrizer.
Only nonzero parameter and absence of positive roots of unity are needed. -/
theorem threeLocalData_C {n : ℕ} (D : LusztigCartanDatum (Fin n))
    (hD : D.cartanMatrix = (CartanMatrix.C n))
    (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) (i : Fin n) : ThreeLocalData D v i := by
  apply threeLocalData_of_graph D i
  · rw [hD]
    exact threeLocalGraph_C n i
  · exact threeLocalScalars_pow D (NeZero.ne v) hpow i

/-- The actual algebra-automorphism-valued Artin representation for literal C.
The compatible root datum and its entire toral lattice are arbitrary. -/
def artinHom_C {n : ℕ} {D : LusztigCartanDatum (Fin n)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = (CartanMatrix.C n))
    (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) :
    SimpleDoubleArtinGroup D →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  threeLocalArtinHom (R := R) (threeLocalData_C D hD hpow)

/-- Evaluation gives the genuine literal C Artin action on the quantum quotient. -/
abbrev artinAction_C {n : ℕ} {D : LusztigCartanDatum (Fin n)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = (CartanMatrix.C n))
    (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) :
    MulSemiringAction (SimpleDoubleArtinGroup D) (QuantumGroup R v) :=
  MulSemiringAction.compHom (QuantumGroup R v) (artinHom_C R hD hpow)

/-- All Chevalley and arbitrary toral generator formulas for the literal C action. -/
theorem artinHom_C_images {n : ℕ} {D : LusztigCartanDatum (Fin n)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = (CartanMatrix.C n))
    (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) (i : Fin n) :
    HasBraidGeneratorImages i
      (artinHom_C R hD hpow (SimpleDoubleArtinGroup.generator i)).toAlgHom :=
  threeLocalArtinHom_images (threeLocalData_C D hD hpow) i

/-- Actual all-node local data for literal F₄, with arbitrary compatible symmetrizer.
Only nonzero parameter and absence of positive roots of unity are needed. -/
theorem threeLocalData_F₄ (D : LusztigCartanDatum (Fin 4))
    (hD : D.cartanMatrix = CartanMatrix.F₄)
    (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) (i : Fin 4) : ThreeLocalData D v i := by
  apply threeLocalData_of_graph D i
  · rw [hD]
    exact threeLocalGraph_F₄ i
  · exact threeLocalScalars_pow D (NeZero.ne v) hpow i

/-- The actual algebra-automorphism-valued Artin representation for literal F₄.
The compatible root datum and its entire toral lattice are arbitrary. -/
def artinHom_F₄ {D : LusztigCartanDatum (Fin 4)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.F₄)
    (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) :
    SimpleDoubleArtinGroup D →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  threeLocalArtinHom (R := R) (threeLocalData_F₄ D hD hpow)

/-- Evaluation gives the genuine literal F₄ Artin action on the quantum quotient. -/
abbrev artinAction_F₄ {D : LusztigCartanDatum (Fin 4)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.F₄)
    (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) :
    MulSemiringAction (SimpleDoubleArtinGroup D) (QuantumGroup R v) :=
  MulSemiringAction.compHom (QuantumGroup R v) (artinHom_F₄ R hD hpow)

/-- All Chevalley and arbitrary toral generator formulas for the literal F₄ action. -/
theorem artinHom_F₄_images {D : LusztigCartanDatum (Fin 4)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.F₄)
    (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) (i : Fin 4) :
    HasBraidGeneratorImages i
      (artinHom_F₄ R hD hpow (SimpleDoubleArtinGroup.generator i)).toAlgHom :=
  threeLocalArtinHom_images (threeLocalData_F₄ D hD hpow) i

end Families

end QuantumGroup
