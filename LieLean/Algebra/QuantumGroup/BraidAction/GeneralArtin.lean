/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.BraidRelationsGeneral
import LieLean.Algebra.QuantumGroup.BraidAction.DoubleEdgeGeneral
import LieLean.Algebra.QuantumGroup.BraidAction.TriangleRelation
import LieLean.GroupTheory.Coxeter.ArtinGroup
import LieLean.GroupTheory.Coxeter.Matsumoto
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroupCoxeter

/-!
# The Artin group action on `U` for a class of Cartan data of arbitrary rank

Let `D` be a Cartan datum with Cartan matrix `A` and Coxeter matrix `M = A.coxeterMatrix`
(`mᵢⱼ = 2, 3, 4, 6, ∞` for `aᵢⱼ aⱼᵢ = 0, 1, 2, 3, ≥ 4`). The general braid automorphisms
`Tᵢ = braidEquivOfGeneric` of `BraidAction/GeneralSerre.lean` satisfy the braid relations of `M`,
hence define an action of the Artin group `M.ArtinGroup` on `U` by algebra automorphisms, as soon
as `D` satisfies `LusztigCartanDatum.BraidOuterCondition`:

* a third node `l` meeting both ends of a simple edge (`aᵢⱼ = aⱼᵢ = -1`) has
  `aᵢₗ = aⱼₗ = -1` (a triangle; `aₗᵢ`, `aₗⱼ` arbitrary);
* at a double edge `aᵢⱼ = -2`, `aⱼᵢ = -1`, every third node `l` has
  `(aᵢₗ, aⱼₗ) ∈ {(0, 0), (-1, 0), (0, -1)}`;
* at a triple edge `aᵢⱼ = -3`, `aⱼᵢ = -1`, every third node is orthogonal to both ends.

Edges with `aᵢⱼ aⱼᵢ ≥ 4` impose no relation. By inspection of the Dynkin diagrams (not formalized
here) the condition holds for every Cartan datum of finite type; it imposes no bound on the rank
and allows, e.g., the cycles of affine type `Ãₙ`, `n ≥ 2` (including the triangle `Ã₂`). It
excludes third nodes meeting both ends of a simple edge with an entry `≤ -2` in the row of an end,
third nodes attached to a double edge by a multiple bond in the row of the double-edge node or
meeting both of its ends, and triple edges with neighbours (e.g. `G̃₂`); for these the braid
relations are not proved here.

## Main definitions / results

* `LusztigCartanDatum.BraidOuterCondition`: the graph condition above.
* `QuantumGroup.isBraidLiftable_braidEquivOfGeneric`: the `Tᵢ` satisfy the braid relations of
  `A.coxeterMatrix` (`CoxeterMatrix.IsBraidLiftable`); in particular Matsumoto's theorem
  (`CoxeterSystem.braidLift`) defines `T_w` for `w` in the Weyl group.
* `QuantumGroup.braidArtinHom`: the Artin group action `A.coxeterMatrix.ArtinGroup →* Aut U`,
  `σᵢ ↦ Tᵢ`, assuming `vᵢ - vᵢ⁻¹ ≠ 0`, `BraidSerreGeneric` and `[3]ᵢ! ≠ 0` at every node.
* `QuantumGroup.braidArtinHomOfNotRoot`: the same when `v` is not a root of unity.

## References

G. Lusztig, *Introduction to quantum groups*, 39.4.3. Reconstructed: the relations are
proved in `BraidAction/BraidRelationsGeneral.lean`, `BraidAction/DoubleEdgeGeneral.lean` and
`BraidAction/GeneralRelations.lean`.
-/

open LieLean

noncomputable section

namespace LusztigCartanDatum

variable {I : Type*} (D : LusztigCartanDatum I)

/-- The graph condition under which the braid relations of the general `Tᵢ` are proved here:
a third node meeting both ends of a simple edge does so with entries `-1` in their rows; the
third nodes at a double edge are attached to
one end only, by an entry `-1` in the row of that end; triple edges are isolated. -/
structure BraidOuterCondition : Prop where
  simple : ∀ i j l, D.cartanMatrix i j = -1 → D.cartanMatrix j i = -1 → l ≠ i → l ≠ j →
    D.cartanMatrix i l = 0 ∨ D.cartanMatrix j l = 0 ∨
      (D.cartanMatrix i l = -1 ∧ D.cartanMatrix j l = -1)
  double : ∀ i j l, D.cartanMatrix i j = -2 → D.cartanMatrix j i = -1 → l ≠ i → l ≠ j →
    (D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = 0) ∨
    (D.cartanMatrix i l = -1 ∧ D.cartanMatrix j l = 0) ∨
    (D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = -1)
  triple : ∀ i j l, D.cartanMatrix i j = -3 → D.cartanMatrix j i = -1 → l ≠ i → l ≠ j →
    D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = 0

end LusztigCartanDatum

namespace LieLean.QuantumGroup

open CoxeterSystem

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k}

omit [DecidableEq I] in
/-- The possible pairs of off-diagonal Cartan entries with a given small product. -/
lemma cartan_entries_of_mul {i j : I} (hij : i ≠ j) {n : ℤ} (hn : 0 < n) (hn3 : n ≤ 3)
    (h : D.cartanMatrix i j * D.cartanMatrix j i = n) :
    -n ≤ D.cartanMatrix i j ∧ -n ≤ D.cartanMatrix j i ∧ D.cartanMatrix i j < 0 ∧
      D.cartanMatrix j i < 0 := by
  have hA := D.isGeneralizedCartan_cartanMatrix
  have hx := hA.offDiag_nonpos i j hij
  have hy := hA.offDiag_nonpos j i hij.symm
  have hx0 : D.cartanMatrix i j ≠ 0 := by rintro h0; rw [h0, zero_mul] at h; omega
  have hy0 : D.cartanMatrix j i ≠ 0 := by rintro h0; rw [h0, mul_zero] at h; omega
  have e1 := mul_nonneg_of_nonpos_of_nonpos hx (show D.cartanMatrix j i + 1 ≤ 0 by omega)
  have e2 := mul_nonneg_of_nonpos_of_nonpos hy (show D.cartanMatrix i j + 1 ≤ 0 by omega)
  refine ⟨?_, ?_, by omega, by omega⟩ <;> nlinarith

omit [DecidableEq I] in
/-- `vᵢ + vᵢ⁻¹ ≠ 0` follows from `[3]ᵢ! ≠ 0`. -/
lemma sum_ne_zero_of_qFactorial_three {q : k} (hq : q ≠ 0) (h3 : qFactorial q 3 ≠ 0) :
    q + q⁻¹ ≠ 0 := by
  rw [tripleSix_qFactorial_three hq] at h3
  exact right_ne_zero_of_mul h3

variable [NeZero v] (hq : ∀ i, v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hS : ∀ i, BraidSerreGeneric D v i) (h3 : ∀ i, qFactorial (v ^ D.d i) 3 ≠ 0)
  (hD : D.BraidOuterCondition)

include h3 hD in
/-- **The braid relations for Lusztig's `Tᵢ` in arbitrary rank**: under
`BraidOuterCondition`, the automorphisms `braidEquivOfGeneric` satisfy the braid relations of the
Coxeter matrix of the Cartan matrix. -/
theorem isBraidLiftable_braidEquivOfGeneric :
    D.cartanMatrix.coxeterMatrix.IsBraidLiftable
      (fun i ↦ braidEquivOfGeneric (R := R) (hq i) (hS i)) := by
  intro i j hij hm
  set T : I → (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
    fun i ↦ braidEquivOfGeneric (R := R) (hq i) (hS i) with hT
  have hA := D.isGeneralizedCartan_cartanMatrix
  have hMij := Matrix.coxeterMatrix_apply_of_ne D.cartanMatrix hij
  have hMji := Matrix.coxeterMatrix_apply_of_ne D.cartanMatrix hij.symm
  rw [mul_comm (D.cartanMatrix j i)] at hMji
  have hp0 : 0 ≤ D.cartanMatrix i j * D.cartanMatrix j i := hA.mul_nonneg hij
  have hg (l : I) := braidGeneric_of_braidSerreGeneric (hq l) (hS l)
  have hs (l : I) := sum_ne_zero_of_qFactorial_three (pow_ne_zero (D.d l) (NeZero.ne v)) (h3 l)
  simp only [braidWord, hMij, hMji] at hm ⊢
  rcases (show (D.cartanMatrix i j * D.cartanMatrix j i).toNat = 0 ∨
      (D.cartanMatrix i j * D.cartanMatrix j i).toNat = 1 ∨
      (D.cartanMatrix i j * D.cartanMatrix j i).toNat = 2 ∨
      (D.cartanMatrix i j * D.cartanMatrix j i).toNat = 3 ∨
      4 ≤ (D.cartanMatrix i j * D.cartanMatrix j i).toNat by omega)
    with hp | hp | hp | hp | hp
  · -- orthogonal nodes: length two
    have h0 : D.cartanMatrix i j = 0 := by
      rcases mul_eq_zero.1 (show D.cartanMatrix i j * D.cartanMatrix j i = 0 by omega) with
        h0 | h0
      · exact h0
      · exact (hA.zero_comm i j).2 h0
    rw [hp]
    simp only [Matrix.coxeterEntry, alternatingWord, List.concat_eq_append, List.nil_append,
      List.cons_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact braidEquiv_comm (hg i) _ (hg j) _ hij h0
  · -- simple edge: length three
    have e : D.cartanMatrix i j * D.cartanMatrix j i = 1 := by omega
    obtain ⟨b1, b2, b3, b4⟩ := cartan_entries_of_mul hij (by norm_num) (by norm_num) e
    have h1 : D.cartanMatrix i j = -1 := by omega
    have h1' : D.cartanMatrix j i = -1 := by omega
    rw [hp]
    simp only [Matrix.coxeterEntry, alternatingWord, List.concat_eq_append, List.nil_append,
      List.cons_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      ← mul_assoc]
    refine (braidEquiv_braid_three_triangle (hg i) _ (hg j) _ hij h1 h1'
      (fun l hli hlj ↦ ?_)).symm
    rcases hD.simple i j l h1 h1' hli hlj with h0 | h0 | ⟨hil, hjl⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr ⟨hil, hjl, hs i⟩)
  · -- double edge: length four
    have e : D.cartanMatrix i j * D.cartanMatrix j i = 2 := by omega
    obtain ⟨b1, b2, b3, b4⟩ := cartan_entries_of_mul hij (by norm_num) (by norm_num) e
    rw [hp]
    simp only [Matrix.coxeterEntry, alternatingWord, List.concat_eq_append, List.nil_append,
      List.cons_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      ← mul_assoc]
    rcases (show (D.cartanMatrix i j = -2 ∧ D.cartanMatrix j i = -1) ∨
        (D.cartanMatrix i j = -1 ∧ D.cartanMatrix j i = -2) by
      interval_cases h : D.cartanMatrix i j <;> omega) with ⟨h2, h1⟩ | ⟨h1, h2⟩
    · exact braidEquiv_braid_four (hg i) _ (hg j) _ hij h2 h1 (hs i) (hs j)
        (fun l hli hlj ↦ hD.double i j l h2 h1 hli hlj)
    · exact (braidEquiv_braid_four (hg j) _ (hg i) _ hij.symm h2 h1 (hs j) (hs i)
        (fun l hlj hli ↦ hD.double j i l h2 h1 hlj hli)).symm
  · -- triple edge: length six
    have e : D.cartanMatrix i j * D.cartanMatrix j i = 3 := by omega
    obtain ⟨b1, b2, b3, b4⟩ := cartan_entries_of_mul hij (by norm_num) (by norm_num) e
    rw [hp]
    simp only [Matrix.coxeterEntry, alternatingWord, List.concat_eq_append, List.nil_append,
      List.cons_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      ← mul_assoc]
    rcases (show (D.cartanMatrix i j = -3 ∧ D.cartanMatrix j i = -1) ∨
        (D.cartanMatrix i j = -1 ∧ D.cartanMatrix j i = -3) by
      interval_cases h : D.cartanMatrix i j <;> omega) with ⟨h3', h1⟩ | ⟨h1, h3'⟩
    · exact braidEquiv_braid_six_of_orthogonal (hg i) _ (hg j) _ hij h3' h1 (h3 i)
        (fun l hli hlj ↦ hD.triple i j l h3' h1 hli hlj)
    · exact (braidEquiv_braid_six_of_orthogonal (hg j) _ (hg i) _ hij.symm h3' h1 (h3 j)
        (fun l hlj hli ↦ hD.triple j i l h3' h1 hlj hli)).symm
  · -- no relation
    exact absurd (Matrix.coxeterEntry_of_four_le hp) hm

/-- **The Artin group action on `U`**: under `BraidOuterCondition`,
`σᵢ ↦ Tᵢ = braidEquivOfGeneric` defines a homomorphism from the Artin group of the Coxeter
matrix of `D` to the algebra automorphisms of `U`. Assumes `v ≠ 0`, `vᵢ - vᵢ⁻¹ ≠ 0`,
`BraidSerreGeneric` and `[3]ᵢ! ≠ 0` at every node. -/
def braidArtinHom :
    D.cartanMatrix.coxeterMatrix.ArtinGroup →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  CoxeterMatrix.artinLift (fun i ↦ braidEquivOfGeneric (R := R) (hq i) (hS i))
    (isBraidLiftable_braidEquivOfGeneric hq hS h3 hD)

@[simp]
theorem braidArtinHom_artinGenerator (i : I) :
    braidArtinHom (R := R) hq hS h3 hD (D.cartanMatrix.coxeterMatrix.artinGenerator i) =
      braidEquivOfGeneric (hq i) (hS i) :=
  CoxeterMatrix.artinLift_artinGenerator _ _ i

omit hq hS h3

variable (R) in
/-- **The Artin group action on `U` at a generic parameter**: if `v` is not a root of unity,
`σᵢ ↦ Tᵢ = braidEquivOfNotRoot` is an action of the Artin group of the Coxeter matrix of any
Cartan datum satisfying `BraidOuterCondition`, in arbitrary rank. -/
def braidArtinHomOfNotRoot (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    D.cartanMatrix.coxeterMatrix.ArtinGroup →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  braidArtinHom (fun i ↦ (shortNode_braidGeneric_of_not_root hv' i).sub_ne)
    (braidSerreGeneric_of_not_root hv')
    (fun i ↦ LusztigF.qFactorial_ne_zero_of_not_root (NeZero.ne v) hv' i 3) hD

@[simp]
theorem braidArtinHomOfNotRoot_artinGenerator (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i : I) :
    braidArtinHomOfNotRoot R hD hv' (D.cartanMatrix.coxeterMatrix.artinGenerator i) =
      braidEquivOfNotRoot R hv' i :=
  braidArtinHom_artinGenerator _ _ _ hD i

end LieLean.QuantumGroup
