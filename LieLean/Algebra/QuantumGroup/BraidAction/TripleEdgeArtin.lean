/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.TripleEdgeRelation
import LieLean.Algebra.QuantumGroup.BraidAction.TwoNodeGeneral
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# The braid group action of type `G₂`

The Artin group of type `G₂` has two generators and a single relator of length six, with no
involution relations. For an exact two-node Cartan datum with entries `aᵢⱼ = -3`, `aⱼᵢ = -1`,
the automorphisms `tripleEdgeBraidEquiv` (at `i`) and `tripleEdgeOtherBraidEquiv` (at `j`)
satisfy the length-six relation (`tripleEdgeBraidEquiv_braid_six`), hence define an action of
this Artin group on `U` by algebra automorphisms, with Lusztig's generator formulas.

## Main definitions and results

* `TripleEdgeArtinGroup i j`: the presented group `⟨i, j | ijijij = jijiji⟩` (over the free group
  on the index type), with `lift`, `lift_unique` and `generator_sq_ne_one`.
* `QuantumGroup.tripleEdgeArtinHomOfBraid`: the action for `braidEquiv` at both nodes of an exact
  two-node `G₂` datum (any transformed-Serre proofs), with all generator formulas
  (`tripleEdgeArtinHomOfBraid_images_left/right`).
* `QuantumGroup.tripleEdgeArtinHom`, `QuantumGroup.tripleEdgeArtinAction`: the action by the
  named automorphisms `tripleEdgeBraidEquiv`, `tripleEdgeOtherBraidEquiv`, under their
  hypotheses (`vᵢ - vᵢ⁻¹ ≠ 0`, `[3]ᵢ! ≠ 0`, `vᵢ⁴ + 1 ≠ 0`, `vⱼ² + 1 ≠ 0`).
* `QuantumGroup.tripleEdgeArtinHom_of_not_root`: the action by `twoNodeBraidEquiv_of_not_root`
  at both nodes, assuming only that `v ≠ 0` is not a root of unity.
* `QuantumGroup.artinHom_G₂`, `QuantumGroup.artinAction_G₂`, `QuantumGroup.artinHom_G₂_images`:
  the action for a Cartan datum whose matrix is Mathlib's literal `CartanMatrix.G₂` (node `0`
  short with `a₀₁ = -3`, node `1` long), for any `v ≠ 0` that is not a root of unity, over any
  field and root-datum lattice.

Faithfulness of the action is not asserted.

## References

The braid group action is [Lus] 39.4.3 (check), [Jan] 8.18 (check); the construction here is
reconstructed from the repository's automorphisms and length-six relation.
-/

/-- The length-six braid relator `ijijij (jijiji)⁻¹` in the free group. -/
def tripleEdgeArtinRelator {I : Type*} (i j : I) : FreeGroup I :=
  (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
      FreeGroup.of j) *
    (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j * FreeGroup.of i * FreeGroup.of j *
      FreeGroup.of i)⁻¹

/-- The Artin group of type `G₂` (dihedral type `I₂(6)`) on the nodes `i, j`: one relator of
length six, no involution relators. (For an index type with more than two elements the other
generators are free.) -/
abbrev TripleEdgeArtinGroup {I : Type*} (i j : I) :=
  PresentedGroup ({tripleEdgeArtinRelator i j} : Set (FreeGroup I))

namespace TripleEdgeArtinGroup

variable {I : Type*} {i j : I}

/-- The Artin generator at a node. -/
def generator (l : I) : TripleEdgeArtinGroup i j := PresentedGroup.of l

/-- The defining length-six relation. -/
theorem generator_six :
    generator (i := i) (j := j) i * generator j * generator i * generator j * generator i *
        generator j =
      generator j * generator i * generator j * generator i * generator j * generator i :=
  PresentedGroup.mk_eq_mk_of_mul_inv_mem rfl

variable {G : Type*} [Group G] (f : I → G)
  (h6 : f i * f j * f i * f j * f i * f j = f j * f i * f j * f i * f j * f i)

/-- Universal property: a map of the nodes satisfying the length-six relation lifts. -/
def lift : TripleEdgeArtinGroup i j →* G :=
  PresentedGroup.toGroup (f := f) (by
    rintro r rfl
    simp only [tripleEdgeArtinRelator, map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [h6, mul_inv_cancel])

@[simp] theorem lift_generator (l : I) : lift f h6 (generator l) = f l :=
  PresentedGroup.toGroup.of _

/-- The lift is determined by its generator images. -/
theorem lift_unique (g : TripleEdgeArtinGroup i j →* G) (hg : ∀ l, g (generator l) = f l) :
    g = lift f h6 := by
  apply PresentedGroup.ext
  intro l
  exact (hg l).trans (lift_generator f h6 l).symm

/-- The total exponent sum: the relator has exponent sum zero. -/
def exponentSum : TripleEdgeArtinGroup i j →* Multiplicative ℤ :=
  lift (fun _ ↦ Multiplicative.ofAdd (1 : ℤ)) rfl

@[simp] theorem exponentSum_generator (l : I) :
    exponentSum (generator (i := i) (j := j) l) = Multiplicative.ofAdd (1 : ℤ) :=
  lift_generator _ _ l

/-- The generators are not involutions (no Coxeter relations are imposed). -/
theorem generator_sq_ne_one (l : I) : generator (i := i) (j := j) l ^ 2 ≠ 1 := by
  intro h
  have hh := congrArg (fun g ↦ (exponentSum g).toAdd) h
  simp at hh

end TripleEdgeArtinGroup

noncomputable section

namespace QuantumGroup

section Action

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  {i j : I} (hij : i ≠ j) (hall : ∀ l, l = i ∨ l = j)
  (h : D.cartanMatrix i j = -3) (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) (h3 : qFactorial (v ^ D.d i) 3 ≠ 0)
  (h4 : (v ^ D.d i) ^ 4 + 1 ≠ 0) (h2 : (v ^ D.d j) ^ 2 + 1 ≠ 0)

/-- The automorphism attached to a node of an exact `G₂` datum. -/
def tripleEdgeNodeEquiv (l : I) : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  if l = i then tripleEdgeBraidEquiv (R := R) hij hall h h' hq h3 h4
  else tripleEdgeOtherBraidEquiv (R := R) hij.symm (fun l ↦ (hall l).symm) h' h
    (tripleSix_sub_ne h h' hq h3) h2

/-- **The braid group action of type `G₂`**: the Artin group acts on `U` by algebra
automorphisms, `i ↦ tripleEdgeBraidEquiv`, `j ↦ tripleEdgeOtherBraidEquiv`. -/
def tripleEdgeArtinHom :
    TripleEdgeArtinGroup i j →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  TripleEdgeArtinGroup.lift (tripleEdgeNodeEquiv (R := R) hij hall h h' hq h3 h4 h2) (by
    simp only [tripleEdgeNodeEquiv, hij.symm, ↓reduceIte]
    exact tripleEdgeBraidEquiv_braid_six hij h h' hq h3 hall h4 h2)

/-- Evaluation of the representation gives the `G₂` Artin action on `U`. -/
abbrev tripleEdgeArtinAction : MulSemiringAction (TripleEdgeArtinGroup i j) (QuantumGroup R v) :=
  MulSemiringAction.compHom (QuantumGroup R v)
    (tripleEdgeArtinHom (R := R) hij hall h h' hq h3 h4 h2)

@[simp] theorem tripleEdgeArtinHom_generator_left :
    tripleEdgeArtinHom (R := R) hij hall h h' hq h3 h4 h2 (TripleEdgeArtinGroup.generator i) =
      tripleEdgeBraidEquiv (R := R) hij hall h h' hq h3 h4 := by
  simp [tripleEdgeArtinHom, tripleEdgeNodeEquiv]

@[simp] theorem tripleEdgeArtinHom_generator_right :
    tripleEdgeArtinHom (R := R) hij hall h h' hq h3 h4 h2 (TripleEdgeArtinGroup.generator j) =
      tripleEdgeOtherBraidEquiv (R := R) hij.symm (fun l ↦ (hall l).symm) h' h
        (tripleSix_sub_ne h h' hq h3) h2 := by
  simp [tripleEdgeArtinHom, tripleEdgeNodeEquiv, hij.symm]

/-- All generator formulas (Chevalley generators and every toral lattice element) for the
generator at the short node. -/
theorem tripleEdgeArtinHom_images_left :
    HasBraidGeneratorImages i
      (tripleEdgeArtinHom (R := R) hij hall h h' hq h3 h4 h2
        (TripleEdgeArtinGroup.generator i)).toAlgHom := by
  rw [tripleEdgeArtinHom_generator_left]
  exact braidHom_hasBraidGeneratorImages (tripleEdge_braidGeneric hij hall h hq h3)
    (tripleEdge_transformedSerre hij hall h h' h4)

/-- All generator formulas for the generator at the long node. -/
theorem tripleEdgeArtinHom_images_right :
    HasBraidGeneratorImages j
      (tripleEdgeArtinHom (R := R) hij hall h h' hq h3 h4 h2
        (TripleEdgeArtinGroup.generator j)).toAlgHom := by
  rw [tripleEdgeArtinHom_generator_right]
  exact braidHom_hasBraidGeneratorImages
    (degreeOne_braidGeneric (fun l ↦ (hall l).symm) h' (tripleSix_sub_ne h h' hq h3))
    (tripleEdgeOther_transformedSerre hij.symm (fun l ↦ (hall l).symm) h' h
      (tripleSix_sub_ne h h' hq h3) h2)

end Action

section Generic

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  {i j : I} (hij : i ≠ j) (hall : ∀ l, l = i ∨ l = j)
  (h : D.cartanMatrix i j = -3) (h' : D.cartanMatrix j i = -1)
  (hgi : BraidGeneric D v i) (hSi : TransformedSerre R v i)
  (hgj : BraidGeneric D v j) (hSj : TransformedSerre R v j)

/-- **The `G₂` Artin action from any braid automorphisms at the two nodes**: for
`braidEquiv` at `i` and at `j` (whatever transformed-Serre proofs they are built from), the
length-six relation holds, so they define an action of the `G₂` Artin group. -/
def tripleEdgeArtinHomOfBraid :
    TripleEdgeArtinGroup i j →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  TripleEdgeArtinGroup.lift
    (fun l ↦ if l = i then braidEquiv hgi hSi else braidEquiv hgj hSj) (by
      simp only [hij.symm, ↓reduceIte]
      have h3 := hgi.qFactorial_ne j hij.symm
      rw [tripleSix_negA h] at h3
      exact braidEquiv_braid_six_of_triple_edge hij h h' hgi.sub_ne h3 hall hgi hSi hgj hSj)

@[simp] theorem tripleEdgeArtinHomOfBraid_generator_left :
    tripleEdgeArtinHomOfBraid hij hall h h' hgi hSi hgj hSj
      (TripleEdgeArtinGroup.generator i) = braidEquiv hgi hSi := by
  simp [tripleEdgeArtinHomOfBraid]

@[simp] theorem tripleEdgeArtinHomOfBraid_generator_right :
    tripleEdgeArtinHomOfBraid hij hall h h' hgi hSi hgj hSj
      (TripleEdgeArtinGroup.generator j) = braidEquiv hgj hSj := by
  simp [tripleEdgeArtinHomOfBraid, hij.symm]

/-- All generator formulas at the short node. -/
theorem tripleEdgeArtinHomOfBraid_images_left :
    HasBraidGeneratorImages i
      (tripleEdgeArtinHomOfBraid hij hall h h' hgi hSi hgj hSj
        (TripleEdgeArtinGroup.generator i)).toAlgHom := by
  rw [tripleEdgeArtinHomOfBraid_generator_left]
  exact braidHom_hasBraidGeneratorImages hgi hSi

/-- All generator formulas at the long node. -/
theorem tripleEdgeArtinHomOfBraid_images_right :
    HasBraidGeneratorImages j
      (tripleEdgeArtinHomOfBraid hij hall h h' hgi hSi hgj hSj
        (TripleEdgeArtinGroup.generator j)).toAlgHom := by
  rw [tripleEdgeArtinHomOfBraid_generator_right]
  exact braidHom_hasBraidGeneratorImages hgj hSj

omit hgi hSi hgj hSj

/-- **The `G₂` braid group action at a parameter that is not a root of unity**, built from
`twoNodeBraidEquiv_of_not_root` at both nodes; only `v ≠ 0` and
`∀ n > 0, vⁿ ≠ 1` are assumed. -/
def tripleEdgeArtinHom_of_not_root (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    TripleEdgeArtinGroup i j →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  tripleEdgeArtinHomOfBraid hij hall h h'
    (twoNode_braidGeneric hij hall (shortNode_braidGeneric_of_not_root hv' i).sub_ne
      (twoNode_qFactorial_ne_zero_of_not_root hv' i j))
    (twoNode_transformedSerre hij hall (shortNode_braidGeneric_of_not_root hv' i).sub_ne
      (twoNode_qFactorial_ne_zero_of_not_root hv' i j))
    (twoNode_braidGeneric hij.symm (fun l ↦ (hall l).symm)
      (shortNode_braidGeneric_of_not_root hv' j).sub_ne
      (twoNode_qFactorial_ne_zero_of_not_root hv' j i))
    (twoNode_transformedSerre hij.symm (fun l ↦ (hall l).symm)
      (shortNode_braidGeneric_of_not_root hv' j).sub_ne
      (twoNode_qFactorial_ne_zero_of_not_root hv' j i))

@[simp] theorem tripleEdgeArtinHom_of_not_root_generator_left
    (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    tripleEdgeArtinHom_of_not_root (R := R) hij hall h h' hv'
      (TripleEdgeArtinGroup.generator i) = twoNodeBraidEquiv_of_not_root hij hall hv' :=
  tripleEdgeArtinHomOfBraid_generator_left ..

@[simp] theorem tripleEdgeArtinHom_of_not_root_generator_right
    (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    tripleEdgeArtinHom_of_not_root (R := R) hij hall h h' hv'
      (TripleEdgeArtinGroup.generator j) =
        twoNodeBraidEquiv_of_not_root hij.symm (fun l ↦ (hall l).symm) hv' :=
  tripleEdgeArtinHomOfBraid_generator_right ..

/-- All generator formulas for the generic-parameter action, at both nodes. -/
theorem tripleEdgeArtinHom_of_not_root_images (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (l : I) :
    HasBraidGeneratorImages l
      (tripleEdgeArtinHom_of_not_root (R := R) hij hall h h' hv'
        (TripleEdgeArtinGroup.generator l)).toAlgHom := by
  rcases hall l with rfl | rfl
  · exact tripleEdgeArtinHomOfBraid_images_left ..
  · exact tripleEdgeArtinHomOfBraid_images_right ..

end Generic

section Literal

variable {k Y : Type*} [Field k] [AddCommGroup Y] {v : k} [NeZero v]

/-- Mathlib's literal `G₂` has `a₀₁ = -3`, `a₁₀ = -1`: node `0` is short. -/
theorem cartanMatrix_G₂_entries :
    CartanMatrix.G₂ 0 1 = -3 ∧ CartanMatrix.G₂ 1 0 = -1 := by
  decide

/-- **The braid group action for Mathlib's literal `G₂`**, for any compatible Cartan datum
and root-datum lattice, and any nonzero parameter `v` that is not a root of unity (over any
field). -/
def artinHom_G₂ {D : LusztigCartanDatum (Fin 2)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.G₂) (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) :
    TripleEdgeArtinGroup (0 : Fin 2) 1 →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  tripleEdgeArtinHom_of_not_root (R := R) (i := 0) (j := 1) (by decide)
    (fun l ↦ by fin_cases l <;> simp)
    (by rw [hD]; exact cartanMatrix_G₂_entries.1) (by rw [hD]; exact cartanMatrix_G₂_entries.2)
    hpow

/-- Evaluation gives the literal `G₂` Artin action on the quantum group. -/
abbrev artinAction_G₂ {D : LusztigCartanDatum (Fin 2)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.G₂) (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) :
    MulSemiringAction (TripleEdgeArtinGroup (0 : Fin 2) 1) (QuantumGroup R v) :=
  MulSemiringAction.compHom (QuantumGroup R v) (artinHom_G₂ R hD hpow)

/-- All generator formulas for the literal `G₂` action, at both nodes. -/
theorem artinHom_G₂_images {D : LusztigCartanDatum (Fin 2)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.G₂) (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1) (l : Fin 2) :
    HasBraidGeneratorImages l
      (artinHom_G₂ R hD hpow (TripleEdgeArtinGroup.generator l)).toAlgHom :=
  tripleEdgeArtinHom_of_not_root_images _ _ _ _ _ l

end Literal

end QuantumGroup
