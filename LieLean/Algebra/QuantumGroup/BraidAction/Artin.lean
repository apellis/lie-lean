/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.SimplyLacedRelations
import Mathlib.GroupTheory.PresentedGroup

/-!
# The triangle-free simply-laced Artin action on the quantum group

## Main definitions / results

* `SimplyLacedArtinGroup`: the free group modulo precisely the length-two/three relators.
* `SimplyLacedArtinGroup.lift`: its universal homomorphism, with uniqueness.
* `QuantumGroup.artinHom`: the actual quantum automorphism representation.
* `QuantumGroup.artinAction`: the resulting multiplicative semiring action.

## References and scope

Reconstructed from Mathlib's `PresentedGroup` universal property and the inspected
`SimplyLaced` / `SimplyLacedRelations` proofs; no external primary source consulted.
No involution relators are imposed. The action need not be faithful.
The Cartan diagram is triangle-free and simply laced, including finite ADE types;
no finiteness or bound on vertex valency is required. Higher Cartan edge multiplicities
and triangles are not covered. The toral lattice is arbitrary. Nonvanishing of both
`q_i - q_i⁻¹` and `q_i + q_i⁻¹` is retained explicitly.
-/

noncomputable section

namespace LusztigCartanDatum

variable {I : Type*} (D : LusztigCartanDatum I)

/-- Global combinatorial hypotheses sufficient for the existing local automorphisms. -/
structure IsTriangleFreeSimplyLaced : Prop where
  edge : ∀ i j, j ≠ i → D.cartanMatrix i j = 0 ∨
    (D.cartanMatrix i j = -1 ∧ D.cartanMatrix j i = -1)
  orthogonal : ∀ i j l, D.cartanMatrix i j = -1 → D.cartanMatrix i l = -1 →
    j ≠ l → D.cartanMatrix j l = 0

/-- Global simple edges imply the local path hypothesis; no extra relation is assumed. -/
theorem IsTriangleFreeSimplyLaced.path (H : D.IsTriangleFreeSimplyLaced)
    (i j l : I) (hij : D.cartanMatrix i j = -1) (hil : D.cartanMatrix i l = 0) :
    D.cartanMatrix j l = 0 ∨ (D.cartanMatrix j l = -1 ∧ D.cartanMatrix l j = -1) := by
  apply H.edge j l
  intro h
  subst l
  omega

/-- Exactly the usual simply-laced Artin relators, not Coxeter involution relators. -/
def simplyLacedArtinRelators : Set (FreeGroup I) :=
  {r | ∃ i j, i ≠ j ∧
    ((D.cartanMatrix i j = 0 ∧
      r = (FreeGroup.of i * FreeGroup.of j) * (FreeGroup.of j * FreeGroup.of i)⁻¹) ∨
     (D.cartanMatrix i j = -1 ∧
      r = (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i) *
        (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹))}

end LusztigCartanDatum

/-- The simply-laced Artin presentation; only Cartan entries zero and minus one
supply relators. Its intended simply-laced scope is certified separately. -/
abbrev SimplyLacedArtinGroup {I : Type*} (D : LusztigCartanDatum I) :=
  PresentedGroup D.simplyLacedArtinRelators

namespace SimplyLacedArtinGroup

variable {I : Type*} {D : LusztigCartanDatum I}

/-- The Artin generator at a node, with no square-one relation. -/
def generator (i : I) : SimplyLacedArtinGroup D := PresentedGroup.of i

/-- Orthogonal Artin generators commute, by the defining presentation. -/
theorem generator_comm {i j : I} (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) :
    generator (D := D) i * generator j = generator j * generator i := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨i, j, hij, Or.inl ⟨h0, rfl⟩⟩

/-- Adjacent Artin generators satisfy the length-three relation. -/
theorem generator_braid {i j : I} (hij : i ≠ j) (h1 : D.cartanMatrix i j = -1) :
    generator (D := D) i * generator j * generator i =
      generator j * generator i * generator j := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨i, j, hij, Or.inr ⟨h1, rfl⟩⟩

variable {G : Type*} [Group G] (f : I → G)
  (h2 : ∀ i j, i ≠ j → D.cartanMatrix i j = 0 → f i * f j = f j * f i)
  (h3 : ∀ i j, i ≠ j → D.cartanMatrix i j = -1 →
    f i * f j * f i = f j * f i * f j)

/-- Universal lift of an assignment satisfying the two Artin relation families. -/
def lift : SimplyLacedArtinGroup D →* G :=
  PresentedGroup.toGroup (f := f) (by
    rintro r ⟨i, j, hij, ⟨h0, rfl⟩ | ⟨h1, rfl⟩⟩
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [h2 i j hij h0, mul_inv_cancel]
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [h3 i j hij h1, mul_inv_cancel])

@[simp] theorem lift_generator (i : I) : lift f h2 h3 (generator i) = f i :=
  PresentedGroup.toGroup.of _

/-- Universal uniqueness, not merely existence of a quotient map. -/
theorem lift_unique (g : SimplyLacedArtinGroup D →* G)
    (hg : ∀ i, g (generator i) = f i) : g = lift f h2 h3 := by
  apply PresentedGroup.ext
  intro i
  exact (hg i).trans (lift_generator f h2 h3 i).symm

/-- Total exponent sum: all Artin relators preserve word length with signs. -/
def exponentSum : SimplyLacedArtinGroup D →* Multiplicative ℤ :=
  lift (fun _ ↦ Multiplicative.ofAdd (1 : ℤ)) (by intros; rfl) (by intros; rfl)

@[simp] theorem exponentSum_generator (i : I) :
    exponentSum (generator (D := D) i) = Multiplicative.ofAdd (1 : ℤ) :=
  lift_generator _ _ _ i

/-- A presentation-level safeguard: these generators are not involutions.
This does not assert faithfulness of the quantum representation. -/
theorem generator_sq_ne_one (i : I) : generator (D := D) i ^ 2 ≠ 1 := by
  intro h
  have hh := congrArg (fun g ↦ (exponentSum g).toAdd) h
  simp at hh

end SimplyLacedArtinGroup

namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  (H : D.IsTriangleFreeSimplyLaced)
  (hq : ∀ i, v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hs : ∀ i, v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)

/-- The actual quotient automorphism at each node, using global diagram hypotheses. -/
def artinGeneratorEquiv (i : I) : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  simplyLacedBraidEquiv i (H.edge i) (H.orthogonal i) (H.path D i) (hq i) (hs i)

/-- The length-two relation in the automorphism group's multiplication convention. -/
theorem artinGeneratorEquiv_comm (i j : I) (hij : i ≠ j)
    (h0 : D.cartanMatrix i j = 0) :
    artinGeneratorEquiv (R := R) H hq hs i * artinGeneratorEquiv H hq hs j =
      artinGeneratorEquiv H hq hs j * artinGeneratorEquiv H hq hs i := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun
    (simplyLacedBraid_comm i j (H.edge i) (H.orthogonal i) (H.path D i) (hq i) (hs i)
      (H.edge j) (H.orthogonal j) (H.path D j) (hq j) (hs j) hij h0) x

/-- The adjacent length-three relation holds on the entire quantum algebra. -/
theorem artinGeneratorEquiv_braid (i j : I) (hij : i ≠ j)
    (h1 : D.cartanMatrix i j = -1) :
    artinGeneratorEquiv (R := R) H hq hs i * artinGeneratorEquiv H hq hs j *
        artinGeneratorEquiv H hq hs i =
      artinGeneratorEquiv H hq hs j * artinGeneratorEquiv H hq hs i *
        artinGeneratorEquiv H hq hs j := by
  have h1' : D.cartanMatrix j i = -1 := by
    rcases H.edge i j hij.symm with h0 | ⟨_, h⟩
    · omega
    · exact h
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun
    (simplyLacedBraid_braid i j (H.edge i) (H.orthogonal i) (H.path D i) (hq i) (hs i)
      (H.edge j) (H.orthogonal j) (H.path D j) (hq j) (hs j) hij h1 h1') x

/-- The genuine Artin-group homomorphism to quantum algebra automorphisms.
Its defining relation proofs use the published quotient maps, not assumed target relations. -/
def artinHom : SimplyLacedArtinGroup D →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  SimplyLacedArtinGroup.lift (artinGeneratorEquiv H hq hs)
    (artinGeneratorEquiv_comm H hq hs) (artinGeneratorEquiv_braid H hq hs)

@[simp] theorem artinHom_generator (i : I) :
    artinHom (R := R) H hq hs (SimplyLacedArtinGroup.generator i) =
      artinGeneratorEquiv H hq hs i := SimplyLacedArtinGroup.lift_generator _ _ _ i

@[simp] theorem artinHom_generator_inv (i : I) :
    artinHom (R := R) H hq hs (SimplyLacedArtinGroup.generator i)⁻¹ =
      (artinGeneratorEquiv H hq hs i).symm := by
  rw [map_inv, artinHom_generator]
  rfl

/-- The representation is uniquely determined by its actual braid generators. -/
theorem artinHom_unique
    (g : SimplyLacedArtinGroup D →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v))
    (hg : ∀ i, g (SimplyLacedArtinGroup.generator i) = artinGeneratorEquiv H hq hs i) :
    g = artinHom H hq hs := SimplyLacedArtinGroup.lift_unique _ _ _ g hg

/-- The actual action, obtained by pulling back evaluation along `artinHom`.
A named instance value avoids globally selecting parameter-dependent actions. -/
abbrev artinAction : MulSemiringAction (SimplyLacedArtinGroup D) (QuantumGroup R v) :=
  MulSemiringAction.compHom (QuantumGroup R v) (artinHom (R := R) H hq hs)

@[simp] theorem artinHom_generator_E (i l : I) :
    artinHom H hq hs (SimplyLacedArtinGroup.generator i) (E R v l) =
      if l = i then braidEi R i else braidEj R v i l := by
  rw [artinHom_generator]
  exact simplyLacedBraid_E i (H.edge i) (H.orthogonal i) (H.path D i) (hq i) (hs i) l

@[simp] theorem artinHom_generator_F (i l : I) :
    artinHom H hq hs (SimplyLacedArtinGroup.generator i) (F R v l) =
      if l = i then braidFi R i else braidFj R v i l := by
  rw [artinHom_generator]
  exact simplyLacedBraid_F i (H.edge i) (H.orthogonal i) (H.path D i) (hq i) (hs i) l

/-- Every toral lattice element is reflected, not only the simple coroots. -/
@[simp] theorem artinHom_generator_K (i : I) (μ : Y) :
    artinHom H hq hs (SimplyLacedArtinGroup.generator i) (K R v μ) =
      K R v (reflY R i μ) := by
  rw [artinHom_generator]
  exact simplyLacedBraid_K i (H.edge i) (H.orthogonal i) (H.path D i) (hq i) (hs i) μ

/-- The inverse Artin generator uses the explicit reversal-conjugate map. -/
theorem artinHom_generator_inv_apply (i : I) (x : QuantumGroup R v) :
    artinHom H hq hs (SimplyLacedArtinGroup.generator i)⁻¹ x =
      braidReversal (artinHom H hq hs (SimplyLacedArtinGroup.generator i)
        (braidReversal x)) := by
  rw [artinHom_generator_inv, artinHom_generator]
  rfl

@[simp] theorem artinHom_generator_inv_Ei (i : I) :
    artinHom H hq hs (SimplyLacedArtinGroup.generator i)⁻¹ (E R v i) =
      braidInvEi R i := by
  rw [artinHom_generator_inv]
  exact simplyLacedBraidInv_Ei i (H.edge i) (H.orthogonal i) (H.path D i) (hq i) (hs i)

@[simp] theorem artinHom_generator_inv_Fi (i : I) :
    artinHom H hq hs (SimplyLacedArtinGroup.generator i)⁻¹ (F R v i) =
      braidInvFi R i := by
  rw [artinHom_generator_inv]
  exact simplyLacedBraidInv_Fi i (H.edge i) (H.orthogonal i) (H.path D i) (hq i) (hs i)

@[simp] theorem artinHom_generator_inv_Ej (i j : I) (hj : j ≠ i)
    (h1 : D.cartanMatrix i j = -1) :
    artinHom H hq hs (SimplyLacedArtinGroup.generator i)⁻¹ (E R v j) =
      E R v j * E R v i - (v ^ D.d i)⁻¹ • (E R v i * E R v j) := by
  rw [artinHom_generator_inv]
  exact simplyLacedBraidInv_Ej i (H.edge i) (H.orthogonal i) (H.path D i)
    (hq i) (hs i) j hj h1

@[simp] theorem artinHom_generator_inv_Fj (i j : I) (hj : j ≠ i)
    (h1 : D.cartanMatrix i j = -1) :
    artinHom H hq hs (SimplyLacedArtinGroup.generator i)⁻¹ (F R v j) =
      F R v i * F R v j - (v ^ D.d i) • (F R v j * F R v i) := by
  rw [artinHom_generator_inv]
  exact simplyLacedBraidInv_Fj i (H.edge i) (H.orthogonal i) (H.path D i)
    (hq i) (hs i) j hj h1

@[simp] theorem artinHom_generator_inv_E_orthogonal (i j : I) (hj : j ≠ i)
    (h0 : D.cartanMatrix i j = 0) :
    artinHom H hq hs (SimplyLacedArtinGroup.generator i)⁻¹ (E R v j) = E R v j := by
  rw [artinHom_generator_inv]
  exact simplyLacedBraidInv_E_of_orthogonal i (H.edge i) (H.orthogonal i) (H.path D i)
    (hq i) (hs i) j hj h0

@[simp] theorem artinHom_generator_inv_F_orthogonal (i j : I) (hj : j ≠ i)
    (h0 : D.cartanMatrix i j = 0) :
    artinHom H hq hs (SimplyLacedArtinGroup.generator i)⁻¹ (F R v j) = F R v j := by
  rw [artinHom_generator_inv]
  exact simplyLacedBraidInv_F_of_orthogonal i (H.edge i) (H.orthogonal i) (H.path D i)
    (hq i) (hs i) j hj h0

@[simp] theorem artinHom_generator_inv_K (i : I) (μ : Y) :
    artinHom H hq hs (SimplyLacedArtinGroup.generator i)⁻¹ (K R v μ) =
      K R v (reflY R i μ) := by
  rw [artinHom_generator_inv]
  exact simplyLacedBraidInv_K i (H.edge i) (H.orthogonal i) (H.path D i) (hq i) (hs i) μ

/-- Evaluation is precisely the specified action (left composition convention). -/
theorem artinAction_smul (g : SimplyLacedArtinGroup D) (x : QuantumGroup R v) :
    letI := artinAction (R := R) H hq hs
    g • x = artinHom H hq hs g x := rfl

/-- The action fixes the coefficient field pointwise, hence is an algebra action. -/
theorem artinAction_algebraMap (g : SimplyLacedArtinGroup D) (a : k) :
    letI := artinAction (R := R) H hq hs
    g • algebraMap k (QuantumGroup R v) a = algebraMap k (QuantumGroup R v) a :=
  (artinHom H hq hs g).commutes a

/-- Scalar linearity of every group element, beyond the semiring-action laws. -/
theorem artinAction_smul_scalar (g : SimplyLacedArtinGroup D)
    (a : k) (x : QuantumGroup R v) :
    letI := artinAction (R := R) H hq hs
    g • (a • x) = a • (g • x) := map_smul (artinHom (R := R) H hq hs g) a x

end QuantumGroup
