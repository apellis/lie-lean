/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.FiniteRoots

/-!
# Full roots of the transposed realization

## Main results

The original and transposed Weyl groups are isomorphic through their common Coxeter
presentation. Their finiteness is therefore equivalent, as is finiteness of their full
root-space-defined root systems. With the existing dual-space Tits cone convention,
this completes the four finiteness/fullness equivalences of Kac Proposition 3.12(e).

## References

Kac, *Infinite dimensional Lie algebras*, third edition, §§1.1, 3.1 and Proposition 3.12(e).
§3.1, p. 30 defines the dual root system as the full root system of the transpose algebra;
§1.1, pp. 1–2 gives the dual realization. The proof is reconstructed using the existing
Coxeter-system theorem, not transcribed.
The full dual roots here mean `KacMoodyAlgebra.roots P.transpose`, not real coroots.
They live in the algebraic double dual of the original Cartan space: the simple roots
are evaluations at original simple coroots. No identification of the whole Cartan space
with its double dual, or additional finite-dimensionality hypothesis, is used.
-/

open Module

namespace Matrix

variable {ι : Type*} [DecidableEq ι]

/-- Transposition preserves the Coxeter matrix, since its entries depend on
`aᵢⱼ aⱼᵢ`. This is the presentation-level duality used in Kac Proposition 3.12(e). -/
@[simp] theorem coxeterMatrix_transpose (A : Matrix ι ι ℤ) :
    Aᵀ.coxeterMatrix = A.coxeterMatrix := by
  ext i j
  simp [coxeterMatrix, mul_comm]

namespace Realization

variable {K H : Type*} [Fintype ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsGeneralizedCartan)

/-- The canonical isomorphism between the original and transposed Weyl groups,
through their common Coxeter presentation (Kac Proposition 3.12(e), reconstructed). -/
noncomputable def weylGroupTransposeEquiv :
    P.weylGroup hA ≃* P.transpose.weylGroup hA.transpose :=
  (P.coxeterSystem hA).mulEquiv.trans
    ((show CoxeterSystem A.coxeterMatrix (P.transpose.weylGroup hA.transpose) from
      coxeterMatrix_transpose A ▸ P.transpose.coxeterSystem hA.transpose).mulEquiv.symm)

omit [DecidableEq ι] in
/-- The original Weyl group is finite exactly when the transposed Weyl group is finite.
No faithful action on a smaller span is assumed (Kac Proposition 3.12(e)). -/
theorem finite_weylGroup_iff_finite_transpose_weylGroup :
    Finite (P.weylGroup hA) ↔ Finite (P.transpose.weylGroup hA.transpose) := by
  classical
  constructor
  · intro h
    let _ := h
    exact Finite.of_equiv _ (P.weylGroupTransposeEquiv hA).toEquiv
  · intro h
    let _ := h
    exact Finite.of_equiv _ (P.weylGroupTransposeEquiv hA).symm.toEquiv

namespace KacMoodyAlgebra

omit [CharZero K] in
/-- Every full root of the transposed realization is an evaluation of an element
of the original coroot lattice (Kac §3.1). This is a range statement for roots,
not a claim that the Cartan space is reflexive. -/
theorem transpose_roots_subset_range_eval :
    roots P.transpose ⊆ Set.range (Dual.eval K H) := by
  intro μ hμ
  rcases mem_posWeights_or_mem_negWeights P.transpose hμ with
    ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩
  · exact ⟨P.corootOf k, (P.transpose_rootOf k).symm⟩
  · exact ⟨-P.corootOf k, by rw [map_neg, ← P.transpose_rootOf]⟩

omit [CharZero K] in
/-- Pulling the full dual roots back to the original Cartan space and then evaluating
recovers exactly the full transposed root system (Kac §3.1). -/
theorem eval_image_preimage_transpose_roots :
    (Dual.eval K H) '' ((Dual.eval K H) ⁻¹' roots P.transpose) = roots P.transpose :=
  Set.image_preimage_eq_of_subset (transpose_roots_subset_range_eval P)

omit [CharZero K] in
/-- The source's Cartan-valued dual roots and the double-dual-valued transposed full
roots have equivalent finiteness. Evaluation is only required to be injective and
surjective onto the root set, never onto the entire double dual (Kac §3.1). -/
theorem finite_eval_preimage_transpose_roots_iff :
    ((Dual.eval K H) ⁻¹' roots P.transpose).Finite ↔ (roots P.transpose).Finite :=
  ⟨fun h ↦ Set.finite_of_finite_preimage h (transpose_roots_subset_range_eval P),
    fun h ↦ h.preimage (Module.eval_apply_injective K).injOn⟩

/-- Full dual-root finiteness is equivalent to original Weyl-group finiteness,
over every characteristic-zero field (Kac Proposition 3.12(e)(i) iff (iv)). -/
theorem finite_transpose_roots_iff_finite_weylGroup :
    (roots P.transpose).Finite ↔ Finite (P.weylGroup hA) :=
  (finite_roots_iff_finite_weylGroup P.transpose hA.transpose).trans
    (P.finite_weylGroup_iff_finite_transpose_weylGroup hA).symm

/-- Kac Proposition 3.12(e)(iv) iff (i), with the full dual-root set transported
to the original Cartan space by evaluation, as in Kac §3.1. -/
theorem finite_eval_preimage_transpose_roots_iff_finite_weylGroup :
    ((Dual.eval K H) ⁻¹' roots P.transpose).Finite ↔ Finite (P.weylGroup hA) :=
  (finite_eval_preimage_transpose_roots_iff P).trans
    (finite_transpose_roots_iff_finite_weylGroup P hA)

include hA in
/-- Finiteness of the full root system is invariant under transpose duality
(Kac Proposition 3.12(e)(iii) iff (iv)). -/
theorem finite_roots_iff_finite_transpose_roots :
    (roots P).Finite ↔ (roots P.transpose).Finite :=
  (finite_roots_iff_finite_weylGroup P hA).trans
    (finite_transpose_roots_iff_finite_weylGroup P hA).symm

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Kac Proposition 3.12(e), in the existing dual-space convention for the Tits cone:
finite Weyl group, full Tits cone, finite full roots, and finite full dual roots are
pairwise equivalent. The three equivalences share the first proposition. -/
theorem finite_weylGroup_iff_titsCone_eq_univ_and_finite_roots :
    (Finite (P.weylGroup hA) ↔ P.titsCone hA = Set.univ) ∧
      (Finite (P.weylGroup hA) ↔ (roots P).Finite) ∧
      (Finite (P.weylGroup hA) ↔ (roots P.transpose).Finite) :=
  ⟨P.finite_weylGroup_iff_titsCone_eq_univ hA,
    (finite_roots_iff_finite_weylGroup P hA).symm,
    (finite_transpose_roots_iff_finite_weylGroup P hA).symm⟩

end KacMoodyAlgebra
end Realization
end Matrix
