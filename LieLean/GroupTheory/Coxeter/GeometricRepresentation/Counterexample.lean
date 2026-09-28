/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.GeometricRepresentation.RootChoice
import LieLean.GroupTheory.Coxeter.GeometricRepresentation.CounterexampleRoots
import LieLean.GroupTheory.Coxeter.GeometricRepresentation.CounterexampleMatrices
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The actual chosen-root geometric counterexample

## Main results
`reflection_matrix` identifies the original reflection formulas with the explicit matrices.
`representation_matrix` identifies the entire representation after extension to complex scalars.
`exists_nonfaithful_choice` exhibits an admissible choice with a nontrivial kernel word.

## References and scope
Reconstructed from the frozen exact primitive-root and Coxeter-presentation certificates.
The original opaque specialization is NOT asserted to be nonfaithful.
-/


namespace GeometricParametric

open GeometricRootBridge GeometricCounterexample GeometricFaithfulScope

/-- Explicitly override precisely the three off-diagonal exponents of the triangle. -/
noncomputable def badChoice : RootChoice ℂ where
  root m := if m = 2 then root4 else if m = 5 then root10 else if m = 10 then root20
    else (opaqueChoice ℂ).root m
  root_zero := by simp [opaqueChoice, CoxeterMatrix.geomRoot]
  order_root := by
    intro m hm
    split_ifs with h2 h5 h10
    · subst m; exact root_orders.1
    · subst m; exact root_orders.2.1
    · subst m; exact root_orders.2.2
    · exact (opaqueChoice ℂ).order_root hm

/-- All relevant roots are the explicit primitive roots, not opaque replacements. -/
theorem badChoice_roots :
    badChoice.root 2 = root4 ∧ badChoice.root 5 = root10 ∧
    badChoice.root 10 = root20 := by norm_num [badChoice]

/-- The exact doubled coefficients appearing in the reflections. -/
theorem badChoice_coefficients :
    2 * coeff badChoice 1 = -2 ∧ 2 * coeff badChoice 2 = 0 ∧
    2 * coeff badChoice 5 = (golden : ℂ) ∧
    2 * coeff badChoice 10 = (badCoefficient : ℂ) := by
  refine ⟨by rw [coeff_one]; ring, ?_, ?_, ?_⟩
  · rw [two_mul_coeff badChoice (by norm_num : 2 ≠ 0), badChoice_roots.1]
    exact root4_add_inv
  · rw [two_mul_coeff badChoice (by norm_num : 5 ≠ 0), badChoice_roots.2.1]
    exact root10_add_inv
  · rw [two_mul_coeff badChoice (by norm_num : 10 ≠ 0), badChoice_roots.2.2]
    exact root20_add_inv

/-- Matrix coordinates in the same simple-root basis used by the geometric construction. -/
noncomputable def coordinates :
    Module.End ℂ (Fin 3 →₀ ℂ) ≃ₐ[ℂ] Mat ℂ :=
  LinearMap.toMatrixAlgEquiv (Finsupp.basisSingleOne : Module.Basis (Fin 3) ℂ _)

/-- Coefficientwise complex extension of the real matrix representation. -/
noncomputable def complexExtension : W →* Mat ℂ :=
  Complex.ofRealHom.mapMatrix.toMonoidHom.comp
    ((Units.coeHom (Mat ℝ)).comp badRepresentation)

/-- The bad geometric representation is constructed by the generic Coxeter lift. -/
noncomputable def badGeometric : W →* Module.End ℂ (Fin 3 →₀ ℂ) :=
  GeometricParametric.representation badChoice triangle triangle.toCoxeterSystem

/-- Formula-level identification: basis matrices are exactly the complexified real ones. -/
theorem reflection_matrix (i : Fin 3) :
    coordinates (reflection badChoice triangle i) =
      Complex.ofRealHom.mapMatrix (generators golden badCoefficient i) := by
  ext j k
  simp only [coordinates, LinearMap.toMatrixAlgEquiv_apply,
    Finsupp.coe_basisSingleOne]
  change (reflection badChoice triangle i (Finsupp.single k 1)) j = _
  rw [reflection_single]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [triangle, badChoice_coefficients.1, badChoice_coefficients.2.1,
      badChoice_coefficients.2.2.1, badChoice_coefficients.2.2.2,
      generators, A, B, C]

/-- Equality of entire representations after complex extension, not unrelated existence. -/
theorem representation_matrix :
    coordinates.toMonoidHom.comp badGeometric = complexExtension := by
  apply triangle.toCoxeterSystem.ext_simple
  intro i
  change coordinates (badGeometric (triangle.simple i)) = _
  rw [show badGeometric (triangle.simple i) = reflection badChoice triangle i from
    representation_simple badChoice triangle triangle.toCoxeterSystem i]
  rw [reflection_matrix]
  change Complex.ofRealHom.mapMatrix (generators golden badCoefficient i) =
    Complex.ofRealHom.mapMatrix (badRepresentation (triangle.simple i) : Mat ℝ)
  rw [badRepresentation_simple]

/-- The fixed nontrivial Coxeter word is killed by these actual reflection formulas. -/
theorem badGeometric_kills_w : badGeometric w = 1 := by
  apply coordinates.injective
  have heq := DFunLike.congr_fun representation_matrix w
  change coordinates (badGeometric w) = complexExtension w at heq
  rw [heq]
  have hw : badRepresentation w = 1 := w_mem_badRepresentation_ker
  simp [complexExtension, hw]

/-- Nonfaithfulness of this admissible-root geometric representation. -/
theorem badGeometric_not_injective : ¬ Function.Injective badGeometric := by
  intro hinj
  exact w_ne_one (hinj (by rw [badGeometric_kills_w, map_one]))

/-- The actual group-valued geometric representation (units in the endomorphism ring). -/
noncomputable def badGeometricUnits : W →* (Module.End ℂ (Fin 3 →₀ ℂ))ˣ :=
  badGeometric.toHomUnits

/-- The same witness proves nonfaithfulness with a genuine group codomain. -/
theorem badGeometricUnits_not_injective : ¬ Function.Injective badGeometricUnits := by
  intro hinj
  apply w_ne_one
  apply hinj
  apply Units.ext
  exact (badGeometric_kills_w.trans (map_one badGeometric).symm)

/-- There exists an admissible primitive-root choice whose geometric lift is nonfaithful. -/
theorem exists_nonfaithful_choice :
    ∃ r : RootChoice ℂ,
      (∀ m : ℕ, 0 < m → IsPrimitiveRoot (r.root m) (2 * m)) ∧
      coordinates.toMonoidHom.comp
        (GeometricParametric.representation r triangle triangle.toCoxeterSystem) =
          complexExtension ∧
      w ≠ 1 ∧
      GeometricParametric.representation r triangle triangle.toCoxeterSystem w = 1 ∧
      ¬ Function.Injective
        (GeometricParametric.representation r triangle triangle.toCoxeterSystem) :=
  ⟨badChoice, fun _ hm ↦ root_primitive badChoice hm, representation_matrix,
    w_ne_one, badGeometric_kills_w, badGeometric_not_injective⟩


end GeometricParametric
