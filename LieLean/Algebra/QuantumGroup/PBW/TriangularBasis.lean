/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.NegativeBasis
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Actual triangular multiplication and full quantum PBW bases

## Main results

* `serreTensorEquiv`: quotienting the two outer factors gives the triangular quotient.
* `triangularMultiplicationEquiv`: actual multiplication `U⁻ ⊗ (k[Y] ⊗ U⁺) ≃ₗ[k] U`.
* `triangularMultiplicationEquiv_tmul`: this equivalence sends `y ⊗ (g ⊗ x)` to `y g x`.
* `finiteTypeFullPBWBasis`: full finite-type PBW basis of `U`.
* `finiteTypeFullPBWBasis_apply`: its vectors are negative monomial times `K_μ` times
  positive monomial, with the established Chevalley-conjugated negative convention.
* `finiteTypeFullPBWBasis_sum_repr`: finite reconstruction of every element of `U`.
* `exists_finiteTypeFullPBWBasis`: existence without a supplied longest reduced word.

The multiplication equivalence and the basis require only a nonzero non-root-of-unity
parameter, over any field.

## References

Reconstructed from `QuantumGroup.triangularEquiv` and Mathlib's quotient tensor-product
isomorphisms and the positive and negative bases of `PBW.GenericBasis`, `PBW.NegativeBasis`.
-/

open LieLean

noncomputable section
open TensorProduct Module
namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k)

/-- The right Serre submodule in the toral-positive tensor product. -/
def toralSerreSubmodule : Submodule k (AddMonoidAlgebra k Y ⊗[k] LusztigF k I) :=
  LinearMap.range (TensorProduct.map LinearMap.id (serreSubmodule D v).subtype)

omit [AddCommGroup Y] [DecidableEq I] in
/-- The span definition of the triangular Serre relations equals the tensor quotient kernel. -/
theorem serreTriSubmodule_eq_tensorSup :
    serreTriSubmodule Y D v =
      LinearMap.range (TensorProduct.map (serreSubmodule D v).subtype
        (LinearMap.id : AddMonoidAlgebra k Y ⊗[k] LusztigF k I →ₗ[k] _)) ⊔
      LinearMap.range (TensorProduct.map (LinearMap.id : LusztigF k I →ₗ[k] _)
        (toralSerreSubmodule (Y := Y) (D := D) v).subtype) := by
  apply le_antisymm
  · rw [serreTriSubmodule, Submodule.span_le]
    rintro _ ⟨y, g, x, rfl, hy | hx⟩
    · exact Submodule.mem_sup_left ⟨⟨y, mem_serreSubmodule.mpr hy⟩ ⊗ₜ (g ⊗ₜ x), rfl⟩
    · exact Submodule.mem_sup_right
        ⟨y ⊗ₜ ⟨g ⊗ₜ x, ⟨g ⊗ₜ ⟨x, mem_serreSubmodule.mpr hx⟩, rfl⟩⟩, rfl⟩
  · apply sup_le
    · rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.inductionOn with
      | tmul y w =>
        exact tmul_mem_serreTriSubmodule_left' (D := D) (v := v) (Y := Y)
          (mem_serreSubmodule.mp y.property) w
      | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    · rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.inductionOn with
      | tmul y w =>
        obtain ⟨z, hz⟩ := w.property
        change y ⊗ₜ w.val ∈ _
        rw [← hz]
        clear hz w
        induction z using TensorProduct.inductionOn with
        | tmul g x =>
          exact tmul_mem_serreTriSubmodule_right y g
            (mem_serreSubmodule.mp x.property)
        | add a b ha hb =>
          simpa only [map_add, tmul_add] using Submodule.add_mem _ ha hb
      | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb

/-- Quotienting the two outer factors gives exactly the existing triangular quotient. -/
def serreTensorEquiv :
    (LusztigF k I ⧸ serreSubmodule D v) ⊗[k]
      (AddMonoidAlgebra k Y ⊗[k] (LusztigF k I ⧸ serreSubmodule D v)) ≃ₗ[k]
      TriSpace k I Y ⧸ serreTriSubmodule Y D v :=
  (TensorProduct.congr (LinearEquiv.refl k _)
      (TensorProduct.tensorQuotientEquiv (AddMonoidAlgebra k Y) (serreSubmodule D v))).trans
    ((TensorProduct.quotientTensorQuotientEquiv (serreSubmodule D v)
      (toralSerreSubmodule (Y := Y) (D := D) v)).trans
      (Submodule.quotEquivOfEq _ _ (serreTriSubmodule_eq_tensorSup (Y := Y) (D := D) v).symm))

omit [AddCommGroup Y] [DecidableEq I] in
@[simp] theorem serreTensorEquiv_mk (y x : LusztigF k I) (g : AddMonoidAlgebra k Y) :
    serreTensorEquiv (Y := Y) (D := D) v
      (Submodule.Quotient.mk y ⊗ₜ (g ⊗ₜ Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (y ⊗ₜ (g ⊗ₜ x)) := rfl

/-- The negative free-algebra map has the actual generated negative subalgebra as range. -/
theorem range_minusHom : (minusHom R v).range = Algebra.adjoin k (Set.range (F R v)) := by
  rw [← Algebra.map_top, ← FreeAlgebra.adjoin_range_ι, AlgHom.map_adjoin, ← Set.range_comp]
  congr 2
  funext i
  simp [minusHom]

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-- The Serre quotient is the actual positive subalgebra, by the proved kernel and range. -/
def serreQuotientEquivPlus :
    (LusztigF k I ⧸ serreSubmodule D v) ≃ₗ[k] Algebra.adjoin k (Set.range (E R v)) :=
  (Submodule.quotEquivOfEq _ _ (by
    ext x
    exact (mem_serreSubmodule.trans (plusHom_eq_zero_iff R v hv x).symm))).trans
    ((plusHom R v).toLinearMap.quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (congrArg Subalgebra.toSubmodule (range_plusHom R v))))

/-- The Serre quotient is the actual negative subalgebra, by the proved kernel and range. -/
def serreQuotientEquivMinus :
    (LusztigF k I ⧸ serreSubmodule D v) ≃ₗ[k] Algebra.adjoin k (Set.range (F R v)) :=
  (Submodule.quotEquivOfEq _ _ (by
    ext x
    exact (mem_serreSubmodule.trans (minusHom_eq_zero_iff R v hv x).symm))).trans
    ((minusHom R v).toLinearMap.quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (congrArg Subalgebra.toSubmodule (range_minusHom R v))))

@[simp] theorem serreQuotientEquivPlus_mk (x : LusztigF k I) :
    (serreQuotientEquivPlus R v hv (Submodule.Quotient.mk x) : QuantumGroup R v) =
      plusHom R v x := rfl

@[simp] theorem serreQuotientEquivMinus_mk (x : LusztigF k I) :
    (serreQuotientEquivMinus R v hv (Submodule.Quotient.mk x) : QuantumGroup R v) =
      minusHom R v x := rfl

/-- Actual negative–toral–positive multiplication is a linear isomorphism.
Only a nonzero non-root-of-unity parameter is required; no basis or spanning premise is used. -/
def triangularMultiplicationEquiv :
    Algebra.adjoin k (Set.range (F R v)) ⊗[k]
      (AddMonoidAlgebra k Y ⊗[k] Algebra.adjoin k (Set.range (E R v))) ≃ₗ[k]
      QuantumGroup R v :=
  (TensorProduct.congr (serreQuotientEquivMinus R v hv).symm
    (TensorProduct.congr (LinearEquiv.refl k _) (serreQuotientEquivPlus R v hv).symm)).trans
    ((serreTensorEquiv (Y := Y) (D := D) v).trans (triangularEquiv R v hv))

/-- The isomorphism is genuinely multiplication in the stated order. -/
@[simp] theorem triangularMultiplicationEquiv_tmul
    (y : Algebra.adjoin k (Set.range (F R v))) (g : AddMonoidAlgebra k Y)
    (x : Algebra.adjoin k (Set.range (E R v))) :
    triangularMultiplicationEquiv R v hv (y ⊗ₜ (g ⊗ₜ x)) =
      (y : QuantumGroup R v) * zeroHom R v g * (x : QuantumGroup R v) := by
  obtain ⟨y, rfl⟩ := (serreQuotientEquivMinus R v hv).surjective y
  obtain ⟨x, rfl⟩ := (serreQuotientEquivPlus R v hv).surjective x
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    induction x using Submodule.Quotient.induction_on with
    | H x => simp [triangularMultiplicationEquiv]

open Matrix.Realization.KacMoodyAlgebra

variable [Fintype I] {K H : Type*} [Field K] [CharZero K]
  [AddCommGroup H] [Module K H]
  (P : Matrix.Realization D.cartanMatrix K H) (hD : D.cartanMatrix.IsFiniteCartan)
  {ω : List I} (hω : (P.coxeterSystem hD.isGeneralizedCartan).IsReduced ω)
  (hw : (P.coxeterSystem hD.isGeneralizedCartan).wordProd ω = finiteTypeLongest P hD)

/-- The full finite-type quantum PBW basis, indexed by negative exponents, a toral lattice
point, and positive exponents. The negative vectors use Chevalley-conjugated braids. -/
def finiteTypeFullPBWBasis :
    Basis ((Fin ω.length → ℕ) × Y × (Fin ω.length → ℕ)) k (QuantumGroup R v) :=
  ((finiteTypeNegativePBWBasis R hv P hD hω hw).tensorProduct
    ((AddMonoidAlgebra.basis Y k).tensorProduct
      (finiteTypePBWBasis R P hD hv hω hw))).map
    (triangularMultiplicationEquiv R v hv)

/-- The full basis vectors are precisely negative monomial times `K_μ` times positive
monomial, with no hidden change of vectors or reversal of either word. -/
theorem finiteTypeFullPBWBasis_apply (a c : Fin ω.length → ℕ) (μ : Y) :
    finiteTypeFullPBWBasis R v hv P hD hω hw (a, μ, c) =
      CoxeterSystem.pbwMonomial (negativeBraidEquiv R hv) (F R v) ω a * QuantumGroup.K R v μ *
        CoxeterSystem.pbwMonomial (braidEquivOfNotRoot R hv) (E R v) ω c := by
  simp [finiteTypeFullPBWBasis, finiteTypeNegativePBWBasis_apply, finiteTypePBWBasis_apply]

/-- Full PBW coordinates give a finite expansion of every element of the actual quantum group. -/
theorem finiteTypeFullPBWBasis_sum_repr (x : QuantumGroup R v) :
    ((finiteTypeFullPBWBasis R v hv P hD hω hw).repr x).sum
      (fun t a ↦ a • (CoxeterSystem.pbwMonomial (negativeBraidEquiv R hv) (F R v) ω t.1 *
        QuantumGroup.K R v t.2.1 *
        CoxeterSystem.pbwMonomial (braidEquivOfNotRoot R hv) (E R v) ω t.2.2)) = x := by
  have hvec (t : (Fin ω.length → ℕ) × Y × (Fin ω.length → ℕ)) :
      finiteTypeFullPBWBasis R v hv P hD hω hw t =
        CoxeterSystem.pbwMonomial (negativeBraidEquiv R hv) (F R v) ω t.1 *
          QuantumGroup.K R v t.2.1 *
          CoxeterSystem.pbwMonomial (braidEquivOfNotRoot R hv) (E R v) ω t.2.2 :=
    finiteTypeFullPBWBasis_apply R v hv P hD hω hw t.1 t.2.2 t.2.1
  simpa only [Finsupp.linearCombination_apply, hvec] using
    (finiteTypeFullPBWBasis R v hv P hD hω hw).linearCombination_repr x

/-- A full PBW basis exists without a supplied reduced word, basis, spanning assertion,
or linear equivalence. -/
theorem exists_finiteTypeFullPBWBasis :
    ∃ ω : List I, (P.coxeterSystem hD.isGeneralizedCartan).IsReduced ω ∧
      (P.coxeterSystem hD.isGeneralizedCartan).wordProd ω = finiteTypeLongest P hD ∧
      ∃ b : Basis ((Fin ω.length → ℕ) × Y × (Fin ω.length → ℕ)) k (QuantumGroup R v),
        ∀ a μ c, b (a, μ, c) =
          CoxeterSystem.pbwMonomial (negativeBraidEquiv R hv) (F R v) ω a * QuantumGroup.K R v μ *
            CoxeterSystem.pbwMonomial (braidEquivOfNotRoot R hv) (E R v) ω c := by
  obtain ⟨ω, hω, hw⟩ :=
    (P.coxeterSystem hD.isGeneralizedCartan).exists_isReduced (finiteTypeLongest P hD)
  exact ⟨ω, hω, hw.symm, finiteTypeFullPBWBasis R v hv P hD hω hw.symm,
    fun a μ c ↦ finiteTypeFullPBWBasis_apply R v hv P hD hω hw.symm a c μ⟩

end LieLean.QuantumGroup
