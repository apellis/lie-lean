/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.SimplyLacedBasis
import LieLean.Algebra.QuantumGroup.PBW.TriangularBasis

/-!
# Full simply-laced quantum PBW bases at non-root-of-unity parameters

## Main results

* `simplyLacedFullPBWBasis`: the actual negative–toral–positive PBW basis.
* `simplyLacedFullPBWBasis_apply`: its vectors are negative monomial times `K_μ` times
  positive monomial, in the actual quantum group.
* `simplyLacedFullPBWBasis_sum_repr`: finite coordinate reconstruction of every element.
* `exists_simplyLacedFullPBWBasis`: a longest reduced word and the full basis, without
  a supplied word, basis, spanning assertion, or multiplication equivalence.

The quantum coefficient field is arbitrary. The parameter must be nonzero and not a
root of unity, but characteristic zero and transcendence are not assumed. Finite Cartan
type, simple lacing, and a finite Coxeter system remain explicit hypotheses. The negative
monomials use exactly `negativeBraidEquiv`, the Chevalley conjugates `C Tᵢ C⁻¹`, with no
word or multiplication-order reversal. No identification with the original negative
operators, or non-simply-laced spanning assertion, is made.

## References

Reconstructed by tensoring the actual bases from `PBW.SimplyLacedBasis` with
`AddMonoidAlgebra.basis` and mapping through the actual multiplication equivalence from
`PBW.TriangularBasis`. That equivalence requires only a nonzero non-root-of-unity parameter;
the older characteristic-zero, transcendental full basis is not used.
-/

open LieLean

noncomputable section
open Module
namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] [Fintype I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) {v : k} [NeZero v]
  (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hSL : D.cartanMatrix.IsSimplyLaced)
  {W : Type*} [Group W] [Finite W]
  (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W)
  (hD : D.cartanMatrix.IsFiniteCartan)
  {w : List I} (hw : cs.IsReduced w) (hw₀ : cs.wordProd w = cs.longestElement)

/-- The actual full PBW basis in finite simply-laced type over any quantum coefficient
field at a nonzero non-root-of-unity parameter. The indices are negative exponents,
a toral lattice point, and positive exponents, in that order. -/
def simplyLacedFullPBWBasis :
    Basis ((Fin w.length → ℕ) × Y × (Fin w.length → ℕ)) k (QuantumGroup R v) :=
  ((simplyLacedNegativePBWBasis R hv hSL cs hD hw hw₀).tensorProduct
    ((AddMonoidAlgebra.basis Y k).tensorProduct
      (simplyLacedPBWBasis R hv hSL cs hD hw hw₀))).map
    (triangularMultiplicationEquiv R v hv)

/-- The basis vectors are exactly negative monomial times `K_μ` times positive monomial,
using the explicit Chevalley-conjugated negative braids and unchanged word order. -/
theorem simplyLacedFullPBWBasis_apply (a c : Fin w.length → ℕ) (μ : Y) :
    simplyLacedFullPBWBasis R hv hSL cs hD hw hw₀ (a, μ, c) =
      CoxeterSystem.pbwMonomial (negativeBraidEquiv R hv) (F R v) w a * QuantumGroup.K R v μ *
        CoxeterSystem.pbwMonomial (braidEquivOfNotRoot R hv) (E R v) w c := by
  simp [simplyLacedFullPBWBasis, simplyLacedNegativePBWBasis_apply, simplyLacedPBWBasis_apply]

/-- The full PBW coordinates give a finite expansion of every actual quantum group element. -/
theorem simplyLacedFullPBWBasis_sum_repr (x : QuantumGroup R v) :
    ((simplyLacedFullPBWBasis R hv hSL cs hD hw hw₀).repr x).sum
      (fun t a ↦ a • (CoxeterSystem.pbwMonomial (negativeBraidEquiv R hv) (F R v) w t.1 *
        QuantumGroup.K R v t.2.1 *
        CoxeterSystem.pbwMonomial (braidEquivOfNotRoot R hv) (E R v) w t.2.2)) = x := by
  have hvec (t : (Fin w.length → ℕ) × Y × (Fin w.length → ℕ)) :
      simplyLacedFullPBWBasis R hv hSL cs hD hw hw₀ t =
        CoxeterSystem.pbwMonomial (negativeBraidEquiv R hv) (F R v) w t.1 *
          QuantumGroup.K R v t.2.1 *
          CoxeterSystem.pbwMonomial (braidEquivOfNotRoot R hv) (E R v) w t.2.2 :=
    simplyLacedFullPBWBasis_apply R hv hSL cs hD hw hw₀ t.1 t.2.2 t.2.1
  simpa only [Finsupp.linearCombination_apply, hvec] using
    (simplyLacedFullPBWBasis R hv hSL cs hD hw hw₀).linearCombination_repr x

include hSL hD in
/-- A longest reduced word and the full PBW basis exist without a supplied word, basis,
spanning assertion, or linear equivalence, over any quantum coefficient field. -/
theorem exists_simplyLacedFullPBWBasis :
    ∃ w : List I, cs.IsReduced w ∧ cs.wordProd w = cs.longestElement ∧
      ∃ b : Basis ((Fin w.length → ℕ) × Y × (Fin w.length → ℕ)) k (QuantumGroup R v),
        ∀ a μ c, b (a, μ, c) =
          CoxeterSystem.pbwMonomial (negativeBraidEquiv R hv) (F R v) w a * QuantumGroup.K R v μ *
            CoxeterSystem.pbwMonomial (braidEquivOfNotRoot R hv) (E R v) w c := by
  obtain ⟨w, hw, he⟩ := cs.exists_isReduced cs.longestElement
  exact ⟨w, hw, he.symm, simplyLacedFullPBWBasis R hv hSL cs hD hw he.symm,
    fun a μ c ↦ simplyLacedFullPBWBasis_apply R hv hSL cs hD hw he.symm a c μ⟩

end LieLean.QuantumGroup
