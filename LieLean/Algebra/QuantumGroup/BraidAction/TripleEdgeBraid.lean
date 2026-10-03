/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.General
import LieLean.Algebra.QuantumGroup.BraidAction.TripleEdge

/-!
# The braid automorphism at the triple node of `G₂`

For an exact two-node Cartan datum with entries `aᵢⱼ = -3`, `aⱼᵢ = -1` (type `G₂`, with `i` the
short simple root), Lusztig's `Tᵢ` is an algebra automorphism of `U`.

## Main results

* `QuantumGroup.tripleEdge_transformedSerre`: the transformed Serre relations at `i`, from the
  degree-three computations of `TripleEdge.lean`.
* `QuantumGroup.tripleEdgeBraidEquiv`: `Tᵢ` as an algebra equivalence, with inverse the
  reversal-conjugate of `Tᵢ` (`braidEquiv`).

Assumptions: exactly two distinct nodes, entries `(-3, -1)`, arbitrary field and root-datum
lattice, `v ≠ 0`, `vᵢ - vᵢ⁻¹ ≠ 0`, `[3]ᵢ! ≠ 0` and `vᵢ⁴ + 1 ≠ 0` (the last is inherited from
the proof of the neighbor-first Serre relation in `TripleEdge.lean`; its necessity is not
claimed). The automorphism at the other node and the length-six braid relation are not
treated here.

## References

Reconstructed from the quotient presentation.
-/

noncomputable section

namespace QuantumGroup

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  {i j : I} (hij : i ≠ j) (hall : ∀ l, l = i ∨ l = j)
  (h : D.cartanMatrix i j = -3) (h' : D.cartanMatrix j i = -1)

include hij hall h h' in
/-- The transformed quantum Serre relations at the triple node of an exact `G₂` datum. -/
theorem tripleEdge_transformedSerre (h4 : (v ^ D.d i) ^ 4 + 1 ≠ 0) :
    TransformedSerre R v i where
  serre_E l m hlm hl := by
    rcases hall l with rfl | rfl <;> rcases hall m with rfl | rfl
    · exact (hlm rfl).elim
    · exact (hl rfl).elim
    · simpa [braidImageE, hij.symm] using
        qSerre_braidEj_braidEi_of_triple_edge (R := R) (NeZero.ne v) h h' h4
    · exact (hlm rfl).elim
  serre_F l m hlm hl := by
    rcases hall l with rfl | rfl <;> rcases hall m with rfl | rfl
    · exact (hlm rfl).elim
    · exact (hl rfl).elim
    · simpa [braidImageF, hij.symm] using
        qSerre_braidFj_braidFi_of_triple_edge (R := R) (NeZero.ne v) h h' h4
    · exact (hlm rfl).elim

omit [DecidableEq I] [NeZero v] in
include hij hall h in
/-- The generic parameter hypotheses at the triple node reduce to `vᵢ - vᵢ⁻¹ ≠ 0` and
`[3]ᵢ! ≠ 0`. -/
theorem tripleEdge_braidGeneric (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (h3 : qFactorial (v ^ D.d i) 3 ≠ 0) : BraidGeneric D v i where
  sub_ne := hq
  qFactorial_ne l hl := by
    rcases hall l with rfl | rfl
    · exact (hl rfl).elim
    · simpa [negA, h] using h3

/-- **Lusztig's braid automorphism at the triple node of `G₂`**, with explicit inverse. -/
def tripleEdgeBraidEquiv (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (h3 : qFactorial (v ^ D.d i) 3 ≠ 0) (h4 : (v ^ D.d i) ^ 4 + 1 ≠ 0) :
    QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  braidEquiv (tripleEdge_braidGeneric hij hall h hq h3)
    (tripleEdge_transformedSerre hij hall h h' h4)

end QuantumGroup
