/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.RankTwoCommutingContextSpan
import LieLean.LinearAlgebra.Matrix.Cartan.BraidOuter

/-!
# Simply-laced reduced-word independence of ordered PBW spans

## Main results

* `QuantumGroup.span_pbwMonomial_of_braidMove_of_simplyLaced`: an actual Coxeter braid
  move preserves the ordered span for Lusztig's constructed braid automorphisms.
* `QuantumGroup.span_pbwMonomial_of_isReduced_of_simplyLaced`: reduced words with the
  same Coxeter-group product have equal ordered spans at non-root-of-unity parameters.

Simply-lacedness discharges the existing outer-node braid condition. No finite-type,
longest-word spanning, linear independence or basis conclusion is asserted.

## References

Reconstructed from the two local contextual span theorems and the repository's Matsumoto theorem.
-/

noncomputable section
namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]
  (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hSL : D.cartanMatrix.IsSimplyLaced)

include hSL

/-- Every actual Coxeter braid move preserves the ordered span in simply-laced type.
The A₂ case uses the full braid relation with its outer-node condition discharged by
`Matrix.IsSimplyLaced.braidOuterCondition`; the commuting case needs no such condition. -/
theorem span_pbwMonomial_of_braidMove_of_simplyLaced {u w : List I}
    (hm : D.cartanMatrix.coxeterMatrix.BraidMove u w) :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv') (E R v) u)) =
      Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
        (braidEquivOfNotRoot R hv') (E R v) w)) := by
  obtain ⟨p, s, i, j, hij, _, rfl, rfl⟩ := hm
  rcases hSL hij with h0 | h1
  · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i j).mp h0
    have hm : D.cartanMatrix.coxeterMatrix i j = 2 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij, h0, h0']
      rfl
    have hm' : D.cartanMatrix.coxeterMatrix j i = 2 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij.symm, h0, h0']
      rfl
    have hw : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix i j = [i, j] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm]
      rfl
    have hw' : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix j i = [j, i] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm']
      rfl
    rw [hw, hw']
    exact span_pbwMonomial_commuting_context_of_not_root R v hv' hij h0 p s
  · have h1' : D.cartanMatrix j i = -1 := by
      rcases hSL hij.symm with hz | hn
      · have := (D.isGeneralizedCartan_cartanMatrix.zero_comm j i).mp hz
        omega
      · exact hn
    have hm : D.cartanMatrix.coxeterMatrix i j = 3 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij, h1, h1']
      rfl
    have hm' : D.cartanMatrix.coxeterMatrix j i = 3 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij.symm, h1, h1']
      rfl
    have hD : D.BraidOuterCondition :=
      ⟨hSL.braidOuterCondition.simple, hSL.braidOuterCondition.double,
        hSL.braidOuterCondition.triple⟩
    have hw : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix i j = [j, i, j] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm]
      rfl
    have hw' : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix j i = [i, j, i] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm']
      rfl
    rw [hw, hw']
    exact (span_pbwMonomial_a2_context_of_not_root R v hij h1 h1' hv' hD p s).symm

/-- Reduced words for the same Coxeter-group element have the same actual ordered PBW
span in simply-laced type, at a non-root-of-unity parameter. This is span independence
only: it does not say that the span is the entire positive quantum group. -/
theorem span_pbwMonomial_of_isReduced_of_simplyLaced {W : Type*} [Group W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {u w : List I}
    (hu : cs.IsReduced u) (hw : cs.IsReduced w) (huw : cs.wordProd u = cs.wordProd w) :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv') (E R v) u)) =
      Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
        (braidEquivOfNotRoot R hv') (E R v) w)) := by
  exact CoxeterSystem.eq_of_reflTransGen_braidMove
    (fun _ _ _ hm ↦ span_pbwMonomial_of_braidMove_of_simplyLaced R v hv' hSL hm)
    hu (CoxeterSystem.reflTransGen_braidMove_of_isReduced hu hw huw)

end QuantumGroup
