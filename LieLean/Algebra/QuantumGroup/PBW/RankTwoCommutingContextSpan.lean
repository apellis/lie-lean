/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.RankTwoA2ContextSpan

/-!
# Ordered PBW spans for commuting nodes in word context

## Main results

* `QuantumGroup.span_pbwMonomial_commuting_braid`: the actual two-letter ordered spans agree.
* `QuantumGroup.span_pbwMonomial_commuting_context`: equality in arbitrary word context,
  using the full operator relation supplied by the Lusztig generator-image formulas.
* `QuantumGroup.span_pbwMonomial_commuting_context_of_not_root`: specialization to the
  constructed braid automorphisms at non-root-of-unity parameters, with no outer-node condition.

These are ordered-span equalities, not global spanning or basis statements.

## References

Reconstructed from the recursive PBW definition, disconnected-node quantum Serre relation,
and the repository's full orthogonal braid relation.
-/

open LieLean

noncomputable section
namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k)
  (T : I → QuantumGroup R v ≃ₐ[k] QuantumGroup R v)
  {i j : I}

/-- For disconnected nodes the actual two-letter recursive monomial is the ordered
product of powers of the two positive generators. -/
theorem pbwMonomial_commuting_eq
    (Hi : HasBraidGeneratorImages i (T i).toAlgHom)
    (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) (c : Fin [i, j].length → ℕ) :
    CoxeterSystem.pbwMonomial T (E R v) [i, j] c =
      E R v i ^ c 0 * E R v j ^ c 1 := by
  have hE : (T i) (E R v j) = E R v j := by
    change (T i).toAlgHom (E R v j) = _
    rw [Hi.map_E, ite_eq_right hij.symm, braidEj_eq_of_cartanMatrix_eq_zero h0]
  simp only [CoxeterSystem.pbwMonomial, map_pow, map_one, mul_one]
  exact congrArg (fun x ↦ E R v i ^ c 0 * x ^ c 1) hE

/-- A length-two commuting braid move preserves the actual local ordered PBW span.
Swapping the exponents already gives equality of the underlying ranges. -/
theorem span_pbwMonomial_commuting_braid
    (Hi : HasBraidGeneratorImages i (T i).toAlgHom)
    (Hj : HasBraidGeneratorImages j (T j).toAlgHom)
    (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v) [i, j])) =
      Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v) [j, i])) := by
  have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i j).mp h0
  have hc := E_commute_E_of_cartanMatrix_eq_zero (R := R) (v := v) h0
  congr 1
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨![c 1, c 0], ?_⟩
    rw [pbwMonomial_commuting_eq R v T Hj hij.symm h0',
      pbwMonomial_commuting_eq R v T Hi hij h0]
    exact (hc.pow_pow (c 0) (c 1)).eq.symm
  · rintro ⟨c, rfl⟩
    refine ⟨![c 1, c 0], ?_⟩
    rw [pbwMonomial_commuting_eq R v T Hi hij h0,
      pbwMonomial_commuting_eq R v T Hj hij.symm h0']
    exact (hc.pow_pow (c 1) (c 0)).eq

/-- Commuting-node ordered-span equality in arbitrary context. The full equality
`T i * T j = T j * T i`, not merely its values on the local generators, transports the suffix. -/
theorem span_pbwMonomial_commuting_context
    (Hi : HasBraidGeneratorImages i (T i).toAlgHom)
    (Hj : HasBraidGeneratorImages j (T j).toAlgHom)
    (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) (p s : List I) :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v)
      (p ++ [i, j] ++ s))) =
      Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v)
        (p ++ [j, i] ++ s))) := by
  apply CoxeterSystem.span_pbwMonomial_context T (E R v)
    (span_pbwMonomial_commuting_braid R v T Hi Hj hij h0)
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    using Hi.equiv_comm Hj hij h0

/-- At a non-root-of-unity parameter, the constructed Lusztig automorphisms preserve
ordered PBW spans under every contextual commuting-node move. No outer-node condition is needed. -/
theorem span_pbwMonomial_commuting_context_of_not_root [NeZero v]
    (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) (p s : List I) :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv') (E R v) (p ++ [i, j] ++ s))) =
      Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
        (braidEquivOfNotRoot R hv') (E R v) (p ++ [j, i] ++ s))) := by
  have H (l : I) : HasBraidGeneratorImages l
      (braidEquivOfNotRoot R hv' l).toAlgHom :=
    braidHom_hasBraidGeneratorImages
      (braidGeneric_of_braidSerreGeneric (shortNode_braidGeneric_of_not_root hv' l).sub_ne
        (braidSerreGeneric_of_not_root hv' l))
      (transformedSerre_of_braidSerreGeneric
        (shortNode_braidGeneric_of_not_root hv' l).sub_ne (braidSerreGeneric_of_not_root hv' l))
  exact span_pbwMonomial_commuting_context R v (braidEquivOfNotRoot R hv')
    (H i) (H j) hij h0 p s

end LieLean.QuantumGroup
