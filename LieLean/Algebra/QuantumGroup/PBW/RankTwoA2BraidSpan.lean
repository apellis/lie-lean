/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.RankTwoA2LocalSpan
import LieLean.Algebra.QuantumGroup.PBW.Monomials

/-!
# Ordered spans of the actual three-letter A₂ PBW words

## Main results

The recursive `CoxeterSystem.pbwMonomial` for `iji` spans the actual two-generator
subalgebra. Consequently the actual words `iji` and `jij` have equal ordered spans.
The ambient Cartan datum is unrestricted. The braid operators must have the
existing Lusztig generator images, and the nonzero denominator needed by the
third-root-vector formula is explicit. This is not a global longest-word spanning
or basis theorem.

## References

Reconstructed from the repository's local A₂ straightening and third-root-vector
identity, with the actual recursive PBW monomial definition.
-/

noncomputable section
namespace QuantumGroup
variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]
  (T : I → QuantumGroup R v ≃ₐ[k] QuantumGroup R v)
  {i j : I} (Hi : HasBraidGeneratorImages i (T i).toAlgHom)
  (Hj : HasBraidGeneratorImages j (T j).toAlgHom)
  (hij : i ≠ j) (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)

include Hi Hj hij h h' hq

/-- The actual recursive three-letter PBW monomial is the local A₂ monomial. -/
theorem pbwMonomial_a2_eq (c : Fin [i, j, i].length → ℕ) :
    CoxeterSystem.pbwMonomial T (E R v) [i, j, i] c =
      a2PBWMono R v i j (c 0, c 1, c 2) := by
  have h₂ := a2_rootVector_two hij Hi
  have h₃ := a2_rootVector_three Hi Hj hij h h' hq
  change (T i) (E R v j) = braidEj R v i j at h₂
  change (T i) ((T j) (E R v i)) = E R v j at h₃
  simp only [CoxeterSystem.pbwMonomial, map_mul, map_pow, map_one, mul_one]
  change E R v i ^ c 0 * ((T i) (E R v j) ^ c 1 *
    (T i) ((T j) (E R v i)) ^ c 2) = _
  rw [h₂, h₃]
  exact (mul_assoc _ _ _).symm

/-- The actual PBW word `iji` spans the two-generator subalgebra. -/
theorem span_pbwMonomial_a2 :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v) [i, j, i])) =
      (Algebra.adjoin k {E R v i, E R v j}).toSubmodule := by
  have hr : Set.range (CoxeterSystem.pbwMonomial T (E R v) [i, j, i]) =
      Set.range (a2PBWMono R v i j) := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨(c 0, c 1, c 2), (pbwMonomial_a2_eq R v T Hi Hj hij h h' hq c).symm⟩
    · rintro ⟨⟨a, b, c⟩, rfl⟩
      exact ⟨![a, b, c], pbwMonomial_a2_eq R v T Hi Hj hij h h' hq _⟩
  rw [hr]
  exact span_a2PBWMono_pair R v hij h h'

/-- The genuine three-letter braid move preserves the local ordered PBW span. -/
theorem span_pbwMonomial_a2_braid :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v) [i, j, i])) =
      Submodule.span k (Set.range (CoxeterSystem.pbwMonomial T (E R v) [j, i, j])) := by
  have hqj : v ^ D.d j - (v ^ D.d j)⁻¹ ≠ 0 := by
    rwa [← D.d_eq_of_simply_laced_edge h h']
  rw [span_pbwMonomial_a2 R v T Hi Hj hij h h' hq,
    span_pbwMonomial_a2 R v T Hj Hi hij.symm h' h hqj, Set.pair_comm]

end QuantumGroup
