/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.FiniteTypeArtin
import LieLean.LinearAlgebra.Matrix.Cartan.FiniteRankTwo

/-!
# The braid group action for every Cartan datum of finite type

For any Cartan datum `D` whose Cartan matrix is of finite type (Mathlib's
`Matrix.IsFiniteCartan`, i.e. `diag(d) A` positive definite for some positive `d`), the
third-node condition `LusztigCartanDatum.BraidOuterCondition` holds
(`LusztigCartanDatum.braidOuterCondition_of_isFiniteCartan`, from
`Matrix.IsFiniteCartan.braidOuterCondition`), so the Artin group of the Coxeter matrix of `D`
acts on `U` by Lusztig's automorphisms `σᵢ ↦ Tᵢ` with no further hypothesis on the diagram
(`QuantumGroup.braidArtinHomOfIsFiniteCartan`, for `v` not a root of unity).

## Main definitions / results

* `LusztigCartanDatum.braidOuterCondition_of_isFiniteCartan`.
* `QuantumGroup.braidArtinHomOfIsFiniteCartan`, with `braidArtinHomOfIsFiniteCartan_artinGenerator`.

## References

G. Lusztig, *Introduction to quantum groups*, 39.4.3 (check). The finite-type diagram facts are
proved from positive definiteness in `LinearAlgebra/Matrix/Cartan/FiniteRankTwo.lean`, not by
the classification.
-/

/-- A Cartan datum of finite type satisfies the third-node condition of the braid relations. -/
theorem LusztigCartanDatum.braidOuterCondition_of_isFiniteCartan {I : Type*} [Fintype I]
    [DecidableEq I] {D : LusztigCartanDatum I} (hA : D.cartanMatrix.IsFiniteCartan) :
    D.BraidOuterCondition :=
  LusztigCartanDatum.BraidOuterCondition.of_cartanMatrix_eq rfl hA.braidOuterCondition

noncomputable section

namespace QuantumGroup

variable {k Y : Type*} [Field k] [AddCommGroup Y] {v : k} [NeZero v] {I : Type*} [Fintype I]
  [DecidableEq I] {D : LusztigCartanDatum I} (R : D.RootDatum Y)
  (hA : D.cartanMatrix.IsFiniteCartan) (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1)

/-- **The braid group action for every Cartan datum of finite type**: the Artin group of the
Coxeter matrix of `D` acts on `U` by `σᵢ ↦ Tᵢ = braidEquivOfNotRoot`, for `v` not a root of
unity, over any field and root-datum lattice. -/
def braidArtinHomOfIsFiniteCartan :
    D.cartanMatrix.coxeterMatrix.ArtinGroup →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  braidArtinHomOfCartanMatrix R rfl hA.braidOuterCondition hpow

@[simp]
theorem braidArtinHomOfIsFiniteCartan_artinGenerator (i : I) :
    braidArtinHomOfIsFiniteCartan R hA hpow (D.cartanMatrix.coxeterMatrix.artinGenerator i) =
      braidEquivOfNotRoot R hpow i :=
  braidArtinHomOfCartanMatrix_artinGenerator R rfl _ hpow i

end QuantumGroup
