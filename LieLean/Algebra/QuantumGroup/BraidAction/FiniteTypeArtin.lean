/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.GeneralArtin
import LieLean.Algebra.QuantumGroup.BraidAction.Families
import LieLean.Algebra.QuantumGroup.BraidAction.TripleEdgeArtin
import LieLean.LinearAlgebra.Matrix.Cartan.BraidOuter

/-!
# Braid group actions for the Cartan matrices of finite type

For a Cartan datum `D` whose Cartan matrix is a given matrix `A` satisfying
`Matrix.BraidOuterCondition` (in particular any of Mathlib's finite-type Cartan matrices), the
Artin group of the Coxeter matrix of `A` acts on `U` by algebra automorphisms,
`σᵢ ↦ Tᵢ = braidEquivOfNotRoot`, for any `v` that is not a root of unity (any field, any
compatible symmetrizer and root-datum lattice).

## Main definitions / results

* `LusztigCartanDatum.BraidOuterCondition.of_cartanMatrix_eq`.
* `QuantumGroup.braidArtinHomOfCartanMatrix`: the action of `A.coxeterMatrix.ArtinGroup`, with
  generator formulas `braidArtinHomOfCartanMatrix_artinGenerator`,
  `braidArtinHomOfCartanMatrix_images`.
* `QuantumGroup.braidArtinHomOfSimplyLaced`: the action for every simply-laced Cartan datum
  (e.g. affine `Ãₙ`, including the triangle `Ã₂`).
* `QuantumGroup.braidArtinHom_A`, `_B`, `_C`, `_D`, `_E`, `_F₄`, `_G₂`: the named actions for
  Mathlib's `CartanMatrix.A n`, `B n`, `C n`, `D n`, `E n` (all `n`), `F₄`, `G₂`.
* `QuantumGroup.braidArtinHom_B_artinGenerator` (and `_C`, `_F₄`, `_G₂`): on every generator they
  agree with the earlier actions `artinHom_B`, `artinHom_C`, `artinHom_F₄` (from
  `BraidAction/Families.lean`) and `artinHom_G₂` (from `BraidAction/TripleEdgeArtin.lean`).

## References

G. Lusztig, *Introduction to quantum groups*, 39.4.3. Reconstructed; the relations are
those of `BraidAction/GeneralArtin.lean`.
-/

open LieLean


/-- A Cartan datum whose Cartan matrix satisfies `Matrix.BraidOuterCondition` satisfies
`LusztigCartanDatum.BraidOuterCondition`. -/
theorem LusztigCartanDatum.BraidOuterCondition.of_cartanMatrix_eq {I : Type*}
    {D : LusztigCartanDatum I} {A : Matrix I I ℤ} (hD : D.cartanMatrix = A)
    (hA : A.BraidOuterCondition) : D.BraidOuterCondition := by
  subst hD
  exact ⟨hA.simple, hA.double, hA.triple⟩

noncomputable section

namespace LieLean.QuantumGroup

variable {k Y : Type*} [Field k] [AddCommGroup Y] {v : k} [NeZero v]

section General

variable {I : Type*} [DecidableEq I] {D : LusztigCartanDatum I} (R : D.RootDatum Y)
  {A : Matrix I I ℤ} (hD : D.cartanMatrix = A) (hA : A.BraidOuterCondition)
  (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1)

/-- **The braid group action for a Cartan datum with a given Cartan matrix `A`** satisfying
`Matrix.BraidOuterCondition`: the Artin group of `A.coxeterMatrix` acts on `U` by
`σᵢ ↦ Tᵢ = braidEquivOfNotRoot`, for `v` not a root of unity. -/
def braidArtinHomOfCartanMatrix :
    A.coxeterMatrix.ArtinGroup →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  CoxeterMatrix.artinLift (fun i ↦ braidEquivOfNotRoot R hpow i) (by
    have h := isBraidLiftable_braidEquivOfGeneric (R := R)
      (fun i ↦ (shortNode_braidGeneric_of_not_root hpow i).sub_ne)
      (braidSerreGeneric_of_not_root hpow)
      (fun i ↦ LusztigF.qFactorial_ne_zero_of_not_root (NeZero.ne v) hpow i 3)
      (LusztigCartanDatum.BraidOuterCondition.of_cartanMatrix_eq hD hA)
    rw [hD] at h
    exact h)

@[simp]
theorem braidArtinHomOfCartanMatrix_artinGenerator (i : I) :
    braidArtinHomOfCartanMatrix R hD hA hpow (A.coxeterMatrix.artinGenerator i) =
      braidEquivOfNotRoot R hpow i :=
  CoxeterMatrix.artinLift_artinGenerator _ _ i

/-- The generator `σᵢ` acts by Lusztig's formulas at `i`. -/
theorem braidArtinHomOfCartanMatrix_images (i : I) :
    HasBraidGeneratorImages i
      (braidArtinHomOfCartanMatrix R hD hA hpow (A.coxeterMatrix.artinGenerator i)).toAlgHom := by
  rw [braidArtinHomOfCartanMatrix_artinGenerator]
  exact braidHom_hasBraidGeneratorImages
    (braidGeneric_of_braidSerreGeneric (shortNode_braidGeneric_of_not_root hpow i).sub_ne
      (braidSerreGeneric_of_not_root hpow i))
    (transformedSerre_of_braidSerreGeneric (shortNode_braidGeneric_of_not_root hpow i).sub_ne
      (braidSerreGeneric_of_not_root hpow i))

omit hD hA in
/-- **The braid group action for any simply-laced Cartan datum** (any rank; triangles such as
affine `Ã₂` allowed), for `v` not a root of unity. -/
def braidArtinHomOfSimplyLaced (hSL : D.cartanMatrix.IsSimplyLaced) :
    D.cartanMatrix.coxeterMatrix.ArtinGroup →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  braidArtinHomOfCartanMatrix R rfl hSL.braidOuterCondition hpow

omit hD hA in
@[simp]
theorem braidArtinHomOfSimplyLaced_artinGenerator (hSL : D.cartanMatrix.IsSimplyLaced) (i : I) :
    braidArtinHomOfSimplyLaced R hpow hSL (D.cartanMatrix.coxeterMatrix.artinGenerator i) =
      braidEquivOfNotRoot R hpow i :=
  braidArtinHomOfCartanMatrix_artinGenerator R rfl _ hpow i

end General

section Named

variable {n : ℕ} (hpow : ∀ m : ℕ, 0 < m → v ^ m ≠ 1)

/-- The braid group action of type `Aₙ₋₁` (Mathlib's `CartanMatrix.A n`), every rank. -/
def braidArtinHom_A {D : LusztigCartanDatum (Fin n)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.A n) :
    (CartanMatrix.A n).coxeterMatrix.ArtinGroup →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  braidArtinHomOfCartanMatrix R hD (CartanMatrix.braidOuterCondition_A n) hpow

/-- The braid group action of type `Bₙ` (Mathlib's `CartanMatrix.B n`), every rank. -/
def braidArtinHom_B {D : LusztigCartanDatum (Fin n)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.B n) :
    (CartanMatrix.B n).coxeterMatrix.ArtinGroup →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  braidArtinHomOfCartanMatrix R hD (CartanMatrix.braidOuterCondition_B n) hpow

/-- The braid group action of type `Cₙ` (Mathlib's `CartanMatrix.C n`), every rank. -/
def braidArtinHom_C {D : LusztigCartanDatum (Fin n)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.C n) :
    (CartanMatrix.C n).coxeterMatrix.ArtinGroup →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  braidArtinHomOfCartanMatrix R hD (CartanMatrix.braidOuterCondition_C n) hpow

/-- The braid group action of type `Dₙ` (Mathlib's `CartanMatrix.D n`), every rank. -/
def braidArtinHom_D {D : LusztigCartanDatum (Fin n)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.D n) :
    (CartanMatrix.D n).coxeterMatrix.ArtinGroup →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  braidArtinHomOfCartanMatrix R hD (CartanMatrix.braidOuterCondition_D n) hpow

/-- The braid group action for Mathlib's `CartanMatrix.E n` (types `E₆`, `E₇`, `E₈` for
`n = 6, 7, 8`, and the same diagram pattern for every `n`). -/
def braidArtinHom_E {D : LusztigCartanDatum (Fin n)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.E n) :
    (CartanMatrix.E n).coxeterMatrix.ArtinGroup →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  braidArtinHomOfCartanMatrix R hD (CartanMatrix.braidOuterCondition_E n) hpow

/-- The braid group action of type `F₄` (Mathlib's `CartanMatrix.F₄`). -/
def braidArtinHom_F₄ {D : LusztigCartanDatum (Fin 4)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.F₄) :
    CartanMatrix.F₄.coxeterMatrix.ArtinGroup →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  braidArtinHomOfCartanMatrix R hD CartanMatrix.braidOuterCondition_F₄ hpow

/-- The braid group action of type `G₂` (Mathlib's `CartanMatrix.G₂`). -/
def braidArtinHom_G₂ {D : LusztigCartanDatum (Fin 2)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.G₂) :
    CartanMatrix.G₂.coxeterMatrix.ArtinGroup →* (QuantumGroup R v ≃ₐ[k] QuantumGroup R v) :=
  braidArtinHomOfCartanMatrix R hD CartanMatrix.braidOuterCondition_G₂ hpow

/-- Agreement with the local-constructor action `artinHom_B` on every generator. -/
theorem braidArtinHom_B_artinGenerator {D : LusztigCartanDatum (Fin n)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.B n) (i : Fin n) :
    braidArtinHom_B hpow R hD ((CartanMatrix.B n).coxeterMatrix.artinGenerator i) =
      artinHom_B R hD hpow (SimpleDoubleArtinGroup.generator i) := by
  have H := (braidArtinHomOfCartanMatrix_images R hD (CartanMatrix.braidOuterCondition_B n)
    hpow i).unique (artinHom_B_images R hD hpow i)
  exact DFunLike.ext _ _ fun x ↦ DFunLike.congr_fun H x

/-- Agreement with the local-constructor action `artinHom_C` on every generator. -/
theorem braidArtinHom_C_artinGenerator {D : LusztigCartanDatum (Fin n)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.C n) (i : Fin n) :
    braidArtinHom_C hpow R hD ((CartanMatrix.C n).coxeterMatrix.artinGenerator i) =
      artinHom_C R hD hpow (SimpleDoubleArtinGroup.generator i) := by
  have H := (braidArtinHomOfCartanMatrix_images R hD (CartanMatrix.braidOuterCondition_C n)
    hpow i).unique (artinHom_C_images R hD hpow i)
  exact DFunLike.ext _ _ fun x ↦ DFunLike.congr_fun H x

/-- Agreement with the local-constructor action `artinHom_F₄` on every generator. -/
theorem braidArtinHom_F₄_artinGenerator {D : LusztigCartanDatum (Fin 4)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.F₄) (i : Fin 4) :
    braidArtinHom_F₄ hpow R hD (CartanMatrix.F₄.coxeterMatrix.artinGenerator i) =
      artinHom_F₄ R hD hpow (SimpleDoubleArtinGroup.generator i) := by
  have H := (braidArtinHomOfCartanMatrix_images R hD CartanMatrix.braidOuterCondition_F₄
    hpow i).unique (artinHom_F₄_images R hD hpow i)
  exact DFunLike.ext _ _ fun x ↦ DFunLike.congr_fun H x

/-- Agreement with the `G₂` action `artinHom_G₂` on every generator. -/
theorem braidArtinHom_G₂_artinGenerator {D : LusztigCartanDatum (Fin 2)} (R : D.RootDatum Y)
    (hD : D.cartanMatrix = CartanMatrix.G₂) (i : Fin 2) :
    braidArtinHom_G₂ hpow R hD (CartanMatrix.G₂.coxeterMatrix.artinGenerator i) =
      artinHom_G₂ R hD hpow (TripleEdgeArtinGroup.generator i) := by
  have H := (braidArtinHomOfCartanMatrix_images R hD CartanMatrix.braidOuterCondition_G₂
    hpow i).unique (artinHom_G₂_images R hD hpow i)
  exact DFunLike.ext _ _ fun x ↦ DFunLike.congr_fun H x

end Named

end LieLean.QuantumGroup
