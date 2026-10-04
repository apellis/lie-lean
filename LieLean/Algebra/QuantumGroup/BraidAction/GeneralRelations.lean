/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.General
import LieLean.Algebra.QuantumGroup.BraidAction.ThreeLocalArtin

/-!
# Braid relations for the general braid automorphisms

The automorphisms `braidEquiv` of `BraidAction/General.lean` have Lusztig's generator formulas
(`HasBraidGeneratorImages`), so the constructor-independent results of
`BraidAction/OrthogonalGeneral.lean` and `BraidAction/ThreeLocalArtin.lean` apply to them.

## Main results

* `QuantumGroup.braidHom_hasBraidGeneratorImages`, `QuantumGroup.braidHom_eq`: the general
  braid homomorphism agrees with every other construction having the same generator formulas.
* `QuantumGroup.braidEquiv_comm`: `Tᵢ Tⱼ = Tⱼ Tᵢ` when `aᵢⱼ = 0`.
* `QuantumGroup.braidEquiv_braid_three`: `Tᵢ Tⱼ Tᵢ = Tⱼ Tᵢ Tⱼ` at a mutual simple edge, under the
  graph condition of `HasBraidGeneratorImages.three_braid` on the other nodes.

## References

Reconstructed; see the files cited above.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v] {i j : I}

/-- The general braid homomorphism has Lusztig's generator formulas. -/
theorem braidHom_hasBraidGeneratorImages (hg : BraidGeneric D v i)
    (hS : TransformedSerre R v i) : HasBraidGeneratorImages i (braidHom hg hS) where
  map_E l := by rw [braidHom_E]; rfl
  map_F l := by rw [braidHom_F]; rfl
  map_K μ := braidHom_K hg hS μ

/-- Any algebra endomorphism with Lusztig's generator formulas is the general braid
homomorphism. -/
theorem braidHom_eq (hg : BraidGeneric D v i) (hS : TransformedSerre R v i)
    {T : QuantumGroup R v →ₐ[k] QuantumGroup R v} (hT : HasBraidGeneratorImages i T) :
    braidHom hg hS = T :=
  (braidHom_hasBraidGeneratorImages hg hS).unique hT

/-- The length-two braid relation `Tᵢ Tⱼ = Tⱼ Tᵢ` for orthogonal nodes. -/
theorem braidEquiv_comm (hgi : BraidGeneric D v i) (hSi : TransformedSerre R v i)
    (hgj : BraidGeneric D v j) (hSj : TransformedSerre R v j) (hij : i ≠ j)
    (h0 : D.cartanMatrix i j = 0) :
    braidEquiv hgi hSi * braidEquiv hgj hSj = braidEquiv hgj hSj * braidEquiv hgi hSi :=
  HasBraidGeneratorImages.equiv_comm (braidHom_hasBraidGeneratorImages hgi hSi)
    (braidHom_hasBraidGeneratorImages hgj hSj) hij h0

/-- The length-three braid relation `Tᵢ Tⱼ Tᵢ = Tⱼ Tᵢ Tⱼ` at a mutual simple edge; every other
node meets at most one of `i, j`, with outgoing entry `0`, `-1` or `-2`. -/
theorem braidEquiv_braid_three (hgi : BraidGeneric D v i) (hSi : TransformedSerre R v i)
    (hgj : BraidGeneric D v j) (hSj : TransformedSerre R v j) (hij : i ≠ j)
    (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
    (hout : ∀ l, l ≠ i → l ≠ j →
      (D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = 0) ∨
      ((D.cartanMatrix i l = -1 ∨ D.cartanMatrix i l = -2) ∧ D.cartanMatrix j l = 0) ∨
      (D.cartanMatrix i l = 0 ∧ (D.cartanMatrix j l = -1 ∨ D.cartanMatrix j l = -2))) :
    braidEquiv hgi hSi * braidEquiv hgj hSj * braidEquiv hgi hSi =
      braidEquiv hgj hSj * braidEquiv hgi hSi * braidEquiv hgj hSj :=
  HasBraidGeneratorImages.three_equiv (braidHom_hasBraidGeneratorImages hgi hSi)
    (braidHom_hasBraidGeneratorImages hgj hSj) hij h h' hgi.sub_ne hout

end LieLean.QuantumGroup
