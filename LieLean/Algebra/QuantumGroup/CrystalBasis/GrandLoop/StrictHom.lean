/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.HighestWeightTensor
import LieLean.RepresentationTheory.Crystal.StrictHomConnected

/-!
# Strict morphisms out of `B(λ)`

Hong–Kang, GSM 42, Proposition 4.5.8, for the crystal `B(λ)` of the crystal base
`(L(λ), B(λ))` of `L_q(λ)` (`GrandLoop.crystalHW`): a strict morphism from `B(λ)` to a connected
crystal is an isomorphism. This is the abstract statement
`Crystal.StrictHom.bijective_of_fWord`, applied with the highest weight element `u_λ`
(`GrandLoop.e_topHW`), which generates `B(λ)` (`GrandLoop.exists_fWord_crystalHW`).

## Main results

* `LieLean.QuantumGroup.GrandLoop.crystalHW_strictHom_bijective`: **Proposition 4.5.8**.
* `LieLean.QuantumGroup.GrandLoop.crystalHWEquivOfStrictHom`: the resulting isomorphism.

## References

* J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, AMS 2002,
  Proposition 4.5.8.
-/

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}
  [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)

/-- **Hong–Kang, Proposition 4.5.8.** A strict morphism from the crystal `B(λ)` of `L_q(λ)` to a
connected crystal is bijective. -/
theorem crystalHW_strictHom_bijective (Λ : Dom R) {B : Type*} {C : Crystal R.crystalDatum B}
    (ψ : Crystal.StrictHom (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ) C)
    (hconn : ∀ x : B, C.closure {x} = Set.univ) : Function.Bijective ψ :=
  ψ.bijective_of_fWord (fun j ↦ e_topHW hinj hϖ hϖv hk hfund Λ j)
    (exists_fWord_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ) hconn

/-- The isomorphism `B(λ) ≅ B` given by a strict morphism to a connected crystal
(Proposition 4.5.8). -/
def crystalHWEquivOfStrictHom (Λ : Dom R) {B : Type*} {C : Crystal R.crystalDatum B}
    (ψ : Crystal.StrictHom (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ) C)
    (hconn : ∀ x : B, C.closure {x} = Set.univ) :
    Crystal.Equiv (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ) C :=
  ψ.equivOfFWord (fun j ↦ e_topHW hinj hϖ hϖv hk hfund Λ j)
    (exists_fWord_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ) hconn

end GrandLoop

end LieLean.QuantumGroup
