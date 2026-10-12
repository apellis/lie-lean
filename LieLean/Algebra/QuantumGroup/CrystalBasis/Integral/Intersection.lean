/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Integral.Strings
import LieLean.Algebra.QuantumGroup.PBW.ProductNorm.IntrinsicDegree

/-!
# Original integral/crystal intersection under raising words

These are genuine operators and lattices, not norm-defined replacements. The residue
coordinate integrality assertion is still a separate theorem, not a hypothesis here.
-/

open LieLean LusztigF
noncomputable section
namespace LieLean.QuantumGroup
open GrandLoop
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩
variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- The actual Kashiwara-word representatives belong to the original integral form. -/
theorem fWi_mem_original_integral (w : List I) :
    negativeQuotientEquiv D (fWi transcendental_ratFunc_X w) ∈ quotientIntegralForm D := by
  induction w with
  | nil =>
    change negativeQuotientEquiv D (Submodule.Quotient.mk (1 : LusztigF 𝕂 I)) ∈ _
    change toQuotient D 𝕧 1 ∈ _
    rw [map_one]
    exact one_mem _
  | cons i w ih => exact negative_kF_mem_integral D i ih

/-- Raising preserves the actual lattice at infinity with no ambient root-regularity premise. -/
theorem kE_mem_original_lattice (i : I) {x : Um D 𝕧}
    (hx : x ∈ latInf transcendental_ratFunc_X InfinityLocalRing) :
    kE transcendental_ratFunc_X i x ∈ latInf transcendental_ratFunc_X InfinityLocalRing := by
  let := Fintype.ofFinite I
  exact kashiwaraE_mem_latInf' (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum i x hx

/-- Every raising word preserves the intersection of the original integral form and the
existing crystal lattice. This does not assert that its crystal coordinates are integers. -/
theorem raisingWord_mem_original_intersection (u : List I) {x : Um D 𝕧}
    (hxI : negativeQuotientEquiv D x ∈ quotientIntegralForm D)
    (hxL : x ∈ latInf transcendental_ratFunc_X InfinityLocalRing) :
    negativeQuotientEquiv D (u.foldr (fun i y ↦ kE transcendental_ratFunc_X i y) x) ∈
      quotientIntegralForm D ∧
      u.foldr (fun i y ↦ kE transcendental_ratFunc_X i y) x ∈
        latInf transcendental_ratFunc_X InfinityLocalRing := by
  induction u with
  | nil => exact ⟨hxI, hxL⟩
  | cons i u ih =>
    exact ⟨negative_kE_mem_integral D i ih.1, kE_mem_original_lattice D i ih.2⟩

namespace Modified
variable {Y : Type*} [AddCommGroup Y] (R : D.RootDatum Y)

/-- Load-bearing PBW consumer: arbitrary raising words on the original reduced-word PBW
preimages remain in the original integral/crystal intersection, with neither integrality nor
lattice membership supplied as hypotheses. -/
theorem integralPBWPreimage_raisingWord_mem {W : Type*} [Group W]
    {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W} {w : List I}
    (hw : cs.IsReduced w) (c : Fin w.length → ℕ) (u : List I) :
    let x := (negativeQuotientEquiv D).symm (integralPBWPreimage R hw c)
    negativeQuotientEquiv D (u.foldr (fun i y ↦ kE transcendental_ratFunc_X i y) x) ∈
      quotientIntegralForm D ∧
      u.foldr (fun i y ↦ kE transcendental_ratFunc_X i y) x ∈
        latInf transcendental_ratFunc_X InfinityLocalRing := by
  apply raisingWord_mem_original_intersection D u
  · simpa only [LinearEquiv.apply_symm_apply] using (integralPBWPreimage R hw c).property
  · exact PBWProductNorm.mem_lattice_degree R hw c

end Modified
end LieLean.QuantumGroup
