/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Integral.Augmentation

/-! Raising words extract the actual residue pairings with crystal words. -/
open LieLean LusztigF
noncomputable section
namespace LieLean.QuantumGroup
open GrandLoop
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X
local notation "hv'" => pow_ne_one_of_transcendental' transcendental_ratFunc_X
local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩
variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- Raise in the order in which the letters of a lowering word are removed. -/
def raiseAlong (w : List I) (x : Um D 𝕧) : Um D 𝕧 :=
  w.foldl (fun y i ↦ kE hvt i y) x

lemma raiseAlong_mem_lattice (w : List I) {x : Um D 𝕧}
    (hx : x ∈ latInf hvt A) : raiseAlong D w x ∈ latInf hvt A := by
  induction w generalizing x with
  | nil => exact hx
  | cons i w ih => exact ih (kE_mem_original_lattice D i hx)

lemma raiseAlong_mem_integral (w : List I) {x : Um D 𝕧}
    (hx : negativeQuotientEquiv D x ∈ quotientIntegralForm D) :
    negativeQuotientEquiv D (raiseAlong D w x) ∈ quotientIntegralForm D := by
  induction w generalizing x with
  | nil => exact hx
  | cons i w ih => exact ih (negative_kE_mem_integral D i hx)

omit [Finite I] in
lemma formU_nil (x : Um D 𝕧) :
    formU hv' (fWi hvt []) x = VermaModule.counitQ D 𝕧 x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change form D 𝕧 1 y = LusztigF.counit y
  exact form_one_left D 𝕧 y

/-- The genuine degree-zero augmentation of any element of the crystal lattice is regular
at infinity. No homogeneity assumption is required. -/
theorem counit_mem_infinity {x : Um D 𝕧} (hx : x ∈ latInf hvt A) :
    ∃ a : A, VermaModule.counitQ D 𝕧 x = algebraMap A 𝕂 a := by
  let := Fintype.ofFinite I
  rw [← formU_nil D]
  exact formU_mem (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum (NegativePart.fWord_mem_latticeInf _ _ []) hx

/-- Repeated adjointness modulo the actual uniformizer identifies a word pairing with the
augmentation after raising. This is coordinate extraction, not an operator-stability wrapper. -/
theorem word_pairing_sub_raised_counit (w : List I) {x : Um D 𝕧}
    (hx : x ∈ latInf hvt A) :
    ∃ a : A, formU hv' (fWi hvt w) x -
      VermaModule.counitQ D 𝕧 (raiseAlong D w x) = algebraMap A 𝕂 (ϖ * a) := by
  let := Fintype.ofFinite I
  induction w generalizing x with
  | nil =>
    refine ⟨0, ?_⟩
    change formU hv' (fWi hvt []) x - VermaModule.counitQ D 𝕧 x = _
    rw [formU_nil, sub_self, mul_zero, map_zero]
  | cons i w ih =>
    obtain ⟨a, ha⟩ := formU_kF_sub_kE_mem (hR := D.isXRegular_extendedRootDatum)
      InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
      InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
      D.exists_fundamental_extendedRootDatum i (NegativePart.fWord_mem_latticeInf _ _ w) hx
    obtain ⟨b, hb⟩ := ih (kE_mem_original_lattice D i hx)
    refine ⟨a + b, ?_⟩
    change formU hv' (kF hvt i (fWi hvt w)) x -
      VermaModule.counitQ D 𝕧 (raiseAlong D w (kE hvt i x)) = _
    rw [mul_add, map_add, ← ha, ← hb]
    ring

/-- Every genuine crystal-word pairing with an original integral/lattice element has an
integer residue. The integer comes from its raised degree-zero augmentation. -/
theorem word_pairing_integer_residue (w : List I) {x : Um D 𝕧}
    (hxI : negativeQuotientEquiv D x ∈ quotientIntegralForm D)
    (hxL : x ∈ latInf hvt A) :
    ∃ (z : ℤ) (a : A), formU hv' (fWi hvt w) x =
      (z : 𝕂) + algebraMap A 𝕂 (ϖ * a) := by
  obtain ⟨b, hb⟩ := counit_mem_infinity D (raiseAlong_mem_lattice D w hxL)
  have hb' : algebraMap A 𝕂 b =
      originalAugmentation D (negativeQuotientEquiv D (raiseAlong D w x)) := by
    simpa [originalAugmentation] using hb.symm
  obtain ⟨z, hz⟩ := originalAugmentation_residue_integer D
    (raiseAlong_mem_integral D w hxI) b hb'
  have hz' : Sl2.RankOne.residue ((show Sl2.RankOne.LocalRing from b) -
      (z : Sl2.RankOne.LocalRing)) = 0 := by rw [map_sub, map_intCast, hz, sub_self]
  obtain ⟨c₀, hc⟩ := (Sl2.RankOne.residue_eq_zero_iff _).mp hz'
  let c : A := c₀
  obtain ⟨a, ha⟩ := word_pairing_sub_raised_counit D w hxL
  refine ⟨z, a + c, ?_⟩
  have he : b = (z : A) + ϖ * c := by
    change b - (z : A) = ϖ * c at hc
    linear_combination hc
  rw [hb, he, map_add, map_intCast] at ha
  rw [mul_add, map_add]
  linear_combination ha

end LieLean.QuantumGroup
