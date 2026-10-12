/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.ProductNorm.Realization
import LieLean.Algebra.QuantumGroup.Modified.IntegralBasisPBW
import LieLean.Algebra.QuantumGroup.PBW.RootVectorGrading

/-!
# Intrinsic homogeneity of the original integral PBW preimage

Inverse braid torus covariance gives the character. The extended realization separates
root-lattice degrees internally; realization independence transfers the actual homogeneous
representative to every supplied root datum. This realization bridge extends the source
ambient root-datum conventions to possibly nonregular supplied realizations; no regularity
premise is added to the result. The norm criterion gives actual quotient crystal-lattice
membership, not a signed canonical-basis residue or the full assertion of 41.1.6.
-/

noncomputable section
open LieLean LieLean.QuantumGroup LusztigF
namespace PBWProductNorm
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)

omit [Finite I] in
/-- The actual inverse braid reflects conjugation characters. -/
theorem inverse_mem_adWeightSpace (i : I) {χ : Y →+ ℤ} {x : QuantumGroup R 𝕧}
    (hx : x ∈ adWeightSpace R 𝕧 χ) :
    (braidEquivOfNotRoot R ratFunc_X_not_root i).symm x ∈
      adWeightSpace R 𝕧 (χ.comp (reflY R i)) := fun μ ↦ by
  have h := congrArg (braidEquivOfNotRoot R ratFunc_X_not_root i).symm
    (hx (reflY R i μ))
  simpa only [map_mul, map_smul, RightStringComparison.inverse_K, reflY_reflY,
    AddMonoidHom.comp_apply] using h

open Modified
attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU

omit [Finite I] in
/-- Inverse-braid divided PBW monomials have the usual reflected character. -/
theorem pbwDivSymm_mem_adWeightSpace (w : List I) (c : Fin w.length → ℕ) :
    pbwDivSymm R w c ∈ adWeightSpace R 𝕧 (pbwWt R w c) := by
  induction w with
  | nil => simpa [pbwDivSymm, CoxeterSystem.pbwDivMonomial, pbwWt]
      using one_mem_adWeightSpace
  | cons i w ih =>
    rw [pbwDivSymm, CoxeterSystem.pbwDivMonomial_cons, pbwWt, Ta_symm_apply]
    exact mul_mem_adWeightSpace (qDivPow_E_mem _ i _) (inverse_mem_adWeightSpace R i (ih _))

variable {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}

/-- Actual homogeneous representatives exist in an internally regular realization. -/
theorem exists_homogeneous_of_regular (hR : R.IsXRegular) {w : List I}
    (hw : cs.IsReduced w) (c : Fin w.length → ℕ) :
    ∃ ν : I →₀ ℕ, R.rootSum ν = pbwWt R w c ∧
      ∃ a : LusztigF 𝕂 I, a ∈ LusztigF.weightSpace 𝕂 ν ∧
        toQuotient D 𝕧 a = (integralPBWPreimage R hw c : Quotient D 𝕧) := by
  have hplus : pbwDivSymm R w c ∈ Algebra.adjoin 𝕂 (Set.range (E R 𝕧)) := by
    rw [← range_plusHom R 𝕧, ← quotientPlus_integralPBWPreimage R hw c]
    obtain ⟨a, ha⟩ := toQuotient_surjective D 𝕧 (integralPBWPreimage R hw c)
    exact ⟨a, congrArg (quotientPlus R) ha⟩
  obtain ⟨ν, hν, a, ha, he⟩ := exists_degree_of_mem_adWeightSpace hR ratFunc_X_not_root
    hplus (pbwDivSymm_mem_adWeightSpace R w c) ((linearIndependent_pbwDivSymm hw).ne_zero c)
  refine ⟨ν, hν, a, ha, quotientPlus_injective R ?_⟩
  rw [quotientPlus_toQuotient, quotientPlus_integralPBWPreimage]
  exact he

/-- The actual original preimage is intrinsically homogeneous for every reduced word.
This is proved, not supplied as an additional hypothesis of the norm criterion. -/
theorem exists_homogeneous {w : List I} (hw : cs.IsReduced w) (c : Fin w.length → ℕ) :
    ∃ ν : I →₀ ℕ, ∃ a : LusztigF 𝕂 I, a ∈ LusztigF.weightSpace 𝕂 ν ∧
      toQuotient D 𝕧 a = (integralPBWPreimage R hw c : Quotient D 𝕧) := by
  let := Fintype.ofFinite I
  obtain ⟨ν, _, a, ha, he⟩ := exists_homogeneous_of_regular D.extendedRootDatum
    D.isXRegular_extendedRootDatum hw c
  exact ⟨ν, a, ha, he.trans (preimage_realization_independent D.extendedRootDatum R hw c)⟩

/-- General membership in the original quotient crystal lattice, using proved homogeneity
and the actual product norm. It does not assert a signed canonical residue. -/
theorem mem_lattice {w : List I} (hw : cs.IsReduced w) (c : Fin w.length → ℕ) :
    (integralPBWPreimage R hw c : Quotient D 𝕧) ∈ quotientCrystalLattice D := by
  obtain ⟨ν, a, ha, he⟩ := exists_homogeneous R hw c
  have hx : (negativeQuotientEquiv D).symm (integralPBWPreimage R hw c) ∈
      GrandLoop.Uw D 𝕧 ν := by
    rw [← he, negativeQuotientEquiv_symm_toQuotient]
    exact ⟨a, ha, rfl⟩
  apply (mem_quotientCrystalLattice_iff D hx).mpr
  obtain ⟨b, hb⟩ := norm_residue R hw c
  exact ⟨_, hb⟩

end PBWProductNorm
