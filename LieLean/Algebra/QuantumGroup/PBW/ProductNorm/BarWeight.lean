/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.LusztigF.BarQuotient
import LieLean.Algebra.QuantumGroup.PBW.ProductNorm.IntrinsicDegree

/-! Bar preserves the actual free and quotient weight spaces. These elementary
reconstructed lemmas supply the degree constraint for the PBW bar comparison;
they do not assert preservation of the crystal lattice or balancedness. -/

noncomputable section
open LieLean LieLean.QuantumGroup
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
namespace LusztigF
variable {I : Type*}

variable [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- On the original quotient, bar preserves the actual grand-loop weight space. -/
theorem quotientBar_mem_Uw {ν : I →₀ ℕ} {x : Quotient D 𝕧}
    (hx : (negativeQuotientEquiv D).symm x ∈ GrandLoop.Uw D 𝕧 ν) :
    (negativeQuotientEquiv D).symm (quotientBar D x) ∈ GrandLoop.Uw D 𝕧 ν := by
  obtain ⟨a, ha, he⟩ := hx
  have hq : toQuotient D 𝕧 a = x := by
    apply (negativeQuotientEquiv D).symm.injective
    rw [negativeQuotientEquiv_symm_toQuotient]
    exact he
  rw [← hq, quotientBar_toQuotient, negativeQuotientEquiv_symm_toQuotient]
  exact ⟨bar a, bar_mem_weightSpace ha, rfl⟩

/-- Bar both preserves and reflects the root-lattice degree. -/
theorem quotientBar_mem_Uw_iff {ν : I →₀ ℕ} {x : Quotient D 𝕧} :
    (negativeQuotientEquiv D).symm (quotientBar D x) ∈ GrandLoop.Uw D 𝕧 ν ↔
      (negativeQuotientEquiv D).symm x ∈ GrandLoop.Uw D 𝕧 ν := by
  constructor
  · intro hx
    simpa only [quotientBar_quotientBar D x] using quotientBar_mem_Uw D hx
  · exact quotientBar_mem_Uw D
end LusztigF

namespace PBWProductNorm
open LusztigF Modified
attribute [local instance] neZero_ratFunc_X
attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU
variable {I Y : Type*} [DecidableEq I] [Finite I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)
  {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}

/-- The bar of the original integral PBW preimage has the same computed degree. -/
theorem bar_homogeneous_Uw {w : List I} (hw : cs.IsReduced w) (c : Fin w.length → ℕ) :
    (negativeQuotientEquiv D).symm
      (quotientBar D (integralPBWPreimage R hw c)) ∈ GrandLoop.Uw D 𝕧 (degree D w c) :=
  quotientBar_mem_Uw D (homogeneous_Uw R hw c)
end PBWProductNorm
