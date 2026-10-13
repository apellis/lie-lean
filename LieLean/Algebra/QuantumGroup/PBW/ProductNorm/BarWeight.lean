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

/-- The coefficient bar fixes every ordered free monomial. -/
theorem bar_monomial (w : List I) : bar (monomial 𝕂 w) = monomial 𝕂 w := by
  induction w with
  | nil => simp
  | cons i w ih => simp only [monomial_cons, map_mul, bar_θ, ih]

/-- Coefficient bar preserves each root-lattice degree in the free algebra. -/
theorem bar_mem_weightSpace {ν : I →₀ ℕ} {x : LusztigF 𝕂 I}
    (hx : x ∈ weightSpace 𝕂 ν) : bar x ∈ weightSpace 𝕂 ν := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [bar_monomial]
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  | zero => simpa only [map_zero] using (weightSpace 𝕂 ν).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (weightSpace 𝕂 ν).add_mem hx hy
  | smul c x _ hx => simpa only [bar_smul] using
      (weightSpace 𝕂 ν).smul_mem (RatFunc.bar c) hx

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
