/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.InfinityLattice

/-!
# Finite-longest coordinates of the original infinity lattice

The headline `longestBasis` supplies infinity-local coordinates for every element of the
original quotient crystal lattice. The original inverse-convention PBW preimages span the
whole radical quotient for a reduced word of the longest element in a finite Coxeter group.
No canonical-basis identification or reduced-word-independent representative is asserted.
-/

noncomputable section
open LieLean LieLean.QuantumGroup LusztigF Modified
namespace PBWInfinityLattice
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝔄" => InfinityLocalRing
local notation "𝒜" => LaurentPolynomial ℤ
attribute [local instance] neZero_ratFunc_X
attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)
  {W : Type*} [Group W] [Finite W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}
  {w : List I} (hw : cs.IsReduced w) (hw₀ : cs.wordProd w = cs.longestElement)
include hw₀

/-- The original inverse-convention preimages span the existing integral form. -/
theorem integral_span_longest :
    Submodule.span 𝒜 (Set.range fun c ↦
      (integralPBWPreimage R hw c : Quotient D 𝕧)) =
        (quotientIntegralForm D).toSubmodule := by
  apply Submodule.map_injective_of_injective
    (f := (quotientPlusIntegral R).toLinearMap) (quotientPlus_injective R)
  rw [Submodule.map_span, ← Set.range_comp]
  change Submodule.span 𝒜 (Set.range fun c ↦
    quotientPlus R (integralPBWPreimage R hw c)) = _
  simp only [quotientPlus_integralPBWPreimage]
  rw [span_pbwDivSymm_longest_eq_all cs hw hw₀]
  exact congrArg Subalgebra.toSubmodule (map_quotientIntegralForm_plus R).symm

/-- At finite longest words the original PBW preimages span the entire radical quotient. -/
theorem field_span_longest :
    Submodule.span 𝕂 (Set.range fun c ↦
      (integralPBWPreimage R hw c : Quotient D 𝕧)) = ⊤ := by
  apply top_unique
  rw [← span_quotientIntegralForm D]
  apply Submodule.span_le.mpr
  intro x hx
  have hx' : x ∈ Submodule.span 𝒜 (Set.range fun c ↦
      (integralPBWPreimage R hw c : Quotient D 𝕧)) := by
    rw [integral_span_longest R hw hw₀]
    exact hx
  obtain ⟨a, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx'
  classical
  apply Submodule.sum_mem
  intro c _
  change integralLaurentEval (a c) • (integralPBWPreimage R hw c : Quotient D 𝕧) ∈ _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

/-- For a finite longest word, the accepted intersection is the entire original lattice. -/
theorem intersection_longest_eq_lattice : intersection R hw = lattice D := by
  rw [intersection, field_span_longest R hw hw₀, Submodule.restrictScalars_top, inf_top_eq]

/-- A genuine infinity-local basis of the entire original quotient crystal lattice. -/
def longestBasis : Module.Basis (Fin w.length → ℕ) 𝔄 (lattice D) :=
  (intersectionBasis R hw).map
    (LinearEquiv.ofEq _ _ (intersection_longest_eq_lattice R hw hw₀))

/-- The whole-lattice basis evaluates to the same original inverse PBW preimage. -/
theorem longestBasis_apply (c : Fin w.length → ℕ) :
    (longestBasis R hw hw₀ c : Quotient D 𝕧) = integralPBWPreimage R hw c := by
  simp [longestBasis, intersectionBasis_apply]

end PBWInfinityLattice
