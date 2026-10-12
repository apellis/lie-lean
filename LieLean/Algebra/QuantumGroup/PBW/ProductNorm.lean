/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.RestrictedBraidIsometry.PBWRecursion

/-!
# Full pairing and product norm of original integral PBW preimages

Iterating the actual restricted inverse-braid recursion gives the full pairing formula
by the pure-PBW unit-tail specialization and iteration of Lusztig,
Introduction to Quantum Groups, 38.2.3, for the preimages of 41.1.5.
This is not the arbitrary adapted-tail statement of 38.2.3.
The parameter is `X` and the inverse braid is `T'_{i,-1}` throughout.
-/

noncomputable section
open LieLean LieLean.QuantumGroup LusztigF Modified
namespace PBWProductNorm
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X
attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)
  {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}

/-- The empty original preimage is the unit of the actual radical quotient. -/
theorem preimage_nil (hw : cs.IsReduced []) (c : Fin [].length → ℕ) :
    (integralPBWPreimage R hw c : Quotient D 𝕧) = 1 := by
  apply quotientPlus_injective R
  rw [quotientPlus_integralPBWPreimage, _root_.map_one]
  simp [pbwDivSymm, CoxeterSystem.pbwDivMonomial]

/-- Full Kronecker pairing, with a product over all positions of the reduced word. -/
theorem pairing {w : List I} (hw : cs.IsReduced w) (c d : Fin w.length → ℕ) :
    quotientForm D (integralPBWPreimage R hw c) (integralPBWPreimage R hw d) =
      if c = d then ∏ n : Fin w.length, GrandLoop.coefU D 𝕧 (w.get n) (c n) else 0 := by
  classical
  induction w with
  | nil =>
    have hcd : c = d := funext fun n ↦ Fin.elim0 n
    have hf : quotientForm D 1 1 = 1 := by
      simpa using quotientForm_toQuotient D (1 : LusztigF 𝕂 I) 1
    simp [preimage_nil, hcd, hf]
  | cons i w ih =>
    rw [RestrictedBraidConsumer.adapted_pbw_pairing_recursion R hw c d,
      ih (by simpa using hw.drop 1)]
    simp only [List.length_cons, Fin.prod_univ_succ]
    have he : c = d ↔ c 0 = d 0 ∧
        (fun n : Fin w.length ↦ c n.succ) = (fun n : Fin w.length ↦ d n.succ) := by
      constructor
      · rintro rfl
        exact ⟨rfl, rfl⟩
      · rintro ⟨h0, ht⟩
        funext n
        refine Fin.cases h0 (fun k ↦ congrFun ht k) n
    by_cases h0 : c 0 = d 0
    · by_cases ht : (fun n : Fin w.length ↦ c n.succ) = (fun n : Fin w.length ↦ d n.succ)
      · simp [he.mpr ⟨h0, ht⟩]
      · have hcd : c ≠ d := fun h ↦ ht (he.mp h).2
        simp [h0, ht, hcd]
    · have hcd : c ≠ d := fun h ↦ h0 (he.mp h).1
      simp [h0, hcd]

/-- Unequal exponent functions give orthogonal original integral PBW preimages. -/
theorem orthogonal {w : List I} (hw : cs.IsReduced w) (c d : Fin w.length → ℕ)
    (hcd : c ≠ d) :
    quotientForm D (integralPBWPreimage R hw c) (integralPBWPreimage R hw d) = 0 := by
  simp only [pairing R hw c d, hcd, ite_false]

/-- The full norm is the product of the actual simple divided-power coefficients. -/
theorem norm {w : List I} (hw : cs.IsReduced w) (c : Fin w.length → ℕ) :
    quotientForm D (integralPBWPreimage R hw c) (integralPBWPreimage R hw c) =
      ∏ n : Fin w.length, GrandLoop.coefU D 𝕧 (w.get n) (c n) := by
  simp only [pairing R hw c c, ite_true]

/-- The actual PBW norm is congruent to one in the existing bar-twisted infinity ring.
This is a norm congruence, not a signed canonical residue assertion. -/
theorem norm_residue {w : List I} (hw : cs.IsReduced w) (c : Fin w.length → ℕ) :
    ∃ a : InfinityLocalRing,
      quotientForm D (integralPBWPreimage R hw c) (integralPBWPreimage R hw c) =
        algebraMap InfinityLocalRing 𝕂 (1 + InfinityLocalRing.uniformizer * a) := by
  induction w with
  | nil =>
    refine ⟨0, ?_⟩
    rw [norm R hw c]
    simp
  | cons i w ih =>
    obtain ⟨a, ha⟩ := quotientForm_divided_norm_factor D i (c 0)
    obtain ⟨b, hb⟩ := ih (by simpa using hw.drop 1) (fun n ↦ c n.succ)
    refine ⟨a + b + InfinityLocalRing.uniformizer * a * b, ?_⟩
    rw [RestrictedBraidConsumer.adapted_pbw_norm_recursion R hw c, ha, hb, ← _root_.map_mul]
    congr 1
    ring

end PBWProductNorm
