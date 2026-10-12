/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Integral.ScalarResidue

/-! The actual degree-zero augmentation preserves the original integral form. -/
open LieLean LusztigF
noncomputable section
namespace LieLean.QuantumGroup
open GrandLoop
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- The existing Serre counit transported to the original radical quotient. -/
def originalAugmentation : Quotient D 𝕧 →ₗ[𝕂] 𝕂 :=
  VermaModule.counitQ D 𝕧 ∘ₗ (negativeQuotientEquiv D).symm.toLinearMap

@[simp] theorem originalAugmentation_toQuotient (x : LusztigF 𝕂 I) :
    originalAugmentation D (toQuotient D 𝕧 x) = LusztigF.counit x := by
  simp [originalAugmentation]

@[simp] theorem originalAugmentation_one : originalAugmentation D 1 = 1 := by
  simpa using originalAugmentation_toQuotient D (1 : LusztigF 𝕂 I)

lemma originalAugmentation_mul (x y : Quotient D 𝕧) :
    originalAugmentation D (x * y) =
      originalAugmentation D x * originalAugmentation D y := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  obtain ⟨y, rfl⟩ := toQuotient_surjective D 𝕧 y
  rw [← map_mul, originalAugmentation_toQuotient, map_mul,
    originalAugmentation_toQuotient, originalAugmentation_toQuotient]

lemma originalAugmentation_integralGenerator (i : I) (n : ℕ) :
    originalAugmentation D (quotientIntegralGenerator D i n) = if n = 0 then 1 else 0 := by
  have hg : quotientIntegralGenerator D i n =
      toQuotient D 𝕧 (qDivPow (𝕧 ^ D.d i) n (θ 𝕂 i)) := by
    simp [quotientIntegralGenerator, qDivPow]
  rw [hg, originalAugmentation_toQuotient]
  cases n with
  | zero => simp [qDivPow, qFactorial]
  | succ n => simp [qDivPow]

/-- Augmentation of the original generated integral form has Laurent-integer coefficients.
No basis or coordinate-integrality premise is used. -/
theorem originalAugmentation_mem_laurent {x : Quotient D 𝕧}
    (hx : x ∈ quotientIntegralForm D) :
    originalAugmentation D x ∈ integralLaurentEval.range := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, n, rfl⟩ := hx
    rw [originalAugmentation_integralGenerator]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | algebraMap a =>
    change originalAugmentation D (algebraMap 𝕂 _ (integralLaurentEval a)) ∈ _
    rw [Algebra.algebraMap_eq_smul_one, map_smul, originalAugmentation_one, smul_eq_mul,
      mul_one]
    exact ⟨a, rfl⟩
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [originalAugmentation_mul]; exact mul_mem hx hy

/-- An augmentation in the actual infinity ring has integer residue. -/
theorem originalAugmentation_residue_integer {x : Quotient D 𝕧}
    (hx : x ∈ quotientIntegralForm D) (a : InfinityLocalRing)
    (ha : algebraMap InfinityLocalRing 𝕂 a = originalAugmentation D x) :
    ∃ z : ℤ, Sl2.RankOne.residue a = z := by
  obtain ⟨f, hf⟩ := originalAugmentation_mem_laurent D hx
  exact InfinityLocalRing.residue_integer_of_laurent a f (ha.trans hf.symm)

end LieLean.QuantumGroup
