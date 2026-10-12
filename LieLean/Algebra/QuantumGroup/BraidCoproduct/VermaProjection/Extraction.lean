/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.VermaProjection.Projection
import LieLean.Algebra.QuantumGroup.BraidCoproduct.FullIntertwining.AllAlgebra

/-!
# Concrete Verma coefficient extraction

The finite intertwiner identifies extracted braid coproducts with projected coproducts.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994),
37.3.1–37.3.2 and the proof of 38.1.8 (printed pp. 293, 297–299).
The finite-cutoff argument uses the actual quantum group and original Verma modules.
No restricted braid isometry or PBW norm conclusion is asserted here.
-/

noncomputable section
open LieLean LusztigF TensorProduct
open LieLean.QuantumGroup FiniteIntertwining
namespace VermaProjection
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (Λ₁ Λ₂ : Y →+ ℤ)

/-- The genuine tensor of the two original lowest generators. -/
def vacuum : VermaModule R 𝕧 Λ₁ ⊗[𝕂] VermaModule R 𝕧 Λ₂ :=
  VermaModule.hwv R 𝕧 Λ₁ ⊗ₜ VermaModule.hwv R 𝕧 Λ₂

/-- Extract the first full coefficient and the second zero-string coefficient. -/
def decode (i : I) :
    (VermaModule R 𝕧 Λ₁ ⊗[𝕂] VermaModule R 𝕧 Λ₂) →ₗ[𝕂]
      (Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧) :=
  TensorProduct.map (vermaEquiv R Λ₁).symm.toLinearMap
    ((quotientSkewProjection D i) ∘ₗ (vermaEquiv R Λ₂).symm.toLinearMap)

@[simp] theorem decode_eval (i : I) (a b : Quotient D 𝕧) :
    decode R Λ₁ Λ₂ i (vermaEquiv R Λ₁ a ⊗ₜ vermaEquiv R Λ₂ b) =
      a ⊗ₜ quotientSkewProjection D i b := by simp [decode]

/-- Toral action is retained at general weights; the Chevalley sign is negative. -/
theorem decode_toral (i : I) (a b : Quotient D 𝕧) (μ : Y) :
    decode R Λ₁ Λ₂ i
      (lowestPair R 𝕧 Λ₁ Λ₂ ((quotientPlus R a * K R 𝕧 μ) ⊗ₜ quotientPlus R b)
        (vacuum R Λ₁ Λ₂)) =
      𝕧 ^ (-Λ₁ μ) • (a ⊗ₜ quotientSkewProjection D i b) := by
  rw [vacuum, lowestPair_tmul]
  simp only [map_mul, chevalley_K, mul_smul, VermaModule.K_smul_hwv, map_neg]
  rw [smul_comm, ← vermaEquiv_apply, ← vermaEquiv_apply, ← smul_tmul', map_smul, decode_eval]

/-- This actual coefficient extractor factors through the actual second Verma quotient. -/
theorem decode_factors (i : I) :
    decode R Λ₁ Λ₂ i =
      TensorProduct.map LinearMap.id (LinearMap.ker (quotientLDeriv D i)).subtype ∘ₗ
        (tensorCoordinateEquiv R Λ₁ Λ₂ i).toLinearMap ∘ₗ
          TensorProduct.map LinearMap.id (vermaEImage R Λ₂ i).mkQ := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

/-- The coordinate map kills every positive E power on an arbitrary second vector. -/
theorem projection_Epow (i : I) (n : ℕ) (m : VermaModule R 𝕧 Λ₂) :
    quotientSkewProjection D i ((vermaEquiv R Λ₂).symm
      (chevalley R 𝕧 (E R 𝕧 i ^ (n + 1)) • m)) = 0 := by
  have h : lowestE R Λ₂ i (chevalley R 𝕧 (E R 𝕧 i ^ n) • m) ∈
      LinearMap.ker (vermaCoordinate R Λ₂ i) := by
    rw [ker_vermaCoordinate]
    exact ⟨_, rfl⟩
  have he := congrArg Subtype.val (LinearMap.mem_ker.mp h)
  change quotientSkewProjection D i ((vermaEquiv R Λ₂).symm
    (chevalley R 𝕧 (E R 𝕧 i) • (chevalley R 𝕧 (E R 𝕧 i ^ n) • m))) = 0 at he
  simpa only [pow_succ', map_mul, mul_smul] using he

/-- Positive series terms vanish after the quotient, on arbitrary inhomogeneous tensors. -/
theorem decode_positive_term (i : I) (n : ℕ)
    (z : VermaModule R 𝕧 Λ₁ ⊗[𝕂] VermaModule R 𝕧 Λ₂) :
    decode R Λ₁ Λ₂ i
      (lowestPair R 𝕧 Λ₁ Λ₂ ((F R 𝕧 i ^ (n + 1)) ⊗ₜ (E R 𝕧 i ^ (n + 1))) z) = 0 := by
  induction z with
  | tmul x y =>
    rw [lowestPair_tmul]
    simp only [decode, map_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
      projection_Epow, tmul_zero]
  | add x y hx hy => simp [hx, hy]

/-- Finite truncation needs no asymptotic argument after the actual quotient. -/
theorem decode_partialSum (i : I) (N : ℕ)
    (z : VermaModule R 𝕧 Λ₁ ⊗[𝕂] VermaModule R 𝕧 Λ₂) :
    decode R Λ₁ Λ₂ i (lowestPair R 𝕧 Λ₁ Λ₂ (partialSum R 𝕧 i N) z) =
      decode R Λ₁ Λ₂ i z := by
  simp only [partialSum, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  rw [Finset.sum_eq_single 0]
  · simp [coeff, ← Algebra.TensorProduct.one_def]
  · intro n _ hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [decode_positive_term, smul_zero]
  · simp

omit [Finite I] in
/-- F kills the actual lowest generator, so S_N fixes the original vacuum. -/
theorem partialSum_vacuum (i : I) (N : ℕ) :
    lowestPair R 𝕧 Λ₁ Λ₂ (partialSum R 𝕧 i N) (vacuum R Λ₁ Λ₂) =
      vacuum R Λ₁ Λ₂ := by
  simp only [partialSum, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  rw [Finset.sum_eq_single 0]
  · simp [coeff, ← Algebra.TensorProduct.one_def]
  · intro n _ hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [vacuum, lowestPair_tmul, pow_succ, mul_smul]
  · simp

/-- Concrete finite coefficient comparison supplied by the all-algebra intertwining theorem. -/
theorem decode_braidDelta (i : I) (u : QuantumGroup R 𝕧) :
    decode R Λ₁ Λ₂ i
      (lowestPair R 𝕧 Λ₁ Λ₂ (braidDelta R 𝕧 ratFunc_X_not_root i u) (vacuum R Λ₁ Λ₂)) =
    decode R Λ₁ Λ₂ i
      (lowestPair R 𝕧 Λ₁ Λ₂ (comul R 𝕧 u) (vacuum R Λ₁ Λ₂)) := by
  obtain ⟨N, hN⟩ := FullIntertwining.lowestPair_intertwine_all R 𝕧 Λ₁ Λ₂
    ratFunc_X_not_root i u (vacuum R Λ₁ Λ₂)
  have h := congrArg (decode R Λ₁ Λ₂ i) (hN N le_rfl)
  rwa [partialSum_vacuum, decode_partialSum] at h

/-- Evaluate the actual tensor action and take the concrete quotient coefficient. -/
def extract (i : I) :
    (QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧) →ₗ[𝕂]
      (Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧) where
  toFun u := decode R Λ₁ Λ₂ i (lowestPair R 𝕧 Λ₁ Λ₂ u (vacuum R Λ₁ Λ₂))
  map_add' a b := by simp
  map_smul' c a := by simp

@[simp] theorem extract_toral (i : I) (a b : Quotient D 𝕧) (μ : Y) :
    extract R Λ₁ Λ₂ i ((quotientPlus R a * K R 𝕧 μ) ⊗ₜ quotientPlus R b) =
      𝕧 ^ (-Λ₁ μ) • (a ⊗ₜ quotientSkewProjection D i b) :=
  decode_toral R Λ₁ Λ₂ i a b μ

/-- At the source's zero weight, toral insertion decodes to the original projected tensor.
No separation of variable weights or independence of the ambient roots is used. -/
theorem extract_positiveComparison (i : I) (z : Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧) :
    extract R 0 Λ₂ i (quotientPositiveTensorComparison R z) =
      TensorProduct.map LinearMap.id (quotientSkewProjection D i) z := by
  induction z with
  | tmul a b =>
    obtain ⟨b, rfl⟩ := toQuotient_surjective D 𝕧 b
    rw [← sum_coeff_gradingHom b, Finsupp.sum, map_sum, tmul_sum, map_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro ν _
    have hb : toQuotient D 𝕧 (LusztigF.weightProj ν b) ∈
        (LusztigF.weightSpace 𝕂 ν).map (toQuotient D 𝕧).toLinearMap :=
      ⟨_, LusztigF.weightProj_mem ν b, rfl⟩
    change extract R 0 Λ₂ i (quotientPositiveTensorComparison R
      (a ⊗ₜ toQuotient D 𝕧 (LusztigF.weightProj ν b))) =
        a ⊗ₜ quotientSkewProjection D i (toQuotient D 𝕧 (LusztigF.weightProj ν b))
    rw [quotientPositiveTensorComparison_tmul_of_mem R a hb, extract_toral]
    simp
  | add z w hz hw => simp [hz, hw]

/-- The actual all-algebra intertwiner now yields a literal tensor identity in f tensor f. -/
theorem extract_braid_positive (i : I) (x : Quotient D 𝕧) :
    extract R 0 Λ₂ i (braidDelta R 𝕧 ratFunc_X_not_root i (quotientPlus R x)) =
      TensorProduct.map LinearMap.id (quotientSkewProjection D i) (quotientComul D x) := by
  change decode R 0 Λ₂ i (lowestPair R 𝕧 0 Λ₂
    (braidDelta R 𝕧 ratFunc_X_not_root i (quotientPlus R x)) (vacuum R 0 Λ₂)) = _
  rw [decode_braidDelta, comul_quotientPlus]
  exact extract_positiveComparison R Λ₂ i (quotientComul D x)

end VermaProjection
