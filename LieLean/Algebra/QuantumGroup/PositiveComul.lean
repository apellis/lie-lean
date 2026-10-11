/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Hopf
import LieLean.Algebra.QuantumGroup.LusztigF.QuotientComul

/-!
# Comparing positive and full coproducts

`comul_plusHom` identifies the actual full quantum-group coproduct with toral insertion
into the original free twisted coproduct, on arbitrary finite expressions.
`comul_quotientPlus` descends this identity to the original radical quotient over `ℚ(v)`.
For a homogeneous second leg of degree `ν`, the insertion is
`a ⊗ b ↦ (a⁺ K_{Σ νᵢ dᵢ i}) ⊗ b⁺`.

The direct coefficient interface `comul_quotientPlus_of_finite_strings` translates
finite divided-power string expansions into full coproduct expansions, retaining
all string indices and toral factors. This is the comparison step used in the proof
of Lusztig, *Introduction to quantum groups*, 38.1.8 (printed p. 298).

The rank-one intertwining identity of 37.3.2, a justified truncation for its selected
coefficients, projected braid compatibility 38.1.8(b), and restricted braid isometry
38.2.1 are not proved here. In particular, no multiplicativity of a projected
coproduct is assumed or asserted.
-/

open LieLean LusztigF TensorProduct
noncomputable section
namespace LieLean.QuantumGroup
variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k)

/-- The toral-positive part of the coproduct, on the free positive algebra. -/
def toralPlusHom : LusztigF k I →ₐ[k] QuantumGroup R v ⊗[k] QuantumGroup R v :=
  FreeAlgebra.lift k fun i ↦ Kt R v i ⊗ₜ E R v i

@[simp] theorem toralPlusHom_theta (i : I) :
    toralPlusHom R v (θ k i) = Kt R v i ⊗ₜ E R v i := by
  simp [toralPlusHom]

/-- Insert the toral weight of the second leg; no projection is used. -/
def positiveTensorComparison :
    LusztigF k I ⊗[k] LusztigF k I →ₗ[k] QuantumGroup R v ⊗[k] QuantumGroup R v :=
  TensorProduct.lift (LinearMap.mk₂ k
    (fun a b ↦ (plusHom R v a ⊗ₜ (1 : QuantumGroup R v)) * toralPlusHom R v b)
    (by intros; simp [add_tmul, add_mul])
    (by intros; rw [map_smul, ← smul_tmul', smul_mul_assoc])
    (by intros; simp [mul_add])
    (by intros; simp))

@[simp] theorem positiveTensorComparison_tmul (a b : LusztigF k I) :
    positiveTensorComparison R v (a ⊗ₜ b) =
      (plusHom R v a ⊗ₜ (1 : QuantumGroup R v)) * toralPlusHom R v b := by
  simp [positiveTensorComparison]

theorem positiveTensorComparison_left (i : I) (z : LusztigF k I ⊗[k] LusztigF k I) :
    positiveTensorComparison R v ((LinearMap.mulLeft k (θ k i)).rTensor _ z) =
      (E R v i ⊗ₜ (1 : QuantumGroup R v)) * positiveTensorComparison R v z := by
  induction z with
  | tmul a b => simp [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => simp [ha, hb, mul_add]

theorem positiveTensorComparison_right (i : I) (z : LusztigF k I ⊗[k] LusztigF k I) :
    positiveTensorComparison R v
      (TensorProduct.map (twist D v i).toLinearMap (LinearMap.mulLeft k (θ k i)) z) =
      (Kt R v i ⊗ₜ E R v i) * positiveTensorComparison R v z := by
  induction z with
  | tmul a b =>
    have h : Kt R v i * plusHom R v a = plusHom R v (twist D v i a) * Kt R v i :=
      (relations R v).toPreRelations.kt_mul_lift i a
    simp only [map_tmul, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
      positiveTensorComparison_tmul, map_mul, toralPlusHom_theta, ← mul_assoc,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, h]
  | add a b ha hb => simp [ha, hb, mul_add]

/-- The coweight attached to a positive root-lattice degree, including symmetrizers. -/
def positiveToralWeight (ν : I →₀ ℕ) : Y := ν.sum fun i n ↦ n • ktilde R i

omit [DecidableEq I] in
@[simp] theorem positiveToralWeight_zero : positiveToralWeight R 0 = 0 := by
  simp [positiveToralWeight]

omit [DecidableEq I] in
theorem positiveToralWeight_add (ν μ : I →₀ ℕ) :
    positiveToralWeight R (ν + μ) = positiveToralWeight R ν + positiveToralWeight R μ :=
  Finsupp.sum_add_index' (by simp) (fun _ _ _ ↦ add_nsmul _ _ _)

omit [DecidableEq I] in
@[simp] theorem positiveToralWeight_single (i : I) (n : ℕ) :
    positiveToralWeight R (Finsupp.single i n) = n • ktilde R i := by
  simp [positiveToralWeight]

/-- On a homogeneous vector the toral-positive map inserts exactly its toral degree. -/
theorem toralPlusHom_of_mem {ν : I →₀ ℕ} {b : LusztigF k I}
    (hb : b ∈ LusztigF.weightSpace k ν) :
    toralPlusHom R v b = K R v (positiveToralWeight R ν) ⊗ₜ plusHom R v b := by
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨w, rfl, rfl⟩ := hb
    induction w with
    | nil => simp [Algebra.TensorProduct.one_def]
    | cons i w ih =>
      simp only [monomial_cons, map_mul, toralPlusHom_theta, ih,
        Algebra.TensorProduct.tmul_mul_tmul, K_add, wordWeight_cons,
        positiveToralWeight_add, positiveToralWeight_single, one_nsmul, plusHom_θ]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb, tmul_add]
  | smul c b _ hb => simp [hb, tmul_smul]

/-- The comparison formula for a homogeneous second leg; the first leg is arbitrary. -/
theorem positiveTensorComparison_tmul_of_mem (a : LusztigF k I)
    {ν : I →₀ ℕ} {b : LusztigF k I} (hb : b ∈ LusztigF.weightSpace k ν) :
    positiveTensorComparison R v (a ⊗ₜ b) =
      (plusHom R v a * K R v (positiveToralWeight R ν)) ⊗ₜ plusHom R v b := by
  rw [positiveTensorComparison_tmul, toralPlusHom_of_mem R v hb,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

variable [NeZero v]
/-- The actual full coproduct is the toral comparison of the original twisted coproduct. -/
theorem comul_plusHom (x : LusztigF k I) :
    comul R v (plusHom R v x) = positiveTensorComparison R v (LusztigF.comul D v x) := by
  induction x using LusztigF.induction_left with
  | algebraMap c => simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
  | smul c x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | θ_mul i x hx =>
    rw [map_mul, plusHom_θ, map_mul, comul_E, add_mul, hx, LusztigF.comul_θ_mul,
      map_add, positiveTensorComparison_left, positiveTensorComparison_right]

/-- Any finite homogeneous expression for the original twisted coproduct gives the full
coproduct, with every Cartan factor retained. -/
theorem comul_plusHom_of_finite {A : Type*} (s : Finset A) (x : LusztigF k I)
    (a b : A → LusztigF k I) (ν : A → I →₀ ℕ)
    (hb : ∀ j ∈ s, b j ∈ LusztigF.weightSpace k (ν j))
    (hx : LusztigF.comul D v x = ∑ j ∈ s, a j ⊗ₜ b j) :
    comul R v (plusHom R v x) =
      ∑ j ∈ s, (plusHom R v (a j) * K R v (positiveToralWeight R (ν j))) ⊗ₜ
        plusHom R v (b j) := by
  rw [comul_plusHom, hx, map_sum]
  exact Finset.sum_congr rfl fun j hj ↦ positiveTensorComparison_tmul_of_mem R v _ (hb j hj)

end LieLean.QuantumGroup

namespace LieLean.QuantumGroup
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)

theorem toralPlusHom_radical {x : LusztigF 𝕂 I} (hx : x ∈ radical D 𝕧) :
    toralPlusHom R 𝕧 x = 0 := by
  rw [radical_eq_serreIdeal_ratFunc] at hx
  rw [← sum_coeff_gradingHom x, Finsupp.sum, map_sum]
  apply Finset.sum_eq_zero
  intro ν hν
  have hm := LusztigF.weightProj_mem ν x
  have hz : plusHom R 𝕧 (LusztigF.weightProj ν x) = 0 :=
    (plusHom_eq_zero_iff R 𝕧 ratFunc_X_not_root _).mpr
      (weightProj_mem_serreIdeal hx ν)
  change toralPlusHom R 𝕧 (LusztigF.weightProj ν x) = 0
  rw [toralPlusHom_of_mem R 𝕧 hm, hz, tmul_zero]

/-- The toral-positive map descended through the original radical quotient. -/
def quotientToralPlus : Quotient D 𝕧 →ₐ[𝕂] QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧 :=
  (radical D 𝕧).ringCon.liftₐ (toralPlusHom R 𝕧) fun x y h ↦ by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact toralPlusHom_radical R (((radical D 𝕧).rel_iff x y).mp h)

@[simp] theorem quotientToralPlus_toQuotient (x : LusztigF 𝕂 I) :
    quotientToralPlus R (toQuotient D 𝕧 x) = toralPlusHom R 𝕧 x := rfl

/-- Toral insertion on the actual quotient tensor product. -/
def quotientPositiveTensorComparison :
    Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧 →ₗ[𝕂] QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧 :=
  TensorProduct.lift (LinearMap.mk₂ 𝕂
    (fun a b ↦ (quotientPlus R a ⊗ₜ (1 : QuantumGroup R 𝕧)) * quotientToralPlus R b)
    (by intros; simp [add_tmul, add_mul])
    (by intros; rw [map_smul, ← smul_tmul', smul_mul_assoc])
    (by intros; simp [mul_add])
    (by intros; simp))

@[simp] theorem quotientPositiveTensorComparison_tmul (a b : Quotient D 𝕧) :
    quotientPositiveTensorComparison R (a ⊗ₜ b) =
      (quotientPlus R a ⊗ₜ (1 : QuantumGroup R 𝕧)) * quotientToralPlus R b := by
  simp [quotientPositiveTensorComparison]

theorem quotientPositiveTensorComparison_toQuotient
    (z : LusztigF 𝕂 I ⊗[𝕂] LusztigF 𝕂 I) :
    quotientPositiveTensorComparison R (quotientTensorMap D z) =
      positiveTensorComparison R 𝕧 z := by
  induction z with
  | tmul a b => simp [quotientTensorMap]
  | add a b ha hb => simp [ha, hb]

/-- The full coproduct of the actual positive embedding equals toral insertion into the
original quotient coproduct, on every quotient element. -/
theorem comul_quotientPlus (x : Quotient D 𝕧) :
    comul R 𝕧 (quotientPlus R x) =
      quotientPositiveTensorComparison R (quotientComul D x) := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  rw [quotientPlus_toQuotient, quotientComul_toQuotient,
    quotientPositiveTensorComparison_toQuotient, comul_plusHom]

/-- The homogeneous formula on the actual quotient. -/
theorem quotientPositiveTensorComparison_tmul_of_mem (a : Quotient D 𝕧)
    {ν : I →₀ ℕ} {b : Quotient D 𝕧}
    (hb : b ∈ (LusztigF.weightSpace 𝕂 ν).map (toQuotient D 𝕧).toLinearMap) :
    quotientPositiveTensorComparison R (a ⊗ₜ b) =
      (quotientPlus R a * K R 𝕧 (positiveToralWeight R ν)) ⊗ₜ quotientPlus R b := by
  obtain ⟨b, hb, rfl⟩ := hb
  simp only [AlgHom.toLinearMap_apply]
  rw [quotientPositiveTensorComparison_tmul, quotientToralPlus_toQuotient,
    toralPlusHom_of_mem R 𝕧 hb, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

/-- Every finite homogeneous expansion of the original quotient coproduct gives the
corresponding exact full coproduct expansion, including all toral weights. -/
theorem comul_quotientPlus_of_finite {A : Type*} (s : Finset A) (x : Quotient D 𝕧)
    (a b : A → Quotient D 𝕧) (ν : A → I →₀ ℕ)
    (hb : ∀ j ∈ s, b j ∈ (LusztigF.weightSpace 𝕂 (ν j)).map (toQuotient D 𝕧).toLinearMap)
    (hx : quotientComul D x = ∑ j ∈ s, a j ⊗ₜ b j) :
    comul R 𝕧 (quotientPlus R x) =
      ∑ j ∈ s, (quotientPlus R (a j) * K R 𝕧 (positiveToralWeight R (ν j))) ⊗ₜ
        quotientPlus R (b j) := by
  rw [comul_quotientPlus, hx, map_sum]
  exact Finset.sum_congr rfl fun j hj ↦
    quotientPositiveTensorComparison_tmul_of_mem R _ (hb j hj)

/-- Exact toral insertion for one divided-power string, with no discarded higher terms. -/
theorem quotientPositiveTensorComparison_string (a : Quotient D 𝕧) (i : I) (n : ℕ)
    {ν : I →₀ ℕ} {b : LusztigF 𝕂 I} (hb : b ∈ LusztigF.weightSpace 𝕂 ν) :
    quotientPositiveTensorComparison R
      (a ⊗ₜ toQuotient D 𝕧 (qDivPow (𝕧 ^ D.d i) n (θ 𝕂 i) * b)) =
      (quotientPlus R a * K R 𝕧 (n • ktilde R i + positiveToralWeight R ν)) ⊗ₜ
        (qDivPow (𝕧 ^ D.d i) n (E R 𝕧 i) * plusHom R 𝕧 b) := by
  rw [quotientPositiveTensorComparison_tmul, quotientToralPlus_toQuotient, map_mul,
    toralPlusHom_of_mem R 𝕧 hb]
  simp only [qDivPow, map_smul, map_pow, toralPlusHom_theta,
    Algebra.TensorProduct.tmul_pow, smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
    Kt, K_pow, K_add]
  rw [mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    ← tmul_smul]

/-- A finite string expansion of the original coproduct becomes the full coproduct
expansion used before the rank-one intertwining step. Every string index survives. -/
theorem comul_quotientPlus_of_finite_strings {A : Type*} (s : Finset A)
    (x : Quotient D 𝕧) (i : I) (a : A → Quotient D 𝕧) (b : A → LusztigF 𝕂 I)
    (n : A → ℕ) (ν : A → I →₀ ℕ)
    (hb : ∀ j ∈ s, b j ∈ LusztigF.weightSpace 𝕂 (ν j))
    (hx : quotientComul D x = ∑ j ∈ s,
      a j ⊗ₜ toQuotient D 𝕧 (qDivPow (𝕧 ^ D.d i) (n j) (θ 𝕂 i) * b j)) :
    comul R 𝕧 (quotientPlus R x) = ∑ j ∈ s,
      (quotientPlus R (a j) * K R 𝕧 (n j • ktilde R i + positiveToralWeight R (ν j))) ⊗ₜ
        (qDivPow (𝕧 ^ D.d i) (n j) (E R 𝕧 i) * plusHom R 𝕧 (b j)) := by
  rw [comul_quotientPlus, hx, map_sum]
  exact Finset.sum_congr rfl fun j hj ↦
    quotientPositiveTensorComparison_string R _ _ _ (hb j hj)

end LieLean.QuantumGroup
