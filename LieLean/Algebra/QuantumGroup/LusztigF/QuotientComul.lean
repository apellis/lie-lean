/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.LusztigF.BraidIntersection
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Equalizer

/-!
# The actual radical-quotient coproduct and skew coideals

Downstream target: Lusztig 41.1.6 general PBW product norms. This module supplies the actual
quotient coproduct and the two coideal containments of 38.1.8(a), using the accepted kernel
and bounded braid-generator theorems. The coproduct is descended from `LusztigF.comul`;
its tensor form is the original quotient form, whose nondegeneracy is proved, not assumed.
The existing zero-string projection is proved self-adjoint and its projected coproduct is
proved adjoint to multiplication on the actual left kernel.

This does NOT prove 37.3.2, projected braid compatibility 38.1.8(b), restricted braid
isometry 38.2.1, or general PBW product norms. No braid-transported coproduct is substituted
for the source coproduct. No finite Weyl group or longest element hypothesis is imposed.
-/

open LieLean TensorProduct
noncomputable section

namespace LieLean.QuantumGroup
open LusztigF
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

lemma quotientForm_separates (x : Quotient D 𝕧)
    (hx : ∀ y, quotientForm D x y = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := toQuotient_surjective D 𝕧 x
  rw [toQuotient_eq_zero_iff, mem_radical_iff]
  intro b
  simpa using hx (toQuotient D 𝕧 b)

lemma quotientForm_comm (x y : Quotient D 𝕧) :
    quotientForm D x y = quotientForm D y x := by
  obtain ⟨a, rfl⟩ := toQuotient_surjective D 𝕧 x
  obtain ⟨b, rfl⟩ := toQuotient_surjective D 𝕧 y
  simp only [quotientForm_toQuotient, form_comm D 𝕧 a b]

-- A tensor is detected by the actual quotient form, without finite-dimensionality.
lemma quotientForm_tensor_separates (z : Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧)
    (hz : ∀ x y, (quotientForm D).tmul (quotientForm D) z (x ⊗ₜ y) = 0) : z = 0 := by
  classical
  let B := quotientForm D
  let b := Module.Free.chooseBasis 𝕂 (Quotient D 𝕧)
  let e := TensorProduct.equivFinsuppOfBasisRight (M := Quotient D 𝕧) b
  have hleft (x : Quotient D 𝕧) :
      TensorProduct.lid 𝕂 (Quotient D 𝕧) ((B.flip x).rTensor _ z) = 0 := by
    apply quotientForm_separates
    intro y
    have he : B (TensorProduct.lid 𝕂 (Quotient D 𝕧) ((B.flip x).rTensor _ z)) y =
        B.tmul B z (x ⊗ₜ y) := by
      clear hz
      induction z with
      | tmul a c => simp [mul_comm]
      | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
    exact he.trans (hz x y)
  apply e.injective
  ext j
  change e z j = 0
  apply quotientForm_separates
  intro x
  have he : B (e z j) x =
      b.coord j (TensorProduct.lid 𝕂 (Quotient D 𝕧) ((B.flip x).rTensor _ z)) := by
    clear hz hleft
    induction z with
    | tmul a c => simp [e, mul_comm]
    | add u v hu hv => simp only [map_add, Finsupp.add_apply, LinearMap.add_apply, hu, hv]
  rw [he, hleft, map_zero]

abbrev quotientTensorMap :
    (LusztigF 𝕂 I ⊗[𝕂] LusztigF 𝕂 I) →ₗ[𝕂]
      (Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧) :=
  TensorProduct.map (toQuotient D 𝕧).toLinearMap (toQuotient D 𝕧).toLinearMap

lemma quotientTensorMap_pair (z : LusztigF 𝕂 I ⊗[𝕂] LusztigF 𝕂 I)
    (a b : LusztigF 𝕂 I) :
    (quotientForm D).tmul (quotientForm D) (quotientTensorMap D z)
      (toQuotient D 𝕧 a ⊗ₜ toQuotient D 𝕧 b) = formTensor D 𝕧 z (a ⊗ₜ b) := by
  induction z with
  | tmul c d => simp [quotientTensorMap, formTensor, quotientForm_toQuotient]
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]

lemma quotientTensorMap_comul_radical {x : LusztigF 𝕂 I}
    (hx : x ∈ radical D 𝕧) : quotientTensorMap D (LusztigF.comul D 𝕧 x) = 0 := by
  apply quotientForm_tensor_separates
  intro a b
  obtain ⟨a, rfl⟩ := toQuotient_surjective D 𝕧 a
  obtain ⟨b, rfl⟩ := toQuotient_surjective D 𝕧 b
  rw [quotientTensorMap_pair, ← form_mul_right]
  exact (mem_radical_iff D 𝕧).mp hx (a * b)

-- Descent via the already-proved comparison with the Serre module quotient.
def quotientComul : Quotient D 𝕧 →ₗ[𝕂] Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧 :=
  ((serreSubmodule D 𝕧).liftQ
    (quotientTensorMap D ∘ₗ LusztigF.comul D 𝕧) (by
      intro x hx
      change quotientTensorMap D (LusztigF.comul D 𝕧 x) = 0
      apply quotientTensorMap_comul_radical
      rw [radical_eq_serreIdeal_ratFunc]
      exact mem_serreSubmodule.mp hx)).comp (negativeQuotientEquiv D).symm.toLinearMap

@[simp] lemma quotientComul_toQuotient (x : LusztigF 𝕂 I) :
    quotientComul D (toQuotient D 𝕧 x) = quotientTensorMap D (LusztigF.comul D 𝕧 x) := by
  simp [quotientComul]

lemma quotientComul_pair (x a b : Quotient D 𝕧) :
    (quotientForm D).tmul (quotientForm D) (quotientComul D x) (a ⊗ₜ b) =
      quotientForm D x (a * b) := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  obtain ⟨a, rfl⟩ := toQuotient_surjective D 𝕧 a
  obtain ⟨b, rfl⟩ := toQuotient_surjective D 𝕧 b
  rw [quotientComul_toQuotient, quotientTensorMap_pair, ← form_mul_right, ← map_mul,
    quotientForm_toQuotient]

lemma quotientForm_lDeriv (i : I) (x y : Quotient D 𝕧) :
    thetaNorm D 𝕧 i * quotientForm D (quotientLDeriv D i x) y =
      quotientForm D x (toQuotient D 𝕧 (θ 𝕂 i) * y) := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  obtain ⟨y, rfl⟩ := toQuotient_surjective D 𝕧 y
  rw [quotientLDeriv_toQuotient, ← map_mul, quotientForm_toQuotient,
    quotientForm_toQuotient, form_comm D 𝕧 x, form_θ_mul, form_comm]

/-- Actual quotient version of the left skew derivation/coproduct identity. -/
lemma quotientLDeriv_rTensor_comul (i : I) (x : Quotient D 𝕧) :
    (quotientLDeriv D i).rTensor _ (quotientComul D x) =
      quotientComul D (quotientLDeriv D i x) := by
  apply sub_eq_zero.mp
  apply quotientForm_tensor_separates
  intro a b
  simp only [map_sub, LinearMap.sub_apply, sub_eq_zero]
  have hn : thetaNorm D 𝕧 i ≠ 0 := thetaNorm_ne_zero D 𝕧 (by
    rw [← pow_mul]
    exact ratFunc_X_not_root _ (Nat.mul_pos (D.d_pos i) (by decide)))
  apply mul_left_cancel₀ hn
  have he (z : Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧) :
      thetaNorm D 𝕧 i * (quotientForm D).tmul (quotientForm D)
        ((quotientLDeriv D i).rTensor _ z) (a ⊗ₜ b) =
      (quotientForm D).tmul (quotientForm D) z
        ((toQuotient D 𝕧 (θ 𝕂 i) * a) ⊗ₜ b) := by
    induction z with
    | tmul c d =>
      simp only [LinearMap.rTensor_tmul, LinearMap.BilinForm.tensorDistrib_tmul,
        smul_eq_mul]
      rw [mul_left_comm, quotientForm_lDeriv]
    | add u v hu hv => simp only [map_add, LinearMap.add_apply, mul_add, hu, hv]
  rw [he, quotientComul_pair, quotientComul_pair, quotientForm_lDeriv, mul_assoc]

/-- Coideal annihilation on arbitrary actual left-kernel vectors (38.1.8(a)). -/
theorem quotientComul_left_kernel (i : I) {x : Quotient D 𝕧}
    (hx : quotientLDeriv D i x = 0) :
    (quotientLDeriv D i).rTensor _ (quotientComul D x) = 0 := by
  rw [quotientLDeriv_rTensor_comul, hx, map_zero]

/-- Actual zero-string projection fixes the first leg of the coproduct of a kernel vector. -/
theorem quotientSkewProjection_rTensor_comul (i : I) {x : Quotient D 𝕧}
    (hx : quotientLDeriv D i x = 0) :
    (quotientSkewProjection D i).rTensor _ (quotientComul D x) = quotientComul D x := by
  classical
  let b := Module.Free.chooseBasis 𝕂 (Quotient D 𝕧)
  let e := TensorProduct.equivFinsuppOfBasisRight (M := Quotient D 𝕧) b
  have he (f : Module.End 𝕂 (Quotient D 𝕧))
      (z : Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧) (j) : e (f.rTensor _ z) j = f (e z j) := by
    induction z with
    | tmul a c => simp [e]
    | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]
  apply e.injective
  ext j
  rw [he]
  apply quotientSkewProjection_of_ker
  rw [← he, quotientComul_left_kernel D i hx, map_zero, Finsupp.zero_apply]

/-- Coideal containment in the tensor image of the actual generated kernel algebra. -/
theorem quotientComul_mem_skewTensor (i : I) {x : Quotient D 𝕧}
    (hx : quotientLDeriv D i x = 0) :
    quotientComul D x ∈ LinearMap.range
      (TensorProduct.map (quotientSkewGenerators D i).toSubmodule.subtype
        (LinearMap.id : Module.End 𝕂 (Quotient D 𝕧))) := by
  let p : Quotient D 𝕧 →ₗ[𝕂] (quotientSkewGenerators D i).toSubmodule :=
    (quotientSkewProjection D i).codRestrict _ fun y ↦ by
      rw [quotientSkewGenerators_eq]
      exact quotientSkewProjection_mem D i y
  refine ⟨TensorProduct.map p LinearMap.id (quotientComul D x), ?_⟩
  have he (z : Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧) :
      TensorProduct.map (quotientSkewGenerators D i).toSubmodule.subtype LinearMap.id
        (TensorProduct.map p LinearMap.id z) = (quotientSkewProjection D i).rTensor _ z := by
    induction z with
    | tmul a b => rfl
    | add u v hu hv => simp only [map_add, hu, hv]
  rw [he, quotientSkewProjection_rTensor_comul D i hx]

lemma quotientForm_skewProjection_of_ker (i : I) (x : Quotient D 𝕧)
    {y : Quotient D 𝕧} (hy : quotientLDeriv D i y = 0) :
    quotientForm D (quotientSkewProjection D i x) y = quotientForm D x y := by
  obtain ⟨N, a, ha, rfl⟩ := exists_quotientSkewGenerators_decomposition D i x
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have ha' := (mem_quotientSkewGenerators_iff D i (a n)).mp (ha n)
  rw [quotientSkewProjection_divided_mul D i n ha']
  have h := quotientForm_divided_mul_of_mem_skewGenerators D i n 0 (ha n)
    ((mem_quotientSkewGenerators_iff D i y).mpr hy)
  have hzero : quotientIntegralGenerator D i 0 = 1 := by
    simp [quotientIntegralGenerator, qDivPow]
  rw [hzero, one_mul] at h
  rw [h]
  split_ifs with hn0
  · subst n
    simp [GrandLoop.coefU]
  · simp

/-- The existing boson projection is self-adjoint for the original form; no orthogonality
hypothesis is introduced. -/
theorem quotientSkewProjection_selfAdjoint (i : I) (x y : Quotient D 𝕧) :
    quotientForm D (quotientSkewProjection D i x) y =
      quotientForm D x (quotientSkewProjection D i y) := by
  have hp (z : Quotient D 𝕧) : quotientLDeriv D i (quotientSkewProjection D i z) = 0 :=
    quotientLDeriv_eq_zero_of_mem D i (quotientSkewProjection_mem D i z)
  calc
    quotientForm D (quotientSkewProjection D i x) y =
        quotientForm D y (quotientSkewProjection D i x) := quotientForm_comm D _ _
    _ = quotientForm D (quotientSkewProjection D i y)
        (quotientSkewProjection D i x) :=
      (quotientForm_skewProjection_of_ker D i y (hp x)).symm
    _ = quotientForm D (quotientSkewProjection D i x)
        (quotientSkewProjection D i y) := quotientForm_comm D _ _
    _ = _ := quotientForm_skewProjection_of_ker D i x (hp y)

/-- The actual free coproduct descended to the radical quotient and projected with the proved
zero-string projection on both factors, not a coproduct defined by transport through a braid. -/
def projectedQuotientComul (i : I) :
    Quotient D 𝕧 →ₗ[𝕂] Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧 :=
  TensorProduct.map (quotientSkewProjection D i) (quotientSkewProjection D i) ∘ₗ quotientComul D

/-- The actual projected coproduct is adjoint to multiplication on the actual left kernel. -/
theorem projectedQuotientComul_pair (i : I) (z : Quotient D 𝕧)
    {x y : Quotient D 𝕧} (hx : quotientLDeriv D i x = 0)
    (hy : quotientLDeriv D i y = 0) :
    (quotientForm D).tmul (quotientForm D) (projectedQuotientComul D i z) (x ⊗ₜ y) =
      quotientForm D z (x * y) := by
  have he (w : Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧) :
      (quotientForm D).tmul (quotientForm D)
        (TensorProduct.map (quotientSkewProjection D i) (quotientSkewProjection D i) w)
        (x ⊗ₜ y) = (quotientForm D).tmul (quotientForm D) w (x ⊗ₜ y) := by
    induction w with
    | tmul a b =>
      simp only [map_tmul, LinearMap.BilinForm.tensorDistrib_tmul,
        quotientForm_skewProjection_of_ker D i a hx,
        quotientForm_skewProjection_of_ker D i b hy]
    | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
  change (quotientForm D).tmul (quotientForm D)
    (TensorProduct.map _ _ (quotientComul D z)) _ = _
  rw [he, quotientComul_pair]

/-- Word reversal on the original radical quotient. -/
def quotientRev : Module.End 𝕂 (Quotient D 𝕧) :=
  (negativeQuotientEquiv D).toLinearMap ∘ₗ GrandLoop.starU D 𝕧 ∘ₗ
    (negativeQuotientEquiv D).symm.toLinearMap

@[simp] lemma quotientRev_toQuotient (a : LusztigF 𝕂 I) :
    quotientRev D (toQuotient D 𝕧 a) = toQuotient D 𝕧 (rev 𝕂 I a) := by
  simp only [quotientRev, LinearMap.comp_apply, LinearEquiv.coe_coe,
    negativeQuotientEquiv_symm_toQuotient, GrandLoop.starU_mk]
  rfl

@[simp] lemma quotientRev_rev (x : Quotient D 𝕧) : quotientRev D (quotientRev D x) = x := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  simp [rev_rev]

lemma quotientRev_mul (x y : Quotient D 𝕧) :
    quotientRev D (x * y) = quotientRev D y * quotientRev D x := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  obtain ⟨y, rfl⟩ := toQuotient_surjective D 𝕧 y
  simp only [← map_mul, quotientRev_toQuotient, rev_mul]

lemma quotientForm_rev (x y : Quotient D 𝕧) :
    quotientForm D (quotientRev D x) (quotientRev D y) = quotientForm D x y := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  obtain ⟨y, rfl⟩ := toQuotient_surjective D 𝕧 y
  simp only [quotientRev_toQuotient, quotientForm_toQuotient, form_rev]

/-- The original right skew derivation, obtained by word reversal. -/
def quotientRDeriv (i : I) : Module.End 𝕂 (Quotient D 𝕧) :=
  quotientRev D ∘ₗ quotientLDeriv D i ∘ₗ quotientRev D

@[simp] lemma quotientRDeriv_toQuotient (i : I) (a : LusztigF 𝕂 I) :
    quotientRDeriv D i (toQuotient D 𝕧 a) = toQuotient D 𝕧 (rDeriv D 𝕧 i a) := by
  simp [quotientRDeriv, lDeriv_rev, rev_rev]

lemma quotientRDeriv_mul_zero (i : I) {x y : Quotient D 𝕧}
    (hx : quotientRDeriv D i x = 0) (hy : quotientRDeriv D i y = 0) :
    quotientRDeriv D i (x * y) = 0 := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  obtain ⟨y, rfl⟩ := toQuotient_surjective D 𝕧 y
  rw [quotientRDeriv_toQuotient] at hx hy
  rw [← map_mul, quotientRDeriv_toQuotient, rDeriv_mul, map_add, map_mul, map_mul, hx, hy]
  simp

lemma quotientForm_rDeriv (i : I) (x y : Quotient D 𝕧) :
    thetaNorm D 𝕧 i * quotientForm D (quotientRDeriv D i x) y =
      quotientForm D x (y * toQuotient D 𝕧 (θ 𝕂 i)) := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  obtain ⟨y, rfl⟩ := toQuotient_surjective D 𝕧 y
  rw [quotientRDeriv_toQuotient, ← map_mul, quotientForm_toQuotient,
    quotientForm_toQuotient, form_comm D 𝕧 x, form_mul_θ, form_comm]

/-- The right-leg skew identity for the same descended coproduct. -/
theorem quotientRDeriv_lTensor_comul (i : I) (x : Quotient D 𝕧) :
    (quotientRDeriv D i).lTensor _ (quotientComul D x) =
      quotientComul D (quotientRDeriv D i x) := by
  apply sub_eq_zero.mp
  apply quotientForm_tensor_separates
  intro a b
  simp only [map_sub, LinearMap.sub_apply, sub_eq_zero]
  have hn : thetaNorm D 𝕧 i ≠ 0 := thetaNorm_ne_zero D 𝕧 (by
    rw [← pow_mul]
    exact ratFunc_X_not_root _ (Nat.mul_pos (D.d_pos i) (by decide)))
  apply mul_left_cancel₀ hn
  have he (z : Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧) :
      thetaNorm D 𝕧 i * (quotientForm D).tmul (quotientForm D)
        ((quotientRDeriv D i).lTensor _ z) (a ⊗ₜ b) =
      (quotientForm D).tmul (quotientForm D) z
        (a ⊗ₜ (b * toQuotient D 𝕧 (θ 𝕂 i))) := by
    induction z with
    | tmul c d =>
      simp only [LinearMap.lTensor_tmul, LinearMap.BilinForm.tensorDistrib_tmul,
        smul_eq_mul]
      rw [← mul_assoc, quotientForm_rDeriv]
    | add u v hu hv => simp only [map_add, LinearMap.add_apply, mul_add, hu, hv]
  rw [he, quotientComul_pair, quotientComul_pair, quotientForm_rDeriv, mul_assoc]

/-- Right coideal annihilation on arbitrary actual right-kernel vectors. -/
theorem quotientComul_right_kernel (i : I) {x : Quotient D 𝕧}
    (hx : quotientRDeriv D i x = 0) :
    (quotientRDeriv D i).lTensor _ (quotientComul D x) = 0 := by
  rw [quotientRDeriv_lTensor_comul, hx, map_zero]

section Braid
attribute [local instance] neZero_ratFunc_X
variable {Y : Type*} [AddCommGroup Y] (R : D.RootDatum Y)

/-- The actual braid image lies in the right skew kernel, proved from the accepted bounded
source-generator formula and kernel generation. -/
theorem quotientRDeriv_braid_image (i : I) {x y : Quotient D 𝕧}
    (hx : quotientLDeriv D i x = 0)
    (hxy : braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) = quotientPlus R y) :
    quotientRDeriv D i y = 0 := by
  have hex : ∀ x ∈ quotientSkewGenerators D i, ∃ y : Quotient D 𝕧,
      braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) = quotientPlus R y ∧
      quotientRDeriv D i y = 0 := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, hij, n, hn, rfl⟩ := hx
      refine ⟨toQuotient D 𝕧 (rev 𝕂 I
        (skewDividedGenerator D 𝕧 i j ((-D.cartanMatrix i j).toNat - n))),
        braid_skewDividedGenerator R hij n hn, ?_⟩
      simp only [quotientRDeriv_toQuotient, rDeriv_rev, skewDividedGenerator,
        map_smul, lDeriv_skewGenerator D 𝕧 i hij]
      simp
    | algebraMap c =>
      refine ⟨algebraMap 𝕂 _ c, by simp, ?_⟩
      rw [← (toQuotient D 𝕧).commutes, quotientRDeriv_toQuotient]
      simp
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', hx0⟩ := hx
      obtain ⟨y', hy', hy0⟩ := hy
      exact ⟨x' + y', by simp only [map_add, hx', hy'], by simp [hx0, hy0]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨x', hx', hx0⟩ := hx
      obtain ⟨y', hy', hy0⟩ := hy
      exact ⟨x' * y', by simp only [map_mul, hx', hy'], quotientRDeriv_mul_zero D i hx0 hy0⟩
  obtain ⟨z, hz, hz0⟩ := hex x ((mem_quotientSkewGenerators_iff D i x).mpr hx)
  have : z = y := quotientPlus_injective R (hz.symm.trans hxy)
  simpa only [this] using hz0

/-- Right coideal containment in the tensor image of the actual right skew kernel. -/
theorem quotientComul_mem_rightKernelTensor (i : I) {x : Quotient D 𝕧}
    (hx : quotientRDeriv D i x = 0) :
    quotientComul D x ∈ LinearMap.range
      ((LinearMap.ker (quotientRDeriv D i)).subtype.lTensor (Quotient D 𝕧)) := by
  have he : (LinearMap.ker (quotientRDeriv D i)).subtype.lTensor (Quotient D 𝕧) =
      AlgebraTensorModule.lTensor 𝕂 (Quotient D 𝕧)
        (LinearMap.ker (quotientRDeriv D i)).subtype := by
    ext a b
    rfl
  have hf : (quotientRDeriv D i).lTensor (Quotient D 𝕧) =
      AlgebraTensorModule.lTensor 𝕂 (Quotient D 𝕧) (quotientRDeriv D i) := by
    ext a b
    rfl
  rw [he, ← Module.Flat.ker_lTensor_eq 𝕂 (Quotient D 𝕧) (quotientRDeriv D i), ← hf]
  exact quotientComul_right_kernel D i hx

/-- Both coideal containments of Lusztig 38.1.8(a), for the actual braid-related elements.
This is not the projected braid compatibility of 38.1.8(b). -/
theorem quotientComul_braid_coideal (i : I) {x y : Quotient D 𝕧}
    (hx : quotientLDeriv D i x = 0)
    (hxy : braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) = quotientPlus R y) :
    quotientComul D x ∈ LinearMap.range
      (TensorProduct.map (quotientSkewGenerators D i).toSubmodule.subtype
        (LinearMap.id : Module.End 𝕂 (Quotient D 𝕧))) ∧
    quotientComul D y ∈ LinearMap.range
      ((LinearMap.ker (quotientRDeriv D i)).subtype.lTensor (Quotient D 𝕧)) :=
  ⟨quotientComul_mem_skewTensor D i hx,
    quotientComul_mem_rightKernelTensor D i (quotientRDeriv_braid_image D R i hx hxy)⟩

end Braid

namespace Modified
attribute [local instance] neZero_ratFunc_X laurentAlgebraK laurentAlgebraU laurentTowerU
variable {Y : Type*} [AddCommGroup Y] (R : D.RootDatum Y)
  {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}
  {i : I} {w : List I}

/-- The actual adapted tail and its actual braid image have the two coideal containments;
no finite Coxeter group, longest element, or additional kernel premise is needed. -/
theorem quotientComul_integralPBWPreimage_cons_zero
    (hw : cs.IsReduced (i :: w)) (c : Fin w.length → ℕ) :
    quotientComul D (integralPBWPreimage R hw (Fin.cons 0 c)) ∈ LinearMap.range
      (TensorProduct.map (quotientSkewGenerators D i).toSubmodule.subtype
        (LinearMap.id : Module.End 𝕂 (Quotient D 𝕧))) ∧
    quotientComul D (integralPBWPreimage R (w := w) (by simpa using hw.drop 1) c) ∈
      LinearMap.range
        ((LinearMap.ker (quotientRDeriv D i)).subtype.lTensor (Quotient D 𝕧)) := by
  apply quotientComul_braid_coideal D R i
  · exact quotientLDeriv_integralPBWPreimage_cons_zero R hw c
  · exact braid_integralPBWPreimage_cons_zero R hw c

end Modified
end LieLean.QuantumGroup
