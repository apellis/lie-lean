/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.RightStringComparison.RightSpan

/-!
# Actual inverse-braid expansion

Construct the ordered inverse expansion, including the reflected second-factor torus.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994),
37.3.1–37.3.2 and the proof of 38.1.8 (printed pp. 293, 297–299).
The finite-cutoff argument uses the actual quantum group and original Verma modules.
No restricted braid isometry or PBW norm conclusion is asserted here.
-/

noncomputable section
open LieLean LusztigF TensorProduct
open LieLean.QuantumGroup FiniteIntertwining VermaProjection
namespace RightStringComparison
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)

omit [Finite I] in
/-- Exact inverse divided-power formula, with the Cartan factor on the LEFT. -/
theorem inverse_divided_E (i : I) (n : ℕ) :
    (braidEquivOfNotRoot R ratFunc_X_not_root i).symm (qDivPow (𝕧 ^ D.d i) n (E R 𝕧 i)) =
      ((-1 : 𝕂) ^ n * (𝕧 ^ D.d i) ^ (-((n * (n - 1) : ℕ) : ℤ))) •
        (K R 𝕧 (-(n • ktilde R i)) * qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i)) := by
  apply (braidEquivOfNotRoot R ratFunc_X_not_root i).injective
  rw [AlgEquiv.apply_symm_apply, map_smul, map_mul,
    braidEquivOfNotRoot_qDivPow_F_self ratFunc_X_not_root R]
  have hk : braidEquivOfNotRoot R ratFunc_X_not_root i (K R 𝕧 (-(n • ktilde R i))) =
      K R 𝕧 (n • ktilde R i) := by
    simpa only [braidK_apply, map_neg, map_nsmul, reflY_ktilde, smul_neg, neg_neg,
      AlgEquiv.coe_toAlgHom] using
      (braidEquivOfNotRoot_hasImages ratFunc_X_not_root R i).map_K (-(n • ktilde R i))
  rw [hk, mul_smul_comm, ← mul_assoc, K_add, smul_neg, add_neg_cancel, K_zero, one_mul,
    smul_smul]
  have hcoeff : ((-1 : 𝕂) ^ n * (𝕧 ^ D.d i) ^ (-((n * (n - 1) : ℕ) : ℤ))) *
      ((-1) ^ n * (𝕧 ^ D.d i) ^ (n * (n - 1))) = 1 := by
    rw [mul_mul_mul_comm, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul,
      zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ RatFunc.X_ne_zero))]
  rw [hcoeff, one_smul]

/-- Chosen positive preimage is backed by the proved generator-algebra existence theorem. -/
def inversePositive (i : I) (b : Quotient D 𝕧) (hb : quotientRDeriv D i b = 0) :
    Quotient D 𝕧 := Classical.choose (exists_inverse_positive R i hb)

lemma inversePositive_spec (i : I) (b : Quotient D 𝕧) (hb : quotientRDeriv D i b = 0) :
    (braidEquivOfNotRoot R ratFunc_X_not_root i).symm (quotientPlus R b) =
      quotientPlus R (inversePositive R i b hb) :=
  Classical.choose_spec (exists_inverse_positive R i hb)

lemma inversePositive_left (i : I) (b : Quotient D 𝕧) (hb : quotientRDeriv D i b = 0) :
    quotientLDeriv D i (inversePositive R i b hb) = 0 :=
  inverse_positive_left R i (inversePositive_spec R i b hb)

lemma braid_inversePositive (i : I) (b : Quotient D 𝕧) (hb : quotientRDeriv D i b = 0) :
    braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R (inversePositive R i b hb)) =
      quotientPlus R b := by
  rw [← inversePositive_spec, AlgEquiv.apply_symm_apply]

/-- Actual inverse braid of the toral comparison map, acting on arbitrary tensors. -/
def inverseComparison (i : I) :
    (Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧) →ₗ[𝕂]
      (QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧) :=
  TensorProduct.map (braidEquivOfNotRoot R ratFunc_X_not_root i).symm.toLinearMap
    (braidEquivOfNotRoot R ratFunc_X_not_root i).symm.toLinearMap ∘ₗ
      quotientPositiveTensorComparison R

/-- The source's actual ordered inverse-braid summand. The second Cartan factor is
K_{s_i |b|}, not K_{|b|}; no assertion about a chosen homogeneous inverse is needed. -/
def RightTerm.inverseTensor {i : I} (t : RightTerm (D := D) i) :
    QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧 :=
  ((-1 : 𝕂) ^ t.n * (𝕧 ^ D.d i) ^ (-((t.n * (t.n - 1) : ℕ) : ℤ))) •
    ((quotientPlus R (inversePositive R i t.a t.ha) * K R 𝕧 (-(t.n • ktilde R i)) *
      qDivPow (𝕧 ^ D.d i) t.n (F R 𝕧 i) * K R 𝕧 (reflY R i (positiveToralWeight R t.ν))) ⊗ₜ
      quotientPlus R (inversePositive R i t.b t.hb))

/-- This is an equality for the original inverse braid and original toral insertion. -/
theorem inverseComparison_rightTerm (i : I) (t : RightTerm (D := D) i) :
    inverseComparison R i t.tensor = t.inverseTensor R := by
  have hc : quotientPositiveTensorComparison R t.tensor =
      (quotientPlus R (t.a * quotientIntegralGenerator D i t.n) *
        K R 𝕧 (positiveToralWeight R t.ν)) ⊗ₜ quotientPlus R t.b := by
    exact quotientPositiveTensorComparison_tmul_of_mem R _ t.hν
  simp only [inverseComparison, LinearMap.comp_apply, hc, map_tmul, AlgEquiv.toLinearMap_apply,
    map_mul, inverse_K]
  rw [inversePositive_spec R i t.a t.ha, inversePositive_spec R i t.b t.hb]
  rw [show quotientPlus R (quotientIntegralGenerator D i t.n) =
      qDivPow (𝕧 ^ D.d i) t.n (E R 𝕧 i) by simp [quotientIntegralGenerator, qDivPow]]
  rw [inverse_divided_E]
  simp only [RightTerm.inverseTensor, mul_smul_comm, smul_mul_assoc, smul_tmul', mul_assoc]

/-- Verma extraction removes all positive right-string indices; its surviving second
coefficient is already in the left kernel, by the actual positive inverse theorem. -/
theorem extract_inverseTerm (i : I) (t : RightTerm (D := D) i) :
    extract R 0 0 i (t.inverseTensor R) =
      if t.n = 0 then inversePositive R i t.a t.ha ⊗ₜ[𝕂] inversePositive R i t.b t.hb else 0 := by
  rw [RightTerm.inverseTensor, map_smul, extract_negative_string]
  split_ifs with hn
  · simp [hn, quotientSkewProjection_of_ker D i (inversePositive_left R i t.b t.hb)]
  · simp

/-- Genuine finite expansion of the original coproduct, not an expansion premise. -/
theorem exists_finite_right_expansion (i : I) {y : Quotient D 𝕧}
    (hy : quotientRDeriv D i y = 0) :
    ∃ c : RightTerm (D := D) i →₀ 𝕂,
      (c.sum fun t d ↦ d • t.tensor) = quotientComul D y :=
  Finsupp.mem_span_range_iff_exists_finsupp.mp (comul_mem_rightTermSpan i hy)

/-- Both actual coproduct expansions are constructed at once, with original maps. -/
theorem exists_actual_inverse_expansion (i : I) {x y : Quotient D 𝕧}
    (hy : quotientRDeriv D i y = 0)
    (hxy : braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) = quotientPlus R y) :
    ∃ c : RightTerm (D := D) i →₀ 𝕂,
      (c.sum fun t d ↦ d • t.tensor) = quotientComul D y ∧
      braidDelta R 𝕧 ratFunc_X_not_root i (quotientPlus R x) =
        c.sum (fun t d ↦ d • t.inverseTensor R) := by
  obtain ⟨c, hc⟩ := exists_finite_right_expansion i hy
  refine ⟨c, hc, ?_⟩
  have he : braidDelta R 𝕧 ratFunc_X_not_root i (quotientPlus R x) =
      inverseComparison R i (quotientComul D y) := by
    simp only [braidDelta, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hxy,
      comul_quotientPlus, inverseComparison, LinearMap.comp_apply]
    rfl
  rw [he, ← hc]
  simp only [Finsupp.sum, map_sum, map_smul, inverseComparison_rightTerm]

end RightStringComparison
