/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import LieLean.Algebra.QuantumGroup.RestrictedBraidIsometry.ActualMap

/-!
# Restricted braid isometry

The original radical-quotient form is preserved by the actual restricted braid map
and its inverse. Inputs need not be homogeneous.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994), 38.2.1, pp. 300–301.
-/

noncomputable section
open LieLean LieLean.QuantumGroup LusztigF TensorProduct RightStringComparison
namespace RestrictedBraidIsometry
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (i : I)

lemma projectedBraid_projection (x : Quotient D 𝕧) :
    projectedBraid R i (quotientSkewProjection D i x) = projectedBraid R i x := by
  apply quotientPlus_injective R
  rw [projectedBraid_spec, projectedBraid_spec,
    quotientSkewProjection_of_ker D i
      (quotientLDeriv_eq_zero_of_mem D i (quotientSkewProjection_mem D i x))]

lemma projectedBraid_mul {a b : Quotient D 𝕧}
    (ha : a ∈ quotientSkewGenerators D i) (hb : b ∈ quotientSkewGenerators D i) :
    projectedBraid R i (a*b) = projectedBraid R i a * projectedBraid R i b := by
  rw [projectedBraid_of_mem R i ⟨a*b, mul_mem ha hb⟩,
    projectedBraid_of_mem R i ⟨a, ha⟩, projectedBraid_of_mem R i ⟨b, hb⟩]
  exact (braidRestriction R i).map_mul ⟨a,ha⟩ ⟨b,hb⟩

lemma projectedBraid_algebraMap (c : 𝕂) :
    projectedBraid R i (algebraMap 𝕂 _ c) = algebraMap 𝕂 _ c := by
  rw [projectedBraid_of_mem R i ⟨_, (quotientSkewGenerators D i).algebraMap_mem c⟩]
  exact (braidRestriction R i).commutes c

lemma projectedBraid_right {a : Quotient D 𝕧} (ha : a ∈ quotientSkewGenerators D i) :
    quotientRDeriv D i (projectedBraid R i a) = 0 := by
  have hker := (mem_quotientSkewGenerators_iff D i a).mp ha
  apply braid_image_right R i hker
  rw [projectedBraid_spec, quotientSkewProjection_of_ker D i hker]

/-- Public38.1.8(b), now as an equality inside the original positive quotient tensor square. -/
lemma original_compatibility {x : Quotient D 𝕧} (hx : x ∈ quotientSkewGenerators D i) :
    TensorProduct.map (projectedBraid R i) (projectedBraid R i) (quotientComul D x) =
      TensorProduct.map (rightProjection (D := D) i) (rightProjection (D := D) i)
        (quotientComul D (projectedBraid R i x)) := by
  have hker := (mem_quotientSkewGenerators_iff D i x).mp hx
  have hxy : braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) =
      quotientPlus R (projectedBraid R i x) := by
    rw [projectedBraid_spec, quotientSkewProjection_of_ker D i hker]
  have h := projected_braid_compatibility R i hker hxy
  have he : (quotientPlus R).toLinearMap ∘ₗ projectedBraid R i =
      ((braidEquivOfNotRoot R ratFunc_X_not_root i).toLinearMap ∘ₗ
        (quotientPlus R).toLinearMap) ∘ₗ quotientSkewProjection D i := by
    ext a
    exact projectedBraid_spec R i a
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (quotientPlus R).toLinearMap
    (LinearMap.ker_eq_bot.mpr (quotientPlus_injective R))
  have hmap : TensorProduct.map (quotientPlus R).toLinearMap (quotientPlus R).toLinearMap
      (TensorProduct.map (projectedBraid R i) (projectedBraid R i) (quotientComul D x)) =
      TensorProduct.map (quotientPlus R).toLinearMap (quotientPlus R).toLinearMap
        (TensorProduct.map (rightProjection (D := D) i) (rightProjection (D := D) i)
          (quotientComul D (projectedBraid R i x))) := by
    simpa only [TensorProduct.map_map, he] using h
  have hh := congrArg (TensorProduct.map r r) hmap
  simpa only [TensorProduct.map_map, ← LinearMap.comp_assoc, hr, LinearMap.id_comp] using hh

lemma quotientForm_rightProjection_of_ker (x : Quotient D 𝕧) {y : Quotient D 𝕧}
    (hy : quotientRDeriv D i y = 0) :
    quotientForm D (rightProjection (D := D) i x) y = quotientForm D x y := by
  calc
    _ = quotientForm D (quotientSkewProjection D i (quotientRev D x)) (quotientRev D y) := by
      have h := quotientForm_rev D (quotientSkewProjection D i (quotientRev D x))
        (quotientRev D y)
      simpa only [rightProjection, LinearMap.comp_apply, quotientRev_rev] using h
    _ = quotientForm D (quotientRev D x) (quotientRev D y) :=
      quotientForm_skewProjection_of_ker D i _ (left_rev_zero i hy)
    _ = _ := quotientForm_rev D x y

lemma right_projected_pair (z : Quotient D 𝕧) {a b : Quotient D 𝕧}
    (ha : quotientRDeriv D i a = 0) (hb : quotientRDeriv D i b = 0) :
    (quotientForm D).tmul (quotientForm D)
      (TensorProduct.map (rightProjection (D := D) i) (rightProjection (D := D) i)
        (quotientComul D z)) (a ⊗ₜ b) = quotientForm D z (a*b) := by
  have h (t : Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧) :
      (quotientForm D).tmul (quotientForm D)
        (TensorProduct.map (rightProjection (D := D) i) (rightProjection (D := D) i) t)
        (a ⊗ₜ b) = (quotientForm D).tmul (quotientForm D) t (a ⊗ₜ b) := by
    induction t with
    | tmul c d =>
      simp only [map_tmul, LinearMap.BilinForm.tensorDistrib_tmul,
        quotientForm_rightProjection_of_ker i c ha, quotientForm_rightProjection_of_ker i d hb]
    | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
  rw [h, quotientComul_pair]

/-- Multiplication step, using actual38.1.8(b) and original-form adjunction on both kernels. -/
lemma pairing_mul_step {a b : Quotient D 𝕧}
    (ha : a ∈ quotientSkewGenerators D i) (hb : b ∈ quotientSkewGenerators D i)
    (hfa : ∀ z ∈ quotientSkewGenerators D i,
      quotientForm D (projectedBraid R i a) (projectedBraid R i z) = quotientForm D a z)
    (hfb : ∀ z ∈ quotientSkewGenerators D i,
      quotientForm D (projectedBraid R i b) (projectedBraid R i z) = quotientForm D b z)
    {z : Quotient D 𝕧} (hz : z ∈ quotientSkewGenerators D i) :
    quotientForm D (projectedBraid R i (a*b)) (projectedBraid R i z) =
      quotientForm D (a*b) z := by
  have hp (u : Quotient D 𝕧) : quotientSkewProjection D i u ∈ quotientSkewGenerators D i :=
    (kernelProjection (D := D) i u).property
  have hpair (t : Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧) :
      (quotientForm D).tmul (quotientForm D)
        (TensorProduct.map (projectedBraid R i) (projectedBraid R i) t)
        (projectedBraid R i a ⊗ₜ projectedBraid R i b) =
      (quotientForm D).tmul (quotientForm D)
        (TensorProduct.map (quotientSkewProjection D i) (quotientSkewProjection D i) t)
        (a ⊗ₜ b) := by
    induction t with
    | tmul c d =>
      simp only [map_tmul, LinearMap.BilinForm.tensorDistrib_tmul]
      congr 1
      · rw [quotientForm_comm D _ (projectedBraid R i b),
          ← projectedBraid_projection R i d, hfb _ (hp d), quotientForm_comm]
      · rw [quotientForm_comm D _ (projectedBraid R i a),
          ← projectedBraid_projection R i c, hfa _ (hp c), quotientForm_comm]
    | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
  rw [projectedBraid_mul R i ha hb, quotientForm_comm D _ (projectedBraid R i z),
    ← right_projected_pair i _ (projectedBraid_right R i ha) (projectedBraid_right R i hb),
    ← original_compatibility R i hz, hpair]
  exact (projectedQuotientComul_pair D i z
    ((mem_quotientSkewGenerators_iff D i a).mp ha)
    ((mem_quotientSkewGenerators_iff D i b).mp hb)).trans (quotientForm_comm D z (a*b))

/-- Original radical-quotient form preserved by the actual restricted braid. -/
theorem projectedBraid_isometry {a z : Quotient D 𝕧}
    (ha : a ∈ quotientSkewGenerators D i) (hz : z ∈ quotientSkewGenerators D i) :
    quotientForm D (projectedBraid R i a) (projectedBraid R i z) = quotientForm D a z := by
  induction ha using Algebra.adjoin_induction generalizing z with
  | mem a ha =>
    obtain ⟨j, hij, n, hn, rfl⟩ := ha
    let g : Gen D i := ⟨(j,n), hij, hn⟩
    change quotientForm D (projectedBraid R i (sourceGen D i g)) (projectedBraid R i z) = _
    rw [projectedBraid_generator]
    exact generator_kernel_pairing R i g hz
  | algebraMap c =>
    rw [projectedBraid_algebraMap, Algebra.algebraMap_eq_smul_one]
    simp only [map_smul, LinearMap.smul_apply, one_kernel_pairing R i hz]
  | add a b _ _ ha hb => simp only [map_add, LinearMap.add_apply, ha hz, hb hz]
  | mul a b ha hb hfa hfb =>
    exact pairing_mul_step R i ha hb (fun z hz ↦ hfa hz) (fun z hz ↦ hfb hz) hz

/-- **Lusztig38.2.1**, for arbitrary original left-kernel vectors and their actual positive
`T''_(i,1)` images. No isometry, norm, expansion, or homogeneity is assumed. -/
theorem restricted_braid_isometry {x z y w : Quotient D 𝕧}
    (hx : quotientLDeriv D i x = 0) (hz : quotientLDeriv D i z = 0)
    (hxy : braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) = quotientPlus R y)
    (hzw : braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R z) = quotientPlus R w) :
    quotientForm D y w = quotientForm D x z := by
  have hy : projectedBraid R i x = y := by
    apply quotientPlus_injective R
    rw [projectedBraid_spec, quotientSkewProjection_of_ker D i hx, hxy]
  have hw : projectedBraid R i z = w := by
    apply quotientPlus_injective R
    rw [projectedBraid_spec, quotientSkewProjection_of_ker D i hz, hzw]
  rw [← hy, ← hw]
  exact projectedBraid_isometry R i
    ((mem_quotientSkewGenerators_iff D i x).mpr hx)
    ((mem_quotientSkewGenerators_iff D i z).mpr hz)

/-- The inverse `T'_(i,-1)` restriction preserves the same original form.
Positivity of both inverse images proves, rather than assumes, their left-kernel membership. -/
theorem restricted_inverse_braid_isometry {x z y w : Quotient D 𝕧}
    (hyx : (braidEquivOfNotRoot R ratFunc_X_not_root i).symm
      (quotientPlus R y) = quotientPlus R x)
    (hwz : (braidEquivOfNotRoot R ratFunc_X_not_root i).symm
      (quotientPlus R w) = quotientPlus R z) :
    quotientForm D x z = quotientForm D y w := by
  apply (restricted_braid_isometry R i (inverse_positive_left R i hyx)
    (inverse_positive_left R i hwz) ?_ ?_).symm
  · rw [← hyx, AlgEquiv.apply_symm_apply]
  · rw [← hwz, AlgEquiv.apply_symm_apply]

end RestrictedBraidIsometry
