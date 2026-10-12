/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.RightStringComparison.InverseExpansion

/-!
# Projected braid compatibility

The original projected coproduct equation of Lusztig 38.1.8(b).

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

/-- Actual forward braid images of the left kernel lie in the right kernel. -/
theorem braid_image_right (i : I) {x y : Quotient D 𝕧}
    (hx : quotientLDeriv D i x = 0)
    (hxy : braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) = quotientPlus R y) :
    quotientRDeriv D i y = 0 := by
  have h : ∀ a ∈ quotientSkewGenerators D i, ∃ b : Quotient D 𝕧,
      quotientRDeriv D i b = 0 ∧
        braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R a) = quotientPlus R b := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, hij, n, hn, rfl⟩ := ha
      refine ⟨quotientRev D (toQuotient D 𝕧
        (skewDividedGenerator D 𝕧 i j (negA D i j - n))), ?_, ?_⟩
      · apply right_rev_zero i
        rw [quotientLDeriv_toQuotient]
        simp [skewDividedGenerator, lDeriv_skewGenerator D 𝕧 i hij]
      · simpa only [quotientRev_toQuotient] using braid_skewDividedGenerator R hij n hn
    | algebraMap c =>
      refine ⟨toQuotient D 𝕧 (algebraMap 𝕂 _ c), ?_, ?_⟩
      · rw [quotientRDeriv_toQuotient]; simp
      · simp
    | add a b _ _ ha hb =>
      obtain ⟨a', ha', he⟩ := ha
      obtain ⟨b', hb', hf⟩ := hb
      exact ⟨a' + b', by simp [ha', hb'], by simp only [map_add, he, hf]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a', ha', he⟩ := ha
      obtain ⟨b', hb', hf⟩ := hb
      exact ⟨a' * b', quotientRDeriv_mul_zero D i ha' hb', by simp only [map_mul, he, hf]⟩
  obtain ⟨b, hb, he⟩ := h x ((mem_quotientSkewGenerators_iff D i x).mpr hx)
  have hby := quotientPlus_injective R (he.symm.trans hxy)
  simpa only [hby] using hb

/-- The first original projector is redundant on r of an actual left-kernel element. -/
theorem left_projector_redundant (i : I) {x : Quotient D 𝕧}
    (hx : quotientLDeriv D i x = 0) :
    TensorProduct.map (quotientSkewProjection D i) (quotientSkewProjection D i)
        (quotientComul D x) =
      TensorProduct.map LinearMap.id (quotientSkewProjection D i) (quotientComul D x) := by
  have h := congrArg (TensorProduct.map LinearMap.id (quotientSkewProjection D i))
    (quotientSkewProjection_rTensor_comul D i hx)
  simpa only [LinearMap.rTensor, TensorProduct.map_map, LinearMap.id_comp,
    LinearMap.comp_id] using h

/-- Actual coefficient identity, after constructing the expansion rather than assuming it.
It retains a finite family of strings, and identifies its precise zero-index sum in F⊗F. -/
theorem exists_zero_coefficient (i : I) {x y : Quotient D 𝕧}
    (hx : quotientLDeriv D i x = 0)
    (hxy : braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) = quotientPlus R y) :
    ∃ c : RightTerm (D := D) i →₀ 𝕂,
      (c.sum fun t d ↦ d • t.tensor) = quotientComul D y ∧
      braidDelta R 𝕧 ratFunc_X_not_root i (quotientPlus R x) =
        c.sum (fun t d ↦ d • t.inverseTensor R) ∧
      TensorProduct.map (quotientSkewProjection D i) (quotientSkewProjection D i)
          (quotientComul D x) =
        c.sum (fun t d ↦ if t.n = 0 then
          d • (inversePositive R i t.a t.ha ⊗ₜ[𝕂] inversePositive R i t.b t.hb) else 0) := by
  obtain ⟨c, hc, hd⟩ := exists_actual_inverse_expansion R i (braid_image_right R i hx hxy) hxy
  refine ⟨c, hc, hd, ?_⟩
  rw [left_projector_redundant i hx]
  have he := congrArg (extract R 0 0 i) hd
  rw [extract_braid_positive] at he
  rw [he]
  simp only [Finsupp.sum, map_sum, map_smul, extract_inverseTerm]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp

/-- **Lusztig 38.1.8(b)** for the original radical quotient, coproduct, braid and projectors.
No finite expansion, compatibility, isometry or faithfulness is a premise. Inputs need
not be homogeneous, and no finite Cartan type or linear independence of roots is assumed. -/
theorem projected_braid_compatibility (i : I) {x y : Quotient D 𝕧}
    (hx : quotientLDeriv D i x = 0)
    (hxy : braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) = quotientPlus R y) :
    TensorProduct.map
      ((braidEquivOfNotRoot R ratFunc_X_not_root i).toLinearMap ∘ₗ (quotientPlus R).toLinearMap)
      ((braidEquivOfNotRoot R ratFunc_X_not_root i).toLinearMap ∘ₗ (quotientPlus R).toLinearMap)
      (TensorProduct.map (quotientSkewProjection D i) (quotientSkewProjection D i)
        (quotientComul D x)) =
    TensorProduct.map (quotientPlus R).toLinearMap (quotientPlus R).toLinearMap
      (TensorProduct.map (rightProjection (D := D) i) (rightProjection (D := D) i)
        (quotientComul D y)) := by
  obtain ⟨c, hc, _, hz⟩ := exists_zero_coefficient R i hx hxy
  rw [hz, ← hc]
  simp only [Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro t _
  simp only [RightTerm.tensor, map_tmul, rightProjection_string i t.n t.ha,
    rightProjection_of_ker i t.hb]
  split_ifs with hn
  · simp only [map_smul, map_tmul, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      AlgHom.toLinearMap_apply, braid_inversePositive]
  · simp

end RightStringComparison
