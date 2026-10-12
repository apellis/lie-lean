/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.VermaProjection.Coefficients

/-!
# Original right strings

Reversal gives the right projection and actual positive inverse-braid coefficients.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994),
37.3.1–37.3.2 and the proof of 38.1.8 (printed pp. 293, 297–299).
The finite-cutoff argument uses the actual quantum group and original Verma modules.
No restricted braid isometry or PBW norm conclusion is asserted here.
-/

/-! Actual right strings and positive inverse braid coefficients in the original quotient.
Source: Lusztig, Introduction to quantum groups, proof of 38.1.8, printed 298–299.
The right projection is literally reversal composed with the existing left projection.
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

/-- The original opposite zero-string projector, not a transported coproduct. -/
def rightProjection (i : I) : Module.End 𝕂 (Quotient D 𝕧) :=
  quotientRev D ∘ₗ quotientSkewProjection D i ∘ₗ quotientRev D

lemma left_rev_zero (i : I) {x : Quotient D 𝕧} (hx : quotientRDeriv D i x = 0) :
    quotientLDeriv D i (quotientRev D x) = 0 := by
  have h := congrArg (quotientRev D) hx
  simpa [quotientRDeriv] using h

lemma right_rev_zero (i : I) {x : Quotient D 𝕧} (hx : quotientLDeriv D i x = 0) :
    quotientRDeriv D i (quotientRev D x) = 0 := by
  simp [quotientRDeriv, hx]

lemma rightProjection_mem (i : I) (x : Quotient D 𝕧) :
    quotientRDeriv D i (rightProjection (D := D) i x) = 0 :=
  right_rev_zero i (quotientLDeriv_eq_zero_of_mem D i (quotientSkewProjection_mem D i _))

lemma rightProjection_of_ker (i : I) {x : Quotient D 𝕧}
    (hx : quotientRDeriv D i x = 0) : rightProjection (D := D) i x = x := by
  simp only [rightProjection, LinearMap.comp_apply,
    quotientSkewProjection_of_ker D i (left_rev_zero i hx), quotientRev_rev]

lemma rev_integralGenerator (i : I) (n : ℕ) :
    quotientRev D (quotientIntegralGenerator D i n) = quotientIntegralGenerator D i n := by
  have hp : quotientRev D ((toQuotient D 𝕧 (θ 𝕂 i)) ^ n) =
      (toQuotient D 𝕧 (θ 𝕂 i)) ^ n := by
    induction n with
    | zero =>
      change quotientRev D (toQuotient D 𝕧 1) = toQuotient D 𝕧 1
      rw [quotientRev_toQuotient, rev_one]
    | succ n ih => rw [pow_succ, quotientRev_mul, ih, quotientRev_toQuotient, rev_θ,
        ← pow_succ', pow_succ]
  simpa only [quotientIntegralGenerator, qDivPow, map_smul, map_pow] using
    congrArg (fun z ↦ (qFactorial (𝕧 ^ D.d i) n)⁻¹ • z) hp

/-- Right-string projection, with every positive index actually killed. -/
theorem rightProjection_string (i : I) (n : ℕ) {a : Quotient D 𝕧}
    (ha : quotientRDeriv D i a = 0) :
    rightProjection (D := D) i (a * quotientIntegralGenerator D i n) =
      if n = 0 then a else 0 := by
  simp only [rightProjection, LinearMap.comp_apply, quotientRev_mul, rev_integralGenerator,
    quotientSkewProjection_divided_mul D i n (left_rev_zero i ha)]
  split_ifs <;> simp

/-- Constructed finite right-string decomposition of every inhomogeneous original element. -/
theorem exists_right_strings (i : I) (x : Quotient D 𝕧) :
    ∃ (N : ℕ) (a : ℕ → Quotient D 𝕧), (∀ n, quotientRDeriv D i (a n) = 0) ∧
      x = ∑ n ∈ Finset.range N, a n * quotientIntegralGenerator D i n := by
  obtain ⟨N, a, ha, he⟩ := exists_quotientSkewGenerators_decomposition D i (quotientRev D x)
  refine ⟨N, fun n ↦ quotientRev D (a n), ?_, ?_⟩
  · intro n
    exact right_rev_zero i ((mem_quotientSkewGenerators_iff D i _).mp (ha n))
  · have h := congrArg (quotientRev D) he
    simpa only [quotientRev_rev, map_sum, quotientRev_mul, rev_integralGenerator] using h

/-- Every actual right-kernel element has an actual positive inverse-braid preimage.
The construction uses bounded source generators and reversed ordered products. -/
theorem exists_inverse_positive (i : I) {b : Quotient D 𝕧}
    (hb : quotientRDeriv D i b = 0) :
    ∃ a : Quotient D 𝕧, (braidEquivOfNotRoot R ratFunc_X_not_root i).symm
      (quotientPlus R b) = quotientPlus R a := by
  have hgen : ∀ z ∈ quotientSkewGenerators D i, ∃ a : Quotient D 𝕧,
      braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R a) =
        quotientPlus R (quotientRev D z) := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨j, hij, n, hn, rfl⟩ := hz
      refine ⟨toQuotient D 𝕧 (skewDividedGenerator D 𝕧 i j (negA D i j - n)), ?_⟩
      have h := braid_skewDividedGenerator R hij (negA D i j - n) (Nat.sub_le _ _)
      have hn' : n ≤ negA D i j := hn
      simpa only [Nat.sub_sub_self hn', quotientRev_toQuotient] using h
    | algebraMap c =>
      refine ⟨algebraMap 𝕂 _ c, ?_⟩
      have hr : quotientRev D (algebraMap 𝕂 (Quotient D 𝕧) c) = algebraMap 𝕂 _ c := by
        rw [← (toQuotient D 𝕧).commutes, quotientRev_toQuotient]
        simp
      simp [hr]
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by simp only [map_add, ha, hb]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨b * a, by simp only [map_mul, ha, hb, quotientRev_mul]⟩
  obtain ⟨a, ha⟩ := hgen (quotientRev D b)
    ((mem_quotientSkewGenerators_iff D i _).mpr (left_rev_zero i hb))
  refine ⟨a, ?_⟩
  rw [quotientRev_rev] at ha
  rw [← ha, AlgEquiv.symm_apply_apply]

/-- Any positive inverse image necessarily belongs to the original left skew kernel. -/
theorem inverse_positive_left (i : I) {a b : Quotient D 𝕧}
    (hab : (braidEquivOfNotRoot R ratFunc_X_not_root i).symm
      (quotientPlus R b) = quotientPlus R a) : quotientLDeriv D i a = 0 := by
  apply (quotientLDeriv_eq_zero_iff_braid_positive R i a).mpr
  rw [← hab, AlgEquiv.apply_symm_apply]
  obtain ⟨b, rfl⟩ := toQuotient_surjective D 𝕧 b
  exact ⟨b, rfl⟩

omit [Finite I] in
/-- Inverse braid reflects the actual torus, with no weight normalization omitted. -/
theorem inverse_K (i : I) (μ : Y) :
    (braidEquivOfNotRoot R ratFunc_X_not_root i).symm (K R 𝕧 μ) =
      K R 𝕧 (reflY R i μ) := by
  apply (braidEquivOfNotRoot R ratFunc_X_not_root i).injective
  rw [AlgEquiv.apply_symm_apply]
  simpa only [braidK_apply, reflY_reflY, AlgEquiv.coe_toAlgHom] using
    ((braidEquivOfNotRoot_hasImages ratFunc_X_not_root R i).map_K (reflY R i μ)).symm

end RightStringComparison
