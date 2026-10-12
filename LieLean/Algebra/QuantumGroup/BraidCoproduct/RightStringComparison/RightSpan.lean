/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.RightStringComparison.RightStrings

/-!
# Homogeneous right-kernel spanning

Finite right-string tensor expansions include arbitrary inhomogeneous inputs.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994),
37.3.1–37.3.2 and the proof of 38.1.8 (printed pp. 293, 297–299).
The finite-cutoff argument uses the actual quantum group and original Verma modules.
No restricted braid isometry or PBW norm conclusion is asserted here.
-/

noncomputable section
open LieLean LusztigF TensorProduct
open LieLean.QuantumGroup
namespace RightStringComparison
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X
variable {I : Type*} [Finite I] [DecidableEq I] {D : LusztigCartanDatum I}

/-- Original homogeneous subspace of the radical quotient. -/
abbrev degreeSpace (ν : I →₀ ℕ) : Submodule 𝕂 (Quotient D 𝕧) :=
  (LusztigF.weightSpace 𝕂 ν).map (toQuotient D 𝕧).toLinearMap

omit [Finite I] in
lemma degree_mul {ν μ : I →₀ ℕ} {a b : Quotient D 𝕧}
    (ha : a ∈ degreeSpace (D := D) ν) (hb : b ∈ degreeSpace (D := D) μ) :
    a * b ∈ degreeSpace (D := D) (ν + μ) := by
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  exact ⟨a * b, mul_mem_weightSpace ha hb, (toQuotient D 𝕧).map_mul a b⟩

lemma degree_rev {ν : I →₀ ℕ} {a : Quotient D 𝕧}
    (ha : a ∈ degreeSpace (D := D) ν) :
    quotientRev D a ∈ degreeSpace (D := D) ν := by
  obtain ⟨a, ha, rfl⟩ := ha
  exact ⟨rev 𝕂 I a, rev_mem_weightSpace ha, (quotientRev_toQuotient D a).symm⟩

omit [Finite I] [DecidableEq I] in
lemma skewGenerator_degree (i j : I) (n : ℕ) :
    skewGenerator D 𝕧 i j n ∈
      LusztigF.weightSpace 𝕂 (Finsupp.single j 1 + n • Finsupp.single i 1) := by
  induction n with
  | zero => simpa using (θ_mem_weightSpace (k := 𝕂) j)
  | succ n ih =>
    rw [skewGenerator_succ, skewAdjoint_apply, twist_skewGenerator, mul_smul_comm]
    have h₁ := mul_mem_weightSpace ih (θ_mem_weightSpace (k := 𝕂) i)
    have h₂ := mul_mem_weightSpace (θ_mem_weightSpace (k := 𝕂) i) ih
    convert Submodule.sub_mem _ h₁ (Submodule.smul_mem _ _ (by
      simpa only [add_comm] using h₂)) using 1
    · simp only [add_nsmul, one_nsmul, add_assoc]

/-- The finite linear span used below, indexed at the chosen node. -/
def rightHomogeneousSpan (i : I) : Submodule 𝕂 (Quotient D 𝕧) :=
  Submodule.span 𝕂 {b | quotientRDeriv D i b = 0 ∧ ∃ ν, b ∈ degreeSpace (D := D) ν}

lemma rightHomogeneousSpan_mul (i : I) {a b : Quotient D 𝕧}
    (ha : a ∈ rightHomogeneousSpan (D := D) i)
    (hb : b ∈ rightHomogeneousSpan (D := D) i) :
    a * b ∈ rightHomogeneousSpan (D := D) i := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨ha, ν, hν⟩ := ha
      obtain ⟨hb, μ, hμ⟩ := hb
      exact Submodule.subset_span ⟨quotientRDeriv_mul_zero D i ha hb,
        ν + μ, degree_mul hν hμ⟩
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using add_mem hb hc
    | smul c b _ hb => simpa only [mul_smul_comm] using Submodule.smul_mem _ c hb
  | zero => simp
  | add a c _ _ ha hc => simpa only [add_mul] using add_mem ha hc
  | smul c a _ ha => simpa only [smul_mul_assoc] using Submodule.smul_mem _ c ha

/-- Every right-kernel vector is a finite sum of homogeneous right-kernel vectors.
This uses actual bounded generator algebra induction, not assumed gradedness of the kernel. -/
theorem right_mem_homogeneousSpan (i : I) {b : Quotient D 𝕧}
    (hb : quotientRDeriv D i b = 0) : b ∈ rightHomogeneousSpan (D := D) i := by
  have h : ∀ a ∈ quotientSkewGenerators D i,
      quotientRev D a ∈ rightHomogeneousSpan (D := D) i := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, hij, n, hn, rfl⟩ := ha
      apply Submodule.subset_span
      constructor
      · apply right_rev_zero i
        rw [quotientLDeriv_toQuotient]
        simp [skewDividedGenerator, lDeriv_skewGenerator D 𝕧 i hij]
      · refine ⟨Finsupp.single j 1 + n • Finsupp.single i 1, degree_rev ?_⟩
        refine ⟨skewDividedGenerator D 𝕧 i j n, ?_, rfl⟩
        exact Submodule.smul_mem _ _ (skewGenerator_degree i j n)
    | algebraMap c =>
      have he : quotientRev D (algebraMap 𝕂 (Quotient D 𝕧) c) =
          toQuotient D 𝕧 (algebraMap 𝕂 _ c) := by
        rw [← (toQuotient D 𝕧).commutes, quotientRev_toQuotient, rev_algebraMap]
      rw [he]
      apply Submodule.subset_span
      refine ⟨?_, 0, ?_⟩
      · rw [quotientRDeriv_toQuotient]; simp
      · exact ⟨algebraMap 𝕂 _ c, algebraMap_mem_weightSpace c, rfl⟩
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [quotientRev_mul]; exact rightHomogeneousSpan_mul i hb ha
  simpa only [quotientRev_rev] using h (quotientRev D b)
    ((mem_quotientSkewGenerators_iff D i _).mpr (left_rev_zero i hb))

/-- An actual right string with a homogeneous second kernel factor. -/
structure RightTerm (i : I) where
  a : Quotient D 𝕧
  b : Quotient D 𝕧
  n : ℕ
  ν : I →₀ ℕ
  ha : quotientRDeriv D i a = 0
  hb : quotientRDeriv D i b = 0
  hν : b ∈ degreeSpace ν

/-- The literal tensor in the right-string expansion of r(y). -/
def RightTerm.tensor {i : I} (t : RightTerm (D := D) i) :
    Quotient D 𝕧 ⊗[𝕂] Quotient D 𝕧 :=
  (t.a * quotientIntegralGenerator D i t.n) ⊗ₜ t.b

/-- All tensors with their second leg in the actual right kernel are spanned by these strings. -/
theorem tmul_mem_rightTermSpan (i : I) (a : Quotient D 𝕧) {b : Quotient D 𝕧}
    (hb : quotientRDeriv D i b = 0) :
    a ⊗ₜ[𝕂] b ∈ Submodule.span 𝕂 (Set.range (RightTerm.tensor (D := D) (i := i))) := by
  have hb' := right_mem_homogeneousSpan i hb
  clear hb
  induction hb' using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨hb, ν, hν⟩ := hb
    obtain ⟨N, c, hc, he⟩ := exists_right_strings i a
    rw [he, sum_tmul]
    apply Submodule.sum_mem
    intro n hn
    exact Submodule.subset_span ⟨⟨c n, b, n, ν, hc n, hb, hν⟩, rfl⟩
  | zero => simp
  | add b c _ _ hb hc => simpa only [tmul_add] using add_mem hb hc
  | smul c b _ hb => simpa only [tmul_smul] using Submodule.smul_mem _ c hb

/-- The original coproduct has an actual finite right-string expansion. -/
theorem comul_mem_rightTermSpan (i : I) {y : Quotient D 𝕧}
    (hy : quotientRDeriv D i y = 0) :
    quotientComul D y ∈ Submodule.span 𝕂 (Set.range (RightTerm.tensor (D := D) (i := i))) := by
  obtain ⟨z, hz⟩ := quotientComul_mem_rightKernelTensor D i hy
  rw [← hz]
  clear hz
  induction z with
  | tmul a b => exact tmul_mem_rightTermSpan i a b.property
  | add z w hz hw => simpa only [map_add] using add_mem hz hw

end RightStringComparison
