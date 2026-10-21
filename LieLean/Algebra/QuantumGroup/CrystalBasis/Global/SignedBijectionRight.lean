/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.CanonicalHighestWeight

/-!
# The bijections `°π_{i,n} : °𝐁_{i;0} → °𝐁_{i;n}`

This file proves [Lus] Thm. 14.3.2 (d) for the signed basis `𝐁 = {±G(b)}` of `U⁻ ≅ f`: for
`x ∈ °𝐁_{i;0}` there is a unique `y ∈ °𝐁_{i;n}` such that `x θᵢ^{(n)} - y` is an `𝒜`-linear
combination of elements of `°𝐁_{i;≥n+1}`, and `x ↦ y` is a bijection
`°π_{i,n} : °𝐁_{i;0} → °𝐁_{i;n}`.

## Main definitions

* `rightDf D i n`: right multiplication by `θᵢ^{(n)}` on `U⁻`, as `σ ∘ θᵢ^{(n)} ∘ σ`
  (`rightDf_mk`: it sends the class of `z` to the class of `z θᵢ^{(n)}`).
* `rightStringMap D i n`: Lusztig's `°π_{i,n} : °𝐁_{i;0} → °𝐁_{i;n}`.

## Main results

* `existsUnique_rightDf_sub_mem_span`, `rightStringMap_bijective`: [Lus] Thm. 14.3.2 (d).

## Implementation notes

As in [Lus], (d) follows from (c) (`existsUnique_df_sub_mem_span`, `signedStringMap_bijective`)
by applying the anti-automorphism `σ` (`starU`), which maps `𝐁_{i;≥n}` onto `°𝐁_{i;≥n}`
(`signedBasisGeRight_eq_image`) and commutes with the `𝒜`-action.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 14.3.2.
-/

open scoped RatFunc Pointwise

noncomputable section

universe u

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I : Type u} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

local notation "bosv" => bos (D := D) (pow_ne_one_of_transcendental' hvt)

/-! ### `σ` and the `𝒜`-action -/

omit [Finite I] in
lemma starU_laurent_smul (c : LaurentPolynomial ℤ) (x : Um D 𝕧) :
    starU D 𝕧 (c • x) = c • starU D 𝕧 x := by
  rw [laurent_smul_eq, laurent_smul_eq, map_smul]

omit [Finite I] in
lemma starU_mem_span_image {S : Set (Um D 𝕧)} {x : Um D 𝕧}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) S) :
    starU D 𝕧 x ∈ Submodule.span (LaurentPolynomial ℤ) (starU D 𝕧 '' S) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [starU_laurent_smul]; exact Submodule.smul_mem _ _ hx

omit [Finite I] [DecidableEq I] in
lemma starU_image_image (S : Set (Um D 𝕧)) : starU D 𝕧 '' (starU D 𝕧 '' S) = S := by
  simp only [Set.image_image, starU_starU, Set.image_id']

lemma mem_signedBasisGeRight_iff {i : I} {n : ℕ} {x : Um D 𝕧} :
    x ∈ signedBasisGeRight D i n ↔ starU D 𝕧 x ∈ signedBasisGe D i n := by
  rw [signedBasisGeRight_eq_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [starU_starU]
  · exact fun h ↦ ⟨_, h, starU_starU x⟩

/-- `°𝐁_{i;n} = σ(𝐁_{i;n})`. -/
lemma mem_signedBasisAtRight_iff {i : I} {n : ℕ} {x : Um D 𝕧} :
    x ∈ signedBasisAtRight D i n ↔ starU D 𝕧 x ∈ signedBasisAt D i n := by
  simp only [signedBasisAtRight, signedBasisAt, Set.mem_diff, mem_signedBasisGeRight_iff]

/-! ### Right multiplication by `θᵢ^{(n)}` -/

/-- Right multiplication by `θᵢ^{(n)}` on `U⁻ ≅ f`, as `σ ∘ θᵢ^{(n)} ∘ σ`. -/
def rightDf (i : I) (n : ℕ) : Module.End 𝕂 (Um D 𝕧) :=
  starU D 𝕧 ∘ₗ (bosv i).df n ∘ₗ starU D 𝕧

omit [Finite I] in
lemma rightDf_apply (i : I) (n : ℕ) (x : Um D 𝕧) :
    rightDf D i n x = starU D 𝕧 ((bosv i).df n (starU D 𝕧 x)) := rfl

omit [Finite I] in
/-- `rightDf D i n` is right multiplication by `θᵢ^{(n)} = θᵢⁿ / [n]ᵢ!`. -/
lemma rightDf_mk (i : I) (n : ℕ) (z : LusztigF 𝕂 I) :
    rightDf D i n (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (z * ((qFactorial (𝕧 ^ D.d i)⁻¹ n)⁻¹ • θ 𝕂 i ^ n)) := by
  have hf : (bosv i).f = NegativePart.f D 𝕧 i := rfl
  rw [rightDf_apply, starU_mk, BosonModule.df_apply, hf, f_pow_mk,
    ← Submodule.Quotient.mk_smul, starU_mk, map_smul, rev_mul, rev_rev, rev_θ_pow,
    mul_smul_comm]

/-! ### [Lus] 14.3.2 (d) -/

/-- **[Lus] Thm. 14.3.2 (d)**: for `x ∈ °𝐁_{i;0}` there is a unique `y ∈ °𝐁_{i;n}` such that
`x θᵢ^{(n)} - y` is an `𝒜`-linear combination of elements of `°𝐁_{i;≥n+1}`. -/
theorem existsUnique_rightDf_sub_mem_span {i : I} (n : ℕ) {x : Um D 𝕧}
    (hx : x ∈ signedBasisAtRight D i 0) :
    ∃! y, y ∈ signedBasisAtRight D i n ∧ rightDf D i n x - y ∈
      Submodule.span (LaurentPolynomial ℤ) (signedBasisGeRight D i (n + 1)) := by
  obtain ⟨y, ⟨hy, hxy⟩, huniq⟩ :=
    existsUnique_df_sub_mem_span D n ((mem_signedBasisAtRight_iff D).1 hx)
  refine ⟨starU D 𝕧 y, ⟨(mem_signedBasisAtRight_iff D).2 (by rwa [starU_starU]), ?_⟩, ?_⟩
  · have h := starU_mem_span_image D hxy
    rw [map_sub, ← signedBasisGeRight_eq_image] at h
    exact h
  · rintro y' ⟨hy', hxy'⟩
    have h := starU_mem_span_image D hxy'
    rw [signedBasisGeRight_eq_image, starU_image_image, map_sub, rightDf_apply,
      starU_starU] at h
    rw [← huniq _ ⟨(mem_signedBasisAtRight_iff D).1 hy', h⟩, starU_starU]

/-- **[Lus] 14.3.2 (d)**: the map `°π_{i,n} : °𝐁_{i;0} → °𝐁_{i;n}`, `x ↦ y` with
`x θᵢ^{(n)} - y` an `𝒜`-linear combination of elements of `°𝐁_{i;≥n+1}`; it is
`σ ∘ π_{i,n} ∘ σ`. -/
def rightStringMap (i : I) (n : ℕ) : signedBasisAtRight D i 0 → signedBasisAtRight D i n :=
  fun x ↦ ⟨starU D 𝕧
      (signedStringMap D i n ⟨starU D 𝕧 x, (mem_signedBasisAtRight_iff D).1 x.2⟩),
    (mem_signedBasisAtRight_iff D).2 (by rw [starU_starU]; exact Subtype.property _)⟩

lemma rightDf_sub_rightStringMap_mem_span (i : I) (n : ℕ) (x : signedBasisAtRight D i 0) :
    rightDf D i n x - rightStringMap D i n x ∈
      Submodule.span (LaurentPolynomial ℤ) (signedBasisGeRight D i (n + 1)) := by
  have h := starU_mem_span_image D
    (df_sub_signedStringMap_mem_span D i n ⟨starU D 𝕧 x, (mem_signedBasisAtRight_iff D).1 x.2⟩)
  rw [map_sub, ← signedBasisGeRight_eq_image] at h
  exact h

/-- **[Lus] Thm. 14.3.2 (d)**: `°π_{i,n} : °𝐁_{i;0} → °𝐁_{i;n}` is a bijection. -/
theorem rightStringMap_bijective (i : I) (n : ℕ) :
    Function.Bijective (rightStringMap D i n) := by
  obtain ⟨hinj, hsurj⟩ := signedStringMap_bijective D i n
  refine ⟨fun x₁ x₂ h ↦ ?_, fun y ↦ ?_⟩
  · have h' := congrArg (fun z : signedBasisAtRight D i n ↦ starU D 𝕧 (z : Um D 𝕧)) h
    simp only [rightStringMap, starU_starU] at h'
    have h'' := congrArg (fun z : signedBasisAt D i 0 ↦ starU D 𝕧 (z : Um D 𝕧))
      (hinj (Subtype.ext h'))
    simp only [starU_starU] at h''
    exact Subtype.ext h''
  · obtain ⟨x, hx⟩ := hsurj ⟨starU D 𝕧 y, (mem_signedBasisAtRight_iff D).1 y.2⟩
    refine ⟨⟨starU D 𝕧 x, (mem_signedBasisAtRight_iff D).2 (by rw [starU_starU]; exact x.2)⟩,
      Subtype.ext ?_⟩
    simp only [rightStringMap, starU_starU, Subtype.coe_eta, hx]

end LieLean.QuantumGroup
