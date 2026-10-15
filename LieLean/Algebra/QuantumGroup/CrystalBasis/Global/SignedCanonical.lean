/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.SignedBasis

/-!
# Lusztig's signed basis `𝐁` of `f`

Lusztig defines the canonical signed basis `𝐁` of `f` ([Lus] 14.2.3) as the set of `x ∈ 𝒜f` with
`x̄ = x` and `(x, x) ∈ 1 + v⁻¹ℤ[[v⁻¹]]`. We work in `U⁻ ≅ f` (`negativeQuotientEquiv`) and
identify `𝐁` with `{±G(b)}` for Kashiwara's global basis `G(b)`, `b ∈ B(∞)`.

## Main definitions

* `signedBasis`: Lusztig's `𝐁` ([Lus] 14.2.3), with no homogeneity condition.

## Main results

* `mem_latInf_of_formU_mem`: [Kas91] Prop. 5.1.3 for elements of `U⁻` that need not be
  homogeneous.
* `mem_signedBasis_iff`: `x ∈ 𝐁` if and only if `x = ±G(b)` for some `b ∈ B(∞)_ν`.
* `signedBasis_eq_iUnion`: [Lus] 14.2.5 (a), `𝐁 = ⋃_ν 𝐁_ν`.
* `linearIndependent_negGlobal`, `linearIndependent_negGlobal_laurent`, `mem_span_negGlobal`,
  `mem_span_negGlobal_field`: the `G(b)`, `b ∈ B(∞)_ν`, form a basis of `U⁻_ν` over `ℚ(v)` and
  of `U⁻_{ℤ,ν}` over `𝒜`. With `mem_signedBasis_iff`, this is [Lus] Thm. 14.2.3 (a) weight by
  weight: `𝐁_ν` is a signed basis of `f_ν` and of `𝒜f_ν`.

## Implementation notes

The proofs are our own. Lusztig proves 14.2.3 with the geometric construction of Part II; here
everything follows from Kashiwara's global basis ([Kas91] §7, `negGlobalAt`) and the signed
characterization `mem_signedGlobal_iff`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 14.2.3, 14.2.5.
* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, Prop. 5.1.3, §7.
-/

open scoped RatFunc Pointwise

noncomputable section

universe u

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X
local notation "hv'" => pow_ne_one_of_transcendental' transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I : Type u} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-! ### Weight components in `U⁻` -/

section Grading

omit [Finite I] [DecidableEq I] in
/-- `U⁻` is the sum of its weight spaces. -/
lemma mem_iSup_Uw (x : Um D 𝕧) : x ∈ ⨆ ν, Uw D 𝕧 ν := by
  have h : (⨆ ν, Uw D 𝕧 ν) = ⊤ := by
    simp only [Uw, ← Submodule.map_iSup, LusztigF.iSup_weightSpace, Submodule.map_top,
      Submodule.range_mkQ]
  rw [h]; trivial

omit [Finite I] [DecidableEq I] in
/-- An element of `U⁻` all of whose weight components vanish is zero. -/
lemma eq_zero_of_forall_proj {x : Um D 𝕧}
    (h : ∀ ν : I →₀ ℕ, NegativePart.proj D 𝕧 (LusztigF.toZ ν) x = 0) : x = 0 := by
  classical
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (mem_iSup_Uw D x)
  have hc : ∀ ν, f ν = 0 := fun ν ↦ by
    have := h ν
    rw [Finsupp.sum, map_sum] at this
    rw [Finset.sum_eq_single ν (fun μ _ hμ ↦ ?_) (fun hν ↦ ?_)] at this
    · rwa [proj_of_mem_Uw (hf ν), ite_eq_left rfl] at this
    · rw [proj_of_mem_Uw (hf μ), ite_eq_right fun e ↦ hμ (LusztigF.toZ_injective e)]
    · rw [Finsupp.notMem_support_iff.1 hν, map_zero]
  simp [Finsupp.sum, hc]

omit [Finite I] [DecidableEq I] in
/-- The weight projections of `U⁻` commute with the bar involution. -/
lemma negBar_proj (γ : I →₀ ℤ) (x : Um D 𝕧) :
    negBar D (NegativePart.proj D 𝕧 γ x) = NegativePart.proj D 𝕧 γ (negBar D x) := by
  classical
  induction mem_iSup_Uw D x using Submodule.iSup_induction' with
  | mem ν x hx =>
    rw [proj_of_mem_Uw hx, proj_of_mem_Uw (negBar_mem_Uw D hx)]
    split_ifs <;> simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Grading

/-! ### `[Kas91] Prop. 5.1.3` without homogeneity -/

section Lattice

/-- Every `x ∈ U⁻` has `ϖⁿ x ∈ L(∞)` for some `n`. -/
lemma exists_pow_smul_mem_latInf' (x : Um D 𝕧) :
    ∃ n : ℕ, ϖ ^ n • x ∈ latInf (D := D) hvt A := by
  let := Fintype.ofFinite I
  induction mem_iSup_Uw D x using Submodule.iSup_induction' with
  | mem ν x hx =>
    exact exists_pow_smul_mem_latInf (hR := D.isXRegular_extendedRootDatum)
      InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
      InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
      D.exists_fundamental_extendedRootDatum hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    rw [smul_add, pow_add, mul_comm, mul_smul, mul_comm, mul_smul]
    exact add_mem (Submodule.smul_mem _ _ hn) (Submodule.smul_mem _ _ hm)

/-- [Kas91] Prop. 5.1.3, for elements of `U⁻` that need not be homogeneous: if `(x, x) ∈ A`,
then `x ∈ L(∞)`. Kashiwara's proof, using `exists_pow_smul_mem_latInf'`. -/
theorem mem_latInf_of_formU_mem {x : Um D 𝕧} {a₀ : A}
    (ha₀ : formU hv' x x = algebraMap A 𝕂 a₀) : x ∈ latInf (D := D) hvt A := by
  classical
  let := Fintype.ofFinite I
  by_contra hnot
  have hex := exists_pow_smul_mem_latInf' D x
  set n := Nat.find hex with hn
  have hxL : ϖ ^ n • x ∈ latInf (D := D) hvt A := Nat.find_spec hex
  have hn0 : n ≠ 0 := fun h ↦ hnot (by simpa [h] using hxL)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hmL : ϖ ^ m • x ∉ latInf (D := D) hvt A := Nat.find_min hex (by omega)
  have hϖ0 : algebraMap A 𝕂 ϖ ≠ 0 := by
    rw [InfinityLocalRing.algebraMap_uniformizer]; exact inv_ne_zero RatFunc.X_ne_zero
  set y := ϖ ^ n • x with hy
  have hyS : y ∉ ϖ • latInf (D := D) hvt A := by
    intro h
    obtain ⟨z, hz, hzy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
    refine hmL ?_
    have : z = ϖ ^ m • x := by
      have e : (algebraMap A 𝕂 ϖ) • z = (algebraMap A 𝕂 ϖ) • (ϖ ^ m • x) := by
        rw [algebraMap_smul, algebraMap_smul, hzy, hy, hm, pow_succ', mul_smul]
      exact smul_right_injective _ hϖ0 e
    exact this ▸ hz
  have hyy : formU hv' y y = algebraMap A 𝕂 (ϖ * (ϖ ^ (2 * n - 1) * a₀)) := by
    simp only [hy, ← algebraMap_smul 𝕂 (ϖ ^ n) x, map_smul, LinearMap.smul_apply, ha₀,
      smul_eq_mul]
    have e2 : n + n = 2 * n - 1 + 1 := by omega
    rw [← map_mul, ← map_mul, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_succ', e2]
  exact hyS (mem_smul_latInf_of_formU_mem (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum hxL hyy)

end Lattice

/-! ### Lusztig's signed basis `𝐁` -/

section Signed

/-- Lusztig's signed basis `𝐁` of `f` ([Lus] 14.2.3), in `U⁻ ≅ f`: the elements `x ∈ 𝒜f` with
`x̄ = x` and `(x, x) ∈ 1 + v⁻¹ℤ[[v⁻¹]]`. No homogeneity is required. -/
def signedBasis : Set (Um D 𝕧) :=
  {x | x ∈ negIntegral D ∧ negBar D x = x ∧ ∃ g ∈ intSeriesInf, formU hv' x x = 1 + 𝕧⁻¹ * g}

/-- The elements of `𝐁` are the `±G(b)`, `b ∈ B(∞)_ν`, `ν ∈ ℕ[I]` (our own proof; see
`mem_signedGlobal_iff` for the homogeneous case). -/
theorem mem_signedBasis_iff {x : Um D 𝕧} :
    x ∈ signedBasis D ↔
      ∃ (ν : I →₀ ℕ) (b : negCrystal D ν), x = negGlobal D ν b ∨ x = -negGlobal D ν b := by
  classical
  constructor
  · rintro ⟨hxZ, hbar, g, hg, hxx⟩
    obtain ⟨a, rfl⟩ := exists_algebraMap_eq_of_mem_intSeriesInf hg
    have hxx' : formU hv' x x = algebraMap A 𝕂 (1 + ϖ * a) := by
      rw [hxx, map_add, map_one, map_mul, InfinityLocalRing.algebraMap_uniformizer]
    have hxL : x ∈ latInf (D := D) hvt A := mem_latInf_of_formU_mem D hxx'
    obtain ⟨w, e, he, hxw⟩ :=
      PBWSignedCrystal.exists_signed_crystal_residue D hxZ hxL ⟨a, hxx'⟩
    set ν := wordWeight w
    set b : negCrystal D ν := Quotient.mk _ ⟨w, rfl⟩
    have hout : fWi (D := D) hvt (Quotient.out b).1 - fWi hvt w ∈ ϖ • latInf (D := D) hvt A :=
      Quotient.exact (Quotient.out_eq b)
    set y := x - (e : 𝕂) • negGlobal D ν b with hy
    have hyS : y ∈ ϖ • latInf (D := D) hvt A := by
      have e1 : y = (x - (e : 𝕂) • fWi (D := D) hvt w) -
          (e : 𝕂) • ((negGlobal D ν b - fWi hvt (Quotient.out b).1) +
            (fWi hvt (Quotient.out b).1 - fWi hvt w)) := by
        rw [hy, sub_add_sub_cancel, smul_sub]; abel
      rw [e1]
      refine sub_mem hxw ?_
      rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (add_mem (negGlobal_sub_mem D ν b) hout) e
    obtain ⟨hG₁, -, hG₃, -⟩ := negGlobal_mem D ν b
    have hyZ : y ∈ negIntegral D := by
      rw [hy, Int.cast_smul_eq_zsmul]; exact sub_mem hxZ (zsmul_mem hG₁ e)
    have hyL : y ∈ latInf (D := D) hvt A := by
      rw [hy, Int.cast_smul_eq_zsmul]; exact sub_mem hxL (zsmul_mem hG₃ e)
    have hybar : negBar D y = y := by
      rw [hy, map_sub, negBar_smul, hbar, negBar_negGlobal, map_intCast]
    have hy0 : y = 0 := by
      refine eq_zero_of_forall_proj D fun μ ↦ ?_
      refine (negGlobalAt D μ).2 _ ⟨proj_mem_negIntegral D _ hyZ, proj_mem_Uw μ y,
        proj_mem_latInf _ hyL, ?_⟩ (proj_mem_smul_latInf _ hyS)
      rw [mem_latInfBar_iff, negBar_proj, hybar]
      exact proj_mem_latInf _ hyL
    refine ⟨ν, b, ?_⟩
    rw [hy, sub_eq_zero] at hy0
    rcases he with rfl | rfl
    · left; simpa using hy0
    · right; simpa using hy0
  · rintro ⟨ν, b, hb⟩
    exact (mem_signedGlobal_iff D (x := x) (by
      rcases hb with rfl | rfl
      · exact (negGlobal_mem D ν b).2.1
      · exact neg_mem (negGlobal_mem D ν b).2.1)).2 ⟨b, hb⟩

/-- **[Lus] 14.2.5 (a)**: `𝐁 = ⋃_ν 𝐁_ν` with `𝐁_ν = 𝐁 ∩ f_ν`; every element of `𝐁` is
homogeneous. -/
theorem signedBasis_eq_iUnion : signedBasis D = ⋃ ν, signedBasis D ∩ Uw D 𝕧 ν := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_inter_iff]
  refine ⟨fun hx ↦ ?_, fun ⟨_, hx, _⟩ ↦ hx⟩
  obtain ⟨ν, b, hb⟩ := (mem_signedBasis_iff D).1 hx
  refine ⟨ν, hx, ?_⟩
  rcases hb with rfl | rfl
  · exact (negGlobal_mem D ν b).2.1
  · exact neg_mem (negGlobal_mem D ν b).2.1

/-- The `G(b)`, `b ∈ B(∞)_ν`, are linearly independent over `ℚ(v)`. -/
theorem linearIndependent_negGlobal (ν : I →₀ ℕ) : LinearIndependent 𝕂 (negGlobal D ν) := by
  let := Fintype.ofFinite I
  exact (residueIndependent_negGlobalLift D.isXRegular_extendedRootDatum
    D.exists_fundamental_extendedRootDatum (globalBelow D.isXRegular_extendedRootDatum
      D.exists_fundamental_extendedRootDatum ν)).linearIndependent
    InfinityLocalRing.injective_algebraMap irreducible_localX.ne_zero
    InfinityLocalRing.exists_pow_mul irreducible_localX

/-- The `G(b)`, `b ∈ B(∞)_ν`, are linearly independent over `𝒜`. -/
theorem linearIndependent_negGlobal_laurent (ν : I →₀ ℕ) :
    LinearIndependent (LaurentPolynomial ℤ) (negGlobal D ν) := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  have h := linearIndependent_iff'.1 (linearIndependent_negGlobal D ν) s
    (fun j ↦ integralLaurentEval (c j)) (by simpa only [laurent_smul_eq] using hc) i hi
  exact integralLaurentEval_injective (by rw [h, map_zero])

/-- `U⁻_{ℤ,ν}` is the `𝒜`-span of the `G(b)`, `b ∈ B(∞)_ν` ([Kas91] (7.5.6)). -/
theorem mem_span_negGlobal {ν : I →₀ ℕ} {x : Um D 𝕧} (hxZ : x ∈ negIntegral D)
    (hxw : x ∈ Uw D 𝕧 ν) :
    x ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range (negGlobal D ν)) := by
  let := Fintype.ofFinite I
  exact mem_span_negGlobalLift D.isXRegular_extendedRootDatum
    D.exists_fundamental_extendedRootDatum (globalBelow D.isXRegular_extendedRootDatum
      D.exists_fundamental_extendedRootDatum ν) hxZ hxw

/-- `U⁻_ν` is the `ℚ(v)`-span of the `G(b)`, `b ∈ B(∞)_ν`. -/
theorem mem_span_negGlobal_field {ν : I →₀ ℕ} {x : Um D 𝕧} (hxw : x ∈ Uw D 𝕧 ν) :
    x ∈ Submodule.span 𝕂 (Set.range (negGlobal D ν)) := by
  set S := Submodule.span 𝕂 (Set.range (negGlobal D ν))
  have hZ : ∀ y, y ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range (negGlobal D ν)) →
      y ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy => rw [laurent_smul_eq]; exact S.smul_mem _ hy
  obtain ⟨N, hN⟩ := exists_inv_pow_smul_mem_latInf hxw
  have hc : ((𝕧⁻¹) ^ N : 𝕂) ≠ 0 := pow_ne_zero _ (inv_ne_zero RatFunc.X_ne_zero)
  have hW : ∀ y ∈ Submodule.span A (fWi (D := D) hvt '' {w | wordWeight w = ν}), y ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      exact hZ _ (mem_span_negGlobal D (fWi_mem_negIntegral D w) (hw ▸ fWi_mem_Uw w))
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy => rw [← algebraMap_smul 𝕂]; exact S.smul_mem _ hy
  have hcx := S.smul_mem (((𝕧⁻¹) ^ N : 𝕂)⁻¹)
    (hW _ (mem_span_fWi_of_mem hN (Submodule.smul_mem _ _ hxw)))
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hcx

end Signed

end LieLean.QuantumGroup
