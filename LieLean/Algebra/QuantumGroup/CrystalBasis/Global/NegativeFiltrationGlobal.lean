/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.FiltrationGlobal

/-!
# Global bases of the string filtrations of `U⁻`: [Kas91] Cor. 7.4.2

[Kas91] Cor. 7.4.2 states that, for `n ≥ 1`, `i ∈ I` and the weight `-ν`,

`(fᵢⁿU⁻)^ℤ_ν ∩ L(∞) ∩ L(∞)⁻ → (fᵢⁿU⁻)^ℤ_ν ∩ L(∞) / (fᵢⁿU⁻)^ℤ_ν ∩ v⁻¹L(∞)`

is an isomorphism onto the `ℤ`-span of `f̃ᵢⁿB(∞) ∩ B(∞)_ν`. As for Prop. 7.4.1
(`hwFiltGlobalAt`), we prove it in basis form (`NegFiltGlobalAt`), under the induction
hypothesis `GlobalBelow` at the weights below `ν`. The proof is Kashiwara's: for `λ` with
`⟨hⱼ, λ⟩ ≥ |ν|` for all `j`, `u ↦ u u_λ` identifies `U⁻_ν` with `V(λ)_{λ-ν}`
(`evq_injective`), `(fᵢⁿU⁻)^ℤ_ν` with `(fᵢⁿV(λ))^ℤ_{λ-ν}`, `L(∞)_ν` with `L(λ)_{λ-ν}`
(`mem_latticeInf_iff`, `mem_smul_latInf_iff`, [Jan] Thm. 10.10 (a)) and `L(∞)⁻_ν` with
`L(λ)⁻_{λ-ν}`.

## Main definitions

* `NegFiltGlobalAt D i n ν`: [Kas91] Cor. 7.4.2 at `(i, n, ν)`, in basis form.

## Main results

* `negFiltGlobalAt`: **[Kas91] Cor. 7.4.2**.
* `negFilt_eq_zero_of_mem`, `exists_negFilt_sub_mem`: the injectivity and surjectivity in (7.4.5).

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, §7.4.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, §10.
-/

open Pointwise

noncomputable section

universe u

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I : Type u} {Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I}

variable (D) in
/-- **[Kas91] Cor. 7.4.2** at `(i, n, ν)`, in basis form: `(fᵢⁿU⁻)^ℤ_ν` is the `𝒜`-span of
vectors `G_k ∈ (fᵢⁿU⁻)^ℤ_ν` with independent residues in `L(∞)/v⁻¹L(∞)` and in `L(∞)⁻/vL(∞)⁻`,
whose residues are the elements `f̃ᵢⁿ f̃_{u_k} 1` of `f̃ᵢⁿB(∞)`, with words `iⁿu_k` of weight
`ν`. -/
def NegFiltGlobalAt (i : I) (n : ℕ) (ν : I →₀ ℕ) : Prop :=
  ∃ (ι : Type u) (g : ι → Um D 𝕧) (u : ι → List I),
    (∀ k, g k ∈ negFilt D i n ν) ∧
    ResidueIndependent A (latInf (D := D) hvt A) ϖ g ∧
    ResidueIndependent LocalRing (latInfBar D) localX g ∧
    (∀ x ∈ negFilt D i n ν, x ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range g)) ∧
    (∀ k, g k - fWi (D := D) hvt (List.replicate n i ++ u k) ∈ ϖ • latInf (D := D) hvt A) ∧
    ∀ k, wordWeight (List.replicate n i ++ u k) = ν

variable {R : D.RootDatum Y} (hR : R.IsXRegular)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)

include hfund in
/-- **[Kas91] Cor. 7.4.2.** Under the induction hypothesis of [Kas91] §7 at the weights below
`ν`, for `i ∈ I` and `n ≥ 1`, `(fᵢⁿU⁻)^ℤ_ν` is the `𝒜`-span of a family with independent
residues on both sides, whose residues lie in `f̃ᵢⁿB(∞)` (`NegFiltGlobalAt`). Kashiwara's proof:
reduction to Prop. 7.4.1 (`hwFiltGlobalAt`) for `λ` large. -/
theorem negFiltGlobalAt {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) (i : I) {n : ℕ} (hn : 1 ≤ n) :
    NegFiltGlobalAt D i n ν := by
  classical
  obtain ⟨Λ, hΛ⟩ := exists_dom_ge (R := R) hfund ν.degree
  obtain ⟨ι, g, u, hgF, hg₀, hg₁, hspan, hgu, hgw⟩ := hwFiltGlobalAt hR hfund hIH Λ i hn
  choose x hx hxg using hgF
  have hxw : ∀ k, x k ∈ Uw D 𝕧 ν := fun k ↦ (mem_negFilt_le D (hx k)).2
  have hL : ∀ {z : Um D 𝕧}, z ∈ Uw D 𝕧 ν →
      (z ∈ latInf (D := D) hvt A ↔ evq hvt Λ z ∈ lat hvt hR A Λ) := fun hz ↦
    mem_latticeInf_iff InfinityLocalRing.injective_algebraMap
      InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
      InfinityLocalRing.exists_pow_mul hfund hΛ hz
  have hLs : ∀ {z : Um D 𝕧}, z ∈ latInf (D := D) hvt A → z ∈ Uw D 𝕧 ν →
      (z ∈ ϖ • latInf (D := D) hvt A ↔ evq hvt Λ z ∈ ϖ • lat hvt hR A Λ) := fun hz hzw ↦
    mem_smul_latInf_iff InfinityLocalRing.injective_algebraMap
      InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
      InfinityLocalRing.exists_pow_mul hfund hΛ hz hzw
  have hsum : ∀ (s : Finset ι) (a : ι → A),
      evq hvt Λ (∑ k ∈ s, a k • x k) = ∑ k ∈ s, a k • g k := fun s a ↦ by
    simp only [map_sum, LinearMap.map_smul_of_tower, hxg]
  have hr₀ : ResidueIndependent A (latInf (D := D) hvt A) ϖ x := by
    refine ⟨fun k ↦ (hL (hxw k)).2 (by rw [hxg]; exact hg₀.1 k), fun s a hs k hk ↦ ?_⟩
    refine hg₀.2 s a ?_ k hk
    rw [← hsum]
    exact evq_mem_smul_lat' hfund hs Λ
  have hr₁ : ResidueIndependent LocalRing (latInfBar D) localX x := by
    refine ⟨fun k ↦ ?_, fun s a hs k hk ↦ ?_⟩
    · rw [mem_latInfBar_iff, hL (negBar_mem_Uw D (hxw k)), ← hwBar_evq hR, hxg]
      exact hg₁.1 k
    · refine hg₁.2 s a ?_ k hk
      rw [mem_localX_smul_latInfBar_iff] at hs
      have : evq hvt Λ (negBar D (∑ k ∈ s, a k • x k)) ∈ ϖ • lat hvt hR A Λ :=
        evq_mem_smul_lat' hfund hs Λ
      rw [← hwBar_evq hR, ← mem_localX_smul_latBar_iff] at this
      simpa only [map_sum, LinearMap.map_smul_of_tower, hxg] using this
  have hinj : Function.Injective ((evq hvt Λ).comp (Uw D 𝕧 ν).subtype) :=
    evq_injective (hR := hR) hΛ
  refine ⟨ι, x, u, hx, hr₀, hr₁, fun y hy ↦ ?_, fun k ↦ ?_, hgw⟩
  · obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1
      (hspan _ (evq_mem_hwFilt Λ hy))
    have hz : (c.sum fun k a ↦ a • x k) ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range x) :=
      Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have hzF : (c.sum fun k a ↦ a • x k) ∈ negFilt D i n ν :=
      Submodule.span_le.2 (Set.range_subset_iff.2 hx) hz
    have hez : evq hvt Λ (c.sum fun k a ↦ a • x k) = evq hvt Λ y := by
      rw [← hc, Finsupp.sum, Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [laurent_smul_eq, map_smul, hxg, ← hw_laurent_smul_eq]
    have := @hinj ⟨_, (mem_negFilt_le D hzF).2⟩ ⟨y, (mem_negFilt_le D hy).2⟩ hez
    rw [← show (c.sum fun k a ↦ a • x k) = y from congrArg Subtype.val this]
    exact hz
  · have hfw : fWi (D := D) hvt (List.replicate n i ++ u k) ∈ Uw D 𝕧 ν := by
      rw [← hgw k]; exact fWi_mem_Uw _
    have hzw : x k - fWi (D := D) hvt (List.replicate n i ++ u k) ∈ Uw D 𝕧 ν :=
      sub_mem (hxw k) hfw
    have hzL : x k - fWi (D := D) hvt (List.replicate n i ++ u k) ∈ latInf (D := D) hvt A :=
      sub_mem (hr₀.1 k) (NegativePart.fWord_mem_latticeInf _ _ _)
    refine (hLs hzL hzw).2 ?_
    have h3 : evq hvt Λ (fWi hvt (List.replicate n i ++ u k)) -
        fW hvt hR Λ (List.replicate n i ++ u k) ∈ ϖ • lat hvt hR A Λ :=
      evq_fWord_sub_fW_mem InfinityLocalRing.injective_algebraMap
        InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
        InfinityLocalRing.exists_pow_mul hfund _ Λ
    have e : evq hvt Λ (x k - fWi (D := D) hvt (List.replicate n i ++ u k)) =
        (g k - fW hvt hR Λ (List.replicate n i ++ u k)) -
          (evq hvt Λ (fWi hvt (List.replicate n i ++ u k)) -
            fW hvt hR Λ (List.replicate n i ++ u k)) := by
      rw [map_sub, hxg]; abel
    rw [e]
    exact sub_mem (hgu k) h3

include hfund in
/-- Injectivity in [Kas91] (7.4.5): an element of `(fᵢⁿU⁻)^ℤ_ν ∩ v⁻¹L(∞) ∩ L(∞)⁻` vanishes. -/
theorem negFilt_eq_zero_of_mem {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) (i : I) {n : ℕ}
    (hn : 1 ≤ n) {x : Um D 𝕧} (hx : x ∈ negFilt D i n ν)
    (hxϖ : x ∈ ϖ • latInf (D := D) hvt A) (hx₁ : x ∈ latInfBar D) : x = 0 := by
  obtain ⟨ι, g, u, -, hg₀, hg₁, hspan, -, -⟩ := negFiltGlobalAt hR hfund hIH i hn
  exact balanced_eq_zero_of_mem_span (laurent_smul_eq D) hg₀ hg₁ (hspan x hx) hxϖ hx₁

include hfund in
/-- Surjectivity in [Kas91] (7.4.5): every element of `(fᵢⁿU⁻)^ℤ_ν ∩ L(∞)` is congruent modulo
`v⁻¹L(∞)` to an element of `(fᵢⁿU⁻)^ℤ_ν ∩ L(∞) ∩ L(∞)⁻`. -/
theorem exists_negFilt_sub_mem {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) (i : I) {n : ℕ}
    (hn : 1 ≤ n) {x : Um D 𝕧} (hx : x ∈ negFilt D i n ν) (hx₀ : x ∈ latInf (D := D) hvt A) :
    ∃ y ∈ negFilt D i n ν, y ∈ latInf (D := D) hvt A ∧ y ∈ latInfBar D ∧
      x - y ∈ ϖ • latInf (D := D) hvt A := by
  obtain ⟨ι, g, u, hgF, hg₀, hg₁, hspan, -, -⟩ := negFiltGlobalAt hR hfund hIH i hn
  obtain ⟨y, hy, hxy⟩ := exists_int_sub_mem_of_mem_span (laurent_smul_eq D) hg₀ (hspan x hx) hx₀
  have key : ∀ y ∈ Submodule.span ℤ (Set.range g),
      y ∈ negFilt D i n ν ∧ y ∈ latInf (D := D) hvt A ∧ y ∈ latInfBar D := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact ⟨hgF k, hg₀.1 k, hg₁.1 k⟩
    | zero => exact ⟨zero_mem _, zero_mem _, zero_mem _⟩
    | add y y' _ _ hy hy' => exact ⟨add_mem hy.1 hy'.1, add_mem hy.2.1 hy'.2.1,
        add_mem hy.2.2 hy'.2.2⟩
    | smul m y _ hy => exact ⟨zsmul_mem hy.1 m, zsmul_mem hy.2.1 m, zsmul_mem hy.2.2 m⟩
  exact ⟨y, (key y hy).1, (key y hy).2.1, (key y hy).2.2, hxy⟩

end LieLean.QuantumGroup
