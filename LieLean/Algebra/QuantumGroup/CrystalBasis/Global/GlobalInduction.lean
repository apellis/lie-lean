/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.NegativeFiltrationSpan

/-!
# The induction of [Kas91] §7: global bases of `U⁻` and of `V(λ)`

Kashiwara proves the statements `(G_l)` of [Kas91] §7.2 by induction on `l`: for every weight
`ν` of height `l`,

* `(G.1)`: `E(ν) = U⁻_{ℤ,ν} ∩ L(∞) ∩ L(∞)⁻ → L_ℤ(∞)_ν / v⁻¹L_ℤ(∞)_ν` is an isomorphism
  (`NegGlobalAt`);
* `(G.2)`: the same for `V_ℤ(λ)_{λ-ν}`, `λ` dominant (`HwGlobalAt`);
* `(G.3)`: the lift `G(b)` of `b ∈ f̃ᵢⁿB(∞)` lies in `fᵢⁿU⁻`.

The induction step (§7.5) uses the part of `(G_{l-1})` packaged as `GlobalBelow`: `(G.1)`,
Lemma 7.5.2 and `(G.3)` for `n = 1`. This file completes the step and the induction.

* By Cor. 7.4.2 (`exists_negFilt_sub_mem`), every `b = f̃_w 1` with `w = i :: w'` has a lift
  `Gᵢ(b) ∈ (fᵢU⁻)^ℤ_ν ∩ L(∞) ∩ L(∞)⁻`; by Lemma 7.5.1 (`eq_of_mem_negFilt`) it does not depend on
  `i`. Indexing by `B(∞)_ν` (`negCrystal`, the words of weight `ν` modulo congruence) gives the
  family `negGlobalLift`, (7.5.4).
* These lifts are bar-invariant (`negBar_eq_of_mem_negFilt`; the argument of Lemma 7.3.4, with
  the injectivity of Cor. 7.4.2), so their residues are independent on both sides
  (`residueIndependent_negGlobalLift`, `residueIndependent_negGlobalLift_bar`).
* Since `U⁻_{ℤ,ν} = Σᵢ (fᵢU⁻)^ℤ_ν` (`mem_iSup_negFilt`) and `(fᵢU⁻)^ℤ_ν` is spanned by the
  `Gᵢ(b)` (Cor. 7.4.2), `U⁻_{ℤ,ν}` is the `𝒜`-span of the lifts, (7.5.6) (`mem_span_negGlobalLift`).
  Lemma 7.1.1 (ii) then gives `(G.1)` at `ν` (`negGlobalAt_of_globalBelow`).
* `(G.3)` for `n = 1` follows: if `ẽᵢb ≠ 0` then `b = f̃ᵢẽᵢb` ([Jan] 10.12) has a lift in
  `(fᵢU⁻)^ℤ` (`negLift_mem_negFilt`).
* **Lemma 7.5.2** (`evq_negLift_eq_zero`): if `π̄_λ(b) = 0` then `G(b)u_λ = 0`. Kashiwara's proof:
  for `ẽᵢb ≠ 0`, `G(b)u_λ ∈ (fᵢV(λ))^ℤ ∩ v⁻¹L(λ) ∩ L(λ)⁻`, which vanishes by Prop. 7.4.1.

Induction on `ν` (`globalAt`) then gives `(G.1)` at every weight (`negGlobalAt`) and `(G.2)` at
every weight and every dominant `λ` (`hwGlobalAt`, by `hwGlobalAt_of_vanishing`). Kashiwara
derives his Theorems 6 and 7 from these statements; we do not state them here.

The weight-zero case uses `U⁻_{ℤ,0} = 𝒜 · 1` (`mem_span_one_of_mem_Uw_zero`), which Kashiwara
calls obvious.

## Main definitions

* `negCrystal D ν`: `B(∞)_ν`, as words of weight `ν` modulo congruence modulo `v⁻¹L(∞)`.
* `negGlobalLift`: the lifts `G(b)`, `b ∈ B(∞)_ν`, under the induction hypothesis.

## Main results

* `negGlobalAt_of_globalBelow`: `(G.1)` at `ν` from `(G_{l-1})`.
* `evq_negLift_eq_zero`: **[Kas91] Lemma 7.5.2**.
* `negLift_mem_negFilt`: `(G.3)` for `n = 1`.
* `globalAt`: **`(G_l)` for every `l`** (the part used in the induction).
* `negGlobalAt`: `(G.1)` at every weight.
* `hwGlobalAt`: `(G.2)` at every weight and every dominant weight `λ`.

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, §7.2–7.5.
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

/-! ### `B(∞)_ν` as classes of words -/

section Crystal

variable (D) in
/-- Two words of weight `ν` are equivalent when they give the same element of `B(∞)`. -/
def negCrystalSetoid (ν : I →₀ ℕ) : Setoid {w : List I // wordWeight w = ν} where
  r w w' := fWi (D := D) hvt w.1 - fWi hvt w'.1 ∈ ϖ • latInf (D := D) hvt A
  iseqv := ⟨fun w ↦ by simp, fun h ↦ by rw [← neg_sub]; exact neg_mem h,
    fun h h' ↦ by rw [← sub_add_sub_cancel]; exact add_mem h h'⟩

variable (D) in
/-- `B(∞)_ν`. -/
abbrev negCrystal (ν : I →₀ ℕ) : Type u := Quotient (negCrystalSetoid D ν)

end Crystal

variable {R : D.RootDatum Y} (hR : R.IsXRegular)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)

/-! ### Bar invariance -/

section Bar

include hfund in
/-- [Kas91] Lemma 7.3.4 for `(fᵢU⁻)^ℤ`: under the induction hypothesis, every element of
`(fᵢU⁻)^ℤ_ν ∩ L(∞) ∩ L(∞)⁻` is bar-invariant. Kashiwara's argument: `(x - x̄)/(v - v⁻¹)` lies in
`(fᵢU⁻)^ℤ_ν ∩ v⁻¹L(∞) ∩ L(∞)⁻`, which is zero by Cor. 7.4.2. -/
theorem negBar_eq_of_mem_negFilt {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) {i : I} {x : Um D 𝕧}
    (hx : x ∈ negFilt D i 1 ν) (hx₀ : x ∈ latInf (D := D) hvt A) (hx₁ : x ∈ latInfBar D) :
    negBar D x = x := by
  obtain ⟨hxZ, hxw⟩ := mem_negFilt_le D hx
  obtain ⟨y, hyZ, hxy⟩ := exists_sub_negBar_eq_smul D hxZ
  have hne : (RatFunc.X - RatFunc.X⁻¹ : 𝕂) ≠ 0 := by
    intro h
    have h' : (RatFunc.X : 𝕂) ^ 2 = 1 := by
      rw [sq]; nth_rewrite 2 [sub_eq_zero.1 h]; exact mul_inv_cancel₀ RatFunc.X_ne_zero
    exact pow_ne_one_of_transcendental' transcendental_ratFunc_X 2 two_pos h'
  have hy' : y = (RatFunc.X - RatFunc.X⁻¹ : 𝕂)⁻¹ • (x - negBar D x) := by
    rw [hxy, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hb₀ : negBar D x ∈ latInf (D := D) hvt A := (mem_latInfBar_iff D x).1 hx₁
  have hb₁ : negBar D x ∈ latInfBar D := negBar_mem_latInfBar D hx₀
  have hyϖ : y ∈ ϖ • latInf (D := D) hvt A := by
    obtain ⟨u, hu⟩ := exists_inv_X_sub_eq_uniformizer_mul
    rw [hy', ← hu, algebraMap_smul, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.smul_mem _ _ (sub_mem hx₀ hb₀))
  have hy₁ : y ∈ latInfBar D := by
    obtain ⟨u, hu⟩ := exists_inv_X_sub_eq_localX_mul
    rw [hy', ← hu, algebraMap_smul]
    exact Submodule.smul_mem _ _ (sub_mem hx₁ hb₁)
  have hyF : y ∈ negFilt D i 1 ν := by
    refine (mem_negFilt_iff_comp_zero D).2 ⟨hyZ, ?_, ?_⟩
    · rw [hy']
      exact Submodule.smul_mem _ _ (sub_mem hxw (negBar_mem_Uw D hxw))
    · rw [hy', map_smul, map_sub, comp_zero_of_mem_negFilt D hx,
        comp_zero_of_mem_negFilt D (negBar_mem_negFilt D hx), sub_zero, smul_zero]
  have hy0 : y = 0 := negFilt_eq_zero_of_mem hR hfund hIH i le_rfl hyF hyϖ hy₁
  rw [hy0, smul_zero, sub_eq_zero] at hxy
  exact hxy.symm

omit [Finite I] in
lemma negBar_fWi_nil : negBar D (fWi (D := D) hvt []) = fWi hvt [] := by
  change negBar D (Submodule.Quotient.mk 1) = Submodule.Quotient.mk 1
  rw [negBar_mk, map_one]

end Bar

/-! ### The lifts `G(b)` -/

section Lift

include hfund in
/-- Every word `w` of weight `ν` has a lift in `E(ν)`, which is bar-invariant, lies in
`(fᵢU⁻)^ℤ_ν` if `w = i :: w'` (Cor. 7.4.2) and is `1` if `w` is empty. -/
lemma exists_negGlobalLift {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) (w : List I)
    (hw : wordWeight w = ν) :
    ∃ y ∈ negBalanced D ν, y - fWi (D := D) hvt w ∈ ϖ • latInf (D := D) hvt A ∧
      negBar D y = y ∧ (w = [] → y = fWi hvt []) ∧
      ∀ i w', w = i :: w' → y ∈ negFilt D i 1 ν := by
  cases w with
  | nil =>
    refine ⟨fWi hvt [], ⟨fWi_mem_negIntegral D [], hw ▸ fWi_mem_Uw [],
      NegativePart.fWord_mem_latticeInf _ _ [], ?_⟩, by simp, negBar_fWi_nil,
      fun _ ↦ rfl, fun _ _ h ↦ (by cases h)⟩
    rw [mem_latInfBar_iff, negBar_fWi_nil]
    exact NegativePart.fWord_mem_latticeInf _ _ []
  | cons i w' =>
    have hx : fWi (D := D) hvt (i :: w') ∈ negFilt D i 1 ν := hw ▸ fWi_cons_mem_negFilt D i w'
    obtain ⟨y, hy, hy₀, hy₁, hxy⟩ := exists_negFilt_sub_mem hR hfund hIH i le_rfl hx
      (NegativePart.fWord_mem_latticeInf _ _ _)
    refine ⟨y, ⟨(mem_negFilt_le D hy).1, (mem_negFilt_le D hy).2, hy₀, hy₁⟩,
      by rw [← neg_sub]; exact neg_mem hxy, negBar_eq_of_mem_negFilt hR hfund hIH hy hy₀ hy₁,
      (fun h ↦ by cases h), fun j w'' h ↦ ?_⟩
    obtain ⟨rfl, -⟩ := List.cons.inj h
    exact hy

/-- The lift `G(b)` of `b ∈ B(∞)_ν` ([Kas91] (7.5.4)), under the induction hypothesis. -/
def negGlobalLift {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) (b : negCrystal D ν) : Um D 𝕧 :=
  (exists_negGlobalLift hR hfund hIH (Quotient.out b).1 (Quotient.out b).2).choose

lemma negGlobalLift_spec {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) (b : negCrystal D ν) :
    negGlobalLift hR hfund hIH b ∈ negBalanced D ν ∧
      negGlobalLift hR hfund hIH b - fWi (D := D) hvt (Quotient.out b).1 ∈
        ϖ • latInf (D := D) hvt A ∧
      negBar D (negGlobalLift hR hfund hIH b) = negGlobalLift hR hfund hIH b ∧
      ((Quotient.out b).1 = [] → negGlobalLift hR hfund hIH b = fWi hvt []) ∧
      ∀ i w', (Quotient.out b).1 = i :: w' → negGlobalLift hR hfund hIH b ∈ negFilt D i 1 ν :=
  (exists_negGlobalLift hR hfund hIH (Quotient.out b).1 (Quotient.out b).2).choose_spec

/-- The lifts `G(b)` have independent residues in `L(∞)/v⁻¹L(∞)` ([Jan] Prop. 10.11 (b)). -/
theorem residueIndependent_negGlobalLift {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) :
    ResidueIndependent A (latInf (D := D) hvt A) ϖ (negGlobalLift hR hfund hIH) := by
  classical
  refine ⟨fun b ↦ (negGlobalLift_spec hR hfund hIH b).1.2.2.1, fun s a hs b hb ↦ ?_⟩
  set o : negCrystal D ν → List I := fun c ↦ (Quotient.out c).1
  have hinj : Set.InjOn o s := fun c₁ _ c₂ _ he ↦ Quotient.out_injective (Subtype.ext he)
  have hsum : ∑ c ∈ s, a c • fWi (D := D) hvt (o c) ∈ ϖ • latInf (D := D) hvt A := by
    have e : ∑ c ∈ s, a c • fWi (D := D) hvt (o c) = ∑ c ∈ s, a c • negGlobalLift hR hfund hIH c -
        ∑ c ∈ s, a c • (negGlobalLift hR hfund hIH c - fWi hvt (o c)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ ↦ by rw [smul_sub, sub_sub_cancel]
    rw [e]
    exact sub_mem hs (Submodule.sum_mem _ fun c _ ↦ Submodule.smul_mem _ _
      (negGlobalLift_spec hR hfund hIH c).2.1)
  let a' : List I → A := fun w ↦ if h : wordWeight w = ν then a (Quotient.mk _ ⟨w, h⟩) else 0
  have ha' : ∀ c, a' (o c) = a c := fun c ↦ by
    change (if h : _ then _ else _) = _
    split_ifs with h
    · exact congrArg a (Quotient.out_eq c)
    · exact absurd (Quotient.out c).2 h
  have := coeff_mem_of_sum_fWi_mem (hR := hR) InfinityLocalRing.injective_algebraMap
    InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
    InfinityLocalRing.exists_pow_mul hfund (s.image o)
    (fun w hw ↦ by obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hw; exact (Quotient.out c).2)
    (fun w₁ hw₁ w₂ hw₂ hne hmem ↦ by
      obtain ⟨c₁, -, rfl⟩ := Finset.mem_image.1 hw₁
      obtain ⟨c₂, -, rfl⟩ := Finset.mem_image.1 hw₂
      refine hne (congrArg o ?_)
      rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂]
      exact Quotient.sound hmem)
    a' (by rw [Finset.sum_image hinj]; simpa only [ha'] using hsum) (o b)
    (Finset.mem_image_of_mem o hb)
  rw [ha'] at this
  exact Ideal.mem_span_singleton.1 this

/-- The lifts `G(b)` have independent residues in `L(∞)⁻/vL(∞)⁻`. -/
theorem residueIndependent_negGlobalLift_bar {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) :
    ResidueIndependent LocalRing (latInfBar D) localX (negGlobalLift hR hfund hIH) := by
  have h := residueIndependent_latInfBar D (residueIndependent_negGlobalLift hR hfund hIH)
  have e : (fun b ↦ negBar D (negGlobalLift hR hfund hIH b)) = negGlobalLift hR hfund hIH :=
    funext fun b ↦ (negGlobalLift_spec hR hfund hIH b).2.2.1
  rwa [e] at h

/-- For `ν ≠ 0`, the lift of `b = f̃_w 1` lies in `(fⱼU⁻)^ℤ_ν` for some `j`. -/
lemma exists_negGlobalLift_mem_negFilt {ν : I →₀ ℕ} (hν : ν ≠ 0) (hIH : GlobalBelow hR ν)
    (b : negCrystal D ν) : ∃ j, negGlobalLift hR hfund hIH b ∈ negFilt D j 1 ν := by
  have hne : (Quotient.out b).1 ≠ [] := fun h ↦ hν (by rw [← (Quotient.out b).2, h]; rfl)
  obtain ⟨j, w', hj⟩ := List.exists_cons_of_ne_nil hne
  exact ⟨j, (negGlobalLift_spec hR hfund hIH b).2.2.2.2 j w' hj⟩

/-- Every element of `(fᵢU⁻)^ℤ_ν` is an `𝒜`-combination of the `G(b)`: the spanning family of
Cor. 7.4.2 consists of lifts `G(b)`, by Lemma 7.5.1. -/
lemma negFilt_le_span_negGlobalLift {ν : I →₀ ℕ} (hν : ν ≠ 0) (hIH : GlobalBelow hR ν) (i : I) :
    negFilt D i 1 ν ≤
      Submodule.span (LaurentPolynomial ℤ) (Set.range (negGlobalLift hR hfund hIH)) := by
  obtain ⟨ι, g, u, hgF, -, hg₁, hspan, hgu, hgw⟩ := negFiltGlobalAt hR hfund hIH i le_rfl
  intro x hx
  refine Submodule.span_le.2 (Set.range_subset_iff.2 fun k ↦ ?_) (hspan x hx)
  set b : negCrystal D ν := Quotient.mk _ ⟨i :: u k, hgw k⟩
  obtain ⟨j, hj⟩ := exists_negGlobalLift_mem_negFilt hR hfund hν hIH b
  have hb : fWi (D := D) hvt (Quotient.out b).1 - fWi hvt (i :: u k) ∈
      ϖ • latInf (D := D) hvt A :=
    Quotient.mk_out (s := negCrystalSetoid D ν) ⟨i :: u k, hgw k⟩
  have hGb : negGlobalLift hR hfund hIH b - fWi hvt (i :: u k) ∈ ϖ • latInf (D := D) hvt A := by
    rw [← sub_add_sub_cancel _ (fWi hvt (Quotient.out b).1)]
    exact add_mem (negGlobalLift_spec hR hfund hIH b).2.1 hb
  have e : g k = negGlobalLift hR hfund hIH b :=
    eq_of_mem_negFilt hR hfund hIH (by simp) (hgF k) (hg₁.1 k) (hgu k) hj
      (negGlobalLift_spec hR hfund hIH b).1.2.2.2 hGb
  rw [e]
  exact Submodule.subset_span ⟨b, rfl⟩

/-- **[Kas91] (7.5.6)**: under the induction hypothesis, `U⁻_{ℤ,ν}` is the `𝒜`-span of the lifts
`G(b)`, `b ∈ B(∞)_ν`. -/
theorem mem_span_negGlobalLift {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) {x : Um D 𝕧}
    (hxZ : x ∈ negIntegral D) (hxw : x ∈ Uw D 𝕧 ν) :
    x ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range (negGlobalLift hR hfund hIH)) := by
  by_cases hν : ν = 0
  · subst hν
    refine Submodule.span_le.2 ?_ (mem_span_one_of_mem_Uw_zero D hxZ hxw)
    rintro _ rfl
    set b : negCrystal D 0 := Quotient.mk _ ⟨[], rfl⟩
    have hnil : (Quotient.out b).1 = [] := GrandLoop.eq_nil_of_wordWeight_eq_zero (Quotient.out b).2
    rw [← (negGlobalLift_spec hR hfund hIH b).2.2.2.1 hnil]
    exact Submodule.subset_span ⟨b, rfl⟩
  · exact (iSup_le fun i ↦ negFilt_le_span_negGlobalLift hR hfund hν hIH i)
      (mem_iSup_negFilt D hν hxZ hxw)

end Lift

/-! ### The induction step -/

section Step

include hfund in
/-- **`(G.1)` at `ν`** from the induction hypothesis ([Kas91] §7.5: from (7.5.6) and
Lemma 7.1.1 (ii)). -/
theorem negGlobalAt_of_globalBelow {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) : NegGlobalAt D ν := by
  have h₀ := residueIndependent_negGlobalLift hR hfund hIH
  have h₁ := residueIndependent_negGlobalLift_bar hR hfund hIH
  refine ⟨fun x hxZ hxw hx₀ ↦ ?_, fun x hx hxϖ ↦ ?_⟩
  · obtain ⟨y, hy, hxy⟩ := exists_int_sub_mem_of_mem_span (laurent_smul_eq D) h₀
      (mem_span_negGlobalLift hR hfund hIH hxZ hxw) hx₀
    refine ⟨y, ?_, hxy⟩
    clear hxy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨b, rfl⟩ := hy; exact (negGlobalLift_spec hR hfund hIH b).1
    | zero => exact ⟨zero_mem _, zero_mem _, zero_mem _, zero_mem _⟩
    | add y y' _ _ hy hy' => exact ⟨add_mem hy.1 hy'.1, add_mem hy.2.1 hy'.2.1,
        add_mem hy.2.2.1 hy'.2.2.1, add_mem hy.2.2.2 hy'.2.2.2⟩
    | smul m y _ hy => exact ⟨zsmul_mem hy.1 m, zsmul_mem hy.2.1 m, zsmul_mem hy.2.2.1 m,
        zsmul_mem hy.2.2.2 m⟩
  · exact balanced_eq_zero_of_mem_span (laurent_smul_eq D) h₀ h₁
      (mem_span_negGlobalLift hR hfund hIH hx.1 hx.2.1) hxϖ hx.2.2.2

/-- Two elements of `E(ν)` congruent modulo `v⁻¹L(∞)` are equal, under `(G.1)` at `ν`. -/
lemma eq_of_mem_negBalanced {ν : I →₀ ℕ} (h : NegGlobalAt D ν) {x y : Um D 𝕧}
    (hx : x ∈ negBalanced D ν) (hy : y ∈ negBalanced D ν)
    (hxy : x - y ∈ ϖ • latInf (D := D) hvt A) : x = y :=
  sub_eq_zero.1 (h.2 _ ⟨sub_mem hx.1 hy.1, sub_mem hx.2.1 hy.2.1, sub_mem hx.2.2.1 hy.2.2.1,
    sub_mem hx.2.2.2 hy.2.2.2⟩ hxy)

include hfund in
/-- **`(G.3)` for `n = 1`** at `ν`: if `ẽᵢb ≠ 0`, then `G(b) ∈ (fᵢU⁻)^ℤ_ν`. Since
`b = f̃ᵢẽᵢb` ([Jan] Prop. 10.12), `b` has a lift in `(fᵢU⁻)^ℤ_ν` by Cor. 7.4.2, which is `G(b)`
by `(G.1)`. -/
theorem negLift_mem_negFilt {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) (h : NegGlobalAt D ν) (i : I)
    (w : {w : List I // wordWeight w = ν})
    (hw : kE hvt i (fWi (D := D) hvt w.1) ∉ ϖ • latInf (D := D) hvt A) :
    negLift h w ∈ negFilt D i 1 ν := by
  rcases kE_fWi_cases (hR := hR) InfinityLocalRing.injective_algebraMap
      InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
      InfinityLocalRing.exists_pow_mul hfund i w.1 with h0 | ⟨w', hw'⟩
  · exact absurd h0 hw
  have hc := fWi_sub_mem_of_kE (hR := hR) InfinityLocalRing.injective_algebraMap
    InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
    InfinityLocalRing.exists_pow_mul hfund i hw hw'
  have hwt : wordWeight (i :: w') = ν := by
    rw [← w.2]
    exact (wordWeight_eq_of_sub_mem_latInf (hR := hR) InfinityLocalRing.injective_algebraMap
      InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
      InfinityLocalRing.exists_pow_mul hfund hc).symm
  have hx : fWi (D := D) hvt (i :: w') ∈ negFilt D i 1 ν := hwt ▸ fWi_cons_mem_negFilt D i w'
  obtain ⟨y, hy, hy₀, hy₁, hxy⟩ := exists_negFilt_sub_mem hR hfund hIH i le_rfl hx
    (NegativePart.fWord_mem_latticeInf _ _ _)
  have e : negLift h w = y := by
    refine eq_of_mem_negBalanced h (negLift_mem h w)
      ⟨(mem_negFilt_le D hy).1, (mem_negFilt_le D hy).2, hy₀, hy₁⟩ ?_
    have e' : negLift h w - y = (negLift h w - fWi hvt w.1) +
        (fWi hvt w.1 - fWi hvt (i :: w')) + (fWi hvt (i :: w') - y) := by abel
    rw [e']
    exact add_mem (add_mem (negLift_sub_mem h w) hc) hxy
  rw [e]
  exact hy

include hfund in
/-- **[Kas91] Lemma 7.5.2**: under the induction hypothesis and `(G.1)` at `ν`, if
`π̄_λ(b) = 0` then `G(b)u_λ = 0`. Kashiwara's proof: choose `i` with `ẽᵢb ≠ 0`; then
`G(b)u_λ ∈ (fᵢV(λ))^ℤ_{λ-ν} ∩ v⁻¹L(λ) ∩ L(λ)⁻`, which is zero by Prop. 7.4.1. -/
theorem evq_negLift_eq_zero {ν : I →₀ ℕ} (hIH : GlobalBelow hR ν) (h : NegGlobalAt D ν)
    (Λ : Dom R) (w : {w : List I // wordWeight w = ν})
    (hw : fW hvt hR Λ w.1 ∈ ϖ • lat hvt hR A Λ) : evq hvt Λ (negLift h w) = 0 := by
  obtain ⟨w, hwν⟩ := w
  cases w with
  | nil =>
    exact absurd hw (fW_nil_notMem InfinityLocalRing.injective_algebraMap
      InfinityLocalRing.uniformizer_mem_maximalIdeal Λ)
  | cons i w' =>
    have hkE : kE hvt i (fWi (D := D) hvt (i :: w')) ∉ ϖ • latInf (D := D) hvt A := by
      change kE hvt i (kF hvt i (fWi hvt w')) ∉ _
      rw [kE_kF]
      exact fWi_notMem (hR := hR) InfinityLocalRing.injective_algebraMap
        InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
        InfinityLocalRing.exists_pow_mul hfund w'
    have hF := negLift_mem_negFilt hR hfund hIH h i ⟨i :: w', hwν⟩ hkE
    refine hwFilt_eq_zero_of_mem hR hfund hIH Λ i le_rfl (evq_mem_hwFilt Λ hF) ?_
      (evq_negLift_mem hfund h ⟨i :: w', hwν⟩ Λ).2.2.2
    have := add_mem (evq_negLift_sub_mem hfund h ⟨i :: w', hwν⟩ Λ) hw
    rwa [sub_add_cancel] at this

end Step

/-! ### The induction -/

section Induction

include hfund in
/-- **[Kas91] `(G_l)` for every `l`**, in the form used in the induction: at every weight `ν`,
`(G.1)` holds, `G(b)u_λ = 0` whenever `π̄_λ(b) = 0` (Lemma 7.5.2, which with `(G.1)` gives
`(G.2)`), and `G(b) ∈ (fᵢU⁻)^ℤ` whenever `ẽᵢb ≠ 0` (`(G.3)` for `n = 1`). -/
theorem globalAt (ν : I →₀ ℕ) :
    ∃ h : NegGlobalAt D ν,
      (∀ (Λ : Dom R) (w : {w : List I // wordWeight w = ν}),
        fW hvt hR Λ w.1 ∈ ϖ • lat hvt hR A Λ → evq hvt Λ (negLift h w) = 0) ∧
      ∀ (i : I) (w : {w : List I // wordWeight w = ν}),
        kE hvt i (fWi (D := D) hvt w.1) ∉ ϖ • latInf (D := D) hvt A →
          negLift h w ∈ negFilt D i 1 ν := by
  induction ν using WellFoundedLT.induction with
  | _ ν ih =>
    have hIH : GlobalBelow hR ν := fun μ hle hne ↦ ih μ (lt_of_le_of_ne hle hne)
    have h := negGlobalAt_of_globalBelow hR hfund hIH
    exact ⟨h, evq_negLift_eq_zero hR hfund hIH h, negLift_mem_negFilt hR hfund hIH h⟩

include hfund in
/-- The induction hypothesis holds at every weight. -/
theorem globalBelow (ν : I →₀ ℕ) : GlobalBelow hR ν :=
  fun μ _ _ ↦ globalAt hR hfund μ

include hfund in
/-- **[Kas91] `(G.2)` at every weight**: for every dominant `λ` and every `ν`,
`V_ℤ(λ)_{λ-ν} ∩ L(λ) ∩ L(λ)⁻ → L_ℤ(λ)_{λ-ν}/v⁻¹L_ℤ(λ)_{λ-ν}` is an isomorphism. -/
theorem hwGlobalAt (Λ : Dom R) (ν : I →₀ ℕ) : HwGlobalAt hR Λ ν := by
  obtain ⟨h, hvan, -⟩ := globalAt hR hfund ν
  exact hwGlobalAt_of_vanishing hfund h Λ (hvan Λ)

variable (D) in
/-- **[Kas91] `(G.1)` at every weight**: `U⁻_{ℤ,ν} ∩ L(∞) ∩ L(∞)⁻ → L_ℤ(∞)_ν/v⁻¹L_ℤ(∞)_ν` is
an isomorphism, for every Cartan datum with finite index set. -/
theorem negGlobalAt (ν : I →₀ ℕ) : NegGlobalAt D ν := by
  let := Fintype.ofFinite I
  exact (globalAt (R := D.extendedRootDatum) D.isXRegular_extendedRootDatum
    D.exists_fundamental_extendedRootDatum ν).1

end Induction

end LieLean.QuantumGroup
