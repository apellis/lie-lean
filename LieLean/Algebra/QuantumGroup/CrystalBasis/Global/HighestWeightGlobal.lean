/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.NegativeGlobal
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.HighestWeightIntegral

/-!
# The global basis of `V(λ)` at one weight: `(G.2)` from `(G.1)`

Let `λ` be dominant. At the weight `λ - ν` of `V(λ) = L_q(λ)`, let

`E_λ(ν) = V_ℤ(λ) ∩ V(λ)_{λ-ν} ∩ L(λ) ∩ L(λ)⁻`

(`hwBalanced`), where `V_ℤ(λ) = U⁻_ℤ u_λ`, `L(λ)` is the crystal lattice at `v = ∞` and
`L(λ)⁻` its image under the bar involution of `V(λ)` (`latBar`). The statement `(G.2)` at `ν`
([Kas91] §7.2) is that `E_λ(ν) → L_ℤ(λ)_{λ-ν}/v⁻¹L_ℤ(λ)_{λ-ν}` is an isomorphism, where
`L_ℤ(λ) = V_ℤ(λ) ∩ L(λ)`. As for `U⁻` (`NegGlobalAt`) we state it as (`HwGlobalAt`):

* every `x ∈ V_ℤ(λ)_{λ-ν} ∩ L(λ)` is congruent modulo `v⁻¹L(λ)` to an element of `E_λ(ν)`, and
* `E_λ(ν) ∩ v⁻¹L(λ) = 0`.

The elements of `B(λ)_{λ-ν}` are the classes of the vectors `f̃_w u_λ ∉ v⁻¹L(λ)` of weight
`λ - ν` (`hwCrystal`, a quotient of a set of words).

At the end of the induction ([Kas91] §7.5), Kashiwara obtains `(G.2)` at `ν` from `(G.1)` at
`ν` and Lemma 7.5.2 (`G(b)u_λ = 0` when `π̄_λ(b) = 0`), by Lemma 7.1.1 (ii). We prove this step
(`hwGlobalAt_of_vanishing`): the vectors `G_λ(b) = G(b)u_λ` lie in `E_λ(ν)`, have independent
residues on both lattices, and span `V_ℤ(λ)_{λ-ν}` over `𝒜` ([Kas91] (7.3.4),
`mem_span_hwLift`), so `span_of_balanced`-type arguments apply (`exists_int_sub_mem_of_mem_span`,
`balanced_eq_zero_of_mem_span`). We also record [Kas91] Lemma 7.3.2 in the form
`G(b)u_λ ≡ f̃_w u_λ` (`evq_negLift_sub_mem`).

The lattice `L(λ)` is that of the grand loop: `R` is `X`-regular (Lusztig assumes `Y`-regular
root data) with fundamental weights.

## Main definitions

* `latBar`: `L(λ)⁻`.
* `hwBalanced`: `E_λ(ν)`.
* `HwGlobalAt`: the statement `(G.2)` at the weight `ν`.
* `hwCrystal`: `B(λ)_{λ-ν}`; `hwLift`: the vectors `G_λ(b)`.

## Main results

* `evq_negLift_sub_mem`: [Kas91] Lemma 7.3.2 in residue form.
* `mem_span_hwLift`: [Kas91] Lemma 7.3.1, (7.3.4), given the vanishing of Lemma 7.5.2.
* `hwGlobalAt_of_vanishing`: `(G.2)` at `ν` from `(G.1)` at `ν` and Lemma 7.5.2 ([Kas91] §7.5,
  last paragraph).

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, §7.
-/

open Pointwise

noncomputable section

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular)

/-! ### The lattice `L(λ)⁻` -/

section Bar

variable (Λ : Dom R)

lemma hwBar_infinity_smul (b : LocalRing) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwBar hR Λ ((show InfinityLocalRing from b) • m) = b • hwBar hR Λ m := by
  rw [← algebraMap_smul 𝕂 (show InfinityLocalRing from b) m, hwBar_smul,
    ← algebraMap_smul 𝕂 b (hwBar hR Λ m)]
  congr 1
  change RatFunc.bar (RatFunc.bar (algebraMap LocalRing 𝕂 b)) = _
  rw [RatFunc.bar_bar]

lemma hwBar_local_smul (b : LocalRing) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwBar hR Λ (b • m) = (show InfinityLocalRing from b) • hwBar hR Λ m := by
  conv_lhs => rw [← hwBar_hwBar hR Λ m, ← hwBar_infinity_smul]
  exact hwBar_hwBar hR Λ _

/-- `L(λ)⁻`: the image of `L(λ)` under bar, a lattice over the local ring at `v = 0`. -/
def latBar : Submodule LocalRing (IrreducibleModule R 𝕧 Λ.1) where
  carrier := {x | hwBar hR Λ x ∈ lat hvt hR A Λ}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_add] at hx hy ⊢
    exact add_mem hx hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact zero_mem _
  smul_mem' b x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [hwBar_local_smul]
    exact Submodule.smul_mem _ _ hx

lemma mem_latBar_iff (x : IrreducibleModule R 𝕧 Λ.1) :
    x ∈ latBar hR Λ ↔ hwBar hR Λ x ∈ lat hvt hR A Λ := Iff.rfl

lemma mem_localX_smul_latBar_iff (x : IrreducibleModule R 𝕧 Λ.1) :
    x ∈ localX • latBar hR Λ ↔ hwBar hR Λ x ∈ ϖ • lat hvt hR A Λ := by
  rw [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hwBar hR Λ y, hy, (hwBar_local_smul hR Λ localX y).symm⟩
  · rintro ⟨y, hy, hxy⟩
    refine ⟨hwBar hR Λ y, (mem_latBar_iff hR Λ _).2 (by rwa [hwBar_hwBar]), ?_⟩
    rw [← hwBar_hwBar hR Λ x, ← hxy]
    exact (hwBar_infinity_smul hR Λ localX y).symm

/-- `E_λ(ν) = V_ℤ(λ) ∩ V(λ)_{λ-ν} ∩ L(λ) ∩ L(λ)⁻`. -/
def hwBalanced (ν : I →₀ ℕ) : Set (IrreducibleModule R 𝕧 Λ.1) :=
  {x | x ∈ hwIntegral Λ ∧ x ∈ wsp Λ ν ∧ x ∈ lat hvt hR A Λ ∧ x ∈ latBar hR Λ}

/-- [Kas91] `(G.2)` at the weight `ν`: the map `E_λ(ν) → L_ℤ(λ)_{λ-ν}/v⁻¹L_ℤ(λ)_{λ-ν}` is
surjective and injective, where `L_ℤ(λ) = V_ℤ(λ) ∩ L(λ)`. -/
def HwGlobalAt (ν : I →₀ ℕ) : Prop :=
  (∀ x ∈ hwIntegral Λ, x ∈ wsp Λ ν → x ∈ lat hvt hR A Λ →
      ∃ y ∈ hwBalanced hR Λ ν, x - y ∈ ϖ • lat hvt hR A Λ) ∧
    ∀ x ∈ hwBalanced hR Λ ν, x ∈ ϖ • lat hvt hR A Λ → x = 0

end Bar

/-! ### `B(λ)` as classes of words -/

section Crystal

variable (Λ : Dom R) (ν : I →₀ ℕ)

/-- The words `w` of weight `ν` with `f̃_w u_λ ∉ v⁻¹L(λ)`. -/
def hwWord : Type _ :=
  {w : List I // wordWeight w = ν ∧ fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ}

/-- Two words are equivalent when they give the same element of `B(λ)`. -/
def hwCrystalSetoid : Setoid (hwWord hR Λ ν) where
  r w w' := fW hvt hR Λ w.1 - fW hvt hR Λ w'.1 ∈ ϖ • lat hvt hR A Λ
  iseqv := ⟨fun w ↦ by simp, fun h ↦ by rw [← neg_sub]; exact neg_mem h,
    fun h h' ↦ by rw [← sub_add_sub_cancel]; exact add_mem h h'⟩

/-- `B(λ)_{λ-ν}`. -/
abbrev hwCrystal : Type _ := Quotient (hwCrystalSetoid hR Λ ν)

end Crystal

/-! ### Weight projections -/

omit [Finite I] in
/-- `π_λ` commutes with the projections to weight spaces. -/
lemma evq_proj (Λ : Dom R) (ν : I →₀ ℕ) (x : Um D 𝕧) :
    evq hvt Λ (NegativePart.proj D 𝕧 (LusztigF.toZ ν) x) =
      weightSetProj (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) {Λ.1 - R.rootSum ν}
        (evq hvt Λ x) := by
  classical
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction y using FreeAlgebra.induction_wordBasis with
  | zero => simp
  | add a b ha hb => rw [Submodule.Quotient.mk_add, map_add, map_add, ha, hb, map_add, map_add]
  | smul c a ha => rw [Submodule.Quotient.mk_smul, map_smul, map_smul, ha, map_smul, map_smul]
  | word w =>
    have hw : (Submodule.Quotient.mk (FreeAlgebra.wordBasis 𝕂 I w) : Um D 𝕧) ∈
        Uw D 𝕧 (wordWeight w) :=
      ⟨_, FreeAlgebra.wordBasis_mem_wordSpan w, rfl⟩
    rw [proj_of_mem_Uw hw, weightSetProj_of_mem _ _ _ (evq_mem_wsp hR hw Λ)]
    have hiff : (Λ.1 - R.rootSum (wordWeight w) ∈ ({Λ.1 - R.rootSum ν} : Set _)) ↔
        wordWeight w = ν := by
      rw [Set.mem_singleton_iff]
      exact ⟨fun h ↦ LusztigCartanDatum.RootDatum.rootSum_injective hR (sub_right_injective h),
        fun h ↦ by rw [h]⟩
    by_cases h : wordWeight w = ν
    · simp [h]
    · have hz : LusztigF.toZ (wordWeight w) ≠ LusztigF.toZ ν :=
        fun e ↦ h (LusztigF.toZ_injective e)
      simp [hz, hiff, h]

omit [Finite I] [DecidableEq I] in
lemma proj_mem_Uw (ν : I →₀ ℕ) (u : Um D 𝕧) :
    NegativePart.proj D 𝕧 (LusztigF.toZ ν) u ∈ Uw D 𝕧 ν := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  refine ⟨_, ?_, (NegativePart.proj_mk _ _).symm⟩
  simp only [zWeightProj, ite_eq_left (nonneg_toZ ν), ofZ_toZ]
  exact weightProj_mem ν y

/-! ### `(G.2)` from `(G.1)` -/

section Global

variable {hR}
variable (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)

lemma negBalanced_sub {ν : I →₀ ℕ} {x y : Um D 𝕧} (hx : x ∈ negBalanced D ν)
    (hy : y ∈ negBalanced D ν) : x - y ∈ negBalanced D ν :=
  ⟨sub_mem hx.1 hy.1, sub_mem hx.2.1 hy.2.1, sub_mem hx.2.2.1 hy.2.2.1, sub_mem hx.2.2.2 hy.2.2.2⟩

/-- Under `(G.1)` at `ν`, two lifts that are congruent modulo `v⁻¹L(∞)` are equal. -/
lemma negLift_eq_of_sub_mem {ν : I →₀ ℕ} (h : NegGlobalAt D ν)
    {w w' : {w : List I // wordWeight w = ν}}
    (hww : fWi (D := D) hvt w.1 - fWi hvt w'.1 ∈ ϖ • latInf (D := D) hvt A) :
    negLift h w = negLift h w' := by
  refine sub_eq_zero.1 (h.2 _ (negBalanced_sub (negLift_mem h w) (negLift_mem h w')) ?_)
  have e : negLift h w - negLift h w' = (negLift h w - fWi hvt w.1) -
      (negLift h w' - fWi hvt w'.1) + (fWi hvt w.1 - fWi hvt w'.1) := by abel
  rw [e]
  exact add_mem (sub_mem (negLift_sub_mem h w) (negLift_sub_mem h w')) hww

include hfund in
lemma evq_mem_lat' {u : Um D 𝕧} (hu : u ∈ latInf (D := D) hvt A) (Λ : Dom R) :
    evq hvt Λ u ∈ lat hvt hR A Λ :=
  evq_mem_lat_of_mem_latticeInf InfinityLocalRing.injective_algebraMap
    InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
    InfinityLocalRing.exists_pow_mul hfund hu Λ

include hfund in
lemma evq_mem_smul_lat' {u : Um D 𝕧} (hu : u ∈ ϖ • latInf (D := D) hvt A) (Λ : Dom R) :
    evq hvt Λ u ∈ ϖ • lat hvt hR A Λ :=
  evq_mem_smul_lat InfinityLocalRing.injective_algebraMap
    InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
    InfinityLocalRing.exists_pow_mul hfund hu Λ

include hfund in
/-- [Kas91] Lemma 7.3.2, residue form: `G(b)u_λ ≡ f̃_w u_λ` modulo `v⁻¹L(λ)` for `b` the class
of `f̃_w 1`. -/
theorem evq_negLift_sub_mem {ν : I →₀ ℕ} (h : NegGlobalAt D ν)
    (w : {w : List I // wordWeight w = ν}) (Λ : Dom R) :
    evq hvt Λ (negLift h w) - fW hvt hR Λ w.1 ∈ ϖ • lat hvt hR A Λ := by
  have e : evq hvt Λ (negLift h w) - fW hvt hR Λ w.1 = evq hvt Λ (negLift h w - fWi hvt w.1) +
      (evq hvt Λ (fWi hvt w.1) - fW hvt hR Λ w.1) := by rw [map_sub]; abel
  rw [e]
  exact add_mem (evq_mem_smul_lat' hfund (negLift_sub_mem h w) Λ)
    (evq_fWord_sub_fW_mem InfinityLocalRing.injective_algebraMap
      InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
      InfinityLocalRing.exists_pow_mul hfund w.1 Λ)

include hfund in
/-- The vectors `G(b)u_λ` lie in `E_λ(ν)`. -/
theorem evq_negLift_mem {ν : I →₀ ℕ} (h : NegGlobalAt D ν)
    (w : {w : List I // wordWeight w = ν}) (Λ : Dom R) :
    evq hvt Λ (negLift h w) ∈ hwBalanced hR Λ ν := by
  obtain ⟨hZ, hw, h₀, -⟩ := negLift_mem h w
  refine ⟨⟨_, hZ, rfl⟩, evq_mem_wsp hR hw Λ, evq_mem_lat' hfund h₀ Λ, ?_⟩
  rw [mem_latBar_iff, hwBar_evq, negBar_eq_of_mem h (negLift_mem h w)]
  exact evq_mem_lat' hfund h₀ Λ

variable (hR) in
/-- The vector `G_λ(b) = G(b)u_λ` for `b ∈ B(λ)_{λ-ν}`, computed from a word representing `b`. -/
def hwLift {ν : I →₀ ℕ} (h : NegGlobalAt D ν) (Λ : Dom R) (b : hwCrystal hR Λ ν) :
    IrreducibleModule R 𝕧 Λ.1 :=
  evq hvt Λ (negLift h ⟨(Quotient.out b).1, (Quotient.out b).2.1⟩)

include hfund in
lemma hwLift_mem {ν : I →₀ ℕ} (h : NegGlobalAt D ν) (Λ : Dom R) (b : hwCrystal hR Λ ν) :
    hwLift hR h Λ b ∈ hwBalanced hR Λ ν :=
  evq_negLift_mem hfund h _ Λ

include hfund in
lemma hwLift_sub_mem {ν : I →₀ ℕ} (h : NegGlobalAt D ν) (Λ : Dom R) (b : hwCrystal hR Λ ν) :
    hwLift hR h Λ b - fW hvt hR Λ (Quotient.out b).1 ∈ ϖ • lat hvt hR A Λ :=
  evq_negLift_sub_mem hfund h _ Λ

lemma hwBar_hwLift {ν : I →₀ ℕ} (h : NegGlobalAt D ν) (Λ : Dom R) (b : hwCrystal hR Λ ν) :
    hwBar hR Λ (hwLift hR h Λ b) = hwLift hR h Λ b := by
  rw [hwLift, hwBar_evq, negBar_eq_of_mem h (negLift_mem h _)]

include hfund in
/-- The `G_λ(b)` have independent residues in `L(λ)/v⁻¹L(λ)`. -/
theorem residueIndependent_hwLift {ν : I →₀ ℕ} (h : NegGlobalAt D ν) (Λ : Dom R) :
    ResidueIndependent InfinityLocalRing (lat hvt hR A Λ) ϖ (hwLift hR h Λ) := by
  classical
  refine ⟨fun b ↦ (hwLift_mem hfund h Λ b).2.2.1, fun s a hs b hb ↦ ?_⟩
  have hD : ∀ r, PropD hvt hR A ϖ r := fun r ↦
    (allProp InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
      InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul hfund r).2.2.2.1
  have hsum : ∑ c ∈ s, a c • fW hvt hR Λ (Quotient.out c).1 ∈ ϖ • lat hvt hR A Λ := by
    have e : ∑ c ∈ s, a c • fW hvt hR Λ (Quotient.out c).1 = ∑ c ∈ s, a c • hwLift hR h Λ c -
        ∑ c ∈ s, a c • (hwLift hR h Λ c - fW hvt hR Λ (Quotient.out c).1) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ ↦ by rw [smul_sub, sub_sub_cancel]
    rw [e]
    exact sub_mem hs (Submodule.sum_mem _ fun c _ ↦ Submodule.smul_mem _ _
      (hwLift_sub_mem hfund h Λ c))
  have := coeff_mem_of_sum_mem hD Λ s (fun c ↦ (Quotient.out c).1)
    (fun c₁ _ c₂ _ he ↦ Quotient.out_injective (Subtype.ext he))
    (fun c _ ↦ (Quotient.out c).2.2)
    (fun c₁ _ c₂ _ hne hmem ↦ hne (by
      rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂]
      exact Quotient.sound hmem))
    a hsum b hb
  exact Ideal.mem_span_singleton.1 this

include hfund in
/-- The `G_λ(b)` have independent residues in `L(λ)⁻/vL(λ)⁻`. -/
theorem residueIndependent_hwLift_bar {ν : I →₀ ℕ} (h : NegGlobalAt D ν) (Λ : Dom R) :
    ResidueIndependent LocalRing (latBar hR Λ) localX (hwLift hR h Λ) := by
  refine ⟨fun b ↦ (hwLift_mem hfund h Λ b).2.2.2, fun s a hs b hb ↦ ?_⟩
  rw [mem_localX_smul_latBar_iff, map_sum] at hs
  simp_rw [hwBar_local_smul, hwBar_hwLift h Λ] at hs
  exact (residueIndependent_hwLift hfund h Λ).2 s (fun c ↦ show InfinityLocalRing from a c) hs b hb

include hfund in
/-- Under `(G.1)` at `ν`, if `G(b)u_λ = 0` whenever `π̄_λ(b) = 0` ([Kas91] Lemma 7.5.2), each
`G(b)u_λ` is zero or one of the `G_λ(b')`. -/
lemma evq_negLift_mem_span {ν : I →₀ ℕ} (h : NegGlobalAt D ν) (Λ : Dom R)
    (hvan : ∀ w : {w : List I // wordWeight w = ν}, fW hvt hR Λ w.1 ∈ ϖ • lat hvt hR A Λ →
      evq hvt Λ (negLift h w) = 0) (w : {w : List I // wordWeight w = ν}) :
    evq hvt Λ (negLift h w) ∈
      Submodule.span (LaurentPolynomial ℤ) (Set.range (hwLift hR h Λ)) := by
  by_cases hw0 : fW hvt hR Λ w.1 ∈ ϖ • lat hvt hR A Λ
  · rw [hvan w hw0]; exact zero_mem _
  let b : hwCrystal hR Λ ν := ⟦⟨w.1, w.2, hw0⟩⟧
  have hrel : fW hvt hR Λ (Quotient.out b).1 - fW hvt hR Λ w.1 ∈ ϖ • lat hvt hR A Λ :=
    Quotient.mk_out (s := hwCrystalSetoid hR Λ ν) ⟨w.1, w.2, hw0⟩
  have hi := fWi_sub_mem_of_fW_sub_mem InfinityLocalRing.injective_algebraMap
    InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
    InfinityLocalRing.exists_pow_mul hfund _ w.1 (Quotient.out b).1 rfl hw0
    (by rw [← neg_sub]; exact neg_mem hrel)
  have e : evq hvt Λ (negLift h w) = hwLift hR h Λ b := by
    rw [hwLift, negLift_eq_of_sub_mem h (w' := ⟨(Quotient.out b).1, (Quotient.out b).2.1⟩) hi]
  rw [e]
  exact Submodule.subset_span ⟨b, rfl⟩

include hfund in
/-- [Kas91] Lemma 7.3.1, (7.3.4): under `(G.1)` at `ν` and the vanishing of Lemma 7.5.2,
`V_ℤ(λ)_{λ-ν}` is the `𝒜`-span of the `G_λ(b)`, `b ∈ B(λ)_{λ-ν}`. -/
theorem mem_span_hwLift {ν : I →₀ ℕ} (h : NegGlobalAt D ν) (Λ : Dom R)
    (hvan : ∀ w : {w : List I // wordWeight w = ν}, fW hvt hR Λ w.1 ∈ ϖ • lat hvt hR A Λ →
      evq hvt Λ (negLift h w) = 0) {x : IrreducibleModule R 𝕧 Λ.1}
    (hxZ : x ∈ hwIntegral Λ) (hxw : x ∈ wsp Λ ν) :
    x ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range (hwLift hR h Λ)) := by
  classical
  obtain ⟨u, hu, rfl⟩ := hxZ
  have e : evq hvt Λ u = evq hvt Λ (NegativePart.proj D 𝕧 (LusztigF.toZ ν) u) := by
    rw [evq_proj hR, weightSetProj_of_mem _ _ _ hxw]
    simp
  rw [e]
  have key : ∀ z ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range (negLift h)),
      evq hvt Λ z ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range (hwLift hR h Λ)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      exact evq_negLift_mem_span hfund h Λ hvan w
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [laurent_smul_eq, map_smul, ← hw_laurent_smul_eq]
      exact Submodule.smul_mem _ _ hy
  exact key _ (mem_span_negLift h (proj_mem_negIntegral D _ hu) (proj_mem_Uw ν u))

lemma mem_hwBalanced_of_mem_span_int {ν : I →₀ ℕ} {Λ : Dom R} {ι : Type*}
    {g : ι → IrreducibleModule R 𝕧 Λ.1} (hg : ∀ b, g b ∈ hwBalanced hR Λ ν)
    {y : IrreducibleModule R 𝕧 Λ.1} (hy : y ∈ Submodule.span ℤ (Set.range g)) :
    y ∈ hwBalanced hR Λ ν := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨b, rfl⟩ := hy; exact hg b
  | zero => exact ⟨zero_mem _, zero_mem _, zero_mem _, zero_mem _⟩
  | add y z _ _ hy hz =>
    exact ⟨add_mem hy.1 hz.1, add_mem hy.2.1 hz.2.1, add_mem hy.2.2.1 hz.2.2.1,
      add_mem hy.2.2.2 hz.2.2.2⟩
  | smul n y _ hy =>
    exact ⟨zsmul_mem hy.1 n, zsmul_mem hy.2.1 n, zsmul_mem hy.2.2.1 n, zsmul_mem hy.2.2.2 n⟩

include hfund in
/-- **`(G.2)` at `ν`** ([Kas91] §7.5, last paragraph): it follows from `(G.1)` at `ν` and the
vanishing `G(b)u_λ = 0` for `π̄_λ(b) = 0` of [Kas91] Lemma 7.5.2, by Lemma 7.1.1 (ii). -/
theorem hwGlobalAt_of_vanishing {ν : I →₀ ℕ} (h : NegGlobalAt D ν) (Λ : Dom R)
    (hvan : ∀ w : {w : List I // wordWeight w = ν}, fW hvt hR Λ w.1 ∈ ϖ • lat hvt hR A Λ →
      evq hvt Λ (negLift h w) = 0) :
    HwGlobalAt hR Λ ν := by
  refine ⟨fun x hxZ hxw hx₀ ↦ ?_, fun x hx hxϖ ↦ ?_⟩
  · obtain ⟨y, hy, hxy⟩ := exists_int_sub_mem_of_mem_span (hw_laurent_smul_eq Λ)
      (residueIndependent_hwLift hfund h Λ) (mem_span_hwLift hfund h Λ hvan hxZ hxw) hx₀
    exact ⟨y, mem_hwBalanced_of_mem_span_int (hwLift_mem hfund h Λ) hy, hxy⟩
  · exact balanced_eq_zero_of_mem_span (hw_laurent_smul_eq Λ)
      (residueIndependent_hwLift hfund h Λ) (residueIndependent_hwLift_bar hfund h Λ)
      (mem_span_hwLift hfund h Λ hvan hx.1 hx.2.1) hxϖ hx.2.2.2

end Global

end LieLean.QuantumGroup
