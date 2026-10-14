/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.BalancedSpan
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.HighestWeightBar
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.NegativeIntegralGrading

/-!
# The global basis of `U⁻` at one weight: consequences of `(G.1)`

Kashiwara constructs the global basis of `U⁻ = U_q⁻(𝔤)` by induction on the height of the weight
([Kas91] §7.2–7.5). At a weight `ν`, let

`E(ν) = U⁻_ℤ ∩ U⁻_ν ∩ L(∞) ∩ L(∞)⁻`

(`negBalanced`), where `U⁻_ℤ` is the `𝒜`-form, `𝒜 = ℤ[v, v⁻¹]`, `L(∞)` the crystal lattice at
`v = ∞` and `L(∞)⁻` its image under bar. The statement `(G.1)` at `ν` ([Kas91] §7.2) is that
`E(ν) → L_ℤ(∞)_ν / v⁻¹L_ℤ(∞)_ν` is an isomorphism, where `L_ℤ(∞) = U⁻_ℤ ∩ L(∞)`. We state it
as (`NegGlobalAt`):

* every `x ∈ U⁻_{ℤ,ν} ∩ L(∞)` is congruent modulo `v⁻¹L(∞)` to an element of `E(ν)`, and
* `E(ν) ∩ v⁻¹L(∞) = 0`.

Since the classes of the `f̃_w 1 ∈ U⁻_ℤ` of weight `ν` are the elements of `B(∞)_ν`, each of them
has a lift `G(b) ∈ E(ν)` (`negLift`).

We prove the consequences of `(G.1)` at `ν` that Kashiwara uses in the induction step:

* [Kas91] Lemma 7.3.4: every element of `E(ν)` is bar-invariant (`negBar_eq_of_mem`);
* [Kas91] Lemma 7.3.1, (7.3.2): `U⁻_{ℤ,ν}` is the `𝒜`-span of the chosen lifts
  (`mem_span_negLift`). The proof is Kashiwara's: Lemma 7.1.1 (`span_of_balanced`), with the
  integrality of the crystal coordinates of `U⁻_ℤ ∩ L(∞)` ([Kas91] Prop. 6.1.1,
  `exists_integer_crystal_residue_coordinates`).

## Main definitions

* `negBalanced`: `E(ν)`.
* `NegGlobalAt`: the statement `(G.1)` at the weight `ν`.
* `negLift`: the lifts `G(b)`, `b ∈ B(∞)_ν`, indexed by the words of weight `ν`.

## Main results

* `negBar_eq_of_mem`: [Kas91] Lemma 7.3.4.
* `mem_span_negLift`: [Kas91] Lemma 7.3.1, (7.3.2).

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

variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

omit [Finite I] [DecidableEq I] in
/-- Bar preserves the weight spaces of `U⁻`. -/
lemma negBar_mem_Uw {ν : I →₀ ℕ} {x : Um D 𝕧} (hx : x ∈ Uw D 𝕧 ν) : negBar D x ∈ Uw D 𝕧 ν := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨LusztigF.bar y, ?_, rfl⟩
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [bar_monomial]
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [LusztigF.bar_smul]; exact Submodule.smul_mem _ _ ha

omit [Finite I] in
lemma negBar_mem_latInfBar {x : Um D 𝕧} (hx : x ∈ latInf (D := D) hvt A) :
    negBar D x ∈ latInfBar D := by
  rw [mem_latInfBar_iff, negBar_negBar]; exact hx

/-- `E(ν) = U⁻_ℤ ∩ U⁻_ν ∩ L(∞) ∩ L(∞)⁻`. -/
def negBalanced (ν : I →₀ ℕ) : Set (Um D 𝕧) :=
  {x | x ∈ negIntegral D ∧ x ∈ Uw D 𝕧 ν ∧ x ∈ latInf (D := D) hvt A ∧ x ∈ latInfBar D}

/-- [Kas91] `(G.1)` at the weight `ν`: the map `E(ν) → L_ℤ(∞)_ν/v⁻¹L_ℤ(∞)_ν` is surjective and
injective, where `L_ℤ(∞) = U⁻_ℤ ∩ L(∞)`. -/
def NegGlobalAt (ν : I →₀ ℕ) : Prop :=
  (∀ x ∈ negIntegral D, x ∈ Uw D 𝕧 ν → x ∈ latInf (D := D) hvt A →
      ∃ y ∈ negBalanced D ν, x - y ∈ ϖ • latInf (D := D) hvt A) ∧
    ∀ x ∈ negBalanced D ν, x ∈ ϖ • latInf (D := D) hvt A → x = 0

variable {D}

/-- [Kas91] Lemma 7.3.4: under `(G.1)` at `ν`, every element of `E(ν)` is bar-invariant. The
proof is Kashiwara's: `(x - x̄)/(v - v⁻¹)` lies in `E(ν) ∩ v⁻¹L(∞)`. -/
theorem negBar_eq_of_mem {ν : I →₀ ℕ} (h : NegGlobalAt D ν) {x : Um D 𝕧}
    (hx : x ∈ negBalanced D ν) : negBar D x = x := by
  obtain ⟨hxZ, hxw, hx₀, hx₁⟩ := hx
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
  have hy0 : y = 0 := by
    refine h.2 y ⟨hyZ, ?_, ?_, ?_⟩ hyϖ
    · rw [hy']
      exact Submodule.smul_mem _ _ (sub_mem hxw (negBar_mem_Uw D hxw))
    · exact Submodule.smul_le_self_of_tower ϖ _ hyϖ
    · obtain ⟨u, hu⟩ := exists_inv_X_sub_eq_localX_mul
      rw [hy', ← hu, algebraMap_smul]
      exact Submodule.smul_mem _ _ (sub_mem hx₁ hb₁)
  rw [hy0, smul_zero, sub_eq_zero] at hxy
  exact hxy.symm

lemma exists_negLift {ν : I →₀ ℕ} (h : NegGlobalAt D ν) {w : List I} (hw : wordWeight w = ν) :
    ∃ x ∈ negBalanced D ν, x - fWi (D := D) hvt w ∈ ϖ • latInf (D := D) hvt A := by
  obtain ⟨y, hy, hxy⟩ := h.1 _ (fWi_mem_negIntegral D w) (hw ▸ fWi_mem_Uw w)
    (NegativePart.fWord_mem_latticeInf _ _ w)
  refine ⟨y, hy, ?_⟩
  rw [← neg_sub]; exact neg_mem hxy

/-- The lifts `G(b)` of [Kas91] `(G.1)`, indexed by the words of weight `ν`. -/
def negLift {ν : I →₀ ℕ} (h : NegGlobalAt D ν) (w : {w : List I // wordWeight w = ν}) :
    Um D 𝕧 :=
  (exists_negLift h w.2).choose

lemma negLift_mem {ν : I →₀ ℕ} (h : NegGlobalAt D ν) (w : {w : List I // wordWeight w = ν}) :
    negLift h w ∈ negBalanced D ν :=
  (exists_negLift h w.2).choose_spec.1

lemma negLift_sub_mem {ν : I →₀ ℕ} (h : NegGlobalAt D ν)
    (w : {w : List I // wordWeight w = ν}) :
    negLift h w - fWi (D := D) hvt w.1 ∈ ϖ • latInf (D := D) hvt A :=
  (exists_negLift h w.2).choose_spec.2

variable (D) in
/-- `U⁻_{ℤ,ν}` as an `𝒜`-submodule. -/
def negIntegralWeight (ν : I →₀ ℕ) : Submodule (LaurentPolynomial ℤ) (Um D 𝕧) where
  carrier := {x | x ∈ negIntegral D ∧ x ∈ Uw D 𝕧 ν}
  add_mem' hx hy := ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
  zero_mem' := ⟨zero_mem _, zero_mem _⟩
  smul_mem' c x hx := ⟨Submodule.smul_mem _ c hx.1, by
    rw [laurent_smul_eq]; exact Submodule.smul_mem _ _ hx.2⟩

/-- Every element of `U⁻_ν` lies in `v^N L(∞)` for some `N`. -/
lemma exists_inv_pow_smul_mem_latInf {ν : I →₀ ℕ} {x : Um D 𝕧} (hx : x ∈ Uw D 𝕧 ν) :
    ∃ N : ℕ, ((𝕧⁻¹) ^ N : 𝕂) • x ∈ latInf (D := D) hvt A := by
  let := Fintype.ofFinite I
  obtain ⟨n, hn⟩ := exists_pow_smul_mem_latInf (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum hx
  refine ⟨n, ?_⟩
  rwa [← algebraMap_smul 𝕂, map_pow, InfinityLocalRing.algebraMap_uniformizer] at hn

/-- [Kas91] Lemma 7.3.1, (7.3.2): under `(G.1)` at `ν`, `U⁻_{ℤ,ν}` is the `𝒜`-span of the lifts
`G(b)`. -/
theorem mem_span_negLift {ν : I →₀ ℕ} (h : NegGlobalAt D ν) {x : Um D 𝕧}
    (hxZ : x ∈ negIntegral D) (hxw : x ∈ Uw D 𝕧 ν) :
    x ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range (negLift h)) := by
  refine span_of_balanced (L₀ := latInf (D := D) hvt A) (L₁ := latInfBar D)
    (M := negIntegralWeight D ν) (laurent_smul_eq D) (fun w ↦ ⟨(negLift_mem h w).1,
      (negLift_mem h w).2.1⟩) (fun w ↦ (negLift_mem h w).2.2.2) ?_ ?_ ?_ ?_ ⟨hxZ, hxw⟩
  · rintro y ⟨hyZ, hyw⟩ hy₀
    obtain ⟨a, ha⟩ := exists_integer_crystal_residue_coordinates D hyZ hy₀
    have hp := proj_mem_smul_latInf (D := D) (LusztigF.toZ ν) ha
    rw [map_sub, proj_of_mem_Uw hyw, Finsupp.sum, map_sum] at hp
    simp only [↓reduceIte] at hp
    classical
    set S := a.support.filter fun w ↦ wordWeight w = ν
    refine ⟨∑ w ∈ S.attach, (a w.1 : ℤ) • negLift h ⟨w.1, (Finset.mem_filter.1 w.2).2⟩,
      Submodule.sum_mem _ fun w _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩), ?_⟩
    have hsum : ∑ w ∈ a.support, NegativePart.proj D 𝕧 (LusztigF.toZ ν)
        ((a w : 𝕂) • fWi (D := D) hvt w) = ∑ w ∈ S.attach, (a w.1 : 𝕂) • fWi (D := D) hvt w.1 := by
      rw [Finset.sum_attach S (fun w ↦ (a w : 𝕂) • fWi (D := D) hvt w), Finset.sum_filter]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      rw [map_smul, proj_of_mem_Uw (fWi_mem_Uw w)]
      by_cases hw : wordWeight w = ν
      · simp [hw]
      · have hz : LusztigF.toZ (wordWeight w) ≠ LusztigF.toZ ν :=
          fun e ↦ hw (LusztigF.toZ_injective e)
        simp [hw, hz]
    rw [hsum] at hp
    have e : y - ∑ w ∈ S.attach, (a w.1 : ℤ) • negLift h ⟨w.1, (Finset.mem_filter.1 w.2).2⟩ =
        (y - ∑ w ∈ S.attach, (a w.1 : 𝕂) • fWi (D := D) hvt w.1) -
          ∑ w ∈ S.attach, (a w.1 : 𝕂) • (negLift h ⟨w.1, (Finset.mem_filter.1 w.2).2⟩ -
            fWi (D := D) hvt w.1) := by
      simp only [smul_sub, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul]
      abel
    rw [e]
    refine sub_mem hp (Submodule.sum_mem _ fun w _ ↦ ?_)
    rw [Int.cast_smul_eq_zsmul]
    exact zsmul_mem (negLift_sub_mem h ⟨w.1, (Finset.mem_filter.1 w.2).2⟩) _
  · rintro y ⟨hyZ, hyw⟩ hyϖ hy₁
    exact h.2 y ⟨hyZ, hyw, Submodule.smul_le_self_of_tower ϖ _ hyϖ, hy₁⟩ hyϖ
  · rintro y ⟨-, hyw⟩
    exact exists_inv_pow_smul_mem_latInf hyw
  · rintro y ⟨-, hyw⟩
    obtain ⟨N, hN⟩ := exists_inv_pow_smul_mem_latInf (negBar_mem_Uw D hyw)
    refine ⟨N, (mem_latInfBar_iff D _).2 ?_⟩
    rwa [negBar_smul, map_pow, RatFunc.bar_X]

end LieLean.QuantumGroup
