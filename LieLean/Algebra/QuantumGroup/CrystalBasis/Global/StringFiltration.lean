/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.HighestWeightGlobal

/-!
# The string filtrations `(fᵢⁿU⁻)^ℤ` and `(fᵢⁿV(λ))^ℤ`

Kashiwara's proof of the global basis ([Kas91] §7.4) runs through the `𝒜`-submodules

`(fᵢⁿU⁻)^ℤ_ν = Σ_{k ≥ n} fᵢ^{(k)} U⁻_{ℤ,ν-kαᵢ}`,
`(fᵢⁿV(λ))^ℤ_{λ-ν} = Σ_{k ≥ n} fᵢ^{(k)} V_ℤ(λ)_{λ-ν+kαᵢ}`

(`negFilt`, `hwFilt`; [Kas91] §7.4, before Prop. 7.4.1). We prove the facts about them used in
the proof of Prop. 7.4.1:

* the congruence (6.1.2): for `x ∈ U⁻_ℤ`, `fᵢ^{(n)} x ≡ fᵢ^{(n)} Pᵢ x` modulo `(fᵢ^{n+1}U⁻)^ℤ`,
  where `Pᵢ` is the projection onto `ker e'ᵢ` along `fᵢU⁻` (`df_sub_df_comp_mem_negFilt`);
* `fᵢ^{(n)} Pᵢ x ≡ f̃ᵢⁿ x` modulo `v⁻¹L(∞)` when `x ∈ L(∞)` and `ẽᵢ x ∈ v⁻¹L(∞)`
  (`df_comp_sub_kF_pow_mem`);
* the reduction of the proof of Prop. 7.4.1 to `n + ⟨hᵢ, λ - ν⟩ ≥ 0`: if `n + ⟨hᵢ, λ - ν⟩ < 0`,
  then `(fᵢⁿV(λ))^ℤ_{λ-ν} = (fᵢ^{n+1}V(λ))^ℤ_{λ-ν}` (`hwFilt_le_succ`). Kashiwara cites
  "Proposition 7.1.3" for this step; the statement needed is Prop. 6.1.3
  (`mem_hwIntegral_wt_iff`).

`(fᵢⁿV(λ))^ℤ_{λ-ν}` is defined as the image of `(fᵢⁿU⁻)^ℤ_ν` under `y ↦ y u_λ`, which is
Kashiwara's definition since `V_ℤ(λ) = U⁻_ℤ u_λ` is graded (`evq_proj`, `proj_mem_negIntegral`).

## Main definitions

* `negFilt D i n ν`: `(fᵢⁿU⁻)^ℤ_ν`.
* `hwFilt Λ i n ν`: `(fᵢⁿV(λ))^ℤ_{λ-ν}`.

## Main results

* `df_sub_df_comp_mem_negFilt`: [Kas91] (6.1.2).
* `df_comp_sub_kF_pow_mem`: the congruence `fᵢ^{(n)} Pᵢ G ≡ f̃ᵢⁿ G` of the proof of Prop. 7.4.1.
* `hwFilt_le_succ`: the reduction step in the proof of Prop. 7.4.1.

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, §6.1, §7.4.
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

/-! ### Divided powers in a boson module -/

/-- `f^{(a)} f^{(b)} = [a+b, a] f^{(a+b)}`. -/
lemma BosonModule.df_df {k M : Type*} [Field k] [AddCommGroup M] [Module k M] {q : k}
    (V : BosonModule q M) (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (a b : ℕ) (m : M) :
    V.df a (V.df b m) = qBinomial q (a + b) a • V.df (a + b) m := by
  have ha := BosonModule.qFactorial_ne_zero' hq0 hq a
  have hb := BosonModule.qFactorial_ne_zero' hq0 hq b
  have hab := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (Nat.le_add_right a b)
  rw [Nat.add_sub_cancel_left] at hab
  have hbin : qBinomial q (a + b) a ≠ 0 := by
    intro h
    rw [h, zero_mul, zero_mul] at hab
    exact BosonModule.qFactorial_ne_zero' hq0 hq (a + b) hab.symm
  rw [BosonModule.df_apply, BosonModule.df_apply, BosonModule.df_apply, map_smul, smul_smul,
    smul_smul, ← Module.End.mul_apply, ← pow_add, ← hab]
  congr 1
  field_simp

/-! ### `(fᵢⁿU⁻)^ℤ` -/

section Negative

variable (D)

local notation "bosv" => bos (D := D) (pow_ne_one_of_transcendental' hvt)

omit [Finite I] in
/-- `fᵢ^{(k)} U⁻_μ ⊆ U⁻_{μ + kαᵢ}`. -/
lemma df_mem_Uw (i : I) (k : ℕ) {μ : I →₀ ℕ} {y : Um D 𝕧} (hy : y ∈ Uw D 𝕧 μ) :
    (bosv i).df k y ∈ Uw D 𝕧 (μ + Finsupp.single i k) := by
  obtain ⟨Y, hY, rfl⟩ := hy
  have hpow : ((NegativePart.f D 𝕧 i) ^ k) (Submodule.Quotient.mk Y : Um D 𝕧) =
      Submodule.Quotient.mk (θ 𝕂 i ^ k * Y) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, NegativePart.f_mk, pow_succ', mul_assoc]
  rw [BosonModule.df_apply]
  refine (Uw D 𝕧 _).smul_mem _ ?_
  change ((NegativePart.f D 𝕧 i) ^ k) (Submodule.Quotient.mk Y : Um D 𝕧) ∈ _
  rw [hpow, add_comm]
  refine ⟨_, mul_mem_weightSpace ?_ hY, rfl⟩
  simpa using pow_mem_weightSpace (θ_mem_weightSpace (k := 𝕂) i) k

lemma df_mem_negIntegral (i : I) (k : ℕ) {y : Um D 𝕧} (hy : y ∈ negIntegral D) :
    (bosv i).df k y ∈ negIntegral D :=
  negative_df_mem_integral D i k hy

/-- `(fᵢⁿU⁻)^ℤ_ν = Σ_{n ≤ k ≤ νᵢ} fᵢ^{(k)} U⁻_{ℤ,ν-kαᵢ}` ([Kas91] §7.4). -/
def negFilt (i : I) (n : ℕ) (ν : I →₀ ℕ) : Submodule (LaurentPolynomial ℤ) (Um D 𝕧) :=
  Submodule.span (LaurentPolynomial ℤ)
    {x | ∃ (k : ℕ) (y : Um D 𝕧), n ≤ k ∧ k ≤ ν i ∧ y ∈ negIntegral D ∧
      y ∈ Uw D 𝕧 (ν - Finsupp.single i k) ∧ x = (bosv i).df k y}

lemma df_mem_negFilt (i : I) {n k : ℕ} {ν : I →₀ ℕ} (hnk : n ≤ k) (hk : k ≤ ν i)
    {y : Um D 𝕧} (hy : y ∈ negIntegral D) (hyw : y ∈ Uw D 𝕧 (ν - Finsupp.single i k)) :
    (bosv i).df k y ∈ negFilt D i n ν :=
  Submodule.subset_span ⟨k, y, hnk, hk, hy, hyw, rfl⟩

omit [Finite I] [DecidableEq I] in
lemma sub_single_add_single {ν : I →₀ ℕ} {i : I} {k : ℕ} (hk : k ≤ ν i) :
    ν - Finsupp.single i k + Finsupp.single i k = ν :=
  tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hk)

lemma negFilt_antitone (i : I) {n n' : ℕ} (h : n ≤ n') (ν : I →₀ ℕ) :
    negFilt D i n' ν ≤ negFilt D i n ν :=
  Submodule.span_mono fun _ ⟨k, y, hk, hkν, hy, hyw, hx⟩ ↦ ⟨k, y, h.trans hk, hkν, hy, hyw, hx⟩

/-- `(fᵢⁿU⁻)^ℤ_ν ⊆ U⁻_{ℤ,ν}`. -/
lemma mem_negFilt_le {i : I} {n : ℕ} {ν : I →₀ ℕ} {x : Um D 𝕧} (hx : x ∈ negFilt D i n ν) :
    x ∈ negIntegral D ∧ x ∈ Uw D 𝕧 ν := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, y, -, hk, hy, hyw, rfl⟩ := hx
    refine ⟨df_mem_negIntegral D i k hy, ?_⟩
    have := df_mem_Uw D i k hyw
    rwa [sub_single_add_single hk] at this
  | zero => exact ⟨zero_mem _, zero_mem _⟩
  | add x y _ _ hx hy => exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
  | smul c x _ hx =>
    refine ⟨Submodule.smul_mem _ c hx.1, ?_⟩
    rw [laurent_smul_eq]
    exact (Uw D 𝕧 ν).smul_mem _ hx.2

omit [Finite I] in
/-- The string components `xₖ` of `x ∈ U⁻_ν` vanish for `k > νᵢ`. -/
lemma comp_eq_zero_of_lt (i : I) {μ : I →₀ ℕ} {x : Um D 𝕧} (hx : x ∈ Uw D 𝕧 μ) {k : ℕ}
    (hk : μ i < k) : comp (D := D) hvt i k x = 0 := by
  have hkE : ∀ (m : ℕ) (y : Um D 𝕧), comp (D := D) hvt i m y = comp hvt i 0 ((kE hvt i ^ m) y) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro y
      rw [← comp_kE, ih, pow_succ, Module.End.mul_apply]
  rw [hkE, show k = (k - (μ i + 1)) + (μ i + 1) by omega, pow_add, Module.End.mul_apply,
    kE_pow_eq_zero i hx, map_zero, map_zero]

/-- **[Kas91] (6.1.2)**: for `x ∈ U⁻_{ℤ,ν-nαᵢ}`, `fᵢ^{(n)} x ≡ fᵢ^{(n)} x₀` modulo
`(fᵢ^{n+1}U⁻)^ℤ_ν`, where `x₀` is the `0`-th string component of `x` (its projection onto
`ker e'ᵢ`). -/
theorem df_sub_df_comp_mem_negFilt (i : I) {n : ℕ} {ν : I →₀ ℕ} (hn : n ≤ ν i) {x : Um D 𝕧}
    (hx : x ∈ negIntegral D) (hxw : x ∈ Uw D 𝕧 (ν - Finsupp.single i n)) :
    (bosv i).df n x - (bosv i).df n (comp hvt i 0 x) ∈ negFilt D i (n + 1) ν := by
  obtain ⟨N, hN, hsum⟩ := exists_sum_comp (D := D) i x
  have hsum' : x = ∑ k ∈ Finset.range (N + 1), (bosv i).df k (comp hvt i k x) := by
    rw [Finset.sum_range_succ, hN N le_rfl, map_zero, add_zero]
    exact hsum
  have hd : (bosv i).df n x - (bosv i).df n (comp hvt i 0 x) =
      ∑ k ∈ Finset.range N, (bosv i).df n ((bosv i).df (k + 1) (comp hvt i (k + 1) x)) := by
    rw [sub_eq_iff_eq_add]
    conv_lhs => rw [hsum']
    rw [map_sum, Finset.sum_range_succ', BosonModule.df_zero]
  rw [hd]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  by_cases hk : k + 1 ≤ (ν - Finsupp.single i n) i
  · have hkn : n + (k + 1) ≤ ν i := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same] at hk
      omega
    have hc : comp hvt i (k + 1) x ∈ negIntegral D :=
      negative_component_mem_integral D i hx (k + 1)
    have hcw : comp hvt i (k + 1) x ∈
        Uw D 𝕧 (ν - Finsupp.single i n - Finsupp.single i (k + 1)) :=
      @component_mem_Uw _ _ _ _ D _ _ _ transcendental_ratFunc_X i _ x hxw (k + 1)
    have hw : ν - Finsupp.single i n - Finsupp.single i (k + 1) =
        ν - Finsupp.single i (n + (k + 1)) := by
      ext l
      by_cases hl : l = i
      · subst hl; simp; omega
      · simp [Ne.symm hl]
    rw [hw] at hcw
    rw [BosonModule.df_df _ (NegativePart.pow_d_ne_zero (NeZero.ne 𝕧) i)
      (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i), qBinomial_inv]
    obtain ⟨a, ha⟩ := isLaurent_qBinomial (D.d i) (n + (k + 1)) n
    rw [← ha, ← laurent_smul_eq]
    exact Submodule.smul_mem _ _ (df_mem_negFilt D i (by omega) hkn hc hcw)
  · rw [comp_eq_zero_of_lt D i hxw (by omega), map_zero, map_zero]
    exact zero_mem _

omit [Finite I] in
/-- `P_γ fᵢ^{(m)} = fᵢ^{(m)} P_{γ - mαᵢ}` for the weight projections of `U⁻`. -/
lemma proj_df (i : I) (m : ℕ) (γ : I →₀ ℤ) (z : Um D 𝕧) :
    NegativePart.proj D 𝕧 γ ((bosv i).df m z) =
      (bosv i).df m (NegativePart.proj D 𝕧 (γ - Finsupp.single i (m : ℤ)) z) := by
  have hpow : ∀ (m : ℕ) (γ : I →₀ ℤ) (z : Um D 𝕧), NegativePart.proj D 𝕧 γ
      (((NegativePart.f D 𝕧 i) ^ m) z) =
        ((NegativePart.f D 𝕧 i) ^ m) (NegativePart.proj D 𝕧 (γ - Finsupp.single i (m : ℤ)) z) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro γ z
      rw [pow_succ', Module.End.mul_apply, NegativePart.proj_f, ih, Module.End.mul_apply,
        sub_sub, ← Finsupp.single_add]
      push_cast
      rw [add_comm (1 : ℤ)]
  rw [BosonModule.df_apply, BosonModule.df_apply, map_smul, NegativePart.boson_f, hpow]

/-- The projection to `U⁻_ν` of `fᵢ^{(m)} z`, `m ≥ n`, `z ∈ U⁻_ℤ`, lies in `(fᵢⁿU⁻)^ℤ_ν`. -/
lemma proj_df_mem_negFilt (i : I) {n m : ℕ} (hnm : n ≤ m) (ν : I →₀ ℕ) {z : Um D 𝕧}
    (hz : z ∈ negIntegral D) :
    NegativePart.proj D 𝕧 (LusztigF.toZ ν) ((bosv i).df m z) ∈ negFilt D i n ν := by
  rw [proj_df]
  by_cases hm : m ≤ ν i
  · have e : LusztigF.toZ ν - Finsupp.single i (m : ℤ) = LusztigF.toZ (ν - Finsupp.single i m) := by
      ext l
      by_cases hl : l = i
      · subst hl; simp; omega
      · simp [Ne.symm hl]
    rw [e]
    exact df_mem_negFilt D i hnm hm (proj_mem_negIntegral D _ hz) (proj_mem_Uw _ _)
  · have h0 : NegativePart.proj D 𝕧 (LusztigF.toZ ν - Finsupp.single i (m : ℤ)) z = 0 := by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      have hn : ¬ (0 ≤ LusztigF.toZ ν - Finsupp.single i (m : ℤ)) := by
        intro h
        have := h i
        simp at this
        omega
      rw [NegativePart.proj_mk]
      simp [zWeightProj, hn]
    rw [h0, map_zero]
    exact zero_mem _

omit [Finite I] in
/-- `fᵢ^{(n)} x₀ ≡ f̃ᵢⁿ x` modulo `v⁻¹L(∞)` when `ẽᵢ x ∈ v⁻¹L(∞)`, where `x₀` is the `0`-th
`i`-string component of `x` (the congruence `f̃ᵢⁿ b ≡ fᵢ^{(n)} Pᵢ G(b)` in the proof of [Kas91]
Prop. 7.4.1). -/
theorem df_comp_sub_kF_pow_mem (i : I) (n : ℕ) {x : Um D 𝕧}
    (hx : kE hvt i x ∈ ϖ • latInf (D := D) hvt A) :
    (bosv i).df n (comp hvt i 0 x) - (kF hvt i ^ n) x ∈ ϖ • latInf (D := D) hvt A := by
  have hq0 := NegativePart.pow_d_ne_zero (D := D) (NeZero.ne 𝕧) i
  have hq := NegativePart.pow_d_ne_one (D := D) (pow_ne_one_of_transcendental' hvt) i
  have h := BosonModule.fTilde_eTilde_add_component (V := bosv i) hq0 hq x
  have hpow : ∀ (m : ℕ) {u : Um D 𝕧}, u ∈ ϖ • latInf (D := D) hvt A →
      (kF hvt i ^ m) u ∈ ϖ • latInf (D := D) hvt A := by
    intro m
    induction m with
    | zero => intro u hu; simpa using hu
    | succ m ih =>
      intro u hu
      rw [pow_succ', Module.End.mul_apply]
      exact kF_mem_smul_latInf i (ih hu)
  have key : (kF hvt i ^ n) x =
      (kF hvt i ^ n) (kF hvt i (kE hvt i x)) + (bosv i).df n (comp hvt i 0 x) := by
    conv_lhs => rw [← h]
    rw [map_add, ← BosonModule.fTilde_pow_apply (V := bosv i) hq0 hq (e_comp i 0 x)]
    rfl
  have e : (bosv i).df n (comp hvt i 0 x) - (kF hvt i ^ n) x =
      -((kF hvt i ^ n) (kF hvt i (kE hvt i x))) := by
    rw [key]; abel
  rw [e]
  exact neg_mem (hpow n (kF_mem_smul_latInf i hx))

end Negative

/-! ### `(fᵢⁿV(λ))^ℤ` -/

section HighestWeight

variable {R : D.RootDatum Y} (hR : R.IsXRegular) (Λ : Dom R)

local notation "bosv" => bos (D := D) (pow_ne_one_of_transcendental' hvt)

/-- `(fᵢⁿV(λ))^ℤ_{λ-ν} = (fᵢⁿU⁻)^ℤ_ν u_λ` ([Kas91] §7.4). -/
def hwFilt (i : I) (n : ℕ) (ν : I →₀ ℕ) :
    Submodule (LaurentPolynomial ℤ) (IrreducibleModule R 𝕧 Λ.1) where
  carrier := evq hvt Λ '' (negFilt D i n ν : Set (Um D 𝕧))
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, add_mem hx hy, map_add _ _ _⟩
  zero_mem' := ⟨0, zero_mem _, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    refine ⟨c • x, Submodule.smul_mem _ c hx, ?_⟩
    rw [laurent_smul_eq, map_smul, hw_laurent_smul_eq]

lemma mem_hwFilt (i : I) (n : ℕ) (ν : I →₀ ℕ) (m : IrreducibleModule R 𝕧 Λ.1) :
    m ∈ hwFilt Λ i n ν ↔ ∃ x ∈ negFilt D i n ν, evq hvt Λ x = m := Iff.rfl

lemma evq_mem_hwFilt {i : I} {n : ℕ} {ν : I →₀ ℕ} {x : Um D 𝕧} (hx : x ∈ negFilt D i n ν) :
    evq hvt Λ x ∈ hwFilt Λ i n ν :=
  ⟨x, hx, rfl⟩

lemma hwFilt_antitone (i : I) {n n' : ℕ} (h : n ≤ n') (ν : I →₀ ℕ) :
    hwFilt Λ i n' ν ≤ hwFilt Λ i n ν := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, negFilt_antitone D i h ν hx, rfl⟩

include hR in
/-- `(fᵢⁿV(λ))^ℤ_{λ-ν} ⊆ V_ℤ(λ)_{λ-ν}`. -/
lemma mem_hwFilt_le {i : I} {n : ℕ} {ν : I →₀ ℕ} {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ hwFilt Λ i n ν) : m ∈ hwIntegral Λ ∧ m ∈ wsp Λ ν := by
  obtain ⟨x, hx, rfl⟩ := hm
  obtain ⟨hxZ, hxw⟩ := mem_negFilt_le D hx
  exact ⟨⟨x, hxZ, rfl⟩, evq_mem_wsp hR hxw Λ⟩

include hR in
/-- **The reduction step in the proof of [Kas91] Prop. 7.4.1**: if `n + ⟨hᵢ, λ - ν⟩ < 0`, then
`(fᵢⁿV(λ))^ℤ_{λ-ν} = (fᵢ^{n+1}V(λ))^ℤ_{λ-ν}`. Kashiwara deduces it from "Proposition 7.1.3";
the statement used is Prop. 6.1.3 (`mem_hwIntegral_wt_iff`). -/
theorem hwFilt_le_succ (i : I) {n : ℕ} {ν : I →₀ ℕ}
    (hneg : (Λ.1 - R.rootSum ν) (R.coroot i) + n < 0) :
    hwFilt Λ i n ν ≤ hwFilt Λ i (n + 1) ν := by
  set P := weightSetProj (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ)
    {Λ.1 - R.rootSum ν}
  -- the projection of `fᵢ^{(m)} y`, `m ≥ n + 1`, `y ∈ V_ℤ(λ)`, lies in `(fᵢ^{n+1}V)^ℤ`
  have hgen : ∀ (m : ℕ), n + 1 ≤ m → ∀ y ∈ hwIntegral Λ,
      P ((nodeSl2 R 𝕧 _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF m y) ∈
        hwFilt Λ i (n + 1) ν := by
    rintro m hm _ ⟨z, hz, rfl⟩
    rw [← evq_df (hR := hR), ← evq_proj hR]
    exact evq_mem_hwFilt Λ (proj_df_mem_negFilt D i hm ν hz)
  have hspan : ∀ u ∈ Submodule.span (LaurentPolynomial ℤ)
      {x | ∃ (j : ℕ) (y : IrreducibleModule R 𝕧 Λ.1), y ∈ hwIntegral Λ ∧
        y ∈ (nodeSl2 R 𝕧 _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).wt
          ((((-(Λ.1 - R.rootSum ν) (R.coroot i)).toNat - 1) + 1 + 2 * j : ℕ) : ℤ) ∧
        x = (nodeSl2 R 𝕧 _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF
          (((-(Λ.1 - R.rootSum ν) (R.coroot i)).toNat - 1) + 1 + j) y},
      P u ∈ hwFilt Λ i (n + 1) ν := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, y, hy, -, rfl⟩ := hx
      exact hgen _ (by omega) y hy
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [hw_laurent_smul_eq, map_smul, ← hw_laurent_smul_eq]
      exact Submodule.smul_mem _ c hx
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, y, hnk, hk, hy, hyw, rfl⟩ := hx
    rcases Nat.lt_or_ge n k with hlt | hle
    · exact evq_mem_hwFilt Λ (df_mem_negFilt D i hlt hk hy hyw)
    have hkn : k = n := le_antisymm hle hnk
    subst hkn
    set u := evq hvt Λ ((bosv i).df k y)
    have huw : u ∈ wsp Λ ν := by
      have := df_mem_Uw D i k hyw
      rw [sub_single_add_single hk] at this
      exact evq_mem_wsp hR this Λ
    have huZ : u ∈ hwIntegral Λ := ⟨_, df_mem_negIntegral D i k hy, rfl⟩
    have hwt : u ∈ (nodeSl2 R 𝕧 _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).wt
        (-((((-(Λ.1 - R.rootSum ν) (R.coroot i)).toNat - 1) + 1 : ℕ) : ℤ)) := by
      rw [nodeSl2_wt]
      have e : (-((((-(Λ.1 - R.rootSum ν) (R.coroot i)).toNat - 1) + 1 : ℕ) : ℤ)) =
          (Λ.1 - R.rootSum ν) (R.coroot i) := by omega
      rw [e]
      exact mem_nodeWt_of_mem huw
    have hu := (mem_hwIntegral_wt_iff hR Λ i _ u).1 ⟨huZ, hwt⟩
    have hPu : P u = u := by
      rw [weightSetProj_of_mem _ _ _ huw]
      simp
    rw [← hPu]
    exact hspan u hu
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [laurent_smul_eq, map_smul, ← hw_laurent_smul_eq]
    exact Submodule.smul_mem _ c hx

end HighestWeight

end LieLean.QuantumGroup
