/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.SignedCanonical

/-!
# The subsets `𝐁_{i;n}` of the signed basis

This file proves [Lus] 14.3.1 and Thm. 14.3.2 (a) for the signed basis
`𝐁 = {±G(b)}` of `U⁻ ≅ f` (`Global/SignedCanonical.lean`), together with the general case of
Kashiwara's `(G.3)`.

## Main definitions

* `NegDepthGe D i n b`: `εᵢ(b) ≥ n` for `b ∈ B(∞)_ν`, i.e. `b` is the class of a word `iⁿu`.
* `signedBasisGe D i n`, `signedBasisAt D i n`: Lusztig's `𝐁_{i;≥n} = 𝐁 ∩ θᵢⁿf` and
  `𝐁_{i;n} = 𝐁_{i;≥n} - 𝐁_{i;≥n+1}` ([Lus] 14.3.1).

## Main results

* `negGlobal_mem_negFilt`: `(G.3)`, if `εᵢ(b) ≥ n` then `G(b) ∈ (fᵢⁿU⁻)^ℤ` ([Kas91] Thm. 7).
* `mem_signedBasisGe_iff`, `mem_signedBasisAt_iff`: `𝐁_{i;≥n}` (resp. `𝐁_{i;n}`) consists of
  the `±G(b)` with `εᵢ(b) ≥ n` (resp. `εᵢ(b) = n`).
* `negFilt_eq_span`, `mem_range_iff_mem_span`: [Lus] Thm. 14.3.2 (a), weight by weight, over
  `𝒜` and over `ℚ(v)`: `(θᵢⁿf)_ν` is spanned by the `G(b)`, `b ∈ B(∞)_ν`, with `εᵢ(b) ≥ n`, and
  these are linearly independent (`linearIndependent_negGlobal_depth`).

## Implementation notes

Lusztig deduces 14.3.2 from his geometric construction of `𝐁` ([Lus] 14.2–14.3). Here the proof
is our own: it uses Kashiwara's Cor. 7.4.2 (`negFiltGlobalAt`) and the uniqueness of the lifts
in the balanced triple. The membership `G(b) ∈ fᵢⁿU⁻ ⇒ εᵢ(b) ≥ n` uses `f̃ᵢⁿ ẽᵢⁿ = 1` on
`fᵢⁿU⁻` (`kF_pow_kE_pow_of_mem_range`), which holds since the components `x_k`, `k < n`, of the
`i`-string decomposition of `x ∈ fᵢⁿU⁻` vanish (`BosonModule.component_eq_zero_of_mem_range`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 14.3.1, 14.3.2.
* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), §7.
-/

open scoped RatFunc Pointwise

noncomputable section

universe u

namespace LieLean.QuantumGroup

/-! ### Strings in boson modules -/

namespace BosonModule

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  {V : BosonModule q M} (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq0 hq

/-- `f f^{(n)} = [n+1] f^{(n+1)}`. -/
lemma f_df (n : ℕ) (x : M) : V.f (V.df n x) = qInt q (n + 1) • V.df (n + 1) x := by
  have h := qInt_ne_zero' hq0 hq (Nat.succ_pos n)
  rw [df_apply, df_apply, map_smul, smul_smul, qFactorial_succ, ← Module.End.mul_apply,
    ← pow_succ', mul_inv, ← mul_assoc, mul_inv_cancel₀ h, one_mul]

/-- The components of `f m`: `(f m)₀ = 0`. -/
lemma component_zero_f (m : M) : V.component hq0 hq 0 (V.f m) = 0 := by
  have : V.component hq0 hq 0 ∘ₗ V.f = 0 :=
    ext_df (V := V) hq0 hq fun n x hx ↦ by
      simp [f_df hq0 hq, component_df hq0 hq hx]
  exact LinearMap.congr_fun this m

/-- The components of `f m`: `(f m)ₙ₊₁ = [n+1] mₙ`. -/
lemma component_succ_f (n : ℕ) (m : M) :
    V.component hq0 hq (n + 1) (V.f m) = qInt q (n + 1) • V.component hq0 hq n m := by
  have : V.component hq0 hq (n + 1) ∘ₗ V.f = qInt q (n + 1) • V.component hq0 hq n :=
    ext_df (V := V) hq0 hq fun j x hx ↦ by
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, f_df hq0 hq, map_smul,
        component_df hq0 hq hx, add_left_inj]
      split_ifs with h
      · subst h; rfl
      · simp
  exact LinearMap.congr_fun this m

/-- The components of `ẽ m`: `(ẽ m)ⱼ = mⱼ₊₁`. -/
lemma component_eTilde (j : ℕ) (m : M) :
    V.component hq0 hq j (V.eTilde hq0 hq m) = V.component hq0 hq (j + 1) m := by
  have : V.component hq0 hq j ∘ₗ V.eTilde hq0 hq = V.component hq0 hq (j + 1) :=
    ext_df (V := V) hq0 hq fun n x hx ↦ by
      rcases n with _ | n
      · have h0 := component_df hq0 hq hx 0 (j + 1)
        simp only [df_zero, Nat.zero_ne_add_one, ↓reduceIte] at h0
        simp [eTilde_of_ker hq0 hq hx, h0]
      · simp [eTilde_df_succ hq0 hq hx, component_df hq0 hq hx]
  exact LinearMap.congr_fun this m

/-- An element of `fⁿ M` has vanishing components `mⱼ`, `j < n`. -/
lemma component_eq_zero_of_mem_range {n : ℕ} {m : M} (h : m ∈ LinearMap.range (V.f ^ n))
    {j : ℕ} (hj : j < n) : V.component hq0 hq j m = 0 := by
  obtain ⟨y, rfl⟩ := h
  induction n generalizing j y with
  | zero => omega
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    rcases j with _ | j
    · exact component_zero_f hq0 hq _
    · rw [component_succ_f hq0 hq, ih (by omega) y, smul_zero]

/-- If the components `mⱼ`, `j < n`, vanish, then `f̃ⁿ ẽⁿ m = m`. -/
lemma fTilde_pow_eTilde_pow {n : ℕ} {m : M} (h : ∀ j < n, V.component hq0 hq j m = 0) :
    (V.fTilde hq0 hq ^ n) ((V.eTilde hq0 hq ^ n) m) = m := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (V.eTilde hq0 hq), pow_succ' (V.fTilde hq0 hq), Module.End.mul_apply,
      Module.End.mul_apply, ih fun j hj ↦ by rw [component_eTilde]; exact h (j + 1) (by omega)]
    have := fTilde_eTilde_add_component (V := V) hq0 hq m
    rwa [h 0 (by omega), add_zero] at this

end BosonModule

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X
local notation "hv'" => pow_ne_one_of_transcendental' transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I : Type u} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

local notation "bosv" => bos (D := D) (pow_ne_one_of_transcendental' hvt)

/-! ### `fᵢⁿU⁻` and the Kashiwara operators -/

section Strings

omit [Finite I] in
/-- `f̃ᵢⁿ ẽᵢⁿ x = x` for `x ∈ fᵢⁿU⁻`. -/
lemma kF_pow_kE_pow_of_mem_range (i : I) {n : ℕ} {x : Um D 𝕧}
    (hx : x ∈ LinearMap.range (NegativePart.f D 𝕧 i ^ n)) :
    (kF hvt i ^ n) ((kE hvt i ^ n) x) = x :=
  BosonModule.fTilde_pow_eTilde_pow (V := bosv i) (NegativePart.pow_d_ne_zero (NeZero.ne 𝕧) i)
    (NegativePart.pow_d_ne_one hv' i) fun _ hj ↦
      BosonModule.component_eq_zero_of_mem_range (V := bosv i)
        (NegativePart.pow_d_ne_zero (NeZero.ne 𝕧) i) (NegativePart.pow_d_ne_one hv' i) hx hj

omit [Finite I] in
/-- `fᵢ^{(k)} y ∈ fᵢⁿU⁻` for `n ≤ k`. -/
lemma df_mem_range (i : I) {n k : ℕ} (hnk : n ≤ k) (y : Um D 𝕧) :
    (bosv i).df k y ∈ LinearMap.range (NegativePart.f D 𝕧 i ^ n) := by
  refine ⟨(qFactorial ((𝕧 ^ D.d i)⁻¹) k)⁻¹ • (NegativePart.f D 𝕧 i ^ (k - n)) y, ?_⟩
  rw [map_smul, ← Module.End.mul_apply, ← pow_add, Nat.add_sub_cancel' hnk,
    BosonModule.df_apply]
  rfl

/-- `(fᵢⁿU⁻)^ℤ_ν ⊆ fᵢⁿU⁻`. -/
lemma negFilt_le_range (i : I) (n : ℕ) (ν : I →₀ ℕ) {x : Um D 𝕧} (hx : x ∈ negFilt D i n ν) :
    x ∈ LinearMap.range (NegativePart.f D 𝕧 i ^ n) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, y, hk, -, -, -, rfl⟩ := hx
    exact df_mem_range D i hk y
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => rw [laurent_smul_eq]; exact Submodule.smul_mem _ _ hx

/-! The crystal `B(∞)` over `ℚ(v)`, specialized from `GrandLoop`. -/

/-- `ẽᵢ` preserves `v⁻¹L(∞)`. -/
lemma kE_mem_smul_latInf_ratFunc (i : I) {x : Um D 𝕧} (hx : x ∈ ϖ • latInf (D := D) hvt A) :
    kE hvt i x ∈ ϖ • latInf (D := D) hvt A := by
  let := Fintype.ofFinite I
  exact kashiwaraE_mem_smul_latInf (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum i hx

lemma kE_pow_mem_smul_latInf_ratFunc (i : I) (n : ℕ) {x : Um D 𝕧}
    (hx : x ∈ ϖ • latInf (D := D) hvt A) : (kE hvt i ^ n) x ∈ ϖ • latInf (D := D) hvt A := by
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact kE_mem_smul_latInf_ratFunc D i ih

/-- `ẽᵢ b ∈ B(∞) ∪ {0}` for `b = f̃_w 1`. -/
lemma kE_fWi_cases_ratFunc (i : I) (w : List I) :
    kE (D := D) hvt i (fWi hvt w) ∈ ϖ • latInf (D := D) hvt A ∨
      ∃ w', kE (D := D) hvt i (fWi hvt w) - fWi hvt w' ∈ ϖ • latInf (D := D) hvt A := by
  let := Fintype.ofFinite I
  exact kE_fWi_cases (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum i w

/-- `b = f̃ᵢ ẽᵢ b` when `ẽᵢ b ≠ 0`. -/
lemma fWi_sub_mem_of_kE_ratFunc (i : I) {w w' : List I}
    (h0 : kE (D := D) hvt i (fWi hvt w) ∉ ϖ • latInf (D := D) hvt A)
    (h : kE (D := D) hvt i (fWi hvt w) - fWi hvt w' ∈ ϖ • latInf (D := D) hvt A) :
    fWi (D := D) hvt w - fWi hvt (i :: w') ∈ ϖ • latInf (D := D) hvt A := by
  let := Fintype.ofFinite I
  exact fWi_sub_mem_of_kE (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum i h0 h

/-- Congruent words have the same weight. -/
lemma wordWeight_eq_of_sub_mem_ratFunc {w w' : List I}
    (h : fWi (D := D) hvt w - fWi hvt w' ∈ ϖ • latInf (D := D) hvt A) :
    wordWeight w = wordWeight w' := by
  let := Fintype.ofFinite I
  exact wordWeight_eq_of_sub_mem_latInf (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum h

/-- `f̃_w 1 ∉ v⁻¹L(∞)`. -/
lemma fWi_notMem_ratFunc (w : List I) : fWi (D := D) hvt w ∉ ϖ • latInf (D := D) hvt A :=
  PBWSignedCrystal.word_not_mem_uniformizer (D := D) w

/-- If `ẽᵢⁿ f̃_w 1 ∉ v⁻¹L(∞)`, then `f̃_w 1 ≡ f̃ᵢⁿ f̃_u 1` for some word `u`. -/
lemma exists_fWi_sub_mem_of_kE_pow (i : I) (n : ℕ) {w : List I}
    (h : (kE hvt i ^ n) (fWi (D := D) hvt w) ∉ ϖ • latInf (D := D) hvt A) :
    ∃ u, fWi (D := D) hvt w - fWi hvt (List.replicate n i ++ u) ∈
      ϖ • latInf (D := D) hvt A := by
  induction n generalizing w with
  | zero => exact ⟨w, by simp⟩
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply] at h
    have h0 : kE (D := D) hvt i (fWi hvt w) ∉ ϖ • latInf (D := D) hvt A :=
      fun h' ↦ h (kE_pow_mem_smul_latInf_ratFunc D i n h')
    rcases kE_fWi_cases_ratFunc D i w with h1 | ⟨w', hw'⟩
    · exact absurd h1 h0
    have hc := fWi_sub_mem_of_kE_ratFunc D i h0 hw'
    have h2 : (kE hvt i ^ n) (fWi (D := D) hvt w') ∉ ϖ • latInf (D := D) hvt A := by
      intro h2
      refine h ?_
      rw [← sub_add_cancel (kE hvt i (fWi hvt w)) (fWi hvt w'), map_add]
      exact add_mem (kE_pow_mem_smul_latInf_ratFunc D i n hw') h2
    obtain ⟨u, hu⟩ := ih h2
    refine ⟨u, ?_⟩
    have e : fWi (D := D) hvt (List.replicate (n + 1) i ++ u) =
        kF hvt i (fWi hvt (List.replicate n i ++ u)) := by
      rw [List.replicate_succ, List.cons_append]; rfl
    have e' : fWi (D := D) hvt (i :: w') = kF hvt i (fWi hvt w') := rfl
    rw [e, ← sub_add_sub_cancel _ (fWi hvt (i :: w')), e', ← map_sub]
    exact add_mem hc (kF_mem_smul_latInf i hu)

end Strings

/-! ### The strings of `B(∞)` and the global basis -/

section Depth

/-- `εᵢ(b) ≥ n` for `b ∈ B(∞)_ν`: `b ∈ f̃ᵢⁿB(∞)`, i.e. `b` is the class of a word `iⁿu`. -/
def NegDepthGe (i : I) (n : ℕ) {ν : I →₀ ℕ} (b : negCrystal D ν) : Prop :=
  ∃ u : List I, fWi (D := D) hvt (Quotient.out b).1 - fWi hvt (List.replicate n i ++ u) ∈
    ϖ • latInf (D := D) hvt A

omit [Finite I] in
lemma negDepthGe_zero (i : I) {ν : I →₀ ℕ} (b : negCrystal D ν) : NegDepthGe D i 0 b :=
  ⟨(Quotient.out b).1, by simp⟩

omit [Finite I] in
lemma NegDepthGe.mono {i : I} {m n : ℕ} (hmn : m ≤ n) {ν : I →₀ ℕ} {b : negCrystal D ν}
    (hb : NegDepthGe D i n b) : NegDepthGe D i m b := by
  obtain ⟨u, hu⟩ := hb
  refine ⟨List.replicate (n - m) i ++ u, ?_⟩
  rwa [← List.append_assoc, List.replicate_append_replicate, Nat.add_sub_cancel' hmn]

omit [Finite I] in
/-- The class of a word congruent to the representative of `b` is `b`. -/
lemma eq_mk_of_sub_mem {ν : I →₀ ℕ} {b : negCrystal D ν} {w : List I} (hw : wordWeight w = ν)
    (h : fWi (D := D) hvt (Quotient.out b).1 - fWi hvt w ∈ ϖ • latInf (D := D) hvt A) :
    b = Quotient.mk _ ⟨w, hw⟩ := by
  conv_lhs => rw [← Quotient.out_eq b]
  exact Quotient.sound h

/-- An element of `E(ν)` congruent to `f̃_w 1` modulo `v⁻¹L(∞)` is `G(b)` for the class `b` of
`w`. -/
lemma negGlobal_eq_of_sub_mem {ν : I →₀ ℕ} {y : Um D 𝕧} (hy : y ∈ negBalanced D ν) {w : List I}
    (hw : wordWeight w = ν) (hyw : y - fWi (D := D) hvt w ∈ ϖ • latInf (D := D) hvt A) :
    y = negGlobal D ν (Quotient.mk _ ⟨w, hw⟩) := by
  refine eq_of_mem_negBalanced (negGlobalAt D ν) hy (negGlobal_mem D ν _) ?_
  have h1 := negGlobal_sub_mem D ν (Quotient.mk _ ⟨w, hw⟩)
  have h2 : fWi (D := D) hvt (Quotient.out (Quotient.mk (negCrystalSetoid D ν) ⟨w, hw⟩)).1 -
      fWi hvt w ∈ ϖ • latInf (D := D) hvt A := Quotient.mk_out (s := negCrystalSetoid D ν) _
  have e : y - negGlobal D ν (Quotient.mk _ ⟨w, hw⟩) = (y - fWi hvt w) -
      (fWi hvt (Quotient.out (Quotient.mk (negCrystalSetoid D ν) ⟨w, hw⟩)).1 - fWi hvt w) -
      (negGlobal D ν (Quotient.mk _ ⟨w, hw⟩) -
        fWi hvt (Quotient.out (Quotient.mk (negCrystalSetoid D ν) ⟨w, hw⟩)).1) := by abel
  rw [e]
  exact sub_mem (sub_mem hyw h2) h1

lemma negGlobal_notMem (ν : I →₀ ℕ) (b : negCrystal D ν) :
    negGlobal D ν b ∉ ϖ • latInf (D := D) hvt A := fun h ↦
  fWi_notMem_ratFunc D (Quotient.out b).1 (by
    rw [← sub_sub_cancel (negGlobal D ν b) (fWi hvt (Quotient.out b).1)]
    exact sub_mem h (negGlobal_sub_mem D ν b))

/-- `f̃ᵢⁿ z ∈ (fᵢⁿU⁻)^ℤ_{μ+nαᵢ}` for `z ∈ U⁻_{ℤ,μ}`. -/
lemma kF_pow_mem_negFilt (i : I) (n : ℕ) {μ : I →₀ ℕ} {z : Um D 𝕧} (hz : z ∈ negIntegral D)
    (hzw : z ∈ Uw D 𝕧 μ) : (kF hvt i ^ n) z ∈ negFilt D i n (μ + Finsupp.single i n) := by
  have hq0 := NegativePart.pow_d_ne_zero (D := D) (NeZero.ne 𝕧) i
  have hq := NegativePart.pow_d_ne_one (D := D) hv' i
  obtain ⟨N, -, hsum⟩ := exists_sum_comp (D := D) i z
  rw [hsum, map_sum]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  have hc : (kF hvt i ^ n) ((bosv i).df k (comp hvt i k z)) =
      (bosv i).df (n + k) (comp hvt i k z) := by
    rw [← BosonModule.fTilde_pow_apply (V := bosv i) hq0 hq (e_comp i k z),
      ← BosonModule.fTilde_pow_apply (V := bosv i) hq0 hq (e_comp i k z), ← Module.End.mul_apply]
    change ((bosv i).fTilde hq0 hq ^ n * (bosv i).fTilde hq0 hq ^ k) (comp hvt i k z) = _
    rw [← pow_add]
  rw [hc]
  by_cases hk : k ≤ μ i
  · have hcw : comp hvt i k z ∈ Uw D 𝕧 (μ - Finsupp.single i k) :=
      @component_mem_Uw _ _ _ _ D _ _ _ transcendental_ratFunc_X i _ z hzw k
    have hw : μ - Finsupp.single i k = μ + Finsupp.single i n - Finsupp.single i (n + k) := by
      ext l
      by_cases hl : l = i
      · subst hl; simp; omega
      · simp [Ne.symm hl]
    rw [hw] at hcw
    exact df_mem_negFilt D i (by omega) (by simp; omega)
      (negative_component_mem_integral D i hz k) hcw
  · rw [comp_eq_zero_of_lt D i hzw (by omega), map_zero]
    exact zero_mem _

/-- **`(G.3)`**: if `εᵢ(b) ≥ n`, then `G(b) ∈ (fᵢⁿU⁻)^ℤ_ν` ([Kas91] Thm. 7(G.3), as a
consequence of Cor. 7.4.2). -/
theorem negGlobal_mem_negFilt {i : I} {n : ℕ} {ν : I →₀ ℕ} {b : negCrystal D ν}
    (hb : NegDepthGe D i n b) : negGlobal D ν b ∈ negFilt D i n ν := by
  let := Fintype.ofFinite I
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hU : negGlobal D ν b ∈ Uw D 𝕧 (ν - Finsupp.single i 0) := by
      simpa using (negGlobal_mem D ν b).2.1
    have h := df_mem_negFilt D i (n := 0) (k := 0) (ν := ν) le_rfl (Nat.zero_le _)
      (negGlobal_mem D ν b).1 hU
    simpa using h
  obtain ⟨u, hu⟩ := hb
  have hwt : wordWeight (List.replicate n i ++ u) = ν :=
    (wordWeight_eq_of_sub_mem_ratFunc D hu).symm.trans (Quotient.out b).2
  have hx : fWi (D := D) hvt (List.replicate n i ++ u) ∈ negFilt D i n ν := by
    have h := kF_pow_mem_negFilt D i n (fWi_mem_negIntegral D u) (fWi_mem_Uw u)
    rw [kF_pow_fWi (D := D) i n u] at h
    rwa [← hwt, LusztigF.wordWeight_append, LusztigF.wordWeight_replicate, add_comm,
      Finsupp.smul_single_one]
  obtain ⟨y, hy, hy₀, hy₁, hxy⟩ := exists_negFilt_sub_mem D.isXRegular_extendedRootDatum
    D.exists_fundamental_extendedRootDatum (globalBelow D.isXRegular_extendedRootDatum
      D.exists_fundamental_extendedRootDatum ν) i hn hx (NegativePart.fWord_mem_latticeInf _ _ _)
  have hyB : y ∈ negBalanced D ν :=
    ⟨(mem_negFilt_le D hy).1, (mem_negFilt_le D hy).2, hy₀, hy₁⟩
  have hyw : y - fWi (D := D) hvt (List.replicate n i ++ u) ∈ ϖ • latInf (D := D) hvt A := by
    rw [← neg_sub]; exact neg_mem hxy
  rw [eq_mk_of_sub_mem D hwt hu, ← negGlobal_eq_of_sub_mem D hyB hwt hyw]
  exact hy

/-- If `G(b) ∈ fᵢⁿU⁻`, then `εᵢ(b) ≥ n`. -/
theorem negDepthGe_of_mem_range {i : I} {n : ℕ} {ν : I →₀ ℕ} {b : negCrystal D ν}
    (hb : negGlobal D ν b ∈ LinearMap.range (NegativePart.f D 𝕧 i ^ n)) :
    NegDepthGe D i n b := by
  set w := (Quotient.out b).1
  have hE : (kE hvt i ^ n) (negGlobal D ν b) ∉ ϖ • latInf (D := D) hvt A := fun h ↦
    negGlobal_notMem D ν b (by
      rw [← kF_pow_kE_pow_of_mem_range D i hb]
      exact kF_pow_mem_smul_latInf D i n h)
  refine exists_fWi_sub_mem_of_kE_pow D i n fun h ↦ hE ?_
  rw [← sub_add_cancel (negGlobal D ν b) (fWi hvt w), map_add]
  exact add_mem (kE_pow_mem_smul_latInf_ratFunc D i n (negGlobal_sub_mem D ν b)) h

/-- **[Kas91] Cor. 7.4.2 / [Lus] 14.3.2 (a) over `𝒜`**: `(fᵢⁿU⁻)^ℤ_ν` is contained in the
`𝒜`-span of the `G(b)` with `εᵢ(b) ≥ n`. -/
theorem negFilt_le_span (i : I) (n : ℕ) (ν : I →₀ ℕ) :
    negFilt D i n ν ≤ Submodule.span (LaurentPolynomial ℤ)
      (negGlobal D ν '' {b | NegDepthGe D i n b}) := by
  let := Fintype.ofFinite I
  intro x hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine Submodule.span_mono ?_ (mem_span_negGlobal D (mem_negFilt_le D hx).1
      (mem_negFilt_le D hx).2)
    rintro _ ⟨b, rfl⟩
    exact ⟨b, negDepthGe_zero D i b, rfl⟩
  obtain ⟨ι, g, u, hgF, hg₀, hg₁, hspan, hgu, hgw⟩ := negFiltGlobalAt
    D.isXRegular_extendedRootDatum D.exists_fundamental_extendedRootDatum
    (globalBelow D.isXRegular_extendedRootDatum D.exists_fundamental_extendedRootDatum ν) i hn
  refine Submodule.span_mono ?_ (hspan x hx)
  rintro _ ⟨k, rfl⟩
  have hB : g k ∈ negBalanced D ν :=
    ⟨(mem_negFilt_le D (hgF k)).1, (mem_negFilt_le D (hgF k)).2, hg₀.1 k, hg₁.1 k⟩
  refine ⟨_, ⟨u k, Quotient.mk_out (s := negCrystalSetoid D ν) ⟨_, hgw k⟩⟩,
    (negGlobal_eq_of_sub_mem D hB (hgw k) (hgu k)).symm⟩

end Depth

/-! ### [Lus] 14.3.1–14.3.2 (a) -/

section Subsets

/-- **[Lus] 14.3.1**: `𝐁_{i;≥n} = 𝐁 ∩ θᵢⁿf`. In `U⁻ ≅ f`, `θᵢⁿf` is `fᵢⁿU⁻`. -/
def signedBasisGe (i : I) (n : ℕ) : Set (Um D 𝕧) :=
  {x | x ∈ signedBasis D ∧ x ∈ LinearMap.range (NegativePart.f D 𝕧 i ^ n)}

/-- **[Lus] 14.3.1**: `𝐁_{i;n} = 𝐁_{i;≥n} - 𝐁_{i;≥n+1}`. -/
def signedBasisAt (i : I) (n : ℕ) : Set (Um D 𝕧) :=
  signedBasisGe D i n \ signedBasisGe D i (n + 1)

/-- `𝐁_{i;≥n}` consists of the `±G(b)` with `εᵢ(b) ≥ n`. -/
theorem mem_signedBasisGe_iff {i : I} {n : ℕ} {x : Um D 𝕧} :
    x ∈ signedBasisGe D i n ↔ ∃ (ν : I →₀ ℕ) (b : negCrystal D ν),
      NegDepthGe D i n b ∧ (x = negGlobal D ν b ∨ x = -negGlobal D ν b) := by
  constructor
  · rintro ⟨hx, hr⟩
    obtain ⟨ν, b, hb⟩ := (mem_signedBasis_iff D).1 hx
    have hG : negGlobal D ν b ∈ LinearMap.range (NegativePart.f D 𝕧 i ^ n) := by
      rcases hb with rfl | rfl
      · exact hr
      · simpa using neg_mem hr
    exact ⟨ν, b, negDepthGe_of_mem_range D hG, hb⟩
  · rintro ⟨ν, b, hd, hb⟩
    refine ⟨(mem_signedBasis_iff D).2 ⟨ν, b, hb⟩, ?_⟩
    have hG := negFilt_le_range D i n ν (negGlobal_mem_negFilt D hd)
    rcases hb with rfl | rfl
    · exact hG
    · exact neg_mem hG

/-- `𝐁_{i;n}` consists of the `±G(b)` with `εᵢ(b) = n`. -/
theorem mem_signedBasisAt_iff {i : I} {n : ℕ} {x : Um D 𝕧} :
    x ∈ signedBasisAt D i n ↔ ∃ (ν : I →₀ ℕ) (b : negCrystal D ν),
      NegDepthGe D i n b ∧ ¬ NegDepthGe D i (n + 1) b ∧
        (x = negGlobal D ν b ∨ x = -negGlobal D ν b) := by
  constructor
  · rintro ⟨hge, hnot⟩
    obtain ⟨ν, b, hd, hb⟩ := (mem_signedBasisGe_iff D).1 hge
    exact ⟨ν, b, hd, fun h ↦ hnot ((mem_signedBasisGe_iff D).2 ⟨ν, b, h, hb⟩), hb⟩
  · rintro ⟨ν, b, hd, hnd, hb⟩
    refine ⟨(mem_signedBasisGe_iff D).2 ⟨ν, b, hd, hb⟩, fun h ↦ hnd ?_⟩
    have hr := h.2
    refine negDepthGe_of_mem_range D ?_
    rcases hb with rfl | rfl
    · exact hr
    · simpa using neg_mem hr

/-- **[Lus] Thm. 14.3.2 (a)** over `𝒜`, at the weight `ν`: `(Σ_{n' ≥ n} θᵢ^{(n')} 𝒜f)_ν`, which
is `(fᵢⁿU⁻)^ℤ_ν`, is the `𝒜`-span of the `G(b)`, `b ∈ B(∞)_ν`, with `εᵢ(b) ≥ n`. -/
theorem negFilt_eq_span (i : I) (n : ℕ) (ν : I →₀ ℕ) :
    negFilt D i n ν = Submodule.span (LaurentPolynomial ℤ)
      (negGlobal D ν '' {b | NegDepthGe D i n b}) :=
  le_antisymm (negFilt_le_span D i n ν) (Submodule.span_le.2 (by
    rintro _ ⟨b, hb, rfl⟩
    exact negGlobal_mem_negFilt D hb))

omit [Finite I] [DecidableEq I] in
lemma mem_span_ratFunc_of_mem_span_laurent {S : Set (Um D 𝕧)} {x : Um D 𝕧}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) S) : x ∈ Submodule.span 𝕂 S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul c y _ hy => rw [laurent_smul_eq]; exact Submodule.smul_mem _ _ hy

/-- **[Lus] Thm. 14.3.2 (a)** over `ℚ(v)`, at the weight `ν`: `(θᵢⁿf)_ν = (fᵢⁿU⁻)_ν` is the
`ℚ(v)`-span of the `G(b)`, `b ∈ B(∞)_ν`, with `εᵢ(b) ≥ n`. -/
theorem mem_range_iff_mem_span {i : I} {n : ℕ} {ν : I →₀ ℕ} {x : Um D 𝕧} (hx : x ∈ Uw D 𝕧 ν) :
    x ∈ LinearMap.range (NegativePart.f D 𝕧 i ^ n) ↔
      x ∈ Submodule.span 𝕂 (negGlobal D ν '' {b | NegDepthGe D i n b}) := by
  constructor
  · rintro ⟨y, rfl⟩
    set S := Submodule.span 𝕂 (negGlobal D ν '' {b | NegDepthGe D i n b})
    have hq := BosonModule.qFactorial_ne_zero' (NegativePart.pow_d_ne_zero (D := D)
      (NeZero.ne 𝕧) i) (NegativePart.pow_d_ne_one hv' i) n
    have hfn : (NegativePart.f D 𝕧 i ^ n) y =
        qFactorial ((𝕧 ^ D.d i)⁻¹) n • (bosv i).df n y := by
      rw [BosonModule.df_apply, smul_smul, mul_inv_cancel₀ hq, one_smul]; rfl
    have hP : NegativePart.proj D 𝕧 (LusztigF.toZ ν) ((NegativePart.f D 𝕧 i ^ n) y) =
        (NegativePart.f D 𝕧 i ^ n) y := by
      rw [proj_of_mem_Uw hx]; simp
    rw [← hP, hfn, map_smul, proj_df]
    refine S.smul_mem _ ?_
    by_cases hn : n ≤ ν i
    · have e : LusztigF.toZ ν - Finsupp.single i (n : ℤ) =
          LusztigF.toZ (ν - Finsupp.single i n) := by
        ext l
        by_cases hl : l = i
        · subst hl; simp; omega
        · simp [Ne.symm hl]
      rw [e]
      have key : ∀ z ∈ Submodule.span 𝕂 (Set.range (negGlobal D (ν - Finsupp.single i n))),
          (bosv i).df n z ∈ S := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨b', rfl⟩ := hz
          exact mem_span_ratFunc_of_mem_span_laurent D (negFilt_le_span D i n ν
            (df_mem_negFilt D i le_rfl hn (negGlobal_mem D _ b').1 (negGlobal_mem D _ b').2.1))
        | zero => rw [map_zero]; exact zero_mem _
        | add z z' _ _ hz hz' => rw [map_add]; exact add_mem hz hz'
        | smul c z _ hz => rw [map_smul]; exact S.smul_mem _ hz
      exact key _ (mem_span_negGlobal_field D (proj_mem_Uw (ν - Finsupp.single i n) y))
    · have h0 : NegativePart.proj D 𝕧 (LusztigF.toZ ν - Finsupp.single i (n : ℤ)) y = 0 := by
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        have hn' : ¬ (0 ≤ LusztigF.toZ ν - Finsupp.single i (n : ℤ)) := by
          intro h
          have := h i
          simp at this
          omega
        rw [NegativePart.proj_mk]
        simp [zWeightProj, hn']
      rw [h0, map_zero]
      exact zero_mem _
  · intro h
    refine Submodule.span_le.2 ?_ h
    rintro _ ⟨b, hb, rfl⟩
    exact negFilt_le_range D i n ν (negGlobal_mem_negFilt D hb)

/-- The `G(b)` with `εᵢ(b) ≥ n` are linearly independent. -/
theorem linearIndependent_negGlobal_depth (i : I) (n : ℕ) (ν : I →₀ ℕ) :
    LinearIndependent 𝕂 fun b : {b : negCrystal D ν // NegDepthGe D i n b} ↦
      negGlobal D ν b.1 :=
  (linearIndependent_negGlobal D ν).comp _ Subtype.val_injective

end Subsets

end LieLean.QuantumGroup
