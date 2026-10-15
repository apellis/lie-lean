/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.SignedSubsets

/-!
# The bijections `π_{i,n} : 𝐁_{i;0} → 𝐁_{i;n}`

This file proves [Lus] Thm. 14.3.2 (c) for the signed basis `𝐁 = {±G(b)}` of `U⁻ ≅ f`: for
`x ∈ 𝐁_{i;0}` there is a unique `y ∈ 𝐁_{i;n}` such that `θᵢ^{(n)} x - y` is an `𝒜`-linear
combination of elements of `𝐁_{i;≥n+1}`, and `x ↦ y` is a bijection `π_{i,n} : 𝐁_{i;0} → 𝐁_{i;n}`.
Explicitly, `π_{i,n}(±G(b)) = ±G(f̃ᵢⁿ b)`.

## Main definitions

* `negCrystalF D i n b`: the element `f̃ᵢⁿ b ∈ B(∞)`, the class of `iⁿw` for a word `w` of `b`.
* `signedStringMap D i n`: Lusztig's `π_{i,n} : 𝐁_{i;0} → 𝐁_{i;n}`.

## Main results

* `df_negGlobal_sub_mem_span`: if `εᵢ(b) = 0`, then `θᵢ^{(n)} G(b) - G(f̃ᵢⁿ b)` is an
  `𝒜`-combination of the `G(b'')` with `εᵢ(b'') ≥ n + 1`.
* `existsUnique_df_sub_mem_span`, `signedStringMap_bijective`: [Lus] Thm. 14.3.2 (c).
* `signedStringMap_signed`: `π_{i,n}(±G(b)) = ±G(f̃ᵢⁿ b)`.

## Implementation notes

Lusztig deduces 14.3.2 (c) from the geometric construction of `𝐁` ([Lus] 14.3, using 10.3.2).
The proof here is our own. Write `θᵢ^{(n)} G(b) - G(f̃ᵢⁿ b) = Σ c_{b''} G(b'')` with
`c_{b''} ∈ 𝒜` ([Kas91] (7.5.6)). The left side is bar-invariant, so the `c_{b''}` are
bar-invariant (`invert_eq_of_negBar_eq`). Modulo `(fᵢ^{n+1}U⁻)^ℤ`, the left side equals
`θᵢ^{(n)} Pᵢ G(b) - G(f̃ᵢⁿ b)`, where `Pᵢ` is the projection to the `i`-string component `0`
([Kas91] (6.1.2)); this element lies in `v⁻¹L(∞)` since `θᵢ^{(n)} Pᵢ G(b) ≡ f̃ᵢⁿ G(b)` when
`ẽᵢ G(b) ∈ v⁻¹L(∞)`. By [Kas91] Cor. 7.4.2 and residue independence, every `c_{b''}` with
`εᵢ(b'') ≤ n` lies in `v⁻¹A`, hence vanishes, being bar-invariant
(`laurent_eq_zero_of_invert_eq`). Uniqueness and bijectivity follow from the linear
independence of the `G(b)` over `𝒜` and the injectivity of `f̃ᵢⁿ` on `B(∞)`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 14.3.2.
* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, §6–7.
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

local notation "bosv" => bos (D := D) (pow_ne_one_of_transcendental' hvt)

/-! ### Coefficients in the global basis -/

section Coefficients

/-- A bar-invariant element of `𝒜` lying in `v⁻¹A` is zero. -/
lemma laurent_eq_zero_of_invert_eq {c : LaurentPolynomial ℤ}
    (hc : LaurentPolynomial.invert c = c) {a : A}
    (ha : algebraMap A 𝕂 (ϖ * a) = integralLaurentEval c) : c = 0 := by
  apply integralLaurentEval_injective
  rw [map_zero]
  refine eq_zero_of_laurent_regular_uniformizer c a ha (ϖ * a : LocalRing) ?_
  have h : integralLaurentEval c = RatFunc.bar (integralLaurentEval c) := by
    rw [bar_integralLaurentEval, hc]
  rw [h, ← ha]
  change _ = RatFunc.bar (RatFunc.bar _)
  rw [RatFunc.bar_bar]
  rfl

/-- If `Σ_b c_b G(b) ∈ v⁻¹L(∞)` with `c_b ∈ 𝒜`, then every `c_b ∈ v⁻¹A`. -/
lemma exists_eq_of_linearCombination_mem {ν : I →₀ ℕ} (c : negCrystal D ν →₀ LaurentPolynomial ℤ)
    (h : Finsupp.linearCombination (LaurentPolynomial ℤ) (negGlobal D ν) c ∈
      ϖ • latInf (D := D) hvt A) (b : negCrystal D ν) :
    ∃ a : A, algebraMap A 𝕂 (ϖ * a) = integralLaurentEval (c b) := by
  let := Fintype.ofFinite I
  by_cases hb : b ∈ c.support
  · rw [Finsupp.linearCombination_apply, Finsupp.sum] at h
    simp_rw [laurent_smul_eq] at h
    obtain ⟨a, ha⟩ := (residueIndependent_negGlobalLift D.isXRegular_extendedRootDatum
      D.exists_fundamental_extendedRootDatum (globalBelow D.isXRegular_extendedRootDatum
        D.exists_fundamental_extendedRootDatum ν)).exists_eq_of_sum_mem_smul
      InfinityLocalRing.injective_algebraMap irreducible_localX.ne_zero
      InfinityLocalRing.exists_pow_mul c.support (fun b ↦ integralLaurentEval (c b)) h b hb
    exact ⟨a, ha.symm⟩
  · rw [Finsupp.notMem_support_iff.1 hb]
    exact ⟨0, by simp⟩

/-- The bar involution on coordinates in the global basis. -/
lemma negBar_linearCombination {ν : I →₀ ℕ} (c : negCrystal D ν →₀ LaurentPolynomial ℤ) :
    negBar D (Finsupp.linearCombination (LaurentPolynomial ℤ) (negGlobal D ν) c) =
      Finsupp.linearCombination (LaurentPolynomial ℤ) (negGlobal D ν)
        (c.mapRange LaurentPolynomial.invert (map_zero _)) := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index (fun b ↦ zero_smul _ (negGlobal D ν b)), Finsupp.sum,
    Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [negBar_laurent_smul, negBar_negGlobal]

/-- If `x = Σ_b c_b G(b)` is bar-invariant, so are the `c_b`. -/
lemma invert_eq_of_negBar_eq {ν : I →₀ ℕ} (c : negCrystal D ν →₀ LaurentPolynomial ℤ)
    (h : negBar D (Finsupp.linearCombination (LaurentPolynomial ℤ) (negGlobal D ν) c) =
      Finsupp.linearCombination (LaurentPolynomial ℤ) (negGlobal D ν) c) (b : negCrystal D ν) :
    LaurentPolynomial.invert (c b) = c b := by
  rw [negBar_linearCombination] at h
  exact DFunLike.congr_fun (linearIndependent_negGlobal_laurent D ν h) b

end Coefficients

/-! ### `θᵢ^{(n)} G(b)` for `εᵢ(b) = 0` -/

section Strings

omit [Finite I] [DecidableEq I] in
lemma wordWeight_replicate_append (i : I) (n : ℕ) (w : List I) :
    wordWeight (List.replicate n i ++ w) = wordWeight w + Finsupp.single i n := by
  rw [LusztigF.wordWeight_append, LusztigF.wordWeight_replicate, add_comm,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- `f̃ᵢⁿ b ∈ B(∞)_{ν+nαᵢ}` for `b ∈ B(∞)_ν`: the class of `iⁿw` for a word `w` of `b`. -/
def negCrystalF (i : I) (n : ℕ) {ν : I →₀ ℕ} (b : negCrystal D ν) :
    negCrystal D (ν + Finsupp.single i n) :=
  Quotient.mk _ ⟨List.replicate n i ++ (Quotient.out b).1,
    by rw [wordWeight_replicate_append, (Quotient.out b).2]⟩

omit [Finite I] in
lemma negDepthGe_negCrystalF (i : I) (n : ℕ) {ν : I →₀ ℕ} (b : negCrystal D ν) :
    NegDepthGe D i n (negCrystalF D i n b) :=
  ⟨(Quotient.out b).1, Quotient.mk_out (s := negCrystalSetoid D (ν + Finsupp.single i n)) _⟩

/-- If `εᵢ(b) = 0`, then `ẽᵢ G(b) ∈ v⁻¹L(∞)`. -/
lemma kE_negGlobal_mem {i : I} {ν : I →₀ ℕ} {b : negCrystal D ν} (hb : ¬ NegDepthGe D i 1 b) :
    kE hvt i (negGlobal D ν b) ∈ ϖ • latInf (D := D) hvt A := by
  by_contra h
  have h1 := kE_mem_smul_latInf_ratFunc D i (negGlobal_sub_mem D ν b)
  rw [map_sub] at h1
  have h2 : kE (D := D) hvt i (fWi hvt (Quotient.out b).1) ∉ ϖ • latInf (D := D) hvt A :=
    fun h' ↦ h (by rw [← sub_add_cancel (kE hvt i (negGlobal D ν b))
      (kE hvt i (fWi hvt (Quotient.out b).1))]; exact add_mem h1 h')
  obtain ⟨u, hu⟩ := exists_fWi_sub_mem_of_kE_pow D i 1 (by rwa [pow_one])
  exact hb ⟨u, hu⟩

/-- **[Lus] 14.3.2 (c), existence**, for `G(b)`: if `εᵢ(b) = 0`, then `θᵢ^{(n)} G(b)` is
`G(f̃ᵢⁿ b)` plus an `𝒜`-linear combination of the `G(b'')` with `εᵢ(b'') ≥ n + 1`. -/
theorem df_negGlobal_sub_mem_span {i : I} (n : ℕ) {ν : I →₀ ℕ} {b : negCrystal D ν}
    (hb : ¬ NegDepthGe D i 1 b) :
    (bosv i).df n (negGlobal D ν b) - negGlobal D (ν + Finsupp.single i n) (negCrystalF D i n b) ∈
      Submodule.span (LaurentPolynomial ℤ) (negGlobal D (ν + Finsupp.single i n) ''
        {b'' | NegDepthGe D i (n + 1) b''}) := by
  set μ := ν + Finsupp.single i n
  set g := negGlobal D ν b
  have hg := negGlobal_mem D ν b
  set c := negCrystalF D i n b
  have hw : μ - Finsupp.single i n = ν := add_tsub_cancel_right _ _
  have hn : n ≤ μ i := by simp [μ]
  have hgw : g ∈ Uw D 𝕧 (μ - Finsupp.single i n) := hw ▸ hg.2.1
  have hcw : comp hvt i 0 g ∈ Uw D 𝕧 (μ - Finsupp.single i n) := by
    have := @component_mem_Uw _ _ _ _ D _ _ _ transcendental_ratFunc_X i _ g hg.2.1 0
    rw [Finsupp.single_zero, tsub_zero] at this
    exact hw ▸ this
  have hx : (bosv i).df n g ∈ negFilt D i n μ := df_mem_negFilt D i le_rfl hn hg.1 hgw
  have hxy := df_sub_df_comp_mem_negFilt D i hn hg.1 hgw
  -- `θᵢ^{(n)} Pᵢ G(b) ≡ G(f̃ᵢⁿ b)` modulo `v⁻¹L(∞)`
  have hyc : (bosv i).df n (comp hvt i 0 g) - negGlobal D μ c ∈ ϖ • latInf (D := D) hvt A := by
    have h1 := df_comp_sub_kF_pow_mem D i n (kE_negGlobal_mem D hb)
    have h2 := kF_pow_mem_smul_latInf D i n (negGlobal_sub_mem D ν b)
    rw [map_sub, kF_pow_fWi] at h2
    have h3 : fWi (D := D) hvt (Quotient.out c).1 -
        fWi hvt (List.replicate n i ++ (Quotient.out b).1) ∈ ϖ • latInf (D := D) hvt A :=
      Quotient.mk_out (s := negCrystalSetoid D μ) _
    have h4 := negGlobal_sub_mem D μ c
    have e : (bosv i).df n (comp hvt i 0 g) - negGlobal D μ c =
        ((bosv i).df n (comp hvt i 0 g) - (kF hvt i ^ n) g) +
        ((kF hvt i ^ n) g - fWi hvt (List.replicate n i ++ (Quotient.out b).1)) -
        (fWi hvt (Quotient.out c).1 - fWi hvt (List.replicate n i ++ (Quotient.out b).1)) -
        (negGlobal D μ c - fWi hvt (Quotient.out c).1) := by abel
    rw [e]
    exact sub_mem (sub_mem (add_mem h1 h2) h3) h4
  -- coordinates of `θᵢ^{(n)} G(b) - G(f̃ᵢⁿ b)`
  have hGc := negGlobal_mem D μ c
  have hd := mem_span_negGlobal D (sub_mem (mem_negFilt_le D hx).1 hGc.1)
    (sub_mem (mem_negFilt_le D hx).2 hGc.2.1)
  rw [← Finsupp.range_linearCombination] at hd
  obtain ⟨f, hf⟩ := hd
  obtain ⟨h, hhS, hh⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1
    (negFilt_le_span D i (n + 1) μ hxy)
  have hbar : negBar D ((bosv i).df n g - negGlobal D μ c) = (bosv i).df n g - negGlobal D μ c := by
    rw [map_sub, negBar_df, negBar_negGlobal, negBar_negGlobal]
  rw [← hf] at hbar
  have hinv := invert_eq_of_negBar_eq D f hbar
  have hres := exists_eq_of_linearCombination_mem D (f - h) (by
    rw [map_sub, hf, hh]
    convert hyc using 1
    abel)
  rw [← hf, Finsupp.mem_span_image_iff_linearCombination]
  refine ⟨f, fun b' hb' ↦ ?_, rfl⟩
  by_contra hbS
  have h0 : h b' = 0 := Finsupp.notMem_support_iff.1 fun h' ↦ hbS (hhS h')
  obtain ⟨a, ha⟩ := hres b'
  rw [Finsupp.sub_apply, h0, sub_zero] at ha
  exact Finsupp.mem_support_iff.1 hb' (laurent_eq_zero_of_invert_eq (hinv b') ha)

end Strings

/-! ### `f̃ᵢⁿ` on `B(∞)` -/

section Crystal

omit [Finite I] in
lemma kE_pow_kF_pow_self (i : I) (n : ℕ) (y : Um D 𝕧) :
    (kE hvt i ^ n) ((kF hvt i ^ n) y) = y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ', Module.End.mul_apply, Module.End.mul_apply, kE_kF, ih]

/-- `f̃_{iⁿu} 1 ≡ f̃_{iⁿu'} 1` implies `f̃_u 1 ≡ f̃_{u'} 1` modulo `v⁻¹L(∞)`. -/
lemma fWi_sub_mem_of_replicate (i : I) (n : ℕ) {u u' : List I}
    (h : fWi (D := D) hvt (List.replicate n i ++ u) - fWi hvt (List.replicate n i ++ u') ∈
      ϖ • latInf (D := D) hvt A) :
    fWi (D := D) hvt u - fWi hvt u' ∈ ϖ • latInf (D := D) hvt A := by
  have := kE_pow_mem_smul_latInf_ratFunc D i n h
  rwa [← kF_pow_fWi, ← kF_pow_fWi, ← map_sub, kE_pow_kF_pow_self] at this

omit [Finite I] in
/-- `f̃_u 1 ≡ f̃_{u'} 1` implies `f̃_{iⁿu} 1 ≡ f̃_{iⁿu'} 1` modulo `v⁻¹L(∞)`. -/
lemma fWi_replicate_sub_mem (i : I) (n : ℕ) {u u' : List I}
    (h : fWi (D := D) hvt u - fWi hvt u' ∈ ϖ • latInf (D := D) hvt A) :
    fWi (D := D) hvt (List.replicate n i ++ u) - fWi hvt (List.replicate n i ++ u') ∈
      ϖ • latInf (D := D) hvt A := by
  have := kF_pow_mem_smul_latInf D i n h
  rwa [map_sub, kF_pow_fWi, kF_pow_fWi] at this

omit [Finite I] in
/-- `f̃_{w} 1 ≡ f̃_{iⁿ w'} 1` for the class `f̃ᵢⁿ b` and a word `w'` of `b`. -/
lemma fWi_out_negCrystalF_sub_mem (i : I) (n : ℕ) {ν : I →₀ ℕ} (b : negCrystal D ν) :
    fWi (D := D) hvt (Quotient.out (negCrystalF D i n b)).1 -
      fWi hvt (List.replicate n i ++ (Quotient.out b).1) ∈ ϖ • latInf (D := D) hvt A :=
  Quotient.mk_out (s := negCrystalSetoid D (ν + Finsupp.single i n)) _

/-- `f̃ᵢⁿ` is injective on `B(∞)`. -/
lemma negCrystalF_injective (i : I) (n : ℕ) (ν : I →₀ ℕ) :
    Function.Injective (negCrystalF D i n (ν := ν)) := by
  intro b₁ b₂ h
  rw [← Quotient.out_eq b₁, ← Quotient.out_eq b₂]
  refine Quotient.sound (fWi_sub_mem_of_replicate D i n ?_)
  exact Quotient.exact h

/-- If `εᵢ(b) = 0`, then `εᵢ(f̃ᵢⁿ b) = n`. -/
lemma not_negDepthGe_negCrystalF {i : I} (n : ℕ) {ν : I →₀ ℕ} {b : negCrystal D ν}
    (hb : ¬ NegDepthGe D i 1 b) : ¬ NegDepthGe D i (n + 1) (negCrystalF D i n b) := by
  rintro ⟨u, hu⟩
  refine hb ⟨u, fWi_sub_mem_of_replicate D i n ?_⟩
  have e : fWi (D := D) hvt (List.replicate n i ++ (Quotient.out b).1) -
      fWi hvt (List.replicate n i ++ (List.replicate 1 i ++ u)) =
      (fWi hvt (Quotient.out (negCrystalF D i n b)).1 -
        fWi hvt (List.replicate (n + 1) i ++ u)) -
      (fWi hvt (Quotient.out (negCrystalF D i n b)).1 -
        fWi hvt (List.replicate n i ++ (Quotient.out b).1)) := by
    rw [← List.append_assoc, ← List.replicate_add]
    abel
  rw [e]
  exact sub_mem hu (fWi_out_negCrystalF_sub_mem D i n b)

/-- Every `c ∈ B(∞)` with `εᵢ(c) = n` is `f̃ᵢⁿ b` for some `b` with `εᵢ(b) = 0`. -/
lemma exists_negCrystalF_eq {i : I} {n : ℕ} {μ : I →₀ ℕ} {c : negCrystal D μ}
    (hn : NegDepthGe D i n c) (hn' : ¬ NegDepthGe D i (n + 1) c) :
    ∃ (ν : I →₀ ℕ) (b : negCrystal D ν) (h : ν + Finsupp.single i n = μ),
      ¬ NegDepthGe D i 1 b ∧ h ▸ negCrystalF D i n b = c := by
  obtain ⟨u, hu⟩ := hn
  set b : negCrystal D (wordWeight u) := Quotient.mk _ ⟨u, rfl⟩
  have hbu : fWi (D := D) hvt (Quotient.out b).1 - fWi hvt u ∈ ϖ • latInf (D := D) hvt A :=
    Quotient.mk_out (s := negCrystalSetoid D (wordWeight u)) _
  have hμ : wordWeight u + Finsupp.single i n = μ := by
    rw [← wordWeight_replicate_append, ← (Quotient.out c).2]
    exact (wordWeight_eq_of_sub_mem_ratFunc D hu).symm
  -- `f̃_{w} 1 ≡ f̃_{iⁿ w'} 1` for the words `w` of `c` and `w'` of `b`
  have hcb : fWi (D := D) hvt (Quotient.out c).1 -
      fWi hvt (List.replicate n i ++ (Quotient.out b).1) ∈ ϖ • latInf (D := D) hvt A := by
    have h := fWi_replicate_sub_mem D i n hbu
    rw [← sub_sub_sub_cancel_right _ _ (fWi hvt (List.replicate n i ++ u))]
    exact sub_mem hu h
  refine ⟨wordWeight u, b, hμ, fun ⟨u', hu'⟩ ↦ hn' ⟨u', ?_⟩, ?_⟩
  · have h := fWi_replicate_sub_mem D i n hu'
    rw [← List.append_assoc, ← List.replicate_add] at h
    rw [← sub_add_sub_cancel _ (fWi hvt (List.replicate n i ++ (Quotient.out b).1))]
    exact add_mem hcb h
  · subst hμ
    exact (eq_mk_of_sub_mem D _ hcb).symm

end Crystal

/-! ### [Lus] 14.3.2 (c) -/

section Bijection

lemma negGlobal_ne_zero {ν : I →₀ ℕ} (b : negCrystal D ν) : negGlobal D ν b ≠ 0 := fun h ↦
  negGlobal_notMem D ν b (h ▸ zero_mem _)

lemma negGlobal_ne_neg {ν : I →₀ ℕ} (b : negCrystal D ν) : negGlobal D ν b ≠ -negGlobal D ν b := by
  intro h
  have h2 : (2 : 𝕂) • negGlobal D ν b = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    exact neg_add_cancel _
  exact negGlobal_ne_zero D b ((smul_eq_zero.1 h2).resolve_left two_ne_zero)

lemma signed_mem_Uw {ν : I →₀ ℕ} {b : negCrystal D ν} {y : Um D 𝕧}
    (hy : y = negGlobal D ν b ∨ y = -negGlobal D ν b) : y ∈ Uw D 𝕧 ν := by
  rcases hy with rfl | rfl
  · exact (negGlobal_mem D ν b).2.1
  · exact neg_mem (negGlobal_mem D ν b).2.1

lemma signed_mem_span {ν : I →₀ ℕ} {b : negCrystal D ν} {S : Set (negCrystal D ν)} (hb : b ∈ S)
    {y : Um D 𝕧} (hy : y = negGlobal D ν b ∨ y = -negGlobal D ν b) :
    y ∈ Submodule.span (LaurentPolynomial ℤ) (negGlobal D ν '' S) := by
  rcases hy with rfl | rfl
  · exact Submodule.subset_span ⟨b, hb, rfl⟩
  · exact neg_mem (Submodule.subset_span ⟨b, hb, rfl⟩)

/-- `±G(b) = ±G(b')` forces equal weights, `b = b'` and equal signs. -/
lemma signed_eq_signed {μ₁ μ₂ : I →₀ ℕ} {c₁ : negCrystal D μ₁} {c₂ : negCrystal D μ₂}
    {y : Um D 𝕧} (h₁ : y = negGlobal D μ₁ c₁ ∨ y = -negGlobal D μ₁ c₁)
    (h₂ : y = negGlobal D μ₂ c₂ ∨ y = -negGlobal D μ₂ c₂) :
    ∃ h : μ₁ = μ₂, h ▸ c₁ = c₂ := by
  have hy0 : y ≠ 0 := by
    rcases h₁ with rfl | rfl
    · exact negGlobal_ne_zero D c₁
    · exact neg_ne_zero.2 (negGlobal_ne_zero D c₁)
  have hμ : μ₁ = μ₂ := by
    by_contra hμ
    have e₁ := proj_of_mem_Uw (signed_mem_Uw D h₁) (toZ μ₁)
    rw [proj_of_mem_Uw (signed_mem_Uw D h₂), ite_eq_left rfl,
      ite_eq_right fun e ↦ hμ (LusztigF.toZ_injective e).symm] at e₁
    exact hy0 e₁.symm
  subst hμ
  have hc : c₁ = c₂ := by
    by_contra hc
    have hd := (linearIndependent_negGlobal_laurent D μ₁).disjoint_span_image
      (s := {c₁}) (t := {c₂}) (Set.disjoint_singleton.2 hc)
    exact hy0 ((Submodule.disjoint_def.1 hd) y (signed_mem_span D (Set.mem_singleton _) h₁)
      (signed_mem_span D (Set.mem_singleton _) h₂))
  exact ⟨rfl, hc⟩

/-- The `μ`-component of an `𝒜`-combination of elements of `𝐁_{i;≥m}` is an `𝒜`-combination of
the `G(b)`, `b ∈ B(∞)_μ`, with `εᵢ(b) ≥ m`. -/
lemma proj_mem_span_of_mem_span_signedBasisGe {i : I} {m : ℕ} {x : Um D 𝕧}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (signedBasisGe D i m)) (μ : I →₀ ℕ) :
    NegativePart.proj D 𝕧 (toZ μ) x ∈
      Submodule.span (LaurentPolynomial ℤ) (negGlobal D μ '' {b | NegDepthGe D i m b}) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ν, b, hb, hx⟩ := (mem_signedBasisGe_iff D).1 hx
    rw [proj_of_mem_Uw (signed_mem_Uw D hx)]
    split_ifs with h
    · obtain rfl := LusztigF.toZ_injective h
      exact signed_mem_span D hb hx
    · exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [laurent_smul_eq, map_smul, ← laurent_smul_eq]
    exact Submodule.smul_mem _ _ hx

/-- Two elements of `𝐁_{i;n}` whose difference is an `𝒜`-combination of elements of
`𝐁_{i;≥n+1}` are equal. -/
theorem eq_of_sub_mem_span_signedBasisGe {i : I} {n : ℕ} {y₁ y₂ : Um D 𝕧}
    (h₁ : y₁ ∈ signedBasisAt D i n) (h₂ : y₂ ∈ signedBasisAt D i n)
    (h : y₁ - y₂ ∈ Submodule.span (LaurentPolynomial ℤ) (signedBasisGe D i (n + 1))) :
    y₁ = y₂ := by
  obtain ⟨μ₁, c₁, -, hc₁, hy₁⟩ := (mem_signedBasisAt_iff D).1 h₁
  obtain ⟨μ₂, c₂, -, hc₂, hy₂⟩ := (mem_signedBasisAt_iff D).1 h₂
  have hp := proj_mem_span_of_mem_span_signedBasisGe D h μ₁
  rw [map_sub, proj_of_mem_Uw (signed_mem_Uw D hy₁), proj_of_mem_Uw (signed_mem_Uw D hy₂),
    ite_eq_left rfl] at hp
  have hlin := linearIndependent_negGlobal_laurent D μ₁
  by_cases hμ : toZ μ₂ = toZ μ₁
  · obtain rfl := LusztigF.toZ_injective hμ
    rw [ite_eq_left rfl] at hp
    have hd := hlin.disjoint_span_image (s := {c₁, c₂}) (t := {b | NegDepthGe D i (n + 1) b})
      (by
        rw [Set.disjoint_left]
        rintro c (rfl | rfl)
        exacts [hc₁, hc₂])
    exact sub_eq_zero.1 ((Submodule.disjoint_def.1 hd) _
      (sub_mem (signed_mem_span D (by simp) hy₁) (signed_mem_span D (by simp) hy₂)) hp)
  · rw [ite_eq_right fun e ↦ hμ e, sub_zero] at hp
    have hd := hlin.disjoint_span_image (s := {c₁}) (t := {b | NegDepthGe D i (n + 1) b})
      (Set.disjoint_singleton_left.2 hc₁)
    have h0 := (Submodule.disjoint_def.1 hd) _ (signed_mem_span D (Set.mem_singleton _) hy₁) hp
    rcases hy₁ with rfl | rfl
    · exact absurd h0 (negGlobal_ne_zero D c₁)
    · exact absurd h0 (neg_ne_zero.2 (negGlobal_ne_zero D c₁))

lemma span_negGlobal_le_span_signedBasisGe (i : I) (m : ℕ) (μ : I →₀ ℕ) :
    Submodule.span (LaurentPolynomial ℤ) (negGlobal D μ '' {b | NegDepthGe D i m b}) ≤
      Submodule.span (LaurentPolynomial ℤ) (signedBasisGe D i m) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨b, hb, rfl⟩
  exact (mem_signedBasisGe_iff D).2 ⟨μ, b, hb, Or.inl rfl⟩

/-- For `b` with `εᵢ(b) = 0`: `θᵢ^{(n)}(±G(b))` is `±G(f̃ᵢⁿ b)` plus an `𝒜`-combination of elements
of `𝐁_{i;≥n+1}`. -/
lemma df_signed_sub_mem_span {i : I} (n : ℕ) {ν : I →₀ ℕ} {b : negCrystal D ν}
    (hb : ¬ NegDepthGe D i 1 b) {x y : Um D 𝕧}
    (hxy : (x = negGlobal D ν b ∧ y = negGlobal D _ (negCrystalF D i n b)) ∨
      (x = -negGlobal D ν b ∧ y = -negGlobal D _ (negCrystalF D i n b))) :
    (bosv i).df n x - y ∈ Submodule.span (LaurentPolynomial ℤ) (signedBasisGe D i (n + 1)) := by
  have h := span_negGlobal_le_span_signedBasisGe D i (n + 1) (ν + Finsupp.single i n)
    (df_negGlobal_sub_mem_span D n hb)
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · rw [map_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub]
    exact neg_mem h

/-- **[Lus] Thm. 14.3.2 (c)**: for `x ∈ 𝐁_{i;0}` there is a unique `y ∈ 𝐁_{i;n}` such that
`θᵢ^{(n)} x - y` is an `𝒜`-linear combination of elements of `𝐁_{i;≥n+1}`. -/
theorem existsUnique_df_sub_mem_span {i : I} (n : ℕ) {x : Um D 𝕧}
    (hx : x ∈ signedBasisAt D i 0) :
    ∃! y, y ∈ signedBasisAt D i n ∧
      (bosv i).df n x - y ∈ Submodule.span (LaurentPolynomial ℤ) (signedBasisGe D i (n + 1)) := by
  obtain ⟨ν, b, -, hb, hx⟩ := (mem_signedBasisAt_iff D).1 hx
  have hy : ∀ y, (y = negGlobal D _ (negCrystalF D i n b) ∨
      y = -negGlobal D _ (negCrystalF D i n b)) → y ∈ signedBasisAt D i n := fun y hy ↦
    (mem_signedBasisAt_iff D).2 ⟨_, negCrystalF D i n b, negDepthGe_negCrystalF D i n b,
      not_negDepthGe_negCrystalF D n hb, hy⟩
  obtain ⟨y, hy⟩ : ∃ y, y ∈ signedBasisAt D i n ∧ (bosv i).df n x - y ∈
      Submodule.span (LaurentPolynomial ℤ) (signedBasisGe D i (n + 1)) := by
    rcases hx with rfl | rfl
    · exact ⟨_, hy _ (Or.inl rfl), df_signed_sub_mem_span D n hb (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨_, hy _ (Or.inr rfl), df_signed_sub_mem_span D n hb (Or.inr ⟨rfl, rfl⟩)⟩
  refine ⟨y, hy, fun y' hy' ↦ eq_of_sub_mem_span_signedBasisGe D hy'.1 hy.1 ?_⟩
  have := sub_mem hy.2 hy'.2
  rwa [sub_sub_sub_cancel_left] at this

/-- **[Lus] 14.3.2 (c)**: the map `π_{i,n} : 𝐁_{i;0} → 𝐁_{i;n}`, `x ↦ y` with
`θᵢ^{(n)} x - y` an `𝒜`-linear combination of elements of `𝐁_{i;≥n+1}`. -/
def signedStringMap (i : I) (n : ℕ) : signedBasisAt D i 0 → signedBasisAt D i n := fun x ↦
  ⟨(existsUnique_df_sub_mem_span D n x.2).exists.choose,
    (existsUnique_df_sub_mem_span D n x.2).exists.choose_spec.1⟩

lemma df_sub_signedStringMap_mem_span (i : I) (n : ℕ) (x : signedBasisAt D i 0) :
    (bosv i).df n x - signedStringMap D i n x ∈
      Submodule.span (LaurentPolynomial ℤ) (signedBasisGe D i (n + 1)) :=
  (existsUnique_df_sub_mem_span D n x.2).exists.choose_spec.2

lemma signedStringMap_eq {i : I} {n : ℕ} (x : signedBasisAt D i 0) {y : Um D 𝕧}
    (hy : y ∈ signedBasisAt D i n)
    (h : (bosv i).df n x - y ∈ Submodule.span (LaurentPolynomial ℤ) (signedBasisGe D i (n + 1))) :
    (signedStringMap D i n x : Um D 𝕧) = y :=
  (existsUnique_df_sub_mem_span D n x.2).unique
    ⟨(signedStringMap D i n x).2, df_sub_signedStringMap_mem_span D i n x⟩ ⟨hy, h⟩

/-- `π_{i,n}(±G(b)) = ±G(f̃ᵢⁿ b)`. -/
lemma signedStringMap_signed {i : I} {n : ℕ} (x : signedBasisAt D i 0) {ν : I →₀ ℕ}
    {b : negCrystal D ν} (hb : ¬ NegDepthGe D i 1 b) {y : Um D 𝕧}
    (hxy : ((x : Um D 𝕧) = negGlobal D ν b ∧ y = negGlobal D _ (negCrystalF D i n b)) ∨
      ((x : Um D 𝕧) = -negGlobal D ν b ∧ y = -negGlobal D _ (negCrystalF D i n b))) :
    (signedStringMap D i n x : Um D 𝕧) = y := by
  refine signedStringMap_eq D x ((mem_signedBasisAt_iff D).2 ⟨_, negCrystalF D i n b,
    negDepthGe_negCrystalF D i n b, not_negDepthGe_negCrystalF D n hb, ?_⟩)
    (df_signed_sub_mem_span D n hb hxy)
  rcases hxy with ⟨-, rfl⟩ | ⟨-, rfl⟩
  exacts [Or.inl rfl, Or.inr rfl]

/-- **[Lus] Thm. 14.3.2 (c)**: `π_{i,n} : 𝐁_{i;0} → 𝐁_{i;n}` is a bijection. -/
theorem signedStringMap_bijective (i : I) (n : ℕ) : Function.Bijective (signedStringMap D i n) := by
  refine ⟨fun x₁ x₂ h ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨ν₁, b₁, -, hb₁, hx₁⟩ := (mem_signedBasisAt_iff D).1 x₁.2
    obtain ⟨ν₂, b₂, -, hb₂, hx₂⟩ := (mem_signedBasisAt_iff D).1 x₂.2
    have e₁ : ∀ y, ((x₁ : Um D 𝕧) = negGlobal D ν₁ b₁ ∧ y = negGlobal D _ (negCrystalF D i n b₁)) ∨
        ((x₁ : Um D 𝕧) = -negGlobal D ν₁ b₁ ∧ y = -negGlobal D _ (negCrystalF D i n b₁)) →
        (signedStringMap D i n x₁ : Um D 𝕧) = y := fun y ↦ signedStringMap_signed D x₁ hb₁
    have e₂ : ∀ y, ((x₂ : Um D 𝕧) = negGlobal D ν₂ b₂ ∧ y = negGlobal D _ (negCrystalF D i n b₂)) ∨
        ((x₂ : Um D 𝕧) = -negGlobal D ν₂ b₂ ∧ y = -negGlobal D _ (negCrystalF D i n b₂)) →
        (signedStringMap D i n x₂ : Um D 𝕧) = y := fun y ↦ signedStringMap_signed D x₂ hb₂
    have h' : (signedStringMap D i n x₁ : Um D 𝕧) = signedStringMap D i n x₂ := by rw [h]
    have hy₁ : (signedStringMap D i n x₁ : Um D 𝕧) = negGlobal D _ (negCrystalF D i n b₁) ∨
        (signedStringMap D i n x₁ : Um D 𝕧) = -negGlobal D _ (negCrystalF D i n b₁) := by
      rcases hx₁ with hx₁ | hx₁
      · exact Or.inl (e₁ _ (Or.inl ⟨hx₁, rfl⟩))
      · exact Or.inr (e₁ _ (Or.inr ⟨hx₁, rfl⟩))
    have hy₂ : (signedStringMap D i n x₁ : Um D 𝕧) = negGlobal D _ (negCrystalF D i n b₂) ∨
        (signedStringMap D i n x₁ : Um D 𝕧) = -negGlobal D _ (negCrystalF D i n b₂) := by
      rw [h']
      rcases hx₂ with hx₂ | hx₂
      · exact Or.inl (e₂ _ (Or.inl ⟨hx₂, rfl⟩))
      · exact Or.inr (e₂ _ (Or.inr ⟨hx₂, rfl⟩))
    obtain ⟨hμ, hc⟩ := signed_eq_signed D hy₁ hy₂
    obtain rfl := add_right_cancel hμ
    obtain rfl := negCrystalF_injective D i n ν₁ hc
    apply Subtype.ext
    rcases hx₁ with hx₁ | hx₁ <;> rcases hx₂ with hx₂ | hx₂
    · rw [hx₁, hx₂]
    · have a₁ := e₁ _ (Or.inl ⟨hx₁, rfl⟩)
      have a₂ := e₂ _ (Or.inr ⟨hx₂, rfl⟩)
      rw [h', a₂] at a₁
      exact (negGlobal_ne_neg D _ a₁.symm).elim
    · have a₁ := e₁ _ (Or.inr ⟨hx₁, rfl⟩)
      have a₂ := e₂ _ (Or.inl ⟨hx₂, rfl⟩)
      rw [h', a₂] at a₁
      exact (negGlobal_ne_neg D _ a₁).elim
    · rw [hx₁, hx₂]
  · obtain ⟨μ, c, hcn, hcn', hy⟩ := (mem_signedBasisAt_iff D).1 y.2
    obtain ⟨ν, b, hμ, hb, hc⟩ := exists_negCrystalF_eq D hcn hcn'
    subst hμ
    subst hc
    rcases hy with hy | hy
    · exact ⟨⟨_, (mem_signedBasisAt_iff D).2 ⟨ν, b, negDepthGe_zero D i b, hb, Or.inl rfl⟩⟩,
        Subtype.ext (signedStringMap_signed D _ hb (Or.inl ⟨rfl, hy⟩))⟩
    · exact ⟨⟨_, (mem_signedBasisAt_iff D).2 ⟨ν, b, negDepthGe_zero D i b, hb, Or.inr rfl⟩⟩,
        Subtype.ext (signedStringMap_signed D _ hb (Or.inr ⟨rfl, hy⟩))⟩

end Bijection

end LieLean.QuantumGroup
