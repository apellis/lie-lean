/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.SignedBijection

/-!
# The canonical basis `B` of `f`

This file defines Lusztig's canonical basis `B = ⊔_ν B_ν` of `f ≅ U⁻` by his choice of signs in
the signed basis `𝐁 = {±G(b)}` ([Lus] 14.4.2). It proves that `B_ν` is exactly Kashiwara's
global basis `{G(b) | b ∈ B(∞)_ν}`, and deduces [Lus] 14.3.3 and Thm. 14.4.3.

## Main definitions

* `IsCanonicalAt D ν`, `canonicalBasisAt D ν`: Lusztig's `B_ν` ([Lus] 14.4.2). It is defined
  inductively by `1 ∈ B_0` and `π_{i,n}(B_ν ∩ 𝐁_{i;0}) ⊆ B_{ν+ni}` for `n > 0`, which is
  equivalent to Lusztig's definition by induction on `tr ν` (`mem_canonicalBasisAt_iff`).
* `canonicalBasis D`: the canonical basis `B = ⊔_ν B_ν` ([Lus] 14.4.6).

## Main results

* `canonicalBasisAt_eq_range`, `mem_canonicalBasis_iff`: `B_ν = {G(b) | b ∈ B(∞)_ν}`, so
  `B = {G(b)}`. Later results about `B` only use this identification.
* `signedBasis_diff_eq_iUnion`: [Lus] 14.3.3, `𝐁 - {±1} = ⋃_{i, n > 0} 𝐁_{i;n}`.
* `signedBasis_eq_union`: `𝐁 = B ∪ (-B)` ([Lus] 14.4.2).
* [Lus] Thm. 14.4.3: (a) `canonicalBasisAt_inter_neg`, (b) `canonicalBasisAt_inter_neg_starU`,
  (c) `starU_image_canonicalBasisAt`, (d) `linearIndependent_canonicalBasis(_laurent)`,
  `span_canonicalBasis(_laurent)`, (e) `linearIndependent_canonicalBasisAt(_laurent)`,
  `span_canonicalBasisAt(_laurent)`.

## Implementation notes

Lusztig proves Thm. 14.4.3 geometrically in the symmetric case (14.4.4) and in general in 19.2.3.
Here the proofs are our own. Using `π_{i,n}(G(b)) = G(f̃ᵢⁿ b)` (`signedStringMap_signed`), an
induction on `tr ν` shows `B_ν = {G(b) | b ∈ B(∞)_ν}`: every `b ∈ B(∞)_ν` with `ν ≠ 0` is
`f̃ᵢⁿ b'` with `n = εᵢ(b) > 0` and `εᵢ(b') = 0`. Part (c) uses `B(∞)* = B(∞)` ([Kas93a]
Thm. 2.1.1, `GrandLoop.starU_fWi_sub_mem`) and the `*`-stability of the balanced triple. In
Lusztig's notation `σ` is the anti-automorphism `starU` of `U⁻ ≅ f`, and `1 ∈ f` is `f̃_∅ 1`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 14.3.3, 14.4.2–14.4.6.
* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, §7.
* [Kas93a] M. Kashiwara, *The crystal base and Littelmann's refined Demazure character formula*,
  Duke Math. J. 71 (1993), 839–858, Thm. 2.1.1.
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

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I : Type u} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-! ### Weight zero and the depth of `b` -/

section Depth

omit [Finite I] [DecidableEq I] in
lemma eq_nil_of_wordWeight_eq_zero {w : List I} (hw : wordWeight w = 0) : w = [] := by
  cases w with
  | nil => rfl
  | cons i w =>
    have := congrArg (· i) hw
    simp [LusztigF.wordWeight_cons] at this

/-- `G(b) = 1` for the unique `b ∈ B(∞)_0`; here `1 = f̃_∅ 1` is the unit of `U⁻ ≅ f`. -/
lemma negGlobal_zero (b : negCrystal D 0) : negGlobal D 0 b = fWi hvt [] := by
  have hb : b = Quotient.mk _ ⟨[], rfl⟩ := by
    rw [← Quotient.out_eq b]
    congr 1
    exact Subtype.ext (eq_nil_of_wordWeight_eq_zero (Quotient.out b).2)
  have hy : fWi (D := D) hvt [] ∈ negBalanced D 0 := by
    refine ⟨fWi_mem_negIntegral D [], fWi_mem_Uw [], NegativePart.fWord_mem_latticeInf _ _ [], ?_⟩
    rw [mem_latInfBar_iff, negBar_fWi_nil]
    exact NegativePart.fWord_mem_latticeInf _ _ []
  rw [hb]
  exact (negGlobal_eq_of_sub_mem D hy rfl (by rw [sub_self]; exact zero_mem _)).symm

/-- If `εᵢ(b) ≥ m` for `b ∈ B(∞)_ν`, then `m ≤ νᵢ`. -/
lemma le_of_negDepthGe {i : I} {m : ℕ} {ν : I →₀ ℕ} {b : negCrystal D ν}
    (hb : NegDepthGe D i m b) : m ≤ ν i := by
  obtain ⟨u, hu⟩ := hb
  have h := wordWeight_eq_of_sub_mem_ratFunc D hu
  rw [(Quotient.out b).2, LusztigF.wordWeight_append, LusztigF.wordWeight_replicate] at h
  rw [h]
  simp

/-- Every `b ∈ B(∞)_ν`, `ν ≠ 0`, has `εᵢ(b) = n > 0` for some `i`. -/
lemma exists_negDepth {ν : I →₀ ℕ} (hν : ν ≠ 0) (b : negCrystal D ν) :
    ∃ i n, 0 < n ∧ NegDepthGe D i n b ∧ ¬ NegDepthGe D i (n + 1) b := by
  classical
  cases hcw : (Quotient.out b).1 with
  | nil =>
    exact absurd (by rw [← (Quotient.out b).2, hcw]; rfl) hν
  | cons i w =>
    have h1 : NegDepthGe D i 1 b := by
      refine ⟨w, ?_⟩
      rw [hcw, List.replicate_one, List.singleton_append, sub_self]
      exact zero_mem _
    have hle := le_of_negDepthGe D h1
    refine ⟨i, Nat.findGreatest (fun m ↦ NegDepthGe D i m b) (ν i), ?_,
      Nat.findGreatest_spec (P := fun m ↦ NegDepthGe D i m b) hle h1, fun h ↦ ?_⟩
    · exact Nat.lt_of_lt_of_le one_pos (Nat.le_findGreatest hle h1)
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (le_of_negDepthGe D h) h

end Depth

/-! ### [Lus] 14.3.3 -/

section Subsets

/-- **[Lus] 14.3.3**: `𝐁 - {±1} = ⋃_{i, n > 0} 𝐁_{i;n}`. -/
theorem signedBasis_diff_eq_iUnion :
    signedBasis D \ {fWi hvt [], -fWi hvt []} =
      ⋃ (i : I) (n : ℕ) (_ : 0 < n), signedBasisAt D i n := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_iUnion,
    exists_prop]
  constructor
  · rintro ⟨hx, hx1⟩
    obtain ⟨ν, b, hx⟩ := (mem_signedBasis_iff D).1 hx
    have hν : ν ≠ 0 := by
      rintro rfl
      rcases hx with rfl | rfl <;> rw [negGlobal_zero] at hx1 <;> simp at hx1
    obtain ⟨i, n, hn, hb, hb'⟩ := exists_negDepth D hν b
    exact ⟨i, n, hn, (mem_signedBasisAt_iff D).2 ⟨ν, b, hb, hb', hx⟩⟩
  · rintro ⟨i, n, hn, hx⟩
    obtain ⟨ν, b, hb, -, hx⟩ := (mem_signedBasisAt_iff D).1 hx
    refine ⟨(mem_signedBasis_iff D).2 ⟨ν, b, hx⟩, fun h1 ↦ ?_⟩
    have hν : 0 < ν i := Nat.lt_of_lt_of_le hn (le_of_negDepthGe D hb)
    have h0 : x = negGlobal D 0 (Quotient.mk _ ⟨[], rfl⟩) ∨
        x = -negGlobal D 0 (Quotient.mk _ ⟨[], rfl⟩) := by
      rw [negGlobal_zero]
      exact h1
    obtain ⟨h, -⟩ := signed_eq_signed D hx h0
    rw [h] at hν
    exact (lt_irrefl 0) hν

end Subsets

/-! ### [Lus] 14.4.2: the subsets `B_ν` -/

section Canonical

/-- **[Lus] 14.4.2**: `IsCanonicalAt D ν x` means `x ∈ B_ν`. The sets `B_ν ⊆ 𝐁_ν` are the least
family with `1 ∈ B_0` and `π_{i,n}(B_ν ∩ 𝐁_{i;0}) ⊆ B_{ν+ni}` for `n > 0`; this is Lusztig's
definition by induction on `tr ν` (`mem_canonicalBasisAt_iff`). -/
inductive IsCanonicalAt : (I →₀ ℕ) → Um D 𝕧 → Prop
  | one : IsCanonicalAt 0 (fWi hvt [])
  | step {ν : I →₀ ℕ} {i : I} {n : ℕ} (hn : 0 < n) (x : signedBasisAt D i 0)
      (hx : IsCanonicalAt ν x) :
      IsCanonicalAt (ν + Finsupp.single i n) (signedStringMap D i n x)

/-- **[Lus] 14.4.2**: the subset `B_ν` of `𝐁_ν`. -/
def canonicalBasisAt (ν : I →₀ ℕ) : Set (Um D 𝕧) := {x | IsCanonicalAt D ν x}

/-- **[Lus] 14.4.2, 14.4.6**: the canonical basis `B = ⊔_ν B_ν` of `f`. -/
def canonicalBasis : Set (Um D 𝕧) := ⋃ ν, canonicalBasisAt D ν

/-- **[Lus] 14.4.2**: `B_0 = {1}`, and for `ν ≠ 0`, `B_ν` is the union of the
`π_{i,n}(B_{ν-ni} ∩ 𝐁_{i;0})` over `i ∈ I` and `0 < n ≤ νᵢ`. -/
theorem mem_canonicalBasisAt_iff {ν : I →₀ ℕ} {x : Um D 𝕧} :
    x ∈ canonicalBasisAt D ν ↔ (ν = 0 ∧ x = fWi hvt []) ∨
      ∃ (i : I) (n : ℕ) (_ : 0 < n ∧ n ≤ ν i) (y : signedBasisAt D i 0),
        (y : Um D 𝕧) ∈ canonicalBasisAt D (ν - Finsupp.single i n) ∧
          x = signedStringMap D i n y := by
  constructor
  · rintro (_ | @⟨ν, i, n, hn, y, hy⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · refine Or.inr ⟨i, n, ⟨hn, by simp⟩, y, ?_, rfl⟩
      change IsCanonicalAt D _ _
      rwa [add_tsub_cancel_right]
  · rintro (⟨rfl, rfl⟩ | ⟨i, n, ⟨hn, hnν⟩, y, hy, rfl⟩)
    · exact IsCanonicalAt.one
    · have h := IsCanonicalAt.step hn y hy
      rwa [tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hnν)] at h

/-- `x ∈ 𝐁_{i;0}` is not in `fᵢU⁻`. -/
lemma not_negDepthGe_of_mem_signedBasisAt_zero {i : I} {ν : I →₀ ℕ} {b : negCrystal D ν}
    (h : negGlobal D ν b ∈ signedBasisAt D i 0) : ¬ NegDepthGe D i 1 b := by
  intro hb
  refine h.2 ⟨h.1.1, ?_⟩
  exact negFilt_le_range D i 1 ν (negGlobal_mem_negFilt D hb)

/-- **The isolating lemma**: Lusztig's `B_ν` is Kashiwara's global basis
`{G(b) | b ∈ B(∞)_ν}`. Our own proof, by induction on `tr ν`, using
`π_{i,n}(G(b)) = G(f̃ᵢⁿ b)` and the fact that every `b ∈ B(∞)_ν`, `ν ≠ 0`, is `f̃ᵢⁿ b'` with
`εᵢ(b') = 0` and `n > 0`. -/
theorem canonicalBasisAt_eq_range (ν : I →₀ ℕ) :
    canonicalBasisAt D ν = Set.range (negGlobal D ν) := by
  ext x
  constructor
  · intro hx
    induction hx with
    | one => exact ⟨Quotient.mk _ ⟨[], rfl⟩, negGlobal_zero D _⟩
    | @step ν i n hn y hy ih =>
      obtain ⟨b, hb⟩ := ih
      have hb0 := not_negDepthGe_of_mem_signedBasisAt_zero D (hb ▸ y.2)
      exact ⟨negCrystalF D i n b,
        (signedStringMap_signed D y hb0 (Or.inl ⟨hb.symm, rfl⟩)).symm⟩
  · rintro ⟨c, rfl⟩
    induction h : ν.degree using Nat.strong_induction_on generalizing ν with
    | _ d ih =>
      by_cases hν : ν = 0
      · subst hν
        rw [negGlobal_zero]
        exact IsCanonicalAt.one
      obtain ⟨i, n, hn, hc, hc'⟩ := exists_negDepth D hν c
      obtain ⟨ν', b, hμ, hb, rfl⟩ := exists_negCrystalF_eq D hc hc'
      subst hμ
      have hdeg : ν'.degree < d := by
        rw [← h, map_add, Finsupp.degree_single]
        omega
      have hy : negGlobal D ν' b ∈ signedBasisAt D i 0 :=
        (mem_signedBasisAt_iff D).2 ⟨ν', b, negDepthGe_zero D i b, hb, Or.inl rfl⟩
      have := IsCanonicalAt.step (D := D) hn ⟨_, hy⟩ (ih _ hdeg ν' b rfl)
      rwa [signedStringMap_signed D ⟨_, hy⟩ hb (Or.inl ⟨rfl, rfl⟩)] at this

/-- **The isolating lemma**, global form: `B = {G(b)}`. -/
theorem mem_canonicalBasis_iff {x : Um D 𝕧} :
    x ∈ canonicalBasis D ↔ ∃ (ν : I →₀ ℕ) (b : negCrystal D ν), x = negGlobal D ν b := by
  simp only [canonicalBasis, Set.mem_iUnion, canonicalBasisAt_eq_range, Set.mem_range,
    eq_comm]

/-- **[Lus] 14.4.2**: `𝐁 = B ∪ (-B)`. -/
theorem signedBasis_eq_union : signedBasis D = canonicalBasis D ∪ -canonicalBasis D := by
  ext x
  simp only [Set.mem_union, Set.mem_neg, mem_canonicalBasis_iff, mem_signedBasis_iff,
    neg_eq_iff_eq_neg]
  constructor
  · rintro ⟨ν, b, h | h⟩
    exacts [Or.inl ⟨ν, b, h⟩, Or.inr ⟨ν, b, h⟩]
  · rintro (⟨ν, b, h⟩ | ⟨ν, b, h⟩)
    exacts [⟨ν, b, Or.inl h⟩, ⟨ν, b, Or.inr h⟩]

end Canonical

/-! ### [Lus] Thm. 14.4.3 -/

section Theorem

/-- `σ(G(b)) = G(b')` for some `b' ∈ B(∞)_ν`. -/
lemma starU_negGlobal_mem_range {ν : I →₀ ℕ} (b : negCrystal D ν) :
    starU D 𝕧 (negGlobal D ν b) ∈ Set.range (negGlobal D ν) := by
  let := Fintype.ofFinite I
  obtain ⟨w', hw'⟩ := GrandLoop.starU_fWi_sub_mem (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum (D := D) (Quotient.out b).1
  have h1 : starU D 𝕧 (negGlobal D ν b) - starU D 𝕧 (fWi hvt (Quotient.out b).1) ∈
      ϖ • latInf (D := D) hvt A := by
    rw [← map_sub]
    exact starU_mem_smul_latInf' (negGlobal_sub_mem D ν b)
  have h2 : starU D 𝕧 (negGlobal D ν b) - fWi hvt w' ∈ ϖ • latInf (D := D) hvt A := by
    rw [← sub_add_sub_cancel _ (starU D 𝕧 (fWi hvt (Quotient.out b).1))]
    exact add_mem h1 hw'
  have hG := negGlobal_mem D ν b
  have hy : starU D 𝕧 (negGlobal D ν b) ∈ negBalanced D ν :=
    ⟨starU_mem_negIntegral hG.1, starU_mem_Uw hG.2.1,
      starU_mem_latInf (hR := D.isXRegular_extendedRootDatum)
        InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
        InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
        D.exists_fundamental_extendedRootDatum hG.2.2.1,
      starU_mem_latInfBar hG.2.2.2⟩
  have hw : wordWeight w' = ν := by
    by_contra hw
    have h3 := proj_mem_smul_latInf (toZ (wordWeight w')) h2
    rw [map_sub, proj_of_mem_Uw hy.2.1, proj_of_mem_Uw (fWi_mem_Uw w'), ite_eq_left rfl,
      ite_eq_right fun e ↦ hw (LusztigF.toZ_injective e).symm, zero_sub] at h3
    exact fWi_notMem_ratFunc D w' (by simpa using neg_mem h3)
  exact ⟨_, (negGlobal_eq_of_sub_mem D hy hw h2).symm⟩

/-- **[Lus] Thm. 14.4.3 (a)**: `B_ν ∩ (-B_ν) = ∅`. -/
theorem canonicalBasisAt_inter_neg (ν : I →₀ ℕ) :
    canonicalBasisAt D ν ∩ -canonicalBasisAt D ν = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hx'⟩
  rw [canonicalBasisAt_eq_range] at hx hx'
  obtain ⟨b, rfl⟩ := hx
  obtain ⟨b', hb'⟩ := Set.mem_neg.1 hx'
  have hb'' : negGlobal D ν b' = -negGlobal D ν b := hb'
  obtain ⟨h, hc⟩ := signed_eq_signed D (y := negGlobal D ν b') (Or.inl rfl) (Or.inr hb'')
  have hc' : b' = b := hc
  subst hc'
  exact negGlobal_ne_neg D b' hb''

/-- **[Lus] Thm. 14.4.3 (c)**: `σ(B_ν) = B_ν`. -/
theorem starU_image_canonicalBasisAt (ν : I →₀ ℕ) :
    starU D 𝕧 '' canonicalBasisAt D ν = canonicalBasisAt D ν := by
  rw [canonicalBasisAt_eq_range]
  refine Set.Subset.antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact starU_negGlobal_mem_range D b
  · obtain ⟨b, rfl⟩ := hx
    exact ⟨_, starU_negGlobal_mem_range D b, starU_starU _⟩

/-- **[Lus] Thm. 14.4.3 (b)**: `B_ν ∩ (-σ(B_ν)) = ∅`. -/
theorem canonicalBasisAt_inter_neg_starU (ν : I →₀ ℕ) :
    canonicalBasisAt D ν ∩ -(starU D 𝕧 '' canonicalBasisAt D ν) = ∅ := by
  rw [starU_image_canonicalBasisAt, canonicalBasisAt_inter_neg]

/-- **[Lus] Thm. 14.4.3 (e)**, over `ℚ(v)`: `B_ν` is linearly independent. -/
theorem linearIndependent_canonicalBasisAt (ν : I →₀ ℕ) :
    LinearIndependent 𝕂 (Subtype.val : canonicalBasisAt D ν → Um D 𝕧) := by
  rw [canonicalBasisAt_eq_range]
  exact (linearIndepOn_id_range_iff (linearIndependent_negGlobal D ν).injective).2
    (linearIndependent_negGlobal D ν)

/-- **[Lus] Thm. 14.4.3 (e)**, over `𝒜`: `B_ν` is linearly independent. -/
theorem linearIndependent_canonicalBasisAt_laurent (ν : I →₀ ℕ) :
    LinearIndependent (LaurentPolynomial ℤ) (Subtype.val : canonicalBasisAt D ν → Um D 𝕧) := by
  rw [canonicalBasisAt_eq_range]
  exact (linearIndepOn_id_range_iff (linearIndependent_negGlobal_laurent D ν).injective).2
    (linearIndependent_negGlobal_laurent D ν)

/-- **[Lus] Thm. 14.4.3 (e)**, over `ℚ(v)`: `B_ν` spans `f_ν`. -/
theorem span_canonicalBasisAt (ν : I →₀ ℕ) :
    Submodule.span 𝕂 (canonicalBasisAt D ν) = Uw D 𝕧 ν := by
  rw [canonicalBasisAt_eq_range]
  refine le_antisymm (Submodule.span_le.2 ?_) fun x hx ↦ mem_span_negGlobal_field D hx
  rintro _ ⟨b, rfl⟩
  exact (negGlobal_mem D ν b).2.1

/-- **[Lus] Thm. 14.4.3 (e)**, over `𝒜`: `B_ν` spans `𝒜f_ν`. -/
theorem span_canonicalBasisAt_laurent (ν : I →₀ ℕ) :
    Submodule.span (LaurentPolynomial ℤ) (canonicalBasisAt D ν) = negIntegralWeight D ν := by
  rw [canonicalBasisAt_eq_range]
  refine le_antisymm (Submodule.span_le.2 ?_) fun x hx ↦ mem_span_negGlobal D hx.1 hx.2
  rintro _ ⟨b, rfl⟩
  exact ⟨(negGlobal_mem D ν b).1, (negGlobal_mem D ν b).2.1⟩

/-- The family of all `G(b)`, `b ∈ B(∞)`, is linearly independent over `ℚ(v)`. -/
theorem linearIndependent_negGlobal_sigma :
    LinearIndependent 𝕂 fun p : Σ ν, negCrystal D ν ↦ negGlobal D p.1 p.2 := by
  rw [linearIndependent_iff']
  intro s g hg ⟨ν, b⟩ hp
  have h := congrArg (NegativePart.proj D 𝕧 (LusztigF.toZ ν)) hg
  rw [map_sum, map_zero] at h
  have e : ∀ q ∈ s, NegativePart.proj D 𝕧 (LusztigF.toZ ν) (g q • negGlobal D q.1 q.2) =
      if q.1 = ν then g q • negGlobal D q.1 q.2 else 0 := by
    intro q _
    rw [map_smul, proj_of_mem_Uw (negGlobal_mem D q.1 q.2).2.1]
    by_cases hq : q.1 = ν
    · rw [ite_eq_left (congrArg LusztigF.toZ hq), ite_eq_left hq]
    · rw [ite_eq_right fun e ↦ hq (LusztigF.toZ_injective e), ite_eq_right hq, smul_zero]
  rw [Finset.sum_congr rfl e] at h
  rw [← Finset.sum_preimage (Sigma.mk ν) s (sigma_mk_injective.injOn) _ (fun q _ hq ↦ by
    obtain ⟨μ, c⟩ := q
    refine ite_eq_right fun e ↦ ?_
    subst e
    exact hq ⟨c, rfl⟩)] at h
  simp only [ite_true] at h
  exact linearIndependent_iff'.1 (linearIndependent_negGlobal D ν) _ (fun c ↦ g ⟨ν, c⟩) h b
    (Finset.mem_preimage.2 hp)

/-- `B` is the set of all `G(b)`, `b ∈ B(∞)`. -/
lemma canonicalBasis_eq_range :
    canonicalBasis D = Set.range fun p : Σ ν, negCrystal D ν ↦ negGlobal D p.1 p.2 := by
  ext x
  rw [mem_canonicalBasis_iff]
  constructor
  · rintro ⟨ν, b, rfl⟩
    exact ⟨⟨ν, b⟩, rfl⟩
  · rintro ⟨⟨ν, b⟩, rfl⟩
    exact ⟨ν, b, rfl⟩

/-- **[Lus] Thm. 14.4.3 (d)**, over `ℚ(v)`: `B` is linearly independent. -/
theorem linearIndependent_canonicalBasis :
    LinearIndependent 𝕂 (Subtype.val : canonicalBasis D → Um D 𝕧) := by
  rw [canonicalBasis_eq_range]
  exact (linearIndepOn_id_range_iff (linearIndependent_negGlobal_sigma D).injective).2
    (linearIndependent_negGlobal_sigma D)

/-- **[Lus] Thm. 14.4.3 (d)**, over `𝒜`: `B` is linearly independent. -/
theorem linearIndependent_canonicalBasis_laurent :
    LinearIndependent (LaurentPolynomial ℤ) (Subtype.val : canonicalBasis D → Um D 𝕧) := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  have h := linearIndependent_iff'.1 (linearIndependent_canonicalBasis D) s
    (fun j ↦ integralLaurentEval (c j)) (by simpa only [laurent_smul_eq] using hc) i hi
  exact integralLaurentEval_injective (by rw [h, map_zero])

/-- **[Lus] Thm. 14.4.3 (d)**, over `ℚ(v)`: `B` spans `f`. -/
theorem span_canonicalBasis : Submodule.span 𝕂 (canonicalBasis D) = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  refine (iSup_le fun ν ↦ ?_ : ⨆ ν, Uw D 𝕧 ν ≤ _) (mem_iSup_Uw D x)
  rw [← span_canonicalBasisAt]
  exact Submodule.span_mono (Set.subset_iUnion (canonicalBasisAt D) ν)

/-- **[Lus] Thm. 14.4.3 (d)**, over `𝒜`: `B` spans `𝒜f`. -/
theorem span_canonicalBasis_laurent :
    Submodule.span (LaurentPolynomial ℤ) (canonicalBasis D) = negIntegral D := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun x hx ↦ ?_
  · intro x hx
    obtain ⟨ν, b, rfl⟩ := (mem_canonicalBasis_iff D).1 hx
    exact (negGlobal_mem D ν b).1
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (mem_iSup_Uw D x)
  refine Submodule.sum_mem _ fun ν _ ↦ ?_
  have hp : NegativePart.proj D 𝕧 (toZ ν) (f.sum fun _ y ↦ y) = f ν := by
    rw [Finsupp.sum, map_sum, Finset.sum_eq_single ν]
    · rw [proj_of_mem_Uw (hf ν), ite_eq_left rfl]
    · intro μ _ hμ
      rw [proj_of_mem_Uw (hf μ), ite_eq_right fun e ↦ hμ (LusztigF.toZ_injective e)]
    · intro hν
      rw [Finsupp.notMem_support_iff.1 hν, map_zero]
  have hν : f ν ∈ negIntegralWeight D ν := ⟨hp ▸ proj_mem_negIntegral D _ hx, hf ν⟩
  rw [← span_canonicalBasisAt_laurent] at hν
  exact Submodule.span_mono (Set.subset_iUnion (canonicalBasisAt D) ν) hν

end Theorem

end LieLean.QuantumGroup
