/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.CanonicalBasis

/-!
# The canonical basis of `Λ_λ`

This file proves [Lus] Thm. 14.3.2 (b) and Thm. 14.4.11: the canonical basis `B` of `f ≅ U⁻`
induces a basis of the integrable highest weight module of highest weight `λ`.

## Main definitions

* `rightRange D i n`: the subspace `fθᵢⁿ = σ(θᵢⁿf)` of `f ≅ U⁻` (`σ` is `starU`).
* `signedBasisGeRight`, `signedBasisAtRight`: Lusztig's `°𝐁_{i;≥n} = 𝐁 ∩ fθᵢⁿ` and
  `°𝐁_{i;n} = °𝐁_{i;≥n} - °𝐁_{i;≥n+1}` ([Lus] 14.3.1).
* `canonicalBasisHW Λ`: Lusztig's `B(λ) = ⋂ᵢ ⋃_{n ≤ ⟨i,λ⟩} °B_{i;n}` ([Lus] 14.4.11).
* `canonicalBasisHWBasis`: the basis `B(Λ_λ) = {b⁻η | b ∈ B(λ)}` ([Lus] 14.4.12).

## Main results

* `signedBasisGeRight_eq_image`: `°𝐁_{i;≥n} = σ(𝐁_{i;≥n})` ([Lus] 14.3.1).
* `mem_rightRange_iff_mem_span`: [Lus] Thm. 14.3.2 (b), weight by weight over `ℚ(v)`:
  `fθᵢⁿ` is spanned by `°𝐁_{i;≥n}`.
* `mem_canonicalBasisHW_iff`: `b ∈ B(λ)` iff `b ∈ B` and `b ∉ fθᵢ^{⟨i,λ⟩+1}` for all `i`.
* [Lus] Thm. 14.4.11: (a) `linearIndependent_evq_canonicalBasisHW`,
  `span_evq_canonicalBasisHW`, `injOn_evq_canonicalBasisHW`, `canonicalBasisHWBasis`;
  (b) `evq_eq_zero_of_notMem_canonicalBasisHW`.

## Implementation notes

Lusztig's `Λ_λ = f / Σᵢ fθᵢ^{⟨i,λ⟩+1}` is the library's `L_q(λ) = IrreducibleModule R 𝕧 λ` with
`b⁻η = evq hvt Λ b`; the kernel of `evq` is described by `ker_ev_eq`, which uses quantum target 2.
As in the grand loop and in `(G.2)`, the root datum is `X`-regular (`R.IsXRegular`), where
Lusztig assumes it `Y`-regular. Lusztig deduces 14.4.11 from 14.3.2; we do the same, using
`B = {G(b)}` (`mem_canonicalBasis_iff`) and that `B` is a basis of `f`
(`linearIndependent_canonicalBasis`, `span_canonicalBasis`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 14.3.1, 14.3.2,
  14.4.11, 14.4.12.
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

/-! ### The subsets `°𝐁_{i;n}` -/

section Right

/-- `fθᵢⁿ = σ(θᵢⁿf)`, as a subspace of `f ≅ U⁻` (`σ = starU`). -/
def rightRange (i : I) (n : ℕ) : Submodule 𝕂 (Um D 𝕧) :=
  (LinearMap.range (NegativePart.f D 𝕧 i ^ n)).map (starU D 𝕧)

omit [Finite I] [DecidableEq I] in
lemma mem_rightRange_iff {i : I} {n : ℕ} {x : Um D 𝕧} :
    x ∈ rightRange D i n ↔ starU D 𝕧 x ∈ LinearMap.range (NegativePart.f D 𝕧 i ^ n) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [starU_starU]
  · exact fun h ↦ ⟨_, h, starU_starU x⟩

omit [Finite I] [DecidableEq I] in
lemma mk_mul_mem_rightRange (i : I) (n : ℕ) (z : LusztigF 𝕂 I) :
    (Submodule.Quotient.mk (z * θ 𝕂 i ^ n) : Um D 𝕧) ∈ rightRange D i n := by
  rw [mem_rightRange_iff, starU_mk, rev_mul, rev_θ_pow]
  exact ⟨Submodule.Quotient.mk (rev 𝕂 I z), GrandLoop.f_pow_mk i n _⟩

omit [Finite I] [DecidableEq I] in
lemma rightRange_anti (i : I) {m n : ℕ} (hmn : m ≤ n) : rightRange D i n ≤ rightRange D i m := by
  intro x hx
  rw [mem_rightRange_iff] at hx ⊢
  obtain ⟨y, hy⟩ := hx
  refine ⟨(NegativePart.f D 𝕧 i ^ (n - m)) y, ?_⟩
  rw [← Module.End.mul_apply, ← pow_add, Nat.add_sub_cancel' hmn, hy]

omit [Finite I] [DecidableEq I] in
lemma mem_rightRange_zero (i : I) (x : Um D 𝕧) : x ∈ rightRange D i 0 := by
  rw [mem_rightRange_iff, pow_zero]
  exact ⟨_, rfl⟩

/-- `σ(𝐁) = 𝐁`. -/
lemma starU_mem_signedBasis {x : Um D 𝕧} (hx : x ∈ signedBasis D) :
    starU D 𝕧 x ∈ signedBasis D := by
  have key : ∀ (ν : I →₀ ℕ) (b : negCrystal D ν), starU D 𝕧 (negGlobal D ν b) ∈ canonicalBasis D :=
    fun ν b ↦ Set.mem_iUnion.2 ⟨ν, by
      rw [← starU_image_canonicalBasisAt, canonicalBasisAt_eq_range]
      exact ⟨_, ⟨b, rfl⟩, rfl⟩⟩
  rw [signedBasis_eq_union]
  obtain ⟨ν, b, rfl | rfl⟩ := (mem_signedBasis_iff D).1 hx
  · exact Or.inl (key ν b)
  · right
    rw [Set.mem_neg, map_neg, neg_neg]
    exact key ν b

/-- **[Lus] 14.3.1**: `°𝐁_{i;≥n} = 𝐁 ∩ fθᵢⁿ`. -/
def signedBasisGeRight (i : I) (n : ℕ) : Set (Um D 𝕧) :=
  {x | x ∈ signedBasis D ∧ x ∈ rightRange D i n}

/-- **[Lus] 14.3.1**: `°𝐁_{i;n} = °𝐁_{i;≥n} - °𝐁_{i;≥n+1}`. -/
def signedBasisAtRight (i : I) (n : ℕ) : Set (Um D 𝕧) :=
  signedBasisGeRight D i n \ signedBasisGeRight D i (n + 1)

/-- **[Lus] 14.3.1**: `°𝐁_{i;≥n} = σ(𝐁_{i;≥n})`. -/
theorem signedBasisGeRight_eq_image (i : I) (n : ℕ) :
    signedBasisGeRight D i n = starU D 𝕧 '' signedBasisGe D i n := by
  ext x
  constructor
  · rintro ⟨hx, hr⟩
    exact ⟨starU D 𝕧 x, ⟨starU_mem_signedBasis D hx, (mem_rightRange_iff D).1 hr⟩,
      starU_starU x⟩
  · rintro ⟨y, ⟨hy, hr⟩, rfl⟩
    exact ⟨starU_mem_signedBasis D hy, (mem_rightRange_iff D).2 (by rwa [starU_starU])⟩

/-- **[Lus] 14.3.2 (b)**, weight by weight over `ℚ(v)`: an element of `U⁻_ν` lies in `fθᵢⁿ` iff
it is in the span of `°𝐁_{i;≥n}`. More precisely, `(fθᵢⁿ)_ν` is spanned by the `σ(G(b))`,
`b ∈ B(∞)_ν`, `εᵢ(b) ≥ n`. -/
theorem mem_rightRange_iff_mem_span {i : I} {n : ℕ} {ν : I →₀ ℕ} {x : Um D 𝕧}
    (hx : x ∈ Uw D 𝕧 ν) :
    x ∈ rightRange D i n ↔
      x ∈ Submodule.span 𝕂 (starU D 𝕧 '' (negGlobal D ν '' {b | NegDepthGe D i n b})) := by
  rw [mem_rightRange_iff, mem_range_iff_mem_span D (starU_mem_Uw hx), Submodule.span_image,
    Submodule.mem_map]
  constructor
  · exact fun h ↦ ⟨_, h, starU_starU x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [starU_starU]

/-- `σ(G(b)) ∈ °𝐁_{i;≥n}` for `εᵢ(b) ≥ n`. -/
lemma starU_negGlobal_mem_signedBasisGeRight {i : I} {n : ℕ} {ν : I →₀ ℕ} {b : negCrystal D ν}
    (hb : NegDepthGe D i n b) : starU D 𝕧 (negGlobal D ν b) ∈ signedBasisGeRight D i n := by
  rw [signedBasisGeRight_eq_image]
  refine ⟨_, ⟨(mem_signedBasis_iff D).2 ⟨ν, b, Or.inl rfl⟩, ?_⟩, rfl⟩
  exact negFilt_le_range D i n ν (negGlobal_mem_negFilt D hb)

/-- **[Lus] 14.3.2 (b)**, weight by weight over `ℚ(v)`, in terms of `°𝐁_{i;≥n}`. -/
theorem mem_rightRange_iff_mem_span_signedBasisGeRight {i : I} {n : ℕ} {ν : I →₀ ℕ}
    {x : Um D 𝕧} (hx : x ∈ Uw D 𝕧 ν) :
    x ∈ rightRange D i n ↔ x ∈ Submodule.span 𝕂 (signedBasisGeRight D i n) := by
  refine ⟨fun h ↦ Submodule.span_mono ?_ ((mem_rightRange_iff_mem_span D hx).1 h), fun h ↦ ?_⟩
  · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact starU_negGlobal_mem_signedBasisGeRight D hb
  · exact (Submodule.span_le.2 fun y hy ↦ hy.2) h

end Right

/-! ### [Lus] 14.4.11 -/

section HighestWeight

variable {Y : Type*} [AddCommGroup Y] {R : D.RootDatum Y} (Λ : Dom R)

/-- **[Lus] 14.4.11**: `B(λ) = ⋂ᵢ ⋃_{n ≤ ⟨i,λ⟩} °B_{i;n}`, where `°B_{i;n} = B ∩ °𝐁_{i;n}`. -/
def canonicalBasisHW : Set (Um D 𝕧) :=
  canonicalBasis D ∩ ⋂ i, ⋃ (n : ℕ) (_ : (n : ℤ) ≤ Λ.1 (R.coroot i)), signedBasisAtRight D i n

lemma canonicalBasis_subset_signedBasis : canonicalBasis D ⊆ signedBasis D := by
  rw [signedBasis_eq_union]
  exact Set.subset_union_left

/-- `b ∈ B(λ)` iff `b ∈ B` and `b ∉ fθᵢ^{⟨i,λ⟩+1}` for all `i`. -/
theorem mem_canonicalBasisHW_iff {x : Um D 𝕧} :
    x ∈ canonicalBasisHW D Λ ↔
      x ∈ canonicalBasis D ∧ ∀ i, x ∉ rightRange D i ((Λ.1 (R.coroot i)).toNat + 1) := by
  classical
  simp only [canonicalBasisHW, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion]
  refine and_congr_right fun hB ↦ forall_congr' fun i ↦ ?_
  have hS := canonicalBasis_subset_signedBasis D hB
  have hΛ := Λ.2 i
  constructor
  · rintro ⟨n, hn, -, hn1⟩ h
    exact hn1 ⟨hS, rightRange_anti D i (by omega) h⟩
  · intro h
    have hex : ∃ m, x ∉ rightRange D i (m + 1) := ⟨_, h⟩
    refine ⟨Nat.find hex, ?_, ⟨hS, ?_⟩, fun h' ↦ Nat.find_spec hex h'.2⟩
    · have := Nat.find_min' hex h
      omega
    · rcases hm : Nat.find hex with _ | m
      · exact mem_rightRange_zero D i x
      · have := Nat.find_min hex (hm ▸ Nat.lt_succ_self m : m < Nat.find hex)
        exact not_not.1 this

variable {D} in
/-- Elements of `fθᵢ^{⟨i,λ⟩+1}` act as zero on `η`. -/
lemma evq_eq_zero_of_mem_rightRange (hR : R.IsXRegular) {i : I} {x : Um D 𝕧}
    (hx : x ∈ rightRange D i ((Λ.1 (R.coroot i)).toNat + 1)) : evq hvt Λ x = 0 := by
  rw [mem_rightRange_iff] at hx
  obtain ⟨y, hy⟩ := hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [GrandLoop.f_pow_mk] at hy
  have hx : x = Submodule.Quotient.mk (rev 𝕂 I z * θ 𝕂 i ^ ((Λ.1 (R.coroot i)).toNat + 1)) := by
    rw [← starU_starU x, ← hy, starU_mk, rev_mul, rev_θ_pow]
  rw [hx, evq_mk, ← LinearMap.mem_ker, ker_ev_eq hR]
  refine Submodule.mem_sup_right ?_
  set n : I → ℕ := fun i ↦ (Λ.1 (R.coroot i)).toNat
  have hle : LinearMap.range (LinearMap.mulRight 𝕂 (θ 𝕂 i ^ (n i + 1))) ≤
      Submodule.span 𝕂 (Set.range fun g ↦ FreeAlgebra.wordBasis 𝕂 I (powWord n g)) := by
    rw [LinearMap.range_eq_map, ← (FreeAlgebra.wordBasis 𝕂 I).span_eq, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨(w, i), ?_⟩
    simp only [powWord, LinearMap.mulRight_apply, ← monomial_eq_wordBasis, monomial,
      List.map_append, List.prod_append, List.map_replicate, List.prod_replicate]
  exact hle ⟨rev 𝕂 I z, rfl⟩

lemma starU_negGlobal_notMem_canonicalBasisHW {i : I} {ν : I →₀ ℕ} {b : negCrystal D ν}
    (hb : NegDepthGe D i ((Λ.1 (R.coroot i)).toNat + 1) b) :
    starU D 𝕧 (negGlobal D ν b) ∉ canonicalBasisHW D Λ := fun h ↦
  ((mem_canonicalBasisHW_iff D Λ).1 h).2 i (starU_negGlobal_mem_signedBasisGeRight D hb).2

variable {D} in
/-- The kernel of `x ↦ x⁻η` is spanned by `B - B(λ)`. -/
lemma mem_span_of_evq_eq_zero (hR : R.IsXRegular) {x : Um D 𝕧} (hx : evq hvt Λ x = 0) :
    x ∈ Submodule.span 𝕂 (canonicalBasis D \ canonicalBasisHW D Λ) := by
  set n : I → ℕ := fun i ↦ (Λ.1 (R.coroot i)).toNat
  obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hZ : Z ∈ evKernel D n := by
    rw [← ker_ev_eq hR Λ, LinearMap.mem_ker]
    exact hx
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hZ
  rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hs, zero_add]
  change (serreSubmodule D 𝕧).mkQ t ∈ _
  refine (Submodule.map_le_iff_le_comap.2 ?_ : Submodule.map (serreSubmodule D 𝕧).mkQ _ ≤ _)
    ⟨t, ht, rfl⟩
  rw [Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.mkQ_apply]
  have hw : (Submodule.Quotient.mk (FreeAlgebra.wordBasis 𝕂 I (powWord n g)) : Um D 𝕧) ∈
      Uw D 𝕧 (wordWeight (powWord n g)) := mk_mem_Uw (wordBasis_mem_weightSpace rfl)
  have hr : (Submodule.Quotient.mk (FreeAlgebra.wordBasis 𝕂 I (powWord n g)) : Um D 𝕧) ∈
      rightRange D g.2 (n g.2 + 1) := by
    rw [← monomial_eq_wordBasis]
    simpa only [powWord, monomial, List.map_append, List.prod_append, List.map_replicate,
      List.prod_replicate] using mk_mul_mem_rightRange D g.2 (n g.2 + 1) (monomial 𝕂 g.1)
  refine Submodule.span_mono ?_ ((mem_rightRange_iff_mem_span D hw).1 hr)
  rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  refine ⟨Set.mem_iUnion.2 ⟨wordWeight (powWord n g), ?_⟩,
    starU_negGlobal_notMem_canonicalBasisHW D Λ hb⟩
  rw [← starU_image_canonicalBasisAt, canonicalBasisAt_eq_range]
  exact ⟨_, ⟨b, rfl⟩, rfl⟩

variable {D} in
/-- **[Lus] Thm. 14.4.11 (b)**: if `b ∈ B - B(λ)`, then `b⁻η = 0`. -/
theorem evq_eq_zero_of_notMem_canonicalBasisHW (hR : R.IsXRegular) {x : Um D 𝕧}
    (hx : x ∈ canonicalBasis D) (hx' : x ∉ canonicalBasisHW D Λ) : evq hvt Λ x = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ rightRange D i ((Λ.1 (R.coroot i)).toNat + 1) := by
    by_contra h
    push Not at h
    exact hx' ((mem_canonicalBasisHW_iff D Λ).2 ⟨hx, h⟩)
  exact evq_eq_zero_of_mem_rightRange Λ hR hi

lemma canonicalBasisHW_subset : canonicalBasisHW D Λ ⊆ canonicalBasis D :=
  Set.inter_subset_left

variable {D} in
/-- **[Lus] Thm. 14.4.11 (a)**: the `b⁻η`, `b ∈ B(λ)`, are linearly independent. -/
theorem linearIndependent_evq_canonicalBasisHW (hR : R.IsXRegular) :
    LinearIndependent 𝕂 fun x : canonicalBasisHW D Λ ↦ evq hvt Λ (x : Um D 𝕧) := by
  have hli : LinearIndependent 𝕂 (Subtype.val : canonicalBasisHW D Λ → Um D 𝕧) :=
    (linearIndependent_canonicalBasis D).comp (Set.inclusion (canonicalBasisHW_subset D Λ))
      (Set.inclusion_injective _)
  refine hli.map (f := evq hvt Λ) ?_
  have hdisj := (linearIndependent_canonicalBasis D).disjoint_span_image
    (s := Subtype.val ⁻¹' canonicalBasisHW D Λ)
    (t := Subtype.val ⁻¹' (canonicalBasis D \ canonicalBasisHW D Λ))
    (Set.disjoint_left.2 fun _ h₁ h₂ ↦ h₂.2 h₁)
  rw [Subtype.image_preimage_coe, Subtype.image_preimage_coe,
    Set.inter_eq_self_of_subset_right (canonicalBasisHW_subset D Λ),
    Set.inter_eq_self_of_subset_right Set.sdiff_subset] at hdisj
  rw [Subtype.range_coe]
  exact hdisj.mono_right fun x hx ↦ mem_span_of_evq_eq_zero Λ hR hx

omit [Finite I] in
/-- `evq` is surjective. -/
lemma evq_surjective : Function.Surjective (evq (D := D) hvt Λ) := fun m ↦ by
  obtain ⟨y, rfl⟩ := ev_surjective (D := D) Λ m
  exact ⟨Submodule.Quotient.mk y, rfl⟩

variable {D} in
/-- **[Lus] Thm. 14.4.11 (a)**: the `b⁻η`, `b ∈ B(λ)`, span `Λ_λ`. -/
theorem span_evq_canonicalBasisHW (hR : R.IsXRegular) :
    Submodule.span 𝕂 (evq hvt Λ '' canonicalBasisHW D Λ) = ⊤ := by
  refine eq_top_iff.2 fun m _ ↦ ?_
  obtain ⟨x, rfl⟩ := evq_surjective D Λ m
  have hx : x ∈ Submodule.span 𝕂 (canonicalBasis D) := by
    rw [span_canonicalBasis]
    trivial
  have : Submodule.map (evq hvt Λ) (Submodule.span 𝕂 (canonicalBasis D)) ≤
      Submodule.span 𝕂 (evq hvt Λ '' canonicalBasisHW D Λ) := by
    rw [Submodule.map_span_le]
    intro y hy
    by_cases hy' : y ∈ canonicalBasisHW D Λ
    · exact Submodule.subset_span ⟨y, hy', rfl⟩
    · rw [evq_eq_zero_of_notMem_canonicalBasisHW Λ hR hy hy']
      exact zero_mem _
  exact this ⟨x, hx, rfl⟩

variable {D} in
/-- **[Lus] Thm. 14.4.11 (a)**: `b ↦ b⁻η` is injective on `B(λ)`. -/
theorem injOn_evq_canonicalBasisHW (hR : R.IsXRegular) :
    Set.InjOn (evq hvt Λ) (canonicalBasisHW D Λ) := fun x hx y hy h ↦
  congrArg Subtype.val ((linearIndependent_evq_canonicalBasisHW Λ hR).injective
    (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)

variable {D} in
/-- **[Lus] 14.4.12**: the canonical basis `B(Λ_λ) = {b⁻η | b ∈ B(λ)}` of `Λ_λ`, indexed by
`B(λ)` ([Lus] Thm. 14.4.11 (a)). -/
def canonicalBasisHWBasis (hR : R.IsXRegular) :
    Module.Basis (canonicalBasisHW D Λ) 𝕂 (IrreducibleModule R 𝕧 Λ.1) :=
  Module.Basis.mk (linearIndependent_evq_canonicalBasisHW Λ hR) (by
    rw [← Set.image_eq_range, span_evq_canonicalBasisHW Λ hR])

variable {D} in
lemma canonicalBasisHWBasis_apply (hR : R.IsXRegular) (x : canonicalBasisHW D Λ) :
    canonicalBasisHWBasis Λ hR x = evq hvt Λ (x : Um D 𝕧) :=
  Module.Basis.mk_apply _ _ _

end HighestWeight

end LieLean.QuantumGroup
