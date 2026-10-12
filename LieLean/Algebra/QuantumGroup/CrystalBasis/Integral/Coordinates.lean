/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Integral.Extraction

/-! Finite integral coordinates of original integral/crystal-lattice intersections. -/
open LieLean LusztigF Finset Pointwise
noncomputable section
namespace LieLean.QuantumGroup
open GrandLoop
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X
local notation "hv'" => pow_ne_one_of_transcendental' transcendental_ratFunc_X
local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩
variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- Any element of the original integral form and crystal lattice has a finite integer
crystal-word expansion modulo the actual uniformizer lattice. Equal residue words are
first grouped; no independence of words or coordinate hypothesis is assumed. -/
theorem exists_integer_crystal_residue_coordinates {x : Um D 𝕧}
    (hxI : negativeQuotientEquiv D x ∈ quotientIntegralForm D)
    (hxL : x ∈ latInf hvt A) :
    ∃ a : List I →₀ ℤ, x - a.sum (fun w n ↦ (n : 𝕂) • fWi (D := D) hvt w) ∈
      ϖ • latInf hvt A := by
  classical
  let := Fintype.ofFinite I
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hxL
  set W := c.support
  obtain ⟨S, -, hSd, hcov⟩ := exists_reps_mod (ϖ • latInf hvt A) (fWi (D := D) hvt) W
  choose! r hrS hr using hcov
  obtain ⟨a, ha⟩ : ∃ a : List I → A, ∀ s, a s = ∑ w ∈ W with r w = s, c w :=
    ⟨_, fun _ ↦ rfl⟩
  set y : Um D 𝕧 := ∑ s ∈ S, algebraMap A 𝕂 (a s) • fWi (D := D) hvt s with hy
  have hy' : y = ∑ w ∈ W, algebraMap A 𝕂 (c w) • fWi (D := D) hvt (r w) := by
    rw [hy, ← Finset.sum_fiberwise_of_maps_to (g := r) (t := S) hrS]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [ha, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [(Finset.mem_filter.1 hw).2]
  have hxy : x - y ∈ ϖ • latInf hvt A := by
    rw [hy', ← hc, Finsupp.sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun w hw ↦ ?_
    rw [← algebraMap_smul 𝕂, ← smul_sub, algebraMap_smul]
    exact Submodule.smul_mem _ _ (hr w hw)
  choose e he using fun s s' ↦
    formU_fWi_fWi (hR := D.isXRegular_extendedRootDatum)
      InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
      InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
      D.exists_fundamental_extendedRootDatum s s'
  have hpair : ∀ s ∈ S, formU hv' (fWi (D := D) hvt s) y = algebraMap A 𝕂 (a s) +
      algebraMap A 𝕂 (ϖ * ∑ t ∈ S, a t * e s t) := by
    intro s hs
    have key : ∀ t ∈ S, algebraMap A 𝕂 (a t) *
        formU hv' (fWi (D := D) hvt s) (fWi (D := D) hvt t) =
        (if s = t then algebraMap A 𝕂 (a t) else 0) +
          algebraMap A 𝕂 (ϖ * (a t * e s t)) := by
      intro t ht
      rw [he]
      by_cases h : s = t
      · subst h
        simp only [sub_self, zero_mem, ↓reduceIte, map_mul]
        ring
      · rw [ite_eq_right_iff.2 (fun h' ↦ absurd h' (hSd s hs t ht h))]
        simp only [h, ↓reduceIte, map_mul]
        ring
    rw [hy]
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl fun t ht ↦ key t ht]
    simp [Finset.sum_add_distrib, hs, map_sum, Finset.mul_sum]
  have hcoeff : ∀ s ∈ S, ∃ (z : ℤ) (b : A), a s - (z : A) = ϖ * b := by
    intro s hs
    obtain ⟨z, b, hb⟩ := word_pairing_integer_residue D s hxI hxL
    obtain ⟨t, ht⟩ := formU_mem_smul (hR := D.isXRegular_extendedRootDatum)
      InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
      InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
      D.exists_fundamental_extendedRootDatum (NegativePart.fWord_mem_latticeInf _ _ s) hxy
    refine ⟨z, b - t - ∑ u ∈ S, a u * e s u, ?_⟩
    apply InfinityLocalRing.injective_algebraMap
    rw [map_sub, hb, hpair s hs] at ht
    simp only [map_sub, map_intCast, map_mul] at ht ⊢
    linear_combination -ht
  choose! z b hb using hcoeff
  let zf : List I →₀ ℤ := Finsupp.onFinset S (fun s ↦ if s ∈ S then z s else 0)
    (by intro s hs; by_contra h; simp [h] at hs)
  have hzf : zf.sum (fun w n ↦ (n : 𝕂) • fWi (D := D) hvt w) =
      ∑ s ∈ S, (z s : 𝕂) • fWi (D := D) hvt s := by
    rw [Finsupp.sum_of_support_subset zf (show zf.support ⊆ S from
      Finsupp.support_onFinset_subset) _ (fun _ _ ↦ by simp)]
    exact Finset.sum_congr rfl fun s hs ↦ by simp [zf, hs]
  refine ⟨zf, ?_⟩
  have hyz : y - zf.sum (fun w n ↦ (n : 𝕂) • fWi (D := D) hvt w) ∈ ϖ • latInf hvt A := by
    rw [hy, hzf, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun s hs ↦ ?_
    rw [← sub_smul, ← map_intCast (algebraMap A 𝕂), ← map_sub, hb s hs,
      algebraMap_smul, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _
      (Submodule.smul_mem _ _ (NegativePart.fWord_mem_latticeInf _ _ s))
  simpa using add_mem hxy hyz

end LieLean.QuantumGroup
