/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Integral.Coordinates

/-! # Grouped integer crystal coordinates and their norm

The proof groups the accepted integer residue expansion by equal crystal classes, then
uses orthonormality modulo the uniformizer. No homogeneity or word independence is assumed.
-/

open LieLean LusztigF Finset Pointwise
open LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop

noncomputable section

namespace PBWSignedCrystal

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X
local notation "hv'" => pow_ne_one_of_transcendental' transcendental_ratFunc_X
local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- The norm of a finite expansion in distinct crystal residue classes is the sum of
coefficient squares modulo the uniformizer. This proof does not require homogeneity. -/
theorem norm_of_distinct_residue_coordinates {x : Um D 𝕧}
    (hxL : x ∈ latInf hvt A) (S : Finset (List I)) (a : List I → A)
    (hSd : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' →
      fWi (D := D) hvt s - fWi hvt s' ∉ ϖ • latInf hvt A)
    (hxy : x - ∑ s ∈ S, a s • fWi (D := D) hvt s ∈ ϖ • latInf hvt A) :
    ∃ t : A, formU hv' x x =
      algebraMap A 𝕂 (∑ s ∈ S, a s ^ 2) + algebraMap A 𝕂 (ϖ * t) := by
  classical
  let := Fintype.ofFinite I
  set y : Um D 𝕧 := ∑ s ∈ S, a s • fWi (D := D) hvt s with hy
  have hyL : y ∈ latInf hvt A := by
    rw [hy]
    exact Submodule.sum_mem _ fun s _ ↦
      Submodule.smul_mem _ _ (NegativePart.fWord_mem_latticeInf _ _ s)
  obtain ⟨t₁, ht₁⟩ := formU_mem_smul (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum hxL hxy
  obtain ⟨t₂, ht₂⟩ := formU_mem_smul (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum hyL hxy
  have hxy' : formU hv' x x - formU hv' y y = algebraMap A 𝕂 (ϖ * (t₁ + t₂)) := by
    have : formU hv' x x - formU hv' y y =
        formU hv' x (x - y) + formU hv' y (x - y) := by
      rw [map_sub, map_sub, formU_comm hv' y x]
      ring
    rw [this, ht₁, ht₂, ← map_add, mul_add]
  choose e he using fun s s' ↦
    formU_fWi_fWi (hR := D.isXRegular_extendedRootDatum)
      InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
      InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
      D.exists_fundamental_extendedRootDatum s s'
  have hexp : formU hv' y y = ∑ s ∈ S, ∑ s' ∈ S, algebraMap A 𝕂 (a s) *
      (algebraMap A 𝕂 (a s') * formU hv' (fWi (D := D) hvt s) (fWi hvt s')) := by
    rw [hy]
    simp only [map_sum, LinearMap.sum_apply, ← algebraMap_smul 𝕂 (a _), map_smul,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
      rw [formU_comm hv']
  have key : ∀ s ∈ S, ∀ s' ∈ S, algebraMap A 𝕂 (a s) *
      (algebraMap A 𝕂 (a s') * formU hv' (fWi (D := D) hvt s) (fWi hvt s')) =
      (if s = s' then algebraMap A 𝕂 (a s ^ 2) else 0) +
        algebraMap A 𝕂 (ϖ * (a s * a s' * e s s')) := by
    intro s hs s' hs'
    rw [he]
    by_cases h : s = s'
    · subst h
      simp only [sub_self, zero_mem, ↓reduceIte, map_mul, map_pow]
      ring
    · rw [ite_eq_right_iff.2 (fun h' ↦ absurd h' (hSd s hs s' hs' h))]
      simp only [h, ↓reduceIte, map_mul]
      ring
  have hyy : formU hv' y y = algebraMap A 𝕂 (∑ s ∈ S, a s ^ 2) +
      algebraMap A 𝕂 (ϖ * ∑ s ∈ S, ∑ s' ∈ S, a s * a s' * e s s') := by
    rw [hexp, Finset.sum_congr rfl fun s hs ↦ Finset.sum_congr rfl fun s' hs' ↦ key s hs s' hs']
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, map_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s hs ↦ by simp [hs]
  refine ⟨t₁ + t₂ + ∑ s ∈ S, ∑ s' ∈ S, a s * a s' * e s s', ?_⟩
  rw [show formU hv' x x = (formU hv' x x - formU hv' y y) + formU hv' y y by ring, hxy', hyy]
  simp only [map_add, map_mul]
  ring

/-- An element of the actual integral form and crystal lattice has integer coordinates on
pairwise distinct crystal residue classes; its norm is their integer sum of squares modulo
the actual uniformizer. The proof uses the accepted integer residue expansion and grouping. -/
theorem grouped_integer_norm_coordinates {x : Um D 𝕧}
    (hxI : negativeQuotientEquiv D x ∈ quotientIntegralForm D)
    (hxL : x ∈ latInf hvt A) :
    ∃ (S : Finset (List I)) (z : List I → ℤ),
      (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' →
        fWi (D := D) hvt s - fWi hvt s' ∉ ϖ • latInf hvt A) ∧
      x - ∑ s ∈ S, (z s : 𝕂) • fWi (D := D) hvt s ∈ ϖ • latInf hvt A ∧
      ∃ t : A, formU hv' x x =
        ((∑ s ∈ S, z s ^ 2 : ℤ) : 𝕂) + algebraMap A 𝕂 (ϖ * t) := by
  classical
  obtain ⟨a, ha⟩ := exists_integer_crystal_residue_coordinates D hxI hxL
  set W := a.support
  obtain ⟨S, -, hSd, hcov⟩ := exists_reps_mod (ϖ • latInf hvt A) (fWi (D := D) hvt) W
  choose! r hrS hr using hcov
  let z : List I → ℤ := fun s ↦ ∑ w ∈ W with r w = s, a w
  set y : Um D 𝕧 := ∑ s ∈ S, (z s : 𝕂) • fWi (D := D) hvt s with hy
  have hy' : y = ∑ w ∈ W, (a w : 𝕂) • fWi (D := D) hvt (r w) := by
    rw [hy, ← Finset.sum_fiberwise_of_maps_to (g := r) (t := S) hrS]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    simp only [z, Int.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [(Finset.mem_filter.1 hw).2]
  have hay : a.sum (fun w n ↦ (n : 𝕂) • fWi (D := D) hvt w) - y ∈
      ϖ • latInf hvt A := by
    rw [hy', Finsupp.sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun w hw ↦ ?_
    rw [← smul_sub, ← map_intCast (algebraMap A 𝕂), algebraMap_smul]
    exact Submodule.smul_mem _ _ (hr w hw)
  have hxy : x - y ∈ ϖ • latInf hvt A := by
    simpa using add_mem ha hay
  refine ⟨S, z, hSd, hxy, ?_⟩
  have hxyA : x - ∑ s ∈ S, (z s : A) • fWi (D := D) hvt s ∈
      ϖ • latInf hvt A := by
    simpa only [hy, ← algebraMap_smul 𝕂 (z _ : A), map_intCast] using hxy
  obtain ⟨t, ht⟩ := norm_of_distinct_residue_coordinates D hxL S
    (fun s ↦ (z s : A)) hSd hxyA
  refine ⟨t, ?_⟩
  simpa only [map_sum, map_pow, map_intCast, Int.cast_sum, Int.cast_pow] using ht

end PBWSignedCrystal
