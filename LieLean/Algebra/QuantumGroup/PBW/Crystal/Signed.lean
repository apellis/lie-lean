/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.Crystal.Grouped
import LieLean.Algebra.QuantumGroup.PBW.Crystal.Uniqueness

/-! # Signed residues from integral norm one

Integer coordinates, grouped by actual residue class, turn the norm residue into an
integer sum of squares. This does not identify a canonical or global basis lift.
-/
noncomputable section
open LieLean LieLean.QuantumGroup LusztigF GrandLoop Finset
open scoped Pointwise
namespace PBWSignedCrystal

/-- An integer sum of squares equal to one has exactly one nonzero coefficient, a sign. -/
lemma integer_sum_squares_one {α : Type*} (S : Finset α) (z : α → ℤ)
    (h : ∑ s ∈ S, z s ^ 2 = 1) :
    ∃ u ∈ S, (z u = 1 ∨ z u = -1) ∧ ∀ t ∈ S, t ≠ u → z t = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at h
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha] at h
    have hn : 0 ≤ ∑ s ∈ S, z s ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    by_cases hz : z a = 0
    · obtain ⟨u, hu, hus, huz⟩ := ih (by simpa [hz] using h)
      refine ⟨u, Finset.mem_insert_of_mem hu, hus, ?_⟩
      intro t ht htu
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hz
      · exact huz t ht htu
    · have hb : -1 ≤ z a ∧ z a ≤ 1 := by constructor <;> nlinarith
      have hs : z a = 1 ∨ z a = -1 := by omega
      have hsum : ∑ s ∈ S, z s ^ 2 = 0 := by rcases hs with hs | hs <;> simp [hs] at h ⊢ <;> omega
      refine ⟨a, Finset.mem_insert_self _ _, hs, ?_⟩
      intro t ht hta
      have htS : t ∈ S := (Finset.mem_insert.mp ht).resolve_left hta
      have hle := Finset.single_le_sum (fun s (_ : s ∈ S) ↦ sq_nonneg (z s)) htS
      rw [hsum] at hle
      nlinarith

local notation "K" => RatFunc ℚ
local notation "v" => (RatFunc.X : K)
local notation "A" => InfinityLocalRing
local notation "π" => InfinityLocalRing.uniformizer
attribute [local instance] neZero_ratFunc_X
variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)
local notation "L" => latInf (D := D) transcendental_ratFunc_X A
local notation "P" => π • L
local notation "B" => fWi (D := D) transcendental_ratFunc_X
local notation "F" => formU (D := D) (pow_ne_one_of_transcendental' transcendental_ratFunc_X)

/-- Every original integral/lattice element of norm residue one has a signed crystal residue.
No homogeneity assumption is used. -/
theorem exists_signed_crystal_residue {x : Um D v}
    (hxI : negativeQuotientEquiv D x ∈ quotientIntegralForm D) (hxL : x ∈ L)
    (hnorm : ∃ a : A, F x x = algebraMap A K (1 + π * a)) :
    ∃ (u : List I) (e : ℤ), (e = 1 ∨ e = -1) ∧ x - (e : K) • B u ∈ P := by
  classical
  obtain ⟨S, z, -, hx, t, ht⟩ := grouped_integer_norm_coordinates D hxI hxL
  obtain ⟨a, ha⟩ := hnorm
  have he : ((∑ s ∈ S, z s ^ 2 - 1 : ℤ) : K) = algebraMap A K (π * (a - t)) := by
    simp only [Int.cast_sub, Int.cast_one, mul_sub, map_sub]
    rw [ha] at ht
    simp only [map_add, map_one] at ht
    linear_combination -ht
  have hsum : ∑ s ∈ S, z s ^ 2 = 1 := by
    have := int_eq_zero_of_uniformizer (∑ s ∈ S, z s ^ 2 - 1) (a - t) he
    omega
  obtain ⟨u, hu, he, hz⟩ := integer_sum_squares_one S z hsum
  refine ⟨u, z u, he, ?_⟩
  have hexp : ∑ s ∈ S, (z s : K) • B s = (z u : K) • B u := by
    apply Finset.sum_eq_single u
    · intro s hs hsu
      simp [hz s hs hsu]
    · exact fun h ↦ False.elim (h hu)
  rwa [hexp] at hx

/-- Existence, nonvanishing, and uniqueness of sign and crystal residue class, not word. -/
theorem unique_signed_crystal_residue {x : Um D v}
    (hxI : negativeQuotientEquiv D x ∈ quotientIntegralForm D) (hxL : x ∈ L)
    (hnorm : ∃ a : A, F x x = algebraMap A K (1 + π * a)) :
    ∃ (u : List I) (e : ℤ), (e = 1 ∨ e = -1) ∧
      x - (e : K) • B u ∈ P ∧ B u ∉ P ∧ x ∉ P ∧
      ∀ (t : List I) (f : ℤ), (f = 1 ∨ f = -1) →
        x - (f : K) • B t ∈ P → e = f ∧ B u - B t ∈ P := by
  obtain ⟨u, e, he, hx⟩ := exists_signed_crystal_residue D hxI hxL hnorm
  refine ⟨u, e, he, hx, word_not_mem_uniformizer u, ?_, ?_⟩
  · intro hx0
    have hh := sub_mem hx0 hx
    rcases he with rfl | rfl
    · exact word_not_mem_uniformizer u (by simpa using hh)
    · exact word_not_mem_uniformizer u (by simpa using neg_mem hh)
  · intro t f hf ht
    exact signed_residue_unique he hf hx ht

end PBWSignedCrystal
