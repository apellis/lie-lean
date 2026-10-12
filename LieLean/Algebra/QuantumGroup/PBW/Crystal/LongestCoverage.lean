/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.LongestInfinityLattice
import LieLean.Algebra.QuantumGroup.PBW.Crystal.IntegralPBW

/-! # Signed PBW coverage of the actual crystal residues at a finite longest word

Reconstructed direct proof from the whole-lattice PBW span and the original form.
No canonical lifts or sign removal are asserted.
-/
noncomputable section
open LieLean LieLean.QuantumGroup LusztigF GrandLoop
open scoped Pointwise
namespace PBWSignedCrystal
local notation "K" => RatFunc ℚ
local notation "v" => (RatFunc.X : K)
local notation "A" => InfinityLocalRing
local notation "π" => InfinityLocalRing.uniformizer
attribute [local instance] neZero_ratFunc_X
variable {I : Type*} [Finite I] [DecidableEq I] {D : LusztigCartanDatum I}
local notation "L" => latInf (D := D) transcendental_ratFunc_X A
local notation "P" => π • L
local notation "B" => fWi (D := D) transcendental_ratFunc_X
local notation "F" => formU (D := D) (pow_ne_one_of_transcendental' transcendental_ratFunc_X)
variable {Y : Type*} [AddCommGroup Y] (R : D.RootDatum Y)
  {W : Type*} [Group W] [Finite W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}
  {w : List I} (hw : cs.IsReduced w)

/-- Every actual word class is a signed original PBW residue for a finite longest word. -/
theorem original_PBW_longest_coverage (hw₀ : cs.wordProd w = cs.longestElement)
    (u : List I) :
    ∃ (c : Fin w.length → ℕ) (e : ℤ), (e = 1 ∨ e = -1) ∧
      (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
        (e : K) • B u ∈ P := by
  classical
  by_contra hn
  let f : Quotient D v →ₗ[A] K :=
    ((F (B u)).restrictScalars A).comp
      ((negativeQuotientEquiv D).symm.toLinearMap.restrictScalars A)
  have hg (c : Fin w.length → ℕ) :
      ∃ a : A, f (Modified.integralPBWPreimage R hw c) = algebraMap A K (π * a) := by
    obtain ⟨t, e, he, ht, -⟩ := original_PBW_unique_signed R hw c
    have hut : B u - B t ∉ P := by
      intro hut
      apply hn
      refine ⟨c, e, he, ?_⟩
      have htu : B t - B u ∈ P := by simpa using neg_mem hut
      have hs : (e : K) • (B t - B u) ∈ P := by
        rcases he with rfl | rfl
        · simpa using htu
        · simpa using neg_mem htu
      convert add_mem ht hs using 1
      rw [smul_sub]
      abel
    obtain ⟨a, ha⟩ := form_mem_uniformizer (NegativePart.fWord_mem_latticeInf _ _ u) ht
    obtain ⟨b, hb⟩ := word_pairing (D := D) u t
    rw [ite_eq_right hut, zero_add] at hb
    rw [map_sub, map_smul, hb] at ha
    refine ⟨a + (e : A) * b, ?_⟩
    change F (B u) ((negativeQuotientEquiv D).symm
      (Modified.integralPBWPreimage R hw c)) = _
    simp only [mul_add, map_add, map_mul, map_intCast]
    simp only [smul_eq_mul, map_mul] at ha
    linear_combination ha
  have hx : negativeQuotientEquiv D (B u) ∈ Submodule.span A
      (Set.range fun c ↦ (Modified.integralPBWPreimage R hw c : Quotient D v)) := by
    rw [← PBWInfinityLattice.intersection_eq_span R hw,
      PBWInfinityLattice.intersection_longest_eq_lattice R hw hw₀]
    change (negativeQuotientEquiv D).symm (negativeQuotientEquiv D (B u)) ∈ L
    simpa only [LinearEquiv.symm_apply_apply] using
      (NegativePart.fWord_mem_latticeInf _ _ u)
  have hall (x : Quotient D v) (hx : x ∈ Submodule.span A
      (Set.range fun c ↦ (Modified.integralPBWPreimage R hw c : Quotient D v))) :
      ∃ a : A, f x = algebraMap A K (π * a) := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact hg c
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by simp only [map_add, ha, hb, mul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      rw [map_smul, ha]
      simp only [Algebra.smul_def, map_mul]
      ring
  obtain ⟨a, ha⟩ := hall _ hx
  change F (B u) ((negativeQuotientEquiv D).symm (negativeQuotientEquiv D (B u))) = _ at ha
  rw [LinearEquiv.symm_apply_apply] at ha
  obtain ⟨b, hb⟩ := word_pairing (D := D) u u
  simp only [sub_self, Submodule.zero_mem, ite_true] at hb
  have h1 : (1 : K) = algebraMap A K (π * (a - b)) := by
    simp only [mul_sub, map_sub]
    linear_combination ha - hb
  have hz := int_eq_zero_of_uniformizer 1 (a - b) (by simpa using h1)
  norm_num at hz

/-- Every actual crystal class has exactly one exponent tuple for a fixed longest word. -/
theorem original_PBW_longest_unique_exponent (hw₀ : cs.wordProd w = cs.longestElement)
    (u : List I) :
    ∃! c : Fin w.length → ℕ, ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
        (e : K) • B u ∈ P := by
  obtain ⟨c, e, he, hc⟩ := original_PBW_longest_coverage R hw hw₀ u
  refine ⟨c, ⟨e, he, hc⟩, ?_⟩
  rintro d ⟨f, hf, hd⟩
  exact original_PBW_unsigned_injective R hw d c hf he hd hc (by simp)

omit [Finite W] in
/-- The exponent and sign are independent of the chosen word representative of a class. -/
theorem original_PBW_longest_representative_independent
    (c d : Fin w.length → ℕ) {e f : ℤ} {u t : List I}
    (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (hc : (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
      (e : K) • B u ∈ P)
    (hd : (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw d) -
      (f : K) • B t ∈ P)
    (hut : B u - B t ∈ P) : c = d ∧ e = f := by
  have hcd := original_PBW_unsigned_injective R hw c d he hf hc hd hut
  subst d
  exact ⟨rfl, (signed_residue_unique he hf hc hd).1⟩

/-- For the unique exponent tuple the sign is also unique; no positivity is claimed. -/
theorem original_PBW_longest_unique_signed_exponent
    (hw₀ : cs.wordProd w = cs.longestElement) (u : List I) :
    ∃! c : Fin w.length → ℕ, ∃! e : ℤ, (e = 1 ∨ e = -1) ∧
      (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
        (e : K) • B u ∈ P := by
  obtain ⟨c, e, he, hc⟩ := original_PBW_longest_coverage R hw hw₀ u
  refine ⟨c, ⟨e, ⟨he, hc⟩, ?_⟩, ?_⟩
  · rintro f ⟨hf, hd⟩
    exact (signed_residue_unique hf he hd hc).1
  · rintro d ⟨f, ⟨hf, hd⟩, -⟩
    exact original_PBW_unsigned_injective R hw d c hf he hd hc (by simp)
end PBWSignedCrystal
