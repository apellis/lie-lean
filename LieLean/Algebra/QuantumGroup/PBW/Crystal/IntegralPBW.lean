/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.Crystal.Signed

/-! # Original arbitrary PBW preimages have unique signed crystal residues

All integral, lattice, and norm conditions are discharged for the actual PBW preimages.
Uniqueness is of sign and crystal residue class, never of the representing word.
Fixed-reduced-word injectivity follows from actual PBW orthogonality. No global basis
or reduced-word independence assertion is made.
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

variable {Y : Type*} [AddCommGroup Y] (R : D.RootDatum Y)
  {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}

/-- Unique signed crystal residue of every original arbitrary integral PBW preimage.
There are no additional integral, lattice, norm, homogeneous, finite-Weyl-group,
longest-word, root-independence, or regularity premises. -/
theorem original_PBW_unique_signed {w : List I} (hw : cs.IsReduced w)
    (c : Fin w.length → ℕ) :
    ∃ (u : List I) (e : ℤ), (e = 1 ∨ e = -1) ∧
      (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
        (e : K) • B u ∈ P ∧ B u ∉ P ∧
      (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) ∉ P ∧
      ∀ (t : List I) (f : ℤ), (f = 1 ∨ f = -1) →
        (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
          (f : K) • B t ∈ P → e = f ∧ B u - B t ∈ P := by
  apply unique_signed_crystal_residue D
  · simpa only [LinearEquiv.apply_symm_apply] using
      (Modified.integralPBWPreimage R hw c).property
  · exact PBWProductNorm.mem_lattice_degree R hw c
  · exact PBWProductNorm.norm_residue R hw c

/-- Actual PBW residues for one fixed reduced word distinguish all exponent tuples. -/
theorem original_PBW_residue_injective {w : List I} (hw : cs.IsReduced w)
    (c d : Fin w.length → ℕ)
    (h : (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
      (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw d) ∈ P) : c = d := by
  by_contra hcd
  exact pbw_sub_smul_not_mem_uniformizer R hw c d hcd 1 (by simpa using h)

/-- Unsigned crystal classes selected from the signed PBW residues are injective for a
fixed reduced word, even when the two signs differ. -/
theorem original_PBW_unsigned_injective {w : List I} (hw : cs.IsReduced w)
    (c d : Fin w.length → ℕ) {e f : ℤ} {u t : List I}
    (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (hc : (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
      (e : K) • B u ∈ P)
    (hd : (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw d) -
      (f : K) • B t ∈ P)
    (hut : B u - B t ∈ P) : c = d :=
  pbw_unsigned_residue_injective R hw c d he hf hc hd hut

/-- Empty reduced words are included, with no nonempty or positive-degree premise. -/
theorem original_PBW_empty_signed (hw : cs.IsReduced []) (c : Fin [].length → ℕ) :
    ∃ (u : List I) (e : ℤ), (e = 1 ∨ e = -1) ∧
      (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw c) -
        (e : K) • B u ∈ P := by
  obtain ⟨u, e, he, hx, -⟩ := original_PBW_unique_signed R hw c
  exact ⟨u, e, he, hx⟩

/-- The all-zero exponent tuple is included for every reduced word. -/
theorem original_PBW_zero_signed {w : List I} (hw : cs.IsReduced w) :
    ∃ (u : List I) (e : ℤ), (e = 1 ∨ e = -1) ∧
      (negativeQuotientEquiv D).symm (Modified.integralPBWPreimage R hw (fun _ ↦ 0)) -
        (e : K) • B u ∈ P := by
  obtain ⟨u, e, he, hx, -⟩ := original_PBW_unique_signed R hw (fun _ ↦ 0)
  exact ⟨u, e, he, hx⟩
end PBWSignedCrystal
