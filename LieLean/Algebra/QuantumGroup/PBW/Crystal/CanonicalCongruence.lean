/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.CanonicalBasis
import LieLean.Algebra.QuantumGroup.PBW.Crystal.IntegralPBW

/-!
# PBW elements are congruent to canonical basis elements ([Lus] 41.1.6)

For a reduced word `w` and an exponent tuple `c`, let `X_c` be the PBW element of `f ≅ U⁻`
(the inverse image in the integral form of the `T'_{i,-1}` monomial, [Lus] 41.1.5,
`Modified.integralPBWPreimage`, viewed in `U⁻` as `PBWSignedCrystal.pbwNegative`). [Lus] 41.1.6
asserts that `X_c ∈ ℒ(f)` and that `X_c ≡ ±b mod v⁻¹ℒ(f)` for a unique `b ∈ B`. The lattice part
is `PBWProductNorm.mem_lattice_degree`; this file proves the congruence part.

## Main results

* `PBWSignedCrystal.exists_canonical_congruence`: `X_c ≡ e • b mod v⁻¹ℒ(∞)` for some `b ∈ B` and
  `e = ±1`.
* `PBWSignedCrystal.existsUnique_canonical_congruence`: [Lus] 41.1.6, congruence part. The element
  `b ∈ B` is unique, and so is the sign.

## Implementation notes

Our own deduction from results already in the library. `X_c` has a signed crystal residue
`±f̃_u 1` (`original_PBW_unique_signed`, from integrality, lattice membership and norm residue one),
and the canonical basis is Kashiwara's global basis, `B = {G(b)}` with `G(b) ≡ b mod v⁻¹ℒ(∞)`
(`mem_canonicalBasis_iff`, `negGlobal_sub_mem`). Uniqueness uses that distinct elements of
`B(∞)`, and `b`, `-b'`, never agree modulo `v⁻¹ℒ(∞)`.

The statement holds for every reduced word in every Coxeter system of the Cartan matrix, with no
finite-Weyl-group or longest-word hypothesis; only finitely many simple roots are needed. The
lattice `ℒ(∞) ⊆ U⁻` corresponds to Lusztig's `ℒ(f)` under `negativeQuotientEquiv`
(`quotientCrystalLattice`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 41.1.5, 41.1.6.
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

/-- Two crystal words that agree modulo `v⁻¹ℒ(∞)` have the same weight. -/
lemma wordWeight_eq_of_sub_mem {u t : List I} (h : B u - B t ∈ P) :
    wordWeight u = wordWeight t :=
  wordWeight_eq_of_mem_Uw (fWi_mem_Uw u) (word_not_mem_uniformizer t)
    (by simpa using neg_mem h)

/-- `G(b)` is congruent to `f̃_u 1` modulo `v⁻¹ℒ(∞)` for every word `u` in the class `b`. -/
lemma negGlobal_mk_sub_mem (u : List I) :
    negGlobal D (wordWeight u) (Quotient.mk _ ⟨u, rfl⟩) - B u ∈ P := by
  have h₁ := negGlobal_sub_mem D (wordWeight u) (Quotient.mk _ ⟨u, rfl⟩)
  have h₂ : B (Quotient.out (Quotient.mk (negCrystalSetoid D (wordWeight u)) ⟨u, rfl⟩)).1 -
      B u ∈ P :=
    Quotient.mk_out (s := negCrystalSetoid D (wordWeight u)) ⟨u, rfl⟩
  simpa using add_mem h₁ h₂

/-- Every element of `B` is congruent to some `f̃_u 1` modulo `v⁻¹ℒ(∞)`. -/
lemma exists_word_of_mem_canonicalBasis {x : Um D v} (hx : x ∈ canonicalBasis D) :
    ∃ u : List I, x - B u ∈ P := by
  obtain ⟨ν, b, rfl⟩ := (mem_canonicalBasis_iff D).1 hx
  exact ⟨(Quotient.out b).1, negGlobal_sub_mem D ν b⟩

/-- Two elements of `B` congruent to the same `f̃_u 1` modulo `v⁻¹ℒ(∞)` are equal. -/
lemma eq_of_mem_canonicalBasis {x y : Um D v} (hx : x ∈ canonicalBasis D)
    (hy : y ∈ canonicalBasis D) {u t : List I} (hxu : x - B u ∈ P) (hyt : y - B t ∈ P)
    (hut : B u - B t ∈ P) : x = y := by
  obtain ⟨ν, b, rfl⟩ := (mem_canonicalBasis_iff D).1 hx
  obtain ⟨μ, b', rfl⟩ := (mem_canonicalBasis_iff D).1 hy
  have hb := negGlobal_sub_mem D ν b
  have hb' := negGlobal_sub_mem D μ b'
  have hbb' : B (Quotient.out b).1 - B (Quotient.out b').1 ∈ P := by
    convert add_mem (add_mem (neg_mem hb) hxu) (add_mem hut (add_mem (neg_mem hyt) hb'))
      using 1
    abel
  have hνμ : ν = μ := by
    rw [← (Quotient.out b).2, ← (Quotient.out b').2]
    exact wordWeight_eq_of_sub_mem hbb'
  subst hνμ
  have : b = b' := by
    rw [← Quotient.out_eq b, ← Quotient.out_eq b']
    exact Quotient.sound hbb'
  rw [this]

variable {Y : Type*} [AddCommGroup Y] (R : D.RootDatum Y)
  {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}

/-- Every PBW element is congruent to `±b`, `b ∈ B`, modulo `v⁻¹ℒ(∞)`. -/
theorem exists_canonical_congruence {w : List I} (hw : cs.IsReduced w) (c : Fin w.length → ℕ) :
    ∃ x ∈ canonicalBasis D, ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ pbwNegative R hw c - (e : K) • x ∈ P := by
  obtain ⟨u, e, he, hX, -⟩ := original_PBW_unique_signed R hw c
  refine ⟨negGlobal D (wordWeight u) (Quotient.mk _ ⟨u, rfl⟩),
    (mem_canonicalBasis_iff D).2 ⟨_, _, rfl⟩, e, he, ?_⟩
  have hG := negGlobal_mk_sub_mem (D := D) u
  have : (e : K) • (negGlobal D (wordWeight u) (Quotient.mk _ ⟨u, rfl⟩) - B u) ∈ P :=
    Submodule.smul_of_tower_mem _ _ hG
  convert sub_mem hX this using 1
  rw [smul_sub]
  abel

/-- **[Lus] 41.1.6**, congruence part: for every reduced word `w` and exponent tuple `c`, the PBW
element `X_c` is congruent modulo `v⁻¹ℒ(∞)` to `±b` for a unique `b` in the canonical basis `B`;
the sign is unique as well. -/
theorem existsUnique_canonical_congruence {w : List I} (hw : cs.IsReduced w)
    (c : Fin w.length → ℕ) :
    ∃! x, x ∈ canonicalBasis D ∧
      ∃! e : ℤ, (e = 1 ∨ e = -1) ∧ pbwNegative R hw c - (e : K) • x ∈ P := by
  obtain ⟨x, hx, e, he, hXx⟩ := exists_canonical_congruence R hw c
  obtain ⟨u, hxu⟩ := exists_word_of_mem_canonicalBasis hx
  have hXu : pbwNegative R hw c - (e : K) • B u ∈ P := by
    have : (e : K) • (x - B u) ∈ P := Submodule.smul_of_tower_mem _ _ hxu
    convert add_mem hXx this using 1
    rw [smul_sub]
    abel
  refine ⟨x, ⟨hx, e, ⟨he, hXx⟩, ?_⟩, ?_⟩
  · rintro f ⟨hf, hXf⟩
    have hXfu : pbwNegative R hw c - (f : K) • B u ∈ P := by
      have : (f : K) • (x - B u) ∈ P := Submodule.smul_of_tower_mem _ _ hxu
      convert add_mem hXf this using 1
      rw [smul_sub]
      abel
    exact (signed_residue_unique hf he hXfu hXu).1
  · rintro y ⟨hy, f, ⟨hf, hXy⟩, -⟩
    obtain ⟨t, hyt⟩ := exists_word_of_mem_canonicalBasis hy
    have hXt : pbwNegative R hw c - (f : K) • B t ∈ P := by
      have : (f : K) • (y - B t) ∈ P := Submodule.smul_of_tower_mem _ _ hyt
      convert add_mem hXy this using 1
      rw [smul_sub]
      abel
    obtain ⟨-, htu⟩ := signed_residue_unique hf he hXt hXu
    exact eq_of_mem_canonicalBasis hy hx hyt hxu htu

end PBWSignedCrystal
