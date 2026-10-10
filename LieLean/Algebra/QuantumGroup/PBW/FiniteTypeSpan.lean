/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.SimplyLacedLongestSpan
import LieLean.Algebra.QuantumGroup.PBW.RankTwoG2BraidSpan

/-!
# Reduced-word independence of ordered PBW spans and longest-word spanning in finite type

## Main results

* `QuantumGroup.span_pbwMonomial_of_braidMove_of_not_root`: every actual Coxeter braid move
  preserves the ordered PBW span for the constructed braid automorphisms at a nonzero parameter
  which is not a root of unity, whenever `aᵢⱼaⱼᵢ ≤ 3` for all `i ≠ j` (the four rank-two
  cases `A₁ × A₁`, `A₂`, `B₂`, `G₂`, in both orientations).
* `QuantumGroup.span_pbwMonomial_of_isReduced_of_isFiniteCartan`: in finite type, reduced words
  with the same Coxeter-group product have equal ordered PBW spans ([Jan] Prop. 8.22 a),
  [Lus] Prop. 40.2.1 (b)).
* `QuantumGroup.span_pbwMonomial_longest_of_isFiniteCartan`: in finite type the ordered monomials
  along any reduced word of the longest element span `U⁺`, over any field, at any nonzero
  parameter which is not a root of unity ([Jan] Thm. 8.24, stated there for the opposite
  multiplication order; [Lus] Cor. 40.2.2, over `ℚ(v)`).

Spanning follows as in the simply-laced case: every simple reflection is a left descent of the
longest element, so for each `i` some reduced word of `w₀` starts with `i`, and its ordered span
is stable under left multiplication by `Eᵢ`.

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, §8.21–8.24.
* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §40.2.

The rank-two inputs ([Jan] Prop. 8.22 b)) are reconstructed (`RankTwoA2ContextSpan`,
`RankTwoB2BraidSpan`, `RankTwoG2BraidSpan`).
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]
  (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

omit [DecidableEq I] in
/-- The pairs of off-diagonal entries of a generalized Cartan matrix with `aᵢⱼaⱼᵢ ≤ 3`. -/
lemma cartanMatrix_pair_cases {i j : I} (hij : i ≠ j)
    (h3 : D.cartanMatrix i j * D.cartanMatrix j i ≤ 3) :
    (D.cartanMatrix i j = 0 ∧ D.cartanMatrix j i = 0) ∨
    (D.cartanMatrix i j = -1 ∧ D.cartanMatrix j i = -1) ∨
    (D.cartanMatrix i j = -2 ∧ D.cartanMatrix j i = -1) ∨
    (D.cartanMatrix i j = -1 ∧ D.cartanMatrix j i = -2) ∨
    (D.cartanMatrix i j = -3 ∧ D.cartanMatrix j i = -1) ∨
    (D.cartanMatrix i j = -1 ∧ D.cartanMatrix j i = -3) := by
  have hA := D.isGeneralizedCartan_cartanMatrix
  have ha := hA.offDiag_nonpos i j hij
  have hb := hA.offDiag_nonpos j i hij.symm
  have hz := hA.zero_comm i j
  set a := D.cartanMatrix i j
  set b := D.cartanMatrix j i
  by_cases h0 : a = 0
  · exact Or.inl ⟨h0, hz.mp h0⟩
  have hb0 : b ≠ 0 := fun h ↦ h0 (hz.mpr h)
  have ha1 : a ≤ -1 := by omega
  have hb1 : b ≤ -1 := by omega
  have ha3 : -3 ≤ a := by nlinarith
  have hb3 : -3 ≤ b := by nlinarith
  interval_cases a <;> interval_cases b <;> simp_all

include hv

/-- **Braid-move invariance.** Every actual Coxeter braid move preserves the ordered PBW span
of the constructed braid automorphisms at a non-root-of-unity parameter, assuming
`aᵢⱼaⱼᵢ ≤ 3` for `i ≠ j` (true in finite type). -/
theorem span_pbwMonomial_of_braidMove_of_not_root
    (hfin : ∀ i j, i ≠ j → D.cartanMatrix i j * D.cartanMatrix j i ≤ 3) {u w : List I}
    (hm : D.cartanMatrix.coxeterMatrix.BraidMove u w) :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv) (E R v) u)) =
      Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
        (braidEquivOfNotRoot R hv) (E R v) w)) := by
  obtain ⟨p, s, i, j, hij, _, rfl, rfl⟩ := hm
  rcases cartanMatrix_pair_cases hij (hfin i j hij) with
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hm : D.cartanMatrix.coxeterMatrix i j = 2 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij, ha, hb]
      rfl
    have hm' : D.cartanMatrix.coxeterMatrix j i = 2 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij.symm, ha, hb]
      rfl
    have hw : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix i j = [i, j] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm]
      rfl
    have hw' : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix j i = [j, i] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm']
      rfl
    rw [hw, hw']
    exact span_pbwMonomial_commuting_context_of_not_root R v hv hij ha p s
  · have hm : D.cartanMatrix.coxeterMatrix i j = 3 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij, ha, hb]
      rfl
    have hm' : D.cartanMatrix.coxeterMatrix j i = 3 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij.symm, ha, hb]
      rfl
    have hw : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix i j = [j, i, j] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm]
      rfl
    have hw' : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix j i = [i, j, i] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm']
      rfl
    rw [hw, hw']
    exact (span_pbwMonomial_a2_context_of_not_root R v hij ha hb hv p s).symm
  · have hm : D.cartanMatrix.coxeterMatrix i j = 4 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij, ha, hb]
      rfl
    have hm' : D.cartanMatrix.coxeterMatrix j i = 4 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij.symm, ha, hb]
      rfl
    have hw : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix i j = [i, j, i, j] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm]
      rfl
    have hw' : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix j i = [j, i, j, i] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm']
      rfl
    rw [hw, hw']
    exact span_pbwMonomial_b2_context_of_not_root R v hij ha hb hv p s
  · have hm : D.cartanMatrix.coxeterMatrix i j = 4 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij, ha, hb]
      rfl
    have hm' : D.cartanMatrix.coxeterMatrix j i = 4 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij.symm, ha, hb]
      rfl
    have hw : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix i j = [i, j, i, j] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm]
      rfl
    have hw' : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix j i = [j, i, j, i] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm']
      rfl
    rw [hw, hw']
    exact (span_pbwMonomial_b2_context_of_not_root R v hij.symm hb ha hv p s).symm
  · have hm : D.cartanMatrix.coxeterMatrix i j = 6 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij, ha, hb]
      rfl
    have hm' : D.cartanMatrix.coxeterMatrix j i = 6 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij.symm, ha, hb]
      rfl
    have hw : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix i j = [i, j, i, j, i, j] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm]
      rfl
    have hw' : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix j i = [j, i, j, i, j, i] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm']
      rfl
    rw [hw, hw']
    exact span_pbwMonomial_g2_context_of_not_root R v hij ha hb hv p s
  · have hm : D.cartanMatrix.coxeterMatrix i j = 6 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij, ha, hb]
      rfl
    have hm' : D.cartanMatrix.coxeterMatrix j i = 6 := by
      rw [Matrix.coxeterMatrix_apply_of_ne _ hij.symm, ha, hb]
      rfl
    have hw : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix i j = [i, j, i, j, i, j] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm]
      rfl
    have hw' : CoxeterSystem.braidWord D.cartanMatrix.coxeterMatrix j i = [j, i, j, i, j, i] := by
      simp only [CoxeterSystem.braidWord]
      rw [hm']
      rfl
    rw [hw, hw']
    exact (span_pbwMonomial_g2_context_of_not_root R v hij.symm hb ha hv p s).symm

/-- **Reduced-word independence** ([Jan] Prop. 8.22 a)): reduced words with the same
Coxeter-group product have the same actual ordered PBW span, if `aᵢⱼaⱼᵢ ≤ 3` for `i ≠ j`. -/
theorem span_pbwMonomial_of_isReduced_of_not_root
    (hfin : ∀ i j, i ≠ j → D.cartanMatrix i j * D.cartanMatrix j i ≤ 3) {W : Type*} [Group W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {u w : List I}
    (hu : cs.IsReduced u) (hw : cs.IsReduced w) (huw : cs.wordProd u = cs.wordProd w) :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv) (E R v) u)) =
      Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
        (braidEquivOfNotRoot R hv) (E R v) w)) :=
  CoxeterSystem.eq_of_reflTransGen_braidMove
    (fun _ _ _ hm ↦ span_pbwMonomial_of_braidMove_of_not_root R v hv hfin hm)
    hu (CoxeterSystem.reflTransGen_braidMove_of_isReduced hu hw huw)

/-- **Reduced-word independence in finite type** ([Jan] Prop. 8.22 a), [Lus] Prop. 40.2.1 (b)):
over any field, at a nonzero
parameter which is not a root of unity. -/
theorem span_pbwMonomial_of_isReduced_of_isFiniteCartan [Fintype I]
    (hA : D.cartanMatrix.IsFiniteCartan) {W : Type*} [Group W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {u w : List I}
    (hu : cs.IsReduced u) (hw : cs.IsReduced w) (huw : cs.wordProd u = cs.wordProd w) :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv) (E R v) u)) =
      Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
        (braidEquivOfNotRoot R hv) (E R v) w)) :=
  span_pbwMonomial_of_isReduced_of_not_root R v hv
    (fun _ _ hij ↦ hA.mul_le_three hij) cs hu hw huw

variable [Fintype I] (hA : D.cartanMatrix.IsFiniteCartan) {W : Type*} [Group W] [Finite W]
  (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W)
  {w : List I} (hw : cs.IsReduced w) (hw₀ : cs.wordProd w = cs.longestElement)

include hA hw hw₀

/-- The ordered longest-word span is stable under left multiplication by each `Eᵢ`. -/
theorem E_mul_mem_span_pbwMonomial_longest_of_isFiniteCartan (i : I) {x : QuantumGroup R v}
    (hx : x ∈ Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv) (E R v) w))) :
    E R v i * x ∈ Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv) (E R v) w)) := by
  obtain ⟨u, hu, hu₀⟩ := CoxeterSystem.exists_reduced_cons_longest cs i
  have hs := span_pbwMonomial_of_isReduced_of_isFiniteCartan R v hv hA cs hu hw
    (hu₀.trans hw₀.symm)
  rw [← hs] at hx ⊢
  exact CoxeterSystem.mul_mem_pbwSpan_cons _ _ i u hx

/-- **PBW spanning in finite type** ([Jan] Thm. 8.24, [Lus] Cor. 40.2.2): the ordered monomials
in the root vectors along any reduced word of the longest element span `U⁺`, over any field, at any
nonzero parameter which is not a root of unity. -/
theorem span_pbwMonomial_longest_of_isFiniteCartan :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv) (E R v) w)) =
      (Algebra.adjoin k (Set.range (E R v))).toSubmodule := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨c, rfl⟩
    exact CoxeterSystem.pbwMonomial_mem _ _
      (fun n hn ↦ rootVector_mem_adjoin_of_not_root hv hw n hn) c
  · let S := Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv) (E R v) w))
    have h1 : (1 : QuantumGroup R v) ∈ S := CoxeterSystem.one_mem_pbwSpan _ _ w
    intro x hx
    have hmul : ∀ y ∈ S, x * y ∈ S := by
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact fun y hy ↦ E_mul_mem_span_pbwMonomial_longest_of_isFiniteCartan
          R v hv hA cs hw hw₀ i hy
      | algebraMap a =>
        intro y hy
        simpa only [Algebra.smul_def] using S.smul_mem a hy
      | add x z _ _ hx hz =>
        intro y hy
        simpa only [add_mul] using S.add_mem (hx y hy) (hz y hy)
      | mul x z _ _ hx hz =>
        intro y hy
        simpa only [mul_assoc] using hx (z * y) (hz y hy)
    simpa only [mul_one] using hmul 1 h1

end LieLean.QuantumGroup
