/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingPositiveSeam

/-!
# Equality transport and crossing output reconstruction

## Main results
In addition to the equality transport, this complete standalone candidate contains
`GluingPair.exists_f_gluing_crossing`, `f_isIntegral_crossing`, and the literal
crossing-time corollary `exists_f_gluing_crossing_of_times`. Original source powers
and strict coarsened representatives are distinguished in the theorem contracts.
The reconstructed crossing proof lowers the left source to the bottom of its string;
it does not identify that exponent with the intermediate exponent in the printed proof.

Actual strict gluing output sectors for Proposition 5.6; source powers and strict
coarsenings are kept separate. No output chains or stability are hypotheses.

## References
Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), Definition 5.3 and Proposition 5.6, pp.514–516.
proofs reconstructed in the literal finite-source encoding.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- Both auxiliary signs of the right last-minimum equality seam, retaining the
actual source string independently of its strict coarsening. -/
theorem exists_f_gluing_at_right_cut {i : ι}
    (hum : g.path.pairing i g.s' = g.path.minPairing i)
    (hlast : ∀ t ∈ Ioc (g.s' : ℝ) 1, g.path.minPairing i < g.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    ∃ (k : ℕ) (υ τ : Presentation P hA) (g' : GluingPair σ τ),
      δ.path.pairing i g.s' = δ.path.minPairing i + k ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i (k + 1) δ.path = some υ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i (k + 1) υ.path = some δ.path ∧
      (∀ t : ℝ, (g.s' : ℝ) ≤ t →
        τ.path t - τ.path g.s' = υ.path t - υ.path g.s') ∧
      (τ.x 0 : Dual ℝ H) = P.reflection hA i (δ.x 0) ∧ g'.path = η ∧
      g'.s = g.s ∧ g'.s' = g.s' ∧
      g'.ν = (if g.μ (P.coroot i) ≤ 0 then g.ν else P.reflection hA i g.ν) ∧
      g'.μ = (if g.μ (P.coroot i) ≤ 0 then g.μ else P.reflection hA i g.μ) ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (δ.x 0) := by
  by_cases hμ : g.μ (P.coroot i) ≤ 0
  · simpa only [ite_eq_left hμ] using g.exists_f_gluing_at_cut_of_nonpos hum hlast hμ hf
  · simpa only [ite_eq_right hμ] using
      g.exists_f_gluing_at_cut_of_pos hum hlast (lt_of_not_ge hμ) hf

/-- Both auxiliary signs of left FIRST-minimum equality raising, by literal reversal.
The terminal source direction reflects; the auxiliaries reflect exactly when ν is negative.
This is the dual of the right last-minimum equality sector of Proposition 5.6. -/
theorem exists_e_gluing_at_left_cut {i : ι}
    (hum : g.path.pairing i g.s = g.path.minPairing i)
    (hfirst : ∀ t ∈ Ico (0 : ℝ) g.s, g.path.minPairing i < g.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)} (he : LittelmannPath.e i g.path = some η) :
    ∃ (k : ℕ) (υ τ : Presentation P hA) (g' : GluingPair τ δ),
      σ.path.pairing i g.s = σ.path.minPairing i + k ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i (k + 1) σ.path = some υ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i (k + 1) υ.path = some σ.path ∧
      (∀ t : ℝ, t ≤ (g.s : ℝ) →
        τ.path t - τ.path g.s = υ.path t - υ.path g.s) ∧
      (τ.x (Fin.last τ.n) : Dual ℝ H) =
        P.reflection hA i (σ.x (Fin.last σ.n)) ∧
      g'.path = η ∧
      g'.s = g.s ∧ g'.s' = g.s' ∧
      g'.ν = (if 0 ≤ g.ν (P.coroot i) then g.ν else P.reflection hA i g.ν) ∧
      g'.μ = (if 0 ≤ g.ν (P.coroot i) then g.μ else P.reflection hA i g.μ) ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  have hm : g.reverse.path.pairing i g.reverse.s' =
      g.reverse.path.minPairing i := by
    rw [g.reverse_path, pairing_rev, minPairing_rev]
    change g.path.pairing i (1 - ((1 - g.s : ℚ) : ℝ)) - _ = _
    simp only [Rat.cast_sub, Rat.cast_one, sub_sub_cancel, hum]
  have hl : ∀ t ∈ Ioc (g.reverse.s' : ℝ) 1,
      g.reverse.path.minPairing i < g.reverse.path.pairing i t := by
    intro t ht
    have ht' : 1 - t ∈ Ico (0 : ℝ) g.s := by
      change ((1 - g.s : ℚ) : ℝ) < t ∧ t ≤ 1 at ht
      push_cast at ht
      constructor <;> linarith [ht.1, ht.2]
    rw [g.reverse_path, pairing_rev, minPairing_rev]
    exact sub_lt_sub_right (hfirst _ ht') _
  have hf : LittelmannPath.f i g.reverse.path = some η.rev := by
    rw [g.reverse_path, f_rev, he, Option.map_some]
  obtain ⟨k, υ, τ, gτ, hk, hυ, -, ht, hx, hp, hs, hs', hν, hμ, ho⟩ :=
    g.reverse.exists_f_gluing_at_right_cut hm hl hf
  have hk' : σ.path.pairing i g.s = σ.path.minPairing i + k := by
    change σ.reverse.path.pairing i ((1 - g.s : ℚ) : ℝ) = _ at hk
    rw [Presentation.reverse_path, pairing_rev, minPairing_rev] at hk
    simp only [Rat.cast_sub, Rat.cast_one, sub_sub_cancel] at hk
    linarith
  have heυ : (LittelmannPath.crystal (P.pathSpace hA)).eIter i (k + 1) σ.path =
      some υ.reverse.path := by
    rw [Presentation.reverse_path, fIter_rev_eq_map_eIter] at hυ
    have hh := congrArg (Option.map LittelmannPath.rev) hυ
    simp only [Option.map_map, Function.comp_def, rev_rev, Option.map_some] at hh
    change Option.map id _ = _ at hh
    rw [Option.map_id] at hh
    rw [Presentation.reverse_path]
    exact hh
  have hout : ∃ (k : ℕ) (υ τ : Presentation P hA)
      (g' : GluingPair τ δ.reverse.reverse),
      σ.path.pairing i g.s = σ.path.minPairing i + k ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i (k + 1) σ.path = some υ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i (k + 1) υ.path = some σ.path ∧
      (∀ t : ℝ, t ≤ (g.s : ℝ) →
        τ.path t - τ.path g.s = υ.path t - υ.path g.s) ∧
      (τ.x (Fin.last τ.n) : Dual ℝ H) =
        P.reflection hA i (σ.x (Fin.last σ.n)) ∧
      g'.path = η ∧
      g'.s = g.s ∧ g'.s' = g.s' ∧
      g'.ν = (if 0 ≤ g.ν (P.coroot i) then g.ν else P.reflection hA i g.ν) ∧
      g'.μ = (if 0 ≤ g.ν (P.coroot i) then g.μ else P.reflection hA i g.μ) ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
    refine ⟨k, υ.reverse, τ.reverse, gτ.reverse, hk', heυ,
      (Crystal.fIter_eq_some_iff _ _ _ _).mpr heυ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t hts
      have hh := ht (1 - t) (by
        change ((1 - g.s : ℚ) : ℝ) ≤ 1 - t
        push_cast
        linarith)
      change τ.path (1 - t) - τ.path ((1 - g.s : ℚ) : ℝ) =
        υ.path (1 - t) - υ.path ((1 - g.s : ℚ) : ℝ) at hh
      push_cast at hh
      simp only [Presentation.reverse_path, rev_apply]
      convert hh using 1 <;> abel
    · change -(τ.x (Fin.last τ.n).rev : Dual ℝ H) = _
      rw [Fin.rev_last, hx]
      change -P.reflection hA i (-(σ.x (0 : Fin (σ.n + 1)).rev : Dual ℝ H)) = _
      rw [Fin.rev_zero, map_neg, neg_neg]
    · rw [gτ.reverse_path, hp, rev_rev]
    · change 1 - gτ.s' = g.s
      rw [hs']
      change 1 - (1 - g.s) = g.s
      ring
    · change 1 - gτ.s = g.s'
      rw [hs]
      change 1 - (1 - g.s') = g.s'
      ring
    · change -gτ.μ = _
      rw [hμ]
      change -(if (-g.ν) (P.coroot i) ≤ 0 then -g.ν else
        P.reflection hA i (-g.ν)) = _
      simp only [LinearMap.neg_apply, neg_nonpos, map_neg]
      split_ifs <;> simp
    · change -gτ.ν = _
      rw [hν]
      change -(if (-g.ν) (P.coroot i) ≤ 0 then -g.μ else
        P.reflection hA i (-g.μ)) = _
      simp only [LinearMap.neg_apply, neg_nonpos, map_neg]
      split_ifs <;> simp
    · intro j
      obtain ⟨v, hv⟩ := ho j.rev
      obtain ⟨w, hw⟩ := σ.orbit (Fin.last σ.n)
      refine ⟨v * w, ?_⟩
      change -(τ.x j.rev : Dual ℝ H) = (v * w).1 (σ.x 0)
      rw [hv]
      change -v.1 (-(σ.x (0 : Fin (σ.n + 1)).rev : Dual ℝ H)) = _
      rw [Fin.rev_zero, map_neg, neg_neg, hw, Subgroup.coe_mul, LinearEquiv.mul_apply]
  rw [δ.reverse_reverse] at hout
  exact hout

/-- All-root output integrality in the left first-minimum equality sector. -/
theorem e_isIntegral_at_left_cut {i : ι}
    (hum : g.path.pairing i g.s = g.path.minPairing i)
    (hfirst : ∀ t ∈ Ico (0 : ℝ) g.s, g.path.minPairing i < g.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)} (he : LittelmannPath.e i g.path = some η) :
    η.IsIntegral := by
  obtain ⟨k, υ, τ, g', -, -, -, -, -, hp, -⟩ :=
    g.exists_e_gluing_at_left_cut hum hfirst he
  rw [← hp]
  exact g'.isIntegral

end GluingPair
end Matrix.Realization.LSGeneralClass

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

/-!
# Actual iterated lowering formulas for crossing gluing sectors

## Main results
Closed running-minimum formulas for actual successful source powers.

## References
Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), §1 and Proposition 5.6, pp.515–516. Reconstructed from the actual operators.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- The right running minimum after one ACTUAL lowering, including the clipped region. -/
theorem rightMin_f_eq_max {π η : LittelmannPath (P.pathSpace hA)} {i : ι}
    (hf : LittelmannPath.f i π = some η) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    η.rightMin i t = max (π.rightMin i t - 2) (π.minPairing i - 1) := by
  have hp (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : η.pairing i v = π.pairing i v -
      2 * (min (π.rightMin i v) (π.minPairing i + 1) - π.minPairing i) := by
    rw [pairing, f_apply hf hv]
    change (π v - _ • P.root i) (P.coroot i) = _
    simp only [LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, P.root_coroot_self hA]
    dsimp only [pairing, pathSpace_coroot]
    ring
  have hm : η.minPairing i = π.minPairing i - 1 := by
    have hh := minPairing_of_e_eq_some (f_eq_some_iff.mp hf)
    linarith
  have hlow : max (π.rightMin i t - 2) (π.minPairing i - 1) ≤ η.rightMin i t := by
    apply max_le
    · apply η.le_rightMin ht.2
      intro v hv
      rw [hp v ⟨ht.1.trans hv.1, hv.2⟩]
      have hh := π.rightMin_le (i := i) hv
      have hc := min_le_right (π.rightMin i v) (π.minPairing i + 1)
      linarith
    · rw [← hm]
      exact η.le_rightMin ht.2 (fun v hv ↦ η.minPairing_le ⟨ht.1.trans hv.1, hv.2⟩)
  apply le_antisymm ?_ hlow
  by_cases hr : π.minPairing i + 1 ≤ π.rightMin i t
  · obtain ⟨v, hv, hvm⟩ := π.exists_rightMin i ht.2
    have hrv : π.rightMin i v = π.rightMin i t := le_antisymm
      ((π.rightMin_le ⟨le_rfl, hv.2⟩).trans_eq hvm)
      (π.le_rightMin hv.2 (fun u hu ↦ π.rightMin_le ⟨hv.1.trans hu.1, hu.2⟩))
    have hh := η.rightMin_le (i := i) hv
    rw [hp v ⟨ht.1.trans hv.1, hv.2⟩, hrv, min_eq_right hr, hvm] at hh
    exact hh.trans (by linarith [le_max_left (π.rightMin i t - 2) (π.minPairing i - 1)])
  · have hr' : π.rightMin i t ≤ π.minPairing i + 1 := (lt_of_not_ge hr).le
    obtain ⟨v, hv, hvm⟩ := π.exists_rightMin i ht.2
    have h1 : π.minPairing i + 1 ≤ π.pairing i 1 := by
      have hh := (f_eq_none_iff (i := i) (π := π)).not.mp (by rw [hf]; simp)
      push Not at hh
      linarith
    obtain ⟨u, hu, heq, hbefore⟩ := exists_first_eq
      ((π.continuous_pairing i).comp (continuous_const.sub continuous_id))
      (show (0 : ℝ) ≤ 1 - v by linarith [hv.2])
      (by simpa using h1) (by simpa using hvm.le.trans hr')
    change π.pairing i (1 - u) = π.minPairing i + 1 at heq
    change ∀ v ∈ Ico 0 u, π.minPairing i + 1 < π.pairing i (1 - v) at hbefore
    have hu01 : 1 - u ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hu.1, hu.2, hv.1, ht.1]
    have hru : π.rightMin i (1 - u) = π.minPairing i + 1 := by
      apply le_antisymm
      · exact (π.rightMin_le ⟨le_rfl, hu01.2⟩).trans_eq heq
      · apply π.le_rightMin hu01.2
        intro w hw
        rcases hw.1.eq_or_lt with he | he
        · rw [← he, heq]
        · have hh := hbefore (1 - w) ⟨by linarith [hw.2], by linarith⟩
          simpa only [sub_sub_cancel] using hh.le
    have hh := η.rightMin_le (i := i) (t := t)
      (show 1 - u ∈ Icc t 1 from ⟨by linarith [hu.2, hv.1], hu01.2⟩)
    rw [hp _ hu01, hru, min_self, heq] at hh
    exact hh.trans (by linarith [le_max_right (π.rightMin i t - 2) (π.minPairing i - 1)])

/-- Actual powers exist up to the available endpoint height, and have the uncluttered
closed coefficient needed to compare two different source exponents at a crossing seam. -/
theorem exists_fIter_formula (π : LittelmannPath (P.pathSpace hA)) (i : ι) (n : ℕ)
    (hn : π.minPairing i + n ≤ π.pairing i 1) :
    ∃ η : LittelmannPath (P.pathSpace hA),
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i n π = some η ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i n η = some π ∧
      η.minPairing i = π.minPairing i - n ∧
      ∀ t ∈ Icc (0 : ℝ) 1, η t = π t -
        (min (π.rightMin i t) (π.minPairing i + n) - π.minPairing i) • P.root i := by
  induction n generalizing π with
  | zero =>
    refine ⟨π, rfl, rfl, by simp, ?_⟩
    intro t ht
    have hh := π.le_rightMin ht.2
      (fun v hv ↦ π.minPairing_le (i := i) ⟨ht.1.trans hv.1, hv.2⟩)
    simp only [Nat.cast_zero, add_zero, min_eq_right hh, sub_self, zero_smul, sub_zero]
  | succ n ih =>
    have h1 : π.minPairing i + 1 ≤ π.pairing i 1 := by
      push_cast at hn
      linarith [Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨ζ, hζ⟩ : ∃ ζ, LittelmannPath.f i π = some ζ := by
      apply Option.ne_none_iff_exists'.mp
      intro hh
      have hbad := f_eq_none_iff.mp hh
      linarith
    have hm : ζ.minPairing i = π.minPairing i - 1 := by
      have hh := minPairing_of_e_eq_some (f_eq_some_iff.mp hζ)
      linarith
    have hp1 : ζ.pairing i 1 = π.pairing i 1 - 2 := by
      have hr : π.rightMin i 1 = π.pairing i 1 := le_antisymm
        (π.rightMin_le ⟨le_rfl, le_rfl⟩)
        (π.le_rightMin le_rfl (fun v hv ↦ by rw [le_antisymm hv.2 hv.1]))
      rw [pairing, f_apply hζ ⟨zero_le_one, le_rfl⟩, hr, min_eq_right h1]
      simp only [add_sub_cancel_left, one_smul, pathSpace_coroot, LinearMap.sub_apply]
      change π.pairing i 1 - (P.root i) (P.coroot i) = _
      rw [P.root_coroot_self hA]
    obtain ⟨η, hf, he, hmin, hform⟩ := ih ζ (by rw [hm, hp1]; push_cast at hn; linarith)
    have hiter : (LittelmannPath.crystal (P.pathSpace hA)).fIter i (n + 1) π =
        some η := by
      rw [Crystal.fIter_succ, LittelmannPath.crystal_f, hζ, Option.bind_some]
      exact hf
    refine ⟨η, hiter, (Crystal.fIter_eq_some_iff _ _ _ _).mp hiter, ?_, ?_⟩
    · rw [hmin, hm]
      push_cast
      ring
    · intro t ht
      rw [hform t ht, rightMin_f_eq_max hζ ht, hm, f_apply hζ ht]
      have hcoeff :
          (min (π.rightMin i t) (π.minPairing i + 1) - π.minPairing i) +
            (min (max (π.rightMin i t - 2) (π.minPairing i - 1))
              (π.minPairing i - 1 + n) - (π.minPairing i - 1)) =
          min (π.rightMin i t) (π.minPairing i + (n + 1 : ℕ)) - π.minPairing i := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast
        rcases le_total (π.rightMin i t) (π.minPairing i + 1) with h | h
        · rw [min_eq_left h, max_eq_right (by linarith),
            min_eq_left (by linarith), min_eq_left (by linarith)]
          ring
        · rw [min_eq_right h, max_eq_left (by linarith)]
          rcases le_total (π.rightMin i t) (π.minPairing i + (n + 1)) with hh | hh
          · rw [min_eq_left (by linarith), min_eq_left hh]
            ring
          · rw [min_eq_right (by linarith), min_eq_right hh]
            ring
      change π t - _ • P.root i - _ • P.root i = _
      rw [← sub_add_eq_sub_sub, ← add_smul, hcoeff]

/-- Source powers with the literal coefficient and a finite original-orbit presentation. -/
theorem Presentation.exists_fIter_formula (σ : Presentation P hA) (i : ι) (n : ℕ)
    (hn : σ.path.minPairing i + n ≤ σ.path.pairing i 1) :
    ∃ υ : Presentation P hA,
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i n σ.path = some υ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i n υ.path = some σ.path ∧
      (∀ t ∈ Icc (0 : ℝ) 1, υ.path t = σ.path t -
        (min (σ.path.rightMin i t) (σ.path.minPairing i + n) -
          σ.path.minPairing i) • P.root i) ∧
      ∀ j, ∃ w : P.weylGroup hA, (υ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  obtain ⟨η, hf, he, -, hform⟩ :=
    Matrix.Realization.LSGeneralClass.exists_fIter_formula σ.path i n hn
  obtain ⟨υ, hp, -, ho⟩ := σ.exists_fIter_presentation i n hf
  exact ⟨υ, by simpa only [hp] using hf, by simpa only [hp] using he,
    by simpa only [hp] using hform, ho⟩

/-- Discard a source suffix, preserving the retained prefix literally and the original orbit. -/
theorem Presentation.exists_coarsen_final (σ : Presentation P hA) {c : ℚ} (hc : 0 < c) :
    ∃ τ : Presentation P hA, τ.a (Fin.last τ.n).castSucc < c ∧
      (∀ t : ℝ, t ≤ (c : ℝ) → τ.path t = σ.path t) ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  obtain ⟨ρ, hcρ, ht, ho⟩ := σ.reverse.exists_coarsen_initial (c := 1 - c) (by linarith)
  have hdiff (t : ℝ) (htc : t ≤ (c : ℝ)) :
      ρ.reverse.path t - ρ.reverse.path c = σ.path t - σ.path c := by
    have hh := ht (1 - t) (by push_cast; linarith)
    simp only [Presentation.reverse_path, rev_apply, Rat.cast_sub, Rat.cast_one,
      sub_sub_cancel] at hh ⊢
    convert hh using 1 <;> abel
  have hzero := hdiff 0 (by exact_mod_cast hc.le)
  simp only [apply_zero, zero_sub, neg_inj] at hzero
  refine ⟨ρ.reverse, ?_, ?_, ?_⟩
  · change 1 - ρ.a (Fin.last ρ.n).castSucc.rev < c
    simpa only [Presentation.reverse, Fin.rev_castSucc, Fin.rev_last] using
      (show 1 - ρ.a (0 : Fin (ρ.n + 1)).succ < c by linarith)
  · intro t htc
    have hh := hdiff t htc
    rw [hzero] at hh
    exact (sub_left_inj).mp hh
  · intro j
    obtain ⟨u, hu⟩ := ho j.rev
    obtain ⟨v, hv⟩ := σ.orbit (Fin.last σ.n)
    refine ⟨u * v, ?_⟩
    change -(ρ.x j.rev : Dual ℝ H) = (u * v).1 (σ.x 0)
    rw [hu]
    change -u.1 (-(σ.x (0 : Fin (σ.n + 1)).rev : Dual ℝ H)) = _
    rw [Fin.rev_zero, map_neg, neg_neg, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]

/-- Two paths with the same initial heights and tails bounded below by their common cut
height have identical right minima on that initial interval. -/
theorem rightMin_eq_of_common_prefix {π η : LittelmannPath (P.pathSpace hA)} {i : ι}
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (heq : ∀ t ∈ Icc (0 : ℝ) c, π.pairing i t = η.pairing i t)
    (hπ : ∀ t ∈ Icc c 1, π.pairing i c ≤ π.pairing i t)
    (hη : ∀ t ∈ Icc c 1, η.pairing i c ≤ η.pairing i t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) c) : π.rightMin i t = η.rightMin i t := by
  have haux (a b : LittelmannPath (P.pathSpace hA))
      (hab : ∀ v ∈ Icc (0 : ℝ) c, a.pairing i v = b.pairing i v)
      (hb : ∀ v ∈ Icc c 1, b.pairing i c ≤ b.pairing i v) :
      a.rightMin i t ≤ b.rightMin i t := by
    apply b.le_rightMin (ht.2.trans hc.2)
    intro v hv
    rcases le_total v c with hvc | hcv
    · rw [← hab v ⟨ht.1.trans hv.1, hvc⟩]
      exact a.rightMin_le hv
    · exact (a.rightMin_le ⟨ht.2, hc.2⟩).trans
        ((hab c ⟨hc.1, le_rfl⟩).le.trans (hb v ⟨hcv, hv.2⟩))
  exact le_antisymm (haux π η heq hη) (haux η π (fun v hv ↦ (heq v hv).symm) hπ)

end Matrix.Realization.LSGeneralClass

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- The first direction is present at every strictly interior first-piece cut. -/
theorem Presentation.hasRightDir_first (σ : Presentation P hA) {c : ℚ}
    (hc0 : 0 ≤ c) (hc : c < σ.a (0 : Fin (σ.n + 1)).succ) :
    σ.path.HasRightDir c (σ.x 0) := by
  have hc' : (c : ℝ) < σ.a (0 : Fin (σ.n + 1)).succ := by exact_mod_cast hc
  have hc0' : (0 : ℝ) ≤ c := by exact_mod_cast hc0
  refine ⟨(σ.a (0 : Fin (σ.n + 1)).succ : ℝ) - c, sub_pos.mpr hc', ?_⟩
  intro t ht
  rw [σ.first_piece t ⟨hc0'.trans ht.1, by linarith [ht.2]⟩,
    σ.first_piece c ⟨hc0', hc'.le⟩, pathSpace_embed]
  module

/-- The last direction is present at every strictly interior last-piece cut. -/
theorem Presentation.hasLeftDir_last (σ : Presentation P hA) {c : ℚ}
    (hc : σ.a (Fin.last σ.n).castSucc < c) (hc1 : c ≤ 1) :
    σ.path.HasLeftDir c (σ.x (Fin.last σ.n)) := by
  have hc' : (σ.a (Fin.last σ.n).castSucc : ℝ) < c := by exact_mod_cast hc
  have hc1' : (c : ℝ) ≤ σ.a (Fin.last σ.n).succ := by
    simpa only [Fin.succ_last, σ.one, Rat.cast_one] using
      (show (c : ℝ) ≤ 1 by exact_mod_cast hc1)
  refine ⟨(c : ℝ) - σ.a (Fin.last σ.n).castSucc, sub_pos.mpr hc', ?_⟩
  intro t ht
  rw [σ.piece _ t ⟨by linarith [ht.1], ht.2.trans hc1'⟩,
    σ.piece _ c ⟨hc'.le, hc1'⟩, pathSpace_embed]
  module

/-- An actual power whose upper level is the next integer above a retained cut reflects
an actual interval to its right. The source LS times are constructed after normalization. -/
theorem Presentation.exists_power_reflected_interval (δ : Presentation P hA) {i : ι}
    {c : ℚ} (hc : (c : ℝ) ∈ Icc (0 : ℝ) 1) (n : ℕ)
    (hlevel : δ.path.minPairing i + n - 1 < δ.path.pairing i c ∧
      δ.path.pairing i c < δ.path.minPairing i + n)
    (htail : ∀ t ∈ Icc (c : ℝ) 1, δ.path.pairing i c ≤ δ.path.pairing i t)
    {ω : Presentation P hA}
    (hf : (LittelmannPath.crystal (P.pathSpace hA)).fIter i n δ.path = some ω.path) :
    ∃ q : ℝ, (c : ℝ) < q ∧ q ≤ 1 ∧ ∀ t ∈ Icc (c : ℝ) q,
      ω.path t - ω.path c = P.reflection hA i (δ.path t - δ.path c) := by
  cases n with
  | zero =>
    have hh := δ.path.minPairing_le (i := i) hc
    simp only [Nat.cast_zero, add_zero] at hlevel
    exact (not_lt_of_ge hh hlevel.2).elim
  | succ k =>
    have hb : ∀ t ∈ Icc (c : ℝ) 1, δ.path.minPairing i + k ≤ δ.path.pairing i t := by
      intro t ht
      have hh := htail t ht
      push_cast at hlevel
      linarith [hlevel.1]
    obtain ⟨ζ, hζ, -, hm, ht⟩ := exists_fIter_translate_tail δ.path i k hc hb
    obtain ⟨ρ, hρ, -, -⟩ := δ.exists_fIter_presentation i k hζ
    have hfρ : LittelmannPath.f i ρ.path = some ω.path := by
      rw [Crystal.fIter_succ', hζ, Option.bind_some, LittelmannPath.crystal_f] at hf
      simpa only [hρ] using hf
    have hp (t : ℝ) (ht' : t ∈ Icc (c : ℝ) 1) :
        ρ.path.pairing i t = δ.path.pairing i t - 2 * k := by
      rw [hρ, pairing, ht t ht']
      simp only [pathSpace_coroot, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, P.root_coroot_self hA]
      change δ.path.pairing i t - (k : ℝ) * 2 = _
      ring
    have hmc : ρ.path.minPairing i < ρ.path.pairing i c ∧
        ρ.path.pairing i c < ρ.path.minPairing i + 1 := by
      rw [hp c ⟨le_rfl, hc.2⟩, hρ, hm]
      push_cast at hlevel
      constructor <;> linarith [hlevel.1, hlevel.2]
    have h1 : ρ.path.minPairing i + 1 ≤ ρ.path.pairing i 1 := by
      have hh := (f_eq_none_iff (i := i) (π := ρ.path)).not.mp (by rw [hfρ]; simp)
      push Not at hh
      linarith
    obtain ⟨p, q, hp0, hpq, hq1, hpm, hplt, hqm, hmono, hqge⟩ :=
      ρ.isLS.exists_f_times i h1
    have hpc : p < (c : ℝ) := by
      by_contra hn
      have hh := htail p ⟨le_of_not_gt hn, hpq.le.trans hq1⟩
      have hh' := hp p ⟨le_of_not_gt hn, hpq.le.trans hq1⟩
      have hc' := hp c ⟨le_rfl, hc.2⟩
      rw [hpm] at hh'
      linarith [hmc.1]
    have hcq : (c : ℝ) < q := by
      by_contra hn
      exact (not_le_of_gt hmc.2) (hqge c ⟨le_of_not_gt hn, hc.2⟩)
    obtain ⟨-, hmiddle, -⟩ := ρ.f_regions hfρ hp0 hpq hq1 hpm hqm hmono hqge
    refine ⟨q, hcq, hq1, ?_⟩
    intro t ht'
    rw [hmiddle t ⟨hpc.le.trans ht'.1, ht'.2⟩, hmiddle c ⟨hpc.le, hcq.le⟩]
    simp only [pathSpace_reflection, hρ]
    rw [ht t ⟨ht'.1, ht'.2.trans hq1⟩, ht c ⟨le_rfl, hc.2⟩,
      map_sub, map_sub, map_sub]
    abel

/-- Full lowering reflects the entire terminal affine piece, up to a fixed translation. -/
theorem Presentation.full_power_final (σ : Presentation P hA) {i : ι} (n : ℕ)
    (hn : σ.path.minPairing i + n = σ.path.pairing i 1)
    (hx : 0 ≤ (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i))
    {υ : Presentation P hA}
    (hf : (LittelmannPath.crystal (P.pathSpace hA)).fIter i n σ.path = some υ.path)
    (t : ℝ) (ht : t ∈ Icc (σ.a (Fin.last σ.n).castSucc : ℝ) 1) :
    υ.path t = P.reflection hA i (σ.path t) + σ.path.minPairing i • P.root i := by
  obtain ⟨ζ, hζ, -, -, hform⟩ :=
    Matrix.Realization.LSGeneralClass.exists_fIter_formula σ.path i n hn.le
  have hυ : ζ = υ.path := Option.some.inj (hζ.symm.trans hf)
  have ht0 : 0 ≤ t := by
    have ha := σ.mono.monotone (Fin.zero_le (Fin.last σ.n).castSucc)
    rw [σ.zero] at ha
    exact (Rat.cast_nonneg.mpr ha).trans ht.1
  have hp (v : ℝ) (hv : v ∈ Icc t 1) : σ.path.pairing i t ≤ σ.path.pairing i v := by
    have htm : t ∈ Icc (σ.a (Fin.last σ.n).castSucc : ℝ)
        (σ.a (Fin.last σ.n).succ : ℝ) :=
      ⟨ht.1, by simpa only [Fin.succ_last, σ.one, Rat.cast_one] using ht.2⟩
    have hvm : v ∈ Icc (σ.a (Fin.last σ.n).castSucc : ℝ)
        (σ.a (Fin.last σ.n).succ : ℝ) :=
      ⟨ht.1.trans hv.1, by simpa only [Fin.succ_last, σ.one, Rat.cast_one] using hv.2⟩
    simp only [pairing, pathSpace_coroot, σ.piece _ t htm, σ.piece _ v hvm,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    nlinarith [hv.1]
  have hr : σ.path.rightMin i t = σ.path.pairing i t :=
    le_antisymm (σ.path.rightMin_le ⟨le_rfl, ht.2⟩) (σ.path.le_rightMin ht.2 hp)
  rw [hυ] at hform
  rw [hform t ⟨ht0, ht.2⟩, hr, hn, min_eq_left (hp 1 ⟨ht.2, le_rfl⟩),
    P.reflection_apply]
  change σ.path t - ((σ.path t) (P.coroot i) - _) • P.root i = _
  module

private theorem exists_nat_of_integral_nonneg {r : ℝ} (h0 : 0 ≤ r)
    (hz : ∃ z : ℤ, r = z) : ∃ n : ℕ, r = n := by
  obtain ⟨z, rfl⟩ := hz
  have hz0 : 0 ≤ z := by exact_mod_cast h0
  exact ⟨z.toNat, by exact_mod_cast (Int.toNat_of_nonneg hz0).symm⟩

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- Literal retained-prefix identity. -/
theorem path_left {t : ℝ} (ht : t ≤ (g.s : ℝ)) : g.path t = σ.path t := g.raw_left ht

/-- Literal retained-tail identity, including the integral offset. -/
theorem path_right {t : ℝ} (ht : (g.s' : ℝ) ≤ t) :
    g.path t = δ.path t + (σ.path g.s - δ.path g.s') := g.raw_right ht

/-- An interior crossing height and the actual future-height bound force both source
slopes positive. No monotonicity is imposed on the artificial pause. -/
theorem crossing_seam_signs {i : ι}
    (hseam : g.path.minPairing i < (σ.path g.s) (P.coroot i) ∧
      (σ.path g.s) (P.coroot i) < g.path.minPairing i + 1)
    (htail : ∀ t ∈ Icc (g.s' : ℝ) 1, (σ.path g.s) (P.coroot i) ≤ g.path.pairing i t) :
    (¬ ∃ z : ℤ, (σ.path g.s) (P.coroot i) = z) ∧
      0 < (δ.x 0 : Dual ℝ H) (P.coroot i) := by
  have hp : ¬ ∃ z : ℤ, (σ.path g.s) (P.coroot i) = z := by
    rintro ⟨z, hz⟩
    obtain ⟨m, hm⟩ := g.isIntegral i
    rw [hm, hz] at hseam
    have hl : m < z := by exact_mod_cast hseam.1
    have hu : z < m + 1 := by exact_mod_cast hseam.2
    omega
  refine ⟨hp, ?_⟩
  have hs1 : (g.s' : ℝ) < 1 := by exact_mod_cast g.lt_one
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  have hcut : g.path.pairing i g.s' = (σ.path g.s) (P.coroot i) := by
    simp only [pairing, pathSpace_coroot, g.path_pause ⟨hss, le_rfl⟩]
  have hyc := g.right_direction.coroot_nonneg (sub_pos.mpr hs1) (i := i)
    (fun t ht ↦ by rw [hcut]; exact htail t ⟨ht.1.le, by linarith [ht.2]⟩)
  have hy : 0 ≤ (δ.x 0 : Dual ℝ H) (P.coroot i) := by
    rw [← coroot_cartanDatum_cast P hA]
    exact_mod_cast hyc
  rcases eq_or_lt_of_le hy with hz | hpos
  · exfalso
    apply hp
    obtain ⟨z, hz'⟩ := g.offset_integral i
    refine ⟨z, ?_⟩
    rw [δ.first_piece _ g.right_cut_mem] at hz'
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      ← hz, mul_zero, sub_zero] using hz'
  · exact hpos

/-- Genuine crossing source-power construction. The left source is lowered to the bottom
of its actual string; the right exponent reaches the integral upper operator level.
Both source powers exist and are finite in their original orbits; no output is assumed. -/
theorem exists_crossing_source_powers {i : ι}
    (hseam : g.path.minPairing i < (σ.path g.s) (P.coroot i) ∧
      (σ.path g.s) (P.coroot i) < g.path.minPairing i + 1)
    (htail : ∀ t ∈ Icc (g.s' : ℝ) 1, (σ.path g.s) (P.coroot i) ≤ g.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    ∃ (n m : ℕ) (υ ω : Presentation P hA),
      σ.path.minPairing i = g.path.minPairing i ∧
      σ.path.pairing i 1 = σ.path.minPairing i + n ∧
      δ.path.minPairing i + m + (σ.path g.s - δ.path g.s') (P.coroot i) =
        g.path.minPairing i + 1 ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i n σ.path = some υ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i n υ.path = some σ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i m δ.path = some ω.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i m ω.path = some δ.path ∧
      (∀ t ∈ Icc (0 : ℝ) g.s, υ.path t = η t) ∧
      (∀ t ∈ Icc (g.s' : ℝ) 1, ω.path t - ω.path g.s' = η t - η g.s) ∧
      (∀ j, ∃ w : P.weylGroup hA, (υ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
      ∀ j, ∃ w : P.weylGroup hA, (ω.x j : Dual ℝ H) = w.1 (δ.x 0) := by
  obtain ⟨hp, hy⟩ := g.crossing_seam_signs hseam htail
  obtain ⟨hx, -⟩ := g.reflect_nonintegral_seam hp hy
  have hs0 : (0 : ℝ) ≤ g.s := by exact_mod_cast g.pos.le
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  have hs1 : (g.s' : ℝ) ≤ 1 := by exact_mod_cast g.lt_one.le
  have hsl : (g.s : ℝ) ≤ 1 := hss.trans hs1
  have hpiece (t : ℝ) (ht : t ∈ Icc (g.s : ℝ) 1) :
      σ.path t = σ.path g.s + (t - (g.s : ℝ)) • (σ.x (Fin.last σ.n) : Dual ℝ H) := by
    have hmem : t ∈ Icc (σ.a (Fin.last σ.n).castSucc : ℝ)
        (σ.a (Fin.last σ.n).succ : ℝ) :=
      ⟨g.left_cut_mem.1.trans ht.1,
        by simpa only [Fin.succ_last, σ.one, Rat.cast_one] using ht.2⟩
    rw [σ.piece _ t hmem, σ.piece _ _ g.left_cut_mem]
    module
  have hσtail (t : ℝ) (ht : t ∈ Icc (g.s : ℝ) 1) :
      σ.path.pairing i g.s ≤ σ.path.pairing i t := by
    simp only [pairing, pathSpace_coroot, hpiece t ht, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr ht.1) hx.le)
  have hgtail (t : ℝ) (ht : t ∈ Icc (g.s : ℝ) 1) :
      g.path.pairing i g.s ≤ g.path.pairing i t := by
    have hcut : g.path.pairing i g.s = (σ.path g.s) (P.coroot i) := by
      simp only [pairing, pathSpace_coroot, g.path_left le_rfl]
    rw [hcut]
    rcases le_total t g.s' with h | h
    · simp only [pairing, pathSpace_coroot, g.path_pause ⟨ht.1, h⟩, le_refl]
    · exact htail t ⟨h, ht.2⟩
  have hrleft (t : ℝ) (ht : t ∈ Icc (0 : ℝ) g.s) :
      σ.path.rightMin i t = g.path.rightMin i t :=
    rightMin_eq_of_common_prefix ⟨hs0, hsl⟩
      (fun v hv ↦ by simp only [pairing, pathSpace_coroot, g.path_left hv.2])
      hσtail hgtail ht
  have hm : σ.path.minPairing i = g.path.minPairing i := by
    simpa only [rightMin_zero] using hrleft 0 ⟨le_rfl, hs0⟩
  let d := (σ.path g.s - δ.path g.s') (P.coroot i)
  have hr (t : ℝ) (ht : (g.s' : ℝ) ≤ t) :
      g.path.pairing i t = δ.path.pairing i t + d := by
    simp only [pairing, pathSpace_coroot, g.path_right ht, LinearMap.add_apply]
    rfl
  have hrmin (t : ℝ) (ht : t ∈ Icc (g.s' : ℝ) 1) :
      g.path.rightMin i t = δ.path.rightMin i t + d := by
    apply le_antisymm
    · obtain ⟨v, hv, heq⟩ := δ.path.exists_rightMin i ht.2
      exact (g.path.rightMin_le hv).trans_eq (by rw [hr v (ht.1.trans hv.1), heq])
    · apply g.path.le_rightMin ht.2
      intro v hv
      rw [hr v (ht.1.trans hv.1)]
      have hh := δ.path.rightMin_le (i := i) hv
      linarith
  have hcut : (σ.path g.s) (P.coroot i) = δ.path.pairing i g.s' + d := by
    dsimp only [d, pairing, pathSpace_coroot]
    simp only [LinearMap.sub_apply]
    ring
  have hrδ : δ.path.rightMin i g.s' = δ.path.pairing i g.s' := by
    apply le_antisymm (δ.path.rightMin_le ⟨le_rfl, hs1⟩)
    apply δ.path.le_rightMin hs1
    intro v hv
    have hh := htail v hv
    rw [hcut, hr v hv.1] at hh
    linarith
  have hrgs : g.path.rightMin i g.s = (σ.path g.s) (P.coroot i) := by
    apply le_antisymm
    · simpa only [pairing, pathSpace_coroot, g.path_left le_rfl] using
        g.path.rightMin_le (i := i) ⟨le_rfl, hsl⟩
    · apply g.path.le_rightMin hsl
      intro t ht
      simpa only [pairing, pathSpace_coroot, g.path_left le_rfl] using hgtail t ht
  obtain ⟨n, hn⟩ := exists_nat_of_integral_nonneg
    (sub_nonneg.mpr (σ.path.minPairing_le ⟨zero_le_one, le_rfl⟩)) (by
      obtain ⟨a, ha⟩ := σ.path.wt.property i
      obtain ⟨b, hb⟩ := σ.isLS.exists_int_minPairing i
      refine ⟨a - b, ?_⟩
      change σ.path.pairing i 1 = (a : ℝ) at ha
      rw [ha, hb]
      push_cast
      rfl)
  have hn' : σ.path.pairing i 1 = σ.path.minPairing i + n := by linarith
  have hm0 : 0 ≤ g.path.minPairing i + 1 - d - δ.path.minPairing i := by
    have hh := δ.path.minPairing_le (i := i) ⟨hs0.trans hss, hs1⟩
    rw [hcut] at hseam
    linarith [hseam.2]
  obtain ⟨m, hm'⟩ := exists_nat_of_integral_nonneg hm0 (by
    obtain ⟨a, ha⟩ := g.isIntegral i
    obtain ⟨b, hb⟩ := g.offset_integral i
    obtain ⟨c, hc⟩ := δ.isLS.exists_int_minPairing i
    refine ⟨a + 1 - b - c, ?_⟩
    change d = (b : ℝ) at hb
    rw [ha, hb, hc]
    push_cast
    ring)
  have hlevel : δ.path.minPairing i + m + d = g.path.minPairing i + 1 := by linarith
  have hend : δ.path.minPairing i + m ≤ δ.path.pairing i 1 := by
    have hh := (f_eq_none_iff (i := i) (π := g.path)).not.mp (by rw [hf]; simp)
    push Not at hh
    rw [hr 1 hs1] at hh
    linarith
  obtain ⟨υ, hυ, heυ, hυform, hoυ⟩ := σ.exists_fIter_formula i n hn'.ge
  obtain ⟨ω, hω, heω, hωform, hoω⟩ := δ.exists_fIter_formula i m hend
  have hηs : η g.s = σ.path g.s -
      ((σ.path g.s) (P.coroot i) - g.path.minPairing i) • P.root i := by
    rw [f_apply hf ⟨hs0, hsl⟩, hrgs, min_eq_left hseam.2.le, g.path_left le_rfl]
    rfl
  refine ⟨n, m, υ, ω, hm, hn', hlevel, hυ, heυ, hω, heω, ?_, ?_, hoυ, hoω⟩
  · intro t ht
    have ht1 : t ≤ 1 := ht.2.trans hsl
    have hrg : g.path.rightMin i t ≤ (σ.path g.s) (P.coroot i) := by
      simpa only [pairing, pathSpace_coroot, g.path_left le_rfl] using
        g.path.rightMin_le (i := i) ⟨ht.2, hsl⟩
    rw [hυform t ⟨ht.1, ht1⟩, ← hn',
      min_eq_left (σ.path.rightMin_le ⟨ht1, le_rfl⟩), hrleft t ht, hm,
      f_apply hf ⟨ht.1, ht1⟩, min_eq_left (hrg.trans hseam.2.le), g.path_left ht.2]
    rfl
  · intro t ht
    have hc : δ.path.pairing i g.s' ≤ δ.path.minPairing i + m := by
      rw [hcut] at hseam
      linarith [hseam.2]
    rw [hωform t ⟨(hs0.trans hss).trans ht.1, ht.2⟩,
      hωform g.s' ⟨hs0.trans hss, hs1⟩, hrδ, min_eq_left hc,
      f_apply hf ⟨(hs0.trans hss).trans ht.1, ht.2⟩, hrmin t ht,
      ← hlevel, min_add_add_right, g.path_right ht.1, hηs, hcut]
    change δ.path t - _ • P.root i - (δ.path g.s' - _ • P.root i) =
      δ.path t + (σ.path g.s - δ.path g.s') - _ • P.root i -
        (σ.path g.s - _ • P.root i)
    module

/-- Actual strict output in the genuine nonintegral crossing sector of [Lit95],
Proposition 5.6, pp.515–516. The input height conditions express that the seam lies
strictly inside the unit reflection window and is a future minimum. Both literal source
powers and their inverse strings are retained separately from the strict representatives. -/
theorem exists_f_gluing_crossing {i : ι}
    (hseam : g.path.minPairing i < (σ.path g.s) (P.coroot i) ∧
      (σ.path g.s) (P.coroot i) < g.path.minPairing i + 1)
    (htail : ∀ t ∈ Icc (g.s' : ℝ) 1, (σ.path g.s) (P.coroot i) ≤ g.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    ∃ (n m : ℕ) (υ ω τ ρ : Presentation P hA) (g' : GluingPair τ ρ),
      σ.path.minPairing i + n = σ.path.pairing i 1 ∧
      δ.path.minPairing i + m + (σ.path g.s - δ.path g.s') (P.coroot i) =
        g.path.minPairing i + 1 ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i n σ.path = some υ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i n υ.path = some σ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i m δ.path = some ω.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i m ω.path = some δ.path ∧
      (∀ t : ℝ, t ≤ (g.s : ℝ) → τ.path t = υ.path t) ∧
      (∀ t : ℝ, (g.s' : ℝ) ≤ t →
        ρ.path t - ρ.path g.s' = ω.path t - ω.path g.s') ∧
      (τ.x (Fin.last τ.n) : Dual ℝ H) = P.reflection hA i (σ.x (Fin.last σ.n)) ∧
      (ρ.x 0 : Dual ℝ H) = P.reflection hA i (δ.x 0) ∧
      g'.path = η ∧ g'.s = g.s ∧ g'.s' = g.s' ∧
      g'.ν = P.reflection hA i g.ν ∧ g'.μ = P.reflection hA i g.μ ∧
      (∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
      ∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (δ.x 0) := by
  obtain ⟨hp, hy⟩ := g.crossing_seam_signs hseam htail
  obtain ⟨hx, -, -, hlc, hrc, hprec⟩ := g.reflect_nonintegral_seam hp hy
  obtain ⟨n, m, υ, ω, -, hn, hm, hυ, heυ, hω, heω, hleft, hright, hoυ, hoω⟩ :=
    g.exists_crossing_source_powers hseam htail hf
  have hn := hn.symm
  obtain ⟨τ, hτcut, hτ, hoτ⟩ := υ.exists_coarsen_final g.pos
  obtain ⟨ρ, hρcut, hρ, hoρ⟩ := ω.exists_coarsen_initial g.lt_one
  have hs0 : (0 : ℝ) ≤ g.s := by exact_mod_cast g.pos.le
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  have hs1 : (g.s' : ℝ) ≤ 1 := by exact_mod_cast g.lt_one.le
  have hsl : (g.s : ℝ) ≤ 1 := hss.trans hs1
  have hslq : g.s ≤ 1 := g.le.trans g.lt_one.le
  have hsp0 : (0 : ℚ) ≤ g.s' := g.pos.le.trans g.le
  have hτdir : (τ.x (Fin.last τ.n) : Dual ℝ H) =
      P.reflection hA i (σ.x (Fin.last σ.n)) := by
    let x' := (P.cartanDatum hA).reflection i (σ.x (Fin.last σ.n))
    have hx' : (x' : Dual ℝ H) = P.reflection hA i (σ.x (Fin.last σ.n)) := by
      simpa only [pathSpace_embed, pathSpace_reflection] using
        (P.pathSpace hA).embed_reflection i (σ.x (Fin.last σ.n))
    have hlast : (σ.a (Fin.last σ.n).castSucc : ℝ) < g.s := by exact_mod_cast g.last_lt
    have htrans : τ.path.HasLeftDir g.s x' :=
      (σ.hasLeftDir_last g.last_lt hslq).of_eq (sub_pos.mpr hlast)
        (P.reflection hA i).toLinearMap (σ.path.minPairing i • P.root i)
        (fun t ht ↦ by
          rw [hτ t ht.2]
          exact σ.full_power_final n hn hx.le hυ t ⟨by linarith [ht.1], ht.2.trans hsl⟩)
        (by exact hx'.symm)
    have heq := (τ.hasLeftDir_last hτcut hslq).unique htrans
    exact (congrArg (fun z : P.integralWeights ↦ (z : Dual ℝ H)) heq).trans hx'
  have hδtail (t : ℝ) (ht : t ∈ Icc (g.s' : ℝ) 1) :
      δ.path.pairing i g.s' ≤ δ.path.pairing i t := by
    have hh := htail t ht
    simp only [pairing, pathSpace_coroot, g.path_right ht.1, LinearMap.add_apply,
      LinearMap.sub_apply] at hh ⊢
    linarith
  have hlevel : δ.path.minPairing i + m - 1 < δ.path.pairing i g.s' ∧
      δ.path.pairing i g.s' < δ.path.minPairing i + m := by
    simp only [LinearMap.sub_apply] at hm
    change _ < (δ.path g.s') (P.coroot i) ∧ (δ.path g.s') (P.coroot i) < _
    constructor <;> linarith [hseam.1, hseam.2]
  obtain ⟨q, hsq, hq1, hωref⟩ :=
    δ.exists_power_reflected_interval ⟨hs0.trans hss, hs1⟩ m hlevel hδtail hω
  have hρdir : (ρ.x 0 : Dual ℝ H) = P.reflection hA i (δ.x 0) := by
    let y' := (P.cartanDatum hA).reflection i (δ.x 0)
    have hy' : (y' : Dual ℝ H) = P.reflection hA i (δ.x 0) := by
      simpa only [pathSpace_embed, pathSpace_reflection] using
        (P.pathSpace hA).embed_reflection i (δ.x 0)
    have htrans : ρ.path.HasRightDir g.s' y' :=
      (δ.hasRightDir_first hsp0 g.first_gt).of_eq (sub_pos.mpr hsq)
        (P.reflection hA i).toLinearMap (ρ.path g.s' - P.reflection hA i (δ.path g.s'))
        (fun t ht ↦ by
          have hh := (hρ t ht.1).trans (hωref t ⟨ht.1, by linarith [ht.2]⟩)
          simp only [map_sub] at hh
          change ρ.path t = P.reflection hA i (δ.path t) + _
          rw [sub_eq_iff_eq_add] at hh
          rw [hh]
          abel)
        (by exact hy'.symm)
    have heq := (ρ.hasRightDir_first hsp0 hρcut).unique htrans
    exact (congrArg (fun z : P.integralWeights ↦ (z : Dual ℝ H)) heq).trans hy'
  have hrmin (t : ℝ) (ht : t ∈ Icc (g.s : ℝ) (g.s' : ℝ)) :
      g.path.rightMin i t = (σ.path g.s) (P.coroot i) := by
    apply le_antisymm
    · simpa only [pairing, pathSpace_coroot, g.path_pause ht] using
        g.path.rightMin_le (i := i) (t := t) ⟨le_rfl, ht.2.trans hs1⟩
    · apply g.path.le_rightMin (ht.2.trans hs1)
      intro v hv
      rcases le_total v (g.s' : ℝ) with hvs | hsv
      · simp only [pairing, pathSpace_coroot, g.path_pause ⟨ht.1.trans hv.1, hvs⟩,
          le_refl]
      · exact htail v ⟨hsv, hv.2⟩
  have hpause (t : ℝ) (ht : t ∈ Icc (g.s : ℝ) (g.s' : ℝ)) : η t = η g.s := by
    rw [f_apply hf ⟨hs0.trans ht.1, ht.2.trans hs1⟩,
      f_apply hf ⟨hs0, hsl⟩, hrmin t ht, hrmin g.s ⟨le_rfl, hss⟩,
      g.path_pause ht, g.path_left le_rfl]
  have hraw (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      glueRaw τ ρ g.s g.s' t = η t := by
    by_cases hts : t ≤ (g.s : ℝ)
    · simp only [glueRaw, min_eq_left hts, max_eq_right (hts.trans hss),
        add_sub_cancel_right, hτ t hts, hleft t ⟨ht.1, hts⟩]
    by_cases hts' : t ≤ (g.s' : ℝ)
    · simp only [glueRaw, min_eq_right (le_of_not_ge hts), max_eq_right hts',
        add_sub_cancel_right, hτ g.s le_rfl, hleft g.s ⟨hs0, le_rfl⟩]
      exact (hpause t ⟨le_of_not_ge hts, hts'⟩).symm
    · have ht' : (g.s' : ℝ) ≤ t := le_of_not_ge hts'
      have hh := (hρ t ht').trans (hright t ⟨ht', ht.2⟩)
      rw [glueRaw, min_eq_right (hss.trans ht'), max_eq_left ht', hτ g.s le_rfl,
        hleft g.s ⟨hs0, le_rfl⟩]
      rw [sub_eq_iff_eq_add] at hh
      rw [hh]
      abel
  let g' : GluingPair τ ρ :=
    { s := g.s
      s' := g.s'
      pos := g.pos
      le := g.le
      lt_one := g.lt_one
      last_lt := hτcut
      first_gt := hρcut
      ν := P.reflection hA i g.ν
      μ := P.reflection hA i g.μ
      left_chain := by simpa only [hτdir] using hlc
      right_chain := by simpa only [hρdir] using hrc
      precedes := hprec
      endpoint := by
        rw [hraw 1 ⟨zero_le_one, le_rfl⟩]
        simpa only [apply_one, pathSpace_embed] using η.wt.property }
  refine ⟨n, m, υ, ω, τ, ρ, g', hn, hm, hυ, heυ, hω, heω, hτ, hρ,
    hτdir, hρdir, ext_of_eqOn hraw, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro j
    obtain ⟨u, hu⟩ := hoτ j
    obtain ⟨v, hv⟩ := hoυ 0
    exact ⟨u * v, by rw [hu, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩
  · intro j
    obtain ⟨u, hu⟩ := hoρ j
    obtain ⟨v, hv⟩ := hoω 0
    exact ⟨u * v, by rw [hu, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩

/-- All-root integrality follows from the constructed strict crossing output pair,
not from its selected-root coefficient formula or an assumed closure property. -/
theorem f_isIntegral_crossing {i : ι}
    (hseam : g.path.minPairing i < (σ.path g.s) (P.coroot i) ∧
      (σ.path g.s) (P.coroot i) < g.path.minPairing i + 1)
    (htail : ∀ t ∈ Icc (g.s' : ℝ) 1, (σ.path g.s) (P.coroot i) ≤ g.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    η.IsIntegral := by
  obtain ⟨n, m, υ, ω, τ, ρ, g', -, -, -, -, -, -, -, -, -, -, hp, -⟩ :=
    g.exists_f_gluing_crossing hseam htail hf
  rw [← hp]
  exact g'.isIntegral

/-- The literal crossing-time contract implies the input-only height criterion.
Strict increase is required separately on the two retained intervals, never across a
nontrivial pause. The upper-level future bound is part of the actual lowering-time data. -/
theorem crossing_window_of_times {i : ι} {p q : ℝ}
    (hp : p < (g.s : ℝ)) (hq : (g.s' : ℝ) < q)
    (hpm : g.path.pairing i p = g.path.minPairing i)
    (hqm : g.path.pairing i q = g.path.minPairing i + 1)
    (hl : StrictMonoOn (g.path.pairing i) (Icc p (g.s : ℝ)))
    (hr : StrictMonoOn (g.path.pairing i) (Icc (g.s' : ℝ) q))
    (hafter : ∀ t ∈ Icc q 1, g.path.minPairing i + 1 ≤ g.path.pairing i t) :
    (g.path.minPairing i < (σ.path g.s) (P.coroot i) ∧
      (σ.path g.s) (P.coroot i) < g.path.minPairing i + 1) ∧
    ∀ t ∈ Icc (g.s' : ℝ) 1, (σ.path g.s) (P.coroot i) ≤ g.path.pairing i t := by
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  have hcs : g.path.pairing i g.s = (σ.path g.s) (P.coroot i) := by
    simp only [pairing, pathSpace_coroot, g.path_left le_rfl]
  have hcs' : g.path.pairing i g.s' = (σ.path g.s) (P.coroot i) := by
    simp only [pairing, pathSpace_coroot, g.path_pause ⟨hss, le_rfl⟩]
  have hlo := hl ⟨le_rfl, hp.le⟩ ⟨hp.le, le_rfl⟩ hp
  have hhi := hr ⟨le_rfl, hq.le⟩ ⟨hq.le, le_rfl⟩ hq
  rw [hpm, hcs] at hlo
  rw [hcs', hqm] at hhi
  refine ⟨⟨hlo, hhi⟩, ?_⟩
  intro t ht
  rcases le_total t q with htq | hqt
  · rw [← hcs']
    exact hr.monotoneOn ⟨le_rfl, hq.le⟩ ⟨ht.1, htq⟩ ht.1
  · exact hhi.le.trans (hafter t ⟨hqt, ht.2⟩)

/-- Actual output and all-root integrality for `t₀ < s ≤ s' < t₁`, with the two
retained strictly increasing intervals and the correct upper-level future bound.
The stronger source-power and strict representative contracts are in
`exists_f_gluing_crossing`. -/
theorem exists_f_gluing_crossing_of_times {i : ι} {p q : ℝ}
    (hp0 : 0 ≤ p) (hp : p < (g.s : ℝ)) (hq : (g.s' : ℝ) < q) (hq1 : q ≤ 1)
    (hpm : g.path.pairing i p = g.path.minPairing i)
    (hqm : g.path.pairing i q = g.path.minPairing i + 1)
    (hl : StrictMonoOn (g.path.pairing i) (Icc p (g.s : ℝ)))
    (hr : StrictMonoOn (g.path.pairing i) (Icc (g.s' : ℝ) q))
    (hafter : ∀ t ∈ Icc q 1, g.path.minPairing i + 1 ≤ g.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    ∃ (τ ρ : Presentation P hA) (g' : GluingPair τ ρ),
      g'.path = η ∧ g'.s = g.s ∧ g'.s' = g.s' ∧
      g'.ν = P.reflection hA i g.ν ∧ g'.μ = P.reflection hA i g.μ ∧
      (∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
      (∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (δ.x 0)) ∧
      η.IsIntegral := by
  have _hp_mem : p ∈ Icc (0 : ℝ) 1 :=
    ⟨hp0, hp.le.trans ((Rat.cast_le.mpr g.le).trans (hq.le.trans hq1))⟩
  obtain ⟨hseam, htail⟩ := g.crossing_window_of_times hp hq hpm hqm hl hr hafter
  obtain ⟨n, m, υ, ω, τ, ρ, g', -, -, -, -, -, -, -, -, -, -, heq,
      hs, hs', hν, hμ, hoτ, hoρ⟩ := g.exists_f_gluing_crossing hseam htail hf
  exact ⟨τ, ρ, g', heq, hs, hs', hν, hμ, hoτ, hoρ, heq ▸ g'.isIntegral⟩

end GluingPair
end Matrix.Realization.LSGeneralClass
