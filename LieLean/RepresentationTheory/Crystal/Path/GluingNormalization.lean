/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingBefore

/-!
# Actual source-power normalization of retained gluing tails

## Main results

`exists_fIter_translate_tail` constructs actual lowering/raising inverse strings.
`GluingPair.exists_normalized_source_after` derives the natural discarded-height gap,
constructs its finite source lowering output, and proves literal unchanged re-gluing.
`GluingPair.exists_f_source_power_after` constructs the actual glued lowering from
`fᵢ^(k+1)` of the ORIGINAL source, where `k` is that gap, with literal equality at all
real times. It includes unmatched positive-outgoing sources without any sign restriction.
Success, integrality of the gap, finite source chains and original orbits are derived.

The output source has a strict finite subdivision, but may have breakpoints before
the right cut. Consequently these are normalization/source-power lemmas, not strict
output `GluingPair` witnesses; cut coarsening and compatible cut chains remain open.

## References

Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142 (1995),
Remark 5.4 and Proposition 5.6, pp. 514–516. Proofs reconstructed from actual operators.
This file does not claim strict-cut output assembly or full Proposition 5.6.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- If a retained tail is at least `k` above the global minimum, the actual `k`-fold
lowering exists and translates that entire tail by exactly `-k αᵢ`. Its inverse is the
actual raising string. No integrality or dominance premise is needed for this lemma. -/
theorem exists_fIter_translate_tail (π : LittelmannPath (P.pathSpace hA)) (i : ι)
    (k : ℕ) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (hbound : ∀ t ∈ Icc c 1, π.minPairing i + k ≤ π.pairing i t) :
    ∃ η : LittelmannPath (P.pathSpace hA),
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i k π = some η ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i k η = some π ∧
      η.minPairing i = π.minPairing i - k ∧
      ∀ t ∈ Icc c 1, η t = π t - (k : ℝ) • P.root i := by
  induction k with
  | zero =>
    exact ⟨π, rfl, rfl, by simp, fun _ _ ↦ by simp⟩
  | succ k ih =>
    obtain ⟨η, hη, -, hm, heq⟩ := ih (fun t ht ↦ by
      have hh := hbound t ht
      push_cast at hh
      linarith)
    have hp (t : ℝ) (ht : t ∈ Icc c 1) :
        η.pairing i t = π.pairing i t - 2 * k := by
      simp only [pairing, heq t ht, pathSpace_coroot, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul, P.root_coroot_self hA]
      ring
    have hb (t : ℝ) (ht : t ∈ Icc c 1) : η.minPairing i + 1 ≤ η.pairing i t := by
      rw [hp t ht, hm]
      have hh := hbound t ht
      push_cast at hh
      linarith
    obtain ⟨ζ, hζ⟩ : ∃ ζ, LittelmannPath.f i η = some ζ := by
      apply Option.ne_none_iff_exists'.mp
      intro hn
      have hh := f_eq_none_iff.mp hn
      have hgood := hb 1 ⟨hc.2, le_rfl⟩
      linarith
    have hiter : (LittelmannPath.crystal (P.pathSpace hA)).fIter i (k + 1) π =
        some ζ := by
      rw [Crystal.fIter_succ', hη, Option.bind_some]
      exact hζ
    refine ⟨ζ, hiter, (Crystal.fIter_eq_some_iff _ _ _ _).mp hiter, ?_, ?_⟩
    · have hh := minPairing_of_e_eq_some (f_eq_some_iff.mp hζ)
      rw [hm] at hh
      push_cast
      linarith
    · intro t ht
      have hr : η.minPairing i + 1 ≤ η.rightMin i t :=
        η.le_rightMin ht.2 (fun v hv ↦ hb v ⟨ht.1.trans hv.1, hv.2⟩)
      rw [f_apply hζ ⟨hc.1.trans ht.1, ht.2⟩, min_eq_right hr]
      simp only [add_sub_cancel_left, one_smul]
      change η t - P.root i = _
      rw [heq t ht]
      push_cast
      module

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- At an actual late glued minimum, the discarded-source minimum gap is a natural
integer. The integrality is derived from the glued minimum and integral cut offset. -/
theorem exists_nat_source_gap {i : ι} {u : ℝ}
    (hu : u ∈ Ioc (g.s' : ℝ) 1)
    (hum : g.path.pairing i u = g.path.minPairing i) :
    ∃ k : ℕ, δ.path.pairing i u = δ.path.minPairing i + k := by
  have hright : g.path.pairing i u = δ.path.pairing i u +
      (σ.path g.s - δ.path g.s') (P.coroot i) := by
    change (glueRaw σ δ g.s g.s' u) (P.coroot i) = _
    rw [g.raw_right hu.1.le, LinearMap.add_apply]
    rfl
  obtain ⟨a, ha⟩ := g.isIntegral i
  obtain ⟨b, hb⟩ := g.offset_integral i
  obtain ⟨d, hd⟩ := δ.isLS.exists_int_minPairing i
  have hgap : δ.path.pairing i u - δ.path.minPairing i = (a - b - d : ℤ) := by
    rw [hum, ha, hb] at hright
    rw [hd]
    push_cast
    linarith
  have hnonneg : 0 ≤ a - b - d := by
    have hu0 : 0 ≤ u := (g.right_cut_mem.1.trans hu.1.le)
    have hh := δ.path.minPairing_le (i := i) ⟨hu0, hu.2⟩
    have hcast : (0 : ℝ) ≤ (a - b - d : ℤ) := by linarith
    exact_mod_cast hcast
  refine ⟨(a - b - d).toNat, ?_⟩
  have hcast : (((a - b - d).toNat : ℕ) : ℝ) = (a - b - d : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  rw [hcast]
  linarith

/-- An actual late glued minimum determines a successful source normalization power.
The finite normalized source stays in the original orbit, its retained tail differs
only by an integral root translation, and re-gluing is literally unchanged at EVERY
real time. This is not a strict `GluingPair`: the normalization may add early cuts. -/
theorem exists_normalized_source_after {i : ι} {u : ℝ}
    (hu : u ∈ Ioc (g.s' : ℝ) 1)
    (hum : g.path.pairing i u = g.path.minPairing i) :
    ∃ (k : ℕ) (τ : Presentation P hA),
      δ.path.pairing i u = δ.path.minPairing i + k ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i k δ.path = some τ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i k τ.path = some δ.path ∧
      τ.path.minPairing i = δ.path.minPairing i - k ∧
      τ.path.pairing i u = τ.path.minPairing i ∧
      (∀ t, (g.s' : ℝ) ≤ t → τ.path t = δ.path t - (k : ℝ) • P.root i) ∧
      (∀ t, glueRaw σ τ g.s g.s' t = g.path t) ∧
      Set.range δ.a ⊆ Set.range τ.a ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (δ.x 0) := by
  obtain ⟨k, hk⟩ := g.exists_nat_source_gap hu hum
  have hs0 : (0 : ℝ) ≤ g.s' := g.right_cut_mem.1
  have hs1 : (g.s' : ℝ) ≤ 1 := by exact_mod_cast g.lt_one.le
  have hr (t : ℝ) (ht : (g.s' : ℝ) ≤ t) : g.path.pairing i t =
      δ.path.pairing i t + (σ.path g.s - δ.path g.s') (P.coroot i) := by
    change (glueRaw σ δ g.s g.s' t) (P.coroot i) = _
    rw [g.raw_right ht, LinearMap.add_apply]
    rfl
  have hb (t : ℝ) (ht : t ∈ Icc (g.s' : ℝ) 1) :
      δ.path.minPairing i + k ≤ δ.path.pairing i t := by
    have hh := g.path.minPairing_le (i := i) ⟨hs0.trans ht.1, ht.2⟩
    rw [← hum, hr u hu.1.le, hr t ht.1, hk] at hh
    linarith
  obtain ⟨η, hf, he, hm, ht⟩ :=
    exists_fIter_translate_tail δ.path i k ⟨hs0, hs1⟩ hb
  obtain ⟨τ, hτ, hsub, ho⟩ := δ.exists_fIter_presentation i k hf
  have htall (t : ℝ) (ht' : (g.s' : ℝ) ≤ t) :
      τ.path t = δ.path t - (k : ℝ) • P.root i := by
    rw [hτ]
    rcases le_total t 1 with hle | hle
    · exact ht t ⟨ht', hle⟩
    · simpa only [apply_one, η.apply_of_one_le hle, δ.path.apply_of_one_le hle]
        using ht 1 ⟨hs1, le_rfl⟩
  refine ⟨k, τ, hk, by simpa only [hτ] using hf, by simpa only [hτ] using he,
    by simpa only [hτ] using hm, ?_, htall, ?_, hsub, ho⟩
  · rw [pairing, htall u hu.1.le]
    simp only [pathSpace_coroot, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, P.root_coroot_self hA]
    change δ.path.pairing i u - (k : ℝ) * 2 = _
    rw [hk, hτ, hm]
    ring
  · intro t
    change glueRaw σ τ g.s g.s' t = glueRaw σ δ g.s g.s' t
    unfold glueRaw
    rw [htall _ (le_max_right _ _), htall _ le_rfl]
    module

/-- The unmatched strict-after source-power formula. If `k` is the discarded-height
gap, an actual glued lowering is re-glued from the unchanged left source and the
actual `(k + 1)`-fold lowering of the original right source, in its ORIGINAL orbit.
The right source is finite with strict subdivision and actual source chains. The
literal raw equality does not assert that its first breakpoint remains after the cut. -/
theorem exists_f_source_power_after {i : ι} {u : ℝ}
    (hu : u ∈ Ioc (g.s' : ℝ) 1)
    (hum : g.path.pairing i u = g.path.minPairing i)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    ∃ (k : ℕ) (υ : Presentation P hA),
      δ.path.pairing i u = δ.path.minPairing i + k ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i (k + 1) δ.path = some υ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i (k + 1) υ.path = some δ.path ∧
      (∀ t, glueRaw σ υ g.s g.s' t = η t) ∧
      Set.range δ.a ⊆ Set.range υ.a ∧
      ∀ j, ∃ w : P.weylGroup hA, (υ.x j : Dual ℝ H) = w.1 (δ.x 0) := by
  obtain ⟨k, τ, hk, hτ, -, -, hτmin, -, hraw, hsub, horbit⟩ :=
    g.exists_normalized_source_after hu hum
  have hs0 : (0 : ℝ) < g.s := by exact_mod_cast g.pos
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  have hs1 : (g.s' : ℝ) < 1 := by exact_mod_cast g.lt_one
  let d := (σ.path g.s - τ.path g.s') (P.coroot i)
  have hr (t : ℝ) (ht : (g.s' : ℝ) ≤ t) :
      g.path.pairing i t = τ.path.pairing i t + d := by
    rw [pairing, ← hraw t]
    simp only [glueRaw, min_eq_right (hss.trans ht), max_eq_left ht,
      pathSpace_coroot, LinearMap.add_apply, LinearMap.sub_apply]
    dsimp [pairing, d]
    ring
  have hm : g.path.minPairing i = τ.path.minPairing i + d := by
    rw [← hum, hr u hu.1.le, hτmin]
  obtain ⟨ζ, hζ⟩ : ∃ ζ, LittelmannPath.f i τ.path = some ζ := by
    apply Option.ne_none_iff_exists'.mp
    intro hn
    have hh := f_eq_none_iff.mp hn
    have hgood : ¬ g.path.pairing i 1 - g.path.minPairing i < 1 := by
      intro hbad
      have hn' := f_eq_none_iff.mpr hbad
      rw [hf] at hn'
      contradiction
    rw [hr 1 hs1.le, hm] at hgood
    apply hgood
    linarith
  obtain ⟨υ, hυ, hsub', ho⟩ := τ.exists_f_presentation hζ
  have hcut : ζ g.s' = τ.path g.s' :=
    τ.f_eqOn_initial hs1.le ⟨u, hu, hτmin⟩ hζ g.s'
      ⟨hs0.le.trans hss, le_rfl⟩
  have hout (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      glueRaw σ υ g.s g.s' t = η t := by
    rcases le_total t g.s' with hts | hst
    · have hmin : g.path.rightMin i t = g.path.minPairing i := le_antisymm
        ((g.path.rightMin_le ⟨hts.trans hu.1.le, hu.2⟩).trans_eq hum)
        (g.path.le_rightMin ht.2 (fun v hv ↦
          g.path.minPairing_le ⟨ht.1.trans hv.1, hv.2⟩))
      rw [f_apply hf ht, hmin, min_eq_left (by linarith)]
      simp only [sub_self, zero_smul, sub_zero]
      rw [← hraw t]
      simp only [glueRaw, max_eq_right hts, add_sub_cancel_right]
    · have hmin : g.path.rightMin i t = τ.path.rightMin i t + d := by
        apply le_antisymm
        · obtain ⟨v, hv, hvm⟩ := τ.path.exists_rightMin i ht.2
          exact (g.path.rightMin_le hv).trans_eq (by rw [hr v (hst.trans hv.1), hvm])
        · apply g.path.le_rightMin ht.2
          intro v hv
          rw [hr v (hst.trans hv.1)]
          have hh := τ.path.rightMin_le (i := i) hv
          linarith
      have hcoeff : min (g.path.rightMin i t) (g.path.minPairing i + 1) -
          g.path.minPairing i =
          min (τ.path.rightMin i t) (τ.path.minPairing i + 1) - τ.path.minPairing i := by
        rw [hmin, hm, show τ.path.minPairing i + d + 1 =
          τ.path.minPairing i + 1 + d by ring, min_add_add_right]
        ring
      rw [f_apply hf ht, hcoeff, ← hraw t]
      simp only [glueRaw, min_eq_right (hss.trans hst), max_eq_left hst]
      rw [hυ, hcut, f_apply hζ ht]
      module
  have hiter : (LittelmannPath.crystal (P.pathSpace hA)).fIter i (k + 1) δ.path =
      some υ.path := by
    rw [Crystal.fIter_succ', hτ, Option.bind_some]
    simpa only [hυ, LittelmannPath.crystal_f] using hζ
  refine ⟨k, υ, hk, hiter, (Crystal.fIter_eq_some_iff _ _ _ _).mp hiter,
    ?_, hsub.trans hsub', ?_⟩
  · intro t
    by_cases ht0 : 0 ≤ t
    · by_cases ht1 : t ≤ 1
      · exact hout t ⟨ht0, ht1⟩
      · have h1t := le_of_not_ge ht1
        have hs : (g.s : ℝ) ≤ 1 := hss.trans hs1.le
        simpa only [glueRaw, min_eq_right (hs.trans h1t), min_eq_right hs,
          max_eq_left (hs1.le.trans h1t), max_eq_left hs1.le,
          υ.path.apply_of_one_le h1t, η.apply_of_one_le h1t, apply_one]
          using hout 1 ⟨zero_le_one, le_rfl⟩
    · have ht : t ≤ 0 := (lt_of_not_ge ht0).le
      simp only [glueRaw, min_eq_left (ht.trans hs0.le),
        max_eq_right (ht.trans (hs0.le.trans hss)), σ.path.apply_of_nonpos ht,
        η.apply_of_nonpos ht, zero_add, sub_self]
  · intro j
    obtain ⟨w, hw⟩ := ho j
    obtain ⟨v, hv⟩ := horbit 0
    exact ⟨w * v, by rw [hw, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩

end GluingPair

end Matrix.Realization.LSGeneralClass
