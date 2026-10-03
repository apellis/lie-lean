/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingStrict

/-!
# Complementary strict-before and equality-seam reconstruction

## Main results

`GluingPair.exists_e_gluing_strict_before` transports general strict-before raising
through literal complementary-time reversal, without source matching or slope restrictions.
`GluingPair.exists_f_gluing_at_cut_of_nonpos` closes the equality case where the last
global minimum is at the right cut and the right auxiliary direction is nonpositive.
It constructs a strict output witness: the outgoing source direction is reflected,
but both auxiliary directions, both cuts and the left source remain unchanged.
Both sectors derive all-simple-root output global-minimum integrality.

Closed-right source normalization includes equality at the cut. A finite normalized
source supplies an actual reflected output interval, and prefix coarsening gives the
strict right source with the reflected initial direction. The integral-position chain
reflection needed at this equality seam is proved via the published source-chain bridge.
The actual source string and its strict representative are never identified.

Positive-auxiliary equality, left-end equality, crossing seams and mixed-word stability
remain open. This module does not claim full Proposition 5.6.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), Definition 5.3, Remark 5.4, Proposition 5.6, pp. 514–516.
The proofs are reconstructed.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- At an integral position, reflection of a positive target leaves a nonpositive
initial direction unchanged. This is the integral branch needed at equality seams. -/
theorem PositionChain.reflect_integral_target {p x y : Dual ℝ H} {i : ι}
    (h : PositionChain P hA p x y) (hint : x ∈ P.integralWeights)
    (hp : ∃ z : ℤ, p (P.coroot i) = z)
    (hx : x (P.coroot i) ≤ 0) (hy : 0 < y (P.coroot i)) :
    PositionChain P hA p x (P.reflection hA i y) := by
  let X : P.integralWeights := ⟨x, hint⟩
  have hxO : ∃ w : P.weylGroup hA, x = w.1 X := ⟨1, by simp [X]⟩
  obtain ⟨hi, hc, -⟩ := h.to_chain hxO hint
  let Y : P.integralWeights := ⟨y, hi⟩
  have hxc : (P.cartanDatum hA).coroot i X ≤ 0 := by
    rw [← coroot_cartanDatum_cast P hA i X] at hx
    exact_mod_cast hx
  have hyc : 0 < (P.cartanDatum hA).coroot i Y :=
    coroot_cartanDatum_pos_iff.mpr hy
  have hnew := (hc.reflection (i := i) hp hxO).2 hxc hyc
  have hh := (chain_iff_positionChain X X ((P.cartanDatum hA).reflection i Y) p hxO).mp hnew
  simpa only [coe_reflection_cartanDatum] using hh

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- The general strict-before raising sector of Proposition 5.6, with no terminal
slope or source-minimum matching premise. The actual source exponent is derived;
the coarsened strict representative is not identified with that source string. -/
theorem exists_e_gluing_strict_before {i : ι} {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) g.s)
    (hum : g.path.pairing i u = g.path.minPairing i)
    {η : LittelmannPath (P.pathSpace hA)} (he : LittelmannPath.e i g.path = some η) :
    ∃ (k : ℕ) (υ τ : Presentation P hA) (g' : GluingPair τ δ),
      σ.path.pairing i u = σ.path.minPairing i + k ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i (k + 1) σ.path = some υ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i (k + 1) υ.path = some σ.path ∧
      (∀ t : ℝ, t ≤ (g.s : ℝ) →
        τ.path t - τ.path g.s = υ.path t - υ.path g.s) ∧
      τ.x (Fin.last τ.n) = σ.x (Fin.last σ.n) ∧ g'.path = η ∧
      g'.s = g.s ∧ g'.s' = g.s' ∧ g'.ν = g.ν ∧ g'.μ = g.μ ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  have hlate : 1 - u ∈ Ioc (g.reverse.s' : ℝ) 1 := by
    change ((1 - g.s : ℚ) : ℝ) < 1 - u ∧ 1 - u ≤ 1
    push_cast
    constructor <;> linarith [hu.1, hu.2]
  have hm : g.reverse.path.pairing i (1 - u) = g.reverse.path.minPairing i := by
    rw [g.reverse_path, pairing_rev, minPairing_rev, sub_sub_cancel, hum]
  have hf : LittelmannPath.f i g.reverse.path = some η.rev := by
    rw [g.reverse_path, f_rev, he, Option.map_some]
  obtain ⟨k, υ, τ, gτ, hk, hυ, -, ht, hx, hp, hs, hs', hν, hμ, ho⟩ :=
    g.reverse.exists_f_gluing_strict_after hlate hm hf
  have hk' : σ.path.pairing i u = σ.path.minPairing i + k := by
    rw [Presentation.reverse_path, pairing_rev, minPairing_rev, sub_sub_cancel] at hk
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
      σ.path.pairing i u = σ.path.minPairing i + k ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i (k + 1) σ.path = some υ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i (k + 1) υ.path = some σ.path ∧
      (∀ t : ℝ, t ≤ (g.s : ℝ) →
        τ.path t - τ.path g.s = υ.path t - υ.path g.s) ∧
      τ.x (Fin.last τ.n) = σ.x (Fin.last σ.n) ∧ g'.path = η ∧
      g'.s = g.s ∧ g'.s' = g.s' ∧ g'.ν = g.ν ∧ g'.μ = g.μ ∧
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
    · change -τ.x (Fin.last τ.n).rev = σ.x (Fin.last σ.n)
      rw [Fin.rev_last, hx]
      change -(-σ.x (0 : Fin (σ.n + 1)).rev) = _
      rw [Fin.rev_zero, neg_neg]
    · rw [gτ.reverse_path, hp, rev_rev]
    · change 1 - gτ.s' = g.s
      rw [hs']
      change 1 - (1 - g.s) = g.s
      ring
    · change 1 - gτ.s = g.s'
      rw [hs]
      change 1 - (1 - g.s') = g.s'
      ring
    · change -gτ.μ = g.ν
      rw [hμ]
      exact neg_neg _
    · change -gτ.ν = g.μ
      rw [hν]
      exact neg_neg _
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

/-- Every simple-root global minimum of an actual strict-before raising output
is integral, including unmatched negative-terminal sources. -/
theorem e_isIntegral_strict_before {i : ι} {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) g.s)
    (hum : g.path.pairing i u = g.path.minPairing i)
    {η : LittelmannPath (P.pathSpace hA)} (he : LittelmannPath.e i g.path = some η) :
    η.IsIntegral := by
  obtain ⟨k, υ, τ, g', -, -, -, -, -, hp, -⟩ :=
    g.exists_e_gluing_strict_before hu hum he
  rw [← hp]
  exact g'.isIntegral

/-- At an actual glued minimum at or after the right cut, the discarded-source gap is a natural
integer. The integrality is derived from the glued minimum and integral cut offset. -/
theorem exists_nat_source_gap_closed {i : ι} {u : ℝ}
    (hu : u ∈ Icc (g.s' : ℝ) 1)
    (hum : g.path.pairing i u = g.path.minPairing i) :
    ∃ k : ℕ, δ.path.pairing i u = δ.path.minPairing i + k := by
  have hright : g.path.pairing i u = δ.path.pairing i u +
      (σ.path g.s - δ.path g.s') (P.coroot i) := by
    change (glueRaw σ δ g.s g.s' u) (P.coroot i) = _
    rw [g.raw_right hu.1, LinearMap.add_apply]
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
    have hu0 : 0 ≤ u := (g.right_cut_mem.1.trans hu.1)
    have hh := δ.path.minPairing_le (i := i) ⟨hu0, hu.2⟩
    have hcast : (0 : ℝ) ≤ (a - b - d : ℤ) := by linarith
    exact_mod_cast hcast
  refine ⟨(a - b - d).toNat, ?_⟩
  have hcast : (((a - b - d).toNat : ℕ) : ℝ) = (a - b - d : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  rw [hcast]
  linarith

/-- A minimum at or after the right cut determines a successful source normalization power.
The finite normalized source stays in the original orbit, its retained tail differs
only by an integral root translation, and re-gluing is literally unchanged at EVERY
real time. This is not a strict `GluingPair`: the normalization may add early cuts. -/
theorem exists_normalized_source_closed {i : ι} {u : ℝ}
    (hu : u ∈ Icc (g.s' : ℝ) 1)
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
  obtain ⟨k, hk⟩ := g.exists_nat_source_gap_closed hu hum
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
    rw [← hum, hr u hu.1, hr t ht.1, hk] at hh
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
  · rw [pairing, htall u hu.1]
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

/-- The closed-right source-power formula, including the equality seam. Here `k` is the height
gap, an actual glued lowering is re-glued from the unchanged left source and the
actual `(k + 1)`-fold lowering of the original right source, in its ORIGINAL orbit.
The right source is finite with strict subdivision and actual source chains. The
literal raw equality does not assert that its first breakpoint remains after the cut. -/
theorem exists_f_source_power_closed {i : ι} {u : ℝ}
    (hu : u ∈ Icc (g.s' : ℝ) 1)
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
    g.exists_normalized_source_closed hu hum
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
    rw [← hum, hr u hu.1, hτmin]
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
  have hcut : ζ g.s' = τ.path g.s' := by
    have hmcut : τ.path.rightMin i g.s' = τ.path.minPairing i := le_antisymm
      ((τ.path.rightMin_le hu).trans_eq hτmin)
      (τ.path.le_rightMin hs1.le (fun v hv ↦
        τ.path.minPairing_le ⟨(hs0.le.trans hss).trans hv.1, hv.2⟩))
    rw [f_apply hζ ⟨hs0.le.trans hss, hs1.le⟩, hmcut,
      min_eq_left (by linarith)]
    simp
  have hout (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      glueRaw σ υ g.s g.s' t = η t := by
    rcases le_total t g.s' with hts | hst
    · have hmin : g.path.rightMin i t = g.path.minPairing i := le_antisymm
        ((g.path.rightMin_le ⟨hts.trans hu.1, hu.2⟩).trans_eq hum)
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

/-- At the last-minimum equality seam, the actual lowering reflects a genuine
right-hand interval. The interval is obtained from a normalized finite source,
not from any assumed LS condition or integrality of the glued output. -/
theorem exists_f_reflected_interval_at_cut {i : ι}
    (hum : g.path.pairing i g.s' = g.path.minPairing i)
    (hlast : ∀ t ∈ Ioc (g.s' : ℝ) 1, g.path.minPairing i < g.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    ∃ q : ℝ, (g.s' : ℝ) < q ∧ q ≤ 1 ∧
      ∀ t ∈ Icc (g.s' : ℝ) q,
        η t - η g.s' = P.reflection hA i (δ.path t - δ.path g.s') := by
  have hs0 := g.right_cut_mem.1
  have hs1 : (g.s' : ℝ) ≤ 1 := by exact_mod_cast g.lt_one.le
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  obtain ⟨k, τ, -, -, -, -, hτm, -, hraw, -⟩ :=
    g.exists_normalized_source_closed ⟨le_rfl, hs1⟩ hum
  let d := (σ.path g.s - τ.path g.s') (P.coroot i)
  have hr (t : ℝ) (ht : (g.s' : ℝ) ≤ t) :
      g.path.pairing i t = τ.path.pairing i t + d := by
    rw [pairing, ← hraw t]
    simp only [glueRaw, min_eq_right (hss.trans ht), max_eq_left ht,
      pathSpace_coroot, LinearMap.add_apply, LinearMap.sub_apply]
    dsimp [pairing, d]
    ring
  have hm : g.path.minPairing i = τ.path.minPairing i + d := by
    rw [← hum, hr _ le_rfl, hτm]
  have h1 : τ.path.minPairing i + 1 ≤ τ.path.pairing i 1 := by
    have hh := (f_eq_none_iff (i := i) (π := g.path)).not.mp (by rw [hf]; simp)
    rw [hr 1 hs1, hm] at hh
    push Not at hh
    linarith
  obtain ⟨p, q, hp0, hpq, hq1, hpm, hplt, hqm, hmono, hqge⟩ :=
    τ.isLS.exists_f_times i h1
  have hpc : p = (g.s' : ℝ) := by
    rcases lt_trichotomy p (g.s' : ℝ) with h | h | h
    · have hh := hplt _ ⟨h, hs1⟩
      rw [hτm] at hh
      exact (lt_irrefl _ hh).elim
    · exact h
    · have hh := hlast p ⟨h, hpq.le.trans hq1⟩
      rw [hr p h.le, hm, hpm] at hh
      exact (lt_irrefl _ hh).elim
  subst p
  have hcoeff (t : ℝ) (ht : t ∈ Icc (g.s' : ℝ) q) :
      min (g.path.rightMin i t) (g.path.minPairing i + 1) - g.path.minPairing i =
        g.path.pairing i t - g.path.minPairing i := by
    have htq : τ.path.pairing i t ≤ τ.path.minPairing i + 1 :=
      hqm ▸ hmono.monotoneOn ht ⟨hpq.le, le_rfl⟩ ht.2
    have hh : g.path.rightMin i t = g.path.pairing i t := le_antisymm
      (g.path.rightMin_le ⟨le_rfl, ht.2.trans hq1⟩)
      (g.path.le_rightMin (ht.2.trans hq1) (fun v hv ↦ by
        rw [hr t ht.1, hr v (ht.1.trans hv.1)]
        apply add_le_add_left
        rcases le_total v q with hvq | hqv
        · exact hmono.monotoneOn ht ⟨ht.1.trans hv.1, hvq⟩ hv.1
        · exact htq.trans (hqge v ⟨hqv, hv.2⟩)))
    rw [hh, min_eq_left (by rw [hr t ht.1, hm]; linarith)]
  refine ⟨q, hpq, hq1, ?_⟩
  intro t ht
  rw [f_apply hf ⟨hs0.trans ht.1, ht.2.trans hq1⟩, hcoeff t ht,
    f_apply hf ⟨hs0, hs1⟩, hcoeff _ ⟨le_rfl, hpq.le⟩, hum]
  simp only [sub_self, zero_smul, sub_zero]
  have hdiff : g.path t - g.path g.s' = δ.path t - δ.path g.s' := by
    change glueRaw σ δ g.s g.s' t - glueRaw σ δ g.s g.s' g.s' = _
    rw [g.raw_right ht.1, g.raw_right le_rfl]
    abel
  rw [← hum, ← hdiff, Matrix.Realization.reflection_apply]
  simp only [pairing, pathSpace_coroot, LinearMap.sub_apply]
  change g.path t - _ • P.root i - g.path g.s' = _
  module

/-- The equality case `t₀ = s'`, `⟨μ, αᵢ∨⟩ ≤ 0` of Proposition 5.6,
p.515. The outgoing source direction is reflected but the auxiliary directions
are unchanged. The strict representative and the actual source string are distinct. -/
theorem exists_f_gluing_at_cut_of_nonpos {i : ι}
    (hum : g.path.pairing i g.s' = g.path.minPairing i)
    (hlast : ∀ t ∈ Ioc (g.s' : ℝ) 1, g.path.minPairing i < g.path.pairing i t)
    (hμ : g.μ (P.coroot i) ≤ 0)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    ∃ (k : ℕ) (υ τ : Presentation P hA) (g' : GluingPair σ τ),
      δ.path.pairing i g.s' = δ.path.minPairing i + k ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i (k + 1) δ.path = some υ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i (k + 1) υ.path = some δ.path ∧
      (∀ t : ℝ, (g.s' : ℝ) ≤ t →
        τ.path t - τ.path g.s' = υ.path t - υ.path g.s') ∧
      (τ.x 0 : Dual ℝ H) = P.reflection hA i (δ.x 0) ∧ g'.path = η ∧
      g'.s = g.s ∧ g'.s' = g.s' ∧ g'.ν = g.ν ∧ g'.μ = g.μ ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (δ.x 0) := by
  have hs0 := g.right_cut_mem.1
  have hs1 : (g.s' : ℝ) < 1 := by exact_mod_cast g.lt_one
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  obtain ⟨k, υ, hk, hυ, heυ, hraw, -, hoυ⟩ :=
    g.exists_f_source_power_closed ⟨le_rfl, hs1.le⟩ hum hf
  obtain ⟨τ, hfirst, htail, hoτ⟩ := υ.exists_coarsen_initial g.lt_one
  have hout (t : ℝ) : glueRaw σ τ g.s g.s' t = η t := by
    rw [← hraw t]
    have hh := htail (max t (g.s' : ℝ)) (le_max_right _ _)
    unfold glueRaw
    simpa only [add_sub_assoc] using congrArg (σ.path (min t (g.s : ℝ)) + ·) hh
  obtain ⟨q, hq, hq1, hreflect⟩ := g.exists_f_reflected_interval_at_cut hum hlast hf
  have hτfirst : (g.s' : ℝ) < τ.a (0 : Fin (τ.n + 1)).succ := by
    exact_mod_cast hfirst
  have hδfirst : (g.s' : ℝ) < δ.a (0 : Fin (δ.n + 1)).succ := by
    exact_mod_cast g.first_gt
  let v := ((g.s' : ℝ) + min q
    (min (τ.a (0 : Fin (τ.n + 1)).succ : ℝ)
      (δ.a (0 : Fin (δ.n + 1)).succ : ℝ))) / 2
  have hv : (g.s' : ℝ) < v ∧ v ≤ q ∧
      v ≤ τ.a (0 : Fin (τ.n + 1)).succ ∧
      v ≤ δ.a (0 : Fin (δ.n + 1)).succ := by
    have hm := lt_min hq (lt_min hτfirst hδfirst)
    have hm1 := min_le_left q
      (min (τ.a (0 : Fin (τ.n + 1)).succ : ℝ)
        (δ.a (0 : Fin (δ.n + 1)).succ : ℝ))
    have hm2 := (min_le_right q
      (min (τ.a (0 : Fin (τ.n + 1)).succ : ℝ)
        (δ.a (0 : Fin (δ.n + 1)).succ : ℝ))).trans (min_le_left _ _)
    have hm3 := (min_le_right q
      (min (τ.a (0 : Fin (τ.n + 1)).succ : ℝ)
        (δ.a (0 : Fin (δ.n + 1)).succ : ℝ))).trans (min_le_right _ _)
    dsimp only [v]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hx : (τ.x 0 : Dual ℝ H) = P.reflection hA i (δ.x 0) := by
    have hh := hreflect v ⟨hv.1.le, hv.2.1⟩
    rw [← hout v, ← hout g.s'] at hh
    simp only [glueRaw, min_eq_right (hss.trans hv.1.le), max_eq_left hv.1.le,
      min_eq_right hss, max_self, add_sub_cancel_right] at hh
    rw [τ.first_piece v ⟨hs0.trans hv.1.le, hv.2.2.1⟩,
      τ.first_piece g.s' ⟨hs0, hτfirst.le⟩,
      δ.first_piece v ⟨hs0.trans hv.1.le, hv.2.2.2⟩,
      δ.first_piece g.s' ⟨hs0, hδfirst.le⟩, map_sub, map_smul, map_smul] at hh
    apply (smul_right_inj (sub_ne_zero.mpr hv.1.ne')).mp
    simp only [sub_smul]
    calc
      _ = σ.path g.s + v • (τ.x 0 : Dual ℝ H) -
          (g.s' : ℝ) • (τ.x 0 : Dual ℝ H) - σ.path g.s := by abel
      _ = _ := hh
  have hy : 0 < (δ.x 0 : Dual ℝ H) (P.coroot i) := by
    have hh := g.right_direction.coroot_pos (sub_pos.mpr hs1) (i := i) (fun t ht ↦ by
      rw [hum]
      exact hlast t ⟨ht.1, by linarith [ht.2]⟩)
    exact coroot_cartanDatum_pos_iff.mp hh
  have hint : ∃ z : ℤ, (δ.path g.s') (P.coroot i) = z := by
    obtain ⟨a, ha⟩ := g.isIntegral i
    obtain ⟨b, hb⟩ := g.offset_integral i
    have hh : g.path.pairing i g.s' = (σ.path g.s) (P.coroot i) := by
      simp only [pairing, pathSpace_coroot, g.path_pause ⟨hss, le_rfl⟩]
    rw [hum, ha] at hh
    simp only [LinearMap.sub_apply] at hb
    refine ⟨a - b, ?_⟩
    push_cast
    linarith
  have hright : AChain P hA (g.s' : ℝ) g.μ (P.reflection hA i (δ.x 0)) := by
    have hp := g.right_chain.at_target
    rw [← δ.first_piece g.s' g.right_cut_mem] at hp
    have hn := hp.reflect_integral_target g.right_direction_integral hint hμ hy
    apply (hn.to_aChain ?_).1
    have hh := (g.right_chain.to_positionChain
      (p := (g.s' : ℝ) • g.μ) (by simp)).2
    rw [δ.first_piece g.s' g.right_cut_mem]
    simpa only [neg_sub] using (LSAChainBridge.rootLattice P).neg_mem hh
  let g' : GluingPair σ τ :=
    { s := g.s
      s' := g.s'
      pos := g.pos
      le := g.le
      lt_one := g.lt_one
      last_lt := g.last_lt
      first_gt := hfirst
      ν := g.ν
      μ := g.μ
      left_chain := g.left_chain
      right_chain := by rw [hx]; exact hright
      precedes := g.precedes
      endpoint := by rw [hout 1, η.apply_one]; exact η.wt.property }
  refine ⟨k, υ, τ, g', hk, hυ, heυ, htail, hx, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · apply LittelmannPath.ext_of_eqOn
    intro t _
    exact hout t
  · intro j
    obtain ⟨w, hw⟩ := hoτ j
    obtain ⟨z, hz⟩ := hoυ 0
    exact ⟨w * z, by rw [hw, hz, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩

/-- All-root global-minimum integrality for the actual nonpositive-auxiliary
right equality-seam lowering output, not only integrality of the operated root. -/
theorem f_isIntegral_at_cut_of_nonpos {i : ι}
    (hum : g.path.pairing i g.s' = g.path.minPairing i)
    (hlast : ∀ t ∈ Ioc (g.s' : ℝ) 1, g.path.minPairing i < g.path.pairing i t)
    (hμ : g.μ (P.coroot i) ≤ 0)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    η.IsIntegral := by
  obtain ⟨k, υ, τ, g', -, -, -, -, -, hp, -⟩ :=
    g.exists_f_gluing_at_cut_of_nonpos hum hlast hμ hf
  rw [← hp]
  exact g'.isIntegral

end GluingPair
end Matrix.Realization.LSGeneralClass
