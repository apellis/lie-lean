/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingCrossing

/-!
# Dual crossing and the exhaustive last-minimum partition

## Main results
Actual raising crossing outputs are transported by reversal, retaining literal source
powers separately from strict coarsenings. The lowering partition derives its crossing
window and future bound from minimum locations, rather than assuming operator times.

## References
Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), Definition 5.3 and Proposition 5.6, pp.514–516. Proofs reconstructed from
literal finite source paths; this file does not claim full Proposition 5.6.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

namespace Presentation

/-- Negating a reversed source orbit restores its original, not its dual, Weyl orbit. -/
theorem reverse_orbit_transport {σ τ : Presentation P hA}
    (ho : ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.reverse.x 0)) :
    ∀ j, ∃ w : P.weylGroup hA, (τ.reverse.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  intro j
  obtain ⟨v, hv⟩ := ho j.rev
  obtain ⟨w, hw⟩ := σ.orbit (Fin.last σ.n)
  refine ⟨v * w, ?_⟩
  change -(τ.x j.rev : Dual ℝ H) = (v * w).1 (σ.x 0)
  rw [hv]
  change -v.1 (-(σ.x (0 : Fin (σ.n + 1)).rev : Dual ℝ H)) = _
  rw [Fin.rev_zero, map_neg, neg_neg, hw, Subgroup.coe_mul, LinearEquiv.mul_apply]

/-- Transport an actual lowering string on a reversed source to its raising string. -/
theorem eIter_of_reverse_fIter {σ υ : Presentation P hA} {i : ι} {n : ℕ}
    (hf : (LittelmannPath.crystal (P.pathSpace hA)).fIter i n σ.reverse.path =
      some υ.path) :
    (LittelmannPath.crystal (P.pathSpace hA)).eIter i n σ.path =
      some υ.reverse.path := by
  rw [Presentation.reverse_path, fIter_rev_eq_map_eIter] at hf
  have hh := congrArg (Option.map LittelmannPath.rev) hf
  simp only [Option.map_map, Function.comp_def, rev_rev, Option.map_some] at hh
  change Option.map id _ = _ at hh
  rw [Option.map_id] at hh
  rw [Presentation.reverse_path]
  exact hh

end Presentation

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- The raising crossing window, with its past bound, is exactly the lowering window
on the reversed pair. The seam height is unchanged apart from endpoint translation. -/
theorem reverse_crossing_window {i : ι}
    (hseam : g.path.minPairing i < (σ.path g.s) (P.coroot i) ∧
      (σ.path g.s) (P.coroot i) < g.path.minPairing i + 1)
    (hpast : ∀ t ∈ Icc (0 : ℝ) g.s, (σ.path g.s) (P.coroot i) ≤ g.path.pairing i t) :
    (g.reverse.path.minPairing i <
        (δ.reverse.path g.reverse.s) (P.coroot i) ∧
      (δ.reverse.path g.reverse.s) (P.coroot i) < g.reverse.path.minPairing i + 1) ∧
    ∀ t ∈ Icc (g.reverse.s' : ℝ) 1,
      (δ.reverse.path g.reverse.s) (P.coroot i) ≤ g.reverse.path.pairing i t := by
  have hc : (δ.reverse.path g.reverse.s) (P.coroot i) =
      (σ.path g.s) (P.coroot i) - g.path.pairing i 1 := by
    have he := g.path_right (show (g.s' : ℝ) ≤ 1 by exact_mod_cast g.lt_one.le)
    change _ = (σ.path g.s) (P.coroot i) - (g.path 1) (P.coroot i)
    rw [he, Presentation.reverse_path, rev_apply, apply_one]
    change (δ.path (1 - ((1 - g.s' : ℚ) : ℝ)) - δ.path 1) (P.coroot i) = _
    simp only [Rat.cast_sub, Rat.cast_one, sub_sub_cancel, LinearMap.sub_apply,
      LinearMap.add_apply, apply_one]
    ring
  refine ⟨?_, ?_⟩
  · rw [hc, g.reverse_path, minPairing_rev]
    constructor <;> linarith [hseam.1, hseam.2]
  · intro t ht
    have ht' : 1 - t ∈ Icc (0 : ℝ) g.s := by
      change ((1 - g.s : ℚ) : ℝ) ≤ t ∧ t ≤ 1 at ht
      push_cast at ht
      constructor <;> linarith [ht.1, ht.2]
    rw [hc, g.reverse_path, pairing_rev]
    exact sub_le_sub_right (hpast _ ht') _

/-- Actual strict raising crossing output, dual to Proposition 5.6's lowering sector.
Both original source orbits, powers and inverse strings survive reversal. The left power
ends at height `m+1`; the right source is raised to the top of its string. Neither literal
power is silently identified with its separately constructed strict representative. -/
theorem exists_e_gluing_crossing {i : ι}
    (hseam : g.path.minPairing i < (σ.path g.s) (P.coroot i) ∧
      (σ.path g.s) (P.coroot i) < g.path.minPairing i + 1)
    (hpast : ∀ t ∈ Icc (0 : ℝ) g.s, (σ.path g.s) (P.coroot i) ≤ g.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)} (he : LittelmannPath.e i g.path = some η) :
    ∃ (n m : ℕ) (υ ω τ ρ : Presentation P hA) (g' : GluingPair τ ρ),
      σ.path.minPairing i + n = g.path.minPairing i + 1 ∧
      δ.path.minPairing i + m = 0 ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i n σ.path = some υ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i n υ.path = some σ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i m δ.path = some ω.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i m ω.path = some δ.path ∧
      (∀ t : ℝ, t ≤ (g.s : ℝ) →
        τ.path t - τ.path g.s = υ.path t - υ.path g.s) ∧
      (∀ t : ℝ, (g.s' : ℝ) ≤ t →
        ρ.path t - ρ.path g.s' = ω.path t - ω.path g.s') ∧
      (τ.x (Fin.last τ.n) : Dual ℝ H) = P.reflection hA i (σ.x (Fin.last σ.n)) ∧
      (ρ.x 0 : Dual ℝ H) = P.reflection hA i (δ.x 0) ∧
      g'.path = η ∧ g'.s = g.s ∧ g'.s' = g.s' ∧
      g'.ν = P.reflection hA i g.ν ∧ g'.μ = P.reflection hA i g.μ ∧
      (∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
      ∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (δ.x 0) := by
  obtain ⟨hw, ht⟩ := g.reverse_crossing_window hseam hpast
  have hf : LittelmannPath.f i g.reverse.path = some η.rev := by
    rw [g.reverse_path, f_rev, he, Option.map_some]
  obtain ⟨m, n, ω, υ, ρ, τ, g', hm, hn, hω, -, hυ, -, hρ, hτ,
      hy, hx, hp, hs, hs', hν, hμ, hoρ, hoτ⟩ :=
    g.reverse.exists_f_gluing_crossing hw ht hf
  have heυ := Presentation.eIter_of_reverse_fIter hυ
  have heω := Presentation.eIter_of_reverse_fIter hω
  have hm' : δ.path.minPairing i + m = 0 := by
    rw [Presentation.reverse_path, minPairing_rev, pairing_rev, sub_self,
      pairing_zero] at hm
    linarith
  have hn' : σ.path.minPairing i + n = g.path.minPairing i + 1 := by
    rw [Presentation.reverse_path, minPairing_rev, g.reverse_path, minPairing_rev] at hn
    simp only [Presentation.reverse_path, rev_apply, apply_one] at hn
    have he1 := g.path_right (show (g.s' : ℝ) ≤ 1 by exact_mod_cast g.lt_one.le)
    change σ.path.minPairing i - σ.path.pairing i 1 + n +
      ((δ.path (1 - ((1 - g.s' : ℚ) : ℝ)) - δ.path 1) -
        (σ.path (1 - ((1 - g.s : ℚ) : ℝ)) - σ.path 1)) (P.coroot i) = _ at hn
    simp only [Rat.cast_sub, Rat.cast_one, sub_sub_cancel, LinearMap.sub_apply] at hn
    simp only [pairing, pathSpace_coroot, he1, LinearMap.add_apply,
      LinearMap.sub_apply] at hn
    linarith
  refine ⟨n, m, υ.reverse, ω.reverse, τ.reverse, ρ.reverse, g'.reverse,
    hn', hm', heυ, (Crystal.fIter_eq_some_iff _ _ _ _).mpr heυ,
    heω, (Crystal.fIter_eq_some_iff _ _ _ _).mpr heω, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, Presentation.reverse_orbit_transport hoτ,
    Presentation.reverse_orbit_transport hoρ⟩
  · intro t ht'
    have hh := hτ (1 - t) (by
      change ((1 - g.s : ℚ) : ℝ) ≤ 1 - t
      push_cast
      linarith)
    change τ.path (1 - t) - τ.path ((1 - g.s : ℚ) : ℝ) =
      υ.path (1 - t) - υ.path ((1 - g.s : ℚ) : ℝ) at hh
    push_cast at hh
    simp only [Presentation.reverse_path, rev_apply]
    convert hh using 1 <;> abel
  · intro t ht'
    have hh := hρ (1 - t) (by
      change 1 - t ≤ ((1 - g.s' : ℚ) : ℝ)
      push_cast
      linarith)
    have hc := hρ (1 - (g.s' : ℝ)) (by
      change 1 - (g.s' : ℝ) ≤ ((1 - g.s' : ℚ) : ℝ)
      push_cast
      exact le_rfl)
    simp only [Presentation.reverse_path, rev_apply]
    rw [hh, hc]
    abel
  · change -(τ.x (Fin.last τ.n).rev : Dual ℝ H) = _
    rw [Fin.rev_last, hx]
    change -P.reflection hA i (-(σ.x (0 : Fin (σ.n + 1)).rev : Dual ℝ H)) = _
    rw [Fin.rev_zero, map_neg, neg_neg]
  · change -(ρ.x (0 : Fin (ρ.n + 1)).rev : Dual ℝ H) = _
    rw [Fin.rev_zero, hy]
    change -P.reflection hA i (-(δ.x (Fin.last δ.n).rev : Dual ℝ H)) = _
    rw [Fin.rev_last, map_neg, neg_neg]
  · rw [g'.reverse_path, hp, rev_rev]
  · change 1 - g'.s' = g.s
    rw [hs']
    change 1 - (1 - g.s) = g.s
    ring
  · change 1 - g'.s = g.s'
    rw [hs]
    change 1 - (1 - g.s') = g.s'
    ring
  · change -g'.μ = _
    rw [hμ]
    change -P.reflection hA i (-g.ν) = _
    rw [map_neg, neg_neg]
  · change -g'.ν = _
    rw [hν]
    change -P.reflection hA i (-g.μ) = _
    rw [map_neg, neg_neg]

/-- All-simple-root integrality from the actual strict dual crossing output. -/
theorem e_isIntegral_crossing {i : ι}
    (hseam : g.path.minPairing i < (σ.path g.s) (P.coroot i) ∧
      (σ.path g.s) (P.coroot i) < g.path.minPairing i + 1)
    (hpast : ∀ t ∈ Icc (0 : ℝ) g.s, (σ.path g.s) (P.coroot i) ≤ g.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)} (he : LittelmannPath.e i g.path = some η) :
    η.IsIntegral := by
  obtain ⟨n, m, υ, ω, τ, ρ, g', -, -, -, -, -, -, -, -, -, -, hp, -⟩ :=
    g.exists_e_gluing_crossing hseam hpast he
  rw [← hp]
  exact g'.isIntegral

/-- A tail without a global minimizer cannot dip below both the seam and the next
integral level. This is derived from actual right-source local-minimum integrality and
the integral offset; no monotonicity or crossing-time hypothesis is supplied. -/
theorem tail_bound_of_no_minimum {i : ι}
    (hno : ∀ t ∈ Icc (g.s' : ℝ) 1, g.path.minPairing i < g.path.pairing i t) :
    ∀ t ∈ Icc (g.s' : ℝ) 1,
      min ((σ.path g.s) (P.coroot i)) (g.path.minPairing i + 1) ≤ g.path.pairing i t := by
  have hs0 : (0 : ℝ) < g.s' := by exact_mod_cast g.pos.trans_le g.le
  have hs1 : (g.s' : ℝ) < 1 := by exact_mod_cast g.lt_one
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  obtain ⟨w, hw, hmin, hlast⟩ :=
    exists_last_minimizer (g.path.continuous_pairing i) hs1.le
  intro t ht
  by_cases hws : w = (g.s' : ℝ)
  · apply (min_le_left _ _).trans
    have hh := hmin t ht
    simpa only [hws, pairing, pathSpace_coroot, g.path_pause ⟨hss, le_rfl⟩] using hh
  have hsw : (g.s' : ℝ) < w := lt_of_le_of_ne hw.1 (Ne.symm hws)
  have hint : ∃ z : ℤ, g.path.pairing i w = z := by
    rcases eq_or_lt_of_le hw.2 with hw1 | hw1
    · exact ⟨_, by rw [hw1, pairing_one]⟩
    have hr (v : ℝ) (hv : (g.s' : ℝ) ≤ v) :
        g.path.pairing i v = δ.path.pairing i v +
          (σ.path g.s - δ.path g.s') (P.coroot i) := by
      simp only [pairing, pathSpace_coroot, g.path_right hv, LinearMap.add_apply]
    obtain ⟨z, hz⟩ := δ.isLS.exists_int_of_isMin ⟨hs0.trans hsw, hw1⟩ hsw hw1
      (fun v hv ↦ by
        have hh := hmin v hv
        rw [hr w hw.1, hr v hv.1] at hh
        linarith)
      (fun v hv ↦ by
        have hh := hlast v hv
        rw [hr w hw.1, hr v (hw.1.trans hv.1.le)] at hh
        linarith)
    obtain ⟨d, hd⟩ := g.offset_integral i
    refine ⟨z + d, ?_⟩
    rw [hr w hw.1, hz, hd, Int.cast_add]
  obtain ⟨z, hz⟩ := hint
  obtain ⟨m, hm⟩ := g.isIntegral i
  have hzm : m < z := by exact_mod_cast (show (m : ℝ) < z by simpa [hz, hm] using hno w hw)
  have hstep : (m : ℝ) + 1 ≤ z := by exact_mod_cast (show m + 1 ≤ z by omega)
  have hlevel : g.path.minPairing i + 1 ≤ g.path.pairing i w := by
    simpa only [hm, hz] using hstep
  exact (min_le_right _ _).trans (hlevel.trans (hmin t ht))

/-- The exact exhaustive lowering partition by the LAST global minimum and seam height.
The genuine crossing sector's unit window and future bound are conclusions. The final
sector isolates precisely the retained-left endpoint/strict-before lowering gap. -/
theorem lowering_location_partition (i : ι) :
    (∃ u ∈ Ioc (g.s' : ℝ) 1, g.path.pairing i u = g.path.minPairing i) ∨
    (g.path.pairing i g.s' = g.path.minPairing i ∧
      ∀ t ∈ Ioc (g.s' : ℝ) 1, g.path.minPairing i < g.path.pairing i t) ∨
    ((g.path.minPairing i < (σ.path g.s) (P.coroot i) ∧
        (σ.path g.s) (P.coroot i) < g.path.minPairing i + 1) ∧
      ∀ t ∈ Icc (g.s' : ℝ) 1, (σ.path g.s) (P.coroot i) ≤ g.path.pairing i t) ∨
    (∃ p ∈ Ico (0 : ℝ) g.s,
      g.path.pairing i p = g.path.minPairing i ∧
      (∀ t ∈ Ioc p 1, g.path.minPairing i < g.path.pairing i t) ∧
      g.path.minPairing i + 1 ≤ (σ.path g.s) (P.coroot i) ∧
      ∀ t ∈ Icc (g.s' : ℝ) 1, g.path.minPairing i + 1 ≤ g.path.pairing i t) := by
  have hs0 : (0 : ℝ) ≤ g.s := by exact_mod_cast g.pos.le
  have hs1 : (g.s' : ℝ) ≤ 1 := by exact_mod_cast g.lt_one.le
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  obtain ⟨p, hp, hmin, hlast⟩ :=
    exists_last_minimizer (g.path.continuous_pairing i) (zero_le_one (α := ℝ))
  have hpm : g.path.pairing i p = g.path.minPairing i := by
    apply le_antisymm _ (g.path.minPairing_le hp)
    obtain ⟨u, hu, hum⟩ := g.path.exists_minPairing i
    exact (hmin u hu).trans_eq hum
  have hlast' : ∀ t ∈ Ioc p 1, g.path.minPairing i < g.path.pairing i t := by
    simpa only [hpm] using hlast
  rcases lt_trichotomy (g.s' : ℝ) p with hlate | heq | hearly
  · exact Or.inl ⟨p, ⟨hlate, hp.2⟩, hpm⟩
  · exact Or.inr (Or.inl (by simpa only [← heq] using And.intro hpm hlast'))
  have hno : ∀ t ∈ Icc (g.s' : ℝ) 1, g.path.minPairing i < g.path.pairing i t :=
    fun t ht ↦ hlast' t ⟨hearly.trans_le ht.1, ht.2⟩
  have hc : g.path.minPairing i < (σ.path g.s) (P.coroot i) := by
    simpa only [pairing, pathSpace_coroot, g.path_pause ⟨hss, le_rfl⟩] using
      hno g.s' ⟨le_rfl, hs1⟩
  have hps : p < (g.s : ℝ) := by
    by_contra h
    have hh : g.path.pairing i p = (σ.path g.s) (P.coroot i) := by
      simp only [pairing, pathSpace_coroot, g.path_pause ⟨le_of_not_gt h, hearly.le⟩]
    linarith
  by_cases hupper : (σ.path g.s) (P.coroot i) < g.path.minPairing i + 1
  · exact Or.inr (Or.inr (Or.inl ⟨⟨hc, hupper⟩, by
      simpa only [min_eq_left hupper.le] using g.tail_bound_of_no_minimum hno⟩))
  · have hh := le_of_not_gt hupper
    exact Or.inr (Or.inr (Or.inr ⟨p, ⟨hp.1, hps⟩, hpm, hlast', hh, by
      simpa only [min_eq_right hh] using g.tail_bound_of_no_minimum hno⟩))

/-- In the unresolved retained-left sector, the actual upper operator endpoint exists
at or before the left cut. Strict increase and the entire future bound are derived from
left-source local-minimum integrality, not postulated as a time interface. -/
theorem exists_f_times_before_cut {i : ι} {p : ℝ}
    (hp : p ∈ Ico (0 : ℝ) g.s)
    (hpm : g.path.pairing i p = g.path.minPairing i)
    (hlast : ∀ t ∈ Ioc p 1, g.path.minPairing i < g.path.pairing i t)
    (hlevel : g.path.minPairing i + 1 ≤ (σ.path g.s) (P.coroot i))
    (htail : ∀ t ∈ Icc (g.s' : ℝ) 1,
      g.path.minPairing i + 1 ≤ g.path.pairing i t) :
    ∃ q ∈ Ioc p (g.s : ℝ),
      g.path.pairing i q = g.path.minPairing i + 1 ∧
      StrictMonoOn (g.path.pairing i) (Icc p q) ∧
      ∀ t ∈ Icc q 1, g.path.minPairing i + 1 ≤ g.path.pairing i t := by
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  have hs1 : (g.s' : ℝ) ≤ 1 := by exact_mod_cast g.lt_one.le
  have hsl : (g.s : ℝ) ≤ 1 := hss.trans hs1
  have hc : g.path.pairing i g.s = (σ.path g.s) (P.coroot i) := by
    simp only [pairing, pathSpace_coroot, g.path_left le_rfl]
  have hleft (t : ℝ) (ht : t ≤ (g.s : ℝ)) :
      g.path.pairing i t = σ.path.pairing i t := by
    simp only [pairing, pathSpace_coroot, g.path_left ht]
  obtain ⟨n, hn⟩ := g.isIntegral i
  obtain ⟨q, hq, hqv, hqlt⟩ := exists_first_eq
    (g := fun t ↦ -g.path.pairing i t) (g.path.continuous_pairing i).neg hp.2.le
    (c := -(g.path.minPairing i + 1))
    (show -(g.path.minPairing i + 1) ≤ -g.path.pairing i p by linarith)
    (show -g.path.pairing i g.s ≤ -(g.path.minPairing i + 1) by linarith)
  simp only [neg_inj] at hqv
  have hqlt' : ∀ v ∈ Ico p q, g.path.pairing i v < g.path.minPairing i + 1 :=
    fun v hv ↦ by linarith [hqlt v hv]
  have hpq : p < q := lt_of_le_of_ne hq.1 (by intro h; rw [← h, hpm] at hqv; linarith)
  have hnoint : ∀ w ∈ Ioo p q, ¬ ∃ k : ℤ, g.path.pairing i w = k := by
    intro w hw ⟨k, hk⟩
    have h₁ := hlast w ⟨hw.1, hw.2.le.trans (hq.2.trans hsl)⟩
    have h₂ := hqlt' w ⟨hw.1.le, hw.2⟩
    rw [hk, hn] at h₁ h₂
    have h₁' : n < k := by exact_mod_cast h₁
    have h₂' : k < n + 1 := by exact_mod_cast h₂
    omega
  have hmono : StrictMonoOn (g.path.pairing i) (Icc p q) := by
    intro u hu v hv huv
    by_contra hvu
    replace hvu := not_lt.mp hvu
    obtain ⟨w, hw, hwmin, hwlt⟩ :=
      exists_last_minimizer (g.path.continuous_pairing i) hu.2
    have hvq : v < q := lt_of_le_of_ne hv.2 (by
      intro h
      have hh := hqlt' u ⟨hu.1, huv.trans_le hv.2⟩
      rw [h] at hvu
      linarith)
    have hwv := hwmin v ⟨huv.le, hv.2⟩
    have hwq : w ≠ q := by
      intro h
      have hh := hqlt' v ⟨hv.1, hvq⟩
      rw [h] at hwv
      linarith
    have hwu : w ≠ u := by
      intro h
      have hh := hwlt v ⟨h ▸ huv, hv.2⟩
      rw [h] at hh
      linarith
    have huw := lt_of_le_of_ne hw.1 (Ne.symm hwu)
    have hwq' := lt_of_le_of_ne hw.2 hwq
    apply hnoint w ⟨hu.1.trans_lt huw, hwq'⟩
    rw [hleft w (hw.2.trans hq.2)]
    exact σ.isLS.exists_int_of_isMin
      ⟨hp.1.trans_lt (hu.1.trans_lt huw), hwq'.trans_le (hq.2.trans hsl)⟩ huw hwq'
      (fun t ht ↦ by
        simpa only [hleft w (hw.2.trans hq.2), hleft t (ht.2.trans hq.2)] using hwmin t ht)
      (fun t ht ↦ by
        simpa only [hleft w (hw.2.trans hq.2), hleft t (ht.2.trans hq.2)] using hwlt t ht)
  refine ⟨q, ⟨hpq, hq.2⟩, hqv, hmono, ?_⟩
  intro t ht
  by_cases hts : t ≤ (g.s : ℝ)
  · by_contra h
    have hlow := lt_of_not_ge h
    obtain ⟨w, hw, hwmin, hwlt⟩ :=
      exists_last_minimizer (g.path.continuous_pairing i) hq.2
    have hws : g.path.pairing i w < g.path.minPairing i + 1 :=
      (hwmin t ⟨ht.1, hts⟩).trans_lt hlow
    have hwm := hlast w ⟨hpq.trans_le hw.1, hw.2.trans hsl⟩
    have hwq : q < w := lt_of_le_of_ne hw.1 (by intro h; rw [← h, hqv] at hws; linarith)
    have hwcut : w < (g.s : ℝ) := lt_of_le_of_ne hw.2 (by
      intro h
      rw [h, hc] at hws
      linarith)
    obtain ⟨k, hk⟩ := σ.isLS.exists_int_of_isMin
      ⟨hp.1.trans_lt (hpq.trans hwq), hwcut.trans_le hsl⟩ hwq hwcut
      (fun v hv ↦ by simpa only [hleft w hw.2, hleft v hv.2] using hwmin v hv)
      (fun v hv ↦ by simpa only [hleft w hw.2, hleft v hv.2] using hwlt v hv)
    rw [hleft w hw.2, hk, hn] at hws hwm
    have h₁ : n < k := by exact_mod_cast hwm
    have h₂ : k < n + 1 := by exact_mod_cast hws
    omega
  · by_cases hts' : t ≤ (g.s' : ℝ)
    · simpa only [pairing, pathSpace_coroot,
        g.path_pause ⟨le_of_not_ge hts, hts'⟩] using hlevel
    · exact htail t ⟨le_of_not_ge hts', ht.2⟩

/-- Exhaustive successful lowering: an actual strict original-orbit output with
all-root integrality, or the explicitly delimited `p < q ≤ s` sector. In the latter
sector the literal output on the whole suffix is proved, not assumed. This theorem
records a remaining construction obligation; it does not assert unconditional stability. -/
theorem exists_f_gluing_or_before_cut {i : ι}
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    (∃ (τ ρ : Presentation P hA) (g' : GluingPair τ ρ),
      g'.path = η ∧ g'.s = g.s ∧ g'.s' = g.s' ∧
      ((g'.ν = g.ν ∧ g'.μ = g.μ) ∨
        (g'.ν = P.reflection hA i g.ν ∧ g'.μ = P.reflection hA i g.μ)) ∧
      (∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
      (∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (δ.x 0)) ∧
      η.IsIntegral) ∨
    (∃ p q : ℝ, 0 ≤ p ∧ p < q ∧ q ≤ (g.s : ℝ) ∧
      g.path.pairing i p = g.path.minPairing i ∧
      (∀ t ∈ Ioc p 1, g.path.minPairing i < g.path.pairing i t) ∧
      g.path.pairing i q = g.path.minPairing i + 1 ∧
      StrictMonoOn (g.path.pairing i) (Icc p q) ∧
      (∀ t ∈ Icc q 1, g.path.minPairing i + 1 ≤ g.path.pairing i t) ∧
      ∀ t ∈ Icc q 1, η t = g.path t - P.root i) := by
  rcases g.lowering_location_partition i with h | h | h | h
  · obtain ⟨u, hu, hum⟩ := h
    obtain ⟨k, υ, τ, g', -, -, -, -, -, hp, hs, hs', hν, hμ, ho⟩ :=
      g.exists_f_gluing_strict_after hu hum hf
    exact Or.inl ⟨σ, τ, g', hp, hs, hs', Or.inl ⟨hν, hμ⟩,
      σ.orbit, ho, hp ▸ g'.isIntegral⟩
  · obtain ⟨k, υ, τ, g', -, -, -, -, -, hp, hs, hs', hν, hμ, ho⟩ :=
      g.exists_f_gluing_at_right_cut h.1 h.2 hf
    refine Or.inl ⟨σ, τ, g', hp, hs, hs', ?_, σ.orbit, ho, hp ▸ g'.isIntegral⟩
    by_cases hμ0 : g.μ (P.coroot i) ≤ 0
    · exact Or.inl ⟨by simpa only [ite_eq_left hμ0] using hν,
        by simpa only [ite_eq_left hμ0] using hμ⟩
    · exact Or.inr ⟨by simpa only [ite_eq_right hμ0] using hν,
        by simpa only [ite_eq_right hμ0] using hμ⟩
  · obtain ⟨n, m, υ, ω, τ, ρ, g', -, -, -, -, -, -, -, -, -, -, hp,
        hs, hs', hν, hμ, hoτ, hoρ⟩ := g.exists_f_gluing_crossing h.1 h.2 hf
    exact Or.inl ⟨τ, ρ, g', hp, hs, hs', Or.inr ⟨hν, hμ⟩, hoτ, hoρ,
      hp ▸ g'.isIntegral⟩
  · obtain ⟨p, hp, hpm, hlast, hlevel, htail⟩ := h
    obtain ⟨q, hq, hqm, hmono, hfuture⟩ :=
      g.exists_f_times_before_cut hp hpm hlast hlevel htail
    refine Or.inr ⟨p, q, hp.1, hq.1, hq.2, hpm, hlast, hqm, hmono, hfuture, ?_⟩
    intro t ht
    have hr : g.path.minPairing i + 1 ≤ g.path.rightMin i t :=
      g.path.le_rightMin ht.2 (fun u hu ↦ hfuture u ⟨ht.1.trans hu.1, hu.2⟩)
    rw [f_apply hf ⟨(hp.1.trans hq.1.le).trans ht.1, ht.2⟩, min_eq_right hr]
    simp only [add_sub_cancel_left, one_smul]
    rfl

/-- Exhaustive successful raising, transported from the literal lowering partition.
The only unresolved sector has `s' ≤ a < b`, first global minimum `b`, upper level `a`,
strict decrease between them and the derived upper-level bound on the entire prefix.
Both equality endpoints are included explicitly; no mixed-word closure is inferred. -/
theorem exists_e_gluing_or_after_cut {i : ι}
    {η : LittelmannPath (P.pathSpace hA)} (he : LittelmannPath.e i g.path = some η) :
    (∃ (τ ρ : Presentation P hA) (g' : GluingPair τ ρ),
      g'.path = η ∧ g'.s = g.s ∧ g'.s' = g.s' ∧
      ((g'.ν = g.ν ∧ g'.μ = g.μ) ∨
        (g'.ν = P.reflection hA i g.ν ∧ g'.μ = P.reflection hA i g.μ)) ∧
      (∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
      (∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (δ.x 0)) ∧
      η.IsIntegral) ∨
    (∃ a b : ℝ, (g.s' : ℝ) ≤ a ∧ a < b ∧ b ≤ 1 ∧
      g.path.pairing i b = g.path.minPairing i ∧
      (∀ t ∈ Ico (0 : ℝ) b, g.path.minPairing i < g.path.pairing i t) ∧
      g.path.pairing i a = g.path.minPairing i + 1 ∧
      StrictAntiOn (g.path.pairing i) (Icc a b) ∧
      ∀ t ∈ Icc (0 : ℝ) a, g.path.minPairing i + 1 ≤ g.path.pairing i t) := by
  have hf : LittelmannPath.f i g.reverse.path = some η.rev := by
    rw [g.reverse_path, f_rev, he, Option.map_some]
  rcases g.reverse.exists_f_gluing_or_before_cut hf with hout | hgap
  · obtain ⟨ρ, τ, g', hp, hs, hs', haux, hoρ, hoτ, -⟩ := hout
    have hp' : g'.reverse.path = η := by rw [g'.reverse_path, hp, rev_rev]
    refine Or.inl ⟨τ.reverse, ρ.reverse, g'.reverse, hp', ?_, ?_, ?_,
      Presentation.reverse_orbit_transport hoτ,
      Presentation.reverse_orbit_transport hoρ, hp' ▸ g'.reverse.isIntegral⟩
    · change 1 - g'.s' = g.s
      rw [hs']
      change 1 - (1 - g.s) = g.s
      ring
    · change 1 - g'.s = g.s'
      rw [hs]
      change 1 - (1 - g.s') = g.s'
      ring
    · rcases haux with ⟨hν, hμ⟩ | ⟨hν, hμ⟩
      · left
        change -g'.μ = g.ν ∧ -g'.ν = g.μ
        rw [hμ, hν]
        exact ⟨neg_neg _, neg_neg _⟩
      · right
        change -g'.μ = _ ∧ -g'.ν = _
        rw [hμ, hν]
        change -P.reflection hA i (-g.ν) = _ ∧ -P.reflection hA i (-g.μ) = _
        simp only [map_neg, neg_neg, and_self]
  · obtain ⟨p, q, hp0, hpq, hqs, hpm, hlast, hqm, hmono, hfuture, -⟩ := hgap
    change q ≤ ((1 - g.s' : ℚ) : ℝ) at hqs
    push_cast at hqs
    have hheight (t : ℝ) : g.reverse.path.pairing i t =
        g.path.pairing i (1 - t) - g.path.pairing i 1 := by
      rw [g.reverse_path, pairing_rev]
    have hmin : g.reverse.path.minPairing i =
        g.path.minPairing i - g.path.pairing i 1 := by
      rw [g.reverse_path, minPairing_rev]
    refine Or.inr ⟨1 - q, 1 - p, by linarith, by linarith, by linarith, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hheight, hmin] at hpm
      linarith
    · intro t ht
      have hh := hlast (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [hheight, hmin, sub_sub_cancel] at hh
      linarith
    · rw [hheight, hmin] at hqm
      linarith
    · intro u hu v hv huv
      have hh := hmono (a := 1 - v) (b := 1 - u)
        ⟨by linarith [hv.2], by linarith [hv.1]⟩
        ⟨by linarith [hu.2], by linarith [hu.1]⟩ (by linarith)
      simp only [hheight, sub_sub_cancel] at hh
      linarith
    · intro t ht
      have hh := hfuture (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [hheight, hmin, sub_sub_cancel] at hh
      linarith

end GluingPair
end Matrix.Realization.LSGeneralClass
