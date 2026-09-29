/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingPartition

/-!
# Retained-left reconstruction for gluing operators

## Main results

An integral lower bound at a terminal-piece cut admits a finite original-orbit
extension with that lower bound on its whole discarded suffix. The extension may
bend at a later integral level; it is not asserted to be a pure original-source power.
`GluingPair.exists_f_gluing_before_cut` resolves both retained-left sectors
`p < q < s` and `p < q = s`, with constructed cut chains and original Weyl orbits.
`GluingPair.exists_f_gluing` and `GluingPair.exists_e_gluing` prove unconditional
single-step strict output stability; `f_isIntegral` and `e_isIntegral` derive
all-simple-root minimum integrality. No mixed-word or decomposition claim is made.

## References

Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142 (1995),
Definition 5.3, Remark 5.4 and Proposition 5.6, pp.514–516. Primary scans consulted;
the safe terminal extension below is a reconstructed argument.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

namespace Presentation

/-- The last affine piece, based at any of its points. -/
theorem terminal_piece_from (σ : Presentation P hA) {c t : ℝ}
    (hc : c ∈ Icc (σ.a (Fin.last σ.n).castSucc : ℝ) 1)
    (ht : t ∈ Icc (σ.a (Fin.last σ.n).castSucc : ℝ) 1) :
    σ.path t = σ.path c + (t - c) • (σ.x (Fin.last σ.n) : Dual ℝ H) := by
  have hc' : c ∈ Icc (σ.a (Fin.last σ.n).castSucc : ℝ)
      (σ.a (Fin.last σ.n).succ : ℝ) := by simpa [σ.one] using hc
  have ht' : t ∈ Icc (σ.a (Fin.last σ.n).castSucc : ℝ)
      (σ.a (Fin.last σ.n).succ : ℝ) := by simpa [σ.one] using ht
  rw [σ.piece _ t ht', σ.piece _ c hc']
  module

/-- An integral level below the cut height can be made a bound on the entire
source suffix without changing the retained prefix. A falling discarded piece is
bent by its actual simple saturated chain at the level, not normalized by fiat. -/
theorem exists_safe_terminal_extension (σ : Presentation P hA) {i : ι} {c : ℚ}
    (hc : σ.a (Fin.last σ.n).castSucc < c) (hc1 : c < 1) (z : ℤ)
    (hz : (z : ℝ) ≤ σ.path.pairing i c) :
    ∃ ψ : Presentation P hA,
      (∀ t : ℝ, t ≤ (c : ℝ) → ψ.path t = σ.path t) ∧
      (∀ t ∈ Icc (c : ℝ) 1, (z : ℝ) ≤ ψ.path.pairing i t) ∧
      ∀ j, ∃ w : P.weylGroup hA, (ψ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  have hcR : (σ.a (Fin.last σ.n).castSucc : ℝ) < c := by exact_mod_cast hc
  have hc1R : (c : ℝ) < 1 := by exact_mod_cast hc1
  have hpiece (t : ℝ) (ht : t ∈ Icc (c : ℝ) 1) :
      σ.path.pairing i t = σ.path.pairing i c +
        (t - c) * (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) := by
    simp only [pairing, pathSpace_coroot,
      σ.terminal_piece_from ⟨hcR.le, hc1R.le⟩ ⟨hcR.le.trans ht.1, ht.2⟩,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  by_cases hend : (z : ℝ) ≤ σ.path.pairing i 1
  · refine ⟨σ, fun _ _ ↦ rfl, ?_, σ.orbit⟩
    intro t ht
    rw [hpiece t ht]
    by_cases hx : 0 ≤ (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i)
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.1) hx]
    · rw [hpiece 1 ⟨hc1R.le, le_rfl⟩] at hend
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) (le_of_not_ge hx)]
  · have hend' : σ.path.pairing i 1 < (z : ℝ) := lt_of_not_ge hend
    have hx : (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) < 0 := by
      rw [hpiece 1 ⟨hc1R.le, le_rfl⟩] at hend'
      by_contra hn
      have hh := mul_nonneg (sub_nonneg.mpr hc1R.le) (le_of_not_gt hn)
      linarith
    obtain ⟨r, hr, hlevel⟩ := intermediate_value_Icc' hc1R.le
      (σ.path.continuous_pairing i).continuousOn ⟨hend'.le, hz⟩
    have hr1 : r < 1 := by
      rcases lt_or_eq_of_le hr.2 with h | h
      · exact h
      · subst r
        linarith
    obtain ⟨b, hb⟩ := σ.rational_time (Fin.last σ.n)
      ⟨hcR.le.trans hr.1, by simpa [σ.one] using hr.2⟩ ⟨z, hlevel⟩ hx.ne
    have hcb : c ≤ b := by exact_mod_cast (show (c : ℝ) ≤ b by rw [hb]; exact hr.1)
    have hblast : σ.a (Fin.last σ.n).castSucc < b := hc.trans_le hcb
    have hb1 : b < 1 := by exact_mod_cast (show (b : ℝ) < 1 by rw [hb]; exact hr1)
    have hbmem : (b : ℝ) ∈ Icc (σ.a (Fin.last σ.n).castSucc : ℝ)
        (σ.a (Fin.last σ.n).succ : ℝ) := by
      rw [hb]
      exact ⟨hcR.le.trans hr.1, by simpa [σ.one] using hr.2⟩
    have hint : ∃ k : ℤ,
        ((b : ℝ) • (σ.x (Fin.last σ.n) : Dual ℝ H)) (P.coroot i) = k := by
      obtain ⟨k, hk⟩ := LSAChainBridge.rootLattice_le_integralWeights
        (σ.congruence (Fin.last σ.n) b hbmem) i
      refine ⟨z - k, ?_⟩
      change (σ.path b) (P.coroot i) -
        ((b : ℝ) • (σ.x (Fin.last σ.n) : Dual ℝ H)) (P.coroot i) = k at hk
      change (σ.path r) (P.coroot i) = (z : ℝ) at hlevel
      rw [hb] at hk ⊢
      push_cast
      linarith
    let y := (P.cartanDatum hA).reflection i (σ.x (Fin.last σ.n))
    have hy : (y : Dual ℝ H) = P.reflection hA i (σ.x (Fin.last σ.n)) :=
      coe_reflection_cartanDatum P hA i _
    have hchain : AChain P hA (b : ℝ) (σ.x (Fin.last σ.n)) y := by
      rw [hy]
      obtain ⟨k, hk⟩ := hint
      exact Relation.ReflTransGen.single
        ⟨Dual.eval ℝ H (P.coroot i), saturatedStep_simple
          (σ.x (Fin.last σ.n)).property hx, k, by simpa using hk⟩
    let ψ := σ.extendCut b y hblast hb1 hchain
    have hzero : ψ.x 0 = σ.x 0 := by
      change (Fin.snoc (α := fun _ ↦ P.integralWeights) σ.x y)
        ((0 : Fin (σ.n + 1)).castSucc) = σ.x 0
      rw [Fin.snoc_castSucc]
    refine ⟨ψ, ?_, ?_, ?_⟩
    · intro t ht
      exact σ.extendCut_path_of_le hblast hb1 hchain
        (ht.trans (by exact_mod_cast hcb))
    · intro t ht
      rcases le_total t b with htb | hbt
      · rw [pairing, σ.extendCut_path_of_le hblast hb1 hchain htb]
        change (z : ℝ) ≤ σ.path.pairing i t
        have heq : σ.path.pairing i b = z := by rw [hb]; exact hlevel
        rw [hpiece b ⟨by exact_mod_cast hcb, hbmem.2.trans_eq (by simp [σ.one])⟩]
          at heq
        rw [hpiece t ht]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr htb) hx.le]
      · change (z : ℝ) ≤ (ψ.path t) (P.coroot i)
        rw [σ.extendCut_path_of_mem hblast hb1 hchain ⟨hbt, ht.2⟩,
          LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hy,
          reflection_apply_coroot_self]
        have heq : (σ.path b) (P.coroot i) = (z : ℝ) := by
          rw [hb]; exact hlevel
        rw [heq]
        nlinarith [mul_nonneg (sub_nonneg.mpr hbt) (neg_nonneg.mpr hx.le)]
    · intro j
      simpa only [hzero] using ψ.orbit j

end Presentation

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- The retained-left sector has an actual finite lowering of a reconstructed
source, in the original orbit. The source is chosen with a safe discarded suffix;
no unsupported identification with a power of the original source is made. -/
theorem exists_f_source_before_cut {i : ι} {q : ℝ}
    (hq0 : 0 ≤ q) (hqs : q ≤ (g.s : ℝ))
    (hqm : g.path.pairing i q = g.path.minPairing i + 1)
    (hfuture : ∀ t ∈ Icc q 1, g.path.minPairing i + 1 ≤ g.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    ∃ ψ υ : Presentation P hA,
      (∀ t : ℝ, t ≤ (g.s : ℝ) → ψ.path t = σ.path t) ∧
      (∀ t ∈ Icc (g.s : ℝ) 1, g.path.minPairing i + 1 ≤ ψ.path.pairing i t) ∧
      ψ.path.minPairing i = g.path.minPairing i ∧
      LittelmannPath.f i ψ.path = some υ.path ∧
      (∀ t : ℝ, t ≤ (g.s : ℝ) → υ.path t = η t) ∧
      (∀ j, ∃ w : P.weylGroup hA, (ψ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
      ∀ j, ∃ w : P.weylGroup hA, (υ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  have hs0 : (0 : ℝ) ≤ g.s := by exact_mod_cast g.pos.le
  have hs1 : (g.s : ℝ) ≤ 1 := by exact_mod_cast g.le.trans g.lt_one.le
  have hq1 : q ≤ 1 := hqs.trans hs1
  obtain ⟨z, hz⟩ := g.isIntegral i
  have hzcut : ((z + 1 : ℤ) : ℝ) ≤ σ.path.pairing i g.s := by
    have hh := hfuture g.s ⟨hqs, hs1⟩
    simpa only [hz, Int.cast_add, Int.cast_one, pairing, pathSpace_coroot,
      g.path_left le_rfl] using hh
  obtain ⟨ψ, hψ, hbound, hoψ⟩ := σ.exists_safe_terminal_extension g.last_lt
    (g.le.trans_lt g.lt_one) (z + 1) hzcut
  have hψg (t : ℝ) (ht : t ≤ (g.s : ℝ)) : ψ.path t = g.path t := by
    rw [hψ t ht, g.path_left ht]
  have hb (t : ℝ) (ht : t ∈ Icc (g.s : ℝ) 1) :
      g.path.minPairing i + 1 ≤ ψ.path.pairing i t := by
    simpa only [hz, Int.cast_add, Int.cast_one] using hbound t ht
  have hbq (t : ℝ) (ht : t ∈ Icc q 1) :
      g.path.minPairing i + 1 ≤ ψ.path.pairing i t := by
    rcases le_total t g.s with ht' | ht'
    · simpa only [pairing, hψg t ht'] using hfuture t ht
    · exact hb t ⟨ht', ht.2⟩
  have hr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) q) :
      ψ.path.rightMin i t = g.path.rightMin i t := by
    apply rightMin_eq_of_common_prefix ⟨hq0, hq1⟩
      (fun v hv ↦ by simp only [pairing, hψg v (hv.2.trans hqs)])
      ?_ ?_ ht
    · intro v hv
      simpa only [pairing, hψg q hqs, ← hqm] using hbq v hv
    · simpa only [hqm] using hfuture
  have hm : ψ.path.minPairing i = g.path.minPairing i := by
    simpa only [rightMin_zero] using hr 0 ⟨le_rfl, hq0⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ, LittelmannPath.f i ψ.path = some ζ := by
    apply Option.ne_none_iff_exists'.mp
    intro hn
    have hh := f_eq_none_iff.mp hn
    have hh' := hb 1 ⟨hs1, le_rfl⟩
    rw [hm] at hh
    linarith
  obtain ⟨υ, hυ, -, hoυ⟩ := ψ.exists_f_presentation hζ
  have hout (t : ℝ) (ht : t ≤ (g.s : ℝ)) : υ.path t = η t := by
    rw [hυ]
    by_cases ht0 : 0 ≤ t
    · have ht1 := ht.trans hs1
      rw [f_apply hζ ⟨ht0, ht1⟩, f_apply hf ⟨ht0, ht1⟩, hm, hψg t ht]
      rcases le_total t q with htq | hqt
      · rw [hr t ⟨ht0, htq⟩]
      · have hψr : g.path.minPairing i + 1 ≤ ψ.path.rightMin i t :=
          ψ.path.le_rightMin ht1 (fun v hv ↦ hbq v ⟨hqt.trans hv.1, hv.2⟩)
        have hgr : g.path.minPairing i + 1 ≤ g.path.rightMin i t :=
          g.path.le_rightMin ht1 (fun v hv ↦ hfuture v ⟨hqt.trans hv.1, hv.2⟩)
        rw [min_eq_right hψr, min_eq_right hgr]
    · rw [ζ.apply_of_nonpos (le_of_not_ge ht0), η.apply_of_nonpos (le_of_not_ge ht0)]
  refine ⟨ψ, υ, hψ, hb, hm, by simpa only [hυ] using hζ, hout, hoψ, ?_⟩
  intro j
  obtain ⟨w, hw⟩ := hoυ j
  obtain ⟨v, hv⟩ := hoψ 0
  exact ⟨w * v, by rw [hw, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩

/-- Strict retained-left lowering, including the exact upper-time equality `q = s`.
The actual safe-source lowering and its strict coarsening are separate witnesses.
The right source, both auxiliaries and both cuts remain unchanged. -/
theorem exists_f_gluing_before_cut {i : ι} {p q : ℝ}
    (hp0 : 0 ≤ p) (hpq : p < q) (hqs : q ≤ (g.s : ℝ))
    (hpm : g.path.pairing i p = g.path.minPairing i)
    (hqm : g.path.pairing i q = g.path.minPairing i + 1)
    (hmono : StrictMonoOn (g.path.pairing i) (Icc p q))
    (hfuture : ∀ t ∈ Icc q 1, g.path.minPairing i + 1 ≤ g.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    ∃ (ψ υ τ : Presentation P hA) (g' : GluingPair τ δ),
      (∀ t : ℝ, t ≤ (g.s : ℝ) → ψ.path t = σ.path t) ∧
      ψ.path.minPairing i = g.path.minPairing i ∧
      LittelmannPath.f i ψ.path = some υ.path ∧
      (∀ t : ℝ, t ≤ (g.s : ℝ) → τ.path t = υ.path t) ∧
      (q < (g.s : ℝ) → τ.x (Fin.last τ.n) = σ.x (Fin.last σ.n)) ∧
      (q = (g.s : ℝ) → (τ.x (Fin.last τ.n) : Dual ℝ H) =
        P.reflection hA i (σ.x (Fin.last σ.n))) ∧
      g'.path = η ∧ g'.s = g.s ∧ g'.s' = g.s' ∧ g'.ν = g.ν ∧ g'.μ = g.μ ∧
      (∀ j, ∃ w : P.weylGroup hA, (ψ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
      (∀ j, ∃ w : P.weylGroup hA, (υ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  have hs0 : (0 : ℝ) ≤ g.s := by exact_mod_cast g.pos.le
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  have hs'1 : (g.s' : ℝ) ≤ 1 := by exact_mod_cast g.lt_one.le
  have hs1 := hss.trans hs'1
  have hs1Q := g.le.trans g.lt_one.le
  have hq0 := hp0.trans hpq.le
  have hq1 := hqs.trans hs1
  obtain ⟨ψ, υ, hψ, hb, hm, hυ, hυη, hoψ, hoυ⟩ :=
    g.exists_f_source_before_cut hq0 hqs hqm hfuture hf
  obtain ⟨τ, hcut, hτ, hoτ⟩ := υ.exists_coarsen_final g.pos
  have hτη (t : ℝ) (ht : t ≤ (g.s : ℝ)) : τ.path t = η t := by
    rw [hτ t ht, hυη t ht]
  have hsuffix (t : ℝ) (ht : t ∈ Icc q 1) : η t = g.path t - P.root i := by
    have hr : g.path.minPairing i + 1 ≤ g.path.rightMin i t :=
      g.path.le_rightMin ht.2 (fun v hv ↦ hfuture v ⟨ht.1.trans hv.1, hv.2⟩)
    rw [f_apply hf ⟨hq0.trans ht.1, ht.2⟩, min_eq_right hr]
    simp only [add_sub_cancel_left, one_smul]
    rfl
  have hdirlt (h : q < (g.s : ℝ)) : τ.x (Fin.last τ.n) = σ.x (Fin.last σ.n) := by
    have htrans : τ.path.HasLeftDir g.s (σ.x (Fin.last σ.n)) :=
      (σ.hasLeftDir_last g.last_lt hs1Q).of_eq (sub_pos.mpr h)
        (LinearMap.id : Dual ℝ H →ₗ[ℝ] Dual ℝ H) (-P.root i)
        (fun t ht ↦ by
          rw [hτη t ht.2, hsuffix t ⟨by linarith [ht.1], ht.2.trans hs1⟩,
            g.path_left ht.2]
          rfl) rfl
    exact (τ.hasLeftDir_last hcut hs1Q).unique htrans
  have hdireq (h : q = (g.s : ℝ)) : (τ.x (Fin.last τ.n) : Dual ℝ H) =
      P.reflection hA i (σ.x (Fin.last σ.n)) := by
    subst q
    have hψp : ψ.path.pairing i p = ψ.path.minPairing i := by
      simpa only [hm, pairing, hψ p hpq.le, g.path_left hpq.le] using hpm
    have hψs : ψ.path.pairing i g.s = ψ.path.minPairing i + 1 := by
      simpa only [hm, pairing, hψ g.s le_rfl, g.path_left le_rfl] using hqm
    have hψmono : StrictMonoOn (ψ.path.pairing i) (Icc p (g.s : ℝ)) := by
      intro u hu v hv huv
      simpa only [pairing, hψ u hu.2, hψ v hv.2, g.path_left hu.2,
        g.path_left hv.2] using hmono hu hv huv
    obtain ⟨-, hmiddle, -⟩ := ψ.f_regions hυ hp0 hpq hs1 hψp hψs hψmono
      (by simpa only [hm] using hb)
    let x' := (P.cartanDatum hA).reflection i (σ.x (Fin.last σ.n))
    have hx' : (x' : Dual ℝ H) = P.reflection hA i (σ.x (Fin.last σ.n)) :=
      coe_reflection_cartanDatum P hA i _
    have htrans : τ.path.HasLeftDir g.s x' :=
      (σ.hasLeftDir_last g.last_lt hs1Q).of_eq (sub_pos.mpr hpq)
        (P.reflection hA i).toLinearMap (g.path.minPairing i • P.root i)
        (fun t ht ↦ by
          rw [hτ t ht.2, hmiddle t ⟨by linarith [ht.1], ht.2⟩,
            hψ t ht.2, hm]
          rfl) hx'.symm
    exact (congrArg (fun x : P.integralWeights ↦ (x : Dual ℝ H))
      ((τ.hasLeftDir_last hcut hs1Q).unique htrans)).trans hx'
  have hchain : AChain P hA (g.s : ℝ) (τ.x (Fin.last τ.n)) g.ν := by
    rcases lt_or_eq_of_le hqs with h | h
    · rw [hdirlt h]
      exact g.left_chain
    · rw [hdireq h]
      have hx : 0 < (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) := by
        apply coroot_cartanDatum_pos_iff.mp
        apply g.left_direction.coroot_pos (sub_pos.mpr (hpq.trans_eq h))
        intro t ht
        have ht' : t ∈ Icc p q := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        simpa only [h] using hmono ht' ⟨hpq.le, le_rfl⟩ (by linarith [ht.2])
      have hint : ∃ k : ℤ,
          ((g.s : ℝ) • (σ.x (Fin.last σ.n) : Dual ℝ H)) (P.coroot i) = k := by
        obtain ⟨z, hz⟩ := g.isIntegral i
        obtain ⟨k, hk⟩ := LSAChainBridge.rootLattice_le_integralWeights
          (σ.congruence (Fin.last σ.n) g.s g.left_cut_mem) i
        have heq : (σ.path g.s) (P.coroot i) = (z : ℝ) + 1 := by
          simpa only [h, hz, pairing, pathSpace_coroot, g.path_left le_rfl] using hqm
        refine ⟨z + 1 - k, ?_⟩
        simp only [LinearMap.sub_apply] at hk
        push_cast
        linarith
      obtain ⟨k, hk⟩ := hint
      have hstep : AChain P hA (g.s : ℝ)
          (P.reflection hA i (σ.x (Fin.last σ.n))) (σ.x (Fin.last σ.n)) := by
        have hrint : P.reflection hA i (σ.x (Fin.last σ.n)) ∈ P.integralWeights := by
          rw [← coe_reflection_cartanDatum P hA i]
          exact ((P.cartanDatum hA).reflection i (σ.x (Fin.last σ.n))).property
        have hs := saturatedStep_simple (hA := hA) hrint
          (show (P.reflection hA i (σ.x (Fin.last σ.n))) (P.coroot i) < 0 by
            rw [reflection_apply_coroot_self]; linarith)
        rw [reflection_reflection] at hs
        exact Relation.ReflTransGen.single ⟨Dual.eval ℝ H (P.coroot i), hs, -k, by
          simp only [LinearMap.smul_apply, smul_eq_mul] at hk
          simpa only [Dual.eval_apply, reflection_apply_coroot_self, mul_neg,
            Int.cast_neg] using congrArg Neg.neg hk⟩
      exact hstep.trans g.left_chain
  have hout (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : glueRaw τ δ g.s g.s' t = η t := by
    rcases le_total t g.s with hts | hst
    · simp only [glueRaw, min_eq_left hts, max_eq_right (hts.trans hss),
        add_sub_cancel_right, hτη t hts]
    · rw [hsuffix t ⟨hqs.trans hst, ht.2⟩]
      have hs : τ.path g.s = σ.path g.s - P.root i := by
        rw [hτη g.s le_rfl, hsuffix g.s ⟨hqs, hs1⟩, g.path_left le_rfl]
      change glueRaw τ δ g.s g.s' t = glueRaw σ δ g.s g.s' t - P.root i
      simp only [glueRaw, min_eq_right hst, hs]
      abel
  let g' : GluingPair τ δ :=
    { s := g.s
      s' := g.s'
      pos := g.pos
      le := g.le
      lt_one := g.lt_one
      last_lt := hcut
      first_gt := g.first_gt
      ν := g.ν
      μ := g.μ
      left_chain := hchain
      right_chain := g.right_chain
      precedes := g.precedes
      endpoint := by rw [hout 1 ⟨zero_le_one, le_rfl⟩, η.apply_one]; exact η.wt.property }
  refine ⟨ψ, υ, τ, g', hψ, hm, hυ, hτ, hdirlt, hdireq, ?_,
    rfl, rfl, rfl, rfl, hoψ, hoυ, ?_⟩
  · apply LittelmannPath.ext_of_eqOn
    exact hout
  · intro j
    obtain ⟨w, hw⟩ := hoτ j
    obtain ⟨v, hv⟩ := hoυ 0
    exact ⟨w * v, by rw [hw, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩

/-- Unconditional single-step strict gluing stability for lowering. All directions
remain in the original source orbits; the auxiliary pair is unchanged or simultaneously
reflected. This closes the residual retained-left branches of the input-only partition. -/
theorem exists_f_gluing {i : ι} {η : LittelmannPath (P.pathSpace hA)}
    (hf : LittelmannPath.f i g.path = some η) :
    ∃ (τ ρ : Presentation P hA) (g' : GluingPair τ ρ),
      g'.path = η ∧ g'.s = g.s ∧ g'.s' = g.s' ∧
      ((g'.ν = g.ν ∧ g'.μ = g.μ) ∨
        (g'.ν = P.reflection hA i g.ν ∧ g'.μ = P.reflection hA i g.μ)) ∧
      (∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
      (∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (δ.x 0)) ∧
      η.IsIntegral := by
  rcases g.exists_f_gluing_or_before_cut hf with hout | hgap
  · exact hout
  · obtain ⟨p, q, hp0, hpq, hqs, hpm, -, hqm, hmono, hfuture, -⟩ := hgap
    obtain ⟨ψ, υ, τ, g', -, -, -, -, -, -, hp, hs, hs', hν, hμ, -, -, hoτ⟩ :=
      g.exists_f_gluing_before_cut hp0 hpq hqs hpm hqm hmono hfuture hf
    exact ⟨τ, δ, g', hp, hs, hs', Or.inl ⟨hν, hμ⟩,
      hoτ, δ.orbit, hp ▸ g'.isIntegral⟩

/-- Unconditional single-step strict gluing stability for raising. Literal reversal
transports the constructed lowering output, including both original Weyl orbits and
strict complementary cuts. No first-minimum output or integrality premise is assumed. -/
theorem exists_e_gluing {i : ι} {η : LittelmannPath (P.pathSpace hA)}
    (he : LittelmannPath.e i g.path = some η) :
    ∃ (τ ρ : Presentation P hA) (g' : GluingPair τ ρ),
      g'.path = η ∧ g'.s = g.s ∧ g'.s' = g.s' ∧
      ((g'.ν = g.ν ∧ g'.μ = g.μ) ∨
        (g'.ν = P.reflection hA i g.ν ∧ g'.μ = P.reflection hA i g.μ)) ∧
      (∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
      (∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (δ.x 0)) ∧
      η.IsIntegral := by
  have hf : LittelmannPath.f i g.reverse.path = some η.rev := by
    rw [g.reverse_path, f_rev, he, Option.map_some]
  obtain ⟨ρ, τ, g', hp, hs, hs', haux, hoρ, hoτ, -⟩ := g.reverse.exists_f_gluing hf
  have hp' : g'.reverse.path = η := by rw [g'.reverse_path, hp, rev_rev]
  refine ⟨τ.reverse, ρ.reverse, g'.reverse, hp', ?_, ?_, ?_,
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

/-- All-simple-root global-minimum integrality of every successful lowering output. -/
theorem f_isIntegral {i : ι} {η : LittelmannPath (P.pathSpace hA)}
    (hf : LittelmannPath.f i g.path = some η) : η.IsIntegral := by
  obtain ⟨τ, ρ, g', -, -, -, -, -, -, hi⟩ := g.exists_f_gluing hf
  exact hi

/-- All-simple-root global-minimum integrality of every successful raising output. -/
theorem e_isIntegral {i : ι} {η : LittelmannPath (P.pathSpace hA)}
    (he : LittelmannPath.e i g.path = some η) : η.IsIntegral := by
  obtain ⟨τ, ρ, g', -, -, -, -, -, -, hi⟩ := g.exists_e_gluing he
  exact hi

end GluingPair
end Matrix.Realization.LSGeneralClass
