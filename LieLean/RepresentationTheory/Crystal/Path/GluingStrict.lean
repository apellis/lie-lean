/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingNormalization

/-!
# Strict reconstruction after discarded-prefix normalization

## Main results

Finite source coarsening discards pieces before a cut and extends the first retained
source direction back to zero. Source chains after the cut are retained, not assumed.
`GluingPair.exists_f_gluing_strict_after` consumes the published unmatched normalization
and constructs a strict output gluing pair for every actual late-minimum lowering.
The left source, both cuts and both auxiliary directions remain unchanged. The actual
right source string and its coarsened representative are related by exact tail increments.
`GluingPair.f_isIntegral_strict_after` derives output integrality for every simple root.

This does not assert general equality/crossing-seam stability or mixed-word closure.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), Definition 5.3, Remark 5.4 and Proposition 5.6, pp. 514–516. The proof below
is reconstructed; the altered representative need not equal the original source string.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

namespace Presentation

/-- Discarding a finite source prefix gives a genuine source with a strict first-cut
bound and identical retained increments. Its directions remain in the original orbit.
The discarded prefix is replaced, not asserted to be a redundant subdivision. -/
theorem exists_coarsen_initial (σ : Presentation P hA) {c : ℚ}
    (hc1 : c < 1) :
    ∃ τ : Presentation P hA, c < τ.a (0 : Fin (τ.n + 1)).succ ∧
      (∀ t : ℝ, (c : ℝ) ≤ t → τ.path t - τ.path c = σ.path t - σ.path c) ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  suffices ∀ n (σ : Presentation P hA), σ.n = n →
      ∃ τ : Presentation P hA, c < τ.a (0 : Fin (τ.n + 1)).succ ∧
        (∀ t : ℝ, (c : ℝ) ≤ t → τ.path t - τ.path c = σ.path t - σ.path c) ∧
        ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) by
    exact this σ.n σ rfl
  intro n
  induction n with
  | zero =>
    intro σ hn
    have hb : σ.a (0 : Fin (σ.n + 1)).succ = 1 := by
      convert σ.one using 1
      congr 1
      apply Fin.ext
      simp [hn]
    exact ⟨σ, by rw [hb]; exact hc1, fun _ _ ↦ rfl, σ.orbit⟩
  | succ n ih =>
    intro σ hn
    by_cases hfirst : c < σ.a (0 : Fin (σ.n + 1)).succ
    · exact ⟨σ, hfirst, fun _ _ ↦ rfl, σ.orbit⟩
    cases σ with
    | mk m a x ha ha0 ha1 hchains =>
      dsimp at hn
      subst m
      let b : Fin (n + 2) → ℚ := Fin.cons 0 (fun j ↦ a j.succ.succ)
      let y : Fin (n + 1) → P.integralWeights := fun j ↦ x j.succ
      have hb : StrictMono b := by
        rw [Fin.strictMono_iff_lt_succ]
        intro j
        refine Fin.cases ?_ (fun k ↦ ?_) j
        · change 0 < a (0 : Fin (n + 1)).succ.succ
          rw [← ha0]
          exact ha (by change (0 : ℕ) < 2; omega)
        · simpa [b] using ha k.succ.succ.castSucc_lt_succ
      have hb0 : b 0 = 0 := rfl
      have hb1 : b (Fin.last (n + 1)) = 1 := by
        simpa [b] using ha1
      have hy : ∀ j : Fin n, AChain P hA (b j.succ.castSucc : ℝ)
          (y j.castSucc) (y j.succ) := by
        intro j
        simpa [b, y] using hchains j.succ
      let ρ : Presentation P hA := ⟨n, b, y, hb, hb0, hb1, hy⟩
      let σ : Presentation P hA := ⟨n + 1, a, x, ha, ha0, ha1, hchains⟩
      have hac : (a (0 : Fin (n + 2)).succ : ℝ) ≤ c := by
        exact_mod_cast le_of_not_gt hfirst
      have ha01 : (0 : ℝ) ≤ a (0 : Fin (n + 2)).succ := by
        exact_mod_cast (show 0 ≤ a (0 : Fin (n + 2)).succ by
          rw [← ha0]; exact (ha Fin.zero_lt_one).le)
      have htail (t : ℝ) (ht : (c : ℝ) ≤ t) :
          ρ.path t = σ.path t + (a (0 : Fin (n + 2)).succ : ℝ) •
            ((x (0 : Fin (n + 1)).succ : Dual ℝ H) - (x 0 : Dual ℝ H)) := by
        change raw (P.pathSpace hA) b y t = raw (P.pathSpace hA) a x t + _
        unfold raw
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
        have ham : (a (0 : Fin (n + 2)).succ : ℝ) ≤
            min t (a (0 : Fin (n + 1)).succ.succ : ℝ) :=
          le_min (hac.trans ht) (by exact_mod_cast (ha (by change (1 : ℕ) < 2; omega)).le)
        simp only [b, y, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
          Fin.castSucc_succ, ha0, Rat.cast_zero, min_eq_right (hac.trans ht),
          sub_zero, max_eq_right ha01, max_eq_right (sub_nonneg.mpr ham),
          max_eq_right (ha01.trans ham), pathSpace_embed]
        simp only [sub_smul, smul_sub]
        abel
      obtain ⟨τ, hτ, ht, ho⟩ := ih ρ rfl
      refine ⟨τ, hτ, ?_, ?_⟩
      · intro t hct
        rw [ht t hct, htail t hct, htail c le_rfl]
        abel
      · intro j
        obtain ⟨u, hu⟩ := ho j
        obtain ⟨v, hv⟩ := σ.orbit (0 : Fin (n + 1)).succ
        exact ⟨u * v, by
          change (τ.x j : Dual ℝ H) = (u * v).1 (x 0)
          rw [hu]
          change u.1 (x (0 : Fin (n + 1)).succ) = _
          rw [hv, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩

end Presentation

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- The full strict-after lowering sector, with no outgoing-slope or minimum-matching
premise. The actual right source string has exponent `k + 1`. Its coarsened representative
has the same retained increments, the original first direction, and a strict right cut.
Both cut chains and positive-root compatibility are the original input witnesses. -/
theorem exists_f_gluing_strict_after {i : ι} {u : ℝ}
    (hu : u ∈ Ioc (g.s' : ℝ) 1)
    (hum : g.path.pairing i u = g.path.minPairing i)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    ∃ (k : ℕ) (υ τ : Presentation P hA) (g' : GluingPair σ τ),
      δ.path.pairing i u = δ.path.minPairing i + k ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i (k + 1) δ.path = some υ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i (k + 1) υ.path = some δ.path ∧
      (∀ t : ℝ, (g.s' : ℝ) ≤ t →
        τ.path t - τ.path g.s' = υ.path t - υ.path g.s') ∧
      τ.x 0 = δ.x 0 ∧ g'.path = η ∧
      g'.s = g.s ∧ g'.s' = g.s' ∧ g'.ν = g.ν ∧ g'.μ = g.μ ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (δ.x 0) := by
  obtain ⟨k, υ, hk, hυ, heυ, hraw, -, hoυ⟩ :=
    g.exists_f_source_power_after hu hum hf
  obtain ⟨τ, hfirst, htail, hoτ⟩ := υ.exists_coarsen_initial g.lt_one
  have hout (t : ℝ) : glueRaw σ τ g.s g.s' t = η t := by
    rw [← hraw t]
    have hh := htail (max t (g.s' : ℝ)) (le_max_right _ _)
    unfold glueRaw
    simpa only [add_sub_assoc] using congrArg (σ.path (min t (g.s : ℝ)) + ·) hh
  have hs0 : (0 : ℝ) ≤ g.s' := g.right_cut_mem.1
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  have hτfirst : (g.s' : ℝ) < τ.a (0 : Fin (τ.n + 1)).succ := by
    exact_mod_cast hfirst
  have hδfirst : (g.s' : ℝ) < δ.a (0 : Fin (δ.n + 1)).succ := by
    exact_mod_cast g.first_gt
  let v := ((g.s' : ℝ) + min u
    (min (τ.a (0 : Fin (τ.n + 1)).succ : ℝ)
      (δ.a (0 : Fin (δ.n + 1)).succ : ℝ))) / 2
  have hv : (g.s' : ℝ) < v ∧ v ≤ u ∧
      v ≤ τ.a (0 : Fin (τ.n + 1)).succ ∧
      v ≤ δ.a (0 : Fin (δ.n + 1)).succ := by
    have hm := lt_min hu.1 (lt_min hτfirst hδfirst)
    have hm1 := min_le_left u
      (min (τ.a (0 : Fin (τ.n + 1)).succ : ℝ)
        (δ.a (0 : Fin (δ.n + 1)).succ : ℝ))
    have hm2 := (min_le_right u
      (min (τ.a (0 : Fin (τ.n + 1)).succ : ℝ)
        (δ.a (0 : Fin (δ.n + 1)).succ : ℝ))).trans (min_le_left _ _)
    have hm3 := (min_le_right u
      (min (τ.a (0 : Fin (τ.n + 1)).succ : ℝ)
        (δ.a (0 : Fin (δ.n + 1)).succ : ℝ))).trans (min_le_right _ _)
    dsimp only [v]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hv01 : v ∈ Icc (0 : ℝ) 1 := ⟨hs0.trans hv.1.le, hv.2.1.trans hu.2⟩
  have hfix : η v = g.path v := by
    have hm : g.path.rightMin i v = g.path.minPairing i := le_antisymm
      ((g.path.rightMin_le ⟨hv.2.1, hu.2⟩).trans_eq hum)
      (g.path.le_rightMin hv01.2 (fun t ht ↦
        g.path.minPairing_le ⟨hv01.1.trans ht.1, ht.2⟩))
    rw [f_apply hf hv01, hm, min_eq_left (by linarith)]
    simp
  have hx : τ.x 0 = δ.x 0 := by
    have hh := (hout v).trans hfix
    change glueRaw σ τ g.s g.s' v = glueRaw σ δ g.s g.s' v at hh
    simp only [glueRaw, min_eq_right (hss.trans hv.1.le), max_eq_left hv.1.le] at hh
    rw [τ.first_piece v ⟨hv01.1, hv.2.2.1⟩,
      τ.first_piece g.s' ⟨hs0, hτfirst.le⟩,
      δ.first_piece v ⟨hv01.1, hv.2.2.2⟩,
      δ.first_piece g.s' ⟨hs0, hδfirst.le⟩] at hh
    apply Subtype.ext
    have heq : (v - (g.s' : ℝ)) • (τ.x 0 : Dual ℝ H) =
        (v - (g.s' : ℝ)) • (δ.x 0 : Dual ℝ H) := by
      have hh' : v • (τ.x 0 : Dual ℝ H) - (g.s' : ℝ) • (τ.x 0 : Dual ℝ H) =
          v • (δ.x 0 : Dual ℝ H) - (g.s' : ℝ) • (δ.x 0 : Dual ℝ H) :=
        add_left_cancel (by simpa only [add_sub_assoc] using hh)
      calc
        _ = v • (τ.x 0 : Dual ℝ H) - (g.s' : ℝ) • (τ.x 0 : Dual ℝ H) := by module
        _ = _ := hh'
        _ = _ := by module
    exact (smul_right_inj (sub_ne_zero.mpr hv.1.ne')).mp heq
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
      right_chain := by rw [hx]; exact g.right_chain
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

/-- All simple-root global minima of an actual strict-after lowering output are
integral, now including the unmatched positive-outgoing source case. -/
theorem f_isIntegral_strict_after {i : ι} {u : ℝ}
    (hu : u ∈ Ioc (g.s' : ℝ) 1)
    (hum : g.path.pairing i u = g.path.minPairing i)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    η.IsIntegral := by
  obtain ⟨k, υ, τ, g', hk, hfυ, heυ, ht, hx, hpath, hrest⟩ :=
    g.exists_f_gluing_strict_after hu hum hf
  rw [← hpath]
  exact g'.isIntegral

end GluingPair
end Matrix.Realization.LSGeneralClass
