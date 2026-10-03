/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingOperators

/-!
# Actual gluing outputs in a strict-after root-operator region

## Main results

`Presentation.exists_f_presentation_after` constructs a finite lowering output with an
unchanged first direction and a strict first-piece cut bound. Exact refinement membership,
not a weakened cut condition, ensures that no artificial breakpoint enters the initial cut.
`GluingPair.exists_f_gluing_after` matches the actual glued and source lowering operators.
`GluingPair.exists_fIter_gluing_after` constructs strict gluing witnesses for arbitrary
successful same-root iterates, with the SAME exponent on the right source.
`GluingPair.exists_fIter_gluing_after_of_nonpos` derives all source-minimum matching from
an actual glued minimizer after the right cut and a nonpositive outgoing source slope.

These close the source-matched strict-after sector, including its entire nonpositive
outgoing-slope case. No output presentation, source success, closure, or dominance is
assumed. The left source, both cuts and both auxiliary cut directions stay unchanged.
The result is not full Proposition 5.6: equality seams, crossing, raising and general
positive-outgoing-slope normalization/coarsening remain outside this file.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142 (1995),
pp. 515–516, Proposition 5.6. Proofs are reconstructed.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

private theorem finite_interval {K : Type*} [LinearOrder K] {n : ℕ}
    (a : Fin (n + 1) → K) {t : K} (ht : t ∈ Ico (a 0) (a (Fin.last n))) :
    ∃ j : Fin n, t ∈ Ico (a j.castSucc) (a j.succ) := by
  classical
  have hex : ∃ j, t < a j := ⟨Fin.last n, ht.2⟩
  let j := Fin.find (fun j ↦ t < a j) hex
  have hj : j ≠ 0 := by
    intro heq
    have hs := Fin.find_spec hex
    change t < a j at hs
    rw [heq] at hs
    exact (not_lt_of_ge ht.1) hs
  exact ⟨j.pred hj, le_of_not_gt (Fin.find_min hex (Fin.castSucc_pred_lt hj)),
    by simpa [Fin.succ_pred] using Fin.find_spec hex⟩

private theorem rational_refinement {n : ℕ} {a : Fin (n + 2) → ℚ}
    (ha : StrictMono a) (ha0 : a 0 = 0) (ha1 : a (Fin.last (n + 1)) = 1)
    {p q : ℚ} (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ 1) :
    ∃ (m : ℕ) (b : Fin (m + 2) → ℚ), StrictMono b ∧ b 0 = 0 ∧
      b (Fin.last (m + 1)) = 1 ∧ Set.range a ⊆ Set.range b ∧
      p ∈ Set.range b ∧ q ∈ Set.range b ∧
      ∀ t ∈ Set.range b, t ∈ Set.range a ∨ t = p ∨ t = q := by
  classical
  let F := insert p (insert q (Finset.univ.image a))
  have hz : (0 : ℚ) ∈ F := by simp [F, ← ha0]
  have ho : (1 : ℚ) ∈ F := by simp [F, ← ha1]
  have hc : 2 ≤ F.card := by
    have hs : ({0, 1} : Finset ℚ) ⊆ F := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hz
      · exact ho
    have := Finset.card_le_card hs
    norm_num at this ⊢
    exact this
  obtain ⟨m, hcard⟩ : ∃ m, F.card = m + 2 := ⟨F.card - 2, by omega⟩
  let b := F.orderEmbOfFin hcard
  have hb (t : ℚ) : t ∈ Set.range b ↔ t ∈ F := by
    rw [Finset.range_orderEmbOfFin]
    rfl
  have hbound (t : ℚ) (ht : t ∈ F) : 0 ≤ t ∧ t ≤ 1 := by
    simp only [F, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at ht
    rcases ht with rfl | rfl | ⟨j, rfl⟩
    · exact ⟨hp, hpq.le.trans hq⟩
    · exact ⟨hp.trans hpq.le, hq⟩
    · constructor
      · simpa [ha0] using ha.monotone (Fin.zero_le j)
      · simpa [ha1] using ha.monotone (Fin.le_last j)
  have hb0 : b 0 = 0 := by
    obtain ⟨j, hj⟩ := (hb 0).mpr hz
    exact le_antisymm (hj ▸ b.monotone (Fin.zero_le j))
      (hbound _ ((hb _).mp ⟨0, rfl⟩)).1
  have hb1 : b (Fin.last (m + 1)) = 1 := by
    obtain ⟨j, hj⟩ := (hb 1).mpr ho
    exact le_antisymm (hbound _ ((hb _).mp ⟨_, rfl⟩)).2
      (hj ▸ b.monotone (Fin.le_last j))
  refine ⟨m, b, b.strictMono, hb0, hb1, ?_, (hb p).mpr ?_, (hb q).mpr ?_, ?_⟩
  · rintro t ⟨j, rfl⟩
    apply (hb _).mpr
    simp [F]
  · simp [F]
  · simp [F]
  · intro t ht
    have ht := (hb t).mp ht
    simpa only [F, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and,
      Set.mem_range, or_comm, or_left_comm, or_assoc] using ht

private theorem interval_refinement {n m : ℕ}
    {a : Fin (n + 2) → ℚ} {b : Fin (m + 2) → ℚ}
    (_ha : StrictMono a) (ha0 : a 0 = 0) (ha1 : a (Fin.last (n + 1)) = 1)
    (hb : StrictMono b) (hb0 : b 0 = 0) (hb1 : b (Fin.last (m + 1)) = 1)
    (hr : Set.range a ⊆ Set.range b) (j : Fin (m + 1)) :
    ∃ k : Fin (n + 1), a k.castSucc ≤ b j.castSucc ∧ b j.succ ≤ a k.succ := by
  have h0 : 0 ≤ b j.castSucc := by simpa [hb0] using hb.monotone (Fin.zero_le _)
  have h1 : b j.castSucc < 1 := by
    simpa [hb1] using hb (Fin.castSucc_lt_last _)
  obtain ⟨k, hk⟩ := finite_interval a (by simpa [ha0, ha1] using And.intro h0 h1)
  refine ⟨k, hk.1, ?_⟩
  obtain ⟨l, hl⟩ := hr ⟨k.succ, rfl⟩
  have hjl : j.castSucc < l := hb.lt_iff_lt.mp (by rw [hl]; exact hk.2)
  have hsucc : j.succ ≤ l := hjl
  simpa [hl] using hb.monotone hsucc

private theorem interval_side {m : ℕ} {b : Fin (m + 2) → ℚ}
    (hb : StrictMono b) {c : ℚ} (hc : c ∈ Set.range b) (j : Fin (m + 1)) :
    b j.succ ≤ c ∨ c ≤ b j.castSucc := by
  obtain ⟨k, rfl⟩ := hc
  by_cases hk : k ≤ j.castSucc
  · exact Or.inr (hb.monotone hk)
  · exact Or.inl (hb.monotone (show j.succ ≤ k from lt_of_not_ge hk))

namespace Presentation

variable (σ : Presentation P hA)

/-- Actual source lowering after a strict initial cut, with the unchanged first direction
and a strict output first-piece bound. No output subdivision or closure is assumed. -/
theorem exists_f_presentation_after {i : ι} {c : ℚ} (hc : 0 < c)
    (hfirst : c < σ.a (0 : Fin (σ.n + 1)).succ)
    (hlate : ∃ u ∈ Ioc (c : ℝ) 1, σ.path.pairing i u = σ.path.minPairing i)
    {η : LittelmannPath (P.pathSpace hA)}
    (hf : LittelmannPath.f i σ.path = some η) :
    ∃ τ : Presentation P hA, τ.path = η ∧ c < τ.a (0 : Fin (τ.n + 1)).succ ∧
      τ.x 0 = σ.x 0 ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  classical
  have h1 : σ.path.minPairing i + 1 ≤ σ.path.pairing i 1 := by
    have hn := (f_eq_none_iff (i := i) (π := σ.path)).not.mp (by rw [hf]; simp)
    push Not at hn
    linarith
  obtain ⟨p, q, hp0, hpq, hq1, hpm, hplt, hqm, hm, hqge⟩ :=
    σ.exists_rational_f_times i h1
  have hcp : (c : ℝ) < p := by
    obtain ⟨u, hu, hum⟩ := hlate
    by_contra hn
    exact (hplt u ⟨(le_of_not_gt hn).trans_lt hu.1, hu.2⟩).ne hum.symm
  have hcpQ : c < p := by exact_mod_cast hcp
  have hp0' : (0 : ℝ) ≤ p := by exact_mod_cast hp0
  have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
  have hq1' : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
  obtain ⟨hleft, hmiddle, hright⟩ := σ.f_regions hf hp0' hpq' hq1' hpm hqm hm hqge
  obtain ⟨m, b, hb, hb0, hb1, hr, hpr, hqr, hbmem⟩ :=
    rational_refinement σ.mono σ.zero σ.one hp0 hpq hq1
  have hpieces : ∀ j : Fin (m + 1), ∃ x : P.integralWeights,
      (∃ w : P.weylGroup hA, (x : Dual ℝ H) = w.1 (σ.x 0)) ∧
      ∀ t ∈ Icc (b j.castSucc : ℝ) (b j.succ : ℝ),
        η t = η (b j.castSucc : ℝ) + (t - (b j.castSucc : ℝ)) • (x : Dual ℝ H) := by
    intro j
    obtain ⟨k, hk0, hk1⟩ := interval_refinement σ.mono σ.zero σ.one hb hb0 hb1 hr j
    have hj0 : (0 : ℝ) ≤ b j.castSucc := by
      exact_mod_cast (show 0 ≤ b j.castSucc by simpa [hb0] using hb.monotone (Fin.zero_le _))
    have hj1 : (b j.succ : ℝ) ≤ 1 := by
      exact_mod_cast (show b j.succ ≤ 1 by simpa [hb1] using hb.monotone (Fin.le_last _))
    have hjle : (b j.castSucc : ℝ) ≤ b j.succ := by
      exact_mod_cast (hb Fin.castSucc_lt_succ).le
    have hsource : ∀ t ∈ Icc (b j.castSucc : ℝ) (b j.succ : ℝ),
        σ.path t = σ.path (b j.castSucc : ℝ) +
          (t - (b j.castSucc : ℝ)) • (σ.x k : Dual ℝ H) := by
      intro t ht
      have h0 : (σ.a k.castSucc : ℝ) ≤ b j.castSucc := by exact_mod_cast hk0
      have h1 : (b j.succ : ℝ) ≤ σ.a k.succ := by exact_mod_cast hk1
      rw [σ.piece k t ⟨h0.trans ht.1, ht.2.trans h1⟩,
        σ.piece k _ ⟨h0, hjle.trans h1⟩]
      module
    rcases interval_side hb hpr j with hbefore | hafter
    · have hbefore' : (b j.succ : ℝ) ≤ p := by exact_mod_cast hbefore
      refine ⟨σ.x k, σ.orbit k, ?_⟩
      intro t ht
      rw [hleft t ⟨hj0.trans ht.1, ht.2.trans hbefore'⟩,
        hleft _ ⟨hj0, hjle.trans hbefore'⟩, hsource t ht]
    · rcases interval_side hb hqr j with hbefore | hafterq
      · have hp : (p : ℝ) ≤ b j.castSucc := by exact_mod_cast hafter
        have hq : (b j.succ : ℝ) ≤ q := by exact_mod_cast hbefore
        let x := (P.cartanDatum hA).reflection i (σ.x k)
        have hx : ∃ w : P.weylGroup hA, (x : Dual ℝ H) = w.1 (σ.x 0) :=
          (lsData P hA (σ.x 0)).reflection_mem i (σ.x k) (σ.orbit k)
        refine ⟨x, hx, ?_⟩
        intro t ht
        rw [hmiddle t ⟨hp.trans ht.1, ht.2.trans hq⟩,
          hmiddle _ ⟨hp, hjle.trans hq⟩, hsource t ht, map_add, map_smul]
        have hemb := (P.pathSpace hA).embed_reflection i (σ.x k)
        change (x : Dual ℝ H) = (P.pathSpace hA).reflection i (σ.x k : Dual ℝ H) at hemb
        rw [← hemb]
        abel
      · have hq : (q : ℝ) ≤ b j.castSucc := by exact_mod_cast hafterq
        refine ⟨σ.x k, σ.orbit k, ?_⟩
        intro t ht
        rw [hright t ⟨hq.trans ht.1, ht.2.trans hj1⟩,
          hright _ ⟨hq, hjle.trans hj1⟩, hsource t ht]
        abel
  choose x hx hshape using hpieces
  obtain ⟨τ, hτ, -, hrange, horbit⟩ :=
    presentation_of_affine (σ.isLS.f hf) hb hb0 hb1 hx hshape
  have hτfirst : c < τ.a (0 : Fin (τ.n + 1)).succ := by
    have hpos := τ.mono (show (0 : Fin (τ.n + 1)).castSucc < (0 : Fin (τ.n + 1)).succ from
      Fin.castSucc_lt_succ)
    simp only [Fin.castSucc_zero, τ.zero] at hpos
    have hmem : τ.a (0 : Fin (τ.n + 1)).succ ∈ Set.range b := by
      rw [← hrange]
      exact ⟨_, rfl⟩
    rcases hbmem _ hmem with ⟨j, hj⟩ | hj | hj
    · have hj0 : (0 : Fin (σ.n + 2)) < j := by
        apply σ.mono.lt_iff_lt.mp
        simpa [σ.zero, hj] using hpos
      exact hfirst.trans_le (hj ▸ σ.mono.monotone hj0)
    · simpa only [hj] using hcpQ
    · simpa only [hj] using hcpQ.trans hpq
  have hx0 : τ.x 0 = σ.x 0 := by
    apply Subtype.ext
    have heq : (c : ℝ) • (τ.x 0 : Dual ℝ H) = (c : ℝ) • (σ.x 0 : Dual ℝ H) := by
      rw [← τ.first_piece c ⟨by exact_mod_cast hc.le, by exact_mod_cast hτfirst.le⟩,
        hτ, hleft c ⟨by exact_mod_cast hc.le, hcp.le⟩,
        σ.first_piece c ⟨by exact_mod_cast hc.le, by exact_mod_cast hfirst.le⟩]
    exact (smul_right_inj (show (c : ℝ) ≠ 0 by exact_mod_cast hc.ne')).mp heq
  exact ⟨τ, hτ, hτfirst, hx0, horbit⟩

/-- A source minimizer strictly after an initial cut ensures that actual lowering
fixes the entire closed initial interval. Used to propagate strict-after gluing. -/
theorem f_eqOn_initial {i : ι} {c : ℝ} (hc : c ≤ 1)
    (hlate : ∃ u ∈ Ioc c 1, σ.path.pairing i u = σ.path.minPairing i)
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i σ.path = some η) :
    ∀ t ∈ Icc (0 : ℝ) c, η t = σ.path t := by
  obtain ⟨u, hu, hum⟩ := hlate
  intro t ht
  have hr : σ.path.rightMin i t = σ.path.minPairing i := le_antisymm
    ((σ.path.rightMin_le ⟨ht.2.trans hu.1.le, hu.2⟩).trans_eq hum)
    (σ.path.le_rightMin (ht.2.trans hc) fun v hv ↦
      σ.path.minPairing_le ⟨ht.1.trans hv.1, hv.2⟩)
  rw [f_apply hf ⟨ht.1, ht.2.trans hc⟩, hr, min_eq_left (by linarith)]
  simp

end Presentation

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- A concrete strict-after case of Proposition 5.6. The source minimum occurs strictly
past the right cut, and the retained left part never lies below its translated value.
The actual lowering output is glued from the unchanged left source and one actual
lowering of the right source. The finite output, strict cuts, original classes and both
unchanged cut chains are constructed. No output closure or presentation is assumed. -/
theorem exists_f_gluing_after {i : ι} {η : LittelmannPath (P.pathSpace hA)}
    (hlate : ∃ u ∈ Ioc (g.s' : ℝ) 1, δ.path.pairing i u = δ.path.minPairing i)
    (hleft : ∀ t ∈ Icc (0 : ℝ) g.s,
      δ.path.minPairing i + (σ.path g.s - δ.path g.s') (P.coroot i) ≤
        σ.path.pairing i t)
    (hf : LittelmannPath.f i g.path = some η) :
    ∃ (τ : Presentation P hA) (g' : GluingPair σ τ),
      g'.path = η ∧ LittelmannPath.f i δ.path = some τ.path ∧
      g'.s = g.s ∧ g'.s' = g.s' ∧ g'.ν = g.ν ∧ g'.μ = g.μ ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (δ.x 0) := by
  have hs0 : (0 : ℝ) < g.s := by exact_mod_cast g.pos
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  have hs1 : (g.s' : ℝ) < 1 := by exact_mod_cast g.lt_one
  let d := (σ.path g.s - δ.path g.s') (P.coroot i)
  have hright (t : ℝ) (ht : (g.s' : ℝ) ≤ t) :
      g.path.pairing i t = δ.path.pairing i t + d := by
    change (glueRaw σ δ g.s g.s' t) (P.coroot i) = _
    rw [g.raw_right ht, LinearMap.add_apply]
    rfl
  obtain ⟨u, hu', hum⟩ := hlate
  have hsu : (g.s' : ℝ) < u := hu'.1
  have hu : u ∈ Icc (0 : ℝ) 1 := ⟨(hs0.le.trans hss).trans hsu.le, hu'.2⟩
  have hgm : g.path.minPairing i = δ.path.minPairing i + d := by
    apply le_antisymm
    · exact (g.path.minPairing_le hu).trans_eq (by rw [hright u hsu.le, hum])
    · apply g.path.le_runningMin zero_le_one
      intro t ht
      rcases le_total t g.s with hts | hst
      · change _ ≤ (glueRaw σ δ g.s g.s' t) (P.coroot i)
        rw [g.raw_left hts]
        exact hleft t ⟨ht.1, hts⟩
      · rcases le_total t g.s' with hts' | hst'
        · have hh := hleft g.s ⟨hs0.le, le_rfl⟩
          simpa only [pairing, pathSpace_coroot, g.path_pause ⟨hst, hts'⟩] using hh
        · rw [hright t hst']
          have hh := δ.path.minPairing_le (i := i) ht
          linarith
  have hδ : ∃ ζ, LittelmannPath.f i δ.path = some ζ := by
    apply Option.ne_none_iff_exists'.mp
    intro hn
    have hbad := f_eq_none_iff.mp hn
    have hgood : ¬ g.path.pairing i 1 - g.path.minPairing i < 1 := by
      intro hh
      have he := f_eq_none_iff.mpr hh
      rw [hf] at he
      contradiction
    rw [hright 1 hs1.le, hgm] at hgood
    apply hgood
    linarith
  obtain ⟨ζ, hζ⟩ := hδ
  obtain ⟨τ, hτ, hfirst, hx0, horbit⟩ := δ.exists_f_presentation_after
    (g.pos.trans_le g.le) g.first_gt ⟨u, hu', hum⟩ hζ
  have hζcut : ζ g.s' = δ.path g.s' := by
    have hr : δ.path.rightMin i g.s' = δ.path.minPairing i := le_antisymm
      ((δ.path.rightMin_le ⟨hsu.le, hu.2⟩).trans_eq hum)
      (δ.path.le_rightMin hs1.le fun t ht ↦
        δ.path.minPairing_le ⟨(hs0.le.trans hss).trans ht.1, ht.2⟩)
    rw [f_apply hζ ⟨hs0.le.trans hss, hs1.le⟩, hr,
      min_eq_left (by linarith)]
    simp
  have hraw : ∀ t ∈ Icc (0 : ℝ) 1, glueRaw σ τ g.s g.s' t = η t := by
    intro t ht
    rcases le_total t g.s' with hts | hst
    · have hr : g.path.rightMin i t = g.path.minPairing i := le_antisymm
        ((g.path.rightMin_le ⟨hts.trans hsu.le, hu.2⟩).trans_eq
          (by rw [hright u hsu.le, hum, hgm]))
        (g.path.le_rightMin ht.2 fun v hv ↦
          g.path.minPairing_le ⟨ht.1.trans hv.1, hv.2⟩)
      rw [f_apply hf ht, hr, min_eq_left (by linarith)]
      simp only [sub_self, zero_smul, sub_zero]
      change glueRaw σ τ g.s g.s' t = glueRaw σ δ g.s g.s' t
      simp [glueRaw, max_eq_right hts]
    · have hr : g.path.rightMin i t = δ.path.rightMin i t + d := by
        apply le_antisymm
        · obtain ⟨v, hv, hvm⟩ := δ.path.exists_rightMin i ht.2
          exact (g.path.rightMin_le hv).trans_eq
            (by rw [hright v (hst.trans hv.1), hvm])
        · apply g.path.le_rightMin ht.2
          intro v hv
          rw [hright v (hst.trans hv.1)]
          have hh := δ.path.rightMin_le (i := i) hv
          linarith
      have hcoeff :
          min (g.path.rightMin i t) (g.path.minPairing i + 1) - g.path.minPairing i =
          min (δ.path.rightMin i t) (δ.path.minPairing i + 1) - δ.path.minPairing i := by
        rw [hr, hgm, show δ.path.minPairing i + d + 1 =
          δ.path.minPairing i + 1 + d by ring, min_add_add_right]
        ring
      rw [f_apply hf ht, hcoeff]
      change glueRaw σ τ g.s g.s' t = glueRaw σ δ g.s g.s' t - _
      rw [glueRaw, min_eq_right (hss.trans hst), max_eq_left hst, hτ, hζcut,
        f_apply hζ ht, g.raw_right hst]
      abel
  let g' : GluingPair σ τ := {
    s := g.s
    s' := g.s'
    pos := g.pos
    le := g.le
    lt_one := g.lt_one
    last_lt := g.last_lt
    first_gt := hfirst
    ν := g.ν
    μ := g.μ
    left_chain := g.left_chain
    right_chain := by simpa only [hx0] using g.right_chain
    precedes := g.precedes
    endpoint := by
      rw [hraw 1 ⟨zero_le_one, le_rfl⟩, η.apply_one]
      exact η.wt.property }
  refine ⟨τ, g', LittelmannPath.ext_of_eqOn hraw, ?_, rfl, rfl, rfl, rfl, horbit⟩
  simpa only [hτ] using hζ

/-- In the strict-after minimum-dominated region, every successful glued lowering
iterate is obtained by the SAME exponent on the right source. The output includes an
actual strict gluing pair, its original two cuts and directions, and unchanged source
initial path. This is an invariant concrete sector of Proposition 5.6, not full stability. -/
theorem exists_fIter_gluing_after (i : ι) (n : ℕ)
    (hlate : ∃ u ∈ Ioc (g.s' : ℝ) 1, δ.path.pairing i u = δ.path.minPairing i)
    (hleft : ∀ t ∈ Icc (0 : ℝ) g.s,
      δ.path.minPairing i + (σ.path g.s - δ.path g.s') (P.coroot i) ≤
        σ.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)}
    (hf : (LittelmannPath.crystal (P.pathSpace hA)).fIter i n g.path = some η) :
    ∃ (τ : Presentation P hA) (g' : GluingPair σ τ),
      g'.path = η ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i n δ.path = some τ.path ∧
      g'.s = g.s ∧ g'.s' = g.s' ∧ g'.ν = g.ν ∧ g'.μ = g.μ ∧
      (∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (δ.x 0)) ∧
      τ.path.minPairing i = δ.path.minPairing i - n ∧
      (∃ u ∈ Ioc (g.s' : ℝ) 1, τ.path.pairing i u = τ.path.minPairing i) ∧
      ∀ t ∈ Icc (0 : ℝ) g.s', τ.path t = δ.path t := by
  induction n generalizing η with
  | zero =>
    simp only [Crystal.fIter_zero, Option.some.injEq] at hf
    subst η
    exact ⟨δ, g, rfl, rfl, rfl, rfl, rfl, rfl, δ.orbit, by simp, hlate,
      fun _ _ ↦ rfl⟩
  | succ n ih =>
    rw [Crystal.fIter_succ', Option.bind_eq_some_iff] at hf
    obtain ⟨ζ, hζ, hstep⟩ := hf
    obtain ⟨τ, gτ, hgτ, hsource, hs, hs', hν, hμ, horbit, hm, hτlate, hinit⟩ := ih hζ
    have hτlate' : ∃ u ∈ Ioc (gτ.s' : ℝ) 1,
        τ.path.pairing i u = τ.path.minPairing i := by
      simpa only [hs'] using hτlate
    have hτleft : ∀ t ∈ Icc (0 : ℝ) gτ.s,
        τ.path.minPairing i + (σ.path gτ.s - τ.path gτ.s') (P.coroot i) ≤
          σ.path.pairing i t := by
      intro t ht
      rw [hs] at ht
      rw [hs, hs', hinit g.s' ⟨by exact_mod_cast g.pos.le.trans g.le, le_rfl⟩, hm]
      have hh := hleft t ht
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hstep' : LittelmannPath.f i gτ.path = some η := by
      simpa only [hgτ, LittelmannPath.crystal_f] using hstep
    obtain ⟨υ, gυ, hgυ, hυ, hυs, hυs', hυν, hυμ, hυorbit⟩ :=
      gτ.exists_f_gluing_after hτlate' hτleft hstep'
    have hfix := τ.f_eqOn_initial (by exact_mod_cast gτ.lt_one.le) hτlate' hυ
    have hmin := minPairing_of_e_eq_some (f_eq_some_iff.mp hυ)
    refine ⟨υ, gυ, hgυ, ?_, hυs.trans hs, hυs'.trans hs',
      hυν.trans hν, hυμ.trans hμ, ?_, ?_, ?_, ?_⟩
    · rw [Crystal.fIter_succ', hsource, Option.bind_some]
      exact hυ
    · intro j
      obtain ⟨u, hu⟩ := hυorbit j
      obtain ⟨v, hv⟩ := horbit 0
      exact ⟨u * v, by rw [hu, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩
    · rw [hm] at hmin
      push_cast
      linarith
    · obtain ⟨v, hv, hvm⟩ := υ.path.exists_minPairing i
      refine ⟨v, ⟨?_, hv.2⟩, hvm⟩
      by_contra hn
      have he := hfix v ⟨hv.1, by simpa only [hs'] using le_of_not_gt hn⟩
      have hp : υ.path.pairing i v = τ.path.pairing i v := by
        simp only [pairing, he]
      have hh := τ.path.minPairing_le (i := i) hv
      rw [← hp, hvm] at hh
      linarith
    · intro t ht
      exact (hfix t (by simpa only [hs'] using ht)).trans (hinit t ht)

/-- At an actual glued minimum after the right cut, a nonpositive initial right
slope forces source-minimum matching. This removes the source-height bounds from
that whole sign case of the strict-after operator region in Proposition 5.6. -/
theorem after_min_matching {i : ι} {u : ℝ}
    (hu : u ∈ Ioc (g.s' : ℝ) 1)
    (hgu : g.path.pairing i u = g.path.minPairing i)
    (hx : (δ.x 0 : Dual ℝ H) (P.coroot i) ≤ 0) :
    δ.path.pairing i u = δ.path.minPairing i ∧
    ∀ t ∈ Icc (0 : ℝ) g.s,
      δ.path.minPairing i + (σ.path g.s - δ.path g.s') (P.coroot i) ≤
        σ.path.pairing i t := by
  have hs0 : (0 : ℝ) < g.s := by exact_mod_cast g.pos
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  have hs1 : (g.s' : ℝ) ≤ 1 := by exact_mod_cast g.lt_one.le
  let d := (σ.path g.s - δ.path g.s') (P.coroot i)
  have hr (t : ℝ) (ht : (g.s' : ℝ) ≤ t) :
      g.path.pairing i t = δ.path.pairing i t + d := by
    change (glueRaw σ δ g.s g.s' t) (P.coroot i) = _
    rw [g.raw_right ht, LinearMap.add_apply]
    rfl
  have hu0 : 0 ≤ u := (hs0.le.trans hss).trans hu.1.le
  have hcut : δ.path.pairing i u ≤ δ.path.pairing i g.s' := by
    have hh := g.path.minPairing_le (i := i) ⟨hs0.le.trans hss, hs1⟩
    rw [← hgu, hr u hu.1.le, hr g.s' le_rfl] at hh
    linarith
  have hsource : δ.path.pairing i u = δ.path.minPairing i := by
    apply le_antisymm
    · apply δ.path.le_runningMin zero_le_one
      intro t ht
      rcases le_total t g.s' with hts | hst
      · have hc : δ.path.pairing i g.s' ≤ δ.path.pairing i t := by
          have htmem : t ∈ Icc (0 : ℝ) (δ.a (0 : Fin (δ.n + 1)).succ : ℝ) :=
            ⟨ht.1, hts.trans g.right_cut_mem.2⟩
          simp only [pairing, δ.first_piece _ g.right_cut_mem,
            δ.first_piece t htmem, pathSpace_coroot, LinearMap.smul_apply, smul_eq_mul]
          exact mul_le_mul_of_nonpos_right hts hx
        exact hcut.trans hc
      · have hh := g.path.minPairing_le (i := i) ht
        rw [← hgu, hr u hu.1.le, hr t hst] at hh
        linarith
    · exact δ.path.minPairing_le ⟨hu0, hu.2⟩
  refine ⟨hsource, ?_⟩
  intro t ht
  have hh := g.path.minPairing_le (i := i) ⟨ht.1, ht.2.trans (hss.trans hs1)⟩
  rw [← hgu, hr u hu.1.le, hsource] at hh
  change _ ≤ (glueRaw σ δ g.s g.s' t) (P.coroot i) at hh
  rw [g.raw_left ht.2] at hh
  exact hh

/-- The entire nonpositive-outgoing-slope strict-after case, with actual iterated
glued outputs. The only location premise is an ACTUAL glued global minimizer after
the right cut. No source minimum, source success, or output witness is assumed. -/
theorem exists_fIter_gluing_after_of_nonpos (i : ι) (n : ℕ)
    (hlate : ∃ u ∈ Ioc (g.s' : ℝ) 1, g.path.pairing i u = g.path.minPairing i)
    (hx : (δ.x 0 : Dual ℝ H) (P.coroot i) ≤ 0)
    {η : LittelmannPath (P.pathSpace hA)}
    (hf : (LittelmannPath.crystal (P.pathSpace hA)).fIter i n g.path = some η) :
    ∃ (τ : Presentation P hA) (g' : GluingPair σ τ),
      g'.path = η ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i n δ.path = some τ.path ∧
      g'.s = g.s ∧ g'.s' = g.s' ∧ g'.ν = g.ν ∧ g'.μ = g.μ ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (δ.x 0) := by
  obtain ⟨u, hu, hum⟩ := hlate
  obtain ⟨hδ, hleft⟩ := g.after_min_matching hu hum hx
  obtain ⟨τ, g', hpath, hsource, hs, hs', hν, hμ, horbit, -⟩ :=
    g.exists_fIter_gluing_after i n ⟨u, hu, hδ⟩ hleft hf
  exact ⟨τ, g', hpath, hsource, hs, hs', hν, hμ, horbit⟩


/-- The integral-global-minimum part of Proposition 5.6 for every successful lowering
iterate in the verified nonpositive-outgoing strict-after sector. -/
theorem fIter_isIntegral_after_of_nonpos (i : ι) (n : ℕ)
    (hlate : ∃ u ∈ Ioc (g.s' : ℝ) 1, g.path.pairing i u = g.path.minPairing i)
    (hx : (δ.x 0 : Dual ℝ H) (P.coroot i) ≤ 0)
    {η : LittelmannPath (P.pathSpace hA)}
    (hf : (LittelmannPath.crystal (P.pathSpace hA)).fIter i n g.path = some η) :
    η.IsIntegral := by
  obtain ⟨τ, g', hpath, -⟩ := g.exists_fIter_gluing_after_of_nonpos i n hlate hx hf
  rw [← hpath]
  exact g'.isIntegral

end GluingPair

end Matrix.Realization.LSGeneralClass
