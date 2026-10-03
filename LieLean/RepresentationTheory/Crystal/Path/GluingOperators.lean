/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingReconstruction

/-!
# Finite source reconstruction for root operators

## Main results

Finite rational affine decompositions of actual LS paths reconstruct source presentations.
The root-operator construction below uses the existing LS stability theorem, not an
assumed output presentation. This is a prerequisite for Littelmann Proposition 5.6.

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

/-- The source chains can be recovered from the actual local LS condition and a finite
rational affine formula. The root-lattice invariant is derived by induction from zero. -/
theorem presentation_of_affine {Λ : P.integralWeights}
    {η : LittelmannPath (P.pathSpace hA)} (hη : IsLS (lsData P hA Λ) η)
    {n : ℕ} {a : Fin (n + 2) → ℚ} (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (n + 1)) = 1) {x : Fin (n + 1) → P.integralWeights}
    (hx : ∀ j, ∃ w : P.weylGroup hA, (x j : Dual ℝ H) = w.1 Λ)
    (hp : ∀ j t, t ∈ Icc (a j.castSucc : ℝ) (a j.succ : ℝ) →
      η t = η (a j.castSucc : ℝ) + (t - (a j.castSucc : ℝ)) • (x j : Dual ℝ H)) :
    ∃ τ : Presentation P hA, τ.path = η ∧
      τ.n = n ∧ Set.range τ.a = Set.range a ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 Λ := by
  have ha' : StrictMono (fun j ↦ (a j : ℝ)) := by
    intro j k hjk
    change (a j : ℝ) < (a k : ℝ)
    exact_mod_cast ha hjk
  have hc : ∀ j : Fin n, (lsData P hA Λ).Chain (η (a j.succ.castSucc : ℝ))
      (x j.castSucc) (x j.succ) := by
    apply (isLS_finitePieces_iff ha' (by simp [ha0]) (by simp [ha1]) hx
      (p := fun j ↦ η (a j.castSucc : ℝ) -
        (a j.castSucc : ℝ) • (x j : Dual ℝ H)) ?_).mp hη
    intro j t ht
    rw [hp j t ht]
    simp only [pathSpace_embed]
    module
  have hd (j : Fin (n + 1)) :
      η (a j.succ : ℝ) - (a j.succ : ℝ) • (x j : Dual ℝ H) =
        η (a j.castSucc : ℝ) - (a j.castSucc : ℝ) • (x j : Dual ℝ H) := by
    rw [hp j _ ⟨(ha' Fin.castSucc_lt_succ).le, le_rfl⟩]
    dsimp
    module
  have hq : ∀ j : Fin (n + 1),
      η (a j.castSucc : ℝ) - (a j.castSucc : ℝ) • (x j : Dual ℝ H) ∈
        LSAChainBridge.rootLattice P := by
    intro j
    induction j using Fin.induction with
    | zero => simp [ha0]
    | succ j ih =>
      have hin : η (a j.succ.castSucc : ℝ) -
          (a j.succ.castSucc : ℝ) • (x j.castSucc : Dual ℝ H) ∈
          LSAChainBridge.rootLattice P := by
        rw [Fin.castSucc_succ, hd j.castSucc]
        exact ih
      exact (((chain_iff_positionChain Λ _ _ _ (hx j.castSucc)).mp (hc j)).to_aChain hin).2
  have ht : ∀ j : Fin n, AChain P hA (a j.succ.castSucc : ℝ)
      (x j.castSucc) (x j.succ) := by
    intro j
    apply (chain_iff_aChain Λ _ _ (hx j.castSucc) ?_).mp (hc j)
    rw [Fin.castSucc_succ, hd j.castSucc]
    exact hq j.castSucc
  let τ : Presentation P hA := ⟨n, a, x, ha, ha0, ha1, ht⟩
  refine ⟨τ, ?_, rfl, rfl, hx⟩
  have heq : ∀ j : Fin (n + 2), τ.path (a j : ℝ) = η (a j : ℝ) := by
    intro j
    induction j using Fin.induction with
    | zero => simp [ha0]
    | succ j ih =>
      have hmem : (a j.succ : ℝ) ∈ Icc (a j.castSucc : ℝ) (a j.succ : ℝ) :=
        ⟨(ha' Fin.castSucc_lt_succ).le, le_rfl⟩
      have hstart := τ.piece j (a j.castSucc : ℝ)
        ⟨le_rfl, (ha' Fin.castSucc_lt_succ).le⟩
      change τ.path (a j.castSucc : ℝ) =
        finitePiecePosition (P.pathSpace hA) a x j.castSucc +
          ((a j.castSucc : ℝ) - (a j.castSucc : ℝ)) • (x j : Dual ℝ H) at hstart
      simp only [sub_self, zero_smul, add_zero] at hstart
      rw [τ.piece j _ hmem, ← hstart, ih, hp j _ hmem]
  apply LittelmannPath.ext_of_eqOn
  intro t ht'
  rcases lt_or_eq_of_le ht'.2 with hlt | rfl
  · obtain ⟨j, hj⟩ := finite_interval (fun j ↦ (a j : ℝ))
      (by simpa [ha0, ha1] using (show t ∈ Ico (0 : ℝ) 1 from ⟨ht'.1, hlt⟩))
    have hstart := τ.piece j (a j.castSucc : ℝ)
      ⟨le_rfl, (ha' Fin.castSucc_lt_succ).le⟩
    change τ.path (a j.castSucc : ℝ) =
        finitePiecePosition (P.pathSpace hA) a x j.castSucc +
          ((a j.castSucc : ℝ) - (a j.castSucc : ℝ)) • (x j : Dual ℝ H) at hstart
    simp only [sub_self, zero_smul, add_zero] at hstart
    rw [τ.piece j _ ⟨hj.1, hj.2.le⟩, ← hstart, heq, hp j _ ⟨hj.1, hj.2.le⟩]
  · simpa [ha1] using heq (Fin.last (n + 1))

private theorem finite_interval_left {n : ℕ} (a : Fin (n + 1) → ℝ) {t : ℝ}
    (ht : t ∈ Ioc (a 0) (a (Fin.last n))) :
    ∃ j : Fin n, t ∈ Ioc (a j.castSucc) (a j.succ) := by
  classical
  have hex : ∃ j, t ≤ a j := ⟨Fin.last n, ht.2⟩
  let j := Fin.find (fun j ↦ t ≤ a j) hex
  have hj : j ≠ 0 := by
    intro heq
    have hs := Fin.find_spec hex
    change t ≤ a j at hs
    rw [heq] at hs
    exact (not_le_of_gt ht.1) hs
  exact ⟨j.pred hj, lt_of_not_ge (Fin.find_min hex (Fin.castSucc_pred_lt hj)),
    by simpa [Fin.succ_pred] using Fin.find_spec hex⟩

namespace Presentation

variable (σ : Presentation P hA)

/-- An integral height on a nonhorizontal source segment occurs at a rational time. -/
theorem rational_time {i : ι} (j : Fin (σ.n + 1)) {t : ℝ}
    (ht : t ∈ Icc (σ.a j.castSucc : ℝ) (σ.a j.succ : ℝ))
    (hh : ∃ z : ℤ, σ.path.pairing i t = z)
    (hx : (σ.x j : Dual ℝ H) (P.coroot i) ≠ 0) : ∃ r : ℚ, (r : ℝ) = t := by
  obtain ⟨z, hz⟩ := hh
  obtain ⟨k, hk⟩ := LSAChainBridge.rootLattice_le_integralWeights (σ.congruence j t ht) i
  obtain ⟨d, hd⟩ := (σ.x j).property i
  have heq : σ.path.pairing i t - t * (σ.x j : Dual ℝ H) (P.coroot i) = k := by
    change σ.path t (P.coroot i) - t * (σ.x j : Dual ℝ H) (P.coroot i) = k
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] using hk
  have hd0 : (d : ℝ) ≠ 0 := by rwa [← hd]
  refine ⟨((z : ℚ) - k) / d, ?_⟩
  push_cast
  apply (div_eq_iff hd0).mpr
  rw [hz, hd] at heq
  linarith

private theorem slope_ne_zero {i : ι} (j : Fin (σ.n + 1)) {u v : ℝ}
    (hu : u ∈ Icc (σ.a j.castSucc : ℝ) (σ.a j.succ : ℝ))
    (hv : v ∈ Icc (σ.a j.castSucc : ℝ) (σ.a j.succ : ℝ))
    (hh : σ.path.pairing i u < σ.path.pairing i v) :
    (σ.x j : Dual ℝ H) (P.coroot i) ≠ 0 := by
  intro hzero
  have heq : σ.path.pairing i u = σ.path.pairing i v := by
    change σ.path u (P.coroot i) = σ.path v (P.coroot i)
    rw [σ.piece j u hu, σ.piece j v hv]
    simp [hzero]
  exact hh.ne heq

/-- Both actual lowering-operator times are rational. No output partition is supplied. -/
theorem exists_rational_f_times (i : ι)
    (h1 : σ.path.minPairing i + 1 ≤ σ.path.pairing i 1) :
    ∃ p q : ℚ, 0 ≤ p ∧ p < q ∧ q ≤ 1 ∧
      σ.path.pairing i p = σ.path.minPairing i ∧
      (∀ t ∈ Ioc (p : ℝ) 1, σ.path.minPairing i < σ.path.pairing i t) ∧
      σ.path.pairing i q = σ.path.minPairing i + 1 ∧
      StrictMonoOn (σ.path.pairing i) (Icc (p : ℝ) (q : ℝ)) ∧
      ∀ t ∈ Icc (q : ℝ) 1, σ.path.minPairing i + 1 ≤ σ.path.pairing i t := by
  obtain ⟨p, q, hp0, hpq, hq1, hpm, hplt, hqm, hm, hqge⟩ :=
    σ.isLS.exists_f_times i h1
  obtain ⟨z, hz⟩ := σ.isLS.exists_int_minPairing i
  obtain ⟨j, hj⟩ := finite_interval (fun j ↦ (σ.a j : ℝ))
    (by simpa [σ.zero, σ.one] using
      (show p ∈ Ico (0 : ℝ) 1 from ⟨hp0, hpq.trans_le hq1⟩))
  let v := (p + min q (σ.a j.succ : ℝ)) / 2
  have hv : p < v ∧ v ≤ q ∧ v < (σ.a j.succ : ℝ) := by
    dsimp [v]
    have := lt_min hpq hj.2
    have := min_le_left q (σ.a j.succ : ℝ)
    have := min_le_right q (σ.a j.succ : ℝ)
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  obtain ⟨pr, hpr⟩ := σ.rational_time j ⟨hj.1, hj.2.le⟩ ⟨z, hpm.trans hz⟩
    (σ.slope_ne_zero j ⟨hj.1, hj.2.le⟩ ⟨hj.1.trans hv.1.le, hv.2.2.le⟩
      (hm ⟨le_rfl, hpq.le⟩ ⟨hv.1.le, hv.2.1⟩ hv.1))
  obtain ⟨k, hk⟩ := finite_interval_left (fun j ↦ (σ.a j : ℝ))
    (by simpa [σ.zero, σ.one] using
      (show q ∈ Ioc (0 : ℝ) 1 from ⟨hp0.trans_lt hpq, hq1⟩))
  let u := (max p (σ.a k.castSucc : ℝ) + q) / 2
  have hu : p ≤ u ∧ (σ.a k.castSucc : ℝ) < u ∧ u < q := by
    dsimp [u]
    have := max_lt hpq hk.1
    have := le_max_left p (σ.a k.castSucc : ℝ)
    have := le_max_right p (σ.a k.castSucc : ℝ)
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  obtain ⟨qr, hqr⟩ := σ.rational_time k ⟨hk.1.le, hk.2⟩
    ⟨z + 1, by rw [hqm, hz]; push_cast; rfl⟩
    (σ.slope_ne_zero k ⟨hu.2.1.le, hu.2.2.le.trans hk.2⟩ ⟨hk.1.le, hk.2⟩
      (hm ⟨hu.1, hu.2.2.le⟩ ⟨hpq.le, le_rfl⟩ hu.2.2))
  refine ⟨pr, qr, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hpr ▸ hp0
  · exact_mod_cast (show (pr : ℝ) < (qr : ℝ) by rwa [hpr, hqr])
  · exact_mod_cast (show (qr : ℝ) ≤ 1 by rwa [hqr])
  · simpa only [hpr, hqr] using And.intro hpm ⟨hplt, hqm, hm, hqge⟩

end Presentation

private theorem rational_refinement {n : ℕ} {a : Fin (n + 2) → ℚ}
    (ha : StrictMono a) (ha0 : a 0 = 0) (ha1 : a (Fin.last (n + 1)) = 1)
    {p q : ℚ} (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ 1) :
    ∃ (m : ℕ) (b : Fin (m + 2) → ℚ), StrictMono b ∧ b 0 = 0 ∧
      b (Fin.last (m + 1)) = 1 ∧ Set.range a ⊆ Set.range b ∧
      p ∈ Set.range b ∧ q ∈ Set.range b := by
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
  refine ⟨m, b, b.strictMono, hb0, hb1, ?_, (hb p).mpr ?_, (hb q).mpr ?_⟩
  · rintro t ⟨j, rfl⟩
    apply (hb _).mpr
    simp [F]
  · simp [F]
  · simp [F]

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

/-- The closed three-region formula for a successful lowering operation, including
both equality endpoints. This will be used on the constructed finite refinement. -/
theorem f_regions {i : ι} {η : LittelmannPath (P.pathSpace hA)}
    (hf : LittelmannPath.f i σ.path = some η) {p q : ℝ}
    (hp0 : 0 ≤ p) (hpq : p < q) (hq1 : q ≤ 1)
    (hpm : σ.path.pairing i p = σ.path.minPairing i)
    (hqm : σ.path.pairing i q = σ.path.minPairing i + 1)
    (hm : StrictMonoOn (σ.path.pairing i) (Icc p q))
    (hqge : ∀ t ∈ Icc q 1, σ.path.minPairing i + 1 ≤ σ.path.pairing i t) :
    (∀ t ∈ Icc (0 : ℝ) p, η t = σ.path t) ∧
    (∀ t ∈ Icc p q, η t = (P.pathSpace hA).reflection i (σ.path t) +
      σ.path.minPairing i • (P.pathSpace hA).root i) ∧
    (∀ t ∈ Icc q 1, η t = σ.path t - (P.pathSpace hA).root i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have hr : σ.path.rightMin i t = σ.path.minPairing i := le_antisymm
      ((σ.path.rightMin_le ⟨ht.2, hpq.le.trans hq1⟩).trans hpm.le)
      (σ.path.le_rightMin (ht.2.trans (hpq.le.trans hq1)) fun u hu ↦
        σ.path.minPairing_le ⟨ht.1.trans hu.1, hu.2⟩)
    rw [f_apply hf ⟨ht.1, ht.2.trans (hpq.le.trans hq1)⟩, hr,
      min_eq_left (by linarith)]
    simp
  · intro t ht
    have htq : σ.path.pairing i t ≤ σ.path.minPairing i + 1 :=
      hqm ▸ hm.monotoneOn ht ⟨hpq.le, le_rfl⟩ ht.2
    have hr : σ.path.rightMin i t = σ.path.pairing i t := le_antisymm
      (σ.path.rightMin_le ⟨le_rfl, ht.2.trans hq1⟩)
      (σ.path.le_rightMin (ht.2.trans hq1) fun u hu ↦ by
        rcases le_total u q with huq | huq
        · exact hm.monotoneOn ht ⟨ht.1.trans hu.1, huq⟩ hu.1
        · exact htq.trans (hqge u ⟨huq, hu.2⟩))
    rw [f_apply hf ⟨hp0.trans ht.1, ht.2.trans hq1⟩, hr, min_eq_left htq,
      CartanDatum.PathSpace.reflection_apply]
    simp only [pairing]
    module
  · intro t ht
    have hr : σ.path.minPairing i + 1 ≤ σ.path.rightMin i t :=
      σ.path.le_rightMin ht.2 fun u hu ↦ hqge u ⟨ht.1.trans hu.1, hu.2⟩
    rw [f_apply hf ⟨(hp0.trans hpq.le).trans ht.1, ht.2⟩, min_eq_right hr]
    module

/-- A successful actual root operator on ANY integral source presentation has a finite
source output presentation in the same class. Strict rational breakpoints, source saturated
a-chains, and literal path equality are constructed, not assumed. All original breakpoints
are retained; the two operator times are inserted, with coincidences deduplicated.
This is the finite-output prerequisite used in Proposition 5.6, not two-class stability. -/
theorem exists_f_presentation {i : ι} {η : LittelmannPath (P.pathSpace hA)}
    (hf : LittelmannPath.f i σ.path = some η) :
    ∃ τ : Presentation P hA, τ.path = η ∧ Set.range σ.a ⊆ Set.range τ.a ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  classical
  have h1 : σ.path.minPairing i + 1 ≤ σ.path.pairing i 1 := by
    have hn := (f_eq_none_iff (i := i) (π := σ.path)).not.mp (by rw [hf]; simp)
    push Not at hn
    linarith
  obtain ⟨p, q, hp0, hpq, hq1, hpm, -, hqm, hm, hqge⟩ :=
    σ.exists_rational_f_times i h1
  have hp0' : (0 : ℝ) ≤ p := by exact_mod_cast hp0
  have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
  have hq1' : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
  obtain ⟨hleft, hmiddle, hright⟩ := σ.f_regions hf hp0' hpq' hq1' hpm hqm hm hqge
  obtain ⟨m, b, hb, hb0, hb1, hr, hpr, hqr⟩ :=
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
  exact ⟨τ, hτ, hrange.symm ▸ hr, horbit⟩

end Presentation
/-- At a nonintegral height, a source position chain with positive endpoints can be
simultaneously reflected step by step. Integrality of intermediate directions is derived. -/
theorem PositionChain.reflect_nonintegral {p x y : Dual ℝ H} {i : ι}
    (h : PositionChain P hA p x y) (hp : ¬ ∃ z : ℤ, p (P.coroot i) = z)
    (hint : x ∈ P.integralWeights) (hx : 0 < x (P.coroot i))
    (hy : 0 < y (P.coroot i)) :
    PositionChain P hA (P.reflection hA i p)
      (P.reflection hA i x) (P.reflection hA i y) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head x z hxz hzy ih =>
    obtain ⟨c, hc, k, hk⟩ := hxz
    have hz : 0 < z (P.coroot i) := by
      by_contra hn
      exact hp (PositionChain.exists_int hzy (Or.inl ⟨le_of_not_gt hn, hy⟩))
    refine Relation.ReflTransGen.head
      ⟨c ∘ₗ (P.reflection hA i).toLinearMap, hc.reflection_pos hint hx hz, k, ?_⟩
      (ih (hc.1.integral_end hint) hz)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, reflection_reflection] using hk

/-- The reflected source chain has the SAME time parameter, not a rescaled chain. -/
theorem AChain.reflect_nonintegral {a : ℝ} {x y : Dual ℝ H} {i : ι}
    (h : AChain P hA a x y) (hp : ¬ ∃ z : ℤ, (a • x) (P.coroot i) = z)
    (hint : x ∈ P.integralWeights) (hx : 0 < x (P.coroot i))
    (hy : 0 < y (P.coroot i)) :
    AChain P hA a (P.reflection hA i x) (P.reflection hA i y) := by
  have hr := (h.to_positionChain (p := a • x) (by simp)).1.reflect_nonintegral hp hint hx hy
  exact (hr.to_aChain (by simp)).1

private theorem nonintegral_of_difference {p q : Dual ℝ H} {i : ι}
    (hp : ¬ ∃ z : ℤ, p (P.coroot i) = z) (hd : p - q ∈ P.integralWeights) :
    ¬ ∃ z : ℤ, q (P.coroot i) = z := by
  rintro ⟨k, hk⟩
  obtain ⟨l, hl⟩ := hd i
  apply hp
  refine ⟨l + k, ?_⟩
  simp only [LinearMap.sub_apply] at hl
  push_cast
  linarith

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- The nonintegral crossing-seam step of Proposition 5.6, pp.515–516. A positive
outgoing source slope forces BOTH auxiliary cut directions positive, and yields BOTH
reflected time chains and simultaneous Weyl compatibility. No strict same-cut pair is
asserted for the auxiliary extensions, whose inserted breakpoints equal the cuts. -/
theorem reflect_nonintegral_seam {i : ι}
    (hp : ¬ ∃ z : ℤ, (σ.path g.s) (P.coroot i) = z)
    (hy : 0 < (δ.x 0 : Dual ℝ H) (P.coroot i)) :
    0 < (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) ∧
    0 < g.ν (P.coroot i) ∧ 0 < g.μ (P.coroot i) ∧
    AChain P hA (g.s : ℝ) (P.reflection hA i (σ.x (Fin.last σ.n)))
      (P.reflection hA i g.ν) ∧
    AChain P hA (g.s' : ℝ) (P.reflection hA i g.μ)
      (P.reflection hA i (δ.x 0)) ∧
    P.GluingPrecedes hA (P.reflection hA i g.ν) (P.reflection hA i g.μ) := by
  have hx : 0 < (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) := by
    by_contra hn
    exact hp (g.cut_height_integral_of_nonpos (le_of_not_gt hn) hy)
  have hr : PositionChain P hA (σ.path g.s) g.μ (δ.x 0) := by
    have hh := g.right_chain.at_target.add_weight
      (⟨σ.path g.s - δ.path g.s', g.offset_integral⟩ : P.integralWeights)
    simpa only [← δ.first_piece _ g.right_cut_mem, add_sub_cancel] using hh
  have hμ : 0 < g.μ (P.coroot i) := by
    by_contra hn
    exact hp (hr.exists_int (Or.inl ⟨le_of_not_gt hn, hy⟩))
  have hleft := σ.congruence (Fin.last σ.n) g.s g.left_cut_mem
  have hν : 0 < g.ν (P.coroot i) := by
    rcases lt_trichotomy (g.ν (P.coroot i)) 0 with hn | hz | hpos
    · exact False.elim ((not_le_of_gt hμ) (g.precedes.simple hn))
    · have hh := LSAChainBridge.rootLattice_le_integralWeights
        (g.left_chain.to_positionChain hleft).2 i
      exact False.elim (hp (by
        simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
          hz, mul_zero, sub_zero] using hh))
    · exact hpos
  have hlni : ¬ ∃ z : ℤ,
      ((g.s : ℝ) • (σ.x (Fin.last σ.n) : Dual ℝ H)) (P.coroot i) = z :=
    nonintegral_of_difference hp (LSAChainBridge.rootLattice_le_integralWeights hleft)
  have hright := (g.right_chain.to_positionChain
    (p := (g.s' : ℝ) • g.μ) (by simp)).2
  have hd : σ.path g.s - (g.s' : ℝ) • g.μ ∈ P.integralWeights := by
    have hh := P.integralWeights.sub_mem g.offset_integral
      (LSAChainBridge.rootLattice_le_integralWeights hright)
    convert hh using 1
    rw [δ.first_piece _ g.right_cut_mem]
    abel
  exact ⟨hx, hν, hμ,
    g.left_chain.reflect_nonintegral hlni (σ.x (Fin.last σ.n)).property hx hν,
    g.right_chain.reflect_nonintegral (nonintegral_of_difference hp hd)
      g.right_direction_integral hμ hy,
    g.precedes.reflection_of_pos_of_nonneg hν hμ.le⟩

end GluingPair
/-- Iterated lowering, as required for the source modifications in Proposition 5.6,
still has an actual finite source presentation. No orbit or presentation of intermediate
paths is assumed, and the original source subdivision is retained throughout. -/
theorem Presentation.exists_fIter_presentation (σ : Presentation P hA) (i : ι) (n : ℕ)
    {η : LittelmannPath (P.pathSpace hA)}
    (hf : (LittelmannPath.crystal (P.pathSpace hA)).fIter i n σ.path = some η) :
    ∃ τ : Presentation P hA, τ.path = η ∧ Set.range σ.a ⊆ Set.range τ.a ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  induction n generalizing η with
  | zero =>
    simp only [Crystal.fIter_zero, Option.some.injEq] at hf
    subst η
    exact ⟨σ, rfl, Set.Subset.rfl, σ.orbit⟩
  | succ n ih =>
    rw [Crystal.fIter_succ', Option.bind_eq_some_iff] at hf
    obtain ⟨ζ, hζ, hstep⟩ := hf
    obtain ⟨τ, hτ, hr, ho⟩ := ih hζ
    have hstep' : LittelmannPath.f i τ.path = some η := by
      simpa only [hτ, LittelmannPath.crystal_f] using hstep
    obtain ⟨υ, hυ, hs, hu⟩ := τ.exists_f_presentation hstep'
    refine ⟨υ, hυ, hr.trans hs, ?_⟩
    intro j
    obtain ⟨u, hu⟩ := hu j
    obtain ⟨v, hv⟩ := ho 0
    exact ⟨u * v, by rw [hu, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩

/-- A finite output object chosen from the proved root-operator construction. -/
noncomputable def Presentation.lower (σ : Presentation P hA) {i : ι}
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i σ.path = some η) :
    Presentation P hA :=
  (σ.exists_f_presentation hf).choose

/-- The chosen finite source object is literally the actual root-operator output. -/
theorem Presentation.lower_path (σ : Presentation P hA) {i : ι}
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i σ.path = some η) :
    (σ.lower hf).path = η :=
  (σ.exists_f_presentation hf).choose_spec.1

end Matrix.Realization.LSGeneralClass
