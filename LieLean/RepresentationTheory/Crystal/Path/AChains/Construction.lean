/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.AChains

/-!
# Constructing finite rational LS paths from source a-chains

## Main definitions / results

* `LittelmannPath.FiniteConstruction.raw`: the explicit clamped cumulative affine function.
* `Matrix.Realization.LSAChainBridge.raw_endpoint_integral`: endpoint integrality derived
  from source a-chains and the actual root-lattice displacement theorem.
* `Matrix.Realization.LSAChainBridge.ofAChains`: the resulting `LittelmannPath`.
* `Matrix.Realization.LSAChainBridge.isLS_ofAChains`: its global concrete LS condition.

There is no supplied path, integral-endpoint premise, or LS premise. Arbitrarily many
pieces, a single segment, and arbitrary finite rank are covered. The ambient realization
may have any generalized Cartan matrix; no symmetrizability is needed for this construction.
Allowing redundant equal directions is an explicit extension of the source's strict
presentation. The interface requires continuous coroot evaluations; additionally
`continuous_raw` proves ambient continuity for any compatible vector-space topology.
No reparametrization quotient or component/crystal isomorphism is claimed.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142 (1995),
499–525, Section 4, pp. 509–510, Remark 4.2 and the cumulative affine formula
.
The proof is reconstructed using the source-oriented chain bridge in `Path.AChains`.
-/

open Set

namespace LittelmannPath.FiniteConstruction

variable {ι X V : Type*} [AddCommGroup X] [AddCommGroup V] [Module ℝ V]
  {D : CartanDatum ι X} (S : D.PathSpace ℝ V)

/-- The finite cumulative affine function, clamped separately on each piece. -/
noncomputable def raw {n : ℕ} (a : Fin (n + 1) → ℚ) (x : Fin n → X) (t : ℝ) : V :=
  ∑ j : Fin n, (max 0 (min t (a j.succ : ℝ) - (a j.castSucc : ℝ))) • S.embed (x j)

/-- Successive cumulative positions differ by the full intervening segment.
This is a direct finite-sum identity; no monotonicity is needed. -/
theorem finitePiecePosition_succ {n : ℕ} (a : Fin (n + 1) → ℚ) (x : Fin n → X)
    (i : Fin n) :
    finitePiecePosition S a x i.succ = finitePiecePosition S a x i.castSucc +
      ((a i.succ : ℝ) - (a i.castSucc : ℝ)) • S.embed (x i) := by
  classical
  have hset : (Finset.univ.filter fun j : Fin n ↦ j.castSucc < i.succ) =
      insert i (Finset.univ.filter fun j : Fin n ↦ j.castSucc < i.castSucc) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
    omega
  unfold finitePiecePosition
  rw [hset, Finset.sum_insert (by simp)]
  exact add_comm _ _

/-- On each closed piece, the clamped sum is the cumulative affine formula.
Reconstructed directly by splitting summands before, at, and after the active piece. -/
theorem raw_eq_piece {n : ℕ} {a : Fin (n + 1) → ℚ} (ha : StrictMono a)
    (x : Fin n → X) (i : Fin n) (t : ℝ)
    (ht : t ∈ Icc (a i.castSucc : ℝ) (a i.succ : ℝ)) :
    raw S a x t = finitePiecePosition S a x i.castSucc +
      (t - (a i.castSucc : ℝ)) • S.embed (x i) := by
  classical
  have ham : Monotone (fun k ↦ (a k : ℝ)) := by
    intro j k hjk
    change (a j : ℝ) ≤ (a k : ℝ)
    exact_mod_cast ha.monotone hjk
  have hterm (j : Fin n) :
      (max 0 (min t (a j.succ : ℝ) - (a j.castSucc : ℝ))) • S.embed (x j) =
      (if j.castSucc < i.castSucc then
        ((a j.succ : ℝ) - (a j.castSucc : ℝ)) • S.embed (x j) else 0) +
      (if j = i then (t - (a i.castSucc : ℝ)) • S.embed (x i) else 0) := by
    rcases lt_trichotomy j i with hji | rfl | hij
    · have hlt : j.castSucc < i.castSucc := by simpa using hji
      have hne : j ≠ i := ne_of_lt hji
      have hbefore : (a j.succ : ℝ) ≤ t :=
        (ham (show j.succ ≤ i.castSucc from hji)).trans ht.1
      have hnonneg : 0 ≤ (a j.succ : ℝ) - (a j.castSucc : ℝ) :=
        sub_nonneg.mpr (ham (Fin.castSucc_lt_succ.le))
      simp [hlt, hne, min_eq_right hbefore, max_eq_right hnonneg]
    · simp [min_eq_left ht.2, max_eq_right (sub_nonneg.mpr ht.1)]
    · have hnlt : ¬j.castSucc < i.castSucc := by simpa using (not_lt_of_ge hij.le)
      have hne : j ≠ i := ne_of_gt hij
      have hafter : t ≤ (a j.castSucc : ℝ) :=
        ht.2.trans (ham (show i.succ ≤ j.castSucc from hij))
      have hnonpos : min t (a j.succ : ℝ) - (a j.castSucc : ℝ) ≤ 0 :=
        sub_nonpos.mpr ((min_le_left _ _).trans hafter)
      simp [hnlt, hne, max_eq_left hnonpos]
  unfold raw finitePiecePosition
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_filter]

/-- The cumulative raw function vanishes throughout the nonpositive half-line. -/
theorem raw_of_nonpos {n : ℕ} {a : Fin (n + 2) → ℚ} (ha : StrictMono a)
    (ha0 : a 0 = 0) (x : Fin (n + 1) → X) {t : ℝ} (ht : t ≤ 0) :
    raw S a x t = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hj : (0 : ℝ) ≤ (a j.castSucc : ℝ) := by
    have h := ha.monotone (show (0 : Fin (n + 2)) ≤ j.castSucc from Fin.zero_le _)
    rw [ha0] at h
    exact_mod_cast h
  have hc : min t (a j.succ : ℝ) - (a j.castSucc : ℝ) ≤ 0 :=
    sub_nonpos.mpr ((min_le_left _ _).trans (ht.trans hj))
  rw [max_eq_left hc, zero_smul]

/-- In particular, the raw cumulative function starts at zero. -/
@[simp] theorem raw_zero {n : ℕ} {a : Fin (n + 2) → ℚ} (ha : StrictMono a)
    (ha0 : a 0 = 0) (x : Fin (n + 1) → X) : raw S a x 0 = 0 :=
  raw_of_nonpos S ha ha0 x le_rfl

/-- Every simple-coroot evaluation is globally continuous, even without ordered breakpoints.
No topology on the ambient vector space is needed. -/
theorem continuous_coroot_raw {n : ℕ} (a : Fin (n + 1) → ℚ) (x : Fin n → X)
    (k : ι) : Continuous (fun t ↦ S.coroot k (raw S a x t)) := by
  simp only [raw, map_sum, map_smul, smul_eq_mul]
  fun_prop

end LittelmannPath.FiniteConstruction


open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace LittelmannPath.FiniteConstruction

variable {ι X V : Type*} [AddCommGroup X] [AddCommGroup V] [Module ℝ V]
  {D : CartanDatum ι X} (S : D.PathSpace ℝ V)

/-- The raw path is constant after the last breakpoint, normalized to one. -/
theorem raw_of_one_le {n : ℕ} {a : Fin (n + 2) → ℚ} (ha : StrictMono a)
    (ha1 : a (Fin.last (n + 1)) = 1) (x : Fin (n + 1) → X)
    {t : ℝ} (ht : 1 ≤ t) : raw S a x t = raw S a x 1 := by
  unfold raw
  apply Finset.sum_congr rfl
  intro j _
  have hj : (a j.succ : ℝ) ≤ 1 := by
    have h := ha.monotone (Fin.le_last j.succ)
    rw [ha1] at h
    exact_mod_cast h
  rw [min_eq_right (hj.trans ht), min_eq_right hj]

/-- For every compatible vector-space topology, the same finite formula is continuous.
The base path interface itself needs only continuous simple-coroot evaluations. -/
theorem continuous_raw [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℝ V] {n : ℕ} (a : Fin (n + 1) → ℚ) (x : Fin n → X) :
    Continuous (raw S a x) := by
  unfold raw
  fun_prop

end LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSAChainBridge

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}
  {Λ : Dual ℝ H} (hΛ : P.IsDominantIntegral Λ)
  {n : ℕ} {a : Fin (n + 2) → ℚ} {x : Fin (n + 1) → P.integralWeights}

omit [DecidableEq ι] in
/-- Root-lattice displacements are integral weights. -/
theorem rootLattice_le_integralWeights : rootLattice P ≤ P.integralWeights := by
  rintro _ ⟨k, rfl⟩ i
  exact ⟨(A *ᵥ k) i, rootOf_apply_coroot P k i⟩

include hΛ

/-- Source a-chains propagate the cumulative root-lattice invariant before a path exists.
This is the same invariant as `finite_congruences`, without its supplied-path premise. -/
theorem cumulative_congruences (ha0 : a 0 = 0)
    (hc : ∀ i : Fin n, AChain P hA Λ (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) :
    ∀ i : Fin (n + 1),
      finitePiecePosition (P.pathSpace hA) a x i.castSucc -
        (a i.castSucc : ℝ) • (x i : Dual ℝ H) ∈ rootLattice P := by
  intro i
  induction i using Fin.induction with
  | zero => simp [ha0]
  | succ i ih =>
    have heq : finitePiecePosition (P.pathSpace hA) a x i.succ.castSucc -
        (a i.succ.castSucc : ℝ) • (x i.castSucc : Dual ℝ H) =
        finitePiecePosition (P.pathSpace hA) a x i.castSucc.castSucc -
        (a i.castSucc.castSucc : ℝ) • (x i.castSucc : Dual ℝ H) := by
      rw [Fin.castSucc_succ, finitePiecePosition_succ]
      simp only [pathSpace_embed, sub_smul]
      abel
    exact (aChain_to_chain hΛ (hc i) (heq ▸ ih)).2

/-- The constructed endpoint differs from its final integral direction by a root-lattice
vector. No integrality or LS condition on the endpoint is assumed. -/
theorem raw_endpoint_congruence (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (n + 1)) = 1)
    (hc : ∀ i : Fin n, AChain P hA Λ (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) :
    raw (P.pathSpace hA) a x 1 - (x (Fin.last n) : Dual ℝ H) ∈ rootLattice P := by
  have hi := cumulative_congruences hΛ ha0 hc (Fin.last n)
  have ht : (1 : ℝ) ∈ Icc (a (Fin.last n).castSucc : ℝ)
      (a (Fin.last n).succ : ℝ) := by
    constructor
    · have h := ha.monotone (Fin.le_last (Fin.last n).castSucc)
      rw [ha1] at h
      exact_mod_cast h
    · simp [ha1]
  rw [raw_eq_piece (P.pathSpace hA) ha x (Fin.last n) 1 ht]
  convert hi using 1
  simp only [pathSpace_embed, sub_smul, one_smul]
  abel

/-- Endpoint integrality derived from source a-chains via the actual root lattice.
This supplies, rather than assumes, the missing field of `LittelmannPath`. -/
theorem raw_endpoint_integral (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (n + 1)) = 1)
    (hc : ∀ i : Fin n, AChain P hA Λ (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) :
    raw (P.pathSpace hA) a x 1 ∈ P.integralWeights := by
  have h := rootLattice_le_integralWeights (raw_endpoint_congruence hΛ ha ha0 ha1 hc)
  have hs := P.integralWeights.add_mem h (x (Fin.last n)).property
  simpa only [sub_add_cancel] using hs

/-- The actual finite rational LS path, from source a-chain data. Its endpoint is proved
integral, not part of the input. Compare Littelmann 1995, §4, pp. 509–510, Remark 4.2.
Redundant equal directions are permitted (an explicit extension of the strict presentation). -/
noncomputable def ofAChains (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (n + 1)) = 1)
    (hc : ∀ i : Fin n, AChain P hA Λ (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) : LittelmannPath (P.pathSpace hA) where
  toFun := raw (P.pathSpace hA) a x
  wt := ⟨raw (P.pathSpace hA) a x 1, raw_endpoint_integral hΛ ha ha0 ha1 hc⟩
  toFun_of_nonpos' := fun _ ht ↦ raw_of_nonpos (P.pathSpace hA) ha ha0 x ht
  toFun_of_one_le' := fun _ ht ↦ raw_of_one_le (P.pathSpace hA) ha ha1 x ht
  continuous_coroot' := continuous_coroot_raw (P.pathSpace hA) a x

/-- The constructor has the literal cumulative affine formula on each closed piece. -/
theorem ofAChains_piece (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (n + 1)) = 1)
    (hc : ∀ i : Fin n, AChain P hA Λ (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) (i : Fin (n + 1)) (t : ℝ)
    (ht : t ∈ Icc (a i.castSucc : ℝ) (a i.succ : ℝ)) :
    ofAChains hΛ ha ha0 ha1 hc t = finitePiecePosition (P.pathSpace hA) a x i.castSucc +
      (t - (a i.castSucc : ℝ)) • (x i : Dual ℝ H) :=
  raw_eq_piece (P.pathSpace hA) ha x i t ht

/-- The constructed path satisfies the concrete global LS condition.
The source dominant-orbit a-chains, not an LS premise, are the hypotheses. -/
theorem isLS_ofAChains (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (n + 1)) = 1)
    (hx : ∀ i, ∃ w : P.weylGroup hA, (x i : Dual ℝ H) = w.1 Λ)
    (hc : ∀ i : Fin n, AChain P hA Λ (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) :
    IsLS (P.lsData hA hΛ) (ofAChains hΛ ha ha0 ha1 hc) :=
  (isLS_rationalPieces_iff_aChains hΛ ha ha0
    (ofAChains_piece hΛ ha ha0 ha1 hc) ha1 hx).mpr hc

/-- The constructed weight is exactly the full cumulative displacement. -/
theorem ofAChains_wt (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (n + 1)) = 1)
    (hc : ∀ i : Fin n, AChain P hA Λ (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) :
    ((ofAChains hΛ ha ha0 ha1 hc).wt : Dual ℝ H) =
      finitePiecePosition (P.pathSpace hA) a x (Fin.last (n + 1)) := by
  change raw (P.pathSpace hA) a x 1 = _
  have ht : (a (Fin.last n).succ : ℝ) ∈
      Icc (a (Fin.last n).castSucc : ℝ) (a (Fin.last n).succ : ℝ) := by
    exact ⟨by exact_mod_cast (ha Fin.castSucc_lt_succ).le, le_rfl⟩
  have h := raw_eq_piece (P.pathSpace hA) ha x (Fin.last n) _ ht
  rw [← finitePiecePosition_succ] at h
  simpa [ha1] using h

/-- Direct existence of a genuine LS path from finite dominant-orbit a-chain data.
This is the constructor/existence direction missing from the supplied-path criterion. -/
theorem exists_isLS_rationalPieces (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (n + 1)) = 1)
    (hx : ∀ i, ∃ w : P.weylGroup hA, (x i : Dual ℝ H) = w.1 Λ)
    (hc : ∀ i : Fin n, AChain P hA Λ (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) :
    ∃ π : LittelmannPath (P.pathSpace hA), IsLS (P.lsData hA hΛ) π ∧
      (∀ i t, t ∈ Icc (a i.castSucc : ℝ) (a i.succ : ℝ) →
        π t = finitePiecePosition (P.pathSpace hA) a x i.castSucc +
          (t - (a i.castSucc : ℝ)) • (x i : Dual ℝ H)) ∧
      (π.wt : Dual ℝ H) = finitePiecePosition (P.pathSpace hA) a x (Fin.last (n + 1)) :=
  ⟨ofAChains hΛ ha ha0 ha1 hc, isLS_ofAChains hΛ ha ha0 ha1 hx hc,
    ofAChains_piece hΛ ha ha0 ha1 hc, ofAChains_wt hΛ ha ha0 ha1 hc⟩

/-- The single-segment case is exactly the straight line, with no internal chain input. -/
theorem ofAChains_single {a : Fin 2 → ℚ} {x : Fin 1 → P.integralWeights}
    (ha : StrictMono a) (ha0 : a 0 = 0) (ha1 : a (Fin.last 1) = 1) :
    ofAChains (x := x) hΛ ha ha0 ha1 (fun i : Fin 0 ↦ Fin.elim0 i) =
      straightLine (P.pathSpace hA) (x 0) := by
  apply LittelmannPath.ext_of_eqOn
  intro t ht
  have ha1' : a 1 = 1 := ha1
  have h := ofAChains_piece (hA := hA) (x := x) hΛ ha ha0 ha1 (fun i : Fin 0 ↦ Fin.elim0 i) 0 t
    (by simpa [ha0, ha1'] using ht)
  rw [h, straightLine_apply, min_eq_right ht.2, max_eq_right ht.1]
  simp [ha0]

end Matrix.Realization.LSAChainBridge
