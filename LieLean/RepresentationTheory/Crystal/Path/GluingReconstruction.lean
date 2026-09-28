/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GeneralClassGluing

/-!
# Finite cut-extension reconstruction for arbitrary-class gluing

## Main definitions / results

`Presentation.extendCut` constructs the finite source presentation used at the left cut.
The new final direction is supplied by an actual source chain, not an assumed LS path.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), Remark 5.4, p. 514, used in Proposition 5.6, pp. 515–516. Scans inspected;
proofs reconstructed. Neither integral class needs dominance. This is a reconstruction
input to the crossing-seam case, not the full root-operator stability theorem.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

namespace Presentation

variable (σ : Presentation P hA)

/-- Insert the cut just before the terminal time, retaining all earlier breakpoints. -/
def cutTimes (s : ℚ) : Fin (σ.n + 3) → ℚ :=
  Fin.snoc (Fin.snoc (fun j : Fin (σ.n + 1) ↦ σ.a j.castSucc) s) 1

/-- The inserted cut gives a strict rational subdivision. -/
theorem cutTimes_strictMono {s : ℚ}
    (hs : σ.a (Fin.last σ.n).castSucc < s) (hs1 : s < 1) :
    StrictMono (σ.cutTimes s) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · simpa [cutTimes] using hs1
  · refine Fin.lastCases ?_ (fun l ↦ ?_) k
    · simpa only [cutTimes, Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        Fin.succ_last] using hs
    · simpa only [cutTimes, Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        Fin.succ_last] using
        σ.mono l.castSucc.castSucc_lt_succ

/-- Remark 5.4's explicit left-cut extension. Its endpoint integrality is derived
by the source constructor; it is not a new hypothesis. Equal adjacent directions
are allowed, as in the production presentation API. -/
noncomputable def extendCut (s : ℚ) (ν : P.integralWeights)
    (hs : σ.a (Fin.last σ.n).castSucc < s) (hs1 : s < 1)
    (hc : AChain P hA (s : ℝ) (σ.x (Fin.last σ.n)) ν) : Presentation P hA where
  n := σ.n + 1
  a := σ.cutTimes s
  x := Fin.snoc σ.x ν
  mono := σ.cutTimes_strictMono hs hs1
  zero := by
    change σ.cutTimes s ((0 : Fin (σ.n + 1)).castSucc.castSucc) = 0
    rw [cutTimes, Fin.snoc_castSucc, Fin.snoc_castSucc]
    exact σ.zero
  one := by simp [cutTimes]
  chains := by
    intro j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simpa [cutTimes] using hc
    · simpa only [cutTimes, Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        Fin.succ_last] using σ.chains k

variable {σ} {s : ℚ} {ν : P.integralWeights}
  (hs : σ.a (Fin.last σ.n).castSucc < s) (hs1 : s < 1)
  (hc : AChain P hA (s : ℝ) (σ.x (Fin.last σ.n)) ν)

/-- The finite reconstructed path agrees literally with the original up to the cut;
there is no quotient or reparametrization in this equality. -/
theorem extendCut_path_of_le {t : ℝ} (ht : t ≤ s) :
    (σ.extendCut s ν hs hs1 hc).path t = σ.path t := by
  have hs1R : (s : ℝ) ≤ 1 := by exact_mod_cast hs1.le
  change raw (P.pathSpace hA) (σ.cutTimes s) (Fin.snoc σ.x ν) t =
    raw (P.pathSpace hA) σ.a σ.x t
  unfold raw
  rw [Fin.sum_univ_castSucc]
  have hz : max 0 (min t (1 : ℝ) - s) = 0 :=
    max_eq_left (sub_nonpos.mpr ((min_le_left t 1).trans ht))
  simp only [cutTimes, Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc,
    Rat.cast_one, hz, zero_smul, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · simp only [Fin.succ_castSucc, Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last,
      σ.one, Rat.cast_one, min_eq_left ht, min_eq_left (ht.trans hs1R)]
  · simp only [Fin.succ_castSucc, Fin.snoc_castSucc]

/-- On its new final segment the extension follows exactly the cut direction. -/
theorem extendCut_path_of_mem {t : ℝ} (ht : t ∈ Icc (s : ℝ) 1) :
    (σ.extendCut s ν hs hs1 hc).path t = σ.path s + (t - s) • (ν : Dual ℝ H) := by
  let τ := σ.extendCut s ν hs hs1 hc
  have hb : τ.a (Fin.last τ.n).castSucc = s := by simp [τ, extendCut, cutTimes]
  have hx : τ.x (Fin.last τ.n) = ν := by simp [τ, extendCut]
  have ht' : t ∈ Icc (τ.a (Fin.last τ.n).castSucc : ℝ)
      (τ.a (Fin.last τ.n).succ : ℝ) := by simpa [hb, τ.one] using ht
  have hs' : (s : ℝ) ∈ Icc (τ.a (Fin.last τ.n).castSucc : ℝ)
      (τ.a (Fin.last τ.n).succ : ℝ) := by
    simp only [hb, Fin.succ_last, τ.one, Rat.cast_one, mem_Icc, le_refl, true_and]
    exact_mod_cast hs1.le
  have hcut := τ.piece (Fin.last τ.n) s hs'
  simp only [hb, hx, sub_self, zero_smul, add_zero] at hcut
  rw [τ.piece (Fin.last τ.n) t ht', hb, hx, ← hcut]
  rw [extendCut_path_of_le hs hs1 hc le_rfl]

/-- The extension is in the original integral class, not a newly chosen orbit. -/
theorem extendCut_isLS :
    IsLS (lsData P hA (σ.x 0)) (σ.extendCut s ν hs hs1 hc).path := by
  have hzero : (σ.extendCut s ν hs hs1 hc).x 0 = σ.x 0 := by
    change (Fin.snoc (α := fun _ ↦ P.integralWeights) σ.x ν)
      ((0 : Fin (σ.n + 1)).castSucc) = σ.x 0
    rw [Fin.snoc_castSucc]
  simpa only [hzero] using (σ.extendCut s ν hs hs1 hc).isLS

/-- Insert a right cut just after zero, retaining every later breakpoint. -/
def initialCutTimes (σ : Presentation P hA) (s : ℚ) : Fin (σ.n + 3) → ℚ :=
  Fin.cons 0 (Fin.cons s (fun j : Fin (σ.n + 1) ↦ σ.a j.succ))

/-- A strict subdivision for the right-cut reconstruction. -/
theorem initialCutTimes_strictMono (σ : Presentation P hA) {s : ℚ}
    (hs0 : 0 < s) (hs : s < σ.a (0 : Fin (σ.n + 1)).succ) :
    StrictMono (σ.initialCutTimes s) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simpa [initialCutTimes] using hs0
  · refine Fin.cases ?_ (fun l ↦ ?_) k
    · simpa only [initialCutTimes, Fin.castSucc_succ, Fin.castSucc_zero,
        Fin.cons_succ, Fin.cons_zero] using hs
    · simpa only [initialCutTimes, Fin.castSucc_succ, Fin.cons_succ] using
        σ.mono l.succ.castSucc_lt_succ

/-- Remark 5.4's right-cut presentation: prepend the actual source-chain direction. -/
noncomputable def prependCut (σ : Presentation P hA) (s : ℚ) (μ : P.integralWeights)
    (hs0 : 0 < s) (hs : s < σ.a (0 : Fin (σ.n + 1)).succ)
    (hc : AChain P hA (s : ℝ) μ (σ.x 0)) : Presentation P hA where
  n := σ.n + 1
  a := σ.initialCutTimes s
  x := Fin.cons μ σ.x
  mono := σ.initialCutTimes_strictMono hs0 hs
  zero := by simp [initialCutTimes]
  one := by
    change σ.initialCutTimes s (Fin.last σ.n).succ.succ = 1
    rw [initialCutTimes, Fin.cons_succ, Fin.cons_succ, Fin.succ_last, σ.one]
  chains := by
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simpa [initialCutTimes] using hc
    · simpa only [initialCutTimes, Fin.castSucc_succ, Fin.cons_succ] using σ.chains k

variable (σ : Presentation P hA) {s : ℚ} {μ : P.integralWeights}
  (hs0 : 0 < s) (hs : s < σ.a (0 : Fin (σ.n + 1)).succ)
  (hc : AChain P hA (s : ℝ) μ (σ.x 0))

/-- The reconstructed initial piece is the literal cut direction. -/
theorem prependCut_path_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) s) :
    (σ.prependCut s μ hs0 hs hc).path t = t • (μ : Dual ℝ H) := by
  exact (σ.prependCut s μ hs0 hs hc).first_piece t ht

/-- The discarded initial piece changes the retained right path by exactly the
source cut offset. This is an equality of paths at their original parameters. -/
theorem prependCut_path_of_le {t : ℝ} (ht : (s : ℝ) ≤ t) :
    (σ.prependCut s μ hs0 hs hc).path t =
      σ.path t + (s : ℝ) • ((μ : Dual ℝ H) - (σ.x 0 : Dual ℝ H)) := by
  have hs0R : (0 : ℝ) ≤ s := by exact_mod_cast hs0.le
  have hsR : (s : ℝ) ≤ σ.a (0 : Fin (σ.n + 1)).succ := by exact_mod_cast hs.le
  have hmin : (s : ℝ) ≤ min t (σ.a (0 : Fin (σ.n + 1)).succ : ℝ) :=
    le_min ht hsR
  change raw (P.pathSpace hA) (σ.initialCutTimes s) (Fin.cons μ σ.x) t =
    raw (P.pathSpace hA) σ.a σ.x t + _
  unfold raw
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [initialCutTimes, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
    Fin.castSucc_succ, σ.zero, Rat.cast_zero, min_eq_right ht, sub_zero,
    max_eq_right hs0R, max_eq_right (sub_nonneg.mpr hmin),
    max_eq_right (hs0R.trans hmin), pathSpace_embed]
  simp only [sub_smul, smul_sub]
  abel

/-- The right reconstruction remains LS in the original second class. -/
theorem prependCut_isLS :
    IsLS (lsData P hA (σ.x 0)) (σ.prependCut s μ hs0 hs hc).path := by
  apply isLS_ofAChains (σ.prependCut s μ hs0 hs hc).mono
    (σ.prependCut s μ hs0 hs hc).zero (σ.prependCut s μ hs0 hs hc).one
    ?_ (σ.prependCut s μ hs0 hs hc).chains
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · obtain ⟨u, hu⟩ := hc.eq_weyl
    refine ⟨u⁻¹, ?_⟩
    change (μ : Dual ℝ H) = u.1.symm (σ.x 0)
    rw [hu]
    simp
  · change ∃ w : P.weylGroup hA, (σ.x k : Dual ℝ H) = w.1 (σ.x 0)
    exact σ.orbit k

end Presentation

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- Integrality of the actual left cut direction follows from its source orbit. -/
theorem left_direction_integral : g.ν ∈ P.integralWeights := by
  obtain ⟨w, hw⟩ := g.left_orbit
  rw [hw]
  exact fun i ↦ exists_int_apply_coroot (σ.x 0).property w i

/-- The reversed right-chain orientation still gives an integral cut direction. -/
theorem right_direction_integral : g.μ ∈ P.integralWeights := by
  obtain ⟨w, hw⟩ := g.right_orbit
  rw [hw]
  exact fun i ↦ exists_int_apply_coroot (δ.x 0).property w i

/-- The actual left finite presentation of Remark 5.4. -/
noncomputable def leftExtension : Presentation P hA :=
  σ.extendCut g.s ⟨g.ν, g.left_direction_integral⟩ g.last_lt
    (g.le.trans_lt g.lt_one) g.left_chain

/-- The actual right finite presentation of Remark 5.4. -/
noncomputable def rightExtension : Presentation P hA :=
  δ.prependCut g.s' ⟨g.μ, g.right_direction_integral⟩ (g.pos.trans_le g.le)
    g.first_gt g.right_chain

/-- Both cut extensions are genuine finite source LS presentations in the original
classes, and reconstruct the *same* literal glued function. This is Remark 5.4's
input to the seam-crossing argument of Proposition 5.6; it does not assert that
these auxiliary presentations themselves satisfy the strict interior-cut fields
of a new `GluingPair`. -/
theorem cut_reconstruction :
    IsLS (lsData P hA (σ.x 0)) g.leftExtension.path ∧
    IsLS (lsData P hA (δ.x 0)) g.rightExtension.path ∧
    (g.leftExtension.x (Fin.last g.leftExtension.n) : Dual ℝ H) = g.ν ∧
    (g.rightExtension.x 0 : Dual ℝ H) = g.μ ∧
    ∀ t : ℝ, glueRaw g.leftExtension g.rightExtension g.s g.s' t = g.path t := by
  refine ⟨Presentation.extendCut_isLS _ _ _, δ.prependCut_isLS _ _ _, ?_, rfl, ?_⟩
  · simp [leftExtension, Presentation.extendCut]
  · intro t
    change g.leftExtension.path (min t (g.s : ℝ)) +
      g.rightExtension.path (max t (g.s' : ℝ)) - g.rightExtension.path g.s' =
      σ.path (min t (g.s : ℝ)) + δ.path (max t (g.s' : ℝ)) - δ.path g.s'
    unfold leftExtension rightExtension
    rw [Presentation.extendCut_path_of_le _ _ _ (min_le_right _ _),
      Presentation.prependCut_path_of_le _ _ _ _ (le_max_right _ _),
      Presentation.prependCut_path_of_le _ _ _ _ le_rfl]
    abel

end GluingPair
end Matrix.Realization.LSGeneralClass
