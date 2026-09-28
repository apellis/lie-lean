/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingDirections

/-!
# A concrete finite gluing pair and integrality at its cut

Source: P. Littelmann, *Paths and root operators in representation theory*, Ann. Math.
142 (1995), 499–525, Definition 5.3 and Lemma 5.5, printed pp. 514–515, with the
literal gluing formula on p. 513. Proofs below are reconstructed.

Scope: both LS presentations have dominant integral classes, using the published
positive-real-root saturated `AChain` implementation. Directions need not be dominant;
the number of pieces, rank, and generalized Cartan matrix are unrestricted. This is
NOT the extension of that chain implementation to all rational classes in the source.
Redundant equal directions are allowed, as in the published finite constructor.

The input includes the two actual source cut-time chains and the source's integral
endpoint condition. It does not assume position-chain compatibility, integral cut
height, local-minimum integrality, or stability. These are not abstract LSData inputs:
all chains use the concrete realization. We construct the paused finite rational-PL
path, derive its two position chains, and prove the new seam integrality argument.
`GluingPair.isIntegral` then proves that every simple-coroot global minimum of the
constructed path is an integer, splitting the last minimizer before/at/after the pause.
The local statement proved is `plateau_min_integral` (weak on the incoming side and
strict on the outgoing side across the whole pause), not an unqualified assertion
about every point of every locally constant interval.
Neither Proposition 5.6 nor an isomorphism of arbitrary continuous paths is claimed.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGluing

open LSAChainBridge

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}
  {Λ Μ : Dual ℝ H}

/-- Finite source time-chain data, not a supplied path or an LS assumption. -/
structure Presentation (P : Realization A ℝ H) (hA : A.IsGeneralizedCartan)
    (Λ : Dual ℝ H) where
  n : ℕ
  a : Fin (n + 2) → ℚ
  x : Fin (n + 1) → P.integralWeights
  mono : StrictMono a
  zero : a 0 = 0
  one : a (Fin.last (n + 1)) = 1
  orbit : ∀ j, ∃ w : P.weylGroup hA, (x j : Dual ℝ H) = w.1 Λ
  chains : ∀ j : Fin n, AChain P hA Λ (a j.succ.castSucc : ℝ)
    (x j.castSucc) (x j.succ)

namespace Presentation

variable (hΛ : P.IsDominantIntegral Λ) (σ : Presentation P hA Λ)

/-- The actual path built from the source presentation. -/
noncomputable def path : LittelmannPath (P.pathSpace hA) :=
  ofAChains hΛ σ.mono σ.zero σ.one σ.chains

/-- Its LS condition is a theorem, not a field of the presentation. -/
theorem isLS : IsLS (P.lsData hA hΛ) (σ.path hΛ) :=
  isLS_ofAChains hΛ σ.mono σ.zero σ.one σ.orbit σ.chains

/-- The affine formula on every closed piece. -/
theorem piece (j : Fin (σ.n + 1)) (t : ℝ)
    (ht : t ∈ Icc (σ.a j.castSucc : ℝ) (σ.a j.succ : ℝ)) :
    σ.path hΛ t = finitePiecePosition (P.pathSpace hA) σ.a σ.x j.castSucc +
      (t - (σ.a j.castSucc : ℝ)) • (σ.x j : Dual ℝ H) :=
  ofAChains_piece hΛ σ.mono σ.zero σ.one σ.chains j t ht

/-- At any time in a piece the incoming root-lattice invariant still holds. -/
theorem congruence (j : Fin (σ.n + 1)) (t : ℝ)
    (ht : t ∈ Icc (σ.a j.castSucc : ℝ) (σ.a j.succ : ℝ)) :
    σ.path hΛ t - t • (σ.x j : Dual ℝ H) ∈ rootLattice P := by
  rw [σ.piece hΛ j t ht]
  convert cumulative_congruences hΛ σ.zero σ.chains j using 1
  rw [sub_smul t (σ.a j.castSucc : ℝ) (σ.x j : Dual ℝ H)]
  abel

/-- On the first piece, the path is exactly the initial straight line. -/
theorem first_piece (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (σ.a (0 : Fin (σ.n + 1)).succ : ℝ)) :
    σ.path hΛ t = t • (σ.x 0 : Dual ℝ H) := by
  simpa [σ.zero] using σ.piece hΛ 0 t (by simpa [σ.zero] using ht)

end Presentation

variable (hΛ : P.IsDominantIntegral Λ) (hΜ : P.IsDominantIntegral Μ)
  (σ : Presentation P hA Λ) (δ : Presentation P hA Μ)

/-- The literal p. 513 glue `σ^s ∘ θ ∘ δ_s'`, with no time compression.
The min/max expression also gives a globally continuous finite clipped-affine formula. -/
noncomputable def glueRaw (s s' : ℚ) (t : ℝ) : Dual ℝ H :=
  σ.path hΛ (min t (s : ℝ)) + δ.path hΜ (max t (s' : ℝ)) - δ.path hΜ s'

/-- Definition 5.3, in the concrete dominant-integral-class implementation.
The two cut chains have the source orientations `λ_r → ν` and `μ → μ_1`.
Endpoint integrality is precisely the source hypothesis `η ∈ Π_int`. -/
structure GluingPair where
  s : ℚ
  s' : ℚ
  pos : 0 < s
  le : s ≤ s'
  lt_one : s' < 1
  last_lt : σ.a (Fin.last σ.n).castSucc < s
  first_gt : s' < δ.a (0 : Fin (δ.n + 1)).succ
  ν : P.integralWeights
  μ : P.integralWeights
  ν_orbit : ∃ w : P.weylGroup hA, (ν : Dual ℝ H) = w.1 Λ
  μ_orbit : ∃ w : P.weylGroup hA, (μ : Dual ℝ H) = w.1 Μ
  left_chain : AChain P hA Λ (s : ℝ) (σ.x (Fin.last σ.n)) ν
  right_chain : AChain P hA Μ (s' : ℝ) μ (δ.x 0)
  precedes : P.GluingPrecedes hA ν μ
  endpoint : glueRaw hΛ hΜ σ δ s s' 1 ∈ P.integralWeights

namespace GluingPair

variable {hΛ hΜ σ δ} (g : GluingPair hΛ hΜ σ δ)

/-- The unchanged initial portion of the glued path. -/
theorem raw_left {t : ℝ} (ht : t ≤ g.s) :
    glueRaw hΛ hΜ σ δ g.s g.s' t = σ.path hΛ t := by
  have hle : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  simp [glueRaw, min_eq_left ht, max_eq_right (ht.trans hle)]

/-- The glue is genuinely paused on the whole closed interval, including `s = s'`. -/
theorem raw_pause {t : ℝ} (ht : t ∈ Icc (g.s : ℝ) (g.s' : ℝ)) :
    glueRaw hΛ hΜ σ δ g.s g.s' t = σ.path hΛ g.s := by
  simp [glueRaw, min_eq_right ht.1, max_eq_right ht.2]

/-- The translated final portion, with the source's endpoint-preserving offset. -/
theorem raw_right {t : ℝ} (ht : (g.s' : ℝ) ≤ t) :
    glueRaw hΛ hΜ σ δ g.s g.s' t =
      δ.path hΜ t + (σ.path hΛ g.s - δ.path hΜ g.s') := by
  have hle : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  rw [glueRaw, min_eq_right (hle.trans ht), max_eq_left ht]
  abel

/-- An actual path, constructed rather than assumed; rational PL is given by the
finite clipped sums in `raw_formula` and the three literal gluing identities. -/
noncomputable def path : LittelmannPath (P.pathSpace hA) where
  toFun := glueRaw hΛ hΜ σ δ g.s g.s'
  wt := ⟨glueRaw hΛ hΜ σ δ g.s g.s' 1, g.endpoint⟩
  toFun_of_nonpos' := by
    intro t ht
    have hs : (0 : ℝ) < g.s := by exact_mod_cast g.pos
    rw [g.raw_left (ht.trans hs.le), (σ.path hΛ).apply_of_nonpos ht]
  toFun_of_one_le' := by
    intro t ht
    have hs : (g.s' : ℝ) ≤ 1 := by exact_mod_cast g.lt_one.le
    change glueRaw hΛ hΜ σ δ g.s g.s' t = glueRaw hΛ hΜ σ δ g.s g.s' 1
    rw [g.raw_right (hs.trans ht), g.raw_right hs,
      (δ.path hΜ).apply_of_one_le ht, (δ.path hΜ).apply_one]
  continuous_coroot' := by
    intro i
    simp only [glueRaw, map_sub, map_add]
    exact (((σ.path hΛ).continuous_pairing i).comp
      (continuous_id.min continuous_const)).add
      (((δ.path hΜ).continuous_pairing i).comp
        (continuous_id.max continuous_const)) |>.sub continuous_const

/-- Explicit finite rational clipped-affine formula; no arbitrary continuous-path
existence principle is used in the construction. -/
theorem raw_formula (t : ℝ) :
    g.path t =
      (∑ j : Fin (σ.n + 1),
        max 0 (min (min t (g.s : ℝ)) (σ.a j.succ : ℝ) -
          (σ.a j.castSucc : ℝ)) • (σ.x j : Dual ℝ H)) +
      (∑ j : Fin (δ.n + 1),
        max 0 (min (max t (g.s' : ℝ)) (δ.a j.succ : ℝ) -
          (δ.a j.castSucc : ℝ)) • (δ.x j : Dual ℝ H)) -
      (∑ j : Fin (δ.n + 1),
        max 0 (min (g.s' : ℝ) (δ.a j.succ : ℝ) -
          (δ.a j.castSucc : ℝ)) • (δ.x j : Dual ℝ H)) := rfl

/-- In particular the gluing construction agrees with the source on its plateau. -/
theorem path_pause {t : ℝ} (ht : t ∈ Icc (g.s : ℝ) (g.s' : ℝ)) :
    g.path t = σ.path hΛ g.s := g.raw_pause ht

/-- The left cut belongs to the final affine segment. -/
theorem left_cut_mem : (g.s : ℝ) ∈
    Icc (σ.a (Fin.last σ.n).castSucc : ℝ) (σ.a (Fin.last σ.n).succ : ℝ) := by
  constructor
  · exact_mod_cast g.last_lt.le
  · have h : g.s ≤ 1 := g.le.trans g.lt_one.le
    simpa [σ.one] using (show (g.s : ℝ) ≤ 1 by exact_mod_cast h)

/-- The right cut belongs to the initial affine segment. -/
theorem right_cut_mem : (g.s' : ℝ) ∈ Icc (0 : ℝ) (δ.a (0 : Fin (δ.n + 1)).succ : ℝ) :=
  ⟨by exact_mod_cast (g.pos.le.trans g.le), by exact_mod_cast g.first_gt.le⟩

/-- The first actual cut-position chain is derived from the source `s`-chain
and the proved cumulative root-lattice invariant. -/
theorem left_position_chain :
    (P.lsData hA hΛ).Chain (σ.path hΛ g.s) (σ.x (Fin.last σ.n)) g.ν :=
  (aChain_to_chain hΛ g.left_chain (σ.congruence hΛ _ _ g.left_cut_mem)).1

/-- A source time chain also gives a position chain at its scaled *target*.
This is proved by transporting the root-lattice invariant through the chain and back. -/
theorem aChain_at_target {x y : P.integralWeights} {a : ℝ}
    (hc : AChain P hA Μ a x y) :
    (P.lsData hA hΜ).Chain (a • (y : Dual ℝ H)) x y := by
  have hd := (aChain_to_chain hΜ hc
    (show a • (x : Dual ℝ H) - a • (x : Dual ℝ H) ∈ rootLattice P by simp)).2
  have hq : a • (y : Dual ℝ H) - a • (x : Dual ℝ H) ∈ rootLattice P := by
    simpa only [neg_sub] using (rootLattice P).neg_mem hd
  exact (aChain_to_chain hΜ hc hq).1

/-- The second actual cut-position chain, derived with the correct reversed
endpoint role: the source `s'`-chain ends at the initial direction of `δ`. -/
theorem right_position_chain :
    (P.lsData hA hΜ).Chain (δ.path hΜ g.s') g.μ (δ.x 0) := by
  rw [δ.first_piece hΜ _ g.right_cut_mem]
  exact aChain_at_target (hΜ := hΜ) g.right_chain

/-- The translation between the two cuts is an integral weight, derived from
`η(1) ∈ X` and `δ(1) ∈ X`, not assumed at the seam. -/
theorem offset_integral : σ.path hΛ g.s - δ.path hΜ g.s' ∈ P.integralWeights := by
  have hs : (g.s' : ℝ) ≤ 1 := by exact_mod_cast g.lt_one.le
  have he := g.endpoint
  rw [g.raw_right hs] at he
  have hd := (δ.path hΜ).wt.property
  change δ.path hΜ 1 ∈ P.integralWeights at hd
  simpa only [add_sub_cancel_left] using P.integralWeights.sub_mem he hd

/-- Both source cut chains can be placed at the SAME glued cut point. -/
theorem right_glued_chain :
    (P.lsData hA hΜ).Chain (σ.path hΛ g.s) g.μ (δ.x 0) := by
  have hh := g.right_position_chain.add_embed
    (⟨σ.path hΛ g.s - δ.path hΜ g.s', g.offset_integral⟩ : P.integralWeights)
  simpa only [pathSpace_embed, add_sub_cancel] using hh

/-- The substantive seam step of Lemma 5.5, pp. 514–515.
If the incoming slope is negative and the outgoing slope positive, the common
plateau height is integral. The cut chains and all-positive-root compatibility,
not any integrality/stability conclusion, supply the proof. -/
theorem cut_height_integral {i : ι}
    (hleft : (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) < 0)
    (hright : 0 < (δ.x 0 : Dual ℝ H) (P.coroot i)) :
    ∃ z : ℤ, (σ.path hΛ g.s) (P.coroot i) = z := by
  by_cases hν : 0 ≤ (g.ν : Dual ℝ H) (P.coroot i)
  · apply g.left_position_chain.exists_int
    right
    constructor
    · exact coroot_cartanDatum_neg_iff.mpr hleft
    · rw [← coroot_cartanDatum_cast P hA] at hν
      exact_mod_cast hν
  · have hμ := g.precedes.simple (lt_of_not_ge hν)
    apply g.right_glued_chain.exists_int
    left
    constructor
    · rw [← coroot_cartanDatum_cast P hA] at hμ
      exact_mod_cast hμ
    · exact coroot_cartanDatum_pos_iff.mpr hright

/-- Every time on that plateau has the same integral simple-coroot height. -/
theorem plateau_height_integral {i : ι}
    (hleft : (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) < 0)
    (hright : 0 < (δ.x 0 : Dual ℝ H) (P.coroot i))
    {t : ℝ} (ht : t ∈ Icc (g.s : ℝ) (g.s' : ℝ)) :
    ∃ z : ℤ, g.path.pairing i t = z := by
  simpa only [pairing, pathSpace_coroot, g.path_pause ht] using
    g.cut_height_integral hleft hright

/-- The zero incoming-slope case is also integral, by the cumulative invariant.
This removes the strict-slope simplification in the printed proof of Lemma 5.5. -/
theorem cut_height_integral_of_left_zero {i : ι}
    (hz : (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) = 0) :
    ∃ z : ℤ, (σ.path hΛ g.s) (P.coroot i) = z := by
  have h := rootLattice_le_integralWeights
    (σ.congruence hΛ _ _ g.left_cut_mem) i
  simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hz,
    mul_zero, sub_zero] using h

/-- The weak incoming-slope variant needed when a minimum extends backwards. -/
theorem cut_height_integral_of_nonpos {i : ι}
    (hleft : (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) ≤ 0)
    (hright : 0 < (δ.x 0 : Dual ℝ H) (P.coroot i)) :
    ∃ z : ℤ, (σ.path hΛ g.s) (P.coroot i) = z := by
  rcases lt_or_eq_of_le hleft with hl | hl
  · exact g.cut_height_integral hl hright
  · exact g.cut_height_integral_of_left_zero hl

/-- The glued path has the actual last incoming direction at its left cut. -/
theorem left_direction : g.path.HasLeftDir g.s (σ.x (Fin.last σ.n)) := by
  have hs : (σ.a (Fin.last σ.n).castSucc : ℝ) < g.s := by exact_mod_cast g.last_lt
  refine ⟨g.s - (σ.a (Fin.last σ.n).castSucc : ℝ), sub_pos.mpr hs, ?_⟩
  intro t ht
  have ht' : t ∈ Icc (σ.a (Fin.last σ.n).castSucc : ℝ)
      (σ.a (Fin.last σ.n).succ : ℝ) :=
    ⟨by linarith [ht.1], ht.2.trans g.left_cut_mem.2⟩
  change glueRaw hΛ hΜ σ δ g.s g.s' t =
    glueRaw hΛ hΜ σ δ g.s g.s' g.s + _
  rw [g.raw_left ht.2, g.raw_left le_rfl, σ.piece hΛ _ _ ht',
    σ.piece hΛ _ _ g.left_cut_mem, pathSpace_embed]
  module

/-- The glued path has the actual first outgoing direction at its right cut. -/
theorem right_direction : g.path.HasRightDir g.s' (δ.x 0) := by
  have hs : (g.s' : ℝ) < δ.a (0 : Fin (δ.n + 1)).succ := by exact_mod_cast g.first_gt
  refine ⟨(δ.a (0 : Fin (δ.n + 1)).succ : ℝ) - g.s', sub_pos.mpr hs, ?_⟩
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) (δ.a (0 : Fin (δ.n + 1)).succ : ℝ) :=
    ⟨g.right_cut_mem.1.trans ht.1, by linarith [ht.2]⟩
  change glueRaw hΛ hΜ σ δ g.s g.s' t =
    glueRaw hΛ hΜ σ δ g.s g.s' g.s' + _
  rw [g.raw_right ht.1, g.raw_right le_rfl, δ.first_piece hΜ _ ht',
    δ.first_piece hΜ _ g.right_cut_mem, pathSpace_embed]
  module

/-- A plateau minimum, weak on the incoming side and strict on the outgoing side,
has integral height. The signs are derived from the path, not extra chain premises. -/
theorem plateau_min_integral {i : ι} {a b : ℝ}
    (ha : a < g.s) (hb : (g.s' : ℝ) < b)
    (hmin : ∀ t ∈ Icc a b, g.path.pairing i g.s ≤ g.path.pairing i t)
    (hlt : ∀ t ∈ Ioc (g.s' : ℝ) b, g.path.pairing i g.s' < g.path.pairing i t) :
    ∃ z : ℤ, g.path.pairing i g.s' = z := by
  have hle : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  have hl := g.left_direction.coroot_nonpos (sub_pos.mpr ha) (i := i) (fun t ht ↦
    hmin t ⟨by linarith [ht.1], ht.2.le.trans (hle.trans hb.le)⟩)
  have hr := g.right_direction.coroot_pos (sub_pos.mpr hb) (i := i) (fun t ht ↦
    hlt t ⟨ht.1, by linarith [ht.2]⟩)
  have hl' : (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) ≤ 0 := by
    rw [← coroot_cartanDatum_cast P hA]
    exact_mod_cast hl
  have hr' := coroot_cartanDatum_pos_iff.mp hr
  simpa only [pairing, pathSpace_coroot, g.path_pause ⟨hle, le_rfl⟩] using
    g.cut_height_integral_of_nonpos hl' hr'

/-- Lemma 5.5's global-minimum consequence for these concrete gluing pairs.
This is the `IsIntegral` input needed by the linking and stability arguments.
No component integrality or root-operator stability is assumed. -/
theorem isIntegral : g.path.IsIntegral := by
  intro i
  have hs0 : (0 : ℝ) < g.s := by exact_mod_cast g.pos
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  have hs1 : (g.s' : ℝ) < 1 := by exact_mod_cast g.lt_one
  obtain ⟨w, hw, hmin, hlt⟩ := exists_last_minimizer (g.path.continuous_pairing i)
    (zero_le_one (α := ℝ))
  have hm : g.path.minPairing i = g.path.pairing i w :=
    le_antisymm (g.path.minPairing_le hw)
      (g.path.le_runningMin zero_le_one fun t ht ↦ hmin t ht)
  rw [hm]
  by_cases hw0 : w = 0
  · subst w
    exact ⟨0, by simp⟩
  by_cases hw1 : w = 1
  · subst w
    exact ⟨(P.cartanDatum hA).coroot i g.path.wt, g.path.pairing_one i⟩
  have hw' : w ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hw.1 (Ne.symm hw0), lt_of_le_of_ne hw.2 hw1⟩
  have hleft (t : ℝ) (ht : t ≤ g.s) :
      g.path.pairing i t = (σ.path hΛ).pairing i t := by
    change (glueRaw hΛ hΜ σ δ g.s g.s' t) (P.coroot i) = _
    rw [g.raw_left ht]
    rfl
  have hright (t : ℝ) (ht : (g.s' : ℝ) ≤ t) :
      g.path.pairing i t = (δ.path hΜ).pairing i t +
        (σ.path hΛ g.s - δ.path hΜ g.s') (P.coroot i) := by
    change (glueRaw hΛ hΜ σ δ g.s g.s' t) (P.coroot i) = _
    rw [g.raw_right ht, LinearMap.add_apply]
    rfl
  by_cases hws : w < g.s
  · rw [hleft w hws.le]
    apply (σ.isLS hΛ).exists_int_of_isMin hw' hw'.1 hws
    · intro t ht
      have hh := hmin t ⟨ht.1, ht.2.trans (hss.trans hs1.le)⟩
      simpa only [hleft w hws.le, hleft t ht.2] using hh
    · intro t ht
      have hh := hlt t ⟨ht.1, ht.2.trans (hss.trans hs1.le)⟩
      simpa only [hleft w hws.le, hleft t ht.2] using hh
  by_cases hws' : (g.s' : ℝ) < w
  · obtain ⟨z, hz⟩ := (δ.isLS hΜ).exists_int_of_isMin hw' hws' hw'.2
      (fun t ht ↦ by
        have hh := hmin t ⟨(hs0.le.trans hss).trans ht.1, ht.2⟩
        rw [hright w hws'.le, hright t ht.1] at hh
        exact (add_le_add_iff_right _).mp hh)
      (fun t ht ↦ by
        have hh := hlt t ht
        rw [hright w hws'.le, hright t (hws'.le.trans ht.1.le)] at hh
        exact (add_lt_add_iff_right _).mp hh)
    obtain ⟨k, hk⟩ := g.offset_integral i
    exact ⟨z + k, by rw [hright w hws'.le, hz, hk, Int.cast_add]⟩
  have hsw : (g.s : ℝ) ≤ w := le_of_not_gt hws
  have hws' : w ≤ (g.s' : ℝ) := le_of_not_gt hws'
  have heq : w = (g.s' : ℝ) := by
    by_contra hne
    have hh := hlt g.s' ⟨lt_of_le_of_ne hws' hne, hs1.le⟩
    have hp : g.path.pairing i w = g.path.pairing i g.s' := by
      simp only [pairing, g.path_pause ⟨hsw, hws'⟩, g.path_pause ⟨hss, le_rfl⟩]
    exact (ne_of_lt hh) hp
  subst w
  apply g.plateau_min_integral hs0 hs1
  · intro t ht
    have hp : g.path.pairing i g.s = g.path.pairing i g.s' := by
      simp only [pairing, g.path_pause ⟨le_rfl, hss⟩, g.path_pause ⟨hss, le_rfl⟩]
    rw [hp]
    exact hmin t ht
  · exact hlt

end GluingPair

end Matrix.Realization.LSGluing
