/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GeneralClassStability

/-!
# Arbitrary-integral-class LS bridge and finite gluing integrality

Source: P. Littelmann, *Paths and root operators in representation theory*,
Ann. Math. 142 (1995), §§4–5, pp. 509–515, source a-chains, Definition 5.3,
and Lemma 5.5. The scanned pages were inspected; proofs are reconstructed.
Neither class is assumed dominant or dominant-conjugate. Redundant subdivisions
are allowed. No gluing-class root-operator stability is asserted.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGeneralClass

open LSAChainBridge

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- Source position chains starting in the orbit lift to the integral-weight LS interface.
Orbit membership and integrality of every intermediate weight are derived. -/
theorem PositionChain.to_chain {Λ : P.integralWeights} {p x y : Dual ℝ H}
    (h : PositionChain P hA p x y)
    (hx : ∃ w : P.weylGroup hA, x = w.1 Λ) (hi : x ∈ P.integralWeights) :
    ∃ hy : y ∈ P.integralWeights,
      (lsData P hA Λ).Chain p ⟨x, hi⟩ ⟨y, hy⟩ ∧
      ∃ w : P.weylGroup hA, y = w.1 Λ := by
  induction h with
  | refl => exact ⟨hi, .refl, hx⟩
  | @tail y z _ hyz ih =>
    obtain ⟨hy, hc, v, hv⟩ := ih
    obtain ⟨c, hs, hint⟩ := hyz
    obtain ⟨u, hu⟩ := hs.1.eq_weyl
    have hz : z ∈ P.integralWeights := hs.1.integral_end hy
    have ho : ∃ w : P.weylGroup hA, z = w.1 Λ :=
      ⟨u * v, by rw [hu, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩
    exact ⟨hz, hc.tail ⟨c, ⟨⟨v, hv⟩, ho, hs⟩, hint⟩, ho⟩

/-- Exact Chain/PositionChain bridge, with the necessary initial-orbit premise.
A reflexive LS chain alone does not assert orbit membership. -/
theorem chain_iff_positionChain (Λ x y : P.integralWeights) (p : Dual ℝ H)
    (hx : ∃ w : P.weylGroup hA, (x : Dual ℝ H) = w.1 Λ) :
    (lsData P hA Λ).Chain p x y ↔ PositionChain P hA p x y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hs ih =>
      obtain ⟨c, hc, hint⟩ := hs
      exact ih.tail ⟨c, hc.2.2, hint⟩
  · intro h
    obtain ⟨hy, hc, -⟩ := h.to_chain hx x.property
    exact hc

/-- Source a-chains and LS position chains agree under the actual root-lattice
congruence, without a dominant representative. -/
theorem chain_iff_aChain (Λ x y : P.integralWeights) {p : Dual ℝ H} {a : ℝ}
    (hx : ∃ w : P.weylGroup hA, (x : Dual ℝ H) = w.1 Λ)
    (hq : p - a • (x : Dual ℝ H) ∈ rootLattice P) :
    (lsData P hA Λ).Chain p x y ↔ AChain P hA a x y := by
  rw [chain_iff_positionChain Λ x y p hx]
  exact ⟨fun h ↦ (h.to_aChain hq).1, fun h ↦ (h.to_positionChain hq).1⟩

/-- The arbitrary-integral source constructor satisfies the concrete LS condition.
Endpoint integrality was already derived by `ofAChains`, not assumed here. -/
theorem isLS_ofAChains {Λ : P.integralWeights} {n : ℕ}
    {a : Fin (n + 2) → ℚ} {x : Fin (n + 1) → P.integralWeights}
    (ha : StrictMono a) (ha0 : a 0 = 0) (ha1 : a (Fin.last (n + 1)) = 1)
    (hx : ∀ i, ∃ w : P.weylGroup hA, (x i : Dual ℝ H) = w.1 Λ)
    (hc : ∀ i : Fin n, AChain P hA (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) :
    IsLS (lsData P hA Λ) (ofAChains ha ha0 ha1 hc) := by
  apply (isLS_rationalPieces_iff ha ha0 ha1 hx
    (ofAChains_piece ha ha0 ha1 hc)).mpr
  intro i
  apply (chain_iff_positionChain Λ _ _ _ (hx i.castSucc)).mpr
  apply ((hc i).to_positionChain ?_).1
  have hi := cumulative_congruences ha0 hc i.castSucc
  convert hi using 1
  rw [Fin.castSucc_succ, finitePiecePosition_succ]
  simp only [pathSpace_embed, sub_smul]
  abel

/-- The finite source presentation is an LS path in its genuine initial orbit. -/
theorem Presentation.isLS (σ : Presentation P hA) :
    IsLS (lsData P hA (σ.x 0)) σ.path :=
  isLS_ofAChains σ.mono σ.zero σ.one σ.orbit σ.chains

namespace Presentation

variable (σ : Presentation P hA)

/-- Every finite mixed root-operator descendant stays LS in the genuine initial
orbit. This concerns a single source presentation, not a two-class gluing pair. -/
theorem component_isLS : ∀ η ∈ σ.path.component,
    IsLS (lsData P hA (σ.x 0)) η :=
  Crystal.closure_subset (isStable_setOf_isLS (lsData P hA (σ.x 0)))
    (singleton_subset_iff.mpr σ.isLS)

/-- The whole component of any finite arbitrary-integral-class source path has
integral simple-coroot global minima. No component-integrality premise is supplied. -/
theorem component_isIntegral : ∀ η ∈ σ.path.component, η.IsIntegral := by
  intro η hη i
  exact (σ.component_isLS η hη).exists_int_minPairing i

/-- The affine formula on every closed piece. -/
theorem piece (j : Fin (σ.n + 1)) (t : ℝ)
    (ht : t ∈ Icc (σ.a j.castSucc : ℝ) (σ.a j.succ : ℝ)) :
    σ.path t = finitePiecePosition (P.pathSpace hA) σ.a σ.x j.castSucc +
      (t - (σ.a j.castSucc : ℝ)) • (σ.x j : Dual ℝ H) :=
  ofAChains_piece σ.mono σ.zero σ.one σ.chains j t ht

/-- At any time in a piece the incoming root-lattice invariant still holds. -/
theorem congruence (j : Fin (σ.n + 1)) (t : ℝ)
    (ht : t ∈ Icc (σ.a j.castSucc : ℝ) (σ.a j.succ : ℝ)) :
    σ.path t - t • (σ.x j : Dual ℝ H) ∈ rootLattice P := by
  rw [σ.piece j t ht]
  convert cumulative_congruences σ.zero σ.chains j using 1
  rw [sub_smul t (σ.a j.castSucc : ℝ) (σ.x j : Dual ℝ H)]
  abel

/-- On the first piece, the path is exactly the initial straight line. -/
theorem first_piece (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (σ.a (0 : Fin (σ.n + 1)).succ : ℝ)) :
    σ.path t = t • (σ.x 0 : Dual ℝ H) := by
  simpa [σ.zero] using σ.piece 0 t (by simpa [σ.zero] using ht)


end Presentation

variable (σ δ : Presentation P hA)

/-- Definition 5.3 for two arbitrary integral classes. The actual cut chains,
positive-root compatibility and integral endpoint are the only gluing premises. -/
structure GluingPair where
  s : ℚ
  s' : ℚ
  pos : 0 < s
  le : s ≤ s'
  lt_one : s' < 1
  last_lt : σ.a (Fin.last σ.n).castSucc < s
  first_gt : s' < δ.a (0 : Fin (δ.n + 1)).succ
  ν : Dual ℝ H
  μ : Dual ℝ H
  left_chain : AChain P hA (s : ℝ) (σ.x (Fin.last σ.n)) ν
  right_chain : AChain P hA (s' : ℝ) μ (δ.x 0)
  precedes : P.GluingPrecedes hA ν μ
  endpoint : glueRaw σ δ s s' 1 ∈ P.integralWeights

namespace GluingPair

variable {σ δ} (g : GluingPair σ δ)

/-- The left cut direction lies in the first class, derived from its source chain. -/
theorem left_orbit : ∃ w : P.weylGroup hA, g.ν = w.1 (σ.x 0) := by
  obtain ⟨u, hu⟩ := g.left_chain.eq_weyl
  obtain ⟨v, hv⟩ := σ.orbit (Fin.last σ.n)
  exact ⟨u * v, by rw [hu, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩

/-- The reversed endpoint role of the right cut still forces the actual second
orbit. No second-class orbit or dominance witness is a gluing-pair field. -/
theorem right_orbit : ∃ w : P.weylGroup hA, g.μ = w.1 (δ.x 0) := by
  obtain ⟨u, hu⟩ := g.right_chain.eq_weyl
  refine ⟨u⁻¹, ?_⟩
  rw [hu]
  change g.μ = u.1.symm (u.1 g.μ)
  simp

/-- The unchanged initial portion of the glued path. -/
theorem raw_left {t : ℝ} (ht : t ≤ g.s) :
    glueRaw σ δ g.s g.s' t = σ.path t := by
  have hle : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  simp [glueRaw, min_eq_left ht, max_eq_right (ht.trans hle)]

/-- The glue is genuinely paused on the whole closed interval, including `s = s'`. -/
theorem raw_pause {t : ℝ} (ht : t ∈ Icc (g.s : ℝ) (g.s' : ℝ)) :
    glueRaw σ δ g.s g.s' t = σ.path g.s := by
  simp [glueRaw, min_eq_right ht.1, max_eq_right ht.2]

/-- The translated final portion, with the source's endpoint-preserving offset. -/
theorem raw_right {t : ℝ} (ht : (g.s' : ℝ) ≤ t) :
    glueRaw σ δ g.s g.s' t =
      δ.path t + (σ.path g.s - δ.path g.s') := by
  have hle : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  rw [glueRaw, min_eq_right (hle.trans ht), max_eq_left ht]
  abel

/-- An actual path, constructed rather than assumed; rational PL is given by the
finite clipped sums in `raw_formula` and the three literal gluing identities. -/
noncomputable def path : LittelmannPath (P.pathSpace hA) where
  toFun := glueRaw σ δ g.s g.s'
  wt := ⟨glueRaw σ δ g.s g.s' 1, g.endpoint⟩
  toFun_of_nonpos' := by
    intro t ht
    have hs : (0 : ℝ) < g.s := by exact_mod_cast g.pos
    rw [g.raw_left (ht.trans hs.le), (σ.path).apply_of_nonpos ht]
  toFun_of_one_le' := by
    intro t ht
    have hs : (g.s' : ℝ) ≤ 1 := by exact_mod_cast g.lt_one.le
    change glueRaw σ δ g.s g.s' t = glueRaw σ δ g.s g.s' 1
    rw [g.raw_right (hs.trans ht), g.raw_right hs,
      (δ.path).apply_of_one_le ht, (δ.path).apply_one]
  continuous_coroot' := by
    intro i
    simp only [glueRaw, map_sub, map_add]
    exact (((σ.path).continuous_pairing i).comp
      (continuous_id.min continuous_const)).add
      (((δ.path).continuous_pairing i).comp
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
    g.path t = σ.path g.s := g.raw_pause ht

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

/-- The translation between the two cuts is an integral weight, derived from
`η(1) ∈ X` and `δ(1) ∈ X`, not assumed at the seam. -/
theorem offset_integral : σ.path g.s - δ.path g.s' ∈ P.integralWeights := by
  have hs : (g.s' : ℝ) ≤ 1 := by exact_mod_cast g.lt_one.le
  have he := g.endpoint
  rw [g.raw_right hs] at he
  have hd := (δ.path).wt.property
  change δ.path 1 ∈ P.integralWeights at hd
  simpa only [add_sub_cancel_left] using P.integralWeights.sub_mem he hd

/-- Lemma 5.5's seam argument for arbitrary classes, using the production
source-chain theorem rather than any dominant-class LS data. -/
theorem cut_height_integral {i : ι}
    (hleft : (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) < 0)
    (hright : 0 < (δ.x 0 : Dual ℝ H) (P.coroot i)) :
    ∃ z : ℤ, (σ.path g.s) (P.coroot i) = z :=
  finite_seam_integral σ δ g.le g.lt_one g.left_cut_mem g.right_cut_mem
    g.left_chain g.right_chain g.precedes g.endpoint hleft hright


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
    ∃ z : ℤ, (σ.path g.s) (P.coroot i) = z := by
  have h := rootLattice_le_integralWeights
    (σ.congruence _ _ g.left_cut_mem) i
  simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hz,
    mul_zero, sub_zero] using h

/-- The weak incoming-slope variant needed when a minimum extends backwards. -/
theorem cut_height_integral_of_nonpos {i : ι}
    (hleft : (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) ≤ 0)
    (hright : 0 < (δ.x 0 : Dual ℝ H) (P.coroot i)) :
    ∃ z : ℤ, (σ.path g.s) (P.coroot i) = z := by
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
  change glueRaw σ δ g.s g.s' t =
    glueRaw σ δ g.s g.s' g.s + _
  rw [g.raw_left ht.2, g.raw_left le_rfl, σ.piece _ _ ht',
    σ.piece _ _ g.left_cut_mem, pathSpace_embed]
  module

/-- The glued path has the actual first outgoing direction at its right cut. -/
theorem right_direction : g.path.HasRightDir g.s' (δ.x 0) := by
  have hs : (g.s' : ℝ) < δ.a (0 : Fin (δ.n + 1)).succ := by exact_mod_cast g.first_gt
  refine ⟨(δ.a (0 : Fin (δ.n + 1)).succ : ℝ) - g.s', sub_pos.mpr hs, ?_⟩
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) (δ.a (0 : Fin (δ.n + 1)).succ : ℝ) :=
    ⟨g.right_cut_mem.1.trans ht.1, by linarith [ht.2]⟩
  change glueRaw σ δ g.s g.s' t =
    glueRaw σ δ g.s g.s' g.s' + _
  rw [g.raw_right ht.1, g.raw_right le_rfl, δ.first_piece _ ht',
    δ.first_piece _ g.right_cut_mem, pathSpace_embed]
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
      g.path.pairing i t = (σ.path).pairing i t := by
    change (glueRaw σ δ g.s g.s' t) (P.coroot i) = _
    rw [g.raw_left ht]
    rfl
  have hright (t : ℝ) (ht : (g.s' : ℝ) ≤ t) :
      g.path.pairing i t = (δ.path).pairing i t +
        (σ.path g.s - δ.path g.s') (P.coroot i) := by
    change (glueRaw σ δ g.s g.s' t) (P.coroot i) = _
    rw [g.raw_right ht, LinearMap.add_apply]
    rfl
  by_cases hws : w < g.s
  · rw [hleft w hws.le]
    apply σ.isLS.exists_int_of_isMin hw' hw'.1 hws
    · intro t ht
      have hh := hmin t ⟨ht.1, ht.2.trans (hss.trans hs1.le)⟩
      simpa only [hleft w hws.le, hleft t ht.2] using hh
    · intro t ht
      have hh := hlt t ⟨ht.1, ht.2.trans (hss.trans hs1.le)⟩
      simpa only [hleft w hws.le, hleft t ht.2] using hh
  by_cases hws' : (g.s' : ℝ) < w
  · obtain ⟨z, hz⟩ := δ.isLS.exists_int_of_isMin hw' hws' hw'.2
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

end Matrix.Realization.LSGeneralClass
