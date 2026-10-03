/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingSeams

/-!
# Positive-auxiliary equality-seam reconstruction

## Main results

The last-minimum right equality seam admits simultaneous auxiliary reflection.
The source incoming sign and the same-cut chains are derived, including zero auxiliary
left pairing. The strict output uses the actual source power and a distinct coarsening.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), Definition 5.3 and Proposition 5.6, pp. 514–516. Proofs reconstructed in the literal
finite-source encoding.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- At integral height, both positive chain endpoints can be reflected at the SAME position. -/
theorem PositionChain.reflect_integral_pos {p x y : Dual ℝ H} {i : ι}
    (h : PositionChain P hA p x y) (hint : x ∈ P.integralWeights)
    (hp : ∃ z : ℤ, p (P.coroot i) = z)
    (hx : 0 < x (P.coroot i)) (hy : 0 < y (P.coroot i)) :
    PositionChain P hA p (P.reflection hA i x) (P.reflection hA i y) := by
  let X : P.integralWeights := ⟨x, hint⟩
  have hxO : ∃ w : P.weylGroup hA, x = w.1 X := ⟨1, by simp [X]⟩
  obtain ⟨hi, hc, -⟩ := h.to_chain hxO hint
  let Y : P.integralWeights := ⟨y, hi⟩
  have hxc : 0 < (P.cartanDatum hA).coroot i X :=
    coroot_cartanDatum_pos_iff.mpr hx
  have hyc : 0 < (P.cartanDatum hA).coroot i Y :=
    coroot_cartanDatum_pos_iff.mpr hy
  have hnew := (hc.reflection (i := i) hp hxO).1 hxc hyc
  have hxo := (lsData P hA X).reflection_mem i X hxO
  have hh := (chain_iff_positionChain X ((P.cartanDatum hA).reflection i X)
    ((P.cartanDatum hA).reflection i Y) p hxo).mp hnew
  simpa only [coe_reflection_cartanDatum] using hh

/-- Simultaneous reflection keeps the original time parameter at integral source height. -/
theorem AChain.reflect_integral_pos {a : ℝ} {x y : Dual ℝ H} {i : ι}
    (h : AChain P hA a x y) (hint : x ∈ P.integralWeights)
    (hp : ∃ z : ℤ, (a • x) (P.coroot i) = z)
    (hx : 0 < x (P.coroot i)) (hy : 0 < y (P.coroot i)) :
    AChain P hA a (P.reflection hA i x) (P.reflection hA i y) := by
  classical
  have hn := (h.to_positionChain (p := a • x) (by simp)).1.reflect_integral_pos
    hint hp hx hy
  apply (hn.to_aChain ?_).1
  obtain ⟨z, hz⟩ := hp
  refine ⟨z • Pi.single i 1, ?_⟩
  simp only [LinearMap.smul_apply, smul_eq_mul] at hz
  rw [map_zsmul, P.rootOf_single, ← Int.cast_smul_eq_zsmul ℝ,
    reflection_apply, smul_sub, smul_smul, hz]
  module

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- The positive-auxiliary equality sector's indispensable same-cut chains and compatibility.
The incoming source sign follows from the actual minimum, not an extra slope hypothesis.
The zero left-auxiliary pairing is treated by its reflection fixed-point identity. -/
theorem reflect_pos_at_last_minimum {i : ι}
    (hum : g.path.pairing i g.s' = g.path.minPairing i)
    (hlast : ∀ t ∈ Ioc (g.s' : ℝ) 1, g.path.minPairing i < g.path.pairing i t)
    (hμ : 0 < g.μ (P.coroot i)) :
    (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) ≤ 0 ∧
    0 ≤ g.ν (P.coroot i) ∧ 0 < (δ.x 0 : Dual ℝ H) (P.coroot i) ∧
    AChain P hA (g.s : ℝ) (σ.x (Fin.last σ.n)) (P.reflection hA i g.ν) ∧
    AChain P hA (g.s' : ℝ) (P.reflection hA i g.μ)
      (P.reflection hA i (δ.x 0)) ∧
    P.GluingPrecedes hA (P.reflection hA i g.ν) (P.reflection hA i g.μ) := by
  have hs0 : (0 : ℝ) < g.s := by exact_mod_cast g.pos
  have hs1 : (g.s' : ℝ) < 1 := by exact_mod_cast g.lt_one
  have hss : (g.s : ℝ) ≤ g.s' := by exact_mod_cast g.le
  have hm : g.path.pairing i g.s = g.path.minPairing i := by
    rw [← hum]
    simp only [pairing, pathSpace_coroot, g.path_pause ⟨le_rfl, hss⟩,
      g.path_pause ⟨hss, le_rfl⟩]
  have hxc := g.left_direction.coroot_nonpos hs0 (i := i) (fun t ht ↦ by
    rw [hm]
    exact g.path.minPairing_le ⟨by linarith [ht.1], ht.2.le.trans (hss.trans hs1.le)⟩)
  have hx : (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) ≤ 0 := by
    rw [← coroot_cartanDatum_cast P hA]
    exact_mod_cast hxc
  have hy : 0 < (δ.x 0 : Dual ℝ H) (P.coroot i) := by
    apply coroot_cartanDatum_pos_iff.mp
    exact g.right_direction.coroot_pos (sub_pos.mpr hs1) (i := i) (fun t ht ↦ by
      rw [hum]
      exact hlast t ⟨ht.1, by linarith [ht.2]⟩)
  have hν : 0 ≤ g.ν (P.coroot i) := by
    by_contra hn
    exact (not_le_of_gt hμ) (g.precedes.simple (lt_of_not_ge hn))
  have hp : ∃ z : ℤ, (σ.path g.s) (P.coroot i) = z := by
    obtain ⟨z, hz⟩ := g.isIntegral i
    refine ⟨z, ?_⟩
    have hh := hum.trans hz
    simpa only [pairing, pathSpace_coroot, g.path_pause ⟨hss, le_rfl⟩] using hh
  have hleft : AChain P hA (g.s : ℝ) (σ.x (Fin.last σ.n))
      (P.reflection hA i g.ν) := by
    rcases eq_or_lt_of_le hν with hz | hpos
    · have heq : P.reflection hA i g.ν = g.ν := by
        rw [reflection_apply, ← hz, zero_smul, sub_zero]
      rw [heq]
      exact g.left_chain
    · have hq := σ.congruence (Fin.last σ.n) g.s g.left_cut_mem
      have hn := (g.left_chain.to_positionChain hq).1.reflect_integral_target
        (σ.x (Fin.last σ.n)).property hp hx hpos
      exact (hn.to_aChain hq).1
  have hpδ : ∃ z : ℤ, (δ.path g.s') (P.coroot i) = z := by
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := g.offset_integral i
    simp only [LinearMap.sub_apply] at hb
    refine ⟨a - b, ?_⟩
    push_cast
    linarith
  have hpμ : ∃ z : ℤ, ((g.s' : ℝ) • g.μ) (P.coroot i) = z := by
    have hq := (g.right_chain.to_positionChain
      (p := (g.s' : ℝ) • g.μ) (by simp)).2
    obtain ⟨a, ha⟩ := LSAChainBridge.rootLattice_le_integralWeights hq i
    obtain ⟨b, hb⟩ := hpδ
    rw [δ.first_piece g.s' g.right_cut_mem] at hb
    simp only [LinearMap.sub_apply] at ha
    refine ⟨a + b, ?_⟩
    push_cast
    linarith
  exact ⟨hx, hν, hy, hleft,
    g.right_chain.reflect_integral_pos g.right_direction_integral hpμ hμ hy,
    (g.precedes.reflection_iff i).mpr (fun _ ↦ hμ.le)⟩

/-- The positive-auxiliary equality case of Proposition 5.6, p.515. Both auxiliaries
are simultaneously reflected; the left source and cuts remain unchanged. The actual
source operator string and its strict coarsening are explicitly distinguished. -/
theorem exists_f_gluing_at_cut_of_pos {i : ι}
    (hum : g.path.pairing i g.s' = g.path.minPairing i)
    (hlast : ∀ t ∈ Ioc (g.s' : ℝ) 1, g.path.minPairing i < g.path.pairing i t)
    (hμ : 0 < g.μ (P.coroot i))
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    ∃ (k : ℕ) (υ τ : Presentation P hA) (g' : GluingPair σ τ),
      δ.path.pairing i g.s' = δ.path.minPairing i + k ∧
      (LittelmannPath.crystal (P.pathSpace hA)).fIter i (k + 1) δ.path = some υ.path ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i (k + 1) υ.path = some δ.path ∧
      (∀ t : ℝ, (g.s' : ℝ) ≤ t →
        τ.path t - τ.path g.s' = υ.path t - υ.path g.s') ∧
      (τ.x 0 : Dual ℝ H) = P.reflection hA i (δ.x 0) ∧ g'.path = η ∧
      g'.s = g.s ∧ g'.s' = g.s' ∧ g'.ν = P.reflection hA i g.ν ∧
      g'.μ = P.reflection hA i g.μ ∧
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
  obtain ⟨-, -, -, hleft, hright, hcompat⟩ :=
    g.reflect_pos_at_last_minimum hum hlast hμ
  let g' : GluingPair σ τ :=
    { s := g.s
      s' := g.s'
      pos := g.pos
      le := g.le
      lt_one := g.lt_one
      last_lt := g.last_lt
      first_gt := hfirst
      ν := P.reflection hA i g.ν
      μ := P.reflection hA i g.μ
      left_chain := hleft
      right_chain := by rw [hx]; exact hright
      precedes := hcompat
      endpoint := by rw [hout 1, η.apply_one]; exact η.wt.property }
  refine ⟨k, υ, τ, g', hk, hυ, heυ, htail, hx, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · apply LittelmannPath.ext_of_eqOn
    intro t _
    exact hout t
  · intro j
    obtain ⟨w, hw⟩ := hoτ j
    obtain ⟨z, hz⟩ := hoυ 0
    exact ⟨w * z, by rw [hw, hz, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩

/-- All-root global-minimum integrality for the actual positive-auxiliary
right equality-seam lowering output, not only integrality of the operated root. -/
theorem f_isIntegral_at_cut_of_pos {i : ι}
    (hum : g.path.pairing i g.s' = g.path.minPairing i)
    (hlast : ∀ t ∈ Ioc (g.s' : ℝ) 1, g.path.minPairing i < g.path.pairing i t)
    (hμ : 0 < g.μ (P.coroot i))
    {η : LittelmannPath (P.pathSpace hA)} (hf : LittelmannPath.f i g.path = some η) :
    η.IsIntegral := by
  obtain ⟨k, υ, τ, g', -, -, -, -, -, hp, -⟩ :=
    g.exists_f_gluing_at_cut_of_pos hum hlast hμ hf
  rw [← hp]
  exact g'.isIntegral

end GluingPair
end Matrix.Realization.LSGeneralClass
