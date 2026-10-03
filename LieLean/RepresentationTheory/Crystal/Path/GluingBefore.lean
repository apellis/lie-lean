/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingAfter

/-!
# Source reversal and actual strict-before raising outputs

## Main results

`Presentation.reverse` reverses the actual source saturated chains at complementary
rational times, and `Presentation.reverse_path` identifies the actual reversed path.
`GluingPair.reverse` reverses a strict gluing pair without relaxing either strict cut.
`Presentation.exists_eIter_presentation` reconstructs arbitrary successful source raising
iterates in the original orbit, with no dominance premise.
`GluingPair.exists_eIter_gluing_before` constructs actual strict-before raising outputs
in the source-minimum-matched sector. `exists_eIter_gluing_before_of_nonneg` derives
matching from an ACTUAL early glued minimizer and nonnegative final source slope.
The left source uses the SAME exponent; the right source, cuts and auxiliary directions
remain unchanged. `eIter_isIntegral_before_of_nonneg` proves output integrality for all roots.

Positive-outgoing strict-after and negative-terminal strict-before normalization,
equality/crossing seams, coarsening and mixed-word stability remain open.
This does not assert full Proposition 5.6 or the component isomorphism theorem.

## References

Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142 (1995),
pp. 515–516, Proposition 5.6. Proofs are reconstructed.
Neither source class is assumed dominant. Strict source monotonicity is never imposed
across the artificial glued pause, and no Remark 5.4 equality-cut presentation is
used as a strict same-cut gluing pair.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- The coroot in a source step has opposite values at its endpoints. -/
theorem RootStep.coroot_neg_end {x y : Dual ℝ H} {c : Dual ℝ (Dual ℝ H)}
    (h : RootStep P hA x y c) : c (-y) = c x := by
  classical
  obtain ⟨u, j, hp, rfl, hn, hy⟩ := h
  have htwo : LSAChainBridgeRoots.rootCoroot P hA u j (u.1 (P.root j)) = 2 := by
    change (u⁻¹).1 (u.1 (P.root j)) (P.coroot j) = 2
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
    exact P.root_coroot_self hA j
  rw [map_neg, hy, map_sub, map_smul, htwo, smul_eq_mul]
  ring

/-- Complementary-time reversal of actual saturated source chains. Integrality
of the source weights, not dominance, supplies the complementary time condition. -/
theorem AChain.neg_reverse_complement {x y : Dual ℝ H} {a : ℝ}
    (h : AChain P hA a x y) (hx : x ∈ P.integralWeights) :
    AChain P hA (1 - a) (-y) (-x) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head x v hs _ ih =>
    obtain ⟨c, hc, z, hz⟩ := hs
    have hv := hc.1.integral_end hx
    obtain ⟨k, hk⟩ := hc.1.integral_weight ⟨x, hx⟩
    refine (ih hv).tail ⟨c, hc.neg_reverse, k - z, ?_⟩
    rw [hc.1.coroot_neg_end]
    push_cast
    change (1 - a) * c x = (k : ℝ) - z
    change c x = (k : ℝ) at hk
    rw [sub_mul, one_mul, hz, hk]

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

namespace Presentation

/-- Finite source reversal, with literal complementary rational breakpoints. -/
noncomputable def reverse (σ : Presentation P hA) : Presentation P hA where
  n := σ.n
  a j := 1 - σ.a j.rev
  x j := -σ.x j.rev
  mono := by
    intro j k hjk
    exact sub_lt_sub_left (σ.mono (Fin.rev_lt_rev.mpr hjk)) 1
  zero := by simp [σ.one]
  one := by simp [σ.zero]
  chains j := by
    have h := (σ.chains j.rev).neg_reverse_complement (σ.x j.rev.castSucc).property
    simpa only [Fin.rev_castSucc, Fin.rev_succ, Rat.cast_sub, Rat.cast_one,
      Fin.castSucc_succ, AddSubgroup.coe_neg] using h

/-- The reversed finite source is the actual reversed path, at all real times. -/
theorem reverse_path (σ : Presentation P hA) : σ.reverse.path = σ.path.rev := by
  let τ := σ.reverse
  have hshape (j : Fin (σ.n + 1)) (t : ℝ)
      (ht : t ∈ Icc (τ.a j.castSucc : ℝ) (τ.a j.succ : ℝ)) :
      σ.path.rev t = σ.path.rev (τ.a j.castSucc : ℝ) +
        (t - (τ.a j.castSucc : ℝ)) • (τ.x j : Dual ℝ H) := by
    have hmem : 1 - t ∈ Icc (σ.a j.rev.castSucc : ℝ) (σ.a j.rev.succ : ℝ) := by
      dsimp [τ, reverse] at ht
      simp only [Fin.rev_castSucc, Fin.rev_succ, Rat.cast_sub, Rat.cast_one] at ht
      constructor <;> linarith [ht.1, ht.2]
    have hle : (σ.a j.rev.castSucc : ℝ) ≤ σ.a j.rev.succ := by
      exact_mod_cast (σ.mono Fin.castSucc_lt_succ).le
    simp only [rev_apply]
    rw [σ.piece j.rev _ hmem]
    have heq : 1 - (τ.a j.castSucc : ℝ) = σ.a j.rev.succ := by
      simp [τ, reverse, Fin.rev_castSucc]
    rw [heq, σ.piece j.rev _ ⟨hle, le_rfl⟩]
    simp only [τ, reverse, AddSubgroup.coe_neg, smul_neg]
    push_cast
    simp only [Fin.rev_castSucc]
    module
  have hshape' (j : Fin (τ.n + 1)) (t : ℝ)
      (ht : t ∈ Icc (τ.a j.castSucc : ℝ) (τ.a j.succ : ℝ)) := hshape j t ht
  have heq : ∀ j : Fin (τ.n + 2), τ.path (τ.a j : ℝ) = σ.path.rev (τ.a j : ℝ) := by
    intro j
    induction j using Fin.induction with
    | zero => simp [τ.zero]
    | succ j ih =>
      have hmem : (τ.a j.succ : ℝ) ∈ Icc (τ.a j.castSucc : ℝ) (τ.a j.succ : ℝ) :=
        ⟨by exact_mod_cast (τ.mono Fin.castSucc_lt_succ).le, le_rfl⟩
      have hstart := τ.piece j (τ.a j.castSucc : ℝ) ⟨le_rfl, hmem.1⟩
      simp only [sub_self, zero_smul, add_zero] at hstart
      rw [τ.piece j _ hmem, ← hstart, ih, hshape' j _ hmem]
      rfl
  apply LittelmannPath.ext_of_eqOn
  intro t ht
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · obtain ⟨j, hj⟩ := finite_interval (fun j ↦ (τ.a j : ℝ))
      (by simpa [τ.zero, τ.one] using And.intro ht.1 hlt)
    have hstart := τ.piece j (τ.a j.castSucc : ℝ) ⟨le_rfl, hj.1.trans hj.2.le⟩
    simp only [sub_self, zero_smul, add_zero] at hstart
    rw [τ.piece j t ⟨hj.1, hj.2.le⟩, ← hstart, heq, hshape' j t ⟨hj.1, hj.2.le⟩]
    rfl
  · simpa [τ.one] using heq (Fin.last (τ.n + 1))

/-- Reversing a finite presentation twice is literally the original presentation. -/
@[simp] theorem reverse_reverse (σ : Presentation P hA) : σ.reverse.reverse = σ := by
  cases σ
  simp only [reverse, Fin.rev_rev, sub_sub_cancel, neg_neg]

end Presentation

/-- Source compatibility is preserved by negation and reversal of the two directions. -/
theorem gluingPrecedes_neg_reverse {ν μ : Dual ℝ H} (h : P.GluingPrecedes hA ν μ) :
    P.GluingPrecedes hA (-μ) (-ν) := by
  intro u j hp hμ
  simp only [map_neg] at hμ ⊢
  by_contra hn
  have hν : LSAChainBridgeRoots.rootCoroot P hA u j ν < 0 := by linarith
  have := h u j hp hν
  linarith

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- Literal reversal of the raw gluing formula, with complementary cuts. -/
theorem reverse_raw (t : ℝ) :
    glueRaw δ.reverse σ.reverse (1 - g.s') (1 - g.s) t =
      g.path.rev t := by
  have hmin : 1 - min t (1 - (g.s' : ℝ)) = max (1 - t) (g.s' : ℝ) := by
    rcases le_total t (1 - (g.s' : ℝ)) with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]
    · rw [min_eq_right h, max_eq_right (by linarith)]
      ring
  have hmax : 1 - max t (1 - (g.s : ℝ)) = min (1 - t) (g.s : ℝ) := by
    rcases le_total t (1 - (g.s : ℝ)) with h | h
    · rw [max_eq_right h, min_eq_right (by linarith)]
      ring
    · rw [max_eq_left h, min_eq_left (by linarith)]
  rw [rev_apply]
  change _ = glueRaw σ δ g.s g.s' (1 - t) - glueRaw σ δ g.s g.s' 1
  rw [g.raw_right (t := 1) (by exact_mod_cast g.lt_one.le)]
  simp only [glueRaw, Presentation.reverse_path, rev_apply, Rat.cast_sub, Rat.cast_one,
    hmin, hmax, sub_sub_cancel]
  abel

/-- A genuine strict gluing pair for the reversed path; both source chains are
reversed at complementary times, not weakened to auxiliary equality-cut presentations. -/
noncomputable def reverse : GluingPair δ.reverse σ.reverse where
  s := 1 - g.s'
  s' := 1 - g.s
  pos := by linarith [g.lt_one]
  le := by linarith [g.le]
  lt_one := by linarith [g.pos]
  last_lt := by
    simpa only [Presentation.reverse, Fin.rev_castSucc, Fin.rev_last] using
      sub_lt_sub_left g.first_gt 1
  first_gt := by
    change 1 - g.s < 1 - σ.a ((0 : Fin (σ.n + 1)).succ.rev)
    simpa only [Presentation.reverse, Fin.rev_succ, Fin.rev_zero] using
      sub_lt_sub_left g.last_lt 1
  ν := -g.μ
  μ := -g.ν
  left_chain := by
    have h := g.right_chain.neg_reverse_complement g.right_direction_integral
    simpa only [Presentation.reverse, Fin.rev_last, Rat.cast_sub, Rat.cast_one,
      AddSubgroup.coe_neg] using h
  right_chain := by
    change AChain P hA ((1 - g.s : ℚ) : ℝ) (-g.ν)
      ((-σ.x (0 : Fin (σ.n + 1)).rev : P.integralWeights) : Dual ℝ H)
    have h := g.left_chain.neg_reverse_complement (σ.x (Fin.last σ.n)).property
    simpa only [Presentation.reverse, Fin.rev_zero, Rat.cast_sub, Rat.cast_one,
      AddSubgroup.coe_neg] using h
  precedes := gluingPrecedes_neg_reverse g.precedes
  endpoint := by
    rw [g.reverse_raw, g.path.rev.apply_one]
    exact g.path.rev.wt.property

/-- Reversal commutes exactly with the constructed strict gluing path. -/
theorem reverse_path : g.reverse.path = g.path.rev := by
  apply LittelmannPath.ext_of_eqOn
  intro t _
  exact g.reverse_raw t

end GluingPair

/-- Time reversal exchanges successful iterated raising and lowering, with the
same exponent. This uses the actual operators, including their failure values. -/
theorem fIter_rev_eq_map_eIter (i : ι) (n : ℕ)
    (π : LittelmannPath (P.pathSpace hA)) :
    (LittelmannPath.crystal (P.pathSpace hA)).fIter i n π.rev =
      ((LittelmannPath.crystal (P.pathSpace hA)).eIter i n π).map LittelmannPath.rev := by
  induction n generalizing π with
  | zero => rfl
  | succ n ih =>
    rw [Crystal.fIter_succ, Crystal.eIter_succ, crystal_f, crystal_e, f_rev]
    cases he : LittelmannPath.e i π with
    | none => simp
    | some ζ => simpa using ih ζ

namespace Presentation

/-- Actual finite raising reconstruction for arbitrary integral classes and arbitrary
same-root exponents. Reversal transports the existing finite source lowering construction;
no output presentation or closure premise is supplied. -/
theorem exists_eIter_presentation (σ : Presentation P hA) (i : ι) (n : ℕ)
    {η : LittelmannPath (P.pathSpace hA)}
    (he : (LittelmannPath.crystal (P.pathSpace hA)).eIter i n σ.path = some η) :
    ∃ τ : Presentation P hA, τ.path = η ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  have hf : (LittelmannPath.crystal (P.pathSpace hA)).fIter i n σ.reverse.path =
      some η.rev := by
    rw [reverse_path, fIter_rev_eq_map_eIter, he, Option.map_some]
  obtain ⟨τ, hτ, -, horbit⟩ := σ.reverse.exists_fIter_presentation i n hf
  refine ⟨τ.reverse, ?_, ?_⟩
  · rw [reverse_path, hτ, rev_rev]
  · intro j
    obtain ⟨u, hu⟩ := horbit j.rev
    obtain ⟨v, hv⟩ := σ.orbit (Fin.last σ.n)
    refine ⟨u * v, ?_⟩
    change -(τ.x j.rev : Dual ℝ H) = (u * v).1 (σ.x 0)
    rw [hu]
    change -u.1 (-(σ.x (0 : Fin (σ.n + 1)).rev : Dual ℝ H)) = _
    rw [Fin.rev_zero, map_neg, neg_neg, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]

/-- A successful actual source raising operator has a finite presentation in its
original orbit, without dominance. -/
theorem exists_e_presentation (σ : Presentation P hA)
    {i : ι} {η : LittelmannPath (P.pathSpace hA)}
    (he : LittelmannPath.e i σ.path = some η) :
    ∃ τ : Presentation P hA, τ.path = η ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) :=
  σ.exists_eIter_presentation i 1 (by simpa using he)

end Presentation

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- The source-minimum-matched strict-before raising sector of Proposition 5.6.
Actual same-exponent output witnesses preserve the right source, cuts, auxiliary
directions and original left orbit. Neither slope signs nor dominance are assumed. -/
theorem exists_eIter_gluing_before (i : ι) (n : ℕ)
    (hearly : ∃ u ∈ Ico (0 : ℝ) g.s, σ.path.pairing i u = σ.path.minPairing i)
    (hright : ∀ t ∈ Icc (g.s' : ℝ) 1, σ.path.minPairing i ≤ g.path.pairing i t)
    {η : LittelmannPath (P.pathSpace hA)}
    (he : (LittelmannPath.crystal (P.pathSpace hA)).eIter i n g.path = some η) :
    ∃ (τ : Presentation P hA) (g' : GluingPair τ δ),
      g'.path = η ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i n σ.path = some τ.path ∧
      g'.s = g.s ∧ g'.s' = g.s' ∧ g'.ν = g.ν ∧ g'.μ = g.μ ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  have hlate : ∃ u ∈ Ioc (g.reverse.s' : ℝ) 1,
      σ.reverse.path.pairing i u = σ.reverse.path.minPairing i := by
    obtain ⟨u, hu, hum⟩ := hearly
    refine ⟨1 - u, ⟨?_, by linarith [hu.1]⟩, ?_⟩
    · change ((1 - g.s : ℚ) : ℝ) < 1 - u
      push_cast
      linarith [hu.2]
    · rw [Presentation.reverse_path, pairing_rev, minPairing_rev, sub_sub_cancel, hum]
  have hleft : ∀ t ∈ Icc (0 : ℝ) g.reverse.s,
      σ.reverse.path.minPairing i +
        (δ.reverse.path g.reverse.s - σ.reverse.path g.reverse.s') (P.coroot i) ≤
          δ.reverse.path.pairing i t := by
    intro t ht
    have ht' : 1 - t ∈ Icc (g.s' : ℝ) 1 := by
      change 0 ≤ t ∧ t ≤ ((1 - g.s' : ℚ) : ℝ) at ht
      push_cast at ht
      constructor <;> linarith [ht.1, ht.2]
    have hh := hright (1 - t) ht'
    change σ.path.minPairing i ≤ (glueRaw σ δ g.s g.s' (1 - t)) (P.coroot i) at hh
    rw [g.raw_right ht'.1] at hh
    change σ.reverse.path.minPairing i +
      (δ.reverse.path ((1 - g.s' : ℚ) : ℝ) -
        σ.reverse.path ((1 - g.s : ℚ) : ℝ)) (P.coroot i) ≤ δ.reverse.path.pairing i t
    simp only [Presentation.reverse_path, minPairing_rev, rev_apply,
      Rat.cast_sub, Rat.cast_one, sub_sub_cancel, pairing, pathSpace_coroot,
      LinearMap.sub_apply, LinearMap.add_apply] at hh ⊢
    linarith
  have hf : (LittelmannPath.crystal (P.pathSpace hA)).fIter i n g.reverse.path =
      some η.rev := by
    rw [g.reverse_path, fIter_rev_eq_map_eIter, he, Option.map_some]
  obtain ⟨τ, gτ, hpath, hsource, hs, hs', hν, hμ, horbit, -⟩ :=
    g.reverse.exists_fIter_gluing_after i n hlate hleft hf
  have heτ : (LittelmannPath.crystal (P.pathSpace hA)).eIter i n σ.path =
      some τ.reverse.path := by
    rw [Presentation.reverse_path, fIter_rev_eq_map_eIter] at hsource
    have hh := congrArg (Option.map LittelmannPath.rev) hsource
    simp only [Option.map_map, Function.comp_def, rev_rev, Option.map_some] at hh
    change Option.map id _ = _ at hh
    rw [Option.map_id] at hh
    rw [Presentation.reverse_path]
    exact hh
  have hout : ∃ (υ : Presentation P hA) (gg : GluingPair υ δ.reverse.reverse),
      gg.path = η ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i n σ.path = some υ.path ∧
      gg.s = g.s ∧ gg.s' = g.s' ∧ gg.ν = g.ν ∧ gg.μ = g.μ ∧
      ∀ j, ∃ w : P.weylGroup hA, (υ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
    refine ⟨τ.reverse, gτ.reverse, ?_, heτ, ?_, ?_, ?_, ?_, ?_⟩
    · rw [gτ.reverse_path, hpath, rev_rev]
    · change 1 - gτ.s' = g.s
      rw [hs']
      change 1 - (1 - g.s) = g.s
      ring
    · change 1 - gτ.s = g.s'
      rw [hs]
      change 1 - (1 - g.s') = g.s'
      ring
    · change -gτ.μ = g.ν
      rw [hμ]
      exact neg_neg _
    · change -gτ.ν = g.μ
      rw [hν]
      exact neg_neg _
    · intro j
      obtain ⟨u, hu⟩ := horbit j.rev
      obtain ⟨v, hv⟩ := σ.orbit (Fin.last σ.n)
      refine ⟨u * v, ?_⟩
      change -(τ.x j.rev : Dual ℝ H) = (u * v).1 (σ.x 0)
      rw [hu]
      change -u.1 (-(σ.x (0 : Fin (σ.n + 1)).rev : Dual ℝ H)) = _
      rw [Fin.rev_zero, map_neg, neg_neg, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]
  rw [δ.reverse_reverse] at hout
  exact hout

/-- The strict-before raising sector of Proposition 5.6 with nonnegative terminal
left-source slope. Every successful same-root raising iterate has an ACTUAL strict
output witness with unchanged right source, cuts and auxiliary directions. No source
success, output witness, closure or dominant representative is assumed. -/
theorem exists_eIter_gluing_before_of_nonneg (i : ι) (n : ℕ)
    (hearly : ∃ u ∈ Ico (0 : ℝ) g.s, g.path.pairing i u = g.path.minPairing i)
    (hx : 0 ≤ (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i))
    {η : LittelmannPath (P.pathSpace hA)}
    (he : (LittelmannPath.crystal (P.pathSpace hA)).eIter i n g.path = some η) :
    ∃ (τ : Presentation P hA) (g' : GluingPair τ δ),
      g'.path = η ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i n σ.path = some τ.path ∧
      g'.s = g.s ∧ g'.s' = g.s' ∧ g'.ν = g.ν ∧ g'.μ = g.μ ∧
      ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  have hlate : ∃ u ∈ Ioc (g.reverse.s' : ℝ) 1,
      g.reverse.path.pairing i u = g.reverse.path.minPairing i := by
    obtain ⟨u, hu, hum⟩ := hearly
    refine ⟨1 - u, ⟨?_, by linarith [hu.1]⟩, ?_⟩
    · change ((1 - g.s : ℚ) : ℝ) < 1 - u
      push_cast
      linarith [hu.2]
    · rw [g.reverse_path, pairing_rev, minPairing_rev, sub_sub_cancel, hum]
  have hx' : (σ.reverse.x 0 : Dual ℝ H) (P.coroot i) ≤ 0 := by
    change ((-σ.x (0 : Fin (σ.n + 1)).rev : P.integralWeights) : Dual ℝ H)
      (P.coroot i) ≤ 0
    simpa only [Fin.rev_zero, AddSubgroup.coe_neg, LinearMap.neg_apply, neg_nonpos] using hx
  have hf : (LittelmannPath.crystal (P.pathSpace hA)).fIter i n g.reverse.path =
      some η.rev := by
    rw [g.reverse_path, fIter_rev_eq_map_eIter, he, Option.map_some]
  obtain ⟨τ, gτ, hpath, hsource, hs, hs', hν, hμ, horbit⟩ :=
    g.reverse.exists_fIter_gluing_after_of_nonpos i n hlate hx' hf
  have heτ : (LittelmannPath.crystal (P.pathSpace hA)).eIter i n σ.path =
      some τ.reverse.path := by
    rw [Presentation.reverse_path, fIter_rev_eq_map_eIter] at hsource
    have hh := congrArg (Option.map LittelmannPath.rev) hsource
    simp only [Option.map_map, Function.comp_def, rev_rev, Option.map_some] at hh
    change Option.map id _ = _ at hh
    rw [Option.map_id] at hh
    rw [Presentation.reverse_path]
    exact hh
  have hout : ∃ (υ : Presentation P hA) (gg : GluingPair υ δ.reverse.reverse),
      gg.path = η ∧
      (LittelmannPath.crystal (P.pathSpace hA)).eIter i n σ.path = some υ.path ∧
      gg.s = g.s ∧ gg.s' = g.s' ∧ gg.ν = g.ν ∧ gg.μ = g.μ ∧
      ∀ j, ∃ w : P.weylGroup hA, (υ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
    refine ⟨τ.reverse, gτ.reverse, ?_, heτ, ?_, ?_, ?_, ?_, ?_⟩
    · rw [gτ.reverse_path, hpath, rev_rev]
    · change 1 - gτ.s' = g.s
      rw [hs']
      change 1 - (1 - g.s) = g.s
      ring
    · change 1 - gτ.s = g.s'
      rw [hs]
      change 1 - (1 - g.s') = g.s'
      ring
    · change -gτ.μ = g.ν
      rw [hμ]
      exact neg_neg _
    · change -gτ.ν = g.μ
      rw [hν]
      exact neg_neg _
    · intro j
      obtain ⟨u, hu⟩ := horbit j.rev
      obtain ⟨v, hv⟩ := σ.orbit (Fin.last σ.n)
      refine ⟨u * v, ?_⟩
      change -(τ.x j.rev : Dual ℝ H) = (u * v).1 (σ.x 0)
      rw [hu]
      change -u.1 (-(σ.x (0 : Fin (σ.n + 1)).rev : Dual ℝ H)) = _
      rw [Fin.rev_zero, map_neg, neg_neg, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]
  rw [δ.reverse_reverse] at hout
  exact hout

/-- Integral global minima for every simple root of every actual raising output
in the nonnegative-terminal-slope strict-before sector. -/
theorem eIter_isIntegral_before_of_nonneg (i : ι) (n : ℕ)
    (hearly : ∃ u ∈ Ico (0 : ℝ) g.s, g.path.pairing i u = g.path.minPairing i)
    (hx : 0 ≤ (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i))
    {η : LittelmannPath (P.pathSpace hA)}
    (he : (LittelmannPath.crystal (P.pathSpace hA)).eIter i n g.path = some η) :
    η.IsIntegral := by
  obtain ⟨τ, g', hpath, -⟩ := g.exists_eIter_gluing_before_of_nonneg i n hearly hx he
  rw [← hpath]
  exact g'.isIntegral

end GluingPair
end Matrix.Realization.LSGeneralClass
