/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingDirections
import LieLean.RepresentationTheory.Crystal.Path.AChains.Construction

/-!
# Source root chains without a dominant-class assumption

## Main definitions

`RootStep` is the positive-real-root, negative-initial-pairing relation of [Lit95] §4.
`RootWalk` records its finite lengths. `SaturatedStep` says a root step has no walk
of length greater than one: exactly the source's distance-one condition, without
introducing a maximum-distance function for unrelated endpoints.

## Main results

The distance-one crossing argument uses the explicit two/three-step detour on
pp. 509–510, rather than dominant-orbit Bruhat representatives. The chain layer
permits arbitrary ambient real weights, in particular every rational class. The
finite path constructor uses arbitrary integral directions (the denominator-cleared
setting of Remark 5.1), never dominant-class witnesses. The finite gluing seam is
proved from source chains and an integral glued endpoint. This is local chain
support, not component stability or the isomorphism theorem.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), 499–525, §4 pp. 509–510 (Lemma 4.1, Corollary 1 and a-chain definition),
§5 pp. 513–516 (Remark 5.1, Definition 5.3, Lemma 5.5 and Proposition 5.7). Proofs reconstructed.
-/

open Module

namespace Matrix.Realization.LSGeneralClass

open LSAChainBridgeRoots LSAChainBridge

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} (P : Realization A ℝ H) (hA : A.IsGeneralizedCartan)

/-- One source descending step, with its actual positive real root and coroot.
There is no dominant weight or minimal Weyl representative in this definition. -/
def RootStep (x y : Dual ℝ H) (c : Dual ℝ (Dual ℝ H)) : Prop :=
  ∃ (u : P.weylGroup hA) (j : ι),
    (∃ k : ι → ℤ, 0 ≤ k ∧ u.1 (P.root j) = P.rootOf k) ∧
    c = rootCoroot P hA u j ∧ c x < 0 ∧
    y = x - c x • u.1 (P.root j)

/-- Finite source sequences with their literal number of strict root steps. -/
inductive RootWalk : Dual ℝ H → Dual ℝ H → ℕ → Prop
  | refl (x) : RootWalk x x 0
  | head {x y z n} (step : ∃ c, RootStep P hA x y c)
      (tail : RootWalk y z n) : RootWalk x z (n + 1)

/-- Source distance one, expressed by the exact bound on all possible walk lengths.
The displayed root step witnesses that length one is attained. -/
def SaturatedStep (x y : Dual ℝ H) (c : Dual ℝ (Dual ℝ H)) : Prop :=
  RootStep P hA x y c ∧ ∀ n, RootWalk P hA x y n → n ≤ 1

variable {P hA} {x y : Dual ℝ H} {c : Dual ℝ (Dual ℝ H)}

/-- A source root step is a walk of length one. -/
theorem RootStep.walk (h : RootStep P hA x y c) : RootWalk P hA x y 1 :=
  .head ⟨c, h⟩ (.refl y)

/-- Source distance one is literally a greatest walk length equal to one, not
an assumed Bruhat cover or a separately supplied crossing property. -/
theorem saturatedStep_iff_greatest :
    SaturatedStep P hA x y c ↔ RootStep P hA x y c ∧
      IsGreatest {n : ℕ | RootWalk P hA x y n} 1 := by
  constructor
  · rintro ⟨hs, hb⟩
    exact ⟨hs, hs.walk, fun n hn ↦ hb n hn⟩
  · rintro ⟨hs, -, hb⟩
    exact ⟨hs, fun n hn ↦ hb hn⟩

/-- A negative simple pairing gives a descending source step. -/
theorem rootStep_simple {i : ι} (hx : x (P.coroot i) < 0) :
    RootStep P hA x (P.reflection hA i x) (Dual.eval ℝ H (P.coroot i)) := by
  classical
  refine ⟨1, i, ⟨Pi.single i 1, fun j ↦ by
    by_cases hj : j = i <;> simp [hj], by simp⟩, rfl, hx, ?_⟩
  exact P.reflection_apply hA i x

/-- Away from the exceptional simple root, conjugating the source step by a
simple reflection preserves positivity and negative initial pairing. -/
theorem rootStep_reflected [DecidableEq ι] {u : P.weylGroup hA} {j i : ι}
    (hp : ∃ k : ι → ℤ, 0 ≤ k ∧ u.1 (P.root j) = P.rootOf k)
    (hne : u.1 (P.root j) ≠ P.root i)
    (hn : rootCoroot P hA u j x < 0)
    (hy : y = x - rootCoroot P hA u j x • u.1 (P.root j)) :
    RootStep P hA (P.reflection hA i x) (P.reflection hA i y)
      (rootCoroot P hA ((P.coxeterSystem hA).simple i * u) j) := by
  refine ⟨(P.coxeterSystem hA).simple i * u, j,
    positive_root_simple_mul P hA hp hne, rfl, ?_, ?_⟩
  · simpa only [rootCoroot_simple_mul, reflection_reflection] using hn
  · rw [rootCoroot_simple_mul, reflection_reflection, coe_simple_mul_apply, hy,
      map_sub, map_smul]

/-- Corollary 1 of [Lit95], p. 509: a saturated crossing must use the simple root.
Both weak/strict crossing conventions are included, as in the source. The proof is
the two/three-step contradiction on p. 510, valid outside the Tits cone too. -/
theorem SaturatedStep.crossing (h : SaturatedStep P hA x y c) {i : ι}
    (hc : (x (P.coroot i) ≤ 0 ∧ 0 < y (P.coroot i)) ∨
      (x (P.coroot i) < 0 ∧ 0 ≤ y (P.coroot i))) :
    c = Dual.eval ℝ H (P.coroot i) ∧ y = P.reflection hA i x := by
  classical
  obtain ⟨hs, hsat⟩ := h
  obtain ⟨u, j, hp, rfl, hn, hy⟩ := hs
  have hroot : u.1 (P.root j) = P.root i := by
    by_contra hne
    have hs := rootStep_reflected hp hne hn hy
    rcases lt_or_eq_of_le (hc.elim And.left (fun h ↦ h.1.le)) with hx | hx
    · have hfirst := rootStep_simple (hA := hA) hx
      rcases lt_or_eq_of_le (hc.elim (fun h ↦ h.2.le) And.right) with hypos | hyzero
      · have hlast := rootStep_simple (hA := hA)
          (i := i) (x := P.reflection hA i y) (by
            rw [reflection_apply_coroot_self]; exact neg_neg_of_pos hypos)
        have hw : RootWalk P hA x y 3 :=
          .head ⟨_, hfirst⟩ (.head ⟨_, hs⟩ (by
            simpa only [reflection_reflection] using hlast.walk))
        have := hsat 3 hw
        omega
      · have hfix : P.reflection hA i y = y := by
          rw [reflection_apply, ← hyzero, zero_smul, sub_zero]
        have hw : RootWalk P hA x y 2 :=
          .head ⟨_, hfirst⟩ (by simpa only [hfix] using hs.walk)
        have := hsat 2 hw
        omega
    · have hypos : 0 < y (P.coroot i) := by
        rcases hc with hc | hc
        · exact hc.2
        · exact (lt_irrefl _ (hx ▸ hc.1)).elim
      have hfix : P.reflection hA i x = x := by
        rw [reflection_apply, hx, zero_smul, sub_zero]
      have hlast := rootStep_simple (hA := hA)
        (i := i) (x := P.reflection hA i y) (by
          rw [reflection_apply_coroot_self]; exact neg_neg_of_pos hypos)
      have hw : RootWalk P hA x y 2 :=
        .head ⟨_, by simpa only [hfix] using hs⟩ (by
          simpa only [reflection_reflection] using hlast.walk)
      have := hsat 2 hw
      omega
  have hcor : rootCoroot P hA u j = Dual.eval ℝ H (P.coroot i) := by
    ext v
    exact rootCoroot_eq_simple_of_root_eq P hA hroot v
  refine ⟨hcor, ?_⟩
  rw [hy, hroot, hcor, Dual.eval_apply, reflection_apply]

variable (P hA) in
/-- Position chains formed from actual saturated source root steps. -/
def PositionChain (p : Dual ℝ H) : Dual ℝ H → Dual ℝ H → Prop :=
  Relation.ReflTransGen fun x y ↦ ∃ c,
    SaturatedStep P hA x y c ∧ ∃ z : ℤ, c p = z

/-- Arbitrary-class source chains have the simple-coroot crossing integrality
needed at the gluing seam. No abstract `LSData`, dominance, or integrality conclusion
is supplied as an input. -/
theorem PositionChain.exists_int {p : Dual ℝ H} (h : PositionChain P hA p x y) {i : ι}
    (hc : (x (P.coroot i) ≤ 0 ∧ 0 < y (P.coroot i)) ∨
      (x (P.coroot i) < 0 ∧ 0 ≤ y (P.coroot i))) :
    ∃ z : ℤ, p (P.coroot i) = z := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rcases hc with hc | hc <;> linarith [hc.1, hc.2]
  | @head x v hxv _ ih =>
    obtain ⟨c, hs, z, hz⟩ := hxv
    rcases lt_trichotomy (v (P.coroot i)) 0 with hv | hv | hv
    · exact ih (Or.inr ⟨hv, hc.elim (fun h ↦ h.2.le) And.right⟩)
    · by_cases hx : x (P.coroot i) < 0
      · obtain ⟨rfl, -⟩ := hs.crossing (Or.inr ⟨hx, hv.ge⟩)
        exact ⟨z, hz⟩
      · have hyp : 0 < y (P.coroot i) := hc.resolve_right (by rintro ⟨hx', -⟩; exact hx hx') |>.2
        exact ih (Or.inl ⟨hv.le, hyp⟩)
    · obtain ⟨rfl, -⟩ := hs.crossing
        (Or.inl ⟨hc.elim And.left (fun h ↦ h.1.le), hv⟩)
      exact ⟨z, hz⟩

variable (P hA) in
/-- Source time-integral saturated chains for arbitrary ambient weights. Rational
classes are included without choosing a dominant representative. -/
def AChain (a : ℝ) : Dual ℝ H → Dual ℝ H → Prop :=
  Relation.ReflTransGen fun x y ↦ ∃ c,
    SaturatedStep P hA x y c ∧ ∃ z : ℤ, a * c x = z

/-- Every root step is the action of its stated Weyl reflection; consequently
allowing ambient weights in walks does not add weights outside the source orbit. -/
theorem RootStep.eq_weyl (h : RootStep P hA x y c) :
    ∃ w : P.weylGroup hA, y = w.1 x := by
  classical
  obtain ⟨u, j, -, rfl, -, hy⟩ := h
  exact ⟨u * (P.coxeterSystem hA).simple j * u⁻¹,
    hy.trans (conjugate_apply P hA u j x).symm⟩

/-- The intermediate weights of source walks remain in their starting Weyl orbit. -/
theorem RootWalk.eq_weyl {n : ℕ} (h : RootWalk P hA x y n) :
    ∃ w : P.weylGroup hA, y = w.1 x := by
  induction h with
  | refl => exact ⟨1, rfl⟩
  | @head x y z n hs _ ih =>
    obtain ⟨c, hc⟩ := hs
    obtain ⟨u, hu⟩ := hc.eq_weyl
    obtain ⟨v, hv⟩ := ih
    exact ⟨v * u, by rw [hv, hu, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩

/-- Actual real-root coroots take integer values on the actual root lattice,
independently of the class of the weights in the step. -/
theorem RootStep.integral_rootLattice (h : RootStep P hA x y c)
    {q : Dual ℝ H} (hq : q ∈ rootLattice P) : ∃ z : ℤ, c q = z := by
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨u, j, -, rfl, -, -⟩ := h
  obtain ⟨l, hl⟩ := P.exists_apply_rootOf_eq_rootOf hA (u⁻¹).2 k
  refine ⟨(A *ᵥ l) j, ?_⟩
  change (u⁻¹).1 (P.rootOf k) (P.coroot j) = _
  rw [hl, rootOf_apply_coroot]

/-- Real-root coroots also take integer values on every integral weight. -/
theorem RootStep.integral_weight (h : RootStep P hA x y c)
    (q : P.integralWeights) : ∃ z : ℤ, c q = z := by
  obtain ⟨u, j, -, rfl, -, -⟩ := h
  exact exists_int_apply_coroot q.2 u⁻¹ j

/-- An integral time step has root-lattice displacement, without dominance. -/
theorem RootStep.displacement (h : RootStep P hA x y c) {a : ℝ}
    (hi : ∃ z : ℤ, a * c x = z) : a • x - a • y ∈ rootLattice P := by
  obtain ⟨u, j, ⟨k, -, hk⟩, -, -, hy⟩ := h
  obtain ⟨z, hz⟩ := hi
  refine ⟨z • k, ?_⟩
  rw [map_zsmul, hy, hk, smul_sub, smul_smul, hz, Int.cast_smul_eq_zsmul]
  abel

/-- Time integrality and position integrality agree under the necessary
root-lattice congruence; this congruence is propagated below, not postulated globally. -/
theorem RootStep.integral_iff (h : RootStep P hA x y c) {a : ℝ} {p : Dual ℝ H}
    (hq : p - a • x ∈ rootLattice P) :
    (∃ z : ℤ, c p = z) ↔ ∃ z : ℤ, a * c x = z := by
  obtain ⟨k, hk⟩ := h.integral_rootLattice hq
  rw [map_sub, map_smul, smul_eq_mul] at hk
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z - k, by push_cast; linarith⟩
  · rintro ⟨z, hz⟩
    exact ⟨z + k, by push_cast; linarith⟩

/-- Every arbitrary-class source time chain supplies a position chain and
propagates the root-lattice congruence through all its steps. -/
theorem AChain.to_positionChain {a : ℝ} {p : Dual ℝ H} (h : AChain P hA a x y)
    (hq : p - a • x ∈ rootLattice P) :
    PositionChain P hA p x y ∧ p - a • y ∈ rootLattice P := by
  induction h with
  | refl => exact ⟨.refl, hq⟩
  | @tail y z _ hyz ih =>
    obtain ⟨c, hc, hint⟩ := hyz
    refine ⟨ih.1.tail ⟨c, hc, (hc.1.integral_iff ih.2).mpr hint⟩, ?_⟩
    have hh := (rootLattice P).add_mem ih.2 (hc.1.displacement hint)
    convert hh using 1
    abel

/-- Conversely, position chains propagate the same invariant and recover source
`a`-chains. Thus the bridge does not enlarge the source step relation. -/
theorem PositionChain.to_aChain {a : ℝ} {p : Dual ℝ H}
    (h : PositionChain P hA p x y) (hq : p - a • x ∈ rootLattice P) :
    AChain P hA a x y ∧ p - a • y ∈ rootLattice P := by
  induction h with
  | refl => exact ⟨.refl, hq⟩
  | @tail y z _ hyz ih =>
    obtain ⟨c, hc, hint⟩ := hyz
    have ht := (hc.1.integral_iff ih.2).mp hint
    refine ⟨ih.1.tail ⟨c, hc, ht⟩, ?_⟩
    have hh := (rootLattice P).add_mem ih.2 (hc.1.displacement ht)
    convert hh using 1
    abel

/-- A source time chain gives a position chain at its scaled target, with the
original descending orientation. This is the right-cut bridge of Definition 5.3. -/
theorem AChain.at_target {a : ℝ} (h : AChain P hA a x y) :
    PositionChain P hA (a • y) x y := by
  have hd := (h.to_positionChain (p := a • x) (by simp)).2
  have hq : a • y - a • x ∈ rootLattice P := by
    simpa only [neg_sub] using (rootLattice P).neg_mem hd
  exact (h.to_positionChain hq).1

/-- Integral-weight translations preserve arbitrary-class position chains. -/
theorem PositionChain.add_weight {p : Dual ℝ H} (h : PositionChain P hA p x y)
    (q : P.integralWeights) : PositionChain P hA (p + q) x y := by
  induction h with
  | refl => exact .refl
  | @tail y z _ hyz ih =>
    obtain ⟨c, hc, k, hk⟩ := hyz
    obtain ⟨l, hl⟩ := hc.1.integral_weight q
    exact ih.tail ⟨c, hc, k + l, by rw [map_add, hk, hl, Int.cast_add]⟩

/-- The gluing seam argument, now for arbitrary classes on BOTH sides.
The inputs are actual saturated root chains at the cut and the source positive-root
compatibility, not assumed LSData or a supplied seam-integrality condition. -/
theorem seam_integral {p ν μ : Dual ℝ H}
    (hl : PositionChain P hA p x ν) (hr : PositionChain P hA p μ y)
    (hp : P.GluingPrecedes hA ν μ) {i : ι}
    (hx : x (P.coroot i) < 0) (hy : 0 < y (P.coroot i)) :
    ∃ z : ℤ, p (P.coroot i) = z := by
  by_cases hν : 0 ≤ ν (P.coroot i)
  · exact hl.exists_int (Or.inr ⟨hx, hν⟩)
  · exact hr.exists_int (Or.inl ⟨hp.simple (lt_of_not_ge hν), hy⟩)

/-- Time-chain form of the arbitrary-class seam theorem. The left incoming
congruence and the integral translation are the invariants derived by finite path
construction and the source integral-endpoint condition, respectively. -/
theorem seam_integral_of_aChains {a b : ℝ} {p q ν μ : Dual ℝ H}
    (hl : AChain P hA a x ν) (hr : AChain P hA b μ y)
    (hlq : p - a • x ∈ rootLattice P) (hqr : q = b • y)
    (hoff : p - q ∈ P.integralWeights) (hp : P.GluingPrecedes hA ν μ) {i : ι}
    (hx : x (P.coroot i) < 0) (hy : 0 < y (P.coroot i)) :
    ∃ z : ℤ, p (P.coroot i) = z := by
  apply seam_integral (hl.to_positionChain hlq).1 (hp := hp) (hx := hx) (hy := hy)
  have hh := hr.at_target.add_weight (⟨p - q, hoff⟩ : P.integralWeights)
  simpa only [← hqr, add_sub_cancel] using hh

/-- Positive scaling preserves source root steps and their actual coroots. -/
theorem RootStep.smul (h : RootStep P hA x y c) {r : ℝ} (hr : 0 < r) :
    RootStep P hA (r • x) (r • y) c := by
  obtain ⟨u, j, hp, hc, hn, hy⟩ := h
  refine ⟨u, j, hp, hc, ?_, ?_⟩
  · rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hr hn
  · rw [hy, smul_sub, map_smul, smul_eq_mul, smul_smul]

/-- Positive scaling preserves every finite source walk with its exact length. -/
theorem RootWalk.smul {n : ℕ} (h : RootWalk P hA x y n) {r : ℝ} (hr : 0 < r) :
    RootWalk P hA (r • x) (r • y) n := by
  induction h with
  | refl => exact .refl _
  | head hs _ ih =>
    obtain ⟨c, hc⟩ := hs
    exact .head ⟨c, hc.smul hr⟩ ih

/-- The actual maximal-length-one condition survives positive scaling. The
reverse inequality is proved by scaling ANY candidate walk back, not by asserting
that clearing denominators makes a weight dominant. -/
theorem SaturatedStep.smul (h : SaturatedStep P hA x y c) {r : ℝ} (hr : 0 < r) :
    SaturatedStep P hA (r • x) (r • y) c := by
  refine ⟨h.1.smul hr, fun n hw ↦ h.2 n ?_⟩
  simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using
    hw.smul (inv_pos.mpr hr)

/-- Source time chains transport under positive weight scaling with reciprocal
time scaling. This is the precise local scaling law for denominator clearing. -/
theorem AChain.smul {a r : ℝ} (h : AChain P hA a x y) (hr : 0 < r) :
    AChain P hA (a / r) (r • x) (r • y) := by
  induction h with
  | refl => exact .refl
  | @tail y z _ hyz ih =>
    obtain ⟨c, hc, k, hk⟩ := hyz
    refine ih.tail ⟨c, hc.smul hr, k, ?_⟩
    rw [map_smul, smul_eq_mul, ← mul_assoc, div_mul_cancel₀ a hr.ne']
    exact hk

/-- A chain never leaves its initial orbit, even without a dominant representative. -/
theorem AChain.eq_weyl {a : ℝ} (h : AChain P hA a x y) :
    ∃ w : P.weylGroup hA, y = w.1 x := by
  induction h with
  | refl => exact ⟨1, rfl⟩
  | @tail y z _ hyz ih =>
    obtain ⟨c, hc, -⟩ := hyz
    obtain ⟨u, hu⟩ := hc.1.eq_weyl
    obtain ⟨v, hv⟩ := ih
    exact ⟨u * v, by rw [hu, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩

open Set LittelmannPath LittelmannPath.FiniteConstruction

section Finite

variable {n : ℕ} {a : Fin (n + 2) → ℚ} {x : Fin (n + 1) → P.integralWeights}

/-- Source a-chains propagate the cumulative root-lattice invariant before a path exists.
This is the same invariant as `finite_congruences`, without its supplied-path premise. -/
theorem cumulative_congruences (ha0 : a 0 = 0)
    (hc : ∀ i : Fin n, AChain P hA (a i.succ.castSucc : ℝ)
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
    exact ((hc i).to_positionChain (heq ▸ ih)).2

/-- The constructed endpoint differs from its final integral direction by a root-lattice
vector. No integrality or LS condition on the endpoint is assumed. -/
theorem raw_endpoint_congruence (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (n + 1)) = 1)
    (hc : ∀ i : Fin n, AChain P hA (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) :
    raw (P.pathSpace hA) a x 1 - (x (Fin.last n) : Dual ℝ H) ∈ rootLattice P := by
  have hi := cumulative_congruences ha0 hc (Fin.last n)
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
    (hc : ∀ i : Fin n, AChain P hA (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) :
    raw (P.pathSpace hA) a x 1 ∈ P.integralWeights := by
  have h := rootLattice_le_integralWeights (raw_endpoint_congruence ha ha0 ha1 hc)
  have hs := P.integralWeights.add_mem h (x (Fin.last n)).property
  simpa only [sub_add_cancel] using hs

/-- The actual finite rational-PL path for arbitrary integral directions with source
a-chains. Its endpoint is derived. No dominant-class hypothesis occurs. Compare
Littelmann 1995, §4, pp. 509–511 (definitions on p. 510; Lemma 4.5 a) for the integral
endpoint); this does not assert abstract `IsLS` or stability.
Redundant equal directions are permitted (an explicit extension of the strict presentation). -/
noncomputable def ofAChains (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (n + 1)) = 1)
    (hc : ∀ i : Fin n, AChain P hA (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) : LittelmannPath (P.pathSpace hA) where
  toFun := raw (P.pathSpace hA) a x
  wt := ⟨raw (P.pathSpace hA) a x 1, raw_endpoint_integral ha ha0 ha1 hc⟩
  toFun_of_nonpos' := fun _ ht ↦ raw_of_nonpos (P.pathSpace hA) ha ha0 x ht
  toFun_of_one_le' := fun _ ht ↦ raw_of_one_le (P.pathSpace hA) ha ha1 x ht
  continuous_coroot' := continuous_coroot_raw (P.pathSpace hA) a x

/-- The constructor has the literal cumulative affine formula on each closed piece. -/
theorem ofAChains_piece (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (n + 1)) = 1)
    (hc : ∀ i : Fin n, AChain P hA (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) (i : Fin (n + 1)) (t : ℝ)
    (ht : t ∈ Icc (a i.castSucc : ℝ) (a i.succ : ℝ)) :
    ofAChains ha ha0 ha1 hc t = finitePiecePosition (P.pathSpace hA) a x i.castSucc +
      (t - (a i.castSucc : ℝ)) • (x i : Dual ℝ H) :=
  raw_eq_piece (P.pathSpace hA) ha x i t ht

/-- At every time in a closed affine piece, the incoming root-lattice invariant
holds for the newly constructed arbitrary-class path. -/
theorem ofAChains_congruence (ha : StrictMono a) (ha0 : a 0 = 0)
    (ha1 : a (Fin.last (n + 1)) = 1)
    (hc : ∀ i : Fin n, AChain P hA (a i.succ.castSucc : ℝ)
      (x i.castSucc) (x i.succ)) (i : Fin (n + 1)) (t : ℝ)
    (ht : t ∈ Icc (a i.castSucc : ℝ) (a i.succ : ℝ)) :
    ofAChains ha ha0 ha1 hc t - t • (x i : Dual ℝ H) ∈ rootLattice P := by
  rw [ofAChains_piece ha ha0 ha1 hc i t ht]
  convert cumulative_congruences ha0 hc i using 1
  rw [sub_smul t (a i.castSucc : ℝ) (x i : Dual ℝ H)]
  abel

end Finite

variable (P hA) in
/-- Finite source presentation with an arbitrary integral class, specified by its
initial direction and the actual saturated source time chains. No dominant witness,
LSData, supplied path, or endpoint/minimum-integrality field is present. -/
structure Presentation where
  n : ℕ
  a : Fin (n + 2) → ℚ
  x : Fin (n + 1) → P.integralWeights
  mono : StrictMono a
  zero : a 0 = 0
  one : a (Fin.last (n + 1)) = 1
  chains : ∀ j : Fin n, AChain P hA (a j.succ.castSucc : ℝ)
    (x j.castSucc) (x j.succ)

/-- All directions of the presentation belong to its initial Weyl orbit;
no orbit membership, let alone a dominant representative, is assumed as a field. -/
theorem Presentation.orbit (σ : Presentation P hA) (j : Fin (σ.n + 1)) :
    ∃ w : P.weylGroup hA, (σ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  induction j using Fin.induction with
  | zero => exact ⟨1, rfl⟩
  | succ j ih =>
    obtain ⟨u, hu⟩ := (σ.chains j).eq_weyl
    obtain ⟨v, hv⟩ := ih
    exact ⟨u * v, by rw [hu, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩

/-- The actual finite rational-PL path of an arbitrary-integral-class presentation. -/
noncomputable def Presentation.path (σ : Presentation P hA) :
    LittelmannPath (P.pathSpace hA) :=
  ofAChains σ.mono σ.zero σ.one σ.chains

/-- The literal paused gluing function, with the original parameter unchanged. -/
noncomputable def glueRaw (σ δ : Presentation P hA) (s s' : ℚ) (t : ℝ) : Dual ℝ H :=
  σ.path (min t (s : ℝ)) + δ.path (max t (s' : ℝ)) - δ.path s'

/-- The actual finite glued seam is integral for two arbitrary integral classes.
All source position congruences and the integral translation are DERIVED. The only
global integrality premise is the source's integral glued endpoint. This feeds Lemma 5.5
for the denominator-cleared classes of Remark 5.1, including arbitrary second classes
outside the Tits cone. It does not assume their dominance or dominant conjugacy. -/
theorem finite_seam_integral (σ δ : Presentation P hA) {s s' : ℚ}
    (hle : s ≤ s') (hlt : s' < 1)
    (hs : (s : ℝ) ∈ Icc (σ.a (Fin.last σ.n).castSucc : ℝ)
      (σ.a (Fin.last σ.n).succ : ℝ))
    (hs' : (s' : ℝ) ∈ Icc 0 (δ.a (0 : Fin (δ.n + 1)).succ : ℝ))
    {ν μ : Dual ℝ H}
    (hl : AChain P hA (s : ℝ) (σ.x (Fin.last σ.n)) ν)
    (hr : AChain P hA (s' : ℝ) μ (δ.x 0))
    (hp : P.GluingPrecedes hA ν μ)
    (hend : glueRaw σ δ s s' 1 ∈ P.integralWeights) {i : ι}
    (hx : (σ.x (Fin.last σ.n) : Dual ℝ H) (P.coroot i) < 0)
    (hy : 0 < (δ.x 0 : Dual ℝ H) (P.coroot i)) :
    ∃ z : ℤ, (σ.path s) (P.coroot i) = z := by
  have hlq := ofAChains_congruence σ.mono σ.zero σ.one σ.chains (Fin.last σ.n) s hs
  have hfirst : δ.path s' = (s' : ℝ) • (δ.x 0 : Dual ℝ H) := by
    have ht : (s' : ℝ) ∈ Icc (δ.a (0 : Fin (δ.n + 1)).castSucc : ℝ)
        (δ.a (0 : Fin (δ.n + 1)).succ : ℝ) := by simpa [δ.zero] using hs'
    simpa [Presentation.path, δ.zero] using
      ofAChains_piece δ.mono δ.zero δ.one δ.chains 0 s' ht
  have hs1 : (s : ℝ) ≤ 1 := by exact_mod_cast hle.trans hlt.le
  have hs'1 : (s' : ℝ) ≤ 1 := by exact_mod_cast hlt.le
  have he : δ.path 1 + (σ.path s - δ.path s') ∈ P.integralWeights := by
    convert hend using 1
    rw [glueRaw, min_eq_right hs1, max_eq_left hs'1]
    abel
  have hd : δ.path 1 ∈ P.integralWeights := δ.path.wt.property
  have hoff : σ.path s - δ.path s' ∈ P.integralWeights := by
    simpa only [add_sub_cancel_left] using P.integralWeights.sub_mem he hd
  exact seam_integral_of_aChains hl hr hlq hfirst hoff hp hx hy

end Matrix.Realization.LSGeneralClass
