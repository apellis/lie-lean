/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GeneralClass

/-!
# Saturated arbitrary-integral-class source walks

## Main results

Source distance is a maximum, not a shortest-path distance. Integral source walks
have bounded lengths; maximal walks consist of saturated steps. From this we prove
simple-root saturation and same-sign saturation-preserving reflection (Lemma 4.1),
and construct `LSGeneralClass.lsData` for any integral weight, without dominance.

## References

Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), pp. 509–510, Lemma 4.1. Scanned source inspected; proofs reconstructed.
-/

open Module
namespace Matrix.Realization.LSGeneralClass
open LSAChainBridgeRoots
variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}
  {x y z : Dual ℝ H} {c : Dual ℝ (Dual ℝ H)}

/-- Source walks concatenate with addition of their actual lengths. -/
theorem RootWalk.append {m n : ℕ} (h : RootWalk P hA x y m)
    (k : RootWalk P hA y z n) : RootWalk P hA x z (m + n) := by
  induction h with
  | refl => simpa using k
  | head hs _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (RootWalk.head hs (ih k))

/-- Every source step starting at an integral weight ends at an integral weight. -/
theorem RootStep.integral_end (h : RootStep P hA x y c)
    (hx : x ∈ P.integralWeights) : y ∈ P.integralWeights := by
  obtain ⟨w, rfl⟩ := h.eq_weyl
  exact fun i ↦ exists_int_apply_coroot hx w i

/-- Reflection transports a raw source step with positive initial simple pairing. -/
theorem RootStep.reflection_pos (h : RootStep P hA x y c) {i : ι}
    (hx : 0 < x (P.coroot i)) :
    RootStep P hA (P.reflection hA i x) (P.reflection hA i y)
      (c ∘ₗ (P.reflection hA i).toLinearMap) := by
  classical
  obtain ⟨u, j, hp, rfl, hn, hy⟩ := h
  have hne : u.1 (P.root j) ≠ P.root i := by
    intro he
    rw [rootCoroot_eq_simple_of_root_eq P hA he] at hn
    linarith
  convert rootStep_reflected hp hne hn hy using 1
  ext v
  exact (rootCoroot_simple_mul P hA i u j v).symm

/-- Height increases by at least one on each integral source step. -/
theorem RootStep.height_add_one_le (h : RootStep P hA x y c)
    (hx : x ∈ P.integralWeights) (g : Dual ℝ (Dual ℝ H))
    (hg : ∀ i, g (P.root i) = 1) : g x + 1 ≤ g y := by
  classical
  obtain ⟨a, ha⟩ := h.integral_weight ⟨x, hx⟩
  obtain ⟨u, j, ⟨k, hk, hroot⟩, rfl, hn, hy⟩ := h
  have hkne : k ≠ 0 := by
    intro he
    rw [he, map_zero] at hroot
    exact P.linearIndependent_root.ne_zero j (u.1.injective (by simpa using hroot))
  have hkpos : 0 < ∑ i, k i := by
    apply Finset.sum_pos'
    · intro i _; exact hk i
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hkne
      exact ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hk i) (Ne.symm hi)⟩
  have hgroot : g (u.1 (P.root j)) = ((∑ i, k i : ℤ) : ℝ) := by
    simp [hroot, rootOf_apply, hg]
  have ha' : (a : ℝ) < 0 := by simpa only [← ha] using hn
  have han : a ≤ -1 := by
    have : a < 0 := by exact_mod_cast ha'
    omega
  have hkone : (1 : ℝ) ≤ ((∑ i, k i : ℤ) : ℝ) := by exact_mod_cast hkpos
  have ham : (1 : ℝ) ≤ -(a : ℝ) := by
    have : (a : ℝ) ≤ -1 := by exact_mod_cast han
    linarith
  rw [hy, map_sub, map_smul, hgroot, ha, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_right ham (show 0 ≤ ((∑ i, k i : ℤ) : ℝ) by positivity)]

/-- Integral source walks have a numerical upper bound on their literal length. -/
theorem RootWalk.height_bound {n : ℕ} (h : RootWalk P hA x y n)
    (hx : x ∈ P.integralWeights) (g : Dual ℝ (Dual ℝ H))
    (hg : ∀ i, g (P.root i) = 1) : g x + n ≤ g y := by
  induction h with
  | refl => simp
  | head hs _ ih =>
    obtain ⟨c, hs⟩ := hs
    have hstep := hs.height_add_one_le hx g hg
    have htail := ih (hs.integral_end hx)
    push_cast
    linarith

/-- Integral source walks cannot have a nonempty cycle. -/
theorem RootWalk.eq_zero_of_loop {n : ℕ} (h : RootWalk P hA x x n)
    (hx : x ∈ P.integralWeights) : n = 0 := by
  obtain ⟨g, hg⟩ := exists_linearMap_root_eq_one (P := P)
  have hb := h.height_bound hx g hg
  have : (n : ℝ) ≤ 0 := by linarith
  exact Nat.eq_zero_of_le_zero (by exact_mod_cast this)

/-- Every inhabited integral interval has a maximum source-walk length. -/
theorem RootWalk.exists_greatest {n : ℕ} (h : RootWalk P hA x y n)
    (hx : x ∈ P.integralWeights) :
    ∃ m, IsGreatest {k : ℕ | RootWalk P hA x y k} m := by
  obtain ⟨g, hg⟩ := exists_linearMap_root_eq_one (P := P)
  obtain ⟨b, hb⟩ := exists_nat_gt (g y - g x)
  have hbound : BddAbove {k : ℕ | RootWalk P hA x y k} := by
    refine ⟨b, fun k hk ↦ ?_⟩
    have hlen := hk.height_bound hx g hg
    have : (k : ℝ) ≤ b := by linarith
    exact_mod_cast this
  exact hbound.exists_isGreatest_of_nonempty ⟨n, h⟩

/-- A source walk all of whose steps have maximum length one. -/
inductive SaturatedWalk (P : Realization A ℝ H) (hA : A.IsGeneralizedCartan) :
    Dual ℝ H → Dual ℝ H → ℕ → Prop
  | refl (x : Dual ℝ H) : SaturatedWalk P hA x x 0
  | head {x y z : Dual ℝ H} {n : ℕ} (step : ∃ c, SaturatedStep P hA x y c)
      (tail : SaturatedWalk P hA y z n) : SaturatedWalk P hA x z (n + 1)

/-- A saturated walk is a raw source walk of the same length. -/
theorem SaturatedWalk.walk {n : ℕ} (h : SaturatedWalk (P := P) (hA := hA) x y n) :
    RootWalk P hA x y n := by
  induction h with
  | refl => exact .refl _
  | head hs _ ih => exact .head (by obtain ⟨c, hc⟩ := hs; exact ⟨c, hc.1⟩) ih

/-- A maximal walk has saturated steps; no finiteness assumption is hidden here. -/
theorem RootWalk.saturated_of_maximal {n : ℕ} (h : RootWalk P hA x y n)
    (hm : ∀ k, RootWalk P hA x y k → k ≤ n) : SaturatedWalk P hA x y n := by
  induction h with
  | refl => exact .refl _
  | @head x y z n hs ht ih =>
    obtain ⟨c, hc⟩ := hs
    refine .head ⟨c, hc, fun k hk ↦ ?_⟩ (ih fun k hk ↦ ?_)
    · have := hm (k + n) (hk.append ht)
      omega
    · have := hm (k + 1) (.head ⟨c, hc⟩ hk)
      omega

/-- Simultaneous induction for the positive-end lifting and same-sign walk transport
in [Lit95], Lemma 4.1. Only already-proved source saturation/crossing is used. -/
theorem SaturatedWalk.lift_positive {n : ℕ} (h : SaturatedWalk P hA x y n) (i : ι) :
    (x (P.coroot i) ≤ 0 → 0 < y (P.coroot i) →
      ∃ k, k + 1 = n ∧ RootWalk P hA x (P.reflection hA i y) k) ∧
    (0 < x (P.coroot i) → 0 < y (P.coroot i) →
      RootWalk P hA (P.reflection hA i x) (P.reflection hA i y) n) := by
  induction h with
  | refl => exact ⟨fun hx hy ↦ (not_lt_of_ge hx hy).elim, fun _ _ ↦ .refl _⟩
  | @head x z y n hs ht ih =>
    obtain ⟨c, hs⟩ := hs
    constructor
    · intro hx hy
      by_cases hz : 0 < z (P.coroot i)
      · obtain ⟨_, he⟩ := hs.crossing (Or.inl ⟨hx, hz⟩)
        refine ⟨n, rfl, ?_⟩
        have hw := ih.2 hz hy
        simpa only [he, reflection_reflection] using hw
      · obtain ⟨k, hk, hw⟩ := ih.1 (le_of_not_gt hz) hy
        exact ⟨k + 1, by omega, .head ⟨c, hs.1⟩ hw⟩
    · intro hx hy
      by_cases hz : 0 < z (P.coroot i)
      · exact .head ⟨_, hs.1.reflection_pos hx⟩ (ih.2 hz hy)
      · obtain ⟨k, hk, hw⟩ := ih.1 (le_of_not_gt hz) hy
        have hfirst := rootStep_simple (hA := hA) (i := i)
          (x := P.reflection hA i x) (by
            rw [reflection_apply_coroot_self]; linarith)
        have hw' : RootWalk P hA (P.reflection hA i x)
            (P.reflection hA i y) (k + 1 + 1) :=
          .head ⟨_, hfirst⟩ (by
            simpa only [reflection_reflection] using (RootWalk.head ⟨c, hs.1⟩ hw))
        convert hw' using 1
        omega

/-- Simple-root steps have source distance one on every integral class.
There is no dominant-conjugacy premise. -/
theorem saturatedStep_simple {i : ι} (hx : x ∈ P.integralWeights)
    (hn : x (P.coroot i) < 0) :
    SaturatedStep P hA x (P.reflection hA i x) (Dual.eval ℝ H (P.coroot i)) := by
  refine ⟨rootStep_simple hn, fun n hw ↦ ?_⟩
  obtain ⟨m, hm, hmax⟩ := hw.exists_greatest hx
  have hs := hm.saturated_of_maximal fun k hk ↦ hmax hk
  obtain ⟨k, hk, hloop⟩ := (hs.lift_positive i).1 hn.le (by
    rw [reflection_apply_coroot_self]; linarith)
  have hzero : k = 0 := (by
    simpa only [reflection_reflection] using hloop : RootWalk P hA x x k).eq_zero_of_loop hx
  have := hmax hw
  omega

/-- Negating and reversing a raw source step preserves its actual coroot. -/
theorem RootStep.neg_reverse (h : RootStep P hA x y c) :
    RootStep P hA (-y) (-x) c := by
  classical
  obtain ⟨u, j, hp, rfl, hn, hy⟩ := h
  have htwo : rootCoroot P hA u j (u.1 (P.root j)) = 2 := by
    change (u⁻¹).1 (u.1 (P.root j)) (P.coroot j) = 2
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
    exact P.root_coroot_self hA j
  have hpair : rootCoroot P hA u j (-y) = rootCoroot P hA u j x := by
    rw [map_neg, hy, map_sub, map_smul, htwo, smul_eq_mul]
    ring
  refine ⟨u, j, hp, rfl, by rwa [hpair], ?_⟩
  rw [hpair, hy]
  abel

/-- Negation reverses source walks without changing their lengths. -/
theorem RootWalk.neg_reverse {n : ℕ} (h : RootWalk P hA x y n) :
    RootWalk P hA (-y) (-x) n := by
  induction h with
  | refl => exact .refl _
  | head hs _ ih =>
    obtain ⟨c, hc⟩ := hs
    exact ih.append hc.neg_reverse.walk

/-- Negation/reversal preserves maximum-length-one saturation. -/
theorem SaturatedStep.neg_reverse (h : SaturatedStep P hA x y c) :
    SaturatedStep P hA (-y) (-x) c := by
  refine ⟨h.1.neg_reverse, fun n hn ↦ h.2 n ?_⟩
  simpa only [neg_neg] using hn.neg_reverse

/-- Saturated source walks concatenate. -/
theorem SaturatedWalk.append {m n : ℕ} (h : SaturatedWalk P hA x y m)
    (k : SaturatedWalk P hA y z n) : SaturatedWalk P hA x z (m + n) := by
  induction h with
  | refl => simpa using k
  | head hs _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (SaturatedWalk.head hs (ih k))

/-- Negation reverses saturated walks, preserving each source cover. -/
theorem SaturatedWalk.neg_reverse {n : ℕ} (h : SaturatedWalk P hA x y n) :
    SaturatedWalk P hA (-y) (-x) n := by
  induction h with
  | refl => exact .refl _
  | head hs _ ih =>
    obtain ⟨c, hc⟩ := hs
    exact ih.append (.head ⟨c, hc.neg_reverse⟩ (.refl _))

/-- The negative same-sign form of [Lit95], Lemma 4.1(c), for saturated walks. -/
theorem SaturatedWalk.reflection_neg {n : ℕ} (h : SaturatedWalk P hA x y n) {i : ι}
    (hx : x (P.coroot i) < 0) (hy : y (P.coroot i) < 0) :
    RootWalk P hA (P.reflection hA i x) (P.reflection hA i y) n := by
  have hw := (h.neg_reverse.lift_positive i).2 (by simpa using hy) (by simpa using hx)
  simpa only [map_neg, neg_neg] using hw.neg_reverse

/-- Saturation is preserved by simultaneous reflection at two negative pairings,
on arbitrary integral classes, as in [Lit95], Lemma 4.1(c). -/
theorem SaturatedStep.reflection_neg (h : SaturatedStep P hA x y c)
    (hint : x ∈ P.integralWeights) {i : ι}
    (hx : x (P.coroot i) < 0) (hy : y (P.coroot i) < 0) :
    SaturatedStep P hA (P.reflection hA i x) (P.reflection hA i y)
      (c ∘ₗ (P.reflection hA i).toLinearMap) := by
  have hraw := h.1.neg_reverse.reflection_pos (i := i) (by simpa using hy)
  refine ⟨by simpa only [map_neg, neg_neg] using hraw.neg_reverse, fun n hn ↦ ?_⟩
  have hsint : P.reflection hA i x ∈ P.integralWeights :=
    (rootStep_simple hx).integral_end hint
  obtain ⟨m, hm, hmax⟩ := hn.exists_greatest hsint
  have hs := hm.saturated_of_maximal fun k hk ↦ hmax hk
  have hw := (hs.lift_positive i).2 (by rw [reflection_apply_coroot_self]; linarith)
    (by rw [reflection_apply_coroot_self]; linarith)
  have hb := h.2 m (by simpa only [reflection_reflection] using hw)
  have := hmax hn
  omega

/-- Saturation is preserved by simultaneous reflection at two positive pairings,
on arbitrary integral classes, as in [Lit95], Lemma 4.1(c). -/
theorem SaturatedStep.reflection_pos (h : SaturatedStep P hA x y c)
    (hint : x ∈ P.integralWeights) {i : ι}
    (hx : 0 < x (P.coroot i)) (hy : 0 < y (P.coroot i)) :
    SaturatedStep P hA (P.reflection hA i x) (P.reflection hA i y)
      (c ∘ₗ (P.reflection hA i).toLinearMap) := by
  refine ⟨h.1.reflection_pos hx, fun n hn ↦ ?_⟩
  have hsint : P.reflection hA i x ∈ P.integralWeights := by
    classical
    exact fun j ↦ exists_int_apply_coroot hint ((P.coxeterSystem hA).simple i) j
  obtain ⟨m, hm, hmax⟩ := hn.exists_greatest hsint
  have hs := hm.saturated_of_maximal fun k hk ↦ hmax hk
  have hw := hs.reflection_neg (i := i) (by rw [reflection_apply_coroot_self]; linarith)
    (by rw [reflection_apply_coroot_self]; linarith)
  have hb := h.2 m (by simpa only [reflection_reflection] using hw)
  have := hmax hn
  omega

/-- Actual arbitrary-integral-orbit LS data: steps are precisely source
maximum-length-one root steps between orbit points. All interface fields are proved
from source chains, never from an assumed stability theorem or dominant representative.
This supplies the combinatorial input of [Lit95], §4, pp. 509–510. -/
noncomputable def lsData (P : Realization A ℝ H) (hA : A.IsGeneralizedCartan)
    (Λ : P.integralWeights) : LittelmannPath.LSData (P.pathSpace hA) := by
  classical
  let O : Set P.integralWeights := {x | ∃ w : P.weylGroup hA, (x : Dual ℝ H) = w.1 Λ}
  have hr (i : ι) (x : P.integralWeights) (hx : x ∈ O) :
      (P.cartanDatum hA).reflection i x ∈ O := by
    obtain ⟨w, hw⟩ := hx
    exact ⟨(P.coxeterSystem hA).simple i * w, by
      rw [coe_reflection_cartanDatum, hw, coe_simple_mul_apply]⟩
  exact {
    O := O
    Step := fun x y c ↦ x ∈ O ∧ y ∈ O ∧ SaturatedStep P hA x y c
    reflection_mem := hr
    step_mem := fun _ _ _ h ↦ ⟨h.1, h.2.1⟩
    exists_int := fun _ _ _ h μ ↦ h.2.2.1.integral_weight μ
    step_reflection_pos := fun i x y c h hx hy ↦ by
      refine ⟨hr i x h.1, hr i y h.2.1, ?_⟩
      have hs := h.2.2.reflection_pos x.2
        (coroot_cartanDatum_pos_iff.mp hx) (coroot_cartanDatum_pos_iff.mp hy)
      convert hs using 1
      · exact coe_reflection_cartanDatum P hA i x
      · exact coe_reflection_cartanDatum P hA i y
      · ext v
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, pathSpace_reflection]
    step_reflection_neg := fun i x y c h hx hy ↦ by
      refine ⟨hr i x h.1, hr i y h.2.1, ?_⟩
      have hs := h.2.2.reflection_neg x.2
        (coroot_cartanDatum_neg_iff.mp hx) (coroot_cartanDatum_neg_iff.mp hy)
      convert hs using 1
      · exact coe_reflection_cartanDatum P hA i x
      · exact coe_reflection_cartanDatum P hA i y
      · ext v
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, pathSpace_reflection]
    step_simple := fun i x hx hi ↦ by
      refine ⟨hr i x hx, hx, ?_⟩
      have hs := saturatedStep_simple (hA := hA)
        ((P.cartanDatum hA).reflection i x).2 (i := i) (by
          rw [coe_reflection_cartanDatum, reflection_apply_coroot_self]
          exact neg_neg_of_pos (coroot_cartanDatum_pos_iff.mp hi))
      have hc : (P.pathSpace hA).coroot i = Dual.eval ℝ H (P.coroot i) := by
        ext v
        exact pathSpace_coroot P hA i v
      simpa only [coe_reflection_cartanDatum, reflection_reflection, hc] using hs
    step_neg_pos := fun i x y c h hx hy ↦ by
      obtain ⟨hc, he⟩ := h.2.2.crossing (Or.inl
        ⟨(coroot_cartanDatum_neg_iff.mp hx).le, coroot_cartanDatum_pos_iff.mp hy⟩)
      refine ⟨Subtype.ext ?_, Or.inl ?_⟩
      · simpa only [coe_reflection_cartanDatum] using he
      · ext v
        rw [hc, pathSpace_coroot]
        rfl
    coroot_nonpos_of_step := fun i x y c h hx ↦ by
      by_contra hy
      have hyp := coroot_cartanDatum_pos_iff.mp (lt_of_not_ge hy)
      have hxz := coroot_cartanDatum_eq_zero_iff.mp hx
      obtain ⟨_, he⟩ := h.2.2.crossing (Or.inl ⟨hxz.le, hyp⟩)
      have hye := congrArg (fun v : Dual ℝ H ↦ v (P.coroot i)) he
      rw [reflection_apply_coroot_self, hxz] at hye
      linarith
    coroot_ne_zero_of_step := fun i x y c h hx hy ↦ by
      have hxn := coroot_cartanDatum_neg_iff.mp hx
      have hyz := coroot_cartanDatum_eq_zero_iff.mp hy
      obtain ⟨_, he⟩ := h.2.2.crossing (Or.inr ⟨hxn, hyz.ge⟩)
      have hye := congrArg (fun v : Dual ℝ H ↦ v (P.coroot i)) he
      rw [reflection_apply_coroot_self, hyz] at hye
      linarith }

/-- The source relation is literally the relation used by arbitrary-class LS data;
no Bruhat representatives or dominant-orbit premise occur. -/
theorem lsData_step_iff (Λ : P.integralWeights) (x y : P.integralWeights)
    (c : Dual ℝ (Dual ℝ H)) :
    (lsData P hA Λ).Step x y c ↔
      (∃ w : P.weylGroup hA, (x : Dual ℝ H) = w.1 Λ) ∧
      (∃ w : P.weylGroup hA, (y : Dual ℝ H) = w.1 Λ) ∧
      SaturatedStep P hA x y c := Iff.rfl

end Matrix.Realization.LSGeneralClass
