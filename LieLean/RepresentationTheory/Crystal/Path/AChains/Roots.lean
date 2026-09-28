/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Stability
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Positive real-root witnesses for concrete LS steps

## Main definitions / results

The target is the positive-real-root presentation of the concrete `lsData` covers.
All roots below are actual Weyl translates of simple roots, not arbitrary directions.

## References

Littelmann, *Paths and root operators in representation theory*, §4, pp. 509–510:
the descending relation has positive real roots and negative initial coroot pairing;
Remark 4.2 identifies dominant-orbit distance with minimal-representative length difference. Arguments here are reconstructed from reduced words.
-/

open Module

namespace Matrix.Realization.LSAChainBridgeRoots

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} (P : Realization A ℝ H) (hA : A.IsGeneralizedCartan)

/-- The actual coroot functional paired with the real root `u αⱼ`. -/
noncomputable def rootCoroot (u : P.weylGroup hA) (j : ι) : Dual ℝ (Dual ℝ H) :=
  Dual.eval ℝ H (P.coroot j) ∘ₗ (u⁻¹).1.toLinearMap

/-- Conjugate reflection formula, without a positivity assumption. -/
theorem conjugate_apply (u : P.weylGroup hA) (j : ι) (μ : Dual ℝ H) :
    (u * (P.coxeterSystem hA).simple j * u⁻¹).1 μ =
      μ - rootCoroot P hA u j μ • u.1 (P.root j) := by
  have huu : u.1 ((u⁻¹).1 μ) = μ := by
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
    rfl
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, coxeterSystem_simple,
    reflection_apply, map_sub, map_smul, huu, rootCoroot, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Dual.eval_apply]

/-- Reduced-word inversions admit positive real-root witnesses with nonpositive pairing
on a dominant orbit point. Reconstructed proof of the root orientation used in [Lit] §4. -/
theorem inversion_positive_witness {Λ : Dual ℝ H} (hΛ : P.IsDominantIntegral Λ)
    {m t : P.weylGroup hA} (ht : (P.coxeterSystem hA).IsLeftInversion m t) :
    ∃ (u : P.weylGroup hA) (j : ι),
      t = u * (P.coxeterSystem hA).simple j * u⁻¹ ∧
      (∃ k : ι → ℤ, 0 ≤ k ∧ u.1 (P.root j) = P.rootOf k) ∧
      rootCoroot P hA u j (m.1 Λ) ≤ 0 := by
  let cs := P.coxeterSystem hA
  obtain ⟨ω, hω, hmω⟩ := cs.exists_isReduced m
  have hmem : t ∈ cs.leftInvSeq ω := by
    apply CoxeterSystem.IsLeftInversion.mem_leftInvSeq
    rwa [← hmω]
  obtain ⟨r, hr, hrt⟩ := List.mem_iff_getElem.mp hmem
  have hrω : r < ω.length := by simpa using hr
  rw [cs.getElem_leftInvSeq ω r hrω] at hrt
  let u := cs.wordProd (ω.take r)
  let j := ω[r]
  let q := cs.wordProd (ω.drop (r + 1))
  have htake : ω.take (r + 1) = ω.take r ++ [j] := List.take_succ_eq_append_getElem hrω
  have hdrop : ω.drop r = j :: ω.drop (r + 1) := List.drop_eq_getElem_cons hrω
  have hum : m = u * cs.simple j * q := by
    rw [hmω, ← List.take_append_drop r ω, hdrop, cs.wordProd_append, cs.wordProd_cons]
    simp only [u, q, mul_assoc]
  have huLen : cs.length u = r := by
    simpa [u, List.length_take, Nat.min_eq_left hrω.le] using (hω.take r).eq
  have husLen : cs.length (u * cs.simple j) = r + 1 := by
    have hh := (hω.take (r + 1)).eq
    rw [htake, cs.wordProd_append, cs.wordProd_singleton] at hh
    simpa [u, List.length_take, Nat.min_eq_left hrω.le] using hh
  have hqLen : cs.length q = ω.length - (r + 1) := by
    simpa [q] using (hω.drop (r + 1)).eq
  have hsqLen : cs.length (cs.simple j * q) = ω.length - r := by
    have hh := (hω.drop r).eq
    rw [hdrop, cs.wordProd_cons] at hh
    simp only [List.length_cons, List.length_drop] at hh
    dsimp [q]
    omega
  have huPos : ¬cs.IsRightDescent u j := by
    change ¬cs.length (u * cs.simple j) < cs.length u
    omega
  have hqPos : ¬cs.IsLeftDescent q j := by
    change ¬cs.length (cs.simple j * q) < cs.length q
    omega
  refine ⟨u, j, hrt.symm, (P.not_isRightDescent_coxeterSystem_iff hA).mp huPos, ?_⟩
  have hpair := apply_coroot_nonneg_of_not_isLeftDescent hΛ hqPos
  have hcancel : (u⁻¹).1 (m.1 Λ) = (cs.simple j * q).1 Λ := by
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hum]
    congr 2
    group
  change (u⁻¹).1 (m.1 Λ) (P.coroot j) ≤ 0
  rw [hcancel, coe_simple_mul_apply, reflection_apply_coroot_self]
  exact neg_nonpos.mpr hpair

/-- Equal conjugate reflections have coroot functionals equal up to sign. -/
theorem rootCoroot_eq_or_neg {u v : P.weylGroup hA} {i j : ι}
    (h : u * (P.coxeterSystem hA).simple i * u⁻¹ =
      v * (P.coxeterSystem hA).simple j * v⁻¹) :
    rootCoroot P hA u i = rootCoroot P hA v j ∨
      rootCoroot P hA u i = -rootCoroot P hA v j := by
  have hc : (v⁻¹ * u) * (P.coxeterSystem hA).simple i * (v⁻¹ * u)⁻¹ =
      (P.coxeterSystem hA).simple j := by
    calc
      _ = v⁻¹ * (u * (P.coxeterSystem hA).simple i * u⁻¹) * v := by group
      _ = _ := by rw [h]; group
  have happ (μ : Dual ℝ H) :
      ((v⁻¹ * u)⁻¹).1 ((v⁻¹).1 μ) = (u⁻¹).1 μ := by
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul]
    congr 2
    group
  rcases eval_comp_eq_or_eq_neg hc with hc | hc
  · left
    ext μ
    have hh := congrArg (fun f : Dual ℝ (Dual ℝ H) ↦ f ((v⁻¹).1 μ)) hc
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Dual.eval_apply, happ,
      rootCoroot] using hh
  · right
    ext μ
    have hh := congrArg (fun f : Dual ℝ (Dual ℝ H) ↦ f ((v⁻¹).1 μ)) hc
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Dual.eval_apply, happ,
      rootCoroot, LinearMap.neg_apply] using hh

/-- Source-style saturated descending step on a dominant orbit: explicit minimal
representatives and Bruhat cover, together with a positive real root and negative pairing.
Positivity is a nonnegative integral simple-root expansion; the root is automatically nonzero
because it is `u αⱼ`. This uses Remark 4.2's length-one presentation, not a new distance axiom. -/
def SourceStep (Λ : Dual ℝ H) (x y : P.integralWeights)
    (c : Dual ℝ (Dual ℝ H)) : Prop :=
  ∃ m n : P.weylGroup hA, P.IsMinRep hA Λ m ∧ P.IsMinRep hA Λ n ∧
    (x : Dual ℝ H) = m.1 Λ ∧ (y : Dual ℝ H) = n.1 Λ ∧
    (P.coxeterSystem hA).BruhatLE n m ∧
    (P.coxeterSystem hA).length n + 1 = (P.coxeterSystem hA).length m ∧
    ∃ (u : P.weylGroup hA) (j : ι),
      n = u * (P.coxeterSystem hA).simple j * u⁻¹ * m ∧
      c = rootCoroot P hA u j ∧
      (∃ k : ι → ℤ, 0 ≤ k ∧ u.1 (P.root j) = P.rootOf k) ∧ c (x : Dual ℝ H) < 0

variable {P hA} {Λ : Dual ℝ H} (hΛ : P.IsDominantIntegral Λ)
  {x y : P.integralWeights} {c : Dual ℝ (Dual ℝ H)}

/-- Forgetting the source orientation gives the existing concrete LS step. -/
theorem SourceStep.step (h : SourceStep P hA Λ x y c) : (P.lsData hA hΛ).Step x y c := by
  obtain ⟨m, n, hm, hn, hx, hy, hb, hl, u, j, he, hc, -, -⟩ := h
  exact ⟨m, n, hm, hn, hx, hy, hb, hl, u, j, he, hc⟩

/-- Every concrete LS cover has a positive-root, negative-pairing source witness with
coroot equal to the original one up to sign. The minimal representatives are retained.
Reconstructed reduced-word proof of the orientation in [Lit] §4, pp. 509–510. -/
theorem step_exists_sourceStep (h : (P.lsData hA hΛ).Step x y c) :
    ∃ d, SourceStep P hA Λ x y d ∧ (d = c ∨ d = -c) := by
  obtain ⟨m, n, hm, hn, hx, hy, hb, hl, u, j, he, rfl⟩ := h
  let t := u * (P.coxeterSystem hA).simple j * u⁻¹
  have ht : (P.coxeterSystem hA).IsLeftInversion m t := by
    refine ⟨⟨u, j, rfl⟩, ?_⟩
    change (P.coxeterSystem hA).length (t * m) < (P.coxeterSystem hA).length m
    rw [← he]
    omega
  obtain ⟨v, i, htv, hp, hc⟩ := inversion_positive_witness P hA hΛ ht
  have hnvm : n = (v * (P.coxeterSystem hA).simple i * v⁻¹) * m := he.trans (by rw [← htv])
  have hact : (y : Dual ℝ H) = (x : Dual ℝ H) -
      rootCoroot P hA v i (x : Dual ℝ H) • v.1 (P.root i) := by
    rw [hy, hnvm, Subgroup.coe_mul, LinearEquiv.mul_apply, conjugate_apply, ← hx]
  have hne : rootCoroot P hA v i (x : Dual ℝ H) ≠ 0 := by
    intro hz
    rw [hz, zero_smul, sub_zero] at hact
    have hlen := hm n (hy.symm.trans (hact.trans hx))
    omega
  have hneg : rootCoroot P hA v i (x : Dual ℝ H) < 0 :=
    lt_of_le_of_ne (hx ▸ hc) hne
  refine ⟨rootCoroot P hA v i,
    ⟨m, n, hm, hn, hx, hy, hb, hl, v, i, hnvm, rfl, hp, hneg⟩, ?_⟩
  exact rootCoroot_eq_or_neg P hA htv.symm

/-- Replacing `u` by `u rⱼ` changes the coroot sign and not its reflection. -/
theorem rootCoroot_mul_simple (u : P.weylGroup hA) (j : ι) :
    rootCoroot P hA (u * (P.coxeterSystem hA).simple j) j =
      -rootCoroot P hA u j := by
  ext μ
  simp only [rootCoroot, LinearMap.comp_apply, LinearEquiv.coe_coe, Dual.eval_apply,
    LinearMap.neg_apply, _root_.mul_inv_rev, CoxeterSystem.inv_simple, Subgroup.coe_mul,
    LinearEquiv.mul_apply, coxeterSystem_simple, reflection_apply_coroot_self]

/-- Concrete LS steps are invariant under changing only the coroot sign. -/
theorem step_neg (h : (P.lsData hA hΛ).Step x y c) : (P.lsData hA hΛ).Step x y (-c) := by
  obtain ⟨m, n, hm, hn, hx, hy, hb, hl, u, j, he, hc⟩ := h
  refine ⟨m, n, hm, hn, hx, hy, hb, hl, u * (P.coxeterSystem hA).simple j, j, ?_, ?_⟩
  · rw [he]
    congr 1
    rw [_root_.mul_inv_rev, CoxeterSystem.inv_simple]
    simp only [mul_assoc, CoxeterSystem.simple_mul_simple_cancel_left]
  · change -c = rootCoroot P hA (u * (P.coxeterSystem hA).simple j) j
    rw [rootCoroot_mul_simple]
    exact congrArg Neg.neg hc

/-- Exactly one of the two coroot orientations of an LS step has negative initial pairing;
that orientation is the positive-real-root source step. -/
theorem sourceStep_iff_step_and_neg :
    SourceStep P hA Λ x y c ↔ (P.lsData hA hΛ).Step x y c ∧ c (x : Dual ℝ H) < 0 := by
  constructor
  · intro h
    refine ⟨h.step hΛ, ?_⟩
    obtain ⟨m, n, hm, hn, hx, hy, hb, hl, u, j, he, hc, hp, hneg⟩ := h
    exact hneg
  · rintro ⟨h, hneg⟩
    obtain ⟨d, hd, hd'⟩ := step_exists_sourceStep hΛ h
    rcases hd' with rfl | rfl
    · exact hd
    · obtain ⟨m, n, hm, hn, hx, hy, hb, hl, u, j, he, hc, hp, hneg'⟩ := hd
      simp only [LinearMap.neg_apply] at hneg'
      linarith

/-- The precise fixed-coroot comparison: a concrete step is a source step for `c` or `-c`. -/
theorem step_iff_sourceStep_or_neg :
    (P.lsData hA hΛ).Step x y c ↔
      SourceStep P hA Λ x y c ∨ SourceStep P hA Λ x y (-c) := by
  constructor
  · intro h
    obtain ⟨d, hd, hd'⟩ := step_exists_sourceStep hΛ h
    rcases hd' with rfl | rfl
    · exact Or.inl hd
    · exact Or.inr hd
  · rintro (h | h)
    · exact h.step hΛ
    · simpa only [neg_neg] using step_neg hΛ (h.step hΛ)

/-- Forgetting the coroot label gives exactly the same source and concrete covers. -/
theorem exists_step_iff_exists_sourceStep :
    (∃ c, (P.lsData hA hΛ).Step x y c) ↔ ∃ c, SourceStep P hA Λ x y c := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨d, hd, -⟩ := step_exists_sourceStep hΛ hc
    exact ⟨d, hd⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.step hΛ⟩

/-- A source step supplies a genuinely nonzero positive integral real root and the actual
reflection formula; no root-lattice displacement is smuggled into its hypotheses. -/
theorem SourceStep.exists_positive_root (h : SourceStep P hA Λ x y c) :
    ∃ (u : P.weylGroup hA) (j : ι) (k : ι → ℤ),
      0 ≤ k ∧ k ≠ 0 ∧ u.1 (P.root j) = P.rootOf k ∧
      c = rootCoroot P hA u j ∧
      (y : Dual ℝ H) = (x : Dual ℝ H) - c (x : Dual ℝ H) • P.rootOf k := by
  obtain ⟨m, n, hm, hn, hx, hy, hb, hl, u, j, he, hc, ⟨k, hk, huk⟩, hneg⟩ := h
  have hk0 : k ≠ 0 := by
    intro hz
    rw [hz, map_zero, LinearEquiv.map_eq_zero_iff] at huk
    exact P.linearIndependent_root.ne_zero j huk
  refine ⟨u, j, k, hk, hk0, huk, hc, ?_⟩
  rw [hy, he, Subgroup.coe_mul, LinearEquiv.mul_apply, conjugate_apply, ← hx, ← hc, huk]

/-- Source `a`-integrality is unchanged by the necessary coroot orientation. This is the
single-cover bridge for the `a`-chain definition on [Lit] p. 510. -/
theorem exists_step_integral_iff_exists_sourceStep_integral (a : ℝ) :
    (∃ c, (P.lsData hA hΛ).Step x y c ∧ ∃ z : ℤ, a * c (x : Dual ℝ H) = z) ↔
      ∃ c, SourceStep P hA Λ x y c ∧ ∃ z : ℤ, a * c (x : Dual ℝ H) = z := by
  constructor
  · rintro ⟨c, hc, z, hz⟩
    obtain ⟨d, hd, hd'⟩ := step_exists_sourceStep hΛ hc
    refine ⟨d, hd, ?_⟩
    rcases hd' with rfl | rfl
    · exact ⟨z, hz⟩
    · refine ⟨-z, ?_⟩
      simp only [LinearMap.neg_apply, mul_neg, hz, Int.cast_neg]
  · rintro ⟨c, hc, z, hz⟩
    exact ⟨c, hc.step hΛ, z, hz⟩

end Matrix.Realization.LSAChainBridgeRoots
