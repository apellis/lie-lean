/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroupExchange
import LieLean.RepresentationTheory.Crystal.Path.AChains.Construction
import LieLean.RepresentationTheory.Crystal.Path.Linking

/-!
# The positive-root compatibility relation for gluing LS paths

## Main definitions

* `Matrix.Realization.GluingPrecedes`: the relation `ν ▷ μ` of [Lit95], p. 514.
  It quantifies over every actual positive real root `u αⱼ`, with the very same
  coroot functional as the source `a`-chains in `Path.AChains.Roots`.

## Main results

* `GluingPrecedes.reflection_iff`: the exact simple-coroot obstruction to simultaneous
  reflection of a compatible pair.
* `GluingPrecedes.reflection_of_neg`: [Lit95], Lemma 5.2(a).
* `GluingPrecedes.reflection_of_pos_of_nonneg`: [Lit95], Lemma 5.2(b).

This is the earliest missing gluing-stability input: Proposition 5.6, p. 515, invokes
Lemma 5.2 to prove compatibility of the reflected gluing directions. The positive-root
permutation and compatibility at the exceptional root are proved, not hypotheses.
The source's rational weights are included in the proved, stronger real-weight statement.
There is no dominance assumption on either weight and no restriction to a finite Weyl
group, rank one, or a bounded root-operator word. Symmetrizability is unnecessary for
this particular lemma. No stability or integrality of a path component is assumed.

This file does not yet construct the two cut-point chains in Definition 5.3, prove
Lemma 5.5, or complete Proposition 5.6. In particular `GluingPrecedes` is the sign
condition of a gluing pair, NOT by itself a complete gluing pair. Nor does this file
extend the source isomorphism theorem to arbitrary continuous paths or identify
pause-allowing parametrizations with order automorphisms.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), 499–525, p. 514, definition preceding Lemma 5.2 and Lemma 5.2(a,b);
application in Proposition 5.6, p. 515.
-/

open Module

namespace Matrix.Realization

open LSAChainBridgeRoots

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} (P : Realization A ℝ H) (hA : A.IsGeneralizedCartan)

/-- The source compatibility relation `ν ▷ μ`: for every positive real root `β`,
`⟨ν, β∨⟩ < 0` implies `⟨μ, β∨⟩ ≤ 0`. Positivity is a nonnegative integral
simple-root expansion and the coroot is the actual `a`-chain coroot functional.
This is [Lit95], p. 514, without a dominance restriction on either direction. -/
def GluingPrecedes (ν μ : Dual ℝ H) : Prop :=
  ∀ (u : P.weylGroup hA) (j : ι),
    (∃ k : ι → ℤ, 0 ≤ k ∧ u.1 (P.root j) = P.rootOf k) →
    rootCoroot P hA u j ν < 0 → rootCoroot P hA u j μ ≤ 0

namespace LSAChainBridgeRoots

/-- The coroot attached to the identity witness is the simple coroot functional. -/
theorem rootCoroot_one (j : ι) (ν : Dual ℝ H) :
    rootCoroot P hA 1 j ν = ν (P.coroot j) := rfl

/-- Covariance of the actual source coroot functional under simple reflection. -/
theorem rootCoroot_simple_mul [DecidableEq ι] (i : ι) (u : P.weylGroup hA) (j : ι)
    (ν : Dual ℝ H) :
    rootCoroot P hA ((P.coxeterSystem hA).simple i * u) j ν =
      rootCoroot P hA u j (P.reflection hA i ν) := by
  simp only [rootCoroot, LinearMap.comp_apply, LinearEquiv.coe_coe, Dual.eval_apply,
    _root_.mul_inv_rev, CoxeterSystem.inv_simple, Subgroup.coe_mul,
    LinearEquiv.mul_apply, coxeterSystem_simple]

/-- A positive real root other than `αᵢ` remains positive under `sᵢ`.
This proves the nonexceptional-root step in [Lit95], Lemma 5.2, directly for the
same positive-root witnesses used by `SourceStep`. -/
theorem positive_root_simple_mul [DecidableEq ι] {u : P.weylGroup hA} {j i : ι}
    (hp : ∃ k : ι → ℤ, 0 ≤ k ∧ u.1 (P.root j) = P.rootOf k)
    (hne : u.1 (P.root j) ≠ P.root i) :
    ∃ k : ι → ℤ, 0 ≤ k ∧
      ((P.coxeterSystem hA).simple i * u).1 (P.root j) = P.rootOf k := by
  rcases P.apply_root_nonneg_or_nonpos hA
    ((P.coxeterSystem hA).simple i * u).property j with hpos | hneg
  · exact hpos
  · obtain ⟨k, hk, huk⟩ := hp
    obtain ⟨l, hl, hrl⟩ := hneg
    have heq := P.eq_root_of_reflection_apply hA u.property hk huk hl
      (by simpa only [coe_simple_mul_apply] using hrl)
    exact (hne heq).elim

/-- If a real-root witness is the simple root `αᵢ`, its coroot functional is
exactly the simple coroot, with no sign ambiguity. This proves the exceptional-root
step in [Lit95], Lemma 5.2, rather than assuming a root-coroot identification. -/
theorem rootCoroot_eq_simple_of_root_eq {u : P.weylGroup hA} {j i : ι}
    (hroot : u.1 (P.root j) = P.root i) (ν : Dual ℝ H) :
    rootCoroot P hA u j ν = ν (P.coroot i) := by
  classical
  have heq : (u * (P.coxeterSystem hA).simple j * u⁻¹).1 = P.reflection hA i := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coxeterSystem_simple] using
      P.mul_reflection_mul_inv_eq hA u.property hroot
  have happ := conjugate_apply P hA u j ν
  rw [heq, reflection_apply, hroot] at happ
  exact smul_left_injective ℝ (P.linearIndependent_root.ne_zero i)
    (sub_right_injective happ.symm)

end LSAChainBridgeRoots

variable {P hA} {ν μ : Dual ℝ H}

/-- In particular compatibility controls each simple-coroot pairing. -/
theorem GluingPrecedes.simple (h : P.GluingPrecedes hA ν μ) {i : ι}
    (hν : ν (P.coroot i) < 0) : μ (P.coroot i) ≤ 0 := by
  classical
  exact h 1 i ⟨Pi.single i 1, fun j ↦ by
    by_cases hj : j = i <;> simp [hj], by simp⟩ hν

/-- The complete obstruction to simultaneous simple reflection is at the reflected
simple root. Every other positive real root stays positive under reflection.
This strengthens the two sufficient cases of [Lit95], Lemma 5.2, p. 514. -/
theorem GluingPrecedes.reflection_iff (h : P.GluingPrecedes hA ν μ) (i : ι) :
    P.GluingPrecedes hA (P.reflection hA i ν) (P.reflection hA i μ) ↔
      (0 < ν (P.coroot i) → 0 ≤ μ (P.coroot i)) := by
  classical
  constructor
  · intro hs hν
    have hμ := hs.simple (i := i) (by
      rw [reflection_apply_coroot_self]
      exact neg_neg_of_pos hν)
    rwa [reflection_apply_coroot_self, neg_nonpos] at hμ
  · intro hi u j hp hν
    by_cases hroot : u.1 (P.root j) = P.root i
    · rw [rootCoroot_eq_simple_of_root_eq P hA hroot,
        reflection_apply_coroot_self] at hν ⊢
      exact neg_nonpos.mpr (hi (neg_neg_iff_pos.mp hν))
    · have ht := h ((P.coxeterSystem hA).simple i * u) j
        (positive_root_simple_mul P hA hp hroot)
      rw [rootCoroot_simple_mul, rootCoroot_simple_mul] at ht
      exact ht hν

/-- [Lit95], Lemma 5.2(a), p. 514: if `ν ▷ μ` and the simple-coroot pairing
of `ν` is negative, the reflected pair is still compatible. -/
theorem GluingPrecedes.reflection_of_neg (h : P.GluingPrecedes hA ν μ) {i : ι}
    (hν : ν (P.coroot i) < 0) :
    P.GluingPrecedes hA (P.reflection hA i ν) (P.reflection hA i μ) :=
  (h.reflection_iff i).mpr fun hpos ↦ False.elim ((not_lt_of_ge hν.le) hpos)

/-- [Lit95], Lemma 5.2(b), p. 514: if `ν ▷ μ`, the simple-coroot pairing of
`ν` is positive and that of `μ` is nonnegative, the reflected pair is compatible.
The positivity premise is retained to match the source statement exactly. -/
theorem GluingPrecedes.reflection_of_pos_of_nonneg
    (h : P.GluingPrecedes hA ν μ) {i : ι}
    (hν : 0 < ν (P.coroot i)) (hμ : 0 ≤ μ (P.coroot i)) :
    P.GluingPrecedes hA (P.reflection hA i ν) (P.reflection hA i μ) := by
  apply (h.reflection_iff i).mpr
  simpa only [hν, true_implies] using hμ

end Matrix.Realization
