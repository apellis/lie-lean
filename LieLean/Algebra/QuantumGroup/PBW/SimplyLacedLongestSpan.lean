/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.SimplyLacedSpanInvariance
import LieLean.Algebra.QuantumGroup.PBW.RootVectorGeneration

/-!
# Ordered longest-word spanning in finite simply-laced type

## Main results

* `QuantumGroup.adjoin_le_span_pbwMonomial_longest_of_simplyLaced`: the positive algebra
  is contained in the actual ordered PBW span of any longest reduced word in a finite
  Coxeter system, at a nonzero parameter which is not a root of unity.
* `QuantumGroup.span_pbwMonomial_longest_of_isFiniteCartan_of_simplyLaced`: in finite
  Cartan type this span equals the positive algebra.

Every simple reflection is a left descent of the longest element. Choose a reduced word
starting with it, increment the first exponent, and use the proved reduced-word span
independence. Algebra-generation induction then gives spanning. The reverse inclusion
uses the existing actual root-vector membership theorem, with finite Cartan hypotheses;
it is not inferred merely from finiteness of an abstract Coxeter group.

No transcendental-parameter dimension or basis theorem is used. No linear independence,
basis, triangular decomposition, or non-simply-laced spanning conclusion is asserted.

## References

Reconstructed from the repository's longest-element, Matsumoto span-invariance, and
finite-type root-vector membership theorems.
-/

open LieLean

noncomputable section

namespace CoxeterSystem

variable {B k A : Type*} [Field k] [Ring A] [Algebra k A]
  (T : B → A ≃ₐ[k] A) (E : B → A)

lemma pbwMonomial_zero_exponents (w : List B) :
    pbwMonomial T E w (fun _ ↦ 0) = 1 := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [pbwMonomial_cons, ih]

lemma one_mem_pbwSpan (w : List B) :
    (1 : A) ∈ Submodule.span k (Set.range (pbwMonomial T E w)) := by
  rw [← pbwMonomial_zero_exponents T E w]
  exact Submodule.subset_span ⟨_, rfl⟩

lemma mul_mem_pbwSpan_cons (i : B) (w : List B) {x : A}
    (hx : x ∈ Submodule.span k (Set.range (pbwMonomial T E (i :: w)))) :
    E i * x ∈ Submodule.span k (Set.range (pbwMonomial T E (i :: w))) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, rfl⟩ := hx
    have he : E i * pbwMonomial T E (i :: w) c =
        pbwMonomial T E (i :: w) (Fin.cons (c 0 + 1) (fun n ↦ c n.succ)) := by
      change E i * (E i ^ c 0 * T i (pbwMonomial T E w (fun n ↦ c n.succ))) =
        E i ^ (c 0 + 1) * T i (pbwMonomial T E w (fun n ↦ c n.succ))
      rw [pow_succ', mul_assoc]
    rw [he]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [mul_smul_comm] using Submodule.smul_mem _ a hx

lemma exists_reduced_cons_longest {W : Type*} [Group W] [Finite W]
    {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (i : B) :
    ∃ u : List B, cs.IsReduced (i :: u) ∧ cs.wordProd (i :: u) = cs.longestElement := by
  obtain ⟨u, hu, he⟩ := cs.exists_isReduced (cs.simple i * cs.longestElement)
  have hp : cs.wordProd (i :: u) = cs.longestElement := by
    rw [cs.wordProd_cons, ← he]
    simp
  refine ⟨u, ?_, hp⟩
  unfold IsReduced
  rw [hp, List.length_cons, ← hu.eq, ← he]
  exact ((cs.isLeftDescent_iff).mp (cs.isLeftDescent_longestElement i)).symm

end CoxeterSystem

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]
  (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hSL : D.cartanMatrix.IsSimplyLaced)
  {W : Type*} [Group W] [Finite W]
  (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W)
  {w : List I} (hw : cs.IsReduced w) (hw₀ : cs.wordProd w = cs.longestElement)

include hSL cs hw hw₀

/-- The actual ordered longest-word span is stable under left multiplication by each
simple positive generator. Reduced-word independence transports the recursion argument. -/
theorem E_mul_mem_span_pbwMonomial_longest_of_simplyLaced (i : I) {x : QuantumGroup R v}
    (hx : x ∈ Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv) (E R v) w))) :
    E R v i * x ∈ Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv) (E R v) w)) := by
  obtain ⟨u, hu, hu₀⟩ := CoxeterSystem.exists_reduced_cons_longest cs i
  have hs := span_pbwMonomial_of_isReduced_of_simplyLaced R v hv hSL cs hu hw
    (hu₀.trans hw₀.symm)
  rw [← hs] at hx ⊢
  exact CoxeterSystem.mul_mem_pbwSpan_cons _ _ i u hx

/-- Genuine ordered spanning in the forward direction, without assuming that the abstract
finite Coxeter system's root vectors lie in the positive part. -/
theorem adjoin_le_span_pbwMonomial_longest_of_simplyLaced :
    (Algebra.adjoin k (Set.range (E R v))).toSubmodule ≤
      Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
        (braidEquivOfNotRoot R hv) (E R v) w)) := by
  let S := Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
    (braidEquivOfNotRoot R hv) (E R v) w))
  have h1 : (1 : QuantumGroup R v) ∈ S := CoxeterSystem.one_mem_pbwSpan _ _ w
  intro x hx
  have hmul : ∀ y ∈ S, x * y ∈ S := by
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact fun y hy ↦ E_mul_mem_span_pbwMonomial_longest_of_simplyLaced
        R v hv hSL cs hw hw₀ i hy
    | algebraMap a =>
      intro y hy
      simpa only [Algebra.smul_def] using S.smul_mem a hy
    | add x z _ _ hx hz =>
      intro y hy
      simpa only [add_mul] using S.add_mem (hx y hy) (hz y hy)
    | mul x z _ _ hx hz =>
      intro y hy
      simpa only [mul_assoc] using hx (z * y) (hz y hy)
  simpa only [mul_one] using hmul 1 h1

/-- The actual ordered monomials of any longest reduced word span `U⁺` in finite
simply-laced Cartan type, at every nonzero non-root-of-unity parameter over any field.
Finite Cartan type supplies the hypotheses of actual positive root-vector membership. -/
theorem span_pbwMonomial_longest_of_isFiniteCartan_of_simplyLaced [Fintype I]
    (hD : D.cartanMatrix.IsFiniteCartan) :
    Submodule.span k (Set.range (CoxeterSystem.pbwMonomial
      (braidEquivOfNotRoot R hv) (E R v) w)) =
      (Algebra.adjoin k (Set.range (E R v))).toSubmodule := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨c, rfl⟩
    exact CoxeterSystem.pbwMonomial_mem _ _
      (fun n hn ↦ rootVector_mem_adjoin_of_not_root
        (fun _ _ hij ↦ hD.mul_le_three hij) hv hw n hn) c
  · exact adjoin_le_span_pbwMonomial_longest_of_simplyLaced R v hv hSL cs hw hw₀

end LieLean.QuantumGroup
