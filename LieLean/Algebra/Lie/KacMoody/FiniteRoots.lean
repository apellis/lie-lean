/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.FiniteType
import LieLean.LinearAlgebra.Matrix.Cartan.TitsCone.Finite
import LieLean.LinearAlgebra.Matrix.Cartan.TitsCone.FiniteConverse

/-!
# Finiteness of the full Kac–Moody root system

## Main results

The finite Weyl group forces every full root to be real, without assuming finite type
or symmetrizability. Positive imaginary roots remain positive under every Weyl element.
Averaging a functional positive on the simple roots over the finite Weyl group gives
an invariant functional, which annihilates every simple root. It cannot be positive
on an entire positive imaginary orbit.

## References

Kac, *Infinite dimensional Lie algebras*, third edition, Proposition 3.12(e).
This averaging argument is reconstructed, not transcribed from the printed proof.
The statements concern the existing full root-space-defined `KacMoodyAlgebra.roots`,
not merely real roots. The full-root/Weyl equivalence holds over every characteristic-zero
field, including the source's complex field. Positivity is applied to integral root heights,
not to the scalar field. Only the final Tits-cone equivalence requires an ordered field.
Finite-dimensionality and symmetrizability are not additional hypotheses.
-/

open Module

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsGeneralizedCartan)

omit [DecidableEq ι] in
/-- Finite real roots imply a finite Weyl group, using its faithful action on simple roots.
This extracts the argument used in the existing finite-type theorem without its extra hypothesis. -/
theorem finite_weylGroup_of_finite_realRoots (h : (P.realRoots hA).Finite) :
    Finite (P.weylGroup hA) := by
  have := h.to_subtype
  let f : P.weylGroup hA → ι → P.realRoots hA :=
    fun w i ↦ ⟨w.1 (P.root i), w.1, w.2, i, rfl⟩
  refine Finite.of_injective f fun w v heq ↦ ?_
  have hone : v.1⁻¹ * w.1 = 1 := by
    refine P.eq_one_of_forall_apply_root_eq hA (mul_mem (inv_mem v.2) w.2) fun i ↦ ?_
    have hi := congrArg Subtype.val (congrFun heq i)
    simp only [f] at hi
    rw [LinearEquiv.mul_apply, hi, ← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  exact Subtype.ext (inv_mul_eq_one.mp hone).symm

/-- Finiteness of the full root system implies finiteness of the Weyl group.
This implication of Kac Proposition 3.12(e) works over any characteristic-zero field. -/
theorem finite_weylGroup_of_finite_roots (h : (KacMoodyAlgebra.roots P).Finite) :
    Finite (P.weylGroup hA) :=
  P.finite_weylGroup_of_finite_realRoots hA
    (h.subset (KacMoodyAlgebra.realRoots_subset_roots P hA))

namespace KacMoodyAlgebra

/-- Every Weyl translate of a positive non-real full root is positive.
Reconstructed from the simple-reflection positivity theorem (Kac, Lemma 3.7). -/
theorem apply_mem_posWeights_of_not_mem_realRoots {μ : Dual K H}
    (hμ : μ ∈ roots P) (hp : μ ∈ P.posWeights) (hn : μ ∉ P.realRoots hA)
    {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA) :
    w μ ∈ P.posWeights := by
  have hall : w μ ∈ roots P ∧ w μ ∈ P.posWeights ∧ w μ ∉ P.realRoots hA := by
    refine P.weylGroup_induction hA
      (p := fun w ↦ w μ ∈ roots P ∧ w μ ∈ P.posWeights ∧ w μ ∉ P.realRoots hA)
      ⟨hμ, hp, hn⟩ (fun i v ih ↦ ?_) hw
    refine ⟨apply_mem_roots P hA (P.reflection_mem_weylGroup hA i) ih.1,
      reflection_mem_posWeights P hA ih.1 ih.2.1 (fun heq ↦ ?_), ?_⟩
    · exact ih.2.2 (heq ▸ P.root_mem_realRoots hA i)
    · intro hr
      have hh := P.apply_mem_realRoots hA (P.reflection_mem_weylGroup hA i) hr
      rw [LinearEquiv.mul_apply, P.reflection_reflection hA] at hh
      exact ih.2.2 hh
  exact hall.2.1

omit [DecidableEq ι] [CharZero K] in
/-- The dual Weyl vector evaluates a root-lattice weight to its integral height. -/
lemma transpose_rho_rootOf (k : ι → ℤ) :
    P.transpose.rho (P.rootOf k) = (height k : K) := by
  classical
  have hr (j : ι) : P.transpose.rho (P.root j) = 1 := P.transpose.rho_coroot j
  simp [rootOf_apply, hr, height]

omit [DecidableEq ι] in
/-- Averaging any functional over a finite Weyl group annihilates every simple root:
right multiplication by its reflection negates the sum. -/
lemma sum_apply_root_eq_zero [Fintype (P.weylGroup hA)]
    (φ : Dual K (Dual K H)) (i : ι) :
    ∑ w : P.weylGroup hA, φ (w.1 (P.root i)) = 0 := by
  let r : P.weylGroup hA := ⟨P.reflection hA i, P.reflection_mem_weylGroup hA i⟩
  have heq : (∑ w : P.weylGroup hA, φ (w.1 (P.root i))) =
      ∑ w : P.weylGroup hA, -φ (w.1 (P.root i)) := by
    refine Fintype.sum_equiv (Equiv.mulRight r) _ _ fun w ↦ ?_
    change φ (w.1 (P.root i)) = -φ (w.1 (P.reflection hA i (P.root i)))
    simp
  rw [Finset.sum_neg_distrib] at heq
  exact CharZero.eq_neg_self_iff.mp heq

/-- For a finite Weyl group, every full root is real (no imaginary roots).
This reconstructed averaging proof needs neither finite type nor symmetrizability. -/
theorem roots_eq_realRoots_of_finite_weylGroup [Finite (P.weylGroup hA)] :
    roots P = P.realRoots hA := by
  classical
  let _ := Fintype.ofFinite (P.weylGroup hA)
  have hpositive {μ : Dual K H} (hμ : μ ∈ roots P) (hp : μ ∈ P.posWeights) :
      μ ∈ P.realRoots hA := by
    by_contra hn
    choose k hk hkw using fun w : P.weylGroup hA ↦
      apply_mem_posWeights_of_not_mem_realRoots P hA hμ hp hn w.2
    have hpos : 0 < ∑ w : P.weylGroup hA, height (k w) := by
      apply Finset.sum_pos _ Finset.univ_nonempty
      intro w _
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (hk w).2
      exact Finset.sum_pos' (fun j _ ↦ (hk w).1 j)
        ⟨i, Finset.mem_univ _, lt_of_le_of_ne ((hk w).1 i) (Ne.symm hi)⟩
    have hcast : (∑ w : P.weylGroup hA, height (k w) : ℤ) = 0 ↔
        (∑ w : P.weylGroup hA, P.transpose.rho (w.1 μ)) = 0 := by
      simp_rw [← hkw, transpose_rho_rootOf, ← Int.cast_sum, Int.cast_eq_zero]
    have hne := (ne_of_gt hpos)
    obtain ⟨k, -, rfl⟩ := hp
    have hzero : ∑ w : P.weylGroup hA, P.transpose.rho (w.1 (P.rootOf k)) = 0 := by
      simp only [rootOf_apply, map_sum, map_smul, smul_eq_mul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sum_apply_root_eq_zero P hA, mul_zero]
      simp
    exact hne (hcast.mpr hzero)
  refine subset_antisymm (fun μ hμ ↦ ?_) (realRoots_subset_roots P hA)
  rcases mem_posWeights_or_mem_negWeights P hμ with hp | ⟨k, hk, hkμ⟩
  · exact hpositive hμ hp
  · have hneg : -μ ∈ P.posWeights := ⟨k, hk, by simp [← hkμ]⟩
    simpa using P.neg_mem_realRoots hA (hpositive (neg_mem_roots P hμ) hneg)

/-- Finite Weyl group implies finiteness of the full root-space-defined root system.
Kac Proposition 3.12(e), reconstructed over arbitrary characteristic-zero fields. -/
theorem finite_roots_of_finite_weylGroup [Finite (P.weylGroup hA)] :
    (roots P).Finite := by
  rw [roots_eq_realRoots_of_finite_weylGroup P hA]
  refine (Set.finite_range (fun p : P.weylGroup hA × ι ↦ p.1.1 (P.root p.2))).subset ?_
  rintro μ ⟨w, hw, i, rfl⟩
  exact ⟨(⟨w, hw⟩, i), rfl⟩

/-- Full root-system finiteness is equivalent to Weyl-group finiteness,
including the absence of imaginary roots in the finite case (Kac Proposition 3.12(e)). -/
theorem finite_roots_iff_finite_weylGroup :
    (roots P).Finite ↔ Finite (P.weylGroup hA) := by
  constructor
  · exact P.finite_weylGroup_of_finite_roots hA
  · intro h
    let _ := h
    exact finite_roots_of_finite_weylGroup P hA

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Finiteness of the full root system is equivalent to fullness of the existing dual Tits
cone. This combines the full-root bridge with the separately reviewed converse, and does not
replace the full root system by the positive real coroots (Kac Proposition 3.12(e)). -/
theorem finite_roots_iff_titsCone_eq_univ :
    (roots P).Finite ↔ P.titsCone hA = Set.univ :=
  (finite_roots_iff_finite_weylGroup P hA).trans
    (P.finite_weylGroup_iff_titsCone_eq_univ hA)

end KacMoodyAlgebra
end Matrix.Realization
