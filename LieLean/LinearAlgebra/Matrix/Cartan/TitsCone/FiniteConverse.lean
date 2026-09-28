/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.Matrix.Cartan.TitsCone.Finite

/-!
# Full Tits cones have finite Weyl groups

## Main results

* `Matrix.Realization.finite_weylGroup_of_finite_posRealCoroots`.
* `Matrix.Realization.finite_weylGroup_of_titsCone_eq_univ`.
* `Matrix.Realization.finite_weylGroup_iff_titsCone_eq_univ`.

## References

Kac, *Infinite dimensional Lie algebras*, third edition, Proposition 3.12(e),
implication (ii) to (i), in the existing dual-space convention. The proof here is
reconstructed: finiteness of real coroots bounds the possible images of the simple
coroots under the contragredient action. Equality of these images implies that the
quotient Weyl element preserves the strictly dominant weight's chamber; the existing
fundamental-domain and open-chamber-freeness theorems then identify it with the identity
on the entire dual space. No faithfulness on the coroot span is assumed.
-/

open Module

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsGeneralizedCartan)

/-- Finitely many positive real coroots imply finitely many real coroots, by the sign
alternative. This concerns real coroots, not the full Kac–Moody coroot system. -/
lemma finite_realCoroots_of_finite_posRealCoroots
    (h : (P.posRealCoroots hA).Finite) : (P.realCoroots hA).Finite := by
  refine (h.union (h.image fun x ↦ -x)).subset fun x hx ↦ ?_
  rcases P.mem_posRealCoroots_or_neg_mem hA hx with hp | hn
  · exact Or.inl hp
  · exact Or.inr ⟨-x, hn, neg_neg x⟩

/-- The Weyl group is finite if the set of positive real coroots is finite.
The proof uses freeness at a strictly dominant weight to justify injectivity on the
whole dual space, including directions outside the span of the simple roots. -/
theorem finite_weylGroup_of_finite_posRealCoroots
    (h : (P.posRealCoroots hA).Finite) : Finite (P.weylGroup hA) := by
  classical
  have hr := P.finite_realCoroots_of_finite_posRealCoroots hA h
  let _ := hr.fintype
  choose u hu hpair using fun w : P.weylGroup hA ↦
    P.exists_coweylGroup_apply_apply hA w.2
  let f : P.weylGroup hA → (ι → P.realCoroots hA) := fun w i ↦
    ⟨u w (P.coroot i), P.apply_mem_realCoroots hA (hu w)
      (P.coroot_mem_realCoroots hA i)⟩
  apply Finite.of_injective f
  intro w v heq
  have hcoroot (i : ι) : u w (P.coroot i) = u v (P.coroot i) :=
    congrArg Subtype.val (congrFun heq i)
  have hpos (i : ι) : 0 < P.rho (P.coroot i) := by simp
  have hdom : (v.1 * w.1⁻¹) P.rho ∈ P.dominantChamber := by
    intro i
    change 0 ≤ v.1 (w.1⁻¹ P.rho) (P.coroot i)
    rw [hpair v, ← hcoroot, ← hpair w]
    simp
  have hfix : (v.1 * w.1⁻¹) P.rho = P.rho :=
    P.apply_eq_self_of_mem_dominantChamber hA (fun i ↦ (hpos i).le)
      (mul_mem v.2 (inv_mem w.2)) hdom
  have hone : v.1 * w.1⁻¹ = 1 :=
    P.eq_one_of_apply_eq_self_of_forall_pos hA hpos
      (mul_mem v.2 (inv_mem w.2)) hfix
  exact Subtype.ext (mul_inv_eq_one.mp hone).symm

/-- A full Tits cone implies a finite Weyl group. This proves Kac, third edition,
Proposition 3.12(e), (ii) to (i), dually over any linearly ordered field. -/
theorem finite_weylGroup_of_titsCone_eq_univ (h : P.titsCone hA = Set.univ) :
    Finite (P.weylGroup hA) :=
  P.finite_weylGroup_of_finite_posRealCoroots hA
    ((P.titsCone_eq_univ_iff_finite_posRealCoroots hA).mp h)

/-- Finiteness of the Weyl group is equivalent to fullness of the Tits cone.
This is the equivalence of (i) and (ii) in Kac, third edition, Proposition 3.12(e),
in the dual-space convention and over an arbitrary linearly ordered field. -/
theorem finite_weylGroup_iff_titsCone_eq_univ :
    Finite (P.weylGroup hA) ↔ P.titsCone hA = Set.univ := by
  constructor
  · intro h
    let _ := h
    exact P.titsCone_eq_univ_of_finite_weylGroup hA
  · exact P.finite_weylGroup_of_titsCone_eq_univ hA

end Matrix.Realization
