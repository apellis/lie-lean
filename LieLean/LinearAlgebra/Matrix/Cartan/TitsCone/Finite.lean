/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.Matrix.Cartan.TitsCone.Convex
import LieLean.LinearAlgebra.Matrix.Cartan.Symmetrizable

/-!
# Finite Weyl groups have full Tits cones

## Main results

* `Matrix.Realization.titsCone_eq_univ_of_finite_weylGroup`: the implication (i) to (ii)
  of Kac, Proposition 3.12(e), in the project's dual-space convention.
* `Matrix.Realization.titsCone_eq_univ_iff_finite_posRealCoroots`: fullness is equivalent
  to finiteness of positive real coroots. This is not a statement about all roots.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Proposition 3.12(e),
  p. 40. The proof below uses the same maximum-on-a-finite-orbit argument.

The ground field is any linearly ordered field, not just the real numbers. No
symmetrizability or extra finite-dimensionality hypothesis is imposed.
-/

open Module

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsGeneralizedCartan)

/-- A finite Weyl group has full Tits cone. This is Kac, third edition, Proposition
3.12(e), implication (i) to (ii), for the dual action and over any ordered field. -/
theorem titsCone_eq_univ_of_finite_weylGroup [Finite (P.weylGroup hA)] :
    P.titsCone hA = Set.univ := by
  classical
  let _ := Fintype.ofFinite (P.weylGroup hA)
  apply Set.eq_univ_of_forall
  intro μ
  obtain ⟨w, -, hw⟩ := Finset.exists_max_image Finset.univ
    (fun w : P.weylGroup hA ↦ P.transpose.rho (w.1 μ)) Finset.univ_nonempty
  have hC : w.1 μ ∈ P.dominantChamber := by
    intro i
    have h := hw (⟨P.reflection hA i, P.reflection_mem_weylGroup hA i⟩ * w)
      (Finset.mem_univ _)
    have hr : P.transpose.rho (P.root i) = 1 := P.transpose.rho_coroot i
    change P.transpose.rho (P.reflection hA i (w.1 μ)) ≤ P.transpose.rho (w.1 μ) at h
    rw [reflection_apply, map_sub, map_smul, hr, smul_eq_mul, mul_one] at h
    linarith
  exact ⟨w.1⁻¹, inv_mem w.2, w.1 μ, hC, w.1.symm_apply_apply μ⟩

/-- The chosen weight `ρ` is strictly positive on every positive real coroot. This is the
real-coroot version of the positivity used in Kac, Proposition 3.12(e), (ii) to (iii). -/
lemma rho_pos_of_mem_posRealCoroots {x : H} (hx : x ∈ P.posRealCoroots hA) :
    0 < P.rho x := by
  classical
  obtain ⟨hx, k, hk, rfl⟩ := hx
  have hk0 : k ≠ 0 := by
    intro h
    exact P.ne_zero_of_mem_realCoroots hA hx (by simp [h])
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk0
  have hip : 0 < k i := lt_of_le_of_ne (hk i) (Ne.symm hi)
  rw [apply_corootOf]
  simp only [rho_coroot, mul_one]
  exact Finset.sum_pos' (fun j _ ↦ by exact_mod_cast hk j)
    ⟨i, Finset.mem_univ _, by exact_mod_cast hip⟩

/-- Fullness of the Tits cone is equivalent to finiteness of positive real coroots.
This is a real-coroot analogue of Kac, Proposition 3.12(e), not the assertion about
all roots of the Kac–Moody algebra printed in (iii) and (iv). -/
theorem titsCone_eq_univ_iff_finite_posRealCoroots :
    P.titsCone hA = Set.univ ↔ (P.posRealCoroots hA).Finite := by
  constructor
  · intro h
    have hneg : -P.rho ∈ P.titsCone hA := by rw [h]; trivial
    refine (P.finite_of_mem_titsCone hA hneg).subset fun x hx ↦ ⟨hx, ?_⟩
    simpa using neg_neg_of_pos (P.rho_pos_of_mem_posRealCoroots hA hx)
  · intro h
    apply Set.eq_univ_of_forall
    intro μ
    exact P.mem_titsCone_of_finite hA (h.subset fun _ hx ↦ hx.1)

end Matrix.Realization
