/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralB2
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.DividedPowers

/-!
# Integral B₂ spanning in the opposite order

The B₂ relations in the opposite algebra become B₂ relations at the inverse parameter after
rescaling the two middle root vectors by Laurent units. Thus the integral PBW spanning theorem
also applies to the reversed multiplication. This is the rank-two input for inverse braid
operators.

## Main results

* `B2Integral.coe_orderedSpan_eq_genRing_of_op`: integral spanning from opposite B₂ relations.
-/

open MulOpposite

noncomputable section

namespace LieLean.QuantumGroup

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

namespace B2PBW.Rel

/-- Reversing multiplication and inverting the parameter preserves the B₂ relations, after
rescaling the middle two vectors. -/
lemma inv_of_op {p : k} {e x y f : B} (hp : p ≠ 0)
    (H : B2PBW.Rel p (op e) (op x) (op y) (op f)) :
    B2PBW.Rel p⁻¹ e (p • x) (-p • y) f := by
  have hfe := congrArg unop H.fe
  have hye := congrArg unop H.ye
  have hxe := congrArg unop H.xe
  have hfy := congrArg unop H.fy
  simp only [unop_mul, unop_sub, unop_smul, unop_op] at hfe hye hxe hfy
  constructor
  · rw [hfe]
    simp only [neg_smul, smul_neg, smul_sub, smul_smul, inv_mul_cancel₀ hp, one_smul]
    abel
  · simp only [smul_mul_assoc, mul_smul_comm]
    rw [hye]
    module
  · simp only [inv_inv, smul_mul_assoc, mul_smul_comm]
    rw [hxe]
    simp only [smul_smul, mul_inv_cancel₀ hp, mul_one]
  · simp only [inv_inv, smul_mul_assoc, mul_smul_comm]
    rw [hfy]
    simp only [smul_smul]
    congr 1
    field_simp

end B2PBW.Rel

namespace B2Integral

variable {q : k} {Λ : Subring k} {e X y f : B}

lemma orderedSpan_inv : orderedSpan q⁻¹ Λ e X y f = orderedSpan q Λ e X y f := by
  simp only [orderedSpan, M4, M3, inv_pow, A2Integral.qDivPow_inv']

lemma genRing_inv : genRing q⁻¹ Λ e f = genRing q Λ e f := by
  simp only [genRing, inv_pow, A2Integral.qDivPow_inv']

lemma orderedSpan_smul_le {u v : k} (hu : u ∈ Λ) (hv : v ∈ Λ) :
    orderedSpan q Λ e (u • X) (v • y) f ≤ orderedSpan q Λ e X y f := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro z ⟨c, hc, a, b, c', d, rfl⟩
  simp only [M4, M3, qDivPow_smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul]
  exact smul_mem_orderedSpan (mul_mem hc (mul_mem (pow_mem hv _) (pow_mem hu _)))
    (M4_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (X := X) (y := y) (f := f) a b c' d)

/-- Multiplying the middle root vectors by units of the coefficient subring does not change
the ordered integral span. -/
lemma orderedSpan_smul {u v : k} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hu : u ∈ Λ) (hu' : u⁻¹ ∈ Λ) (hv : v ∈ Λ) (hv' : v⁻¹ ∈ Λ) :
    orderedSpan q Λ e (u • X) (v • y) f = orderedSpan q Λ e X y f := by
  refine le_antisymm (orderedSpan_smul_le hu hv) ?_
  have h := orderedSpan_smul_le (q := q) (e := e) (X := u • X) (y := v • y) (f := f) hu' hv'
  simpa only [smul_smul, inv_mul_cancel₀ hu0, inv_mul_cancel₀ hv0, one_smul] using h

/-- **Integral B₂ spanning with opposite relations.** The reversed ordered root vectors span
the same integral subring. -/
theorem coe_orderedSpan_eq_genRing_of_op (hq0 : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 2) n ≠ 0)
    (H : B2PBW.Rel (q ^ 2) (op e) (qInt q 2 • op X) (op y) (op f))
    (hqΛ : q ∈ Λ) (hqΛ' : q⁻¹ ∈ Λ) :
    (orderedSpan q Λ e X y f : Set B) = genRing q Λ e f := by
  have H' := H.inv_of_op (pow_ne_zero 2 hq0)
  have hrel : B2PBW.Rel (q⁻¹ ^ 2) e
      (qInt q⁻¹ 2 • (q ^ 2 • X)) (-q ^ 2 • y) f := by
    simpa only [inv_pow, A2Integral.qInt_inv', smul_smul, mul_comm, unop_op] using H'
  have hqi' : ∀ n : ℕ, 0 < n → qInt q⁻¹ n ≠ 0 := by
    simpa only [A2Integral.qInt_inv'] using hqi
  have hpi' : ∀ n : ℕ, 0 < n → qInt (q⁻¹ ^ 2) n ≠ 0 := by
    simpa only [inv_pow, A2Integral.qInt_inv'] using hpi
  have h := coe_orderedSpan_eq_genRing (inv_ne_zero hq0) hqi' hpi' hrel hqΛ'
    (by simpa only [inv_inv] using hqΛ)
  rw [orderedSpan_inv, genRing_inv, orderedSpan_smul (pow_ne_zero 2 hq0)
    (neg_ne_zero.mpr (pow_ne_zero 2 hq0)) (pow_mem hqΛ 2)
    (by simpa only [inv_pow] using pow_mem hqΛ' 2) (neg_mem (pow_mem hqΛ 2))
    (by simpa only [inv_neg, inv_pow] using neg_mem (pow_mem hqΛ' 2))] at h
  exact h

end B2Integral

end LieLean.QuantumGroup
