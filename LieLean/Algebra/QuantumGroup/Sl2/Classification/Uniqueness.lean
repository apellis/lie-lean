/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Sl2.Classification.Equivalence

/-!
# Uniqueness of finite-dimensional quantum sl₂ parameters

## Main results

* `QuantumGroup.Sl2.simpleRep_parameters_eq`: equivalent standard simple representations
  have the same highest-weight parameters.

## References

The argument is reconstructed from the explicit operators in `Sl2.SimpleModule`: dimension
fixes the string length, and the one-dimensional raising kernel fixes the highest eigenvalue.
No external source was consulted.
-/

namespace QuantumGroup.Sl2

variable {k : Type*} [Field k] {v σ τ : k} {n m : ℕ}

/-- In a standard simple representation, the raising kernel is the highest-weight line.
Reconstructed directly from the nonzero superdiagonal coefficients. -/
theorem eq_smul_highest_of_simpleRep_E_eq_zero
    (hv : v ≠ 0) (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1) (hσ : σ ^ 2 = 1)
    (x : Fin (n + 1) → k)
    (hx : simpleRep v n σ hv (hv' 2 two_pos) hσ (E sl2RootDatum v ()) x = 0) :
    x = x 0 • Pi.single 0 1 := by
  classical
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ
  have hq (r : ℕ) (hr : 0 < r) : qInt v r ≠ 0 :=
    qInt_ne_zero hv (hv' _ (by omega))
  ext j
  by_cases hj : j = 0
  · subst j
    simp
  · have hjpos : 0 < j.val := by
      have : j.val ≠ 0 := fun h ↦ hj (Fin.ext h)
      omega
    have hzero := congrArg (fun y ↦ coord n y (j.val - 1)) hx
    rw [simpleRep_E, coord_opE, coord_zero, Nat.sub_add_cancel hjpos] at hzero
    have hc : eCoeff v n σ j.val ≠ 0 :=
      mul_ne_zero (mul_ne_zero hσ0 (hq _ hjpos)) (hq _ (by omega))
    have hxj : x j = 0 := by
      simpa using (mul_eq_zero.mp hzero).resolve_left hc
    simp [hj, hxj]

/-- Equivalence of standard simple representations determines both the dimension parameter
and the sign of the highest weight. Valid over any field at generic parameter; reconstructed
from dimensions and the highest-weight line, without algebraic closedness. -/
theorem simpleRep_parameters_eq (hv : v ≠ 0)
    (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1) (hσ : σ ^ 2 = 1) (hτ : τ ^ 2 = 1)
    (e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (m + 1) → k))
    (he : ∀ (u : Sl2 v) x,
      e (simpleRep v n σ hv (hv' 2 two_pos) hσ u x) =
        simpleRep v m τ hv (hv' 2 two_pos) hτ u (e x)) : n = m ∧ σ = τ := by
  classical
  have hdim : n + 1 = m + 1 := by simpa using e.finrank_eq
  have hnm : n = m := by omega
  subst m
  refine ⟨rfl, ?_⟩
  let x : Fin (n + 1) → k := e (Pi.single 0 1)
  have hxE : simpleRep v n τ hv (hv' 2 two_pos) hτ (E sl2RootDatum v ()) x = 0 := by
    rw [← he]
    simp only [simpleRep_E_single, Fin.val_zero, lt_self_iff_false, ↓reduceDIte, map_zero]
  have hx := eq_smul_highest_of_simpleRep_E_eq_zero hv hv' hτ x hxE
  have hx0 : x 0 ≠ 0 := by
    intro h0
    have hzero : x = 0 := by rw [hx, h0, zero_smul]
    have hh : (Pi.single (0 : Fin (n + 1)) (1 : k)) = 0 :=
      e.injective (hzero.trans e.map_zero.symm)
    have := congrFun hh 0
    simp at this
  have hK := congrFun (he (K sl2RootDatum v 1) (Pi.single (0 : Fin (n + 1)) 1)) 0
  rw [simpleRep_K_single, map_smul] at hK
  simp only [simpleRep_K, opK, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_zero,
    Nat.cast_zero, mul_zero, sub_zero, one_mul, zpow_one, zpow_natCast,
    Pi.smul_apply, smul_eq_mul] at hK
  change (σ * v ^ n) * x 0 = (τ * v ^ n) * x 0 at hK
  exact mul_right_cancel₀ (pow_ne_zero n hv) (mul_right_cancel₀ hx0 hK)

/-- Standard simple representations are equivalent exactly when both parameters agree.
Together with `irreducible_iff_equiv_simpleRep`, this makes the finite-dimensional
classification unique up to equivalence. Reconstructed from the previous uniqueness proof. -/
theorem simpleRep_equiv_iff (hv : v ≠ 0)
    (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1) (hσ : σ ^ 2 = 1) (hτ : τ ^ 2 = 1) :
    (∃ e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (m + 1) → k),
      ∀ (u : Sl2 v) x,
        e (simpleRep v n σ hv (hv' 2 two_pos) hσ u x) =
          simpleRep v m τ hv (hv' 2 two_pos) hτ u (e x)) ↔ n = m ∧ σ = τ := by
  constructor
  · rintro ⟨e, he⟩
    exact simpleRep_parameters_eq hv hv' hσ hτ e he
  · rintro ⟨rfl, rfl⟩
    exact ⟨LinearEquiv.refl k _, fun _ _ ↦ rfl⟩

end QuantumGroup.Sl2
