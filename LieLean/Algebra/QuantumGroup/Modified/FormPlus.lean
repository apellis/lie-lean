/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.FormSigma

/-!
# The form on `U̇` restricted to `U⁺ 1_λ`

([Lus] 26.1.5) `(x⁺ 1_λ, x'⁺ 1_λ) = (x, x')` for `x, x' ∈ 'f`.

## Main results

* `QuantumGroup.rho_plusHom_monomial`: `ρ(θ_w⁺) = v^{(ν·ν)/2} K̃_ν θ_{σ(w)}⁻` for a word `w` of
  weight `ν`.
* `QuantumGroup.Modified.formFunctional_braidReversal`: `P_{-λ}(σ z) = P_λ(z)` for `z ∈ U_0`, from
  [Lus] 26.1.4.
* `QuantumGroup.Modified.form_plusHom_leftAct_one`: [Lus] 26.1.5.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 26.1.5.
-/

open LieLean LusztigF

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]

omit [DecidableEq I] in
lemma wordWeight_reverse (w : List I) : wordWeight w.reverse = wordWeight w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [List.reverse_cons, wordWeight_append, ih, wordWeight_cons, wordWeight_cons,
      wordWeight_nil, add_zero, add_comm]

/-- `ρ(θ_w⁺) = v^{(ν·ν)/2} K̃_ν θ_{σ(w)}⁻` for a word `w` of weight `ν`. -/
theorem rho_plusHom_monomial (w : List I) :
    rho R v (plusHom R v (monomial k w)) =
      v ^ (normSq R (wordWeight w) / 2) •
        (K R v (ktildeSum R (wordWeight w)) * minusHom R v (monomial k w.reverse)) := by
  have hv := NeZero.ne v
  have h := congrArg (rho R v) (rho_minusHom_monomial (k := k) (R := R) (v := v) w.reverse)
  rw [rho_rho, map_smul, rho_mul, rho_K, List.reverse_reverse, wordWeight_reverse] at h
  rw [h, mul_smul_comm, smul_smul, ← mul_assoc, K_add, add_neg_cancel, K_zero, one_mul,
    ← zpow_add₀ hv, add_neg_cancel, zpow_zero, one_smul]

lemma braidReversal_plusHom (x : LusztigF k I) :
    braidReversal (plusHom R v x) = plusHom R v (rev k I x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes, rev_algebraMap, AlgHom.commutes, braidReversal_algebraMap]
  | grade1 i =>
    rw [show FreeAlgebra.ι k i = θ k i from rfl, plusHom_θ, rev_θ, plusHom_θ, braidReversal_E]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | mul a b ha hb => rw [map_mul, braidReversal_mul, ha, hb, rev_mul, map_mul]

namespace Modified

variable (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv

/-- `P_{-λ}(σ z) = P_λ(z)` for `z ∈ U_0`: [Lus] 26.1.4 applied to `(1_λ, z 1_λ)`. -/
theorem formFunctional_braidReversal (l : Y →+ ℤ) {z : QuantumGroup R v}
    (hz : z ∈ adWeightSpace R v 0) :
    formFunctional R v hv (-l) (braidReversal z) = formFunctional R v hv l z := by
  have hz' : z ∈ adWeightSpace R v (l - l) := by rw [sub_self]; exact hz
  have h := form_sigma_sigma hv (one l) (elt l l z hz')
  rw [one, sigma_elt, sigma_elt, form_elt_elt_self, form_elt_elt_self, rho_one, one_mul,
    show braidReversal (1 : QuantumGroup R v) = 1 by simp [braidReversal], rho_one,
    one_mul] at h
  exact h

/-- **[Lus] 26.1.5**: `(x⁺ 1_λ, x'⁺ 1_λ) = (x, x')` for `x, x' ∈ 'f`. -/
theorem form_plusHom_leftAct_one (l : Y →+ ℤ) (x y : LusztigF k I) :
    form R v hv (leftAct R v hv (plusHom R v x) (one l))
      (leftAct R v hv (plusHom R v y) (one l)) = LusztigF.form D v x y := by
  have h : ((form R v hv).compl₁₂ (leftAct R v hv ∘ₗ (plusHom R v).toLinearMap |>.flip (one l))
      (leftAct R v hv ∘ₗ (plusHom R v).toLinearMap |>.flip (one l))) = LusztigF.form D v :=
    LinearMap.ext_basis (FreeAlgebra.wordBasis k I) (FreeAlgebra.wordBasis k I) fun w w' ↦ by
      simp only [LinearMap.compl₁₂_apply, LinearMap.flip_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, wordBasis_eq_monomial]
      rw [one, leftAct_elt hv (plusHom_monomial_mem_adWeightSpace w),
        leftAct_elt hv (plusHom_monomial_mem_adWeightSpace w'), form_elt_elt]
      split_ifs with h
      · have hχ : wordChar R w = wordChar R w' := by
          simpa using (Prod.mk.inj h).1
        have hz : rho R v (plusHom R v (monomial k w) * 1) * (plusHom R v (monomial k w') * 1) ∈
            adWeightSpace R v 0 := by
          have := mul_mem_adWeightSpace
            (rho_mem_adWeightSpace (plusHom_monomial_mem_adWeightSpace (R := R) (v := v) w))
            (plusHom_monomial_mem_adWeightSpace (R := R) (v := v) w')
          rwa [hχ, neg_add_cancel, ← mul_one (plusHom R v (monomial k w')),
            ← mul_one (plusHom R v (monomial k w))] at this
        rw [← formFunctional_braidReversal hv l hz, mul_one, mul_one, braidReversal_mul,
          rho_plusHom_monomial, map_smul, braidReversal_mul, braidReversal_K,
          braidReversal_minusHom, braidReversal_plusHom, rev_monomial, rev_monomial,
          List.reverse_reverse, mul_smul_comm, map_smul, ← mul_assoc, formFunctional_mul_K,
          ← mul_one (plusHom R v (monomial k w'.reverse)), ← K_zero R v,
          formFunctional_plusHom_K_minusHom_monomial, rev_monomial, List.reverse_reverse,
          LusztigF.form_comm, formScale, smul_eq_mul, ← mul_assoc, ← mul_assoc,
          ← zpow_add₀ (NeZero.ne v), ← zpow_add₀ (NeZero.ne v)]
        convert one_mul (LusztigF.form D v (monomial k w) (monomial k w'))
        convert zpow_zero v using 2
        simp only [map_neg, AddMonoidHom.neg_apply, map_zero, neg_neg]
        ring
      · refine (LusztigF.form_eq_zero_of_ne D v (fun hw ↦ h ?_) (monomial_mem_weightSpace w)
          (monomial_mem_weightSpace w')).symm
        rw [wordChar_eq_rootSum, wordChar_eq_rootSum, hw]
  exact LinearMap.congr_fun₂ h x y

end Modified

end LieLean.QuantumGroup
