/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Integral.Derivative

/-!
# Integral string components in the original half

Reconstructed from local nilpotence and the actual divided-power boson relation.
This proves integral preservation of the existing string components and Kashiwara operators;
it does not identify the integral crystal residue lattice.
-/

open LieLean LusztigF
noncomputable section
namespace LieLean.QuantumGroup
open GrandLoop
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩
variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

private abbrev V (i : I) :=
  bos (D := D) (pow_ne_one_of_transcendental' transcendental_ratFunc_X) i
private abbrev hq0 (i : I) :=
  NegativePart.pow_d_ne_zero (v := 𝕧) RatFunc.X_ne_zero (D := D) i
private abbrev hq (i : I) :=
  NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' transcendental_ratFunc_X) (D := D) i

omit [Finite I] in
/-- The inverse coefficient in top-string elimination is a Laurent monomial, not just
an arbitrary nonzero rational function. -/
lemma integral_top_string_coefficient (i : I) {x : Um D 𝕧}
    (hx : (V D i).e x = 0) (n : ℕ) :
    ∃ z : ℤ, ((V D i).e ^ n) ((V D i).df n x) = 𝕧 ^ z • x := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨(D.d i : ℤ) * n + z, ?_⟩
    rw [pow_succ, Module.End.mul_apply, BosonModule.e_df_succ (hq0 D i) (hq D i) hx,
      map_smul, hz, smul_smul]
    simp only [inv_inv]
    rw [zpow_add₀ RatFunc.X_ne_zero, zpow_mul, zpow_natCast, zpow_natCast]

/-- The actual boson derivative preserves the transported original integral form. -/
lemma negative_e_mem_integral (i : I) {x : Um D 𝕧}
    (hx : negativeQuotientEquiv D x ∈ quotientIntegralForm D) :
    negativeQuotientEquiv D ((V D i).e x) ∈ quotientIntegralForm D := by
  simpa only [quotientLDeriv, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using quotientLDeriv_mem_integralForm D i hx

/-- Actual divided multiplication preserves the original integral form. -/
lemma negative_df_mem_integral (i : I) (n : ℕ) {x : Um D 𝕧}
    (hx : negativeQuotientEquiv D x ∈ quotientIntegralForm D) :
    negativeQuotientEquiv D ((V D i).df n x) ∈ quotientIntegralForm D := by
  rw [negativeQuotientEquiv_df]
  exact mul_mem (quotientIntegralGenerator_mem D i n) hx

/-- Every existing boson string component of an original integral element is integral.
The proof eliminates the top nonzero derivative using only Laurent units. -/
theorem negative_component_mem_integral (i : I) {x : Um D 𝕧}
    (hx : negativeQuotientEquiv D x ∈ quotientIntegralForm D) (n : ℕ) :
    negativeQuotientEquiv D ((V D i).component (hq0 D i) (hq D i) n x) ∈
      quotientIntegralForm D := by
  obtain ⟨N, hN⟩ := (V D i).exists_e_pow_eq_zero x
  induction N using Nat.strong_induction_on generalizing x with
  | h N ih =>
    cases N with
    | zero =>
      have hx0 : x = 0 := by simpa using hN
      simp [hx0]
    | succ N =>
      let y := ((V D i).e ^ N) x
      have hy0 : (V D i).e y = 0 := by
        rw [← Module.End.mul_apply, ← pow_succ']
        exact hN
      have hyI : negativeQuotientEquiv D y ∈ quotientIntegralForm D := by
        have hp (m : ℕ) : negativeQuotientEquiv D (((V D i).e ^ m) x) ∈
            quotientIntegralForm D := by
          induction m with
          | zero => exact hx
          | succ m hm =>
            rw [pow_succ', Module.End.mul_apply]
            exact negative_e_mem_integral D i hm
        exact hp N
      obtain ⟨z, hz⟩ := integral_top_string_coefficient D i hy0 N
      let t := 𝕧 ^ (-z) • (V D i).df N y
      have htI : negativeQuotientEquiv D t ∈ quotientIntegralForm D := by
        rw [map_smul]
        exact zpow_smul_mem_quotientIntegralForm D (-z) (negative_df_mem_integral D i N hyI)
      have ht : ((V D i).e ^ N) t = y := by
        rw [map_smul, hz, smul_smul, ← zpow_add₀ RatFunc.X_ne_zero, neg_add_cancel,
          zpow_zero, one_smul]
      have hrem : ((V D i).e ^ N) (x - t) = 0 := by
        rw [map_sub, ht]
        exact sub_self _
      have hi := ih N (Nat.lt_succ_self N) (by simpa using sub_mem hx htI) hrem
      have hct : negativeQuotientEquiv D
          ((V D i).component (hq0 D i) (hq D i) n t) ∈ quotientIntegralForm D := by
        rw [map_smul, BosonModule.component_df (hq0 D i) (hq D i) hy0, map_smul]
        split_ifs
        · exact zpow_smul_mem_quotientIntegralForm D (-z) hyI
        · simp
      have heq : x = (x - t) + t := by abel
      rw [heq, map_add, map_add]
      exact add_mem hi hct

/-- The existing Kashiwara raising operator preserves the original integral form. -/
theorem negative_kE_mem_integral (i : I) {x : Um D 𝕧}
    (hx : negativeQuotientEquiv D x ∈ quotientIntegralForm D) :
    negativeQuotientEquiv D (kE transcendental_ratFunc_X i x) ∈ quotientIntegralForm D := by
  obtain ⟨N, _, heq⟩ := (V D i).exists_sum_component (hq0 D i) (hq D i) x
  rw [heq, map_sum, map_sum]
  apply (quotientIntegralForm D).sum_mem
  intro n _
  have hn := negative_component_mem_integral D i hx n
  have he := (V D i).e_component (hq0 D i) (hq D i) n x
  cases n with
  | zero =>
    simp only [BosonModule.df_zero]
    change negativeQuotientEquiv D ((V D i).eTilde (hq0 D i) (hq D i) _) ∈ _
    rw [BosonModule.eTilde_of_ker (hq0 D i) (hq D i) he, map_zero]
    exact zero_mem _
  | succ n =>
    change negativeQuotientEquiv D ((V D i).eTilde (hq0 D i) (hq D i) _) ∈ _
    rw [BosonModule.eTilde_df_succ (hq0 D i) (hq D i) he]
    exact negative_df_mem_integral D i n hn

/-- The existing Kashiwara lowering operator preserves the original integral form. -/
theorem negative_kF_mem_integral (i : I) {x : Um D 𝕧}
    (hx : negativeQuotientEquiv D x ∈ quotientIntegralForm D) :
    negativeQuotientEquiv D (kF transcendental_ratFunc_X i x) ∈ quotientIntegralForm D := by
  obtain ⟨N, _, heq⟩ := (V D i).exists_sum_component (hq0 D i) (hq D i) x
  rw [heq, map_sum, map_sum]
  apply (quotientIntegralForm D).sum_mem
  intro n _
  change negativeQuotientEquiv D ((V D i).fTilde (hq0 D i) (hq D i) _) ∈ _
  rw [BosonModule.fTilde_df (hq0 D i) (hq D i)
    ((V D i).e_component (hq0 D i) (hq D i) n x)]
  exact negative_df_mem_integral D i (n + 1) (negative_component_mem_integral D i hx n)

namespace Modified
variable {Y : Type*} [AddCommGroup Y] (R : D.RootDatum Y)

/-- Every Kashiwara raising step on an arbitrary original integral PBW preimage stays integral. -/
theorem integralPBWPreimage_kE_mem {W : Type*} [Group W]
    {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W} {w : List I}
    (hw : cs.IsReduced w) (c : Fin w.length → ℕ) (i : I) :
    negativeQuotientEquiv D (kE transcendental_ratFunc_X i
      ((negativeQuotientEquiv D).symm (integralPBWPreimage R hw c))) ∈
        quotientIntegralForm D :=
  negative_kE_mem_integral D i (by
    simpa only [LinearEquiv.apply_symm_apply] using (integralPBWPreimage R hw c).property)

end Modified
end LieLean.QuantumGroup
