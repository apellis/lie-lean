/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.ProductNorm

/-!
# Integral stability of the actual quotient skew derivative

The proof is reconstructed from divided-power differentiation and algebra generation.
It uses the original integer Laurent integral form and the original quotient derivative.
No comparison with a crystal integral form is assumed.
-/

open LieLean
noncomputable section
namespace LieLean.QuantumGroup
open LusztigF GrandLoop
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩
variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

omit [Finite I] in
/-- Integer powers of the parameter act on the actual integral form. -/
lemma zpow_smul_mem_quotientIntegralForm (z : ℤ) {x : Quotient D 𝕧}
    (hx : x ∈ quotientIntegralForm D) : 𝕧 ^ z • x ∈ quotientIntegralForm D := by
  have h := (quotientIntegralForm D).smul_mem hx (LaurentPolynomial.T z)
  change integralLaurentEval (LaurentPolynomial.T z) • x ∈ quotientIntegralForm D at h
  simpa only [integralLaurentEval_T] using h

/-- The quotient derivative kills the unit. -/
@[simp] lemma quotientLDeriv_one (i : I) : quotientLDeriv D i 1 = 0 := by
  simpa only [map_one, lDeriv_one, map_zero] using quotientLDeriv_toQuotient D i 1

/-- Differentiation of a nonzero simple divided power, in the actual quotient. -/
lemma quotientLDeriv_integralGenerator_succ (i : I) (n : ℕ) :
    quotientLDeriv D i (quotientIntegralGenerator D i (n + 1)) =
      (𝕧 ^ D.d i) ^ n • quotientIntegralGenerator D i n := by
  let V := bos (D := D) (pow_ne_one_of_transcendental' transcendental_ratFunc_X) i
  let x := (negativeQuotientEquiv D).symm 1
  have hx : V.e x = 0 := by
    apply (negativeQuotientEquiv D).injective
    simpa only [quotientLDeriv, LinearMap.comp_apply, LinearEquiv.coe_coe,
      map_zero] using quotientLDeriv_one D i
  have hd (m : ℕ) : negativeQuotientEquiv D (V.df m x) =
      quotientIntegralGenerator D i m := by
    simpa only [x, LinearEquiv.apply_symm_apply, mul_one] using
      negativeQuotientEquiv_df D i m x
  rw [← hd (n + 1)]
  simp only [quotientLDeriv, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rw [BosonModule.e_df_succ (NegativePart.pow_d_ne_zero RatFunc.X_ne_zero i)
    (NegativePart.pow_d_ne_one
      (pow_ne_one_of_transcendental' transcendental_ratFunc_X) i) hx, map_smul, hd]
  simp only [inv_inv]

/-- Every simple divided-power generator has integral derivative. -/
lemma quotientLDeriv_integralGenerator_mem (i j : I) (n : ℕ) :
    quotientLDeriv D i (quotientIntegralGenerator D j n) ∈ quotientIntegralForm D := by
  by_cases hij : i = j
  · subst j
    cases n with
    | zero => simp [quotientIntegralGenerator, qDivPow, qFactorial]
    | succ n =>
      rw [quotientLDeriv_integralGenerator_succ]
      have h := zpow_smul_mem_quotientIntegralForm D (D.d i * n)
        (quotientIntegralGenerator_mem D i n)
      simpa only [zpow_mul, zpow_natCast] using h
  · have hp : ∀ n : ℕ, lDeriv D 𝕧 i (θ 𝕂 j ^ n) = 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => simp [pow_succ, lDeriv_mul, ih, hij]
    have he : quotientIntegralGenerator D j n =
        toQuotient D 𝕧 (qDivPow (𝕧 ^ D.d j) n (θ 𝕂 j)) := by
      simp [quotientIntegralGenerator, qDivPow]
    rw [he, quotientLDeriv_toQuotient]
    simp [qDivPow, hp]

/-- An integral element has a free representative whose twist and derivative have integral
images. This is proved by generation, not by assuming an integral comparison theorem. -/
lemma exists_integral_derivative_lift (i : I) {x : Quotient D 𝕧}
    (hx : x ∈ quotientIntegralForm D) :
    ∃ a : LusztigF 𝕂 I, toQuotient D 𝕧 a = x ∧
      toQuotient D 𝕧 (twist D 𝕧 i a) ∈ quotientIntegralForm D ∧
      toQuotient D 𝕧 (lDeriv D 𝕧 i a) ∈ quotientIntegralForm D := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, n, rfl⟩ := hx
    let a := qDivPow (𝕧 ^ D.d j) n (θ 𝕂 j)
    have ha : toQuotient D 𝕧 a = quotientIntegralGenerator D j n := by
      simp [a, qDivPow, quotientIntegralGenerator]
    refine ⟨a, ha, ?_, ?_⟩
    · have ht : twist D 𝕧 i a = (𝕧 ^ D.dot i j) ^ n • a := by
        simp only [a, qDivPow, map_smul, map_pow, twist_θ, smul_pow, smul_smul]
        congr 1
        exact mul_comm _ _
      rw [ht, map_smul, ha]
      have h := zpow_smul_mem_quotientIntegralForm D (D.dot i j * (n : ℤ))
        (quotientIntegralGenerator_mem D j n)
      simpa only [zpow_mul, zpow_natCast] using h
    · rw [← quotientLDeriv_toQuotient, ha]
      exact quotientLDeriv_integralGenerator_mem D i j n
  | algebraMap c =>
    refine ⟨algebraMap 𝕂 _ (integralLaurentEval c), ?_, ?_, ?_⟩
    · exact (toQuotient D 𝕧).commutes _
    · rw [AlgHom.commutes, AlgHom.commutes]
      exact (quotientIntegralForm D).algebraMap_mem c
    · simp
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl, hat, had⟩ := hx
    obtain ⟨b, rfl, hbt, hbd⟩ := hy
    refine ⟨a + b, map_add _ _ _, ?_, ?_⟩
    · simpa only [map_add] using add_mem hat hbt
    · simpa only [map_add] using add_mem had hbd
  | mul x y hx hy hdx hdy =>
    obtain ⟨a, rfl, hat, had⟩ := hdx
    obtain ⟨b, rfl, hbt, hbd⟩ := hdy
    refine ⟨a * b, map_mul _ _ _, ?_, ?_⟩
    · simpa only [map_mul] using mul_mem hat hbt
    · rw [lDeriv_mul, map_add, map_mul, map_mul]
      exact add_mem (mul_mem had hy) (mul_mem hat hbd)

/-- The actual left skew derivative preserves the original integer Laurent integral form.
The proof is reconstructed by integral divided-power generation. -/
theorem quotientLDeriv_mem_integralForm (i : I) {x : Quotient D 𝕧}
    (hx : x ∈ quotientIntegralForm D) :
    quotientLDeriv D i x ∈ quotientIntegralForm D := by
  obtain ⟨a, rfl, _, had⟩ := exists_integral_derivative_lift D i hx
  rwa [quotientLDeriv_toQuotient]

namespace Modified
variable {Y : Type*} [AddCommGroup Y] (R : D.RootDatum Y)

/-- Arbitrary original reduced-word PBW preimages retain integrality under every simple
left skew derivative. There is no adapted-first-node restriction. -/
theorem quotientLDeriv_integralPBWPreimage_mem {W : Type*} [Group W]
    {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W} {w : List I}
    (hw : cs.IsReduced w) (c : Fin w.length → ℕ) (i : I) :
    quotientLDeriv D i (integralPBWPreimage R hw c) ∈ quotientIntegralForm D :=
  quotientLDeriv_mem_integralForm D i (integralPBWPreimage R hw c).property

end Modified
end LieLean.QuantumGroup
