/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.HighestWeightBar
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.StringIdentity
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityCompare
import LieLean.Algebra.QuantumGroup.Modified.Triangular

/-!
# `V_ℤ(λ)` is a `U_ℤ`-module

Kashiwara's `𝒜`-form `V_ℤ(λ) = U⁻_ℤ u_λ` ([Kas91] (6.1.12), `hwIntegral`) is stable under the
divided powers `Eᵢ^{(n)}` and `Fᵢ^{(n)}`: it is a `U_ℤ`-module, as stated after (6.1.12). For
`Fᵢ^{(n)}` this is the stability of `U⁻_ℤ` under left multiplication by `fᵢ^{(n)}`
(`dF_smul_mem_hwIntegral`). For `Eᵢ^{(N)}` (`dE_smul_mem_hwIntegral`) we write an element of
`U⁻_ℤ` as an `𝒜`-combination of products of divided powers and move `Eᵢ^{(N)}` to the right
with the commutation formula ([Lus] 3.1.9, `qDivPow_E_smul_qDivPow_F_smul`) on weight vectors,
whose coefficients `[m; t]ᵢ` lie in `𝒜` ([Lus] 1.3.1 (d), `Modified.isLaurent_qBinomZ`); finally
`Eᵢ^{(N)} u_λ = 0` for `N > 0`.

Consequently Prop. 6.1.3 of [Kas91] applies to `V_ℤ(λ)` at every node
(`mem_hwIntegral_wt_iff`): the vectors of `V_ℤ(λ)` of `i`-weight `-n ≤ -1` are the
`𝒜`-combinations of vectors `Fᵢ^{(k)} y`, `k ≥ n`, with `y ∈ V_ℤ(λ)` of `i`-weight `2k - n`.

Kashiwara deduces the `U_ℤ`-stability from the commutation relations (his (1.1.23)); the proof
here, through Lusztig's commutation formula on weight vectors, is our own write-up of that step.

## Main results

* `dF_smul_mem_hwIntegral`, `dE_smul_mem_hwIntegral`: `V_ℤ(λ)` is stable under `Fᵢ^{(n)}` and
  `Eᵢ^{(n)}`.
* `mem_hwIntegral_wt_iff`: [Kas91] Prop. 6.1.3 for `V_ℤ(λ)` at every node.

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, §6.1.
* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.3.1, 3.1.9.
-/

open Finset LusztigF

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop Sl2.RankOne

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "hvt" => transcendental_ratFunc_X
local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular) (Λ : Dom R)

omit [Finite I] in
lemma toQuotient_qDivPow (i : I) (n : ℕ) :
    toQuotient D 𝕧 (qDivPow (𝕧 ^ D.d i) n (θ 𝕂 i)) = quotientIntegralGenerator D i n := by
  rw [quotientIntegralGenerator, qDivPow, qDivPow, map_smul, map_pow]

omit [Finite I] in
/-- `(θⱼ^{(n)} y)⁻ v_λ = Fⱼ^{(n)} (y⁻ v_λ)`. -/
lemma ev_qDivPow_mul (j : I) (n : ℕ) (y : LusztigF 𝕂 I) :
    ev R 𝕧 Λ.1 (qDivPow (𝕧 ^ D.d j) n (θ 𝕂 j) * y) =
      qDivPow (𝕧 ^ D.d j) n (F R 𝕧 j) • ev R 𝕧 Λ.1 y := by
  have hpow : ∀ n : ℕ, ev R 𝕧 Λ.1 (θ 𝕂 j ^ n * y) = F R 𝕧 j ^ n • ev R 𝕧 Λ.1 y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, ev_ι_mul, ih, pow_succ', mul_smul]
  rw [qDivPow, qDivPow, smul_mul_assoc, map_smul, hpow, smul_assoc]

/-- `V_ℤ(λ)` is stable under `Fᵢ^{(n)}`. -/
theorem dF_smul_mem_hwIntegral (i : I) (n : ℕ) {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ hwIntegral Λ) : qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) • m ∈ hwIntegral Λ := by
  obtain ⟨x, hx, rfl⟩ := hm
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨Submodule.Quotient.mk (qDivPow (𝕧 ^ D.d i) n (θ 𝕂 i) * y), ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_negIntegral] at hx ⊢
    change toQuotient D 𝕧 (_ * y) ∈ _
    rw [map_mul, toQuotient_qDivPow]
    exact mul_mem (quotientIntegralGenerator_mem D i n) hx
  · rw [evq_mk, evq_mk, ev_qDivPow_mul]

lemma symm_toQuotient (z : LusztigF 𝕂 I) :
    (negativeQuotientEquiv D).symm (toQuotient D 𝕧 z) = NegativePart.mk (D := D) (v := 𝕧) z :=
  (negativeQuotientEquiv D).symm_apply_eq.2 rfl

omit [Finite I] in
lemma qDivPow_E_smul_hwv (i : I) {N : ℕ} (hN : 0 < N) :
    qDivPow (𝕧 ^ D.d i) N (E R 𝕧 i) • IrreducibleModule.hwv R 𝕧 Λ.1 = 0 := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_lt hN
  rw [qDivPow, smul_assoc, pow_succ, mul_smul, IrreducibleModule.E_smul_hwv, smul_zero,
    smul_zero]

lemma hwv_mem_hwIntegral : IrreducibleModule.hwv R 𝕧 Λ.1 ∈ hwIntegral Λ := by
  refine ⟨NegativePart.mk 1, ?_, by rw [evq_mk, ev_one]⟩
  rw [SetLike.mem_coe, mem_negIntegral]
  change toQuotient D 𝕧 1 ∈ _
  rw [map_one]
  exact one_mem _

include hR in
/-- The induction step for `dE_smul_mem_hwIntegral`: `Eᵢ^{(N)} (y u_λ) ∈ V_ℤ(λ)` for products
`y` of divided powers `fⱼ^{(n)}`. -/
lemma dE_smul_evq_mem_of_mem_closure {y : Quotient D 𝕧}
    (hy : y ∈ Submonoid.closure {x | ∃ j n, x = quotientIntegralGenerator D j n}) :
    ∀ (i : I) (N : ℕ), qDivPow (𝕧 ^ D.d i) N (E R 𝕧 i) •
      evq hvt Λ ((negativeQuotientEquiv D).symm y) ∈ hwIntegral Λ := by
  induction hy using Submonoid.closure_induction_left with
  | one =>
    intro i N
    rw [← map_one (toQuotient D 𝕧), symm_toQuotient, evq_mk, ev_one]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [qDivPow_zero', one_smul]; exact hwv_mem_hwIntegral Λ
    · rw [qDivPow_E_smul_hwv Λ i hN]; exact zero_mem _
  | mul_left x hx y hy ih =>
    intro i N
    obtain ⟨j, n, rfl⟩ := hx
    obtain ⟨ν, z, hz, rfl, -⟩ := exists_homogeneous_of_mem_closure D hy
    rw [symm_toQuotient, evq_mk] at ih
    rw [← toQuotient_qDivPow, ← map_mul, symm_toQuotient, evq_mk, ev_qDivPow_mul]
    by_cases hij : i = j
    · subst hij
      have hm := ev_mem_weightSpace hvn_ratFunc hR Λ.1 hz
      rw [qDivPow_E_smul_qDivPow_F_smul hvn_ratFunc hm]
      refine sum_mem fun t _ ↦ ?_
      rw [efTerm]
      split_ifs
      · obtain ⟨a, ha⟩ := Modified.isLaurent_qBinomZ (D.d i) (D.d_pos i)
          ((Λ.1 - R.rootSum ν) (R.coroot i) + N - n) t
        rw [← ha, ← hw_laurent_smul_eq]
        exact Submodule.smul_mem _ _ (dF_smul_mem_hwIntegral Λ i _ (ih i (N - t)))
      · exact zero_mem _
    · have hc : Commute (qDivPow (𝕧 ^ D.d i) N (E R 𝕧 i)) (qDivPow (𝕧 ^ D.d j) n (F R 𝕧 j)) :=
        ((Commute.pow_pow (E_mul_F_of_ne (R := R) (v := 𝕧) hij) N n).smul_left _).smul_right _
      rw [← mul_smul, hc.eq, mul_smul]
      exact dF_smul_mem_hwIntegral Λ j n (ih i N)

include hR in
/-- `V_ℤ(λ)` is stable under `Eᵢ^{(N)}` ([Kas91], after (6.1.12)). -/
theorem dE_smul_mem_hwIntegral (i : I) (N : ℕ) {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ hwIntegral Λ) : qDivPow (𝕧 ^ D.d i) N (E R 𝕧 i) • m ∈ hwIntegral Λ := by
  obtain ⟨x, hx, rfl⟩ := hm
  have h : negativeQuotientEquiv D x ∈ Subalgebra.toSubmodule (quotientIntegralForm D) :=
    (mem_negIntegral D x).1 hx
  rw [quotientIntegralForm, Algebra.adjoin_eq_span] at h
  rw [← (negativeQuotientEquiv D).symm_apply_apply x]
  generalize negativeQuotientEquiv D x = y at h
  induction h using Submodule.span_induction with
  | mem y hy => exact dE_smul_evq_mem_of_mem_closure hR Λ hy i N
  | zero => simp
  | add y y' _ _ hy hy' => rw [map_add, map_add, smul_add]; exact add_mem hy hy'
  | smul c y _ hy =>
    have : (negativeQuotientEquiv D).symm (c • y) = c • (negativeQuotientEquiv D).symm y := by
      change (negativeQuotientEquiv D).symm (integralLaurentEval c • y) =
        integralLaurentEval c • (negativeQuotientEquiv D).symm y
      exact map_smul _ _ _
    rw [this, laurent_smul_eq, map_smul, smul_algebra_smul_comm, ← hw_laurent_smul_eq]
    exact Submodule.smul_mem _ _ hy

/-! ### Prop. 6.1.3 for `V_ℤ(λ)` -/

omit [Finite I] [DecidableEq I] [AddCommGroup Y] in
/-- The `q`-binomials `[n, j]ᵢ` lie in `𝒜`. -/
lemma isLaurent_qBinomial (d n j : ℕ) : Modified.IsLaurent (qBinomial (𝕧 ^ d) n j) := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => exact Modified.isLaurent_one
    | succ j => exact Modified.isLaurent_zero
  | succ n ih =>
    cases j with
    | zero => exact Modified.isLaurent_one
    | succ j =>
      rw [qBinomial_succ_succ]
      exact ((Modified.isLaurent_inv_pow_pow d _).mul (ih _)).add
        ((Modified.isLaurent_pow_pow d _).mul (ih _))

omit [Finite I] in
lemma nodeSl2_dE_eq (i : I) (a : ℕ) (m : IrreducibleModule R 𝕧 Λ.1) :
    (nodeSl2 R 𝕧 _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dE a m =
      qDivPow (𝕧 ^ D.d i) a (E R 𝕧 i) • m := by
  rw [IntegrableSl2.dE_apply, nodeSl2_E, ← map_pow, qDivPow, smul_assoc]
  rfl

omit [Finite I] in
lemma nodeSl2_dF_eq (i : I) (a : ℕ) (m : IrreducibleModule R 𝕧 Λ.1) :
    (nodeSl2 R 𝕧 _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF a m =
      qDivPow (𝕧 ^ D.d i) a (F R 𝕧 i) • m := by
  rw [IntegrableSl2.dF_apply, nodeSl2_F, ← map_pow, qDivPow, smul_assoc]
  rfl

/-- **[Kas91] Prop. 6.1.3 for `V_ℤ(λ)`**: at a node `i`, the vectors of `V_ℤ(λ)` of `i`-weight
`-(h+1)` are the `𝒜`-linear combinations of vectors `Fᵢ^{(h+1+j)} y` with `y ∈ V_ℤ(λ)` of
`i`-weight `h+1+2j`. -/
theorem mem_hwIntegral_wt_iff (i : I) (h : ℕ) (u : IrreducibleModule R 𝕧 Λ.1) :
    u ∈ hwIntegral Λ ∧
        u ∈ (nodeSl2 R 𝕧 _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).wt
          (-((h + 1 : ℕ) : ℤ)) ↔
      u ∈ Submodule.span (LaurentPolynomial ℤ)
        {x | ∃ (j : ℕ) (y : IrreducibleModule R 𝕧 Λ.1), y ∈ hwIntegral Λ ∧
          y ∈ (nodeSl2 R 𝕧 _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).wt
            ((h + 1 + 2 * j : ℕ) : ℤ) ∧
          x = (nodeSl2 R 𝕧 _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF
            (h + 1 + j) y} :=
  IntegrableSl2.mem_integral_wt_iff (pow_ne_zero _ RatFunc.X_ne_zero)
    (fun n hn ↦ by rw [← pow_mul]; exact hvn_ratFunc _ (Nat.mul_pos (D.d_pos i) hn))
    integralLaurentEval (fun _ _ ↦ rfl) (hwIntegral Λ)
    (fun a x hx ↦ by rw [nodeSl2_dE_eq hR]; exact dE_smul_mem_hwIntegral hR Λ i a hx)
    (fun a x hx ↦ by rw [nodeSl2_dF_eq hR]; exact dF_smul_mem_hwIntegral Λ i a hx)
    (fun n j ↦ isLaurent_qBinomial (D.d i) n j) h u

end LieLean.QuantumGroup
