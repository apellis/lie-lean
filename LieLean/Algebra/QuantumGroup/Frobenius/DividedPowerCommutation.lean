/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Frobenius.Generators
import LieLean.Algebra.QuantumGroup.RootOfUnity.GaussBinomialSums

/-!
# Commuting `θᵢ^{(lᵢ)}` past `θⱼ` at a root of `1`

[Lus] Prop. 35.3.1: over the field `F` of [Lus] 35.2.1, if `i ≠ j` and `lᵢ ≥ a + 1` with
`a = -⟨i, j'⟩`, then in `_F f`
`θᵢ^{(lᵢ)} θⱼ = Σ_{r=0}^{a} vᵢ^{lᵢ(a-r)} [a; r]ᵢ θᵢ^{(r)} θⱼ θᵢ^{(lᵢ-r)}`.

## Main results

* `QuantumGroup.integralGenerator_mul_integralGenerator_eq_sum`: [Lus] Cor. 7.1.7 in `𝒜f`, with
  Laurent coefficients `laurentHigherSerreCoeff`.
* `QuantumGroup.baseGen_frobOrder_mul_baseGen`: [Lus] Prop. 35.3.1.

## Proof

As in [Lus]: Cor. 7.1.7 with `m = lᵢ`, `n = 1`, and the identity [Lus] 34.1.4 (a)
(`sum_qBinomial_root`) for the coefficients.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 7.1.7, 34.1.4, 35.2.1,
  35.3.1.
-/

open LieLean Finset LusztigF
open scoped TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

universe u

variable {I : Type u} [DecidableEq I] (D : LusztigCartanDatum I)

/-- The Laurent polynomial `γ_s = Σ_{q=0}^{m-an-1} (-1)^{s+1+q} vᵢ^{-s(an-m+1+q)+q} [s; q]ᵢ` of
[Lus] Cor. 7.1.7. -/
def laurentHigherSerreCoeff (i : I) (a n m s : ℕ) : 𝒜 :=
  ∑ q ∈ range (m - a * n), (-1) ^ (s + 1 + q) *
    LaurentPolynomial.T ((D.d i : ℤ) * (-(s : ℤ) * ((a : ℤ) * n - m + 1 + q) + q)) *
      qBinomialU (laurentTUnit (D.d i)) s q

omit [DecidableEq I] in
lemma integralLaurentEval_laurentHigherSerreCoeff (i : I) (a n m s : ℕ) :
    integralLaurentEval (laurentHigherSerreCoeff D i a n m s) = higherSerreCoeff D i a n m s := by
  have hT : integralLaurentEval (laurentTUnit (D.d i) : 𝒜) = 𝕧 ^ D.d i := by
    simp [laurentTUnit]
  simp only [laurentHigherSerreCoeff, higherSerreCoeff, map_sum, map_mul, map_pow, map_neg,
    map_one, integralLaurentEval_T, map_qBinomialU, hT]

/-- [Lus] Cor. 7.1.7 in `𝒜f`: for `i ≠ j`, `a = -⟨i, j'⟩` and `m > an`,
`θᵢ^{(m)} θⱼ^{(n)} = Σ_{r ≤ an} γ_{m-r} θᵢ^{(r)} θⱼ^{(n)} θᵢ^{(m-r)}`. -/
theorem integralGenerator_mul_integralGenerator_eq_sum {i j : I} (hij : i ≠ j) {a n m : ℕ}
    (ha : D.cartanMatrix i j = -a) (hm : a * n < m) :
    integralGenerator D i m * integralGenerator D j n =
      ∑ r ∈ range (a * n + 1), laurentHigherSerreCoeff D i a n m (m - r) •
        (integralGenerator D i r * integralGenerator D j n * integralGenerator D i (m - r)) := by
  apply Subtype.ext
  rw [MulMemClass.coe_mul, coe_integralGenerator, coe_integralGenerator, ← map_mul,
    toQuotient_fDivPow_mul_fDivPow hij ha hm, AddSubmonoidClass.coe_finsetSum]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [coe_smul_integralForm, integralLaurentEval_laurentHigherSerreCoeff, MulMemClass.coe_mul,
    MulMemClass.coe_mul, coe_integralGenerator, coe_integralGenerator, coe_integralGenerator,
    map_mul, map_mul]

variable {F : Type*} [Field F] [Algebra 𝒜 F] {l : ℕ}

local notation "ε" => algebraMap 𝒜 F (LaurentPolynomial.T 1)

variable (hl0 : 0 < l) (hl : algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (2 * l) = 1)
  (hprim : ∀ t, 0 < t → t < l → algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (2 * t) ≠ 1)
include hl0 hl hprim

omit [DecidableEq I] in
/-- The coefficients of [Lus] 7.1.7 at `m = lᵢ`, `n = 1` in `F` ([Lus] 34.1.4 (a)). -/
lemma algebraMap_laurentHigherSerreCoeff (i : I) {a r : ℕ} (hra : r ≤ a)
    (hal : a < D.frobOrder l i) :
    algebraMap 𝒜 F (laurentHigherSerreCoeff D i a 1 (D.frobOrder l i) (D.frobOrder l i - r)) =
      (ε ^ D.d i) ^ ((D.frobOrder l i : ℤ) * ((a : ℤ) - r)) * qBinomial (ε ^ D.d i) a r := by
  set L := D.frobOrder l i
  set q := ε ^ D.d i
  have hε := algebraMap_T_one_ne_zero (F := F) hl0 hl
  have hq : q ≠ 0 := pow_ne_zero _ hε
  rw [← sum_qBinomial_root hq (pow_d_pow_frobOrder D hl0 hl hprim i)
    (pow_d_pow_ne_one D hl0 hl hprim i) hra hal, laurentHigherSerreCoeff, map_sum, mul_one]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [map_mul, map_mul, map_pow, map_neg, map_one, algebraMap_T, map_qBinomialU,
    algebraMap_laurentTUnit, show (L - r + 1 + s) = L - r + 1 + s from rfl]
  congr 2
  rw [zpow_mul, zpow_natCast]
  congr 1
  push_cast [show r ≤ L by omega]
  ring

/-- **[Lus] Prop. 35.3.1**: if `i ≠ j`, `a = -⟨i, j'⟩` and `lᵢ ≥ a + 1`, then in `_F f`
`θᵢ^{(lᵢ)} θⱼ = Σ_{r=0}^{a} vᵢ^{lᵢ(a-r)} [a; r]ᵢ θᵢ^{(r)} θⱼ θᵢ^{(lᵢ-r)}`. -/
theorem baseGen_frobOrder_mul_baseGen {i j : I} (hij : i ≠ j) {a : ℕ}
    (ha : D.cartanMatrix i j = -a) (hal : a < D.frobOrder l i) :
    baseGen D F i (D.frobOrder l i) * baseGen D F j 1 =
      ∑ r ∈ range (a + 1), ((ε ^ D.d i) ^ ((D.frobOrder l i : ℤ) * ((a : ℤ) - r)) *
        qBinomial (ε ^ D.d i) a r) •
          (baseGen D F i r * baseGen D F j 1 * baseGen D F i (D.frobOrder l i - r)) := by
  simp only [baseGen]
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    integralGenerator_mul_integralGenerator_eq_sum D hij ha (by omega), mul_one,
    TensorProduct.tmul_sum]
  refine sum_congr rfl fun r hr ↦ ?_
  rw [TensorProduct.tmul_smul, ← algebraMap_smul F,
    algebraMap_laurentHigherSerreCoeff D hl0 hl hprim i (by simpa [Nat.lt_succ_iff] using hr) hal,
    Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]

end LieLean.QuantumGroup
