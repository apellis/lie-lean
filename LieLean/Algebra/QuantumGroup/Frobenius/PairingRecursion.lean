/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Frobenius.RadicalWords
import LieLean.Algebra.QuantumGroup.Modified.Triangular
import LieLean.Algebra.QuantumGroup.GabberKac.VermaOperator

/-!
# Pairing of Frobenius words at a root of `1`

Let `k` be a field of characteristic zero over `𝒜 = ℤ[v, v⁻¹]` in which `v` is a primitive
`2l`-th root of `1`, and `λ` a dominant weight satisfying the hypotheses of
`baseGen_one_mul_mem_frobRad` ([Lus] 35.3.2). We compute the form `frobPairBase` of `Λ_λ` on the
image of the splitting `Fr' : f_k → _k f`, `θᵢ ↦ θᵢ^{(lᵢ)}` ([Lus] 35.1.8): on words it is a
Shapovalov-type pairing `vermaForm` for explicit Gaussian-binomial coefficients, up to a unit.
This is a step towards [Lus] 35.4.2; the argument is ours.

Modulo the vectors of `V_ℤ(λ)` whose pairings with `V_ℤ(λ)` vanish in `k` (`nullSub`), the
divided powers `Fᵢ^{(b)}` and `Eᵢ^{(a)}` with `0 < a, b < lᵢ` act by zero (35.3.2 (c), (d) and
contravariance), so the commutation formula [Lus] 3.1.9 for `Eᵢ^{(lᵢ)} Fᵢ^{(lᵢ)}` reduces to
two terms.

## Main results

* `qBinomInt_eq_qBinomZ`, `integralLaurentEval_gaussBinom`: comparison of Gaussian binomials
  with integer top.
* `dE_smul_frobVec_sub_mem`: `Eᵢ^{(lᵢ)}` on the vectors `Fr(x)⁻ η` is the Verma-type operator
  `vermaOp` with coefficients `frobCoeff`, modulo `nullSub`.
* `exists_frobPair_eq_vermaForm`, `exists_frobPairBase_eq_vermaForm`: the pairing of Frobenius
  words is a unit times `vermaForm`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 3.1.9, 35.1.8, 35.3.2,
  35.4.2.
-/

open LieLean Finset LusztigF PowerSeries
open scoped TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ
local notation "hvt" => transcendental_ratFunc_X

/-! ### Two forms of the Gaussian binomial with integer top -/

section Binomial

variable {k : Type*} [Field k] {q : k}

/-- Pascal's rule `[a + 1; t + 1] = q^{-(t+1)} [a; t + 1] + q^{a-t} [a; t]` for `qBinomInt`. -/
lemma qBinomInt_add_one_succ (hq : q ≠ 0) (a : ℤ) (t : ℕ) :
    qBinomInt q (a + 1) (t + 1) =
      q ^ (-((t : ℤ) + 1)) * qBinomInt q a (t + 1) + q ^ (a - t) * qBinomInt q a t := by
  rw [← coeff_qBinomIntSeries, qBinomIntSeries_add_one hq, add_mul, one_mul, map_add,
    mul_assoc, coeff_C_mul, coeff_succ_X_mul, coeff_rescale, coeff_rescale,
    coeff_qBinomIntSeries, coeff_qBinomIntSeries, inv_pow, inv_pow, ← zpow_natCast,
    ← zpow_natCast, ← zpow_neg, ← zpow_neg, ← mul_assoc, ← zpow_add₀ hq]
  push_cast
  ring_nf

end Binomial

/-- `qBinomInt` and `qBinomZ` agree at a parameter which is not a root of `1`. -/
lemma qBinomInt_eq_qBinomZ {q : 𝕂} (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (m : ℤ)
    (t : ℕ) : qBinomInt q m t = qBinomZ q m t := by
  induction t generalizing m with
  | zero => simp
  | succ t ih =>
    have ht : qIntZ q ((t : ℤ) + 1) ≠ 0 := qIntZ_ne_zero hq0 hq (by omega)
    have hc : q ^ (-((t : ℤ) + 1)) ≠ 0 := zpow_ne_zero _ hq0
    induction m using Int.induction_on with
    | zero =>
      rw [Modified.qBinomZ_zero_succ, ← Nat.cast_zero, qBinomInt_natCast, qBinomial_zero_succ]
    | succ m hm => rw [qBinomInt_add_one_succ hq0, Modified.qBinomZ_succ_succ_eq hq0 _ _ ht, hm, ih]
    | pred m hm =>
      have h1 := qBinomInt_add_one_succ hq0 (-(m : ℤ) - 1) t
      have h2 := Modified.qBinomZ_succ_succ_eq hq0 (-(m : ℤ) - 1) t ht
      rw [sub_add_cancel] at h1 h2
      rw [hm, h2, ih] at h1
      exact (mul_left_cancel₀ hc (add_right_cancel h1)).symm

/-- Gaussian binomials over `𝒜` evaluated in `ℚ(v)`. -/
lemma integralLaurentEval_gaussBinom (d : ℕ) (hd : 0 < d) (m : ℤ) (t : ℕ) :
    integralLaurentEval (gaussBinom (laurentTUnit d) m t) = qBinomZ (𝕧 ^ d) m t := by
  have hv : integralLaurentEval (laurentTUnit d : 𝒜) = 𝕧 ^ d := by
    change integralLaurentEval (LaurentPolynomial.T (d : ℤ)) = _
    rw [integralLaurentEval_T, zpow_natCast]
  rw [map_gaussBinom_field, hv]
  refine qBinomInt_eq_qBinomZ (pow_ne_zero _ RatFunc.X_ne_zero) (fun n hn ↦ ?_) m t
  rw [← pow_mul]
  exact pow_ne_one_of_transcendental' hvt _ (Nat.mul_pos hd hn)

open GrandLoop

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular) (Λ : Dom R)

lemma quotientMinus_integralGenerator (i : I) (n : ℕ) :
    quotientMinus R (integralGenerator D i n : Quotient D 𝕧) = qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) := by
  change quotientMinus R (quotientIntegralGenerator D i n) = _
  rw [quotientIntegralGenerator, map_qDivPow', quotientMinus_θ]

lemma exists_quotientMinus_smul_hwv_eq {m : IrreducibleModule R 𝕧 Λ.1} (hm : m ∈ hwIntegral Λ) :
    ∃ z : quotientIntegralForm D,
      quotientMinus R (z : Quotient D 𝕧) • IrreducibleModule.hwv R 𝕧 Λ.1 = m := by
  obtain ⟨x, hx, rfl⟩ := hm
  exact ⟨⟨negativeQuotientEquiv D x, hx⟩, (evq_eq_quotientMinus_smul Λ x).symm⟩

/-! ### Vectors which pair to zero in `F` -/

section Null

variable (k : Type*) [Field k] [Algebra 𝒜 k]

/-- The vectors `m ∈ V_ℤ(λ)` whose pairings `(m, m')`, `m' ∈ V_ℤ(λ)`, vanish in `k`. -/
def nullSub : Submodule 𝒜 (IrreducibleModule R 𝕧 Λ.1) where
  carrier := {m | m ∈ hwIntegral Λ ∧ ∀ m' ∈ hwIntegral Λ, ∀ a : 𝒜,
    integralLaurentEval a = formL hvt hR Λ m m' → algebraMap 𝒜 k a = 0}
  add_mem' := by
    rintro m₁ m₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    refine ⟨add_mem h₁ h₂, fun m' hm' a ha ↦ ?_⟩
    obtain ⟨a₁, ha₁⟩ := isLaurent_formL hR Λ h₁ hm'
    obtain ⟨a₂, ha₂⟩ := isLaurent_formL hR Λ h₂ hm'
    have : a = a₁ + a₂ := integralLaurentEval_injective (by
      rw [ha, map_add, LinearMap.add_apply, map_add, ha₁, ha₂])
    rw [this, map_add, h₁' m' hm' a₁ ha₁, h₂' m' hm' a₂ ha₂, add_zero]
  zero_mem' := ⟨zero_mem _, fun m' _ a ha ↦ by
    rw [map_zero, LinearMap.zero_apply, ← map_zero integralLaurentEval] at ha
    rw [integralLaurentEval_injective ha, map_zero]⟩
  smul_mem' := by
    rintro c m ⟨h, h'⟩
    refine ⟨Submodule.smul_mem _ c h, fun m' hm' a ha ↦ ?_⟩
    obtain ⟨a₁, ha₁⟩ := isLaurent_formL hR Λ h hm'
    have : a = c * a₁ := integralLaurentEval_injective (by
      rw [ha, map_mul, ha₁, hw_laurent_smul_eq, map_smul, LinearMap.smul_apply, smul_eq_mul])
    rw [this, map_mul, h' m' hm' a₁ ha₁, mul_zero]

variable {k}

lemma mem_nullSub_iff {m : IrreducibleModule R 𝕧 Λ.1} :
    m ∈ nullSub hR Λ k ↔ m ∈ hwIntegral Λ ∧ ∀ m' ∈ hwIntegral Λ, ∀ a : 𝒜,
      integralLaurentEval a = formL hvt hR Λ m m' → algebraMap 𝒜 k a = 0 := Iff.rfl

lemma nullSub_le : nullSub hR Λ k ≤ hwIntegral Λ := fun _ h ↦ h.1

/-- `Fⱼ^{(n)}` preserves `nullSub`. -/
lemma dF_smul_mem_nullSub (j : I) (n : ℕ) {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ nullSub hR Λ k) : qDivPow (𝕧 ^ D.d j) n (F R 𝕧 j) • m ∈ nullSub hR Λ k := by
  refine ⟨dF_smul_mem_hwIntegral Λ j n hm.1, fun m' hm' a ha ↦ ?_⟩
  have h := rho_qDivPow_F_smul_mem_hwIntegral hR Λ j n hm'
  refine hm.2 _ h a ?_
  rw [ha, IrreducibleModule.isContravariant_form hR (pow_ne_one_of_transcendental' hvt)]

end Null

/-! ### Small divided powers of `θᵢ` lie in the radical -/

section Small

variable {k : Type*} [Field k] [Algebra 𝒜 k] {l : ℕ} (hl0 : 0 < l)
  (hl : algebraMap 𝒜 k (LaurentPolynomial.T 1) ^ (2 * l) = 1)
  (hprim : ∀ t, 0 < t → t < l → algebraMap 𝒜 k (LaurentPolynomial.T 1) ^ (2 * t) ≠ 1)
  (hA : ∀ i j, i ≠ j → 2 ≤ D.frobOrder l j → ∀ a : ℕ, D.cartanMatrix i j = -a →
    a < D.frobOrder l i)
  (hΛ : ∀ i, 2 ≤ D.frobOrder l i → D.frobOrder l i ∣ (Λ.1 (R.coroot i)).toNat)
include hl0 hl hprim hA hΛ

/-- If `lᵢ ≥ 2`, then `θᵢ Z` lies in the radical for every `Z ∈ _F f` (cf. [Lus] 35.3.2). -/
theorem baseGen_one_mul_mem_frobRad_of_two_le [CharZero k] (i : I) (hi : 2 ≤ D.frobOrder l i)
    (Z : k ⊗[𝒜] quotientIntegralForm D) : baseGen D k i 1 * Z ∈ frobRad hR Λ k := by
  have hZ : Z ∈ (⊤ : Submodule k (k ⊗[𝒜] quotientIntegralForm D)) := trivial
  rw [← span_frobWords_sup_frobRad hR Λ hl0 hl hprim hA hΛ, Submodule.mem_sup] at hZ
  obtain ⟨s, hs, r, hr, rfl⟩ := hZ
  rw [mul_add]
  refine add_mem ?_ (mul_mem_frobRad hR Λ k _ hr)
  induction hs using Submodule.span_induction with
  | mem w hw => exact baseGen_one_mul_mem_frobRad hR Λ hl0 hl hprim hA hΛ hw i hi
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha

/-- `Fᵢ^{(b)} V_ℤ(λ) ⊆ nullSub` for `0 < b < lᵢ`. -/
theorem dF_smul_mem_nullSub_of_lt [CharZero k] (i : I) {b : ℕ} (hb0 : 0 < b)
    (hb : b < D.frobOrder l i) {m : IrreducibleModule R 𝕧 Λ.1} (hm : m ∈ hwIntegral Λ) :
    qDivPow (𝕧 ^ D.d i) b (F R 𝕧 i) • m ∈ nullSub hR Λ k := by
  refine ⟨dF_smul_mem_hwIntegral Λ i b hm, fun m' hm' a ha ↦ ?_⟩
  obtain ⟨z, rfl⟩ := exists_quotientMinus_smul_hwv_eq Λ hm
  obtain ⟨z', rfl⟩ := exists_quotientMinus_smul_hwv_eq Λ hm'
  have e : a = frobPair hR Λ (integralGenerator D i b * z) z' := integralLaurentEval_injective (by
    rw [ha, integralLaurentEval_frobPair, Subalgebra.coe_mul, map_mul, mul_smul,
      quotientMinus_integralGenerator])
  have hX : (1 : k) ⊗ₜ[𝒜] (integralGenerator D i b * z) ∈ frobRad hR Λ k := by
    rw [show (1 : k) ⊗ₜ[𝒜] (integralGenerator D i b * z) =
        baseGen D k i b * (1 ⊗ₜ[𝒜] z) by rw [baseGen, Algebra.TensorProduct.tmul_mul_tmul, one_mul],
      baseGen_eq_smul_pow_of_lt D hl0 hl hprim i hb, ← Nat.sub_add_cancel hb0, pow_succ',
      smul_mul_assoc, mul_assoc]
    exact Submodule.smul_mem _ _
      (baseGen_one_mul_mem_frobRad_of_two_le hR Λ hl0 hl hprim hA hΛ i (by omega) _)
  have h0 := LinearMap.congr_fun ((LinearMap.mem_ker).1 hX) ((1 : k) ⊗ₜ[𝒜] z')
  rw [frobPairBase_tmul, mul_one, mul_one, LinearMap.zero_apply] at h0
  rw [e, h0]

end Small

/-! ### Frobenius words in `L_q(λ)` -/

section Words

variable (D) in
/-- `Σⱼ μⱼ lⱼ j'`. -/
def frobRootSum (R : D.RootDatum Y) (l : ℕ) (μ : I →₀ ℕ) : Y →+ ℤ :=
  μ.sum fun j n ↦ (n * D.frobOrder l j) • R.root j

omit [Finite I] [DecidableEq I] in
lemma frobRootSum_add (l : ℕ) (μ ν : I →₀ ℕ) :
    frobRootSum D R l (μ + ν) = frobRootSum D R l μ + frobRootSum D R l ν :=
  Finsupp.sum_add_index' (by simp) (fun _ _ _ ↦ by rw [add_mul, add_smul])

omit [Finite I] [DecidableEq I] in
@[simp] lemma frobRootSum_zero (l : ℕ) : frobRootSum D R l 0 = 0 := by
  simp [frobRootSum]

omit [Finite I] [DecidableEq I] in
@[simp] lemma frobRootSum_single (l : ℕ) (j : I) (n : ℕ) :
    frobRootSum D R l (Finsupp.single j n) = (n * D.frobOrder l j) • R.root j := by
  simp [frobRootSum]

variable (D) in
/-- The algebra map `FreeAlgebra 𝒜 I → 𝒜f`, `xⱼ ↦ θⱼ^{(lⱼ)}`. -/
def frobGen (l : ℕ) : FreeAlgebra 𝒜 I →ₐ[𝒜] quotientIntegralForm D :=
  FreeAlgebra.lift 𝒜 fun j ↦ integralGenerator D j (D.frobOrder l j)

variable (l : ℕ)

/-- The vector `Fr(x)⁻ η ∈ V_ℤ(λ)` attached to `x ∈ FreeAlgebra 𝒜 I`. -/
def frobVec (x : FreeAlgebra 𝒜 I) : IrreducibleModule R 𝕧 Λ.1 :=
  quotientMinus R (frobGen D l x : Quotient D 𝕧) • IrreducibleModule.hwv R 𝕧 Λ.1

lemma frobVec_mem (x : FreeAlgebra 𝒜 I) : frobVec Λ l x ∈ hwIntegral Λ :=
  quotientMinus_smul_hwv_mem_hwIntegral Λ (frobGen D l x).2

@[simp] lemma frobVec_one : frobVec Λ l 1 = IrreducibleModule.hwv R 𝕧 Λ.1 := by
  simp [frobVec]

lemma frobVec_ι_mul (j : I) (x : FreeAlgebra 𝒜 I) :
    frobVec Λ l (FreeAlgebra.ι 𝒜 j * x) =
      qDivPow (𝕧 ^ D.d j) (D.frobOrder l j) (F R 𝕧 j) • frobVec Λ l x := by
  rw [frobVec, frobVec, map_mul, frobGen, FreeAlgebra.lift_ι_apply, Subalgebra.coe_mul, map_mul,
    mul_smul, quotientMinus_integralGenerator]

lemma frobVec_add (x y : FreeAlgebra 𝒜 I) :
    frobVec Λ l (x + y) = frobVec Λ l x + frobVec Λ l y := by
  rw [frobVec, frobVec, frobVec, map_add, Subalgebra.coe_add, map_add, add_smul]

@[simp] lemma frobVec_zero : frobVec Λ l 0 = 0 := by
  simp [frobVec]

lemma frobVec_smul (c : 𝒜) (x : FreeAlgebra 𝒜 I) :
    frobVec Λ l (c • x) = c • frobVec Λ l x := by
  rw [frobVec, frobVec, map_smul, coe_smul_integralForm, map_smul, smul_assoc,
    ← hw_laurent_smul_eq]

lemma frobVec_mem_weightSpace {μ : I →₀ ℕ} {x : FreeAlgebra 𝒜 I}
    (hx : x ∈ FreeAlgebra.wordSpan 𝒜 μ) :
    frobVec Λ l x ∈ weightSpace R 𝕧 _ (Λ.1 - frobRootSum D R l μ) := by
  induction hx using FreeAlgebra.wordSpan_induction with
  | word w hw =>
    subst hw
    induction w with
    | nil =>
      simpa using IrreducibleModule.hwv_mem_weightSpace (R := R) (v := 𝕧) (Λ := Λ.1)
    | cons j w ih =>
      rw [← FreeAlgebra.ι_mul_wordBasis, frobVec_ι_mul, wordWeight_cons, frobRootSum_add,
        frobRootSum_single, one_mul, sub_add_eq_sub_sub_swap]
      exact qDivPow_F_smul_mem_weightSpace ih j _
  | zero => rw [← zero_smul 𝒜 (0 : FreeAlgebra 𝒜 I), frobVec_smul, zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [frobVec_add]; exact add_mem hx hy
  | smul c x _ hx => rw [frobVec_smul, hw_laurent_smul_eq]; exact Submodule.smul_mem _ _ hx

/-- The coefficients `[⟨i, λ - Σⱼ μⱼ lⱼ j'⟩; lᵢ]ᵢ` of the operator `Eᵢ^{(lᵢ)}` on Frobenius
words. -/
def frobCoeff (i : I) (μ : I →₀ ℕ) : 𝒜 :=
  gaussBinom (laurentTUnit (D.d i)) ((Λ.1 - frobRootSum D R l μ) (R.coroot i)) (D.frobOrder l i)


/-! ### The pairing on Frobenius words -/

omit [Finite I] in
/-- `ρ(Fᵢ^{(n)})` acts on the vectors of weight `μ` as `v^e Eᵢ^{(n)}`, with `e` depending only on
`μ`, `i` and `n` (cf. [Lus] 19.3.2). -/
lemma exists_rho_dF_smul_eq (μ : Y →+ ℤ) (i : I) (n : ℕ) : ∃ e : ℤ,
    ∀ m ∈ weightSpace R 𝕧 (IrreducibleModule R 𝕧 Λ.1) μ,
      rho R 𝕧 (qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i)) • m =
        𝕧 ^ e • (qDivPow (𝕧 ^ D.d i) n (E R 𝕧 i) • m) := by
  have h1 : ∃ e : ℤ, ∀ m ∈ weightSpace R 𝕧 (IrreducibleModule R 𝕧 Λ.1) μ,
      (K R 𝕧 (-ktilde R i) * E R 𝕧 i) ^ n • m = 𝕧 ^ e • (E R 𝕧 i ^ n • m) := by
    induction n with
    | zero => exact ⟨0, fun m _ ↦ by simp⟩
    | succ n ih =>
      obtain ⟨e, he⟩ := ih
      refine ⟨e + (μ + (n + 1) • R.root i) (-ktilde R i), fun m hm ↦ ?_⟩
      rw [pow_succ', mul_smul, he m hm, smul_comm _ (𝕧 ^ e), mul_smul, ← mul_smul (E R 𝕧 i),
        ← pow_succ', E_pow_smul_mem_weightSpace Λ hm i (n + 1) (-ktilde R i), smul_smul,
        ← zpow_add₀ (NeZero.ne _)]
  obtain ⟨e, he⟩ := h1
  refine ⟨(D.d i * n : ℕ) + e, fun m hm ↦ ?_⟩
  rw [qDivPow, qDivPow, map_smul, rho_pow, rho_F, rhoF, smul_pow, smul_assoc, smul_assoc,
    he m hm, smul_assoc, smul_smul, smul_smul, smul_smul, zpow_add₀ (NeZero.ne _), zpow_natCast,
    pow_mul]
  ring_nf

/-- The `𝒜`-valued pairing of the Frobenius words: `frobPair` of `Fr(x)`, `Fr(y)`. -/
lemma integralLaurentEval_frobPair_frobGen (x y : FreeAlgebra 𝒜 I) :
    integralLaurentEval (frobPair hR Λ (frobGen D l x) (frobGen D l y)) =
      formL hvt hR Λ (frobVec Λ l x) (frobVec Λ l y) :=
  integralLaurentEval_frobPair hR Λ _ _

/-- The pairing with the empty word is the augmentation: `(η, Fr(y)⁻ η) = ε(y)`. -/
lemma frobPair_nil (hl0 : 0 < l) (y : FreeAlgebra 𝒜 I) :
    frobPair hR Λ (frobGen D l (FreeAlgebra.wordBasis 𝒜 I [])) (frobGen D l y) =
      FreeAlgebra.algebraMapInv y := by
  induction y using FreeAlgebra.induction_wordBasis with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul c x hx => rw [map_smul, map_smul, map_smul, hx]
  | word u =>
    refine integralLaurentEval_injective ?_
    rw [integralLaurentEval_frobPair_frobGen, FreeAlgebra.wordBasis_nil, frobVec_one]
    cases u with
    | nil => simp
    | cons j u =>
      obtain ⟨n, hn⟩ : ∃ n, D.frobOrder l j = n + 1 :=
        Nat.exists_eq_succ_of_ne_zero (D.frobOrder_pos hl0 j).ne'
      rw [← FreeAlgebra.ι_mul_wordBasis, frobVec_ι_mul, hn, qDivPow, smul_assoc, map_smul,
        pow_succ', mul_smul, IrreducibleModule.form_hwv_F_smul, smul_zero]
      simp [FreeAlgebra.algebraMapInv]


end Words

section Core

variable {k : Type*} [Field k] [Algebra 𝒜 k] [CharZero k] {l : ℕ} (hl0 : 0 < l)
  (hl : algebraMap 𝒜 k (LaurentPolynomial.T 1) ^ (2 * l) = 1)
  (hprim : ∀ t, 0 < t → t < l → algebraMap 𝒜 k (LaurentPolynomial.T 1) ^ (2 * t) ≠ 1)
  (hA : ∀ i j, i ≠ j → 2 ≤ D.frobOrder l j → ∀ a : ℕ, D.cartanMatrix i j = -a →
    a < D.frobOrder l i)
  (hΛ : ∀ i, 2 ≤ D.frobOrder l i → D.frobOrder l i ∣ (Λ.1 (R.coroot i)).toNat)
include hl0 hl hprim hA hΛ

/-- **The commutation of `Eᵢ^{(lᵢ)}` with Frobenius words**: modulo vectors pairing to zero in
`k`, `Eᵢ^{(lᵢ)}` acts on the vectors `Fr(x)⁻ η` as the Verma-type operator with coefficients
`frobCoeff` (via [Lus] 3.1.9 and 35.3.2 (c), (d)). -/
theorem dE_smul_frobVec_sub_mem (i : I) (x : FreeAlgebra 𝒜 I) :
    qDivPow (𝕧 ^ D.d i) (D.frobOrder l i) (E R 𝕧 i) • frobVec Λ l x -
      frobVec Λ l (vermaOp i (frobCoeff Λ l i) x) ∈ nullSub hR Λ k := by
  obtain ⟨n, hn⟩ : ∃ n, D.frobOrder l i = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (D.frobOrder_pos hl0 i).ne'
  induction x using FreeAlgebra.induction_wordBasis with
  | zero =>
    rw [← zero_smul 𝒜 (0 : FreeAlgebra 𝒜 I), map_smul, frobVec_smul, frobVec_smul, zero_smul,
      zero_smul, smul_zero, sub_zero]
    exact zero_mem _
  | add x y hx hy =>
    rw [map_add, frobVec_add, frobVec_add, smul_add]
    convert add_mem hx hy using 1
    abel
  | smul c x hx =>
    rw [map_smul, frobVec_smul, frobVec_smul, laurent_smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ c hx
  | word w =>
    induction w with
    | nil =>
      rw [FreeAlgebra.wordBasis_nil, vermaOp_one, frobVec_one, hn,
        qDivPow_E_smul_hwv Λ i n.succ_pos, ← zero_smul 𝒜 (0 : FreeAlgebra 𝒜 I), frobVec_smul,
        zero_smul, sub_zero]
      exact zero_mem _
    | cons j w ih =>
      rw [← FreeAlgebra.ι_mul_wordBasis, vermaOp_ι_mul, frobVec_ι_mul, frobVec_add,
        frobVec_ι_mul]
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl, weightScale_of_mem _ (FreeAlgebra.wordBasis_mem_wordSpan w),
          frobVec_smul]
        have hm := frobVec_mem_weightSpace Λ l (FreeAlgebra.wordBasis_mem_wordSpan (R := 𝒜) w)
        rw [hn, qDivPow_E_smul_qDivPow_F_smul hvn_ratFunc hm, sum_range_succ, sum_range_succ']
        set m := frobVec Λ l (FreeAlgebra.wordBasis 𝒜 I w)
        have hlast : efTerm R 𝕧 i ((Λ.1 - frobRootSum D R l (wordWeight w)) (R.coroot i))
            (n + 1) (n + 1) (n + 1) m = frobCoeff Λ l i (wordWeight w) • m := by
          rw [efTerm, ite_eq_left le_rfl, frobCoeff, hn, hw_laurent_smul_eq,
            integralLaurentEval_gaussBinom _ (D.d_pos i), Nat.sub_self, qDivPow_zero',
            qDivPow_zero', one_smul, one_smul, add_sub_cancel_right]
        have hfirst : efTerm R 𝕧 i ((Λ.1 - frobRootSum D R l (wordWeight w)) (R.coroot i))
            (n + 1) (n + 1) 0 m - qDivPow (𝕧 ^ D.d i) (n + 1) (F R 𝕧 i) •
              frobVec Λ l (vermaOp i (frobCoeff Λ l i) (FreeAlgebra.wordBasis 𝒜 I w)) ∈
              nullSub hR Λ k := by
          rw [efTerm, ite_eq_left (Nat.zero_le _), qBinomZ_zero, one_smul, Nat.sub_zero,
            ← smul_sub]
          rw [hn] at ih
          exact dF_smul_mem_nullSub hR Λ i _ ih
        have hmid : ∑ t ∈ range n, efTerm R 𝕧 i
            ((Λ.1 - frobRootSum D R l (wordWeight w)) (R.coroot i)) (n + 1) (n + 1) (t + 1) m ∈
              nullSub hR Λ k := by
          refine sum_mem fun t ht ↦ ?_
          rw [mem_range] at ht
          rw [efTerm, ite_eq_left (by omega)]
          obtain ⟨a, ha⟩ := Modified.isLaurent_qBinomZ (D.d i) (D.d_pos i)
            ((Λ.1 - frobRootSum D R l (wordWeight w)) (R.coroot i) + ↑(n + 1) - ↑(n + 1)) (t + 1)
          rw [← ha, ← hw_laurent_smul_eq]
          refine Submodule.smul_mem _ _ (dF_smul_mem_nullSub_of_lt hR Λ hl0 hl hprim hA hΛ i
            (by omega) (by omega) (dE_smul_mem_hwIntegral hR Λ i _ (frobVec_mem Λ l _)))
        convert add_mem (add_mem hmid hfirst) (zero_mem (nullSub hR Λ k)) using 1
        rw [hlast]
        abel
      · rw [ite_eq_right hij, frobVec_zero, add_zero]
        have hc : Commute (qDivPow (𝕧 ^ D.d i) (D.frobOrder l i) (E R 𝕧 i))
            (qDivPow (𝕧 ^ D.d j) (D.frobOrder l j) (F R 𝕧 j)) :=
          ((Commute.pow_pow (E_mul_F_of_ne (R := R) (v := 𝕧) hij) _ _).smul_left _).smul_right _
        rw [← mul_smul, hc.eq, mul_smul, ← smul_sub]
        exact dF_smul_mem_nullSub hR Λ j _ ih

/-- **The recursion for the pairing on Frobenius words**: in `k`,
`(Fr(iw)⁻η, Fr(x)⁻η) = v^e (Fr(w)⁻η, Fr(Eᵢ'x)⁻η)` for `x` of weight `μ`, where `Eᵢ'` is the
Verma-type operator with coefficients `frobCoeff` and `e` depends only on `μ` and `i`. -/
theorem exists_frobPair_cons_eq (i : I) (μ : I →₀ ℕ) : ∃ e : ℤ,
    ∀ x ∈ FreeAlgebra.wordSpan 𝒜 μ, ∀ w : List I,
      algebraMap 𝒜 k (frobPair hR Λ (frobGen D l (FreeAlgebra.wordBasis 𝒜 I (i :: w)))
        (frobGen D l x)) =
      algebraMap 𝒜 k (LaurentPolynomial.T e) *
        algebraMap 𝒜 k (frobPair hR Λ (frobGen D l (FreeAlgebra.wordBasis 𝒜 I w))
          (frobGen D l (vermaOp i (frobCoeff Λ l i) x))) := by
  obtain ⟨e, he⟩ := exists_rho_dF_smul_eq Λ (Λ.1 - frobRootSum D R l μ) i (D.frobOrder l i)
  refine ⟨e, fun x hx w ↦ ?_⟩
  set mw := frobVec Λ l (FreeAlgebra.wordBasis 𝒜 I w)
  have hN := dE_smul_frobVec_sub_mem hR Λ hl0 hl hprim hA hΛ (k := k) i x
  obtain ⟨a, ha⟩ := isLaurent_formL hR Λ hN.1 (frobVec_mem Λ l (FreeAlgebra.wordBasis 𝒜 I w))
  have hk := hN.2 _ (frobVec_mem Λ l _) a ha
  rw [IrreducibleModule.form_comm, map_sub] at ha
  have key : frobPair hR Λ (frobGen D l (FreeAlgebra.wordBasis 𝒜 I (i :: w))) (frobGen D l x) =
      LaurentPolynomial.T e * (frobPair hR Λ (frobGen D l (FreeAlgebra.wordBasis 𝒜 I w))
        (frobGen D l (vermaOp i (frobCoeff Λ l i) x)) + a) := by
    refine integralLaurentEval_injective ?_
    rw [map_mul, map_add, integralLaurentEval_T, integralLaurentEval_frobPair_frobGen,
      integralLaurentEval_frobPair_frobGen, ha,
      ← FreeAlgebra.ι_mul_wordBasis, frobVec_ι_mul,
      IrreducibleModule.isContravariant_form hR (pow_ne_one_of_transcendental' hvt),
      he _ (frobVec_mem_weightSpace Λ l hx), map_smul, smul_eq_mul]
    ring
  rw [key, map_mul, map_add, hk, add_zero]

/-- **The pairing on Frobenius words is a Shapovalov-type form**: for a word
`w` and a weight `μ` there is a unit `κ` of `k` with `(Fr(w)⁻η, Fr(x)⁻η) = κ S(w, x)` in `k`
for all `x` of weight `μ`, where `S` is the pairing `vermaForm` of the operators with
coefficients `frobCoeff`. -/
theorem exists_frobPair_eq_vermaForm (w : List I) (μ : I →₀ ℕ) : ∃ κ : k, IsUnit κ ∧
    ∀ x ∈ FreeAlgebra.wordSpan 𝒜 μ,
      algebraMap 𝒜 k (frobPair hR Λ (frobGen D l (FreeAlgebra.wordBasis 𝒜 I w))
        (frobGen D l x)) =
      κ * algebraMap 𝒜 k (vermaForm (fun i ↦ frobCoeff Λ l i) w x) := by
  induction w generalizing μ with
  | nil =>
    exact ⟨1, isUnit_one, fun x _ ↦ by
      rw [one_mul, frobPair_nil hR Λ (l := l) hl0, vermaForm_nil]⟩
  | cons i w ih =>
    obtain ⟨e, he⟩ := exists_frobPair_cons_eq hR Λ hl0 hl hprim hA hΛ (k := k) i μ
    obtain ⟨κ, hκ, hκ'⟩ := ih (μ - Finsupp.single i 1)
    refine ⟨algebraMap 𝒜 k (LaurentPolynomial.T e) * κ,
      ((LaurentPolynomial.isUnit_T e).map _).mul hκ, fun x hx ↦ ?_⟩
    rw [he x hx w, hκ' _ (vermaOp_mem_wordSpan _ _ hx), vermaForm_cons, mul_assoc]

omit [Finite I] [CharZero k] hl0 hl hprim hA hΛ in
lemma frobSplitHom_wordBasis (u : List I) :
    frobSplitHom D k l (FreeAlgebra.wordBasis k I u) =
      (1 : k) ⊗ₜ frobGen D l (FreeAlgebra.wordBasis 𝒜 I u) := by
  induction u with
  | nil => simp [Algebra.TensorProduct.one_def]
  | cons j u ih =>
    rw [← FreeAlgebra.ι_mul_wordBasis, ← FreeAlgebra.ι_mul_wordBasis, map_mul, map_mul, ih,
      frobGen, FreeAlgebra.lift_ι_apply, ← frobGen]
    rw [show frobSplitHom D k l (FreeAlgebra.ι k j) = baseGen D k j (D.frobOrder l j) from
      frobSplitHom_θ D k l j, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- **The form of `Λ_λ` on `_k f` via the splitting `Fr'`**: for a word `w`
and a weight `μ` there is a unit `κ` with `(Fr'(θ_w), Fr'(y)) = κ S(w, y)` for all `y ∈ f_k` of
weight `μ`, `S` the pairing `vermaForm` over `k` with the images of the coefficients
`frobCoeff`. -/
theorem exists_frobPairBase_eq_vermaForm (w : List I) (μ : I →₀ ℕ) : ∃ κ : k, IsUnit κ ∧
    ∀ y ∈ FreeAlgebra.wordSpan k μ,
      frobPairBase hR Λ k (frobSplitHom D k l (FreeAlgebra.wordBasis k I w))
        (frobSplitHom D k l y) =
      κ * vermaForm (fun i ↦ algebraMap 𝒜 k ∘ frobCoeff Λ l i) w y := by
  obtain ⟨κ, hκ, hκ'⟩ := exists_frobPair_eq_vermaForm hR Λ hl0 hl hprim hA hΛ (k := k) w μ
  refine ⟨κ, hκ, fun y hy ↦ ?_⟩
  induction hy using FreeAlgebra.wordSpan_induction with
  | word u hu =>
    rw [frobSplitHom_wordBasis, frobSplitHom_wordBasis, frobPairBase_tmul, mul_one,
      hκ' _ (hu ▸ FreeAlgebra.wordBasis_mem_wordSpan u), map_vermaForm,
      FreeAlgebra.mapCoeffs_wordBasis, mul_one]
  | zero => rw [map_zero, map_zero, map_zero, mul_zero]
  | add y z _ _ hy hz => rw [map_add, map_add, map_add, hy, hz, mul_add]
  | smul c y _ hy => rw [map_smul, map_smul, map_smul, hy, smul_eq_mul, smul_eq_mul, mul_left_comm]

end Core

end LieLean.QuantumGroup
