/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Frobenius.PairingRecursion
import LieLean.Algebra.QuantumGroup.IrreducibleCharacter.ShapovalovSign

/-!
# The splitting `Fr'` modulo the radical of `Λ_λ`

Let `k` be a field of characteristic zero over `𝒜 = ℤ[v, v⁻¹]` in which `v` is a primitive
`2l`-th root of `1`, `ε` the image of `v`, and `λ` a dominant weight satisfying the hypotheses of
`baseGen_one_mul_mem_frobRad` ([Lus] 35.3.2). Write `lᵢ` for the integers of [Lus] 2.2.4,
`(I, ∘)` for the Cartan datum `LusztigCartanDatum.frobenius` and `nᵢ = ⟨i, λ⟩ / lᵢ`.

By `exists_frobPairBase_eq_vermaForm`, the form `frobPairBase` of `Λ_λ` on the image of the
splitting `Fr' : f_k → _k f`, `θᵢ ↦ θᵢ^{(lᵢ)}` ([Lus] 35.1.8) is, up to units, the pairing
`vermaForm` with coefficients the images of the Gaussian binomials
`[lᵢ (nᵢ - ⟨μ, αᵢ^∨⟩_∘); lᵢ]ᵢ`. By [Lus] 34.1.2 (b) these are `qᵢ^{nᵢ + 1 - ⟨μ, αᵢ^∨⟩_∘}` times
the classical coefficients `nᵢ - ⟨μ, αᵢ^∨⟩_∘` of `(I, ∘)`, with `qᵢ = ε^{dᵢ*} = ±1`
(`algebraMap_frobCoeff`). So the quasi-classical kernel
(`LusztigF.mem_serreSpan_of_shapovalovMap_eq_zero_of_sq_eq_one`) applies: an element `y` of
`f_k` of weight `ν` with `νᵢ ≤ nᵢ` for all `i` and `Fr'(y)` in the radical `frobRad` lies in the
span of the quantum Serre products of `(I, ∘)` at `ε`
(`mem_serreSpan_of_frobSplitHom_mem_frobRad`), so its image in `_k f*` is zero
(`quasiClassicalHom_eq_zero_of_frobSplitHom_mem_frobRad`). This is a step towards
[Lus] 35.4.2; the argument is ours.

## Main results

* `frobRootSum_coroot`: `⟨Σⱼ μⱼ lⱼ j', i⟩ = lᵢ ⟨μ, αᵢ^∨⟩_∘`.
* `algebraMap_frobCoeff`: the coefficients `frobCoeff` in `k`.
* `frobPairBase_comm`: the form `frobPairBase` is symmetric.
* `mem_serreSpan_of_frobPairBase_eq_zero`, `mem_serreSpan_of_frobSplitHom_mem_frobRad`,
  `quasiClassicalHom_eq_zero_of_frobSplitHom_mem_frobRad`: the kernel of `Fr'` modulo the
  radical in weights `ν ≤ n`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 2.2.4, 34.1.2, 35.1.8,
  35.3.2, 35.4.2.
-/

open LieLean LusztigF _root_.LusztigF
open scoped TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop

local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

/-! ### Sign characters of weights -/

section Sign

variable {K I : Type*} [Field K] (D : LusztigCartanDatum I)

lemma coPairing_add (i : I) (μ ν : I →₀ ℕ) :
    D.coPairing i (μ + ν) = D.coPairing i μ + D.coPairing i ν :=
  Finsupp.sum_add_index' (by simp) (fun _ _ _ ↦ by push_cast; ring)

@[simp] lemma coPairing_single (i j : I) (m : ℕ) :
    D.coPairing i (Finsupp.single j m) = m * D.cartanMatrix i j := by
  simp [LusztigCartanDatum.coPairing]

/-- For `q² = 1`, `q^{serreExp i k - 1} = q^{-aᵢₖ}` (also for `k = i`). -/
lemma pow_serreExp_sub_one {q : K} (hq : q ^ 2 = 1) (i k : I) :
    q ^ (serreExp D i k - 1) = q ^ (-D.cartanMatrix i k) := by
  by_cases hik : i = k
  · subst hik
    rw [D.cartanMatrix_self, show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
      hq, inv_one]
    simp [serreExp, D.cartanMatrix_self]
  · have h := D.isGeneralizedCartan_cartanMatrix.offDiag_nonpos i k hik
    have : serreExp D i k - 1 = (-D.cartanMatrix i k).toNat := by simp only [serreExp]; omega
    rw [this, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]

/-- The sign character `μ ↦ ∏ₖ q^{(serreExp i k - 1) μₖ}` is `q^{-⟨μ, αᵢ^∨⟩}` for `q² = 1`. -/
lemma weightSign_pow_serreExp {q : K} (hq : q ^ 2 = 1) (i : I) (μ : I →₀ ℕ) :
    weightSign (fun k ↦ q ^ (serreExp D i k - 1)) μ = q ^ (-D.coPairing i μ) := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  induction μ using Finsupp.induction_linear with
  | zero => simp
  | add μ ν hμ hν => rw [weightSign_add, hμ, hν, coPairing_add, neg_add, zpow_add₀ hq0]
  | single j m =>
    rw [weightSign_single, pow_serreExp_sub_one D hq, coPairing_single, ← zpow_natCast,
      ← zpow_mul]
    congr 1
    ring

end Sign

/-! ### The coefficients and the form -/

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular) (Λ : Dom R)

omit [Finite I] [DecidableEq I] in
/-- `⟨Σⱼ μⱼ lⱼ j', i⟩ = lᵢ ⟨μ, αᵢ^∨⟩_∘` for the Cartan datum `(I, ∘)`. -/
lemma frobRootSum_coroot {l : ℕ} (hl0 : 0 < l) (μ : I →₀ ℕ) (i : I) :
    frobRootSum D R l μ (R.coroot i) = D.frobOrder l i * (D.frobenius hl0).coPairing i μ := by
  induction μ using Finsupp.induction_linear with
  | zero => simp
  | add μ ν hμ hν =>
    rw [frobRootSum_add, AddMonoidHom.add_apply, hμ, hν, coPairing_add, mul_add]
  | single j m =>
    rw [frobRootSum_single, AddMonoidHom.nsmul_apply, R.root_coroot, coPairing_single,
      nsmul_eq_mul]
    push_cast
    linear_combination -(m : ℤ) * D.frobOrder_mul_cartanMatrix_frobenius hl0 i j

/-- `frobPair` is symmetric. -/
lemma frobPair_comm (x y : quotientIntegralForm D) : frobPair hR Λ x y = frobPair hR Λ y x :=
  integralLaurentEval_injective (by
    rw [integralLaurentEval_frobPair, integralLaurentEval_frobPair, IrreducibleModule.form_comm])

/-- `frobPairBase` is symmetric. -/
lemma frobPairBase_comm (k : Type*) [Field k] [Algebra 𝒜 k]
    (X Z : k ⊗[𝒜] quotientIntegralForm D) :
    frobPairBase hR Λ k X Z = frobPairBase hR Λ k Z X :=
  (LinearMap.BilinForm.IsSymm.baseChange (A := k)
    (LinearMap.isSymm_def.2 (frobPair_comm hR Λ))).eq X Z

variable (l : ℕ) in
/-- `nᵢ = ⟨i, λ⟩ / lᵢ`. -/
def frobTop (i : I) : ℕ := (Λ.1 (R.coroot i)).toNat / D.frobOrder l i

section Core

variable {k : Type*} [Field k] [Algebra 𝒜 k] [CharZero k] {l : ℕ} (hl0 : 0 < l)
  (hl : algebraMap 𝒜 k (LaurentPolynomial.T 1) ^ (2 * l) = 1)
  (hprim : ∀ t, 0 < t → t < l → algebraMap 𝒜 k (LaurentPolynomial.T 1) ^ (2 * t) ≠ 1)
  (hA : ∀ i j, i ≠ j → 2 ≤ D.frobOrder l j → ∀ a : ℕ, D.cartanMatrix i j = -a →
    a < D.frobOrder l i)
  (hΛ : ∀ i, 2 ≤ D.frobOrder l i → D.frobOrder l i ∣ (Λ.1 (R.coroot i)).toNat)

set_option quotPrecheck false in
/-- The image `ε` of `v` in `k`. -/
local notation "ε" => algebraMap 𝒜 k (LaurentPolynomial.T 1)

omit [Finite I] [DecidableEq I] in
include hl0 hΛ in
/-- `⟨i, λ⟩ = lᵢ nᵢ`. -/
lemma coroot_eq_frobOrder_mul_frobTop (i : I) :
    Λ.1 (R.coroot i) = D.frobOrder l i * frobTop Λ l i := by
  have h0 : 0 ≤ Λ.1 (R.coroot i) := Λ.2 i
  have hdvd : D.frobOrder l i ∣ (Λ.1 (R.coroot i)).toNat := by
    by_cases h2 : 2 ≤ D.frobOrder l i
    · exact hΛ i h2
    · rw [show D.frobOrder l i = 1 by have := D.frobOrder_pos hl0 i; omega]
      exact one_dvd _
  rw [frobTop, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd, Int.toNat_of_nonneg h0]

omit [Finite I] [DecidableEq I] in
include hl0 hl hprim hΛ in
/-- **The coefficients `frobCoeff` in `k`** ([Lus] 34.1.2 (b)): with `qᵢ = ε^{dᵢ*}`,
`[lᵢ (nᵢ - ⟨μ, αᵢ^∨⟩_∘); lᵢ]ᵢ = qᵢ^{nᵢ + 1} qᵢ^{-⟨μ, αᵢ^∨⟩_∘} (nᵢ - ⟨μ, αᵢ^∨⟩_∘)`. -/
lemma algebraMap_frobCoeff (i : I) (μ : I →₀ ℕ) :
    algebraMap 𝒜 k (frobCoeff Λ l i μ) =
      (ε ^ (D.frobenius hl0).d i) ^ (frobTop Λ l i + 1) *
        (ε ^ (D.frobenius hl0).d i) ^ (-(D.frobenius hl0).coPairing i μ) *
          (((frobTop Λ l i : ℤ) - (D.frobenius hl0).coPairing i μ : ℤ) : k) := by
  have hε : ε ≠ 0 := by
    rintro h
    rw [h, zero_pow (by omega)] at hl
    exact zero_ne_one hl
  set φ := algebraMap 𝒜 k
  set u : kˣ := Units.map φ.toMonoidHom (laurentTUnit (D.d i))
  have hu : (u : k) = ε ^ D.d i := algebraMap_laurentTUnit k (D.d i)
  set a₁ : ℤ := (frobTop Λ l i : ℤ) - (D.frobenius hl0).coPairing i μ
  have harg : (Λ.1 - frobRootSum D R l μ) (R.coroot i) = D.frobOrder l i * a₁ := by
    rw [AddMonoidHom.sub_apply, coroot_eq_frobOrder_mul_frobTop Λ hl0 hΛ, frobRootSum_coroot hl0]
    ring
  rw [frobCoeff, map_gaussBinom, harg, show D.frobOrder l i = D.frobOrder l i * 1 from
      (mul_one _).symm, Nat.cast_mul, Nat.cast_one, mul_one,
    gaussBinom_mul_mul (v := u) (by rw [hu]; exact pow_d_pow_frobOrder D hl0 hl hprim i)
      (by rw [hu]; exact pow_d_pow_ne_one D hl0 hl hprim i) (D.frobOrder_pos hl0 i),
    Ring.choose_one_right, Units.val_zpow_eq_zpow_val, hu, D.frobenius_d hl0]
  have hq0 : ε ^ (D.frobOrder l i ^ 2 * D.d i) ≠ 0 := pow_ne_zero _ hε
  rw [show ((ε ^ D.d i) ^ ((D.frobOrder l i : ℤ) ^ 2 * (a₁ + 1) * ((1 : ℕ) : ℤ))) =
      (ε ^ (D.frobOrder l i ^ 2 * D.d i)) ^ (((frobTop Λ l i + 1 : ℕ) : ℤ) +
        -(D.frobenius hl0).coPairing i μ) by
    rw [← zpow_natCast ε (D.d i), ← zpow_natCast ε (_ * _), ← zpow_mul, ← zpow_mul]
    congr 1
    simp only [a₁]
    push_cast
    ring,
    zpow_add₀ hq0, zpow_natCast]

include hl0 hl hprim hA hΛ in
/-- **The kernel of `Fr'` modulo the form in small weights**: if `y ∈ f_k` has weight `ν`
with `νᵢ ≤ nᵢ` for all `i` and `Fr'(y)` is orthogonal to the elements `Fr'(θ_w)` for the form of
`Λ_λ`, then `y` lies in the span of the quantum Serre products of `(I, ∘)` at the parameters
`ε^{dᵢ*} = ±1`. -/
theorem mem_serreSpan_of_frobPairBase_eq_zero {ν : I →₀ ℕ} (hν : ∀ i, ν i ≤ frobTop Λ l i)
    {y : LusztigF k I} (hy : y ∈ LusztigF.weightSpace k ν)
    (hpair : ∀ w : List I, frobPairBase hR Λ k (frobSplitHom D k l y)
      (frobSplitHom D k l (FreeAlgebra.wordBasis k I w)) = 0) :
    y ∈ serreSpan (D.frobenius hl0) (fun i ↦ ε ^ (D.frobenius hl0).d i) ν := by
  set D' := D.frobenius hl0
  have hε : ε ≠ 0 := by
    rintro h
    rw [h, zero_pow (by omega)] at hl
    exact zero_ne_one hl
  have hq : ∀ i, (ε ^ D'.d i) ^ 2 = 1 := sq_pow_frobenius_d D hl0 hl hprim
  refine mem_serreSpan_of_shapovalovMap_eq_zero_of_sq_eq_one D' hq (fun i j _ ↦ ?_)
    (frobTop Λ l) (c := fun i ↦ algebraMap 𝒜 k ∘ frobCoeff Λ l i)
    (s := fun i ↦ (ε ^ D'.d i) ^ (frobTop Λ l i + 1)) (fun i ↦ pow_ne_zero _ (pow_ne_zero _ hε))
    (fun i μ ↦ ?_) hν hy ?_
  · rw [pow_serreExp_sub_one D' (hq i), pow_serreExp_sub_one D' (hq j), ← zpow_natCast,
      ← zpow_natCast ε (D'.d j), ← zpow_mul, ← zpow_mul]
    congr 1
    have := D'.d_mul_cartanMatrix_comm i j
    linarith
  · rw [Function.comp_apply, algebraMap_frobCoeff Λ hl0 hl hprim hΛ,
      weightSign_pow_serreExp D' (hq i), classicalCoeff]
  · funext w
    obtain ⟨κ, hκ, h⟩ := exists_frobPairBase_eq_vermaForm hR Λ hl0 hl hprim hA hΛ (k := k) w.1 ν
    have h0 := hpair w.1
    rw [frobPairBase_comm, h y hy] at h0
    rw [shapovalovMap_apply, Pi.zero_apply]
    exact (mul_eq_zero.1 h0).resolve_left hκ.ne_zero

include hl0 hl hprim hA hΛ in
/-- **The kernel of `Fr'` modulo the radical in small weights**: if `y ∈ f_k` has weight `ν`
with `νᵢ ≤ nᵢ` for all `i` and `Fr'(y)` lies in the radical of the form of `Λ_λ`, then `y` lies
in the span of the quantum Serre products of `(I, ∘)` at the parameters `ε^{dᵢ*} = ±1`. -/
theorem mem_serreSpan_of_frobSplitHom_mem_frobRad {ν : I →₀ ℕ} (hν : ∀ i, ν i ≤ frobTop Λ l i)
    {y : LusztigF k I} (hy : y ∈ LusztigF.weightSpace k ν)
    (hrad : frobSplitHom D k l y ∈ frobRad hR Λ k) :
    y ∈ serreSpan (D.frobenius hl0) (fun i ↦ ε ^ (D.frobenius hl0).d i) ν :=
  mem_serreSpan_of_frobPairBase_eq_zero hR Λ hl0 hl hprim hA hΛ hν hy fun w ↦ by
    rw [frobRad, LinearMap.mem_ker] at hrad
    rw [hrad, LinearMap.zero_apply]

include hl0 hl hprim hA hΛ in
/-- **`Fr'` is injective modulo the radical in small weights** (towards [Lus] 35.4.2): if
`y ∈ f_k` has weight `ν` with `νᵢ ≤ nᵢ` for all `i` and `Fr'(y)` lies in the radical of the
form of `Λ_λ`, then the image of `y` in `_k f*` (`θᵢ ↦ 1 ⊗ θᵢ` for `(I, ∘)`) is zero. -/
theorem quasiClassicalHom_eq_zero_of_frobSplitHom_mem_frobRad {ν : I →₀ ℕ}
    (hν : ∀ i, ν i ≤ frobTop Λ l i) {y : LusztigF k I} (hy : y ∈ LusztigF.weightSpace k ν)
    (hrad : frobSplitHom D k l y ∈ frobRad hR Λ k) :
    quasiClassicalHom (D.frobenius hl0) k y = 0 :=
  (quasiClassicalHom_eq_zero_iff (D.frobenius hl0) k (sq_pow_frobenius_d D hl0 hl hprim) y).2
    (serreSpan_quasi_le_serreIdeal (D.frobenius hl0) k (sq_pow_frobenius_d D hl0 hl hprim)
      (mem_serreSpan_of_frobSplitHom_mem_frobRad hR Λ hl0 hl hprim hA hΛ hν hy hrad))

end Core

end LieLean.QuantumGroup
