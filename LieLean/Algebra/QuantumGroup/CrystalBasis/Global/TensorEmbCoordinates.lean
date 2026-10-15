/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.HighestWeightCoordinates
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorCanonicalBasis
import LieLean.Algebra.QuantumGroup.CrystalBasis.Integral.ScalarResidue
import LieLean.Algebra.QuantumGroup.Modified.TensorVermaIntegral

/-!
# The canonical basis under `Λ_{λ+λ'} → Λ_λ ⊗ Λ_{λ'}`

Let `λ, λ'` be dominant and let `χ : Λ_{λ+λ'} → Λ_λ ⊗ Λ_{λ'}` be the homomorphism of `U`-modules
with `χ(η'') = η ⊗ η'` (`tensorEmb`, [Lus] 25.1.2 (a)). For `b ∈ B` write
`χ(b⁻η'') = Σ f(b; b₁, b₂) b₁⁻η ⊗ b₂⁻η'` (`b₁ ∈ B(λ)`, `b₂ ∈ B(λ')`). [Lus] Prop. 25.1.2 (b)
asserts `f(b; b₁, b₂) ∈ ℤ[v⁻¹]`.

## Main results

* `isIntInv_of_algebraMap_eq`: `𝒜 ∩ A ⊆ ℤ[v⁻¹]` inside `ℚ(v)`, `A` the local ring at `v = ∞`.
* `repr_tensorEmb_evq_mem_range`: the coordinates `f(b; b₁, b₂)` of `χ(x⁻η'')` for
  `x ∈ U⁻_ℤ` lie in `𝒜` (cf. [Lus] 23.2.3).
* `isIntInv_repr_tensorEmb_evq_of_fund`: **[Lus] Prop. 25.1.2 (b)** for root data with
  fundamental weights (an intermediate statement, see below).

## Proof

As in [Lus], the coordinates lie in `𝒜` and in the local ring at `v = ∞`, and these two rings
meet in `ℤ[v⁻¹]`. Lusztig obtains the second property from his lattice `ℒ(Λ_λ)` ([Lus] 18.1.4,
18.1.8). Here we use Kashiwara's lattice instead: `χ` maps `L(λ + λ')` into `L(λ) ⊗ L(λ')`
(`GrandLoop.tensorEmb_mem_LL`, [Jan] 10.9) and the `b⁻η` span `L(λ)` over the local ring
(`repr_mem_of_mem_lat`), which is our own route. The integrality in `𝒜` is the argument of
[Lus] 23.2.3: `V_ℤ(λ + λ')` is generated from `η''` by the divided powers `Fᵢ^{(n)}`, which act on
`Λ_λ ⊗ Λ_{λ'}` by `𝒜`-combinations of `Fᵢ^{(s)} ⊗ Fᵢ^{(t)}`.

Kashiwara's lattice is that of the grand loop, which assumes that the root datum has
fundamental weights (`hfund`). The statement here carries this extra hypothesis, which is not
in [Lus]; `TensorEmbTransfer.lean` removes it (`isIntInv_repr_tensorEmb_evq`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.2.3, 25.1.2.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 10.9.
-/

open scoped RatFunc Pointwise
open TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

/-! ### `𝒜 ∩ A = ℤ[v⁻¹]` -/

section Scalar

open LaurentPolynomial

/-- If `a v⁻ⁿ` is an integer polynomial in `v⁻¹`, then that polynomial is divisible by `Xⁿ`. -/
lemma X_pow_dvd_of_mul_localX_pow (a : Sl2.RankOne.LocalRing) (n : ℕ) (p : Polynomial ℤ)
    (h : a * localX ^ n = integerLocalPolynomial p) : Polynomial.X ^ n ∣ p := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    have hz : p.coeff 0 = 0 := by
      have hh := congrArg residue h
      rw [map_mul, map_pow, residue_localX, zero_pow (Nat.succ_ne_zero n),
        mul_zero, residue_integerLocalPolynomial] at hh
      exact_mod_cast hh.symm
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr hz
    rw [pow_succ']
    refine mul_dvd_mul_left _ (ih q ?_)
    apply mul_right_cancel₀ irreducible_localX.ne_zero
    rw [mul_assoc, ← pow_succ, h, map_mul]
    simp [integerLocalPolynomial, mul_comm]

/-- **`𝒜 ∩ A ⊆ ℤ[v⁻¹]`**: a Laurent integer that is regular at `v = ∞` lies in `ℤ[v⁻¹]`. -/
theorem isIntInv_of_algebraMap_eq (f : LaurentPolynomial ℤ) (a : A)
    (h : algebraMap A 𝕂 a = integralLaurentEval f) : IsIntInv (integralLaurentEval f) := by
  have hb : algebraMap Sl2.RankOne.LocalRing 𝕂 a = integralLaurentEval (invert f) := by
    have hh := congrArg RatFunc.bar h
    change RatFunc.bar (RatFunc.bar (algebraMap Sl2.RankOne.LocalRing 𝕂 a)) = _ at hh
    simpa only [RatFunc.bar_bar, bar_integralLaurentEval] using hh
  obtain ⟨n, p, hp⟩ := exists_T_pow (invert f)
  have hloc : (show Sl2.RankOne.LocalRing from a) * localX ^ n = integerLocalPolynomial p := by
    apply injective_algebraMap_localRing
    rw [map_mul, map_pow, algebraMap_localX, map_integerLocalPolynomial, hp, map_mul,
      integralLaurentEval_T, hb]
    simp
  obtain ⟨q, rfl⟩ := X_pow_dvd_of_mul_localX_pow a n p hloc
  have hq : invert f = Polynomial.toLaurent q := by
    rw [map_mul, Polynomial.toLaurent_X_pow, mul_comm] at hp
    exact ((isUnit_T (n : ℤ)).mul_left_inj).1 hp.symm
  refine ⟨T (-1) * f, fun m hm ↦ ?_, ?_⟩
  · rw [coeff_T_mul, show m - -1 = -(-(m + 1)) by ring, ← invert_apply, hq]
    by_contra hne
    have hmem : -(m + 1) ∈ (Polynomial.toLaurent q).coeff.support := Finsupp.mem_support_iff.2 hne
    rw [support_coeff_toLaurent, Finset.mem_map] at hmem
    obtain ⟨k, -, hk⟩ := hmem
    change (k : ℤ) = -(m + 1) at hk
    omega
  · rw [map_mul, integralLaurentEval_T, zpow_neg_one]

end Scalar

/-! ### `𝒜`-spans and coordinates -/

section LaurentSpan

variable {V ι : Type*} [AddCommGroup V] [Module 𝕂 V] (B : Module.Basis ι 𝕂 V)

/-- If the vectors of `S` have coordinates in `𝒜`, so do the vectors of the `𝒜`-span of `S`. -/
lemma repr_mem_range_of_mem_laurentSpan {S : Set V}
    (hS : ∀ s ∈ S, ∀ i, B.repr s i ∈ (integralLaurentEval : LaurentPolynomial ℤ →+* 𝕂).range)
    {x : V} (hx : x ∈ laurentSpan S) (i : ι) :
    B.repr x i ∈ (integralLaurentEval : LaurentPolynomial ℤ →+* 𝕂).range := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, s, hs, rfl⟩ := hx
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem ⟨LaurentPolynomial.T k, by rw [integralLaurentEval_T]⟩ (hS s hs i)
  | zero => rw [map_zero, Finsupp.zero_apply]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add, Finsupp.add_apply]; exact add_mem ha hb
  | smul c a _ ha => rw [map_zsmul, Finsupp.smul_apply]; exact zsmul_mem ha c

end LaurentSpan

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular)

/-! ### Integrality in `𝒜` -/

section Integral

variable (Λ₁ Λ₂ : Dom R)

/-- The vectors `x ⊗ y` of `Λ_λ ⊗ Λ_{λ'}` with `x ∈ V_ℤ(λ)` and `y ∈ V_ℤ(λ')` a weight vector. -/
def hwIntegralTensor :
    Set (TensorModule 𝕂 (IrreducibleModule R 𝕧 Λ₁.1) (IrreducibleModule R 𝕧 Λ₂.1)) :=
  {z | ∃ x ∈ hwIntegral Λ₁, ∃ (μ : Y →+ ℤ) (y : IrreducibleModule R 𝕧 Λ₂.1),
    y ∈ hwIntegral Λ₂ ∧ y ∈ weightSpace R 𝕧 (IrreducibleModule R 𝕧 Λ₂.1) μ ∧
      z = TensorModule.mk _ _ (x ⊗ₜ[𝕂] y)}

/-- The `𝒜`-span of `hwIntegralTensor` is stable under the `Fᵢ^{(n)}`. -/
lemma qDivPow_F_smul_mem_laurentSpan (i : I) (n : ℕ)
    {z : TensorModule 𝕂 (IrreducibleModule R 𝕧 Λ₁.1) (IrreducibleModule R 𝕧 Λ₂.1)}
    (hz : z ∈ laurentSpan (hwIntegralTensor Λ₁ Λ₂)) :
    qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) • z ∈ laurentSpan (hwIntegralTensor Λ₁ Λ₂) := by
  refine map_mem_laurentSpan (DistribSMul.toLinearMap 𝕂 _ (qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i)))
    ?_ hz
  rintro _ ⟨x, hx, μ, y, hy, hyμ, rfl⟩
  rw [DistribSMul.toLinearMap_apply, TensorModule.qDivPow_F_smul_tmul ratFunc_X_not_root i _ hyμ]
  refine Submodule.sum_mem _ fun p _ ↦
    laurent_smul_mem_laurentSpan (Modified.isLaurent_vd_zpow _ _) ?_
  exact mem_laurentSpan_of_mem ⟨_, dF_smul_mem_hwIntegral Λ₁ i p.1 hx, _, _,
    dF_smul_mem_hwIntegral Λ₂ i p.2 hy, qDivPow_F_smul_mem_weightSpace hyμ i p.2, rfl⟩

/-- `χ(V_ℤ(λ + λ'))` lies in the `𝒜`-span of the `x ⊗ y`, `x ∈ V_ℤ(λ)`, `y ∈ V_ℤ(λ')`. -/
theorem tensorEmb_evq_mem_laurentSpan {x : Um D 𝕧} (hx : x ∈ negIntegral D) :
    tensorEmb hvt hR Λ₁.2 Λ₂.2 (evq hvt (Λ₁ + Λ₂) x) ∈
      laurentSpan (hwIntegralTensor Λ₁ Λ₂) := by
  have h : negativeQuotientEquiv D x ∈ Subalgebra.toSubmodule (quotientIntegralForm D) :=
    (mem_negIntegral D x).1 hx
  rw [quotientIntegralForm, Algebra.adjoin_eq_span] at h
  rw [← (negativeQuotientEquiv D).symm_apply_apply x]
  generalize negativeQuotientEquiv D x = y at h
  induction h using Submodule.span_induction with
  | mem y hy =>
    induction hy using Submonoid.closure_induction_left with
    | one =>
      rw [← map_one (toQuotient D 𝕧), symm_toQuotient, evq_mk, ev_one]
      change tensorEmb hvt hR Λ₁.2 Λ₂.2 (IrreducibleModule.hwv R 𝕧 (Λ₁.1 + Λ₂.1)) ∈ _
      rw [tensorEmb_hwv]
      exact mem_laurentSpan_of_mem ⟨_, hwv_mem_hwIntegral Λ₁, _, _, hwv_mem_hwIntegral Λ₂,
        IrreducibleModule.hwv_mem_weightSpace, rfl⟩
    | mul_left a ha y hy ih =>
      obtain ⟨j, n, rfl⟩ := ha
      obtain ⟨ν, z, -, rfl, -⟩ := exists_homogeneous_of_mem_closure D hy
      rw [symm_toQuotient, evq_mk] at ih
      rw [← toQuotient_qDivPow, ← map_mul, symm_toQuotient, evq_mk, ev_qDivPow_mul (Λ₁ + Λ₂),
        map_smul]
      exact qDivPow_F_smul_mem_laurentSpan Λ₁ Λ₂ j n ih
  | zero => rw [map_zero, map_zero, map_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [map_add, map_add, map_add]; exact add_mem hy hy'
  | smul c y _ hy =>
    have : (negativeQuotientEquiv D).symm (c • y) =
        integralLaurentEval c • (negativeQuotientEquiv D).symm y :=
      map_smul (negativeQuotientEquiv D).symm (integralLaurentEval c) y
    rw [this, map_smul, LinearMap.map_smul_of_tower]
    exact laurent_smul_mem_laurentSpan ⟨c, rfl⟩ hy

/-- **`𝒜`-integrality** ([Lus] 23.2.3 for `Λ_λ ⊗ Λ_{λ'}`): for `x ∈ U⁻_ℤ`, the coordinates of
`χ(x⁻η'')` in the basis `b₁⁻η ⊗ b₂⁻η'` lie in `𝒜`. -/
theorem repr_tensorEmb_evq_mem_range {x : Um D 𝕧} (hx : x ∈ negIntegral D)
    (p : canonicalBasisHW D Λ₁ × canonicalBasisHW D Λ₂) :
    (tensorHWBasis hR Λ₁ Λ₂).repr (tensorEmb hvt hR Λ₁.2 Λ₂.2 (evq hvt (Λ₁ + Λ₂) x)) p ∈
      (integralLaurentEval : LaurentPolynomial ℤ →+* 𝕂).range := by
  refine repr_mem_range_of_mem_laurentSpan _ ?_ (tensorEmb_evq_mem_laurentSpan hR Λ₁ Λ₂ hx) p
  rintro _ ⟨x, hx, μ, y, hy, -, rfl⟩ p
  exact repr_tensorHWBasis_mk_mem hR Λ₁ Λ₂ _ (repr_mem_of_mem_hwIntegral hR Λ₁ hx)
    (repr_mem_of_mem_hwIntegral hR Λ₂ hy) p

end Integral

/-! ### [Lus] Prop. 25.1.2 (b) -/

variable (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
  (Λ₁ Λ₂ : Dom R)

include hfund in
/-- **[Lus] Prop. 25.1.2 (b)**, for root data with fundamental weights: for `b ∈ B`, the
coordinates `f(b; b₁, b₂)` of `χ(b⁻η'')` in the basis `b₁⁻η ⊗ b₂⁻η'` of `Λ_λ ⊗ Λ_{λ'}` lie in
`ℤ[v⁻¹]`.

This is an intermediate statement: Lusztig assumes `Y`-regular root data (here `X`-regular), and
the extra hypothesis `hfund` (fundamental weights) comes from our route through Kashiwara's
lattice. It is removed in `isIntInv_repr_tensorEmb_evq`. -/
theorem isIntInv_repr_tensorEmb_evq_of_fund {x : Um D 𝕧} (hx : x ∈ canonicalBasis D)
    (p : canonicalBasisHW D Λ₁ × canonicalBasisHW D Λ₂) :
    IsIntInv ((tensorHWBasis hR Λ₁ Λ₂).repr
      (tensorEmb hvt hR Λ₁.2 Λ₂.2 (evq hvt (Λ₁ + Λ₂) x)) p) := by
  obtain ⟨ν, b, rfl⟩ := (mem_canonicalBasis_iff D).1 hx
  have hG := negGlobal_mem D ν b
  obtain ⟨f, hf⟩ := repr_tensorEmb_evq_mem_range hR Λ₁ Λ₂ hG.1 p
  have hL : tensorEmb hvt hR Λ₁.2 Λ₂.2 (evq hvt (Λ₁ + Λ₂) (negGlobal D ν b)) ∈
      LL hvt hR A Λ₁ Λ₂ :=
    tensorEmb_mem_LL InfinityLocalRing.uniformizer_mem_maximalIdeal
      InfinityLocalRing.algebraMap_uniformizer
      (fun s ↦ (allProp InfinityLocalRing.injective_algebraMap
        InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
        InfinityLocalRing.exists_pow_mul hfund s).1)
      (evq_mem_lat' hfund hG.2.2.1 (Λ₁ + Λ₂))
  obtain ⟨a, ha⟩ := repr_mem_of_mem_LL hR hfund Λ₁ Λ₂ hL p
  rw [← hf] at ha ⊢
  exact isIntInv_of_algebraMap_eq f a ha

end LieLean.QuantumGroup
