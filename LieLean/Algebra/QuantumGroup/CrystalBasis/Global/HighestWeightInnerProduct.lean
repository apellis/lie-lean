/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorEmbCounit
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorEmbTransfer
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.HighestWeightForm

/-!
# The inner product of `Λ_λ` on the canonical basis

Let `( , )` be the contravariant form of `Λ_λ = L_q(λ)` with `(η, η) = 1` ([Lus] 19.1.2). For
`b, b' ∈ B(λ)`, [Lus] Prop. 19.3.3 states that `(b⁻η, b'⁻η) ∈ v⁻¹ℤ[v⁻¹]` if `b ≠ b'` and
`(b⁻η, b⁻η) ∈ 1 + v⁻¹ℤ[v⁻¹]`.

## Main results

* `formL_hwv_left`: `(η, m)` is the coordinate of `m` at `1 ∈ B(λ)`;
* `rho_qDivPow_F_smul_mem_hwIntegral`: `ρ(Fᵢ^{(n)}) V_ℤ(λ) ⊆ V_ℤ(λ)`, cf. [Lus] 19.3.2;
* `isLaurent_formL`: `(V_ℤ(λ), V_ℤ(λ)) ⊆ 𝒜`, the statement (c) in the proof of [Lus] 19.3.3;
* `formL_hwTransfer`: the form depends only on the pairings `⟨i, λ⟩`;
* `isNegLaurent_formL_evq_sub`: **[Lus] Prop. 19.3.3**.

## Implementation notes

Lusztig deduces 19.3.3 from (c) and Lemma 19.1.4, the almost orthonormality of `B(λ)` modulo
`v⁻¹` in the local ring `A` at `v = ∞`. Here the latter comes from Kashiwara's crystal base
`(L(λ), B(λ))` instead: `b⁻η ∈ L(λ)` is congruent modulo `v⁻¹L(λ)` to an element of `B(λ)`,
and `B(λ)` is orthonormal modulo `v⁻¹` ([HK] Lemma 5.1.6). This uses fundamental weights, so we
prove it for the root datum `freeCoroot R` and transfer the result (our own route). The root
datum is `X`-regular, where Lusztig assumes it `Y`-regular.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 19.1.2, 19.3.2, 19.3.3.
* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.1.
-/

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop LusztigF
open scoped Pointwise

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular)

/-! ### `(η, m)` and integrality over `𝒜` -/

section Laurent

variable (Λ : Dom R)

/-- `(η, m)` is the coordinate of `m` at `1 ∈ B(λ)`. -/
lemma formL_hwv_left (m : IrreducibleModule R 𝕧 Λ.1) :
    formL hvt hR Λ (IrreducibleModule.hwv R 𝕧 Λ.1) m = hwCounit hR Λ m := by
  induction m using hw_induction with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | smul c a ha => rw [map_smul, map_smul, ha]
  | hwv => rw [IrreducibleModule.form_hwv, hwCounit_hwv]
  | F i a _ =>
    have hE : E R 𝕧 i • IrreducibleModule.hwv R 𝕧 Λ.1 = 0 := by
      rw [IrreducibleModule.hwv, ← Submodule.Quotient.mk_smul, VermaModule.E_smul_hwv,
        Submodule.Quotient.mk_zero]
    rw [hwCounit_F_smul, IrreducibleModule.form_comm,
      IrreducibleModule.isContravariant_form hR (pow_ne_one_of_transcendental' hvt), rho_F,
      rhoF, smul_assoc, mul_smul, hE, smul_zero, smul_zero, map_zero]

omit [Finite I] in
lemma rho_pow (x : QuantumGroup R 𝕧) (n : ℕ) : rho R 𝕧 (x ^ n) = rho R 𝕧 x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rho_one]
  | succ n ih => rw [pow_succ, rho_mul, ih, pow_succ']

omit [Finite I] in
lemma E_pow_smul_mem_weightSpace {μ : Y →+ ℤ} {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ weightSpace R 𝕧 _ μ) (i : I) (n : ℕ) :
    E R 𝕧 i ^ n • m ∈ weightSpace R 𝕧 _ (μ + n • R.root i) := by
  induction n with
  | zero => rw [pow_zero, one_smul, zero_smul, add_zero]; exact hm
  | succ n ih =>
    rw [pow_succ', mul_smul, succ_nsmul, ← add_assoc]
    exact E_smul_mem_weightSpace ih i

omit [Finite I] in
lemma exists_KE_pow_smul {μ : Y →+ ℤ} {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ weightSpace R 𝕧 _ μ) (i : I) (n : ℕ) :
    ∃ e : ℤ, (K R 𝕧 (-ktilde R i) * E R 𝕧 i) ^ n • m = 𝕧 ^ e • (E R 𝕧 i ^ n • m) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e + (μ + (n + 1) • R.root i) (-ktilde R i), ?_⟩
    rw [pow_succ', mul_smul, he, smul_comm _ (𝕧 ^ e), mul_smul, ← mul_smul (E R 𝕧 i),
      ← pow_succ', E_pow_smul_mem_weightSpace Λ hm i (n + 1) (-ktilde R i), smul_smul,
      ← zpow_add₀ (NeZero.ne _)]

include hR in
/-- `ρ(Fᵢ^{(n)}) V_ℤ(λ) ⊆ V_ℤ(λ)`: on a weight vector, `ρ(Fᵢ^{(n)}) = vᵢⁿ (K_{-ĩ}Eᵢ)ⁿ/[n]ᵢ!` is a
power of `v` times `Eᵢ^{(n)}` (cf. [Lus] 19.3.2). -/
lemma rho_qDivPow_F_smul_mem_hwIntegral (i : I) (n : ℕ) {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ hwIntegral Λ) :
    rho R 𝕧 (qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i)) • m ∈ hwIntegral Λ := by
  obtain ⟨x, hx, rfl⟩ := hm
  rw [SetLike.mem_coe, ← span_canonicalBasis_laurent] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he⟩ := exists_KE_pow_smul Λ (evq_mem_wsp hR (mem_Uw_cbWt ⟨x, hx⟩) Λ) i n
    have key : rho R 𝕧 (qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i)) • evq hvt Λ x =
        (LaurentPolynomial.T ((D.d i * n : ℕ) + e) : LaurentPolynomial ℤ) •
          (qDivPow (𝕧 ^ D.d i) n (E R 𝕧 i) • evq hvt Λ x) := by
      rw [hw_laurent_smul_eq, integralLaurentEval_T, qDivPow, qDivPow, map_smul, rho_pow, rho_F,
        rhoF, smul_pow, smul_assoc, smul_assoc, he, smul_assoc, smul_smul, smul_smul,
        smul_smul, zpow_add₀ (NeZero.ne _), zpow_natCast, pow_mul]
      ring_nf
    rw [key]
    exact Submodule.smul_mem _ _ (dE_smul_mem_hwIntegral hR Λ i n
      ⟨x, negIntegral_of_mem_canonicalBasis hx, rfl⟩)
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [laurent_smul_eq, map_smul, smul_algebra_smul_comm, ← hw_laurent_smul_eq]
    exact Submodule.smul_mem _ _ hx

include hR in
/-- `ρ(x⁻) V_ℤ(λ) ⊆ V_ℤ(λ)` for `x ∈ 𝒜f`. -/
lemma rho_quotientMinus_smul_mem_hwIntegral {z : Quotient D 𝕧} (hz : z ∈ quotientIntegralForm D)
    {m : IrreducibleModule R 𝕧 Λ.1} (hm : m ∈ hwIntegral Λ) :
    rho R 𝕧 (quotientMinus R z) • m ∈ hwIntegral Λ := by
  induction hz using Algebra.adjoin_induction generalizing m with
  | mem z hz =>
    obtain ⟨i, n, rfl⟩ := hz
    rw [quotientIntegralGenerator, map_qDivPow', quotientMinus_θ]
    exact rho_qDivPow_F_smul_mem_hwIntegral hR Λ i n hm
  | algebraMap c =>
    rw [show algebraMap (LaurentPolynomial ℤ) (Quotient D 𝕧) c =
      algebraMap 𝕂 (Quotient D 𝕧) (integralLaurentEval c) from rfl, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, map_smul, rho_one, smul_assoc, one_smul,
      ← hw_laurent_smul_eq]
    exact Submodule.smul_mem _ _ hm
  | add a b _ _ ha hb => rw [map_add, map_add, add_smul]; exact add_mem (ha hm) (hb hm)
  | mul a b _ _ ha hb => rw [map_mul, rho_mul, mul_smul]; exact hb (ha hm)

include hR in
/-- `(η, m) ∈ 𝒜` for `m ∈ V_ℤ(λ)`. -/
lemma isLaurent_formL_hwv {m : IrreducibleModule R 𝕧 Λ.1} (hm : m ∈ hwIntegral Λ) :
    Modified.IsLaurent (formL hvt hR Λ (IrreducibleModule.hwv R 𝕧 Λ.1) m) := by
  rw [formL_hwv_left, ← repr_canonicalBasisHWBasis_one]
  exact isLaurent_repr_of_mem_hwIntegral hR Λ hm _

include hR in
/-- **`(V_ℤ(λ), V_ℤ(λ)) ⊆ 𝒜`**: the statement (c) in the proof of [Lus] Prop. 19.3.3. -/
theorem isLaurent_formL {x y : IrreducibleModule R 𝕧 Λ.1} (hx : x ∈ hwIntegral Λ)
    (hy : y ∈ hwIntegral Λ) : Modified.IsLaurent (formL hvt hR Λ x y) := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [evq_eq_quotientMinus_smul,
    IrreducibleModule.isContravariant_form hR (pow_ne_one_of_transcendental' hvt)]
  exact isLaurent_formL_hwv hR Λ (rho_quotientMinus_smul_mem_hwIntegral hR Λ hz hy)

end Laurent

/-! ### Almost orthonormality with fundamental weights -/

section Fund

variable (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
  (Λ : Dom R)

local notation "𝔅" => canonicalBasisHWBasis Λ hR

include hfund in
/-- The coordinates of a vector of `v⁻¹L(λ)` lie in `v⁻¹A`. -/
lemma exists_repr_eq_of_mem_smul_lat {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ ϖ • lat hvt hR A Λ) (b : canonicalBasisHW D Λ) :
    ∃ a : A, (𝔅).repr m b = algebraMap A 𝕂 (ϖ * a) := by
  obtain ⟨n, hn, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
  obtain ⟨a, ha⟩ := repr_mem_of_mem_lat hR hfund Λ hn b
  refine ⟨a, ?_⟩
  rw [← algebraMap_smul 𝕂 ϖ n, map_smul, Finsupp.smul_apply, smul_eq_mul, ← ha, map_mul]

include hfund in
lemma notMem_smul_lat_of_repr_eq_one {m : IrreducibleModule R 𝕧 Λ.1} (b : canonicalBasisHW D Λ)
    (hb : (𝔅).repr m b = 1) : m ∉ ϖ • lat hvt hR A Λ := by
  intro hm
  obtain ⟨a, ha⟩ := exists_repr_eq_of_mem_smul_lat hR hfund Λ hm b
  rw [hb, ← map_one (algebraMap A 𝕂)] at ha
  have hu : IsUnit ϖ := IsUnit.of_mul_eq_one a (InfinityLocalRing.injective_algebraMap ha).symm
  exact (IsLocalRing.mem_maximalIdeal _).1 InfinityLocalRing.uniformizer_mem_maximalIdeal hu

omit [Finite I] in
lemma smul_lat_le : ϖ • lat hvt hR A Λ ≤ lat hvt hR A Λ := by
  intro m hm
  obtain ⟨n, hn, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
  exact Submodule.smul_mem _ _ hn

include hfund in
/-- `b⁻η ≡ f̃_w η` modulo `v⁻¹L(λ)` for some word `w`. -/
lemma exists_evq_sub_fW_mem (b : canonicalBasisHW D Λ) :
    ∃ w : List I, evq hvt Λ (b : Um D 𝕧) - fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ := by
  obtain ⟨ν, c, hc⟩ := (mem_canonicalBasis_iff D).1 (canonicalBasisHW_subset D Λ b.2)
  refine ⟨(Quotient.out c).1, ?_⟩
  have hc' : (b : Um D 𝕧) = negGlobal D ν c := by exact hc
  rw [hc', show evq hvt Λ (negGlobal D ν c) - fW hvt hR Λ (Quotient.out c).1 =
      evq hvt Λ (negGlobal D ν c - fWi hvt (Quotient.out c).1) +
        (evq hvt Λ (fWi hvt (Quotient.out c).1) - fW hvt hR Λ (Quotient.out c).1) by
    rw [map_sub]; abel]
  exact add_mem (evq_mem_smul_lat' hfund (negGlobal_sub_mem D ν c) Λ)
    (evq_fWord_sub_fW_mem InfinityLocalRing.injective_algebraMap
      InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
      InfinityLocalRing.exists_pow_mul hfund _ Λ)

open Classical in
include hfund in
/-- `(b⁻η, b'⁻η) ≡ δ_{b,b'}` modulo `v⁻¹A`, with fundamental weights. -/
theorem exists_formL_evq_eq (b b' : canonicalBasisHW D Λ) :
    ∃ a : A, formL hvt hR Λ (evq hvt Λ b) (evq hvt Λ b') =
      (if b = b' then 1 else 0) + algebraMap A 𝕂 (ϖ * a) := by
  have hv' := pow_ne_one_of_transcendental' hvt
  have hL : ∀ w, fW hvt hR Λ w ∈ lat hvt hR A Λ :=
    IrreducibleModule.fWord_mem_lattice hR hv' Λ.2 A
  have hrb : ∀ b₀ : canonicalBasisHW D Λ, (𝔅).repr (evq hvt Λ b₀) b₀ = 1 := fun b₀ ↦ by
    rw [← canonicalBasisHWBasis_apply Λ hR, Module.Basis.repr_self, Finsupp.single_eq_same]
  obtain ⟨w, hw⟩ := exists_evq_sub_fW_mem hR hfund Λ b
  obtain ⟨w', hw'⟩ := exists_evq_sub_fW_mem hR hfund Λ b'
  set d := evq hvt Λ (b : Um D 𝕧) - fW hvt hR Λ w
  set d' := evq hvt Λ (b' : Um D 𝕧) - fW hvt hR Λ w'
  have e : evq hvt Λ (b : Um D 𝕧) = fW hvt hR Λ w + d := by simp only [d]; abel
  have e' : evq hvt Λ (b' : Um D 𝕧) = fW hvt hR Λ w' + d' := by simp only [d']; abel
  have hwL : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ := by
    intro h
    exact notMem_smul_lat_of_repr_eq_one hR hfund Λ b (hrb b) (e ▸ add_mem h hw)
  have hwL' : fW hvt hR Λ w' ∉ ϖ • lat hvt hR A Λ := by
    intro h
    exact notMem_smul_lat_of_repr_eq_one hR hfund Λ b' (hrb b') (e' ▸ add_mem h hw')
  have hiff : (fW hvt hR Λ w - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ) ↔ b = b' := by
    constructor
    · intro h
      by_contra hne
      have h₁ : evq hvt Λ (b : Um D 𝕧) - evq hvt Λ (b' : Um D 𝕧) ∈ ϖ • lat hvt hR A Λ := by
        rw [e, e', show fW hvt hR Λ w + d - (fW hvt hR Λ w' + d') =
          (fW hvt hR Λ w - fW hvt hR Λ w') + (d - d') by abel]
        exact add_mem h (sub_mem hw hw')
      refine notMem_smul_lat_of_repr_eq_one hR hfund Λ b ?_ h₁
      rw [map_sub, Finsupp.sub_apply, hrb, ← canonicalBasisHWBasis_apply Λ hR,
        Module.Basis.repr_self, Finsupp.single_eq_of_ne hne, sub_zero]
    · rintro rfl
      rw [show fW hvt hR Λ w - fW hvt hR Λ w' = d' - d by simp only [d, d']; abel]
      exact sub_mem hw' hw
  obtain ⟨a₀, ha₀⟩ := formL_fW_fW InfinityLocalRing.injective_algebraMap
    InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
    InfinityLocalRing.exists_pow_mul hfund Λ w w' hwL hwL'
  obtain ⟨a₁, ha₁⟩ := formL_mem_smul InfinityLocalRing.injective_algebraMap
    InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
    InfinityLocalRing.exists_pow_mul hfund Λ (hL w) hw'
  obtain ⟨a₂, ha₂⟩ := formL_mem_smul InfinityLocalRing.injective_algebraMap
    InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
    InfinityLocalRing.exists_pow_mul hfund Λ (hL w') hw
  obtain ⟨a₃, ha₃⟩ := formL_mem_smul InfinityLocalRing.injective_algebraMap
    InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
    InfinityLocalRing.exists_pow_mul hfund Λ (smul_lat_le hR Λ hw) hw'
  refine ⟨a₀ + a₁ + a₂ + a₃, ?_⟩
  rw [e, e']
  simp only [map_add, LinearMap.add_apply]
  rw [ha₀, ha₁, ha₃, IrreducibleModule.form_comm hR hv' d, ha₂, if_congr hiff rfl rfl]
  simp only [mul_add, map_add]
  ring

omit [Finite I] [DecidableEq I] in
/-- An element of `𝒜 ∩ v⁻¹A` lies in `v⁻¹ℤ[v⁻¹]`. -/
lemma isNegLaurent_of_isLaurent {c : 𝕂} (hc : Modified.IsLaurent c) (a : A)
    (h : c = algebraMap A 𝕂 (ϖ * a)) : IsNegLaurent c := by
  obtain ⟨f, rfl⟩ := hc
  have ha : algebraMap A 𝕂 a = integralLaurentEval (LaurentPolynomial.T 1 * f) := by
    rw [map_mul, InfinityLocalRing.algebraMap_uniformizer] at h
    rw [map_mul, integralLaurentEval_T, zpow_one, h, ← mul_assoc,
      mul_inv_cancel₀ (NeZero.ne _), one_mul]
  have := isIntInv_of_algebraMap_eq _ a ha
  rwa [IsIntInv, map_mul, integralLaurentEval_T, zpow_one, ← mul_assoc,
    inv_mul_cancel₀ (NeZero.ne _), one_mul] at this

open Classical in
include hfund in
/-- [Lus] Prop. 19.3.3 with fundamental weights. -/
theorem isNegLaurent_formL_evq_sub_of_fund (b b' : canonicalBasisHW D Λ) :
    IsNegLaurent (formL hvt hR Λ (evq hvt Λ b) (evq hvt Λ b') - if b = b' then 1 else 0) := by
  obtain ⟨a, ha⟩ := exists_formL_evq_eq hR hfund Λ b b'
  have hint : ∀ b₀ : canonicalBasisHW D Λ, evq hvt Λ (b₀ : Um D 𝕧) ∈ hwIntegral Λ :=
    fun b₀ ↦ ⟨b₀, negIntegral_of_mem_canonicalBasis (canonicalBasisHW_subset D Λ b₀.2), rfl⟩
  refine isNegLaurent_of_isLaurent ?_ a (by rw [ha]; ring)
  refine (isLaurent_formL hR Λ (hint b) (hint b')).sub ?_
  split_ifs
  · exact Modified.isLaurent_one
  · exact Modified.isLaurent_zero

end Fund

/-! ### Transfer and [Lus] Prop. 19.3.3 -/

section Transfer

variable {Y' : Type*} [AddCommGroup Y'] {R' : D.RootDatum Y'} (hR' : R'.IsXRegular)
  {Λ : Dom R} {Λ' : Dom R'} (h : ∀ i, Λ'.1 (R'.coroot i) = Λ.1 (R.coroot i))

/-- The inner product of `L_q(λ)` depends only on the pairings `⟨i, λ⟩`: `hwTransfer` is an
isometry. -/
lemma formL_hwTransfer (x y : IrreducibleModule R 𝕧 Λ.1) :
    formL hvt hR' Λ' (hwTransfer hR hR' h x) (hwTransfer hR hR' h y) = formL hvt hR Λ x y := by
  obtain ⟨a, rfl⟩ := ev_surjective Λ x
  obtain ⟨b, rfl⟩ := ev_surjective Λ y
  rw [hwTransfer_ev, hwTransfer_ev, ev_apply, ev_apply, ev_apply, ev_apply,
    IrreducibleModule.form_mk, IrreducibleModule.form_mk, ← VermaModule.shapF_apply,
    ← VermaModule.shapF_apply, VermaModule.shapF_eq_shapZ, VermaModule.shapF_eq_shapZ]
  congr 1
  funext i
  simp only [VermaModule.zcoef, h]

end Transfer

variable (Λ : Dom R)

open Classical in
/-- **[Lus] Prop. 19.3.3**: for `b, b' ∈ B(λ)`, `(b⁻η, b'⁻η) - δ_{b,b'} ∈ v⁻¹ℤ[v⁻¹]`, i.e.
(a) `(b⁻η, b'⁻η) ∈ v⁻¹ℤ[v⁻¹]` for `b ≠ b'` and (b) `(b⁻η, b⁻η) ∈ 1 + v⁻¹ℤ[v⁻¹]`.

Lusztig assumes `Y`-regular root data; here the root datum is `X`-regular. The proof (our own
route) transfers `isNegLaurent_formL_evq_sub_of_fund` from the root datum `freeCoroot R`, which
has fundamental weights. -/
theorem isNegLaurent_formL_evq_sub (b b' : canonicalBasisHW D Λ) :
    IsNegLaurent (formL hvt hR Λ (evq hvt Λ b) (evq hvt Λ b') - if b = b' then 1 else 0) := by
  have h := domFreeCoroot_coroot Λ
  have hR₁ := isXRegular_freeCoroot hR
  set e := Set.equivOfEq (canonicalBasisHW_eq h).symm
  have := isNegLaurent_formL_evq_sub_of_fund hR₁ exists_fund_freeCoroot (domFreeCoroot Λ)
    (e b) (e b')
  rw [show ((e b : canonicalBasisHW D (domFreeCoroot Λ)) : Um D 𝕧) = b from
    rfl, show ((e b' : canonicalBasisHW D (domFreeCoroot Λ)) : Um D 𝕧) = b' from rfl,
    ← hwTransfer_evq hR hR₁ h, ← hwTransfer_evq hR hR₁ h, formL_hwTransfer] at this
  convert this using 2
  simp only [e.injective.eq_iff]

end LieLean.QuantumGroup
