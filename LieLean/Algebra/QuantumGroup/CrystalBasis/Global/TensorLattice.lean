/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorBar
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.HighestWeightIntegral

/-!
# The matrix of `Ψ` on `ʷL_q(λ) ⊗ L_q(λ')`

For dominant `λ, λ'`, the elements `b⁺ξ_{-λ} ⊗ b'⁻η_{λ'}`, `b ∈ B(λ)`, `b' ∈ B(λ')`, form a
basis of `ʷL_q(λ) ⊗ L_q(λ')` ([Lus] 24.3.1). Lusztig writes
`Ψ(b₁⁺ξ_{-λ} ⊗ b₁'⁻η_{λ'}) = Σ ρ_{b₁,b₁';b₂,b₂'} b₂⁺ξ_{-λ} ⊗ b₂'⁻η_{λ'}` and observes that the
coefficients lie in `𝒜 = ℤ[v, v⁻¹]`, that `ρ_{b₁,b₁';b₁,b₁'} = 1`, and that the other
coefficients vanish unless `(b₂, b₂')` is lower than `(b₁, b₁')` ([Lus] 24.3.2). This file proves
these three facts.

## Main definitions

* `tensorBasis`: the basis `b⁺ξ_{-λ} ⊗ b'⁻η_{λ'}` of `ʷL_q(λ) ⊗ L_q(λ')`.
* `cbWt`: the weight `|b|` of an element `b` of the canonical basis `B`.
* `TensorLower`: `(b₂, b₂') ≺ (b₁, b₁')` when `|b₁| = |b₂| + ν`, `|b₁'| = |b₂'| + ν` for some
  `ν ≠ 0`.

## Main results

* `isLaurent_repr_tensorPsi`: the coefficients `ρ` lie in `𝒜`;
* `repr_tensorPsi_self`: `ρ_{b₁,b₁';b₁,b₁'} = 1`;
* `repr_tensorPsi_eq_zero`: `ρ_{b₁,b₁';b₂,b₂'} = 0` unless `(b₂, b₂') = (b₁, b₁')` or
  `(b₂, b₂') ≺ (b₁, b₁')`.

## Implementation notes

The relation `≺` refines Lusztig's partial order of 24.3.1, which only compares the traces
`tr |b|`. Integrality uses [Lus] 24.1.5 (`Modified.quasiRAct_mem_quotTensorLattice`), for which
we identify the `𝒜`-span of the `F_w η` in `L_q(λ)` with the `𝒜`-span of the `b⁻η`,
`b ∈ B(λ)` (`evq_mem_hwLaurentLattice`, `isLaurent_repr_of_mem_hwLaurentLattice`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 24.1.5, 24.3.1–24.3.2.
-/

open scoped RatFunc
open TensorProduct

noncomputable section

universe u

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I : Type u} [Finite I] [DecidableEq I] {D : LusztigCartanDatum I}
  {Y : Type*} [AddCommGroup Y] {R : D.RootDatum Y} (hR : R.IsXRegular)

/-! ### The `𝒜`-form of `L_q(λ)` -/

section Lattice

variable (Λ : Dom R)

/-- The `𝒜`-span of the `F_w η` in `L_q(λ)` (Lusztig's `𝒜Λ_λ`). -/
abbrev hwLaurentLattice : Submodule ℤ (IrreducibleModule R 𝕧 Λ.1) :=
  laurentSpan {m | ∃ w : List (I × ℕ), m = Modified.fPow R w • IrreducibleModule.hwv R 𝕧 Λ.1}

omit [Finite I] in
lemma qDivPow_F_smul_mem_hwLaurentLattice (i : I) (n : ℕ) {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ hwLaurentLattice Λ) :
    qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) • m ∈ hwLaurentLattice Λ := by
  refine map_mem_laurentSpan (DistribSMul.toLinearMap 𝕂 _ (qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i)))
    ?_ hm
  rintro _ ⟨w, rfl⟩
  refine mem_laurentSpan_of_mem ⟨(i, n) :: w, ?_⟩
  rw [DistribSMul.toLinearMap_apply, ← mul_smul, Modified.fPow_cons']

lemma evq_eq_quotientMinus_smul (x : Um D 𝕧) :
    evq hvt Λ x = quotientMinus R (negativeQuotientEquiv D x) • IrreducibleModule.hwv R 𝕧 Λ.1 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [evq_mk, ev_apply, VermaModule.toVerma_apply]
  rfl

/-- The `b⁻η`, `b ∈ 𝒜f`, lie in the `𝒜`-span of the `F_w η`. -/
lemma evq_mem_hwLaurentLattice {x : Um D 𝕧} (hx : x ∈ negIntegral D) :
    evq hvt Λ x ∈ hwLaurentLattice Λ := by
  have key : ∀ z ∈ quotientIntegralForm D, ∀ m ∈ hwLaurentLattice Λ,
      quotientMinus R z • m ∈ hwLaurentLattice Λ := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨i, n, rfl⟩ := hz
      intro m hm
      rw [quotientIntegralGenerator, map_qDivPow', quotientMinus_θ]
      exact qDivPow_F_smul_mem_hwLaurentLattice Λ i n hm
    | algebraMap c =>
      intro m hm
      rw [show algebraMap (LaurentPolynomial ℤ) (Quotient D 𝕧) c =
        algebraMap 𝕂 (Quotient D 𝕧) (integralLaurentEval c) from rfl, AlgHom.commutes,
        algebraMap_smul]
      exact laurent_smul_mem_laurentSpan ⟨c, rfl⟩ hm
    | add a b _ _ ha hb =>
      intro m hm
      rw [map_add, add_smul]
      exact add_mem (ha m hm) (hb m hm)
    | mul a b _ _ ha hb =>
      intro m hm
      rw [map_mul, mul_smul]
      exact ha _ (hb m hm)
  rw [evq_eq_quotientMinus_smul]
  exact key _ hx _ (mem_laurentSpan_of_mem ⟨[], by rw [Modified.fPow_nil, one_smul]⟩)

lemma fPow_smul_hwv_mem_hwIntegral (w : List (I × ℕ)) :
    Modified.fPow R w • IrreducibleModule.hwv R 𝕧 Λ.1 ∈ hwIntegral Λ := by
  induction w with
  | nil => rw [Modified.fPow_nil, one_smul]; exact hwv_mem_hwIntegral Λ
  | cons p w ih =>
    rw [← Modified.fPow_cons', mul_smul]
    exact dF_smul_mem_hwIntegral Λ p.1 p.2 ih

include hR in
/-- The coordinates of an element of `V_ℤ(λ)` in the basis `b⁻η`, `b ∈ B(λ)`, lie in `𝒜`. -/
lemma isLaurent_repr_of_mem_hwIntegral {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ hwIntegral Λ) (b : canonicalBasisHW D Λ) :
    Modified.IsLaurent ((canonicalBasisHWBasis Λ hR).repr m b) := by
  classical
  obtain ⟨x, hx, rfl⟩ := hm
  rw [SetLike.mem_coe, ← span_canonicalBasis_laurent] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    by_cases hx' : x ∈ canonicalBasisHW D Λ
    · rw [show evq hvt Λ x = canonicalBasisHWBasis Λ hR ⟨x, hx'⟩ from
        (canonicalBasisHWBasis_apply Λ hR ⟨x, hx'⟩).symm, Module.Basis.repr_self,
        Finsupp.single_apply]
      split_ifs
      · exact Modified.isLaurent_one
      · exact Modified.isLaurent_zero
    · rw [evq_eq_zero_of_notMem_canonicalBasisHW Λ hR hx hx', map_zero, Finsupp.zero_apply]
      exact Modified.isLaurent_zero
  | zero => rw [map_zero, map_zero, Finsupp.zero_apply]; exact Modified.isLaurent_zero
  | add x y _ _ hx hy =>
    rw [map_add, map_add, Finsupp.add_apply]; exact hx.add hy
  | smul c x _ hx =>
    rw [laurent_smul_eq, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact (Modified.IsLaurent.mul ⟨c, rfl⟩ hx)

include hR in
/-- The coordinates of an element of `𝒜Λ_λ` in the basis `b⁻η`, `b ∈ B(λ)`, lie in `𝒜`. -/
lemma isLaurent_repr_of_mem_hwLaurentLattice {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ hwLaurentLattice Λ) (b : canonicalBasisHW D Λ) :
    Modified.IsLaurent ((canonicalBasisHWBasis Λ hR).repr m b) := by
  change m ∈ Submodule.span ℤ _ at hm
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨k, _, ⟨w, rfl⟩, rfl⟩ := hm
    rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact (Modified.isLaurent_zpow k).mul
      (isLaurent_repr_of_mem_hwIntegral hR Λ (fPow_smul_hwv_mem_hwIntegral Λ w) b)
  | zero => rw [map_zero, Finsupp.zero_apply]; exact Modified.isLaurent_zero
  | add x y _ _ hx hy => rw [map_add, Finsupp.add_apply]; exact hx.add hy
  | smul c x _ hx =>
    rw [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]
    exact (Modified.IsLaurent.mul ⟨c, by simp⟩ hx)

end Lattice

/-! ### The basis `b⁺ξ_{-λ} ⊗ b'⁻η_{λ'}` -/

section Basis

variable (Λ Λ' : Dom R)

/-- The basis `b⁺ξ_{-λ} ⊗ b'⁻η_{λ'}`, `b ∈ B(λ)`, `b' ∈ B(λ')`, of `ʷL_q(λ) ⊗ L_q(λ')`
([Lus] 24.3.1). Here `b⁺ξ_{-λ}` is `b⁻η_λ` viewed in the twist `ʷL_q(λ)`. -/
def tensorBasis : Module.Basis (canonicalBasisHW D Λ × canonicalBasisHW D Λ') 𝕂
    (TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) :=
  ((canonicalBasisHWBasis Λ hR).map (ChevalleyTwist.toTwist R 𝕧 _)).tensorProduct
    (canonicalBasisHWBasis Λ' hR)

lemma tensorBasis_apply (h : canonicalBasisHW D Λ × canonicalBasisHW D Λ') :
    tensorBasis hR Λ Λ' h =
      ChevalleyTwist.toTwist R 𝕧 _ (evq hvt Λ h.1) ⊗ₜ[𝕂] evq hvt Λ' h.2 := by
  rw [tensorBasis, Module.Basis.tensorProduct_apply', Module.Basis.map_apply,
    canonicalBasisHWBasis_apply, canonicalBasisHWBasis_apply]

lemma tensorBasis_repr_tmul (m : IrreducibleModule R 𝕧 Λ.1) (m' : IrreducibleModule R 𝕧 Λ'.1)
    (h : canonicalBasisHW D Λ × canonicalBasisHW D Λ') :
    (tensorBasis hR Λ Λ').repr (ChevalleyTwist.toTwist R 𝕧 _ m ⊗ₜ[𝕂] m') h =
      (canonicalBasisHWBasis Λ' hR).repr m' h.2 * (canonicalBasisHWBasis Λ hR).repr m h.1 := by
  rw [tensorBasis, ← Prod.mk.eta (p := h), Module.Basis.tensorProduct_repr_tmul_apply,
    Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, smul_eq_mul]

/-- The coordinates of an element of `ʷ(𝒜Λ_λ) ⊗ 𝒜Λ_{λ'}` lie in `𝒜`. -/
lemma isLaurent_repr_of_mem_quotTensorLattice
    {z : TensorModule 𝕂 (TwL Λ) (IrreducibleModule R 𝕧 Λ'.1)}
    (hz : z ∈ Modified.quotTensorLattice R (VermaModule.maxSubmodule R 𝕧 Λ.1)
      (VermaModule.maxSubmodule R 𝕧 Λ'.1))
    (h : canonicalBasisHW D Λ × canonicalBasisHW D Λ') :
    Modified.IsLaurent ((tensorBasis hR Λ Λ').repr ((TensorModule.mk _ _).symm z) h) := by
  change z ∈ Submodule.span ℤ _ at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, _, ⟨w, w', rfl⟩, rfl⟩ := hz
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
    refine (Modified.isLaurent_zpow k).mul ?_
    change Modified.IsLaurent ((tensorBasis hR Λ Λ').repr
      (ChevalleyTwist.toTwist R 𝕧 _ (Modified.fPow R w • IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
        (Modified.fPow R w' • IrreducibleModule.hwv R 𝕧 Λ'.1)) h)
    rw [tensorBasis_repr_tmul]
    exact (isLaurent_repr_of_mem_hwIntegral hR Λ' (fPow_smul_hwv_mem_hwIntegral Λ' w') _).mul
      (isLaurent_repr_of_mem_hwIntegral hR Λ (fPow_smul_hwv_mem_hwIntegral Λ w) _)
  | zero => rw [map_zero, map_zero, Finsupp.zero_apply]; exact Modified.isLaurent_zero
  | add x y _ _ hx hy => rw [map_add, map_add, Finsupp.add_apply]; exact hx.add hy
  | smul c x _ hx =>
    rw [map_zsmul, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]
    exact (Modified.IsLaurent.mul ⟨c, by simp⟩ hx)

end Basis

/-! ### Weights of the basis vectors -/

section Weight

variable (D) in
/-- The weight `|b|` of an element `b` of the canonical basis `B` of `f`. -/
def cbWt (b : canonicalBasis D) : I →₀ ℕ := ((mem_canonicalBasis_iff D).1 b.2).choose

lemma mem_Uw_cbWt (b : canonicalBasis D) : (b : Um D 𝕧) ∈ Uw D 𝕧 (cbWt D b) := by
  obtain ⟨b', hb'⟩ := ((mem_canonicalBasis_iff D).1 b.2).choose_spec
  rw [hb']
  exact (negGlobal_mem D _ b').2.1

lemma negIntegral_of_mem_canonicalBasis {x : Um D 𝕧} (hx : x ∈ canonicalBasis D) :
    x ∈ negIntegral D := by
  obtain ⟨ν, b, rfl⟩ := (mem_canonicalBasis_iff D).1 hx
  exact (negGlobal_mem D ν b).1

lemma negBar_of_mem_canonicalBasis {x : Um D 𝕧} (hx : x ∈ canonicalBasis D) : negBar D x = x := by
  obtain ⟨ν, b, rfl⟩ := (mem_canonicalBasis_iff D).1 hx
  exact negBar_negGlobal D ν b

variable (Λ : Dom R)

/-- The weight `|b|` of `b ∈ B(λ)`. -/
abbrev hwbWt (b : canonicalBasisHW D Λ) : I →₀ ℕ :=
  cbWt D ⟨b, canonicalBasisHW_subset D Λ b.2⟩

include hR in
lemma evq_mem_hwWt (b : canonicalBasisHW D Λ) : evq hvt Λ b ∈ hwWt Λ (hwbWt Λ b) :=
  evq_mem_wsp hR (mem_Uw_cbWt _) Λ

lemma hwBar_evq_canonicalBasisHW (b : canonicalBasisHW D Λ) :
    hwBar hR Λ (evq hvt Λ b) = evq hvt Λ b := by
  rw [hwBar_evq, negBar_of_mem_canonicalBasis (canonicalBasisHW_subset D Λ b.2)]

/-- The coordinates of a vector of weight `λ - μ` vanish at the `b⁻η` with `|b| ≠ μ`. -/
lemma repr_eq_zero_of_mem_hwWt {μ : I →₀ ℕ} {m : IrreducibleModule R 𝕧 Λ.1}
    (hm : m ∈ hwWt Λ μ) (b : canonicalBasisHW D Λ) (hb : hwbWt Λ b ≠ μ) :
    (canonicalBasisHWBasis Λ hR).repr m b = 0 := by
  classical
  set B := canonicalBasisHWBasis Λ hR
  set P := weightSetProj (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ)
    {Λ.1 - R.rootSum μ}
  have hiff : ∀ ν : I →₀ ℕ, Λ.1 - R.rootSum ν ∈ ({Λ.1 - R.rootSum μ} : Set (Y →+ ℤ)) ↔
      ν = μ := fun ν ↦ by
    rw [Set.mem_singleton_iff]
    exact ⟨fun h ↦ LusztigCartanDatum.RootDatum.rootSum_injective hR (sub_right_injective h),
      fun h ↦ by rw [h]⟩
  have hφ : B.coord b ∘ₗ P = 0 := B.ext fun b' ↦ by
    rw [LinearMap.comp_apply, canonicalBasisHWBasis_apply,
      weightSetProj_of_mem _ _ _ (evq_mem_hwWt hR Λ b'), LinearMap.zero_apply]
    split_ifs with h
    · rw [← canonicalBasisHWBasis_apply Λ hR, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply, ite_eq_right_iff]
      rintro rfl
      exact absurd ((hiff _).1 h) hb
    · rw [map_zero]
  have := LinearMap.congr_fun hφ m
  rwa [LinearMap.comp_apply, weightSetProj_of_mem _ _ _ hm,
    ite_eq_left_iff.2 fun h ↦ absurd (Set.mem_singleton _) h, LinearMap.zero_apply,
    Module.Basis.coord_apply] at this

end Weight

/-! ### The matrix of `Ψ` -/

section Matrix

variable (Λ Λ' : Dom R)

/-- `(b₂, b₂') ≺ (b₁, b₁')`: `|b₁| = |b₂| + ν` and `|b₁'| = |b₂'| + ν` for some `ν ≠ 0`. This
refines Lusztig's order of [Lus] 24.3.1. -/
def TensorLower (h₂ h₁ : canonicalBasisHW D Λ × canonicalBasisHW D Λ') : Prop :=
  ∃ ν : I →₀ ℕ, ν ≠ 0 ∧ hwbWt Λ h₁.1 = hwbWt Λ h₂.1 + ν ∧ hwbWt Λ' h₁.2 = hwbWt Λ' h₂.2 + ν

omit [Finite I] in
lemma tmul_mem_quotTensorLattice {m : IrreducibleModule R 𝕧 Λ.1} (hm : m ∈ hwLaurentLattice Λ)
    {m' : IrreducibleModule R 𝕧 Λ'.1} (hm' : m' ∈ hwLaurentLattice Λ') :
    TensorModule.mk (TwL Λ) (IrreducibleModule R 𝕧 Λ'.1)
        (ChevalleyTwist.toTwist R 𝕧 _ m ⊗ₜ[𝕂] m') ∈
      Modified.quotTensorLattice R (VermaModule.maxSubmodule R 𝕧 Λ.1)
        (VermaModule.maxSubmodule R 𝕧 Λ'.1) := by
  unfold Modified.quotTensorLattice
  refine map_mem_laurentSpan ((TensorModule.mk _ _).toLinearMap ∘ₗ
    (TensorProduct.mk 𝕂 (TwL Λ) _).flip m' ∘ₗ (ChevalleyTwist.toTwist R 𝕧 _).toLinearMap) ?_ hm
  rintro _ ⟨w, rfl⟩
  refine map_mem_laurentSpan ((TensorModule.mk _ _).toLinearMap ∘ₗ TensorProduct.mk 𝕂 (TwL Λ) _
    (ChevalleyTwist.toTwist R 𝕧 _ (Modified.fPow R w • IrreducibleModule.hwv R 𝕧 Λ.1))) ?_ hm'
  rintro _ ⟨w', rfl⟩
  exact mem_laurentSpan_of_mem ⟨w, w', rfl⟩

lemma tensorBasis_mem_tensorWt (h : canonicalBasisHW D Λ × canonicalBasisHW D Λ') :
    tensorBasis hR Λ Λ' h ∈ tensorWt Λ Λ' (hwbWt Λ h.1) (hwbWt Λ' h.2) := by
  rw [tensorBasis_apply]
  exact tmul_mem_tensorWt Λ Λ' (evq_mem_hwWt hR Λ _) (evq_mem_hwWt hR Λ' _)

lemma barPair_tensorBasis (h : canonicalBasisHW D Λ × canonicalBasisHW D Λ') :
    barPair (twBar hR Λ) (hwBar hR Λ').toAddMonoidHom (twBar_smul_U hR Λ)
      (hwBar_smul_U' hR Λ') (tensorBasis hR Λ Λ' h) = tensorBasis hR Λ Λ' h := by
  rw [tensorBasis_apply, barPair_tmul, twBar_toTwist]
  change ChevalleyTwist.toTwist R 𝕧 _ (hwBar hR Λ (evq hvt Λ h.1)) ⊗ₜ[𝕂]
    hwBar hR Λ' (evq hvt Λ' h.2) = _
  rw [hwBar_evq_canonicalBasisHW, hwBar_evq_canonicalBasisHW]

/-- The coordinates of a vector of `(ʷL_q(λ))_{-λ+μ} ⊗ L_q(λ')_{λ'-μ'}` vanish outside the
`(b, b')` with `|b| = μ`, `|b'| = μ'`. -/
lemma repr_eq_zero_of_mem_tensorWt {μ μ' : I →₀ ℕ} {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1}
    (hz : z ∈ tensorWt Λ Λ' μ μ') (h : canonicalBasisHW D Λ × canonicalBasisHW D Λ')
    (hh : ¬ (hwbWt Λ h.1 = μ ∧ hwbWt Λ' h.2 = μ')) : (tensorBasis hR Λ Λ').repr z h = 0 := by
  obtain ⟨t, rfl⟩ := hz
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, Finsupp.add_apply, ha, hb, add_zero]
  | tmul m m' =>
    simp only [TensorProduct.map_tmul, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, LinearEquiv.coe_coe]
    rw [tensorBasis_repr_tmul]
    rcases not_and_or.1 hh with hh | hh
    · rw [repr_eq_zero_of_mem_hwWt hR Λ m.2 _ hh, mul_zero]
    · rw [repr_eq_zero_of_mem_hwWt hR Λ' m'.2 _ hh, zero_mul]

lemma repr_tensorPsi_tensorBasis (h₁ h₂ : canonicalBasisHW D Λ × canonicalBasisHW D Λ') :
    (tensorBasis hR Λ Λ').repr (tensorPsi hR Λ Λ' (tensorBasis hR Λ Λ' h₁)) h₂ =
      ∑ᶠ ν, (tensorBasis hR Λ Λ').repr (TensorModule.actPair R 𝕧 (TwL Λ)
        (IrreducibleModule R 𝕧 Λ'.1) (quasiR R ν) (tensorBasis hR Λ Λ' h₁)) h₂ := by
  rw [tensorPsi_apply, barPair_tensorBasis]
  exact ((Finsupp.lapply h₂ ∘ₗ (tensorBasis hR Λ Λ').repr.toLinearMap).toAddMonoidHom).map_finsum
    (support_quasiR_finite (isPlusLocallyNilpotent_hw Λ') _)

lemma repr_actPair_quasiR_eq_zero {ν : I →₀ ℕ} (hν : ν ≠ 0)
    (h₁ h₂ : canonicalBasisHW D Λ × canonicalBasisHW D Λ') (hl : ¬ TensorLower Λ Λ' h₂ h₁) :
    (tensorBasis hR Λ Λ').repr (TensorModule.actPair R 𝕧 (TwL Λ)
      (IrreducibleModule R 𝕧 Λ'.1) (quasiR R ν) (tensorBasis hR Λ Λ' h₁)) h₂ = 0 := by
  by_cases hle : ν ≤ hwbWt Λ h₁.1 ∧ ν ≤ hwbWt Λ' h₁.2
  · refine repr_eq_zero_of_mem_tensorWt hR Λ Λ'
      (actPair_quasiR_mem_tensorWt Λ Λ' hle.1 hle.2 (tensorBasis_mem_tensorWt hR Λ Λ' h₁)) h₂ ?_
    rintro ⟨e₁, e₂⟩
    exact hl ⟨ν, hν, by rw [e₁, tsub_add_cancel_of_le hle.1],
      by rw [e₂, tsub_add_cancel_of_le hle.2]⟩
  · rw [actPair_quasiR_eq_zero hR Λ Λ' hle (tensorBasis_mem_tensorWt hR Λ Λ' h₁), map_zero,
      Finsupp.zero_apply]

/-- **[Lus] 24.3.2**: `ρ_{b₁,b₁';b₁,b₁'} = 1`. -/
theorem repr_tensorPsi_self (h : canonicalBasisHW D Λ × canonicalBasisHW D Λ') :
    (tensorBasis hR Λ Λ').repr (tensorPsi hR Λ Λ' (tensorBasis hR Λ Λ' h)) h = 1 := by
  rw [repr_tensorPsi_tensorBasis, finsum_eq_single _ 0]
  · rw [quasiR_zero, map_one, Module.End.one_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same]
  · intro ν hν
    refine repr_actPair_quasiR_eq_zero hR Λ Λ' hν h h ?_
    rintro ⟨ν', hν', e₁, -⟩
    exact hν' (by simpa using e₁)

/-- **[Lus] 24.3.2**: `ρ_{b₁,b₁';b₂,b₂'} = 0` unless `(b₂, b₂') = (b₁, b₁')` or
`(b₂, b₂') ≺ (b₁, b₁')`. -/
theorem repr_tensorPsi_eq_zero {h₁ h₂ : canonicalBasisHW D Λ × canonicalBasisHW D Λ'}
    (hne : h₂ ≠ h₁) (hl : ¬ TensorLower Λ Λ' h₂ h₁) :
    (tensorBasis hR Λ Λ').repr (tensorPsi hR Λ Λ' (tensorBasis hR Λ Λ' h₁)) h₂ = 0 := by
  classical
  rw [repr_tensorPsi_tensorBasis]
  refine finsum_eq_zero_of_forall_eq_zero fun ν ↦ ?_
  by_cases hν : ν = 0
  · rw [hν, quasiR_zero, map_one, Module.End.one_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne hne]
  · exact repr_actPair_quasiR_eq_zero hR Λ Λ' hν h₁ h₂ hl

/-- **[Lus] 24.3.2**: the coefficients `ρ_{b₁,b₁';b₂,b₂'}` lie in `𝒜`. -/
theorem isLaurent_repr_tensorPsi (h₁ h₂ : canonicalBasisHW D Λ × canonicalBasisHW D Λ') :
    Modified.IsLaurent
      ((tensorBasis hR Λ Λ').repr (tensorPsi hR Λ Λ' (tensorBasis hR Λ Λ' h₁)) h₂) := by
  rw [tensorPsi_apply, barPair_tensorBasis]
  have hmem := tmul_mem_quotTensorLattice Λ Λ'
    (evq_mem_hwLaurentLattice Λ (negIntegral_of_mem_canonicalBasis
      (canonicalBasisHW_subset D Λ h₁.1.2)))
    (evq_mem_hwLaurentLattice Λ' (negIntegral_of_mem_canonicalBasis
      (canonicalBasisHW_subset D Λ' h₁.2.2)))
  have := isLaurent_repr_of_mem_quotTensorLattice hR Λ Λ'
    (Modified.quasiRAct_mem_quotTensorLattice _ _ hmem) h₂
  rwa [tensorBasis_apply]

end Matrix

end LieLean.QuantumGroup
