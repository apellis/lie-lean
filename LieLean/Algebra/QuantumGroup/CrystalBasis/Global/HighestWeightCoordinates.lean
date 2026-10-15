/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.CanonicalHighestWeight

/-!
# Coordinates in the canonical basis of `Λ_λ`

Coordinates of vectors of `Λ_λ = L_q(λ)` in the canonical basis `{b⁻η | b ∈ B(λ)}`
(`canonicalBasisHWBasis`, [Lus] 14.4.12), and of vectors of `Λ_λ ⊗ Λ_{λ'}` in the product basis.

## Main results

* `repr_mem_of_mem_lat`: the vectors of Kashiwara's lattice `L(λ)` (at `v = ∞`) have coordinates
  in the local ring at `v = ∞`, i.e. the `b⁻η` span `L(λ)` over this ring.
* `repr_mem_of_mem_hwIntegral`: the vectors of `V_ℤ(λ) = U⁻_ℤ η` have coordinates in `𝒜`.
* `tensorHWBasis`: the basis `b₁⁻η ⊗ b₂⁻η'` of `Λ_λ ⊗ Λ_{λ'}`, and `repr_mem_of_mem_LL`: the
  vectors of `L(λ) ⊗ L(λ')` have coordinates in the local ring at `v = ∞`.

These are the inputs for [Lus] 25.1.2 (b). Lusztig's lattice `ℒ(Λ_λ)` is the `ℤ[v⁻¹]`-span of the
canonical basis ([Lus] 18.1.8); here the corresponding statements are deduced from Kashiwara's
global basis theory ([Kas91] (G.1), (G.2)) instead of [Lus] Ch. 18 (our own route).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 14.4.11, 18.1.8.
* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), §7.
-/

open scoped RatFunc Pointwise
open TensorProduct

noncomputable section

universe u

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

/-! ### Coordinates of spans -/

section Span

variable {S M ι : Type*} [CommRing S] [AddCommGroup M] [Module 𝕂 M] [Module S M]
  (f : S →+* 𝕂) (hsmul : ∀ (c : S) (m : M), c • m = f c • m) (B : Module.Basis ι 𝕂 M)
include hsmul

/-- If the vectors of `s` have coordinates in `f(S)`, so do the vectors of the `S`-span of `s`. -/
lemma repr_mem_range_of_mem_span {s : Set M} (hs : ∀ m ∈ s, ∀ i, B.repr m i ∈ f.range) {m : M}
    (hm : m ∈ Submodule.span S s) (i : ι) : B.repr m i ∈ f.range := by
  induction hm using Submodule.span_induction with
  | mem m hm => exact hs m hm i
  | zero => rw [map_zero, Finsupp.zero_apply]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add, Finsupp.add_apply]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [hsmul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem ⟨c, rfl⟩ ha

end Span

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular)

/-! ### The canonical basis of `Λ_λ` -/

section HighestWeight

variable (Λ : Dom R)

local notation "𝔅" => canonicalBasisHWBasis Λ hR

/-- For `x ∈ B`, the coordinates of `x⁻η` are `0` or `1`. -/
lemma repr_evq_mem {x : Um D 𝕧} (hx : x ∈ canonicalBasis D) (S : Subring 𝕂)
    (b : canonicalBasisHW D Λ) : (𝔅).repr (evq hvt Λ x) b ∈ S := by
  classical
  by_cases hx' : x ∈ canonicalBasisHW D Λ
  · have he : evq hvt Λ x = 𝔅 ⟨x, hx'⟩ := (canonicalBasisHWBasis_apply Λ hR ⟨x, hx'⟩).symm
    rw [he, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem S
    · exact zero_mem S
  · rw [evq_eq_zero_of_notMem_canonicalBasisHW Λ hR hx hx', map_zero, Finsupp.zero_apply]
    exact zero_mem S

/-- The vectors of the `S`-span of `{b⁻η | b ∈ B}` have coordinates in `f(S)`. -/
lemma repr_mem_of_mem_span_evq {S : Type*} [CommRing S] [Module S (IrreducibleModule R 𝕧 Λ.1)]
    (f : S →+* 𝕂) (hsmul : ∀ (c : S) (m : IrreducibleModule R 𝕧 Λ.1), c • m = f c • m)
    {m : IrreducibleModule R 𝕧 Λ.1} (hm : m ∈ Submodule.span S (evq hvt Λ '' canonicalBasis D))
    (b : canonicalBasisHW D Λ) : (𝔅).repr m b ∈ f.range :=
  repr_mem_range_of_mem_span f hsmul 𝔅 (by
    rintro _ ⟨x, hx, rfl⟩ b
    exact repr_evq_mem hR Λ hx _ b) hm b

/-- **`𝒜`-coordinates**: `V_ℤ(λ) = U⁻_ℤ η` is contained in the `𝒜`-span of the canonical basis,
so its vectors have coordinates in `𝒜` ([Lus] 14.4.11, [Kas91] (7.3.4)). -/
theorem repr_mem_of_mem_hwIntegral {m : IrreducibleModule R 𝕧 Λ.1} (hm : m ∈ hwIntegral Λ)
    (b : canonicalBasisHW D Λ) :
    (𝔅).repr m b ∈ (integralLaurentEval : LaurentPolynomial ℤ →+* 𝕂).range := by
  obtain ⟨x, hx, rfl⟩ := hm
  rw [← span_canonicalBasis_laurent] at hx
  refine repr_mem_of_mem_span_evq hR Λ integralLaurentEval (hw_laurent_smul_eq Λ) ?_ b
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a c _ _ ha hc => rw [map_add]; exact add_mem ha hc
  | smul c a _ ha =>
    rw [laurent_smul_eq, map_smul, ← hw_laurent_smul_eq]
    exact Submodule.smul_mem _ c ha

end HighestWeight

/-! ### Coordinates of the crystal lattice

Here the root datum has fundamental weights, as in Kashiwara's grand loop which defines `L(λ)`. -/

variable (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)

section Lattice

variable (Λ : Dom R)

local notation "𝔅" => canonicalBasisHWBasis Λ hR

include hfund in
/-- `L(λ)_{λ-ν}` is spanned over the local ring at `v = ∞` by the `G(b)η`, `b ∈ B(∞)_ν`: their
residues are those of the `f̃_w η` (Nakayama's lemma). -/
theorem lat_inf_wsp_le_span (ν : I →₀ ℕ) :
    lat hvt hR A Λ ⊓ (wsp Λ ν).restrictScalars A ≤
      Submodule.span A (Set.range fun b : negCrystal D ν ↦ evq hvt Λ (negGlobal D ν b)) := by
  have hv' := pow_ne_one_of_transcendental' transcendental_ratFunc_X
  set M : Submodule A (IrreducibleModule R 𝕧 Λ.1) := lat hvt hR A Λ ⊓ (wsp Λ ν).restrictScalars A
  set N := Submodule.span A (Set.range fun b : negCrystal D ν ↦ evq hvt Λ (negGlobal D ν b))
  have hMfg : M.FG := by
    have := (wtN_fg Λ (Λ.1 - R.rootSum ν) :
      (wtN hvt hR A Λ (Λ.1 - R.rootSum ν)).FG).map
      (lat hvt hR A Λ).subtype
    convert this using 1
    ext y
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map,
      Submodule.subtype_apply, M]
    constructor
    · rintro ⟨hy, hyw⟩; exact ⟨⟨y, hy⟩, (mem_wtN).2 hyw, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, (mem_wtN).1 hy⟩
  have hϖ0 : algebraMap A 𝕂 ϖ ≠ 0 := by
    rw [InfinityLocalRing.algebraMap_uniformizer]; exact inv_ne_zero (NeZero.ne 𝕧)
  have hle : M ≤ N ⊔ Ideal.span {ϖ} • M := by
    intro y ⟨hy, hyw⟩
    have key : ∀ z ∈ lat hvt hR A Λ, weightSetProj hv' (isInt hvt hR Λ) {Λ.1 - R.rootSum ν} z ∈
        Submodule.span A (fW hvt hR Λ '' {w | wordWeight w = ν}) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨w, rfl⟩ := hz
        rw [weightSetProj_fW]
        · split_ifs with h
          · exact Submodule.subset_span ⟨w, h, rfl⟩
          · exact zero_mem _
        · exact transcendental_ratFunc_X
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul c a _ ha =>
        rw [← algebraMap_smul 𝕂 c a, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ c ha
    have hP : weightSetProj hv' (isInt hvt hR Λ) {Λ.1 - R.rootSum ν} y = y := by
      rw [weightSetProj_of_mem _ _ _ hyw]; simp
    have hy' := key y hy
    rw [hP] at hy'
    refine (Submodule.span_le.2 ?_) hy'
    rintro _ ⟨w, hw, rfl⟩
    set b : negCrystal D ν := Quotient.mk _ ⟨w, hw⟩
    have hout : fWi (D := D) hvt (Quotient.out b).1 - fWi hvt w ∈ ϖ • latInf (D := D) hvt A :=
      Quotient.mk_out (s := negCrystalSetoid D ν) ⟨w, hw⟩
    have hd : fW hvt hR Λ w - evq hvt Λ (negGlobal D ν b) ∈ ϖ • lat hvt hR A Λ := by
      have e : fW hvt hR Λ w - evq hvt Λ (negGlobal D ν b) =
          -(evq hvt Λ (fWi hvt w) - fW hvt hR Λ w) -
            evq hvt Λ ((negGlobal D ν b - fWi hvt (Quotient.out b).1) +
              (fWi hvt (Quotient.out b).1 - fWi hvt w)) := by
        rw [map_add, map_sub, map_sub]; abel
      rw [e]
      refine sub_mem (neg_mem (evq_fWord_sub_fW_mem InfinityLocalRing.injective_algebraMap
        InfinityLocalRing.uniformizer_mem_maximalIdeal InfinityLocalRing.algebraMap_uniformizer
        InfinityLocalRing.exists_pow_mul hfund w Λ)) ?_
      exact evq_mem_smul_lat' hfund (add_mem (negGlobal_sub_mem D ν b) hout) Λ
    have hdw : fW hvt hR Λ w - evq hvt Λ (negGlobal D ν b) ∈ wsp Λ ν :=
      sub_mem (hw ▸ fW_mem_wsp hvt hR Λ w) (evq_mem_wsp hR (negGlobal_mem D ν b).2.1 Λ)
    obtain ⟨z₀, hz₀, hz₀w, hz⟩ := TensorModule.exists_smul_weight hϖ0 hd hdw
    have e : fW hvt hR Λ w = evq hvt Λ (negGlobal D ν b) + ϖ • z₀ := by rw [← hz]; abel
    rw [e]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨b, rfl⟩))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ)
        ⟨hz₀, hz₀w⟩))
  have hjac : Ideal.span {ϖ} ≤ Ideal.jacobson (⊥ : Ideal A) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le,
      Set.singleton_subset_iff]
    exact InfinityLocalRing.uniformizer_mem_maximalIdeal
  exact Submodule.le_of_le_smul_of_le_jacobson_bot hMfg hjac hle

include hfund in
/-- `L(λ)` is contained in the span of `{b⁻η | b ∈ B}` over the local ring at `v = ∞`. -/
theorem lat_le_span : lat hvt hR A Λ ≤ Submodule.span A (evq hvt Λ '' canonicalBasis D) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨w, rfl⟩
  have h := lat_inf_wsp_le_span hR hfund Λ (wordWeight w)
    ⟨Submodule.subset_span ⟨w, rfl⟩, fW_mem_wsp hvt hR Λ w⟩
  refine Submodule.span_mono ?_ h
  rintro _ ⟨b, rfl⟩
  exact ⟨_, (mem_canonicalBasis_iff D).2 ⟨_, b, rfl⟩, rfl⟩

include hfund in
/-- **`A`-coordinates**: the vectors of `L(λ)` have coordinates in the local ring at `v = ∞` in
the canonical basis `{b⁻η | b ∈ B(λ)}`. -/
theorem repr_mem_of_mem_lat {m : IrreducibleModule R 𝕧 Λ.1} (hm : m ∈ lat hvt hR A Λ)
    (b : canonicalBasisHW D Λ) : (𝔅).repr m b ∈ (algebraMap A 𝕂).range :=
  repr_mem_of_mem_span_evq hR Λ (algebraMap A 𝕂) (fun c m ↦ (algebraMap_smul 𝕂 c m).symm)
    (lat_le_span hR hfund Λ hm) b

end Lattice

/-! ### The product basis of `Λ_λ ⊗ Λ_{λ'}` -/

section Tensor

variable (Λ₁ Λ₂ : Dom R)

/-- The basis `b₁⁻η ⊗ b₂⁻η'` (`b₁ ∈ B(λ)`, `b₂ ∈ B(λ')`) of `Λ_λ ⊗ Λ_{λ'}`. -/
def tensorHWBasis : Module.Basis (canonicalBasisHW D Λ₁ × canonicalBasisHW D Λ₂) 𝕂
    (TensorModule 𝕂 (IrreducibleModule R 𝕧 Λ₁.1) (IrreducibleModule R 𝕧 Λ₂.1)) :=
  ((canonicalBasisHWBasis Λ₁ hR).tensorProduct (canonicalBasisHWBasis Λ₂ hR)).map
    (TensorModule.mk _ _)

lemma tensorHWBasis_apply (p : canonicalBasisHW D Λ₁ × canonicalBasisHW D Λ₂) :
    tensorHWBasis hR Λ₁ Λ₂ p =
      TensorModule.mk _ _ (evq hvt Λ₁ (p.1 : Um D 𝕧) ⊗ₜ[𝕂] evq hvt Λ₂ (p.2 : Um D 𝕧)) := by
  rw [tensorHWBasis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply',
    canonicalBasisHWBasis_apply, canonicalBasisHWBasis_apply]

lemma repr_tensorHWBasis_mk (x : IrreducibleModule R 𝕧 Λ₁.1) (y : IrreducibleModule R 𝕧 Λ₂.1)
    (p : canonicalBasisHW D Λ₁ × canonicalBasisHW D Λ₂) :
    (tensorHWBasis hR Λ₁ Λ₂).repr (TensorModule.mk _ _ (x ⊗ₜ[𝕂] y)) p =
      (canonicalBasisHWBasis Λ₁ hR).repr x p.1 * (canonicalBasisHWBasis Λ₂ hR).repr y p.2 := by
  rw [tensorHWBasis, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    ← Prod.mk.eta (p := p), Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, mul_comm]

/-- If `x`, `y` have coordinates in a subring `S`, so does `x ⊗ y`. -/
lemma repr_tensorHWBasis_mk_mem (S : Subring 𝕂) {x : IrreducibleModule R 𝕧 Λ₁.1}
    {y : IrreducibleModule R 𝕧 Λ₂.1} (hx : ∀ b, (canonicalBasisHWBasis Λ₁ hR).repr x b ∈ S)
    (hy : ∀ b, (canonicalBasisHWBasis Λ₂ hR).repr y b ∈ S)
    (p : canonicalBasisHW D Λ₁ × canonicalBasisHW D Λ₂) :
    (tensorHWBasis hR Λ₁ Λ₂).repr (TensorModule.mk _ _ (x ⊗ₜ[𝕂] y)) p ∈ S := by
  rw [repr_tensorHWBasis_mk]
  exact mul_mem (hx _) (hy _)

include hfund in
/-- The vectors of `L(λ) ⊗ L(λ')` have coordinates in the local ring at `v = ∞` in the basis
`b₁⁻η ⊗ b₂⁻η'`. -/
theorem repr_mem_of_mem_LL {z : TensorModule 𝕂 (IrreducibleModule R 𝕧 Λ₁.1)
    (IrreducibleModule R 𝕧 Λ₂.1)} (hz : z ∈ LL hvt hR A Λ₁ Λ₂)
    (p : canonicalBasisHW D Λ₁ × canonicalBasisHW D Λ₂) :
    (tensorHWBasis hR Λ₁ Λ₂).repr z p ∈ (algebraMap A 𝕂).range := by
  refine repr_mem_range_of_mem_span (algebraMap A 𝕂) (fun c m ↦ (algebraMap_smul 𝕂 c m).symm)
    _ ?_ hz p
  rintro _ ⟨x, hx, y, hy, rfl⟩ p
  exact repr_tensorHWBasis_mk_mem hR Λ₁ Λ₂ (algebraMap A 𝕂).range
    (repr_mem_of_mem_lat hR hfund Λ₁ hx) (repr_mem_of_mem_lat hR hfund Λ₂ hy) p

end Tensor

end LieLean.QuantumGroup
