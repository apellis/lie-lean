/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityWall

/-!
# Slices of `y⁻ (x ⊗ y')`

With Lusztig's coproduct `Fⱼ (x ⊗ y) = Fⱼ x ⊗ K̃ⱼ⁻¹ y + x ⊗ Fⱼ y`, for `u ∈ U⁻` the vector
`u (x ⊗ y)` is `x ⊗ u y` plus terms whose first factor lies in a subspace `S` stable under the
`Fⱼ` and containing all `Fⱼ x` (`TensorModule.minusHom_smul_tmul_sub_mem`). Hence a functional
`f` on the first factor vanishing on `S` gives `(f ⊗ 1)(u (x ⊗ y)) = f(x) u y`
(`TensorModule.prL_minusHom_smul_tmul`).

For `V(μ) ⊗ V(λ)` with `⟨i, λ⟩ = 0` and `z` of weight `μ - m αᵢ`:
`(z, ·) ⊗ 1` sends `y⁻ Fᵢ^m (v_μ ⊗ v_λ)` to `(z, Fᵢ^m v_μ) y⁻ v_λ`
(`GrandLoop.prL_tensorEmb_ev_mul_θ_pow`).

Lattice estimates used with it, in the grand-loop setting: for `⟨j, μ⟩ ≫ 0`,
`(π_μ x, π_μ y)_μ ≡ (x, y)` on `L(∞)` (`GrandLoop.exists_form_evq_sub_formU_large`), the form
`(z, ·)` is `A`-valued on `L(μ)` (`GrandLoop.exists_form_mem_of_large`) and
`(f̃_a v_μ, f̃_b v_μ)_μ ≡ δ` (`GrandLoop.exists_form_fW_fW`); `T = Φ ∘ π_{μ+λ}` is injective
modulo `ϖ` on `L(∞)` (`GrandLoop.exists_mem_smul_latInf_of_tensorEmb_mem`, from `Ψ ∘ Φ = 1` and
[HK] Lemma 5.3.15) and `T(f̃ₛ 1) ≡ f̃_{s₁} v_μ ⊗ f̃_{s₂} v_λ`
(`GrandLoop.exists_tensorEmb_evq_fWi_sub`);
and `B(λ)` is linearly independent for indexed families (`GrandLoop.coeff_mem_of_sum_fW_mem`).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
-/

open Finset Pointwise TensorProduct LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace TensorModule

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]
  {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁]
  [AddCommGroup M₂] [Module k M₂] [Module (QuantumGroup R v) M₂]
  [IsScalarTower k (QuantumGroup R v) M₂]

variable (M₂) in
/-- The span of the `x ⊗ y` with `x ∈ S`. -/
def lowSpan (S : Submodule k M₁) : Submodule k (TensorModule k M₁ M₂) :=
  Submodule.span k (Set.range fun p : S × M₂ ↦ mk M₁ M₂ ((p.1 : M₁) ⊗ₜ[k] p.2))

omit [DecidableEq I] [NeZero v] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁] [Module (QuantumGroup R v) M₂]
  [IsScalarTower k (QuantumGroup R v) M₂] in
lemma tmul_mem_lowSpan {S : Submodule k M₁} {x : M₁} (hx : x ∈ S) (y : M₂) :
    mk M₁ M₂ (x ⊗ₜ[k] y) ∈ lowSpan M₂ S :=
  Submodule.subset_span ⟨(⟨x, hx⟩, y), rfl⟩

lemma F_smul_mem_lowSpan {S : Submodule k M₁} (hS : ∀ j, ∀ x ∈ S, F R v j • x ∈ S) (j : I)
    {w : TensorModule k M₁ M₂} (hw : w ∈ lowSpan M₂ S) : F R v j • w ∈ lowSpan M₂ S := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨⟨x, hx⟩, y⟩, rfl⟩ := hw
    rw [F_smul_tmul, map_add]
    exact add_mem (tmul_mem_lowSpan (hS j x hx) _) (tmul_mem_lowSpan hx _)
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ _ ha

lemma minusHom_smul_mem_lowSpan {S : Submodule k M₁} (hS : ∀ j, ∀ x ∈ S, F R v j • x ∈ S)
    (a : LusztigF k I) {w : TensorModule k M₁ M₂} (hw : w ∈ lowSpan M₂ S) :
    minusHom R v a • w ∈ lowSpan M₂ S := by
  induction a using FreeAlgebra.induction generalizing w with
  | grade0 c =>
    rw [AlgHom.commutes, algebraMap_smul]; exact Submodule.smul_mem _ _ hw
  | grade1 j =>
    rw [show FreeAlgebra.ι k j = θ k j from rfl, minusHom_θ]
    exact F_smul_mem_lowSpan hS j hw
  | mul a b ha hb => rw [map_mul, mul_smul]; exact ha (hb hw)
  | add a b ha hb => rw [map_add, add_smul]; exact add_mem (ha hw) (hb hw)

/-- `u (x ⊗ y) ≡ x ⊗ u y` modulo the span of `S ⊗ M₂`, for `u ∈ U⁻`. -/
theorem minusHom_smul_tmul_sub_mem {S : Submodule k M₁} (hS : ∀ j, ∀ x ∈ S, F R v j • x ∈ S)
    {x : M₁} (hx : ∀ j, F R v j • x ∈ S) (a : LusztigF k I) :
    ∀ y : M₂, minusHom R v a • mk M₁ M₂ (x ⊗ₜ[k] y) -
      mk M₁ M₂ (x ⊗ₜ[k] (minusHom R v a • y)) ∈ lowSpan M₂ S := by
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    intro y
    rw [AlgHom.commutes, algebraMap_smul, algebraMap_smul, tmul_smul, map_smul, sub_self]
    exact zero_mem _
  | grade1 j =>
    intro y
    rw [show FreeAlgebra.ι k j = θ k j from rfl, minusHom_θ, F_smul_tmul, map_add,
      add_sub_cancel_right]
    exact tmul_mem_lowSpan (hx j) _
  | mul a b ha hb =>
    intro y
    have e : minusHom R v (a * b) • mk M₁ M₂ (x ⊗ₜ[k] y) -
        mk M₁ M₂ (x ⊗ₜ[k] (minusHom R v (a * b) • y)) =
        minusHom R v a • (minusHom R v b • mk M₁ M₂ (x ⊗ₜ[k] y) -
          mk M₁ M₂ (x ⊗ₜ[k] (minusHom R v b • y))) +
        (minusHom R v a • mk M₁ M₂ (x ⊗ₜ[k] (minusHom R v b • y)) -
          mk M₁ M₂ (x ⊗ₜ[k] (minusHom R v a • (minusHom R v b • y)))) := by
      rw [map_mul, mul_smul, mul_smul, smul_sub]; abel
    rw [e]
    exact add_mem (minusHom_smul_mem_lowSpan hS a (hb y)) (ha _)
  | add a b ha hb =>
    intro y
    have e : minusHom R v (a + b) • mk M₁ M₂ (x ⊗ₜ[k] y) -
        mk M₁ M₂ (x ⊗ₜ[k] (minusHom R v (a + b) • y)) =
        (minusHom R v a • mk M₁ M₂ (x ⊗ₜ[k] y) - mk M₁ M₂ (x ⊗ₜ[k] (minusHom R v a • y))) +
        (minusHom R v b • mk M₁ M₂ (x ⊗ₜ[k] y) - mk M₁ M₂ (x ⊗ₜ[k] (minusHom R v b • y))) := by
      rw [map_add, add_smul, add_smul, tmul_add, map_add]; abel
    rw [e]
    exact add_mem (ha y) (hb y)

variable (M₂) in
/-- `f ⊗ 1 : M₁ ⊗ M₂ → M₂` for a functional `f` on `M₁`. -/
def prL (f : M₁ →ₗ[k] k) : TensorModule k M₁ M₂ →ₗ[k] M₂ :=
  TensorProduct.lift ((LinearMap.lsmul k M₂).comp f) ∘ₗ (mk M₁ M₂).symm.toLinearMap

omit [DecidableEq I] [NeZero v] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁] [Module (QuantumGroup R v) M₂]
  [IsScalarTower k (QuantumGroup R v) M₂] in
@[simp] lemma prL_tmul (f : M₁ →ₗ[k] k) (x : M₁) (y : M₂) :
    prL M₂ f (mk M₁ M₂ (x ⊗ₜ[k] y)) = f x • y := by
  simp [prL]

omit [DecidableEq I] [NeZero v] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁] [Module (QuantumGroup R v) M₂]
  [IsScalarTower k (QuantumGroup R v) M₂] in
lemma prL_eq_zero_of_mem {S : Submodule k M₁} {f : M₁ →ₗ[k] k} (hf : ∀ x ∈ S, f x = 0)
    {w : TensorModule k M₁ M₂} (hw : w ∈ lowSpan M₂ S) : prL M₂ f w = 0 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨⟨x, hx⟩, y⟩, rfl⟩ := hw
    rw [prL_tmul, hf x hx, zero_smul]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

/-- **The slice formula**: `(f ⊗ 1)(u (x ⊗ y)) = f(x) u y` for `u ∈ U⁻`, if `f` vanishes on an
`Fⱼ`-stable `S` containing the `Fⱼ x`. -/
theorem prL_minusHom_smul_tmul {S : Submodule k M₁} (hS : ∀ j, ∀ x ∈ S, F R v j • x ∈ S)
    {x : M₁} (hx : ∀ j, F R v j • x ∈ S) {f : M₁ →ₗ[k] k} (hf : ∀ x ∈ S, f x = 0)
    (a : LusztigF k I) (y : M₂) :
    prL M₂ f (minusHom R v a • mk M₁ M₂ (x ⊗ₜ[k] y)) = f x • (minusHom R v a • y) := by
  have h := prL_eq_zero_of_mem hf (minusHom_smul_tmul_sub_mem hS hx a y)
  rwa [map_sub, prL_tmul, sub_eq_zero] at h

end TensorModule

namespace GrandLoop

open TensorModule

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular}

omit [CharZero k] in
/-- `Fᵢ v_λ = 0` if `⟨i, λ⟩ = 0`. -/
lemma F_smul_hwv_eq_zero (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {Λ : Dom R}
    {i : I} (hΛi : Λ.1 (R.coroot i) = 0) : F R v i • IrreducibleModule.hwv R v Λ.1 = 0 := by
  have h := VermaModule.fPowSubmodule_le_maxSubmodule hR hv' Λ.2
    (Submodule.subset_span ⟨i, rfl⟩)
  simp only [hΛi, Int.toNat_zero, zero_add, pow_one] at h
  change F R v i • (Submodule.Quotient.mk (VermaModule.hwv R v Λ.1) :
    IrreducibleModule R v Λ.1) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact h

omit [CharZero k] [NeZero v] in
/-- `K̃ᵢ⁻¹ v_λ = v_λ` if `⟨i, λ⟩ = 0`. -/
lemma K_neg_ktilde_smul_hwv {Λ : Dom R} {i : I} (hΛi : Λ.1 (R.coroot i) = 0) :
    K R v (-ktilde R i) • IrreducibleModule.hwv R v Λ.1 = IrreducibleModule.hwv R v Λ.1 := by
  have h := IrreducibleModule.hwv_mem_weightSpace (R := R) (v := v) (Λ := Λ.1) (-ktilde R i)
  rw [h, map_neg, ktilde, map_nsmul, hΛi, nsmul_zero, neg_zero, zpow_zero, one_smul]

omit [CharZero k] in
/-- `Fᵢⁿ (x ⊗ v_λ) = Fᵢⁿ x ⊗ v_λ` if `⟨i, λ⟩ = 0`. -/
lemma F_pow_smul_tmul_hwv (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {Λ₁ Λ : Dom R}
    {i : I}
    (hΛi : Λ.1 (R.coroot i) = 0) (n : ℕ) (x : IrreducibleModule R v Λ₁.1) :
    F R v i ^ n • TensorModule.mk _ _ (x ⊗ₜ[k] IrreducibleModule.hwv R v Λ.1) =
      TensorModule.mk _ _ ((F R v i ^ n • x) ⊗ₜ[k] IrreducibleModule.hwv R v Λ.1) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, mul_smul, F_smul_tmul, K_neg_ktilde_smul_hwv hΛi,
      F_smul_hwv_eq_zero hR hv' hΛi, tmul_zero, add_zero, ih]

omit [CharZero k] in
lemma F_smul_mem_wsp {Λ : Dom R} {ν : I →₀ ℕ} {x : IrreducibleModule R v Λ.1} (hx : x ∈ wsp Λ ν)
    (j : I) : F R v j • x ∈ wsp Λ (ν + Finsupp.single j 1) := by
  have h := F_smul_mem_weightSpace hx j
  rwa [show Λ.1 - R.rootSum ν - R.root j = Λ.1 - R.rootSum (ν + Finsupp.single j 1) by
    rw [R.rootSum_add, R.rootSum_single, one_nsmul, sub_sub]] at h

omit [CharZero k] in
lemma F_pow_smul_hwv_mem_wsp (Λ : Dom R) (i : I) (n : ℕ) :
    F R v i ^ n • IrreducibleModule.hwv R v Λ.1 ∈ wsp Λ (n • Finsupp.single i 1) := by
  induction n with
  | zero =>
    simpa [wsp] using IrreducibleModule.hwv_mem_weightSpace (R := R) (v := v) (Λ := Λ.1)
  | succ n ih =>
    rw [pow_succ', mul_smul, succ_nsmul]
    exact F_smul_mem_wsp ih i

variable (Λ : Dom R) (ν₀ : I →₀ ℕ) in
/-- The weight spaces of `V(λ)` strictly below `λ - ν₀`. -/
def lowWsp : Submodule k (IrreducibleModule R v Λ.1) :=
  ⨆ ν' : {ν' : I →₀ ℕ // ν₀ ≤ ν' ∧ ν' ≠ ν₀}, wsp Λ ν'.1

omit [CharZero k] in
lemma F_smul_mem_lowWsp {Λ : Dom R} {ν₀ : I →₀ ℕ} (j : I) {x : IrreducibleModule R v Λ.1}
    (hx : x ∈ lowWsp Λ ν₀) : F R v j • x ∈ lowWsp Λ ν₀ := by
  refine Submodule.iSup_induction _ (motive := fun x ↦ F R v j • x ∈ lowWsp Λ ν₀) hx
    (fun ν' x hx ↦ ?_) (by rw [smul_zero]; exact zero_mem _)
    (fun a b ha hb ↦ by rw [smul_add]; exact add_mem ha hb)
  refine Submodule.mem_iSup_of_mem ⟨ν'.1 + Finsupp.single j 1, ?_, ?_⟩ (F_smul_mem_wsp hx j)
  · exact le_trans ν'.2.1 le_self_add
  · intro h
    have h1 : ν₀ ≤ ν'.1 := ν'.2.1
    have h2 : ν₀ j ≤ ν'.1 j := h1 j
    have h3 := congrArg (fun f ↦ f j) h
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at h3
    have : ν'.1 j + 1 ≤ ν'.1 j := by omega
    simp at this

omit [CharZero k] in
lemma F_smul_mem_lowWsp_of_mem {Λ : Dom R} {ν₀ : I →₀ ℕ} {x : IrreducibleModule R v Λ.1}
    (hx : x ∈ wsp Λ ν₀) (j : I) : F R v j • x ∈ lowWsp Λ ν₀ := by
  refine Submodule.mem_iSup_of_mem ⟨ν₀ + Finsupp.single j 1, le_self_add, fun h ↦ ?_⟩
    (F_smul_mem_wsp hx j)
  have := congrArg (fun f ↦ f j) h
  simp at this

omit [CharZero k] in
/-- The form `(z, ·)` vanishes on the weight spaces below the weight of `z`. -/
lemma form_eq_zero_of_mem_lowWsp (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {Λ : Dom R} {ν₀ : I →₀ ℕ} {z : IrreducibleModule R v Λ.1} (hz : z ∈ wsp Λ ν₀)
    {x : IrreducibleModule R v Λ.1} (hx : x ∈ lowWsp Λ ν₀) :
    IrreducibleModule.form Λ.1 hR hv' z x = 0 := by
  refine Submodule.iSup_induction _ (motive := fun x ↦ IrreducibleModule.form Λ.1 hR hv' z x = 0)
    hx (fun ν' x hx ↦ ?_) (by simp) (fun a b ha hb ↦ by rw [map_add, ha, hb, add_zero])
  refine (IrreducibleModule.isContravariant_form hR hv').eq_zero_of_ne ?_ hz hx hv'
  intro h
  exact ν'.2.2 (LusztigCartanDatum.RootDatum.rootSum_injective hR (sub_right_injective h)).symm

/-- **The slice formula on `V(μ) ⊗ V(λ)`**: for `⟨i, λ⟩ = 0` and `z` of weight `μ - m αᵢ`,
`((z, ·) ⊗ 1) Φ((y Fᵢ^m) v_{μ+λ}) = (z, Fᵢ^m v_μ) y v_λ`. -/
theorem prL_tensorEmb_ev_mul_θ_pow [Finite I] (hR : R.IsXRegular) {Λ₁ Λ : Dom R} {i : I}
    (hΛi : Λ.1 (R.coroot i) = 0) (m : ℕ) {z : IrreducibleModule R v Λ₁.1}
    (hz : z ∈ wsp Λ₁ (m • Finsupp.single i 1)) (y : LusztigF k I) :
    prL _ (IrreducibleModule.form Λ₁.1 hR (pow_ne_one_of_transcendental' hvt) z)
        (tensorEmb hvt hR Λ₁.2 Λ.2 (ev R v (Λ₁ + Λ).1 (y * θ k i ^ m))) =
      IrreducibleModule.form Λ₁.1 hR (pow_ne_one_of_transcendental' hvt) z
          (F R v i ^ m • IrreducibleModule.hwv R v Λ₁.1) • ev R v Λ.1 y := by
  set hv' := pow_ne_one_of_transcendental' hvt
  have hev : ∀ (Λ' : Dom R) (y' : LusztigF k I),
      ev R v Λ'.1 y' = minusHom R v y' • IrreducibleModule.hwv R v Λ'.1 := by
    intro Λ' y'
    rw [ev_apply, VermaModule.toVerma_apply, Submodule.Quotient.mk_smul]
  rw [hev, hev, map_smul, map_mul, mul_smul, map_pow, minusHom_θ]
  change prL _ _ (minusHom R v y • (F R v i ^ m • tensorEmb hvt hR Λ₁.2 Λ.2
    (IrreducibleModule.hwv R v (Λ₁.1 + Λ.1)))) = _
  rw [tensorEmb_hwv, F_pow_smul_tmul_hwv hR hv' hΛi]
  exact prL_minusHom_smul_tmul (S := lowWsp Λ₁ (m • Finsupp.single i 1))
    (fun j x hx ↦ F_smul_mem_lowWsp j hx)
    (fun j ↦ F_smul_mem_lowWsp_of_mem (F_pow_smul_hwv_mem_wsp Λ₁ i m) j)
    (fun x hx ↦ form_eq_zero_of_mem_lowWsp hR hv' hz hx) y _

/-! ### Lattice estimates for `V(μ) ⊗ V(λ)` -/

section Base

open VermaModule

variable {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}
variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

omit hinj hϖ hfund [IsDomain A] [IsDiscreteValuationRing A] in
include hR in
/-- For `⟨j, λ⟩ ≫ 0` for all `j`, `(π_λ x, π_λ y)_λ ≡ (x, y)` modulo `ϖ` on `L(∞) ∩ U⁻_{-ν}`. -/
theorem exists_form_evq_sub_formU_large (ν : I →₀ ℕ) :
    ∃ m₀ : ℕ, ∀ Λ : Dom R, (∀ j, (m₀ : ℤ) ≤ Λ.1 (R.coroot j)) →
      ∀ x ∈ latInf hvt A, x ∈ Uw D v ν → ∀ y ∈ latInf hvt A, y ∈ Uw D v ν →
        ∃ a : A, IrreducibleModule.form Λ.1 hR (pow_ne_one_of_transcendental' hvt)
          (evq hvt Λ x) (evq hvt Λ y) - formU (pow_ne_one_of_transcendental' hvt) x y =
              algebraMap A k (ϖ * a) := by
  classical
  set hv' := pow_ne_one_of_transcendental' hvt
  obtain ⟨c, hc⟩ := exists_pow_smul_eq_mk (hvt := hvt) hk ν
  obtain ⟨C, hC⟩ := exists_shapZ_sub_shapZ_mem (D := D) (v := v) A hk ν.degree (fun _ ↦ 0)
  refine ⟨C + 2 * c + 1, fun Λ hΛ x hx hxw y hy hyw ↦ ?_⟩
  set m₀ := C + 2 * c + 1
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨P, hP, eP⟩ := hc x hx hxw
  obtain ⟨Q, hQ, eQ⟩ := hc y hy hyw
  have hz : ∀ j, ∃ a : A, zcoef R v Λ.1 j - algebraMap A k ((fun _ ↦ (0 : A)) j) =
      algebraMap A k (ϖ ^ m₀ * a) := by
    intro j
    rw [zcoef_eq hϖv Λ.1 j (Λ.2 j), map_zero, sub_zero]
    have h1 := hΛ j
    have h2 := D.d_pos j
    obtain ⟨d, hd⟩ : ∃ d, 2 * D.d j * (Λ.1 (R.coroot j)).toNat = m₀ + d := by
      refine ⟨2 * D.d j * (Λ.1 (R.coroot j)).toNat - m₀, ?_⟩
      have : (m₀ : ℤ) ≤ ((Λ.1 (R.coroot j)).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg (Λ.2 j)]; exact h1
      have h3 : m₀ ≤ (Λ.1 (R.coroot j)).toNat := by exact_mod_cast this
      have h4 : (Λ.1 (R.coroot j)).toNat ≤ 2 * D.d j * (Λ.1 (R.coroot j)).toNat := by
        nlinarith
      omega
    exact ⟨ϖ ^ d, by rw [hd, pow_add]⟩
  obtain ⟨a, ha⟩ := hC (zcoef R v Λ.1) m₀ hz P hP Q hQ
  simp only [map_zero] at ha
  rw [show (fun _ : I ↦ (0 : k)) = (0 : I → k) from rfl, ← form_eq_shapZ_zero,
    ← shapF_eq_shapZ R hv', shapF_apply, ← IrreducibleModule.form_mk hR] at ha
  have e1 : IrreducibleModule.form Λ.1 hR hv' (Submodule.Quotient.mk (toVerma R v Λ.1 P))
      (Submodule.Quotient.mk (toVerma R v Λ.1 Q)) =
      algebraMap A k (ϖ ^ c) * algebraMap A k (ϖ ^ c) *
        IrreducibleModule.form Λ.1 hR hv' (evq hvt Λ x) (evq hvt Λ y) := by
    have hx' : (Submodule.Quotient.mk (toVerma R v Λ.1 P) : IrreducibleModule R v Λ.1) =
        algebraMap A k (ϖ ^ c) • evq hvt Λ x := by
      rw [← map_smul, algebraMap_smul, eP]; rfl
    have hy' : (Submodule.Quotient.mk (toVerma R v Λ.1 Q) : IrreducibleModule R v Λ.1) =
        algebraMap A k (ϖ ^ c) • evq hvt Λ y := by
      rw [← map_smul, algebraMap_smul, eQ]; rfl
    rw [hx', hy']
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
  have e2 : LusztigF.form D v P Q =
      algebraMap A k (ϖ ^ c) * algebraMap A k (ϖ ^ c) * formU hv' x y := by
    rw [← formU_mk hv', ← eP, ← eQ, ← algebraMap_smul k, ← algebraMap_smul k (ϖ ^ c) y,
      map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]; ring
  rw [e1, e2] at ha
  refine ⟨a, ?_⟩
  have hne : algebraMap A k (ϖ ^ (C + 2 * c)) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hϖ0
  apply mul_left_cancel₀ hne
  have em : m₀ = C + 2 * c + 1 := rfl
  rw [em, pow_succ, show C + 2 * c = C + c + c by ring] at ha
  rw [show C + 2 * c = C + c + c by ring]
  simp only [pow_add, map_mul] at ha ⊢
  linear_combination ha

include hR in
/-- For `⟨j, μ⟩ ≫ 0`, `(z, x)_μ ∈ A` for `z ∈ L(μ)_{μ-ν₀}` and `x ∈ L(μ)`. -/
theorem exists_form_mem_of_large (ν₀ : I →₀ ℕ) :
    ∃ m₀ : ℕ, ∀ Λ : Dom R, (∀ j, (m₀ : ℤ) ≤ Λ.1 (R.coroot j)) →
      ∀ z ∈ lat hvt hR A Λ, z ∈ wsp Λ ν₀ → ∀ x ∈ lat hvt hR A Λ,
        ∃ a : A, IrreducibleModule.form Λ.1 hR (pow_ne_one_of_transcendental' hvt) z x =
          algebraMap A k a := by
  set hv' := pow_ne_one_of_transcendental' hvt
  obtain ⟨m₀, hm₀⟩ := exists_form_evq_sub_formU_large (hR := hR) hϖv hk ν₀
  refine ⟨m₀, fun Λ hΛ z hz hzw x hx ↦ ?_⟩
  obtain ⟨b, hbL, hbw, rfl⟩ := exists_evq_eq (hR := hR) hinj hϖ hϖv hk hfund hz hzw
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    by_cases hw : wordWeight w = ν₀
    · have hxw : fW hvt hR Λ w ∈ wsp Λ ν₀ := hw ▸ fW_mem_wsp hvt hR Λ w
      obtain ⟨c, hcL, hcw, hc⟩ := exists_evq_eq (hR := hR) hinj hϖ hϖv hk hfund
        (IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A w) hxw
      obtain ⟨a₁, ha₁⟩ := hm₀ Λ hΛ b hbL hbw c hcL hcw
      obtain ⟨a₂, ha₂⟩ := formU_mem (hR := hR) hinj hϖ hϖv hk hfund hbL hcL
      refine ⟨ϖ * a₁ + a₂, ?_⟩
      rw [← hc, map_add, ← ha₂, ← ha₁]; ring
    · refine ⟨0, ?_⟩
      rw [map_zero]
      refine (IrreducibleModule.isContravariant_form hR hv').eq_zero_of_ne ?_
        (evq_mem_wsp hR hbw Λ) (fW_mem_wsp hvt hR Λ w) hv'
      intro h
      exact hw (LusztigCartanDatum.RootDatum.rootSum_injective hR (sub_right_injective h)).symm
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b', hb'⟩ := hy
    exact ⟨a + b', by rw [map_add, ha, hb', map_add]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [← algebraMap_smul k c x, map_smul, ha, smul_eq_mul, map_mul]⟩

omit hinj hϖ hϖv hk hfund [IsDomain A] [IsDiscreteValuationRing A] [Finite I] in
lemma prL_mem_lat {Λ₁ Λ₂ : Dom R} {f : IrreducibleModule R v Λ₁.1 →ₗ[k] k}
    (hf : ∀ x ∈ lat hvt hR A Λ₁, ∃ a : A, f x = algebraMap A k a) {w : TM v Λ₁ Λ₂}
    (hw : w ∈ LL hvt hR A Λ₁ Λ₂) : prL _ f w ∈ lat hvt hR A Λ₂ := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hw
    rw [prL_tmul]
    obtain ⟨a, ha⟩ := hf x hx
    rw [ha, algebraMap_smul]
    exact Submodule.smul_mem _ _ hy
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [← algebraMap_smul k c a, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ _ ha

omit hinj hϖ hϖv hk hfund [IsDomain A] [IsDiscreteValuationRing A] [Finite I] in
lemma prL_mem_smul_lat {Λ₁ Λ₂ : Dom R} {f : IrreducibleModule R v Λ₁.1 →ₗ[k] k}
    (hf : ∀ x ∈ lat hvt hR A Λ₁, ∃ a : A, f x = algebraMap A k a) {w : TM v Λ₁ Λ₂}
    (hw : w ∈ ϖ • LL hvt hR A Λ₁ Λ₂) : prL _ f w ∈ ϖ • lat hvt hR A Λ₂ := by
  obtain ⟨w₀, hw₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hw
  rw [← algebraMap_smul k, map_smul, algebraMap_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (prL_mem_lat hf hw₀)

include hR in
/-- **`T = Φ ∘ π_{μ+λ}` is injective modulo `ϖ`** on `L(∞) ∩ U⁻_{-ν}` for `μ = Λ + Λs`
(from `Ψ ∘ Φ = 1` and [HK] Lemma 5.3.15). -/
theorem exists_mem_smul_latInf_of_tensorEmb_mem {ν : I →₀ ℕ} (hν : ν.degree ≠ 0) :
    ∃ Λs : Dom R, (∀ j, (ν.degree : ℤ) ≤ Λs.1 (R.coroot j)) ∧ ∀ Λ Λ₂ : Dom R,
      ∀ u ∈ latInf hvt A, u ∈ Uw D v ν →
        tensorEmb hvt hR (Λ + Λs).2 Λ₂.2 (evq hvt (Λ + Λs + Λ₂) u) ∈
          ϖ • LL hvt hR A (Λ + Λs) Λ₂ → u ∈ ϖ • latInf hvt A := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hν
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  obtain ⟨ρ, hρ⟩ := exists_rho hfund
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨Λs, hΛs, hproj⟩ := tensorProj_mem_lat_of_large (hvt := hvt) (hR := hR) hk hinj hϖ hϖv
    hr (fun s _ ↦ (hall s).1) (fun s _ ↦ (hall s).2.1) (fun s _ ↦ (hall s).2.2.1)
    (hall (r + 1)).2.2.2.2.1 (hall r).2.2.2.2.2.1 ρ hρ
  refine ⟨Λs, fun j ↦ by rw [hr]; exact hΛs j, fun Λ Λ₂ u hu huw hT ↦ ?_⟩
  obtain ⟨z, hz, ez⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hT
  have hzw : z ∈ weightSpace R v (TM v (Λ + Λs) Λ₂) ((Λ + Λs).1 + Λ₂.1 - R.rootSum ν) := by
    have h := map_mem_weightSpace (tensorEmb hvt hR (Λ + Λs).2 Λ₂.2)
      (evq_mem_wsp (hvt := hvt) hR huw (Λ + Λs + Λ₂))
    rw [← ez, ← algebraMap_smul k] at h
    have := Submodule.smul_mem _ (algebraMap A k ϖ)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hϖ0, one_smul] at this
  have hP := hproj Λ Λ₂ z hz hzw
  have he : evq hvt (Λ + Λs + Λ₂) u = ϖ • tensorProj hvt hR (Λ + Λs).2 Λ₂.2 z := by
    rw [← algebraMap_smul k, ← LinearMap.map_smul_of_tower, algebraMap_smul, ez,
      tensorProj_tensorEmb]
  have hlarge : ∀ j, (ν.degree : ℤ) ≤ (Λ + Λs + Λ₂).1 (R.coroot j) := by
    intro j
    have h1 := hΛs j
    have h2 := Λ.2 j
    have h3 := Λ₂.2 j
    change (ν.degree : ℤ) ≤ (Λ.1 + Λs.1 + Λ₂.1) (R.coroot j)
    rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, hr]
    omega
  rw [mem_smul_latInf_iff (hR := hR) hinj hϖ hϖv hk hfund hlarge hu huw, he]
  exact Submodule.smul_mem_pointwise_smul _ _ _ hP

include hR in
/-- `T(f̃ₛ 1) ≡ f̃_{s₁} v_μ ⊗ f̃_{s₂} v_λ` modulo `ϖ (L(μ) ⊗ L(λ))`. -/
theorem exists_tensorEmb_evq_fWi_sub (Λ₁ Λ₂ : Dom R) (s : List I) :
    ∃ s₁ s₂ : List I, wordWeight s₁ + wordWeight s₂ = wordWeight s ∧
      tensorEmb hvt hR Λ₁.2 Λ₂.2 (evq hvt (Λ₁ + Λ₂) (fWi hvt s)) -
        TensorModule.mk _ _ (fW hvt hR Λ₁ s₁ ⊗ₜ[k] fW hvt hR Λ₂ s₂) ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  obtain ⟨s₁, s₂, -, -, -, hw, hcong⟩ := fTw_fW_tmul (hvt := hvt) (hR := hR) (Λ₁ := Λ₁)
    (Λ₂ := Λ₂) hϖ hϖv s (w₁ := []) (w₂ := []) (fun t _ ↦ (hall t).1) (fun t _ ↦ (hall t).2.1)
    (fun t _ ↦ (hall t).2.2.1)
  refine ⟨s₁, s₂, by simpa using hw, ?_⟩
  have h1 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund s (Λ₁ + Λ₂)
  obtain ⟨y, hy, ey⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
  have h2 : tensorEmb hvt hR Λ₁.2 Λ₂.2 (evq hvt (Λ₁ + Λ₂) (fWi hvt s)) -
      tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) s) ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
    rw [← map_sub, ← ey, ← algebraMap_smul k, LinearMap.map_smul_of_tower, algebraMap_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _
      (tensorEmb_mem_LL hϖ hϖv (fun t ↦ (hall t).1) hy)
  rw [tensorEmb_fW] at h2
  simp only [fW_nil] at hcong
  simpa using add_mem h2 hcong

include hR in
/-- Linear independence of `B(λ)` for an indexed family of words. -/
theorem coeff_mem_of_sum_fW_mem {ι : Type*} (Λ : Dom R) {ν : I →₀ ℕ} (T : Finset ι)
    (g : ι → List I) (c : ι → A) (hgw : ∀ t ∈ T, wordWeight (g t) = ν)
    (h0 : ∀ t ∈ T, fW hvt hR Λ (g t) ∉ ϖ • lat hvt hR A Λ)
    (hd : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → fW hvt hR Λ (g t) - fW hvt hR Λ (g t') ∉ ϖ • lat hvt hR A Λ)
    (hsum : ∑ t ∈ T, c t • fW hvt hR Λ (g t) ∈ ϖ • lat hvt hR A Λ) :
    ∀ t ∈ T, c t ∈ Ideal.span {ϖ} := by
  classical
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  have hinjg : Set.InjOn g T := fun t ht t' ht' h ↦ by
    by_contra hne
    exact hd t ht t' ht' hne (by rw [h, sub_self]; exact zero_mem _)
  set b : List I → A := fun w ↦ ∑ t ∈ T with g t = w, c t
  have hb : ∀ t ∈ T, b (g t) = c t := by
    intro t ht
    change ∑ t' ∈ T with g t' = g t, c t' = c t
    rw [Finset.sum_eq_single t]
    · intro t' ht' hne
      exact absurd (hinjg (Finset.mem_filter.1 ht').1 ht (Finset.mem_filter.1 ht').2) hne
    · intro h; simp [ht] at h
  have hsum' : ∑ w ∈ T.image g, b w • fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ := by
    rwa [Finset.sum_image (fun t ht t' ht' h ↦ hinjg ht ht' h),
      Finset.sum_congr rfl fun t ht ↦ by rw [hb t ht]]
  intro t ht
  rw [← hb t ht]
  refine (hall ν.degree).2.2.2.1 Λ ν rfl (T.image g) ?_ ?_ ?_ b hsum' (g t)
    (Finset.mem_image_of_mem g ht)
  · intro w hw
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hw
    exact hgw t' ht'
  · intro w hw
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hw
    exact h0 t' ht'
  · intro w₁ hw₁ w₂ hw₂ hne
    obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.1 hw₁
    obtain ⟨t₂, ht₂, rfl⟩ := Finset.mem_image.1 hw₂
    exact hd t₁ ht₁ t₂ ht₂ fun h ↦ hne (h ▸ rfl)

include hR in
open scoped Classical in
/-- For `⟨j, μ⟩ ≫ 0`, `(f̃_a v_μ, f̃_b v_μ)_μ ≡ δ` modulo `ϖ` on words of weight `ν₀`, where
`δ = 1` iff `f̃_a 1 ≡ f̃_b 1` modulo `ϖ L(∞)`. -/
theorem exists_form_fW_fW (ν₀ : I →₀ ℕ) :
    ∃ m₀ : ℕ, ∀ Λ : Dom R, (∀ j, (m₀ : ℤ) ≤ Λ.1 (R.coroot j)) →
      ∀ a b : List I, wordWeight a = ν₀ → wordWeight b = ν₀ → ∃ t : A,
        IrreducibleModule.form Λ.1 hR (pow_ne_one_of_transcendental' hvt) (fW hvt hR Λ a)
          (fW hvt hR Λ b) =
        (if fWi (D := D) hvt a - fWi hvt b ∈ ϖ • latInf hvt A then 1 else 0) +
          algebraMap A k (ϖ * t) := by
  set hv' := pow_ne_one_of_transcendental' hvt
  obtain ⟨m₁, hm₁⟩ := exists_form_evq_sub_formU_large (hR := hR) hϖv hk ν₀
  obtain ⟨m₂, hm₂⟩ := exists_form_mem_of_large (hR := hR) hinj hϖ hϖv hk hfund ν₀
  refine ⟨m₁ + m₂, fun Λ hΛ a b ha hb ↦ ?_⟩
  have hΛ₁ : ∀ j, (m₁ : ℤ) ≤ Λ.1 (R.coroot j) := fun j ↦ by have := hΛ j; omega
  have hΛ₂ : ∀ j, (m₂ : ℤ) ≤ Λ.1 (R.coroot j) := fun j ↦ by have := hΛ j; omega
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  -- `π(f̃_a 1) = f̃_a v + ϖ xₐ`
  have hdec : ∀ c : List I, wordWeight c = ν₀ → ∃ x ∈ lat hvt hR A Λ, x ∈ wsp Λ ν₀ ∧
      evq hvt Λ (fWi hvt c) = fW hvt hR Λ c + ϖ • x := by
    intro c hc
    obtain ⟨x, hx, ex⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
      (evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund c Λ)
    refine ⟨x, hx, ?_, by rw [ex]; abel⟩
    have h := sub_mem (evq_mem_wsp (hvt := hvt) hR (hc ▸ fWi_mem_Uw (hvt := hvt) c) Λ)
      (hc ▸ fW_mem_wsp hvt hR Λ c)
    rw [← ex, ← algebraMap_smul k] at h
    have := Submodule.smul_mem _ (algebraMap A k ϖ)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hϖ0, one_smul] at this
  obtain ⟨xa, hxa, hxaw, ea⟩ := hdec a ha
  obtain ⟨xb, hxb, hxbw, eb⟩ := hdec b hb
  have hfa : fW hvt hR Λ a ∈ lat hvt hR A Λ := IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A a
  have hfb : fW hvt hR Λ b ∈ lat hvt hR A Λ := IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A b
  obtain ⟨c₁, hc₁⟩ := hm₂ Λ hΛ₂ xa hxa hxaw _ hfb
  obtain ⟨c₂, hc₂⟩ := hm₂ Λ hΛ₂ (fW hvt hR Λ a) hfa (ha ▸ fW_mem_wsp hvt hR Λ a) xb hxb
  obtain ⟨c₃, hc₃⟩ := hm₂ Λ hΛ₂ xa hxa hxaw xb hxb
  obtain ⟨d, hd⟩ := hm₁ Λ hΛ₁ _ (NegativePart.fWord_mem_latticeInf _ _ a)
    (ha ▸ fWi_mem_Uw (hvt := hvt) a) _ (NegativePart.fWord_mem_latticeInf _ _ b)
    (hb ▸ fWi_mem_Uw (hvt := hvt) b)
  obtain ⟨e, he⟩ := formU_fWi_fWi (hR := hR) (A := A) (D := D) hinj hϖ hϖv hk hfund a b
  refine ⟨d + e - c₁ - c₂ - ϖ * c₃, ?_⟩
  rw [← algebraMap_smul k] at ea eb
  rw [ea, eb] at hd
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hd
  rw [he] at hd
  rw [IrreducibleModule.form_comm hR hv' xa] at hc₁
  rw [IrreducibleModule.form_comm hR hv' xa (fW hvt hR Λ b)] at hd
  simp only [map_sub, map_add, map_mul] at hc₁ hc₂ hc₃ hd ⊢
  linear_combination hd - (algebraMap A k ϖ) * hc₁ - (algebraMap A k ϖ) * hc₂ -
    (algebraMap A k ϖ) * (algebraMap A k ϖ) * hc₃

include hR in
lemma tensorEmb_evq_mem_smul_LL (Λ₁ Λ₂ : Dom R) {u : Um D v} (hu : u ∈ ϖ • latInf hvt A) :
    tensorEmb hvt hR Λ₁.2 Λ₂.2 (evq hvt (Λ₁ + Λ₂) u) ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  obtain ⟨y, hy, ey⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
    (evq_mem_smul_lat (hR := hR) hinj hϖ hϖv hk hfund hu (Λ₁ + Λ₂))
  rw [← ey, ← algebraMap_smul k, LinearMap.map_smul_of_tower, algebraMap_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (tensorEmb_mem_LL hϖ hϖv (fun t ↦ (hall t).1) hy)


end Base

end GrandLoop

end LieLean.QuantumGroup
