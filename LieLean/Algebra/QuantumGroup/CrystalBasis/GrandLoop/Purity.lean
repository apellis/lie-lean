/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Dual

/-!
# Kashiwara's grand loop: `Ψ(L(λ₁) ⊗ v_{λ₂}) ⊆ L(λ₁ + λ₂)` for `λ₁` large

Let `S' : M ⊗ V(λ₂) → M`, `x ⊗ y ↦ (v_{λ₂}, y) x` (`GrandLoop.tensorTail`). It commutes with
`Fᵢ` up to the scalar `vᵢ^{-⟨i,λ₂⟩} ∈ ϖ^{dᵢ⟨i,λ₂⟩} A` (`tensorTail_F_smul`), so
`S'(Φ(y v_{λ₁+λ₂})) = ϖ^n y v_{λ₁}` for `y ∈ 'f_ν` (`tensorTail_tensorEmb_ev`), and
`(Ψ(x ⊗ v_{λ₂}), y v_{λ₁+λ₂}) = ϖ^n (y v_{λ₁}, x)`. With the stable dual lattices of
`GrandLoop.Dual` and `L^∨∨ = L` ([HK] Lemma 5.3.13) this gives
`Ψ(L(λ₁)_{λ₁-ν} ⊗ v_{λ₂}) ⊆ L(λ₁ + λ₂)` for `λ₁` large (`GrandLoop.tensorProj_tmul_hwv_mem`),
the main step of [HK] Lemma 5.3.15 (whose printed proof uses [HK] Exercise 5.13).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
-/

open Finset Pointwise LusztigF TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]

/-! ### The map `S'` -/

section Tail

variable (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (Λ₂ : Y →+ ℤ)
  {M : Type*} [AddCommGroup M] [Module k M]

/-- `S' : M ⊗ V(λ₂) → M`, `x ⊗ y ↦ (v_{λ₂}, y) x`. -/
def tensorTail : TensorModule k M (IrreducibleModule R v Λ₂) →ₗ[k] M :=
  TensorProduct.rid k M ∘ₗ
    TensorProduct.map LinearMap.id
      (IrreducibleModule.form Λ₂ hR hv' (IrreducibleModule.hwv R v Λ₂)) ∘ₗ
    (TensorModule.mk _ _).symm.toLinearMap

omit [CharZero k] in
lemma tensorTail_tmul (x : M) (y : IrreducibleModule R v Λ₂) :
    tensorTail hR hv' Λ₂ (TensorModule.mk _ _ (x ⊗ₜ y)) =
      IrreducibleModule.form Λ₂ hR hv' (IrreducibleModule.hwv R v Λ₂) y • x := by
  simp [tensorTail]

variable [Module (QuantumGroup R v) M] [IsScalarTower k (QuantumGroup R v) M]

omit [CharZero k] in
/-- `S'(Fᵢ z) = vᵢ^{-⟨i,λ₂⟩} Fᵢ S'(z)`. -/
theorem tensorTail_F_smul (i : I) (z : TensorModule k M (IrreducibleModule R v Λ₂)) :
    tensorTail hR hv' Λ₂ (F R v i • z) =
      v ^ Λ₂ (-ktilde R i) • F R v i • tensorTail hR hv' Λ₂ z := by
  obtain ⟨z, rfl⟩ := (TensorModule.mk M (IrreducibleModule R v Λ₂)).surjective z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    have h1 : IrreducibleModule.form Λ₂ hR hv' (IrreducibleModule.hwv R v Λ₂)
        (K R v (-ktilde R i) • y) =
        v ^ Λ₂ (-ktilde R i) *
          IrreducibleModule.form Λ₂ hR hv' (IrreducibleModule.hwv R v Λ₂) y := by
      rw [IrreducibleModule.form_comm, IrreducibleModule.isContravariant_form, rho_K,
        IrreducibleModule.hwv_mem_weightSpace, map_smul, smul_eq_mul,
        IrreducibleModule.form_comm]
    rw [TensorModule.F_smul_tmul, map_add, map_add, tensorTail_tmul, tensorTail_tmul,
      tensorTail_tmul, IrreducibleModule.form_hwv_F_smul, zero_smul, add_zero, h1, mul_smul,
      smul_comm (F R v i)]
  | add a b ha hb => rw [map_add, smul_add, map_add, ha, hb, map_add, smul_add, smul_add]

end Tail

/-! ### `S' ∘ Φ` on `ev` -/

section TailEmb

variable {hvt : Transcendental ℚ v} {hR : R.IsXRegular}

/-- The scalar of `S' ∘ Φ` on a word. -/
def tailCoef (Λ₂ : Y →+ ℤ) (w : List I) : k := (w.map fun j ↦ v ^ Λ₂ (-ktilde R j)).prod

omit [CharZero k] [NeZero v] [DecidableEq I] in
@[simp] lemma tailCoef_nil (Λ₂ : Y →+ ℤ) : tailCoef (R := R) (v := v) Λ₂ [] = 1 := rfl

omit [CharZero k] [NeZero v] [DecidableEq I] in
@[simp] lemma tailCoef_cons (Λ₂ : Y →+ ℤ) (j : I) (w : List I) :
    tailCoef (R := R) (v := v) Λ₂ (j :: w) = v ^ Λ₂ (-ktilde R j) *
      tailCoef (R := R) (v := v) Λ₂ w := rfl

/-- `S'(Φ(θ_w v_{λ₁+λ₂})) = c_w θ_w v_{λ₁}`. -/
lemma tensorTail_tensorEmb_ev_wordBasis [Finite I] (Λ₁ Λ₂ : Dom R) (w : List I) :
    tensorTail hR (pow_ne_one_of_transcendental' hvt) Λ₂.1
        (tensorEmb hvt hR Λ₁.2 Λ₂.2 (ev R v (Λ₁ + Λ₂).1 (FreeAlgebra.wordBasis k I w))) =
      tailCoef (R := R) (v := v) Λ₂.1 w • ev R v Λ₁.1 (FreeAlgebra.wordBasis k I w) := by
  induction w with
  | nil =>
    rw [FreeAlgebra.wordBasis_nil, ev_one, ev_one]
    erw [tensorEmb_hwv]
    rw [tensorTail_tmul, IrreducibleModule.form_hwv, one_smul, tailCoef_nil, one_smul]
  | cons j w ih =>
    rw [← FreeAlgebra.ι_mul_wordBasis, ev_ι_mul, ev_ι_mul, map_smul, tensorTail_F_smul, ih,
      tailCoef_cons, mul_smul, smul_comm (F R v j)]

omit [CharZero k] [NeZero v] [DecidableEq I] in
/-- `c_w = ϖ^{e(ν)}` for words of weight `ν`. -/
lemma tailCoef_eq {A : Type*} [CommRing A] [Algebra A k] {ϖ : A} (hϖv : algebraMap A k ϖ = v⁻¹)
    {Λ₂ : Y →+ ℤ} (hΛ₂ : ∀ i, 0 ≤ Λ₂ (R.coroot i)) (w : List I) :
    tailCoef (R := R) (v := v) Λ₂ w = algebraMap A k
      (ϖ ^ ((wordWeight w).sum fun i n ↦ n * (D.d i * (Λ₂ (R.coroot i)).toNat))) := by
  induction w with
  | nil => simp
  | cons j w ih =>
    rw [tailCoef_cons, ih, wordWeight_cons, Finsupp.sum_add_index' (by simp)
      (fun _ _ _ ↦ by ring), Finsupp.sum_single_index (by simp), pow_add, map_mul, one_mul]
    congr 1
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (hΛ₂ j)
    rw [ktilde, map_neg, map_nsmul, hn, Int.toNat_natCast, map_pow, hϖv, inv_pow,
      ← zpow_natCast, ← zpow_neg, nsmul_eq_mul]
    congr 1

/-- `S'(Φ(y v_{λ₁+λ₂})) = ϖ^{e(ν)} y v_{λ₁}` for `y ∈ 'f_ν`. -/
lemma tensorTail_tensorEmb_ev [Finite I] {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}
    (hϖv : algebraMap A k ϖ = v⁻¹) (Λ₁ Λ₂ : Dom R) {ν : I →₀ ℕ} {y : LusztigF k I}
    (hy : y ∈ LusztigF.weightSpace k ν) :
    tensorTail hR (pow_ne_one_of_transcendental' hvt) Λ₂.1
        (tensorEmb hvt hR Λ₁.2 Λ₂.2 (ev R v (Λ₁ + Λ₂).1 y)) =
      algebraMap A k (ϖ ^ (ν.sum fun i n ↦ n * (D.d i * (Λ₂.1 (R.coroot i)).toNat))) •
        ev R v Λ₁.1 y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [monomial_eq_wordBasis, tensorTail_tensorEmb_ev_wordBasis, tailCoef_eq hϖv Λ₂.2]
    rw [show wordWeight w = ν from hw]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb, map_add, smul_add]
  | smul c a _ ha => rw [map_smul, LinearMap.map_smul_of_tower, map_smul, ha, map_smul,
      smul_comm]

/-- `(z, x ⊗ v_{λ₂}) = (S' z, x)`. -/
lemma tensorForm_tmul_hwv (hvt : Transcendental ℚ v) (Λ₁ Λ₂ : Y →+ ℤ)
    (z : TensorModule k (IrreducibleModule R v Λ₁) (IrreducibleModule R v Λ₂))
    (x : IrreducibleModule R v Λ₁) :
    tensorForm hvt hR Λ₁ Λ₂ z (TensorModule.mk _ _ (x ⊗ₜ IrreducibleModule.hwv R v Λ₂)) =
      IrreducibleModule.form Λ₁ hR (pow_ne_one_of_transcendental' hvt)
        (tensorTail hR (pow_ne_one_of_transcendental' hvt) Λ₂ z) x := by
  obtain ⟨z, rfl⟩ := (TensorModule.mk _ _).surjective z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [TensorModule.form_tmul, tensorTail_tmul, map_smul, LinearMap.smul_apply, smul_eq_mul,
      IrreducibleModule.form_comm (x := b), mul_comm]
  | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, ha, hb, map_add, map_add,
      LinearMap.add_apply]

end TailEmb

/-! ### Dictionary with `U⁻_ν` -/

section Dictionary

variable {hvt : Transcendental ℚ v} {hR : R.IsXRegular}

lemma gF_apply (hR : R.IsXRegular) (Λ : Dom R) {ν : I →₀ ℕ} (x y : Uw D v ν) :
    gF R hvt Λ.1 ν x y = IrreducibleModule.form Λ.1 hR (pow_ne_one_of_transcendental' hvt)
      (evq hvt Λ x) (evq hvt Λ y) := by
  obtain ⟨_, P, hP, rfl⟩ := x
  obtain ⟨_, Q, hQ, rfl⟩ := y
  change VermaModule.shapF R _ Λ.1 P Q = _
  rw [VermaModule.shapF_apply]
  exact (IrreducibleModule.form_mk hR _ _ _).symm

/-- For `⟨i, λ⟩ ≥ |ν|`, `G_λ` is nondegenerate on `U⁻_ν`. -/
lemma nondegenerate_gF [Finite I] (hR : R.IsXRegular) {Λ : Dom R} {ν : I →₀ ℕ}
    (hΛ : ∀ i, (ν.degree : ℤ) ≤ Λ.1 (R.coroot i)) : (gF R hvt Λ.1 ν).Nondegenerate := by
  have hv' := pow_ne_one_of_transcendental' hvt
  have hB := IrreducibleModule.isGoodForm_form hR hv' Λ.2
  have hL : ∀ x : Uw D v ν, (∀ y, gF R hvt Λ.1 ν x y = 0) → x = 0 := by
    intro x hx
    refine evq_injective (hvt := hvt) (hR := hR) hΛ ?_
    rw [map_zero]
    refine hB.nondegenerate _ fun m' ↦ ?_
    have hm' : m' ∈ ⨆ Λ', weightSpace R v (IrreducibleModule R v Λ.1) Λ' := by
      rw [hB.isIntegrable.iSup_weightSpace_eq_top]; trivial
    have hxw : evq hvt Λ x ∈ wsp Λ ν := by
      obtain ⟨_, P, hP, rfl⟩ := x
      exact ev_mem_weightSpace hv' hR Λ.1 hP
    induction hm' using Submodule.iSup_induction' with
    | mem Λ' m' hm' =>
      by_cases h : Λ.1 - R.rootSum ν = Λ'
      · subst h
        rw [weightSpace_eq_map_ev hv' hR] at hm'
        obtain ⟨Q, hQ, rfl⟩ := hm'
        have := hx ⟨_, mk_mem_Uw hQ⟩
        rwa [gF_apply hR] at this
      · exact hB.isContravariant.eq_zero_of_ne h hxw hm' hv'
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  have hs : ∀ x y : Uw D v ν, gF R hvt Λ.1 ν x y = gF R hvt Λ.1 ν y x := fun x y ↦ by
    rw [gF_apply hR Λ x y, gF_apply hR Λ y x]
    exact hB.symm _ _
  exact ⟨hL, fun y h ↦ hL y fun x ↦ by rw [hs]; exact h x⟩

end Dictionary

/-! ### The main step of [HK] Lemma 5.3.15 -/

section Purity

variable {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k]
  {ϖ : A} (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
include hk

/-- **`Ψ(L(λ₁)_{λ₁-ν} ⊗ v_{λ₂}) ⊆ L(λ₁ + λ₂)` for `λ₁` large** (the main step of [HK]
Lemma 5.3.15, library order). -/
theorem tensorProj_tmul_hwv_mem [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
    (hinj : Function.Injective (algebraMap A k)) (hϖv : algebraMap A k ϖ = v⁻¹) {ν : I →₀ ℕ}
    (hA : ∀ s < ν.degree, PropA hvt hR A s) (hE : PropE hvt hR A ν.degree) (ρ : Dom R)
    (hρ : ∀ i, 1 ≤ ρ.1 (R.coroot i)) :
    ∃ Λs : Dom R, (∀ i, (ν.degree : ℤ) ≤ Λs.1 (R.coroot i)) ∧ ∀ Λ Λ₂ : Dom R,
      ∀ x ∈ lat hvt hR A (Λ + Λs), x ∈ wsp (Λ + Λs) ν →
        tensorProj hvt hR (Λ + Λs).2 Λ₂.2
          (TensorModule.mk _ _ (x ⊗ₜ[k] IrreducibleModule.hwv R v Λ₂.1)) ∈
          lat hvt hR A (Λ + Λs + Λ₂) := by
  classical
  have hv' := pow_ne_one_of_transcendental' hvt
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨Λs, hΛs, hst⟩ := exists_dual_stLat_eq hk hϖv hA hE ρ hρ
  refine ⟨Λs, hΛs, fun Λ Λ₂ x hx hxw ↦ ?_⟩
  set St := stLat hvt hR A Λs ν
  have eΓ : Λ + Λs + Λ₂ = (Λ + Λ₂) + Λs := Subtype.ext (by simp only [Dom.add_val]; abel)
  have hbig : ∀ (Λ' : Dom R) i, (ν.degree : ℤ) ≤ (Λ' + Λs).1 (R.coroot i) := fun Λ' i ↦ by
    have h1 := Λ'.2 i
    have h2 := hΛs i
    rw [Dom.add_val, AddMonoidHom.add_apply]
    omega
  have hΓ : ∀ i, (ν.degree : ℤ) ≤ (Λ + Λs + Λ₂).1 (R.coroot i) := by rw [eΓ]; exact hbig _
  have hStΓ : stLat hvt hR A (Λ + Λs + Λ₂) ν = St := by rw [eΓ]; exact (hst _).1
  have hStΛ₁ : stLat hvt hR A (Λ + Λs) ν = St := (hst Λ).1
  have hDΓ : DualLattice.dual (gF R hvt (Λ + Λs + Λ₂).1 ν) St =
      DualLattice.dual (g0 D hvt ν) St := by
    have := (hst (Λ + Λ₂)).2
    rwa [← eΓ] at this
  have hDΛ₁ : DualLattice.dual (gF R hvt (Λ + Λs).1 ν) St = DualLattice.dual (g0 D hvt ν) St :=
    (hst Λ).2
  -- `Ψ(x ⊗ v)` has weight `Γ - ν`
  have hzw : tensorProj hvt hR (Λ + Λs).2 Λ₂.2
      (TensorModule.mk _ _ (x ⊗ₜ[k] IrreducibleModule.hwv R v Λ₂.1)) ∈
      wsp (Λ + Λs + Λ₂) ν := by
    have h1 := TensorModule.tmul_mem_weightSpace hxw
      (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := v) (Λ := Λ₂.1))
    intro μ
    rw [← LinearMap.map_smul, h1 μ, LinearMap.map_smul_of_tower]
    congr 2
    simp only [Dom.add_val, AddMonoidHom.add_apply, AddMonoidHom.sub_apply]
    ring
  rw [wsp, weightSpace_eq_map_ev hv' hR] at hzw
  obtain ⟨P, hP, hPz⟩ := hzw
  set t : Uw D v ν := ⟨_, mk_mem_Uw hP⟩
  change evq hvt (Λ + Λs + Λ₂) t = _ at hPz
  suffices ht : t ∈ St by
    have : t ∈ stLat hvt hR A (Λ + Λs + Λ₂) ν := hStΓ ▸ ht
    rw [mem_stLat, hPz] at this
    exact this
  -- `St^∨∨ = St` for `G_Γ`
  have hfg : St.FG := stLat_fg hk hϖ0 hΛs
  have hspan : Submodule.span k (St : Set (Uw D v ν)) = ⊤ := by
    obtain ⟨C, hC⟩ := exists_pow_smul_mon_le (hvt := hvt) (hR := hR) hϖv hA
    refine eq_top_iff.2 ?_
    rw [← span_mon (D := D) (v := v) A ν]
    refine Submodule.span_le.2 fun y hy ↦ ?_
    have h1 : ϖ ^ C • y ∈ Submodule.span k (St : Set (Uw D v ν)) :=
      Submodule.subset_span (hC Λs y hy)
    have h2 := Submodule.smul_mem _ (algebraMap A k (ϖ ^ C))⁻¹ h1
    have e : (algebraMap A k (ϖ ^ C))⁻¹ • (ϖ ^ C • y) = y := by
      rw [← algebraMap_smul k (ϖ ^ C) y, smul_smul,
        inv_mul_cancel₀ (by rw [map_pow]; exact pow_ne_zero _ hϖ0), one_smul]
    rwa [e] at h2
  have hsymm : (gF R hvt (Λ + Λs + Λ₂).1 ν).IsSymm := ⟨fun x y ↦ by
    rw [gF_apply hR _ x y, gF_apply hR _ y x]
    exact IrreducibleModule.form_comm _ _ _ _⟩
  rw [← DualLattice.dual_dual_of_fg hk hinj hϖ0 (nondegenerate_gF hR hΓ) hsymm hfg hspan]
  intro s hs
  rw [hDΓ, ← hDΛ₁] at hs
  -- `G_Γ(t, s) = ϖ^n G_{λ₁}(s, s_x)`
  obtain ⟨_, S, hS, rfl⟩ := s
  have hxw' := hxw
  rw [wsp, weightSpace_eq_map_ev hv' hR] at hxw'
  obtain ⟨X, hX, rfl⟩ := hxw'
  have hsx : (⟨_, mk_mem_Uw hX⟩ : Uw D v ν) ∈ St := by
    rw [← hStΛ₁, mem_stLat]; exact hx
  obtain ⟨a, ha⟩ := hs _ hsx
  refine ⟨ϖ ^ (ν.sum fun i n ↦ n * (D.d i * (Λ₂.1 (R.coroot i)).toNat)) * a, ?_⟩
  rw [gF_apply hR, hPz]
  change _ = IrreducibleModule.form (Λ + Λs + Λ₂).1 hR hv' _ (ev R v (Λ + Λs + Λ₂).1 S)
  erw [form_tensorProj]
  rw [TensorModule.form_comm (IrreducibleModule.form_comm hR hv')
    (IrreducibleModule.form_comm hR hv'), tensorForm_tmul_hwv,
    tensorTail_tensorEmb_ev hϖv (Λ + Λs) Λ₂ hS, map_smul, LinearMap.smul_apply, smul_eq_mul,
    map_mul, ha, gF_apply hR]
  all_goals first | rfl | exact hvt

end Purity

end GrandLoop

end LieLean.QuantumGroup
