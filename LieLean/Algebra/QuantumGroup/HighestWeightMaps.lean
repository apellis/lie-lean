/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ContravariantForm
import LieLean.Algebra.QuantumGroup.Character
import LieLean.Algebra.QuantumGroup.CrystalBasis.Integrable

/-!
# Maps out of highest weight modules and adjoints

Let `U = U_q(𝔤)` (`QuantumGroup R v`), `v` not a root of unity.

* **Universal properties.** A vector `w` of a `U`-module with `Eᵢ w = 0` and `K_μ w = v^{⟨μ, Λ⟩} w`
  defines a `U`-linear map `M_q(Λ) → N`, `v_Λ ↦ w` (`QuantumGroup.VermaModule.lift`). If moreover
  `Fᵢ^{⟨i,Λ⟩+1} w = 0` for all `i` (which holds automatically for `Λ` dominant and `N`
  integrable, `QuantumGroup.F_pow_smul_eq_zero_of_primitive`), it factors through `L̃_q(Λ)`,
  hence (for `v` transcendental over `ℚ`, `L̃_q(Λ) ≅ L_q(Λ)`) through `L_q(Λ)`
  (`QuantumGroup.IrreducibleModule.lift`).
* **Adjoints.** If `M` is an integrable module with finite-dimensional weight spaces and a
  nondegenerate symmetric contravariant form, and `N` an integrable module with a contravariant
  form, then every `U`-linear `Φ : M → N` has a `U`-linear adjoint `Ψ : N → M`,
  `(Ψ n, m) = (n, Φ m)` (`QuantumGroup.adjoint`), constructed weight space by weight space.

These are the maps `Φ_{λ,μ} : V(λ+μ) → V(λ) ⊗ V(μ)` and `Ψ_{λ,μ} = Φ_{λ,μ}^*` of Kashiwara's
grand loop ([HK] §5.3, (5.6)–(5.8)), constructed in `QuantumGroup.tensorEmb`,
`QuantumGroup.tensorProj` with `Ψ ∘ Φ = 1` (`QuantumGroup.tensorProj_tensorEmb`), together with
the `Fᵢ`-equivariant map `S : L_q(Λ₁) ⊗ M → M`, `x ⊗ y ↦ (v_{Λ₁}, x) y` (`QuantumGroup.tensorHead`).
The arguments are standard; the formulation is ours.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 5.5, 9.20.
-/

open LieLean TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]

/-! ### Universal properties -/

section Lift

variable {N : Type*} [AddCommGroup N] [Module k N] [Module (QuantumGroup R v) N]
  [IsScalarTower k (QuantumGroup R v) N]

namespace VermaModule

variable {Λ : Y →+ ℤ} (w : N) (hE : ∀ i, E R v i • w = 0)
  (hK : ∀ μ, K R v μ • w = v ^ Λ μ • w)
include hE hK

omit [NeZero v] in
lemma vermaIdeal_le_ker :
    vermaIdeal R v Λ ≤ LinearMap.ker (LinearMap.toSpanSingleton (QuantumGroup R v) N w) := by
  rw [vermaIdeal, Submodule.span_le]
  rintro _ (⟨i, rfl⟩ | ⟨μ, rfl⟩)
  · simp [hE i]
  · simp [sub_smul, hK μ, algebraMap_smul]

/-- The universal property of `M_q(Λ)`: `v_Λ ↦ w` for `w` primitive of weight `Λ`. -/
def lift : VermaModule R v Λ →ₗ[QuantumGroup R v] N :=
  (vermaIdeal R v Λ).liftQ (LinearMap.toSpanSingleton _ N w) (vermaIdeal_le_ker w hE hK)

omit [NeZero v] in
@[simp] lemma lift_mk (u : QuantumGroup R v) :
    lift w hE hK (Submodule.Quotient.mk u) = u • w := rfl

omit [NeZero v] in
@[simp] lemma lift_hwv : lift w hE hK (hwv R v Λ) = w := by
  simp [hwv]

end VermaModule

variable {Λ : Y →+ ℤ}

/-- For `Λ` dominant and `N` integrable, a primitive vector of weight `Λ` is killed by
`Fᵢ^{⟨i,Λ⟩+1}`. -/
theorem F_pow_smul_eq_zero_of_primitive (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    (hN : IsIntegrable R v N) {w : N} (hw : w ∈ weightSpace R v N Λ)
    (hE : ∀ i, E R v i • w = 0) (i : I) : F R v i ^ ((Λ (R.coroot i)).toNat + 1) • w = 0 := by
  set V := nodeSl2 R v N hv' hN i
  have hwt : w ∈ V.wt (Λ (R.coroot i)) := mem_nodeWt_of_mem hw
  by_cases hΛ : 0 ≤ Λ (R.coroot i)
  · have h0 := IntegrableSl2.dF_eq_zero_of_primitive (V := V) (pow_d_ne_zero i)
      (pow_d_ne_one hv' i) hwt (hE i) (b := (Λ (R.coroot i)).toNat + 1)
      (by push_cast; omega)
    rw [IntegrableSl2.dF_apply, smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact absurd h0 (inv_ne_zero (qFactorial_ne_zero_of_pow_ne_one
        (pow_d_ne_zero i) (pow_d_ne_one hv' i) _))
    · have : ∀ n : ℕ, (V.F ^ n) w = F R v i ^ n • w := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, nodeSl2_F,
            Algebra.lsmul_apply, ← mul_smul, ← pow_succ']
      rw [← this]; exact h0
  · have h0 := IntegrableSl2.eq_zero_of_primitive_of_neg (V := V) (pow_d_ne_zero i)
      (pow_d_ne_one hv' i) hwt (hE i) (by omega)
    rw [h0, smul_zero]

namespace IrreducibleModule

variable [Finite I] [CharZero k] (hvt : Transcendental ℚ v) (hR : R.IsXRegular)
  (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hΛ : ∀ i, 0 ≤ Λ (R.coroot i))
  (hN : IsIntegrable R v N) (w : N) (hw : w ∈ weightSpace R v N Λ) (hE : ∀ i, E R v i • w = 0)

/-- The universal property of `L_q(Λ)` for `Λ` dominant: `v_Λ ↦ w` for a primitive vector `w` of
weight `Λ` in an integrable module (`v` transcendental over `ℚ`, so that `L̃_q(Λ) ≅ L_q(Λ)`). -/
def lift : IrreducibleModule R v Λ →ₗ[QuantumGroup R v] N :=
  (VermaModule.fPowSubmodule R v Λ).liftQ (VermaModule.lift w hE (mem_weightSpace.1 hw))
      (by
        rw [VermaModule.fPowSubmodule, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.map_smul, VermaModule.lift_hwv]
        exact F_pow_smul_eq_zero_of_primitive hv' hN hw hE i) ∘ₗ
    (FPowQuotient.equivIrreducibleModule hvt hR hv' hΛ).symm.toLinearMap

@[simp] lemma lift_hwv : lift hvt hR hv' hΛ hN w hw hE (hwv R v Λ) = w := by
  have : (FPowQuotient.equivIrreducibleModule hvt hR hv' hΛ).symm (hwv R v Λ) =
      Submodule.Quotient.mk (VermaModule.hwv R v Λ) := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp [lift, this]

end IrreducibleModule

end Lift

/-! ### Adjoints -/

section Adjoint

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  {M N : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] [AddCommGroup N] [Module k N]
  [Module (QuantumGroup R v) N] [IsScalarTower k (QuantumGroup R v) N]

/-- A nondegenerate symmetric contravariant form on an integrable module with finite-dimensional
weight spaces. -/
structure IsGoodForm (B : LinearMap.BilinForm k M) : Prop where
  isIntegrable : IsIntegrable R v M
  finiteDimensional : ∀ Λ, FiniteDimensional k (weightSpace R v M Λ)
  isContravariant : IsContravariant R v B
  symm : ∀ m m', B m m' = B m' m
  nondegenerate : ∀ m, (∀ m', B m m' = 0) → m = 0

variable {hv'} {BM : LinearMap.BilinForm k M} (hB : IsGoodForm (R := R) (v := v) BM)
  {BN : LinearMap.BilinForm k N} (hN : IsIntegrable R v N) (hBN : IsContravariant R v BN)
  (Φ : M →ₗ[QuantumGroup R v] N)

include hv' hB in
/-- A nondegenerate symmetric contravariant form is nondegenerate on each weight space. -/
lemma IsGoodForm.nondegenerate_restrict (Λ : Y →+ ℤ) :
    (BM.restrict (weightSpace R v M Λ)).Nondegenerate := by
  have key : ∀ x : weightSpace R v M Λ, (∀ y : weightSpace R v M Λ, BM x y = 0) → x = 0 := by
    intro x hx
    refine Subtype.ext (hB.nondegenerate _ fun m' ↦ ?_)
    have hm' : m' ∈ ⨆ Λ', weightSpace R v M Λ' := by
      rw [hB.isIntegrable.iSup_weightSpace_eq_top]; trivial
    induction hm' using Submodule.iSup_induction' with
    | mem Λ' m' hm' =>
      by_cases h : Λ = Λ'
      · subst h; exact hx ⟨m', hm'⟩
      · exact hB.isContravariant.eq_zero_of_ne h x.2 hm' hv'
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  exact ⟨fun x hx ↦ key x hx, fun y hy ↦ key y fun x ↦ by rw [hB.symm]; exact hy x⟩

variable (hv') in
/-- The adjoint on one weight space: `n ↦ Ψ n ∈ M^Λ` with `(Ψ n, m) = (n, Φ m)` for `m ∈ M^Λ`. -/
def adjointWeight (BN : LinearMap.BilinForm k N) (Λ : Y →+ ℤ) : weightSpace R v N Λ →ₗ[k] M :=
  haveI := hB.finiteDimensional Λ
  (weightSpace R v M Λ).subtype ∘ₗ
    ((BM.restrict (weightSpace R v M Λ)).toDual
      (hB.nondegenerate_restrict (hv' := hv') Λ)).symm.toLinearMap ∘ₗ
    (BN.compl₂ ((Φ.restrictScalars k) ∘ₗ (weightSpace R v M Λ).subtype)) ∘ₗ
    (weightSpace R v N Λ).subtype

lemma adjointWeight_mem (Λ : Y →+ ℤ) (n : weightSpace R v N Λ) :
    adjointWeight hv' hB Φ BN Λ n ∈ weightSpace R v M Λ := by
  simp [adjointWeight]

lemma form_adjointWeight (Λ : Y →+ ℤ) (n : weightSpace R v N Λ) {m : M}
    (hm : m ∈ weightSpace R v M Λ) : BM (adjointWeight hv' hB Φ BN Λ n) m = BN n (Φ m) := by
  have := hB.finiteDimensional Λ
  have := LinearMap.BilinForm.apply_toDual_symm_apply
    (hB := hB.nondegenerate_restrict (hv' := hv') Λ)
    ((BN.compl₂ ((Φ.restrictScalars k) ∘ₗ (weightSpace R v M Λ).subtype)) n) ⟨m, hm⟩
  simpa [adjointWeight] using this

variable (hv') in
open scoped Classical in
/-- The adjoint of `Φ : M → N`: `(Ψ n, m) = (n, Φ m)`. -/
def adjoint (BN : LinearMap.BilinForm k N) : N →ₗ[k] M :=
  DirectSum.toModule k (Y →+ ℤ) M (adjointWeight hv' hB Φ BN) ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap (weightSpace R v N))
      (isInternal_weightSpace hv' hN)).symm.toLinearMap

lemma adjoint_of_mem {Λ : Y →+ ℤ} {n : N} (hn : n ∈ weightSpace R v N Λ) :
    adjoint hv' hB hN Φ BN n = adjointWeight hv' hB Φ BN Λ ⟨n, hn⟩ := by
  classical
  have h : (LinearEquiv.ofBijective (DirectSum.coeLinearMap (weightSpace R v N))
      (isInternal_weightSpace hv' hN)).symm n =
      DirectSum.of (fun Λ ↦ weightSpace R v N Λ) Λ ⟨n, hn⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact (DirectSum.coeLinearMap_of (A := weightSpace R v N) Λ ⟨n, hn⟩).symm
  simp only [adjoint, LinearMap.comp_apply, LinearEquiv.coe_coe, h]
  exact DirectSum.toModule_lof k Λ _

include hBN in
/-- **The adjoint property** `(Ψ n, m) = (n, Φ m)`. -/
theorem form_adjoint (n : N) (m : M) : BM (adjoint hv' hB hN Φ BN n) m = BN n (Φ m) := by
  have hn : n ∈ ⨆ Λ, weightSpace R v N Λ := by rw [hN.iSup_weightSpace_eq_top]; trivial
  induction hn using Submodule.iSup_induction' with
  | mem Λ n hn =>
    have hm : m ∈ ⨆ Λ', weightSpace R v M Λ' := by
      rw [hB.isIntegrable.iSup_weightSpace_eq_top]; trivial
    induction hm using Submodule.iSup_induction' with
    | mem Λ' m hm =>
      rw [adjoint_of_mem hB hN Φ hn]
      by_cases h : Λ = Λ'
      · subst h; exact form_adjointWeight hB Φ Λ _ hm
      · rw [hB.isContravariant.eq_zero_of_ne h (adjointWeight_mem hB Φ Λ _) hm hv',
          hBN.eq_zero_of_ne h hn (map_mem_weightSpace Φ hm) hv']
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, LinearMap.add_apply, ha, hb, map_add,
      LinearMap.add_apply]

include hBN in
/-- The adjoint is `U`-linear. -/
theorem adjoint_smul (u : QuantumGroup R v) (n : N) :
    adjoint hv' hB hN Φ BN (u • n) = u • adjoint hv' hB hN Φ BN n := by
  rw [← sub_eq_zero]
  refine hB.nondegenerate _ fun m ↦ ?_
  rw [map_sub, LinearMap.sub_apply, form_adjoint hB hN hBN, hBN, ← map_smul,
    hB.isContravariant, form_adjoint hB hN hBN, sub_self]

variable (hv') in
/-- The adjoint as a `U`-module map. -/
def adjointHom : N →ₗ[QuantumGroup R v] M where
  toFun := adjoint hv' hB hN Φ BN
  map_add' := map_add _
  map_smul' := adjoint_smul hB hN hBN Φ

@[simp] lemma adjointHom_apply (n : N) :
    adjointHom hv' hB hN hBN Φ n = adjoint hv' hB hN Φ BN n := rfl

end Adjoint

/-! ### Weight spaces of quotients -/

section Quotient

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

/-- The weight spaces of a quotient of a weight module are the images of the weight spaces (`v` not
a root of unity). -/
theorem weightSpace_quotient_le_map (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    (hM : ⨆ Λ, weightSpace R v M Λ = ⊤) (P : Submodule (QuantumGroup R v) M) (Λ : Y →+ ℤ) :
    weightSpace R v (M ⧸ P) Λ ≤ (weightSpace R v M Λ).map (P.mkQ.restrictScalars k) := by
  intro x hx
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hm : m ∈ weightSpace R v M Λ ⊔ ⨆ (μ : Y →+ ℤ) (_ : μ ≠ Λ), weightSpace R v M μ := by
    have : ⊤ ≤ weightSpace R v M Λ ⊔ ⨆ (μ : Y →+ ℤ) (_ : μ ≠ Λ), weightSpace R v M μ := by
      rw [← hM]
      refine iSup_le fun μ ↦ ?_
      by_cases h : μ = Λ
      · subst h; exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le μ h le_rfl)
    exact this Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hm
  have hb' : (Submodule.Quotient.mk b : M ⧸ P) ∈
      ⨆ (μ : Y →+ ℤ) (_ : μ ≠ Λ), weightSpace R v (M ⧸ P) μ := by
    clear hx ha hm
    induction hb using Submodule.iSup_induction' with
    | mem μ b hb =>
      induction hb using Submodule.iSup_induction' with
      | mem hμ b hb =>
        refine Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ fun ν ↦ ?_)
        rw [← Submodule.Quotient.mk_smul, hb ν, Submodule.Quotient.mk_smul]
      | zero => simp
      | add x y _ _ hx hy => rw [Submodule.Quotient.mk_add]; exact add_mem hx hy
    | zero => simp
    | add x y _ _ hx hy => rw [Submodule.Quotient.mk_add]; exact add_mem hx hy
  have ha' : (Submodule.Quotient.mk a : M ⧸ P) ∈ weightSpace R v (M ⧸ P) Λ := fun ν ↦ by
    rw [← Submodule.Quotient.mk_smul, ha ν, Submodule.Quotient.mk_smul]
  have hb0 : (Submodule.Quotient.mk b : M ⧸ P) = 0 := by
    have hbΛ : (Submodule.Quotient.mk b : M ⧸ P) ∈ weightSpace R v (M ⧸ P) Λ := by
      have := sub_mem hx ha'
      rwa [Submodule.Quotient.mk_add, add_sub_cancel_left] at this
    exact (Submodule.disjoint_def.1 (iSupIndep_weightSpace hv' Λ)) _ hbΛ hb'
  refine ⟨a, ha, ?_⟩
  change Submodule.Quotient.mk a = _
  rw [Submodule.Quotient.mk_add, hb0, add_zero]

end Quotient

/-! ### `L_q(Λ)`: finite-dimensional weight spaces and the good form -/

namespace IrreducibleModule

variable (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {Λ : Y →+ ℤ}

include hR hv' in
/-- The weight spaces of `L_q(Λ)` are finite-dimensional. -/
theorem finiteDimensional_weightSpace (Λ' : Y →+ ℤ) :
    FiniteDimensional k (weightSpace R v (IrreducibleModule R v Λ) Λ') := by
  have hle := weightSpace_quotient_le_map hv' VermaModule.iSup_weightSpace_eq_top
    (VermaModule.maxSubmodule R v Λ) Λ'
  by_cases h : ∃ ν, Λ' = Λ - R.rootSum ν
  · obtain ⟨ν, rfl⟩ := h
    have := VermaModule.finiteDimensional_weightSpace (Λ := Λ) hv' hR ν
    exact Submodule.finiteDimensional_of_le hle
  · push Not at h
    rw [VermaModule.weightSpace_eq_bot hv' h, Submodule.map_bot] at hle
    rw [le_bot_iff.1 hle]
    infer_instance

omit [NeZero v] in
lemma E_smul_hwv (i : I) : E R v i • hwv R v Λ = 0 := by
  rw [hwv, ← Submodule.Quotient.mk_smul, VermaModule.E_smul_hwv, Submodule.Quotient.mk_zero]

omit [NeZero v] in
lemma hwv_mem_weightSpace : hwv R v Λ ∈ weightSpace R v (IrreducibleModule R v Λ) Λ := fun μ ↦ by
  rw [hwv, ← Submodule.Quotient.mk_smul, VermaModule.K_smul_hwv, Submodule.Quotient.mk_smul]

include hR hv' in
/-- For `Λ` dominant, the contravariant form of `L_q(Λ)` is a good form. -/
theorem isGoodForm_form (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) :
    IsGoodForm (R := R) (v := v) (form Λ hR hv') where
  isIntegrable := IrreducibleModule.isIntegrable hR hv' hΛ
  finiteDimensional := finiteDimensional_weightSpace hR hv'
  isContravariant := isContravariant_form hR hv'
  symm := form_comm hR hv'
  nondegenerate _ h := eq_zero_of_form_eq_zero hR hv' h

end IrreducibleModule

/-! ### The maps `Φ`, `Ψ` and `S` -/

section TensorMaps

variable [Finite I] [CharZero k] (hvt : Transcendental ℚ v) (hR : R.IsXRegular)
  {Λ₁ Λ₂ : Y →+ ℤ} (hΛ₁ : ∀ i, 0 ≤ Λ₁ (R.coroot i)) (hΛ₂ : ∀ i, 0 ≤ Λ₂ (R.coroot i))

omit [NeZero v] [Finite I] in
lemma pow_ne_one_of_transcendental' (hvt : Transcendental ℚ v) : ∀ n : ℕ, 0 < n → v ^ n ≠ 1 :=
  fun _ hn ↦ LusztigF.pow_ne_one_of_transcendental hvt hn

open IrreducibleModule TensorModule in
include hvt hR hΛ₁ hΛ₂ in
/-- `Φ_{Λ₁,Λ₂} : L_q(Λ₁ + Λ₂) → L_q(Λ₁) ⊗ L_q(Λ₂)`, `v_{Λ₁+Λ₂} ↦ v_{Λ₁} ⊗ v_{Λ₂}`
([HK] (5.6)). -/
def tensorEmb : IrreducibleModule R v (Λ₁ + Λ₂) →ₗ[QuantumGroup R v]
    TensorModule k (IrreducibleModule R v Λ₁) (IrreducibleModule R v Λ₂) :=
  IrreducibleModule.lift hvt hR (pow_ne_one_of_transcendental' hvt)
    (fun i ↦ by rw [AddMonoidHom.add_apply]; exact add_nonneg (hΛ₁ i) (hΛ₂ i))
    (TensorModule.isIntegrable
      (IrreducibleModule.isIntegrable hR (pow_ne_one_of_transcendental' hvt) hΛ₁)
      (IrreducibleModule.isIntegrable hR (pow_ne_one_of_transcendental' hvt) hΛ₂))
    (mk _ _ (hwv R v Λ₁ ⊗ₜ hwv R v Λ₂))
    (tmul_mem_weightSpace hwv_mem_weightSpace hwv_mem_weightSpace)
    (fun i ↦ by rw [E_smul_tmul, E_smul_hwv, E_smul_hwv, zero_tmul, tmul_zero, add_zero,
      map_zero])

@[simp] lemma tensorEmb_hwv :
    tensorEmb hvt hR hΛ₁ hΛ₂ (IrreducibleModule.hwv R v (Λ₁ + Λ₂)) =
      TensorModule.mk _ _ (IrreducibleModule.hwv R v Λ₁ ⊗ₜ IrreducibleModule.hwv R v Λ₂) :=
  IrreducibleModule.lift_hwv _ _ _ _ _ _ _ _

/-- The contravariant form on `L_q(Λ₁) ⊗ L_q(Λ₂)`. -/
abbrev tensorForm (hvt : Transcendental ℚ v) (hR : R.IsXRegular) (Λ₁ Λ₂ : Y →+ ℤ) :
    LinearMap.BilinForm k (TensorModule k (IrreducibleModule R v Λ₁) (IrreducibleModule R v Λ₂)) :=
  TensorModule.form (IrreducibleModule.form Λ₁ hR (pow_ne_one_of_transcendental' hvt))
    (IrreducibleModule.form Λ₂ hR (pow_ne_one_of_transcendental' hvt))

omit [Finite I] in
lemma isContravariant_tensorForm : IsContravariant R v (tensorForm hvt hR Λ₁ Λ₂) :=
  TensorModule.isContravariant_form (IrreducibleModule.isContravariant_form _ _)
    (IrreducibleModule.isContravariant_form _ _)

/-- `Φ` is an isometry ([HK] (5.8), [Jan] 9.20 (c)). -/
theorem tensorForm_tensorEmb (x y : IrreducibleModule R v (Λ₁ + Λ₂)) :
    tensorForm hvt hR Λ₁ Λ₂ (tensorEmb hvt hR hΛ₁ hΛ₂ x) (tensorEmb hvt hR hΛ₁ hΛ₂ y) =
      IrreducibleModule.form (Λ₁ + Λ₂) hR (pow_ne_one_of_transcendental' hvt) x y := by
  have hB : IsContravariant R v ((tensorForm hvt hR Λ₁ Λ₂).compl₁₂
      ((tensorEmb hvt hR hΛ₁ hΛ₂).restrictScalars k)
      ((tensorEmb hvt hR hΛ₁ hΛ₂).restrictScalars k)) := by
    intro u a b
    simp only [LinearMap.compl₁₂_apply, LinearMap.coe_restrictScalars, map_smul]
    exact isContravariant_tensorForm hvt hR u _ _
  have := IrreducibleModule.eq_smul_form_of_isContravariant hR
    (pow_ne_one_of_transcendental' hvt) hB x y
  simp only [LinearMap.compl₁₂_apply, LinearMap.coe_restrictScalars, tensorEmb_hwv,
    TensorModule.form_tmul, IrreducibleModule.form_hwv, mul_one, one_mul] at this
  exact this

include hvt hR hΛ₁ hΛ₂ in
/-- `Ψ_{Λ₁,Λ₂} : L_q(Λ₁) ⊗ L_q(Λ₂) → L_q(Λ₁ + Λ₂)`, the adjoint of `Φ_{Λ₁,Λ₂}` ([HK] (5.6),
(5.8)). -/
def tensorProj :
    TensorModule k (IrreducibleModule R v Λ₁) (IrreducibleModule R v Λ₂) →ₗ[QuantumGroup R v]
      IrreducibleModule R v (Λ₁ + Λ₂) :=
  adjointHom (pow_ne_one_of_transcendental' hvt)
    (IrreducibleModule.isGoodForm_form hR (pow_ne_one_of_transcendental' hvt)
      (fun i ↦ by rw [AddMonoidHom.add_apply]; exact add_nonneg (hΛ₁ i) (hΛ₂ i)))
    (TensorModule.isIntegrable
      (IrreducibleModule.isIntegrable hR (pow_ne_one_of_transcendental' hvt) hΛ₁)
      (IrreducibleModule.isIntegrable hR (pow_ne_one_of_transcendental' hvt) hΛ₂))
    (isContravariant_tensorForm hvt hR) (tensorEmb hvt hR hΛ₁ hΛ₂)

/-- `(Ψ z, x) = (z, Φ x)`. -/
theorem form_tensorProj (z : TensorModule k (IrreducibleModule R v Λ₁) (IrreducibleModule R v Λ₂))
    (x : IrreducibleModule R v (Λ₁ + Λ₂)) :
    IrreducibleModule.form (Λ₁ + Λ₂) hR (pow_ne_one_of_transcendental' hvt)
      (tensorProj hvt hR hΛ₁ hΛ₂ z) x = tensorForm hvt hR Λ₁ Λ₂ z (tensorEmb hvt hR hΛ₁ hΛ₂ x) :=
  form_adjoint (IrreducibleModule.isGoodForm_form hR (pow_ne_one_of_transcendental' hvt)
      (fun i ↦ by rw [AddMonoidHom.add_apply]; exact add_nonneg (hΛ₁ i) (hΛ₂ i)))
    (TensorModule.isIntegrable
      (IrreducibleModule.isIntegrable hR (pow_ne_one_of_transcendental' hvt) hΛ₁)
      (IrreducibleModule.isIntegrable hR (pow_ne_one_of_transcendental' hvt) hΛ₂))
    (isContravariant_tensorForm hvt hR) (tensorEmb hvt hR hΛ₁ hΛ₂) z x

/-- `Ψ ∘ Φ = 1` ([HK] (5.7)). -/
theorem tensorProj_tensorEmb (x : IrreducibleModule R v (Λ₁ + Λ₂)) :
    tensorProj hvt hR hΛ₁ hΛ₂ (tensorEmb hvt hR hΛ₁ hΛ₂ x) = x := by
  rw [← sub_eq_zero]
  refine IrreducibleModule.eq_zero_of_form_eq_zero hR (pow_ne_one_of_transcendental' hvt)
    fun y ↦ ?_
  rw [map_sub, LinearMap.sub_apply, form_tensorProj, tensorForm_tensorEmb, sub_self]

end TensorMaps

/-! ### The map `S` -/

section TensorHead

variable (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (Λ₁ : Y →+ ℤ)
  {M : Type*} [AddCommGroup M] [Module k M]

omit [NeZero v] in
lemma rhoF_smul_hwv (i : I) : rhoF R v i • IrreducibleModule.hwv R v Λ₁ = 0 := by
  rw [rhoF, smul_assoc, mul_smul, IrreducibleModule.E_smul_hwv, smul_zero, smul_zero]

/-- `(v_Λ, Fᵢ x) = 0` in `L_q(Λ)`. -/
lemma IrreducibleModule.form_hwv_F_smul (i : I) (x : IrreducibleModule R v Λ₁) :
    IrreducibleModule.form Λ₁ hR hv' (IrreducibleModule.hwv R v Λ₁) (F R v i • x) = 0 := by
  rw [IrreducibleModule.form_comm, IrreducibleModule.isContravariant_form, rho_F,
    rhoF_smul_hwv, map_zero]

/-- `S : L_q(Λ₁) ⊗ M → M`, `x ⊗ y ↦ (v_{Λ₁}, x) y`: projection onto the highest weight component of
the first factor (cf. [HK] §5.3). It commutes with the `Fᵢ` (`tensorHead_F_smul`). -/
def tensorHead : TensorModule k (IrreducibleModule R v Λ₁) M →ₗ[k] M :=
  TensorProduct.lid k M ∘ₗ
    TensorProduct.map (IrreducibleModule.form Λ₁ hR hv' (IrreducibleModule.hwv R v Λ₁))
      LinearMap.id ∘ₗ (TensorModule.mk _ _).symm.toLinearMap

lemma tensorHead_tmul (x : IrreducibleModule R v Λ₁) (y : M) :
    tensorHead hR hv' Λ₁ (TensorModule.mk _ _ (x ⊗ₜ y)) =
      IrreducibleModule.form Λ₁ hR hv' (IrreducibleModule.hwv R v Λ₁) x • y := by
  simp [tensorHead]

variable [Module (QuantumGroup R v) M] [IsScalarTower k (QuantumGroup R v) M]

/-- `S` commutes with the `Fᵢ`. -/
theorem tensorHead_F_smul (i : I) (z : TensorModule k (IrreducibleModule R v Λ₁) M) :
    tensorHead hR hv' Λ₁ (F R v i • z) = F R v i • tensorHead hR hv' Λ₁ z := by
  obtain ⟨z, rfl⟩ := (TensorModule.mk (IrreducibleModule R v Λ₁) M).surjective z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorModule.F_smul_tmul, map_add, map_add, tensorHead_tmul, tensorHead_tmul,
      tensorHead_tmul, IrreducibleModule.form_hwv_F_smul, zero_smul, zero_add, smul_comm]
  | add a b ha hb => rw [map_add, smul_add, map_add, ha, hb, map_add, smul_add]

end TensorHead

section TensorHeadEmb

variable [Finite I] [CharZero k] (hvt : Transcendental ℚ v) (hR : R.IsXRegular)
  {Λ₁ Λ₂ : Y →+ ℤ} (hΛ₁ : ∀ i, 0 ≤ Λ₁ (R.coroot i)) (hΛ₂ : ∀ i, 0 ≤ Λ₂ (R.coroot i))

/-- `S ∘ Φ` sends `v_{Λ₁+Λ₂}` to `v_{Λ₂}`. -/
lemma tensorHead_tensorEmb_hwv :
    tensorHead hR (pow_ne_one_of_transcendental' hvt) Λ₁
      (tensorEmb hvt hR hΛ₁ hΛ₂ (IrreducibleModule.hwv R v (Λ₁ + Λ₂))) =
      IrreducibleModule.hwv R v Λ₂ := by
  rw [tensorEmb_hwv, tensorHead_tmul, IrreducibleModule.form_hwv, one_smul]

/-- `S ∘ Φ` commutes with the `Fᵢ`. -/
lemma tensorHead_tensorEmb_F_smul (i : I) (x : IrreducibleModule R v (Λ₁ + Λ₂)) :
    tensorHead hR (pow_ne_one_of_transcendental' hvt) Λ₁ (tensorEmb hvt hR hΛ₁ hΛ₂ (F R v i • x)) =
      F R v i • tensorHead hR (pow_ne_one_of_transcendental' hvt) Λ₁
        (tensorEmb hvt hR hΛ₁ hΛ₂ x) := by
  rw [map_smul, tensorHead_F_smul]

end TensorHeadEmb

end LieLean.QuantumGroup
