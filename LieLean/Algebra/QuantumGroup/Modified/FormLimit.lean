/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Faithful
import LieLean.Algebra.QuantumGroup.Modified.FormOmega
import LieLean.Algebra.QuantumGroup.ShapovalovLimit

/-!
# The inner product on `U̇` as a limit

For `Λ, Λ' : Y →+ ℤ` consider the `U`-module `ʷL_q(Λ) ⊗ L_q(Λ')`, where `ʷL_q(Λ)` is `L_q(Λ)`
with `u` acting as `ω(u)` (`QuantumGroup.ChevalleyTwist`), and the bilinear form
`(x ⊗ x', y ⊗ y') = (x, y)_Λ (x', y')_{Λ'}` on it ([Lus] 26.2.1,
`QuantumGroup.IrreducibleModule.tensorForm`).

## Main results

* `QuantumGroup.ChevalleyTwist.isContravariant_form`: a contravariant form on `M` is
  contravariant on `ʷM`, since `ω ρ = ρ ω`.
* `QuantumGroup.IrreducibleModule.isContravariant_tensorForm`: [Lus] Lemma 26.2.2,
  `(u X, X') = (X, ρ(u) X')` on `ʷL_q(Λ) ⊗ L_q(Λ')`.
* `QuantumGroup.IrreducibleModule.tendstoAtInfinity_tensorForm`: [Lus] Prop. 26.2.3,
  `(x(ξ_{-Λ} ⊗ η_{Λ'}), y(ξ_{-Λ} ⊗ η_{Λ'}))_{Λ,Λ'} → (x, y)` for `x, y ∈ U̇ 1_ζ` as `Λ → ∞` with
  `Λ' - Λ = ζ` fixed. Limits are `ϖ`-adic (`QuantumGroup.TendstoAtInfinity`): `k = A[ϖ⁻¹]` with
  `ϖ ↦ v⁻¹`, which for `k = ℚ(v)` and `A = ℚ[v⁻¹]_{(v⁻¹)}` is convergence in `ℚ((v⁻¹))`.

Lusztig assumes a `Y`-regular root datum and works with the modules `Λ_λ` (`λ` dominant). Here
`L_q(Λ) = M_q(Λ) ⧸ M'_q(Λ)` carries its contravariant form `IrreducibleModule.form`, which is
defined for `X`-regular root data; for `v` transcendental and `Λ` dominant `L_q(Λ)` is `Λ_Λ`
(`FPowQuotient.equivIrreducibleModule`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 19.3.7, 26.2.1–26.2.3.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]

namespace ChevalleyTwist

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

variable (R v) in
/-- A bilinear form on `M`, as a bilinear form on the twist `ʷM`. -/
def form (B : LinearMap.BilinForm k M) : LinearMap.BilinForm k (ChevalleyTwist R v M) :=
  B.compl₁₂ (toTwist R v M).symm.toLinearMap (toTwist R v M).symm.toLinearMap

omit [DecidableEq I] [NeZero v] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] in
@[simp] lemma form_toTwist (B : LinearMap.BilinForm k M) (x y : M) :
    form R v B (toTwist R v M x) (toTwist R v M y) = B x y := rfl

omit [IsScalarTower k (QuantumGroup R v) M] in
/-- A contravariant form on `M` is contravariant on `ʷM`: `ω ρ = ρ ω` ([Lus] 26.2.2, proof). -/
theorem isContravariant_form {B : LinearMap.BilinForm k M} (hB : IsContravariant R v B) :
    IsContravariant R v (form R v B) := by
  intro u x y
  obtain ⟨x, rfl⟩ := (toTwist R v M).surjective x
  obtain ⟨y, rfl⟩ := (toTwist R v M).surjective y
  rw [smul_toTwist, smul_toTwist, form_toTwist, form_toTwist, hB, chevalley_rho]

end ChevalleyTwist

namespace IrreducibleModule

variable (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-- The form `(x ⊗ x', y ⊗ y') = (x, y)_Λ (x', y')_{Λ'}` on `ʷL_q(Λ) ⊗ L_q(Λ')`
([Lus] 26.2.1). -/
def tensorForm (Λ Λ' : Y →+ ℤ) : LinearMap.BilinForm k
    (TensorModule k (ChevalleyTwist R v (IrreducibleModule R v Λ)) (IrreducibleModule R v Λ')) :=
  TensorModule.form (ChevalleyTwist.form R v (form Λ hR hv')) (form Λ' hR hv')

/-- **[Lus] Lemma 26.2.2**: the form on `ʷL_q(Λ) ⊗ L_q(Λ')` is contravariant,
`(u X, X') = (X, ρ(u) X')`. -/
theorem isContravariant_tensorForm (Λ Λ' : Y →+ ℤ) :
    IsContravariant R v (tensorForm hR hv' Λ Λ') :=
  TensorModule.isContravariant_form
    (ChevalleyTwist.isContravariant_form (isContravariant_form hR hv'))
    (isContravariant_form hR hv')

end IrreducibleModule

/-! ### Limits at infinity -/

section Limit

variable {A : Type*} [CommRing A] [Algebra A k]

variable (R) in
/-- `f(Λ) → c` as `⟨i, Λ⟩ → ∞` for all `i`, `ϖ`-adically: for every `m` there is `M` such that
`f(Λ) - c ∈ ϖ^m A` whenever `⟨i, Λ⟩ ≥ M` for all `i`. For `k = ℚ(v)`, `A = ℚ[v⁻¹]_{(v⁻¹)}` and
`ϖ = v⁻¹` this is convergence in `ℚ((v⁻¹))`. -/
def TendstoAtInfinity (ϖ : A) (f : (Y →+ ℤ) → k) (c : k) : Prop :=
  ∀ m : ℕ, ∃ M : ℤ, ∀ Λ : Y →+ ℤ, (∀ i, M ≤ Λ (R.coroot i)) →
    ∃ a : A, f Λ - c = algebraMap A k (ϖ ^ m * a)

namespace TendstoAtInfinity

variable {ϖ : A} {f g : (Y →+ ℤ) → k} {c d : k}

omit [DecidableEq I] [NeZero v] in
/-- Limits add. -/
theorem add (hf : TendstoAtInfinity R ϖ f c) (hg : TendstoAtInfinity R ϖ g d) :
    TendstoAtInfinity R ϖ (fun Λ ↦ f Λ + g Λ) (c + d) := by
  intro m
  obtain ⟨M, hM⟩ := hf m
  obtain ⟨M', hM'⟩ := hg m
  refine ⟨max M M', fun Λ hΛ ↦ ?_⟩
  obtain ⟨a, ha⟩ := hM Λ fun i ↦ (le_max_left _ _).trans (hΛ i)
  obtain ⟨a', ha'⟩ := hM' Λ fun i ↦ (le_max_right _ _).trans (hΛ i)
  refine ⟨a + a', ?_⟩
  rw [mul_add, map_add, ← ha, ← ha']
  ring

omit [DecidableEq I] [NeZero v] in
/-- Limits are `k`-linear (`k = A[ϖ⁻¹]`). -/
theorem const_mul (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
    (hf : TendstoAtInfinity R ϖ f c) (b : k) :
    TendstoAtInfinity R ϖ (fun Λ ↦ b * f Λ) (b * c) := by
  intro m
  obtain ⟨e, b', hb'⟩ := hk b
  obtain ⟨M, hM⟩ := hf (m + e)
  refine ⟨M, fun Λ hΛ ↦ ?_⟩
  obtain ⟨a, ha⟩ := hM Λ hΛ
  refine ⟨b' * a, ?_⟩
  rw [← mul_sub, ha, pow_add]
  simp only [map_mul] at hb' ⊢
  rw [← hb']
  ring

omit [DecidableEq I] [NeZero v] in
/-- Shifting the argument by a fixed `ζ` does not change the limit. -/
theorem comp_add [Finite I] (hf : TendstoAtInfinity R ϖ f c) (ζ : Y →+ ℤ) :
    TendstoAtInfinity R ϖ (fun Λ ↦ f (ζ + Λ)) c := by
  have := Fintype.ofFinite I
  intro m
  obtain ⟨M, hM⟩ := hf m
  refine ⟨M + ∑ i, |ζ (R.coroot i)|, fun Λ hΛ ↦ hM _ fun i ↦ ?_⟩
  have h1 := hΛ i
  have h2 : |ζ (R.coroot i)| ≤ ∑ j, |ζ (R.coroot j)| :=
    Finset.single_le_sum (f := fun j ↦ |ζ (R.coroot j)|) (fun j _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
  have h3 := neg_abs_le (ζ (R.coroot i))
  rw [AddMonoidHom.add_apply]
  omega

end TendstoAtInfinity

end Limit

namespace IrreducibleModule

variable (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-- [Lus] Prop. 19.3.7 as a limit: `(x⁻ η_Λ, y⁻ η_Λ)_Λ → (x, y)`. -/
theorem tendstoAtInfinity_form_minusHom [CharZero k] [Finite I] {A : Type*} [CommRing A]
    [Algebra A k] {ϖ : A}
    (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
    (hϖv : algebraMap A k ϖ = v⁻¹) (x y : LusztigF k I) :
    TendstoAtInfinity R ϖ
      (fun Λ ↦ form Λ hR hv' (minusHom R v x • hwv R v Λ) (minusHom R v y • hwv R v Λ))
      (LusztigF.form D v x y) :=
  fun m ↦ exists_form_minusHom_sub_mem hR hv' hk hϖv x y m

/-- The vector `ξ_{-Λ} ⊗ η_{Λ'}` of `ʷL_q(Λ) ⊗ L_q(Λ')`: `η_Λ`, of weight `-Λ` in the twist,
tensored with `η_{Λ'}`. -/
def tensorHwv (Λ Λ' : Y →+ ℤ) :
    TensorModule k (ChevalleyTwist R v (IrreducibleModule R v Λ)) (IrreducibleModule R v Λ') :=
  TensorModule.mk _ _ (ChevalleyTwist.toTwist R v _ (hwv R v Λ) ⊗ₜ[k] hwv R v Λ')

omit [NeZero v] in
/-- `K_μ η_Λ = v^{⟨μ,Λ⟩} η_Λ`. -/
lemma K_smul_hwv (Λ : Y →+ ℤ) (μ : Y) : K R v μ • hwv R v Λ = v ^ Λ μ • hwv R v Λ := by
  rw [hwv, ← Submodule.Quotient.mk_smul, VermaModule.K_smul_hwv, Submodule.Quotient.mk_smul]

/-- `x⁻ (ξ_{-Λ} ⊗ m) = ξ_{-Λ} ⊗ x⁻ m`, since `Fᵢ ξ_{-Λ} = ω(Fᵢ) η_Λ = Eᵢ η_Λ = 0`. -/
lemma minusHom_smul_tmul (Λ Λ' : Y →+ ℤ) (x : LusztigF k I) (m : IrreducibleModule R v Λ') :
    minusHom R v x • TensorModule.mk (ChevalleyTwist R v (IrreducibleModule R v Λ)) _
        (ChevalleyTwist.toTwist R v _ (hwv R v Λ) ⊗ₜ[k] m) =
      TensorModule.mk _ _ (ChevalleyTwist.toTwist R v _ (hwv R v Λ) ⊗ₜ[k]
        (minusHom R v x • m)) := by
  induction x using FreeAlgebra.induction generalizing m with
  | grade0 c =>
    rw [AlgHom.commutes, algebraMap_smul, algebraMap_smul, TensorProduct.tmul_smul, map_smul]
  | grade1 i =>
    have hE : F R v i • ChevalleyTwist.toTwist R v (IrreducibleModule R v Λ) (hwv R v Λ) = 0 := by
      rw [ChevalleyTwist.smul_toTwist, chevalley_F, hwv, ← Submodule.Quotient.mk_smul,
        VermaModule.E_smul_hwv, Submodule.Quotient.mk_zero, map_zero]
    rw [← LusztigF.θ, minusHom_θ, TensorModule.F_smul_tmul, hE, TensorProduct.zero_tmul, zero_add]
  | add a b ha hb => rw [map_add, add_smul, ha, hb, add_smul, TensorProduct.tmul_add, map_add]
  | mul a b ha hb => rw [map_mul, mul_smul, hb, ha, mul_smul]

/-- `ξ_{-Λ} ⊗ η_{Λ'}` has weight `Λ' - Λ`. -/
lemma K_smul_tensorHwv (Λ Λ' : Y →+ ℤ) (μ : Y) :
    K R v μ • tensorHwv (R := R) (v := v) Λ Λ' = v ^ (Λ' - Λ) μ • tensorHwv Λ Λ' := by
  rw [tensorHwv, TensorModule.K_smul_tmul, ChevalleyTwist.smul_toTwist, chevalley_K,
    K_smul_hwv, K_smul_hwv, LinearEquiv.map_smul, TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul', map_smul, map_smul, smul_smul]
  congr 1
  rw [map_neg, AddMonoidHom.sub_apply, sub_eq_add_neg, zpow_add₀ (NeZero.ne v)]

/-- `(ξ_{-Λ} ⊗ m, ξ_{-Λ} ⊗ m') = (m, m')_{Λ'}`, as `(η_Λ, η_Λ)_Λ = 1`. -/
lemma tensorForm_tmul (Λ Λ' : Y →+ ℤ) (m m' : IrreducibleModule R v Λ') :
    tensorForm hR hv' Λ Λ'
        (TensorModule.mk _ _ (ChevalleyTwist.toTwist R v _ (hwv R v Λ) ⊗ₜ[k] m))
        (TensorModule.mk _ _ (ChevalleyTwist.toTwist R v _ (hwv R v Λ) ⊗ₜ[k] m')) =
      form Λ' hR hv' m m' := by
  rw [tensorForm, TensorModule.form_tmul, ChevalleyTwist.form_toTwist, form_hwv, one_mul]

/-- **[Lus] Prop. 26.2.3**: let `ζ ∈ X`, `u, u' ∈ U`, and `x = u 1_ζ`, `y = u' 1_ζ` (every element
of `U̇ 1_ζ` has this form, `Modified.leftAct_one_eq_elt`; it acts on vectors of weight `ζ` as
`u`). As the pair `(Λ, Λ' = ζ + Λ)` tends to `∞` (`⟨i, Λ⟩ → ∞` for all `i`), the inner product
`(x(ξ_{-Λ} ⊗ η_{Λ'}), y(ξ_{-Λ} ⊗ η_{Λ'}))_{Λ,Λ'}` converges `ϖ`-adically to `(x, y)`
(`Modified.form`). Here `k = A[ϖ⁻¹]`, `ϖ ↦ v⁻¹`; for `k = ℚ(v)` and `A = ℚ[v⁻¹]_{(v⁻¹)}` this is
convergence in `ℚ((v⁻¹))` as in the source. The forms on `L_q(Λ)` need `R` to be `X`-regular;
Lusztig assumes `Y`-regular.

The proof follows the source: Lemma 26.2.2 and [Lus] 26.1.2 (b) reduce to `x = 1_ζ`, and the
values on `y = ρ(x₁⁻) y₁⁻ K_μ 1_ζ` come from Prop. 19.3.7 and 26.1.2 (c). -/
theorem tendstoAtInfinity_tensorForm [CharZero k] [Finite I] {A : Type*} [CommRing A]
    [Algebra A k] {ϖ : A}
    (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
    (hϖv : algebraMap A k ϖ = v⁻¹) (ζ : Y →+ ℤ) (u u' : QuantumGroup R v) :
    TendstoAtInfinity R ϖ
      (fun Λ ↦ tensorForm hR hv' Λ (ζ + Λ) (u • tensorHwv Λ (ζ + Λ))
        (u' • tensorHwv Λ (ζ + Λ)))
      (Modified.form R v hv' (Modified.leftAct R v hv' u (Modified.one ζ))
        (Modified.leftAct R v hv' u' (Modified.one ζ))) := by
  have key : ∀ z : QuantumGroup R v, TendstoAtInfinity R ϖ
      (fun Λ ↦ tensorForm hR hv' Λ (ζ + Λ) (tensorHwv Λ (ζ + Λ)) (z • tensorHwv Λ (ζ + Λ)))
      (Modified.form R v hv' (Modified.one ζ) (Modified.leftAct R v hv' z (Modified.one ζ))) := by
    intro z
    induction z using induction_rho_minusHom with
    | h0 => exact fun m ↦ ⟨0, fun Λ _ ↦ ⟨0, by simp⟩⟩
    | hadd x y hx hy =>
      convert hx.add hy using 1
      · funext Λ; rw [add_smul, map_add]
      · rw [map_add, LinearMap.add_apply, map_add]
    | hsmul c x hx =>
      convert hx.const_mul hk c using 1
      · funext Λ; rw [smul_assoc, map_smul, smul_eq_mul]
      · rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]
    | hmon w w' μ =>
      have hlim := ((tendstoAtInfinity_form_minusHom hR hv' hk hϖv
        (LusztigF.monomial k w) (LusztigF.monomial k w')).comp_add ζ).const_mul hk (v ^ ζ μ)
      convert hlim using 1
      · funext Λ
        rw [mul_smul, K_smul_tensorHwv, add_sub_cancel_right,
          smul_comm (rho R v (minusHom R v (LusztigF.monomial k w)) *
            minusHom R v (LusztigF.monomial k w')) (v ^ ζ μ), map_smul, smul_eq_mul, mul_smul,
          ← isContravariant_tensorForm hR hv', tensorHwv, minusHom_smul_tmul,
          minusHom_smul_tmul, tensorForm_tmul]
      · rw [Modified.one_leftAct_one_eq_formFunctional hv' (Modified.form_leftAct_left hv')
          (Modified.form_minusHom_leftAct_one hv'), formFunctional_rho_minusHom]
  convert key (rho R v u * u') using 1
  · funext Λ; rw [isContravariant_tensorForm hR hv', mul_smul]
  · rw [Modified.form_leftAct_left hv', Modified.leftAct_mul]

end IrreducibleModule

end LieLean.QuantumGroup
