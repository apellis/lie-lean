/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Integrable
import LieLean.Algebra.QuantumGroup.IrreducibleCharacter.Verma
import LieLean.Algebra.QuantumGroup.TensorModule

/-!
# Contravariant forms on `U_q(𝔤)`-modules

Let `U = U_q(𝔤)` (`QuantumGroup R v`). Lusztig's anti-automorphism `ρ` of `U` ([Lus] 19.1.1) is
`ρ(Eᵢ) = vᵢ K̃ᵢ Fᵢ`, `ρ(Fᵢ) = vᵢ K̃ᵢ⁻¹ Eᵢ`, `ρ(K_μ) = K_μ`; it is an involution
(`QuantumGroup.rho_rho`). A bilinear form `B` on a `U`-module is *contravariant*
(`QuantumGroup.IsContravariant`) if `B(u x, y) = B(x, ρ(u) y)` for all `u ∈ U`; it suffices to check
this on the generators (`QuantumGroup.isContravariant_of_generators`). The tensor product of
contravariant forms is contravariant for the coproduct of `U` (`QuantumGroup.TensorModule.form`,
`QuantumGroup.TensorModule.isContravariant_form`): `Δ ∘ ρ = (ρ ⊗ ρ) ∘ Δ` on generators.

On the Verma module `M_q(Λ)` the *Shapovalov form* `B(u v_Λ, m) = ⟨v_Λ-coefficient of ρ(u) m⟩`
(`QuantumGroup.VermaModule.shapForm`) is well defined, contravariant and symmetric, with
`B(v_Λ, v_Λ) = 1`, and its radical is the maximal submodule `M'_q(Λ)`. Hence it descends to a
nondegenerate symmetric contravariant form on `L_q(Λ)` (`QuantumGroup.IrreducibleModule.form`),
the unique such form with `(v_Λ, v_Λ) = 1`
(`QuantumGroup.IrreducibleModule.eq_smul_form_of_isContravariant`; [Lus] Prop. 19.1.2, over
`ℚ(v)`).
Symmetry comes from `χ ∘ ρ = χ` for `χ(u) = ⟨v_Λ-coefficient of u v_Λ⟩`, checked on the triangular
spanning set `y⁻ K_μ x⁺`.

These are the forms used by Kashiwara ([HK] (5.1)–(5.2), §5.3; [Jan] 9.20, there with Jantzen's
anti-automorphism `τ₁` and his coproduct). The arguments are standard; the formulation is ours.

## Main definitions

* `QuantumGroup.rhoOp`, `QuantumGroup.rho`: Lusztig's anti-automorphism `ρ`.
* `QuantumGroup.IsContravariant`.
* `QuantumGroup.VermaModule.shapForm`, `QuantumGroup.IrreducibleModule.form`.
* `QuantumGroup.TensorModule.form`: the tensor product of two forms.

## Main results

* `QuantumGroup.rho_mul`, `QuantumGroup.rho_rho`.
* `QuantumGroup.VermaModule.shapForm_comm`, `QuantumGroup.VermaModule.shapForm_eq_zero_iff`.
* `QuantumGroup.VermaModule.eq_smul_shapForm_of_isContravariant`: uniqueness on `M_q(Λ)`.
* `QuantumGroup.IrreducibleModule.isContravariant_form`, `form_comm`, `form_hwv`,
  `eq_zero_of_form_eq_zero` (nondegeneracy), `eq_smul_form_of_isContravariant` (uniqueness).
* `QuantumGroup.IsContravariant.eq_zero_of_ne`: orthogonality of weight spaces.
* `QuantumGroup.TensorModule.isContravariant_form`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 19.1.1–19.1.2.
* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.1, §5.3.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 9.20.
-/

open LieLean MulOpposite TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k)

/-! ### Lusztig's anti-automorphism `ρ` -/

/-- `ρ(Eᵢ) = vᵢ K̃ᵢ Fᵢ`. -/
def rhoE (i : I) : QuantumGroup R v := (v ^ D.d i) • (Kt R v i * F R v i)

/-- `ρ(Fᵢ) = vᵢ K̃ᵢ⁻¹ Eᵢ`. -/
def rhoF (i : I) : QuantumGroup R v := (v ^ D.d i) • (K R v (-ktilde R i) * E R v i)

/-- `μ ↦ K_μ` into the opposite algebra. -/
def rhoK : Multiplicative Y →* (QuantumGroup R v)ᵐᵒᵖ where
  toFun μ := op (K R v μ.toAdd)
  map_one' := by simp
  map_mul' μ ν := by
    rw [← op_mul, K_add, toAdd_mul, add_comm]

variable {R v}

omit [DecidableEq I] in
lemma zpow_dot_mul (hv : v ≠ 0) (i : I) : (v ^ D.d i) * (v ^ D.d i) * v ^ (-D.dot i i) = 1 := by
  have h : ((D.d i + D.d i : ℕ) : ℤ) + -(2 * (D.d i : ℤ)) = 0 := by push_cast; ring
  rw [← D.two_mul_d i, ← pow_add, ← zpow_natCast, ← zpow_add₀ hv, h, zpow_zero]

variable [NeZero v]

lemma rhoE_mul_K (i : I) (μ : Y) :
    rhoE R v i * K R v μ = v ^ R.root i μ • (K R v μ * rhoE R v i) := by
  rw [rhoE, smul_mul_assoc, mul_assoc, F_mul_K (NeZero.ne v), mul_smul_comm, ← mul_assoc,
    K_comm, mul_assoc, smul_comm, mul_smul_comm]

lemma rhoF_mul_K (i : I) (μ : Y) :
    rhoF R v i * K R v μ = v ^ (-R.root i μ) • (K R v μ * rhoF R v i) := by
  rw [rhoF, smul_mul_assoc, mul_assoc, E_mul_K (NeZero.ne v), mul_smul_comm, ← mul_assoc,
    K_comm, mul_assoc, smul_comm, mul_smul_comm]

lemma rhoF_mul_rhoE_sub (i j : I) :
    rhoF R v j * rhoE R v i - rhoE R v i * rhoF R v j = if i = j then
      (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (Kt R v i - K R v (-ktilde R i)) else 0 := by
  have hv := NeZero.ne v
  have e1 : rhoF R v j * rhoE R v i = ((v ^ D.d j * v ^ D.d i) * v ^ (-D.dot i j)) •
      (K R v (-ktilde R j) * Kt R v i * (E R v j * F R v i)) := by
    rw [rhoF, rhoE, smul_mul_smul_comm, mul_assoc, ← mul_assoc (E R v j), E_mul_K hv,
      root_ktilde_eq_dot]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  have e2 : rhoE R v i * rhoF R v j = ((v ^ D.d j * v ^ D.d i) * v ^ (-D.dot i j)) •
      (K R v (-ktilde R j) * Kt R v i * (F R v i * E R v j)) := by
    rw [rhoE, rhoF, smul_mul_smul_comm, mul_assoc, ← mul_assoc (F R v i), F_mul_K hv,
      map_neg, root_ktilde_eq_dot, D.dot_comm j i]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    congr 1
    · ring
    · rw [← mul_assoc, K_comm, mul_assoc]
  rw [e1, e2, ← smul_sub, ← mul_sub, E_mul_F_sub]
  by_cases h : i = j
  · subst h
    simp only [ite_true]
    rw [mul_smul_comm, K_add, neg_add_cancel, K_zero, one_mul, zpow_dot_mul hv, one_smul]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, mul_zero, smul_zero]

theorem rho_relations :
    Relations R v (fun i ↦ op (rhoE R v i)) (fun i ↦ op (rhoF R v i)) (rhoK R v) where
  K_mul_E μ i := by
    apply unop_injective
    simp only [rhoK, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, unop_mul, unop_op,
      unop_smul]
    exact rhoE_mul_K i μ
  K_mul_F μ i := by
    apply unop_injective
    simp only [rhoK, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, unop_mul, unop_op,
      unop_smul]
    exact rhoF_mul_K i μ
  E_mul_F i j := by
    apply unop_injective
    simp only [unop_sub, unop_mul, unop_op]
    rw [rhoF_mul_rhoE_sub]
    split_ifs
    · simp [rhoK, Kt]
    · simp
  serre_E i j hij := by
    have hv := NeZero.ne v
    rw [qSerre_op, rhoE, rhoE, qSerre_smul_smul,
      qSerre_mul_mul (t := v ^ (-R.root i (ktilde R i))) (s := v ^ R.root i (ktilde R j))
        (zpow_ne_zero _ hv) (K_mul_F R v _ i) (F_mul_K hv _ i)
        (by rw [F_mul_K hv, root_ktilde_eq_dot, root_ktilde_eq_dot, D.dot_comm]) (K_comm R v _ _),
      serre_F R v hij]
    simp
  serre_F i j hij := by
    have hv := NeZero.ne v
    rw [qSerre_op, rhoF, rhoF, qSerre_smul_smul,
      qSerre_mul_mul (t := v ^ R.root i (-ktilde R i)) (s := v ^ (-R.root i (-ktilde R j)))
        (zpow_ne_zero _ hv) (K_mul_E R v _ i) (E_mul_K hv _ i)
        (by rw [E_mul_K hv, map_neg, map_neg, root_ktilde_eq_dot, root_ktilde_eq_dot,
          D.dot_comm]) (K_comm R v _ _),
      serre_E R v hij]
    simp

variable (R v) in
/-- Lusztig's anti-automorphism `ρ` as an algebra map to the opposite algebra ([Lus] 19.1.1). -/
def rhoOp : QuantumGroup R v →ₐ[k] (QuantumGroup R v)ᵐᵒᵖ := lift rho_relations

variable (R v) in
/-- Lusztig's anti-automorphism `ρ` ([Lus] 19.1.1): `ρ(Eᵢ) = vᵢ K̃ᵢ Fᵢ`, `ρ(Fᵢ) = vᵢ K̃ᵢ⁻¹ Eᵢ`,
`ρ(K_μ) = K_μ`. -/
def rho : QuantumGroup R v →ₗ[k] QuantumGroup R v :=
  (opLinearEquiv k).symm.toLinearMap.comp (rhoOp R v).toLinearMap

@[simp] lemma rho_E (i : I) : rho R v (E R v i) = rhoE R v i := by simp [rho, rhoOp]

@[simp] lemma rho_F (i : I) : rho R v (F R v i) = rhoF R v i := by simp [rho, rhoOp]

@[simp] lemma rho_K (μ : Y) : rho R v (K R v μ) = K R v μ := by simp [rho, rhoOp, rhoK]

@[simp] lemma rho_algebraMap (c : k) : rho R v (algebraMap k _ c) = algebraMap k _ c := by
  simp [rho]

/-- `ρ` reverses products. -/
theorem rho_mul (x y : QuantumGroup R v) : rho R v (x * y) = rho R v y * rho R v x := by
  simp [rho]

@[simp] lemma rho_one : rho R v 1 = 1 := by simp [rho]

lemma rho_rhoE (i : I) : rho R v (rhoE R v i) = E R v i := by
  have hv := NeZero.ne v
  rw [rhoE, map_smul, rho_mul, rho_F, rho_K, rhoF, smul_mul_assoc, mul_assoc, E_mul_K hv,
    root_ktilde_eq_dot, mul_smul_comm, ← mul_assoc, K_add, neg_add_cancel, K_zero, one_mul,
    smul_smul, smul_smul, zpow_dot_mul hv, one_smul]

lemma rho_rhoF (i : I) : rho R v (rhoF R v i) = F R v i := by
  have hv := NeZero.ne v
  rw [rhoF, map_smul, rho_mul, rho_E, rho_K, rhoE, smul_mul_assoc, mul_assoc, F_mul_K hv,
    map_neg, root_ktilde_eq_dot, mul_smul_comm, ← mul_assoc, K_add, add_neg_cancel, K_zero,
    one_mul, smul_smul, smul_smul, zpow_dot_mul hv, one_smul]

/-- `ρ` is an involution. -/
theorem rho_rho (x : QuantumGroup R v) : rho R v (rho R v x) = x := by
  induction x using QuantumGroup.induction_on with
  | algebraMap c => simp
  | E i => rw [rho_E, rho_rhoE]
  | F i => rw [rho_F, rho_rhoF]
  | K μ => rw [rho_K, rho_K]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | mul x y hx hy => rw [rho_mul, rho_mul, hx, hy]

/-! ### Contravariant forms -/

section Contravariant

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

variable (R v) in
/-- A bilinear form on a `U`-module is contravariant if `B(u x, y) = B(x, ρ(u) y)`. -/
def IsContravariant (B : LinearMap.BilinForm k M) : Prop :=
  ∀ (u : QuantumGroup R v) (x y : M), B (u • x) y = B x (rho R v u • y)

/-- A form is contravariant as soon as `B(u x, y) = B(x, ρ(u) y)` for the generators `u`. -/
theorem isContravariant_of_generators {B : LinearMap.BilinForm k M}
    (hE : ∀ i x y, B (E R v i • x) y = B x (rhoE R v i • y))
    (hF : ∀ i x y, B (F R v i • x) y = B x (rhoF R v i • y))
    (hK : ∀ μ x y, B (K R v μ • x) y = B x (K R v μ • y)) : IsContravariant R v B := by
  intro u
  induction u using QuantumGroup.induction_on with
  | algebraMap c => intro x y; simp [algebraMap_smul]
  | E i => intro x y; rw [rho_E]; exact hE i x y
  | F i => intro x y; rw [rho_F]; exact hF i x y
  | K μ => intro x y; rw [rho_K]; exact hK μ x y
  | add a b ha hb => intro x y; rw [add_smul, map_add, LinearMap.add_apply, ha, hb, map_add,
      add_smul, map_add]
  | mul a b ha hb => intro x y; rw [mul_smul, ha, hb, rho_mul, mul_smul]

/-- Weight spaces of different weights are orthogonal for a contravariant form (`v` not a root of
unity). -/
theorem IsContravariant.eq_zero_of_ne {B : LinearMap.BilinForm k M} (hB : IsContravariant R v B)
    {Λ Λ' : Y →+ ℤ} (h : Λ ≠ Λ') {x y : M} (hx : x ∈ weightSpace R v M Λ)
    (hy : y ∈ weightSpace R v M Λ') (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) : B x y = 0 := by
  obtain ⟨μ, hμ⟩ := DFunLike.ne_iff.1 h
  have e := hB (K R v μ) x y
  rw [rho_K, hx μ, hy μ, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
    smul_eq_mul] at e
  have hne : v ^ Λ μ ≠ v ^ Λ' μ := by
    intro he
    refine zpow_ne_one_of_not_root hv' (sub_ne_zero.2 hμ) ?_
    rw [zpow_sub₀ (NeZero.ne v), he, div_self (zpow_ne_zero _ (NeZero.ne v))]
  have : (v ^ Λ μ - v ^ Λ' μ) * B x y = 0 := by rw [sub_mul, e, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

end Contravariant

/-! ### The Shapovalov form on `M_q(Λ)` -/

namespace VermaModule

variable {Λ : Y →+ ℤ} (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

variable (Λ) in
/-- The pairing `U × M_q(Λ) → k`, `(u, m) ↦ ⟨v_Λ-coefficient of ρ(u) m⟩`. -/
def shapAux : QuantumGroup R v →ₗ[k] VermaModule R v Λ →ₗ[k] k :=
  LinearMap.llcomp k _ _ _ (hwCoord Λ hv') ∘ₗ
    (Algebra.lsmul k k (VermaModule R v Λ)).toLinearMap ∘ₗ rho R v

lemma shapAux_apply (u : QuantumGroup R v) (m : VermaModule R v Λ) :
    shapAux Λ hv' u m = hwCoord Λ hv' (rho R v u • m) := rfl

lemma hwCoord_F_smul (i : I) (m : VermaModule R v Λ) : hwCoord Λ hv' (F R v i • m) = 0 := by
  rw [← minusHom_θ (R := R) (v := v) (k := k), hwCoord_minusHom_smul, LusztigF.counit_θ,
    zero_mul]

lemma hwCoord_rhoE_smul (i : I) (m : VermaModule R v Λ) :
    hwCoord Λ hv' (rhoE R v i • m) = 0 := by
  rw [rhoE, smul_assoc, mul_smul, map_smul, hwCoord_K_smul, hwCoord_F_smul, mul_zero, smul_zero]

lemma shapAux_mul (a b : QuantumGroup R v) (m : VermaModule R v Λ) :
    shapAux Λ hv' (a * b) m = shapAux Λ hv' b (rho R v a • m) := by
  rw [shapAux_apply, shapAux_apply, rho_mul, mul_smul]

lemma shapAux_eq_zero_of_mem {z : QuantumGroup R v} (hz : z ∈ vermaIdeal R v Λ) :
    shapAux Λ hv' z = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    refine LinearMap.ext fun m ↦ ?_
    rcases hz with ⟨i, rfl⟩ | ⟨μ, rfl⟩
    · rw [shapAux_apply, rho_E, hwCoord_rhoE_smul, LinearMap.zero_apply]
    · rw [shapAux_apply, (rho R v).map_sub, rho_K, rho_algebraMap, sub_smul, algebraMap_smul,
        (hwCoord Λ hv').map_sub, hwCoord_K_smul, (hwCoord Λ hv').map_smul, smul_eq_mul, sub_self,
        LinearMap.zero_apply]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx =>
    refine LinearMap.ext fun m ↦ ?_
    rw [smul_eq_mul, shapAux_mul, hx, LinearMap.zero_apply, LinearMap.zero_apply]

variable (Λ) in
/-- The Shapovalov form on `M_q(Λ)`: `B(u v_Λ, m) = ⟨v_Λ-coefficient of ρ(u) m⟩`. -/
def shapForm : LinearMap.BilinForm k (VermaModule R v Λ) :=
  ((vermaIdeal R v Λ).restrictScalars k).liftQ (shapAux Λ hv')
      (fun _ hz ↦ shapAux_eq_zero_of_mem hv' hz) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k (vermaIdeal R v Λ)).symm.toLinearMap

lemma shapForm_smul_hwv (u : QuantumGroup R v) (m : VermaModule R v Λ) :
    shapForm Λ hv' (u • hwv R v Λ) m = hwCoord Λ hv' (rho R v u • m) := by
  rw [← mk_eq_smul_hwv]
  rfl

/-- The Shapovalov form is contravariant. -/
theorem isContravariant_shapForm :
    IsContravariant (M := VermaModule R v Λ) R v (shapForm Λ hv') := by
  intro u x y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mk_eq_smul_hwv, ← mul_smul, shapForm_smul_hwv, shapForm_smul_hwv, rho_mul, mul_smul]

/-- `ρ(y⁻) v_Λ = ε(y) v_Λ`. -/
lemma rho_minusHom_smul_hwv (y : LusztigF k I) :
    rho R v (minusHom R v y) • hwv R v Λ = LusztigF.counit y • hwv R v Λ := by
  induction y using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes, rho_algebraMap, algebraMap_smul, LusztigF.counit_algebraMap]
  | grade1 i =>
    rw [minusHom_θ, rho_F, LusztigF.counit_θ, zero_smul, rhoF, smul_assoc, mul_smul,
      E_smul_hwv, smul_zero, smul_zero]
  | mul a b ha hb =>
    rw [map_mul, rho_mul, mul_smul, ha, smul_comm, hb, smul_smul, map_mul, mul_comm]
  | add a b ha hb => rw [map_add, map_add, add_smul, ha, hb, map_add, add_smul]

/-- `⟨v_Λ-coefficient of ρ(x⁺) m⟩ = ε(x) ⟨v_Λ-coefficient of m⟩`. -/
lemma hwCoord_rho_plusHom_smul (x : LusztigF k I) (m : VermaModule R v Λ) :
    hwCoord Λ hv' (rho R v (plusHom R v x) • m) = LusztigF.counit x * hwCoord Λ hv' m := by
  induction x using FreeAlgebra.induction generalizing m with
  | grade0 c =>
    rw [AlgHom.commutes, rho_algebraMap, algebraMap_smul, map_smul, LusztigF.counit_algebraMap,
      smul_eq_mul]
  | grade1 i => rw [plusHom_θ, rho_E, hwCoord_rhoE_smul, LusztigF.counit_θ, zero_mul]
  | mul a b ha hb => rw [map_mul, rho_mul, mul_smul, hb, ha, map_mul]; ring
  | add a b ha hb => rw [map_add, map_add, add_smul, map_add, ha, hb, map_add, add_mul]

/-- `χ ∘ ρ = χ` for `χ(u) = ⟨v_Λ-coefficient of u v_Λ⟩`. -/
lemma hwCoord_rho_smul_hwv (u : QuantumGroup R v) :
    hwCoord Λ hv' (rho R v u • hwv R v Λ) = hwCoord Λ hv' (u • hwv R v Λ) := by
  induction mem_triangularSpan_of u (NeZero.ne v) using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨w, μ, w', rfl⟩ := hu
    set y := LusztigF.monomial k w
    set x := LusztigF.monomial k w'
    have h1 : rho R v (minusHom R v y * K R v μ * plusHom R v x) • hwv R v Λ =
        rho R v (plusHom R v x) • ((LusztigF.counit y * v ^ Λ μ) • hwv R v Λ) := by
      rw [rho_mul, rho_mul, rho_K, mul_smul, mul_smul, rho_minusHom_smul_hwv,
        smul_comm (K R v μ) (LusztigF.counit y), K_smul_hwv, smul_smul]
    have h2 : (minusHom R v y * K R v μ * plusHom R v x) • hwv R v Λ =
        minusHom R v y • ((LusztigF.counit x * v ^ Λ μ) • hwv R v Λ) := by
      rw [mul_smul, mul_smul, plusHom_smul_hwv, smul_comm (K R v μ) (LusztigF.counit x),
        K_smul_hwv, smul_smul]
    rw [h1, h2, hwCoord_rho_plusHom_smul, hwCoord_minusHom_smul, (hwCoord Λ hv').map_smul,
      (hwCoord Λ hv').map_smul, hwCoord_hwv]
    simp only [smul_eq_mul]
    ring
  | zero => simp
  | add x y _ _ hx hy =>
    rw [(rho R v).map_add, add_smul, (hwCoord Λ hv').map_add, hx, hy, add_smul,
      (hwCoord Λ hv').map_add]
  | smul c x _ hx =>
    rw [(rho R v).map_smul, smul_assoc, (hwCoord Λ hv').map_smul, hx, smul_assoc,
      (hwCoord Λ hv').map_smul]

/-- The Shapovalov form is symmetric. -/
theorem shapForm_comm (x y : VermaModule R v Λ) : shapForm Λ hv' x y = shapForm Λ hv' y x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [mk_eq_smul_hwv, mk_eq_smul_hwv, shapForm_smul_hwv, shapForm_smul_hwv, ← mul_smul,
    ← mul_smul, ← hwCoord_rho_smul_hwv hv' (rho R v b * a), rho_mul, rho_rho]

@[simp] lemma shapForm_hwv : shapForm Λ hv' (hwv R v Λ) (hwv R v Λ) = 1 := by
  have := shapForm_smul_hwv hv' (1 : QuantumGroup R v) (hwv R v Λ)
  rwa [one_smul, rho_one, one_smul, hwCoord_hwv] at this

/-- The radical of the Shapovalov form is the maximal submodule `M'_q(Λ)`. -/
theorem shapForm_eq_zero_iff (hR : R.IsXRegular) (x : VermaModule R v Λ) :
    (∀ y, shapForm Λ hv' x y = 0) ↔ x ∈ maxSubmodule R v Λ := by
  rw [mem_maxSubmodule_iff hR hv']
  refine ⟨fun h u ↦ ?_, fun h y ↦ ?_⟩
  · have := h (rho R v u • hwv R v Λ)
    rwa [shapForm_comm, shapForm_smul_hwv, rho_rho] at this
  · obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [shapForm_comm, mk_eq_smul_hwv, shapForm_smul_hwv, h]

/-- `B(u v_Λ, v_Λ) = ⟨v_Λ-coefficient of u v_Λ⟩ B(v_Λ, v_Λ)` for a contravariant form `B`. -/
lemma eq_hwCoord_mul_of_isContravariant {B : LinearMap.BilinForm k (VermaModule R v Λ)}
    (hB : IsContravariant R v B) (u : QuantumGroup R v) :
    B (u • hwv R v Λ) (hwv R v Λ) = hwCoord Λ hv' (u • hwv R v Λ) * B (hwv R v Λ) (hwv R v Λ) := by
  induction mem_triangularSpan_of u (NeZero.ne v) using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨w, μ, w', rfl⟩ := hu
    set y := LusztigF.monomial k w
    set x := LusztigF.monomial k w'
    have h2 : (minusHom R v y * K R v μ * plusHom R v x) • hwv R v Λ =
        minusHom R v y • ((LusztigF.counit x * v ^ Λ μ) • hwv R v Λ) := by
      rw [mul_smul, mul_smul, plusHom_smul_hwv, smul_comm (K R v μ) (LusztigF.counit x),
        K_smul_hwv, smul_smul]
    rw [h2, hB, rho_minusHom_smul_hwv]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hwCoord_minusHom_smul, hwCoord_hwv]
    ring
  | zero => simp
  | add a b _ _ ha hb =>
    rw [add_smul, map_add, LinearMap.add_apply, ha, hb, (hwCoord Λ hv').map_add, add_mul]
  | smul c a _ ha =>
    rw [smul_assoc, map_smul, LinearMap.smul_apply, ha, (hwCoord Λ hv').map_smul, smul_eq_mul,
      smul_eq_mul, mul_assoc]

/-- **Uniqueness of contravariant forms** on `M_q(Λ)`: a contravariant form is
`B(v_Λ, v_Λ)` times the Shapovalov form. -/
theorem eq_smul_shapForm_of_isContravariant {B : LinearMap.BilinForm k (VermaModule R v Λ)}
    (hB : IsContravariant R v B) (x y : VermaModule R v Λ) :
    B x y = B (hwv R v Λ) (hwv R v Λ) * shapForm Λ hv' x y := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [mk_eq_smul_hwv, mk_eq_smul_hwv, hB, ← mul_smul, shapForm_smul_hwv, ← mul_smul]
  have : B (hwv R v Λ) ((rho R v a * b) • hwv R v Λ) =
      B ((rho R v (rho R v a * b)) • hwv R v Λ) (hwv R v Λ) := by
    rw [hB, rho_rho]
  rw [this, eq_hwCoord_mul_of_isContravariant hv' hB, hwCoord_rho_smul_hwv, mul_comm]

end VermaModule

/-! ### The form on `L_q(Λ)` -/

namespace IrreducibleModule

open VermaModule (shapForm shapForm_eq_zero_iff shapForm_comm shapForm_hwv
  isContravariant_shapForm maxSubmodule)

variable (R v) in
/-- The highest weight vector of `L_q(Λ)`. -/
abbrev hwv (Λ : Y →+ ℤ) : IrreducibleModule R v Λ := Submodule.Quotient.mk (VermaModule.hwv R v Λ)

variable {Λ : Y →+ ℤ} (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hR hv'

lemma shapForm_left_eq_zero {x : VermaModule R v Λ} (hx : x ∈ maxSubmodule R v Λ)
    (y : VermaModule R v Λ) : shapForm Λ hv' x y = 0 :=
  (shapForm_eq_zero_iff hv' hR x).2 hx y

lemma shapForm_right_eq_zero (x : VermaModule R v Λ) {y : VermaModule R v Λ}
    (hy : y ∈ maxSubmodule R v Λ) : shapForm Λ hv' x y = 0 := by
  rw [shapForm_comm]; exact shapForm_left_eq_zero hR hv' hy x

variable (Λ) in
/-- The contravariant form on `L_q(Λ)`, induced by the Shapovalov form. -/
def form : LinearMap.BilinForm k (IrreducibleModule R v Λ) :=
  ((maxSubmodule R v Λ).restrictScalars k).liftQ
      ((((maxSubmodule R v Λ).restrictScalars k).liftQ (shapForm Λ hv').flip
          fun y hy ↦ LinearMap.ext fun x ↦ shapForm_right_eq_zero hR hv' x hy).flip)
      (fun x hx ↦ LinearMap.ext fun y ↦ by
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact shapForm_left_eq_zero hR hv' hx y) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k (maxSubmodule R v Λ)).symm.toLinearMap

lemma form_mk (x y : VermaModule R v Λ) :
    form Λ hR hv' (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = shapForm Λ hv' x y := by
  simp [form]
  rfl

/-- The form on `L_q(Λ)` is contravariant. -/
theorem isContravariant_form : IsContravariant R v (form Λ hR hv') := by
  intro u x y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, form_mk, form_mk,
    isContravariant_shapForm]

/-- The form on `L_q(Λ)` is symmetric. -/
theorem form_comm (x y : IrreducibleModule R v Λ) : form Λ hR hv' x y = form Λ hR hv' y x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [form_mk, form_mk, shapForm_comm]

@[simp] lemma form_hwv : form Λ hR hv' (hwv R v Λ) (hwv R v Λ) = 1 := by
  rw [form_mk, shapForm_hwv]

/-- The form on `L_q(Λ)` is nondegenerate. -/
theorem eq_zero_of_form_eq_zero {x : IrreducibleModule R v Λ}
    (h : ∀ y, form Λ hR hv' x y = 0) : x = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, ← shapForm_eq_zero_iff hv' hR]
  intro y
  rw [← form_mk hR hv']
  exact h _

/-- **Uniqueness of contravariant forms** on `L_q(Λ)` ([Jan] 9.20 (c)): a contravariant form is
`B(v_Λ, v_Λ)` times `form`. -/
theorem eq_smul_form_of_isContravariant {B : LinearMap.BilinForm k (IrreducibleModule R v Λ)}
    (hB : IsContravariant R v B) (x y : IrreducibleModule R v Λ) :
    B x y = B (hwv R v Λ) (hwv R v Λ) * form Λ hR hv' x y := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  set π := (Submodule.Quotient.restrictScalarsEquiv k (maxSubmodule R v Λ)).toLinearMap ∘ₗ
    ((maxSubmodule R v Λ).restrictScalars k).mkQ
  have hπ : ∀ z, π z = Submodule.Quotient.mk z := fun z ↦ rfl
  have hB' : IsContravariant R v (B.compl₁₂ π π) := by
    intro u a b
    simp only [LinearMap.compl₁₂_apply, hπ, Submodule.Quotient.mk_smul]
    exact hB u _ _
  have := VermaModule.eq_smul_shapForm_of_isContravariant hv' hB' x y
  simp only [LinearMap.compl₁₂_apply, hπ] at this
  rw [this, form_mk]

end IrreducibleModule

/-! ### Tensor products -/

namespace TensorModule

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁] [AddCommGroup M₂] [Module k M₂]
  [Module (QuantumGroup R v) M₂] [IsScalarTower k (QuantumGroup R v) M₂]

/-- The tensor product `(x ⊗ y, x' ⊗ y') = B₁(x, x') B₂(y, y')` of two bilinear forms. -/
def form (B₁ : LinearMap.BilinForm k M₁) (B₂ : LinearMap.BilinForm k M₂) :
    LinearMap.BilinForm k (TensorModule k M₁ M₂) :=
  LinearMap.BilinForm.tmul B₁ B₂

omit [NeZero v] [Module (QuantumGroup R v) M₁] [IsScalarTower k (QuantumGroup R v) M₁]
  [Module (QuantumGroup R v) M₂] [IsScalarTower k (QuantumGroup R v) M₂] in
@[simp] lemma form_tmul (B₁ : LinearMap.BilinForm k M₁) (B₂ : LinearMap.BilinForm k M₂)
    (x x' : M₁) (y y' : M₂) :
    form B₁ B₂ (mk M₁ M₂ (x ⊗ₜ y)) (mk M₁ M₂ (x' ⊗ₜ y')) = B₁ x x' * B₂ y y' := by
  change LinearMap.BilinForm.tensorDistrib k k (B₁ ⊗ₜ B₂) (x ⊗ₜ y) (x' ⊗ₜ y') = _
  rw [LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul, mul_comm]

omit [NeZero v] [Module (QuantumGroup R v) M₁] [IsScalarTower k (QuantumGroup R v) M₁]
  [Module (QuantumGroup R v) M₂] [IsScalarTower k (QuantumGroup R v) M₂] in
/-- The tensor product of symmetric forms is symmetric. -/
lemma form_comm {B₁ : LinearMap.BilinForm k M₁} {B₂ : LinearMap.BilinForm k M₂}
    (h₁ : ∀ x x', B₁ x x' = B₁ x' x) (h₂ : ∀ y y', B₂ y y' = B₂ y' y)
    (z z' : TensorModule k M₁ M₂) : form B₁ B₂ z z' = form B₁ B₂ z' z := by
  have := LinearMap.IsSymm.tmul (B₁ := B₁) (B₂ := B₂) ⟨fun x x' ↦ h₁ x x'⟩ ⟨fun y y' ↦ h₂ y y'⟩
  exact this.eq z z'

/-- To prove `B(u z, z') = B(z, u' z')` on `M₁ ⊗ M₂` it suffices to check pure tensors. -/
lemma form_smul_eq_of_tmul {B : LinearMap.BilinForm k (TensorModule k M₁ M₂)}
    (u u' : QuantumGroup R v)
    (h : ∀ x y x' y', B (u • mk M₁ M₂ (x ⊗ₜ y)) (mk M₁ M₂ (x' ⊗ₜ y')) =
      B (mk M₁ M₂ (x ⊗ₜ y)) (u' • mk M₁ M₂ (x' ⊗ₜ y'))) (z z' : TensorModule k M₁ M₂) :
    B (u • z) z' = B z (u' • z') := by
  obtain ⟨z, rfl⟩ := (mk M₁ M₂).surjective z
  obtain ⟨z', rfl⟩ := (mk M₁ M₂).surjective z'
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, smul_add, map_add, LinearMap.add_apply, ha, hb, map_add,
      LinearMap.add_apply]
  | tmul x y =>
    induction z' using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, map_add, ha, hb, smul_add, map_add]
    | tmul x' y' => exact h x y x' y'

/-- **The tensor product of contravariant forms is contravariant** (for the coproduct of `U`;
cf. [Jan] 9.20 (b)). -/
theorem isContravariant_form {B₁ : LinearMap.BilinForm k M₁} {B₂ : LinearMap.BilinForm k M₂}
    (h₁ : IsContravariant R v B₁) (h₂ : IsContravariant R v B₂) :
    IsContravariant R v (form B₁ B₂) := by
  refine isContravariant_of_generators (fun i ↦ form_smul_eq_of_tmul _ _ fun x y x' y' ↦ ?_)
    (fun i ↦ form_smul_eq_of_tmul _ _ fun x y x' y' ↦ ?_)
    (fun μ ↦ form_smul_eq_of_tmul _ _ fun x y x' y' ↦ ?_)
  · simp only [rhoE, smul_assoc, mul_smul, E_smul_tmul, F_smul_tmul, K_smul_tmul, map_add,
      smul_add, LinearMap.add_apply, map_smul, form_tmul, smul_eq_mul,
      h₁ (E R v i), h₂ (E R v i), h₁ (Kt R v i), rho_E, rho_K]
    rw [← mul_smul (Kt R v i) (K R v (-ktilde R i)), K_add, add_neg_cancel, K_zero, one_smul]
    ring
  · simp only [rhoF, smul_assoc, mul_smul, E_smul_tmul, F_smul_tmul, K_smul_tmul, map_add,
      smul_add, LinearMap.add_apply, map_smul, form_tmul, smul_eq_mul,
      h₁ (F R v i), h₂ (F R v i), h₂ (K R v (-ktilde R i)), rho_F, rho_K]
    rw [← mul_smul (K R v (-ktilde R i)) (Kt R v i), K_add, neg_add_cancel, K_zero, one_smul]
    ring
  · simp only [K_smul_tmul, form_tmul, h₁ (K R v μ), h₂ (K R v μ), rho_K]

end TensorModule

end LieLean.QuantumGroup
