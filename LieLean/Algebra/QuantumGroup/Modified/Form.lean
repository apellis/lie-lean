/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.FormFunctional

/-!
# The symmetric bilinear form on `U̇`

Lusztig's form `(,) : U̇ × U̇ → k` ([Lus] 26.1.2) is the unique bilinear form with
* (a) `(1_λ x 1_λ', 1_μ y 1_μ') = 0` unless `λ = μ` and `λ' = μ'`;
* (b) `(u x, y) = (x, ρ̄(u) y)` for `u ∈ U`;
* (c) `(x⁻ 1_λ, y⁻ 1_λ) = (x, y)` for `x, y ∈ 'f`;

and it is symmetric (d). Here `U` acts on `U̇` by `Modified.leftAct` and `ρ̄` is
`QuantumGroup.rhoBar` (26.1.1). On the components,
`(π_{λ',λ''}(a), π_{λ',λ''}(b)) = P_{λ''}(ρ̄(a) b)` with `P_ζ = formFunctional`, and the form is
zero between different components.

## Main definitions and results

* `QuantumGroup.Modified.form`: the form `(,)` on `U̇`.
* `QuantumGroup.Modified.form_one_mul_mul_one_eq_zero`, `form_leftAct_left`,
  `form_minusHom_leftAct_one`, `form_comm`: (a)–(d) of [Lus] 26.1.2.
* `QuantumGroup.Modified.eq_form`: uniqueness.

Lusztig works over `ℚ(v)`; we work over any field `k` with `v ≠ 0` not a root of unity (which is
what the triangular decomposition and the action of `U` on `U̇` use).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 26.1.2.
-/

open LieLean LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace Modified

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

attribute [local instance] decEqIdx

section Descend

include hv

lemma formFunctional_rhoBar_mul_eq_zero_left {l₁ l₂ : Y →+ ℤ} {a b : QuantumGroup R v}
    (ha : a ∈ modRel R v l₁ l₂) (hb : b ∈ adWeightSpace R v (l₁ - l₂)) :
    formFunctional R v hv l₂ (rhoBar R v a * b) = 0 := by
  have hv0 := NeZero.ne v
  induction ha using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨μ, u, hu, rfl⟩ | ⟨μ, u, hu, rfl⟩
    · have hub : rhoBar R v u * b ∈ adWeightSpace R v 0 := by
        simpa using mul_mem_adWeightSpace (rhoBar_mem_adWeightSpace hu) hb
      rw [rhoBar_mul, map_sub, rhoBar_K, rhoBar_algebraMap, mul_sub, sub_mul,
        ← Algebra.commutes, ← Algebra.smul_def, smul_mul_assoc, map_sub, map_smul, mul_assoc,
        hb μ, mul_smul_comm, ← mul_assoc, map_smul, formFunctional_mul_K, smul_eq_mul,
        smul_eq_mul, ← mul_assoc, ← zpow_add₀ hv0, AddMonoidHom.sub_apply, sub_add_cancel,
        sub_self]
    · have hub : rhoBar R v u * b ∈ adWeightSpace R v 0 := by
        simpa using mul_mem_adWeightSpace (rhoBar_mem_adWeightSpace hu) hb
      rw [rhoBar_mul, map_sub, rhoBar_K, rhoBar_algebraMap, sub_mul, sub_mul, mul_assoc,
        mul_assoc, ← Algebra.smul_def, map_sub, map_smul, formFunctional_K_mul hv _ hub,
        smul_eq_mul, sub_self]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, add_mul, map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, smul_mul_assoc, map_smul, hx, smul_zero]

lemma formFunctional_rhoBar_mul_eq_zero_right {l₁ l₂ : Y →+ ℤ} {a b : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (l₁ - l₂)) (hb : b ∈ modRel R v l₁ l₂) :
    formFunctional R v hv l₂ (rhoBar R v a * b) = 0 := by
  have hv0 := NeZero.ne v
  have ha' := rhoBar_mem_adWeightSpace ha
  induction hb using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨μ, u, hu, rfl⟩ | ⟨μ, u, hu, rfl⟩
    · have hau : rhoBar R v a * u ∈ adWeightSpace R v 0 := by
        simpa using mul_mem_adWeightSpace ha' hu
      rw [sub_mul, mul_sub, ← Algebra.smul_def, mul_smul_comm, map_sub,
        map_smul, ← mul_assoc, mul_K_of_mem_adWeightSpace ha', smul_mul_assoc, mul_assoc,
        map_smul, formFunctional_K_mul hv _ hau, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        ← zpow_add₀ hv0]
      simp only [AddMonoidHom.neg_apply, neg_neg, AddMonoidHom.sub_apply, sub_add_cancel,
        sub_self]
    · rw [mul_sub, mul_sub, ← Algebra.commutes, ← Algebra.smul_def, mul_smul_comm, ← mul_assoc,
        map_sub, map_smul, formFunctional_mul_K, smul_eq_mul, sub_self]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [mul_smul_comm, map_smul, hx, smul_zero]

variable (R v) in
/-- `(a, b) ↦ P_{λ''}(ρ̄(a) b)` on `U_{λ'-λ''}`. -/
def formEltAux (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    adWeightSpace R v (p.1 - p.2) →ₗ[k] adWeightSpace R v (p.1 - p.2) →ₗ[k] k :=
  ((LinearMap.mul k (QuantumGroup R v)).compr₂ (formFunctional R v hv p.2)).compl₁₂
    (rhoBar R v ∘ₗ (adWeightSpace R v (p.1 - p.2)).subtype) (adWeightSpace R v (p.1 - p.2)).subtype

lemma formEltAux_apply (p : (Y →+ ℤ) × (Y →+ ℤ)) (a b : adWeightSpace R v (p.1 - p.2)) :
    formEltAux R v hv p a b = formFunctional R v hv p.2 (rhoBar R v a.1 * b.1) := rfl

variable (R v) in
/-- The form on `ₗU_λ''` descended in the second variable. -/
def formComp₁ (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    adWeightSpace R v (p.1 - p.2) →ₗ[k] Comp R v p →ₗ[k] k :=
  (Submodule.liftQ _ (formEltAux R v hv p).flip fun _ hb ↦ LinearMap.ext fun a ↦
    formFunctional_rhoBar_mul_eq_zero_right hv a.2 hb).flip

variable (R v) in
/-- The form on the component `ₗU_λ''`, `(π(a), π(b)) = P_{λ''}(ρ̄(a) b)`. -/
def formComp (p : (Y →+ ℤ) × (Y →+ ℤ)) : Comp R v p →ₗ[k] Comp R v p →ₗ[k] k :=
  Submodule.liftQ _ (formComp₁ R v hv p) fun _ ha ↦ LinearMap.ext fun b ↦ by
    obtain ⟨b, rfl⟩ := Comp.mk_surjective R v p b
    exact formFunctional_rhoBar_mul_eq_zero_left hv ha b.2

lemma formComp_mk (p : (Y →+ ℤ) × (Y →+ ℤ)) (a b : adWeightSpace R v (p.1 - p.2)) :
    formComp R v hv p (Comp.mk R v p a) (Comp.mk R v p b) =
      formFunctional R v hv p.2 (rhoBar R v a.1 * b.1) := rfl

end Descend

variable (R v) in
/-- **Lusztig's bilinear form on `U̇`** ([Lus] 26.1.2): `(π_{λ',λ''}(a), π_{λ',λ''}(b)) =
P_{λ''}(ρ̄(a) b)` and different components are orthogonal. -/
def form : Modified R v →ₗ[k] Modified R v →ₗ[k] k :=
  DirectSum.toModule k _ _ fun p ↦
    (formComp R v hv p).compl₂ (DirectSum.component k _ (Comp R v) p)

lemma form_elt_elt_self (l₁ l₂ : Y →+ ℤ) {a b : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (l₁ - l₂)) (hb : b ∈ adWeightSpace R v (l₁ - l₂)) :
    form R v hv (elt l₁ l₂ a ha) (elt l₁ l₂ b hb) =
      formFunctional R v hv l₂ (rhoBar R v a * b) := by
  rw [form, elt, DirectSum.toModule_lof, LinearMap.compl₂_apply, elt, DirectSum.component.lof_self]
  rfl

lemma form_elt_elt_of_ne {l₁ l₂ m₁ m₂ : Y →+ ℤ} (h : (l₁, l₂) ≠ (m₁, m₂)) {a b : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (l₁ - l₂)) (hb : b ∈ adWeightSpace R v (m₁ - m₂)) :
    form R v hv (elt l₁ l₂ a ha) (elt m₁ m₂ b hb) = 0 := by
  rw [form, elt, DirectSum.toModule_lof, LinearMap.compl₂_apply, elt, DirectSum.component.of]
  split_ifs with h'
  · exact absurd h' (Ne.symm h)
  · exact map_zero _

lemma form_elt_elt {l₁ l₂ m₁ m₂ : Y →+ ℤ} {a b : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (l₁ - l₂)) (hb : b ∈ adWeightSpace R v (m₁ - m₂)) :
    form R v hv (elt l₁ l₂ a ha) (elt m₁ m₂ b hb) =
      if (l₁, l₂) = (m₁, m₂) then formFunctional R v hv l₂ (rhoBar R v a * b) else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact form_elt_elt_self hv l₁ l₂ ha hb
  · exact form_elt_elt_of_ne hv h ha hb

/-! ### Properties (a)–(c) -/

lemma one_mul_mul_one (l₁ l₂ m₁ m₂ : Y →+ ℤ) {a : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (m₁ - m₂)) :
    one l₁ * elt m₁ m₂ a ha * one l₂ = if (l₁, l₂) = (m₁, m₂) then elt m₁ m₂ a ha else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rw [one_mul_elt, elt_mul_one]
  · by_cases h₁ : l₁ = m₁
    · subst h₁
      have h₂ : m₂ ≠ l₂ := fun h₂ ↦ h (by rw [h₂])
      rw [one_mul_elt, one, elt_mul_elt_of_ne h₂]
    · rw [one, elt_mul_elt_of_ne h₁, zero_mul]

/-- **[Lus] 26.1.2 (a)**: `(1_λ x 1_λ', 1_μ y 1_μ') = 0` unless `(λ, λ') = (μ, μ')`. -/
theorem form_one_mul_mul_one_eq_zero {l₁ l₂ m₁ m₂ : Y →+ ℤ} (h : (l₁, l₂) ≠ (m₁, m₂))
    (x y : Modified R v) : form R v hv (one l₁ * x * one l₂) (one m₁ * y * one m₂) = 0 := by
  induction x using induction_on with
  | h0 => simp
  | hadd x x' hx hx' => rw [mul_add', add_mul', map_add, LinearMap.add_apply, hx, hx', add_zero]
  | helt a₁ a₂ a ha =>
  induction y using induction_on with
  | h0 => simp
  | hadd y y' hy hy' => rw [mul_add', add_mul', map_add, hy, hy', add_zero]
  | helt b₁ b₂ b hb =>
    rw [one_mul_mul_one, one_mul_mul_one]
    split_ifs with h₁ h₂
    · rw [form_elt_elt_of_ne hv (by rwa [← h₁, ← h₂])]
    all_goals simp

/-- **[Lus] 26.1.2 (b)**: `(u x, y) = (x, ρ̄(u) y)` for `u ∈ U`. -/
theorem form_leftAct_left (u : QuantumGroup R v) (x y : Modified R v) :
    form R v hv (leftAct R v hv u x) y = form R v hv x (leftAct R v hv (rhoBar R v u) y) := by
  induction u using induction_adWeightSpace with
  | h0 => simp
  | hadd u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']
  | hhom χ u hu =>
  induction x using induction_on with
  | h0 => simp
  | hadd x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | helt l₁ l₂ a ha =>
  induction y using induction_on with
  | h0 => simp
  | hadd y y' hy hy' => simp only [map_add, hy, hy']
  | helt m₁ m₂ b hb =>
    rw [leftAct_elt hv hu, leftAct_elt hv (rhoBar_mem_adWeightSpace hu), form_elt_elt,
      form_elt_elt, rhoBar_mul, mul_assoc]
    have : ((l₁ + χ, l₂) = (m₁, m₂)) ↔ ((l₁, l₂) = (m₁ + -χ, m₂)) := by
      simp only [Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨by abel, rfl⟩
      · rintro ⟨rfl, rfl⟩; exact ⟨by abel, rfl⟩
    simp only [this]

/-- **[Lus] 26.1.2 (c)**: `(x⁻ 1_λ, y⁻ 1_λ) = (x, y)` for `x, y ∈ 'f`. -/
theorem form_minusHom_leftAct_one (l : Y →+ ℤ) (x y : LusztigF k I) :
    form R v hv (leftAct R v hv (minusHom R v x) (one l))
      (leftAct R v hv (minusHom R v y) (one l)) = LusztigF.form D v x y := by
  have h : ((form R v hv).compl₁₂ (leftAct R v hv ∘ₗ (minusHom R v).toLinearMap |>.flip (one l))
      (leftAct R v hv ∘ₗ (minusHom R v).toLinearMap |>.flip (one l))) = LusztigF.form D v :=
    LinearMap.ext_basis (FreeAlgebra.wordBasis k I) (FreeAlgebra.wordBasis k I) fun w w' ↦ by
      simp only [LinearMap.compl₁₂_apply, LinearMap.flip_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, wordBasis_eq_monomial]
      rw [one, leftAct_elt hv (minusHom_monomial_mem_adWeightSpace w),
        leftAct_elt hv (minusHom_monomial_mem_adWeightSpace w'), form_elt_elt]
      split_ifs with h
      · rw [mul_one, mul_one, ← mul_one (minusHom R v (monomial k w')), ← K_zero R v,
          ← mul_assoc, formFunctional_rhoBar_minusHom, map_zero, zpow_zero, one_mul]
      · refine (LusztigF.form_eq_zero_of_ne D v (fun hw ↦ h ?_) (monomial_mem_weightSpace w)
          (monomial_mem_weightSpace w')).symm
        rw [wordChar_eq_rootSum, wordChar_eq_rootSum, hw]
  exact LinearMap.congr_fun₂ h x y

/-! ### Uniqueness and symmetry -/

/-- A bilinear form on `U̇` with (a) and (b) of [Lus] 26.1.2 is determined by the values
`(1_ζ, z 1_ζ)`. -/
theorem eq_of_one_leftAct {B B' : Modified R v →ₗ[k] Modified R v →ₗ[k] k}
    (ha : ∀ l₁ l₂ m₁ m₂, (l₁, l₂) ≠ (m₁, m₂) → ∀ x y,
      B (one l₁ * x * one l₂) (one m₁ * y * one m₂) = 0)
    (ha' : ∀ l₁ l₂ m₁ m₂, (l₁, l₂) ≠ (m₁, m₂) → ∀ x y,
      B' (one l₁ * x * one l₂) (one m₁ * y * one m₂) = 0)
    (hb : ∀ u x y, B (leftAct R v hv u x) y = B x (leftAct R v hv (rhoBar R v u) y))
    (hb' : ∀ u x y, B' (leftAct R v hv u x) y = B' x (leftAct R v hv (rhoBar R v u) y))
    (h : ∀ ζ z, B (one ζ) (leftAct R v hv z (one ζ)) = B' (one ζ) (leftAct R v hv z (one ζ))) :
    B = B' := by
  refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
  induction x using induction_on with
  | h0 => simp
  | hadd x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | helt l₁ l₂ a hA =>
  induction y using induction_on with
  | h0 => simp
  | hadd y y' hy hy' => simp only [map_add, hy, hy']
  | helt m₁ m₂ b hB =>
    by_cases hlm : (l₁, l₂) = (m₁, m₂)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlm
      have hz : rhoBar R v a * b ∈ adWeightSpace R v ((l₂ + 0) - l₂) := by
        simpa using mul_mem_adWeightSpace (rhoBar_mem_adWeightSpace hA) hB
      have e : leftAct R v hv (rhoBar R v a) (elt l₁ l₂ b hB) =
          leftAct R v hv (rhoBar R v a * b) (one l₂) := by
        rw [leftAct_mul, leftAct_one_eq_elt hv hB]
      rw [← leftAct_one_eq_elt hv hA, hb, hb', e, h]
    · have e₁ := one_mul_mul_one l₁ l₂ l₁ l₂ hA
      have e₂ := one_mul_mul_one m₁ m₂ m₁ m₂ hB
      simp only [↓reduceIte] at e₁ e₂
      rw [← e₁, ← e₂, ha _ _ _ _ hlm, ha' _ _ _ _ hlm]

/-- Properties (b), (c) of [Lus] 26.1.2 determine `(1_ζ, z 1_ζ) = P_ζ(z)`. -/
theorem one_leftAct_one_eq_formFunctional {B : Modified R v →ₗ[k] Modified R v →ₗ[k] k}
    (hb : ∀ u x y, B (leftAct R v hv u x) y = B x (leftAct R v hv (rhoBar R v u) y))
    (hc : ∀ l x y, B (leftAct R v hv (minusHom R v x) (one l))
      (leftAct R v hv (minusHom R v y) (one l)) = LusztigF.form D v x y)
    (ζ : Y →+ ℤ) (z : QuantumGroup R v) :
    B (one ζ) (leftAct R v hv z (one ζ)) = formFunctional R v hv ζ z := by
  induction z using induction_rhoBar_minusHom with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, LinearMap.add_apply, map_add, map_add, hx, hy]
  | hsmul c x hx => rw [map_smul, LinearMap.smul_apply, map_smul, map_smul, hx]
  | hmon w w' μ =>
    have h1 : (1 : QuantumGroup R v) ∈ adWeightSpace R v (ζ - ζ) := by
      rw [sub_self]; exact one_mem_adWeightSpace
    have h2 : K R v μ * 1 ∈ adWeightSpace R v (ζ - ζ) := by
      rw [sub_self, mul_one]; exact K_mem_adWeightSpace μ
    have hK : leftAct R v hv (K R v μ) (one ζ) = v ^ ζ μ • one ζ := by
      rw [one, leftAct_elt hv (K_mem_adWeightSpace μ), elt_index (add_zero ζ) rfl rfl _ h2,
        elt_K_mul ζ ζ μ h1 h2]
    rw [leftAct_mul, leftAct_mul, hK, map_smul, map_smul, map_smul, ← hb, hc,
      formFunctional_rhoBar_minusHom, smul_eq_mul]

/-- **Uniqueness in [Lus] 26.1.2**: a bilinear form on `U̇` with properties (a), (b), (c) is
`Modified.form`. -/
theorem eq_form {B : Modified R v →ₗ[k] Modified R v →ₗ[k] k}
    (ha : ∀ l₁ l₂ m₁ m₂, (l₁, l₂) ≠ (m₁, m₂) → ∀ x y,
      B (one l₁ * x * one l₂) (one m₁ * y * one m₂) = 0)
    (hb : ∀ u x y, B (leftAct R v hv u x) y = B x (leftAct R v hv (rhoBar R v u) y))
    (hc : ∀ l x y, B (leftAct R v hv (minusHom R v x) (one l))
      (leftAct R v hv (minusHom R v y) (one l)) = LusztigF.form D v x y) :
    B = form R v hv :=
  eq_of_one_leftAct hv ha (fun _ _ _ _ h ↦ form_one_mul_mul_one_eq_zero hv h) hb
    (form_leftAct_left hv) fun ζ z ↦ by
      rw [one_leftAct_one_eq_formFunctional hv hb hc, one_leftAct_one_eq_formFunctional hv
        (form_leftAct_left hv) (form_minusHom_leftAct_one hv)]

/-- **[Lus] 26.1.2 (d)**: the form on `U̇` is symmetric. -/
theorem form_comm (x y : Modified R v) : form R v hv x y = form R v hv y x := by
  have h := eq_form hv (B := (form R v hv).flip)
    (fun _ _ _ _ h x y ↦ form_one_mul_mul_one_eq_zero hv (Ne.symm h) y x)
    (fun u x y ↦ by
      rw [LinearMap.flip_apply, LinearMap.flip_apply, form_leftAct_left, rhoBar_rhoBar])
    (fun l x y ↦ by rw [LinearMap.flip_apply, form_minusHom_leftAct_one, LusztigF.form_comm])
  exact (LinearMap.flip_apply _ _ _).symm.trans (LinearMap.congr_fun₂ h y x)

end Modified

end LieLean.QuantumGroup
