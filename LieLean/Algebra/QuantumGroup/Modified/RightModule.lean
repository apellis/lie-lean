/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.LeftModule

/-!
# `U̇` as a right `U`-module

For `u ∈ U` of weight `χ` (`adWeightSpace R v χ`) and `t ∈ U_{λ'-λ''}`,
`π_{λ',λ''}(t) · u = π_{λ',λ''-χ}(tu)` ([Lus] 23.1.3). As for the left action
(`Modified.leftAct`), the decomposition `U = ⊕_χ U_χ` (`v ≠ 0` not a root of unity) extends this
to all of `U`.

## Main definitions and results

* `QuantumGroup.Modified.rightAct`: the action `U̇ × U → U̇`, `rightAct u x = x · u`.
* `QuantumGroup.Modified.rightAct_elt`: `π_{λ',λ''}(t) · u = π_{λ',λ''-χ}(tu)` for `u ∈ U_χ`.
* `QuantumGroup.Modified.rightAct_mul`, `rightAct_one`: it is a right action.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.1.3.
-/

open LieLean DirectSum

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]

lemma mul_mem_adWeightSpace_sub_sub {χ l₁ l₂ : Y →+ ℤ} {a b : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (l₁ - l₂)) (hb : b ∈ adWeightSpace R v χ) :
    a * b ∈ adWeightSpace R v (l₁ - (l₂ - χ)) := by
  rw [show l₁ - (l₂ - χ) = (l₁ - l₂) + χ by abel]
  exact mul_mem_adWeightSpace ha hb

lemma mul_mem_modRel_sub {χ l₁ l₂ : Y →+ ℤ} {a b : QuantumGroup R v}
    (ha : a ∈ modRel R v l₁ l₂) (hb : b ∈ adWeightSpace R v χ) :
    a * b ∈ modRel R v l₁ (l₂ - χ) :=
  mul_mem_modRel_left ha (by rwa [sub_sub_cancel])

namespace Modified

attribute [local instance] decEqIdx decEqChar

/-- The product `U_{λ'-λ''} × U_χ → U_{λ'-(λ''-χ)}`. -/
def ractAux (χ : Y →+ ℤ) (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    adWeightSpace R v (p.1 - p.2) →ₗ[k] adWeightSpace R v χ →ₗ[k]
      adWeightSpace R v (p.1 - (p.2 - χ)) :=
  LinearMap.mk₂ k (fun a b ↦ ⟨a.1 * b.1, mul_mem_adWeightSpace_sub_sub a.2 b.2⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul _ _ _)) (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ ↦ Subtype.ext (mul_add _ _ _)) (fun _ _ _ ↦ Subtype.ext (mul_smul_comm _ _ _))

/-- The action `ₗU_λ'' × U_χ → ₗU_{λ''-χ}`, `π(t) · u = π(tu)`. -/
def ractComp (χ : Y →+ ℤ) (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    Comp R v p →ₗ[k] adWeightSpace R v χ →ₗ[k] Comp R v (p.1, p.2 - χ) :=
  Submodule.liftQ _ ((ractAux (R := R) (v := v) χ p).compr₂ (Comp.mk R v (p.1, p.2 - χ)))
    fun _ ha ↦ LinearMap.ext fun b ↦
      (Comp.mk_eq_zero (p := (p.1, p.2 - χ))).2 (mul_mem_modRel_sub ha b.2)

/-- The action of `U_χ` on `U̇` from the right. -/
def ractHom (χ : Y →+ ℤ) : adWeightSpace R v χ →ₗ[k] Modified R v →ₗ[k] Modified R v :=
  (DirectSum.toModule k _ _ fun p ↦
    (ractComp χ p).compr₂ (DirectSum.lof k _ (Comp R v) (p.1, p.2 - χ))).flip

lemma ractHom_elt (χ : Y →+ ℤ) (b : adWeightSpace R v χ) (l₁ l₂ : Y →+ ℤ)
    {t : QuantumGroup R v} (ht : t ∈ adWeightSpace R v (l₁ - l₂)) :
    ractHom χ b (elt l₁ l₂ t ht) =
      elt l₁ (l₂ - χ) (t * b.1) (mul_mem_adWeightSpace_sub_sub ht b.2) := by
  rw [ractHom, LinearMap.flip_apply, elt, DirectSum.toModule_lof, LinearMap.compr₂_apply]
  rfl

variable (R v) in
/-- **The right action of `U` on `U̇`** ([Lus] 23.1.3), as a bilinear map:
`rightAct u x = x · u`, with `π_{λ',λ''}(t) · u = π_{λ',λ''-χ}(tu)` for `u ∈ U_χ`. -/
def rightAct (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    QuantumGroup R v →ₗ[k] Modified R v →ₗ[k] Modified R v :=
  (DirectSum.toModule k _ _ fun χ ↦ ractHom χ) ∘ₗ (adDecompose R v hv).toLinearMap

lemma rightAct_elt (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {χ : Y →+ ℤ} {u : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v χ) (l₁ l₂ : Y →+ ℤ) {t : QuantumGroup R v}
    (ht : t ∈ adWeightSpace R v (l₁ - l₂)) :
    rightAct R v hv u (elt l₁ l₂ t ht) =
      elt l₁ (l₂ - χ) (t * u) (mul_mem_adWeightSpace_sub_sub ht hu) := by
  rw [rightAct, LinearMap.comp_apply, LinearEquiv.coe_coe, adDecompose_of_mem hv hu,
    DirectSum.toModule_lof, ractHom_elt]

/-- `(x · u) · u' = x · (u u')`. -/
theorem rightAct_mul (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (u u' : QuantumGroup R v)
    (x : Modified R v) :
    rightAct R v hv (u * u') x = rightAct R v hv u' (rightAct R v hv u x) := by
  induction u using induction_adWeightSpace with
  | h0 => simp
  | hadd a b ha hb => simp only [add_mul, map_add, LinearMap.add_apply, ha, hb]
  | hhom χ a ha =>
  induction u' using induction_adWeightSpace with
  | h0 => simp
  | hadd b c hb hc => simp only [mul_add, map_add, LinearMap.add_apply, hb, hc]
  | hhom χ' b hb =>
  induction x using induction_on with
  | h0 => simp
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | helt l₁ l₂ t ht =>
    rw [rightAct_elt hv (mul_mem_adWeightSpace ha hb), rightAct_elt hv ha, rightAct_elt hv hb]
    exact elt_index rfl (by abel) (mul_assoc _ _ _).symm _ _

/-- `x · 1 = x`. -/
theorem rightAct_one (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (x : Modified R v) :
    rightAct R v hv 1 x = x := by
  induction x using induction_on with
  | h0 => simp
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | helt l₁ l₂ t ht =>
    rw [rightAct_elt hv one_mem_adWeightSpace]
    exact elt_index rfl (sub_zero l₂) (mul_one t) _ _

end Modified

end LieLean.QuantumGroup
