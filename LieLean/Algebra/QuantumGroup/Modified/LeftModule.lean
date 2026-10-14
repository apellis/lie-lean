/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.Quotient

/-!
# `U̇` as a left `U`-module

The modified quantum group `U̇` is a `U`-bimodule ([Lus] 23.1.3): for `u ∈ U` of weight `χ` (for
conjugation by the torus, `adWeightSpace R v χ`) and `t ∈ U_{λ'-λ''}`, `u · π_{λ',λ''}(t) =
π_{λ'+χ,λ''}(ut)`. Since `U = ⊕_χ U_χ` (`isInternal_adWeightSpace`, `v ≠ 0` not a root of unity),
this determines the action of every `u ∈ U`. We construct the left action as a bilinear map
(it depends on the hypothesis on `v`, so it is not registered as an instance); the right action is
not needed here.

## Main definitions and results

* `QuantumGroup.Modified.leftAct`: the action `U × U̇ → U̇`.
* `QuantumGroup.Modified.leftAct_elt`: `u · π_{λ',λ''}(t) = π_{λ'+χ,λ''}(ut)` for `u ∈ U_χ`.
* `QuantumGroup.Modified.leftAct_mul`, `leftAct_one`: it is an action.
* `QuantumGroup.Modified.leftAct_one_eq_elt`: `u · 1_λ'' = π_{λ',λ''}(u)`.
* `QuantumGroup.induction_adWeightSpace`: elements of `U` are sums of homogeneous ones.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.1.3.
-/

open LieLean DirectSum

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]

lemma mul_mem_adWeightSpace_add_sub {χ l₁ l₂ : Y →+ ℤ} {a b : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v χ) (hb : b ∈ adWeightSpace R v (l₁ - l₂)) :
    a * b ∈ adWeightSpace R v ((l₁ + χ) - l₂) := by
  rw [show (l₁ + χ) - l₂ = χ + (l₁ - l₂) by abel]
  exact mul_mem_adWeightSpace ha hb

lemma mul_mem_modRel_add {χ l₁ l₂ : Y →+ ℤ} {a b : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v χ) (hb : b ∈ modRel R v l₁ l₂) :
    a * b ∈ modRel R v (l₁ + χ) l₂ := by
  refine mul_mem_modRel_right ?_ hb
  rwa [add_sub_cancel_left]

/-- Every element of `U` is a finite sum of elements homogeneous for conjugation by the torus. -/
theorem induction_adWeightSpace {P : QuantumGroup R v → Prop} (u : QuantumGroup R v) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hhom : ∀ χ x, x ∈ adWeightSpace R v χ → P x) : P u := by
  have hu : u ∈ ⨆ χ, adWeightSpace R v χ := by rw [iSup_adWeightSpace R v]; trivial
  exact Submodule.iSup_induction (adWeightSpace R v) (motive := P) hu hhom h0 hadd

namespace Modified

attribute [local instance] decEqIdx

/-- A decidable equality on weights (classical), used for the decomposition `U = ⊕_χ U_χ`. -/
noncomputable abbrev decEqChar : DecidableEq (Y →+ ℤ) := Classical.decEq _

attribute [local instance] decEqChar

/-- The product `U_χ × U_{λ'-λ''} → U_{λ'+χ-λ''}`. -/
def actAux (χ : Y →+ ℤ) (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    adWeightSpace R v χ →ₗ[k] adWeightSpace R v (p.1 - p.2) →ₗ[k]
      adWeightSpace R v ((p.1 + χ) - p.2) :=
  LinearMap.mk₂ k (fun a b ↦ ⟨a.1 * b.1, mul_mem_adWeightSpace_add_sub a.2 b.2⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul _ _ _)) (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ ↦ Subtype.ext (mul_add _ _ _)) (fun _ _ _ ↦ Subtype.ext (mul_smul_comm _ _ _))

lemma actComp_aux (χ : Y →+ ℤ) (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    (modRel R v p.1 p.2).comap (adWeightSpace R v (p.1 - p.2)).subtype ≤
      LinearMap.ker ((actAux (R := R) (v := v) χ p).compr₂
        (Comp.mk R v (p.1 + χ, p.2))).flip := fun b hb ↦ by
  rw [LinearMap.mem_ker]
  ext a
  exact (Comp.mk_eq_zero (p := (p.1 + χ, p.2))).2 (mul_mem_modRel_add a.2 hb)

/-- The action `U_χ × ₗU_λ'' → ₗ₊χU_λ''`, `u · π(t) = π(ut)`. -/
def actComp (χ : Y →+ ℤ) (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    adWeightSpace R v χ →ₗ[k] Comp R v p →ₗ[k] Comp R v (p.1 + χ, p.2) :=
  (Submodule.liftQ _ _ (actComp_aux χ p)).flip

lemma actComp_mk (χ : Y →+ ℤ) (p : (Y →+ ℤ) × (Y →+ ℤ)) (a : adWeightSpace R v χ)
    (b : adWeightSpace R v (p.1 - p.2)) :
    actComp χ p a (Comp.mk R v p b) = Comp.mk R v (p.1 + χ, p.2) (actAux χ p a b) :=
  rfl

/-- The action of `U_χ` on `U̇`. -/
def actHom (χ : Y →+ ℤ) : adWeightSpace R v χ →ₗ[k] Modified R v →ₗ[k] Modified R v :=
  (DirectSum.toModule k _ _ fun p ↦
    ((actComp χ p).compr₂ (DirectSum.lof k _ (Comp R v) (p.1 + χ, p.2))).flip).flip

lemma actHom_elt (χ : Y →+ ℤ) (a : adWeightSpace R v χ) (l₁ l₂ : Y →+ ℤ)
    {t : QuantumGroup R v} (ht : t ∈ adWeightSpace R v (l₁ - l₂)) :
    actHom χ a (elt l₁ l₂ t ht) =
      elt (l₁ + χ) l₂ (a.1 * t) (mul_mem_adWeightSpace_add_sub a.2 ht) := by
  rw [actHom, LinearMap.flip_apply, elt, DirectSum.toModule_lof, LinearMap.flip_apply,
    LinearMap.compr₂_apply]
  rfl

variable (R v) in
/-- The decomposition `U ≃ ⊕_χ U_χ` (`v ≠ 0` not a root of unity). -/
def adDecompose (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    QuantumGroup R v ≃ₗ[k] ⨁ χ, adWeightSpace R v χ :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (adWeightSpace R v))
    (by
      have h := isInternal_adWeightSpace R hv
      unfold DirectSum.IsInternal at h
      convert h using 1
      funext x
      induction x using DirectSum.induction_on with
      | zero => simp
      | of χ y => simp
      | add x y hx hy => simp only [map_add, hx, hy])).symm

lemma adDecompose_of_mem (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {χ : Y →+ ℤ}
    {u : QuantumGroup R v} (hu : u ∈ adWeightSpace R v χ) :
    adDecompose R v hv u = DirectSum.lof k _ (fun χ ↦ adWeightSpace R v χ) χ ⟨u, hu⟩ := by
  rw [adDecompose, LinearEquiv.symm_apply_eq]
  change u = DirectSum.coeLinearMap _ (DirectSum.lof k _ (fun χ ↦ adWeightSpace R v χ) χ ⟨u, hu⟩)
  rw [DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]

variable (R v) in
/-- **The left action of `U` on `U̇`** ([Lus] 23.1.3), as a bilinear map:
`u · π_{λ',λ''}(t) = π_{λ'+χ,λ''}(ut)` for `u ∈ U_χ`. -/
def leftAct (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    QuantumGroup R v →ₗ[k] Modified R v →ₗ[k] Modified R v :=
  (DirectSum.toModule k _ _ fun χ ↦ actHom χ) ∘ₗ (adDecompose R v hv).toLinearMap

lemma leftAct_elt (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {χ : Y →+ ℤ} {u : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v χ) (l₁ l₂ : Y →+ ℤ) {t : QuantumGroup R v}
    (ht : t ∈ adWeightSpace R v (l₁ - l₂)) :
    leftAct R v hv u (elt l₁ l₂ t ht) =
      elt (l₁ + χ) l₂ (u * t) (mul_mem_adWeightSpace_add_sub hu ht) := by
  rw [leftAct, LinearMap.comp_apply, LinearEquiv.coe_coe, adDecompose_of_mem hv hu,
    DirectSum.toModule_lof, actHom_elt]

lemma leftAct_zero_left (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (x : Modified R v) :
    leftAct R v hv 0 x = 0 := by
  rw [map_zero, LinearMap.zero_apply]

/-- `u · (u' · x) = (u u') · x`. -/
theorem leftAct_mul (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (u u' : QuantumGroup R v)
    (x : Modified R v) :
    leftAct R v hv (u * u') x = leftAct R v hv u (leftAct R v hv u' x) := by
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
    rw [leftAct_elt hv (mul_mem_adWeightSpace ha hb), leftAct_elt hv hb, leftAct_elt hv ha]
    exact elt_index (by abel) rfl (mul_assoc _ _ _) _ _

/-- `1 · x = x`. -/
theorem leftAct_one (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (x : Modified R v) :
    leftAct R v hv 1 x = x := by
  induction x using induction_on with
  | h0 => simp
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | helt l₁ l₂ t ht =>
    rw [leftAct_elt hv one_mem_adWeightSpace]
    exact elt_index (add_zero l₁) rfl (one_mul t) _ _

/-- `u · 1_λ'' = π_{λ',λ''}(u)` for `u ∈ U_{λ'-λ''}`. -/
theorem leftAct_one_eq_elt (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {l₁ l₂ : Y →+ ℤ}
    {u : QuantumGroup R v} (hu : u ∈ adWeightSpace R v (l₁ - l₂)) :
    leftAct R v hv u (one l₂) = elt l₁ l₂ u hu := by
  rw [one, leftAct_elt hv hu]
  exact elt_index (by abel) rfl (mul_one u) _ _

end Modified

end LieLean.QuantumGroup
