/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.Form

/-!
# The elements `u 1_λ` of `U̇`

Elementary identities for the left action of `U` on `U̇` ([Lus] 23.1.3) and for the elements
`u 1_λ`, used when comparing `U̇` with other presentations and its form ([Lus] 26.1.2).

## Main definitions and results

* `QuantumGroup.Modified.leftActOne λ : U →ₗ U̇`, `u ↦ u 1_λ`, with `leftActOne_eq_elt`
  (`u 1_λ = π_{λ+χ,λ}(u)` for `u ∈ U_χ`) and `leftActOne_K` (`K_μ 1_λ = v^{⟨μ,λ⟩} 1_λ`).
* `QuantumGroup.Modified.leftAct_mul_right`: `u (x y) = (u x) y`.
* `QuantumGroup.Modified.leftActOne_mul_leftActOne`:
  `u 1_μ · u' 1_ν = δ_{μ, ν + χ'} u u' 1_ν` for `u'` of weight `χ'`.
* `QuantumGroup.Modified.form_one_mul`: `(1_ν x, y) = (x, 1_ν y)`.
* `QuantumGroup.Modified.one_mul_leftAct_rho_E`, `one_mul_leftAct_rho_F`: the action of `ρ(Eᵢ)`,
  `ρ(Fᵢ)` (Lusztig's `ρ`, [Lus] 19.1.1) after `1_ν`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.1.3, 26.1.2.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup.Modified

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) {v : k} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-- `u ↦ u 1_λ`, the left action of `U` on `1_λ ∈ U̇`. -/
def leftActOne (μ : Y →+ ℤ) : QuantumGroup R v →ₗ[k] Modified R v :=
  (leftAct R v hv).flip (one μ)

variable {R}

theorem leftActOne_apply (μ : Y →+ ℤ) (u : QuantumGroup R v) :
    leftActOne R hv μ u = leftAct R v hv u (one μ) :=
  rfl

theorem leftActOne_one (μ : Y →+ ℤ) : leftActOne R hv μ 1 = one μ :=
  leftAct_one hv _

/-- `u 1_λ = π_{λ+χ,λ}(u)` for `u ∈ U_χ`. -/
theorem leftActOne_eq_elt {χ : Y →+ ℤ} {u : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v χ) (μ : Y →+ ℤ) :
    leftActOne R hv μ u = elt (μ + χ) μ u (by simpa using hu) :=
  leftAct_one_eq_elt hv _

open scoped Classical in
/-- `1_ν π_{λ',λ''}(t) = δ_{ν,λ'} π_{λ',λ''}(t)`. -/
theorem one_mul_elt_eq_ite (ν : Y →+ ℤ) {l₁ l₂ : Y →+ ℤ} {t : QuantumGroup R v}
    (ht : t ∈ adWeightSpace R v (l₁ - l₂)) :
    one ν * elt l₁ l₂ t ht = if ν = l₁ then elt l₁ l₂ t ht else 0 := by
  split_ifs with h
  · subst h
    exact one_mul_elt _ _ _
  · exact elt_mul_elt_of_ne h _ _

/-- `u (x y) = (u x) y`: the left action commutes with right multiplication. -/
theorem leftAct_mul_right (u : QuantumGroup R v) (x y : Modified R v) :
    leftAct R v hv u (x * y) = leftAct R v hv u x * y := by
  induction u using induction_adWeightSpace with
  | h0 => simp
  | hadd a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_mul]
  | hhom χ u hu =>
  induction x using induction_on with
  | h0 => simp
  | hadd x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | helt l₁ l₂ s hs =>
  induction y using induction_on with
  | h0 => simp
  | hadd y y' hy hy' => simp only [mul_add, map_add, hy, hy']
  | helt m₁ m₂ t ht =>
    rw [leftAct_elt hv hu]
    by_cases h : l₂ = m₁
    · subst h
      rw [elt_mul_elt, elt_mul_elt, leftAct_elt hv hu]
      exact elt_index rfl rfl (mul_assoc u s t).symm _ _
    · rw [elt_mul_elt_of_ne h, elt_mul_elt_of_ne h, map_zero]

open scoped Classical in
/-- `u 1_μ · u' 1_ν = δ_{μ, ν + χ'} u u' 1_ν` for `u'` of weight `χ'`. -/
theorem leftActOne_mul_leftActOne {χ χ' : Y →+ ℤ} {u u' : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v χ) (hu' : u' ∈ adWeightSpace R v χ') (μ ν : Y →+ ℤ) :
    leftActOne R hv μ u * leftActOne R hv ν u' =
      if μ = ν + χ' then leftActOne R hv ν (u * u') else 0 := by
  rw [leftActOne_eq_elt hv hu, leftActOne_eq_elt hv hu']
  split_ifs with h
  · subst h
    rw [elt_mul_elt, leftActOne_eq_elt hv (mul_mem_adWeightSpace hu hu')]
    exact elt_index (by abel) rfl rfl _ _
  · exact elt_mul_elt_of_ne h _ _

/-- `u 1_μ · w = u (1_μ w)`. -/
theorem leftActOne_mul (μ : Y →+ ℤ) (u : QuantumGroup R v) (w : Modified R v) :
    leftActOne R hv μ u * w = leftAct R v hv u (one μ * w) := by
  rw [leftAct_mul_right, leftActOne_apply]

/-- `K_x π_{λ',λ''}(t) = v^{⟨x,λ'⟩} π_{λ',λ''}(t)`. -/
theorem leftAct_K_elt (x : Y) {l₁ l₂ : Y →+ ℤ} {t : QuantumGroup R v}
    (ht : t ∈ adWeightSpace R v (l₁ - l₂)) :
    leftAct R v hv (K R v x) (elt l₁ l₂ t ht) = v ^ l₁ x • elt l₁ l₂ t ht := by
  have h2 : K R v x * t ∈ adWeightSpace R v (l₁ - l₂) := by
    simpa using mul_mem_adWeightSpace (K_mem_adWeightSpace x) ht
  rw [leftAct_elt hv (K_mem_adWeightSpace x), elt_index (add_zero l₁) rfl rfl _ h2,
    elt_K_mul l₁ l₂ x ht h2]

/-- `K_x 1_λ = v^{⟨x,λ⟩} 1_λ`. -/
theorem leftActOne_K (μ : Y →+ ℤ) (x : Y) :
    leftActOne R hv μ (K R v x) = v ^ μ x • one μ := by
  rw [leftActOne_apply, one, leftAct_K_elt]

/-- `(1_ν x, y) = (x, 1_ν y)` for Lusztig's form on `U̇`. -/
theorem form_one_mul (ν : Y →+ ℤ) (x y : Modified R v) :
    form R v hv (one ν * x) y = form R v hv x (one ν * y) := by
  induction x using induction_on with
  | h0 => simp
  | hadd x x' hx hx' =>
    rw [mul_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hx, hx']
  | helt l₁ l₂ s hs =>
  induction y using induction_on with
  | h0 => simp
  | hadd y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy']
  | helt m₁ m₂ t ht =>
    rw [one_mul_elt_eq_ite, one_mul_elt_eq_ite]
    split_ifs with h1 h2 h2
    · rfl
    · rw [map_zero, form_elt_elt_of_ne hv]
      intro h
      exact h2 (h1.trans (Prod.mk.inj h).1)
    · rw [map_zero, LinearMap.zero_apply, form_elt_elt_of_ne hv]
      intro h
      exact h1 (h2.trans (Prod.mk.inj h).1.symm)
    · simp

/-- `1_ν ρ(Eᵢ) w = vᵢ v^{⟨K̃ᵢ, ν⟩} Fᵢ 1_{ν+αᵢ} w`. -/
theorem one_mul_leftAct_rho_E (i : I) (ν : Y →+ ℤ) (w : Modified R v) :
    one ν * leftAct R v hv (rho R v (E R v i)) w =
      (v ^ D.d i * v ^ ν (ktilde R i)) • leftAct R v hv (F R v i) (one (ν + R.root i) * w) := by
  induction w using induction_on with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, mul_add, hx, hy, mul_add, map_add, smul_add]
  | helt m₁ m₂ t ht =>
    rw [rho_E, rhoE, map_smul, LinearMap.smul_apply, leftAct_mul,
      leftAct_elt hv (F_mem_adWeightSpace i), leftAct_K_elt, mul_smul_comm, mul_smul_comm,
      one_mul_elt_eq_ite, one_mul_elt_eq_ite]
    by_cases h : ν = m₁ + -R.root i
    · rw [ite_eq_left h, ite_eq_left (by rw [h]; abel),
        leftAct_elt hv (F_mem_adWeightSpace i), smul_smul, h]
    · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (by rw [← h']; abel)), smul_zero, map_zero,
        smul_zero, smul_zero]

/-- `1_ν ρ(Fᵢ) w = vᵢ v^{-⟨K̃ᵢ, ν⟩} Eᵢ 1_{ν-αᵢ} w`. -/
theorem one_mul_leftAct_rho_F (i : I) (ν : Y →+ ℤ) (w : Modified R v) :
    one ν * leftAct R v hv (rho R v (F R v i)) w =
      (v ^ D.d i * v ^ ν (-ktilde R i)) •
        leftAct R v hv (E R v i) (one (ν - R.root i) * w) := by
  induction w using induction_on with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, mul_add, hx, hy, mul_add, map_add, smul_add]
  | helt m₁ m₂ t ht =>
    rw [rho_F, rhoF, map_smul, LinearMap.smul_apply, leftAct_mul,
      leftAct_elt hv (E_mem_adWeightSpace i), leftAct_K_elt, mul_smul_comm, mul_smul_comm,
      one_mul_elt_eq_ite, one_mul_elt_eq_ite]
    by_cases h : ν = m₁ + R.root i
    · rw [ite_eq_left h, ite_eq_left (by rw [h]; abel),
        leftAct_elt hv (E_mem_adWeightSpace i), smul_smul, h]
    · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (by rw [← h']; abel)), smul_zero, map_zero,
        smul_zero, smul_zero]

end LieLean.QuantumGroup.Modified
