/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BarInvolution
import LieLean.Algebra.QuantumGroup.Modified.IntegralForm
import LieLean.Algebra.QuantumGroup.Modified.LeftActOne

/-!
# The bar involution of `U̇`

Over `ℚ(v)` (`v = RatFunc.X`), the bar involution `u ↦ ū` of `U` ([Lus] 3.1.12) preserves each
`U_χ` and each relation space `N(λ', λ'')`, so it induces maps `ₗU_λ'' → ₗU_λ''`; their direct sum
is the bar involution of `U̇` ([Lus] 23.1.8).

## Main definitions and results

* `QuantumGroup.barHom_mem_adWeightSpace`, `QuantumGroup.barHom_mem_modRel`: `ū` lies in `U_χ`,
  resp. `N(λ', λ'')`, if `u` does.
* `QuantumGroup.Modified.bar`: the bar involution of `U̇` ([Lus] 23.1.8), with `bar_elt`
  (`π_{λ',λ''}(u) ↦ π_{λ',λ''}(ū)`), `bar_smul` (semilinear for `v ↦ v⁻¹`), `bar_bar`
  (square `1`), `bar_mul` (multiplicative), `bar_one` (`1_λ ↦ 1_λ`), `bar_leftAct`
  (`\overline{t s} = t̄ s̄` for `t ∈ U`, `s ∈ U̇`) and `bar_leftActOne`
  (`\overline{u 1_λ} = ū 1_λ`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 3.1.12, 23.1.8.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "barRH" => RingHomClass.toRingHom (RatFunc.bar (K := ℚ))

attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

/-- The bar involution of `U` preserves `U_χ`. -/
theorem barHom_mem_adWeightSpace {χ : Y →+ ℤ} {x : QuantumGroup R 𝕧}
    (hx : x ∈ adWeightSpace R 𝕧 χ) : barHom R x ∈ adWeightSpace R 𝕧 χ := fun μ ↦ by
  have h := congrArg (barHom R) (hx (-μ))
  rwa [map_mul, barHom_smul, map_mul, barHom_K, neg_neg, bar_zpow_X, map_neg, neg_neg] at h

/-- The bar involution of `U` preserves `N(λ', λ'')`. -/
theorem barHom_mem_modRel {l₁ l₂ : Y →+ ℤ} {x : QuantumGroup R 𝕧}
    (hx : x ∈ modRel R 𝕧 l₁ l₂) : barHom R x ∈ modRel R 𝕧 l₁ l₂ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨μ, u, hu, rfl⟩ | ⟨μ, u, hu, rfl⟩
    · refine Submodule.subset_span (Or.inl ⟨-μ, barHom R u, barHom_mem_adWeightSpace hu, ?_⟩)
      rw [map_mul, map_sub, barHom_K, barHom_algebraMap, bar_zpow_X, map_neg]
    · refine Submodule.subset_span (Or.inr ⟨-μ, barHom R u, barHom_mem_adWeightSpace hu, ?_⟩)
      rw [map_mul, map_sub, barHom_K, barHom_algebraMap, bar_zpow_X, map_neg]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [barHom_smul]; exact Submodule.smul_mem _ _ hx

namespace Modified

attribute [local instance] decEqIdx

/-- The bar involution of `U` on `U_χ`, a semilinear map. -/
def barWeight (χ : Y →+ ℤ) :
    adWeightSpace R 𝕧 χ →ₛₗ[barRH] adWeightSpace R 𝕧 χ where
  toFun x := ⟨barHom R x, barHom_mem_adWeightSpace x.2⟩
  map_add' x y := Subtype.ext (map_add (barHom R) x.1 y.1)
  map_smul' c x := Subtype.ext (barHom_smul R c x)

/-- The bar involution on the component `ₗU_λ''`. -/
def barComp (p : (Y →+ ℤ) × (Y →+ ℤ)) : Comp R 𝕧 p →ₛₗ[barRH] Comp R 𝕧 p :=
  Submodule.mapQ _ _ (barWeight (p.1 - p.2)) fun _ hx ↦ barHom_mem_modRel hx

variable (R) in
/-- **The bar involution of `U̇`** ([Lus] 23.1.8): `π_{λ',λ''}(u) ↦ π_{λ',λ''}(ū)`. -/
def bar : Modified R 𝕧 →+ Modified R 𝕧 :=
  DirectSum.toAddMonoid fun p ↦
    (DirectSum.lof 𝕂 _ (Comp R 𝕧) p).toAddMonoidHom.comp (barComp p).toAddMonoidHom

theorem bar_elt (l₁ l₂ : Y →+ ℤ) {u : QuantumGroup R 𝕧} (hu : u ∈ adWeightSpace R 𝕧 (l₁ - l₂)) :
    bar R (elt l₁ l₂ u hu) = elt l₁ l₂ (barHom R u) (barHom_mem_adWeightSpace hu) := by
  rw [elt, DirectSum.lof_eq_of, bar, DirectSum.toAddMonoid_of]
  rfl

theorem bar_smul (c : 𝕂) (x : Modified R 𝕧) : bar R (c • x) = RatFunc.bar c • bar R x := by
  induction x using induction_on with
  | h0 => rw [smul_zero, map_zero, smul_zero]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | helt l₁ l₂ u hu =>
    rw [← elt_smul, bar_elt, bar_elt, ← elt_smul]
    exact elt_congr (barHom_smul R c u) _ _

/-- The bar involution of `U̇` has square `1`. -/
@[simp] theorem bar_bar (x : Modified R 𝕧) : bar R (bar R x) = x := by
  induction x using induction_on with
  | h0 => rw [map_zero, map_zero]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]
  | helt l₁ l₂ u hu =>
    rw [bar_elt, bar_elt]
    exact elt_congr (barHom_barHom R u) _ _

/-- The bar involution of `U̇` respects the multiplication. -/
theorem bar_mul (x y : Modified R 𝕧) : bar R (x * y) = bar R x * bar R y := by
  induction x using induction_on with
  | h0 => rw [zero_mul, map_zero, zero_mul]
  | hadd x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
  | helt a b u hu =>
  induction y using induction_on with
  | h0 => rw [mul_zero, map_zero, mul_zero]
  | hadd y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
  | helt c d w hw =>
  by_cases hbc : b = c
  · subst hbc
    rw [elt_mul_elt, bar_elt, bar_elt, bar_elt, elt_mul_elt]
    exact elt_congr (_root_.map_mul _ _ _) _ _
  · rw [elt_mul_elt_of_ne hbc, map_zero, bar_elt, bar_elt, elt_mul_elt_of_ne hbc]

/-- The bar involution of `U̇` fixes `1_λ`. -/
@[simp] theorem bar_one (l : Y →+ ℤ) : bar R (one l) = one l := by
  rw [one, bar_elt]
  exact elt_congr (_root_.map_one (barHom R)) _ _

/-- `\overline{t s} = t̄ s̄` for `t ∈ U`, `s ∈ U̇` ([Lus] 23.1.8). -/
theorem bar_leftAct (hv : ∀ n : ℕ, 0 < n → 𝕧 ^ n ≠ 1) (u : QuantumGroup R 𝕧)
    (x : Modified R 𝕧) : bar R (leftAct R 𝕧 hv u x) = leftAct R 𝕧 hv (barHom R u) (bar R x) := by
  induction u using induction_adWeightSpace with
  | h0 => simp only [map_zero, LinearMap.zero_apply]
  | hadd u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']
  | hhom χ u hχ =>
  induction x using induction_on with
  | h0 => rw [map_zero, map_zero, map_zero]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | helt l₁ l₂ t ht =>
    rw [leftAct_elt hv hχ, bar_elt, bar_elt, leftAct_elt hv (barHom_mem_adWeightSpace hχ)]
    exact elt_congr (_root_.map_mul _ _ _) _ _

/-- `\overline{u 1_λ} = ū 1_λ`. -/
theorem bar_leftActOne (hv : ∀ n : ℕ, 0 < n → 𝕧 ^ n ≠ 1) (l : Y →+ ℤ) (u : QuantumGroup R 𝕧) :
    bar R (leftActOne R hv l u) = leftActOne R hv l (barHom R u) := by
  rw [leftActOne_apply, bar_leftAct, bar_one, leftActOne_apply]

end Modified

end LieLean.QuantumGroup
