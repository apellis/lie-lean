/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationProjective

/-!
# Translation of the dominant Verma module: `T_μ^λ M(w_λ·μ) ≅ P(w_λ w_μ°·λ)`

Humphreys, GSM 94, Proposition 7.13: for `λ`, `μ` antidominant and compatible, with `μ♮` in the
closure of the chamber of `λ♮`, `T_μ^λ M(w_λ·μ) ≅ P(w_λ w_μ°·λ)`, where `w_λ` is the longest
element of `W_[λ]` and `w_μ°` the longest element of the stabilizer `W_μ°` of `μ` (dot action).

We use the defining properties of these longest elements instead of the length functions of the
reflection groups `W_[λ]` and `W_μ°`:

* `Matrix.Realization.IsLongestIntegral`: `w ∈ W_[λ]` maps every positive root integral for `λ`
  to a negative root;
* `Matrix.Realization.IsLongestStabilizer`: `u` fixes `b = μ + ρ` and maps every positive root
  orthogonal to `b` to a negative root.

## Main results

* `Matrix.Realization.isDominant_weylDot_of_isLongestIntegral`: `w_λ·μ` is dominant.
* `Matrix.Realization.upperClosureCondition_mul_of_isLongest`: `w_λ w_μ°·μ = w_λ·μ` lies in the
  upper closure of the facet of `w_λ w_μ°·λ`.
* `Matrix.Realization.exists_isLongestIntegral`, `Matrix.Realization.exists_isLongestStabilizer`:
  such elements exist when `λ` is regular (`λ♮` in a chamber), as in Humphreys.
* `Matrix.Realization.KacMoodyAlgebra.nonempty_equiv_projectiveCover_translation_verma_longest`:
  **Proposition 7.13**. The second assertion of 7.13 (the Verma modules in a standard filtration
  of this projective are the `M(w_λ w·λ)`, `w ∈ W_μ°`, each once) is Theorem 7.12 for `w = w_λ`,
  `exists_translation_verma_filtration_of_isAntidominant`.

## Proof

By `nonempty_equiv_projectiveCover_translation_verma`, `T_μ^λ M(w_λ·μ) ≅ P(x·λ)` for an `x` with
`x·μ = w_λ·μ` and `x·μ` in the upper closure of the facet of `x·λ`; such an `x·λ` is unique
(`exists_apply_sub_eq_rootOf_of_upperClosureCondition_of_integral`). For `x = w_λ w_μ°` the
upper-closure condition is checked root by root: if `β > 0` is orthogonal to `x(μ + ρ)`, then
`γ = x⁻¹ β` is a positive root (`w_λ⁻¹ β < 0` since it is integral, then `γ > 0` by the property
of `w_μ°`), so `⟨x(λ + ρ), β^∨⟩ = ⟨λ + ρ, γ^∨⟩ ≤ 0`. Humphreys deduces the proposition from
Theorem 7.12 with the Bruhat order on `W_μ°`, BGG reciprocity and Verma's theorem; the argument
here is our own.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.13.
-/

noncomputable section

open Module

namespace Matrix.Realization

section Combinatorics

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsGeneralizedCartan)

/-- `w ∈ W_[λ]` maps every positive root integral for `λ` to a negative root. This is the defining
property of the longest element `w_λ` of the reflection group `W_[λ]` (Humphreys, GSM 94, §7.13). -/
def IsLongestIntegral (lam : Dual K H) (w : P.weylGroup hA) : Prop :=
  w ∈ P.integralWeylGroup hA lam ∧ ∀ v i, P.IsPosRoot hA v i → P.IsIntegralRoot hA lam v i →
    ¬P.IsPosRoot hA (w * v) i

/-- `u` fixes `b` and maps every positive root orthogonal to `b` to a negative root. For
`b = μ + ρ` this is the defining property of the longest element `w_μ°` of the stabilizer `W_μ°`
of `μ` for the dot action (Humphreys, GSM 94, §7.13). -/
def IsLongestStabilizer (b : Dual K H) (u : P.weylGroup hA) : Prop :=
  (u : Dual K H ≃ₗ[K] Dual K H) b = b ∧ ∀ v i, P.IsPosRoot hA v i →
    P.corootPairing hA b v i = 0 → ¬P.IsPosRoot hA (u * v) i

variable {P hA}

omit [DecidableEq ι] [CharZero K] in
/-- If `λ - μ` is integral, so is `λ - (μ + ρ)`. -/
lemma integral_sub_add_rho {lam μ : Dual K H}
    (hint : ∀ j, ∃ n : ℤ, ((lam + P.rho) - (μ + P.rho)) (P.coroot j) = n) (j : ι) :
    ∃ z : ℤ, (lam - (μ + P.rho)) (P.coroot j) = z := by
  obtain ⟨m, hm⟩ := hint j
  refine ⟨m - 1, ?_⟩
  simp only [LinearMap.sub_apply, LinearMap.add_apply, rho_coroot] at hm ⊢
  push_cast
  linear_combination hm

omit [DecidableEq ι] [CharZero K] in
lemma corootPairing_mul_eq_of_apply_eq {u : P.weylGroup hA} {b : Dual K H}
    (hu : (u : Dual K H ≃ₗ[K] Dual K H) b = b) (v : P.weylGroup hA) (i : ι) :
    P.corootPairing hA b (u * v) i = P.corootPairing hA b v i := by
  have h := corootPairing_apply u (u * v) b i
  rwa [hu, ← mul_assoc, inv_mul_cancel, one_mul] at h

omit [DecidableEq ι] [CharZero K] in
/-- `W_[λ] = W_[-λ]`. -/
lemma integralWeylGroup_neg (lam : Dual K H) :
    P.integralWeylGroup hA (-lam) = P.integralWeylGroup hA lam := by
  ext w
  rw [mem_integralWeylGroup, mem_integralWeylGroup, map_neg,
    show -(w : Dual K H ≃ₗ[K] Dual K H) lam - -lam =
      -((w : Dual K H ≃ₗ[K] Dual K H) lam - lam) by abel, neg_mem_iff]

end Combinatorics

section Finite

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  (hF : A.IsFiniteCartan)

/-- If `μ` is antidominant, `λ - μ` is integral and `w_λ` maps the positive roots integral for
`λ` to negative roots, then `w_λ·μ` is dominant (Humphreys, GSM 94, §7.13). -/
theorem isDominant_weylDot_of_isLongestIntegral {lam μ : Dual K H}
    (hμ : P.IsAntidominant hF.isGeneralizedCartan μ)
    (hint : ∀ j, ∃ n : ℤ, ((lam + P.rho) - (μ + P.rho)) (P.coroot j) = n)
    {wl : P.weylGroup hF.isGeneralizedCartan}
    (hwl : P.IsLongestIntegral hF.isGeneralizedCartan lam wl) :
    P.IsDominant hF.isGeneralizedCartan (P.weylDot hF.isGeneralizedCartan wl μ) := by
  intro v i hv n hn
  rw [weylDot_add_rho, corootPairing_apply] at hn
  have hint' : P.IsIntegralRoot hF.isGeneralizedCartan lam (wl⁻¹ * v) i := by
    rw [P.isIntegralRoot_congr hF.isGeneralizedCartan (μ' := μ + P.rho)
      (integral_sub_add_rho hint)]
    exact ⟨n, hn⟩
  rcases P.isPosRoot_or (wl⁻¹ * v) i with hpos | hneg
  · exact absurd (by rwa [← mul_assoc, mul_inv_cancel, one_mul]) (hwl.2 _ i hpos hint')
  · have := hμ _ i hneg (-n) (by rw [corootPairing_mul_simple, hn]; push_cast; ring)
    omega

/-- **The upper-closure condition for `w_λ w_μ°`.** If `λ` is antidominant, `λ - μ` is integral,
`w_λ` maps the positive roots integral for `λ` to negative roots and `u` fixes `μ + ρ` and maps the
positive roots orthogonal to `μ + ρ` to negative roots, then every positive root `β` orthogonal
to `w_λ u (μ + ρ)` has `⟨w_λ u (λ + ρ), β^∨⟩ ∈ ℤ_{≤ 0}`. -/
theorem upperClosureCondition_mul_of_isLongest {lam μ : Dual K H}
    (hlam : P.IsAntidominant hF.isGeneralizedCartan lam)
    (hint : ∀ j, ∃ n : ℤ, ((lam + P.rho) - (μ + P.rho)) (P.coroot j) = n)
    {wl u : P.weylGroup hF.isGeneralizedCartan}
    (hwl : P.IsLongestIntegral hF.isGeneralizedCartan lam wl)
    (hu : P.IsLongestStabilizer hF.isGeneralizedCartan (μ + P.rho) u) :
    P.UpperClosureCondition hF.isGeneralizedCartan ((wl * u).val (lam + P.rho))
      ((wl * u).val (μ + P.rho)) := by
  have hA := hF.isGeneralizedCartan
  intro v' hv' i hpos h0
  set v : P.weylGroup hF.isGeneralizedCartan := ⟨v', hv'⟩
  have hvpos : P.IsPosRoot hF.isGeneralizedCartan v i := isPosRoot_iff_mem_posWeights.mpr hpos
  rw [symm_apply_coroot_eq_corootPairing (v := v)] at h0 ⊢
  rw [show ((wl * u).val (μ + P.rho)) = ((wl * u : P.weylGroup hF.isGeneralizedCartan) :
    Dual K H ≃ₗ[K] Dual K H) (μ + P.rho) from rfl, corootPairing_apply] at h0
  rw [show ((wl * u).val (lam + P.rho)) = ((wl * u : P.weylGroup hF.isGeneralizedCartan) :
    Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) from rfl, corootPairing_apply]
  set γ := (wl * u)⁻¹ * v with hγ
  -- integrality of roots orthogonal to `μ + ρ`
  have hcongr : ∀ x : P.weylGroup hF.isGeneralizedCartan,
      P.IsIntegralRoot hF.isGeneralizedCartan (μ + P.rho) x i →
        P.IsIntegralRoot hF.isGeneralizedCartan lam x i := fun x hx ↦ by
    rwa [P.isIntegralRoot_congr hF.isGeneralizedCartan (μ' := μ + P.rho)
      (integral_sub_add_rho hint)]
  -- `δ = w_λ⁻¹ β = u γ` is negative
  have hδ : u * γ = wl⁻¹ * v := by rw [hγ]; group
  have hδ0 : P.corootPairing hF.isGeneralizedCartan (μ + P.rho) (u * γ) i = 0 := by
    rw [corootPairing_mul_eq_of_apply_eq hu.1]; exact h0
  have hδneg : ¬P.IsPosRoot hF.isGeneralizedCartan (u * γ) i := by
    intro hδpos
    refine hwl.2 _ i hδpos (hcongr _ ⟨0, by rw [Int.cast_zero]; exact hδ0⟩) ?_
    rwa [hδ, ← mul_assoc, mul_inv_cancel, one_mul]
  -- `γ` is positive
  have hγpos : P.IsPosRoot hF.isGeneralizedCartan γ i := by
    rcases P.isPosRoot_or γ i with h | h
    · exact h
    · exfalso
      have hγ0 : P.corootPairing hF.isGeneralizedCartan (μ + P.rho)
          (γ * (P.coxeterSystem hF.isGeneralizedCartan).simple i) i = 0 := by
        rw [corootPairing_mul_simple, ← corootPairing_mul_eq_of_apply_eq hu.1, hδ0, neg_zero]
      have := hu.2 _ i h hγ0
      rw [← mul_assoc] at this
      rcases P.isPosRoot_or (u * γ) i with h' | h'
      · exact hδneg h'
      · exact this h'
  -- `⟨λ + ρ, γ^∨⟩ ∈ ℤ_{≤ 0}`
  have hγint := hcongr γ ⟨0, by
    rw [Int.cast_zero]; exact (corootPairing_mul_eq_of_apply_eq hu.1 γ i).symm.trans hδ0⟩
  obtain ⟨n, hn⟩ := (P.isIntegralRoot_congr hF.isGeneralizedCartan (μ' := lam + P.rho)
    (fun j ↦ ⟨-1, by simp⟩) γ i).mp hγint
  have hle := hlam γ i hγpos n hn
  have hn' : P.corootPairing hF.isGeneralizedCartan (lam + P.rho) γ i = n := hn
  have hnat : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
  refine ⟨(-n).toNat, ?_⟩
  rw [hn', show (((-n).toNat : ℕ) : K) = ((((-n).toNat : ℕ) : ℤ) : K) by norm_cast, hnat]
  push_cast
  ring

/-- For regular antidominant `λ` (`λ♮` in a chamber), there is `w_λ ∈ W_[λ]` mapping every
positive root integral for `λ` to a negative root: take `w⁻¹` for `w ∈ W_[λ]` with `w·(-λ - 2ρ)`
antidominant. -/
theorem exists_isLongestIntegral {lam : Dual K H}
    (hlam : P.IsAntidominant hF.isGeneralizedCartan lam)
    (hreg : ∀ v i, P.IsPosRoot hF.isGeneralizedCartan v i →
      P.corootPairing hF.isGeneralizedCartan (lam + P.rho) v i ≠ 0) :
    ∃ wl, P.IsLongestIntegral hF.isGeneralizedCartan lam wl := by
  obtain ⟨w, hw, hanti⟩ := P.exists_isAntidominant_weylDot hF (-(lam + P.rho) - P.rho)
  have hW : P.integralWeylGroup hF.isGeneralizedCartan (-(lam + P.rho) - P.rho) =
      P.integralWeylGroup hF.isGeneralizedCartan lam := by
    rw [P.integralWeylGroup_eq_of_integral hF.isGeneralizedCartan
      (μ' := -(lam + P.rho)) fun j ↦ ⟨-1, by simp⟩, integralWeylGroup_neg,
      ← P.integralWeylGroup_eq_of_integral hF.isGeneralizedCartan (μ := lam) fun j ↦ ⟨-1, by simp⟩]
  refine ⟨w⁻¹, inv_mem (hW ▸ hw), fun v i hv hint hpos ↦ ?_⟩
  obtain ⟨n, hn⟩ := (P.isIntegralRoot_congr hF.isGeneralizedCartan (μ' := lam + P.rho)
    (fun j ↦ ⟨-1, by simp⟩) _ i).mp
    (P.isIntegralRoot_mul hF.isGeneralizedCartan
      (inv_mem (hW ▸ hw : w ∈ P.integralWeylGroup _ lam)) hint)
  replace hn : P.corootPairing hF.isGeneralizedCartan (lam + P.rho) (w⁻¹ * v) i = n := hn
  have hle := hlam _ i hpos n hn
  have hne : n ≠ 0 := fun h ↦ hreg _ i hpos (by rw [hn, h, Int.cast_zero])
  have h2 := hanti v i hv (-n) (by
    rw [sub_add_cancel, sub_add_cancel, corootPairing_apply, corootPairing_neg, hn]; push_cast
    ring)
  omega

/-- For regular antidominant `λ` and antidominant `μ` with `λ - μ` integral, and `w_λ` as above,
there is `u` fixing `μ + ρ` and mapping every positive root orthogonal to `μ + ρ` to a negative
root (the longest element `w_μ°` of the stabilizer of `μ`). -/
theorem exists_isLongestStabilizer [FiniteDimensional K H] {lam μ : Dual K H}
    (hlam : P.IsAntidominant hF.isGeneralizedCartan lam)
    (hreg : ∀ v i, P.IsPosRoot hF.isGeneralizedCartan v i →
      P.corootPairing hF.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    (hint : ∀ j, ∃ n : ℤ, ((lam + P.rho) - (μ + P.rho)) (P.coroot j) = n)
    {wl : P.weylGroup hF.isGeneralizedCartan}
    (hwl : P.IsLongestIntegral hF.isGeneralizedCartan lam wl) :
    ∃ u, P.IsLongestStabilizer hF.isGeneralizedCartan (μ + P.rho) u := by
  have hwa : wl ∈ P.integralWeylGroup hF.isGeneralizedCartan (lam + P.rho) := by
    rw [← P.integralWeylGroup_eq_of_integral hF.isGeneralizedCartan (μ := lam)
      fun j ↦ ⟨-1, by simp⟩]
    exact hwl.1
  obtain ⟨x, -, hxb, hxC, -⟩ := exists_upperClosureCondition_of_integral (P := P) hF hint hlam hwa
  refine ⟨wl⁻¹ * x, ?_, fun v i hv h0 hpos ↦ ?_⟩
  · change ((wl⁻¹ : P.weylGroup hF.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H)
      (x.val (μ + P.rho)) = μ + P.rho
    rw [hxb]
    exact inv_apply_apply wl (μ + P.rho)
  · -- `δ = u γ` is a positive root orthogonal to `μ + ρ`, hence integral
    set δ := wl⁻¹ * x * v
    have hδ0 : P.corootPairing hF.isGeneralizedCartan (μ + P.rho) δ i = 0 := by
      rw [corootPairing_mul_eq_of_apply_eq (u := wl⁻¹ * x) (by
        change ((wl⁻¹ : P.weylGroup hF.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H)
          (x.val (μ + P.rho)) = μ + P.rho
        rw [hxb]; exact inv_apply_apply wl (μ + P.rho))]
      exact h0
    have hδint : P.IsIntegralRoot hF.isGeneralizedCartan lam δ i := by
      rw [P.isIntegralRoot_congr hF.isGeneralizedCartan (μ' := μ + P.rho)
      (integral_sub_add_rho hint)]
      exact ⟨0, by rw [Int.cast_zero]; exact hδ0⟩
    -- `w_λ δ = x γ` is negative, so `β = -x γ` is positive and orthogonal to `x (μ + ρ)`
    have hxneg := hwl.2 δ i hpos hδint
    have hxv : wl * δ = x * v := by simp only [δ]; group
    rw [hxv] at hxneg
    have hβ := (P.isPosRoot_or (x * v) i).resolve_left hxneg
    have hβ' : (((x * v * (P.coxeterSystem hF.isGeneralizedCartan).simple i :
        P.weylGroup hF.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H) (P.root i)) ∈
        P.posWeights := isPosRoot_iff_mem_posWeights.mp hβ
    obtain ⟨n, hn⟩ := hxC _ (x * v * (P.coxeterSystem hF.isGeneralizedCartan).simple i).2 i hβ' (by
      rw [symm_apply_coroot_eq_corootPairing (v := x * v * _), ← hxb,
        show x.val (μ + P.rho) = (x : Dual K H ≃ₗ[K] Dual K H) (μ + P.rho) from rfl,
        corootPairing_apply, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul,
        corootPairing_mul_simple, h0, neg_zero])
    rw [symm_apply_coroot_eq_corootPairing (v := x * v * _),
      show x.val (lam + P.rho) = (x : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) from rfl,
      corootPairing_apply, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul,
      corootPairing_mul_simple, neg_eq_iff_eq_neg, neg_neg] at hn
    -- `⟨λ + ρ, γ^∨⟩ = n ≥ 0`, so it is `0`, against regularity
    have hle := hlam v i hv n (by rw [hn]; norm_cast)
    have hn0 : n = 0 := by omega
    exact hreg v i hv (by rw [hn, hn0, Nat.cast_zero])

/-- **Identification of `x`.** If `w_λ`, `w_μ°` are as above and `x·μ = w_λ·μ` lies in the upper
closure of the facet of `x·λ`, then `x·λ = w_λ w_μ°·λ`. -/
theorem weylDot_eq_of_memUpperClosure_of_isLongest [FiniteDimensional K H] {lam μ : Dual K H}
    (hlam : P.IsAntidominant hF.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hF.isGeneralizedCartan μ)
    (hint : ∀ j, ∃ n : ℤ, ((lam + P.rho) - (μ + P.rho)) (P.coroot j) = n)
    (hfacet : ∀ v i, P.IsPosRoot hF.isGeneralizedCartan v i →
      P.corootPairing hF.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hF.isGeneralizedCartan (μ + P.rho) v i = 0)
    {wl u x : P.weylGroup hF.isGeneralizedCartan}
    (hwl : P.IsLongestIntegral hF.isGeneralizedCartan lam wl)
    (hu : P.IsLongestStabilizer hF.isGeneralizedCartan (μ + P.rho) u)
    (hxμ : P.weylDot hF.isGeneralizedCartan x μ = P.weylDot hF.isGeneralizedCartan wl μ)
    (hxup : P.MemUpperClosure hF.isGeneralizedCartan (P.weylDot hF.isGeneralizedCartan x lam)
      (P.weylDot hF.isGeneralizedCartan x μ)) :
    P.weylDot hF.isGeneralizedCartan x lam = P.weylDot hF.isGeneralizedCartan (wl * u) lam := by
  have hA' := hF.isGeneralizedCartan
  have hxC := (memUpperClosure_weylDot_iff_of_isAntidominant hF hlam hμ hint hfacet x).mp hxup
  have hC := upperClosureCondition_mul_of_isLongest hF hlam hint hwl hu
  have hb : (wl * u).val (μ + P.rho) = x.val (μ + P.rho) := by
    have h1 := congrArg (· + P.rho) hxμ
    simp only [weylDot, sub_add_cancel] at h1
    rw [h1]
    change (wl : Dual K H ≃ₗ[K] Dual K H) ((u : Dual K H ≃ₗ[K] Dual K H) (μ + P.rho)) = _
    rw [hu.1]
  have ha : ∀ v i, P.IsPosRoot hA' v i → ∀ n : ℤ, P.corootPairing hA' (lam + P.rho) v i = n →
      n ≤ 0 := hlam
  obtain ⟨c₁, hc₁, h₁⟩ := exists_apply_sub_eq_rootOf_of_upperClosureCondition_of_integral
    (P := P) hF hint ha hC hb.symm
  obtain ⟨c₂, hc₂, h₂⟩ := exists_apply_sub_eq_rootOf_of_upperClosureCondition_of_integral
    (P := P) hF hint ha hxC hb
  have h0 : P.rootOf (c₁ + c₂) = P.rootOf 0 := by
    rw [map_add, ← h₁, ← h₂, map_zero]; abel
  have hc0 : c₁ = 0 := by
    have := P.rootOf_injective h0
    ext j
    have h1 := congrFun this j
    have h2 : (0 : ℤ) ≤ c₁ j := hc₁ j
    have h3 : (0 : ℤ) ≤ c₂ j := hc₂ j
    simp only [Pi.add_apply, Pi.zero_apply] at h1 ⊢
    omega
  rw [hc0, map_zero, sub_eq_zero] at h₁
  simp only [weylDot, h₁]

end Finite

end Matrix.Realization

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

universe u₁ u₂

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- **Humphreys, GSM 94, Proposition 7.13.** Let `λ`, `μ` be antidominant, with every positive
root orthogonal to `λ + ρ` orthogonal to `μ + ρ`, let `ν = z (λ - μ)` (`z ∈ W`) be dominant
integral and `T_μ^λ = pr_{χ_λ}(pr_{χ_μ}(−) ⊗ L(ν))`. Let `w_λ ∈ W_[λ]` map the positive roots
integral for `λ` to negative roots, and let `w_μ°` fix `μ + ρ` and map the positive roots orthogonal
to `μ + ρ` to negative roots (the longest elements of `W_[λ]` and `W_μ°`, see
`exists_isLongestIntegral`, `exists_isLongestStabilizer`). Then `T_μ^λ M(w_λ·μ) ≅ P(w_λ w_μ°·λ)`.

Humphreys assumes `μ♮` in the closure of the chamber of `λ♮` (so `λ` is regular), which implies
the facet hypothesis here, and states the result over `ℂ` for `𝔤` semisimple. -/
theorem nonempty_equiv_projectiveCover_translation_verma_longest {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    {wl u : P.weylGroup hA.isGeneralizedCartan}
    (hwl : P.IsLongestIntegral hA.isGeneralizedCartan lam wl)
    (hu : P.IsLongestStabilizer hA.isGeneralizedCartan (μ + P.rho) u) :
    Nonempty (ProjectiveCover P hA (P.weylDot hA.isGeneralizedCartan (wl * u) lam) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
        (centralCharacter P lam) (VermaModule P (P.weylDot hA.isGeneralizedCartan wl μ))) := by
  -- the integrality of `λ - μ`
  have hint : ∀ j, ∃ n : ℤ, ((lam + P.rho) - (μ + P.rho)) (P.coroot j) = n := fun j ↦ by
    obtain ⟨n, hn⟩ := sub_rho_integral (lam := μ) (μ := lam) P hA hν hz hzν j
    refine ⟨-n, ?_⟩
    rw [show (lam + P.rho) - (μ + P.rho) = -((μ + P.rho) - (lam + P.rho)) by abel,
      LinearMap.neg_apply, hn, Int.cast_neg]
  -- `w_λ·μ` is dominant, hence maximal in its dot orbit
  have hdom := isDominant_weylDot_of_isLongestIntegral hA hμ hint hwl
  have h := nonempty_equiv_projectiveCover_translation_verma P hA hlam hμ
    hfacet hν hz hzν hwl.1 fun w' hw' k hk hwk ↦ hdom.eq_zero_of_apply_eq P hA hw' hk hwk
  rw [← weylDot_eq_of_memUpperClosure_of_isLongest hA hlam hμ hint hfacet hwl hu
    h.choose_spec.1 h.choose_spec.2.1]
  exact h.choose_spec.2.2

end Matrix.Realization.KacMoodyAlgebra
