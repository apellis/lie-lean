/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterDenominator
import LieLean.Algebra.Lie.KacMoody.CompositionSeries.Casimir

/-!
# The support of `R · ch V` for highest-weight modules

Let `A` be a symmetrizable generalized Cartan matrix, `R = ∏_{α > 0} (1 - e^{-α})^{mult α}` the
denominator, and `V` a quotient of the Verma module `M(Λ)`. Writing `R · ch V = ∑_λ c_λ e^λ`
(`c_λ ∈ ℤ`), we show that `c_λ ≠ 0` only if `λ ≤ Λ` and `(λ + 2ρ | λ) = (Λ + 2ρ | Λ)`, i.e.
`|λ + ρ|² = |Λ + ρ|²`. Since `R · ch M(λ) = e^λ`, this says that `ch V` is a (possibly infinite)
integral combination of the `ch M(λ)` with such `λ` ([Kac] Prop. 9.8); it is the form
used in the proof of the Weyl–Kac character formula ([Kac] §10.4).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.coeffAt_denominator_mul_eq`: `(R f)_ξ` only depends on the
  coefficients `f_β`, `β ≥ ξ`.
* `Matrix.Realization.KacMoodyAlgebra.IsLocalCompositionSeries.coeffAt_denominator_mul_character`:
  `(R · ch V)_ξ = ∑_{j ∈ J} (R · ch L(λ_j))_ξ` for a local composition series for `ξ`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.coeffAt_denominator_mul_character_ne_zero`,
  `Matrix.Realization.KacMoodyAlgebra.coeffAt_denominator_mul_character_ne_zero`: if `V` is a
  quotient of `M(Λ)` and `(R · ch V)_ξ ≠ 0`, then `ξ ≤ Λ` and `(Λ + 2ρ | Λ) = (ξ + 2ρ | ξ)`.

## Proof

Since the support of `R` lies in `-Q₊`, `(R · ch V)_ξ` only depends on the `dim V_β`, `β ≥ ξ`;
by a local composition series for `ξ` it equals `∑_{j ∈ J} (R · ch L(λ_j))_ξ`, where
`ξ ≤ λ_j ≤ Λ` and `(λ_j + 2ρ | λ_j) = (Λ + 2ρ | Λ)` ([Kac] §9.8, proof of Prop. 9.8). So it suffices
to treat `V = L(μ)`, and we show `(R · ch L(μ))_ξ = 0` if `ξ ≤ μ` and `(ξ + 2ρ | ξ) ≠ (μ + 2ρ | μ)`
by induction on the height of `μ - ξ`: decomposing `M(μ)` in the same way,
`0 = (e^μ)_ξ = (R · ch M(μ))_ξ = (R · ch L(μ))_ξ + ∑ (R · ch L(λ_j))_ξ`, where `L(μ)` occurs exactly
once (as `dim M(μ)_μ = 1`) and the other `λ_j` satisfy `ξ ≤ λ_j < μ` and
`(λ_j + 2ρ | λ_j) = (μ + 2ρ | μ)`, so their terms vanish by induction. This is the argument of
[Kac] §9.8 in the language of `ℰ`, written out by us.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.6–9.8, §10.2–10.4.
-/

open Module LieModule HahnSeries

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

open CharacterRing WeightOrd

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

variable (P) in
/-- The support of the denominator `R` lies in `-Q₊`. -/
lemma exists_eq_neg_rootOf_of_coeffAt_denominator_ne_zero {ν : Dual K H}
    (h : (denominator P).coeffAt ν ≠ 0) : ∃ k : ι → ℤ, 0 ≤ k ∧ ν = -P.rootOf k := by
  by_contra hν
  refine h ?_
  rw [coeffAt, denominator, SummableFamily.coeff_hsum]
  refine finsum_eq_zero_of_forall_eq_zero fun S ↦ ?_
  simp only [denominatorFamily, SummableFamily.coe_mk]
  refine coeff_single_of_ne fun heq ↦ hν ?_
  obtain ⟨k, hk, hkS⟩ := exists_finsetWt_eq_rootOf P S
  exact ⟨k, hk, by rw [← hkS]; exact (toWeightOrd P).injective heq⟩

/-- `(R f)_ξ` only depends on the coefficients `f_β` for `β ≥ ξ`. -/
theorem coeffAt_denominator_mul_eq {f g : P.CharacterRing ℤ} {ξ : Dual K H}
    (h : ∀ β, ξ ∈ cone P β → f.coeffAt β = g.coeffAt β) :
    (denominator P * f).coeffAt ξ = (denominator P * g).coeffAt ξ := by
  rw [CharacterRing.coeff_mul, CharacterRing.coeff_mul]
  refine finsum_congr fun ν ↦ ?_
  by_cases hν : (denominator P).coeffAt ν = 0
  · rw [hν, zero_mul, zero_mul]
  · obtain ⟨k, hk, rfl⟩ := exists_eq_neg_rootOf_of_coeffAt_denominator_ne_zero P hν
    rw [h _ ⟨k, hk, by rw [sub_neg_eq_add, add_sub_cancel_right]⟩]

omit [DecidableEq ι] in
lemma coeffAt_list_sum_map {α : Type*} (t : List α) (F : α → P.CharacterRing ℤ) (ξ : Dual K H) :
    (t.map F).sum.coeffAt ξ = (t.map fun a ↦ (F a).coeffAt ξ).sum := by
  induction t with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    exact coeff_add

/-- Along a local composition series for `ξ` of a module `V` in `𝒪`,
`(R · ch V)_ξ = ∑_{j ∈ J} (R · ch L(λ_j))_ξ`. -/
theorem IsLocalCompositionSeries.coeffAt_denominator_mul_character (hV : IsCategoryO P V)
    {ξ : Dual K H} {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P ξ ⊥ l ⊤) :
    (denominator P * hV.character).coeffAt ξ = ((factorWeights l).map fun μ ↦
      (denominator P * (IrreducibleModule.isCategoryO P μ).character).coeffAt ξ).sum := by
  have hagree (β : Dual K H) (hβ : ξ ∈ cone P β) : hV.character.coeffAt β =
      ((factorWeights l).map fun μ ↦ (IrreducibleModule.isCategoryO P μ).character).sum.coeffAt
        β := by
    rw [coeffAt_list_sum_map, IsCategoryO.coeffAt_character, hl.finrank_weightSpace_eq hV hβ,
      Nat.cast_list_sum, List.map_map]
    rfl
  rw [coeffAt_denominator_mul_eq hagree, ← List.sum_map_mul_left, coeffAt_list_sum_map]

variable [FiniteDimensional K H] {S : A.Symmetrization}
  {B : LinearMap.BilinForm K P.KacMoodyAlgebra}

namespace IsStandardForm

variable (hB : IsStandardForm P S B) (hA : A.IsGeneralizedCartan)
include hB hA

/-- If `ξ ≤ μ` and `(ξ + 2ρ | ξ) ≠ (μ + 2ρ | μ)`, the coefficient of `e^ξ` in `R · ch L(μ)`
vanishes. -/
theorem coeffAt_denominator_mul_character_irreducibleModule_eq_zero {μ ξ : Dual K H}
    (hξ : ξ ∈ cone P μ)
    (hne : P.dualBilinForm S (μ + 2 • P.rho) μ ≠ P.dualBilinForm S (ξ + 2 • P.rho) ξ) :
    (denominator P * (IrreducibleModule.isCategoryO P μ).character).coeffAt ξ = 0 := by
  classical
  obtain ⟨k, hk, hξμ⟩ := hξ
  suffices H : ∀ n : ℕ, ∀ (μ ξ : Dual K H) (k : ι → ℤ), 0 ≤ k → ξ = μ - P.rootOf k →
      ∑ i, k i ≤ n →
      P.dualBilinForm S (μ + 2 • P.rho) μ ≠ P.dualBilinForm S (ξ + 2 • P.rho) ξ →
      (denominator P * (IrreducibleModule.isCategoryO P μ).character).coeffAt ξ = 0 from
    H _ μ ξ k hk hξμ (Int.self_le_toNat _) hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro μ ξ k hk hξμ hkn hne
  have hμξ : ξ ≠ μ := fun h ↦ hne (by rw [h])
  obtain ⟨l, hl⟩ := (VermaModule.isCategoryO P μ).exists_isLocalCompositionSeries ξ
  have hM := hl.coeffAt_denominator_mul_character (VermaModule.isCategoryO P μ)
  rw [VermaModule.denominator_mul_character, coeff_exp,
    ite_eq_right_iff.mpr fun h ↦ absurd h hμξ] at hM
  -- the factors `L(λ)` of `M(μ)` have `ξ ≤ λ ≤ μ` and `(λ + 2ρ | λ) = (μ + 2ρ | μ)`
  have hfac (κ : Dual K H) (hκ : κ ∈ factorWeights l) :
      κ ∈ cone P μ ∧ P.dualBilinForm S (μ + 2 • P.rho) μ =
        P.dualBilinForm S (κ + 2 • P.rho) κ := by
    have := hB.mem_cone_and_eq_of_mem_factorWeights hA LieModuleHom.id Function.surjective_id hl
      hκ
    rwa [dualBilinForm_add_rho_add_rho_eq_iff] at this
  -- all factors other than `L(μ)` contribute `0`
  have hzero (κ : Dual K H) (hκ : κ ∈ factorWeights l) (hne' : κ ≠ μ) :
      (denominator P * (IrreducibleModule.isCategoryO P κ).character).coeffAt ξ = 0 := by
    obtain ⟨⟨j, hj, hκμ⟩, hc⟩ := hfac κ hκ
    obtain ⟨k', hk', hξκ⟩ := hl.mem_cone_of_mem_factorWeights hκ
    have hkj : k = j + k' := P.rootOf_injective (by
      have e1 : P.rootOf k = μ - ξ := by rw [hξμ]; abel
      have e2 : P.rootOf j = μ - κ := by rw [hκμ]; abel
      have e3 : P.rootOf k' = κ - ξ := by rw [hξκ]; abel
      rw [map_add, e1, e2, e3]
      abel)
    have hj0 : j ∈ posCone ι := ⟨hj, fun h0 ↦ hne' (by rw [hκμ, h0, map_zero, sub_zero])⟩
    have h1 := one_le_sum_of_mem_posCone hj0
    have h2 : ∑ i, k i = ∑ i, j i + ∑ i, k' i := by
      rw [hkj, ← Finset.sum_add_distrib]
      rfl
    have h3 : 0 ≤ ∑ i, k' i := Finset.sum_nonneg fun i _ ↦ hk' i
    exact ih (∑ i, k' i).toNat (by omega) κ ξ k' hk' hξκ (Int.self_le_toNat _)
      (by rwa [← hc])
  -- `L(μ)` occurs exactly once
  have hcount : (factorWeights l).count μ = 1 := by
    have hdim := hl.finrank_weightSpace_eq (VermaModule.isCategoryO P μ) ⟨k, hk, hξμ⟩ (ξ := μ)
    rw [show weightSpace P (VermaModule P μ) μ = K ∙ VermaModule.hwv P μ from
      VermaModule.weightSpace_self P μ, finrank_span_singleton (VermaModule.hwv_ne_zero P μ),
      List.sum_map_eq_nsmul_single μ _ fun κ hne' hκ ↦ ?_,
      IrreducibleModule.finrank_weightSpace_self, smul_eq_mul, mul_one] at hdim
    · exact hdim.symm
    · by_contra h0
      have h1 := IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero h0
      obtain ⟨⟨j, hj, hκμ⟩, -⟩ := hfac κ hκ
      obtain ⟨j', hj', hμκ⟩ := h1
      have hjj : j + j' = 0 := P.rootOf_injective (by
        have e2 : P.rootOf j = μ - κ := by rw [hκμ]; abel
        have e3 : P.rootOf j' = κ - μ := by rw [hμκ]; abel
        rw [map_add, map_zero, e2, e3]
        abel)
      have hj0 : j = 0 := le_antisymm (fun i ↦ by
        have := congrFun hjj i
        have := hj' i
        simp only [Pi.add_apply, Pi.zero_apply] at *
        omega) hj
      exact hne' (by rw [hκμ, hj0, map_zero, sub_zero])
  rw [List.sum_map_eq_nsmul_single μ _ fun κ hne' hκ ↦ hzero κ hκ hne', hcount,
    one_smul] at hM
  exact hM.symm

/-- **[Kac] Prop. 9.8**, character form: if `V` is a quotient of `M(Λ)` and the
coefficient of `e^ξ` in `R · ch V` is nonzero, where `R = ∏_{α > 0} (1 - e^{-α})^{mult α}`, then
`ξ ≤ Λ` and `(Λ + 2ρ | Λ) = (ξ + 2ρ | ξ)`. Equivalently (as `R · ch M(λ) = e^λ`),
`ch V = ∑_λ c_λ ch M(λ)` with `c_λ ∈ ℤ` vanishing unless `λ ≤ Λ` and
`|λ + ρ|² = |Λ + ρ|²`. -/
theorem coeffAt_denominator_mul_character_ne_zero {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ)
    (hV : IsCategoryO P V) {ξ : Dual K H} (hξ : (denominator P * hV.character).coeffAt ξ ≠ 0) :
    ξ ∈ cone P Λ ∧
      P.dualBilinForm S (Λ + 2 • P.rho) Λ = P.dualBilinForm S (ξ + 2 • P.rho) ξ := by
  classical
  obtain ⟨l, hl⟩ := hV.exists_isLocalCompositionSeries ξ
  rw [hl.coeffAt_denominator_mul_character hV] at hξ
  obtain ⟨κ, hκ, hne⟩ : ∃ κ ∈ factorWeights l,
      (denominator P * (IrreducibleModule.isCategoryO P κ).character).coeffAt ξ ≠ 0 := by
    by_contra! h
    exact hξ (List.sum_eq_zero fun x hx ↦ by
      obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hx
      exact h κ hκ)
  have hfac := hB.mem_cone_and_eq_of_mem_factorWeights hA φ hφ hl hκ
  rw [dualBilinForm_add_rho_add_rho_eq_iff] at hfac
  have hξκ := hl.mem_cone_of_mem_factorWeights hκ
  refine ⟨mem_cone_trans hξκ hfac.1, hfac.2.trans ?_⟩
  by_contra hc
  exact hne (hB.coeffAt_denominator_mul_character_irreducibleModule_eq_zero hA hξκ hc)

end IsStandardForm

/-- **[Kac] Prop. 9.8**, character form, for a symmetrizable generalized Cartan matrix
`A` with symmetrization `S`: if `V` is a quotient of `M(Λ)` and the coefficient of `e^ξ` in
`R · ch V` is nonzero, then `ξ ≤ Λ` and `(Λ + 2ρ | Λ) = (ξ + 2ρ | ξ)`. -/
theorem coeffAt_denominator_mul_character_ne_zero (S : A.Symmetrization)
    (hA : A.IsGeneralizedCartan) {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ)
    (hV : IsCategoryO P V) {ξ : Dual K H} (hξ : (denominator P * hV.character).coeffAt ξ ≠ 0) :
    ξ ∈ cone P Λ ∧
      P.dualBilinForm S (Λ + 2 • P.rho) Λ = P.dualBilinForm S (ξ + 2 • P.rho) ξ :=
  (isStandardForm_invForm P S).coeffAt_denominator_mul_character_ne_zero hA φ hφ hV hξ

end Matrix.Realization.KacMoodyAlgebra
