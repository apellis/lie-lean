/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.Verma
import LieLean.Algebra.Lie.KacMoody.CharacterFormula

/-!
# The Euler characteristic of the BGG resolution

Let `A` be a symmetrizable generalized Cartan matrix, `𝔤 = 𝔤(A)` over a field `K` of
characteristic zero, and `Λ` a dominant integral weight. The BGG resolution of `L(Λ)` has terms
`C_k = ⊕_{ℓ(w) = k} M(w · Λ)`, so its Euler characteristic is
`∑_{w ∈ W} (-1)^{ℓ(w)} ch M(w · Λ)`. We show that this (in general infinite) sum is summable in
the algebra `ℰ` of formal characters and equals `ch L(Λ)` ([HumO] §6.3 (check); [Kac] §10.4 (check);
[Kum] §9.1 (check)). This is a reformulation of the Weyl–Kac character formula
(`Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.exp_rho_mul_denominator_mul_character`)
using `ch M(λ) = e^λ ∏_{α > 0} (1 - e^{-α})^{-mult α}`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.dotExpFamily`: the summable family
  `w ↦ (-1)^{ℓ(w)} e^{w · Λ}` indexed by `W`.
* `Matrix.Realization.KacMoodyAlgebra.vermaAltFamily`: the summable family
  `w ↦ (-1)^{ℓ(w)} ch M(w · Λ)` indexed by `W`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.vermaAltFamily_apply`: its terms are
  `(-1)^{ℓ(w)} ch M(w · Λ)`.
* `Matrix.Realization.KacMoodyAlgebra.hsum_vermaAltFamily`:
  `∑_{w ∈ W} (-1)^{ℓ(w)} ch M(w · Λ) = ch L(Λ)`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §6.3 (check).
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §10.4 (check).
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §9.1 (check).
-/

open Module LieModule HahnSeries

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

open CharacterRing WeightOrd

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)
  {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
include hΛ

omit [DecidableEq ι] in
/-- `Λ - w · Λ ∈ Q₊` for `Λ` dominant integral ([Kac] Prop. 3.12 (check)). -/
lemma exists_sub_weylDot_eq_rootOf (w : P.weylGroup hA) :
    ∃ k : ι → ℤ, 0 ≤ k ∧ Λ - P.weylDot hA w Λ = P.rootOf k := by
  obtain ⟨k, hk, hwk⟩ := P.exists_sub_apply_eq_rootOf hA (fun i ↦ by
    obtain ⟨n, hn⟩ := P.add_rho_regular hΛ i
    exact ⟨n + 1, by rw [hn]; push_cast; rfl⟩) w
  refine ⟨k, hk, ?_⟩
  rw [← hwk, weylDot]
  abel

omit [DecidableEq ι] in
/-- The dot action is injective on `W` for `Λ` dominant integral. -/
lemma weylDot_injective : Function.Injective fun w : P.weylGroup hA ↦ P.weylDot hA w Λ := by
  intro w w' h
  refine P.apply_injective_of_regular hA (P.add_rho_regular hΛ) ?_
  simpa [weylDot] using h

/-- The family `w ↦ (-1)^{ℓ(w)} e^{w · Λ}` in `ℰ`, indexed by the Weyl group. -/
def dotExpFamily : SummableFamily P.WeightOrd ℤ (P.weylGroup hA) where
  toFun w := HahnSeries.single (toWeightOrd P (P.weylDot hA w Λ))
    ((-1) ^ (P.coxeterSystem hA).length w)
  isPWO_iUnion_support' := by
    refine (isPWO_Ici P (toWeightOrd P Λ)).mono (Set.iUnion_subset fun w μ hμ ↦ ?_)
    obtain rfl := support_single_subset hμ
    obtain ⟨k, hk, hwk⟩ := exists_sub_weylDot_eq_rootOf P hA hΛ w
    exact ⟨k, hk, hwk⟩
  finite_co_support' g := by
    refine Set.Subsingleton.finite fun w hw w' hw' ↦ weylDot_injective P hA hΛ ?_
    have h₁ : toWeightOrd P (P.weylDot hA w Λ) = g := by
      by_contra h; exact hw (coeff_single_of_ne (Ne.symm h))
    have h₂ : toWeightOrd P (P.weylDot hA w' Λ) = g := by
      by_contra h; exact hw' (coeff_single_of_ne (Ne.symm h))
    exact (toWeightOrd P).injective (h₁.trans h₂.symm)

lemma dotExpFamily_apply (w : P.weylGroup hA) :
    dotExpFamily P hA hΛ w = (-1) ^ (P.coxeterSystem hA).length w • exp P ℤ (P.weylDot hA w Λ) := by
  ext g
  simp only [dotExpFamily, SummableFamily.coe_mk, exp, HahnSeries.coeff_smul, coeff_single,
    smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- The family `w ↦ (-1)^{ℓ(w)} ch M(w · Λ)` in `ℰ`, indexed by the Weyl group: the Euler
characteristic of the BGG resolution. It is summable since its terms are
`∏_{α > 0} (1 - e^{-α})^{-mult α} (-1)^{ℓ(w)} e^{w · Λ}` (`vermaAltFamily_apply`). -/
def vermaAltFamily : SummableFamily P.WeightOrd ℤ (P.weylGroup hA) :=
  kostantSeries P • dotExpFamily P hA hΛ

/-- The terms of `vermaAltFamily` are `(-1)^{ℓ(w)} ch M(w · Λ)`. -/
theorem vermaAltFamily_apply (w : P.weylGroup hA) :
    vermaAltFamily P hA hΛ w = (-1) ^ (P.coxeterSystem hA).length w •
      (VermaModule.isCategoryO P (P.weylDot hA w Λ)).character := by
  rw [vermaAltFamily, SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul,
    dotExpFamily_apply, VermaModule.character_eq_exp_mul_kostantSeries, mul_smul_comm, mul_comm]

/-- The sum of `dotExpFamily` is `e^{-ρ} ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ)}`. -/
lemma hsum_dotExpFamily :
    (dotExpFamily P hA hΛ).hsum =
      exp P ℤ (-P.rho) * weylAltSum P hA (IrreducibleModule.isDominantIntegral_add_rho hΛ) := by
  ext g
  change (dotExpFamily P hA hΛ).hsum.coeff (toWeightOrd P g) = _
  rw [SummableFamily.coeff_hsum, coeff_exp_mul, coeffAt_weylAltSum, sub_neg_eq_add]
  refine finsum_congr fun w ↦ ?_
  simp only [dotExpFamily, SummableFamily.coe_mk, coeff_single]
  have : (toWeightOrd P g = toWeightOrd P (P.weylDot hA w Λ)) ↔
      ((w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) = g + P.rho) := by
    rw [← weylDot_add_rho, add_left_inj, (toWeightOrd P).injective.eq_iff, eq_comm]
  by_cases h : toWeightOrd P g = toWeightOrd P (P.weylDot hA w Λ)
  · rw [ite_eq_left h, ite_eq_left (this.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (this.mpr h'))]

variable [FiniteDimensional K H] (hS : A.IsSymmetrizable)

include hS in
/-- **The Euler characteristic of the BGG resolution** ([HumO] §6.3 (check); [Kum] §9.1 (check)):
for a symmetrizable generalized Cartan matrix and `Λ` dominant integral,
`∑_{w ∈ W} (-1)^{ℓ(w)} ch M(w · Λ) = ch L(Λ)` in the algebra `ℰ` of formal characters, where
`w · Λ = w(Λ + ρ) - ρ`. This is equivalent to the Weyl–Kac character formula. -/
theorem hsum_vermaAltFamily :
    (vermaAltFamily P hA hΛ).hsum = (IrreducibleModule.isCategoryO P Λ).character := by
  rw [vermaAltFamily, SummableFamily.hsum_smul, hsum_dotExpFamily,
    ← IrreducibleModule.exp_rho_mul_denominator_mul_character hA hS hΛ]
  have h1 : exp P ℤ (-P.rho) * exp P ℤ P.rho = 1 := by
    rw [← exp_add, neg_add_cancel]; rfl
  calc kostantSeries P * (exp P ℤ (-P.rho) *
          (exp P ℤ P.rho * denominator P * (IrreducibleModule.isCategoryO P Λ).character))
      = (denominator P * kostantSeries P) * (exp P ℤ (-P.rho) * exp P ℤ P.rho) *
          (IrreducibleModule.isCategoryO P Λ).character := by ring
    _ = _ := by rw [denominator_mul_kostantSeries, h1, one_mul, one_mul]

include hS in
/-- **The Euler characteristic of the BGG resolution**, coefficientwise: for every weight `μ`,
`∑_{w ∈ W} (-1)^{ℓ(w)} dim M(w · Λ)_μ = dim L(Λ)_μ` (a finite sum). -/
theorem finsum_neg_one_pow_finrank_weightSpace (μ : Dual K H) :
    ∑ᶠ w : P.weylGroup hA, (-1) ^ (P.coxeterSystem hA).length w *
        (finrank K (VermaModule.weightSpace P (P.weylDot hA w Λ) μ) : ℤ) =
      finrank K (weightSpaceOfMap (IrreducibleModule P Λ) (h P) μ) := by
  have := congrArg (fun c ↦ HahnSeries.coeff c (toWeightOrd P μ))
    (hsum_vermaAltFamily P hA hΛ hS)
  simp only [SummableFamily.coeff_hsum, vermaAltFamily_apply,
    HahnSeries.coeff_smul, smul_eq_mul] at this
  exact this

end Matrix.Realization.KacMoodyAlgebra
