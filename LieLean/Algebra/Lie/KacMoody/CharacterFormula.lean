/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterFormula.Orbit
import LieLean.Algebra.Lie.KacMoody.CompositionSeries.Character

/-!
# The Weyl–Kac character formula

Let `A` be a symmetrizable generalized Cartan matrix (`A.IsSymmetrizable`), `(𝔥, Π, Π^∨)` a
realization of `A` over a field `K` of characteristic zero, `𝔤 = 𝔤(A)` the Kac–Moody algebra, `W`
its Weyl group with length function `ℓ`, `ρ ∈ 𝔥*` with `⟨ρ, αᵢ^∨⟩ = 1` (`Matrix.Realization.rho`),
and `R = ∏_{α ∈ Δ₊} (1 - e^{-α})^{mult α}` the denominator. For a dominant integral weight `Λ`,
the **Weyl–Kac character formula** ([Kac] Thm. 10.4) states
`ch L(Λ) · e^ρ · R = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ)}`.
As `W` is infinite in general, the right-hand side is an infinite formal sum; its support lies
in the cone `Λ + ρ - Q₊`, so it is an element of the algebra `ℰ` of formal characters
(`CharacterRing.weylAltSum`), and the formula is an identity in `ℰ`. We also state it
coefficientwise: the coefficient of `e^μ` in `e^ρ R ch L(Λ)` is
`∑_{w ∈ W, w(Λ + ρ) = μ} (-1)^{ℓ(w)}`, a sum with at most one nonzero term, as the stabilizer of
`Λ + ρ` in `W` is trivial.

## Proof ([Kac] §10.4)

* `e^ρ R ch L(Λ)` is `W`-anti-invariant: `e^ρ R` is anti-invariant ([Kac] §10.2,
  `KacMoodyAlgebra.isWeylAntiInvariant_exp_rho_mul_denominator`) and `ch L(Λ)` is `W`-invariant
  as `L(Λ)` is integrable ([Kac] Lemma 10.1, Prop. 3.7).
* By [Kac] Prop. 9.8 (`KacMoodyAlgebra.coeffAt_denominator_mul_character_ne_zero`), the
  coefficient of `e^μ` in `R ch L(Λ)` vanishes unless `μ ≤ Λ` and `|μ + ρ|² = |Λ + ρ|²`; and it is
  `1` for `μ = Λ`.
* An anti-invariant element with these properties is `∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ)}`
  (`CharacterRing.coeffAt_eq_finsum_of_isWeylAntiInvariant`).

## Main definitions

* `Matrix.Realization.CharacterRing.weylAltSum`: the element `∑_{w ∈ W} (-1)^{ℓ(w)} e^{w λ}` of
  `ℰ`, for `λ` dominant integral.

## Main results

All in the namespace `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule`:

* `exp_rho_mul_denominator_mul_character`: the Weyl–Kac character formula
  `e^ρ R ch L(Λ) = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ)}` ([Kac] Thm. 10.4).
* `coeffAt_exp_rho_mul_denominator_mul_character`: the same, coefficientwise.
* `coeffAt_exp_rho_mul_denominator_mul_character_apply`,
  `coeffAt_exp_rho_mul_denominator_mul_character_eq_zero`: the coefficient of `e^{w(Λ + ρ)}` is
  `(-1)^{ℓ(w)}`, and the coefficients of `e^μ`, `μ ∉ W(Λ + ρ)`, vanish.
* `character_zero`: `L(0)` is the trivial module, `ch L(0) = 1`.
* `exp_rho_mul_denominator`: the denominator identity
  `e^ρ ∏_{α ∈ Δ₊} (1 - e^{-α})^{mult α} = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w ρ}` ([Kac] (10.4.4)).

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.8, §10.1–10.4.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization

namespace CharacterRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)

open Classical in
/-- The alternating sum `∑_{w ∈ W} (-1)^{ℓ(w)} e^{w λ}` for a dominant integral weight `λ`, as an
element of `ℰ`: its support lies in the cone `λ - Q₊`
(`Matrix.Realization.exists_sub_apply_eq_rootOf`). The coefficient of `e^μ` is
`∑_{w ∈ W, w λ = μ} (-1)^{ℓ(w)}`. -/
def weylAltSum {μ₀ : Dual K H} (hμ₀ : ∀ i, ∃ n : ℕ, μ₀ (P.coroot i) = n) : P.CharacterRing ℤ :=
  ofFun P (fun μ ↦ ∑ᶠ w : P.weylGroup hA,
    if (w : Dual K H ≃ₗ[K] Dual K H) μ₀ = μ then (-1) ^ (P.coxeterSystem hA).length w else 0)
    ⟨{μ₀}, fun μ hμ ↦ by
      obtain ⟨w, hw⟩ : ∃ w : P.weylGroup hA, (w : Dual K H ≃ₗ[K] Dual K H) μ₀ = μ := by
        by_contra! h
        exact hμ (finsum_eq_zero_of_forall_eq_zero fun w ↦ ite_eq_right (h w))
      obtain ⟨k, hk, hwk⟩ := P.exists_sub_apply_eq_rootOf hA hμ₀ w
      exact ⟨μ₀, Finset.mem_singleton_self _, k, hk, by rw [← hw, ← hwk, sub_sub_cancel]⟩⟩

open Classical in
lemma coeffAt_weylAltSum {μ₀ : Dual K H} (hμ₀ : ∀ i, ∃ n : ℕ, μ₀ (P.coroot i) = n)
    (μ : Dual K H) :
    (weylAltSum P hA hμ₀).coeffAt μ = ∑ᶠ w : P.weylGroup hA,
      if (w : Dual K H ≃ₗ[K] Dual K H) μ₀ = μ then (-1) ^ (P.coxeterSystem hA).length w else 0 :=
  rfl

end CharacterRing

namespace KacMoodyAlgebra

open CharacterRing WeightOrd

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}

omit [DecidableEq ι] in
/-- `β ≤ Λ` and `Λ ≤ β` imply `β = Λ`. -/
lemma eq_of_mem_cone_of_mem_cone {β Λ : Dual K H} (h₁ : β ∈ cone P Λ) (h₂ : Λ ∈ cone P β) :
    β = Λ :=
  (toWeightOrd P).injective (le_antisymm
    ((toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr h₂)
    ((toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr h₁))

namespace IrreducibleModule

/-- The coefficient of `e^Λ` in `R ch L(Λ)` is `1`. -/
theorem coeffAt_denominator_mul_character_self (Λ : Dual K H) :
    (denominator P * (isCategoryO P Λ).character).coeffAt Λ = 1 := by
  have hM := VermaModule.denominator_mul_character P Λ
  rw [coeffAt_denominator_mul_eq (g := (VermaModule.isCategoryO P Λ).character), hM,
    coeff_exp_self]
  intro β hβ
  rw [IsCategoryO.coeffAt_character, IsCategoryO.coeffAt_character]
  by_cases hβΛ : β = Λ
  · subst hβΛ
    exact_mod_cast (finrank_weightSpace_self P β).trans
      (VermaModule.finrank_weightSpace_self P β).symm
  · have h1 : finrank K (weightSpaceOfMap (IrreducibleModule P Λ) (h P) β) = 0 := by
      by_contra h0
      exact hβΛ (eq_of_mem_cone_of_mem_cone (mem_cone_of_finrank_weightSpace_ne_zero h0) hβ)
    have h2 : finrank K (weightSpaceOfMap (VermaModule P Λ) (h P) β) = 0 := by
      by_contra h0
      have hne : weightSpaceOfMap (VermaModule P Λ) (h P) β ≠ ⊥ := fun hbot ↦
        h0 (by rw [hbot, finrank_bot])
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      exact hβΛ (eq_of_mem_cone_of_mem_cone
        (VermaModule.exists_eq_sub_of_mem_weightSpace P Λ LieModuleHom.id Function.surjective_id
          hx hx0) hβ)
    rw [h1, h2]

omit [DecidableEq ι] [CharZero K] in
/-- `Λ + ρ` is dominant integral if `Λ` is. -/
lemma isDominantIntegral_add_rho {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ) :
    ∀ i, ∃ n : ℕ, (Λ + P.rho) (P.coroot i) = n := fun i ↦ by
  obtain ⟨n, hn⟩ := hΛ i
  exact ⟨n + 1, by rw [LinearMap.add_apply, hn, rho_coroot]; push_cast; rfl⟩

omit [DecidableEq ι] [CharZero K] in
/-- `0` is dominant integral. -/
lemma isDominantIntegral_zero : P.IsDominantIntegral 0 := fun _ ↦ ⟨0, by simp⟩

omit [DecidableEq ι] [CharZero K] in
/-- `ρ` is dominant integral: `⟨ρ, αᵢ^∨⟩ = 1`. -/
lemma isDominantIntegral_rho : P.IsDominantIntegral P.rho := fun i ↦ ⟨1, by simp⟩

/-! ### The trivial module `L(0)` -/

section Trivial

variable (hA : A.IsGeneralizedCartan)
include hA

/-- `𝔤` kills the highest-weight vector of `L(0)`: the `eᵢ` and `𝔥` kill it, and so do the `fᵢ`
since `fᵢ v_0` is a singular vector of `M(0)` ([Kac] §10.1). -/
lemma lie_hwv_zero (x : P.KacMoodyAlgebra) : ⁅x, hwv P (0 : Dual K H)⁆ = 0 := by
  refine induction_on P x (fun i ↦ ?_) (fun i ↦ ?_) (fun a ↦ ?_) (zero_lie _)
    (fun y z hy hz ↦ by rw [add_lie, hy, hz, add_zero])
    (fun c y hy ↦ by rw [smul_lie, hy, smul_zero])
    (fun y z hy hz ↦ by rw [lie_lie, hy, hz, lie_zero, lie_zero, sub_zero])
  · rw [hwv, ← LieModuleHom.map_lie, VermaModule.lie_e_hwv, map_zero]
  · rw [hwv, ← LieModuleHom.map_lie]
    have hmem := VermaModule.fPowHwv_mem_maxSubmodule P (0 : Dual K H) hA
      (i := i) (n := 0) (by simp)
    rw [VermaModule.fPowHwv, zero_add, pow_one, toEnd_apply_apply] at hmem
    exact LieSubmodule.Quotient.mk_eq_zero'.mpr hmem
  · rw [hwv, ← LieModuleHom.map_lie, VermaModule.lie_h_hwv, LinearMap.zero_apply, zero_smul,
      map_zero]

/-- `𝔤` acts trivially on `L(0)`. -/
theorem lie_eq_zero_of_zero (x : P.KacMoodyAlgebra) (m : IrreducibleModule P (0 : Dual K H)) :
    ⁅x, m⁆ = 0 := by
  have htop := VermaModule.lieSpan_map_hwv_eq_top
    (LieSubmodule.Quotient.mk' (VermaModule.maxSubmodule P (0 : Dual K H)))
    (LieSubmodule.Quotient.surjective_mk' _)
  have hle : LieSubmodule.lieSpan K P.KacMoodyAlgebra
      {LieSubmodule.Quotient.mk' (VermaModule.maxSubmodule P (0 : Dual K H))
        (VermaModule.hwv P 0)} ≤
      maxTrivSubmodule K P.KacMoodyAlgebra (IrreducibleModule P (0 : Dual K H)) := by
    rw [LieSubmodule.lieSpan_le]
    rintro _ rfl
    exact fun y ↦ lie_hwv_zero hA y
  rw [htop] at hle
  exact hle (LieSubmodule.mem_top m) x

/-- The character of `L(0)` is `1`: `L(0)` is the trivial one-dimensional module. -/
theorem character_zero : (isCategoryO P (0 : Dual K H)).character = 1 := by
  ext ν
  rw [IsCategoryO.coeffAt_character, ← exp_zero (P := P) (R := ℤ), coeff_exp]
  split_ifs with hν
  · subst hν
    exact_mod_cast finrank_weightSpace_self P (0 : Dual K H)
  · have hbot : weightSpaceOfMap (IrreducibleModule P (0 : Dual K H)) (h P) ν = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨a, ha⟩ : ∃ a, ν a ≠ 0 := by
        by_contra! h0
        exact hν (LinearMap.ext h0)
      have hxa : ⁅h P a, x⁆ = ν a • x := hx a
      rw [lie_eq_zero_of_zero hA] at hxa
      exact (Submodule.mem_bot K).mpr ((smul_eq_zero.mp hxa.symm).resolve_left ha)
    rw [hbot, finrank_bot, Nat.cast_zero]

end Trivial

/-! ### The character formula -/

section Formula

variable [FiniteDimensional K H] (hA : A.IsGeneralizedCartan) (hS : A.IsSymmetrizable)
  {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
include hA hS hΛ

open Classical in
/-- **The Weyl–Kac character formula** ([Kac] Thm. 10.4): for a symmetrizable generalized
Cartan matrix and a dominant integral weight `Λ`,
`e^ρ R ch L(Λ) = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ)}`, where
`R = ∏_{α ∈ Δ₊} (1 - e^{-α})^{mult α}`. It is stated coefficientwise: the coefficient of `e^μ` in
`e^ρ R ch L(Λ)` is `∑_{w ∈ W, w(Λ + ρ) = μ} (-1)^{ℓ(w)}` (a sum with at most one nonzero term). -/
theorem coeffAt_exp_rho_mul_denominator_mul_character (μ : Dual K H) :
    (exp P ℤ P.rho * denominator P * (isCategoryO P Λ).character).coeffAt μ =
      ∑ᶠ w : P.weylGroup hA, if (w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) = μ then
        (-1) ^ (P.coxeterSystem hA).length w else 0 := by
  obtain ⟨S⟩ := isSymmetrizable_iff_nonempty_symmetrization.mp hS
  have hcoeff : ∀ ν, (exp P ℤ P.rho * denominator P * (isCategoryO P Λ).character).coeffAt ν =
      (denominator P * (isCategoryO P Λ).character).coeffAt (ν - P.rho) := fun ν ↦ by
    rw [mul_assoc, coeff_exp_mul]
  refine coeffAt_eq_finsum_of_isWeylAntiInvariant S
    (IsCategoryO.isWeylAntiInvariant_exp_rho_mul_character hA _
      ((isIntegrable_iff P hA).mpr hΛ)) (fun i ↦ ?_) ?_ (fun ν hν ↦ ?_) μ
  · obtain ⟨n, hn⟩ := hΛ i
    exact ⟨n, by rw [LinearMap.add_apply, hn, rho_coroot]⟩
  · rw [hcoeff, add_sub_cancel_right, coeffAt_denominator_mul_character_self]
  · rw [hcoeff] at hν
    obtain ⟨⟨k, hk, hνk⟩, hform⟩ := coeffAt_denominator_mul_character_ne_zero S hA
      (LieSubmodule.Quotient.mk' _) (LieSubmodule.Quotient.surjective_mk' _) _ hν
    refine ⟨⟨k, hk, ?_⟩, ?_⟩
    · rw [sub_eq_iff_eq_add] at hνk
      rw [hνk]
      abel
    · have := (dualBilinForm_add_rho_add_rho_eq_iff S Λ (ν - P.rho)).mpr hform
      rw [sub_add_cancel] at this
      exact this.symm

/-- The Weyl–Kac character formula ([Kac] Thm. 10.4): the coefficient of `e^{w(Λ + ρ)}`
in `e^ρ R ch L(Λ)` is `(-1)^{ℓ(w)}`. -/
theorem coeffAt_exp_rho_mul_denominator_mul_character_apply (w : P.weylGroup hA) :
    (exp P ℤ P.rho * denominator P * (isCategoryO P Λ).character).coeffAt
      ((w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho)) = (-1) ^ (P.coxeterSystem hA).length w := by
  classical
  have hreg : ∀ i, ∃ n : ℕ, (Λ + P.rho) (P.coroot i) = n + 1 := fun i ↦ by
    obtain ⟨n, hn⟩ := hΛ i
    exact ⟨n, by rw [LinearMap.add_apply, hn, rho_coroot]⟩
  rw [coeffAt_exp_rho_mul_denominator_mul_character hA hS hΛ,
    finsum_eq_single _ w fun w' hw' ↦ ite_eq_right fun h ↦ hw'
      (P.apply_injective_of_regular hA hreg h)]
  exact ite_eq_left rfl

/-- The Weyl–Kac character formula ([Kac] Thm. 10.4): the coefficient of `e^μ` in
`e^ρ R ch L(Λ)` vanishes if `μ` is not in the orbit `W(Λ + ρ)`. -/
theorem coeffAt_exp_rho_mul_denominator_mul_character_eq_zero {μ : Dual K H}
    (hμ : ∀ w : P.weylGroup hA, (w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) ≠ μ) :
    (exp P ℤ P.rho * denominator P * (isCategoryO P Λ).character).coeffAt μ = 0 := by
  classical
  rw [coeffAt_exp_rho_mul_denominator_mul_character hA hS hΛ]
  exact finsum_eq_zero_of_forall_eq_zero fun w ↦ ite_eq_right (hμ w)

/-- **The Weyl–Kac character formula** ([Kac] Thm. 10.4): for a symmetrizable generalized
Cartan matrix and a dominant integral weight `Λ`,
`e^ρ R ch L(Λ) = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ)}` in the algebra `ℰ` of formal characters,
where `R = ∏_{α ∈ Δ₊} (1 - e^{-α})^{mult α}`. -/
theorem exp_rho_mul_denominator_mul_character :
    exp P ℤ P.rho * denominator P * (isCategoryO P Λ).character =
      weylAltSum P hA (isDominantIntegral_add_rho hΛ) := by
  ext μ
  rw [coeffAt_weylAltSum, coeffAt_exp_rho_mul_denominator_mul_character hA hS hΛ]

end Formula

variable [FiniteDimensional K H] (hA : A.IsGeneralizedCartan) (hS : A.IsSymmetrizable)
include hA hS

/-- **The Weyl–Kac denominator identity** ([Kac] (10.4.4)): for a symmetrizable
generalized Cartan matrix, `e^ρ ∏_{α ∈ Δ₊} (1 - e^{-α})^{mult α} = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w ρ}`.
This is the character formula for the trivial module `L(0)`. -/
theorem exp_rho_mul_denominator :
    exp P ℤ P.rho * denominator P = weylAltSum P hA (isDominantIntegral_rho (P := P)) := by
  have h := exp_rho_mul_denominator_mul_character hA hS (isDominantIntegral_zero (P := P))
  rw [character_zero hA, mul_one] at h
  ext μ
  rw [h]
  simp only [coeffAt_weylAltSum, zero_add]
  rfl

end IrreducibleModule

end KacMoodyAlgebra

end Matrix.Realization
