/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.CharacterFormula
import LieLean.Algebra.Lie.KacMoody.Grothendieck

/-!
# Littelmann's Littlewood–Richardson rule

Let `A` be a symmetrizable generalized Cartan matrix with a realization over a conditionally
complete ordered field (i.e. over `ℝ`), and `λ, μ` dominant integral weights. Call a path
`π ∈ B(μ)` `λ`-dominant if `λ + π(t)` lies in the dominant chamber for all `t ∈ [0, 1]`, i.e. no
`hⱼ = ⟨π(·), αⱼ^∨⟩` reaches the level `-1 - ⟨λ, αⱼ^∨⟩`. We prove Littelmann's
**Littlewood–Richardson rule**
`ch L(λ) · ch L(μ) = ∑_{π ∈ B(μ) λ-dominant} ch L(λ + π(1))`
in the algebra `ℰ` of formal characters; for integrable modules this is the decomposition of
`L(λ) ⊗ L(μ)` ([Lit94] Thm., [Lit95] §10 (check)).

## Proof

Multiply both sides by the unit `e^ρ R` of `ℰ`. By the Weyl–Kac formula and
`ch L(μ) = ch B(μ)` (`Matrix.Realization.pathCharacter_eq_character`), the left side becomes
`(∑_w (-1)^{ℓ(w)} e^{w(λ + ρ)}) · ch B(μ)`, which by the generalized Brauer–Klimyk formula
(`Matrix.Realization.coeffAt_weylAltSum_mul_pathCharacter`) is
`∑_{π λ-dominant} ∑_w (-1)^{ℓ(w)} e^{w(λ + π(1) + ρ)}`. For `λ`-dominant `π`, the weight
`λ + π(1)` is dominant integral (the minima of the `hⱼ` on Lakshmibai–Seshadri paths are
integers), so the inner sum is `e^ρ R ch L(λ + π(1))` by the Weyl–Kac formula again.

## Main definitions

* `Matrix.Realization.lrFamily`: the summable family `π ↦ ch L(λ + π(1))` over the `λ`-dominant
  paths `π ∈ B(μ)` (and `0` for the other paths).

## Main results

* `Matrix.Realization.isDominantIntegral_add_wt`: `λ + π(1)` is dominant integral for
  `λ`-dominant `π ∈ B(μ)`.
* `Matrix.Realization.character_mul_character`: **the Littlewood–Richardson rule**
  `ch L(λ) ch L(μ) = ∑_{π ∈ B(μ) λ-dominant} ch L(λ + π(1))`.

## References

* [Lit94] P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*,
  Invent. Math. **116** (1994), 329–346.
* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
-/

open Module Set HahnSeries

namespace Matrix.Realization

open CharacterRing KacMoodyAlgebra LittelmannPath WeightOrd

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [ConditionallyCompleteLinearOrder K]
  [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] [FloorRing K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H} (hA : A.IsGeneralizedCartan)
  {Λ₁ Λ₂ : Dual K H} (hΛ₁ : P.IsDominantIntegral Λ₁) (hΛ₂ : P.IsDominantIntegral Λ₂)

omit [DecidableEq ι] in
/-- For regular dominant integral `ρ'`, only finitely many pairs `(w, π) ∈ W × B(μ)` have
`w(π(1) + ρ') = κ`. -/
lemma finite_setOf_apply_wt_add_eq {ρ' : Dual K H}
    (hρ' : ∀ i, ∃ n : ℕ, ρ' (P.coroot i) = n + 1) (κ : Dual K H) :
    {p : P.weylGroup hA × (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component |
      p.1.1 ((p.2.1.wt : Dual K H) + ρ') = κ}.Finite := by
  refine ((finite_setOf_pathMult_ne_zero hA hΛ₂ hρ' κ).biUnion fun w _ ↦
    (Set.finite_singleton w).prod (finite_fibre hA hΛ₂ ((w⁻¹).1 κ - ρ'))).subset ?_
  rintro ⟨w, b⟩ (hp : w.1 _ = κ)
  have hb : (b.1.wt : Dual K H) = (w⁻¹).1 κ - ρ' := by
    rw [← hp, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
    exact (add_sub_cancel_right _ _).symm
  refine Set.mem_biUnion (x := w) ?_ ⟨rfl, hb⟩
  change pathMult hA hΛ₂ (κ - w.1 ρ') ≠ 0
  rw [show κ - w.1 ρ' = w.1 (b.1.wt : Dual K H) by rw [← hp, map_add, add_sub_cancel_right],
    pathMult_apply]
  exact (Nat.card_pos_iff.mpr ⟨⟨⟨b, rfl⟩⟩, (finite_fibre hA hΛ₂ _).to_subtype⟩).ne'

omit [DecidableEq ι] in
/-- If `π ∈ B(μ)` is `λ`-dominant (no `hⱼ` reaches `-1 - ⟨λ, αⱼ^∨⟩`), then `λ + π(1)` is
dominant integral: the minimum of each `hⱼ` is an integer `> -1 - ⟨λ, αⱼ^∨⟩`. -/
lemma isDominantIntegral_add_wt
    (b : (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component)
    (hb : b.1.hitSet (shiftLevel hA hΛ₁) = ∅) :
    P.IsDominantIntegral (Λ₁ + (b.1.wt : Dual K H)) := by
  classical
  intro i
  obtain ⟨n, hn⟩ :=
    ((component_straightLine_eq_fOrbit (hA := hA) hΛ₂).2 b.1 b.2).exists_int_minPairing i
  have hlt : ¬b.1.minPairing i ≤ (shiftLevel hA hΛ₁ i : K) := fun h ↦
    (Set.nonempty_iff_ne_empty.mp (hitSet_nonempty h)) hb
  obtain ⟨N, hN⟩ := hΛ₁ i
  rw [hn, shiftLevel_cast, hN, not_le] at hlt
  have h1 := b.1.minPairing_le_pairing_one i
  rw [hn, pairing_one] at h1
  have hlt' : -1 - (N : ℤ) < n := by exact_mod_cast hlt
  have h1' : n ≤ (P.cartanDatum hA).coroot i b.1.wt := by exact_mod_cast h1
  refine ⟨((N : ℤ) + (P.cartanDatum hA).coroot i b.1.wt).toNat, ?_⟩
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), LinearMap.add_apply, hN, Int.cast_add,
    coroot_cartanDatum_cast, Int.cast_natCast]

open Classical in
/-- The summable family `π ↦ ch L(λ + π(1))` over the paths `π ∈ B(μ)` which are `λ`-dominant
(no `hⱼ` reaches `-1 - ⟨λ, αⱼ^∨⟩`), and `π ↦ 0` for the other paths. -/
noncomputable def lrFamily : SummableFamily P.WeightOrd ℤ
    (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component where
  toFun b := if b.1.hitSet (shiftLevel hA hΛ₁) = ∅ then
    (IrreducibleModule.isCategoryO P (Λ₁ + (b.1.wt : Dual K H))).character else 0
  isPWO_iUnion_support' := by
    refine (isPWO_iff P).mpr ⟨{Λ₁ + Λ₂}, fun ν hν ↦ ?_⟩
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hν
    rw [HahnSeries.mem_support] at hb
    by_cases hd : b.1.hitSet (shiftLevel hA hΛ₁) = ∅
    · rw [ite_eq_left hd] at hb
      have h2 : (IrreducibleModule.isCategoryO P (Λ₁ + (b.1.wt : Dual K H))).character.coeffAt
          (ofWeightOrd P ν) ≠ 0 := hb
      rw [IsCategoryO.coeffAt_character, Nat.cast_ne_zero] at h2
      obtain ⟨l, hl, hνμ⟩ := IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero h2
      obtain ⟨k, hk, hbk⟩ := exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ₂ b
      change (b.1.wt : Dual K H) = _ at hbk
      refine ⟨Λ₁ + Λ₂, Finset.mem_singleton_self _, k + l, add_nonneg hk hl, ?_⟩
      rw [hνμ, hbk, map_add]
      abel
    · rw [ite_eq_right hd, HahnSeries.coeff_zero] at hb
      exact absurd rfl hb
  finite_co_support' g := by
    refine ((finite_setOf_mem_cone_and_mem_cone P (Λ₁ + Λ₂) (ofWeightOrd P g)).biUnion
      fun μ _ ↦ finite_fibre hA hΛ₂ (μ - Λ₁)).subset fun b hb ↦ ?_
    rw [Set.mem_ofPred_eq] at hb
    by_cases hd : b.1.hitSet (shiftLevel hA hΛ₁) = ∅
    · rw [ite_eq_left hd] at hb
      have h2 : (IrreducibleModule.isCategoryO P (Λ₁ + (b.1.wt : Dual K H))).character.coeffAt
          (ofWeightOrd P g) ≠ 0 := hb
      rw [IsCategoryO.coeffAt_character, Nat.cast_ne_zero] at h2
      obtain ⟨k, hk, hbk⟩ := exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ₂ b
      change (b.1.wt : Dual K H) = _ at hbk
      refine Set.mem_biUnion (x := Λ₁ + (b.1.wt : Dual K H))
        ⟨⟨k, hk, by rw [hbk]; abel⟩,
          IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero h2⟩ ?_
      change (b.1.wt : Dual K H) = Λ₁ + (b.1.wt : Dual K H) - Λ₁
      abel
    · rw [ite_eq_right hd, HahnSeries.coeff_zero] at hb
      exact absurd rfl hb

open Classical in
lemma lrFamily_apply
    (b : (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component) :
    lrFamily hA hΛ₁ hΛ₂ b = if b.1.hitSet (shiftLevel hA hΛ₁) = ∅ then
      (IrreducibleModule.isCategoryO P (Λ₁ + (b.1.wt : Dual K H))).character else 0 :=
  rfl

/-- **Littelmann's Littlewood–Richardson rule** ([Lit94] Thm. (check), [Lit95] §10 (check)): for
a symmetrizable generalized Cartan matrix and dominant integral weights `λ, μ`,
`ch L(λ) · ch L(μ) = ∑_{π ∈ B(μ) λ-dominant} ch L(λ + π(1))` in `ℰ`, where `π ∈ B(μ)` is
`λ`-dominant if no `hⱼ` reaches `-1 - ⟨λ, αⱼ^∨⟩` (equivalently, `λ + π(t)` is dominant for all
`t`). The proof multiplies by the unit `e^ρ R` and combines the Weyl–Kac formula with the
generalized Brauer–Klimyk formula `Matrix.Realization.coeffAt_weylAltSum_mul_pathCharacter`. -/
theorem character_mul_character [FiniteDimensional K H] (hS : A.IsSymmetrizable) :
    (IrreducibleModule.isCategoryO P Λ₁).character *
        (IrreducibleModule.isCategoryO P Λ₂).character =
      (lrFamily hA hΛ₁ hΛ₂).hsum := by
  classical
  set πΛ := straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩ with hπΛ
  have hR : IsUnit (denominator P) := by
    have := VermaModule.denominator_mul_character P 0
    rw [exp_zero] at this
    exact IsUnit.of_mul_eq_one _ this
  have hρ : IsUnit (exp P ℤ P.rho) :=
    IsUnit.of_mul_eq_one (exp P ℤ (-P.rho)) (by rw [← exp_add, add_neg_cancel, exp_zero])
  have hreg : ∀ i, ∃ n : ℕ, (Λ₁ + P.rho) (P.coroot i) = n + 1 := fun i ↦ by
    obtain ⟨n, hn⟩ := hΛ₁ i
    exact ⟨n, by rw [LinearMap.add_apply, hn, rho_coroot]⟩
  apply (hρ.mul hR).mul_left_cancel
  rw [← mul_assoc, IrreducibleModule.exp_rho_mul_denominator_mul_character hA hS hΛ₁,
    ← pathCharacter_eq_character hA hΛ₂ hS, ← SummableFamily.hsum_smul]
  ext κ
  rw [coeffAt_weylAltSum_mul_pathCharacter hA hΛ₂ hΛ₁ κ, coeffAt, SummableFamily.coeff_hsum]
  have hterm : ∀ b : πΛ.component,
      (((exp P ℤ P.rho * denominator P) • lrFamily hA hΛ₁ hΛ₂) b).coeff (toWeightOrd P κ) =
        ∑ᶠ w : P.weylGroup hA, if b.1.hitSet (shiftLevel hA hΛ₁) = ∅ ∧
          w.1 ((b.1.wt : Dual K H) + (Λ₁ + P.rho)) = κ then
            (-1) ^ (P.coxeterSystem hA).length w else 0 := by
    intro b
    rw [SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul, lrFamily_apply]
    by_cases hd : b.1.hitSet (shiftLevel hA hΛ₁) = ∅
    · rw [ite_eq_left hd, IrreducibleModule.exp_rho_mul_denominator_mul_character hA hS
        (isDominantIntegral_add_wt hA hΛ₁ hΛ₂ b hd)]
      change (weylAltSum P hA _).coeffAt κ = _
      rw [coeffAt_weylAltSum]
      refine finsum_congr fun w ↦ ?_
      rw [show Λ₁ + (b.1.wt : Dual K H) + P.rho = (b.1.wt : Dual K H) + (Λ₁ + P.rho) by abel]
      simp only [hd, true_and]
    · rw [ite_eq_right hd, mul_zero, HahnSeries.coeff_zero]
      exact (finsum_eq_zero_of_forall_eq_zero fun w ↦ ite_eq_right fun h ↦ hd h.1).symm
  rw [finsum_congr hterm, ← finsum_comp_equiv (Equiv.prodComm πΛ.component (P.weylGroup hA)),
    finsum_curry]
  · rfl
  · refine ((finite_setOf_apply_wt_add_eq hA hΛ₂ hreg κ).preimage
      (Equiv.prodComm _ _).injective.injOn).subset fun q hq ↦ ?_
    rw [Function.mem_support] at hq
    by_contra h
    exact hq (ite_eq_right fun h' ↦ h h'.2)

end Matrix.Realization
