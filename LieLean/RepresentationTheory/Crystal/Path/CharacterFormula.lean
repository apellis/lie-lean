/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Stability
import LieLean.RepresentationTheory.Crystal.Path.Cancellation
import LieLean.Algebra.Lie.KacMoody.CharacterFormula
import Mathlib.Data.Pi.Interval

/-!
# Littelmann's character formula

Let `A` be a generalized Cartan matrix with a realization over a conditionally complete ordered
field (i.e. over `ℝ`), and `λ` a dominant integral weight. The character of Littelmann's crystal
`B(λ)` (the connected component of the straight line path `π_λ`) is
`ch B(λ) = ∑_{π ∈ B(λ)} e^{π(1)} ∈ ℰ` (`Matrix.Realization.pathCharacter`; its weights lie in
`λ - Q₊` with finite multiplicities by `LieLean.RepresentationTheory.Crystal.Path.Stability`). We
prove the path-model Weyl character formula
`(∑_{w ∈ W} (-1)^{ℓ(w)} e^{wρ}) · ch B(λ) = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(λ + ρ)}`
for every generalized Cartan matrix, and deduce `ch B(λ) = ch L(λ)` for symmetrizable `A` from the
Weyl–Kac character formula.

## Proof of the character formula ([Lit95] §9 (check); our write-up)

By the `W`-invariance of the weight multiplicities of `B(λ)`
(`Matrix.Realization.card_wt_weylGroup_pathCrystal`), the coefficient of `e^μ` on the left is
`∑ (-1)^{ℓ(w)}` over the finite set of pairs `(w, π)`, `w ∈ W`, `π ∈ B(λ)`, with
`w(π(1) + ρ) = μ`. If `π ≠ π_λ`, some `hⱼ` reaches `-1` (as `π = fⱼ π''` for some `j`), and
Littelmann's involution `(w, π) ↦ (w rᵢ, π')` (`LittelmannPath.exists_reflectAfter_hitIndex`,
`Matrix.Realization.reflectPair`) preserves `w(π(1) + ρ)` and reverses the sign, so these pairs
cancel. The pairs `(w, π_λ)` give `∑_{w(λ + ρ) = μ} (-1)^{ℓ(w)}`.

For symmetrizable `A`, the left side is `e^ρ R ch B(λ)` by the denominator identity, and
`e^ρ R ch L(λ)` is the same alternating sum by the Weyl–Kac formula; since `e^ρ R` is a unit of
`ℰ`, `ch B(λ) = ch L(λ)`.

## Main definitions

* `Matrix.Realization.pathCharacter`: the character of `B(λ)` in `ℰ`.
* `Matrix.Realization.shiftLevel`: the levels `-1 - ⟨ν, αⱼ^∨⟩` of `ν`-dominance.
* `Matrix.Realization.reflectPair`: Littelmann's involution on pairs `(w, π)`.

## Main results

* `Matrix.Realization.coeffAt_weylAltSum_mul_pathCharacter`: the generalized Brauer–Klimyk
  formula `(∑_w (-1)^{ℓ(w)} e^{w(ν+ρ)}) ch B(λ) = ∑_{π ν-dominant} ∑_w (-1)^{ℓ(w)} e^{w(ν+π(1)+ρ)}`,
  coefficientwise.
* `Matrix.Realization.weylAltSum_rho_mul_pathCharacter`: the path-model Weyl character formula
  (any generalized Cartan matrix).
* `Matrix.Realization.pathCharacter_eq_character`: **Littelmann's character formula**
  `ch B(λ) = ch L(λ)` for symmetrizable `A` ([Lit95] Thm. 9.1 (check), [Lit94]).

## References

* [Lit94] P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*,
  Invent. Math. **116** (1994), 329–346.
* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §10.4.
-/

open Module Set

namespace Matrix.Realization

open CharacterRing KacMoodyAlgebra LittelmannPath

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [ConditionallyCompleteLinearOrder K]
  [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] [FloorRing K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H} (hA : A.IsGeneralizedCartan)
  {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)

omit [DecidableEq ι] [TopologicalSpace K] [OrderTopology K] [FloorRing K] in
variable (P) in
/-- `ρ` is regular dominant integral. -/
lemma rho_regular : ∀ i, ∃ n : ℕ, P.rho (P.coroot i) = n + 1 := fun i ↦ ⟨0, by simp⟩

omit [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] in
lemma coe_mul_simple_apply (w : P.weylGroup hA) (i : ι) (μ : Dual K H) :
    (w * (P.coxeterSystem hA).simple i).1 μ = w.1 (P.reflection hA i μ) := by
  rw [Subgroup.coe_mul, coxeterSystem_simple, LinearEquiv.mul_apply]

omit [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] in
lemma neg_one_pow_length_mul_simple (w : P.weylGroup hA) (i : ι) :
    ((-1 : ℤ) ^ (P.coxeterSystem hA).length (w * (P.coxeterSystem hA).simple i)) =
      -(-1) ^ (P.coxeterSystem hA).length w := by
  rcases (P.coxeterSystem hA).length_mul_simple w i with h | h
  · rw [h, pow_succ]; ring
  · rw [← h, pow_succ]; ring

section Fibres

include hΛ

/-- The multiplicity `#{π ∈ B(λ) | π(1) = x}`. -/
noncomputable abbrev pathMult (x : Dual K H) : ℕ :=
  Nat.card {b : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component //
    (b.1.wt : Dual K H) = x}

omit [DecidableEq ι] in
lemma finite_fibre (x : Dual K H) :
    {b : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component |
      (b.1.wt : Dual K H) = x}.Finite := by
  by_cases hx : x ∈ P.integralWeights
  · refine ((finite_setOf_wt_pathCrystal (hA := hA) hΛ ⟨x, hx⟩).preimage
      Subtype.val_injective.injOn).subset fun b hb ↦ ⟨b.2, Subtype.ext hb⟩
  · convert Set.finite_empty
    ext b
    simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro h
    exact hx (h ▸ b.1.wt.2)

omit [DecidableEq ι] in
/-- Weight multiplicities of `B(λ)` are `W`-invariant. -/
lemma pathMult_apply (w : P.weylGroup hA) (x : Dual K H) :
    pathMult hA hΛ (w.1 x) = pathMult hA hΛ x :=
  card_wt_weylGroup_pathCrystal hA hΛ w.2 x

omit [DecidableEq ι] in
/-- For each `μ` and each regular dominant integral `ρ'`, only finitely many `w ∈ W` have
`μ - wρ'` a weight of `B(λ)`. -/
lemma finite_setOf_pathMult_ne_zero {ρ' : Dual K H}
    (hρ' : ∀ i, ∃ n : ℕ, ρ' (P.coroot i) = n + 1) (μ : Dual K H) :
    {w : P.weylGroup hA | pathMult hA hΛ (μ - w.1 ρ') ≠ 0}.Finite := by
  classical
  have hρ : P.IsDominantIntegral ρ' := fun i ↦ by
    obtain ⟨n, hn⟩ := hρ' i
    exact ⟨n + 1, by rw [hn]; push_cast; ring⟩
  -- if `μ - wρ' = wt b`, then `Λ + ρ' - μ = (ρ' - wρ') + (Λ - wt b)` with both terms in `Q₊`
  have key : ∀ w : P.weylGroup hA, pathMult hA hΛ (μ - w.1 ρ') ≠ 0 →
      ∃ k k' : ι → ℤ, 0 ≤ k ∧ 0 ≤ k' ∧ ρ' - w.1 ρ' = P.rootOf k ∧
        Λ + ρ' - μ = P.rootOf (k + k') := by
    intro w hw
    obtain ⟨⟨b, hb⟩⟩ : Nonempty {b : (straightLine (P.pathSpace hA)
        ⟨Λ, hΛ.mem_integralWeights⟩).component // (b.1.wt : Dual K H) = μ - w.1 ρ'} := by
      by_contra h
      exact hw (by rw [not_nonempty_iff] at h; exact Nat.card_of_isEmpty)
    obtain ⟨k, hk, hwk⟩ := P.exists_sub_apply_eq_rootOf hA hρ w
    obtain ⟨k', hk', hbk⟩ := exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ b
    refine ⟨k, k', hk, hk', hwk, ?_⟩
    change (b.1.wt : Dual K H) = _ at hbk
    rw [map_add, ← hwk]
    rw [hb] at hbk
    rw [show P.rootOf k' = Λ - (μ - w.1 ρ') by rw [hbk]; abel]
    abel
  by_cases hne : ∃ w₀ : P.weylGroup hA, pathMult hA hΛ (μ - w₀.1 ρ') ≠ 0
  · obtain ⟨w₀, hw₀⟩ := hne
    obtain ⟨k₀, k₀', hk₀, hk₀', -, hμ₀⟩ := key w₀ hw₀
    refine (((Set.finite_Icc (0 : ι → ℤ) (k₀ + k₀')).image fun k ↦ ρ' - P.rootOf k).preimage
      (P.apply_injective_of_regular hA hρ').injOn).subset fun w hw ↦ ?_
    obtain ⟨k, k', hk, hk', hwk, hμ⟩ := key w hw
    have hkk : k + k' = k₀ + k₀' := P.rootOf_injective (hμ.symm.trans hμ₀)
    refine ⟨k, ⟨hk, fun j ↦ ?_⟩, by simp only; rw [← hwk]; abel⟩
    have := congr_fun hkk j
    have := hk' j
    have := hk₀ j
    have := hk₀' j
    simp only [Pi.add_apply, Pi.zero_apply] at *
    omega
  · push Not at hne
    convert Set.finite_empty
    ext w
    simp [hne w]

omit [DecidableEq ι] in
/-- A path of `B(λ)` other than `π_λ` has some `hⱼ` reaching `-1`. -/
lemma hitSet_nonempty_of_ne
    (b : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component)
    (hb : b.1 ≠ straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩) :
    (b.1.hitSet fun _ ↦ -1).Nonempty := by
  classical
  have h := (component_straightLine_eq_fOrbit (hA := hA) hΛ).1
  obtain ⟨l, hl⟩ : b.1 ∈ (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).fOrbit :=
    h ▸ b.2
  cases l with
  | nil => exact absurd (Option.some_injective _ hl).symm hb
  | cons j l =>
    obtain ⟨b', -, hf⟩ := Option.bind_eq_some_iff.mp hl
    have he := f_eq_some_iff.mp hf
    have hm : b.1.minPairing j ≤ ((-1 : ℤ) : K) := by
      by_contra hlt
      push_cast at hlt
      rw [(e_eq_none_iff).mpr (not_le.mp hlt)] at he
      simp at he
    exact hitSet_nonempty (c := fun _ ↦ -1) hm

omit [DecidableEq ι] in
lemma hitSet_straightLine :
    ((straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).hitSet fun _ ↦ -1) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ⟨ht, j, hj⟩ ↦ ?_
  rw [pairing_straightLine] at hj
  have : (0 : K) ≤ ((P.cartanDatum hA).coroot j ⟨Λ, hΛ.mem_integralWeights⟩ : K) := by
    exact_mod_cast IsDominantIntegral.coroot_nonneg hA hΛ j
  have := mul_nonneg (le_max_left 0 (min 1 t)) this
  push_cast at hj
  linarith

end Fibres

/-! ### Dominance relative to a weight -/

section Shift

variable {ν : Dual K H} (hν : P.IsDominantIntegral ν)

/-- The levels `cⱼ = -1 - ⟨ν, αⱼ^∨⟩` for a dominant integral weight `ν`: a path `η` has
`hⱼ > cⱼ` everywhere iff `ν + η(t)` has all `⟨·, αⱼ^∨⟩ > -1` (for Lakshmibai–Seshadri paths:
iff `ν + η(t)` is dominant for all `t`). -/
noncomputable def shiftLevel (j : ι) : ℤ :=
  -1 - (P.cartanDatum hA).coroot j ⟨ν, hν.mem_integralWeights⟩

omit [DecidableEq ι] [TopologicalSpace K] [OrderTopology K] in
lemma shiftLevel_le (j : ι) : shiftLevel hA hν j ≤ -1 := by
  have := IsDominantIntegral.coroot_nonneg hA hν j
  unfold shiftLevel
  omega

omit [DecidableEq ι] [TopologicalSpace K] [OrderTopology K] in
lemma shiftLevel_cast (j : ι) : (shiftLevel hA hν j : K) = -1 - ν (P.coroot j) := by
  rw [shiftLevel, Int.cast_sub, coroot_cartanDatum_cast]
  norm_num

omit [DecidableEq ι] [TopologicalSpace K] [OrderTopology K] in
lemma shiftLevel_zero (j : ι) :
    shiftLevel hA (IrreducibleModule.isDominantIntegral_zero (P := P)) j = -1 := by
  have := shiftLevel_cast hA (IrreducibleModule.isDominantIntegral_zero (P := P)) j
  rw [LinearMap.zero_apply, sub_zero] at this
  exact_mod_cast this

include hΛ

/-- Littelmann's involution on pairs `(w, π)`, `π ∈ B(λ)` not `ν`-dominant: with `τ` the first
time some `hⱼ(τ) = cⱼ = -1 - ⟨ν, αⱼ^∨⟩` and `i` the chosen such index, `(w, π) ↦ (w rᵢ, π')`
where `π'` reflects the part of `π` after `τ` (`LittelmannPath.exists_reflectAfter_hitIndex`). -/
noncomputable def reflectPair
    (p : P.weylGroup hA × (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component)
    (h : (p.2.1.hitSet (shiftLevel hA hν)).Nonempty) :
    P.weylGroup hA × (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component :=
  (p.1 * (P.coxeterSystem hA).simple (hitIndex h),
    ⟨(exists_reflectAfter_hitIndex (shiftLevel_le hA hν) h).choose,
      Crystal.closure_singleton_subset p.2.2
        (exists_reflectAfter_hitIndex (shiftLevel_le hA hν) h).choose_spec.2.1⟩)

lemma reflectPair_spec
    (p : P.weylGroup hA × (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component)
    (h : (p.2.1.hitSet (shiftLevel hA hν)).Nonempty) :
    ∃ h' : ((reflectPair hA hΛ hν p h).2.1.hitSet (shiftLevel hA hν)).Nonempty,
      hitIndex h' = hitIndex h ∧
      ((reflectPair hA hΛ hν p h).2.1.wt : Dual K H) + (ν + P.rho) =
        P.reflection hA (hitIndex h) ((p.2.1.wt : Dual K H) + (ν + P.rho)) ∧
      reflectPair hA hΛ hν (reflectPair hA hΛ hν p h) h' = p := by
  obtain ⟨-, -, h', hi, hwt, hback⟩ :=
    (exists_reflectAfter_hitIndex (shiftLevel_le hA hν) h).choose_spec
  refine ⟨h', hi, ?_, ?_⟩
  · change ((exists_reflectAfter_hitIndex (shiftLevel_le hA hν) h).choose.wt : Dual K H) +
      (ν + P.rho) = _
    rw [hwt, AddSubgroup.coe_add, coe_reflection_cartanDatum, AddSubgroup.coe_zsmul,
      coe_root_cartanDatum, ← Int.cast_smul_eq_zsmul K, shiftLevel_cast, map_add, map_add,
      reflection_apply P hA _ P.rho, rho_coroot, one_smul, reflection_apply P hA _ ν]
    module
  · have hc := (exists_reflectAfter_hitIndex (shiftLevel_le hA hν) h').choose_spec.1
    have hc2 : reflectAfter (reflectPair hA hΛ hν p h).2.1 (hitIndex h')
        (shiftLevel hA hν (hitIndex h')) = some p.2.1 := by
      rw [hi]
      exact hback
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change p.1 * _ * (P.coxeterSystem hA).simple (hitIndex h') = p.1
      rw [hi, CoxeterSystem.simple_mul_simple_cancel_right]
    · exact Option.some_injective _ (hc.symm.trans hc2)

end Shift

/-! ### The path-model Weyl character formula -/

section Formula

/-- The character `ch B(λ) = ∑_{π ∈ B(λ)} e^{π(1)} ∈ ℰ` of Littelmann's crystal `B(λ)`
(its weights lie in `λ - Q₊`, with finite multiplicities). -/
noncomputable def pathCharacter : P.CharacterRing ℤ :=
  Crystal.formalCharacterOfCones (P.pathCrystal hA hΛ)
    ⟨{Λ}, fun b ↦ ⟨Λ, Finset.mem_singleton_self _, exists_wt_eq_sub_rootOf_pathCrystal hΛ b⟩⟩

omit [DecidableEq ι] in
lemma coeffAt_pathCharacter (μ : Dual K H) :
    (pathCharacter hA hΛ).coeffAt μ = pathMult hA hΛ μ :=
  Crystal.coeffAt_formalCharacterOfCones _ _ μ

open Classical in
/-- **Littelmann's generalized Brauer–Klimyk formula** ([Lit94] §5–6, [Lit95] §9 (check); our
write-up): for dominant integral `ν` and `λ`, the coefficient of `e^κ` in
`(∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(ν + ρ)}) · ch B(λ)` is the signed count of pairs `(w, π)`,
`π ∈ B(λ)` `ν`-dominant (no `hⱼ` reaches `-1 - ⟨ν, αⱼ^∨⟩`), with `w(ν + π(1) + ρ) = κ`. That
is, `(∑_w (-1)^{ℓ(w)} e^{w(ν + ρ)}) · ch B(λ)` is
`∑_{π ν-dominant} ∑_w (-1)^{ℓ(w)} e^{w(ν + π(1) + ρ)}`.

Proof: by the `W`-invariance of the weight multiplicities, the coefficient is the signed count of
all pairs `(w, π)` with `w(π(1) + ν + ρ) = κ`; the pairs with `π` not `ν`-dominant cancel under
Littelmann's involution (`Matrix.Realization.reflectPair`). -/
theorem coeffAt_weylAltSum_mul_pathCharacter {ν : Dual K H} (hν : P.IsDominantIntegral ν)
    (κ : Dual K H) :
    (weylAltSum P hA (IrreducibleModule.isDominantIntegral_add_rho hν) *
      pathCharacter hA hΛ).coeffAt κ =
    ∑ᶠ p : P.weylGroup hA ×
        (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component,
      if p.2.1.hitSet (shiftLevel hA hν) = ∅ ∧
          p.1.1 ((p.2.1.wt : Dual K H) + (ν + P.rho)) = κ then
        (-1) ^ (P.coxeterSystem hA).length p.1 else 0 := by
  classical
  set πΛ := straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩ with hπΛ
  set ε : P.weylGroup hA → ℤ := fun w ↦ (-1) ^ (P.coxeterSystem hA).length w with hε
  set ρ' := ν + P.rho with hρ'
  have hreg : ∀ i, ∃ n : ℕ, ρ' (P.coroot i) = n + 1 := fun i ↦ by
    obtain ⟨n, hn⟩ := hν i
    exact ⟨n, by rw [hρ', LinearMap.add_apply, hn, rho_coroot]⟩
  have hinj := P.apply_injective_of_regular hA hreg
  have hF := finite_setOf_pathMult_ne_zero hA hΛ hreg κ
  set T := hF.toFinset with hT
  -- the coefficient as a sum over `w`
  have step1 : (weylAltSum P hA (IrreducibleModule.isDominantIntegral_add_rho hν) *
      pathCharacter hA hΛ).coeffAt κ = ∑ w ∈ T, ε w * (pathMult hA hΛ (κ - w.1 ρ') : ℤ) := by
    rw [coeff_mul, finsum_eq_sum_of_support_subset _ (s := T.image fun w ↦ w.1 ρ') ?_,
      Finset.sum_image fun w _ w' _ h ↦ hinj h]
    · refine Finset.sum_congr rfl fun w _ ↦ ?_
      simp only [weylAltSum, coeff_ofFun]
      rw [finsum_eq_single _ w fun w' hw' ↦
        ite_eq_right fun h ↦ hw' (hinj h), ite_eq_left rfl, coeffAt_pathCharacter]
    · intro μ hμ
      rw [Function.mem_support] at hμ
      obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hμ
      simp only [weylAltSum, coeff_ofFun] at h₁
      obtain ⟨w, hw⟩ : ∃ w : P.weylGroup hA, w.1 ρ' = μ := by
        by_contra! h
        exact h₁ (finsum_eq_zero_of_forall_eq_zero fun w ↦ ite_eq_right (h w))
      rw [Finset.coe_image]
      refine ⟨w, ?_, hw⟩
      rw [hT, Set.Finite.coe_toFinset]
      rw [coeffAt_pathCharacter, ← hw] at h₂
      exact_mod_cast h₂
  -- the fibres and the set of pairs
  have hinv : ∀ (w : P.weylGroup hA) (x : Dual K H), w.1 x = κ ↔ x = (w⁻¹).1 κ := by
    intro w x
    constructor
    · rintro rfl
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
      rfl
    · rintro rfl
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
      rfl
  have hfin := fun w : P.weylGroup hA ↦ finite_fibre hA hΛ ((w⁻¹).1 κ - ρ')
  have hκw : ∀ w : P.weylGroup hA, κ - w.1 ρ' = w.1 ((w⁻¹).1 κ - ρ') := fun w ↦ by
    rw [map_sub, ((hinv w _).mpr rfl)]
  have hcard : ∀ w : P.weylGroup hA,
      pathMult hA hΛ (κ - w.1 ρ') = (hfin w).toFinset.card := fun w ↦ by
    rw [hκw, pathMult_apply, ← Nat.card_eq_card_finite_toFinset]
    rfl
  set Fall := T.biUnion fun w ↦ (hfin w).toFinset
  set S := (T ×ˢ Fall).filter fun p ↦ p.1.1 ((p.2.1.wt : Dual K H) + ρ') = κ with hS
  have hmemfib : ∀ (w : P.weylGroup hA) (b : πΛ.component),
      b ∈ (hfin w).toFinset ↔ w.1 ((b.1.wt : Dual K H) + ρ') = κ := fun w b ↦ by
    rw [Set.Finite.mem_toFinset, hinv, Set.mem_ofPred_eq, eq_sub_iff_add_eq]
  have hmemT : ∀ (w : P.weylGroup hA) (b : πΛ.component),
      w.1 ((b.1.wt : Dual K H) + ρ') = κ → w ∈ T := fun w b hb ↦ by
    rw [hT, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hcard]
    exact Finset.card_ne_zero.mpr ⟨b, (hmemfib w b).mpr hb⟩
  have hmemS : ∀ p, p ∈ S ↔ p.1.1 ((p.2.1.wt : Dual K H) + ρ') = κ := by
    rintro ⟨w, b⟩
    simp only [hS, Finset.mem_filter, Finset.mem_product, Fall, Finset.mem_biUnion]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨⟨hmemT w b h, w, hmemT w b h, (hmemfib w b).mpr h⟩, h⟩⟩
  have step2 : ∑ w ∈ T, ε w * (pathMult hA hΛ (κ - w.1 ρ') : ℤ) = ∑ p ∈ S, ε p.1 := by
    rw [hS, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    have hfil : Fall.filter (fun b ↦ w.1 ((b.1.wt : Dual K H) + ρ') = κ) =
        (hfin w).toFinset := by
      ext b
      simp only [Finset.mem_filter, Fall, Finset.mem_biUnion]
      exact ⟨fun h ↦ (hmemfib w b).mpr h.2, fun h ↦ ⟨⟨w, hw, h⟩, (hmemfib w b).mp h⟩⟩
    rw [← Finset.sum_filter]
    dsimp only
    rw [hfil, Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]
  rw [step1, step2, ← Finset.sum_filter_add_sum_filter_not S
    (fun p ↦ p.2.1.hitSet (shiftLevel hA hν) = ∅)]
  -- the pairs which are not `ν`-dominant cancel
  have hne : ∀ p ∈ S.filter (fun p ↦ ¬p.2.1.hitSet (shiftLevel hA hν) = ∅),
      (p.2.1.hitSet (shiftLevel hA hν)).Nonempty := fun p hp ↦
    Set.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp hp).2
  have hzero : ∑ p ∈ S.filter (fun p ↦ ¬p.2.1.hitSet (shiftLevel hA hν) = ∅), ε p.1 = 0 := by
    refine Finset.sum_involution (fun p hp ↦ reflectPair hA hΛ hν p (hne p hp))
      (fun p hp ↦ ?_) (fun p hp _ ↦ ?_) (fun p hp ↦ ?_) (fun p hp ↦ ?_)
    · change ε p.1 + ε (p.1 * _) = 0
      rw [hε]
      simp only [neg_one_pow_length_mul_simple]
      ring
    · intro h
      have h1 := congrArg Prod.fst h
      change p.1 * _ = p.1 at h1
      have h2 := (P.coxeterSystem hA).length_simple (hitIndex (hne p hp))
      rw [mul_eq_left.mp h1, CoxeterSystem.length_one] at h2
      exact absurd h2 (by norm_num)
    · obtain ⟨h', -, hwt, -⟩ := reflectPair_spec hA hΛ hν p (hne p hp)
      refine Finset.mem_filter.mpr ⟨(hmemS _).mpr ?_, Set.nonempty_iff_ne_empty.mp h'⟩
      change (p.1 * _).1 _ = κ
      rw [coe_mul_simple_apply, hwt, reflection_reflection]
      exact (hmemS p).mp (Finset.mem_filter.mp hp).1
    · obtain ⟨h', -, -, hback⟩ := reflectPair_spec hA hΛ hν p (hne p hp)
      exact hback
  rw [hzero, add_zero, finsum_eq_sum_of_support_subset _ (s := S) fun p hp ↦ ?_,
    Finset.sum_filter]
  · refine Finset.sum_congr rfl fun p hp ↦ ?_
    by_cases hd : p.2.1.hitSet (shiftLevel hA hν) = ∅
    · rw [ite_eq_left hd, ite_eq_left (And.intro hd ((hmemS p).mp hp))]
    · rw [ite_eq_right hd, ite_eq_right fun h : _ ∧ _ ↦ hd h.1]
  · rw [Function.mem_support] at hp
    exact (hmemS p).mpr (by by_contra h; exact hp (ite_eq_right fun h' : _ ∧ _ ↦ h h'.2))

/-- **Littelmann's path-model Weyl character formula** ([Lit95] Thm. 9.1 (check), in the form of
the Weyl character formula): for any generalized Cartan matrix and dominant integral `λ`,
`(∑_{w ∈ W} (-1)^{ℓ(w)} e^{wρ}) · ch B(λ) = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(λ + ρ)}` in `ℰ`. This is
the case `ν = 0` of `Matrix.Realization.coeffAt_weylAltSum_mul_pathCharacter`: `π_λ` is the only
dominant path of `B(λ)`. -/
theorem weylAltSum_rho_mul_pathCharacter :
    weylAltSum P hA (IrreducibleModule.isDominantIntegral_rho (P := P)) * pathCharacter hA hΛ =
      weylAltSum P hA (IrreducibleModule.isDominantIntegral_add_rho hΛ) := by
  set πΛ := straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩ with hπΛ
  have h0 := IrreducibleModule.isDominantIntegral_zero (P := P)
  have hdom : ∀ b : πΛ.component, b.1.hitSet (shiftLevel hA h0) = ∅ ↔ b.1 = πΛ := by
    intro b
    have hl : shiftLevel hA h0 = fun _ ↦ -1 := funext (shiftLevel_zero hA)
    rw [hl]
    constructor
    · intro h
      by_contra hne
      exact (Set.nonempty_iff_ne_empty.mp (hitSet_nonempty_of_ne hA hΛ b hne)) h
    · intro h
      rw [h]
      exact hitSet_straightLine hA hΛ
  have hreg : ∀ i, ∃ n : ℕ, (Λ + P.rho) (P.coroot i) = n + 1 := fun i ↦ by
    obtain ⟨n, hn⟩ := hΛ i
    exact ⟨n, by rw [LinearMap.add_apply, hn, rho_coroot]⟩
  have hinj' := P.apply_injective_of_regular hA hreg
  have hcongr : ∀ (μ₀ μ₁ : Dual K H) (_ : μ₀ = μ₁) (h₀ : ∀ i, ∃ n : ℕ, μ₀ (P.coroot i) = n)
      (h₁ : ∀ i, ∃ n : ℕ, μ₁ (P.coroot i) = n), weylAltSum P hA h₀ = weylAltSum P hA h₁ := by
    rintro μ₀ μ₁ rfl h₀ h₁
    rfl
  ext κ
  have key := coeffAt_weylAltSum_mul_pathCharacter hA hΛ h0 κ
  rw [← hcongr _ _ (zero_add P.rho).symm (IrreducibleModule.isDominantIntegral_rho (P := P))
    (IrreducibleModule.isDominantIntegral_add_rho h0)] at key
  rw [key]
  simp only [weylAltSum, coeff_ofFun]
  by_cases hex : ∃ w₀ : P.weylGroup hA, w₀.1 (Λ + P.rho) = κ
  · obtain ⟨w₀, hw₀⟩ := hex
    rw [finsum_eq_single _ w₀ fun w hw ↦
        ite_eq_right fun (h : w.1 (Λ + P.rho) = κ) ↦ hw (hinj' (h.trans hw₀.symm)),
      ite_eq_left hw₀, finsum_eq_single _ (w₀, ⟨πΛ, πΛ.mem_component_self⟩) ?_]
    · refine ite_eq_left ⟨(hdom _).mpr rfl, ?_⟩
      change w₀.1 (Λ + (0 + P.rho)) = κ
      rw [zero_add]
      exact hw₀
    · rintro ⟨w, b⟩ hne
      refine ite_eq_right fun ⟨h1, h2⟩ ↦ hne ?_
      obtain rfl : b = ⟨πΛ, πΛ.mem_component_self⟩ := Subtype.ext ((hdom b).mp h1)
      change w.1 (Λ + (0 + P.rho)) = κ at h2
      rw [zero_add] at h2
      rw [show w = w₀ from hinj' (h2.trans hw₀.symm)]
  · push Not at hex
    rw [finsum_eq_zero_of_forall_eq_zero fun w : P.weylGroup hA ↦ ite_eq_right (hex w)]
    refine finsum_eq_zero_of_forall_eq_zero fun p ↦ ite_eq_right fun ⟨h1, h2⟩ ↦ hex p.1 ?_
    have hb := (hdom p.2).mp h1
    change p.1.1 ((p.2.1.wt : Dual K H) + (0 + P.rho)) = κ at h2
    rw [hb, zero_add] at h2
    exact h2

/-- **Littelmann's character formula** ([Lit95] Thm. 9.1 (check), [Lit94]): for a symmetrizable
generalized Cartan matrix and a dominant integral weight `λ`, the character of the path crystal
`B(λ)` is the character of the irreducible highest-weight module `L(λ)`:
`∑_{π ∈ B(λ)} e^{π(1)} = ch L(λ)`. By `Matrix.Realization.weylAltSum_rho_mul_pathCharacter`,
the denominator identity and the Weyl–Kac character formula, both sides have the same product
with the unit `e^ρ R` of `ℰ`. -/
theorem pathCharacter_eq_character [FiniteDimensional K H] (hS : A.IsSymmetrizable) :
    pathCharacter hA hΛ = (IrreducibleModule.isCategoryO P Λ).character := by
  have h1 := IrreducibleModule.exp_rho_mul_denominator_mul_character hA hS hΛ
  have h2 := IrreducibleModule.exp_rho_mul_denominator (P := P) hA hS
  have h3 := weylAltSum_rho_mul_pathCharacter hA hΛ
  have hR : IsUnit (denominator P) := by
    have := VermaModule.denominator_mul_character P 0
    rw [exp_zero] at this
    exact IsUnit.of_mul_eq_one _ this
  have hρ : IsUnit (exp P ℤ P.rho) :=
    IsUnit.of_mul_eq_one (exp P ℤ (-P.rho)) (by rw [← exp_add, add_neg_cancel, exp_zero])
  apply (hρ.mul hR).mul_left_cancel
  rw [h1, ← h3, h2]

end Formula

end Matrix.Realization
