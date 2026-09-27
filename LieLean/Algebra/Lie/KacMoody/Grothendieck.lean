/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CompositionSeries.Multiplicity
import Mathlib.RingTheory.HahnSeries.Summable

/-!
# Characters and multiplicities in the category `𝒪`

Let `V` be a module in the category `𝒪` over the Kac–Moody algebra `𝔤(A)`, with multiplicities
`[V : L(μ)]` (`IsCategoryO.multiplicity`, defined through local composition series). We prove
the identity

  `ch V = ∑_μ [V : L(μ)] ch L(μ)`

in the algebra `ℰ` of formal characters, where the right-hand side is a summable (in general
infinite) family, and that the characters `ch L(μ)` are linearly independent in the strong sense
that `c ↦ ∑_μ c_μ ch L(μ)` is injective on `ℰ` (the family is unitriangular for the dominance
order).

## The Grothendieck group of `𝒪`

Modules in `𝒪` need not have finite length, so the natural home of the classes `[V]` is a
completion of the Grothendieck group: we record `[V]` as the element
`IsCategoryO.multiplicities hV = ∑_μ [V : L(μ)] e^μ` of `ℰ` (the multiplicities are supported
in finitely many cones `λ - Q₊`), so that `[L(μ)] = e^μ` and the (completed) Grothendieck group
of `𝒪` is identified with a subgroup of `ℰ` (as an abelian group). With this formulation:

* `V ↦ [V]` is additive on short exact sequences (`IsCategoryO.multiplicity_eq_add`);
* the character is `ch V = χ([V])` for the injective additive map
  `χ = sumIrreducibleCharacter : ℰ → ℰ`, `c ↦ ∑_μ c_μ ch L(μ)`
  (`IsCategoryO.character_eq_sumIrreducibleCharacter`, `sumIrreducibleCharacter_injective`);
* hence `V ↦ ch V` identifies the Grothendieck group with the additive subgroup of `ℰ`
  spanned by characters, and `ch V = ch W ↔ [V] = [W]` (`IsCategoryO.character_eq_iff`).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.sumIrreducibleCharacter`: the additive map
  `ℰ → ℰ`, `c ↦ ∑_μ c_μ ch L(μ)`.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.multiplicities`: the class
  `[V] = ∑_μ [V : L(μ)] e^μ ∈ ℰ`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.finrank_weightSpace_eq_finsum`:
  `dim V_ξ = ∑_μ [V : L(μ)] dim L(μ)_ξ`.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.character_eq_sumIrreducibleCharacter`:
  `ch V = ∑_μ [V : L(μ)] ch L(μ)` ([Kac] §9.6 (check); [HumO] §1.14–1.15 (check)).
* `Matrix.Realization.KacMoodyAlgebra.sumIrreducibleCharacter_injective`: the `ch L(μ)` are
  linearly independent (also for infinite combinations).
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.character_eq_iff`,
  `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.multiplicity_eq_add`.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.multiplicity_le_finrank`:
  `[V : L(μ)] ≤ dim V_μ`.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.multiplicity_eq`:
  `[L(λ) : L(μ)] = δ_{λμ}`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.multiplicity_self`: `[M(λ) : L(λ)] = 1`, and
  `VermaModule.mem_cone_of_multiplicity_ne_zero`: `[M(λ) : L(μ)] ≠ 0 → μ ≤ λ`.

## Proof

By a local composition series for `ξ` (`IsLocalCompositionSeries.finrank_weightSpace_eq`),
`dim V_ξ = ∑_{j ∈ J} dim L(λ_j)_ξ`, and only the `λ_j ≥ ξ` contribute; for those, the number of
`j` with `λ_j = μ` is `[V : L(μ)]` (`IsCategoryO.count_factorWeights_eq_multiplicity`). This gives
the character identity coefficientwise. For injectivity, if `c ≠ 0`, let `μ₀` be maximal (for
the dominance order) in the support of `c` (it exists since the support is partially
well-ordered); then the coefficient of `e^{μ₀}` in `∑_μ c_μ ch L(μ)` is `c_{μ₀}`, since
`dim L(μ₀)_{μ₀} = 1` and `L(μ)_{μ₀} = 0` unless `μ ≥ μ₀`. The arguments are standard and were
written out by us.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.6–9.7.
* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, §1.2–1.3, §1.14–1.15 (check).
-/

open Module LieModule HahnSeries

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

open CharacterRing WeightOrd

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  {W : Type*} [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]

/-! ### Intervals for the dominance order -/

omit [DecidableEq ι] in
variable (P) in
/-- The interval `{μ | ξ ≤ μ ≤ Λ}` for the dominance order is finite. -/
theorem finite_setOf_mem_cone_and_mem_cone (Λ ξ : Dual K H) :
    {μ | μ ∈ cone P Λ ∧ ξ ∈ cone P μ}.Finite := by
  by_cases h : ∃ c : ι → ℤ, P.rootOf c = Λ - ξ
  · obtain ⟨c, hc⟩ := h
    refine ((Set.Finite.pi (t := fun i ↦ Set.Icc 0 (c i)) fun i ↦ Set.finite_Icc _ _).image
      fun k ↦ Λ - P.rootOf k).subset ?_
    rintro μ ⟨⟨k, hk, rfl⟩, ⟨l, hl, hξ⟩⟩
    have hkl : k + l = c := P.rootOf_injective (by rw [map_add, hc, hξ]; abel)
    refine ⟨k, fun i _ ↦ ⟨hk i, ?_⟩, rfl⟩
    rw [← hkl, Pi.add_apply]
    exact le_add_of_nonneg_right (hl i)
  · refine Set.finite_empty.subset ?_
    rintro μ ⟨⟨k, hk, rfl⟩, ⟨l, hl, hξ⟩⟩
    exact h ⟨k + l, by rw [map_add, hξ]; abel⟩

/-! ### The map `c ↦ ∑_μ c_μ ch L(μ)` -/

variable (P) in
/-- The summable family `μ ↦ c_μ ch L(μ)` in `ℰ`, for `c ∈ ℰ`. -/
def irreducibleCharacterFamily (c : P.CharacterRing ℤ) :
    SummableFamily P.WeightOrd ℤ (Dual K H) where
  toFun μ := c.coeffAt μ • (IrreducibleModule.isCategoryO P μ).character
  isPWO_iUnion_support' := by
    obtain ⟨t, ht⟩ := c.exists_finset
    refine (isPWO_iff P).mpr ⟨t, fun ν hν ↦ ?_⟩
    obtain ⟨μ, hμ⟩ := Set.mem_iUnion.mp hν
    rw [HahnSeries.mem_support, HahnSeries.coeff_smul, smul_eq_mul] at hμ
    obtain ⟨Λ, hΛ, k, hk, hμΛ⟩ := ht μ (left_ne_zero_of_mul hμ)
    have h2 : (IrreducibleModule.isCategoryO P μ).character.coeffAt (ofWeightOrd P ν) ≠ 0 :=
      right_ne_zero_of_mul hμ
    rw [IsCategoryO.coeffAt_character, Nat.cast_ne_zero] at h2
    obtain ⟨l, hl, hνμ⟩ := IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero h2
    exact ⟨Λ, hΛ, k + l, add_nonneg hk hl, by rw [hνμ, hμΛ, map_add]; abel⟩
  finite_co_support' g := by
    obtain ⟨t, ht⟩ := c.exists_finset
    refine (t.finite_toSet.biUnion fun Λ _ ↦
      finite_setOf_mem_cone_and_mem_cone P Λ (ofWeightOrd P g)).subset fun μ hμ ↦ ?_
    rw [Set.mem_ofPred_eq, HahnSeries.coeff_smul, smul_eq_mul] at hμ
    obtain ⟨Λ, hΛ, hμΛ⟩ := ht μ (left_ne_zero_of_mul hμ)
    have h2 : (IrreducibleModule.isCategoryO P μ).character.coeffAt (ofWeightOrd P g) ≠ 0 :=
      right_ne_zero_of_mul hμ
    rw [IsCategoryO.coeffAt_character, Nat.cast_ne_zero] at h2
    exact Set.mem_biUnion (x := Λ) hΛ
      ⟨hμΛ, IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero h2⟩

variable (P) in
/-- The additive map `ℰ → ℰ`, `c ↦ ∑_μ c_μ ch L(μ)`. Its injectivity
(`sumIrreducibleCharacter_injective`) expresses the linear independence of the characters
`ch L(μ)`, and `ch V = sumIrreducibleCharacter [V]` for `V` in `𝒪`
(`IsCategoryO.character_eq_sumIrreducibleCharacter`). -/
def sumIrreducibleCharacter : P.CharacterRing ℤ →+ P.CharacterRing ℤ where
  toFun c := (irreducibleCharacterFamily P c).hsum
  map_zero' := by
    ext μ
    simp [coeffAt, SummableFamily.coeff_hsum, irreducibleCharacterFamily]
  map_add' c d := by
    rw [← SummableFamily.hsum_add]
    congr 1
    ext μ : 1
    simp only [SummableFamily.add_apply, irreducibleCharacterFamily, SummableFamily.coe_mk,
      coeffAt, HahnSeries.coeff_add, add_smul]

/-- The coefficients of `∑_μ c_μ ch L(μ)`: `(∑_μ c_μ ch L(μ))_ξ = ∑_μ c_μ dim L(μ)_ξ`. -/
theorem coeffAt_sumIrreducibleCharacter (c : P.CharacterRing ℤ) (ξ : Dual K H) :
    (sumIrreducibleCharacter P c).coeffAt ξ =
      ∑ᶠ μ, c.coeffAt μ * finrank K (weightSpace P (IrreducibleModule P μ) ξ) := by
  simp only [sumIrreducibleCharacter, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeffAt,
    SummableFamily.coeff_hsum]
  rfl

/-- `ch L(μ) = ∑_ν δ_{μν} ch L(ν)`. -/
theorem sumIrreducibleCharacter_exp (μ : Dual K H) :
    sumIrreducibleCharacter P (exp P ℤ μ) = (IrreducibleModule.isCategoryO P μ).character := by
  classical
  ext ξ
  rw [coeffAt_sumIrreducibleCharacter, finsum_eq_single _ μ fun ν hν ↦ by
    simp [coeff_exp, hν], coeff_exp_self, one_mul, IsCategoryO.coeffAt_character]

/-- **Linear independence of the irreducible characters** (unitriangularity): if
`∑_μ c_μ ch L(μ) = 0` in `ℰ`, then `c = 0`. -/
theorem sumIrreducibleCharacter_injective :
    Function.Injective (sumIrreducibleCharacter P) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra hc0
  have hne : c.support.Nonempty := HahnSeries.support_nonempty_iff.mpr hc0
  obtain ⟨μ₀', -, hmin⟩ := c.isPWO_support.exists_le_minimal hne.some_mem
  set μ₀ := ofWeightOrd P μ₀' with hμ₀
  have h0 := congrArg (fun d ↦ d.coeffAt μ₀) hc
  simp only [coeffAt_sumIrreducibleCharacter, HahnSeries.coeff_zero] at h0
  rw [finsum_eq_single _ μ₀ fun μ hμ ↦ ?_] at h0
  · rw [IrreducibleModule.finrank_weightSpace_self, Nat.cast_one, mul_one] at h0
    exact hmin.1 h0
  · by_contra hne0
    have h1 := left_ne_zero_of_mul hne0
    have h2 := IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero
      (by exact_mod_cast right_ne_zero_of_mul hne0)
    have hle : toWeightOrd P μ ≤ μ₀' :=
      (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr h2
    exact hμ (congrArg (ofWeightOrd P) (le_antisymm hle (hmin.2 h1 hle)))

/-! ### The character identity -/

namespace IsCategoryO

variable (hV : IsCategoryO P V)
include hV

/-- For a local composition series `l` for `ξ`, the number of factors `L(μ)` with `L(μ)_ξ ≠ 0`
is `[V : L(μ)]`. -/
lemma count_mul_finrank_eq [DecidableEq (Dual K H)] {ξ : Dual K H}
    {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P ξ ⊥ l ⊤) (μ : Dual K H) :
    (factorWeights l).count μ * finrank K (weightSpace P (IrreducibleModule P μ) ξ) =
      hV.multiplicity μ * finrank K (weightSpace P (IrreducibleModule P μ) ξ) := by
  by_cases h : finrank K (weightSpace P (IrreducibleModule P μ) ξ) = 0
  · rw [h, mul_zero, mul_zero]
  · rw [hV.count_factorWeights_eq_multiplicity
      (IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero h) hl]

/-- The function `μ ↦ [V : L(μ)] dim L(μ)_ξ` has finite support. -/
lemma finite_support_multiplicity_mul (ξ : Dual K H) :
    (Function.support fun μ ↦
      hV.multiplicity μ * finrank K (weightSpace P (IrreducibleModule P μ) ξ)).Finite := by
  classical
  obtain ⟨l, hl⟩ := hV.exists_isLocalCompositionSeries ξ
  refine (factorWeights l).toFinset.finite_toSet.subset fun μ hμ ↦ ?_
  rw [Function.mem_support, ← hV.count_mul_finrank_eq hl] at hμ
  exact List.mem_toFinset.mpr (List.count_pos_iff.mp (Nat.pos_of_ne_zero
    (left_ne_zero_of_mul hμ)))

/-- **Weight multiplicities from composition multiplicities** ([Kac] §9.6 (check)):
`dim V_ξ = ∑_μ [V : L(μ)] dim L(μ)_ξ` for a module `V` in `𝒪`. -/
theorem finrank_weightSpace_eq_finsum (ξ : Dual K H) :
    finrank K (weightSpace P V ξ) =
      ∑ᶠ μ, hV.multiplicity μ * finrank K (weightSpace P (IrreducibleModule P μ) ξ) := by
  classical
  obtain ⟨l, hl⟩ := hV.exists_isLocalCompositionSeries ξ
  rw [hl.finrank_weightSpace_eq hV (mem_cone_self ξ), Finset.sum_list_map_count,
    finsum_eq_sum_of_support_subset _ (s := (factorWeights l).toFinset) fun μ hμ ↦ ?_]
  · refine Finset.sum_congr rfl fun μ _ ↦ ?_
    rw [smul_eq_mul, hV.count_mul_finrank_eq hl]
  · rw [Function.mem_support, ← hV.count_mul_finrank_eq hl] at hμ
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (Nat.pos_of_ne_zero
      (left_ne_zero_of_mul hμ)))

/-- `[V : L(μ)] ≤ dim V_μ`. -/
theorem multiplicity_le_finrank (μ : Dual K H) :
    hV.multiplicity μ ≤ finrank K (weightSpace P V μ) := by
  rw [hV.finrank_weightSpace_eq_finsum μ]
  refine le_trans ?_ (single_le_finsum μ (hV.finite_support_multiplicity_mul μ)
    fun _ ↦ Nat.zero_le _)
  rw [IrreducibleModule.finrank_weightSpace_self, mul_one]

/-- If `[V : L(μ)] ≠ 0`, then `μ` is a weight of `V`. -/
theorem weightSpace_ne_bot_of_multiplicity_ne_zero {μ : Dual K H}
    (hμ : hV.multiplicity μ ≠ 0) : weightSpace P V μ ≠ ⊥ := fun h ↦ by
  have := hV.multiplicity_le_finrank μ
  rw [h, finrank_bot] at this
  omega

/-- The class `[V] = ∑_μ [V : L(μ)] e^μ ∈ ℰ` of a module `V` in `𝒪` in the (completed)
Grothendieck group of `𝒪`, realized in `ℰ` (see the module docstring). The multiplicities are
supported in the finitely many cones containing the weights of `V`. -/
def multiplicities : P.CharacterRing ℤ :=
  ofFun P (fun μ ↦ (hV.multiplicity μ : ℤ)) (by
    obtain ⟨s, hs⟩ := hV.exists_finset
    exact ⟨s, fun μ hμ ↦ hs μ (hV.weightSpace_ne_bot_of_multiplicity_ne_zero
      (by exact_mod_cast hμ))⟩)

@[simp] lemma coeffAt_multiplicities (μ : Dual K H) :
    hV.multiplicities.coeffAt μ = hV.multiplicity μ := rfl

/-- **The character of a module in `𝒪` in terms of irreducible characters** ([Kac] §9.6
(check); [HumO] §1.15 (check)): `ch V = ∑_μ [V : L(μ)] ch L(μ)` in `ℰ`, the sum being a
summable family (`irreducibleCharacterFamily`). -/
theorem character_eq_sumIrreducibleCharacter :
    hV.character = sumIrreducibleCharacter P hV.multiplicities := by
  ext ξ
  rw [coeffAt_sumIrreducibleCharacter, coeffAt_character, finrank_weightSpace_eq_finsum hV ξ]
  have := (Nat.castAddMonoidHom ℤ).map_finsum (hV.finite_support_multiplicity_mul ξ)
  simp only [Nat.coe_castAddMonoidHom, Nat.cast_mul] at this
  rw [this]
  rfl

omit hV in
/-- **The character determines the multiplicities**: two modules in `𝒪` have the same character
iff they have the same multiplicities `[V : L(μ)]`. -/
theorem character_eq_iff (hV : IsCategoryO P V) (hW : IsCategoryO P W) :
    hV.character = hW.character ↔ ∀ μ, hV.multiplicity μ = hW.multiplicity μ := by
  rw [character_eq_sumIrreducibleCharacter, character_eq_sumIrreducibleCharacter,
    sumIrreducibleCharacter_injective.eq_iff]
  refine ⟨fun h μ ↦ ?_, fun h ↦ CharacterRing.ext fun μ ↦ ?_⟩
  · have := congrArg (fun c ↦ c.coeffAt μ) h
    simp only [coeffAt_multiplicities, Nat.cast_inj] at this
    exact this
  · simp [h μ]

/-- **Multiplicities are additive** on short exact sequences: `[V : L(μ)] = [N : L(μ)] +
[V/N : L(μ)]` for a submodule `N` of a module `V` in `𝒪`. Thus `V ↦ [V]` factors through the
Grothendieck group of `𝒪`. -/
theorem multiplicity_eq_add (N : LieSubmodule K P.KacMoodyAlgebra V) (μ : Dual K H) :
    hV.multiplicity μ =
      (hV.lieSubmodule N).multiplicity μ + (hV.quotient N).multiplicity μ := by
  have h := hV.character_eq_add N (hV.lieSubmodule N) (hV.quotient N)
  rw [character_eq_sumIrreducibleCharacter, character_eq_sumIrreducibleCharacter,
    character_eq_sumIrreducibleCharacter, ← map_add] at h
  have := congrArg (fun c ↦ c.coeffAt μ) (sumIrreducibleCharacter_injective h)
  simp only [coeffAt_multiplicities, coeffAt, HahnSeries.coeff_add] at this
  exact_mod_cast this

end IsCategoryO

/-! ### Multiplicities in irreducible modules -/

namespace IrreducibleModule

/-- The class of `L(λ)` in the (completed) Grothendieck group is `[L(λ)] = e^λ`. -/
theorem multiplicities_eq (Λ : Dual K H) : (isCategoryO P Λ).multiplicities = exp P ℤ Λ :=
  sumIrreducibleCharacter_injective (by
    rw [← IsCategoryO.character_eq_sumIrreducibleCharacter, sumIrreducibleCharacter_exp])

open Classical in
/-- `[L(λ) : L(μ)] = δ_{λμ}`. -/
theorem multiplicity_eq (Λ μ : Dual K H) :
    (isCategoryO P Λ).multiplicity μ = if μ = Λ then 1 else 0 := by
  have := congrArg (fun c ↦ c.coeffAt μ) (multiplicities_eq (P := P) Λ)
  simp only [IsCategoryO.coeffAt_multiplicities, coeff_exp] at this
  split_ifs at this ⊢ <;> exact_mod_cast this

end IrreducibleModule

/-! ### Multiplicities in Verma modules -/

namespace VermaModule

/-- `[M(λ) : L(μ)] ≠ 0` implies `μ ≤ λ` ([Kac] §9.2 (check); [HumO] §1.3 (check)). -/
theorem mem_cone_of_multiplicity_ne_zero {Λ μ : Dual K H}
    (h : (isCategoryO P Λ).multiplicity μ ≠ 0) : μ ∈ cone P Λ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((isCategoryO P Λ).weightSpace_ne_bot_of_multiplicity_ne_zero h)
  exact exists_eq_sub_of_mem_weightSpace P Λ LieModuleHom.id Function.surjective_id hx hx0

/-- `[M(λ) : L(λ)] = 1` ([Kac] §9.2–9.3 (check); [HumO] §1.3 (check)). -/
theorem multiplicity_self (Λ : Dual K H) : (isCategoryO P Λ).multiplicity Λ = 1 := by
  have h := (isCategoryO P Λ).finrank_weightSpace_eq_finsum Λ
  rw [finrank_weightSpace_self, finsum_eq_single _ Λ fun μ hμ ↦ ?_,
    IrreducibleModule.finrank_weightSpace_self, mul_one] at h
  · exact h.symm
  · by_contra hne
    have h1 := mem_cone_of_multiplicity_ne_zero (left_ne_zero_of_mul hne)
    have h2 := IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero
      (right_ne_zero_of_mul hne)
    refine hμ (congrArg (ofWeightOrd P) (le_antisymm (a := toWeightOrd P μ)
      ((toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr h2)
      ((toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr h1)))

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
