/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationFacetClosureNonintegral
import LieLean.Algebra.Lie.KacMoody.TranslationUpperClosureNonintegral

/-!
# Translation to and back from a facet closure

Let `A` be of finite type, `λ`, `μ` antidominant with every positive root orthogonal to `λ + ρ`
orthogonal to `μ + ρ` (`μ♮` lies in the closure of the facet of `λ♮`), `ν` dominant integral in
`W (λ - μ)` and `ν'` dominant integral in `W (μ - λ)`. With `T_μ^λ = pr_{χ_λ}(pr_{χ_μ}(−) ⊗ L(ν))`
and `T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν'))`, for every `M` in the block of `μ`:

`ch T_λ^μ T_μ^λ M = |W_μ°/W_λ°| ch M`

(Humphreys, GSM 94, Corollary 7.12), for arbitrary (not necessarily integral) weights.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.multiplicity_centralTranslation_eq_finsetSum`:
  `[T V : L(y)] = ∑_η [V : L(η)] [T L(η) : L(y)]` (exactness of translation on multiplicities).
* `Matrix.Realization.KacMoodyAlgebra.multiplicity_centralTranslation_of_equiv_eq_sum`:
  the same for a composite of two translations.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.centralCharacter_eq_of_multiplicity_ne_zero`:
  the composition factors of a module in one central block lie in that block.
* `Matrix.Realization.KacMoodyAlgebra.multiplicity_translation_translation_irreducible`:
  `[T_λ^μ T_μ^λ L(x·μ) : L(y)] = |W_μ°/W_λ°| δ_{x·μ, y}`.
* `Matrix.Realization.KacMoodyAlgebra.character_translation_translation`: Corollary 7.12.
* `Matrix.Realization.KacMoodyAlgebra.multiplicity_translation_translation_verma`: the Verma case.

## Proof

As in Humphreys, the Verma case follows from Theorem 7.12 and Theorem 7.6:
`T_μ^λ M(x·μ)` has the character of `⊕_{w'} M((x w')·λ)` and `T_λ^μ M((x w')·λ) ≅ M(x·μ)`.
Humphreys then expands `ch M` in Verma characters; here the multiplicity formula reduces the
general case to simple modules, and the simple case follows from the Verma case by induction
over the (finite, unitriangular) linkage class `W·μ`.

The composite `T_λ^μ T_μ^λ V` is stated as `T_λ^μ X` for a module `X` with `X ≅ T_μ^λ V` (take
`X = T_μ^λ V`): iterating the translated module types in a statement makes elaboration and kernel
checking very expensive, while the parametrized statements are cheap to instantiate.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.12.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Generic

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V X Z Z' : Type*}
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]
  [AddCommGroup Z] [Module K Z] [LieRingModule P.KacMoodyAlgebra Z]
  [LieModule K P.KacMoodyAlgebra Z]
  [AddCommGroup Z'] [Module K Z'] [LieRingModule P.KacMoodyAlgebra Z']
  [LieModule K P.KacMoodyAlgebra Z']

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

omit [DecidableEq ι] [CharZero K] in
variable {P} in
lemma sub_sub_mem_cone {y ν ν' η ξ : Dual K H} (h₁ : y - ν' ∈ cone P η) (h₂ : η - ν ∈ cone P ξ) :
    y - ν - ν' ∈ cone P ξ := by
  obtain ⟨k, hk, hke⟩ := h₁
  obtain ⟨k', hk', hke'⟩ := h₂
  refine ⟨k + k', add_nonneg hk hk', ?_⟩
  rw [map_add]
  have : y - ν - ν' = (y - ν') - ν := by abel
  rw [this, hke, sub_sub, add_comm (P.rootOf k), ← sub_sub, hke', sub_sub, add_comm]

/-- If the character of `X` is the sum of the characters of Verma modules `M(y)`, `y ∈ T`, then
`[X : L(η)] = ∑_{y ∈ T} [M(y) : L(η)]`. -/
theorem IsCategoryO.multiplicity_eq_sum_of_character_eq_sum (hX : IsCategoryO P X)
    (T : Finset (Dual K H))
    (h : hX.character = ∑ y ∈ T, (VermaModule.isCategoryO P y).character) (η : Dual K H) :
    hX.multiplicity η = ∑ y ∈ T, (VermaModule.isCategoryO P y).multiplicity η := by
  simp_rw [IsCategoryO.character_eq_sumIrreducibleCharacter, ← map_sum] at h
  have h1 := congrArg (fun c ↦ c.coeffAt η) (sumIrreducibleCharacter_injective h)
  simp only [IsCategoryO.coeffAt_multiplicities] at h1
  rw [CharacterRing.coeffAt, HahnSeries.coeff_sum] at h1
  simp only [← CharacterRing.coeffAt.eq_1, IsCategoryO.coeffAt_multiplicities] at h1
  exact_mod_cast h1

/-- If `[X : L(y)] = n [V : L(y)]` for all `y`, then `ch X = n ch V`. -/
theorem IsCategoryO.character_eq_nsmul_of_multiplicity_eq (hX : IsCategoryO P X)
    (hV : IsCategoryO P V) (n : ℕ) (h : ∀ y, hX.multiplicity y = n * hV.multiplicity y) :
    hX.character = n • hV.character := by
  rw [IsCategoryO.character_eq_sumIrreducibleCharacter,
    IsCategoryO.character_eq_sumIrreducibleCharacter, ← map_nsmul]
  congr 1
  ext y
  simp only [IsCategoryO.coeffAt_multiplicities, CharacterRing.coeffAt, HahnSeries.coeff_nsmul,
    Pi.smul_apply]
  rw [h, nsmul_eq_mul, Nat.cast_mul]

variable [IsAlgClosed K]

/-- **Translation on multiplicities.** For `V`, `Z` in `𝒪` with the weights of `Z` `≤ ν`,
`[T V : L(y)] = ∑_{η ∈ s} [V : L(η)] [T L(η) : L(y)]`, `T = pr_{χ₂}(pr_{χ₁}(−) ⊗ Z)`, for any
finite set `s` containing the `η ≥ y - ν` with `[V : L(η)] ≠ 0`. -/
theorem multiplicity_centralTranslation_eq_finsetSum (hV : IsCategoryO P V)
    (hZ : IsCategoryO P Z) (χ₁ χ₂ : 𝓩 →ₐ[K] K) {ν y : Dual K H}
    (hZν : ∀ ν', weightSpace P Z ν' ≠ ⊥ → ν' ∈ cone P ν) (s : Finset (Dual K H))
    (hs : ∀ η, y - ν ∈ cone P η → hV.multiplicity η ≠ 0 → η ∈ s) :
    (hV.centralTranslation P hZ χ₁ χ₂).multiplicity y =
      ∑ η ∈ s, hV.multiplicity η *
        ((IrreducibleModule.isCategoryO P η).centralTranslation P hZ χ₁ χ₂).multiplicity y := by
  classical
  obtain ⟨l, hl⟩ := hV.exists_isLocalCompositionSeries (y - ν)
  rw [multiplicity_centralTranslation_eq_sum P hV hZ χ₁ χ₂ hZν hl, Finset.sum_list_map_count]
  symm
  refine Finset.sum_subset (fun η hη ↦ ?_) (fun η _ hηl ↦ ?_) |>.symm.trans
    (Finset.sum_congr rfl fun η hη ↦ ?_)
  · have hη' := List.mem_toFinset.mp hη
    have hc := hl.mem_cone_of_mem_factorWeights hη'
    exact hs η hc ((hV.multiplicity_ne_zero_iff hc hl).mpr hη')
  · by_cases hc : y - ν ∈ cone P η
    · have : hV.multiplicity η = 0 := by
        by_contra h
        exact hηl (List.mem_toFinset.mpr ((hV.multiplicity_ne_zero_iff hc hl).mp h))
      rw [this, zero_mul]
    · rw [IsCategoryO.multiplicity_eq_zero_of_weightSpace_eq_bot
        ((IrreducibleModule.isCategoryO P η).centralTranslation P hZ χ₁ χ₂) ?_, mul_zero]
      refine weightSpace_centralTranslation_eq_bot P (IrreducibleModule.isCategoryO P η) hZ χ₁ χ₂
        hZν fun μ hμ ↦ weightSpace_lieSubmodule_eq_bot _ ?_
      by_contra hne
      exact hc (mem_cone_trans hμ (IrreducibleModule.mem_cone_of_weightSpace_ne_bot hne))
  · have hc := hl.mem_cone_of_mem_factorWeights (List.mem_toFinset.mp hη)
    rw [smul_eq_mul, hV.count_factorWeights_eq_multiplicity hc hl]

omit [IsAlgClosed K] in
/-- The weights `η` with `[T L(ξ) : L(η)] ≠ 0` satisfy `η ≤ ξ + ν`. -/
theorem mem_cone_of_multiplicity_centralTranslation_ne_zero (hZ : IsCategoryO P Z)
    (χ₁ χ₂ : 𝓩 →ₐ[K] K) {ν ξ η : Dual K H}
    (hZν : ∀ ν', weightSpace P Z ν' ≠ ⊥ → ν' ∈ cone P ν)
    (h : ((IrreducibleModule.isCategoryO P ξ).centralTranslation P hZ χ₁ χ₂).multiplicity η ≠ 0) :
    η - ν ∈ cone P ξ := by
  by_contra hc
  refine h (IsCategoryO.multiplicity_eq_zero_of_weightSpace_eq_bot _ ?_)
  refine weightSpace_centralTranslation_eq_bot P (IrreducibleModule.isCategoryO P ξ) hZ χ₁ χ₂
    hZν fun μ hμ ↦ weightSpace_lieSubmodule_eq_bot _ ?_
  by_contra hne
  exact hc (mem_cone_trans hμ (IrreducibleModule.mem_cone_of_weightSpace_ne_bot hne))

/-- **A composite of translations on multiplicities.** Let `T = pr_{χ₂}(pr_{χ₁}(−) ⊗ Z)` and
`T' = pr_{χ₃}(pr_{χ₂}(−) ⊗ Z')`, the weights of `Z`, `Z'` being `≤ ν`, `≤ ν'`, and `X ≅ T V`. Then
`[T' X : L(y)] = ∑_{ξ ∈ s} [V : L(ξ)] ∑_η [T L(ξ) : L(η)] [T' L(η) : L(y)]` for any finite set `s`
containing the `ξ ≥ y - ν - ν'` with `[V : L(ξ)] ≠ 0`. (The module `X` is a parameter so that
the statement does not iterate the translated types.) -/
theorem multiplicity_centralTranslation_of_equiv_eq_sum (hV : IsCategoryO P V)
    (hX : IsCategoryO P X) (hZ : IsCategoryO P Z) (hZ' : IsCategoryO P Z')
    (χ₁ χ₂ χ₃ : 𝓩 →ₐ[K] K) (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P Z χ₁ χ₂ V) {ν ν' y : Dual K H}
    (hZν : ∀ ν'', weightSpace P Z ν'' ≠ ⊥ → ν'' ∈ cone P ν)
    (hZν' : ∀ ν'', weightSpace P Z' ν'' ≠ ⊥ → ν'' ∈ cone P ν') (s : Finset (Dual K H))
    (hs : ∀ ξ, y - ν - ν' ∈ cone P ξ → hV.multiplicity ξ ≠ 0 → ξ ∈ s) :
    (hX.centralTranslation P hZ' χ₂ χ₃).multiplicity y =
      ∑ ξ ∈ s, hV.multiplicity ξ * ∑ᶠ η,
        ((IrreducibleModule.isCategoryO P ξ).centralTranslation P hZ χ₁ χ₂).multiplicity η *
          ((IrreducibleModule.isCategoryO P η).centralTranslation P hZ' χ₂ χ₃).multiplicity y := by
  let a : Dual K H → Dual K H → ℕ := fun ξ η ↦
    ((IrreducibleModule.isCategoryO P ξ).centralTranslation P hZ χ₁ χ₂).multiplicity η
  let b : Dual K H → ℕ := fun η ↦
    ((IrreducibleModule.isCategoryO P η).centralTranslation P hZ' χ₂ χ₃).multiplicity y
  have hfin := hX.finite_setOf_mem_cone (y - ν')
  have hmemH : ∀ η, y - ν' ∈ cone P η → hX.multiplicity η ≠ 0 → η ∈ hfin.toFinset :=
    fun η hc hη ↦ (Set.Finite.mem_toFinset _).mpr
      ⟨hc, hX.weightSpace_ne_bot_of_multiplicity_ne_zero hη⟩
  have hHs : ∀ η ∈ hfin.toFinset, y - ν' ∈ cone P η := fun η hη ↦
    ((Set.Finite.mem_toFinset _).mp hη).1
  -- `[X : L(η)] = ∑_{ξ ∈ s} [V : L(ξ)] [T L(ξ) : L(η)]` for `η ≥ y - ν'`
  have hXη : ∀ η, y - ν' ∈ cone P η → hX.multiplicity η = ∑ ξ ∈ s, hV.multiplicity ξ * a ξ η :=
    fun η hc ↦ (IsCategoryO.multiplicity_congr hX (hV.centralTranslation P hZ χ₁ χ₂) eX η).trans
      (multiplicity_centralTranslation_eq_finsetSum P hV hZ χ₁ χ₂ hZν s
        fun ξ hξ hm ↦ hs ξ (sub_sub_mem_cone hc hξ) hm)
  have h1 : (hX.centralTranslation P hZ' χ₂ χ₃).multiplicity y =
      ∑ η ∈ hfin.toFinset, hX.multiplicity η * b η :=
    multiplicity_centralTranslation_eq_finsetSum P hX hZ' χ₂ χ₃ hZν' hfin.toFinset hmemH
  have hF : ∀ ξ ∈ s, hV.multiplicity ξ ≠ 0 →
      ∑ᶠ η, a ξ η * b η = ∑ η ∈ hfin.toFinset, a ξ η * b η := by
    intro ξ _ hξ
    refine finsum_eq_sum_of_support_subset _ fun η hη ↦ ?_
    have hne : a ξ η * b η ≠ 0 := Function.mem_support.mp hη
    have ha : a ξ η ≠ 0 := left_ne_zero_of_mul hne
    have hc : y - ν' ∈ cone P η :=
      mem_cone_of_multiplicity_centralTranslation_ne_zero P hZ' χ₂ χ₃ hZν'
        (right_ne_zero_of_mul hne)
    refine Finset.mem_coe.mpr (hmemH η hc fun h0 ↦ ?_)
    have := hXη η hc
    rw [h0] at this
    have hterm := (Finset.sum_eq_zero_iff.mp this.symm) ξ (hs ξ (sub_sub_mem_cone hc
      (mem_cone_of_multiplicity_centralTranslation_ne_zero P hZ χ₁ χ₂ hZν ha)) hξ)
    exact (mul_ne_zero hξ ha) hterm
  calc (hX.centralTranslation P hZ' χ₂ χ₃).multiplicity y
      = ∑ η ∈ hfin.toFinset, hX.multiplicity η * b η := h1
    _ = ∑ η ∈ hfin.toFinset, ∑ ξ ∈ s, hV.multiplicity ξ * a ξ η * b η :=
        Finset.sum_congr rfl fun η hη ↦ by rw [hXη η (hHs η hη), Finset.sum_mul]
    _ = ∑ ξ ∈ s, ∑ η ∈ hfin.toFinset, hV.multiplicity ξ * a ξ η * b η := Finset.sum_comm
    _ = ∑ ξ ∈ s, hV.multiplicity ξ * ∑ᶠ η, a ξ η * b η := Finset.sum_congr rfl fun ξ hξs ↦ by
        by_cases hξ : hV.multiplicity ξ = 0
        · simp only [hξ, zero_mul, Finset.sum_const_zero]
        · rw [hF ξ hξs hξ, Finset.mul_sum]
          exact Finset.sum_congr rfl fun η _ ↦ by ring

omit [IsAlgClosed K] in
/-- Translation of `V` and a module equivalent to it have the same multiplicities. -/
theorem multiplicity_centralTranslation_eq_of_equiv (hV : IsCategoryO P V)
    (hZ : IsCategoryO P Z) (χ₁ χ₂ : 𝓩 →ₐ[K] K) (hX : IsCategoryO P X)
    (e : X ≃ₗ⁅K,𝔤⁆ centralTranslation P Z χ₁ χ₂ V) (y : Dual K H) :
    (hV.centralTranslation P hZ χ₁ χ₂).multiplicity y = hX.multiplicity y :=
  (IsCategoryO.multiplicity_congr hX (hV.centralTranslation P hZ χ₁ χ₂) e y).symm

omit [IsAlgClosed K] in
/-- **The composition factors of a module in one central block lie in that block**: if
`pr_χ V = V` and `[V : L(y)] ≠ 0`, then `χ_y = χ`. -/
theorem IsCategoryO.centralCharacter_eq_of_multiplicity_ne_zero (hV : IsCategoryO P V)
    {χ : 𝓩 →ₐ[K] K} (hχ : KacMoodyAlgebra.centralBlock P V χ = ⊤) {y : Dual K H}
    (h : hV.multiplicity y ≠ 0) : centralCharacter P y = χ := by
  classical
  obtain ⟨l, hl⟩ := hV.exists_isLocalCompositionSeries y
  have hy := (hV.multiplicity_ne_zero_iff (mem_cone_self y) hl).mp h
  obtain ⟨M₁, M₂, -, h12, -, -, ⟨e⟩⟩ := hl.exists_of_mem_factorWeights hy
  by_contra hne
  -- the highest weight vector of `L(y)` lies in the block `χ`
  obtain ⟨q, hq⟩ := LieSubmodule.Quotient.surjective_mk' (M₁.comap M₂.incl)
    (e.symm (IrreducibleModule.hwv P y))
  have hm : (q : V) ∈ KacMoodyAlgebra.centralBlock P V χ := by rw [hχ]; trivial
  have hq' : q ∈ KacMoodyAlgebra.centralBlock P M₂ χ :=
    mem_centralBlock_of_injective P M₂.incl (fun a b h ↦ Subtype.ext h) χ hm
  have h1 := map_mem_centralBlock P (e.toLieModuleHom.comp
    (LieSubmodule.Quotient.mk' (M₁.comap M₂.incl))) χ hq'
  have h2 : (e.toLieModuleHom.comp (LieSubmodule.Quotient.mk' (M₁.comap M₂.incl))) q =
      IrreducibleModule.hwv P y := by
    rw [LieModuleHom.comp_apply, hq]
    exact e.apply_symm_apply _
  rw [h2, centralBlock_irreducible_eq_bot P y χ hne] at h1
  exact IrreducibleModule.hwv_ne_zero P y ((LieSubmodule.mem_bot _).mp h1)

end Generic

section FacetClosure

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- The composition factors of a translated module lie in the target block. -/
theorem centralCharacter_eq_of_multiplicity_centralTranslation_ne_zero {V Z : Type*}
    [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
    [LieModule K P.KacMoodyAlgebra V]
    [AddCommGroup Z] [Module K Z] [LieRingModule P.KacMoodyAlgebra Z]
    [LieModule K P.KacMoodyAlgebra Z] (hV : IsCategoryO P V)
    (hZ : IsCategoryO P Z)
    (χ₁ χ₂ : Subalgebra.center K (UniversalEnvelopingAlgebra K P.KacMoodyAlgebra) →ₐ[K] K)
    {y : Dual K H} (h : (hV.centralTranslation P hZ χ₁ χ₂).multiplicity y ≠ 0) :
    centralCharacter P y = χ₂ :=
  IsCategoryO.centralCharacter_eq_of_multiplicity_ne_zero P _
    (centralBlock_centralBlock_eq_top P _) h

/-- The number `|W_μ°/W_λ°|` of weights `w'·λ` with `w'·μ = μ`. -/
def stabilizerIndex (hA : A.IsGeneralizedCartan) (lam μ : Dual K H) : ℕ :=
  Nat.card {y | ∃ w' : P.weylGroup hA, P.weylDot hA w' μ = μ ∧ y = P.weylDot hA w' lam}

omit [DecidableEq ι] [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] in
/-- The weights `(w w')·λ`, `w'·μ = μ`, are `|W_μ°/W_λ°|` in number. -/
theorem card_eq_stabilizerIndex (hA : A.IsGeneralizedCartan) (lam μ : Dual K H)
    (w : P.weylGroup hA) (T : Finset (Dual K H))
    (hT : (T : Set (Dual K H)) = {y | ∃ w' : P.weylGroup hA,
      P.weylDot hA w' μ = μ ∧ y = P.weylDot hA (w * w') lam}) :
    T.card = stabilizerIndex P hA lam μ := by
  classical
  rw [stabilizerIndex, ← Nat.card_eq_finsetCard, ← Finset.coe_sort_coe, hT]
  refine Nat.card_congr (Equiv.ofBijective (fun y ↦ ⟨P.weylDot hA w⁻¹ y.1, ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨w', hw', hy⟩ := y.2
    refine ⟨w', hw', ?_⟩
    rw [hy]
    simp only [weylDot, sub_add_cancel, Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  · intro a b hab
    have := congrArg (fun y : {y | ∃ w' : P.weylGroup hA, P.weylDot hA w' μ = μ ∧
      y = P.weylDot hA w' lam} ↦ P.weylDot hA w y.1) hab
    simp only [weylDot, sub_add_cancel] at this
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]
      at this
    exact Subtype.ext (by simpa using this)
  · rintro ⟨y, w', hw', rfl⟩
    refine ⟨⟨P.weylDot hA (w * w') lam, w', hw', rfl⟩, Subtype.ext ?_⟩
    simp only [weylDot, sub_add_cancel]
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← mul_assoc, inv_mul_cancel, one_mul]

include hA in
/-- **Translation there and back on Verma modules** (cf. Humphreys, GSM 94, Corollary 7.12): for
`X ≅ T_μ^λ M(x·μ)`, `[T_λ^μ X : L(y)] = |W_μ°/W_λ°| [M(x·μ) : L(y)]`. -/
theorem multiplicity_translation_translation_verma {lam μ ν ν' : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    (hν' : P.IsDominantIntegral ν') {z' : Dual K H ≃ₗ[K] Dual K H}
    (hz' : z' ∈ P.weylGroup hA.isGeneralizedCartan) (hzν' : z' (μ - lam) = ν')
    (x : P.weylGroup hA.isGeneralizedCartan) {X : Type*} [AddCommGroup X] [Module K X]
    [LieRingModule P.KacMoodyAlgebra X] [LieModule K P.KacMoodyAlgebra X] (hX : IsCategoryO P X)
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
      (centralCharacter P lam) (VermaModule P (P.weylDot hA.isGeneralizedCartan x μ)))
    (y : Dual K H) :
    (hX.centralTranslation P (IrreducibleModule.isCategoryO P ν') (centralCharacter P lam)
        (centralCharacter P μ)).multiplicity y =
      stabilizerIndex P hA.isGeneralizedCartan lam μ *
        (VermaModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan x μ)).multiplicity y := by
  have hA' := hA.isGeneralizedCartan
  have hMχ : centralBlock P (VermaModule P (P.weylDot hA' x μ)) (centralCharacter P μ) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' x.property μ) ▸
      centralBlock_verma P (P.weylDot hA' x μ)
  -- the character of `X ≅ T_μ^λ M(x·μ)` (Theorem 7.12)
  have hch0 := character_translation_verma_of_isAntidominant hA hlam hμ hν hz hzν x
  obtain ⟨T, hT, hch⟩ := hch0
  let eTB := centralBlockEquiv P (rTensorEquiv P (IrreducibleModule P ν)
      (equivCentralBlockOfEqTop P hMχ)) (centralCharacter P lam)
  have hchX : hX.character = ∑ y' ∈ T, (VermaModule.isCategoryO P y').character :=
    (IsCategoryO.character_congr hX _ (eX.trans eTB)).trans hch
  have hmX := hX.multiplicity_eq_sum_of_character_eq_sum P T hchX
  have hZν' : ∀ ν'', weightSpace P (IrreducibleModule P ν') ν'' ≠ ⊥ → ν'' ∈ cone P ν' :=
    fun _ h ↦ IrreducibleModule.mem_cone_of_weightSpace_ne_bot h
  have hfin := hX.finite_setOf_mem_cone (y - ν')
  have hmemH : ∀ η, y - ν' ∈ cone P η → hX.multiplicity η ≠ 0 → η ∈ hfin.toFinset :=
    fun η hc hη ↦ (Set.Finite.mem_toFinset _).mpr
      ⟨hc, hX.weightSpace_ne_bot_of_multiplicity_ne_zero hη⟩
  let b : Dual K H → ℕ := fun η ↦
    ((IrreducibleModule.isCategoryO P η).centralTranslation P
      (IrreducibleModule.isCategoryO P ν') (centralCharacter P lam)
        (centralCharacter P μ)).multiplicity y
  let m : Dual K H → Dual K H → ℕ := fun y' η ↦ (VermaModule.isCategoryO P y').multiplicity η
  have h1 : (hX.centralTranslation P (IrreducibleModule.isCategoryO P ν')
      (centralCharacter P lam) (centralCharacter P μ)).multiplicity y =
      ∑ η ∈ hfin.toFinset, hX.multiplicity η * b η :=
    multiplicity_centralTranslation_eq_finsetSum P hX (IrreducibleModule.isCategoryO P ν')
      (centralCharacter P lam) (centralCharacter P μ) hZν' hfin.toFinset hmemH
  -- each Verma step `M((x w')·λ)` translates back to `M(x·μ)` (Theorem 7.6)
  have hstep : ∀ y' ∈ T, ∑ η ∈ hfin.toFinset, m y' η * b η =
      (VermaModule.isCategoryO P (P.weylDot hA' x μ)).multiplicity y := by
    intro y' hy'
    have hy'' : y' ∈ (T : Set (Dual K H)) := hy'
    rw [hT] at hy''
    obtain ⟨w', hw', rfl⟩ := hy''
    have hA1 := multiplicity_centralTranslation_eq_finsetSum P (VermaModule.isCategoryO P _)
      (IrreducibleModule.isCategoryO P ν') (centralCharacter P lam) (centralCharacter P μ)
      hZν' hfin.toFinset fun η hc hη ↦ hmemH η hc fun h0 ↦ hη
        ((Finset.sum_eq_zero_iff.mp ((hmX η).symm.trans h0)) _ hy')
    obtain ⟨e⟩ := translation_verma_equiv_of_isAntidominant P hA hlam hμ hfacet hν' hz' hzν'
      (x * w')
    have hxw : P.weylDot hA' (x * w') μ = P.weylDot hA' x μ := by
      have h1 : (w' : Dual K H ≃ₗ[K] Dual K H) (μ + P.rho) = μ + P.rho := by
        have := congrArg (· + P.rho) hw'
        simpa [weylDot] using this
      simp only [weylDot, Subgroup.coe_mul, LinearEquiv.mul_apply, h1]
    have h2 := multiplicity_centralTranslation_eq_of_equiv P
      (VermaModule.isCategoryO P (P.weylDot hA' (x * w') lam))
      (IrreducibleModule.isCategoryO P ν') (centralCharacter P lam) (centralCharacter P μ)
      (VermaModule.isCategoryO P (P.weylDot hA' (x * w') μ)) e y
    exact hA1.symm.trans (h2.trans (by rw [hxw]))
  calc _ = ∑ η ∈ hfin.toFinset, hX.multiplicity η * b η := h1
    _ = ∑ η ∈ hfin.toFinset, ∑ y' ∈ T, m y' η * b η :=
        Finset.sum_congr rfl fun η _ ↦ by rw [hmX η, Finset.sum_mul]
    _ = ∑ y' ∈ T, ∑ η ∈ hfin.toFinset, m y' η * b η := Finset.sum_comm
    _ = ∑ y' ∈ T, (VermaModule.isCategoryO P (P.weylDot hA' x μ)).multiplicity y :=
        Finset.sum_congr rfl hstep
    _ = _ := by rw [Finset.sum_const, smul_eq_mul, card_eq_stabilizerIndex P hA' lam μ x T hT]

open Classical in
include hA in
/-- **Translation there and back on simple modules** (cf. Humphreys, GSM 94, Corollary 7.12):
`∑_η [T_μ^λ L(x·μ) : L(η)] [T_λ^μ L(η) : L(y)] = |W_μ°/W_λ°| δ_{x·μ, y}`, i.e.
`[T_λ^μ T_μ^λ L(x·μ) : L(y)] = |W_μ°/W_λ°| δ_{x·μ, y}`
(`multiplicity_centralTranslation_of_equiv_eq_sum`). -/
theorem multiplicity_translation_translation_irreducible {lam μ ν ν' : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    (hν' : P.IsDominantIntegral ν') {z' : Dual K H ≃ₗ[K] Dual K H}
    (hz' : z' ∈ P.weylGroup hA.isGeneralizedCartan) (hzν' : z' (μ - lam) = ν')
    (x : P.weylGroup hA.isGeneralizedCartan) (y : Dual K H) :
    ∑ᶠ η, ((IrreducibleModule.isCategoryO P
        (P.weylDot hA.isGeneralizedCartan x μ)).centralTranslation P
          (IrreducibleModule.isCategoryO P ν) (centralCharacter P μ)
            (centralCharacter P lam)).multiplicity η *
        ((IrreducibleModule.isCategoryO P η).centralTranslation P
          (IrreducibleModule.isCategoryO P ν') (centralCharacter P lam)
            (centralCharacter P μ)).multiplicity y =
      if P.weylDot hA.isGeneralizedCartan x μ = y then
        stabilizerIndex P hA.isGeneralizedCartan lam μ else 0 := by
  classical
  have hA' := hA.isGeneralizedCartan
  have := P.finite_weylGroup hA
  have : Fintype (P.weylGroup hA') := Fintype.ofFinite _
  have hZν : ∀ ν'', weightSpace P (IrreducibleModule P ν) ν'' ≠ ⊥ → ν'' ∈ cone P ν :=
    fun _ h ↦ IrreducibleModule.mem_cone_of_weightSpace_ne_bot h
  have hZν' : ∀ ν'', weightSpace P (IrreducibleModule P ν') ν'' ≠ ⊥ → ν'' ∈ cone P ν' :=
    fun _ h ↦ IrreducibleModule.mem_cone_of_weightSpace_ne_bot h
  -- abbreviations
  let a : Dual K H → Dual K H → ℕ := fun ξ η ↦
    ((IrreducibleModule.isCategoryO P ξ).centralTranslation P
      (IrreducibleModule.isCategoryO P ν) (centralCharacter P μ)
      (centralCharacter P lam)).multiplicity η
  let b : Dual K H → Dual K H → ℕ := fun η y ↦
    ((IrreducibleModule.isCategoryO P η).centralTranslation P
      (IrreducibleModule.isCategoryO P ν') (centralCharacter P lam)
      (centralCharacter P μ)).multiplicity y
  let G : Dual K H → Dual K H → ℕ := fun ξ y ↦ ∑ᶠ η, a ξ η * b η y
  let m : Dual K H → Dual K H → ℕ := fun ξ ξ' ↦ (VermaModule.isCategoryO P ξ).multiplicity ξ'
  -- `G ξ y ≠ 0` forces `ξ ≥ y - ν - ν'` and `y` linked to `μ`
  have hGη : ∀ ξ y, G ξ y ≠ 0 → ∃ η, a ξ η ≠ 0 ∧ b η y ≠ 0 := by
    intro ξ y hG
    by_contra hne
    push Not at hne
    exact hG (finsum_eq_zero_of_forall_eq_zero fun η ↦ by
      by_cases ha : a ξ η = 0
      · rw [ha, zero_mul]
      · rw [hne η ha, mul_zero])
  have hGc : ∀ ξ y, G ξ y ≠ 0 → y - ν - ν' ∈ cone P ξ := by
    intro ξ y hG
    obtain ⟨η, ha, hb⟩ := hGη ξ y hG
    exact sub_sub_mem_cone
      (mem_cone_of_multiplicity_centralTranslation_ne_zero P (IrreducibleModule.isCategoryO P ν')
        _ _ hZν' hb)
      (mem_cone_of_multiplicity_centralTranslation_ne_zero P (IrreducibleModule.isCategoryO P ν)
        _ _ hZν ha)
  -- the finite linkage class `S = W·μ`
  let S : Finset (Dual K H) := Finset.univ.image fun w : P.weylGroup hA' ↦ P.weylDot hA' w μ
  have hS : ∀ ξ, centralCharacter P ξ = centralCharacter P μ → ξ ∈ S := by
    intro ξ hξ
    obtain ⟨w, hw, hwe⟩ := (VermaModule.centralCharacter_eq_iff P hA μ ξ).mp hξ.symm
    exact Finset.mem_image.mpr ⟨⟨w, hw⟩, Finset.mem_univ _, by
      rw [weylDot, hwe, add_sub_cancel_right]⟩
  have hwS : ∀ w : P.weylGroup hA', P.weylDot hA' w μ ∈ S := fun w ↦
    Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
  have hGS : ∀ ξ y, G ξ y ≠ 0 → y ∈ S := by
    intro ξ y hG
    obtain ⟨η, -, hb⟩ := hGη ξ y hG
    exact hS y (centralCharacter_eq_of_multiplicity_centralTranslation_ne_zero P
      (IrreducibleModule.isCategoryO P η) (IrreducibleModule.isCategoryO P ν') _ _ hb)
  -- the Verma identity `n [M(ξ) : L(y)] = ∑_{ξ' ∈ S} [M(ξ) : L(ξ')] G ξ' y`
  have hverma : ∀ w : P.weylGroup hA', ∀ y, stabilizerIndex P hA' lam μ *
      m (P.weylDot hA' w μ) y = ∑ ξ' ∈ S, m (P.weylDot hA' w μ) ξ' * G ξ' y := by
    intro w y
    have hξV := VermaModule.isCategoryO P (P.weylDot hA' w μ)
    have hX := hξV.centralTranslation P (IrreducibleModule.isCategoryO P ν)
      (centralCharacter P μ) (centralCharacter P lam)
    have hfin := hξV.finite_setOf_mem_cone (y - ν - ν')
    have hs : ∀ ξ', y - ν - ν' ∈ cone P ξ' → hξV.multiplicity ξ' ≠ 0 → ξ' ∈ hfin.toFinset :=
      fun ξ' hc h ↦ (Set.Finite.mem_toFinset _).mpr
        ⟨hc, hξV.weightSpace_ne_bot_of_multiplicity_ne_zero h⟩
    have hB := multiplicity_translation_translation_verma P hA hlam hμ hfacet hν hz hzν hν' hz'
      hzν' w hX LieModuleEquiv.refl y
    have hA2 := multiplicity_centralTranslation_of_equiv_eq_sum P hξV hX
      (IrreducibleModule.isCategoryO P ν) (IrreducibleModule.isCategoryO P ν')
      (centralCharacter P μ) (centralCharacter P lam) (centralCharacter P μ) LieModuleEquiv.refl
      hZν hZν' hfin.toFinset hs
    have hBA : stabilizerIndex P hA' lam μ * m (P.weylDot hA' w μ) y =
        ∑ ξ' ∈ hfin.toFinset, m (P.weylDot hA' w μ) ξ' * G ξ' y := hB.symm.trans hA2
    have hblock : centralBlock P (VermaModule P (P.weylDot hA' w μ)) (centralCharacter P μ) = ⊤ :=
      (VermaModule.centralCharacter_weyl P hA' w.property μ) ▸
        centralBlock_verma P (P.weylDot hA' w μ)
    have e1 : ∑ ξ' ∈ hfin.toFinset, m (P.weylDot hA' w μ) ξ' * G ξ' y =
        ∑ ξ' ∈ hfin.toFinset ∪ S, m (P.weylDot hA' w μ) ξ' * G ξ' y :=
      Finset.sum_subset Finset.subset_union_left fun ξ' _ hξ' ↦ by
        by_cases hc : y - ν - ν' ∈ cone P ξ'
        · by_cases hm : m (P.weylDot hA' w μ) ξ' = 0
          · rw [hm, zero_mul]
          · exact absurd (hs ξ' hc hm) hξ'
        · by_cases hG : G ξ' y = 0
          · rw [hG, mul_zero]
          · exact absurd (hGc ξ' y hG) hc
    have e2 : ∑ ξ' ∈ S, m (P.weylDot hA' w μ) ξ' * G ξ' y =
        ∑ ξ' ∈ hfin.toFinset ∪ S, m (P.weylDot hA' w μ) ξ' * G ξ' y :=
      Finset.sum_subset Finset.subset_union_right fun ξ' _ hξ' ↦ by
        by_cases hm : m (P.weylDot hA' w μ) ξ' = 0
        · rw [hm, zero_mul]
        · exact absurd (hS ξ' (hξV.centralCharacter_eq_of_multiplicity_ne_zero P hblock hm)) hξ'
    exact hBA.trans (e1.trans e2.symm)
  -- induction over the linkage class
  have key : ∀ N : ℕ, ∀ w : P.weylGroup hA',
      (S.filter (· ∈ cone P (P.weylDot hA' w μ))).card ≤ N →
      ∀ y, y ∈ S → G (P.weylDot hA' w μ) y =
        if P.weylDot hA' w μ = y then stabilizerIndex P hA' lam μ else 0 := by
    intro N
    induction N with
    | zero =>
      intro w hw
      exfalso
      have : P.weylDot hA' w μ ∈ S.filter (· ∈ cone P (P.weylDot hA' w μ)) :=
        Finset.mem_filter.mpr ⟨hwS w, mem_cone_self _⟩
      exact absurd (Finset.card_pos.mpr ⟨_, this⟩) (by omega)
    | succ N ih =>
      intro w hw y hy
      have hv := hverma w y
      have hself : m (P.weylDot hA' w μ) (P.weylDot hA' w μ) = 1 :=
        VermaModule.multiplicity_self (P := P) _
      rw [← Finset.add_sum_erase S _ (hwS w), hself, one_mul] at hv
      -- the lower terms
      have hlow : ∀ ξ' ∈ S.erase (P.weylDot hA' w μ), m (P.weylDot hA' w μ) ξ' * G ξ' y =
          m (P.weylDot hA' w μ) ξ' * (if ξ' = y then stabilizerIndex P hA' lam μ else 0) := by
        intro ξ' hξ'
        obtain ⟨hne, hξ'S⟩ := Finset.mem_erase.mp hξ'
        by_cases hm : m (P.weylDot hA' w μ) ξ' = 0
        · rw [hm, zero_mul, zero_mul]
        obtain ⟨w', -, rfl⟩ := Finset.mem_image.mp hξ'S
        have hlt := VermaModule.mem_cone_of_multiplicity_ne_zero (P := P) hm
        refine congrArg _ (ih w' ?_ y hy)
        refine Nat.lt_succ_iff.mp (lt_of_lt_of_le (Finset.card_lt_card ?_) hw)
        refine ⟨fun a ha ↦ ?_, fun hsub ↦ ?_⟩
        · obtain ⟨haS, hac⟩ := Finset.mem_filter.mp ha
          exact Finset.mem_filter.mpr ⟨haS, mem_cone_trans hac hlt⟩
        · have hξmem : P.weylDot hA' w μ ∈ S.filter (· ∈ cone P (P.weylDot hA' w μ)) :=
            Finset.mem_filter.mpr ⟨hwS w, mem_cone_self _⟩
          exact hne (eq_of_mem_cone_of_mem_cone hlt (Finset.mem_filter.mp (hsub hξmem)).2)
      rw [Finset.sum_congr rfl hlow] at hv
      by_cases hξy : P.weylDot hA' w μ = y
      · subst hξy
        rw [Finset.sum_eq_zero fun ξ' hξ' ↦ by
          rw [ite_eq_right (Finset.mem_erase.mp hξ').1, mul_zero], add_zero, hself, mul_one] at hv
        rw [ite_eq_left rfl]
        exact hv.symm
      · rw [ite_eq_right hξy]
        have hyS : y ∈ S.erase (P.weylDot hA' w μ) := Finset.mem_erase.mpr ⟨Ne.symm hξy, hy⟩
        rw [← Finset.add_sum_erase _ _ hyS, ite_eq_left rfl,
          Finset.sum_eq_zero fun ξ' hξ' ↦ by
            rw [ite_eq_right (Finset.mem_erase.mp hξ').1, mul_zero], add_zero] at hv
        have hc := mul_comm (stabilizerIndex P hA' lam μ) (m (P.weylDot hA' w μ) y)
        omega
  -- conclusion
  change G (P.weylDot hA' x μ) y = _
  by_cases hy : y ∈ S
  · exact key _ x le_rfl y hy
  · rw [ite_eq_right fun (h : P.weylDot hA' x μ = y) ↦ hy (h ▸ hwS x)]
    by_contra hG
    exact hy (hGS _ y hG)

include hA in
/-- **Translation to a facet closure and back** (Humphreys, GSM 94, Corollary 7.12, arbitrary
weights). Let `λ`, `μ` be antidominant with every positive root orthogonal to `λ + ρ` orthogonal
to `μ + ρ`, `ν = z (λ - μ)` and `ν' = z' (μ - λ)` dominant integral (`z, z' ∈ W`),
`T_μ^λ = pr_{χ_λ}(pr_{χ_μ}(−) ⊗ L(ν))`, `T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν'))`. For `V` in `𝒪`
lying in the block of `μ` and `X ≅ T_μ^λ V` (e.g. `X = T_μ^λ V`):
`ch T_λ^μ X = |W_μ°/W_λ°| ch V`. (Humphreys writes `M ∈ 𝒪`; the block condition is implicit
there.) -/
theorem character_translation_translation {lam μ ν ν' : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    (hν' : P.IsDominantIntegral ν') {z' : Dual K H ≃ₗ[K] Dual K H}
    (hz' : z' ∈ P.weylGroup hA.isGeneralizedCartan) (hzν' : z' (μ - lam) = ν')
    {V X : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
    [LieModule K P.KacMoodyAlgebra V] [AddCommGroup X] [Module K X]
    [LieRingModule P.KacMoodyAlgebra X] [LieModule K P.KacMoodyAlgebra X]
    (hV : IsCategoryO P V) (hVμ : centralBlock P V (centralCharacter P μ) = ⊤)
    (hX : IsCategoryO P X)
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
      (centralCharacter P lam) V) :
    (hX.centralTranslation P (IrreducibleModule.isCategoryO P ν') (centralCharacter P lam)
        (centralCharacter P μ)).character =
      stabilizerIndex P hA.isGeneralizedCartan lam μ • hV.character := by
  classical
  have hA' := hA.isGeneralizedCartan
  have hZν : ∀ ν'', weightSpace P (IrreducibleModule P ν) ν'' ≠ ⊥ → ν'' ∈ cone P ν :=
    fun _ h ↦ IrreducibleModule.mem_cone_of_weightSpace_ne_bot h
  have hZν' : ∀ ν'', weightSpace P (IrreducibleModule P ν') ν'' ≠ ⊥ → ν'' ∈ cone P ν' :=
    fun _ h ↦ IrreducibleModule.mem_cone_of_weightSpace_ne_bot h
  let G : Dual K H → Dual K H → ℕ := fun ξ y ↦ ∑ᶠ η,
    ((IrreducibleModule.isCategoryO P ξ).centralTranslation P
      (IrreducibleModule.isCategoryO P ν) (centralCharacter P μ)
      (centralCharacter P lam)).multiplicity η *
    ((IrreducibleModule.isCategoryO P η).centralTranslation P
      (IrreducibleModule.isCategoryO P ν') (centralCharacter P lam)
      (centralCharacter P μ)).multiplicity y
  -- the simple factors of `V` are the `L(x·μ)`
  have hG : ∀ ξ y, hV.multiplicity ξ ≠ 0 →
      G ξ y = if ξ = y then stabilizerIndex P hA' lam μ else 0 := by
    intro ξ y hξ
    have hχ := hV.centralCharacter_eq_of_multiplicity_ne_zero P hVμ hξ
    obtain ⟨w, hw, hwe⟩ := (VermaModule.centralCharacter_eq_iff P hA μ ξ).mp hχ.symm
    have hξ' : ξ = P.weylDot hA' ⟨w, hw⟩ μ := by rw [weylDot, hwe, add_sub_cancel_right]
    subst hξ'
    exact multiplicity_translation_translation_irreducible P hA hlam hμ hfacet hν hz hzν hν' hz'
      hzν' _ y
  have hmult : ∀ y, (hX.centralTranslation P (IrreducibleModule.isCategoryO P ν')
      (centralCharacter P lam) (centralCharacter P μ)).multiplicity y =
      stabilizerIndex P hA' lam μ * hV.multiplicity y := by
    intro y
    have hfin := hV.finite_setOf_mem_cone (y - ν - ν')
    have hs : ∀ ξ, y - ν - ν' ∈ cone P ξ → hV.multiplicity ξ ≠ 0 →
        ξ ∈ insert y hfin.toFinset := fun ξ hc h ↦ Finset.mem_insert_of_mem
      ((Set.Finite.mem_toFinset _).mpr ⟨hc, hV.weightSpace_ne_bot_of_multiplicity_ne_zero h⟩)
    have h1 : (hX.centralTranslation P (IrreducibleModule.isCategoryO P ν')
        (centralCharacter P lam) (centralCharacter P μ)).multiplicity y =
        ∑ ξ ∈ insert y hfin.toFinset, hV.multiplicity ξ * G ξ y :=
      multiplicity_centralTranslation_of_equiv_eq_sum P hV hX
        (IrreducibleModule.isCategoryO P ν) (IrreducibleModule.isCategoryO P ν') _ _ _ eX hZν
        hZν' _ hs
    refine h1.trans ?_
    rw [Finset.sum_eq_single_of_mem y (Finset.mem_insert_self y _) fun ξ _ hξy ↦ ?_]
    · by_cases hy : hV.multiplicity y = 0
      · rw [hy, zero_mul, mul_zero]
      · rw [hG y y hy, ite_eq_left rfl, mul_comm]
    · by_cases hξ : hV.multiplicity ξ = 0
      · rw [hξ, zero_mul]
      · rw [hG ξ y hξ, ite_eq_right hξy, mul_zero]
  exact IsCategoryO.character_eq_nsmul_of_multiplicity_eq P _ hV _ hmult

end FacetClosure

end Matrix.Realization.KacMoodyAlgebra
