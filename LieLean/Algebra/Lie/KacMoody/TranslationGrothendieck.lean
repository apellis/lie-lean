/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationEquivalence
import LieLean.Algebra.Lie.KacMoody.TranslationShuffling

/-!
# Translation within a facet on Grothendieck groups

Humphreys, GSM 94, Proposition 7.8: if `λ`, `μ` are antidominant and compatible and `λ♮`, `μ♮`
lie in the same facet, then `T_λ^μ` induces an isomorphism between the Grothendieck groups of the
blocks `𝒪_λ` and `𝒪_μ` sending `[M(w·λ)]` to `[M(w·μ)]` and `[L(w·λ)]` to `[L(w·μ)]`. In
particular `[M : L(w·λ)] = [T_λ^μ M : L(w·μ)]` for `M` in the block of `λ`.

Here the Grothendieck group is the completed one of `IsCategoryO.multiplicities`
(`[V] = ∑_η [V : L(η)] e^η ∈ ℰ`), and `T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν))` with `ν = z (μ - λ)`
dominant integral (`z ∈ W`). "Same facet" means that the positive roots orthogonal to `λ + ρ` and
to `μ + ρ` agree. Finite type, algebraically closed field of characteristic zero, arbitrary
(not necessarily integral) weights.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.translationClassMap`: the additive map
  `ℰ → ℰ`, `∑ c_η e^η ↦ ∑_{x ∈ W} c_{x·λ} e^{x·μ}` (one term for each point of the orbit `W·λ`).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.translation_irreducible_of_sameFacet_of_isAntidominant`:
  `T_λ^μ L(w·λ) ≅ L(w·μ)` for all `w ∈ W`.
* `Matrix.Realization.KacMoodyAlgebra.multiplicity_translation_of_sameFacet`:
  `[T_λ^μ V : L(w·μ)] = [V : L(w·λ)]` for `V ∈ 𝒪` in the block of `λ`.
* `Matrix.Realization.KacMoodyAlgebra.multiplicities_translation_of_sameFacet`: Proposition 7.8,
  `[T_λ^μ V] = translationClassMap λ μ [V]`.
* `Matrix.Realization.KacMoodyAlgebra.translationClassMap_exp`,
  `Matrix.Realization.KacMoodyAlgebra.translationClassMap_verma`: `[L(w·λ)] ↦ [L(w·μ)]` and
  `[M(w·λ)] ↦ [M(w·μ)]`.
* `Matrix.Realization.KacMoodyAlgebra.translationClassMap_translationClassMap`: the map for
  `μ, λ` is inverse to the map for `λ, μ` on classes supported on `W·λ`.

## Proof

As in Humphreys, through Theorem 7.6 and Proposition 7.7. That `T_λ^μ L(w·λ)` is nonzero is
deduced from faithfulness of translation within a facet
(`subsingleton_of_subsingleton_translation_of_sameFacet`) rather than from the isomorphism of
Grothendieck groups; then the multiplicity formula for translation
(`multiplicity_centralTranslation_eq_finsetSum`) gives the multiplicities. The stabilizers of
`λ + ρ` and `μ + ρ` in `W` coincide (`weylDot_eq_of_weylDot_eq`), so `x·λ ↦ x·μ` is well defined.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.8.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

/-! ### The orbit map `x·λ ↦ x·μ` -/

include hA in
/-- If every positive root orthogonal to `a + ρ` is orthogonal to `b + ρ`, then `x·a = w·a`
implies `x·b = w·b`. -/
theorem weylDot_eq_of_weylDot_eq {a b : Dual K H}
    (hf : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (a + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (b + P.rho) v i = 0)
    {x w : P.weylGroup hA.isGeneralizedCartan}
    (h : P.weylDot hA.isGeneralizedCartan x a = P.weylDot hA.isGeneralizedCartan w a) :
    P.weylDot hA.isGeneralizedCartan x b = P.weylDot hA.isGeneralizedCartan w b := by
  have h1 : (x : Dual K H ≃ₗ[K] Dual K H) (a + P.rho) =
      (w : Dual K H ≃ₗ[K] Dual K H) (a + P.rho) := sub_left_injective h
  set u := w⁻¹ * x
  have hwu : w * u = x := mul_inv_cancel_left w x
  have hu : (u : Dual K H ≃ₗ[K] Dual K H) (a + P.rho) = a + P.rho := by
    rw [← hwu, Subgroup.coe_mul, LinearEquiv.mul_apply] at h1
    exact (w : Dual K H ≃ₗ[K] Dual K H).injective h1
  have hub : (u : Dual K H ≃ₗ[K] Dual K H) (b + P.rho) = b + P.rho := by
    refine (apply_eq_self_iff_mem_closure_reflectionOf hA (b + P.rho) _).mpr
      (Subgroup.closure_mono ?_ ((apply_eq_self_iff_mem_closure_reflectionOf hA
        (a + P.rho) _).mp hu))
    rintro _ ⟨v', i', h0, rfl⟩
    refine ⟨v', i', ?_, rfl⟩
    rcases isPosRoot_or v' i' with hp | hp
    · exact hf v' i' hp h0
    · have := hf _ _ hp (by rw [corootPairing_mul_simple, h0, neg_zero])
      rwa [corootPairing_mul_simple, neg_eq_zero] at this
  simp only [weylDot]
  rw [← hwu, Subgroup.coe_mul, LinearEquiv.mul_apply, hub]

/-- The finite orbit `W·λ` under the dot action. -/
def dotOrbit (lam : Dual K H) : Finset (Dual K H) :=
  haveI := P.finite_weylGroup hA
  (Set.finite_range fun x : P.weylGroup hA.isGeneralizedCartan ↦
    P.weylDot hA.isGeneralizedCartan x lam).toFinset

theorem mem_dotOrbit {lam η : Dual K H} :
    η ∈ dotOrbit P hA lam ↔ ∃ x, P.weylDot hA.isGeneralizedCartan x lam = η := by
  simp [dotOrbit]

open Classical in
/-- The map `x·λ ↦ x·μ` on the orbit `W·λ` (the identity off the orbit). It is well defined
when `λ♮`, `μ♮` lie in the same facet (`facetShift_weylDot`). -/
def facetShift (lam μ η : Dual K H) : Dual K H :=
  if h : ∃ x, P.weylDot hA.isGeneralizedCartan x lam = η then
    P.weylDot hA.isGeneralizedCartan h.choose μ else η

theorem facetShift_weylDot {lam μ : Dual K H}
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    facetShift P hA lam μ (P.weylDot hA.isGeneralizedCartan w lam) =
      P.weylDot hA.isGeneralizedCartan w μ := by
  have h : ∃ x, P.weylDot hA.isGeneralizedCartan x lam = P.weylDot hA.isGeneralizedCartan w lam :=
    ⟨w, rfl⟩
  rw [facetShift, dite_eq_left_of_eq_true (eq_true h)]
  exact weylDot_eq_of_weylDot_eq P hA hfacet h.choose_spec

/-- **The map of Proposition 7.8 on the completed Grothendieck group**:
`∑ c_η e^η ↦ ∑_{η ∈ W·λ} c_η e^{facetShift η}`, i.e. `e^{x·λ} ↦ e^{x·μ}` on the block of `λ`. -/
def translationClassMap (lam μ : Dual K H) : P.CharacterRing ℤ →+ P.CharacterRing ℤ where
  toFun c := ∑ η ∈ dotOrbit P hA lam, c.coeffAt η • CharacterRing.exp P ℤ (facetShift P hA lam μ η)
  map_zero' := by simp
  map_add' c d := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun η _ ↦ ?_
    rw [← add_smul]
    exact congrArg (· • _) HahnSeries.coeff_add

theorem coeffAt_translationClassMap (lam μ : Dual K H) (c : P.CharacterRing ℤ) (ξ : Dual K H) :
    (translationClassMap P hA lam μ c).coeffAt ξ = ∑ η ∈ dotOrbit P hA lam,
      c.coeffAt η * (CharacterRing.exp P ℤ (facetShift P hA lam μ η)).coeffAt ξ := by
  change HahnSeries.coeff (∑ η ∈ dotOrbit P hA lam, _) _ = _
  rw [HahnSeries.coeff_sum]
  simp only [HahnSeries.coeff_smul, smul_eq_mul]

/-- `translationClassMap` on coefficients: the coefficient at `w·μ` is the coefficient at
`w·λ`. -/
theorem coeffAt_translationClassMap_weylDot {lam μ : Dual K H}
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hfacet' : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0)
    (c : P.CharacterRing ℤ) (w : P.weylGroup hA.isGeneralizedCartan) :
    (translationClassMap P hA lam μ c).coeffAt (P.weylDot hA.isGeneralizedCartan w μ) =
      c.coeffAt (P.weylDot hA.isGeneralizedCartan w lam) := by
  classical
  rw [coeffAt_translationClassMap, Finset.sum_eq_single_of_mem (P.weylDot hA.isGeneralizedCartan
    w lam) ((mem_dotOrbit P hA).mpr ⟨w, rfl⟩)]
  · rw [facetShift_weylDot P hA hfacet, CharacterRing.coeff_exp_self, mul_one]
  · intro η hη hne
    obtain ⟨x, rfl⟩ := (mem_dotOrbit P hA).mp hη
    rw [facetShift_weylDot P hA hfacet, CharacterRing.coeff_exp,
      ite_eq_right_of_eq_false _ _
        (eq_false fun h ↦ hne (weylDot_eq_of_weylDot_eq P hA hfacet' h.symm)),
      mul_zero]

/-- `translationClassMap λ μ` vanishes off the orbit `W·μ`. -/
theorem coeffAt_translationClassMap_eq_zero (lam μ : Dual K H) (c : P.CharacterRing ℤ)
    {ξ : Dual K H} (hξ : ∀ x : P.weylGroup hA.isGeneralizedCartan,
      P.weylDot hA.isGeneralizedCartan x μ ≠ ξ) :
    (translationClassMap P hA lam μ c).coeffAt ξ = 0 := by
  classical
  rw [coeffAt_translationClassMap]
  refine Finset.sum_eq_zero fun η hη ↦ ?_
  obtain ⟨x, rfl⟩ := (mem_dotOrbit P hA).mp hη
  rw [facetShift, dite_eq_left_of_eq_true (eq_true ⟨x, rfl⟩), CharacterRing.coeff_exp,
    ite_eq_right_of_eq_false _ _ (eq_false (hξ _).symm), mul_zero]

/-- **Isomorphism of Grothendieck groups** (Humphreys, GSM 94, Proposition 7.8): on classes
supported on `W·λ`, `translationClassMap μ λ` is inverse to `translationClassMap λ μ`. -/
theorem translationClassMap_translationClassMap {lam μ : Dual K H}
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hfacet' : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0)
    {c : P.CharacterRing ℤ}
    (hc : ∀ ξ, c.coeffAt ξ ≠ 0 → ∃ x, P.weylDot hA.isGeneralizedCartan x lam = ξ) :
    translationClassMap P hA μ lam (translationClassMap P hA lam μ c) = c := by
  ext ξ
  by_cases hξ : ∃ x, P.weylDot hA.isGeneralizedCartan x lam = ξ
  · obtain ⟨x, rfl⟩ := hξ
    rw [coeffAt_translationClassMap_weylDot P hA hfacet' hfacet,
      coeffAt_translationClassMap_weylDot P hA hfacet hfacet']
  · push Not at hξ
    rw [coeffAt_translationClassMap_eq_zero P hA μ lam _ hξ]
    by_contra h
    exact absurd (hc ξ (Ne.symm h)) (not_exists.mpr hξ)

/-! ### Translation of simple modules and multiplicities -/

variable [IsAlgClosed K] [FiniteDimensional K H]

include hA in
/-- **Translation of simple modules within a facet** (Humphreys, GSM 94, §7.8, from
Proposition 7.7; arbitrary weights): if `λ`, `μ` are antidominant with the same positive roots
orthogonal to `λ + ρ` and `μ + ρ`, and `ν = z (μ - λ)` is dominant integral, then
`T_λ^μ L(w·λ) ≅ L(w·μ)` for every `w ∈ W`. -/
theorem translation_irreducible_of_sameFacet_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hfacet' : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    Nonempty (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ)
        (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) := by
  rcases translation_irreducible_of_isAntidominant P hA hlam hμ hfacet hν hz hzν w with h | h
  · exfalso
    have hχ : centralCharacter P (P.weylDot hA.isGeneralizedCartan w lam) =
        centralCharacter P lam := centralCharacter_weyl P hA.isGeneralizedCartan w.property lam
    have hNχ : centralBlock P (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))
        (centralCharacter P lam) = ⊤ := hχ ▸ centralBlock_irreducible P _
    have := subsingleton_of_subsingleton_translation_of_sameFacet P hA hμ hlam hfacet' hfacet hν
      hz hzν (IrreducibleModule.isCategoryO P _) hNχ h
    exact IrreducibleModule.hwv_ne_zero P (P.weylDot hA.isGeneralizedCartan w lam)
      (Subsingleton.elim _ _)
  · exact h

section Modules

include hA in
/-- **Multiplicities under translation within a facet** (Humphreys, GSM 94, §7.8): for `V ∈ 𝒪`
in the block of `λ`, `[T_λ^μ V : L(w·μ)] = [V : L(w·λ)]` for every `w ∈ W`. -/
theorem multiplicity_translation_of_sameFacet {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hfacet' : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
    [LieModule K P.KacMoodyAlgebra V]
    (hV : IsCategoryO P V) (hVlam : centralBlock P V (centralCharacter P lam) = ⊤)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    (hV.centralTranslation P (IrreducibleModule.isCategoryO P ν) (centralCharacter P lam)
      (centralCharacter P μ)).multiplicity (P.weylDot hA.isGeneralizedCartan w μ) =
      hV.multiplicity (P.weylDot hA.isGeneralizedCartan w lam) := by
  classical
  have hs : ∀ η, P.weylDot hA.isGeneralizedCartan w μ - ν ∈ cone P η →
      hV.multiplicity η ≠ 0 → η ∈ dotOrbit P hA lam := by
    intro η _ hη
    obtain ⟨x, hx, hxe⟩ := (VermaModule.centralCharacter_eq_iff P hA lam η).mp
      (hV.centralCharacter_eq_of_multiplicity_ne_zero P hVlam hη).symm
    exact (mem_dotOrbit P hA).mpr ⟨⟨x, hx⟩, by simp only [weylDot]; rw [hxe]; abel⟩
  rw [multiplicity_centralTranslation_eq_finsetSum P hV (IrreducibleModule.isCategoryO P ν) _ _
    (fun _ hne ↦ IrreducibleModule.mem_cone_of_weightSpace_ne_bot hne) _ hs,
    Finset.sum_eq_single_of_mem (P.weylDot hA.isGeneralizedCartan w lam)
      ((mem_dotOrbit P hA).mpr ⟨w, rfl⟩)]
  · obtain ⟨e⟩ := translation_irreducible_of_sameFacet_of_isAntidominant P hA hlam hμ hfacet
      hfacet' hν hz hzν w
    rw [← IsCategoryO.multiplicity_congr (IrreducibleModule.isCategoryO P _) _ e,
      IrreducibleModule.multiplicity_eq, ite_eq_left_of_eq_true _ _ (eq_true rfl), mul_one]
  · intro η hη hne
    obtain ⟨x, rfl⟩ := (mem_dotOrbit P hA).mp hη
    obtain ⟨e⟩ := translation_irreducible_of_sameFacet_of_isAntidominant P hA hlam hμ hfacet
      hfacet' hν hz hzν x
    rw [← IsCategoryO.multiplicity_congr (IrreducibleModule.isCategoryO P _) _ e,
      IrreducibleModule.multiplicity_eq, ite_eq_right_of_eq_false _ _
        (eq_false fun h ↦ hne (weylDot_eq_of_weylDot_eq P hA hfacet' h.symm)), mul_zero]

include hA in
/-- **Translation within a facet on Grothendieck groups** (Humphreys, GSM 94, Proposition 7.8):
for `V ∈ 𝒪` in the block of `λ`, `[T_λ^μ V] = translationClassMap λ μ [V]` in the completed
Grothendieck group. -/
theorem multiplicities_translation_of_sameFacet {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hfacet' : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
    [LieModule K P.KacMoodyAlgebra V]
    (hV : IsCategoryO P V) (hVlam : centralBlock P V (centralCharacter P lam) = ⊤) :
    (hV.centralTranslation P (IrreducibleModule.isCategoryO P ν) (centralCharacter P lam)
      (centralCharacter P μ)).multiplicities =
      translationClassMap P hA lam μ hV.multiplicities := by
  ext ξ
  by_cases hξ : ∃ x, P.weylDot hA.isGeneralizedCartan x μ = ξ
  · obtain ⟨x, rfl⟩ := hξ
    rw [coeffAt_translationClassMap_weylDot P hA hfacet hfacet', IsCategoryO.coeffAt_multiplicities,
      IsCategoryO.coeffAt_multiplicities,
      multiplicity_translation_of_sameFacet P hA hlam hμ hfacet hfacet' hν hz hzν hV hVlam x]
  · push Not at hξ
    rw [coeffAt_translationClassMap_eq_zero P hA lam μ _ hξ, IsCategoryO.coeffAt_multiplicities,
      Nat.cast_eq_zero]
    by_contra hne
    have hχ := IsCategoryO.centralCharacter_eq_of_multiplicity_ne_zero P _
      (centralBlock_centralTranslation_eq_top P (centralCharacter P lam) (centralCharacter P μ)) hne
    obtain ⟨x, hx, hxe⟩ := (VermaModule.centralCharacter_eq_iff P hA μ ξ).mp hχ.symm
    exact hξ ⟨x, hx⟩ (by simp only [weylDot]; rw [hxe]; abel)

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- Proposition 7.8 on simple classes: `translationClassMap λ μ [L(w·λ)] = [L(w·μ)]`. -/
theorem translationClassMap_exp {lam μ : Dual K H}
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hfacet' : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    translationClassMap P hA lam μ
        (CharacterRing.exp P ℤ (P.weylDot hA.isGeneralizedCartan w lam)) =
      CharacterRing.exp P ℤ (P.weylDot hA.isGeneralizedCartan w μ) := by
  classical
  ext ξ
  by_cases hξ : ∃ x, P.weylDot hA.isGeneralizedCartan x μ = ξ
  · obtain ⟨x, rfl⟩ := hξ
    rw [coeffAt_translationClassMap_weylDot P hA hfacet hfacet', CharacterRing.coeff_exp,
      CharacterRing.coeff_exp]
    by_cases h : P.weylDot hA.isGeneralizedCartan x lam = P.weylDot hA.isGeneralizedCartan w lam
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
        ite_eq_left_of_eq_true _ _ (eq_true (weylDot_eq_of_weylDot_eq P hA hfacet h))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _
        (eq_false fun h' ↦ h (weylDot_eq_of_weylDot_eq P hA hfacet' h'))]
  · push Not at hξ
    rw [coeffAt_translationClassMap_eq_zero P hA lam μ _ hξ, CharacterRing.coeff_exp,
      ite_eq_right_of_eq_false _ _ (eq_false (hξ w).symm)]

include hA in
/-- Proposition 7.8 on Verma classes: `translationClassMap λ μ [M(w·λ)] = [M(w·μ)]`. -/
theorem translationClassMap_verma {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hfacet' : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    translationClassMap P hA lam μ (IsCategoryO.multiplicities (P := P)
        (V := VermaModule P (P.weylDot hA.isGeneralizedCartan w lam))
        (VermaModule.isCategoryO P _)) =
      IsCategoryO.multiplicities (P := P)
        (V := VermaModule P (P.weylDot hA.isGeneralizedCartan w μ))
        (VermaModule.isCategoryO P _) := by
  have hχ : centralCharacter P (P.weylDot hA.isGeneralizedCartan w lam) =
      centralCharacter P lam := centralCharacter_weyl P hA.isGeneralizedCartan w.property lam
  have hMχ : centralBlock P (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam))
      (centralCharacter P lam) = ⊤ := hχ ▸ centralBlock_verma P _
  rw [← multiplicities_translation_of_sameFacet P hA hlam hμ hfacet hfacet' hν hz hzν _ hMχ]
  obtain ⟨e⟩ := translation_verma_equiv_of_isAntidominant P hA hlam hμ hfacet hν hz hzν w
  ext ξ
  rw [IsCategoryO.coeffAt_multiplicities, IsCategoryO.coeffAt_multiplicities,
    IsCategoryO.multiplicity_congr (VermaModule.isCategoryO P _) _ e]

end Modules

end Matrix.Realization.KacMoodyAlgebra
