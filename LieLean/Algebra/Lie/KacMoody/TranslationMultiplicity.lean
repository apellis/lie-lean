/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationSameFacet

/-!
# Composition multiplicities and translation functors

Translation `T = pr_{χ₂}(pr_{χ₁}(−) ⊗ Z)` is exact, so it induces a map on Grothendieck groups.
This file records the consequence used for translation of simple modules: for `V` in `𝒪` and a
coefficient module `Z` in `𝒪` whose weights are `≤ ν`,

`[T V : L(y)] = ∑_η [V : L(η)] [T L(η) : L(y)]`,

the sum over the irreducible factors `L(η)` of a local composition series of `V` for the weight
`y - ν` ([Kac] Lemma 9.6); the remaining factors of the series have no weight `≥ y - ν`,
so their translations have no weight `y`.

## Main results

* `IsCategoryO.multiplicity_congr`: isomorphic modules have the same multiplicities.
* `IsCategoryO.multiplicity_eq_add_of_exact`: multiplicities are additive on short exact
  sequences.
* `weightSpace_centralTranslation_eq_bot`: `(T V)_y = 0` if `pr_{χ₁} V` has no weight `≥ y - ν`.
* `multiplicity_centralTranslation_eq_sum`: the formula above.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {U V W Z : Type*}
  [AddCommGroup U] [Module K U] [LieRingModule P.KacMoodyAlgebra U]
  [LieModule K P.KacMoodyAlgebra U]
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]
  [AddCommGroup Z] [Module K Z] [LieRingModule P.KacMoodyAlgebra Z]
  [LieModule K P.KacMoodyAlgebra Z]

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

/-! ### Multiplicities and exact sequences -/

namespace IsCategoryO

variable {P}

/-- Isomorphic modules in `𝒪` have the same composition multiplicities. -/
theorem multiplicity_congr (hV : IsCategoryO P V) (hW : IsCategoryO P W)
    (e : V ≃ₗ⁅K,P.KacMoodyAlgebra⁆ W) (μ : Dual K H) :
    hV.multiplicity μ = hW.multiplicity μ :=
  (character_eq_iff hV hW).mp (character_congr hV hW e) μ

/-- **Multiplicities are additive on short exact sequences** `0 → U → V → W → 0` in `𝒪`. -/
theorem multiplicity_eq_add_of_exact (hU : IsCategoryO P U) (hV : IsCategoryO P V)
    (hW : IsCategoryO P W) (f : U →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (g : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W)
    (hf : Function.Injective f) (hex : g.ker = f.range) (hg : Function.Surjective g)
    (μ : Dual K H) : hV.multiplicity μ = hU.multiplicity μ + hW.multiplicity μ := by
  obtain ⟨e₂⟩ := LieSubmodule.Quotient.nonempty_lieModuleEquiv_of_surjective f.range g hg hex
  let e₁ : U ≃ₗ⁅K,P.KacMoodyAlgebra⁆ f.range :=
    LieModuleEquiv.ofBijective
      (f.codRestrict f.range fun m ↦ by rw [LieModuleHom.mem_range]; exact ⟨m, rfl⟩)
      ⟨fun a b hab ↦ hf (congrArg Subtype.val hab), fun y ↦ by
        have hy := y.2
        rw [LieModuleHom.mem_range] at hy
        obtain ⟨m, hm⟩ := hy
        exact ⟨m, Subtype.ext hm⟩⟩
  rw [hV.multiplicity_eq_add f.range μ]
  congr 1
  · exact (multiplicity_congr hU _ e₁ μ).symm
  · exact multiplicity_congr _ hW e₂ μ

/-- `[V : L(μ)] = 0` if `μ` is not a weight of `V`. -/
theorem multiplicity_eq_zero_of_weightSpace_eq_bot (hV : IsCategoryO P V) {μ : Dual K H}
    (h : weightSpace P V μ = ⊥) : hV.multiplicity μ = 0 := by
  have := hV.multiplicity_le_finrank μ
  rw [h, finrank_bot] at this
  exact Nat.le_zero.mp this

end IsCategoryO

/-! ### Weights of a translated module -/

omit [CharZero K] in
variable {P} in
/-- A weight of a submodule is a weight of the module. -/
theorem weightSpace_lieSubmodule_eq_bot (N : LieSubmodule K P.KacMoodyAlgebra V) {μ : Dual K H}
    (h : weightSpace P V μ = ⊥) : weightSpace P N μ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have hv' : (v : V) ∈ weightSpace P V μ := mem_weightSpaceOfMap_lieSubmodule_iff.mp hv
  rw [h] at hv'
  exact (Submodule.mem_bot K).mpr (Subtype.ext ((Submodule.mem_bot K).mp hv'))

/-- Translation preserves the category `𝒪`. -/
theorem IsCategoryO.centralTranslation (hV : IsCategoryO P V) (hZ : IsCategoryO P Z)
    (χ₁ χ₂ : 𝓩 →ₐ[K] K) : IsCategoryO P (centralTranslation P Z χ₁ χ₂ V) :=
  ((hV.centralBlock P χ₁).tensorProduct hZ).centralBlock P χ₂

omit [CharZero K] in
/-- If the weights of `Z` are `≤ ν` and the block `pr_{χ₁} V` has no weight `≥ y - ν`, then `y`
is not a weight of `T V = pr_{χ₂}(pr_{χ₁} V ⊗ Z)`. -/
theorem weightSpace_centralTranslation_eq_bot (hV : IsCategoryO P V) (hZ : IsCategoryO P Z)
    (χ₁ χ₂ : 𝓩 →ₐ[K] K) {ν y : Dual K H}
    (hZν : ∀ ν', weightSpace P Z ν' ≠ ⊥ → ν' ∈ cone P ν)
    (hQ : ∀ μ, y - ν ∈ cone P μ → weightSpace P (centralBlock P V χ₁) μ = ⊥) :
    weightSpace P (centralTranslation P Z χ₁ χ₂ V) y = ⊥ := by
  have hX : IsHDiagonalizable P (centralBlock P V χ₁) :=
    (hV.centralBlock P χ₁).iSup_weightSpaceOfMap_eq_top
  have hZd : IsHDiagonalizable P Z := hZ.iSup_weightSpaceOfMap_eq_top
  refine weightSpace_lieSubmodule_eq_bot _ ?_
  rw [weightSpace_tensorProduct hX hZd y]
  refine iSup_eq_bot.mpr fun μ ↦ LinearMap.range_eq_bot.mpr ?_
  by_cases hμ : weightSpace P (centralBlock P V χ₁) μ = ⊥
  · have h0 : (weightSpace P (centralBlock P V χ₁) μ).subtype = 0 := LinearMap.ext fun v ↦ by
      have hv : (v : centralBlock P V χ₁) ∈ (⊥ : Submodule K (centralBlock P V χ₁)) := by
        rw [← hμ]
        exact v.2
      exact (Submodule.mem_bot K).mp hv
    rw [h0, TensorProduct.map_zero_left]
  · have hZμ : weightSpace P Z (y - μ) = ⊥ := by
      by_contra hne
      obtain ⟨k, hk, hke⟩ := hZν _ hne
      refine hμ (hQ μ ⟨k, hk, ?_⟩)
      rw [sub_eq_sub_iff_add_eq_add] at hke ⊢
      rw [hke, add_comm]
    have h0 : (weightSpace P Z (y - μ)).subtype = 0 := LinearMap.ext fun v ↦ by
      have hv : (v : Z) ∈ (⊥ : Submodule K Z) := by
        rw [← hZμ]
        exact v.2
      exact (Submodule.mem_bot K).mp hv
    rw [h0, TensorProduct.map_zero_right]

/-! ### Translation and local composition series -/

section Exact

variable [IsAlgClosed K]

set_option maxHeartbeats 400000 in
-- Unifying the instances of the translated subquotients is expensive.
/-- For submodules `N ≤ N'` of a module in `𝒪`:
`[T N' : L(y)] = [T N : L(y)] + [T (N'/N) : L(y)]`, by exactness of translation. -/
theorem multiplicity_centralTranslation_subquotient (hV : IsCategoryO P V)
    (hZ : IsCategoryO P Z) (χ₁ χ₂ : 𝓩 →ₐ[K] K) {N N' : LieSubmodule K P.KacMoodyAlgebra V}
    (h : N ≤ N') (y : Dual K H) :
    ((hV.lieSubmodule N').centralTranslation P hZ χ₁ χ₂).multiplicity y =
      ((hV.lieSubmodule N).centralTranslation P hZ χ₁ χ₂).multiplicity y +
        (((hV.lieSubmodule N').quotient (N.comap N'.incl)).centralTranslation P hZ
          χ₁ χ₂).multiplicity y := by
  let f : N →ₗ⁅K,P.KacMoodyAlgebra⁆ N' := LieSubmodule.inclusion h
  let g : N' →ₗ⁅K,P.KacMoodyAlgebra⁆ N' ⧸ N.comap N'.incl :=
    LieSubmodule.Quotient.mk' (N.comap N'.incl)
  have hf : Function.Injective f := LieSubmodule.inclusion_injective h
  have hg : Function.Surjective g := LieSubmodule.Quotient.surjective_mk' _
  have hex : g.ker = f.range := by
    rw [LieSubmodule.Quotient.mk'_ker]
    ext x
    rw [LieSubmodule.mem_comap, LieModuleHom.mem_range]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    · rintro ⟨m, rfl⟩
      exact m.2
  obtain ⟨hTf, hTex, hTg⟩ := centralTranslationMap_shortExact P Z (hV.lieSubmodule N') hZ f g
    hf hex hg χ₁ χ₂
  exact IsCategoryO.multiplicity_eq_add_of_exact _ _ _ _ _ hTf hTex hTg y

set_option maxHeartbeats 1600000 in
-- Unifying the instances of the translated subquotients is expensive.
/-- Along a local composition series for `y - ν` from `N` to `M` (the weights of `Z` being
`≤ ν`): `[T M : L(y)] = [T N : L(y)] + ∑_η [T L(η) : L(y)]`, the sum over the irreducible
factors `L(η)` of the series. -/
theorem multiplicity_centralTranslation_of_isLocalCompositionSeries (hV : IsCategoryO P V)
    (hZ : IsCategoryO P Z) (χ₁ χ₂ : 𝓩 →ₐ[K] K) {ν y : Dual K H}
    (hZν : ∀ ν', weightSpace P Z ν' ≠ ⊥ → ν' ∈ cone P ν)
    {N M : LieSubmodule K P.KacMoodyAlgebra V}
    {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P (y - ν) N l M) :
    ((hV.lieSubmodule M).centralTranslation P hZ χ₁ χ₂).multiplicity y =
      ((hV.lieSubmodule N).centralTranslation P hZ χ₁ χ₂).multiplicity y +
        ((factorWeights l).map fun η ↦
          ((IrreducibleModule.isCategoryO P η).centralTranslation P hZ χ₁ χ₂).multiplicity
            y).sum := by
  induction l generalizing N with
  | nil =>
    obtain rfl := IsLocalCompositionSeries.nil_iff.mp hl
    simp
  | cons a l ih =>
    obtain ⟨N', o⟩ := a
    obtain ⟨h, hfac, hl'⟩ := IsLocalCompositionSeries.cons_iff.mp hl
    rw [ih hl', multiplicity_centralTranslation_subquotient P hV hZ χ₁ χ₂ h y, add_assoc]
    congr 1
    cases o with
    | none =>
      rw [factorWeights_cons_none]
      have h0 : weightSpace P (centralTranslation P Z χ₁ χ₂ (N.Subquotient N')) y = ⊥ :=
        weightSpace_centralTranslation_eq_bot P ((hV.lieSubmodule N').quotient _) hZ χ₁ χ₂ hZν
          fun μ hμ ↦ weightSpace_lieSubmodule_eq_bot _ (hfac μ hμ)
      rw [IsCategoryO.multiplicity_eq_zero_of_weightSpace_eq_bot _ h0, zero_add]
    | some η =>
      obtain ⟨-, ⟨e⟩⟩ := hfac
      rw [factorWeights_cons_some, List.map_cons, List.sum_cons]
      congr 1
      exact IsCategoryO.multiplicity_congr _ _ (centralTranslationEquiv P Z χ₁ χ₂ e) y

/-- **Translation on the Grothendieck group.** For `V` in `𝒪`, a coefficient module `Z` in `𝒪`
with weights `≤ ν`, and a local composition series `l` of `V` for the weight `y - ν`:
`[T V : L(y)] = ∑_η [T L(η) : L(y)]`, the sum over the irreducible factors `L(η)` of `l` (each
`η` occurring `[V : L(η)]` times). -/
theorem multiplicity_centralTranslation_eq_sum (hV : IsCategoryO P V) (hZ : IsCategoryO P Z)
    (χ₁ χ₂ : 𝓩 →ₐ[K] K) {ν y : Dual K H}
    (hZν : ∀ ν', weightSpace P Z ν' ≠ ⊥ → ν' ∈ cone P ν)
    {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P (y - ν) (⊥ : LieSubmodule K P.KacMoodyAlgebra V) l ⊤) :
    (hV.centralTranslation P hZ χ₁ χ₂).multiplicity y =
      ((factorWeights l).map fun η ↦
        ((IrreducibleModule.isCategoryO P η).centralTranslation P hZ χ₁ χ₂).multiplicity
          y).sum := by
  have h := multiplicity_centralTranslation_of_isLocalCompositionSeries P hV hZ χ₁ χ₂ hZν hl
  have hbot : ((hV.lieSubmodule ⊥).centralTranslation P hZ χ₁ χ₂).multiplicity y = 0 :=
    IsCategoryO.multiplicity_eq_zero_of_weightSpace_eq_bot _
      (weightSpace_centralTranslation_eq_bot P (hV.lieSubmodule ⊥) hZ χ₁ χ₂ hZν fun μ _ ↦
        eq_bot_iff.mpr fun v _ ↦ (Submodule.mem_bot K).mpr
          (Subtype.ext (Subtype.ext ((LieSubmodule.mem_bot _).mp v.1.2))))
  let e : (⊤ : LieSubmodule K P.KacMoodyAlgebra V) ≃ₗ⁅K,P.KacMoodyAlgebra⁆ V :=
    LieModuleEquiv.ofBijective (⊤ : LieSubmodule K P.KacMoodyAlgebra V).incl
      ⟨Subtype.val_injective, fun v ↦ ⟨⟨v, LieSubmodule.mem_top v⟩, rfl⟩⟩
  rw [← IsCategoryO.multiplicity_congr ((hV.lieSubmodule ⊤).centralTranslation P hZ χ₁ χ₂) _
    (centralTranslationEquiv P Z χ₁ χ₂ e) y, h, hbot, zero_add]

end Exact

end Matrix.Realization.KacMoodyAlgebra
