/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationComposite
import LieLean.Algebra.Lie.KacMoody.TranslationShuffling
import LieLean.Algebra.Lie.KacMoody.TranslationWallCrossing

/-!
# Translation within a facet is an equivalence of blocks

Humphreys, GSM 94, Theorem 7.8: if `λ`, `μ` are antidominant and compatible and `λ♮`, `μ♮` lie in
the same facet, then `T_λ^μ` and `T_μ^λ` are inverse equivalences between the blocks `𝒪_λ` and
`𝒪_μ`. Here: for `T = pr_{χ_λ}(pr_{χ_μ}(−) ⊗ L(ν))` (`ν = z (λ - μ)` dominant integral) and its
adjoint `T' = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν)^*)`, the adjunction morphism
`η_V : V → T' T V` (`translationUnit`, natural in `V` by `translationUnit_naturality`) is bijective
for every `V ∈ 𝒪` in the block of `μ` (`bijective_translationUnit_of_sameFacet`). The roles of
`λ` and `μ` are symmetric, so the theorem applied to `μ, λ` and `L(ν)^* ≅ L(ν')` (`ν'` dominant
in `W(μ - λ)`, `IrreducibleModule.exists_equiv_dual`) gives the other composite.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.bijective_of_injective_of_character_eq`:
  an injective morphism between modules in `𝒪` with equal characters is bijective.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.subsingleton_of_character_eq_zero`.
* `Matrix.Realization.KacMoodyAlgebra.stabilizerIndex_eq_one`: `|W_μ°/W_λ°| = 1` when
  `λ♮`, `μ♮` lie in the same facet.
* `Matrix.Realization.KacMoodyAlgebra.character_translation_translation_of_sameFacet`:
  `ch T' T V = ch V` (Corollary 7.12).
* `Matrix.Realization.KacMoodyAlgebra.bijective_translationUnit_of_sameFacet`: Theorem 7.8,
  the natural isomorphism `id ≅ T' T` on the block of `μ`.

## Proof

Humphreys proves that the adjunction morphism `T' T M → M` is an isomorphism by induction on
the length of `M` and the five lemma. Here (reconstructed): the kernel `K` of `η_V` satisfies
`T'(T(K ↪ V)) ∘ η_K = η_V|_K = 0` by naturality, and `T' T` preserves injections, so `η_K = 0`,
i.e. `T K = 0`; as `ch T' T K = ch K` (Corollary 7.12, with `|W_μ°/W_λ°| = 1`), `K = 0`. So `η_V`
is injective, and `ch T' T V = ch V` makes it bijective.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.8, §7.12.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Generic

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V W : Type*}
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]

/-- An injective morphism between modules in `𝒪` with equal characters is bijective. -/
theorem IsCategoryO.bijective_of_injective_of_character_eq (hV : IsCategoryO P V)
    (hW : IsCategoryO P W) (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (hf : Function.Injective f)
    (hch : hV.character = hW.character) : Function.Bijective f := by
  refine ⟨hf, fun w ↦ ?_⟩
  have hw : w ∈ ⨆ μ, weightSpaceOfMap W (h P) μ := hW.iSup_weightSpaceOfMap_eq_top ▸ trivial
  suffices hsub : ⨆ μ, weightSpaceOfMap W (h P) μ ≤ LinearMap.range (f : V →ₗ[K] W) by
    obtain ⟨v, hv⟩ := hsub hw
    exact ⟨v, hv⟩
  refine iSup_le fun μ ↦ ?_
  intro y hy
  have := hV.finiteDimensional_weightSpaceOfMap μ
  have := hW.finiteDimensional_weightSpaceOfMap μ
  let g : weightSpaceOfMap V (h P) μ →ₗ[K] weightSpaceOfMap W (h P) μ :=
    (f : V →ₗ[K] W).restrict fun v hv ↦ map_mem_weightSpaceOfMap P f hv
  have hg : Function.Injective g := fun a b hab ↦
    Subtype.ext (hf (congrArg Subtype.val hab))
  have hdim : finrank K (weightSpaceOfMap V (h P) μ) = finrank K (weightSpaceOfMap W (h P) μ) := by
    have := congrArg (fun c ↦ c.coeffAt μ) hch
    simp only [coeffAt_character] at this
    exact_mod_cast this
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hg ⟨y, hy⟩
  exact ⟨v, congrArg Subtype.val hv⟩

/-- A module in `𝒪` with zero character is zero. -/
theorem IsCategoryO.subsingleton_of_character_eq_zero (hV : IsCategoryO P V)
    (h0 : hV.character = 0) : Subsingleton V := by
  have hμ : ∀ μ, weightSpaceOfMap V (h P) μ = ⊥ := fun μ ↦ by
    have := hV.finiteDimensional_weightSpaceOfMap μ
    have h1 : ((finrank K (weightSpaceOfMap V (h P) μ) : ℕ) : ℤ) = 0 := by
      rw [← IsCategoryO.coeffAt_character hV μ, h0]
      rfl
    exact Submodule.finrank_eq_zero.mp (by exact_mod_cast h1)
  have htop := hV.iSup_weightSpaceOfMap_eq_top
  simp only [hμ, iSup_bot] at htop
  refine ⟨fun a b ↦ ?_⟩
  have ha : a ∈ (⊥ : Submodule K V) := htop ▸ Submodule.mem_top
  have hb : b ∈ (⊥ : Submodule K V) := htop ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at ha hb
  rw [ha, hb]

/-- A zero module has zero character. -/
theorem IsCategoryO.character_eq_zero_of_subsingleton (hV : IsCategoryO P V) [Subsingleton V] :
    hV.character = 0 := by
  ext μ
  simp only [coeffAt_character, HahnSeries.coeff_zero]
  exact_mod_cast Module.finrank_zero_of_subsingleton

end Generic

section SameFacet

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

omit [IsAlgClosed K] [FiniteDimensional K H] in
include hA in
/-- If every positive root orthogonal to `μ + ρ` is orthogonal to `λ + ρ`, then `W_μ° ⊆ W_λ°`, so
`|W_μ°/W_λ°| = 1`. -/
theorem stabilizerIndex_eq_one {lam μ : Dual K H}
    (hfacet' : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0) :
    stabilizerIndex P hA.isGeneralizedCartan lam μ = 1 := by
  have hA' := hA.isGeneralizedCartan
  have hset : {y | ∃ w' : P.weylGroup hA', P.weylDot hA' w' μ = μ ∧ y = P.weylDot hA' w' lam} =
      {lam} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w', hw', rfl⟩
      have hfixm : (w' : Dual K H ≃ₗ[K] Dual K H) (μ + P.rho) = μ + P.rho := by
        have := congrArg (· + P.rho) hw'
        simpa [weylDot] using this
      have hfixl : (w' : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) = lam + P.rho := by
        refine (apply_eq_self_iff_mem_closure_reflectionOf hA (lam + P.rho) _).mpr
          (Subgroup.closure_mono ?_ ((apply_eq_self_iff_mem_closure_reflectionOf hA
            (μ + P.rho) _).mp hfixm))
        rintro _ ⟨v', i', h0, rfl⟩
        refine ⟨v', i', ?_, rfl⟩
        rcases isPosRoot_or v' i' with hp | hp
        · exact hfacet' v' i' hp h0
        · have := hfacet' _ _ hp (by rw [corootPairing_mul_simple, h0, neg_zero])
          rwa [corootPairing_mul_simple, neg_eq_zero] at this
      simp [weylDot, hfixl]
    · rintro rfl
      exact ⟨1, by simp [weylDot], by simp [weylDot]⟩
  rw [stabilizerIndex, hset]
  simp

include hA in
/-- **`ch T' T V = ch V` within a facet** (Humphreys, GSM 94, Corollary 7.12 with
`|W_μ°/W_λ°| = 1`). For `λ`, `μ` antidominant with the same positive roots orthogonal to `λ + ρ`
and `μ + ρ`, `ν = z (λ - μ)` dominant integral, `T = pr_{χ_λ}(pr_{χ_μ}(−) ⊗ L(ν))`,
`T' = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν)^*)`, `V ∈ 𝒪` in the block of `μ` and `X ≅ T V`:
`ch T' X = ch V`. -/
theorem character_translation_translation_of_sameFacet {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hfacet' : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    {V X : Type*} [AddCommGroup V] [Module K V] [LieRingModule 𝔤 V] [LieModule K 𝔤 V]
    [AddCommGroup X] [Module K X] [LieRingModule 𝔤 X] [LieModule K 𝔤 X]
    (hV : IsCategoryO P V) (hVμ : centralBlock P V (centralCharacter P μ) = ⊤)
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
      (centralCharacter P lam) V)
    (hT : IsCategoryO P (centralTranslation P (Module.Dual K (IrreducibleModule P ν))
      (centralCharacter P lam) (centralCharacter P μ) X)) :
    hT.character = hV.character := by
  have hA' := hA.isGeneralizedCartan
  obtain ⟨z', hz', hν', ⟨eν⟩⟩ := IrreducibleModule.exists_equiv_dual P hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have hzz : z' * z ∈ P.weylGroup hA' := mul_mem hz' hz
  have hzν' : (z' * z) (μ - lam) = z' (-ν) := by
    change z' (z (μ - lam)) = z' (-ν)
    rw [← hzν, ← map_neg, neg_sub]
  have hX : IsCategoryO P X :=
    IsCategoryO.of_equiv (P := P) (hV.centralTranslation P (IrreducibleModule.isCategoryO P ν)
      _ _) eX.symm
  have h1 := character_translation_translation P hA hlam hμ hfacet hν hz hzν hν' hzz hzν' hV hVμ
    hX eX
  rw [stabilizerIndex_eq_one P hA hfacet', one_smul] at h1
  rw [← h1]
  exact IsCategoryO.character_congr hT _ (centralTranslationCoeffEquiv P X _ _ eν)

include hA in
/-- **Translation within a facet is faithful**: for `V ∈ 𝒪` in the block of `μ`, `T V = 0` forces
`V = 0` (from `ch T' T V = ch V`). -/
theorem subsingleton_of_subsingleton_translation_of_sameFacet {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hfacet' : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule 𝔤 V] [LieModule K 𝔤 V]
    (hV : IsCategoryO P V) (hVμ : centralBlock P V (centralCharacter P μ) = ⊤)
    (h0 : Subsingleton (centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
      (centralCharacter P lam) V)) : Subsingleton V := by
  obtain ⟨z', hz', hν', ⟨eν⟩⟩ := IrreducibleModule.exists_equiv_dual P hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have hL' : IsCategoryO P (Module.Dual K (IrreducibleModule P ν)) :=
    IsCategoryO.of_equiv (P := P) (IrreducibleModule.isCategoryO P _) eν.symm
  have hT := (hV.centralTranslation P (IrreducibleModule.isCategoryO P ν) (centralCharacter P μ)
    (centralCharacter P lam)).centralTranslation P hL' (centralCharacter P lam)
      (centralCharacter P μ)
  have hc := character_translation_translation_of_sameFacet P hA hlam hμ hfacet hfacet' hν hz
    hzν hV hVμ LieModuleEquiv.refl hT
  have : Subsingleton (centralTranslation P (Module.Dual K (IrreducibleModule P ν))
      (centralCharacter P lam) (centralCharacter P μ) (centralTranslation P
        (IrreducibleModule P ν) (centralCharacter P μ) (centralCharacter P lam) V)) :=
    subsingleton_centralTranslation P _ _
  exact hV.subsingleton_of_character_eq_zero P (hc ▸ hT.character_eq_zero_of_subsingleton P)

include hA in
/-- **Translation within a facet is an equivalence** (Humphreys, GSM 94, Theorem 7.8, arbitrary
weights). Let `λ`, `μ` be antidominant with the same positive roots orthogonal to `λ + ρ` and to
`μ + ρ` (`λ♮`, `μ♮` in the same facet), `ν = z (λ - μ)` dominant integral (`z ∈ W`),
`T = pr_{χ_λ}(pr_{χ_μ}(−) ⊗ L(ν))` and `T' = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν)^*)` its adjoint. For
every `V ∈ 𝒪` in the block of `μ` (and `X ≅ T V`, e.g. `X = T V`), the adjunction morphism
(`L(ν)` is finite-dimensional, `IrreducibleModule.finiteDimensional`)
`η_V : V → T' T V` is bijective. As `η` is natural (`translationUnit_naturality`), this is a
natural isomorphism `id ≅ T' T` on the block of `μ`; exchanging `λ` and `μ` gives the other
composite. -/
theorem bijective_translationUnit_of_sameFacet {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hfacet' : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    {V X : Type*} [AddCommGroup V] [Module K V] [LieRingModule 𝔤 V] [LieModule K 𝔤 V]
    [AddCommGroup X] [Module K X] [LieRingModule 𝔤 X] [LieModule K 𝔤 X]
    (hV : IsCategoryO P V) (hVμ : centralBlock P V (centralCharacter P μ) = ⊤)
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
      (centralCharacter P lam) V)
    (hXχ : centralBlock P X (centralCharacter P lam) = ⊤)
    [FiniteDimensional K (IrreducibleModule P ν)] :
    Function.Bijective (translationUnit P hV (IrreducibleModule.isCategoryO P ν) hVμ eX hXχ) := by
  classical
  obtain ⟨z', hz', hν', ⟨eν⟩⟩ := IrreducibleModule.exists_equiv_dual P hA hν
  have hL := IrreducibleModule.isCategoryO P ν
  have hL' : IsCategoryO P (Module.Dual K (IrreducibleModule P ν)) :=
    IsCategoryO.of_equiv (P := P) (IrreducibleModule.isCategoryO P _) eν.symm
  have hX : IsCategoryO P X :=
    IsCategoryO.of_equiv (P := P) (hV.centralTranslation P hL _ _) eX.symm
  have hT := hX.centralTranslation P hL' (centralCharacter P lam) (centralCharacter P μ)
  have hch := character_translation_translation_of_sameFacet P hA hlam hμ hfacet hfacet' hν hz
    hzν hV hVμ eX hT
  refine hV.bijective_of_injective_of_character_eq P hT _ ?_ hch.symm
  -- the kernel `K` of `η_V`
  let Kk := (translationUnit P hV hL hVμ eX hXχ).ker
  have hK : IsCategoryO P Kk := hV.lieSubmodule Kk
  have hKμ : centralBlock P Kk (centralCharacter P μ) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hx : (x : V) ∈ centralBlock P V (centralCharacter P μ) := by
      rw [hVμ]; exact LieSubmodule.mem_top _
    exact mem_centralBlock_of_injective P Kk.incl Subtype.val_injective _ hx
  -- `η_V ∘ (K ↪ V) = adj(eX⁻¹ ∘ T(K ↪ V)) = 0` forces `T(K ↪ V) = 0`, so `T K = 0`
  have hnat := translationAdjunction_comp_left P hK hV hL hKμ hVμ hXχ Kk.incl
    eX.symm.toLieModuleHom
  have h0 : (translationAdjunction P hV hL hVμ hXχ eX.symm.toLieModuleHom).comp Kk.incl = 0 :=
    LieModuleHom.ext fun x ↦ x.2
  have hzero := (LinearEquiv.map_eq_zero_iff _).mp (hnat.symm.trans h0)
  have hinj := centralTranslationMap_injective P (Z := IrreducibleModule P ν)
    (centralCharacter P μ) (centralCharacter P lam) Kk.incl Subtype.val_injective
  have hsubTK : Subsingleton (centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
      (centralCharacter P lam) Kk) := by
    refine ⟨fun a b ↦ hinj (eX.symm.injective ?_)⟩
    have ha := LieModuleHom.congr_fun hzero a
    have hb := LieModuleHom.congr_fun hzero b
    exact ha.trans hb.symm
  have hsubK : Subsingleton Kk := subsingleton_of_subsingleton_translation_of_sameFacet P hA hlam
    hμ hfacet hfacet' hν hz hzν hK hKμ hsubTK
  refine (injective_iff_map_eq_zero _).mpr fun v hv ↦ ?_
  exact congrArg Subtype.val (Subsingleton.elim (⟨v, hv⟩ : Kk) 0)

end SameFacet

end Matrix.Realization.KacMoodyAlgebra
