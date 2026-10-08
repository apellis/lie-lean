/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.RelativeExt
import LieLean.Algebra.Lie.KacMoody.TranslationWallHead

/-!
# `Ext¹` and translation from a wall

Humphreys, GSM 94, Theorem 7.14 (g): in the setting of §7.14 (`λ` regular antidominant, `μ♮` on
the single wall `H_α` of the chamber of `λ♮`, `s = s_α`, `w α > 0`), if `x ∈ W_[λ]` and
`xs·λ < x·λ`, then
`Ext¹_𝒪(L(w·λ), L(x·λ)) ≅ Hom_𝒪(Rad T_μ^λ L(w·μ), L(x·λ))`.

`Ext¹` is `LieModule.ExtOne` relative to the Cartan subalgebra (`LieLean.Algebra.Lie.RelativeExt`):
classes of extensions in which `𝔥` acts semisimply, which for modules in `𝒪` are exactly the
extensions in `𝒪` (`IsCategoryO.extension`), with the splitting criterion
`LieModule.ExtOne.mk_eq_zero_iff` and the connecting isomorphism
`LieModule.ExtOne.SplitData.connectingEquiv`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.extension`,
  `Matrix.Realization.KacMoodyAlgebra.centralBlock_extension_eq_top`: extensions of modules in
  `𝒪` (in a block) lie in `𝒪` (in that block).
* `Matrix.Realization.KacMoodyAlgebra.translationAdjunction_comp`: naturality of the translation
  adjunction `Hom(T M, N) ≅ Hom(M, T' N)` in `N`.
* `Matrix.Realization.KacMoodyAlgebra.extOne_eq_zero_of_subsingleton_centralTranslation`:
  `Ext¹(T M, N) = 0` when `T' N = 0` ("by adjointness").
* `Matrix.Realization.KacMoodyAlgebra.nonempty_hom_ker_equiv_extOne`: for a surjection
  `p : T M → S` and `T' N = 0`, `Hom(ker p, N) ≅ Ext¹(S, N)`.
* `Matrix.Realization.KacMoodyAlgebra.nonempty_hom_ker_equiv_extOne_wall`: Theorem 7.14 (g).
* `Matrix.Realization.KacMoodyAlgebra.exists_surjective_translation_irreducible_wall`: the
  surjection `T_μ^λ L(w·μ) → L(w·λ)` (head, Theorem 7.14 (c)).

## Proof

As in Humphreys: `T_λ^μ L(x·λ) = 0` (Theorem 7.9), so `Hom` and `Ext¹` from `T_μ^λ L(w·μ)` to
`L(x·λ)` vanish by adjointness, and the long exact sequence of
`0 → Rad → T_μ^λ L(w·μ) → L(w·λ) → 0` gives the isomorphism. The vanishing of `Ext¹` is proved by
splitting extensions: `T'` is exact and kills `L(x·λ)`, so for an extension `E` of `T M` by `N`
the unit `M → T' T M ≅ T' E` is adjoint to a section `T M → E`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.1, §7.2, §7.14.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Generic

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {M N N' L : Type*}
  [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M]
  [AddCommGroup N] [Module K N] [LieRingModule P.KacMoodyAlgebra N]
  [LieModule K P.KacMoodyAlgebra N]
  [AddCommGroup N'] [Module K N'] [LieRingModule P.KacMoodyAlgebra N']
  [LieModule K P.KacMoodyAlgebra N']
  [AddCommGroup L] [Module K L] [LieRingModule P.KacMoodyAlgebra L]
  [LieModule K P.KacMoodyAlgebra L]

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

/-- An extension of modules in `𝒪` by a relative cocycle lies in `𝒪`. -/
theorem IsCategoryO.extension (hN : IsCategoryO P N) (hM : IsCategoryO P M)
    (c : extCocycles (h P) M N) : IsCategoryO P (ExtOne.Extension c) where
  iSup_weightSpaceOfMap_eq_top :=
    ExtOne.Extension.iSup_weightSpaceOfMap_eq_top c hN.1 hM.1
  finiteDimensional_weightSpaceOfMap μ := by
    have := hN.2 μ
    have := hM.2 μ
    exact Module.Finite.of_injective _ (ExtOne.Extension.injective_weightSpaceMap c μ)
  exists_finset := by
    classical
    obtain ⟨s, hs⟩ := hN.3
    obtain ⟨t, ht⟩ := hM.3
    refine ⟨s ∪ t, fun μ hμ ↦ ?_⟩
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
    rw [ExtOne.Extension.mem_weightSpaceOfMap_iff] at hv
    by_cases h1 : (ExtOne.Extension.equiv c v).1 = 0
    · have h2 : (ExtOne.Extension.equiv c v).2 ≠ 0 := fun h2 ↦ hv0
        ((ExtOne.Extension.ext_iff' c).mpr ⟨by rw [h1, map_zero]; rfl, by rw [h2, map_zero]; rfl⟩)
      obtain ⟨Λ, hΛ, h⟩ := ht μ fun hb ↦ h2 ((Submodule.eq_bot_iff _).mp hb _ hv.2)
      exact ⟨Λ, Finset.mem_union_right _ hΛ, h⟩
    · obtain ⟨Λ, hΛ, h⟩ := hs μ fun hb ↦ h1 ((Submodule.eq_bot_iff _).mp hb _ hv.1)
      exact ⟨Λ, Finset.mem_union_left _ hΛ, h⟩

/-- An extension of two modules in the block `χ` lies in the block `χ`. -/
theorem centralBlock_extension_eq_top {χ : 𝓩 →ₐ[K] K} (hN : centralBlock P N χ = ⊤)
    (hM : centralBlock P M χ = ⊤) (c : extCocycles (h P) M N) :
    centralBlock P (ExtOne.Extension c) χ = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  rw [mem_centralBlock]
  intro z
  obtain ⟨a, ha⟩ := (mem_centralBlock P χ _).mp
    (hM ▸ LieSubmodule.mem_top (ExtOne.Extension.snd c v)) z
  have h1 : ExtOne.Extension.snd c
      (((rep P (ExtOne.Extension c) (z : 𝓤) - χ z • 1) ^ a) v) = 0 := by
    rw [map_rep_center_sub_pow]; exact ha
  obtain ⟨n, hn⟩ := ExtOne.Extension.exists_inl_eq_of_snd_eq_zero c h1
  obtain ⟨b, hb⟩ := (mem_centralBlock P χ n).mp (hN ▸ LieSubmodule.mem_top n) z
  refine ⟨b + a, ?_⟩
  rw [pow_add, Module.End.mul_apply, ← hn, ← map_rep_center_sub_pow, hb, map_zero]

variable [FiniteDimensional K L]

/-- Naturality of `N ⊗ L^* ≅ Hom_K(L, N)` in `N`. -/
theorem tensorDualEquivHom_map (q : N →ₗ⁅K,𝔤⁆ N') (t : N ⊗[K] Module.Dual K L) :
    tensorDualEquivHom P N' L (TensorProduct.LieModule.map q LieModuleHom.id t) =
      (q : N →ₗ[K] N') ∘ₗ tensorDualEquivHom P N L t := by
  induction t with
  | tmul n f =>
    ext l
    simp [tensorDualEquivHom]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, LinearMap.comp_add]

variable [CharZero K] [IsAlgClosed K]

omit [FiniteDimensional K L] [CharZero K] [IsAlgClosed K] in
/-- `(e ⊗ 1) ∘ (e⁻¹ ⊗ 1) = 1`. -/
theorem rTensorEquiv_apply_symm_apply {V W : Type*} [AddCommGroup V] [Module K V]
    [LieRingModule 𝔤 V] [LieModule K 𝔤 V] [AddCommGroup W] [Module K W] [LieRingModule 𝔤 W]
    [LieModule K 𝔤 W] (e : V ≃ₗ⁅K,𝔤⁆ W) (z : W ⊗[K] L) :
    rTensorEquiv P L e (rTensorEquiv P L e.symm z) = z := by
  induction z with
  | tmul a b => change e (e.symm a) ⊗ₜ b = a ⊗ₜ b; rw [e.apply_symm_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [FiniteDimensional K L] [CharZero K] [IsAlgClosed K] in
/-- Block restriction of `q ⊗ 1` is compatible with the identifications of the blocks. -/
theorem rTensorEquiv_map_centralBlockMap {χ : 𝓩 →ₐ[K] K} (hN : centralBlock P N χ = ⊤)
    (hN' : centralBlock P N' χ = ⊤) (q : N →ₗ⁅K,𝔤⁆ N') (t : centralBlock P N χ ⊗[K] L) :
    rTensorEquiv P L (equivCentralBlockOfEqTop P hN')
      (TensorProduct.LieModule.map (centralBlockMap P q χ) LieModuleHom.id t) =
      TensorProduct.LieModule.map q LieModuleHom.id
        (rTensorEquiv P L (equivCentralBlockOfEqTop P hN) t) := by
  induction t with
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]


/-- **Naturality of the translation adjunction** in the second variable:
`adj (q ∘ f) = T'(q) ∘ adj f` (Humphreys, GSM 94, §7.2). -/
theorem translationAdjunction_comp (hM : IsCategoryO P M) (hL : IsCategoryO P L)
    {χ₁ χ₂ : 𝓩 →ₐ[K] K} (hMχ : centralBlock P M χ₁ = ⊤) (hNχ : centralBlock P N χ₂ = ⊤)
    (hNχ' : centralBlock P N' χ₂ = ⊤) (q : N →ₗ⁅K,𝔤⁆ N')
    (f : centralTranslation P L χ₁ χ₂ M →ₗ⁅K,𝔤⁆ N) :
    translationAdjunction P hM hL hMχ hNχ' (q.comp f) =
      (centralTranslationMap P (Module.Dual K L) χ₂ χ₁ q).comp
        (translationAdjunction P hM hL hMχ hNχ f) := by
  ext m
  apply (rTensorEquiv P (Module.Dual K L) (equivCentralBlockOfEqTop P hNχ')).injective
  apply (tensorDualEquivHom P N' L).injective
  change tensorDualEquivHom P N' L (rTensorEquiv P (Module.Dual K L)
      (equivCentralBlockOfEqTop P hNχ')
        (rTensorEquiv P (Module.Dual K L) (equivCentralBlockOfEqTop P hNχ').symm _)) =
    tensorDualEquivHom P N' L (rTensorEquiv P (Module.Dual K L) (equivCentralBlockOfEqTop P hNχ')
      (TensorProduct.LieModule.map (centralBlockMap P q χ₂) LieModuleHom.id
        (rTensorEquiv P (Module.Dual K L) (equivCentralBlockOfEqTop P hNχ).symm _)))
  rw [rTensorEquiv_apply_symm_apply, rTensorEquiv_map_centralBlockMap P hNχ hNχ',
    rTensorEquiv_apply_symm_apply, tensorDualEquivHom_map]
  change tensorDualEquivHom P N' L ((tensorDualEquivHom P N' L).symm _) =
    (q : N →ₗ[K] N') ∘ₗ tensorDualEquivHom P N L ((tensorDualEquivHom P N L).symm _)
  rw [LieModuleEquiv.apply_symm_apply, LieModuleEquiv.apply_symm_apply]
  ext l
  rfl

/-- `Hom(T M, N) = 0` if `T' N = 0`, `T'` the right adjoint of `T` (Humphreys, GSM 94,
proof of Theorem 7.14 (g)). Stated for `X ≅ T M`. -/
theorem eq_zero_of_subsingleton_centralTranslation (hM : IsCategoryO P M) (hL : IsCategoryO P L)
    {χ₁ χ₂ : 𝓩 →ₐ[K] K} (hMχ : centralBlock P M χ₁ = ⊤) (hNχ : centralBlock P N χ₂ = ⊤)
    (h0 : Subsingleton (centralTranslation P (Module.Dual K L) χ₂ χ₁ N))
    {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule 𝔤 X] [LieModule K 𝔤 X]
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M) (g : X →ₗ⁅K,𝔤⁆ N) : g = 0 := by
  have : translationAdjunction P hM hL hMχ hNχ (g.comp eX.symm.toLieModuleHom) = 0 :=
    LieModuleHom.ext fun _ ↦ Subsingleton.elim _ _
  have h1 := (LinearEquiv.map_eq_zero_iff _).mp this
  ext x
  simpa using LieModuleHom.congr_fun h1 (eX x)

set_option maxHeartbeats 400000 in
-- Comparing the translated modules of the extension module is expensive.
/-- **`Ext¹(T M, N) = 0` if `T' N = 0`**, `T'` the right adjoint of `T` (Humphreys, GSM 94, proof
of Theorem 7.14 (g), "by adjointness"), stated for `X ≅ T M`. Every extension `0 → N → E → X → 0`
in `𝒪` splits: `T'` is exact and kills `N`, so `T'(E) ≅ T'(X)`, and `M → T' T M ≅ T' X` lifts to
`M → T' E`, whose adjoint gives a section. -/
theorem extOne_eq_zero_of_subsingleton_centralTranslation (hM : IsCategoryO P M)
    (hL : IsCategoryO P L) (hL' : IsCategoryO P (Module.Dual K L))
    {χ₁ χ₂ : 𝓩 →ₐ[K] K} (hMχ : centralBlock P M χ₁ = ⊤)
    (hN : IsCategoryO P N) (hNχ : centralBlock P N χ₂ = ⊤)
    (h0 : Subsingleton (centralTranslation P (Module.Dual K L) χ₂ χ₁ N))
    {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule 𝔤 X] [LieModule K 𝔤 X]
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M) (y : ExtOne (h P) X N) : y = 0 := by
  obtain ⟨c, rfl⟩ := ExtOne.mk_surjective y
  rw [ExtOne.mk_eq_zero_iff]
  have hTX : IsCategoryO P (centralTranslation P L χ₁ χ₂ M) := hM.centralTranslation P hL χ₁ χ₂
  have hX : IsCategoryO P X := IsCategoryO.of_equiv (P := P) hTX eX.symm
  have hTXχ : centralBlock P (centralTranslation P L χ₁ χ₂ M) χ₂ = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    exact mem_centralBlock_of_injective P (centralTranslation P L χ₁ χ₂ M).incl
      Subtype.val_injective χ₂ v.property
  have hXχ : centralBlock P X χ₂ = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hx : eX x ∈ centralBlock P (centralTranslation P L χ₁ χ₂ M) χ₂ := by
      rw [hTXχ]; exact LieSubmodule.mem_top _
    exact mem_centralBlock_of_injective P eX.toLieModuleHom eX.injective χ₂ hx
  have hE := IsCategoryO.extension P hN hX c
  have hEχ := centralBlock_extension_eq_top P hNχ hXχ c
  -- `T'` of the projection `E → X` is bijective
  have hex : (ExtOne.Extension.snd c).ker = (ExtOne.Extension.inl c).range := by
    ext v
    rw [LieModuleHom.mem_ker, LieModuleHom.mem_range]
    exact ⟨fun hv ↦ ExtOne.Extension.exists_inl_eq_of_snd_eq_zero c hv,
      fun ⟨n, hn⟩ ↦ hn ▸ rfl⟩
  obtain ⟨-, hker, hsurj⟩ := centralTranslationMap_shortExact P (Module.Dual K L) hE hL'
    (ExtOne.Extension.inl c) (ExtOne.Extension.snd c) (ExtOne.Extension.injective_inl c) hex
    (ExtOne.Extension.surjective_snd c) χ₂ χ₁
  have hinj : Function.Injective
      (centralTranslationMap P (Module.Dual K L) χ₂ χ₁ (ExtOne.Extension.snd c)) := by
    refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    have hx' : x ∈ (centralTranslationMap P (Module.Dual K L) χ₂ χ₁
        (ExtOne.Extension.snd c)).ker := hx
    rw [hker, LieModuleHom.mem_range] at hx'
    obtain ⟨y, rfl⟩ := hx'
    rw [Subsingleton.elim y 0, map_zero]
  obtain ⟨eT, heT⟩ : ∃ e : centralTranslation P (Module.Dual K L) χ₂ χ₁ (ExtOne.Extension c) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (Module.Dual K L) χ₂ χ₁ X,
      ∀ y, e y = centralTranslationMap P (Module.Dual K L) χ₂ χ₁ (ExtOne.Extension.snd c) y :=
    ⟨LieModuleEquiv.ofBijective _ ⟨hinj, hsurj⟩, fun _ ↦ rfl⟩
  -- the unit `M → T' T M`, transported to `M → T' X`
  obtain ⟨η, hη⟩ : ∃ η : M →ₗ⁅K,𝔤⁆ centralTranslation P (Module.Dual K L) χ₂ χ₁ X,
      η = (centralTranslationMap P (Module.Dual K L) χ₂ χ₁ eX.symm.toLieModuleHom).comp
        (translationAdjunction P hM hL hMχ hTXχ LieModuleHom.id) := ⟨_, rfl⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ' : centralTranslation P L χ₁ χ₂ M →ₗ⁅K,𝔤⁆ ExtOne.Extension c,
      translationAdjunction P hM hL hMχ hEχ σ' = eT.symm.toLieModuleHom.comp η :=
    ⟨(translationAdjunction P hM hL hMχ hEχ).symm _, LinearEquiv.apply_symm_apply _ _⟩
  have key : (ExtOne.Extension.snd c).comp σ' = eX.symm.toLieModuleHom.comp LieModuleHom.id := by
    have h2 := translationAdjunction_comp P hM hL hMχ hTXχ hXχ eX.symm.toLieModuleHom
      LieModuleHom.id
    apply (translationAdjunction P hM hL hMχ hXχ).injective
    rw [h2, ← hη, translationAdjunction_comp P hM hL hMχ hEχ hXχ, hσ']
    refine LieModuleHom.ext fun x ↦ ?_
    have h3 := heT (eT.symm (η x))
    rw [LieModuleEquiv.apply_symm_apply] at h3
    exact h3.symm
  refine ⟨σ'.comp eX.toLieModuleHom, fun x ↦ ?_⟩
  have := LieModuleHom.congr_fun key (eX x)
  simpa using this

/-- **The connecting isomorphism for translated modules** (Humphreys, GSM 94, proof of
Theorem 7.14 (g)). Let `p : X → S` be a surjection onto a module `S ∈ 𝒪`, with
`X ≅ T M = pr_{χ₂}(pr_{χ₁} M ⊗ L)`, and let `N ∈ 𝒪` lie in the block `χ₂` with `T' N = 0`,
`T' = pr_{χ₁}(pr_{χ₂}(−) ⊗ L^*)`. Then `Hom(ker p, N) ≅ Ext¹(S, N)`. -/
theorem nonempty_hom_ker_equiv_extOne (hM : IsCategoryO P M) (hL : IsCategoryO P L)
    (hL' : IsCategoryO P (Module.Dual K L)) {χ₁ χ₂ : 𝓩 →ₐ[K] K} (hMχ : centralBlock P M χ₁ = ⊤)
    (hN : IsCategoryO P N) (hNχ : centralBlock P N χ₂ = ⊤)
    (h0 : Subsingleton (centralTranslation P (Module.Dual K L) χ₂ χ₁ N))
    {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule 𝔤 X] [LieModule K 𝔤 X]
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P L χ₁ χ₂ M)
    {S : Type*} [AddCommGroup S] [Module K S] [LieRingModule 𝔤 S] [LieModule K 𝔤 S]
    (hS : IsCategoryO P S) (p : X →ₗ⁅K,𝔤⁆ S) (hp : Function.Surjective p) :
    Nonempty ((p.ker →ₗ⁅K,𝔤⁆ N) ≃ₗ[K] ExtOne (h P) S N) := by
  have hX : IsCategoryO P X :=
    IsCategoryO.of_equiv (P := P) (hM.centralTranslation P hL χ₁ χ₂) eX.symm
  obtain ⟨D⟩ := ExtOne.exists_splitData (h P) hX.1 hS.1 (i := p.ker.incl) (p := p)
    Subtype.val_injective hp fun b ↦ ⟨fun hb ↦ ⟨⟨b, hb⟩, rfl⟩, fun ⟨a, ha⟩ ↦ ha ▸ a.2⟩
  exact ⟨D.connectingEquiv
    (eq_zero_of_subsingleton_centralTranslation P hM hL hMχ hNχ h0 eX)
    (extOne_eq_zero_of_subsingleton_centralTranslation P hM hL hL' hMχ hN hNχ h0 eX)⟩

end Generic

section Wall

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

omit [IsAlgClosed K] [FiniteDimensional K H] in
include hA in
/-- With `⟨λ + ρ, α^∨⟩ = n < 0` (`α = v αᵢ`, `s = s_α`): if `xs·λ < x·λ` then `x α < 0`. -/
theorem not_isPosRoot_of_weylDot_mul_reflectionOf_lt {lam : Dual K H}
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} {n : ℤ} (hn0 : n < 0)
    (hn : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = n)
    {x : P.weylGroup hA.isGeneralizedCartan}
    (hlt : P.weylDot hA.isGeneralizedCartan (x * P.reflectionOf hA.isGeneralizedCartan v i) lam ∈
        cone P (P.weylDot hA.isGeneralizedCartan x lam) ∧
      P.weylDot hA.isGeneralizedCartan (x * P.reflectionOf hA.isGeneralizedCartan v i) lam ≠
        P.weylDot hA.isGeneralizedCartan x lam) :
    ¬P.IsPosRoot hA.isGeneralizedCartan (x * v) i := by
  rintro ⟨k, hk, hke⟩
  obtain ⟨⟨k', hk', he'⟩, hne⟩ := hlt
  have he : P.weylDot hA.isGeneralizedCartan (x * P.reflectionOf hA.isGeneralizedCartan v i) lam =
      P.weylDot hA.isGeneralizedCartan x lam + P.rootOf ((-n) • k) := by
    simp only [weylDot]
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, reflectionOf_apply', hn, map_sub, map_smul,
      ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hke, map_zsmul, ← Int.cast_smul_eq_zsmul K]
    push_cast
    module
  rw [he] at he' hne
  have h0 : P.rootOf ((-n) • k + k') = 0 := by
    rw [map_add, ← sub_eq_zero.mpr he']
    abel
  have h1 : (-n) • k + k' = 0 := P.rootOf_injective (h0.trans (map_zero _).symm)
  have hk0 : k = 0 := by
    ext j
    have := congrFun h1 j
    have hj := hk j
    have hj' := hk' j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hj hj' ⊢
    nlinarith
  exact hne (by rw [hk0, smul_zero, map_zero, add_zero])

include hA in
/-- **Humphreys, GSM 94, Theorem 7.14 (g)**, arbitrary weights. Let `λ`, `μ` be antidominant with
every positive root orthogonal to `λ + ρ` orthogonal to `μ + ρ`, `ν = z (λ - μ)` (`z ∈ W`)
dominant integral, `α = v αᵢ > 0` with `⟨μ + ρ, α^∨⟩ = 0 ≠ ⟨λ + ρ, α^∨⟩`, `s = s_α`, and
`T_μ^λ = pr_{χ_λ}(pr_{χ_μ}(−) ⊗ L(ν))`. Let `p : X → L(w·λ)` be surjective, `X ≅ T_μ^λ L(w·μ)` (its
kernel is `Rad T_μ^λ L(w·μ)`: by Theorem 7.14 (b), (c) the head is `L(w·λ)`; such `p` exist by
`exists_surjective_translation_irreducible_wall`). If `x ∈ W_[λ]` and `xs·λ < x·λ`, then
`Ext¹_𝒪(L(w·λ), L(x·λ)) ≅ Hom_𝒪(Rad T_μ^λ L(w·μ), L(x·λ))`.

`Ext¹` is `LieModule.ExtOne` relative to the Cartan subalgebra (the Yoneda `Ext¹` of extensions
in which `𝔥` acts semisimply; for modules in `𝒪` these are the extensions in `𝒪`). As in
Humphreys: `T_λ^μ L(x·λ) = 0` by Theorem 7.9, so by adjointness `Hom` and `Ext¹` from
`T_μ^λ L(w·μ)` to `L(x·λ)` vanish, and the long exact sequence of
`0 → Rad → T_μ^λ L(w·μ) → L(w·λ) → 0` gives the isomorphism (the connecting map). The hypotheses
on `w` (`w α > 0`, `w ∈ W_[λ]`, `±α` the only roots orthogonal to `μ + ρ`) are only needed for the
existence of `p` and the identification of its kernel with the radical. -/
theorem nonempty_hom_ker_equiv_extOne_wall {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    (w : P.weylGroup hA.isGeneralizedCartan)
    {x : P.weylGroup hA.isGeneralizedCartan}
    (hxint : x ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    (hlt : P.weylDot hA.isGeneralizedCartan (x * P.reflectionOf hA.isGeneralizedCartan v i) lam ∈
        cone P (P.weylDot hA.isGeneralizedCartan x lam) ∧
      P.weylDot hA.isGeneralizedCartan (x * P.reflectionOf hA.isGeneralizedCartan v i) lam ≠
        P.weylDot hA.isGeneralizedCartan x lam)
    {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule 𝔤 X] [LieModule K 𝔤 X]
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
        (centralCharacter P lam) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ)))
    (p : X →ₗ⁅K,𝔤⁆ IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))
    (hp : Function.Surjective p) :
    Nonempty ((p.ker →ₗ⁅K,𝔤⁆ IrreducibleModule P (P.weylDot hA.isGeneralizedCartan x lam))
      ≃ₗ[K] ExtOne (h P) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))
        (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan x lam))) := by
  classical
  have hA' := hA.isGeneralizedCartan
  obtain ⟨z', hz', hν', ⟨eν⟩⟩ := IrreducibleModule.exists_equiv_dual P hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have hzz : z' * z ∈ P.weylGroup hA' := mul_mem hz' hz
  have hzν' : (z' * z) (μ - lam) = z' (-ν) := by
    change z' (z (μ - lam)) = z' (-ν)
    rw [← hzν, ← map_neg, neg_sub]
  set s := P.reflectionOf hA' v i with hs
  have hint := sub_rho_integral P hA hν' hzz hzν'
  obtain ⟨n, hn⟩ := (P.isIntegralRoot_congr _ hint v i).mpr ⟨0, by rw [Int.cast_zero]; exact hμα⟩
  change P.corootPairing _ (lam + P.rho) v i = n at hn
  have hn0 : n < 0 := lt_of_le_of_ne (hlam v i hv n hn)
    (by rintro rfl; exact hlamα (by simp [hn]))
  have hx := not_isPosRoot_of_weylDot_mul_reflectionOf_lt P hA hn0 hn hlt
  -- `x = x' s` with `x' α > 0`, so `x·μ` is not in the upper closure of the facet of `x·λ`
  have hss : s * s = 1 := reflectionOf_mul_self v i
  have hx' : P.IsPosRoot hA' ((x * s) * v) i := by
    have hsv : s * v = v * (P.coxeterSystem hA').simple i := by
      have hsimp : (⟨P.reflection hA' i, P.reflection_mem_weylGroup hA' i⟩ : P.weylGroup hA') =
          (P.coxeterSystem hA').simple i := by
        ext1
        simp
      rw [hs, reflectionOf, ← hsimp]
      group
    rw [mul_assoc, hsv, ← mul_assoc]
    exact (isPosRoot_or (x * v) i).resolve_left hx
  have hxx : (x * s) * s = x := by rw [mul_assoc, hss, mul_one]
  have hnotU := not_upperClosureCondition_of_wall hA hμα hn0 hn hx'
  rw [hxx] at hnotU
  have hsub := translation_irreducible_of_not_memUpperClosure_of_isAntidominant P hA hlam hμ
    hfacet hν' hzz hzν' x hxint (fun hU ↦ hnotU ((memUpperClosure_weylDot_iff_of_isAntidominant
      hA hlam hμ hint hfacet x).mp hU))
  -- `T_λ^μ L(x·λ) = 0`, with `T_λ^μ` the translation by `L(ν)^* ≅ L(ν')`
  have h0 : Subsingleton (centralTranslation P (Module.Dual K (IrreducibleModule P ν))
      (centralCharacter P lam) (centralCharacter P μ)
        (IrreducibleModule P (P.weylDot hA' x lam))) :=
    @Equiv.subsingleton _ _ (centralTranslationCoeffEquiv P
      (IrreducibleModule P (P.weylDot hA' x lam)) (centralCharacter P lam)
        (centralCharacter P μ) eν).toEquiv hsub
  have hL' : IsCategoryO P (Module.Dual K (IrreducibleModule P ν)) :=
    IsCategoryO.of_equiv (P := P) (IrreducibleModule.isCategoryO P _) eν.symm
  have hMχ : centralBlock P (IrreducibleModule P (P.weylDot hA' w μ))
      (centralCharacter P μ) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' w.property μ) ▸ centralBlock_irreducible P _
  have hNχ : centralBlock P (IrreducibleModule P (P.weylDot hA' x lam))
      (centralCharacter P lam) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' x.property lam) ▸ centralBlock_irreducible P _
  exact nonempty_hom_ker_equiv_extOne P (IrreducibleModule.isCategoryO P _)
    (IrreducibleModule.isCategoryO P ν) hL' hMχ (IrreducibleModule.isCategoryO P _) hNχ h0 eX
    (IrreducibleModule.isCategoryO P _) p hp

include hA in
/-- Under the hypotheses of `exists_hom_translation_irreducible_ne_zero_iff` (Humphreys, GSM 94,
Theorem 7.14 (c)), there is a surjection `T_μ^λ L(w·μ) → L(w·λ)`. -/
theorem exists_surjective_translation_irreducible_wall {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    {w : P.weylGroup hA.isGeneralizedCartan} (hw : P.IsPosRoot hA.isGeneralizedCartan (w * v) i)
    (hwint : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam) :
    ∃ p : centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
        (centralCharacter P lam) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ))
          →ₗ⁅K,𝔤⁆ IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam),
      Function.Surjective p := by
  obtain ⟨f, hf⟩ := (exists_hom_translation_irreducible_ne_zero_iff P hA hlam hμ hfacet hν hz hzν
    hv hμα hwall hlamα hw hwint w).mpr rfl
  have := IrreducibleModule.isIrreducible P (P.weylDot hA.isGeneralizedCartan w lam)
  refine ⟨f, ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top f.range with h | h
  · exact absurd (LieModuleHom.ext fun m ↦ by
      have : f m ∈ f.range := (LieModuleHom.mem_range f _).mpr ⟨m, rfl⟩
      rwa [h, LieSubmodule.mem_bot] at this) hf
  · exact (LieModuleHom.range_eq_top f).mp h

end Wall

end Matrix.Realization.KacMoodyAlgebra
