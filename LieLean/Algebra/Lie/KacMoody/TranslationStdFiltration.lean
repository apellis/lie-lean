/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationNonintegral
import LieLean.Algebra.Lie.KacMoody.TranslationSimple
import LieLean.Algebra.Lie.KacMoody.StandardFiltration

/-!
# Translation of modules with a standard filtration

Humphreys, GSM 94, Corollary 7.6: under the hypotheses of Theorem 7.6, translation `T_λ^μ`
sends a module in the block of `λ` with a standard filtration to a module with a standard
filtration.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.nonempty_equiv_map_centralTranslation`: translation of a
  subquotient `N₁ / N₀` of `X` is the corresponding subquotient of `T X`.
* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.exists_isStdFiltered_centralTranslation`:
  if every Verma factor of a standard filtration of `N ⊆ X` is sent to a Verma module, then the
  image of `T N` in `T X` has a standard filtration.
* `Matrix.Realization.KacMoodyAlgebra.IsStdFiltered.centralCharacter_eq`: the factors of a
  standard filtration of a module in the block `χ` have central character `χ`.
* `Matrix.Realization.KacMoodyAlgebra.exists_isStdFiltered_translation_of_isAntidominant`:
  **Humphreys, GSM 94, Corollary 7.6**.

## Proof

As in Humphreys, by induction along the filtration, using exactness of translation and
Theorem 7.6 for the Verma factors. The filtration of `X` is carried to the images in `T X` of
the `T N`, `N` the steps of the filtration. A factor `M(ν)` of a module in the block of `λ` has
`ν ∈ W·λ` by Harish-Chandra's theorem (`VermaModule.centralCharacter_eq_iff`).

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.6.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Generic

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [IsAlgClosed K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {U V X Z : Type*}
  [AddCommGroup U] [Module K U] [LieRingModule P.KacMoodyAlgebra U]
  [LieModule K P.KacMoodyAlgebra U]
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]
  [AddCommGroup Z] [Module K Z] [LieRingModule P.KacMoodyAlgebra Z]
  [LieModule K P.KacMoodyAlgebra Z]

local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

omit [CharZero K] [IsAlgClosed K] in
/-- `T (g ∘ f) = T g ∘ T f`, pointwise. -/
theorem centralTranslationMap_comp_apply (χ₁ χ₂ : 𝓩 →ₐ[K] K)
    (f : U →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (g : V →ₗ⁅K,P.KacMoodyAlgebra⁆ X) (x) :
    centralTranslationMap P Z χ₁ χ₂ (g.comp f) x =
      centralTranslationMap P Z χ₁ χ₂ g (centralTranslationMap P Z χ₁ χ₂ f x) := by
  rw [centralTranslationMap_comp]
  rfl

/-- Translation of `X → X / N` has kernel the image of `T N`. -/
theorem ker_centralTranslationMap_mk' (hX : IsCategoryO P X) (hZ : IsCategoryO P Z)
    (χ₁ χ₂ : 𝓩 →ₐ[K] K) (N : LieSubmodule K P.KacMoodyAlgebra X) :
    (centralTranslationMap P Z χ₁ χ₂ (LieSubmodule.Quotient.mk' N)).ker =
      (centralTranslationMap P Z χ₁ χ₂ N.incl).range :=
  (centralTranslationMap_shortExact P Z hX hZ N.incl (LieSubmodule.Quotient.mk' N)
    (LieSubmodule.injective_incl _) (by rw [LieSubmodule.Quotient.mk'_ker, LieSubmodule.range_incl])
    (LieSubmodule.Quotient.surjective_mk' _) χ₁ χ₂).2.1

/-- The step of the induction: for `N₀, N₁ ⊆ X` and `V` isomorphic to the image of `N₁` in
`X / N₀`, `T V` is isomorphic to the image of `T N₁` in `T X / T N₀`. -/
theorem nonempty_equiv_map_centralTranslation (hX : IsCategoryO P X) (hZ : IsCategoryO P Z)
    (χ₁ χ₂ : 𝓩 →ₐ[K] K) {N₀ N₁ : LieSubmodule K P.KacMoodyAlgebra X}
    (e : V ≃ₗ⁅K,P.KacMoodyAlgebra⁆ N₁.map (LieSubmodule.Quotient.mk' N₀)) :
    Nonempty (centralTranslation P Z χ₁ χ₂ V ≃ₗ⁅K,P.KacMoodyAlgebra⁆
      (centralTranslationMap P Z χ₁ χ₂ N₁.incl).range.map
        (LieSubmodule.Quotient.mk' (centralTranslationMap P Z χ₁ χ₂ N₀.incl).range)) := by
  let π : X →ₗ⁅K,P.KacMoodyAlgebra⁆ X ⧸ N₀ := LieSubmodule.Quotient.mk' N₀
  let R := (centralTranslationMap P Z χ₁ χ₂ N₀.incl).range
  -- `T X / T N₀ ≅ T (X / N₀)`
  have hkerπ : (centralTranslationMap P Z χ₁ χ₂ π).ker = R :=
    ker_centralTranslationMap_mk' P hX hZ χ₁ χ₂ N₀
  have hsurjπ : Function.Surjective (centralTranslationMap P Z χ₁ χ₂ π) :=
    centralTranslationMap_surjective P hX hZ χ₁ χ₂ π (LieSubmodule.Quotient.surjective_mk' N₀)
  let κ := LieSubmodule.Quotient.lift R (centralTranslationMap P Z χ₁ χ₂ π) hkerπ.ge
  have hκ : Function.Bijective κ := by
    constructor
    · rw [← LieModuleHom.ker_eq_bot, LieSubmodule.eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' R y
      rw [LieModuleHom.mem_ker] at hy
      rw [LieSubmodule.Quotient.mk_eq_zero, ← hkerπ]
      exact hy
    · intro q
      obtain ⟨x, rfl⟩ := hsurjπ q
      exact ⟨LieSubmodule.Quotient.mk' R x, rfl⟩
  let κe := LieModuleEquiv.ofBijective κ hκ
  -- `V → X / N₀` and `N₁ → V`
  let g : V →ₗ⁅K,P.KacMoodyAlgebra⁆ X ⧸ N₀ :=
    (N₁.map π).incl.comp e.toLieModuleHom
  have hg : Function.Injective g := fun a b hab ↦ e.injective (Subtype.ext hab)
  let r₀ : N₁ →ₗ⁅K,P.KacMoodyAlgebra⁆ N₁.map π :=
    (π.comp N₁.incl).codRestrict _ fun x ↦ LieSubmodule.mem_map_of_mem x.2
  have hr₀ : Function.Surjective r₀ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := (LieSubmodule.mem_map _).mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let r : N₁ →ₗ⁅K,P.KacMoodyAlgebra⁆ V := e.symm.toLieModuleHom.comp r₀
  have hr : Function.Surjective r := e.symm.surjective.comp hr₀
  have hgr : g.comp r = π.comp N₁.incl := by
    ext x
    change ((e (e.symm (r₀ x))) : X ⧸ N₀) = π x
    rw [LieModuleEquiv.apply_symm_apply]
    rfl
  have hTg := centralTranslationMap_injective P (Z := Z) χ₁ χ₂ g hg
  have hTr := centralTranslationMap_surjective P (hX.lieSubmodule N₁) hZ χ₁ χ₂ r hr
  -- the embedding `T V → T X / T N₀`
  let γ := κe.symm.toLieModuleHom.comp (centralTranslationMap P Z χ₁ χ₂ g)
  have hγ : ∀ a, γ (centralTranslationMap P Z χ₁ χ₂ r a) =
      LieSubmodule.Quotient.mk' R (centralTranslationMap P Z χ₁ χ₂ N₁.incl a) := by
    intro a
    have h₁ := centralTranslationMap_comp_apply P (Z := Z) χ₁ χ₂ r g a
    have h₂ := centralTranslationMap_comp_apply P (Z := Z) χ₁ χ₂ N₁.incl π a
    have h₃ := LieModuleHom.congr_fun (congrArg (centralTranslationMap P Z χ₁ χ₂) hgr) a
    have h₄ : κe (LieSubmodule.Quotient.mk' R (centralTranslationMap P Z χ₁ χ₂ N₁.incl a)) =
        centralTranslationMap P Z χ₁ χ₂ π (centralTranslationMap P Z χ₁ χ₂ N₁.incl a) :=
      LieSubmodule.Quotient.lift_mk _ _ _ _
    refine κe.injective ((κe.apply_symm_apply _).trans ?_)
    exact h₁.symm.trans (h₃.trans (h₂.trans h₄.symm))
  have hmem : ∀ v, γ v ∈ (centralTranslationMap P Z χ₁ χ₂ N₁.incl).range.map
      (LieSubmodule.Quotient.mk' R) := by
    intro v
    obtain ⟨a, rfl⟩ := hTr v
    rw [hγ]
    exact LieSubmodule.mem_map_of_mem ⟨a, rfl⟩
  refine ⟨LieModuleEquiv.ofBijective (γ.codRestrict _ hmem) ⟨fun a b hab ↦ ?_, ?_⟩⟩
  · have := congrArg Subtype.val hab
    simp only [LieModuleHom.codRestrict_apply, γ, LieModuleHom.comp_apply,
      LieModuleEquiv.coe_toLieModuleHom] at this
    exact hTg (κe.symm.injective this)
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨a, ha⟩ := hx
    exact ⟨centralTranslationMap P Z χ₁ χ₂ r a,
      Subtype.ext ((hγ a).trans ((congrArg (LieSubmodule.Quotient.mk' R) ha).trans hxy))⟩

omit [CharZero K] [IsAlgClosed K] in
/-- The translation of the zero module is zero. -/
theorem range_centralTranslationMap_bot (χ₁ χ₂ : 𝓩 →ₐ[K] K) :
    (centralTranslationMap P Z χ₁ χ₂ (⊥ : LieSubmodule K P.KacMoodyAlgebra X).incl).range =
      ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨a, rfl⟩
  have hsub (u : centralBlock P (⊥ : LieSubmodule K P.KacMoodyAlgebra X) χ₁) : u = 0 :=
    Subtype.ext (Subtype.ext ((LieSubmodule.mem_bot _).mp u.1.2))
  have h0 : ∀ y : centralBlock P (⊥ : LieSubmodule K P.KacMoodyAlgebra X) χ₁ ⊗[K] Z, y = 0 := by
    intro y
    induction y with
    | tmul u z => rw [hsub u, TensorProduct.zero_tmul]
    | add y₁ y₂ h₁ h₂ => rw [h₁, h₂, add_zero]
  have : a = 0 := Subtype.ext (h0 _)
  rw [this, map_zero]
  exact LieSubmodule.zero_mem _

/-- **Translation of standard filtrations.** Let `N ⊆ X` have a standard filtration with factors
`M(ν)`, `ν ∈ s`, and suppose each `T M(ν)` is a Verma module. Then the image of `T N` in `T X`
has a standard filtration (proof of Humphreys, GSM 94, Corollary 7.6). -/
theorem IsStdFiltered.exists_isStdFiltered_centralTranslation (hX : IsCategoryO P X)
    (hZ : IsCategoryO P Z) (χ₁ χ₂ : 𝓩 →ₐ[K] K) {N : LieSubmodule K P.KacMoodyAlgebra X}
    {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s)
    (hfac : ∀ ν ∈ s, ∃ ν', Nonempty (VermaModule P ν' ≃ₗ⁅K,P.KacMoodyAlgebra⁆
      centralTranslation P Z χ₁ χ₂ (VermaModule P ν))) :
    ∃ t, IsStdFiltered P (centralTranslationMap P Z χ₁ χ₂ N.incl).range t := by
  induction hN with
  | bot => exact ⟨0, by rw [range_centralTranslationMap_bot]; exact IsStdFiltered.bot⟩
  | @step N₀ N₁ s₀ ν _ h01 he ih =>
    obtain ⟨t, ht⟩ := ih fun ν' hν' ↦ hfac ν' (Multiset.mem_cons_of_mem hν')
    obtain ⟨e⟩ := he
    obtain ⟨ν', ⟨e'⟩⟩ := hfac ν (Multiset.mem_cons_self _ _)
    obtain ⟨e''⟩ := nonempty_equiv_map_centralTranslation P hX hZ χ₁ χ₂ e
    refine ⟨ν' ::ₘ t, ht.step ?_ ⟨e'.trans e''⟩⟩
    rintro _ ⟨a, rfl⟩
    refine ⟨centralTranslationMap P Z χ₁ χ₂ (LieSubmodule.inclusion h01) a, ?_⟩
    rw [← centralTranslationMap_comp_apply]
    rfl

omit [IsAlgClosed K] in
/-- The Verma factors of a standard filtration of a module in the block `χ` have central
character `χ`. -/
theorem IsStdFiltered.centralCharacter_eq {χ : 𝓩 →ₐ[K] K}
    (hX : centralBlock P X χ = ⊤) {N : LieSubmodule K P.KacMoodyAlgebra X}
    {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s) : ∀ ν ∈ s, centralCharacter P ν = χ := by
  induction hN with
  | bot => simp
  | @step N₀ N₁ s₀ ν _ _ he ih =>
    intro ν' hν'
    rcases Multiset.mem_cons.mp hν' with rfl | hν'
    · obtain ⟨e⟩ := he
      by_contra hne
      let f : VermaModule P ν' →ₗ⁅K,P.KacMoodyAlgebra⁆ X ⧸ N₀ :=
        (N₁.map (LieSubmodule.Quotient.mk' N₀)).incl.comp e.toLieModuleHom
      have hf : Function.Injective f := fun a b hab ↦ e.injective (Subtype.ext hab)
      have hblk : f (hwv P ν') ∈ centralBlock P (X ⧸ N₀) χ := by
        obtain ⟨x, hx⟩ := LieSubmodule.Quotient.surjective_mk' N₀ (f (hwv P ν'))
        rw [← hx]
        exact map_mem_centralBlock P _ χ (hX ▸ LieSubmodule.mem_top x)
      have h0 := mem_centralBlock_of_injective P f hf χ hblk
      rw [centralBlock_verma_eq_bot P ν' χ hne] at h0
      exact hwv_ne_zero P ν' ((LieSubmodule.mem_bot _).mp h0)
    · exact ih ν' hν'

end Generic

section Main

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)
  {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]

include hA in
/-- **Humphreys, GSM 94, Corollary 7.6.** Let `λ`, `μ` be antidominant, with every positive
coroot vanishing on `λ + ρ` vanishing on `μ + ρ` (`μ♮` in the closure of the facet of `λ♮`), and
`T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν))` with `ν` dominant integral in `W(μ - λ)`. If `X ∈ 𝒪` lies
in the block of `λ` and has a standard filtration, then `T_λ^μ X` (a module in the block of `μ`)
has a standard filtration. Finite type, finite-dimensional Cartan, algebraically closed field of
characteristic zero (Humphreys works over `ℂ`). -/
theorem exists_isStdFiltered_translation_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (hX : IsCategoryO P X) (hblock : centralBlock P X (centralCharacter P lam) = ⊤)
    {s : Multiset (Dual K H)} (hs : IsStdFiltered P (⊤ : LieSubmodule K P.KacMoodyAlgebra X) s) :
    ∃ t, IsStdFiltered P (⊤ : LieSubmodule K P.KacMoodyAlgebra
      (centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ) X)) t := by
  have hZ := IrreducibleModule.isCategoryO P ν
  have hfac : ∀ ν' ∈ s, ∃ ν'', Nonempty (VermaModule P ν'' ≃ₗ⁅K,P.KacMoodyAlgebra⁆
      centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ) (VermaModule P ν')) := by
    intro ν' hν'
    have hχ := IsStdFiltered.centralCharacter_eq P hblock hs ν' hν'
    obtain ⟨w, hw, hwe⟩ := (VermaModule.centralCharacter_eq_iff P hA lam ν').mp hχ.symm
    have hν'w : ν' = P.weylDot hA.isGeneralizedCartan ⟨w, hw⟩ lam := by
      change ν' = w (lam + P.rho) - P.rho
      rw [hwe, add_sub_cancel_right]
    subst hν'w
    exact ⟨_, translation_verma_equiv_of_isAntidominant P hA hlam hμ hfacet hν hz hzν ⟨w, hw⟩⟩
  obtain ⟨t, ht⟩ := hs.exists_isStdFiltered_centralTranslation P hX hZ _ _ hfac
  have htop : (centralTranslationMap P (IrreducibleModule P ν) (centralCharacter P lam)
      (centralCharacter P μ) (⊤ : LieSubmodule K P.KacMoodyAlgebra X).incl).range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨a, rfl⟩ := centralTranslationMap_surjective P (hX.lieSubmodule ⊤) hZ _ _
      (⊤ : LieSubmodule K P.KacMoodyAlgebra X).incl (fun x ↦ ⟨⟨x, LieSubmodule.mem_top x⟩, rfl⟩) y
    exact ⟨a, rfl⟩
  exact ⟨t, htop ▸ ht⟩

end Main

end Matrix.Realization.KacMoodyAlgebra
