/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOAbelian
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Enough projectives in the category `𝒪`

In finite type over an algebraically closed field of characteristic zero, the abelian category
`CategoryO P` has enough projectives ([HumO] Thm 3.8, projective part;
`CategoryO.instEnoughProjectives`). Hence Mathlib's `Abelian.Ext` is defined on it
(`CategoryO.instHasExt`): these are the groups `Extⁿ_𝒪(M, N)` of [HumO] §6.1, here computed in
the derived category of `𝒪`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.CategoryO.ofLie`: a `𝔤`-module as a `U(𝔤)`-module.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.ofLieModuleHom`: a morphism of `𝔤`-modules between
  `U(𝔤)`-modules as a morphism of `U(𝔤)`-modules.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.mk`: a module in `𝒪` (in the sense of
  `IsCategoryO` plus finite generation) as an object of `CategoryO P`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.CategoryO.projective_of_isProjectiveO`: an object whose
  underlying module is `IsProjectiveO` is projective in `CategoryO P`.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.instEnoughProjectives`: `𝒪` has enough
  projectives.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Thm 3.8, §6.1.
-/

open CategoryTheory Limits LieModule

noncomputable section

universe w u

namespace Matrix.Realization.KacMoodyAlgebra

namespace CategoryO

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K (KacMoodyAlgebra P)

/-! ### From `𝔤`-modules to `U(𝔤)`-modules -/

/-- A morphism of `𝔤`-modules between `U(𝔤)`-modules is `U(𝔤)`-linear. -/
def ofLieModuleHom {X Y : ModuleCat.{w} 𝓤} (φ : X →ₗ⁅K,𝔤⁆ Y) : X ⟶ Y :=
  ModuleCat.ofHom
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun u m ↦ by
        change φ (u • m) = u • φ m
        induction u using UniversalEnvelopingAlgebra.induction generalizing m with
        | algebraMap r => exact map_smul φ r m
        | ι x => exact LieModuleHom.map_lie φ x m
        | mul a b ha hb => rw [mul_smul, mul_smul, ha, hb]
        | add a b ha hb => rw [add_smul, add_smul, map_add, ha, hb] }

@[simp] lemma ofLieModuleHom_hom_apply {X Y : ModuleCat.{w} 𝓤} (φ : X →ₗ⁅K,𝔤⁆ Y) (m : X) :
    (ofLieModuleHom φ).hom m = φ m :=
  rfl

variable (P) in
/-- A `𝔤`-module as a `U(𝔤)`-module, via the universal property of `U(𝔤)`. -/
def ofLie (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M] :
    ModuleCat.{w} 𝓤 :=
  letI : Module 𝓤 M :=
    Module.compHom M (UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K 𝔤 M)).toRingHom
  ModuleCat.of 𝓤 M

/-- A `𝔤`-module is isomorphic, as a `𝔤`-module, to the `U(𝔤)`-module it defines. -/
def ofLieEquiv (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M] :
    M ≃ₗ⁅K,𝔤⁆ ofLie P M where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c m := by
    change c • m = (UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K 𝔤 M))
      (algebraMap K 𝓤 c) m
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
  map_lie' {x m} := by
    change ⁅x, m⁆ = (UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K 𝔤 M))
      (UniversalEnvelopingAlgebra.ι K x) m
    rw [UniversalEnvelopingAlgebra.lift_ι_apply, LieModule.toEnd_apply_apply]

/-- A module in `𝒪` (finitely generated, `IsCategoryO`) as an object of `CategoryO P`. -/
def mk (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    (hM : IsCategoryO P M) (hS : ∃ S : Finset M, LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤) :
    CategoryO.{w} P :=
  ⟨ofLie P M, hM.of_equiv (ofLieEquiv (P := P) M), by
    obtain ⟨S, hS⟩ := hS
    classical
    refine ⟨S.image (ofLieEquiv (P := P) M), ?_⟩
    rw [Finset.coe_image]
    exact lieSpan_image_eq_top_of_surjective (ofLieEquiv (P := P) M).toLieModuleHom
      (ofLieEquiv (P := P) M).surjective hS⟩

/-! ### Projectives -/

variable [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan]

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
/-- An epimorphism in `𝒪` is surjective. -/
theorem surjective_of_epi {X Y : CategoryO.{w} P} (f : X ⟶ Y) [Epi f] :
    Function.Surjective f.hom.hom := by
  have := (IsObj.{w} P).preservesEpimorphisms_ι_of_isNormalMonoCategory
  exact (ModuleCat.epi_iff_surjective ((IsObj.{w} P).ι.map f)).mp inferInstance

/-- An object of `𝒪` whose underlying module is projective in the sense of `IsProjectiveO` is
projective in the abelian category `𝒪`. -/
theorem projective_of_isProjectiveO (Q : CategoryO.{w} P) (hQ : IsProjectiveO.{w} P Q.obj) :
    Projective Q where
  factors {E X} g e _ := by
    obtain ⟨ψ, hψ⟩ := hQ E.property.1 X.property.1 (toLieModuleHom e.hom) (surjective_of_epi e)
      (toLieModuleHom g.hom)
    refine ⟨(IsObj.{w} P).homMk (ofLieModuleHom ψ), ?_⟩
    ext m
    exact LieModuleHom.congr_fun hψ m

/-- A surjection onto an object of `𝒪` from a projective module in `𝒪` is a projective
presentation. -/
theorem nonempty_projectivePresentation (M : Type w) [AddCommGroup M] [Module K M]
    [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (X : CategoryO.{w} P) (hM : IsCategoryO P M)
    (hS : ∃ S : Finset M, LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤)
    (hproj : IsProjectiveO.{w} P M) (π : M →ₗ⁅K,𝔤⁆ X.obj) (hπ : Function.Surjective π) :
    Nonempty (ProjectivePresentation X) := by
  let e := ofLieEquiv (P := P) M
  have hQ : Projective (mk M hM hS) := projective_of_isProjectiveO _
    (hproj.of_retract e.symm.toLieModuleHom e.toLieModuleHom (by ext; rfl))
  let f : mk M hM hS ⟶ X := (IsObj.{w} P).homMk (ofLieModuleHom (π.comp e.symm.toLieModuleHom))
  have hf : Epi f := (IsObj.{w} P).ι.epi_of_epi_map
    ((ModuleCat.epi_iff_surjective _).mpr fun x ↦ by
      obtain ⟨d, rfl⟩ := hπ x
      exact ⟨e d, rfl⟩)
  exact ⟨⟨mk M hM hS, f⟩⟩

end CategoryO

section Ext

open CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

/-- **Enough projectives in `𝒪`** ([HumO] Thm 3.8, projective part): every object of `𝒪` is a
quotient of a projective object. -/
instance CategoryO.instEnoughProjectives : EnoughProjectives (CategoryO.{u} P) where
  presentation X := by
    obtain ⟨S, hS⟩ := X.property.2
    obtain ⟨κ, _, _, τ, hD, hproj, hgen, π, hπ⟩ :=
      exists_isProjectiveO_surjective P (Fact.out : A.IsFiniteCartan) X.property.1 hS
    exact nonempty_projectivePresentation _ X hD hgen hproj π hπ

/-- `Extⁿ` in `𝒪` ([HumO] §6.1), via the derived category of `𝒪`. -/
instance CategoryO.instHasExt : HasExt.{u} (CategoryO.{u} P) :=
  hasExt_of_enoughProjectives.{u} _

end Ext

end Matrix.Realization.KacMoodyAlgebra
