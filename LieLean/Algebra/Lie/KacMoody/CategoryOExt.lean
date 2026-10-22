/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOProjective
import LieLean.Algebra.Lie.RelativeExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# `Ext¹` in the category `𝒪` and relative `Ext¹`

The relative group `LieModule.ExtOne (h P) M N` (relative `1`-cocycles modulo coboundaries,
classifying the extensions of `M` by `N` on which `𝔥` acts diagonally) is the `Ext¹_𝒪` used for
[HumO] Thm 3.3 (d) and Thm 6.5. Here it is compared with `Ext¹` computed in the derived
category of the abelian category `𝒪` (`CategoryO.instHasExt`): if `ExtOne (h P) M N = 0` then
`Ext¹_𝒪(M, N) = 0` (`CategoryO.ext_one_eq_zero_of_extOne`). This is the base case of the
inductions of [HumO] §6.11–6.12.

## Main results

* `CategoryTheory.Abelian.Ext.eq_zero_of_forall_exists_comp`: in an abelian category, if
  `0 → A → P → X → 0` is exact with `P` projective and every morphism `A → Y` extends to `P`, then
  `Ext¹(X, Y) = 0`.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.shortExact_of_lie`: short exactness in `𝒪` can be
  checked on the underlying `𝔤`-modules.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.ext_one_eq_zero_of_extOne`: relative `Ext¹ = 0`
  implies `Ext¹_𝒪 = 0`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §3.1, §6.10–6.11.
-/

open CategoryTheory Limits LieModule

noncomputable section

universe w u

namespace CategoryTheory.Abelian.Ext

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]

/-- If `0 → A → P → X → 0` is exact with `P` projective and every morphism `A → Y` extends to
`P`, then `Ext¹(X, Y) = 0`. -/
theorem eq_zero_of_forall_exists_comp {S : ShortComplex C} (hS : S.ShortExact) [Projective S.X₂]
    {Y : C} (h : ∀ a : S.X₁ ⟶ Y, ∃ b : S.X₂ ⟶ Y, S.f ≫ b = a) (z : Ext.{w} S.X₃ Y 1) :
    z = 0 := by
  obtain ⟨x₁, rfl⟩ := contravariant_sequence_exact₃ hS Y z (eq_zero_of_projective _)
    (n₀ := 0) rfl
  obtain ⟨b, hb⟩ := h (homEquiv₀ x₁)
  rw [← mk₀_homEquiv₀_apply x₁, ← hb, ← mk₀_comp_mk₀]
  exact hS.extClass_comp_assoc _

end CategoryTheory.Abelian.Ext

namespace Matrix.Realization.KacMoodyAlgebra

namespace CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P

/-- A short complex of `𝒪` is short exact if the underlying sequence of `𝔤`-modules is. -/
theorem shortExact_of_lie {S : ShortComplex (CategoryO.{u} P)}
    (hf : Function.Injective S.f.hom.hom) (hg : Function.Surjective S.g.hom.hom)
    (hfg : ∀ y, S.g.hom.hom y = 0 → ∃ x, S.f.hom.hom x = y) : S.ShortExact :=
  ShortExact.reflects_shortExact_of_faithful (CategoryO.IsObj.{u} P).ι
    { exact := (ShortComplex.moduleCat_exact_iff _).mpr hfg
      mono_f := (ModuleCat.mono_iff_injective _).mpr hf
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hg }

/-- `Ext¹_𝒪(X, Y) = 0` when the relative `Ext¹` vanishes, given a surjection `M → X` from a
projective module in `𝒪`: the kernel sequence `0 → N → M → X → 0` has a weight splitting, and
the vanishing of relative `Ext¹` extends every morphism `N → Y` to `M`. -/
theorem ext_one_eq_zero_of_extOne_aux (M : Type u) [AddCommGroup M] [Module K M]
    [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsCategoryO P M)
    (hS : ∃ S : Finset M, LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤)
    (hproj : IsProjectiveO.{u} P M) (X Y : CategoryO.{u} P) (π : M →ₗ⁅K,𝔤⁆ X.obj)
    (hπ : Function.Surjective π) (hXY : ∀ e : ExtOne (h P) X.obj Y.obj, e = 0)
    (z : Abelian.Ext.{u} X Y 1) : z = 0 := by
  let Q := mk M hM hS
  have hQ : Projective Q := projective_mk M hM hS hproj
  let eM := ofLieEquiv (P := P) M
  let πQ : Q.obj →ₗ⁅K,𝔤⁆ X.obj := π.comp eM.symm.toLieModuleHom
  have hπQ : Function.Surjective πQ := fun x ↦ by
    obtain ⟨m, rfl⟩ := hπ x
    exact ⟨eM m, rfl⟩
  have hexact : ∀ b, πQ b = 0 ↔ ∃ a : πQ.ker, πQ.ker.incl a = b := fun b ↦
    ⟨fun hb ↦ ⟨⟨b, LieModuleHom.mem_ker.mpr hb⟩, rfl⟩, by
      rintro ⟨a, rfl⟩
      exact LieModuleHom.mem_ker.mp a.2⟩
  let eN := ofLieEquiv (P := P) πQ.ker
  let iL : ofLie P πQ.ker ⟶ Q.obj := ofLieModuleHom (πQ.ker.incl.comp eN.symm.toLieModuleHom)
  have hiL : Function.Injective iL.hom := fun a b hab ↦ eN.symm.injective (Subtype.ext hab)
  let Nobj : CategoryO.{u} P := ⟨ofLie P πQ.ker, isObj_of_injective iL hiL Q.property⟩
  let i : Nobj ⟶ Q := (IsObj.{u} P).homMk iL
  let p : Q ⟶ X := (IsObj.{u} P).homMk (ofLieModuleHom πQ)
  let S := ShortComplex.mk i p (by
    ext x
    exact LieModuleHom.mem_ker.mp (eN.symm x).2)
  have hS : S.ShortExact := shortExact_of_lie hiL hπQ fun y hy ↦
    ⟨eN ⟨y, LieModuleHom.mem_ker.mpr hy⟩, rfl⟩
  have : Projective S.X₂ := hQ
  refine Abelian.Ext.eq_zero_of_forall_exists_comp hS (fun a ↦ ?_) z
  obtain ⟨SD⟩ := ExtOne.exists_splitData (h P) Q.property.1.iSup_weightSpaceOfMap_eq_top
    X.property.1.iSup_weightSpaceOfMap_eq_top Subtype.val_injective hπQ hexact
  obtain ⟨g, hg⟩ := (SD.connecting_eq_zero_iff
    ((toLieModuleHom a.hom).comp eN.toLieModuleHom)).mp (hXY _)
  refine ⟨(IsObj.{u} P).homMk (ofLieModuleHom g), ?_⟩
  ext x
  exact LieModuleHom.congr_fun hg (eN.symm x)

/-- **Relative `Ext¹` and `Ext¹_𝒪`.** If the relative `Ext¹` (`LieModule.ExtOne`, the `Ext¹_𝒪`
of [HumO] Thm 3.3 (d) and Thm 6.5) vanishes, then so does `Ext¹` in the derived category of the
abelian category `𝒪`. -/
theorem ext_one_eq_zero_of_extOne (X Y : CategoryO.{u} P)
    (hXY : ∀ e : ExtOne (h P) X.obj Y.obj, e = 0) (z : Abelian.Ext.{u} X Y 1) : z = 0 := by
  obtain ⟨S, hS⟩ := X.property.2
  obtain ⟨κ, _, _, τ, hD, hproj, hgen, π, hπ⟩ :=
    exists_isProjectiveO_surjective P (Fact.out : A.IsFiniteCartan) X.property.1 hS
  exact ext_one_eq_zero_of_extOne_aux _ hD hgen hproj X Y π hπ hXY z

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
