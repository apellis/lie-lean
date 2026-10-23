/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.FiniteLength
import LieLean.Algebra.Lie.KacMoody.TranslationProjectiveCover
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Abelian.Subcategory

/-!
# The category `𝒪` as an abelian category

Humphreys' category `𝒪` ([HumO] §1.1) consists of the finitely generated `𝔤`-modules that are
`𝔥`-semisimple and locally `𝔫`-finite. Here it is realized as a full subcategory of the abelian
category of `U(𝔤)`-modules: `CategoryO.IsObj P X` says that the `U(𝔤)`-module `X`, regarded as a
`𝔤`-module, satisfies `IsCategoryO P` and is finitely generated. In finite type over an
algebraically closed field of characteristic zero this subcategory is closed under subobjects,
quotients and finite products ([HumO] Thm 1.1 and §1.11, where the first needs that modules in
`𝒪` are noetherian), so the full subcategory `CategoryO P` is abelian
(`CategoryO.instAbelian`). This is the setting for the derived functors `Extⁿ_𝒪` used in
[HumO] Ch. 6.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.CategoryO.IsObj`: the object property of lying in `𝒪`.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO`: the full subcategory `𝒪` of `U(𝔤)`-modules.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.toLieModuleHom`: a morphism of `U(𝔤)`-modules as a
  morphism of `𝔤`-modules.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.CategoryO.instAbelian`: `𝒪` is abelian.

## Implementation notes

A `U(𝔤)`-module `X` is a `K`-module by restriction of scalars and a `𝔤`-module with
`⁅x, m⁆ = ι x • m`; these structures are scoped instances in the namespace `CategoryO`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §1.1, Thm 1.11, §6.1.
-/

open CategoryTheory Limits LieModule

noncomputable section

universe w

/-- A Lie module whose lattice of submodules is noetherian is finitely generated. -/
theorem LieSubmodule.exists_finset_lieSpan_eq_top {R L M : Type*} [CommRing R] [LieRing L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [WellFoundedGT (LieSubmodule R L M)] :
    ∃ S : Finset M, LieSubmodule.lieSpan R L (S : Set M) = ⊤ := by
  classical
  obtain ⟨_, ⟨S, rfl⟩, hS⟩ := (wellFounded_gt (α := LieSubmodule R L M)).has_min
    (Set.range fun S : Finset M ↦ LieSubmodule.lieSpan R L (S : Set M)) ⟨_, ∅, rfl⟩
  refine ⟨S, by_contra fun hne ↦ ?_⟩
  obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  refine hS _ ⟨insert x S, rfl⟩ (SetLike.lt_iff_le_and_exists.mpr ⟨?_, x, ?_, hx⟩)
  · exact LieSubmodule.lieSpan_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
  · exact LieSubmodule.subset_lieSpan (by rw [Finset.coe_insert]; exact Set.mem_insert _ _)

namespace Matrix.Realization.KacMoodyAlgebra

open UniversalEnvelopingAlgebra (lieRingModuleOfModule lieModuleOfModule)

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K (KacMoodyAlgebra P)

/-! ### Modules in `𝒪` with no generators and of no weights -/

/-- A zero module lies in `𝒪`. -/
theorem IsCategoryO.of_subsingleton (V : Type*) [AddCommGroup V] [Module K V]
    [LieRingModule 𝔤 V] [LieModule K 𝔤 V] [Subsingleton V] : IsCategoryO P V := by
  have := (Submodule.subsingleton_iff K).mpr ‹Subsingleton V›
  refine ⟨Subsingleton.elim _ _, fun μ ↦ ?_, ⟨∅, fun μ hμ ↦ (hμ (Subsingleton.elim _ _)).elim⟩⟩
  rw [Subsingleton.elim (weightSpaceOfMap V (h P) μ) ⊥]
  infer_instance

namespace CategoryO

/-! ### `U(𝔤)`-modules as `𝔤`-modules -/

/-- A `U(𝔤)`-module is a `K`-module by restriction of scalars. -/
scoped instance instModule (X : ModuleCat.{w} 𝓤) : Module K X :=
  ModuleCat.moduleOfAlgebraModule (k := K) X

scoped instance instIsScalarTower (X : ModuleCat.{w} 𝓤) : IsScalarTower K 𝓤 X :=
  ModuleCat.isScalarTower_of_algebra_moduleCat (k := K) X

/-- A `U(𝔤)`-module is a `𝔤`-module, with `⁅x, m⁆ = ι x • m`. -/
scoped instance instLieRingModule (X : ModuleCat.{w} 𝓤) : LieRingModule 𝔤 X :=
  lieRingModuleOfModule K 𝔤 X

scoped instance instLieModule (X : ModuleCat.{w} 𝓤) : LieModule K 𝔤 X :=
  lieModuleOfModule K 𝔤 X

variable {P}

lemma lie_def {X : ModuleCat.{w} 𝓤} (x : 𝔤) (m : X) :
    ⁅x, m⁆ = UniversalEnvelopingAlgebra.ι K x • m :=
  rfl

/-- A morphism of `U(𝔤)`-modules as a morphism of `𝔤`-modules. -/
def toLieModuleHom {X Y : ModuleCat.{w} 𝓤} (f : X ⟶ Y) : X →ₗ⁅K,𝔤⁆ Y where
  toFun := f.hom
  map_add' := f.hom.map_add
  map_smul' c m := f.hom.map_smul (algebraMap K 𝓤 c) m
  map_lie' {x m} := f.hom.map_smul (UniversalEnvelopingAlgebra.ι K x) m

@[simp] lemma toLieModuleHom_apply {X Y : ModuleCat.{w} 𝓤} (f : X ⟶ Y) (m : X) :
    toLieModuleHom (P := P) f m = f.hom m :=
  rfl

/-- An isomorphism of `U(𝔤)`-modules as an equivalence of `𝔤`-modules. -/
def toLieModuleEquiv {X Y : ModuleCat.{w} 𝓤} (e : X ≅ Y) : X ≃ₗ⁅K,𝔤⁆ Y :=
  { toLieModuleHom (P := P) e.hom with
    invFun := e.inv.hom
    left_inv := fun m ↦ by simp
    right_inv := fun m ↦ by simp }

variable (P)

/-! ### The object property and the category -/

/-- A `U(𝔤)`-module lies in **the category `𝒪`** ([HumO] §1.1) if, as a `𝔤`-module, it satisfies
`IsCategoryO P` and is finitely generated. -/
def IsObj : ObjectProperty (ModuleCat.{w} 𝓤) := fun X ↦
  IsCategoryO P X ∧ ∃ S : Finset X, LieSubmodule.lieSpan K 𝔤 (S : Set X) = ⊤

end CategoryO

/-- **The category `𝒪`** ([HumO] §1.1), as a full subcategory of the category of
`U(𝔤)`-modules. -/
abbrev CategoryO := (CategoryO.IsObj.{w} P).FullSubcategory

namespace CategoryO

variable {P}

/-- A quotient of a module in `𝒪` lies in `𝒪`. -/
theorem isObj_of_surjective {X Y : ModuleCat.{w} 𝓤} (f : X ⟶ Y)
    (hf : Function.Surjective f.hom) (hX : IsObj P X) : IsObj P Y := by
  let φ := toLieModuleHom (P := P) f
  let q := LieSubmodule.Quotient.lift φ.ker φ le_rfl
  have hq : Function.Bijective q := by
    refine ⟨fun a b hab ↦ ?_, LieSubmodule.Quotient.lift_surjective _ _ _ hf⟩
    obtain ⟨a, rfl⟩ := LieSubmodule.Quotient.surjective_mk' φ.ker a
    obtain ⟨b, rfl⟩ := LieSubmodule.Quotient.surjective_mk' φ.ker b
    rw [LieSubmodule.Quotient.lift_mk, LieSubmodule.Quotient.lift_mk] at hab
    rw [← sub_eq_zero, ← map_sub, LieSubmodule.Quotient.mk_eq_zero, LieModuleHom.mem_ker,
      map_sub, hab, sub_self]
  obtain ⟨S, hS⟩ := hX.2
  refine ⟨(hX.1.quotient φ.ker).of_equiv (LieModuleEquiv.ofBijective q hq), ?_⟩
  classical
  refine ⟨S.image f.hom, ?_⟩
  rw [Finset.coe_image]
  exact lieSpan_image_eq_top_of_surjective φ hf hS

/-- A module isomorphic to a module in `𝒪` lies in `𝒪`. -/
instance : (IsObj.{w} P).IsClosedUnderIsomorphisms where
  of_iso e hX := isObj_of_surjective e.hom (toLieModuleEquiv (P := P) e).surjective hX

variable (P) in
/-- The zero `U(𝔤)`-module. -/
def zeroObj : ModuleCat.{w} 𝓤 := ModuleCat.of 𝓤 PUnit.{w + 1}

instance : Subsingleton (zeroObj.{w} P) := inferInstanceAs (Subsingleton PUnit)

instance : (IsObj.{w} P).ContainsZero where
  exists_zero := ⟨zeroObj P, ModuleCat.isZero_of_subsingleton _,
    IsCategoryO.of_subsingleton P _, ⟨∅, by
      have := (LieSubmodule.subsingleton_iff K 𝔤 (zeroObj.{w} P)).mpr inferInstance
      exact Subsingleton.elim _ _⟩⟩

instance : (IsObj.{w} P).IsClosedUnderQuotients where
  prop_of_epi f hf hX := isObj_of_surjective f ((ModuleCat.epi_iff_surjective f).mp hf) hX

/-! ### Finite products -/

section Products

/-- The product `∏ⱼ Mⱼ` of `U(𝔤)`-modules. -/
def piObj {J : Type} (M : J → ModuleCat.{w} 𝓤) : ModuleCat.{w} 𝓤 := ModuleCat.of 𝓤 (∀ j, M j)

/-- A finite direct sum of `U(𝔤)`-modules is identified, as a `𝔤`-module, with the product
`U(𝔤)`-module. -/
def directSumEquivPi {J : Type} [Fintype J] (M : J → ModuleCat.{w} 𝓤) :
    DirectSum J (fun j ↦ M j) ≃ₗ⁅K,𝔤⁆ piObj M where
  toFun m j := m j
  invFun m := (DirectSum.linearEquivFunOnFintype K J (fun j ↦ M j)).symm m
  left_inv m := (DirectSum.linearEquivFunOnFintype K J (fun j ↦ M j)).symm_apply_apply m
  right_inv m := (DirectSum.linearEquivFunOnFintype K J (fun j ↦ M j)).apply_symm_apply m
  map_add' a b := funext fun j ↦ DirectSum.add_apply a b j
  map_smul' c m := funext fun j ↦ DFinsupp.smul_apply c m j
  map_lie' {x m} := funext fun j ↦ DirectSum.lie_module_bracket_apply x m j

lemma isCategoryO_piObj {J : Type} [Finite J] (M : J → ModuleCat.{w} 𝓤)
    (hM : ∀ j, IsCategoryO P (M j)) : IsCategoryO P (piObj M) := by
  have := Fintype.ofFinite J
  exact (IsCategoryO.directSum _ hM).of_equiv (directSumEquivPi M)

lemma exists_finset_lieSpan_piObj_eq_top {J : Type} [Finite J] (M : J → ModuleCat.{w} 𝓤)
    (hM : ∀ j, ∃ S : Finset (M j), LieSubmodule.lieSpan K 𝔤 (S : Set (M j)) = ⊤) :
    ∃ S : Finset (piObj M), LieSubmodule.lieSpan K 𝔤 (S : Set (piObj M)) = ⊤ := by
  classical
  have := Fintype.ofFinite J
  obtain ⟨T, hT⟩ := exists_finset_lieSpan_directSum_eq_top (L := 𝔤) hM
  refine ⟨T.image (directSumEquivPi (P := P) M), ?_⟩
  rw [Finset.coe_image]
  exact lieSpan_image_eq_top_of_surjective (directSumEquivPi (P := P) M).toLieModuleHom
    (directSumEquivPi (P := P) M).surjective hT

/-- A finite product of modules in `𝒪` lies in `𝒪`. -/
theorem isObj_pi {J : Type} [Finite J] (M : J → ModuleCat.{w} 𝓤)
    (hM : ∀ j, IsObj P (M j)) : IsObj P (piObj M) :=
  ⟨isCategoryO_piObj M fun j ↦ (hM j).1, exists_finset_lieSpan_piObj_eq_top M fun j ↦ (hM j).2⟩

lemma isClosedUnderLimitsOfShape_discrete (J : Type) [Finite J] :
    (IsObj.{w} P).IsClosedUnderLimitsOfShape (Discrete J) := by
  refine ObjectProperty.IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  let e : limit F ≅ piObj (fun j ↦ F.obj ⟨j⟩) :=
    HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := F)) ≪≫ ModuleCat.piIsoPi _
  exact (IsObj.{w} P).prop_of_iso e.symm (isObj_pi _ fun j ↦ hF ⟨j⟩)

end Products

instance : (IsObj.{w} P).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := isClosedUnderLimitsOfShape_discrete J

variable [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan]

/-- A submodule of a module in `𝒪` lies in `𝒪`: modules in `𝒪` are noetherian
([HumO] Thm 1.11). -/
theorem isObj_of_injective {X Y : ModuleCat.{w} 𝓤} (f : X ⟶ Y)
    (hf : Function.Injective f.hom) (hY : IsObj P Y) : IsObj P X := by
  let φ := toLieModuleHom (P := P) f
  let r : X →ₗ⁅K,𝔤⁆ φ.range :=
    φ.codRestrict φ.range fun m ↦ (LieModuleHom.mem_range _ _).mpr ⟨m, rfl⟩
  have hr : Function.Bijective r := by
    refine ⟨fun a b hab ↦ hf (congrArg Subtype.val hab), fun ⟨y, hy⟩ ↦ ?_⟩
    obtain ⟨m, rfl⟩ := (LieModuleHom.mem_range _ _).mp hy
    exact ⟨m, rfl⟩
  obtain ⟨S, hS⟩ := hY.2
  have := hY.1.wellFoundedGT_lieSubmodule P (Fact.out : A.IsFiniteCartan) hS
  have : WellFoundedGT (LieSubmodule K 𝔤 X) :=
    (LieSubmodule.mapOrderEmbedding (f := φ) hf).strictMono.wellFoundedGT
  exact ⟨(hY.1.lieSubmodule φ.range).of_equiv (LieModuleEquiv.ofBijective r hr).symm,
    LieSubmodule.exists_finset_lieSpan_eq_top⟩

instance : (IsObj.{w} P).IsClosedUnderSubobjects where
  prop_of_mono f hf hY := isObj_of_injective f ((ModuleCat.mono_iff_injective f).mp hf) hY

/-- **The category `𝒪` is abelian** (finite type, algebraically closed field of characteristic
zero; [HumO] §1.1 and Thm 1.11). -/
instance instAbelian : Abelian (CategoryO.{w} P) := inferInstance

/-- A monomorphism of `𝒪` is injective on the underlying modules. -/
theorem injective_of_mono {X Y : CategoryO.{w} P} (f : X ⟶ Y) [Mono f] :
    Function.Injective f.hom.hom := by
  have := (IsObj.{w} P).preservesMonomorphisms_ι_of_isNormalEpiCategory
  exact (ModuleCat.mono_iff_injective ((IsObj.{w} P).ι.map f)).mp inferInstance

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
