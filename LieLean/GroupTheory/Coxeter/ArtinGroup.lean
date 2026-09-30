/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.PresentedGroup

/-!
# Artin groups of Coxeter matrices

The Artin group (Artin–Tits group, generalized braid group) of a Coxeter matrix `M` is
$$\langle \{\sigma_i\}_{i \in B} \mid \underbrace{\sigma_i \sigma_{i'} \sigma_i \cdots}_{M_{i,i'}}
  = \underbrace{\sigma_{i'} \sigma_i \sigma_{i'} \cdots}_{M_{i,i'}} \ (i \ne i')\rangle,$$
with no relation when `M i i' = 0` (that is, `m = ∞`). It surjects onto the Coxeter group
`M.Group`, but the generators need not be involutions.

## Main definitions

* `CoxeterMatrix.artinRelation`, `CoxeterMatrix.artinRelationsSet`: the braid relators
  `(braidWord M i i').prod * (braidWord M i' i).prod⁻¹`.
* `CoxeterMatrix.ArtinGroup`: the presented group.
* `CoxeterMatrix.artinGenerator`: the generator `σᵢ`.
* `CoxeterMatrix.artinLift`: the universal property: any family `g : B → G` in a group satisfying
  the braid relations extends uniquely to a homomorphism `M.ArtinGroup →* G`.

## Main results

* `CoxeterMatrix.prod_braidWord_artinGenerator`: the generators satisfy the braid relations.
* `CoxeterMatrix.artinLift_artinGenerator`, `CoxeterMatrix.artinGroup_hom_ext`.

## References

* E. Brieskorn, K. Saito, *Artin-Gruppen und Coxeter-Gruppen*, Invent. Math. 17 (1972) (check).
-/

namespace CoxeterMatrix

open CoxeterSystem

variable {B : Type*} (M : CoxeterMatrix B)

/-- The Artin relator `σᵢ σᵢ' σᵢ ⋯ (σᵢ' σᵢ σᵢ' ⋯)⁻¹`, both words of length `M i i'`, as an element
of the free group on `B`. It is `1` when `M i i' = 0` or `i = i'`. -/
def artinRelation (i i' : B) : FreeGroup B :=
  ((braidWord M i i').map FreeGroup.of).prod * ((braidWord M i' i).map FreeGroup.of).prod⁻¹

/-- The set of all Artin relators of `M`. -/
def artinRelationsSet : Set (FreeGroup B) := Set.range <| Function.uncurry M.artinRelation

/-- The **Artin group** of a Coxeter matrix `M`: generators `σᵢ` (`i ∈ B`) subject only to the
braid relations `σᵢ σᵢ' σᵢ ⋯ = σᵢ' σᵢ σᵢ' ⋯` (`M i i'` factors on each side). -/
protected def ArtinGroup : Type _ := PresentedGroup M.artinRelationsSet
deriving Group

/-- The standard generator `σᵢ` of the Artin group. -/
def artinGenerator (i : B) : M.ArtinGroup := PresentedGroup.of i

theorem prod_map_artinGenerator (ω : List B) :
    (ω.map M.artinGenerator).prod =
      PresentedGroup.mk M.artinRelationsSet (ω.map FreeGroup.of).prod := by
  rw [map_list_prod, List.map_map]
  rfl

/-- The generators of the Artin group satisfy the braid relations. -/
theorem prod_braidWord_artinGenerator (i i' : B) :
    ((braidWord M i i').map M.artinGenerator).prod =
      ((braidWord M i' i).map M.artinGenerator).prod := by
  rw [prod_map_artinGenerator, prod_map_artinGenerator]
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨(i, i'), rfl⟩

variable {M} {G : Type*} [Group G] (g : B → G)
  (hg : ∀ i i', i ≠ i' → M i i' ≠ 0 →
    ((braidWord M i i').map g).prod = ((braidWord M i' i).map g).prod)

include hg in
theorem lift_artinRelation (i i' : B) : FreeGroup.lift g (M.artinRelation i i') = 1 := by
  rw [artinRelation, map_mul, map_inv, mul_inv_eq_one, map_list_prod, map_list_prod,
    List.map_map, List.map_map]
  have hc : ⇑(FreeGroup.lift g) ∘ FreeGroup.of = g := funext fun _ ↦ FreeGroup.lift_apply_of
  rw [hc]
  by_cases hii : i = i'
  · subst hii
    rfl
  by_cases hm : M i i' = 0
  · simp [braidWord, hm, M.symmetric i' i ▸ hm, alternatingWord]
  exact hg i i' hii hm

/-- The **universal property of the Artin group**: a family of elements of a group satisfying
the braid relations of `M` extends to a homomorphism from `M.ArtinGroup`. -/
def artinLift : M.ArtinGroup →* G :=
  PresentedGroup.toGroup (f := g) (by
    rintro _ ⟨⟨i, i'⟩, rfl⟩
    exact lift_artinRelation g hg i i')

@[simp]
theorem artinLift_artinGenerator (i : B) : artinLift g hg (M.artinGenerator i) = g i :=
  PresentedGroup.toGroup.of _

/-- Homomorphisms out of the Artin group are determined by the images of the generators. -/
@[ext]
theorem artinGroup_hom_ext {φ ψ : M.ArtinGroup →* G}
    (h : ∀ i, φ (M.artinGenerator i) = ψ (M.artinGenerator i)) : φ = ψ :=
  PresentedGroup.ext h

/-- Uniqueness in the universal property. -/
theorem artinLift_unique (φ : M.ArtinGroup →* G) (h : ∀ i, φ (M.artinGenerator i) = g i) :
    φ = artinLift g hg :=
  artinGroup_hom_ext fun i ↦ (h i).trans (artinLift_artinGenerator g hg i).symm

end CoxeterMatrix
