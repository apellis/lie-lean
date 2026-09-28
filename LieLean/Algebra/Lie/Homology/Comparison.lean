/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.ChainComplex

/-!
# Comparison with categorical Lie algebra homology

The concrete homology `LieModule.ChevalleyEilenberg.homology`, realized as the image of the
cycles in the quotient of `⋀L ⊗ M` by the boundaries, agrees with Mathlib's homology of the
Chevalley–Eilenberg chain complex, in every degree over any commutative ring.

## Main definitions

* `LieModule.ChevalleyEilenberg.chainComplexHomologyIso`: the comparison isomorphism.
* `LieModule.ChevalleyEilenberg.chainComplexHomologyIso_naturality`: compatibility with
  morphisms of coefficient modules.
* `LieModule.ChevalleyEilenberg.chainComplexHomologyIso_homologyπ`: compatibility with the
  homology class of a cycle.

## References

The comparison is reconstructed directly from the definitions of cycles and boundaries and
Mathlib's `ShortComplex.LeftHomologyData`; no external result is assumed.
-/

open CategoryTheory TensorProduct ExteriorAlgebra

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LieModule.ChevalleyEilenberg

universe u v w

variable (R : Type u) (L : Type v) (M : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {R L M} in
/-- A chain is a cycle precisely when its inclusion in `⋀L ⊗ M` is a concrete cycle,
including in degree zero. -/
lemma incl_mem_cycles_iff (k : ℕ) (t : ⋀[R]^k L ⊗[R] M) :
    incl R L M k t ∈ cycles R L M k ↔ ((chainComplex R L M).sc k).g t = 0 := by
  cases k with
  | zero =>
    simp only [cycles_zero, chainsIn, LinearMap.mem_range_self, true_iff]
    simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
  | succ k =>
    rw [incl_mem_cycles_succ_iff]
    change _ ↔ ((chainComplex R L M).d (k + 1)
      ((ComplexShape.down ℕ).next (k + 1))).hom t = 0
    erw [ChainComplex.next_nat_succ, chainComplex_d]
    rfl

variable {R L M} in
/-- A chain represents a boundary in `⋀L ⊗ M` iff it is in the range of the incoming
chain differential. -/
lemma incl_mem_boundaries_iff (k : ℕ) (t : ⋀[R]^k L ⊗[R] M) :
    incl R L M k t ∈ boundaries R L M k ↔
      t ∈ LinearMap.range (((chainComplex R L M).sc k).f.hom) := by
  rw [boundaries_eq_map_d]
  simp only [Submodule.mem_map, (incl_injective k).eq_iff, exists_eq_right]
  change _ ↔ t ∈ LinearMap.range
    (((chainComplex R L M).d ((ComplexShape.down ℕ).prev k) k).hom)
  erw [ChainComplex.prev, chainComplex_d]
  rfl

/-- The concrete homology class of a cycle of the categorical chain complex. -/
def chainComplexCyclesToHomology (k : ℕ) :
    LinearMap.ker (((chainComplex R L M).sc k).g.hom) →ₗ[R] homology R L M k :=
  (((boundaries R L M k).mkQ ∘ₗ incl R L M k).domRestrict _).codRestrict _ fun t ↦
    ⟨_, (incl_mem_cycles_iff k t.1).mpr t.2, rfl⟩

variable {R L M} in
lemma chainComplexCyclesToHomology_surjective (k : ℕ) :
    Function.Surjective (chainComplexCyclesToHomology R L M k) := by
  rintro ⟨x, c, hc, rfl⟩
  obtain ⟨t, rfl⟩ := hc.1
  exact ⟨⟨t, (incl_mem_cycles_iff k t).mp hc⟩, rfl⟩

variable {R L M} in
lemma chainComplexCyclesToHomology_exact (k : ℕ) :
    Function.Exact ((chainComplex R L M).sc k).moduleCatToCycles
      (chainComplexCyclesToHomology R L M k) := by
  intro t
  change (⟨_, _⟩ : homology R L M k) = 0 ↔ _
  rw [Subtype.ext_iff]
  change (boundaries R L M k).mkQ (incl R L M k t.1) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, incl_mem_boundaries_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩

/-- Concrete left homology data for the Chevalley–Eilenberg chain complex: cycles are the
kernel of its outgoing differential, and homology is the image of concrete cycles modulo
boundaries. This is a direct verification of the two universal properties. -/
def chainComplexLeftHomologyData (k : ℕ) :
    ((chainComplex R L M).sc k).LeftHomologyData where
  K := ModuleCat.of R (LinearMap.ker (((chainComplex R L M).sc k).g.hom))
  H := ModuleCat.of R (homology R L M k)
  i := ModuleCat.ofHom (LinearMap.ker (((chainComplex R L M).sc k).g.hom)).subtype
  π := ModuleCat.ofHom (chainComplexCyclesToHomology R L M k)
  wi := by ext t; exact t.2
  hi := ModuleCat.kernelIsLimit _
  wπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact (chainComplexCyclesToHomology_exact k).apply_apply_eq_zero t
  hπ := ModuleCat.isColimitCokernelCofork _ _ (chainComplexCyclesToHomology_exact k)
    (chainComplexCyclesToHomology_surjective k)

/-- The concrete Lie algebra homology is isomorphic to Mathlib's chain-complex homology
in every degree, over any commutative ring. Reconstructed from the two definitions using
Mathlib's kernel and cokernel universal properties. -/
def chainComplexHomologyIso (k : ℕ) :
    (chainComplex R L M).homology k ≅ ModuleCat.of R (homology R L M k) :=
  (chainComplexLeftHomologyData R L M k).homologyIso

/-- The comparison sends a categorical homology class to the class of the same cycle in
`(⋀L ⊗ M) / B_k`. -/
@[reassoc]
lemma chainComplexHomologyIso_homologyπ (k : ℕ) :
    (chainComplex R L M).homologyπ k ≫ (chainComplexHomologyIso R L M k).hom =
      (chainComplexLeftHomologyData R L M k).cyclesIso.hom ≫
        ModuleCat.ofHom (chainComplexCyclesToHomology R L M k) :=
  (chainComplexLeftHomologyData R L M k).homologyπ_comp_homologyIso_hom

variable {R L M}
variable {N : Type w} [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- A coefficient morphism acts on the concrete cycles and homology used in the comparison.
Compatibility follows from the inclusion of chains and the quotient map on boundaries. -/
def chainComplexLeftHomologyMapData (k : ℕ) (f : M →ₗ⁅R,L⁆ N) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) k).map
        (chainComplexMap f))
      (chainComplexLeftHomologyData R L M k) (chainComplexLeftHomologyData R L N k) where
  φK := ModuleCat.ofHom (((mapChains R L k f).domRestrict _).codRestrict _ fun t ↦ by
    apply (incl_mem_cycles_iff k _).mp
    change incl R L N k (mapChains R L k f t.1) ∈ cycles R L N k
    rw [incl_mapChains]
    exact lTensor_mem_cycles f ((incl_mem_cycles_iff k t.1).mpr t.2))
  φH := ModuleCat.ofHom (homologyMap R L k f)
  commi := by ext t; rfl
  commf' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    exact (congrArg (fun g ↦ (ModuleCat.Hom.hom g) t)
      ((chainComplexMap f).comm ((ComplexShape.down ℕ).prev k) k)).symm
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    change Submodule.Quotient.mk ((f : M →ₗ[R] N).lTensor _ (incl R L M k t.1)) =
      Submodule.Quotient.mk (incl R L N k (mapChains R L k f t.1))
    rw [incl_mapChains]

/-- The comparison with Mathlib's homology is natural in the coefficient module. -/
theorem chainComplexHomologyIso_naturality (k : ℕ) (f : M →ₗ⁅R,L⁆ N) :
    HomologicalComplex.homologyMap (chainComplexMap f) k ≫
        (chainComplexHomologyIso R L N k).hom =
      (chainComplexHomologyIso R L M k).hom ≫ ModuleCat.ofHom (homologyMap R L k f) :=
  (chainComplexLeftHomologyMapData k f).homologyMap_comm

end LieModule.ChevalleyEilenberg
