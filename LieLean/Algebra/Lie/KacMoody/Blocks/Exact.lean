/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Blocks

/-!
# Actual exactness of Casimir block restriction

A prerequisite for translation arguments: restrict actual Lie-module morphisms to blocks,
then preserve injectivity, surjectivity, and the middle kernel/image equality of a short
exact sequence. This is stronger than character additivity, but does NOT identify Casimir
blocks with infinitesimal-character blocks and is NOT Humphreys Theorem 7.6.

## References

Humphreys, *Representations of Semisimple Lie Algebras in the BGG Category O*, AMS GSM 94
(2008), §7.1, p. 130 (translation functors are composites of the exact projections onto the
subcategories `O_χ` with tensoring by finite-dimensional modules) and §7.6, Theorem and
Corollary, p. 137 (which use this exactness). The argument below is reconstructed directly from
naturality and the existing Casimir block decomposition, not from a claimed source theorem.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra.IsStandardForm

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H} {S : A.Symmetrization}
  {B : LinearMap.BilinForm K P.KacMoodyAlgebra}
  {U V W : Type*}
  [AddCommGroup U] [Module K U] [LieRingModule P.KacMoodyAlgebra U]
  [LieModule K P.KacMoodyAlgebra U]
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]
  (hB : IsStandardForm P S B) (hA : A.IsGeneralizedCartan)

/-- Restriction of an actual Lie-module morphism to its source and target Casimir blocks. -/
def casimirBlockMap (hV : IsPosFinite P V) (hW : IsPosFinite P W)
    (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (c : K) :
    hB.casimirBlock hA hV c →ₗ⁅K,P.KacMoodyAlgebra⁆ hB.casimirBlock hA hW c :=
  (f.comp (hB.casimirBlock hA hV c).incl).codRestrict _
    fun v ↦ hB.map_mem_casimirBlock hA f hV hW v.property

/-- Block restriction preserves injective morphisms. -/
theorem injective_casimirBlockMap (hV : IsPosFinite P V) (hW : IsPosFinite P W)
    (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (hf : Function.Injective f) (c : K) :
    Function.Injective (hB.casimirBlockMap hA hV hW f c) := by
  intro x y h
  exact Subtype.ext (hf (congrArg Subtype.val h))

/-- Block restriction preserves surjective morphisms between category-O modules. -/
theorem surjective_casimirBlockMap (hV : IsCategoryO P V) (hW : IsCategoryO P W)
    (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (hf : Function.Surjective f) (c : K) :
    Function.Surjective (hB.casimirBlockMap hA hV.isPosFinite hW.isPosFinite f c) := by
  intro w
  obtain ⟨v, hv, hfv⟩ := (LieSubmodule.mem_map _).mp
    (hB.casimirBlock_le_map hA hV hW f hf c w.property)
  exact ⟨⟨v, hv⟩, Subtype.ext hfv⟩

/-- Injective morphisms reflect membership in a Casimir block. No category-O finiteness
is needed beyond existence and naturality of the Casimir operators. -/
theorem mem_casimirBlock_of_injective (hV : IsPosFinite P V) (hW : IsPosFinite P W)
    (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (hf : Function.Injective f) (c : K) {v : V}
    (hv : f v ∈ hB.casimirBlock hA hW c) : v ∈ hB.casimirBlock hA hV c := by
  obtain ⟨k, hk⟩ := (hB.mem_casimirBlock hA hW c).mp hv
  apply (hB.mem_casimirBlock hA hV c).mpr
  refine ⟨k, hf ?_⟩
  rw [hB.map_pow_casimir_sub f hV hW, hk, map_zero]

/-- Actual middle exactness of block restriction for a sequence with injective first map.
Together with the injectivity and surjectivity results, this preserves short exact sequences.
It is a kernel/image equality of Lie-module maps, not just an equality of characters. -/
theorem ker_casimirBlockMap_eq_range (hU : IsPosFinite P U) (hV : IsPosFinite P V)
    (hW : IsPosFinite P W) (f : U →ₗ⁅K,P.KacMoodyAlgebra⁆ V)
    (g : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (hf : Function.Injective f)
    (hex : g.ker = f.range) (c : K) :
    (hB.casimirBlockMap hA hV hW g c).ker =
      (hB.casimirBlockMap hA hU hV f c).range := by
  ext v
  constructor
  · intro hv
    have hgv : g v.val = 0 := congrArg Subtype.val hv
    have hvRange : v.val ∈ f.range := hex ▸ hgv
    obtain ⟨u, hu⟩ := hvRange
    have huBlock : u ∈ hB.casimirBlock hA hU c :=
      hB.mem_casimirBlock_of_injective hA hU hV f hf c (hu ▸ v.property)
    exact ⟨⟨u, huBlock⟩, Subtype.ext hu⟩
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    have hfu : f u.val ∈ g.ker := hex.symm ▸ (show f u.val ∈ f.range from ⟨u.val, rfl⟩)
    exact hfu

end Matrix.Realization.KacMoodyAlgebra.IsStandardForm
