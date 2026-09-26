/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.Quotient

/-!
# Lifting morphisms through quotients of Lie algebras

Additions to `Mathlib.Algebra.Lie.Quotient`.

## Main definitions

* `LieIdeal.mkHom`: the quotient map `L → L ⧸ I` as a morphism of Lie algebras.
* `LieIdeal.lift`: a morphism of Lie algebras `L → L'` vanishing on an ideal `I` induces a
  morphism `L ⧸ I → L'`.
-/

namespace LieIdeal

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L'] (I : LieIdeal R L)

/-- The quotient map `L → L ⧸ I` as a morphism of Lie algebras. -/
def mkHom : L →ₗ⁅R⁆ L ⧸ I :=
  { (LieSubmodule.Quotient.mk' I : L →ₗ[R] L ⧸ I) with
    map_lie' := fun {_ _} ↦ LieSubmodule.Quotient.mk_bracket _ _ _ }

@[simp] lemma mkHom_apply (x : L) : mkHom I x = LieSubmodule.Quotient.mk x := rfl

lemma mkHom_surjective : Function.Surjective (mkHom I) := LieSubmodule.Quotient.surjective_mk' I

lemma mkHom_eq_zero_iff {x : L} : mkHom I x = 0 ↔ x ∈ I := LieSubmodule.Quotient.mk_eq_zero'

/-- A morphism of Lie algebras vanishing on an ideal `I` factors through `L ⧸ I`. -/
def lift (f : L →ₗ⁅R⁆ L') (hf : I ≤ f.ker) : L ⧸ I →ₗ⁅R⁆ L' :=
  { (I : Submodule R L).liftQ (f : L →ₗ[R] L') (fun x hx ↦ by
      have := hf hx
      simpa using this) with
    map_lie' := by
      intro x y
      induction x using Quotient.inductionOn'
      induction y using Quotient.inductionOn'
      exact f.map_lie _ _ }

@[simp] lemma lift_mk (f : L →ₗ⁅R⁆ L') (hf : I ≤ f.ker) (x : L) :
    lift I f hf (LieSubmodule.Quotient.mk x) = f x := rfl

@[simp] lemma lift_mkHom (f : L →ₗ⁅R⁆ L') (hf : I ≤ f.ker) (x : L) :
    lift I f hf (mkHom I x) = f x := rfl

@[simp] lemma lift_comp_mkHom (f : L →ₗ⁅R⁆ L') (hf : I ≤ f.ker) :
    (lift I f hf).comp (mkHom I) = f := rfl

lemma lieHom_ext {g₁ g₂ : L ⧸ I →ₗ⁅R⁆ L'}
    (h : ∀ x, g₁ (LieSubmodule.Quotient.mk x) = g₂ (LieSubmodule.Quotient.mk x)) : g₁ = g₂ := by
  ext x
  induction x using Quotient.inductionOn'
  exact h _

end LieIdeal
