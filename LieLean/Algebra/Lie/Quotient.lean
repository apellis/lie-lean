/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.Quotient

/-!
# Lifting morphisms through quotients of Lie algebras and Lie modules

Additions to `Mathlib.Algebra.Lie.Quotient` (and, for `LieModuleEquiv.ofBijective`, to
`Mathlib.Algebra.Lie.Basic`, which has the analogue `LieEquiv.ofBijective` for Lie algebras).

## Main definitions

* `LieIdeal.mkHom`: the quotient map `L → L ⧸ I` as a morphism of Lie algebras.
* `LieIdeal.lift`: a morphism of Lie algebras `L → L'` vanishing on an ideal `I` induces a
  morphism `L ⧸ I → L'`.
* `LieSubmodule.Quotient.lift`: a morphism of Lie modules `M → M'` vanishing on a submodule `N`
  induces a morphism `M ⧸ N → M'`.
* `LieModuleEquiv.ofBijective`: a bijective morphism of Lie modules is an equivalence.
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

namespace LieSubmodule.Quotient

variable {R L M M' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M]
  [Module R M] [LieRingModule L M] [LieModule R L M] [AddCommGroup M'] [Module R M']
  [LieRingModule L M'] [LieModule R L M'] (N : LieSubmodule R L M)

/-- A morphism of Lie modules vanishing on a submodule `N` factors through `M ⧸ N`. -/
def lift (φ : M →ₗ⁅R,L⁆ M') (hφ : N ≤ φ.ker) : M ⧸ N →ₗ⁅R,L⁆ M' :=
  { N.toSubmodule.liftQ (φ : M →ₗ[R] M') (fun _ hm ↦ hφ hm) with
    map_lie' := by
      intro x m
      induction m using Quotient.inductionOn'
      exact φ.map_lie _ _ }

omit [LieModule R L M'] in
@[simp] lemma lift_mk (φ : M →ₗ⁅R,L⁆ M') (hφ : N ≤ φ.ker) (m : M) :
    lift N φ hφ (mk' N m) = φ m := rfl

omit [LieModule R L M'] in
lemma lift_surjective (φ : M →ₗ⁅R,L⁆ M') (hφ : N ≤ φ.ker) (hs : Function.Surjective φ) :
    Function.Surjective (lift N φ hφ) := fun m' ↦ by
  obtain ⟨m, rfl⟩ := hs m'
  exact ⟨mk' N m, rfl⟩

end LieSubmodule.Quotient

namespace LieModuleEquiv

variable {R L M N : Type*} [CommRing R] [LieRing L] [AddCommGroup M]
  [Module R M] [LieRingModule L M] [AddCommGroup N] [Module R N] [LieRingModule L N]

/-- A bijective morphism of Lie modules is an equivalence of Lie modules. -/
noncomputable def ofBijective (f : M →ₗ⁅R,L⁆ N) (hf : Function.Bijective f) : M ≃ₗ⁅R,L⁆ N :=
  { f, LinearEquiv.ofBijective (f : M →ₗ[R] N) hf with }

@[simp] lemma ofBijective_apply (f : M →ₗ⁅R,L⁆ N) (hf : Function.Bijective f) (m : M) :
    ofBijective f hf m = f m :=
  rfl

end LieModuleEquiv
