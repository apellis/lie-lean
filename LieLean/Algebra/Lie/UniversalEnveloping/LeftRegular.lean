/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping

/-!
# The left-regular module of the enveloping algebra

`UniversalEnvelopingAlgebra.LeftRegular R L` is the enveloping algebra `U(L)` regarded as a Lie
module over `L` by left multiplication, `x • u = ι(x) * u` (not by the adjoint action). It is the
coefficient module of the Koszul resolution `⋀L ⊗ U(L)` of the trivial module.

## Main definitions

* `UniversalEnvelopingAlgebra.LeftRegular`: the coefficient type, with its Lie module structure.
* `UniversalEnvelopingAlgebra.LeftRegular.equiv`: the identification with `U(L)`.
* `UniversalEnvelopingAlgebra.LeftRegular.mulRight`: right multiplication by `u ∈ U(L)`, a
  morphism of Lie modules.
-/

noncomputable section

namespace UniversalEnvelopingAlgebra

attribute [local instance] LieRing.ofAssociativeRing

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The enveloping algebra as a separate coefficient type for its left-regular action. -/
def LeftRegular := UniversalEnvelopingAlgebra R L

namespace LeftRegular

instance : AddCommGroup (LeftRegular R L) :=
  inferInstanceAs (AddCommGroup (UniversalEnvelopingAlgebra R L))

instance : Module R (LeftRegular R L) :=
  inferInstanceAs (Module R (UniversalEnvelopingAlgebra R L))

instance : Module (UniversalEnvelopingAlgebra R L) (LeftRegular R L) :=
  inferInstanceAs (Module (UniversalEnvelopingAlgebra R L) (UniversalEnvelopingAlgebra R L))

instance : IsScalarTower R (UniversalEnvelopingAlgebra R L) (LeftRegular R L) :=
  inferInstanceAs (IsScalarTower R (UniversalEnvelopingAlgebra R L)
    (UniversalEnvelopingAlgebra R L))

instance : LieRingModule L (LeftRegular R L) where
  bracket x u := (ι R x : UniversalEnvelopingAlgebra R L) • u
  add_lie x y u := by
    change ι R (x + y) • u = ι R x • u + ι R y • u
    rw [map_add, add_smul]
  lie_add x u v := smul_add (ι R x) u v
  leibniz_lie x y u := by
    change ι R x • ι R y • u = ι R ⁅x, y⁆ • u + ι R y • ι R x • u
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, sub_smul, mul_smul, mul_smul]
    abel

instance : LieModule R L (LeftRegular R L) where
  smul_lie t x u := by
    change ι R (t • x) • u = t • ι R x • u
    rw [map_smul, smul_assoc]
  lie_smul t x u := smul_comm (ι R x) t u

/-- The underlying linear identification forgets only the coefficient-type tag. -/
def equiv : LeftRegular R L ≃ₗ[R] UniversalEnvelopingAlgebra R L := LinearEquiv.refl R _

/-- The action is left multiplication, not the commutator action. -/
@[simp] theorem equiv_lie (x : L) (u : LeftRegular R L) :
    equiv R L ⁅x, u⁆ = ι R x * equiv R L u := rfl

variable {R L}

/-- Right multiplication `v ↦ v u` on the left-regular module is a morphism of Lie modules. -/
def mulRight (u : UniversalEnvelopingAlgebra R L) : LeftRegular R L →ₗ⁅R,L⁆ LeftRegular R L where
  toLinearMap := (equiv R L).symm.toLinearMap ∘ₗ LinearMap.mulRight R u ∘ₗ (equiv R L).toLinearMap
  map_lie' {x v} := by
    exact mul_assoc (ι R x) (equiv R L v) u

@[simp] theorem equiv_mulRight (u : UniversalEnvelopingAlgebra R L) (v : LeftRegular R L) :
    equiv R L (mulRight u v) = equiv R L v * u := rfl

end LeftRegular

end UniversalEnvelopingAlgebra
