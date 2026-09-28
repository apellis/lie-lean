/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaPBW
import LieLean.Algebra.Lie.Homology.Vanishing

/-!
# Reduction of Verma acyclicity to the left-regular CE complex

## Main definitions / results

* `UniversalEnvelopingAlgebra.LeftRegular`: a separate coefficient type, with action
  `x • u = ι(x) * u`, not the adjoint action.
* `LieModule.ChevalleyEilenberg.homologyEquiv`: coefficient equivalences induce equivalences
  of the actual concrete CE homology in every degree.
* `VermaModule.homologyEquivLeftRegular`: PBW identifies actual Verma homology with
  left-regular enveloping homology.
* `VermaModule.subsingleton_homology_succ_iff_leftRegular_exact`: the precise remaining
  range/kernel equality needed for positive-degree Verma acyclicity.

This is a reduction, NOT a proof of positive-degree acyclicity. The missing theorem is
exactness in positive degrees of the left-regular CE complex for a general Lie algebra.
No BGG exactness or irreducible-module homology computation is used.

## References

Reconstructed from the existing PBW module equivalence and CE functoriality. No external
source consulted for this reduction.
-/

noncomputable section

namespace UniversalEnvelopingAlgebra

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

instance : LieRingModule L (LeftRegular R L) := lieRingModuleOfModule R L _

instance : LieModule R L (LeftRegular R L) := lieModuleOfModule R L _

/-- The underlying linear identification forgets only the coefficient-type tag. -/
def equiv : LeftRegular R L ≃ₗ[R] UniversalEnvelopingAlgebra R L := LinearEquiv.refl R _

/-- The action is left multiplication, not the commutator action. -/
@[simp] theorem equiv_lie (x : L) (u : LeftRegular R L) :
    equiv R L ⁅x, u⁆ = ι R x * equiv R L u := rfl

end LeftRegular
end UniversalEnvelopingAlgebra

namespace LieModule.ChevalleyEilenberg

variable {R L M N : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- A coefficient equivalence induces an equivalence of the actual CE homology.
Reconstructed directly from `homologyMap_comp` and `homologyMap_id`. -/
def homologyEquiv (e : M ≃ₗ⁅R,L⁆ N) (k : ℕ) :
    homology R L M k ≃ₗ[R] homology R L N k :=
  { homologyMap R L k e.toLieModuleHom with
    invFun := homologyMap R L k e.symm.toLieModuleHom
    left_inv := by
      intro x
      change (homologyMap R L k e.symm.toLieModuleHom ∘ₗ
        homologyMap R L k e.toLieModuleHom) x = x
      rw [← homologyMap_comp]
      have h : e.symm.toLieModuleHom.comp e.toLieModuleHom = LieModuleHom.id := by
        ext m
        exact e.symm_apply_apply m
      rw [h, homologyMap_id, LinearMap.id_apply]
    right_inv := by
      intro x
      change (homologyMap R L k e.toLieModuleHom ∘ₗ
        homologyMap R L k e.symm.toLieModuleHom) x = x
      rw [← homologyMap_comp]
      have h : e.toLieModuleHom.comp e.symm.toLieModuleHom = LieModuleHom.id := by
        ext m
        exact e.apply_symm_apply m
      rw [h, homologyMap_id, LinearMap.id_apply] }

end LieModule.ChevalleyEilenberg

namespace Matrix.Realization.KacMoodyAlgebra.VermaModule

open UniversalEnvelopingAlgebra LieModule.ChevalleyEilenberg

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (Λ : Module.Dual K H)

/-- PBW is an equivalence of negative-nilradical modules with LEFT REGULAR coefficients.
Reconstructed from `equivEnvNNeg_mul`. No finiteness or symmetrizability is imposed on A. -/
def equivLeftRegular : LeftRegular K (nNeg P) ≃ₗ⁅K,nNeg P⁆ VermaModule P Λ :=
  { (LeftRegular.equiv K (nNeg P)).trans (equivEnvNNeg P Λ) with
    map_lie' := by
      intro x u
      change equivEnvNNeg P Λ (UniversalEnvelopingAlgebra.ι K x *
        LeftRegular.equiv K (nNeg P) u) = ⁅(x : P.KacMoodyAlgebra), equivEnvNNeg P Λ _⁆
      rw [equivEnvNNeg_mul, UniversalEnvelopingAlgebra.map_ι, lie_eq_smul]
      rfl }

/-- Actual Verma CE homology equals left-regular CE homology in every degree.
This transports homology; it does not assert that either side vanishes. -/
def homologyEquivLeftRegular (k : ℕ) :
    homology K (nNeg P) (VermaModule P Λ) k ≃ₗ[K]
      homology K (nNeg P) (LeftRegular K (nNeg P)) k :=
  homologyEquiv (equivLeftRegular P Λ).symm k

/-- The exact, still unproved regular-CE obligation for positive-degree Verma acyclicity.
Reconstructed from the coefficient equivalence and the concrete CE vanishing criterion. -/
theorem subsingleton_homology_succ_iff_leftRegular_exact (k : ℕ) :
    Subsingleton (homology K (nNeg P) (VermaModule P Λ) (k + 1)) ↔
      LinearMap.range (d K (nNeg P) (LeftRegular K (nNeg P)) (k + 1)) =
        LinearMap.ker (d K (nNeg P) (LeftRegular K (nNeg P)) k) := by
  rw [← subsingleton_homology_succ_iff]
  exact (homologyEquivLeftRegular P Λ (k + 1)).toEquiv.subsingleton_congr

end Matrix.Realization.KacMoodyAlgebra.VermaModule
