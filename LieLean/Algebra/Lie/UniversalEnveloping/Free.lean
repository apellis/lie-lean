/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.UniversalEnveloping.TensorDecomposition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# `U(L)` is a free module over `U(L')`

Let `L'` be a Lie subalgebra of a Lie algebra `L` over a commutative ring `R`. Through the algebra
map `U(L') → U(L)` induced by the inclusion, `U(L)` is a left `U(L')`-module. If `L'` and a
complementary submodule `V` are free `R`-modules, then `U(L)` is a free `U(L')`-module, with basis
the ordered monomials in a (linearly ordered) basis of `V`. In particular `U(L') → U(L)` is
injective. Over a field every subalgebra has such a complement.

## Main definitions

* `UniversalEnvelopingAlgebra.instModuleLieSubalgebra`: the left `U(L')`-module
  structure on `U(L)`, `u • v = map L'.incl u * v`.
* `UniversalEnvelopingAlgebra.pbwBasisOfIsCompl`: the `U(L')`-basis of `U(L)` given by the
  ordered monomials in a basis of a complement of `L'`.

## Main results

* `UniversalEnvelopingAlgebra.free_of_isCompl`, and over a field the instance
  `UniversalEnvelopingAlgebra.instFreeLieSubalgebra`: `U(L)` is a free `U(L')`-module.
* `UniversalEnvelopingAlgebra.map_incl_injective_of_isCompl_submodule`,
  `UniversalEnvelopingAlgebra.map_incl_injective`: `U(L') → U(L)` is injective.

## References

* J. E. Humphreys, *Introduction to Lie algebras and representation theory*, GTM 9, §17.3,
  Corollary D.
* N. Bourbaki, *Lie groups and Lie algebras*, Ch. I, §2.7, Cor. 5.
-/

open Finsupp Module

noncomputable section

namespace UniversalEnvelopingAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (L' : LieSubalgebra R L)

/-- `U(L)` is a left `U(L')`-module via `U(L') → U(L)`. -/
instance instModuleLieSubalgebra :
    Module (UniversalEnvelopingAlgebra R L') (UniversalEnvelopingAlgebra R L) :=
  (map L'.incl).toRingHom.toModule

variable {L'}

theorem lieSubalgebra_smul_def (u : UniversalEnvelopingAlgebra R L')
    (v : UniversalEnvelopingAlgebra R L) :
    u • v = map L'.incl u * v := rfl

instance : IsScalarTower R (UniversalEnvelopingAlgebra R L') (UniversalEnvelopingAlgebra R L) where
  smul_assoc r u v := by
    rw [lieSubalgebra_smul_def, lieSubalgebra_smul_def, map_smul, smul_mul_assoc]

variable {V : Submodule R L} (h : IsCompl L'.toSubmodule V)
variable {σ₁ σ₂ : Type*} (b₁ : Basis σ₁ R L') (b₂ : Basis σ₂ R V)

namespace PBW

/-- The basis of `L` indexed by `σ₁ ⊕ₗ σ₂` obtained from a basis of the Lie subalgebra `L'` and a
basis of a complementary submodule `V`. -/
def basisOfIsComplSubmodule : Basis (σ₁ ⊕ₗ σ₂) R L :=
  ((b₁.prod b₂).map (Submodule.prodEquivOfIsCompl _ _ h)).reindex toLex

theorem basisOfIsComplSubmodule_inl (i : σ₁) :
    basisOfIsComplSubmodule h b₁ b₂ (toLex (Sum.inl i)) = L'.incl (b₁ i) := by
  simp only [basisOfIsComplSubmodule, Basis.reindex_apply, Equiv.symm_apply_apply,
    Basis.map_apply, Basis.prod_apply]
  exact add_zero _

theorem basisOfIsComplSubmodule_inr (i : σ₂) :
    basisOfIsComplSubmodule h b₁ b₂ (toLex (Sum.inr i)) = b₂ i := by
  simp only [basisOfIsComplSubmodule, Basis.reindex_apply, Equiv.symm_apply_apply,
    Basis.map_apply, Basis.prod_apply]
  exact zero_add _

variable [LinearOrder σ₁] [LinearOrder σ₂]

/-- The product of an ordered monomial of `U(L')` and an ordered monomial in the basis of the
complement is an ordered monomial of `U(L)` for the combined basis. -/
theorem map_pbwMonomial_mul_pbwMonomial (s₁ : σ₁ →₀ ℕ) (s₂ : σ₂ →₀ ℕ) :
    map L'.incl (pbwMonomial R b₁ s₁) * pbwMonomial R (fun i ↦ (b₂ i : L)) s₂ =
      pbwMonomial R (basisOfIsComplSubmodule h b₁ b₂) (lexFinsuppEquiv (s₁, s₂)) := by
  rw [lexFinsuppEquiv_apply, pbwMonomial_mapDomain_add, map_pbwMonomial]
  congr 2 <;> ext i <;> simp [basisOfIsComplSubmodule_inl, basisOfIsComplSubmodule_inr]

include h b₁ in
/-- The ordered monomials in a basis of the complement `V` form a `U(L')`-basis of `U(L)`. -/
theorem linearCombination_bijective :
    Function.Bijective (Finsupp.linearCombination (UniversalEnvelopingAlgebra R L')
      (pbwMonomial R (fun i ↦ (b₂ i : L)))) := by
  let B := Finsupp.basis fun _ : σ₂ →₀ ℕ ↦ pbwBasis b₁
  let e : (Σ _ : σ₂ →₀ ℕ, σ₁ →₀ ℕ) ≃ (σ₁ ⊕ₗ σ₂ →₀ ℕ) :=
    ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _)).trans lexFinsuppEquiv
  have : (Finsupp.linearCombination (UniversalEnvelopingAlgebra R L')
      (pbwMonomial R (fun i ↦ (b₂ i : L)))).restrictScalars R =
      (B.equiv (pbwBasis (basisOfIsComplSubmodule h b₁ b₂)) e : _ →ₗ[R] _) :=
    B.ext fun ⟨s₂, s₁⟩ ↦ by
      rw [LinearEquiv.coe_coe, Basis.equiv_apply, pbwBasis_apply]
      simp only [B, coe_basis, pbwBasis_apply, LinearMap.coe_restrictScalars,
        linearCombination_single, lieSubalgebra_smul_def]
      exact map_pbwMonomial_mul_pbwMonomial h b₁ b₂ s₁ s₂
  rw [← LinearMap.coe_restrictScalars R, this]
  exact LinearEquiv.bijective _

end PBW

open PBW

variable [LinearOrder σ₂]

/-- **Corollary of PBW**: let `L'` be a Lie subalgebra of `L` which is free as an `R`-module and
has a complementary submodule `V` with a basis `b₂` indexed by a linearly ordered type. Then
`U(L)` is a free left `U(L')`-module, with basis the ordered monomials in the `b₂ i`. -/
def pbwBasisOfIsCompl [Module.Free R L'] :
    Basis (σ₂ →₀ ℕ) (UniversalEnvelopingAlgebra R L') (UniversalEnvelopingAlgebra R L) :=
  let : LinearOrder (Free.ChooseBasisIndex R L') := IsWellOrder.linearOrder WellOrderingRel
  Basis.ofRepr (LinearEquiv.ofBijective _
    (linearCombination_bijective h (Free.chooseBasis R L') b₂)).symm

@[simp] theorem pbwBasisOfIsCompl_apply [Module.Free R L'] (s : σ₂ →₀ ℕ) :
    pbwBasisOfIsCompl h b₂ s = pbwMonomial R (fun i ↦ (b₂ i : L)) s := by
  simp [pbwBasisOfIsCompl, Basis.coe_ofRepr]

section Free

variable [Module.Free R L'] [Module.Free R V]

include h in
/-- **Corollary of PBW**: if a Lie subalgebra `L'` of `L` and a complementary submodule `V` are
free `R`-modules, then `U(L)` is a free left `U(L')`-module (for the action through
`U(L') → U(L)`). See Humphreys, *Introduction to Lie algebras and representation theory*, §17.3,
Corollary D, stated there over a field; the basis is `pbwBasisOfIsCompl`. -/
theorem free_of_isCompl :
    Module.Free (UniversalEnvelopingAlgebra R L') (UniversalEnvelopingAlgebra R L) :=
  let : LinearOrder (Free.ChooseBasisIndex R V) := IsWellOrder.linearOrder WellOrderingRel
  .of_basis (pbwBasisOfIsCompl h (Free.chooseBasis R V))

include h in
/-- **Corollary of PBW**: if a Lie subalgebra `L'` of `L` and a complementary submodule are free
`R`-modules, then `U(L') → U(L)` is injective. See Humphreys, §17.3, Corollary D. -/
theorem map_incl_injective_of_isCompl_submodule : Function.Injective (map L'.incl) := by
  let : LinearOrder (Free.ChooseBasisIndex R V) := IsWellOrder.linearOrder WellOrderingRel
  set B := pbwBasisOfIsCompl h (Free.chooseBasis R V)
  have h0 : B 0 = 1 := by rw [pbwBasisOfIsCompl_apply, pbwMonomial_zero]
  intro u u' e
  have := congr_arg (fun x ↦ B.repr x 0) (show u • B 0 = u' • B 0 by
    rw [h0, lieSubalgebra_smul_def, lieSubalgebra_smul_def, mul_one, mul_one, e])
  simpa using this

end Free

section Field

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] (L' : LieSubalgebra K L)

/-- **Corollary of PBW**: over a field, `U(L)` is a free `U(L')`-module for every Lie subalgebra
`L'` of `L`. See Humphreys, *Introduction to Lie algebras and representation theory*, §17.3,
Corollary D. -/
instance instFreeLieSubalgebra :
    Module.Free (UniversalEnvelopingAlgebra K L') (UniversalEnvelopingAlgebra K L) :=
  let ⟨_, h⟩ := L'.toSubmodule.exists_isCompl
  free_of_isCompl h

/-- **Corollary of PBW**: over a field, `U(L') → U(L)` is injective for every Lie subalgebra `L'`
of `L`. See Humphreys, *Introduction to Lie algebras and representation theory*, §17.3,
Corollary D. -/
theorem map_incl_injective : Function.Injective (map L'.incl) :=
  let ⟨_, h⟩ := L'.toSubmodule.exists_isCompl
  map_incl_injective_of_isCompl_submodule h

end Field

end UniversalEnvelopingAlgebra
