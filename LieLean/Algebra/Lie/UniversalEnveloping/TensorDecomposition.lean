/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.UniversalEnveloping.PBW
import Mathlib.Data.Sum.Order
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor decomposition of the universal enveloping algebra

Let `L` be a Lie algebra over a commutative ring `R` and let `L₁`, `L₂` be Lie subalgebras of `L`
whose underlying submodules are complementary and free. A consequence of the
Poincaré–Birkhoff–Witt theorem is that multiplication
`U(L₁) ⊗[R] U(L₂) → U(L)`, `u ⊗ v ↦ u * v`, is an isomorphism of `R`-modules. In particular
`U(L₁) → U(L)` is injective.

## Main definitions

* `UniversalEnvelopingAlgebra.map`: the algebra map `U(L₁) →ₐ[R] U(L₂)` induced by a morphism of
  Lie algebras `L₁ →ₗ⁅R⁆ L₂`.
* `UniversalEnvelopingAlgebra.mulMap`: for Lie subalgebras `L₁`, `L₂` of `L`, the linear map
  `U(L₁) ⊗[R] U(L₂) → U(L)`, `u ⊗ v ↦ u * v`.
* `UniversalEnvelopingAlgebra.tensorEquivOfIsCompl`: the linear isomorphism
  `U(L₁) ⊗[R] U(L₂) ≃ₗ[R] U(L)` for complementary free Lie subalgebras.
* `UniversalEnvelopingAlgebra.PBW.basisOfIsCompl`: the basis of `L` indexed by `σ₁ ⊕ₗ σ₂` built
  from bases of complementary Lie subalgebras (auxiliary).

## Main results

* `UniversalEnvelopingAlgebra.mulMap_bijective_of_isCompl`: if `L₁`, `L₂` are Lie subalgebras
  whose underlying submodules are free and complementary then `mulMap L₁ L₂` is bijective.
* `UniversalEnvelopingAlgebra.map_incl_injective_of_isCompl`: under the same hypotheses the
  induced map `U(L₁) → U(L)` is injective.
* `UniversalEnvelopingAlgebra.mulMap_bijective_of_basis`,
  `UniversalEnvelopingAlgebra.map_incl_injective_of_basis`: versions with given ordered bases.

## Proof

Choose linearly ordered bases `b₁`, `b₂` of `L₁`, `L₂`. They combine to a basis `b` of `L`
indexed by the lexicographic sum `σ₁ ⊕ₗ σ₂`, in which every index of `σ₁` precedes every index
of `σ₂`. Hence every ordered monomial for `b` is the product of an ordered monomial for `b₁` and
one for `b₂` (`UniversalEnvelopingAlgebra.pbwMonomial_mapDomain_add`), so the multiplication map
sends the tensor product of the PBW bases of `U(L₁)` and `U(L₂)` bijectively onto the PBW basis
of `U(L)`.

## References

* N. Bourbaki, *Lie groups and Lie algebras*, Ch. I, §2.7, Corollaries 5 (a) and 6.
* J. E. Humphreys, *Introduction to Lie algebras and representation theory*, GTM 9, §17.3
  (Corollary D for the injectivity of `U(L₁) → U(L)`).

The argument, that of the proof of Bourbaki's Corollary 6, is reconstructed
from the PBW basis (`UniversalEnvelopingAlgebra.pbwBasis`).
-/

open Finsupp Module TensorProduct

noncomputable section

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L L' L'' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L'] [LieRing L''] [LieAlgebra R L'']

section Map

variable (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'')

/-- The algebra morphism `U(L) →ₐ[R] U(L')` induced by a morphism of Lie algebras
`f : L →ₗ⁅R⁆ L'`. -/
def map : UniversalEnvelopingAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R L' :=
  lift R ((ι R).comp f)

@[simp] theorem map_ι (x : L) : map f (ι R x) = ι R (f x) := by
  simp [map]

@[simp] theorem map_id : map (LieHom.id : L →ₗ⁅R⁆ L) = AlgHom.id R _ := by
  ext x
  change map _ (ι R x) = ι R x
  rw [map_ι]
  rfl

theorem map_comp : map (g.comp f) = (map g).comp (map f) := by
  ext x
  change map _ (ι R x) = map g (map f (ι R x))
  rw [map_ι, map_ι, map_ι]
  rfl

/-- The image of an ordered monomial under `map f`. -/
theorem map_pbwMonomial {σ : Type*} [LinearOrder σ] (v : σ → L) (s : σ →₀ ℕ) :
    map f (pbwMonomial R v s) = pbwMonomial R (f ∘ v) s := by
  rw [pbwMonomial, pbwMonomial, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ map_ι f (v i)

end Map

section Lex

variable {σ₁ σ₂ : Type*} [LinearOrder σ₁] [LinearOrder σ₂]

/-- For the lexicographic sum `σ₁ ⊕ₗ σ₂`, every ordered monomial is the product of an ordered
monomial in the indices from `σ₁` and one in the indices from `σ₂`. -/
theorem pbwMonomial_mapDomain_add (v : σ₁ ⊕ₗ σ₂ → L) (s₁ : σ₁ →₀ ℕ) (s₂ : σ₂ →₀ ℕ) :
    pbwMonomial R v (s₁.mapDomain (toLex ∘ Sum.inl) + s₂.mapDomain (toLex ∘ Sum.inr)) =
      pbwMonomial R (v ∘ toLex ∘ Sum.inl) s₁ * pbwMonomial R (v ∘ toLex ∘ Sum.inr) s₂ := by
  set f₁ : σ₁ → σ₁ ⊕ₗ σ₂ := toLex ∘ Sum.inl
  set f₂ : σ₂ → σ₁ ⊕ₗ σ₂ := toLex ∘ Sum.inr
  have hsort : ((toMultiset (s₁.mapDomain f₁ + s₂.mapDomain f₂)).sort (· ≤ ·)) =
      ((toMultiset s₁).sort (· ≤ ·)).map f₁ ++ ((toMultiset s₂).sort (· ≤ ·)).map f₂ := by
    refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Multiset.pairwise_sort _ _) ?_ ?_
    · rw [List.pairwise_append, List.pairwise_map, List.pairwise_map]
      refine ⟨(Multiset.pairwise_sort _ _).imp fun h ↦ ?_,
        (Multiset.pairwise_sort _ _).imp fun h ↦ ?_, fun _ ha _ hb ↦ ?_⟩
      · exact Sum.Lex.inl_le_inl_iff.2 h
      · exact Sum.Lex.inr_le_inr_iff.2 h
      · obtain ⟨a, -, rfl⟩ := List.mem_map.1 ha
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hb
        exact Sum.Lex.inl_le_inr a b
    · rw [← Multiset.coe_eq_coe, Multiset.sort_eq, ← Multiset.coe_add, ← Multiset.map_coe,
        ← Multiset.map_coe, Multiset.sort_eq, Multiset.sort_eq, toMultiset_add,
        toMultiset_map, toMultiset_map]
  rw [pbwMonomial, hsort, List.map_append, List.prod_append, List.map_map, List.map_map]
  rfl

end Lex

section Subalgebras

variable (L₁ L₂ : LieSubalgebra R L)

/-- For Lie subalgebras `L₁`, `L₂` of `L`, the linear map `U(L₁) ⊗[R] U(L₂) → U(L)` given by
`u ⊗ v ↦ u * v`. -/
def mulMap :
    UniversalEnvelopingAlgebra R L₁ ⊗[R] UniversalEnvelopingAlgebra R L₂ →ₗ[R]
      UniversalEnvelopingAlgebra R L :=
  TensorProduct.lift <|
    ((LinearMap.mul R _).compl₂ (map L₂.incl).toLinearMap).comp (map L₁.incl).toLinearMap

@[simp] theorem mulMap_tmul (u : UniversalEnvelopingAlgebra R L₁)
    (v : UniversalEnvelopingAlgebra R L₂) :
    mulMap L₁ L₂ (u ⊗ₜ v) = map L₁.incl u * map L₂.incl v := by
  simp [mulMap]

variable {L₁ L₂} (h : IsCompl L₁.toSubmodule L₂.toSubmodule)
variable {σ₁ σ₂ : Type*} (b₁ : Basis σ₁ R L₁) (b₂ : Basis σ₂ R L₂)

namespace PBW

/-- The basis of `L` indexed by `σ₁ ⊕ₗ σ₂` obtained from bases of complementary Lie
subalgebras. -/
def basisOfIsCompl : Basis (σ₁ ⊕ₗ σ₂) R L :=
  ((b₁.prod b₂).map (Submodule.prodEquivOfIsCompl _ _ h)).reindex toLex

/-- The basis vectors of `basisOfIsCompl` indexed by `σ₁` are those of `b₁`. -/
theorem basisOfIsCompl_inl (i : σ₁) :
    basisOfIsCompl h b₁ b₂ (toLex (Sum.inl i)) = L₁.incl (b₁ i) := by
  simp only [basisOfIsCompl, Basis.reindex_apply, Equiv.symm_apply_apply, Basis.map_apply,
    Basis.prod_apply]
  exact add_zero _

/-- The basis vectors of `basisOfIsCompl` indexed by `σ₂` are those of `b₂`. -/
theorem basisOfIsCompl_inr (i : σ₂) :
    basisOfIsCompl h b₁ b₂ (toLex (Sum.inr i)) = L₂.incl (b₂ i) := by
  simp only [basisOfIsCompl, Basis.reindex_apply, Equiv.symm_apply_apply, Basis.map_apply,
    Basis.prod_apply]
  exact zero_add _

/-- The bijection between pairs of exponents for `σ₁` and `σ₂` and exponents for
`σ₁ ⊕ₗ σ₂`. -/
def lexFinsuppEquiv : (σ₁ →₀ ℕ) × (σ₂ →₀ ℕ) ≃ (σ₁ ⊕ₗ σ₂ →₀ ℕ) :=
  sumFinsuppEquivProdFinsupp.symm.trans (Finsupp.domCongr toLex).toEquiv

/-- `lexFinsuppEquiv (s₁, s₂)` is the sum of the pushforwards of `s₁` and `s₂`. -/
theorem lexFinsuppEquiv_apply (s : (σ₁ →₀ ℕ) × (σ₂ →₀ ℕ)) :
    lexFinsuppEquiv s = s.1.mapDomain (toLex ∘ Sum.inl) + s.2.mapDomain (toLex ∘ Sum.inr) := by
  have h₁ : (toLex ∘ Sum.inl : σ₁ → σ₁ ⊕ₗ σ₂).Injective :=
    toLex.injective.comp Sum.inl_injective
  have h₂ : (toLex ∘ Sum.inr : σ₂ → σ₁ ⊕ₗ σ₂).Injective :=
    toLex.injective.comp Sum.inr_injective
  ext x
  obtain ⟨x | x, rfl⟩ := toLex.surjective x
  · rw [Finsupp.add_apply,
      show toLex (Sum.inl x) = (toLex ∘ Sum.inl : σ₁ → σ₁ ⊕ₗ σ₂) x from rfl,
      mapDomain_apply_of_injective h₁, mapDomain_of_notMem_range _ _ (by simp)]
    simp [lexFinsuppEquiv]
  · rw [Finsupp.add_apply,
      show toLex (Sum.inr x) = (toLex ∘ Sum.inr : σ₂ → σ₁ ⊕ₗ σ₂) x from rfl,
      mapDomain_apply_of_injective h₂, mapDomain_of_notMem_range _ _ (by simp)]
    simp [lexFinsuppEquiv]

end PBW

open PBW

variable [LinearOrder σ₁] [LinearOrder σ₂]

/-- The multiplication map sends the tensor product of two ordered monomials for `b₁` and `b₂`
to the ordered monomial for the combined basis `PBW.basisOfIsCompl h b₁ b₂` of `L`. -/
theorem mulMap_pbwMonomial_tmul (s : (σ₁ →₀ ℕ) × (σ₂ →₀ ℕ)) :
    mulMap L₁ L₂ (pbwMonomial R b₁ s.1 ⊗ₜ pbwMonomial R b₂ s.2) =
      pbwMonomial R (basisOfIsCompl h b₁ b₂) (lexFinsuppEquiv s) := by
  rw [lexFinsuppEquiv_apply, pbwMonomial_mapDomain_add, mulMap_tmul, map_pbwMonomial,
    map_pbwMonomial]
  congr 2 <;> ext i <;> simp [basisOfIsCompl_inl, basisOfIsCompl_inr]

include h b₁ b₂ in
/-- Version of `UniversalEnvelopingAlgebra.mulMap_bijective_of_isCompl` with given linearly
ordered bases of the complementary Lie subalgebras `L₁` and `L₂`. -/
theorem mulMap_bijective_of_basis : Function.Bijective (mulMap L₁ L₂) := by
  let B := (pbwBasis b₁).tensorProduct (pbwBasis b₂)
  have : mulMap L₁ L₂ = (B.equiv (pbwBasis (basisOfIsCompl h b₁ b₂)) lexFinsuppEquiv :
      _ →ₗ[R] _) :=
    B.ext fun s ↦ by
      rw [LinearEquiv.coe_coe, Basis.equiv_apply, pbwBasis_apply, ← mulMap_pbwMonomial_tmul h,
        Basis.tensorProduct_apply', pbwBasis_apply, pbwBasis_apply]
  rw [this]
  exact LinearEquiv.bijective _

include h b₁ b₂ in
/-- Version of `UniversalEnvelopingAlgebra.map_incl_injective_of_isCompl` with given linearly
ordered bases of the complementary Lie subalgebras `L₁` and `L₂`. -/
theorem map_incl_injective_of_basis : Function.Injective (map L₁.incl) := by
  have hli : LinearIndependent R
      (pbwBasis (basisOfIsCompl h b₁ b₂) ∘ fun s ↦ lexFinsuppEquiv (s, (0 : σ₂ →₀ ℕ))) :=
    (pbwBasis _).linearIndependent.comp _
      (lexFinsuppEquiv.injective.comp fun _ _ h ↦ (Prod.mk.inj h).1)
  have : (map L₁.incl).toLinearMap = (pbwBasis b₁).constr R
      (pbwBasis (basisOfIsCompl h b₁ b₂) ∘ fun s ↦ lexFinsuppEquiv (s, 0)) :=
    (pbwBasis b₁).ext fun s ↦ by
      rw [Basis.constr_basis, Function.comp_apply, pbwBasis_apply, pbwBasis_apply,
        ← mulMap_pbwMonomial_tmul h b₁ b₂ (s, 0)]
      simp
  have hinj := (pbwBasis b₁).injective_constr_of_linearIndependent (R₂ := R) hli
  rw [← this] at hinj
  exact hinj

section Free

variable [Module.Free R L₁] [Module.Free R L₂]

include h in
/-- **Corollary of PBW**: if `L₁`, `L₂` are Lie subalgebras of `L` whose underlying submodules
are complementary and free, then multiplication `U(L₁) ⊗[R] U(L₂) → U(L)`, `u ⊗ v ↦ u * v`, is
bijective.

See Bourbaki, *Lie groups and Lie algebras*, Ch. I, §2.7, Corollary 6, and Humphreys, *Introduction
to Lie algebras and representation theory*, §17.3 (Corollary D treats `U(L₁) → U(L)` over a field).
The proof here is reconstructed from the PBW basis. -/
theorem mulMap_bijective_of_isCompl : Function.Bijective (mulMap L₁ L₂) := by
  let : LinearOrder (Free.ChooseBasisIndex R L₁) := IsWellOrder.linearOrder WellOrderingRel
  let : LinearOrder (Free.ChooseBasisIndex R L₂) := IsWellOrder.linearOrder WellOrderingRel
  exact mulMap_bijective_of_basis h (Free.chooseBasis R L₁) (Free.chooseBasis R L₂)

/-- **Corollary of PBW**: the linear isomorphism `U(L₁) ⊗[R] U(L₂) ≃ₗ[R] U(L)`,
`u ⊗ v ↦ u * v`, for Lie subalgebras `L₁`, `L₂` of `L` whose underlying submodules are
complementary and free. See `UniversalEnvelopingAlgebra.mulMap_bijective_of_isCompl`. -/
def tensorEquivOfIsCompl :
    UniversalEnvelopingAlgebra R L₁ ⊗[R] UniversalEnvelopingAlgebra R L₂ ≃ₗ[R]
      UniversalEnvelopingAlgebra R L :=
  LinearEquiv.ofBijective (mulMap L₁ L₂) (mulMap_bijective_of_isCompl h)

theorem tensorEquivOfIsCompl_apply (x : UniversalEnvelopingAlgebra R L₁ ⊗[R]
    UniversalEnvelopingAlgebra R L₂) : tensorEquivOfIsCompl h x = mulMap L₁ L₂ x :=
  rfl

@[simp] theorem tensorEquivOfIsCompl_apply_tmul (u : UniversalEnvelopingAlgebra R L₁)
    (v : UniversalEnvelopingAlgebra R L₂) :
    tensorEquivOfIsCompl h (u ⊗ₜ v) = map L₁.incl u * map L₂.incl v :=
  mulMap_tmul L₁ L₂ u v

include h in
/-- **Corollary of PBW**: if a Lie subalgebra `L₁` of `L` has a complementary Lie subalgebra `L₂`
and both are free as modules, then the induced map `U(L₁) → U(L)` is injective.

See Bourbaki, *Lie groups and Lie algebras*, Ch. I, §2.7, and Humphreys, *Introduction to Lie
algebras and representation theory*, §17.3, Corollary D.
-/
theorem map_incl_injective_of_isCompl : Function.Injective (map L₁.incl) := by
  let : LinearOrder (Free.ChooseBasisIndex R L₁) := IsWellOrder.linearOrder WellOrderingRel
  let : LinearOrder (Free.ChooseBasisIndex R L₂) := IsWellOrder.linearOrder WellOrderingRel
  exact map_incl_injective_of_basis h (Free.chooseBasis R L₁) (Free.chooseBasis R L₂)

end Free

end Subalgebras

end UniversalEnvelopingAlgebra
