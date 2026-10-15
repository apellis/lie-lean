/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.HighestWeightSimilarity
import LieLean.Algebra.QuantumGroup.CrystalBasis.DirectSum
import LieLean.Algebra.QuantumGroup.CrystalBasis.Equiv

/-!
# Crystal bases of direct sums of the modules `L_q(λ)`

Hong–Kang, GSM 42, Theorem 5.1.2: a module `M` isomorphic to a direct sum `⊕ⱼ L_q(λⱼ)` of
irreducible highest weight modules with dominant highest weights has a crystal base, namely the
image of `(⊕ⱼ L(λⱼ), ⊔ⱼ B(λⱼ))` under the isomorphism. Hong–Kang write the direct sum as
`⊕_λ V(λ)^{⊕ν(λ)}`; here it is indexed by an arbitrary type `J` with a family `λ : J → P⁺`, and
multiplicities are repetitions in the family.

## Main results

* `IsCrystalBase.exists_of_dfinsupp_equiv`: if `M ≅ ⊕ⱼ Mⱼ` and every `Mⱼ` has a crystal base
  `(Lⱼ, Bⱼ)`, then `M` has a crystal base whose lattice is the image of `⊕ⱼ Lⱼ`.
* `GrandLoop.exists_isCrystalBase_of_equiv`: **Theorem 5.1.2**.

## Proof

As in Hong–Kang: the crystal bases `(L(λ), B(λ))` of Theorem 5.1.1 (`GrandLoop.isCrystalBase`),
direct sums of crystal bases (`IsCrystalBase.dfinsupp`, [HK] Thm. 4.2.10) and transport along
isomorphisms (`IsCrystalBase.of_equiv`, [HK] Prop. 4.2.8).

## References

* J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, AMS 2002,
  Theorem 5.1.2.
-/

noncomputable section

namespace LieLean.QuantumGroup

namespace IrreducibleModule

/-! ### Instances on `L_q(λ)` stated directly

Instance search does not find the quotient instances of `L_q(λ)` for a family `j ↦ L_q(λⱼ)`
(it cannot unify `L_q(λⱼ)` with a quotient `?M j ⧸ ?N j`), so they are restated for
`IrreducibleModule`, which is enough for `Π₀ j, L_q(λⱼ)`. -/

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} (Λ : Y →+ ℤ)

instance instAddCommGroup : AddCommGroup (IrreducibleModule R v Λ) := inferInstance

instance instModule : Module (QuantumGroup R v) (IrreducibleModule R v Λ) := inferInstance

instance instModuleField : Module k (IrreducibleModule R v Λ) := inferInstance

instance instIsScalarTower : IsScalarTower k (QuantumGroup R v) (IrreducibleModule R v Λ) :=
  inferInstance

instance instModuleOfAlgebra {A : Type*} [CommRing A] [Algebra A k] :
    Module A (IrreducibleModule R v Λ) := inferInstance

instance instIsScalarTowerOfAlgebra {A : Type*} [CommRing A] [Algebra A k] :
    IsScalarTower A k (IrreducibleModule R v Λ) := inferInstance

end IrreducibleModule

/-! ### Transport of direct sums of crystal bases -/

section Transport

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] {hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1}
  {J : Type*} {N : J → Type*} [∀ j, AddCommGroup (N j)] [∀ j, Module k (N j)]
  [∀ j, Module (QuantumGroup R v) (N j)] [hNk : ∀ j, IsScalarTower k (QuantumGroup R v) (N j)]
  {hN : ∀ j, IsIntegrable R v (N j)}
  {A : Type*} [CommRing A] [Algebra A k] [∀ j, Module A (N j)]
  [hNA : ∀ j, IsScalarTower A k (N j)]
  {L : ∀ j, Submodule A (N j)}
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] [Module A M] [IsScalarTower A k M]

/-- If `ψ : ⊕ⱼ Mⱼ ≃ M` and every `Mⱼ` has a crystal base `(Lⱼ, Bⱼ)`, then `M` has a crystal base
`(L, B)` with `L = ψ(⊕ⱼ Lⱼ)` ([HK] Thm. 4.2.10 and Prop. 4.2.8). -/
theorem IsCrystalBase.exists_of_dfinsupp_equiv (hM : IsIntegrable R v M)
    (ψ : (Π₀ j, N j) ≃ₗ[QuantumGroup R v] M) {hL : ∀ j, IsCrystalLattice hv (hN j) (L j)}
    {c : A} (hc : ¬IsUnit c) {B : ∀ j, Set (L j ⧸ (Ideal.span {c} • ⊤ : Submodule A (L j)))}
    (hB : ∀ j, IsCrystalBase (hL j) c (B j)) :
    ∃ (L' : Submodule A M) (hL' : IsCrystalLattice hv hM L')
      (B' : Set (L' ⧸ (Ideal.span {c} • ⊤ : Submodule A L'))),
      IsCrystalBase hL' c B' ∧
        ∀ m, m ∈ L' ↔ ψ.symm m ∈ (dfinsuppLattice L : Submodule A (Π₀ j, N j)) := by
  classical
  let L' : Submodule A M :=
    (dfinsuppLattice L).comap ((ψ.symm.restrictScalars k).toLinearMap.restrictScalars A)
  have hLL' : ∀ x, x ∈ (dfinsuppLattice L : Submodule A (Π₀ j, N j)) ↔ ψ x ∈ L' := fun x ↦ by
    change _ ↔ ψ.symm (ψ x) ∈ (dfinsuppLattice L : Submodule A (Π₀ j, N j))
    rw [ψ.symm_apply_apply]
  exact ⟨L', _, _, (IsCrystalBase.dfinsupp hc hB).of_equiv hM ψ hLL' fun _ ↦
    ((IntegrableSl2.quotEquiv (ψ.restrictScalars k) hLL' c).injective.mem_set_image).symm,
    fun _ ↦ Iff.rfl⟩

end Transport

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}
  {J : Type*} (Λ : J → Dom R)

variable (hvt hR A) in
/-- The direct sum `⊕ⱼ L(λⱼ)` of the lattices `L(λⱼ)`, a lattice of `⊕ⱼ L_q(λⱼ)`. -/
abbrev dsSum : Submodule A (Π₀ j, IrreducibleModule R v (Λ j).1) :=
  dfinsuppLattice (M := fun j ↦ IrreducibleModule R v (Λ j).1) fun j ↦ lat hvt hR A (Λ j)

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] [Module A M] [IsScalarTower A k M]
  (hM : IsIntegrable R v M)

include hinj hϖ hϖv hk hfund

/-- **Hong–Kang, Theorem 5.1.2.** If `ψ : ⊕ⱼ L_q(λⱼ) ≃ M` with every `λⱼ` dominant, then `M` has a
crystal base `(L, B)` with `L = ψ(⊕ⱼ L(λⱼ))`; it is the image of `(⊕ⱼ L(λⱼ), ⊔ⱼ B(λⱼ))` under
`ψ` (`IsCrystalBase.exists_of_dfinsupp_equiv`). -/
theorem exists_isCrystalBase_of_equiv
    (ψ : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v] M) :
    ∃ (L : Submodule A M) (hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) hM L)
      (B : Set (L ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L))),
      IsCrystalBase hL ϖ B ∧ ∀ m, m ∈ L ↔ ψ.symm m ∈ dsSum hvt hR A Λ :=
  IsCrystalBase.exists_of_dfinsupp_equiv (N := fun j ↦ IrreducibleModule R v (Λ j).1)
    (hNk := fun j ↦ IrreducibleModule.instIsScalarTower (Λ j).1)
    (hNA := fun j ↦ IrreducibleModule.instIsScalarTowerOfAlgebra (Λ j).1) hM ψ (not_isUnit_ϖ hϖ)
    fun j ↦ isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund (Λ j)

end GrandLoop

end LieLean.QuantumGroup

