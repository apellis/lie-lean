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

## Main definitions

* `GrandLoop.dsLattice`: the image `ψ(⊕ⱼ L(λⱼ))` of the direct sum of the lattices `L(λⱼ)`
  under an isomorphism `ψ : ⊕ⱼ L_q(λⱼ) ≃ M`.
* `GrandLoop.dsBase`: the image `ψ̄(⊔ⱼ B(λⱼ))`.

## Main results

* `GrandLoop.isCrystalBase_dsBase`: `(ψ(⊕ⱼ L(λⱼ)), ψ̄(⊔ⱼ B(λⱼ)))` is a crystal base of `M`.
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

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}
  {J : Type*} (Λ : J → Dom R)
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] [Module A M] [IsScalarTower A k M]
  (ψ : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v] M)

variable (hvt hR A) in
/-- The direct sum `⊕ⱼ L(λⱼ)` of the lattices `L(λⱼ)`, a lattice of `⊕ⱼ L_q(λⱼ)`. -/
abbrev dsSum : Submodule A (Π₀ j, IrreducibleModule R v (Λ j).1) :=
  dfinsuppLattice (M := fun j ↦ IrreducibleModule R v (Λ j).1) fun j ↦ lat hvt hR A (Λ j)

variable (hvt hR A) in
/-- The lattice `ψ(⊕ⱼ L(λⱼ))` of `M`, for an isomorphism `ψ : ⊕ⱼ L_q(λⱼ) ≃ M`. -/
def dsLattice : Submodule A M :=
  (dsSum hvt hR A Λ).comap ((ψ.symm.restrictScalars k).toLinearMap.restrictScalars A)

lemma mem_dsLattice_iff (m : M) :
    m ∈ dsLattice hvt hR A Λ ψ ↔ ψ.symm m ∈ dsSum hvt hR A Λ :=
  Iff.rfl

lemma mem_dsLattice_iff' (x : Π₀ j, IrreducibleModule R v (Λ j).1) :
    x ∈ dsSum hvt hR A Λ ↔ (ψ.restrictScalars k) x ∈ dsLattice hvt hR A Λ ψ := by
  rw [mem_dsLattice_iff]
  exact iff_of_eq (congrArg (· ∈ dsSum hvt hR A Λ) (ψ.symm_apply_apply x).symm)

variable [DecidableEq J]

variable (hvt hR A ϖ) in
/-- The subset `ψ̄(⊔ⱼ B(λⱼ))` of `ψ(⊕ⱼ L(λⱼ)) / ϖ ψ(⊕ⱼ L(λⱼ))`. -/
def dsBase : Set (dsLattice hvt hR A Λ ψ ⧸
    (Ideal.span {ϖ} • ⊤ : Submodule A (dsLattice hvt hR A Λ ψ))) :=
  IntegrableSl2.quotEquiv (ψ.restrictScalars k) (mem_dsLattice_iff' Λ ψ) ϖ ''
    dfinsuppBase (M := fun j ↦ IrreducibleModule R v (Λ j).1) (fun j ↦ lat hvt hR A (Λ j)) ϖ
      fun j ↦ IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) (Λ j).2 A ϖ

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
  (hM : IsIntegrable R v M)

include hinj hϖ hϖv hk hfund

omit [DecidableEq J] in
/-- `ψ(⊕ⱼ L(λⱼ))` is a crystal lattice of `M`. -/
theorem isCrystalLattice_dsLattice :
    IsCrystalLattice (pow_ne_one_of_transcendental' hvt) hM (dsLattice hvt hR A Λ ψ) :=
  (IsCrystalLattice.dfinsupp (M := fun j ↦ IrreducibleModule R v (Λ j).1) fun j ↦
    isCrystalLattice_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund (Λ j)).of_equiv hM ψ
    (mem_dsLattice_iff' Λ ψ)

/-- `(ψ(⊕ⱼ L(λⱼ)), ψ̄(⊔ⱼ B(λⱼ)))` is a crystal base of `M`. -/
theorem isCrystalBase_dsBase :
    IsCrystalBase (isCrystalLattice_dsLattice Λ ψ hinj hϖ hϖv hk hfund hM) ϖ
      (dsBase hvt hR A ϖ Λ ψ) :=
  (IsCrystalBase.dfinsupp (M := fun j ↦ IrreducibleModule R v (Λ j).1) (not_isUnit_ϖ hϖ)
    fun j ↦ isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund (Λ j)).of_equiv hM ψ
    (mem_dsLattice_iff' Λ ψ) fun _ ↦
      ((IntegrableSl2.quotEquiv (ψ.restrictScalars k) (mem_dsLattice_iff' Λ ψ)
        ϖ).injective.mem_set_image).symm

/-- **Hong–Kang, Theorem 5.1.2.** If `M ≅ ⊕ⱼ L_q(λⱼ)` with every `λⱼ` dominant, then `M` has a
crystal base `(L, B)` with `L = ψ(⊕ⱼ L(λⱼ))`; by `isCrystalBase_dsBase` one can take
`B = ψ̄(⊔ⱼ B(λⱼ))`, so that `ψ` identifies `(L, B)` with `(⊕ⱼ L(λⱼ), ⊔ⱼ B(λⱼ))`. -/
theorem exists_isCrystalBase_of_equiv :
    ∃ (L : Submodule A M) (hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) hM L)
      (B : Set (L ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L))),
      IsCrystalBase hL ϖ B ∧ ∀ m, m ∈ L ↔ ψ.symm m ∈ dsSum hvt hR A Λ :=
  ⟨_, _, _, isCrystalBase_dsBase Λ ψ hinj hϖ hϖv hk hfund hM, mem_dsLattice_iff Λ ψ⟩

end GrandLoop

end LieLean.QuantumGroup
