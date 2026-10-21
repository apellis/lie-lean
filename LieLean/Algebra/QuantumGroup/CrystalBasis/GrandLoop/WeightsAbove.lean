/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.CrystalDecomposition
import LieLean.Algebra.QuantumGroup.WeightsAbove

/-!
# Crystal bases of modules with finitely many weights above each weight

The uniqueness of crystal bases ([HK] Thm. 5.2.1) and its consequences for the crystal ([Kas] §4.5,
(4.6)) hold beyond `𝒪_int`: for integrable modules `M` with finite-dimensional weight spaces and
finitely many weights above each weight (`QuantumGroup.HasFiniteWeightsAbove`). Such an `M` is
`⊕ⱼ L_q(λⱼ)` (`QuantumGroup.exists_linearEquiv_dfinsupp_of_hasFiniteWeightsAbove`), and every
summand lies below only finitely many summands, which is what the proof of uniqueness uses. The
main example is the restriction of a module in `𝒪_int` to a Levi subalgebra.

## Main results

* `GrandLoop.finite_summandsAbove_of_hasFiniteWeightsAbove`: every summand of `M ≃ ⊕ⱼ L_q(λⱼ)`
  lies below only finitely many summands.
* `GrandLoop.exists_equiv_of_hasFiniteWeightsAbove`: uniqueness of crystal bases of `M`.
* `GrandLoop.exists_crystalEquiv_sigma_of_hasFiniteWeightsAbove`: the crystal of a crystal base of
  `M` is `⊔ⱼ B(λⱼ)`, with highest weight elements the `u_{λⱼ}`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.2.
* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §4.5.
-/

open Pointwise

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

include hvt hR in
/-- If `M ≃ ⊕ⱼ V(λⱼ)` has finite-dimensional weight spaces and finitely many weights above each
weight, every summand lies below only finitely many summands. -/
lemma finite_summandsAbove_of_hasFiniteWeightsAbove {J : Type*} {Λ : J → Dom R}
    (hfd : ∀ Λ, FiniteDimensional k (weightSpace R v M Λ)) (hab : HasFiniteWeightsAbove R v M)
    (ψ : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v] M) (j : J) :
    (summandsAbove Λ j).Finite := by
  classical
  have hv' := pow_ne_one_of_transcendental' hvt
  -- the image of the highest weight vector of each summand
  have hmem : ∀ j', ψ (DFinsupp.single j' (IrreducibleModule.hwv R v (Λ j').1)) ∈
      weightSpace R v M (Λ j').1 := fun j' ↦
    map_mem_weightSpace (ψ : (Π₀ j, IrreducibleModule R v (Λ j).1) →ₗ[QuantumGroup R v] M)
      (map_mem_weightSpace (DFinsupp.lsingle (R := QuantumGroup R v)
        (M := fun j ↦ IrreducibleModule R v (Λ j).1) j') IrreducibleModule.hwv_mem_weightSpace)
  have hne : ∀ j', ψ (DFinsupp.single j' (IrreducibleModule.hwv R v (Λ j').1)) ≠ 0 := fun j' h ↦ by
    rw [map_eq_zero_iff _ ψ.injective, DFinsupp.single_eq_zero] at h
    exact hwv_ne_zero hR hv' _ h
  -- each weight has finitely many summands
  have hfib : ∀ μ, {j' | (Λ j').1 = μ}.Finite := fun μ ↦ by
    have := hfd μ
    let f : {j' | (Λ j').1 = μ} → weightSpace R v M μ := fun j' ↦
      ⟨ψ (DFinsupp.single j'.1 (IrreducibleModule.hwv R v (Λ j'.1).1)), by
        convert hmem j'.1
        exact (show (Λ j'.1).1 = μ from j'.2).symm⟩
    have hli : LinearIndependent k fun j' : {j' | (Λ j').1 = μ} ↦
        ψ (DFinsupp.single j'.1 (IrreducibleModule.hwv R v (Λ j'.1).1)) :=
      (linearIndependent_dfinsuppSingle (fun j ↦ IrreducibleModule.hwv R v (Λ j).1)
        (fun j ↦ hwv_ne_zero hR hv' _) _).map'
        ((ψ : (Π₀ j, IrreducibleModule R v (Λ j).1) →ₗ[QuantumGroup R v] M).restrictScalars k)
        (LinearMap.ker_eq_bot.2 ψ.injective)
    have hf : LinearIndependent k f := LinearIndependent.of_comp (weightSpace R v M μ).subtype hli
    exact Set.finite_coe_iff.1 hf.finite
  refine ((hab (Λ j).1).biUnion fun ν _ ↦ hfib ((Λ j).1 + R.rootSum ν)).subset
    fun j' ⟨ν, hν⟩ ↦ Set.mem_biUnion (x := ν) ?_ hν
  rw [Set.mem_ofPred_eq, ← hν]
  exact (Submodule.ne_bot_iff _).2 ⟨_, hmem j', hne j'⟩

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
  [Module A M] [IsScalarTower A k M]
  {hM : IsIntegrable R v M} {L : Submodule A M}
  {hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) hM L}
  {B : Set (L ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L))}
  (hfd : ∀ Λ, FiniteDimensional k (weightSpace R v M Λ)) (hab : HasFiniteWeightsAbove R v M)

open scoped Classical in
include hinj hϖ hϖv hk hfund hfd hab in
/-- **Uniqueness of crystal bases** ([HK] Thm. 5.2.1) for an integrable module `M` with
finite-dimensional weight spaces and finitely many weights above each weight, with a crystal base
`(L, B)`: there is an isomorphism `Φ : ⊕ⱼ V(λⱼ) ≃ M` of `U`-modules, for dominant weights `λⱼ`,
mapping `⊕ⱼ L(λⱼ)` onto `L` such that the induced isomorphism `(⊕ⱼ L(λⱼ)) / ϖ ≃ L / ϖL` maps
`⊔ⱼ B(λⱼ)` onto `B`. The summands are indexed by a set of submodules of `M`. -/
theorem exists_equiv_of_hasFiniteWeightsAbove (hB : IsCrystalBase hL ϖ B) :
    ∃ (s : Set (Submodule (QuantumGroup R v) M)) (Λ : s → Dom R)
      (Φ : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v] M)
      (hΦ : ∀ x, x ∈ dsSum hvt hR A Λ ↔ Φ x ∈ L),
      ∀ b, b ∈ dsBase hvt hR A ϖ Λ ↔ IntegrableSl2.quotEquiv (Φ.restrictScalars k) hΦ ϖ b ∈ B := by
  obtain ⟨s, Λ₀, hdom, ⟨ψ⟩⟩ := exists_linearEquiv_dfinsupp_of_hasFiniteWeightsAbove
    (pow_ne_one_of_transcendental' hvt) hM hfd hab hvt hR
  let Λ : s → Dom R := fun j ↦ ⟨Λ₀ j, hdom j⟩
  let ψ' : (Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v] M := ψ
  exact ⟨s, Λ, exists_equiv_of_isCrystalBase hinj hϖ hϖv hk hfund
    (finite_summandsAbove_of_hasFiniteWeightsAbove (hvt := hvt) (hR := hR) hfd hab ψ') ψ' hB⟩

include hinj hϖ hϖv hk hfund hfd hab in
/-- **The crystal of a crystal base** ([Kas] §4.5, (4.6)) of an integrable module `M` with
finite-dimensional weight spaces and finitely many weights above each weight: for a crystal base
`(L, B)` of `M`, the crystal of `B` is isomorphic to the disjoint union `⊔ⱼ B(λⱼ)` of the crystals
of the crystal bases `(L(λⱼ), B(λⱼ))` of the `L_q(λⱼ)`, for dominant weights `λⱼ` (indexed by a set
of submodules of `M`); the highest weight elements of `B` are exactly the images of the `u_{λⱼ}`, of
weight `λⱼ`; and `M ≅ ⊕ⱼ L_q(λⱼ)`. -/
theorem exists_crystalEquiv_sigma_of_hasFiniteWeightsAbove (hB : IsCrystalBase hL ϖ B) :
    ∃ (s : Set (Submodule (QuantumGroup R v) M)) (Λ : s → Dom R)
      (Φ : Crystal.Equiv (Crystal.sigma fun j ↦ crystalHW hvt hR hinj hϖ hϖv hk hfund (Λ j))
        (hB.crystal (not_isUnit_ϖ hϖ))),
      (∀ b, (hB.crystal (not_isUnit_ϖ hϖ)).IsHighestWeight b ↔
        ∃ j, b = Φ ⟨j, topHW hvt hR hinj hϖ (Λ j)⟩) ∧
      (∀ j, (hB.crystal (not_isUnit_ϖ hϖ)).wt (Φ ⟨j, topHW hvt hR hinj hϖ (Λ j)⟩) = (Λ j).1) ∧
      Nonempty ((Π₀ j, IrreducibleModule R v (Λ j).1) ≃ₗ[QuantumGroup R v] M) := by
  classical
  obtain ⟨s, Λ, Ψ, hΨ, hBB⟩ := exists_equiv_of_hasFiniteWeightsAbove hinj hϖ hϖv hk hfund hfd hab hB
  have hc := not_isUnit_ϖ hϖ
  have hB₀ := fun j ↦ isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund (Λ j)
  let Φ := (IsCrystalBase.sigmaCrystalEquiv hc hB₀).trans
    ((IsCrystalBase.dfinsupp hc hB₀).crystalEquivOfEquiv hB hc Ψ hΨ hBB)
  refine ⟨s, Λ, Φ, fun b ↦ ?_, fun j ↦ ?_, ⟨Ψ⟩⟩
  · obtain ⟨⟨j, b₀⟩, rfl⟩ := Φ.toEquiv.surjective b
    rw [Crystal.Equiv.coe_toEquiv, ← Crystal.Equiv.coe_toStrictHom,
      Crystal.StrictHom.isHighestWeight_apply_iff, Crystal.isHighestWeight_sigma_iff]
    change (crystalHW hvt hR hinj hϖ hϖv hk hfund (Λ j)).IsHighestWeight b₀ ↔ _
    rw [isHighestWeight_crystalHW_iff hinj hϖ hϖv hk hfund]
    refine ⟨fun h ↦ ⟨j, by rw [h]; rfl⟩, fun ⟨j', h⟩ ↦ ?_⟩
    obtain ⟨rfl, h'⟩ := Sigma.mk.inj_iff.mp (Φ.toEquiv.injective h)
    exact eq_of_heq h'
  · exact (Φ.toStrictHom.wt_apply _).trans (wt_topHW hinj hϖ hϖv hk hfund (Λ j))

end GrandLoop

end LieLean.QuantumGroup
