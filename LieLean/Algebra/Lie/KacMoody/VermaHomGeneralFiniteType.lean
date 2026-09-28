/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaUniformity
import LieLean.Algebra.Lie.KacMoody.VermaHomFiniteType
import LieLean.Algebra.Lie.KacMoody.HighestWeightVector

/-!
# Irreducible Verma submodules in finite type

Reconstructed finite-Weyl-orbit descent, followed by the Ore/uniformity argument.
Classical context: Humphreys, Representations of semisimple Lie algebras in the
BGG category O, Theorem 4.2. No printed proof was consulted for this construction.
-/

open Module LieModule
noncomputable section
namespace Matrix.Realization.KacMoodyAlgebra.VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- Every arbitrary-weight finite-type Verma module contains an irreducible Verma
module. The highest weight is chosen maximally in reverse dominance among the
finite set of embedded highest weights; finiteness follows from actual KK linkage.
Reconstructed proof, with no assumption of finite length or socle existence. -/
theorem exists_injective_irreducible_verma [IsAlgClosed K]
    (hA : A.IsFiniteCartan) (S : A.Symmetrization) (Λ : Dual K H) :
    ∃ (μ : Dual K H) (φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ),
      Function.Injective φ ∧ IsIrreducible K P.KacMoodyAlgebra (VermaModule P μ) := by
  classical
  have := P.finite_weylGroup hA
  let T : Set P.WeightOrd := {μ | ∃ φ :
    VermaModule P (WeightOrd.ofWeightOrd P μ) →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ, φ ≠ 0}
  have hTfin : T.Finite := by
    apply (Set.finite_range (fun w : P.weylGroup hA.isGeneralizedCartan ↦
      WeightOrd.toWeightOrd P (P.weylDot hA.isGeneralizedCartan w Λ))).subset
    rintro μ ⟨φ, hφ⟩
    obtain ⟨w, hw⟩ := exists_weylDot_of_hom_ne_zero P hA S hφ
    exact ⟨w, congrArg (WeightOrd.toWeightOrd P) hw.symm⟩
  have hTne : T.Nonempty := by
    refine ⟨WeightOrd.toWeightOrd P Λ, LieModuleHom.id, ?_⟩
    intro hid
    have := congrArg (fun f : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ ↦
      f (hwv P Λ)) hid
    exact hwv_ne_zero P Λ this
  obtain ⟨μ, ⟨φ, hφ⟩, hmax⟩ := hTfin.exists_maximal hTne
  refine ⟨WeightOrd.ofWeightOrd P μ, φ, injective_of_ne_zero P hφ, ?_⟩
  apply IsIrreducible.mk
  intro N hN
  have : Nontrivial N :=
    (LieSubmodule.nontrivial_iff_ne_bot K P.KacMoodyAlgebra _).mpr hN
  obtain ⟨ν, ψ, hψ⟩ := ((isCategoryO P _).lieSubmodule N).exists_lieModuleHom_verma
  let g := N.incl.comp ψ
  have hg : g (hwv P ν) ≠ 0 := fun hz ↦ hψ (Subtype.ext hz)
  have hcomp : φ.comp g ≠ 0 := by
    intro hz
    have he : φ (g (hwv P ν)) = φ 0 := by
      have := congrArg (fun f : VermaModule P ν →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ ↦
        f (hwv P ν)) hz
      simpa using this
    exact hg ((injective_of_ne_zero P hφ) he)
  have hνT : WeightOrd.toWeightOrd P ν ∈ T := ⟨φ.comp g, hcomp⟩
  have hμν : μ ≤ WeightOrd.toWeightOrd P ν := by
    obtain ⟨k, hk, heq⟩ := exists_eq_sub_of_mem_weightSpace P _
      LieModuleHom.id Function.surjective_id
      (map_mem_weightSpaceOfMap P g (hwv_mem_weightSpace P ν)) hg
    refine ⟨k, hk, ?_⟩
    change WeightOrd.ofWeightOrd P μ - ν = P.rootOf k
    rw [heq, sub_sub_cancel]
  have hνμ : ν = WeightOrd.ofWeightOrd P μ :=
    congrArg (WeightOrd.ofWeightOrd P) (le_antisymm (hmax hνT hμν) hμν)
  have hw : g (hwv P ν) ∈ weightSpace P (WeightOrd.ofWeightOrd P μ)
      (WeightOrd.ofWeightOrd P μ) := by
    simpa only [hνμ] using map_mem_weightSpaceOfMap P g (hwv_mem_weightSpace P ν)
  rw [weightSpace_self] at hw
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  have hc0 : c ≠ 0 := by
    intro hz
    exact hg (by rw [← hc, hz, zero_smul])
  apply eq_top_of_hwv_mem P _
  have hm : g (hwv P ν) ∈ N := (ψ (hwv P ν)).property
  have := N.smul_mem c⁻¹ hm
  rwa [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

/-- In a finite-type target, two maps from an irreducible Verma module are scalar
multiples. Uniformity forces their images to meet, and irreducibility forces inclusion;
the one-dimensional highest weight space supplies the scalar, without a Schur assumption. -/
theorem exists_smul_eq_of_irreducible (hA : A.IsFiniteCartan) {Λ ν : Dual K H}
    [IsIrreducible K P.KacMoodyAlgebra (VermaModule P ν)]
    (φ ψ : VermaModule P ν →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) (hψ : ψ ≠ 0) :
    ∃ c : K, c • ψ = φ := by
  by_cases hφ : φ = 0
  · exact ⟨0, by simp [hφ]⟩
  have hrφ : φ.range ≠ ⊥ := by
    intro hz
    apply hφ
    apply (eq_zero_iff P φ).mpr
    exact (LieSubmodule.mem_bot _).mp (hz ▸ (show φ (hwv P ν) ∈ φ.range from ⟨_, rfl⟩))
  have hrψ : ψ.range ≠ ⊥ := by
    intro hz
    apply hψ
    apply (eq_zero_iff P ψ).mpr
    exact (LieSubmodule.mem_bot _).mp (hz ▸ (show ψ (hwv P ν) ∈ ψ.range from ⟨_, rfl⟩))
  have hinter := inf_ne_bot_of_finite_type P hA Λ φ.range ψ.range hrφ hrψ
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ φ.range ⊓ ψ.range, x ≠ 0 := by
    simpa only [ne_eq, LieSubmodule.eq_bot_iff, not_forall, exists_prop] using hinter
  obtain ⟨y, hy⟩ := hx.1
  have hpre : ψ.range.comap φ ≠ ⊥ := by
    intro hz
    have hy0 : y = 0 := (LieSubmodule.mem_bot _).mp
      (hz ▸ (show y ∈ ψ.range.comap φ from
        (show φ y ∈ ψ.range from hy.symm ▸ hx.2)))
    exact hx0 (by rw [← hy, hy0, map_zero])
  have htop : ψ.range.comap φ = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left hpre
  have hmem : φ (hwv P ν) ∈ ψ.range :=
    show hwv P ν ∈ ψ.range.comap φ from htop ▸ LieSubmodule.mem_top _
  obtain ⟨z, hz⟩ := hmem
  have hzw : z ∈ weightSpace P ν ν := by
    intro a
    apply injective_of_ne_zero P hψ
    rw [LieModuleHom.map_lie, map_smul, hz]
    exact map_mem_weightSpaceOfMap P φ (hwv_mem_weightSpace P ν) a
  rw [weightSpace_self] at hzw
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzw
  refine ⟨c, hom_ext P ν ?_⟩
  change c • ψ (hwv P ν) = φ (hwv P ν)
  rw [← map_smul, hc, hz]

omit [FiniteDimensional K H] in
/-- Restricting a Verma homomorphism to any nonzero Verma embedding is injective.
This uses the domain theorem for *all* nonzero Verma homomorphisms, not essentiality
of the embedded submodule. -/
theorem precomp_injective {Λ μ ν : Dual K H}
    (j : VermaModule P ν →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P μ) (hj : j ≠ 0) :
    Function.Injective (fun φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ ↦
      φ.comp j) := by
  intro φ ψ heq
  by_contra hne
  have hd : φ - ψ ≠ 0 := sub_ne_zero.mpr hne
  have hzero : (φ - ψ) (j (hwv P ν)) = 0 := by
    change φ (j (hwv P ν)) - ψ (j (hwv P ν)) = 0
    exact sub_eq_zero.mpr (LieModuleHom.congr_fun heq (hwv P ν))
  have hjzero : j (hwv P ν) = 0 :=
    injective_of_ne_zero P hd (hzero.trans (map_zero (φ - ψ)).symm)
  exact hj ((eq_zero_iff P j).mpr hjzero)

/-- **Classical finite-type Verma Hom uniqueness for arbitrary highest weights**.
No integrality, regularity, socle, embedding uniqueness, or Hom-bound hypothesis is
assumed. Reconstructed proof of the finite-type result in Humphreys, category O,
Theorem 4.2(b), using proved KK linkage, finite Weyl descent, and actual Ore uniformity. -/
theorem finrank_hom_le_one_of_finite_type [IsAlgClosed K]
    (hA : A.IsFiniteCartan) (S : A.Symmetrization) (Λ μ : Dual K H) :
    finrank K (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) ≤ 1 := by
  classical
  by_cases hall : ∀ φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ, φ = 0
  · apply finrank_le_one_iff.mpr
    exact ⟨0, fun φ ↦ ⟨0, by rw [hall φ, zero_smul]⟩⟩
  push Not at hall
  obtain ⟨ψ, hψ⟩ := hall
  obtain ⟨ν, j, hj, hirr⟩ := exists_injective_irreducible_verma P hA S μ
  have := hirr
  have hj0 : j ≠ 0 := by
    intro hz
    exact hwv_ne_zero P ν (hj (by rw [hz]; rfl))
  have hψj : ψ.comp j ≠ 0 := by
    intro hz
    have hh : ψ.comp j = (0 :
        VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ).comp j := by
      exact hz.trans (LieModuleHom.ext fun _ ↦ rfl)
    exact hψ (precomp_injective P j hj0 hh)
  apply finrank_le_one_iff.mpr
  refine ⟨ψ, fun φ ↦ ?_⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_of_irreducible P hA (φ.comp j) (ψ.comp j) hψj
  refine ⟨c, precomp_injective P j hj0 ?_⟩
  exact hc

end Matrix.Realization.KacMoodyAlgebra.VermaModule
