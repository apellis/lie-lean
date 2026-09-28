/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.Uniqueness
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Multiplicity
import LieLean.Algebra.Lie.KacMoody.FiniteType
import LieLean.Algebra.Lie.KacMoody.Kostant.Weights

/-!
# Finite-type reductions for Verma homomorphisms

## Main results

* `Matrix.Realization.exists_dominantIntegral_weylGroup`: integral weights over a
  characteristic-zero field have dominant integral translates under a finite Weyl group.
* `Matrix.Realization.exists_dominantIntegral_weylDot_of_regular`: dot-regular integral
  weights lie in dot orbits of dominant integral weights; the field need not be ordered.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_weylDot_of_hom_ne_zero`:
  for finite type, a nonzero Verma hom forces the highest weights into the same dot orbit.
* `VermaModule.finrank_hom_le_one_of_finite_type_regular_integral`:
  over an algebraically closed characteristic-zero field with finite-dimensional Cartan,
  a symmetrizable finite-type matrix and a dot-regular integral target suffice for
  `dim Hom(M(μ), M(Λ)) ≤ 1`, with arbitrary source highest weight `μ`.

## Scope and references

The arguments below are reconstructed from the existing formalized Weyl-group,
Kac–Kazhdan, and BGG uniqueness theorems, not transcribed from a consulted textbook.
In particular, neither a dominant representative nor a shared dot orbit is assumed.
The imported `finiteDimensional_hom` instance ensures that the finrank statement is
an actual dimension bound, not an infinite-dimensional finrank convention.
Singular integral and nonintegral targets remain outside this Hom-bound theorem.
No assertion is made for general noncritical Kac–Moody weights.
-/

open Module
noncomputable section
namespace Matrix.Realization
variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

omit [DecidableEq ι] [FiniteDimensional K H] in
/-- An integral weight has a dominant Weyl translate when the Weyl group is finite.
This is a reconstructed maximal-root-height argument and does not order the field. -/
theorem exists_dominantIntegral_weylGroup
    (hA : A.IsGeneralizedCartan) [Finite (P.weylGroup hA)]
    {ν : Dual K H} (hν : ∀ i, ∃ z : ℤ, ν (P.coroot i) = z) :
    ∃ w : P.weylGroup hA, P.IsDominantIntegral (w.val ν) := by
  classical
  choose k hk using fun w : P.weylGroup hA ↦ P.exists_apply_eq_add_rootOf hA w.property hν
  obtain ⟨w, hw⟩ := Finite.exists_max (fun w ↦ ∑ i, k w i)
  refine ⟨w, fun i ↦ ?_⟩
  obtain ⟨z₀, hz₀⟩ := hν i
  let z : ℤ := z₀ + (A *ᵥ k w) i
  have hz : w.val ν (P.coroot i) = (z : K) := by
    rw [hk w, LinearMap.add_apply, hz₀, P.rootOf_apply_coroot]
    exact (Int.cast_add _ _).symm
  let r : P.weylGroup hA := ⟨P.reflection hA i, P.reflection_mem_weylGroup hA i⟩
  have hk' : k (r * w) = k w - z • Pi.single i 1 := by
    apply P.rootOf_injective
    have heq : (r * w).val ν = ν + P.rootOf (k w - z • Pi.single i 1) := by
      change P.reflection hA i (w.val ν) = _
      rw [P.reflection_apply, hz, hk w, map_sub, map_zsmul, P.rootOf_single,
        ← Int.cast_smul_eq_zsmul K]
      abel
    exact add_left_cancel ((hk (r * w)).symm.trans heq)
  have hznonneg : 0 ≤ z := by
    have hh := hw (r * w)
    rw [hk'] at hh
    simp [Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply] at hh
    omega
  refine ⟨z.toNat, hz.trans ?_⟩
  exact_mod_cast (Int.toNat_of_nonneg hznonneg).symm

omit [DecidableEq ι] [FiniteDimensional K H] in
/-- A dot-regular integral weight lies in the dot orbit of a dominant integral weight
when the Weyl group is finite. Regularity is explicit on every real coroot.
Reconstructed proof: maximize root-lattice height, then subtract rho. -/
theorem exists_dominantIntegral_weylDot_of_regular
    (hA : A.IsGeneralizedCartan) [Finite (P.weylGroup hA)]
    {Λ₀ : Dual K H} (hΛ : ∀ i, ∃ z : ℤ, (Λ₀ + P.rho) (P.coroot i) = z)
    (hreg : ∀ (w : P.weylGroup hA) i, w.val (Λ₀ + P.rho) (P.coroot i) ≠ 0) :
    ∃ Λ, P.IsDominantIntegral Λ ∧ ∃ w : P.weylGroup hA, Λ₀ = P.weylDot hA w Λ := by
  obtain ⟨w, hw⟩ := P.exists_dominantIntegral_weylGroup hA hΛ
  refine ⟨w.val (Λ₀ + P.rho) - P.rho, fun i ↦ ?_, w⁻¹, ?_⟩
  · obtain ⟨n, hn⟩ := hw i
    have hn0 : n ≠ 0 := by
      intro hn0
      exact hreg w i (by rw [hn, hn0, Nat.cast_zero])
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨m, ?_⟩
    rw [LinearMap.sub_apply, hn, rho_coroot, Nat.cast_succ]
    ring
  · simp [weylDot]

namespace KacMoodyAlgebra

/-- In finite type, a Kac–Kazhdan step is a dot reflection in a real root.
Reconstructed from root reality and Weyl invariance of the invariant form. -/
theorem KacKazhdanStep.exists_weylDot
    (hA : A.IsFiniteCartan) (S : A.Symmetrization) {Λ μ : Dual K H}
    (hstep : KacKazhdanStep P S Λ μ) :
    ∃ w : P.weylGroup hA.isGeneralizedCartan, μ = P.weylDot hA.isGeneralizedCartan w Λ := by
  obtain ⟨α, hα, hroot, n, -, rfl, hKK⟩ := hstep
  have hα0 : α ≠ 0 := fun h0 ↦ P.zero_notMem_posWeights (h0 ▸ hα)
  have hreal : α ∈ P.realRoots hA.isGeneralizedCartan := by
    rw [← roots_eq_realRoots P hA]
    exact ⟨hα0, hroot⟩
  obtain ⟨u, hu, i, rfl⟩ := hreal
  let w : P.weylGroup hA.isGeneralizedCartan := ⟨u, hu⟩
  let r : P.weylGroup hA.isGeneralizedCartan :=
    ⟨P.reflection hA.isGeneralizedCartan i,
      P.reflection_mem_weylGroup hA.isGeneralizedCartan i⟩
  have hpair : u.symm (Λ + P.rho) (P.coroot i) = (n : K) := by
    apply (VermaModule.two_mul_dualBilinForm_root_eq_iff P hA.isGeneralizedCartan S _ i n).mp
    have h₁ := P.dualBilinForm_weylGroup hA.isGeneralizedCartan S hu
      (u.symm (Λ + P.rho)) (P.root i)
    have h₂ := P.dualBilinForm_weylGroup hA.isGeneralizedCartan S hu (P.root i) (P.root i)
    simp only [LinearEquiv.apply_symm_apply] at h₁
    simpa only [h₁, h₂] using hKK
  refine ⟨w * r * w⁻¹, ?_⟩
  change Λ - n • u (P.root i) = u (P.reflection hA.isGeneralizedCartan i
    (u.symm (Λ + P.rho))) - P.rho
  rw [reflection_apply, hpair, map_sub, map_smul, LinearEquiv.apply_symm_apply]
  simp only [Nat.cast_smul_eq_nsmul]
  abel

/-- A finite-type Kac–Kazhdan chain stays in one dot orbit, for arbitrary weights.
Reconstructed by composing the real-root dot reflections of its steps. -/
theorem exists_weylDot_of_kacKazhdanChain
    (hA : A.IsFiniteCartan) (S : A.Symmetrization) {Λ μ : Dual K H}
    (hchain : Relation.ReflTransGen (KacKazhdanStep P S) Λ μ) :
    ∃ w : P.weylGroup hA.isGeneralizedCartan, μ = P.weylDot hA.isGeneralizedCartan w Λ := by
  induction hchain with
  | refl => exact ⟨1, (P.weylDot_one hA.isGeneralizedCartan _).symm⟩
  | @tail μ ν _ hstep ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨v, hv⟩ := hstep.exists_weylDot P hA S
    exact ⟨v * w, by rw [weylDot_mul, ← hw, ← hv]⟩

namespace VermaModule

/-- In finite type, every highest weight of a Verma composition factor belongs to the
same dot orbit. This uses the formal Kac–Kazhdan theorem, not a linkage hypothesis. -/
theorem exists_weylDot_of_multiplicity_ne_zero [IsAlgClosed K]
    (hA : A.IsFiniteCartan) (S : A.Symmetrization) {Λ μ : Dual K H}
    (hμ : (isCategoryO P Λ).multiplicity μ ≠ 0) :
    ∃ w : P.weylGroup hA.isGeneralizedCartan, μ = P.weylDot hA.isGeneralizedCartan w Λ :=
  exists_weylDot_of_kacKazhdanChain P hA S
    ((multiplicity_ne_zero_iff_reflTransGen P S hA.isGeneralizedCartan Λ μ).mp hμ)

omit [FiniteDimensional K H] in
/-- A nonzero Verma homomorphism forces its source highest weight to occur as a
composition factor of the target. Reconstructed using the image submodule and additivity. -/
theorem multiplicity_ne_zero_of_hom_ne_zero {Λ μ : Dual K H}
    {φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ} (hφ : φ ≠ 0) :
    (isCategoryO P Λ).multiplicity μ ≠ 0 := by
  let f : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ φ.range :=
    φ.codRestrict φ.range fun m ↦ ⟨m, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact injective_of_ne_zero P hφ (congrArg Subtype.val h)
    · rintro ⟨m, x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  let e := LieModuleEquiv.ofBijective f hf
  have hc := (isCategoryO P μ).character_congr
    ((isCategoryO P Λ).lieSubmodule φ.range) e
  have hm := ((isCategoryO P μ).character_eq_iff
    ((isCategoryO P Λ).lieSubmodule φ.range)).mp hc μ
  rw [multiplicity_self] at hm
  have hadd := (isCategoryO P Λ).multiplicity_eq_add φ.range μ
  omega

/-- In finite type, a nonzero Verma homomorphism forces source and target to lie in
one dot orbit, without any regularity or integrality assumption on either weight. -/
theorem exists_weylDot_of_hom_ne_zero [IsAlgClosed K]
    (hA : A.IsFiniteCartan) (S : A.Symmetrization) {Λ μ : Dual K H}
    {φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ} (hφ : φ ≠ 0) :
    ∃ w : P.weylGroup hA.isGeneralizedCartan, μ = P.weylDot hA.isGeneralizedCartan w Λ :=
  exists_weylDot_of_multiplicity_ne_zero P hA S (multiplicity_ne_zero_of_hom_ne_zero P hφ)

/-- Finite-type uniqueness for a dot-regular integral target and an arbitrary source.
The dot-orbit and dominant representative are proved, not assumed. This reconstructed
argument combines finite Weyl-group maximization, Kac–Kazhdan linkage, and BGG uniqueness.
Singular integral and nonintegral target weights are outside the conclusion. -/
theorem finrank_hom_le_one_of_finite_type_regular_integral [IsAlgClosed K]
    (hA : A.IsFiniteCartan) (S : A.Symmetrization) (Λ μ : Dual K H)
    (hΛ : ∀ i, ∃ z : ℤ, (Λ + P.rho) (P.coroot i) = z)
    (hreg : ∀ (w : P.weylGroup hA.isGeneralizedCartan) i,
      w.val (Λ + P.rho) (P.coroot i) ≠ 0) :
    finrank K (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) ≤ 1 := by
  classical
  by_cases hzero : ∀ φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ, φ = 0
  · have : Subsingleton (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) :=
      ⟨fun φ ψ ↦ (hzero φ).trans (hzero ψ).symm⟩
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  push Not at hzero
  obtain ⟨φ, hφ⟩ := hzero
  obtain ⟨v, hv⟩ := exists_weylDot_of_hom_ne_zero P hA S hφ
  have := P.finite_weylGroup hA
  obtain ⟨Λ', hΛ', w, hw⟩ :=
    P.exists_dominantIntegral_weylDot_of_regular hA.isGeneralizedCartan hΛ hreg
  have hμ : μ = P.weylDot hA.isGeneralizedCartan (v * w) Λ' := by
    rw [weylDot_mul, ← hw, ← hv]
  rw [hw, hμ]
  exact finrank_hom_weylDot_le_one hA.isGeneralizedCartan hΛ' w (v * w)

end VermaModule
end KacMoodyAlgebra
end Matrix.Realization
