/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.HarishChandraIsomorphism
import Mathlib.GroupTheory.CosetCover

/-!
# Central characters separate dot orbits

## Main definitions

* `SymmetricAlgebra.dualTranspose`: the transpose on `H` of a linear map of `Dual K H`, for
  finite-dimensional `H`.
* `SymmetricAlgebra.pullbackDual`: the induced algebra map of `Sym(H)` (polynomial functions on
  `Dual K H`), with `(pullbackDual w p)(λ) = p(w λ)`.

## Main results

* `SymmetricAlgebra.exists_invariant_separating`: invariant polynomials of a finite group of
  linear automorphisms of `Dual K H` separate its orbits, over an infinite field.
* `Matrix.Realization.KacMoodyAlgebra.mem_coreflectionInvariants_iff`: invariance under the
  simple coreflections is invariance under the whole Weyl group.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.centralCharacter_eq_iff`: in finite type,
  `χ_Λ = χ_Λ'` iff `Λ' + ρ ∈ W (Λ + ρ)`, i.e. `Λ'` is in the dot orbit of `Λ`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_weyl_of_hom_ne_zero`: a nonzero
  morphism `M(μ) → M(Λ)` forces `μ` into the dot orbit of `Λ`.

## References

* Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  Theorem 1.10(b).
* Humphreys, *Introduction to Lie algebras and representation theory*, GTM 9, §23.3.
The orbit separation uses the product over the group of a linear polynomial vanishing at one
point and nowhere on the other orbit; the generic linear form exists because a vector space over
an infinite field is not a finite union of proper subspaces. Reconstructed, not transcribed.
-/

noncomputable section

open Module

namespace SymmetricAlgebra

variable {K : Type} {H : Type*} [Field K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]

/-- The transpose on `H` of a linear endomorphism of `Dual K H`, via `H ≃ Dual (Dual H)`. -/
def dualTranspose (w : Dual K H →ₗ[K] Dual K H) : H →ₗ[K] H :=
  (evalEquiv K H).symm.toLinearMap ∘ₗ w.dualMap ∘ₗ (evalEquiv K H).toLinearMap

@[simp] theorem apply_dualTranspose (w : Dual K H →ₗ[K] Dual K H) (φ : Dual K H) (h : H) :
    φ (dualTranspose w h) = w φ h := by
  have key : ∀ x : H, evalEquiv K H x φ = φ x := fun x => rfl
  rw [← key]
  change evalEquiv K H ((evalEquiv K H).symm (w.dualMap (evalEquiv K H h))) φ = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

omit [FiniteDimensional K H] in
theorem eq_of_forall_dual_apply_eq {x y : H} (h : ∀ φ : Dual K H, φ x = φ y) : x = y := by
  rw [← sub_eq_zero]
  refine (forall_dual_apply_eq_zero_iff K (x - y)).mp fun φ => ?_
  rw [map_sub, h, sub_self]

@[simp] theorem dualTranspose_id : dualTranspose (K := K) (H := H) LinearMap.id = LinearMap.id :=
  LinearMap.ext fun h => eq_of_forall_dual_apply_eq (K := K) fun φ => by simp

theorem dualTranspose_comp (v w : Dual K H →ₗ[K] Dual K H) :
    dualTranspose (w ∘ₗ v) = dualTranspose v ∘ₗ dualTranspose w := by
  ext h
  apply eq_of_forall_dual_apply_eq (K := K)
  intro φ
  simp

/-- Pullback of polynomial functions on `Dual K H` along a linear endomorphism `w`. -/
def pullbackDual (w : Dual K H →ₗ[K] Dual K H) : SymmetricAlgebra K H →ₐ[K] SymmetricAlgebra K H :=
  lift ((ι K H).comp (dualTranspose w))

/-- `pullbackDual w p` evaluates at `λ` to `p` at `w λ`. -/
theorem lift_pullbackDual (w : Dual K H →ₗ[K] Dual K H) (a : Dual K H)
    (p : SymmetricAlgebra K H) : lift a (pullbackDual w p) = lift (w a) p := by
  have he : (lift a).comp (pullbackDual w) = lift (w a) := by
    apply algHom_ext
    ext h
    simp [pullbackDual]
  exact DFunLike.congr_fun he p

theorem pullbackDual_pullbackDual (v w : Dual K H →ₗ[K] Dual K H) (p : SymmetricAlgebra K H) :
    pullbackDual v (pullbackDual w p) = pullbackDual (w ∘ₗ v) p := by
  have he : (pullbackDual v).comp (pullbackDual w) = pullbackDual (w ∘ₗ v) := by
    apply algHom_ext
    ext h
    simp [pullbackDual, dualTranspose_comp]
  exact DFunLike.congr_fun he p

@[simp] theorem pullbackDual_id (p : SymmetricAlgebra K H) :
    pullbackDual LinearMap.id p = p := by
  have he : pullbackDual (K := K) (H := H) LinearMap.id = AlgHom.id K _ := by
    apply algHom_ext
    ext h
    simp [pullbackDual]
  exact DFunLike.congr_fun he p

/-- **Invariants separate orbits.** For a finite group `G` of linear automorphisms of
`Dual K H` over an infinite field, if `b` is not in the orbit of `a`, some `G`-invariant
polynomial function vanishes at `b` but not at `a`. -/
theorem exists_invariant_separating [Infinite K] (G : Subgroup (Dual K H ≃ₗ[K] Dual K H))
    [Finite G] {a b : Dual K H} (hab : ∀ w ∈ G, w a ≠ b) :
    ∃ f : SymmetricAlgebra K H, (∀ w ∈ G, pullbackDual (w : Dual K H ≃ₗ[K] Dual K H).toLinearMap
      f = f) ∧ lift b f = 0 ∧ lift a f ≠ 0 := by
  classical
  have := Fintype.ofFinite G
  -- A point of `H` on which no `w a - b` vanishes.
  obtain ⟨h, hh⟩ : ∃ h : H, ∀ w : G, (w.val a - b) h ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hcov : ⋃ w : G, ((LinearMap.ker (w.val a - b) : Subspace K H) : Set H) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, SetLike.mem_coe, LinearMap.mem_ker, Set.mem_univ, iff_true]
      exact hcon x
    obtain ⟨w, hw⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
    apply hab w.val w.property
    rw [← sub_eq_zero]
    exact LinearMap.ker_eq_top.mp hw
  let g : SymmetricAlgebra K H := ι K H h - algebraMap K _ (b h)
  have hg : ∀ c : Dual K H, lift c g = c h - b h := fun c => by simp [g]
  refine ⟨∏ w : G, pullbackDual w.val.toLinearMap g, ?_, ?_, ?_⟩
  · intro v hv
    rw [map_prod]
    simp only [pullbackDual_pullbackDual]
    refine Fintype.prod_equiv (Equiv.mulRight ⟨v, hv⟩) _ _ fun w => ?_
    rfl
  · rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ 1)
    rw [lift_pullbackDual, hg]
    simp
  · rw [map_prod, Finset.prod_ne_zero_iff]
    intro w _
    rw [lift_pullbackDual, hg, ← LinearMap.sub_apply]
    exact hh w

end SymmetricAlgebra

namespace Matrix.Realization.KacMoodyAlgebra

open SymmetricAlgebra

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

omit [DecidableEq ι] [CharZero K] in
theorem dualTranspose_reflection (hA : A.IsGeneralizedCartan) (i : ι) :
    dualTranspose (P.reflection hA i).toLinearMap = (P.coreflection hA i).toLinearMap :=
  LinearMap.ext fun h => eq_of_forall_dual_apply_eq (K := K) fun φ => by
    rw [apply_dualTranspose]
    exact P.reflection_apply_apply hA i φ h

omit [DecidableEq ι] [CharZero K] in
/-- The Weyl-group pullback of a simple reflection is the coreflection pullback. -/
theorem pullbackDual_reflection (hA : A.IsGeneralizedCartan) (i : ι) :
    pullbackDual (P.reflection hA i).toLinearMap =
      affinePullback (P.coreflection hA i).toLinearMap 0 := by
  rw [pullbackDual, dualTranspose_reflection, affinePullback, LinearMap.comp_zero, add_zero]

omit [DecidableEq ι] [CharZero K] in
/-- Coreflection invariance is invariance under the whole Weyl group, acting on polynomial
functions on `Dual K H` by `(w · p)(λ) = p(w λ)`. -/
theorem mem_coreflectionInvariants_iff (hA : A.IsGeneralizedCartan) (f : SymmetricAlgebra K H) :
    f ∈ coreflectionInvariants P hA ↔
      ∀ w ∈ P.weylGroup hA, pullbackDual (w : Dual K H ≃ₗ[K] Dual K H).toLinearMap f = f := by
  rw [mem_coreflectionInvariants]
  constructor
  · intro hf w hw
    refine P.weylGroup_induction hA (p := fun w =>
      pullbackDual (w : Dual K H ≃ₗ[K] Dual K H).toLinearMap f = f) (by simp) (fun i w ih => ?_) hw
    have he : ((P.reflection hA i * w : Dual K H ≃ₗ[K] Dual K H)).toLinearMap =
        (P.reflection hA i).toLinearMap ∘ₗ w.toLinearMap := rfl
    rw [he, ← pullbackDual_pullbackDual, pullbackDual_reflection, hf i, ih]
  · intro hf i
    rw [← pullbackDual_reflection]
    exact hf _ (P.reflection_mem_weylGroup hA i)

variable (hA : A.IsFiniteCartan)

include hA in
/-- **Central characters separate dot orbits** (Humphreys, GSM 94, Theorem 1.10(b)).
In finite type over a characteristic-zero field, the full-centre characters of the Verma
modules `M(Λ)` and `M(Λ')` agree iff `Λ' + ρ = w (Λ + ρ)` for some Weyl group element `w`. -/
theorem VermaModule.centralCharacter_eq_iff (Λ Λ' : Dual K H) :
    VermaModule.centralCharacter P Λ = VermaModule.centralCharacter P Λ' ↔
      ∃ w ∈ P.weylGroup hA.isGeneralizedCartan, w (Λ + P.rho) = Λ' + P.rho := by
  constructor
  · intro hχ
    by_contra hne
    push Not at hne
    have := P.finite_weylGroup hA
    obtain ⟨f, hfinv, hb, ha⟩ := exists_invariant_separating
      (P.weylGroup hA.isGeneralizedCartan) hne
    obtain ⟨z, rfl⟩ := exists_shiftedHarishChandra_eq P hA f
      ((mem_coreflectionInvariants P hA.isGeneralizedCartan).mp
        ((mem_coreflectionInvariants_iff P hA.isGeneralizedCartan f).mpr hfinv))
    rw [eval_shiftedHarishChandra, add_sub_cancel_right] at ha hb
    exact ha (by rw [hχ]; exact hb)
  · rintro ⟨w, hw, he⟩
    have h := VermaModule.centralCharacter_weyl P hA.isGeneralizedCartan hw Λ
    rw [he, add_sub_cancel_right] at h
    exact h.symm

include hA in
/-- **Linkage for Verma morphisms**: in finite type, a nonzero morphism `M(μ) → M(Λ)` forces
`μ + ρ ∈ W (Λ + ρ)`. -/
theorem VermaModule.exists_weyl_of_hom_ne_zero {Λ μ : Dual K H}
    (φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) (hφ : φ ≠ 0) :
    ∃ w ∈ P.weylGroup hA.isGeneralizedCartan, w (Λ + P.rho) = μ + P.rho :=
  (VermaModule.centralCharacter_eq_iff P hA Λ μ).mp
    (VermaModule.centralCharacter_eq_of_hom_ne_zero P φ hφ).symm

end Matrix.Realization.KacMoodyAlgebra
