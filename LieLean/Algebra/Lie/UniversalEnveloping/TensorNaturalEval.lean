/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.UniversalEnveloping.TensorNatural
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Evaluating natural transformations at a faithful module

Let `I` be a two-sided ideal of `U = U(L)`, `A = U / I`, and `M` a module killed by `I`. A
morphism `g : V → A^{ad} ⊗ W` gives `φ_M = tensorNatMap g : M ⊗ V → M ⊗ W`. The map
`g ↦ φ_M` is linear (`tensorNatLinear`); it is injective when `I` is the annihilator of `M`
over a field (`tensorNatLinear_injective`), and hence bijective when the two Hom spaces have
the same finite dimension (`tensorNatLinear_bijective`).

In Humphreys' proof of Theorem 10.7 (Bernstein–Gelfand), `M = M(λ)` with `λ` dominant and
`I = Ann M(λ)`: Duflo's theorem identifies `I`, Kostant's theorem computes the dimension of
`Hom_𝔤(V, A^{ad} ⊗ W)`, and `finrank_hom_tensor_verma_tensor_of_isDominant` computes the
dimension of `Hom_𝔤(M(λ) ⊗ V, M(λ) ⊗ W)`.

## Main results

* `UniversalEnvelopingAlgebra.eq_zero_of_forall_rTensor_flip_eq_zero`: for an injective
  `φ : A → End(M)` over a field, `t ∈ A ⊗ W` with `(a ↦ φ(a) m) ⊗ 1 (t) = 0` for all `m` is `0`.
* `UniversalEnvelopingAlgebra.tensorNatLinear_injective`,
  `UniversalEnvelopingAlgebra.tensorNatLinear_bijective`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8, proof of Thm. 10.7.
-/

noncomputable section

open TensorProduct LieModule

namespace UniversalEnvelopingAlgebra

section Faithful

variable {K A M W : Type*} [Field K] [AddCommGroup A] [Module K A] [AddCommGroup M] [Module K M]
  [AddCommGroup W] [Module K W]

/-- For an injective `φ : A → End(M)` over a field, an element `t ∈ A ⊗ W` that is killed by
`(a ↦ φ(a) m) ⊗ 1` for every `m ∈ M` is zero. -/
theorem eq_zero_of_forall_rTensor_flip_eq_zero (φ : A →ₗ[K] Module.End K M)
    (hφ : Function.Injective φ) (t : A ⊗[K] W) (ht : ∀ m, (φ.flip m).rTensor W t = 0) :
    t = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace K W
  let e := TensorProduct.equivFinsuppOfBasisRight (M := A) b
  -- the `i`-th coordinate of `t`
  let c : _ → A ⊗[K] W →ₗ[K] A := fun i ↦
    (TensorProduct.rid K A).toLinearMap ∘ₗ (b.coord i).lTensor A
  have hc : ∀ i (s : A ⊗[K] W), e s i = c i s := fun i s ↦ by
    induction s with
    | add s s' hs hs' => rw [map_add, map_add, Finsupp.add_apply, hs, hs']
    | tmul a w =>
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
      simp [c]
  have hcm : ∀ i (m : M) (s : A ⊗[K] W), φ (c i s) m =
      ((TensorProduct.rid K M).toLinearMap ∘ₗ (b.coord i).lTensor M)
        ((φ.flip m).rTensor W s) := fun i m s ↦ by
    induction s with
    | add s s' hs hs' => simp only [map_add, LinearMap.add_apply, hs, hs']
    | tmul a w => simp [c]
  apply e.injective
  ext i
  rw [hc, map_zero, Finsupp.zero_apply]
  apply hφ
  ext m
  rw [hcm, ht, map_zero, map_zero, LinearMap.zero_apply]

end Faithful

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {I : TwoSidedIdeal (UniversalEnvelopingAlgebra R L)}
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  {V W : Type*} [AddCommGroup V] [Module R V] [LieRingModule L V] [LieModule R L V]
  [AddCommGroup W] [Module R W] [LieRingModule L W] [LieModule R L W]

/-- `g ↦ tensorNatMap g`, as a linear map
`Hom_L(V, A^{ad} ⊗ W) → Hom_L(M ⊗ V, M ⊗ W)`. -/
def tensorNatLinear (hM : IsKilledBy I M) :
    (V →ₗ⁅R,L⁆ AdQuotient R L I ⊗[R] W) →ₗ[R] (M ⊗[R] V →ₗ⁅R,L⁆ M ⊗[R] W) where
  toFun g := tensorNatMap g hM
  map_add' g g' := by
    ext t
    induction t with
    | add s t hs ht => simp only [map_add, hs, ht]
    | tmul m v => simp [map_add]
  map_smul' c g := by
    ext t
    induction t with
    | add s t hs ht => simp only [map_add, hs, ht]
    | tmul m v => simp [map_smul]

@[simp] theorem tensorNatLinear_apply (hM : IsKilledBy I M)
    (g : V →ₗ⁅R,L⁆ AdQuotient R L I ⊗[R] W) : tensorNatLinear hM g = tensorNatMap g hM := rfl

/-- `quotientAction` is injective when `I` is the annihilator of `M`. -/
theorem quotientAction_injective (hM : IsKilledBy I M)
    (hI : ∀ a, actionHom (R := R) (L := L) M a = 0 → a ∈ I) :
    Function.Injective (quotientAction hM) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H u =>
    rw [LinearMap.mem_ker, quotientAction_mk] at hq
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hI _ hq)

variable {K : Type*} [Field K] [LieAlgebra K L]
  {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K L)}
  {M V W : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]

/-- **Evaluation at a faithful module is injective**: if `I` is the annihilator of `M`, a
morphism `g : V → (U/I)^{ad} ⊗ W` is determined by `φ_M = tensorNatMap g`. -/
theorem tensorNatLinear_injective (hM : IsKilledBy I M)
    (hI : ∀ a, actionHom (R := K) (L := L) M a = 0 → a ∈ I) :
    Function.Injective (tensorNatLinear (V := V) (W := W) hM) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro g hg
  rw [LinearMap.mem_ker, tensorNatLinear_apply] at hg
  ext v
  refine eq_zero_of_forall_rTensor_flip_eq_zero _ (quotientAction_injective hM hI) _ fun m ↦ ?_
  rw [← tensorNatMap_tmul, hg]
  rfl

/-- **Evaluation at a faithful module is bijective** when the two Hom spaces have the same
finite dimension. -/
theorem tensorNatLinear_bijective (hM : IsKilledBy I M)
    (hI : ∀ a, actionHom (R := K) (L := L) M a = 0 → a ∈ I)
    [FiniteDimensional K (V →ₗ⁅K,L⁆ AdQuotient K L I ⊗[K] W)]
    [FiniteDimensional K (M ⊗[K] V →ₗ⁅K,L⁆ M ⊗[K] W)]
    (hdim : Module.finrank K (V →ₗ⁅K,L⁆ AdQuotient K L I ⊗[K] W) =
      Module.finrank K (M ⊗[K] V →ₗ⁅K,L⁆ M ⊗[K] W)) :
    Function.Bijective (tensorNatLinear (V := V) (W := W) hM) := by
  have hinj := tensorNatLinear_injective (V := V) (W := W) hM hI
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

end UniversalEnvelopingAlgebra
