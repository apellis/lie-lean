/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.UniversalEnveloping.TensorNatural
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Changing the ideal, and natural endomorphisms vanishing on `U / I`-modules

For two-sided ideals `I ≤ J` of `U = U(L)`, the quotient map `U / I → U / J` is a morphism of
adjoint modules (`adQuotientMap`), and for a module killed by `J` the natural transformation
attached to `g : V → (U / I)^{ad} ⊗ W` only depends on the image of `g` in `(U / J)^{ad} ⊗ W`
(`tensorNatMap_adQuotientMap`). Taking `I = ⊥`, morphisms `V → U^{ad} ⊗ W` give natural
transformations `M ⊗ V → M ⊗ W` on all modules.

A natural endomorphism `θ` of `M ↦ M ⊗ V` which vanishes on every module killed by `I` is
nilpotent on every module with a filtration of length `n` whose subquotients are killed by `I`:
`θ_M ^ n = 0` (`pow_eq_zero_of_hasKilledFiltration`). This is the step of Humphreys' proof of
Theorem 10.7 (b) that passes from `U / U ker χ`-modules to the whole block of `χ`.

## Main definitions

* `UniversalEnvelopingAlgebra.adQuotientMap`: `(U / I)^{ad} → (U / J)^{ad}` for `I ≤ J`.
* `UniversalEnvelopingAlgebra.HasKilledFiltration I M n`: `M` has a chain of Lie submodules of
  length `n` with subquotients killed by `I`.

## Main results

* `UniversalEnvelopingAlgebra.tensorNatMap_adQuotientMap`.
* `UniversalEnvelopingAlgebra.pow_eq_zero_of_hasKilledFiltration`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8, proof of Thm. 10.7.
-/

noncomputable section

open TensorProduct

namespace UniversalEnvelopingAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {I J : TwoSidedIdeal (UniversalEnvelopingAlgebra R L)}
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  {V W : Type*} [AddCommGroup V] [Module R V] [LieRingModule L V] [LieModule R L V]
  [AddCommGroup W] [Module R W] [LieRingModule L W] [LieModule R L W]

theorem IsKilledBy.mono (hIJ : I ≤ J) (hM : IsKilledBy J M) : IsKilledBy I M :=
  fun a ha ↦ hM a (hIJ ha)

/-- Every module is killed by the zero ideal. -/
theorem isKilledBy_bot : IsKilledBy (⊥ : TwoSidedIdeal (UniversalEnvelopingAlgebra R L)) M :=
  fun a ha ↦ by
    rw [TwoSidedIdeal.mem_bot] at ha
    rw [ha, map_zero]

variable (R L) in
/-- The quotient map `(U / I)^{ad} → (U / J)^{ad}` for `I ≤ J`. -/
def adQuotientMap (hIJ : I ≤ J) : AdQuotient R L I →ₗ⁅R,L⁆ AdQuotient R L J :=
  LieSubmodule.Quotient.lift _ (LieSubmodule.Quotient.mk' (adIdeal R L J))
    fun _ hu ↦ LieModuleHom.mem_ker.mpr ((LieSubmodule.Quotient.mk_eq_zero _).mpr (hIJ hu))

@[simp] theorem adQuotientMap_mk (hIJ : I ≤ J) (u : AdRegular R L) :
    adQuotientMap R L hIJ (LieSubmodule.Quotient.mk u) = LieSubmodule.Quotient.mk u := rfl

theorem adQuotientMap_surjective (hIJ : I ≤ J) : Function.Surjective (adQuotientMap R L hIJ) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H u => exact ⟨LieSubmodule.Quotient.mk u, rfl⟩

theorem quotientAction_adQuotientMap (hIJ : I ≤ J) (hM : IsKilledBy J M) (q : AdQuotient R L I) :
    quotientAction hM (adQuotientMap R L hIJ q) = quotientAction (hM.mono hIJ) q := by
  induction q using Submodule.Quotient.induction_on with
  | H u => rfl

/-- On a module killed by `J ≥ I`, the natural transformation attached to
`g : V → (U / I)^{ad} ⊗ W` is the one attached to its image in `(U / J)^{ad} ⊗ W`. -/
theorem tensorNatMap_adQuotientMap (hIJ : I ≤ J) (g : V →ₗ⁅R,L⁆ AdQuotient R L I ⊗[R] W)
    (hM : IsKilledBy J M) :
    tensorNatMap ((TensorProduct.LieModule.map (adQuotientMap R L hIJ) LieModuleHom.id).comp g) hM =
      tensorNatMap g (hM.mono hIJ) := by
  ext t
  induction t with
  | add s t hs ht => rw [map_add, map_add, hs, ht]
  | tmul m v =>
    rw [tensorNatMap_tmul, tensorNatMap_tmul, LieModuleHom.comp_apply]
    change ((quotientAction hM).flip m).rTensor W
      (((adQuotientMap R L hIJ : AdQuotient R L I →ₗ[R] AdQuotient R L J)).rTensor W (g v)) = _
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    congr 2
    ext q
    exact congrArg (fun f : Module.End R M ↦ f m) (quotientAction_adQuotientMap hIJ hM q)

/-! ### Nilpotence -/

universe u

variable (I) in
/-- `M` has a chain `0 = M₀ ≤ M₁ ≤ ⋯ ≤ Mₙ = M` of Lie submodules whose subquotients are killed
by `I`. -/
inductive HasKilledFiltration : ∀ (M : Type u) [AddCommGroup M] [Module R M] [LieRingModule L M]
    [LieModule R L M], ℕ → Prop
  | zero (M : Type u) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
      [Subsingleton M] : HasKilledFiltration M 0
  | succ (M : Type u) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
      (N : LieSubmodule R L M) (n : ℕ) (hN : HasKilledFiltration N n)
      (hMN : IsKilledBy I (M ⧸ N)) : HasKilledFiltration M (n + 1)

/-- **Nilpotence of natural endomorphisms**: let `θ` be a natural endomorphism of the functor
`M ↦ M ⊗ V` which vanishes on modules killed by `I`. Then `θ_M ^ n = 0` on every module `M` with
a filtration of length `n` whose subquotients are killed by `I`. -/
theorem pow_eq_zero_of_hasKilledFiltration
    (θ : ∀ (M : Type u) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M],
      M ⊗[R] V →ₗ⁅R,L⁆ M ⊗[R] V)
    (hθ : ∀ (M N : Type u) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
      [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N] (f : M →ₗ⁅R,L⁆ N)
      (t : M ⊗[R] V), (f : M →ₗ[R] N).rTensor V (θ M t) = θ N ((f : M →ₗ[R] N).rTensor V t))
    (h0 : ∀ (M : Type u) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M],
      IsKilledBy I M → θ M = 0)
    {M : Type u} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M] {n : ℕ}
    (hM : HasKilledFiltration I M n) : (θ M : M ⊗[R] V →ₗ[R] M ⊗[R] V) ^ n = 0 := by
  induction hM with
  | zero M =>
    refine LinearMap.ext fun t ↦ ?_
    have : Subsingleton (M ⊗[R] V) := inferInstance
    exact Subsingleton.elim _ _
  | succ M N n _ hMN ih =>
    refine LinearMap.ext fun t ↦ ?_
    rw [pow_succ, Module.End.mul_apply, LinearMap.zero_apply]
    -- `θ_M t` lies in the image of `N ⊗ V`
    have hex : Function.Exact ((N.incl : N →ₗ[R] M).rTensor V)
        (((LieSubmodule.Quotient.mk' N : M →ₗ⁅R,L⁆ M ⧸ N) : M →ₗ[R] M ⧸ N).rTensor V) :=
      _root_.rTensor_exact V (fun m ↦ by
          constructor
          · intro hm
            exact ⟨⟨m, (LieSubmodule.Quotient.mk_eq_zero N).mp hm⟩, rfl⟩
          · rintro ⟨n, rfl⟩
            exact (LieSubmodule.Quotient.mk_eq_zero N).mpr n.2)
        (LieSubmodule.Quotient.surjective_mk' N)
    obtain ⟨s, hs⟩ := (hex (θ M t)).mp (by
      rw [hθ M (M ⧸ N) (LieSubmodule.Quotient.mk' N) t, h0 _ hMN, zero_apply])
    have hs' : (θ M : M ⊗[R] V →ₗ[R] M ⊗[R] V) t = (N.incl : N →ₗ[R] M).rTensor V s := hs.symm
    rw [hs']
    have hpow : ∀ k : ℕ, ((θ M : M ⊗[R] V →ₗ[R] M ⊗[R] V) ^ k) ((N.incl : N →ₗ[R] M).rTensor V s) =
        (N.incl : N →ₗ[R] M).rTensor V (((θ N : N ⊗[R] V →ₗ[R] N ⊗[R] V) ^ k) s) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ihk =>
        rw [pow_succ', Module.End.mul_apply, ihk, pow_succ', Module.End.mul_apply]
        exact (hθ N M N.incl _).symm
    rw [hpow, ih, LinearMap.zero_apply, map_zero]

end UniversalEnvelopingAlgebra
