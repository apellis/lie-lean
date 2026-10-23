/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.DominantVermaTensor

/-!
# Hom spaces between tensored dominant Verma modules

For `λ` dominant and finite-dimensional `L`, `L'`, the dimension of
`Hom(M(λ) ⊗ L, M(μ) ⊗ L')` is the dimension of the weight space `(L ⊗ L'^*)_{μ - λ}`. With
`μ = λ` this is `dim (L ⊗ L'^*)_0`, the count used in the proof of Humphreys' Theorem 10.7 (b):
natural transformations between the projective functors `− ⊗ L` and `− ⊗ L'` restricted to a
block are compared with their values on the dominant Verma module of the block.

## Main definitions

* `LieModuleEquiv.tensorAssoc`: associativity `(M ⊗ N) ⊗ Q ≅ M ⊗ (N ⊗ Q)` of tensor products
  of Lie modules, with the diagonal actions.

## Main results

* `finrank_hom_tensor_verma_tensor_of_isDominant`:
  `dim Hom(M(λ) ⊗ L, M(μ) ⊗ L') = dim (L ⊗ L'^*)_{μ - λ}` for `λ` dominant.
* `finrank_hom_tensor_verma_tensor_self_of_isDominant`: the case `μ = λ`.

Finite type, finite-dimensional Cartan subalgebra, algebraically closed field of characteristic
zero, as for `finrank_hom_tensor_verma_of_isDominant`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category `𝒪`*,
  GSM 94, §3.9 (Remark), proof of Theorem 10.7.
-/

noncomputable section

open Module LieModule TensorProduct

namespace LieModuleEquiv

variable {R L M N Q : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  [AddCommGroup Q] [Module R Q] [LieRingModule L Q] [LieModule R L Q]

variable (R L M N Q) in
/-- Associativity of tensor products of Lie modules, with the diagonal actions. -/
def tensorAssoc : (M ⊗[R] N) ⊗[R] Q ≃ₗ⁅R,L⁆ M ⊗[R] (N ⊗[R] Q) :=
  { TensorProduct.assoc R M N Q with
    map_lie' := fun {x t} ↦ by
      change TensorProduct.assoc R M N Q ⁅x, t⁆ = ⁅x, TensorProduct.assoc R M N Q t⁆
      induction t with
      | add s t hs ht => rw [lie_add, map_add, hs, ht, map_add, lie_add]
      | tmul s q =>
        induction s with
        | add s s' hs hs' => rw [add_tmul, lie_add, map_add, hs, hs', map_add, lie_add]
        | tmul m n =>
          simp only [LieModule.lie_tmul_right, add_tmul, map_add, TensorProduct.assoc_tmul,
            tmul_add]
          abel }

@[simp] theorem tensorAssoc_tmul (m : M) (n : N) (q : Q) :
    tensorAssoc R L M N Q ((m ⊗ₜ[R] n) ⊗ₜ[R] q) = m ⊗ₜ[R] (n ⊗ₜ[R] q) := rfl

end LieModuleEquiv

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- **Humphreys, proof of Theorem 10.7**: for `λ` dominant and `L`, `L'` finite-dimensional,
`dim Hom(M(λ) ⊗ L, M(μ) ⊗ L') = dim (L ⊗ L'^*)_{μ - λ}`. Moving `L'` to the left by
`Hom(X, Y ⊗ L') ≅ Hom(X ⊗ L'^*, Y)` reduces this to `finrank_hom_tensor_verma_of_isDominant`. -/
theorem finrank_hom_tensor_verma_tensor_of_isDominant {Λ : Dual K H}
    (hΛ : P.IsDominant hA.isGeneralizedCartan Λ) {L L' : Type*} [AddCommGroup L] [Module K L]
    [LieRingModule 𝔤 L] [LieModule K 𝔤 L] [FiniteDimensional K L] [AddCommGroup L']
    [Module K L'] [LieRingModule 𝔤 L'] [LieModule K 𝔤 L'] [FiniteDimensional K L']
    (μ : Dual K H) :
    finrank K (VermaModule P Λ ⊗[K] L →ₗ⁅K,𝔤⁆ VermaModule P μ ⊗[K] L') =
      finrank K (weightSpaceOfMap (L ⊗[K] Module.Dual K L') (h P) (μ - Λ)) := by
  have e₁ := lieModuleHomCongr P (LieModuleEquiv.refl (M := VermaModule P Λ ⊗[K] L))
    (LieModuleEquiv.tensorCongr (LieModuleEquiv.refl (M := VermaModule P μ))
      (evalEquiv (L := 𝔤) (M := L')))
  have e₂ := (tensorHomAdjunction P (M := VermaModule P Λ ⊗[K] L) (N := VermaModule P μ)
    (L := Module.Dual K L')).symm
  have e₃ := lieModuleHomCongr P
    (LieModuleEquiv.tensorAssoc K 𝔤 (VermaModule P Λ) L (Module.Dual K L'))
    (LieModuleEquiv.refl (M := VermaModule P μ))
  rw [(e₁.trans (e₂.trans e₃)).finrank_eq]
  exact finrank_hom_tensor_verma_of_isDominant P hA hΛ μ

include hA in
/-- The case `μ = λ`: `dim Hom(M(λ) ⊗ L, M(λ) ⊗ L') = dim (L ⊗ L'^*)_0` for `λ` dominant. -/
theorem finrank_hom_tensor_verma_tensor_self_of_isDominant {Λ : Dual K H}
    (hΛ : P.IsDominant hA.isGeneralizedCartan Λ) {L L' : Type*} [AddCommGroup L] [Module K L]
    [LieRingModule 𝔤 L] [LieModule K 𝔤 L] [FiniteDimensional K L] [AddCommGroup L']
    [Module K L'] [LieRingModule 𝔤 L'] [LieModule K 𝔤 L'] [FiniteDimensional K L'] :
    finrank K (VermaModule P Λ ⊗[K] L →ₗ⁅K,𝔤⁆ VermaModule P Λ ⊗[K] L') =
      finrank K (weightSpaceOfMap (L ⊗[K] Module.Dual K L') (h P) 0) := by
  rw [finrank_hom_tensor_verma_tensor_of_isDominant P hA hΛ, sub_self]

end Matrix.Realization.KacMoodyAlgebra
