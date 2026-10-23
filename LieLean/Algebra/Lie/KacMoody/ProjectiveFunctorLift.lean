/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.UniversalEnveloping.TensorNaturalLift
import LieLean.Algebra.Lie.KacMoody.FiniteDimensional

/-!
# Extending natural transformations from `U / I`-modules to all modules

For `A` of finite type, every morphism `V → (U / I)^{ad} ⊗ W` with `V`, `W` finite-dimensional
lifts along `(U / ⊥)^{ad} ⊗ W → (U / I)^{ad} ⊗ W` (`exists_lift_adQuotient`): the adjoint
module `U(𝔤)^{ad}` is a union of finite-dimensional submodules, which are semisimple by Weyl's
theorem. Consequently a natural transformation `M ⊗ V → M ⊗ W` defined on modules killed by `I`
is the restriction of one defined on all modules (`exists_tensorNatMap_eq`). In Humphreys'
proof of Theorem 10.7 (a) this extends a morphism of projective functors on a block, given by
its value at the dominant Verma module, to the whole category.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.exists_lift_adQuotient`.
* `Matrix.Realization.KacMoodyAlgebra.exists_tensorNatMap_eq`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8, proof of Thm. 10.7.
-/

noncomputable section

open TensorProduct UniversalEnvelopingAlgebra

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- For `A` of finite type, every morphism `V → (U / I)^{ad} ⊗ W` with `V`, `W` finite-dimensional
lifts to a morphism `V → (U / ⊥)^{ad} ⊗ W`. -/
theorem exists_lift_adQuotient (I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤))
    {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule 𝔤 V] [LieModule K 𝔤 V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [LieRingModule 𝔤 W]
    [LieModule K 𝔤 W] [FiniteDimensional K W] (g : V →ₗ⁅K,𝔤⁆ AdQuotient K 𝔤 I ⊗[K] W) :
    ∃ g' : V →ₗ⁅K,𝔤⁆ AdQuotient K 𝔤 ⊥ ⊗[K] W,
      (TensorProduct.LieModule.map (adQuotientMap K 𝔤 bot_le) LieModuleHom.id).comp g' = g := by
  have := finiteDimensional P hA
  let π := TensorProduct.LieModule.map (LieSubmodule.Quotient.mk' (adIdeal K 𝔤 I))
    (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W)
  have hπ : Function.Surjective π :=
    TensorProduct.map_surjective (LieSubmodule.Quotient.surjective_mk' _) Function.surjective_id
  obtain ⟨g₀, hg₀⟩ := LieModuleHom.exists_comp_eq_of_surjective π hπ
    exists_finiteDimensional_mem_adRegular_tensor
    (fun N _ ↦ complementedLattice_of_finiteDimensional (V := N) hA) g
  refine ⟨(TensorProduct.LieModule.map (LieSubmodule.Quotient.mk' (adIdeal K 𝔤 ⊥))
    (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W)).comp g₀, ?_⟩
  have hcomp : ∀ t, TensorProduct.LieModule.map (adQuotientMap K 𝔤 bot_le) LieModuleHom.id
      (TensorProduct.LieModule.map (LieSubmodule.Quotient.mk' (adIdeal K 𝔤 ⊥))
        (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W) t) = π t := by
    intro t
    induction t with
    | add s t hs ht => rw [map_add, map_add, hs, ht, map_add]
    | tmul u w => rfl
  rw [← hg₀]
  ext v
  exact hcomp (g₀ v)

include hA in
/-- **Extension of natural transformations**: for `A` of finite type, `V`, `W` finite-dimensional
and `g : V → (U / I)^{ad} ⊗ W`, there is a natural transformation `M ⊗ V → M ⊗ W` on all
modules (`tensorNatMap g'`, `g' : V → (U / ⊥)^{ad} ⊗ W`) which agrees with `tensorNatMap g` on
every module killed by `I`. -/
theorem exists_tensorNatMap_eq (I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤))
    {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule 𝔤 V] [LieModule K 𝔤 V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [LieRingModule 𝔤 W]
    [LieModule K 𝔤 W] [FiniteDimensional K W] (g : V →ₗ⁅K,𝔤⁆ AdQuotient K 𝔤 I ⊗[K] W) :
    ∃ g' : V →ₗ⁅K,𝔤⁆ AdQuotient K 𝔤 ⊥ ⊗[K] W,
      ∀ (M : Type*) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
        (hM : IsKilledBy I M), tensorNatMap g' (isKilledBy_bot (M := M)) = tensorNatMap g hM := by
  obtain ⟨g', hg'⟩ := exists_lift_adQuotient P hA I g
  refine ⟨g', fun M _ _ _ _ hM ↦ ?_⟩
  rw [← hg', tensorNatMap_adQuotientMap]

end Matrix.Realization.KacMoodyAlgebra
