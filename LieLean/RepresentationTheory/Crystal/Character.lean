/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.WeylAction
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Characters of crystals

The character of a finite crystal `B` is `ch B = ∑_{b ∈ B} e^{wt b}`, an element of the group ring
`ℤ[X]` of the weight lattice (`AddMonoidAlgebra ℤ X`). It is multiplicative for the tensor
product, invariant under isomorphisms, and, for seminormal crystals, invariant under the simple
reflections.

## Main definitions

* `Crystal.character`: the character of a finite crystal.

## Main results

* `Crystal.coeff_character`: the coefficient of `e^μ` is the number of elements of weight `μ`.
* `Crystal.character_tensor`: `ch (B₁ ⊗ B₂) = ch B₁ · ch B₂`.
* `Crystal.Equiv.character_eq`: isomorphic crystals have the same character.
* `Crystal.IsSeminormal.mapDomain_reflection_character`: `rᵢ (ch B) = ch B` for seminormal `B`.

## References

* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995).
* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, Ch. 4.
-/

open AddMonoidAlgebra

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B B₁ B₂ : Type*}

/-- The character `ch B = ∑_{b ∈ B} e^{wt b} ∈ ℤ[X]` of a finite crystal. -/
noncomputable def character [Fintype B] (C : Crystal D B) : AddMonoidAlgebra ℤ X :=
  ∑ b, single (C.wt b) 1

variable [Fintype B] (C : Crystal D B)

/-- The coefficient of `e^μ` in `ch B` is the number of elements of `B` of weight `μ`. -/
theorem coeff_character (μ : X) : C.character.coeff μ = Nat.card {b // C.wt b = μ} := by
  classical
  simp only [character, coeff_sum, coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The character of a tensor product of finite crystals is the product of the characters
([Kas] §7.3 (check)). -/
theorem character_tensor [Fintype B₁] [Fintype B₂] (C₁ : Crystal D B₁) (C₂ : Crystal D B₂) :
    (C₁.tensor C₂).character = C₁.character * C₂.character := by
  simp only [character, Finset.sum_mul_sum, single_mul_single, mul_one, tensor_wt]
  exact Fintype.sum_prod_type _

/-- Isomorphic finite crystals have the same character. -/
theorem Equiv.character_eq [Fintype B₁] [Fintype B₂] {C₁ : Crystal D B₁} {C₂ : Crystal D B₂}
    (ψ : Equiv C₁ C₂) : C₁.character = C₂.character := by
  simp only [character]
  exact Fintype.sum_equiv ψ.toEquiv _ _ fun b ↦ by simp

/-- The character of a finite seminormal crystal is invariant under the simple reflections:
`rᵢ (ch B) = ch B`, where `rᵢ` acts on `ℤ[X]` through its action on `X` ([Kas] §7.7 (check)). -/
theorem IsSeminormal.mapDomain_reflection_character {C : Crystal D B} (hC : C.IsSeminormal)
    (i : ι) :
    mapDomainRingEquiv ℤ (D.reflection i).toAddEquiv C.character = C.character := by
  simp only [character, map_sum, mapDomainRingEquiv_single, LinearEquiv.coe_toAddEquiv]
  refine Fintype.sum_equiv (hC.reflectionPerm i) _ _ fun b ↦ ?_
  simp [hC.wt_reflection]

/-- For a finite seminormal crystal, the number of elements of weight `rᵢ μ` equals the number of
elements of weight `μ`. -/
theorem IsSeminormal.coeff_character_reflection {C : Crystal D B} (hC : C.IsSeminormal) (i : ι)
    (μ : X) : C.character.coeff (D.reflection i μ) = C.character.coeff μ := by
  rw [coeff_character, coeff_character, hC.card_wt_reflection]

end Crystal
