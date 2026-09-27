/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Character
import LieLean.Algebra.Lie.KacMoody.HighestWeight

/-!
# Weyl group invariance of characters of integrable modules

The Weyl group `W` does not act on the algebra `ℰ` of formal characters (it does not preserve
the cones `Λ - Q₊`), but it acts on the coefficient functions `𝔥* → R`, and it makes sense to ask
whether an element `c ∈ ℰ` is `W`-invariant: `c_{w μ} = c_μ` for all `w ∈ W` and `μ ∈ 𝔥*`. The
character of an integrable module in the category `𝒪` is `W`-invariant ([Kac] Prop. 3.7 (b),
§10.1 (check)); in particular so is the character of `L(Λ)` for dominant integral `Λ`.

## Main definitions

* `Matrix.Realization.CharacterRing.IsWeylInvariant`: `W`-invariance of an element of `ℰ`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.isWeylInvariant_character`: the character of an
  integrable module in `𝒪` is `W`-invariant.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.isWeylInvariant_character`: the character
  of `L(Λ)`, `Λ` dominant integral, is `W`-invariant.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §3.7, §10.1.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)

namespace CharacterRing

/-- An element `c ∈ ℰ` is `W`-invariant if `c_{w μ} = c_μ` for all `w ∈ W` and `μ ∈ 𝔥*`. -/
def IsWeylInvariant {R : Type*} [Zero R] (c : P.CharacterRing R) : Prop :=
  ∀ w ∈ P.weylGroup hA, ∀ μ, c.coeffAt (w μ) = c.coeffAt μ

end CharacterRing

namespace KacMoodyAlgebra

variable {P} {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-- The character of an integrable module in the category `𝒪` is `W`-invariant
([Kac] Prop. 3.7 (b) (check)). -/
theorem IsCategoryO.isWeylInvariant_character (hV : IsCategoryO P V) (hI : IsIntegrable P V) :
    hV.character.IsWeylInvariant P hA := fun w hw μ ↦ by
  simp only [IsCategoryO.coeffAt_character, finrank]
  rw [rank_weightSpace_weylGroup hA hI hw μ]

/-- The character of the irreducible module `L(Λ)` with dominant integral highest weight `Λ` is
`W`-invariant ([Kac] §10.1 (check)). -/
theorem IrreducibleModule.isWeylInvariant_character {Λ : Dual K H}
    (hΛ : P.IsDominantIntegral Λ) :
    (IrreducibleModule.isCategoryO P Λ).character.IsWeylInvariant P hA :=
  IsCategoryO.isWeylInvariant_character hA _ ((IrreducibleModule.isIntegrable_iff P hA).mpr hΛ)

end KacMoodyAlgebra

end Matrix.Realization
