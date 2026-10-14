/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.FiniteLength
import LieLean.Algebra.Lie.KacMoody.VermaUniformity

/-!
# The simple submodule of a Verma module

In finite type, every Verma module `M(λ)` has a unique simple submodule, which is contained in
every nonzero submodule; it is therefore the socle of `M(λ)` (Humphreys, GSM 94, Proposition 4.1).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.existsUnique_isAtom`: `M(λ)` has a unique
  simple submodule.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_isAtom_le`: there is a simple submodule
  of `M(λ)` contained in every nonzero submodule.

## Proof notes

Existence: `M(λ)` is artinian (`VermaModule.exists_strictMono_lieSubmodule`, from the proof of
Humphreys' Theorem 1.11). Uniqueness: two nonzero submodules of `M(λ)` intersect nontrivially
(`VermaModule.inf_ne_bot_of_finite_type`). Humphreys deduces this from Lemma 4.1
(`Submodule.inf_ne_bot_of_noZeroDivisors`) applied to the noetherian domain `U(𝔫⁻)`; here it
comes from the Ore condition for `U(𝔫⁻)`, proved by polynomial growth of the PBW filtration,
since noetherianity of `U(𝔫⁻)` is not formalized. Humphreys works with semisimple `𝔤` over
`ℂ`; here `K` is any field of characteristic zero and the Cartan matrix is of finite type.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §4.1.
-/

open Module

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

include hA

namespace VermaModule

/-- The simple submodule of `M(λ)`: there is a simple submodule of `M(λ)` contained in every
nonzero submodule (Humphreys, GSM 94, Proposition 4.1). -/
theorem exists_isAtom_le (Λ : Dual K H) :
    ∃ S : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ),
      IsAtom S ∧ ∀ N, N ≠ ⊥ → S ≤ N := by
  obtain ⟨f, hf⟩ := exists_strictMono_lieSubmodule P hA Λ
  have : WellFoundedLT (LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ)) := hf.wellFoundedLT
  have htop : (⊤ : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ)) ≠ ⊥ := fun h ↦
    hwv_ne_zero P Λ ((LieSubmodule.mem_bot _).mp (h ▸ LieSubmodule.mem_top (hwv P Λ)))
  obtain ⟨S, hS, -⟩ := (IsAtomic.eq_bot_or_exists_atom_le (⊤ : LieSubmodule K _ _)).resolve_left
    htop
  refine ⟨S, hS, fun N hN ↦ ?_⟩
  have h := inf_ne_bot_of_finite_type P hA Λ S N hS.1 hN
  rcases hS.le_iff.mp inf_le_left with h' | h'
  · exact absurd h' h
  · exact h' ▸ inf_le_right

/-- **Humphreys, GSM 94, Proposition 4.1.** In finite type, every Verma module `M(λ)` has a
unique simple submodule. -/
theorem existsUnique_isAtom (Λ : Dual K H) :
    ∃! S : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ), IsAtom S := by
  obtain ⟨S, hS, hle⟩ := exists_isAtom_le P hA Λ
  exact ⟨S, hS, fun T hT ↦ ((hT.le_iff.mp (hle T hT.1)).resolve_left hS.1).symm⟩

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
