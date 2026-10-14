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
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_nonempty_equiv_of_isAtom`: a simple
  submodule of `M(λ)` is a Verma module (Humphreys, GSM 94, Theorem 4.2 (c); any GCM).

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
  AMS 2008, §4.1, §4.2.
-/

open Module

namespace Matrix.Realization.KacMoodyAlgebra

section FiniteType

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

end FiniteType

section General

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- **Humphreys, GSM 94, Theorem 4.2 (c).** A simple submodule of a Verma module `M(λ)` is
itself a Verma module. No finite-type hypothesis is needed; in finite type `M(λ)` has exactly one
simple submodule (`VermaModule.existsUnique_isAtom`). -/
theorem VermaModule.exists_nonempty_equiv_of_isAtom {Λ : Dual K H}
    {S : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ)} (hS : IsAtom S) :
    ∃ μ : Dual K H, Nonempty (VermaModule P μ ≃ₗ⁅K,P.KacMoodyAlgebra⁆ S) := by
  have : Nontrivial S := (LieSubmodule.nontrivial_iff_ne_bot K P.KacMoodyAlgebra _).mpr hS.1
  obtain ⟨μ, ψ, hψ⟩ := ((isCategoryO P _).lieSubmodule S).exists_lieModuleHom_verma
  let φ := S.incl.comp ψ
  have hφ0 : φ (hwv P μ) ≠ 0 := fun hz ↦ hψ (Subtype.ext hz)
  have hφ : φ ≠ 0 := fun h ↦ hφ0 (by rw [h, _root_.zero_apply])
  have hinj : Function.Injective ψ := fun a b hab ↦
    injective_of_ne_zero P hφ (by simp only [φ, LieModuleHom.comp_apply, hab])
  have hle : φ.range ≤ S := by
    intro x hx
    obtain ⟨m, rfl⟩ := (LieModuleHom.mem_range _ _).mp hx
    exact (ψ m).2
  have hrange : φ.range = S := by
    rcases hS.le_iff.mp hle with h | h
    · exact absurd ((LieSubmodule.mem_bot _).mp (h ▸ (LieModuleHom.mem_range _ _).mpr
        ⟨hwv P μ, rfl⟩)) hφ0
    · exact h
  have hsurj : Function.Surjective ψ := fun s ↦ by
    have hs : (s : VermaModule P Λ) ∈ φ.range := by rw [hrange]; exact s.2
    obtain ⟨m, hm⟩ := (LieModuleHom.mem_range _ _).mp hs
    exact ⟨m, Subtype.ext hm⟩
  exact ⟨μ, ⟨LieModuleEquiv.ofBijective ψ ⟨hinj, hsurj⟩⟩⟩

end General

end Matrix.Realization.KacMoodyAlgebra
