/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOExtVerma
import LieLean.Algebra.Lie.KacMoody.DualVermaSocle
import LieLean.Algebra.Lie.KacMoody.EnoughInjectives
import LieLean.Algebra.Lie.KacMoody.FiniteLength

/-!
# `Extⁿ` into dual Verma modules

**[HumO] Theorem 6.12**: `Extⁿ_𝒪(M(μ), M(λ)^∨) = 0` for all `n > 0` and all `λ, μ`
(`CategoryO.ext_verma_dualVerma_eq_zero`), and more generally `Extⁿ_𝒪(M, M(λ)^∨) = 0` for every
`M` with a standard filtration (`CategoryO.ext_dualVerma_eq_zero_of_isStdFiltered`). Humphreys
states this for `𝔤` semisimple over `ℂ`; here `𝔤` is of finite type over an algebraically closed
field of characteristic zero.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.CategoryO.dualVerma`: the dual Verma module `M(λ)^∨` as an
  object of `𝒪`.

## Proof

As in Humphreys, by induction on `n`. The case `n = 1` is Theorem 3.3 (d)
(`extOne_verma_restrictedDual_verma_eq_zero`). For the induction step on Verma modules, the kernel
of `P(μ) → M(μ)` has a standard filtration (`ext_succ_verma_eq_zero`), and `Extⁿ` vanishes along
standard filtrations factor by factor (`ext_eq_zero_of_isStdFiltered`).

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §3.3, §6.12.
-/

open CategoryTheory Limits LieModule Module

noncomputable section

universe u

namespace Matrix.Realization.KacMoodyAlgebra

namespace CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P

variable (P) in
/-- The dual Verma module `M(λ)^∨` as an object of `𝒪`. -/
def dualVerma (lam : Dual K H) : CategoryO.{u} P :=
  mk (restrictedDual P (VermaModule P lam))
    (isCategoryO_restrictedDual (VermaModule.isCategoryO P lam)) (by
      obtain ⟨f, hf⟩ :=
        VermaModule.exists_strictMono_lieSubmodule P (Fact.out : A.IsFiniteCartan) lam
      obtain ⟨F, hF⟩ := (VermaModule.isCategoryO P lam).exists_strictMono_restrictedDual P hf
      exact LieSubmodule.exists_finset_lieSpan_eq_top_of_strictMono hF)

/-- `Extⁿ(X, Y) = 0` if `Extⁿ(X', Y) = 0` for the object `X'` given by the submodule `⊤` of `X`. -/
theorem ext_eq_zero_of_ofSub_top (X Y : CategoryO.{u} P) {n : ℕ}
    (h : ∀ x : Abelian.Ext.{u} (ofSub X ⊤) Y n, x = 0) (x : Abelian.Ext.{u} X Y n) : x = 0 := by
  let z : X.obj →ₗ⁅K,𝔤⁆ (ofSub X ⊥).obj := 0
  have hz : Function.Surjective z := fun _ ↦ ⟨0, (ofLieEquiv (P := P)
    (⊥ : LieSubmodule K 𝔤 X.obj)).symm.injective (Subsingleton.elim _ _)⟩
  have hz0 : z.ker = ⊤ := eq_top_iff.mpr fun y _ ↦ LieModuleHom.mem_ker.mpr rfl
  have h' : ∀ x : Abelian.Ext.{u} (ofSub X z.ker) Y n, x = 0 := by
    rw [hz0]
    exact h
  exact Abelian.Ext.eq_zero_of_shortExact_left (shortExact_kerComplex X (ofSub X ⊥) z hz) h'
    (Abelian.Ext.eq_zero_of_isZero_left (isZero_ofSub_bot X)) x

theorem ext_verma_dualVerma_eq_zero_aux (lam : Dual K H) (n : ℕ) : ∀ (μ : Dual K H)
    (x : Abelian.Ext.{u} (verma P μ) (dualVerma P lam) (n + 1)), x = 0 := by
  induction n with
  | zero =>
    intro μ x
    exact ext_one_eq_zero_of_extOne_of_equiv _ _ (VermaModule P μ)
      (restrictedDual P (VermaModule P lam)) (VermaModule.isCategoryO P μ)
      (ofLieEquiv (P := P) (VermaModule P μ))
      (ofLieEquiv (P := P) (restrictedDual P (VermaModule P lam)))
      (extOne_verma_restrictedDual_verma_eq_zero P lam μ) x
  | succ n ih =>
    intro μ x
    exact ext_succ_verma_eq_zero _ μ (n + 1) (fun κ _ _ ↦ ih κ) x

/-- **[HumO] Theorem 6.12**: `Extⁿ_𝒪(M(μ), M(λ)^∨) = 0` for all `n > 0` and all `λ, μ`. -/
theorem ext_verma_dualVerma_eq_zero (μ lam : Dual K H) {n : ℕ} (hn : 0 < n)
    (x : Abelian.Ext.{u} (verma P μ) (dualVerma P lam) n) : x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ext_verma_dualVerma_eq_zero_aux lam m μ x

/-- **[HumO] Theorem 6.12**, general form: `Extⁿ_𝒪(M, M(λ)^∨) = 0` for all `n > 0` if `M` has a
standard filtration. -/
theorem ext_dualVerma_eq_zero_of_isStdFiltered (X : CategoryO.{u} P) {s : Multiset (Dual K H)}
    (hX : IsStdFiltered P (⊤ : LieSubmodule K 𝔤 X.obj) s) (lam : Dual K H) {n : ℕ} (hn : 0 < n)
    (x : Abelian.Ext.{u} X (dualVerma P lam) n) : x = 0 :=
  ext_eq_zero_of_ofSub_top X _
    (ext_eq_zero_of_isStdFiltered X _ hX fun μ _ ↦ ext_verma_dualVerma_eq_zero μ lam hn) x

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
