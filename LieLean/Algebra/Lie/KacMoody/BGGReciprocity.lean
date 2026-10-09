/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.ProjectiveCoverHom
import LieLean.Algebra.Lie.KacMoody.DualVerma

/-!
# BGG reciprocity

Humphreys, GSM 94, Theorem 3.10 and Theorem 3.11: `P(λ)` has a standard filtration, and in every
standard filtration of `P(λ)` the multiplicity of `M(μ)` is `(P(λ) : M(μ)) = [M(μ) : L(λ)]`. In
particular `M(λ)` occurs once and all other `M(μ)` have `μ > λ`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.isStdFiltered_top_range`: a direct summand `e(Q)` with a
  standard filtration as a submodule of `Q` has one as a module.
* `Matrix.Realization.KacMoodyAlgebra.IsProjectiveCover.count_eq_multiplicity`: BGG reciprocity
  for any projective cover with a standard filtration.
* `Matrix.Realization.KacMoodyAlgebra.ProjectiveCover.exists_isStdFiltered`: **Theorem 3.10**,
  `P(λ)` has a standard filtration, `M(λ)` occurs once and the other factors `M(μ)` have
  `λ ∈ μ - Q₊`.
* `Matrix.Realization.KacMoodyAlgebra.ProjectiveCover.count_eq_multiplicity`:
  **Theorem 3.11 (BGG reciprocity)**, `(P(λ) : M(μ)) = [M(μ) : L(λ)]`.

## Proof

As in Humphreys: both sides equal `dim Hom(P(λ), M(μ)^∨)`, by Theorem 3.7
(`IsStdFiltered.count_eq_finrank_hom`) and Theorem 3.9 (c)
(`IsProjectiveCover.finrank_hom_eq_multiplicity`), using `[M(μ)^∨ : L(λ)] = [M(μ) : L(λ)]`
(`multiplicity_restrictedDual`). The standard filtration of `P(λ)` comes from that of
`M(λ + nρ) ⊗ L(nρ)^*` (Theorem 3.6) and Proposition 3.7 (b).

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.10, §3.11.
-/

noncomputable section

open Module LieModule

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Summand

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {Q : Type*} [AddCommGroup Q] [Module K Q] [LieRingModule P.KacMoodyAlgebra Q]
  [LieModule K P.KacMoodyAlgebra Q]

omit [CharZero K] in
/-- If the range of an idempotent `e` has a standard filtration as a submodule of `Q`, then it has
one as a module. -/
theorem isStdFiltered_top_range {e : Q →ₗ⁅K,P.KacMoodyAlgebra⁆ Q} (he : e.comp e = e)
    {t : Multiset (Dual K H)} (ht : IsStdFiltered P e.range t) :
    IsStdFiltered P (⊤ : LieSubmodule K P.KacMoodyAlgebra e.range) t := by
  have hmap : e.range.map (rangeRetr e) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact ⟨y.1, y.2, rangeRetr_incl he y⟩
  rw [← hmap]
  refine ht.map_of_injOn P (rangeRetr e) (fun x hx hx0 ↦ ?_) le_rfl
  obtain ⟨y, rfl⟩ := hx
  have : e (e y) = 0 := congrArg Subtype.val hx0
  rwa [← LieModuleHom.comp_apply e e, he] at this

end Summand

section Reciprocity

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (Λ : Dual K H)

namespace IsProjectiveCover

variable {P Λ} {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] {π : V →ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P Λ}

/-- **BGG reciprocity** (Humphreys, GSM 94, Theorem 3.11) for a projective cover `V → L(λ)` with a
standard filtration with weights `t`: `(V : M(μ)) = [M(μ) : L(λ)]`. -/
theorem count_eq_multiplicity [DecidableEq (Dual K H)] (hπ : IsProjectiveCover P V π)
    (hproj : IsProjectiveO.{max u₁ u₂} P V) {t : Multiset (Dual K H)}
    (ht : IsStdFiltered P (⊤ : LieSubmodule K P.KacMoodyAlgebra V) t) (μ : Dual K H) :
    t.count μ = (VermaModule.isCategoryO P μ).multiplicity Λ := by
  rw [ht.count_eq_finrank_hom hπ.isCategoryO μ,
    hπ.finrank_hom_eq_multiplicity hproj (isCategoryO_restrictedDual (VermaModule.isCategoryO P μ)),
    multiplicity_restrictedDual]

end IsProjectiveCover

variable [IsAlgClosed K] [FiniteDimensional K H] (hA : A.IsFiniteCartan)

namespace ProjectiveCover

omit [IsAlgClosed K] in
/-- `P(λ)` has a standard filtration (as a submodule of `M(λ + nρ) ⊗ L(nρ)^*`, Theorem 3.6 and
Proposition 3.7 (b)). -/
theorem exists_isStdFiltered_range :
    ∃ t, IsStdFiltered P (projectiveCoverIdem P hA Λ).range t := by
  classical
  set n := projectiveCoverShift P hA Λ
  have := IrreducibleModule.finiteDimensional (P := P) hA (isDominantIntegral_nsmul_rho P n)
  obtain ⟨s, hs, -⟩ := exists_isStdFiltered_tensorVerma P
    (isCategoryO_dual_irreducible_nsmul_rho P hA n).iSup_weightSpaceOfMap_eq_top
    (Λ + (n : K) • P.rho)
  obtain ⟨t, -, ht, -, -⟩ := exists_isStdFiltered_range_add P
    (isCategoryO_projectiveCoverAmbient P hA Λ n) hs (projectiveCoverIdem P hA Λ)
    (projectiveCoverIdem_idem P hA Λ)
  exact ⟨t, ht⟩

/-- **Humphreys, GSM 94, Theorem 3.11 (BGG reciprocity).** In every standard filtration of
`P(λ)`, the multiplicity of `M(μ)` is `[M(μ) : L(λ)]`. -/
theorem count_eq_multiplicity [DecidableEq (Dual K H)] {t : Multiset (Dual K H)}
    (ht : IsStdFiltered P (⊤ : LieSubmodule K P.KacMoodyAlgebra (ProjectiveCover P hA Λ)) t)
    (μ : Dual K H) : t.count μ = (VermaModule.isCategoryO P μ).multiplicity Λ :=
  (isProjectiveCover P Λ hA).count_eq_multiplicity (isProjectiveO P hA Λ) ht μ

/-- **Humphreys, GSM 94, Theorem 3.10.** `P(λ)` has a standard filtration; in any such filtration
`M(λ)` occurs exactly once and every factor `M(μ)` has `λ ∈ μ - Q₊`. -/
theorem exists_isStdFiltered [DecidableEq (Dual K H)] :
    ∃ t, IsStdFiltered P (⊤ : LieSubmodule K P.KacMoodyAlgebra (ProjectiveCover P hA Λ)) t ∧
      t.count Λ = 1 ∧ ∀ μ ∈ t, Λ ∈ cone P μ := by
  obtain ⟨t, ht⟩ := exists_isStdFiltered_range P Λ hA
  have ht' := isStdFiltered_top_range P (projectiveCoverIdem_idem P hA Λ) ht
  refine ⟨t, ht', ?_, fun μ hμ ↦ ?_⟩
  · rw [count_eq_multiplicity P Λ hA ht' Λ, VermaModule.multiplicity_self]
  · have h := count_eq_multiplicity P Λ hA ht' μ
    have hpos : t.count μ ≠ 0 := (Multiset.count_pos.mpr hμ).ne'
    rw [h] at hpos
    exact VermaModule.mem_cone_of_multiplicity_ne_zero hpos

end ProjectiveCover

end Reciprocity

end Matrix.Realization.KacMoodyAlgebra
