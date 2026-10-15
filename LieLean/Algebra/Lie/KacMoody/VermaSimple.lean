/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.SelfDualProjective
import LieLean.Algebra.Lie.KacMoody.TranslationUpperClosure
import LieLean.Algebra.Lie.KacMoody.UpperClosureNonintegral

/-!
# Simplicity criterion for Verma modules

For `A` of finite type and `K` algebraically closed of characteristic zero, the Verma module
`M(λ)` is simple if and only if `λ` is antidominant, i.e. `⟨λ + ρ, β^∨⟩ ∉ ℤ_{>0}` for every
positive root `β` ([HumO] Thm. 4.4, proved in general in Thm. 4.8).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.maxSubmodule_eq_bot_iff_isAntidominant`:
  `M'(λ) = 0` if and only if `λ` is antidominant.

## Proof

The direction "antidominant ⇒ simple" is `VermaModule.maxSubmodule_eq_bot_of_isAntidominant`
(linkage). For the converse, a positive root `β` with `⟨λ + ρ, β^∨⟩ = n > 0` gives the
Kac–Kazhdan condition `2 (λ + ρ | β) = n (β | β)` (`kacKazhdanStep_of_wallStep`), so `M(λ)` is
not simple by the Kac–Kazhdan criterion `maxSubmodule_eq_bot_iff_kacKazhdan`. This replaces
Humphreys' use of Verma's embedding `M(s_β · λ) ⊂ M(λ)` for nonsimple `β` ([HumO] Thm. 4.6,
§4.7); the argument is reconstructed.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §4.4, §4.8.
-/

noncomputable section

open Module

namespace Matrix.Realization.KacMoodyAlgebra.VermaModule

variable {ι : Type*} {H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

/-- **Simplicity criterion** ([HumO] Thm. 4.4, Thm. 4.8): for `A` of finite type and `K`
algebraically closed of characteristic zero, `M(λ)` is simple (`M'(λ) = 0`) if and only if `λ`
is antidominant. Humphreys works over `ℂ`. The direction "simple ⇒ antidominant" goes through the
Kac–Kazhdan criterion instead of Verma's embeddings for nonsimple roots (reconstructed). -/
theorem maxSubmodule_eq_bot_iff_isAntidominant {μ : Dual K H} :
    maxSubmodule P μ = ⊥ ↔ P.IsAntidominant hA.isGeneralizedCartan μ := by
  refine ⟨fun hbot v i hpos n hn ↦ ?_, maxSubmodule_eq_bot_of_isAntidominant P hA⟩
  have hA' := hA.isGeneralizedCartan
  by_contra! hn0
  obtain ⟨d, hdpos, hposDef⟩ := hA.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hposDef.isHermitian
  set S := Symmetrization.ofDiagonal d hdpos hsymm
  have hwall : P.WallStep hA' 0 (μ + P.rho)
      (μ + P.rho - n.toNat • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) := by
    refine ⟨v.val, v.2, i, n.toNat, isPosRoot_iff_mem_posWeights.mp hpos, by omega, by simp, ?_,
      rfl⟩
    rw [symm_apply_coroot_eq_corootPairing, hn]
    exact_mod_cast (Int.toNat_of_nonneg hn0.le).symm
  obtain ⟨α, hα, hαne, m, hm, -, hK⟩ := kacKazhdanStep_of_wallStep P S hA' hwall
  rw [sub_add_cancel] at hK
  exact (maxSubmodule_eq_bot_iff_kacKazhdan P S hA' μ).mp hbot α hα hαne m hm hK

end Matrix.Realization.KacMoodyAlgebra.VermaModule
