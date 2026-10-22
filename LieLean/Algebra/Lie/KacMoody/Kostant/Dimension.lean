/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Kostant.Theorem
import LieLean.Algebra.Lie.KacMoody.CharacterFormula.Orbit
import Mathlib.Data.Set.Finite.List

/-!
# Dimensions of `H_k(𝔫₋, L(Λ))`

Let `A` be a symmetrizable generalized Cartan matrix and `Λ` a dominant integral weight. By the
Garland–Lepowsky theorem (`IrreducibleModule.homologyWeightSpace_ne_bot_iff`,
`IrreducibleModule.finrank_homologyWeightSpace_eq_one`), `H_k(𝔫₋, L(Λ))` is the direct sum of
one-dimensional weight spaces of weights `w(Λ + ρ) - ρ`, `ℓ(w) = k`, and these weights are
pairwise distinct since `Λ + ρ` is regular. Hence

  `dim H_k(𝔫₋, L(Λ)) = #{w ∈ W | ℓ(w) = k}`,

a finite number for every `k`. In finite type this is the dimension statement of Bott's theorem
([HumO] Thm. 6.6) in the homological form for `𝔫₋`; the cohomological form for `𝔫` is not
formalized.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.finite_setOf_length_eq`: `W` has finitely
  many elements of each length.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.finrank_homology`:
  `dim H_k(𝔫₋, L(Λ)) = #{w ∈ W | ℓ(w) = k}`.

## References

* [GL] H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent.
  Math. **34** (1976), 37–76, Thm. 8.6.
* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Thm. 6.6.
-/

open Module LieModule LieModule.ChevalleyEilenberg

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

namespace IrreducibleModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  (hA : A.IsGeneralizedCartan) (hS : A.IsSymmetrizable) {Λ : Dual K H}
  (hΛ : P.IsDominantIntegral Λ)

omit [FiniteDimensional K H] in
/-- The Weyl group has finitely many elements of each length. -/
theorem finite_setOf_length_eq (k : ℕ) :
    {w : P.weylGroup hA | (P.coxeterSystem hA).length w = k}.Finite := by
  refine ((List.finite_length_eq ι k).image (P.coxeterSystem hA).wordProd).subset ?_
  intro w hw
  obtain ⟨ω, hω, rfl⟩ := (P.coxeterSystem hA).exists_isReduced w
  exact ⟨ω, hω.eq.symm.trans hw, rfl⟩

omit [DecidableEq ι] [FiniteDimensional K H] in
include hΛ in
/-- The weights `w(Λ + ρ) - ρ`, `w ∈ W`, are pairwise distinct. -/
theorem injective_apply_add_rho_sub_rho :
    Function.Injective fun w : P.weylGroup hA ↦
      (w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho := by
  have hreg : ∀ i, ∃ n : ℕ, (Λ + P.rho) (P.coroot i) = n + 1 := fun i ↦ by
    obtain ⟨n, hn⟩ := hΛ i
    exact ⟨n, by rw [LinearMap.add_apply, hn, rho_coroot]⟩
  exact fun w w' h ↦ P.apply_injective_of_regular hA hreg (sub_left_injective h)

omit [FiniteDimensional K H] in
/-- If the nonzero weight spaces of `H_k(𝔫₋, L(Λ))` are indexed injectively by `T` and are all
one-dimensional, then `dim H_k(𝔫₋, L(Λ)) = |T|`. -/
theorem finrank_homology_eq_card {T : Type*} (k : ℕ) (μ : T → Dual K H)
    (hμ : Function.Injective μ)
    (hne : ∀ ν, (nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace k ν ≠ ⊥ ↔
      ∃ t, μ t = ν)
    (h1 : ∀ t, finrank K ((nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace k
      (μ t)) = 1) :
    finrank K (homology K (nNeg P) (IrreducibleModule P Λ) k) = Nat.card T := by
  choose v hv hv0 using fun t ↦ Submodule.exists_mem_ne_zero_of_ne_bot ((hne (μ t)).mpr ⟨t, rfl⟩)
  have hli := (iSupIndep.comp
    ((nNegDerivAction P (IrreducibleModule P Λ)).iSupIndep_homologyWeightSpace k)
    hμ).linearIndependent _ hv hv0
  have hle (t : T) : (nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace k (μ t) ≤
      K ∙ v t := fun x hx ↦ by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v t, hv t⟩ : ↥(_ : Submodule K _))
      (fun h ↦ hv0 t (congrArg Subtype.val h))).mp (h1 t) ⟨x, hx⟩
    exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
  have hsup : homology K (nNeg P) (IrreducibleModule P Λ) k = Submodule.span K (Set.range v) := by
    rw [← iSup_nNegHomologyWeightSpace P _ (isCategoryO P Λ).iSup_weightSpaceOfMap_eq_top k,
      Submodule.span_range_eq_iSup]
    refine le_antisymm (iSup_le fun ν ↦ ?_) (iSup_le fun t ↦ ?_)
    · by_cases h : (nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace k ν = ⊥
      · exact h.le.trans bot_le
      · obtain ⟨t, rfl⟩ := (hne ν).mp h
        exact (hle t).trans (le_iSup (fun t ↦ K ∙ v t) t)
    · exact ((Submodule.span_singleton_le_iff_mem _ _).mpr (hv t)).trans (le_iSup_of_le _ le_rfl)
  rw [hsup, Module.finrank_eq_nat_card_basis (Module.Basis.span hli)]

include hA hS hΛ

/-- **Dimensions of `H_k(𝔫₋, L(Λ))`** (cf. [HumO] Thm. 6.6, homological form): for `A`
symmetrizable and `Λ` dominant integral, `dim H_k(𝔫₋, L(Λ)) = #{w ∈ W | ℓ(w) = k}`. -/
theorem finrank_homology (k : ℕ) :
    finrank K (homology K (nNeg P) (IrreducibleModule P Λ) k) =
      Nat.card {w : P.weylGroup hA // (P.coxeterSystem hA).length w = k} := by
  refine finrank_homology_eq_card k
    (fun w ↦ ((w.1 : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho)
    ((injective_apply_add_rho_sub_rho hA hΛ).comp Subtype.val_injective) (fun ν ↦ ?_)
    (fun w ↦ ?_)
  · rw [homologyWeightSpace_ne_bot_iff hA hS hΛ k ν]
    exact ⟨fun ⟨w, hw, h⟩ ↦ ⟨⟨w, hw⟩, h⟩, fun ⟨w, h⟩ ↦ ⟨w.1, w.2, h⟩⟩
  · have h := finrank_homologyWeightSpace_eq_one hA hS hΛ w.1
    rwa [w.2] at h

end IrreducibleModule

end Matrix.Realization.KacMoodyAlgebra
