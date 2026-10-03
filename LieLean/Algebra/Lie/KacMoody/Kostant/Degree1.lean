/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Kostant.Theorem

/-!
# `H_1(𝔫₋, L(Λ))`

Let `A` be a symmetrizable generalized Cartan matrix and `Λ` a dominant integral weight. The
elements of length one of the Weyl group are the fundamental reflections `rᵢ`, and
`rᵢ(Λ + ρ) - ρ = Λ - (⟨Λ, αᵢ^∨⟩ + 1) αᵢ`. The Garland–Lepowsky theorem in degree one therefore
says that

  `H_1(𝔫₋, L(Λ)) ≅ ⊕ᵢ K_{Λ - (⟨Λ, αᵢ^∨⟩ + 1) αᵢ}`

as `𝔥`-modules; in particular `dim H_1(𝔫₋, L(Λ)) = |I|`. (In terms of the presentation of
`L(Λ)` as a module over `U(𝔫₋)`, these are the weights of the generators `fᵢ^{⟨Λ, αᵢ^∨⟩ + 1} v_Λ`
of the kernel of `U(𝔫₋) → L(Λ)`, cf. `FPowQuotient.equivIrreducibleModule`.)

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.homologyWeightSpace_one_ne_bot_iff`:
  `H_1(𝔫₋, L(Λ))_μ ≠ 0` iff `μ = Λ - (⟨Λ, αᵢ^∨⟩ + 1) αᵢ` for some `i`.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.finrank_homologyWeightSpace_one`: these
  weight spaces are one-dimensional.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.finrank_homology_one`:
  `dim H_1(𝔫₋, L(Λ)) = |I|`.

## References

* [GL] H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent.
  Math. **34** (1976), 37–76, Thm. 8.6.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §3.2.
-/

open Module LieModule LieModule.ChevalleyEilenberg

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

namespace IrreducibleModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  (hA : A.IsGeneralizedCartan) (hS : A.IsSymmetrizable) {Λ : Dual K H}
  (hΛ : P.IsDominantIntegral Λ)

omit [DecidableEq ι] [CharZero K] [FiniteDimensional K H] in
/-- `rᵢ(Λ + ρ) - ρ = Λ - (⟨Λ, αᵢ^∨⟩ + 1) αᵢ`. -/
lemma reflection_add_rho_sub_rho (i : ι) :
    P.reflection hA i (Λ + P.rho) - P.rho = Λ - (Λ (P.coroot i) + 1) • P.root i := by
  rw [reflection_apply, LinearMap.add_apply, rho_coroot]
  abel

omit [DecidableEq ι] [FiniteDimensional K H] in
include hΛ in
/-- The weights `Λ - (⟨Λ, αᵢ^∨⟩ + 1) αᵢ` are pairwise distinct. -/
lemma injective_sub_smul_root :
    Function.Injective fun i ↦ Λ - (Λ (P.coroot i) + 1) • P.root i := by
  classical
  intro i j hij
  by_contra hne
  have h := sub_right_injective hij
  obtain ⟨n, hn⟩ := hΛ i
  have := linearIndependent_iff'.mp P.linearIndependent_root {i, j}
    (fun k ↦ if k = i then Λ (P.coroot i) + 1 else -(Λ (P.coroot j) + 1)) (by
      rw [Finset.sum_pair hne, ite_eq_left rfl, ite_eq_right (Ne.symm hne), neg_smul, h,
        add_neg_cancel])
    i (Finset.mem_insert_self i {j})
  rw [ite_eq_left rfl, hn] at this
  exact Nat.cast_add_one_ne_zero n this

include hA hS hΛ

/-- **`H_1(𝔫₋, L(Λ))`, weights** (the Garland–Lepowsky theorem in degree one):
`H_1(𝔫₋, L(Λ))_μ ≠ 0` iff `μ = Λ - (⟨Λ, αᵢ^∨⟩ + 1) αᵢ` for some `i`. -/
theorem homologyWeightSpace_one_ne_bot_iff (μ : Dual K H) :
    (nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace 1 μ ≠ ⊥ ↔
      ∃ i, Λ - (Λ (P.coroot i) + 1) • P.root i = μ := by
  rw [homologyWeightSpace_ne_bot_iff hA hS hΛ]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, rfl⟩ := (P.coxeterSystem hA).length_eq_one_iff.mp hw
    exact ⟨i, by rw [coxeterSystem_simple, reflection_add_rho_sub_rho]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, (P.coxeterSystem hA).length_simple i,
      by rw [coxeterSystem_simple, reflection_add_rho_sub_rho]⟩

/-- **`H_1(𝔫₋, L(Λ))`, multiplicities**: `dim H_1(𝔫₋, L(Λ))_{Λ - (⟨Λ, αᵢ^∨⟩ + 1) αᵢ} = 1`. -/
theorem finrank_homologyWeightSpace_one (i : ι) :
    finrank K ((nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace 1
      (Λ - (Λ (P.coroot i) + 1) • P.root i)) = 1 := by
  have := finrank_homologyWeightSpace_eq_one hA hS hΛ ((P.coxeterSystem hA).simple i)
  rwa [(P.coxeterSystem hA).length_simple, coxeterSystem_simple,
    reflection_add_rho_sub_rho] at this

/-- **`dim H_1(𝔫₋, L(Λ)) = |I|`**: `H_1(𝔫₋, L(Λ)) ≅ ⊕ᵢ K_{Λ - (⟨Λ, αᵢ^∨⟩ + 1) αᵢ}`. -/
theorem finrank_homology_one :
    finrank K (homology K (nNeg P) (IrreducibleModule P Λ) 1) = Fintype.card ι := by
  have hne : ∀ i, (nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace 1
      (Λ - (Λ (P.coroot i) + 1) • P.root i) ≠ ⊥ := fun i ↦
    (homologyWeightSpace_one_ne_bot_iff hA hS hΛ _).mpr ⟨i, rfl⟩
  choose v hv hv0 using fun i ↦ Submodule.exists_mem_ne_zero_of_ne_bot (hne i)
  have hli := (iSupIndep.comp
    ((nNegDerivAction P (IrreducibleModule P Λ)).iSupIndep_homologyWeightSpace 1)
    (injective_sub_smul_root hΛ)).linearIndependent _ hv hv0
  have hle (i : ι) : (nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace 1
      (Λ - (Λ (P.coroot i) + 1) • P.root i) ≤ K ∙ v i := fun w hw ↦ by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v i, hv i⟩ : ↥(_ : Submodule K _))
      (fun h ↦ hv0 i (congrArg Subtype.val h))).mp
      (finrank_homologyWeightSpace_one hA hS hΛ i) ⟨w, hw⟩
    exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
  have hsup : homology K (nNeg P) (IrreducibleModule P Λ) 1 = Submodule.span K (Set.range v) := by
    rw [← iSup_nNegHomologyWeightSpace P _ (isCategoryO P Λ).iSup_weightSpaceOfMap_eq_top 1,
      Submodule.span_range_eq_iSup]
    refine le_antisymm (iSup_le fun μ ↦ ?_) (iSup_le fun i ↦ ?_)
    · by_cases h : (nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace 1 μ = ⊥
      · exact h.le.trans bot_le
      · obtain ⟨i, rfl⟩ := (homologyWeightSpace_one_ne_bot_iff hA hS hΛ μ).mp h
        exact (hle i).trans (le_iSup (fun i ↦ K ∙ v i) i)
    · exact ((Submodule.span_singleton_le_iff_mem _ _).mpr (hv i)).trans (le_iSup_of_le _ le_rfl)
  rw [hsup, finrank_span_eq_card hli]

end IrreducibleModule

end Matrix.Realization.KacMoodyAlgebra
