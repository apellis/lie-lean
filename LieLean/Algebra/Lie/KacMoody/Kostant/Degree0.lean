/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Kostant.Euler
import LieLean.Algebra.Lie.KacMoody.CharacterFormula

/-!
# The zeroth `𝔫₋`-homology of `L(Λ)`

For any weight `Λ` (not necessarily dominant integral), `H_0(𝔫₋, L(Λ)) = L(Λ) / 𝔫₋ L(Λ)` is
one-dimensional, of weight `Λ`: this is the degree-zero case `ℓ(w) = 0 ⟺ w = 1` of the
Garland–Lepowsky theorem ([GL] Thm. 8.6 (check); [Kum] Thm. 3.2.7 (check)), and holds for all
`Λ`.

## Proof

In degree `0` the chains are `1 ⊗ L(Λ) ≅ L(Λ)` and the boundaries are `1 ⊗ 𝔫₋ L(Λ)`. If `μ ≠ Λ`,
the weight space `L(Λ)_μ` is spanned by the images of the vectors `f_{j₁} ⋯ f_{jₖ} v_Λ` with
`k ≥ 1`, which lie in `𝔫₋ L(Λ)`; hence `H_0(𝔫₋, L(Λ))_μ = 0`. For `μ = Λ`, no chain of positive
degree has weight `Λ` (the weights of `L(Λ)` are `≤ Λ`), so by the Euler–Poincaré principle
`dim H_0(𝔫₋, L(Λ))_Λ` is the coefficient of `e^Λ` in `R ch L(Λ)`, which is `1`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.homologyWeightSpace_zero_eq_bot`:
  `H_0(𝔫₋, L(Λ))_μ = 0` for `μ ≠ Λ`.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.finrank_homologyWeightSpace_zero_self`:
  `dim H_0(𝔫₋, L(Λ))_Λ = 1`.

## References

* [GL] H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent.
  Math. **34** (1976), 37–76.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §3.2.
-/

open Module LieModule LieModule.ChevalleyEilenberg TensorProduct ExteriorAlgebra

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

open CharacterRing WeightOrd

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

lemma finsetWt_ne_zero {S : Finset (NegRootIndex P)} (hS : S.Nonempty) : finsetWt P S ≠ 0 := by
  obtain ⟨k, ⟨-, hk0⟩, hk⟩ := finsetWt_mem_posWeights P hS
  rw [← hk, ← map_zero P.rootOf]
  exact fun h ↦ hk0 (P.rootOf_injective h)

namespace IrreducibleModule

variable (Λ : Dual K H)

local notation "V" => IrreducibleModule P Λ
local notation "E" => ExteriorAlgebra K (nNeg P) ⊗[K] IrreducibleModule P Λ

/-- The only set `S` of indices with `L(Λ)_{Λ + wt S} ≠ 0` is `S = ∅`. -/
lemma eq_empty_of_weightSpace_add_finsetWt_ne_bot {S : Finset (NegRootIndex P)}
    (hS : weightSpace P V (Λ + finsetWt P S) ≠ ⊥) : S = ∅ := by
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  obtain ⟨k, hk, heq⟩ := VermaModule.exists_eq_sub_of_mem_weightSpace P Λ
    (LieSubmodule.Quotient.mk' _) (LieSubmodule.Quotient.surjective_mk' _) hx hx0
  obtain ⟨l, ⟨hl, -⟩, hlS⟩ := finsetWt_mem_posWeights P (Finset.nonempty_iff_ne_empty.mpr hne)
  have hkl : P.rootOf (k + l) = 0 := by
    rw [map_add, hlS, ← sub_eq_zero.mpr heq]
    abel
  rw [← map_zero P.rootOf] at hkl
  have hkl0 := P.rootOf_injective hkl
  have hl0 : l = 0 := le_antisymm (fun i ↦ by
    have := congrFun hkl0 i
    have := hk i
    simp only [Pi.add_apply, Pi.zero_apply] at *
    omega) hl
  exact finsetWt_ne_zero P (Finset.nonempty_iff_ne_empty.mpr hne) (by rw [← hlS, hl0, map_zero])

/-- No chain of positive degree has weight `Λ`: the maximal degree of a weight-`Λ` chain is `0`. -/
lemma maxDeg_self : (isCategoryO P Λ).maxDeg Λ = 0 := by
  classical
  refine Nat.eq_zero_of_le_zero (Finset.sup_le fun t ht ↦ ?_)
  simp only [IsCategoryO.chainIndexFinset, Finset.mem_biUnion, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq, Finset.mem_image] at ht
  obtain ⟨S, hS, j, -, rfl⟩ := ht
  simp [eq_empty_of_weightSpace_add_finsetWt_ne_bot P Λ hS]

/-- `dim H_0(𝔫₋, L(Λ))_Λ = 1`. -/
theorem finrank_homologyWeightSpace_zero_self :
    finrank K ((nNegDerivAction P V).homologyWeightSpace 0 Λ) = 1 := by
  have h := (isCategoryO P Λ).sum_neg_one_pow_finrank_nNegHomology Λ (N := 0)
    (maxDeg_self P Λ).le
  rw [coeffAt_denominator_mul_character_self, Finset.sum_range_one, pow_zero, one_mul] at h
  exact_mod_cast h

/-- The linear map `v ↦ 1 ⊗ v` from `L(Λ)` onto the chains of degree `0`. -/
abbrev oneTmul : V →ₗ[K] E := TensorProduct.mk K (ExteriorAlgebra K (nNeg P)) V 1

omit [CharZero K] in
lemma oneTmul_injective : Function.Injective (oneTmul P Λ) := by
  refine Function.LeftInverse.injective
    (g := (TensorProduct.lid K V).toLinearMap ∘ₗ LinearMap.rTensor V
      (algebraMapInv : ExteriorAlgebra K (nNeg P) →ₐ[K] K).toLinearMap) fun v ↦ ?_
  simp [oneTmul]

omit [CharZero K] in
lemma chainsIn_zero_le_range : chainsIn K (nNeg P) V 0 ≤ LinearMap.range (oneTmul P Λ) :=
  chainsIn_zero_le fun v ↦ ⟨v, rfl⟩

omit [CharZero K] in
/-- `1 ⊗ [f_j, u]` is a boundary. -/
lemma one_tmul_lie_f_mem_boundaries (j : ι) (u : V) :
    (1 : ExteriorAlgebra K (nNeg P)) ⊗ₜ ⁅f P j, u⁆ ∈ boundaries K (nNeg P) V 0 := by
  let y : nNeg P := ⟨f P j, f_mem_nNeg P j⟩
  refine ⟨-(ExteriorAlgebra.ι K y ⊗ₜ u), neg_mem (tmul_mem_chainsIn ?_ u), ?_⟩
  · rw [exteriorPower, pow_one]
    exact LinearMap.mem_range_self _ y
  · rw [map_neg, diff_ι_tmul, neg_neg, LieSubalgebra.coe_bracket_of_module]

/-- `H_0(𝔫₋, L(Λ))_μ = 0` for `μ ≠ Λ`: the weight vectors of `L(Λ)` of weight `μ ≠ Λ` lie in
`𝔫₋ L(Λ)`. -/
theorem homologyWeightSpace_zero_eq_bot {μ : Dual K H} (hμ : μ ≠ Λ) :
    (nNegDerivAction P V).homologyWeightSpace 0 μ = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨c, ⟨hcZ, hcμ⟩, rfl⟩
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨v, rfl⟩ := chainsIn_zero_le_range P Λ hcZ.1
  -- `v` has weight `μ`
  have hv : v ∈ weightSpaceOfMap V (h P) μ := fun a ↦ oneTmul_injective P Λ (by
    have := DerivAction.mem_chainWeightSpace.mp hcμ a
    simpa [oneTmul, nNegDerivAction, DerivAction.θ_one_tmul, tmul_smul] using this)
  clear hcZ hcμ
  -- `L(Λ)_μ` is the image of `M(Λ)_μ`, spanned by the `f_{j₁} ⋯ f_{jₖ} v_Λ`, `k ≥ 1`
  have hmap := map_weightSpaceOfMap_quotient P (VermaModule.maxSubmodule P Λ)
    (VermaModule.isCategoryO P Λ).iSup_weightSpaceOfMap_eq_top μ
  rw [← hmap, show weightSpaceOfMap (VermaModule P Λ) (h P) μ = VermaModule.wordSpan P Λ μ from
    VermaModule.weightSpace_eq_wordSpan P Λ μ, VermaModule.wordSpan, Submodule.map_span] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hx
    cases w with
    | nil => exact absurd (by simpa using hw) hμ.symm
    | cons j w =>
      beta_reduce
      rw [VermaModule.fWord_smul_cons, quotMk, LieModuleHom.coe_toLinearMap,
        LieModuleHom.map_lie]
      exact one_tmul_lie_f_mem_boundaries P Λ j _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

end IrreducibleModule

end Matrix.Realization.KacMoodyAlgebra
