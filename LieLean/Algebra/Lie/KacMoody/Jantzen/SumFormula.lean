/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Formula

/-!
# The Jantzen sum formula

Let `A` be a symmetrizable generalized Cartan matrix and `K` algebraically closed of
characteristic zero. For `λ₀, δ ∈ 𝔥*` let `M(λ₀)^i` be the Jantzen filtration of the Verma module
`M(λ₀)` along the line `λ₀ + t δ` (`VermaModule.jantzen`). If the line is transversal to the
Kac–Kazhdan hyperplanes through `λ₀` (i.e. `(δ | α) ≠ 0` whenever `2 (λ₀ + ρ | α) = n (α | α)`),
then for every `η ∈ Q₊`

`∑_{i ≥ 1} dim M(λ₀)^i_{λ₀ - η} = ∑_{(α, n)} dim M(λ₀ - n α)_{λ₀ - η}`,

the sum on the right over positive roots `α` (with multiplicity) and `n ≥ 1` with
`2 (λ₀ + ρ | α) = n (α | α)` (`VermaModule.finsum_finrank_jantzen_inf_weightSpace`,
`VermaModule.finsum_finrank_jantzen_inf_weightSpace_eq_sum_verma`). In terms of
formal characters this is the **Jantzen sum formula**
`∑_{i ≥ 1} ch M(λ₀)^i = ∑_{α > 0} ∑_{n ≥ 1, 2 (λ₀ + ρ | α) = n (α | α)} mult α · ch M(λ₀ - n α)`
([HumO] §5.3 for finite type; [KK] and [Kum] Thm. 2.3.4 for the determinant; [Kum] Cor. 2.3.5
for the sum formula itself).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.finsum_finrank_jantzen_inf_weightSpace`,
  `VermaModule.finsum_finrank_jantzen_inf_weightSpace_eq_sum_verma` (in the form with Verma
  modules): the Jantzen sum formula, weight space by weight space.

## Proof

By the order formula (`VermaModule.sum_finrank_jantzen_inf_weightSpace`), the left side is the
order of vanishing at `t = 0` of `D_η(λ₀ + t δ)`, which by the Kac–Kazhdan determinant formula
(`VermaModule.exists_shapovalovDet_eq_prod_kkPairs`) is a nonzero constant times
`∏_{(x, n)} (((λ₀ + ρ | α_x) - n (α_x | α_x)/2) + t (δ | α_x))^{P(η - n α_x)}`. The factors with
`2 (λ₀ + ρ | α_x) = n (α_x | α_x)` vanish to order one, the others not at all.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, §5.3.
* [KK] V. G. Kac, D. A. Kazhdan, *Structure of representations with highest weight of
  infinite-dimensional Lie algebras*, Adv. Math. **34** (1979), 97–108.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, Thm. 2.3.4, Cor. 2.3.5.
-/

open Module LieModule Module.Dual Polynomial

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (S : A.Symmetrization) (hA : A.IsGeneralizedCartan)

namespace VermaModule

include hA in
open Classical in
/-- **The Jantzen sum formula** (weight space form). Let `A` be a symmetrizable generalized Cartan
matrix, `K` algebraically closed of characteristic zero, and `λ₀, δ ∈ 𝔥*` with `(δ | α_x) ≠ 0`
whenever `2 (λ₀ + ρ | α_x) = n (α_x | α_x)` with `n α_x ≤ η`. Then
`∑_{i ≥ 1} dim M(λ₀)^i_{λ₀ - η} = ∑_{(x, n)} P(η - n α_x) = ∑_{(x, n)} dim M(λ₀ - n α_x)_{λ₀ - η}`,
the sums over `x` (an index of the root vector basis of `𝔫₋`) and `n ≥ 1` with `n α_x ≤ η` and
`2 (λ₀ + ρ | α_x) = n (α_x | α_x)`. -/
theorem finsum_finrank_jantzen_inf_weightSpace [IsAlgClosed K] (Λ₀ δ : Dual K H) (η : ι → ℤ)
    (hδ : ∀ x : NegRootIndex P, ∀ n : ℕ, (n + 1) • x.coeff ≤ η →
      2 * P.dualBilinForm S (Λ₀ + P.rho) x.root =
        ((n : K) + 1) * P.dualBilinForm S x.root x.root →
      P.dualBilinForm S δ x.root ≠ 0) :
    ∑ᶠ i : ℕ, finrank K ((jantzen P Λ₀ δ (i + 1)).toSubmodule ⊓
        weightSpace P Λ₀ (Λ₀ - P.rootOf η) : Submodule K _) =
      ∑ z ∈ (kkPairs P η).filter (fun z ↦ 2 * P.dualBilinForm S (Λ₀ + P.rho) z.1.root =
          ((z.2 : K) + 1) * P.dualBilinForm S z.1.root z.1.root),
        kostantPartition P (P.rootOf η - (z.2 + 1) • z.1.root) := by
  obtain ⟨c, hc, h⟩ := exists_shapovalovDet_eq_prod_kkPairs P S hA η
  set Z := kkPairs P η
  set a : NegRootIndex P × ℕ → H := fun z ↦ (P.toDual S).symm z.1.root
  set b : NegRootIndex P × ℕ → K := fun z ↦ P.dualBilinForm S P.rho z.1.root -
    ((z.2 : K) + 1) / 2 * P.dualBilinForm S z.1.root z.1.root
  set e : NegRootIndex P × ℕ → ℕ := fun z ↦ kostantPartition P (P.rootOf η - (z.2 + 1) • z.1.root)
  set F := MvPolynomial.C c * ∏ z ∈ Z, affPoly K H (a z) (b z) ^ e z
  have hab (Λ : Dual K H) (z : NegRootIndex P × ℕ) : Λ (a z) + b z =
      P.dualBilinForm S (Λ + P.rho) z.1.root -
        ((z.2 : K) + 1) / 2 * P.dualBilinForm S z.1.root z.1.root := by
    simp only [a, b, ← dualBilinForm_apply_eq, map_add, LinearMap.add_apply]
    ring
  have hF (Λ : Dual K H) : evalPoly K H F Λ = shapovalovDet P (P.rootOf η) Λ := by
    rw [h Λ]
    simp only [F, map_mul, map_prod, map_pow, Pi.mul_apply, Finset.prod_apply, Pi.pow_apply,
      evalPoly_C, evalPoly_affPoly, hab, e]
  have hiff (z : NegRootIndex P × ℕ) : Λ₀ (a z) + b z = 0 ↔
      2 * P.dualBilinForm S (Λ₀ + P.rho) z.1.root =
        ((z.2 : K) + 1) * P.dualBilinForm S z.1.root z.1.root := by
    rw [hab]
    constructor <;> intro h0
    · linear_combination 2 * h0
    · linear_combination h0 / 2
  have hδ' (z : NegRootIndex P × ℕ) (hz : z ∈ Z) : Λ₀ (a z) + b z = 0 → δ (a z) ≠ 0 :=
    fun h0 ↦ by
      rw [← dualBilinForm_apply_eq]
      exact hδ z.1 z.2 ((mem_kkPairs P).mp hz) ((hiff z).mp h0)
  classical
  set d := linePoly K H Λ₀ δ F
  have hd0 : d ≠ 0 := linePoly_C_mul_prod_ne_zero Z a b e hc hδ'
  have hdt := natTrailingDegree_linePoly_prod Z a b e hc hδ'
  have hdet (t : K) : d.eval t = shapovalovDet P (P.rootOf η) (Λ₀ + t • δ) := by
    rw [eval_linePoly, hF]
  have hsum := sum_finrank_jantzen_inf_weightSpace S Λ₀ δ (P.rootOf η) d hd0 hdet
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range d.natTrailingDegree) fun i hi ↦ ?_,
    hsum, hdt]
  · exact Finset.sum_congr (Finset.filter_congr fun z _ ↦ hiff z) fun _ _ ↦ rfl
  · by_contra hi'
    rw [Finset.coe_range, Set.mem_Iio, not_lt] at hi'
    exact hi (finrank_jantzen_inf_weightSpace_eq_zero S Λ₀ δ _ d hd0 hdet (by omega))

include hA in
open Classical in
/-- **The Jantzen sum formula** in terms of Verma modules:
`∑_{i ≥ 1} dim M(λ₀)^i_{λ₀ - η} = ∑_{(x, n)} dim M(λ₀ - n α_x)_{λ₀ - η}` (see
`finsum_finrank_jantzen_inf_weightSpace`), i.e. coefficientwise
`∑_{i ≥ 1} ch M(λ₀)^i = ∑_{(x, n) : 2 (λ₀ + ρ | α_x) = n (α_x | α_x)} ch M(λ₀ - n α_x)`. -/
theorem finsum_finrank_jantzen_inf_weightSpace_eq_sum_verma [IsAlgClosed K] (Λ₀ δ : Dual K H)
    (η : ι → ℤ)
    (hδ : ∀ x : NegRootIndex P, ∀ n : ℕ, (n + 1) • x.coeff ≤ η →
      2 * P.dualBilinForm S (Λ₀ + P.rho) x.root =
        ((n : K) + 1) * P.dualBilinForm S x.root x.root →
      P.dualBilinForm S δ x.root ≠ 0) :
    ∑ᶠ i : ℕ, finrank K ((jantzen P Λ₀ δ (i + 1)).toSubmodule ⊓
        weightSpace P Λ₀ (Λ₀ - P.rootOf η) : Submodule K _) =
      ∑ z ∈ (kkPairs P η).filter (fun z ↦ 2 * P.dualBilinForm S (Λ₀ + P.rho) z.1.root =
          ((z.2 : K) + 1) * P.dualBilinForm S z.1.root z.1.root),
        finrank K (weightSpace P (Λ₀ - (z.2 + 1) • z.1.root) (Λ₀ - P.rootOf η)) := by
  rw [finsum_finrank_jantzen_inf_weightSpace P S hA Λ₀ δ η hδ]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have := finrank_weightSpace_sub P (Λ₀ - (z.2 + 1) • z.1.root)
    (P.rootOf η - (z.2 + 1) • z.1.root)
  rw [show Λ₀ - (z.2 + 1) • z.1.root - (P.rootOf η - (z.2 + 1) • z.1.root) =
    Λ₀ - P.rootOf η by abel] at this
  exact this.symm

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
