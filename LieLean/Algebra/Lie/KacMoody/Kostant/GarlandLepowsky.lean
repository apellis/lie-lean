/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Kostant.Euler
import LieLean.Algebra.Lie.KacMoody.CharacterFormula

/-!
# `𝔫₋`-homology of integrable highest-weight modules and the Weyl–Kac formula

Let `A` be a symmetrizable generalized Cartan matrix, `𝔤 = 𝔤(A)` over a field `K` of
characteristic zero, and `Λ` a dominant integral weight. The **Garland–Lepowsky theorem**
([GL] Thm. 8.6; [Kum] Thm. 3.2.7; Kostant's theorem in finite type) states that
`H_k(𝔫₋, L(Λ)) ≅ ⊕_{w ∈ W, ℓ(w) = k} K_{w(Λ + ρ) - ρ}` as `𝔥`-modules.

Its standard proof has two steps:
1. (the Casimir step) every weight `μ` of `H_k(𝔫₋, L(Λ))` is of the form `w(Λ + ρ) - ρ` with
   `ℓ(w) = k`;
2. (the Euler characteristic step) by the Euler–Poincaré principle and the Weyl–Kac character
   formula, `∑_k (-1)^k ch H_k(𝔫₋, L(Λ)) = R ch L(Λ) = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ) - ρ}`;
   since the weights `w(Λ + ρ) - ρ` are pairwise distinct and, by step 1, each occurs in the
   single degree `ℓ(w)`, each occurs with multiplicity one.

This file proves step 2 unconditionally in the form of the identity
`e^ρ ∑_k (-1)^k ch H_k(𝔫₋, L(Λ)) = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ)}` (so the Euler
characteristic of `𝔫₋`-homology recovers the Weyl–Kac character formula), and deduces the
multiplicity statement of the Garland–Lepowsky theorem **from step 1, taken as a hypothesis**
(`finrank_homologyWeightSpace_eq_one_of_weights`). Step 1 (the Casimir / Laplacian argument
of [GL] Props. 7.9, 8.3) is proved in `LieLean.Algebra.Lie.KacMoody.Kostant.Theorem`, which contains
the unconditional theorem.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.exp_rho_mul_hsum_homologyEulerFamily`:
  `e^ρ ∑_k (-1)^k ch H_k(𝔫₋, L(Λ)) = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ)}`.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.sum_neg_one_pow_finrank_homology_apply`,
  `..._eq_zero`: the same identity coefficientwise.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.
  finrank_homologyWeightSpace_eq_one_of_weights`: if the weights of `H_k(𝔫₋, L(Λ))` lie in
  `{w(Λ + ρ) - ρ | ℓ(w) = k}` for all `k`, then
  `dim H_{ℓ(w)}(𝔫₋, L(Λ))_{w(Λ + ρ) - ρ} = 1` for all `w ∈ W`.

## References

* [GL] H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent.
  Math. **34** (1976), 37–76.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §3.2.
-/

open Module LieModule LieModule.ChevalleyEilenberg

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

open CharacterRing WeightOrd

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}

/-- The weights of `H_k(𝔫₋, V)` have the form `ν - wt S` with `ν` a weight of `V` and `S` a set of
`k` indices of a basis of root vectors of `𝔫₋`, i.e. `ν` minus a sum of `k` distinct positive
roots (counted with multiplicity). -/
theorem IsCategoryO.exists_of_homologyWeightSpace_ne_bot {V : Type*} [AddCommGroup V]
    [Module K V] [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
    (hV : IsCategoryO P V) {k : ℕ} {μ : Dual K H}
    (h : (nNegDerivAction P V).homologyWeightSpace k μ ≠ ⊥) :
    ∃ S : Finset (NegRootIndex P), S.card = k ∧ weightSpace P V (μ + finsetWt P S) ≠ ⊥ := by
  classical
  have := hV.finiteDimensional_nNegChains k μ
  have h2 : finrank K
      ↥(chainsIn K (nNeg P) V k ⊓ (nNegDerivAction P V).chainWeightSpace μ) ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    obtain ⟨c, ⟨hcZ, hcμ⟩, rfl⟩ := hx
    have hc0 : c ≠ 0 := fun hc ↦ hx0 (by rw [hc, map_zero])
    rw [Ne, Submodule.finrank_eq_zero]
    exact fun hbot ↦ hc0 ((Submodule.mem_bot K).mp (hbot ▸ ⟨hcZ.1, hcμ⟩))
  rw [hV.finrank_nNegChains, Finset.card_ne_zero] at h2
  obtain ⟨t, ht⟩ := h2
  obtain ⟨ht1, rfl⟩ := Finset.mem_filter.mp ht
  simp only [IsCategoryO.chainIndexFinset, Finset.mem_biUnion, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq, Finset.mem_image] at ht1
  obtain ⟨S, hS, j, -, rfl⟩ := ht1
  exact ⟨S, rfl, hS⟩

namespace IrreducibleModule

variable [FiniteDimensional K H] (hA : A.IsGeneralizedCartan) (hS : A.IsSymmetrizable)
  {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
include hA hS hΛ

/-- **The Euler characteristic of `𝔫₋`-homology recovers the Weyl–Kac character formula**
(cf. [GL] §9): for `Λ` dominant integral,
`e^ρ ∑_k (-1)^k ch H_k(𝔫₋, L(Λ)) = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ)}` in `ℰ`. -/
theorem exp_rho_mul_hsum_homologyEulerFamily :
    exp P ℤ P.rho * (isCategoryO P Λ).homologyEulerFamily.hsum =
      weylAltSum P hA (isDominantIntegral_add_rho hΛ) := by
  rw [IsCategoryO.hsum_homologyEulerFamily, ← mul_assoc,
    exp_rho_mul_denominator_mul_character hA hS hΛ]

omit [FiniteDimensional K H] in
omit hA hS hΛ in
lemma coeffAt_denominator_mul_character_eq (μ : Dual K H) :
    (denominator P * (isCategoryO P Λ).character).coeffAt μ =
      (exp P ℤ P.rho * denominator P * (isCategoryO P Λ).character).coeffAt (μ + P.rho) := by
  rw [mul_assoc, coeff_exp_mul, add_sub_cancel_right]

/-- The Euler characteristic of the weight-`w(Λ + ρ) - ρ` part of `𝔫₋`-homology:
`∑_k (-1)^k dim H_k(𝔫₋, L(Λ))_{w(Λ + ρ) - ρ} = (-1)^{ℓ(w)}`. -/
theorem sum_neg_one_pow_finrank_homology_apply (w : P.weylGroup hA) {N : ℕ}
    (hN : (isCategoryO P Λ).maxDeg ((w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho) ≤ N) :
    ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k *
        finrank K ((nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace k
          ((w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho)) =
      (-1) ^ (P.coxeterSystem hA).length w := by
  rw [IsCategoryO.sum_neg_one_pow_finrank_nNegHomology _ _ hN,
    coeffAt_denominator_mul_character_eq, sub_add_cancel,
    coeffAt_exp_rho_mul_denominator_mul_character_apply hA hS hΛ]

/-- The weights `μ` with `μ + ρ ∉ W(Λ + ρ)` do not contribute to the Euler characteristic:
`∑_k (-1)^k dim H_k(𝔫₋, L(Λ))_μ = 0`. -/
theorem sum_neg_one_pow_finrank_homology_eq_zero {μ : Dual K H}
    (hμ : ∀ w : P.weylGroup hA, (w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) ≠ μ + P.rho) {N : ℕ}
    (hN : (isCategoryO P Λ).maxDeg μ ≤ N) :
    ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k *
        finrank K ((nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace k μ) = 0 := by
  rw [IsCategoryO.sum_neg_one_pow_finrank_nNegHomology _ _ hN,
    coeffAt_denominator_mul_character_eq,
    coeffAt_exp_rho_mul_denominator_mul_character_eq_zero hA hS hΛ hμ]

/-- **The Garland–Lepowsky theorem, multiplicity part, from the weight restriction**
([GL] Thm. 8.6; [Kum] Thm. 3.2.7): if every weight of `H_k(𝔫₋, L(Λ))` is of the
form `w(Λ + ρ) - ρ` with `ℓ(w) = k` (hypothesis `hW`, the Casimir step of the proof, which is not
formalized here), then `dim H_{ℓ(w)}(𝔫₋, L(Λ))_{w(Λ + ρ) - ρ} = 1` for every `w ∈ W`. Together with
`hW` this is the full statement `H_k(𝔫₋, L(Λ)) ≅ ⊕_{ℓ(w) = k} K_{w(Λ + ρ) - ρ}`. -/
theorem finrank_homologyWeightSpace_eq_one_of_weights
    (hW : ∀ (k : ℕ) (μ : Dual K H),
      (nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace k μ ≠ ⊥ →
        ∃ w : P.weylGroup hA, (P.coxeterSystem hA).length w = k ∧
          (w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho = μ)
    (w : P.weylGroup hA) :
    finrank K ((nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace
      ((P.coxeterSystem hA).length w) ((w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho)) = 1 := by
  have hreg : ∀ i, ∃ n : ℕ, (Λ + P.rho) (P.coroot i) = n + 1 := fun i ↦ by
    obtain ⟨n, hn⟩ := hΛ i
    exact ⟨n, by rw [LinearMap.add_apply, hn, rho_coroot]⟩
  -- only the degree `ℓ(w)` contributes to the weight `w(Λ + ρ) - ρ`
  have hzero : ∀ k ≠ (P.coxeterSystem hA).length w,
      finrank K ((nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace k
        ((w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho)) = 0 := by
    intro k hk
    by_contra h0
    obtain ⟨w', hw'k, hw'⟩ := hW k _ fun hbot ↦ h0 (by rw [hbot, finrank_bot])
    have : w' = w := P.apply_injective_of_regular hA hreg (sub_left_injective hw')
    exact hk (by rw [← hw'k, this])
  have hsum := sum_neg_one_pow_finrank_homology_apply hA hS hΛ w
    (N := max ((isCategoryO P Λ).maxDeg ((w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho))
      ((P.coxeterSystem hA).length w)) (le_max_left _ _)
  rw [Finset.sum_eq_single ((P.coxeterSystem hA).length w)
    (fun k _ hk ↦ by rw [hzero k hk, Nat.cast_zero, mul_zero])
    (fun h ↦ absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_right _ _))) h)] at hsum
  have hne : ((-1 : ℤ) ^ (P.coxeterSystem hA).length w) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  exact_mod_cast (mul_right_inj' hne).mp (hsum.trans (mul_one _).symm)

end IrreducibleModule

end Matrix.Realization.KacMoodyAlgebra
