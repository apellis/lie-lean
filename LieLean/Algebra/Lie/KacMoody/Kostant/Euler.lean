/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.Euler
import LieLean.Algebra.Lie.KacMoody.Kostant.Chains
import LieLean.Algebra.Lie.KacMoody.Casimir
import LieLean.Algebra.Lie.KacMoody.WeightBasis

/-!
# The Euler characteristic of `𝔫₋`-homology

Let `𝔤 = 𝔤(A)` be a Kac–Moody algebra over a field `K` of characteristic zero and `V` a
`𝔤`-module in the category `𝒪`. The weight spaces `C_k(𝔫₋, V)_μ` of the Chevalley–Eilenberg
complex `C_k(𝔫₋, V) = ⋀ᵏ𝔫₋ ⊗ V` are finite-dimensional, and for fixed `μ` only finitely many
degrees `k` contribute. Using the basis `x_S ⊗ v` of `⋀𝔫₋ ⊗ V` formed from a basis of root vectors
of `𝔫₋` (`nNegBasis`) and a basis of weight vectors of `V`, the Euler characteristic of the
weight-`μ` chains is `∑_S (-1)^{|S|} dim V_{μ + wt S}`, which is the coefficient of `e^μ` in
`R · ch V`, where `R = ∏_{α > 0} (1 - e^{-α})^{mult α} = ∑_S (-1)^{|S|} e^{-wt S}` is the
denominator (`Matrix.Realization.KacMoodyAlgebra.denominator`). With the Euler–Poincaré principle
we obtain ([GL] Lemma 9.2; cf. [Kum] proof of Cor. 3.2.8, for `V = L(Λ)`), in the algebra `ℰ`
of formal characters,
`∑_k (-1)^k ch C_k(𝔫₋, V) = ∑_k (-1)^k ch H_k(𝔫₋, V) = R · ch V`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.weightBasis`: a basis of `V` consisting of
  weight vectors.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.chainCharacter`,
  `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.homologyCharacter`: the formal characters
  `ch C_k(𝔫₋, V)` and `ch H_k(𝔫₋, V)` in `ℰ`.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.chainEulerFamily`,
  `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.homologyEulerFamily`: the summable families
  `k ↦ (-1)^k ch C_k(𝔫₋, V)` and `k ↦ (-1)^k ch H_k(𝔫₋, V)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.finiteDimensional_nNegChains`: the weight
  spaces `C_k(𝔫₋, V)_μ` are finite-dimensional.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.hsum_chainEulerFamily`:
  `∑_k (-1)^k ch C_k(𝔫₋, V) = R · ch V`.
* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.hsum_homologyEulerFamily`:
  `∑_k (-1)^k ch H_k(𝔫₋, V) = R · ch V`.

## References

* [GL] H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent.
  Math. **34** (1976), 37–76.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, Ch. 3.
-/

open Module LieModule LieModule.ChevalleyEilenberg HahnSeries

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

open CharacterRing WeightOrd

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-! ### Weights of sets of negative root indices -/

omit [CharZero K] in
lemma finsetWt_mem_posWeights {S : Finset (NegRootIndex P)} (hS : S.Nonempty) :
    finsetWt P S ∈ P.posWeights := by
  classical
  induction S using Finset.induction_on with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | insert x S hx ih =>
    rw [finsetWt, Finset.sum_insert hx]
    rcases S.eq_empty_or_nonempty with rfl | hS'
    · rw [Finset.sum_empty, add_zero]
      exact x.1.2
    · exact posWeights_add P x.1.2 (ih hS')

omit [CharZero K] in
lemma sum_neg_root (S : Finset (NegRootIndex P)) :
    ∑ x ∈ S, -x.root = -finsetWt P S := by
  rw [Finset.sum_neg_distrib, finsetWt]

/-- For `V` in `𝒪` and a weight `μ`, only finitely many sets `S` of indices have
`V_{μ + wt S} ≠ 0`. -/
theorem IsCategoryO.finite_setOf_weightSpace_add_finsetWt_ne_bot (hV : IsCategoryO P V)
    (μ : Dual K H) :
    {S : Finset (NegRootIndex P) | weightSpace P V (μ + finsetWt P S) ≠ ⊥}.Finite := by
  have hF := hV.finite_setOf_weightSpace_add_ne_bot μ
  refine ((Set.finite_singleton (∅ : Finset (NegRootIndex P))).union
    (hF.biUnion fun β _ ↦ finite_setOf_finsetWt_eq P β)).subset fun S hS ↦ ?_
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact Or.inl rfl
  · refine Or.inr (Set.mem_biUnion (x := finsetWt P S) ⟨finsetWt_mem_posWeights P hne, ?_⟩ rfl)
    rw [Set.mem_ofPred_eq, add_comm] at hS
    exact hS

variable {P}

/-! ### The weight-`μ` basis vectors of `⋀𝔫₋ ⊗ V` -/

variable (hV : IsCategoryO P V)

open Classical in
/-- The (finite) set of indices `(S, (ν, j))` of the basis vectors `x_S ⊗ v_{ν, j}` of weight
`μ` (`ν - wt S = μ`) of `⋀𝔫₋ ⊗ V`. -/
def IsCategoryO.chainIndexFinset (μ : Dual K H) :
    Finset (Finset (NegRootIndex P) × WeightBasisIndex P V) :=
  (hV.finite_setOf_weightSpace_add_finsetWt_ne_bot P μ).toFinset.biUnion fun S ↦
    Finset.univ.image fun j : Fin (finrank K (weightSpace P V (μ + finsetWt P S))) ↦
      (S, ⟨μ + finsetWt P S, j⟩)

open Classical in
lemma IsCategoryO.chainWt_eq_iff_mem (μ : Dual K H)
    (t : Finset (NegRootIndex P) × WeightBasisIndex P V) :
    DerivAction.chainWt (fun x : NegRootIndex P ↦ -x.root) (fun j : WeightBasisIndex P V ↦ j.1)
        t = μ ↔ t ∈ hV.chainIndexFinset μ := by
  obtain ⟨S, ν, j⟩ := t
  simp only [DerivAction.chainWt_apply, sum_neg_root, IsCategoryO.chainIndexFinset,
    Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq]
  constructor
  · intro hμ
    obtain rfl : ν = μ + finsetWt P S := by rw [← hμ]; abel
    refine ⟨S, fun hbot ↦ ?_, j, rfl⟩
    exact (Fin.pos j).ne' (by rw [hbot, finrank_bot])
  · rintro ⟨S', -, j', h⟩
    obtain ⟨rfl, h2⟩ := Prod.ext_iff.mp h
    rw [← (Sigma.mk.inj_iff.mp h2).1]
    abel

open Classical in
lemma IsCategoryO.sum_chainIndexFinset (μ : Dual K H) :
    ∑ t ∈ hV.chainIndexFinset μ, (-1 : ℤ) ^ t.1.card =
      ∑ S ∈ (hV.finite_setOf_weightSpace_add_finsetWt_ne_bot P μ).toFinset,
        (-1 : ℤ) ^ S.card * finrank K (weightSpace P V (μ + finsetWt P S)) := by
  rw [IsCategoryO.chainIndexFinset, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [Finset.sum_image fun j _ j' _ h ↦ by simpa using h]
    simp [mul_comm]
  · intro S _ S' _ hSS'
    refine Finset.disjoint_left.mpr fun t ht ht' ↦ hSS' ?_
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j', -, h⟩ := Finset.mem_image.mp ht'
    exact (Prod.ext_iff.mp h).1.symm

/-- The coefficient of `e^μ` in `R · ch V` is `∑_S (-1)^{|S|} dim V_{μ + wt S}`. -/
theorem IsCategoryO.coeffAt_denominator_mul_character (μ : Dual K H) :
    (denominator P * hV.character).coeffAt μ =
      ∑ S ∈ (hV.finite_setOf_weightSpace_add_finsetWt_ne_bot P μ).toFinset,
        (-1 : ℤ) ^ S.card * finrank K (weightSpace P V (μ + finsetWt P S)) := by
  have hterm : ∀ S : Finset (NegRootIndex P),
      ((hV.character • denominatorFamily P) S).coeff (toWeightOrd P μ) =
        (-1 : ℤ) ^ S.card * finrank K (weightSpace P V (μ + finsetWt P S)) := fun S ↦ by
    change (hV.character * HahnSeries.single _ _).coeff _ = _
    rw [HahnSeries.coeff_mul_single, mul_comm]
    change (-1 : ℤ) ^ S.card * hV.character.coeff (toWeightOrd P μ - toWeightOrd P (-finsetWt P S))
      = _
    rw [← map_sub, sub_neg_eq_add]
    rfl
  rw [mul_comm, denominator, ← SummableFamily.hsum_smul, CharacterRing.coeffAt,
    SummableFamily.coeff_hsum, finsum_eq_sum_of_support_subset _
      (s := (hV.finite_setOf_weightSpace_add_finsetWt_ne_bot P μ).toFinset)]
  · exact Finset.sum_congr rfl fun S _ ↦ hterm S
  · intro S hS
    rw [Function.mem_support, hterm] at hS
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    intro hbot
    rw [hbot, finrank_bot, Nat.cast_zero, mul_zero] at hS
    exact hS rfl

/-! ### Dimensions of the weight spaces of the chains and the Euler characteristic -/

variable (P) in
lemma nNegBasis_mem_weightSpaceOf (x : NegRootIndex P) :
    nNegBasis P x ∈ Module.End.weightSpaceOf (adNNeg P) (-x.root) :=
  fun a ↦ Subtype.ext (by simpa using nNegBasis_mem P x a)

omit [CharZero K] in
lemma IsCategoryO.weightBasis_mem_weightSpaceOf (j : WeightBasisIndex P V) :
    hV.weightBasis j ∈ Module.End.weightSpaceOf (nNegDerivAction P V).φ j.1 :=
  hV.weightBasis_mem j

include hV in
/-- The weight spaces `C_k(𝔫₋, V)_μ` of the chains are finite-dimensional, for `V` in `𝒪`. -/
theorem IsCategoryO.finiteDimensional_nNegChains (k : ℕ) (μ : Dual K H) :
    FiniteDimensional K
      ↥(chainsIn K (nNeg P) V k ⊓ (nNegDerivAction P V).chainWeightSpace μ) :=
  DerivAction.finiteDimensional_chainsIn_inf_chainWeightSpace (nNegBasis P) hV.weightBasis
    (nNegBasis_mem_weightSpaceOf P) hV.weightBasis_mem_weightSpaceOf (hV.chainWt_eq_iff_mem μ) k

/-- A bound for the degrees of the nonzero weight-`μ` chains. -/
def IsCategoryO.maxDeg (μ : Dual K H) : ℕ := (hV.chainIndexFinset μ).sup fun t ↦ t.1.card

lemma IsCategoryO.card_le_maxDeg {μ : Dual K H} {t : Finset (NegRootIndex P) × WeightBasisIndex P V}
    (ht : t ∈ hV.chainIndexFinset μ) : t.1.card ≤ hV.maxDeg μ :=
  Finset.le_sup (f := fun t : Finset (NegRootIndex P) × WeightBasisIndex P V ↦ t.1.card) ht

/-- `dim C_k(𝔫₋, V)_μ = #{(S, (ν, j)) | |S| = k, ν - wt S = μ}`. -/
theorem IsCategoryO.finrank_nNegChains (k : ℕ) (μ : Dual K H) :
    finrank K ↥(chainsIn K (nNeg P) V k ⊓ (nNegDerivAction P V).chainWeightSpace μ) =
      ((hV.chainIndexFinset μ).filter fun t ↦ t.1.card = k).card :=
  DerivAction.finrank_chainsIn_inf_chainWeightSpace (nNegBasis P) hV.weightBasis
    (nNegBasis_mem_weightSpaceOf P) hV.weightBasis_mem_weightSpaceOf (hV.chainWt_eq_iff_mem μ) k

/-- **Euler characteristic of the chains** (cf. [GL] §9): for `N` at least the maximal
degree of a nonzero weight-`μ` chain, `∑_{k ≤ N} (-1)^k dim C_k(𝔫₋, V)_μ` is the coefficient of
`e^μ` in `R · ch V`. -/
theorem IsCategoryO.sum_neg_one_pow_finrank_nNegChains (μ : Dual K H) {N : ℕ}
    (hN : hV.maxDeg μ ≤ N) :
    ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k *
        finrank K ↥(chainsIn K (nNeg P) V k ⊓ (nNegDerivAction P V).chainWeightSpace μ) =
      (denominator P * hV.character).coeffAt μ := by
  rw [hV.coeffAt_denominator_mul_character, ← hV.sum_chainIndexFinset]
  exact DerivAction.sum_neg_one_pow_finrank_chains (nNegBasis P) hV.weightBasis
    (nNegBasis_mem_weightSpaceOf P) hV.weightBasis_mem_weightSpaceOf (hV.chainWt_eq_iff_mem μ)
    fun t ht ↦ (hV.card_le_maxDeg ht).trans hN

/-- **Euler characteristic of the homology** ([GL] Lemma 9.2): for `N` at least the maximal
degree of a nonzero weight-`μ` chain, `∑_{k ≤ N} (-1)^k dim H_k(𝔫₋, V)_μ` is the coefficient of
`e^μ` in `R · ch V`. -/
theorem IsCategoryO.sum_neg_one_pow_finrank_nNegHomology (μ : Dual K H) {N : ℕ}
    (hN : hV.maxDeg μ ≤ N) :
    ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k *
        finrank K ((nNegDerivAction P V).homologyWeightSpace k μ) =
      (denominator P * hV.character).coeffAt μ := by
  rw [hV.coeffAt_denominator_mul_character, ← hV.sum_chainIndexFinset]
  exact DerivAction.sum_neg_one_pow_finrank_homology (nNegBasis P) hV.weightBasis
    (nNegBasis_mem_weightSpaceOf P) hV.weightBasis_mem_weightSpaceOf (hV.chainWt_eq_iff_mem μ)
    fun t ht ↦ (hV.card_le_maxDeg ht).trans hN

/-! ### Formal characters of the chains and of the homology -/

/-- The weights of the chains lie in a finite union of cones `Λ - Q₊`. -/
lemma IsCategoryO.exists_cone_of_nonempty : ∃ s : Finset (Dual K H), ∀ μ,
    (hV.chainIndexFinset μ).Nonempty → ∃ Λ ∈ s, ∃ k : ι → ℤ, 0 ≤ k ∧ μ = Λ - P.rootOf k := by
  classical
  obtain ⟨s, hs⟩ := hV.exists_finset
  refine ⟨s, fun μ ⟨t, ht⟩ ↦ ?_⟩
  simp only [IsCategoryO.chainIndexFinset, Finset.mem_biUnion, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq] at ht
  obtain ⟨S, hS, -⟩ := ht
  obtain ⟨Λ, hΛ, k, hk, hμ⟩ := hs _ hS
  obtain ⟨kS, hkS, hwt⟩ := exists_finsetWt_eq_rootOf P S
  refine ⟨Λ, hΛ, k + kS, add_nonneg hk hkS, ?_⟩
  rw [map_add, ← hwt, sub_add_eq_sub_sub, ← hμ]
  abel

lemma IsCategoryO.nonempty_of_finrank_nNegChains_ne_zero {k : ℕ} {μ : Dual K H}
    (h : finrank K ↥(chainsIn K (nNeg P) V k ⊓ (nNegDerivAction P V).chainWeightSpace μ) ≠ 0) :
    (hV.chainIndexFinset μ).Nonempty ∧ k ≤ hV.maxDeg μ := by
  rw [hV.finrank_nNegChains, Finset.card_ne_zero] at h
  obtain ⟨t, ht⟩ := h
  obtain ⟨ht1, rfl⟩ := Finset.mem_filter.mp ht
  exact ⟨⟨t, ht1⟩, hV.card_le_maxDeg ht1⟩

include hV in
lemma IsCategoryO.finrank_nNegHomology_le (k : ℕ) (μ : Dual K H) :
    finrank K ((nNegDerivAction P V).homologyWeightSpace k μ) ≤
      finrank K ↥(chainsIn K (nNeg P) V k ⊓ (nNegDerivAction P V).chainWeightSpace μ) := by
  have := hV.finiteDimensional_nNegChains k μ
  have hle : cycles K (nNeg P) V k ⊓ (nNegDerivAction P V).chainWeightSpace μ ≤
      chainsIn K (nNeg P) V k ⊓ (nNegDerivAction P V).chainWeightSpace μ :=
    inf_le_inf_right _ inf_le_left
  have := Submodule.finiteDimensional_of_le hle
  have h1 := (nNegDerivAction P V).finrank_homologyWeightSpace_add k μ
  have h2 := Submodule.finrank_mono hle
  omega

lemma IsCategoryO.nonempty_of_finrank_nNegHomology_ne_zero {k : ℕ} {μ : Dual K H}
    (h : finrank K ((nNegDerivAction P V).homologyWeightSpace k μ) ≠ 0) :
    (hV.chainIndexFinset μ).Nonempty ∧ k ≤ hV.maxDeg μ :=
  hV.nonempty_of_finrank_nNegChains_ne_zero fun h0 ↦
    h (Nat.eq_zero_of_le_zero (h0 ▸ hV.finrank_nNegHomology_le k μ))

/-- The coefficient functions of the characters of the chains, and of the homology, are supported
in a finite union of cones `Λ - Q₊`. -/
lemma IsCategoryO.exists_cone_of_support (f : Dual K H → ℤ)
    (hf : ∀ μ, f μ ≠ 0 → (hV.chainIndexFinset μ).Nonempty) :
    ∃ t : Finset (Dual K H), ∀ μ, f μ ≠ 0 → ∃ Λ ∈ t, ∃ k : ι → ℤ, 0 ≤ k ∧ μ = Λ - P.rootOf k := by
  obtain ⟨s, hs⟩ := hV.exists_cone_of_nonempty
  exact ⟨s, fun μ hμ ↦ hs μ (hf μ hμ)⟩

/-- The formal character `ch C_k(𝔫₋, V) = ∑_μ dim C_k(𝔫₋, V)_μ e^μ ∈ ℰ` of the chains. -/
def IsCategoryO.chainCharacter (k : ℕ) : P.CharacterRing ℤ :=
  ofFun P (fun μ ↦ (finrank K
      ↥(chainsIn K (nNeg P) V k ⊓ (nNegDerivAction P V).chainWeightSpace μ) : ℤ))
    (hV.exists_cone_of_support _ fun _ hμ ↦
      (hV.nonempty_of_finrank_nNegChains_ne_zero (by exact_mod_cast hμ)).1)

/-- The formal character `ch H_k(𝔫₋, V) = ∑_μ dim H_k(𝔫₋, V)_μ e^μ ∈ ℰ` of the homology. -/
def IsCategoryO.homologyCharacter (k : ℕ) : P.CharacterRing ℤ :=
  ofFun P (fun μ ↦ (finrank K ((nNegDerivAction P V).homologyWeightSpace k μ) : ℤ))
    (hV.exists_cone_of_support _ fun _ hμ ↦
      (hV.nonempty_of_finrank_nNegHomology_ne_zero (by exact_mod_cast hμ)).1)

@[simp] lemma IsCategoryO.coeffAt_chainCharacter (k : ℕ) (μ : Dual K H) :
    (hV.chainCharacter k).coeffAt μ =
      finrank K ↥(chainsIn K (nNeg P) V k ⊓ (nNegDerivAction P V).chainWeightSpace μ) := rfl

@[simp] lemma IsCategoryO.coeffAt_homologyCharacter (k : ℕ) (μ : Dual K H) :
    (hV.homologyCharacter k).coeffAt μ =
      finrank K ((nNegDerivAction P V).homologyWeightSpace k μ) := rfl

/-- A family `k ↦ (-1)^k ch_k` of formal characters whose weights are weights of the chains and
whose weight-`μ` coefficients vanish in degrees `k > maxDeg μ` is summable. -/
def IsCategoryO.eulerFamily (f : ℕ → Dual K H → ℕ)
    (hf : ∀ k μ, f k μ ≠ 0 → (hV.chainIndexFinset μ).Nonempty ∧ k ≤ hV.maxDeg μ) :
    SummableFamily P.WeightOrd ℤ ℕ where
  toFun k := ofFun P (fun μ ↦ (-1 : ℤ) ^ k * f k μ)
    (hV.exists_cone_of_support _ fun μ hμ ↦ (hf k μ fun h0 ↦ hμ (by
      rw [h0, Nat.cast_zero, mul_zero])).1)
  isPWO_iUnion_support' := by
    obtain ⟨s, hs⟩ := hV.exists_cone_of_nonempty
    refine (isPWO_iff P).mpr ⟨s, fun g hg ↦ hs _ ?_⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hg
    exact (hf k _ fun h0 ↦ hk (by
      change (-1 : ℤ) ^ k * (f k (ofWeightOrd P g) : ℤ) = 0
      rw [h0, Nat.cast_zero, mul_zero])).1
  finite_co_support' g := (Set.finite_Iic (hV.maxDeg (ofWeightOrd P g))).subset fun k hk ↦
    (hf k _ fun h0 ↦ hk (by
      change (-1 : ℤ) ^ k * (f k (ofWeightOrd P g) : ℤ) = 0
      rw [h0, Nat.cast_zero, mul_zero])).2

lemma IsCategoryO.coeff_hsum_eulerFamily (f : ℕ → Dual K H → ℕ)
    (hf : ∀ k μ, f k μ ≠ 0 → (hV.chainIndexFinset μ).Nonempty ∧ k ≤ hV.maxDeg μ)
    (μ : Dual K H) :
    CharacterRing.coeffAt (hV.eulerFamily f hf).hsum μ =
      ∑ k ∈ Finset.range (hV.maxDeg μ + 1), (-1 : ℤ) ^ k * f k μ := by
  rw [CharacterRing.coeffAt, SummableFamily.coeff_hsum,
    finsum_eq_sum_of_support_subset _ (s := Finset.range (hV.maxDeg μ + 1))]
  · rfl
  · intro k hk
    rw [Function.mem_support] at hk
    rw [Finset.coe_range, Set.mem_Iio, Nat.lt_succ_iff]
    exact (hf k μ fun h0 ↦ hk (by
      change (-1 : ℤ) ^ k * (f k (ofWeightOrd P (toWeightOrd P μ)) : ℤ) = 0
      rw [ofWeightOrd_toWeightOrd, h0, Nat.cast_zero, mul_zero])).2

/-- The summable family `k ↦ (-1)^k ch C_k(𝔫₋, V)` in `ℰ`. -/
def IsCategoryO.chainEulerFamily : SummableFamily P.WeightOrd ℤ ℕ :=
  hV.eulerFamily (fun k μ ↦ finrank K
      ↥(chainsIn K (nNeg P) V k ⊓ (nNegDerivAction P V).chainWeightSpace μ))
    fun _ _ h ↦ hV.nonempty_of_finrank_nNegChains_ne_zero h

/-- The summable family `k ↦ (-1)^k ch H_k(𝔫₋, V)` in `ℰ`. -/
def IsCategoryO.homologyEulerFamily : SummableFamily P.WeightOrd ℤ ℕ :=
  hV.eulerFamily (fun k μ ↦ finrank K ((nNegDerivAction P V).homologyWeightSpace k μ))
    fun _ _ h ↦ hV.nonempty_of_finrank_nNegHomology_ne_zero h

lemma IsCategoryO.chainEulerFamily_apply (k : ℕ) :
    hV.chainEulerFamily k = (-1 : ℤ) ^ k • hV.chainCharacter k := by
  ext μ
  change _ = ((-1 : ℤ) ^ k • hV.chainCharacter k).coeff _
  rw [HahnSeries.coeff_smul, smul_eq_mul]
  rfl

lemma IsCategoryO.homologyEulerFamily_apply (k : ℕ) :
    hV.homologyEulerFamily k = (-1 : ℤ) ^ k • hV.homologyCharacter k := by
  ext μ
  change _ = ((-1 : ℤ) ^ k • hV.homologyCharacter k).coeff _
  rw [HahnSeries.coeff_smul, smul_eq_mul]
  rfl

/-- **The Euler characteristic of the chains** (cf. [GL] §9): for `V` in the category `𝒪`,
`∑_k (-1)^k ch C_k(𝔫₋, V) = R · ch V` in `ℰ`, where `R = ∏_{α > 0} (1 - e^{-α})^{mult α}`. -/
theorem IsCategoryO.hsum_chainEulerFamily :
    hV.chainEulerFamily.hsum = denominator P * hV.character := by
  ext μ
  rw [← hV.sum_neg_one_pow_finrank_nNegChains μ le_rfl]
  exact hV.coeff_hsum_eulerFamily _ _ μ

/-- **The Euler characteristic of `𝔫₋`-homology** ([GL] Lemma 9.2; cf. [Kum] proof of
Cor. 3.2.8, for `V = L(Λ)`): for `V` in the category `𝒪`, `∑_k (-1)^k ch H_k(𝔫₋, V) = R · ch V` in
`ℰ`, where `R = ∏_{α > 0} (1 - e^{-α})^{mult α}` is the denominator. -/
theorem IsCategoryO.hsum_homologyEulerFamily :
    hV.homologyEulerFamily.hsum = denominator P * hV.character := by
  ext μ
  rw [← hV.sum_neg_one_pow_finrank_nNegHomology μ le_rfl]
  exact hV.coeff_hsum_eulerFamily _ _ μ

end Matrix.Realization.KacMoodyAlgebra
