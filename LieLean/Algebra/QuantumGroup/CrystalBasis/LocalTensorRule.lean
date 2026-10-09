/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.LocalStrings
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorPiece

/-!
# The tensor product rule for lattices that are only locally `ẽᵢ`-stable

Let `M₁`, `M₂` be integrable `U`-modules with `A`-submodules `L₁`, `L₂` stable under `f̃ᵢ`, and let
`x ∈ L₁ ∩ M₁^{μ₁}`, `y ∈ L₂ ∩ M₂^{μ₂}`. Suppose `L₁` is stable under `ẽᵢ` on the weight spaces
`M₁^{μ₁ + j αᵢ}` (`j ≥ 0`), and similarly for `L₂`. Then:

* `ẽᵢ (x ⊗ y)`, `f̃ᵢ (x ⊗ y) ∈ L₁ ⊗ L₂` (`QuantumGroup.TensorModule.kashiwaraF_tmul_mem`,
  `QuantumGroup.TensorModule.kashiwaraE_tmul_mem`; cf. [HK] Lemma 5.3.2 (1));
* if `x ≡ Fᵢ^{(k₁)} u` and `y ≡ Fᵢ^{(k₂)} u'` modulo `ϖ L₁`, `ϖ L₂`, with `u`, `u'` killed by `Eᵢ`,
  then `f̃ᵢ (x ⊗ y)` and `ẽᵢ (x ⊗ y)` are given modulo `ϖ (L₁ ⊗ L₂)` by the tensor product rule
  (`QuantumGroup.TensorModule.kashiwaraF_tmul_sub_mem`,
  `QuantumGroup.TensorModule.kashiwaraE_tmul_sub_mem`; cf. [HK] Lemma 5.3.2 (2)).

The point is that only the weights above `μ₁`, `μ₂` enter, which is what the grand-loop argument
needs.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
-/

open TensorProduct Finset Pointwise

namespace LieLean.QuantumGroup

namespace TensorModule

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁]
  [AddCommGroup M₂] [Module k M₂] [Module (QuantumGroup R v) M₂]
  [IsScalarTower k (QuantumGroup R v) M₂]
  (h₁ : IsIntegrable R v M₁) (h₂ : IsIntegrable R v M₂) (i : I)
  {A : Type*} [CommRing A] [Algebra A k] [Module A M₁] [IsScalarTower A k M₁]
  [Module A M₂] [IsScalarTower A k M₂] {L₁ : Submodule A M₁} {L₂ : Submodule A M₂}

omit [DecidableEq I] in
lemma stable_iSup {ι : Type*} {Mt : Type*} [AddCommGroup Mt] [Module k Mt] [Module A Mt]
    [IsScalarTower A k Mt] (T : Module.End k Mt) (P : ι → Submodule A Mt)
    (hP : ∀ j, ∀ z ∈ P j, T z ∈ P j) {z : Mt} (hz : z ∈ ⨆ j, P j) : T z ∈ ⨆ j, P j := by
  induction hz using Submodule.iSup_induction' with
  | mem j z hz => exact Submodule.mem_iSup_of_mem j (hP j z hz)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb

include hv in
/-- A nonzero `Eᵢ`-primitive vector has nonnegative `⟨i, ·⟩`-weight. -/
lemma nonneg_of_primitive {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
    [IsScalarTower k (QuantumGroup R v) M] (hM : IsIntegrable R v M) {p : ℤ} {η : M}
    (hp : η ∈ nodeWt R v M i p) (hE : E R v i • η = 0) (h0 : η ≠ 0) : 0 ≤ p := by
  by_contra h
  exact h0 (IntegrableSl2.eq_zero_of_primitive_of_neg (V := nodeSl2 R v M hv hM i)
    (pow_d_ne_zero i) (pow_d_ne_one hv i) hp hE (by omega))

/-- The string pieces through `x ⊗ y`, given string decompositions of `x` and `y` by weights with
components in `L₁`, `L₂`: a submodule of `L₁ ⊗ L₂` containing `x ⊗ y` and stable under `ẽᵢ` and
`f̃ᵢ`. -/
theorem exists_stable_tmul_of_strings (hf₁ : ∀ y ∈ L₁, kashiwaraF R v M₁ hv h₁ i y ∈ L₁)
    (hf₂ : ∀ y ∈ L₂, kashiwaraF R v M₂ hv h₂ i y ∈ L₂) {μ₁ μ₂ : Y →+ ℤ}
    [IsLocalRing A] {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖv : algebraMap A k ϖ = v⁻¹) {N₁ N₂ : ℕ} {η : ℕ → M₁} {ζ : ℕ → M₂}
    (hηw : ∀ j : ℕ, η j ∈ weightSpace R v M₁ (μ₁ + j • R.root i)) (hηE : ∀ j, E R v i • η j = 0)
    (hη2 : ∀ j : ℕ, η j ≠ 0 → 0 ≤ μ₁ (R.coroot i) + j)
    (hζw : ∀ j : ℕ, ζ j ∈ weightSpace R v M₂ (μ₂ + j • R.root i)) (hζE : ∀ j, E R v i • ζ j = 0)
    (hζ2 : ∀ j : ℕ, ζ j ≠ 0 → 0 ≤ μ₂ (R.coroot i) + j)
    (hηL : ∀ j < N₁, η j ∈ L₁) (hζL : ∀ j < N₂, ζ j ∈ L₂) :
    ∃ N : Submodule A (TensorModule k M₁ M₂),
      mk M₁ M₂ ((∑ j ∈ range N₁, (nodeSl2 R v M₁ hv h₁ i).dF j (η j)) ⊗ₜ[k]
        (∑ j ∈ range N₂, (nodeSl2 R v M₂ hv h₂ i).dF j (ζ j))) ∈ N ∧
      N ≤ lattice k A L₁ L₂ ∧
      (∀ z ∈ N, kashiwaraF R v _ hv (isIntegrable h₁ h₂) i z ∈ N) ∧
      (∀ z ∈ N, kashiwaraE R v _ hv (isIntegrable h₁ h₂) i z ∈ N) := by
  classical
  set a : ℕ → ℕ := fun s ↦ (μ₁ (R.coroot i) + 2 * s).toNat
  set b : ℕ → ℕ := fun t ↦ (μ₂ (R.coroot i) + 2 * t).toNat
  have hηp : ∀ s, η s ∈ (nodeSl2 R v M₁ hv h₁ i).prim (a s) := fun s ↦ by
    by_cases h0 : η s = 0
    · rw [h0]; exact zero_mem _
    · have := hη2 s h0
      refine ⟨?_, hηE s⟩
      have hw := mem_nodeWt_of_mem_add_nsmul i (hηw s)
      rwa [show ((a s : ℕ) : ℤ) = μ₁ (R.coroot i) + 2 * s by simp only [a]; omega]
  have hζp : ∀ t, ζ t ∈ (nodeSl2 R v M₂ hv h₂ i).prim (b t) := fun t ↦ by
    by_cases h0 : ζ t = 0
    · rw [h0]; exact zero_mem _
    · have := hζ2 t h0
      refine ⟨?_, hζE t⟩
      have hw := mem_nodeWt_of_mem_add_nsmul i (hζw t)
      rwa [show ((b t : ℕ) : ℤ) = μ₂ (R.coroot i) + 2 * t by simp only [b]; omega]
  let P : Fin N₁ × Fin N₂ → Submodule A (TensorModule k M₁ M₂) := fun st ↦
    pieceLattice hv h₁ h₂ i A (a st.1) (b st.2) (η st.1) (ζ st.2)
  refine ⟨⨆ st, P st, ?_, iSup_le fun st ↦ ?_, fun z hz ↦ stable_iSup _ P (fun st z hz ↦ ?_) hz,
    fun z hz ↦ stable_iSup _ P (fun st z hz ↦ ?_) hz⟩
  · rw [sum_tmul, map_sum]
    refine Submodule.sum_mem _ fun s hs ↦ ?_
    rw [tmul_sum, map_sum]
    refine Submodule.sum_mem _ fun t ht ↦ ?_
    exact Submodule.mem_iSup_of_mem (⟨s, mem_range.1 hs⟩, ⟨t, mem_range.1 ht⟩)
      (tmul_mem_pieceLattice hv h₁ h₂ i (hηp s) (hζp t) s t)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨s', t'⟩, rfl⟩
    refine tmul_mem_lattice ?_ ?_
    · rw [← kashiwaraF_pow_of_primitive hv h₁ i (hηE st.1) (hηp st.1).1]
      exact kashiwaraF_pow_mem hv h₁ i hf₁ _ (hηL _ st.1.2)
    · rw [← kashiwaraF_pow_of_primitive hv h₂ i (hζE st.2) (hζp st.2).1]
      exact kashiwaraF_pow_mem hv h₂ i hf₂ _ (hζL _ st.2.2)
  · by_cases h0 : η st.1 = 0 ∨ ζ st.2 = 0
    · have hP : P st = ⊥ := by
        refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
        rintro _ ⟨⟨s', t'⟩, rfl⟩
        rcases h0 with h0 | h0 <;> simp [h0]
      rw [hP, Submodule.mem_bot] at hz ⊢
      rw [hz, map_zero]
    · push Not at h0
      exact kashiwaraF_mem_pieceLattice hv h₁ h₂ i hϖ hϖv (hηp st.1) (hζp st.2) h0.1 h0.2 hz
  · by_cases h0 : η st.1 = 0 ∨ ζ st.2 = 0
    · have hP : P st = ⊥ := by
        refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
        rintro _ ⟨⟨s', t'⟩, rfl⟩
        rcases h0 with h0 | h0 <;> simp [h0]
      rw [hP, Submodule.mem_bot] at hz ⊢
      rw [hz, map_zero]
    · push Not at h0
      exact kashiwaraE_mem_pieceLattice hv h₁ h₂ i hϖ hϖv (hηp st.1) (hζp st.2) h0.1 h0.2 hz

/-- The string pieces through `x ⊗ y`: a submodule of `L₁ ⊗ L₂` containing `x ⊗ y` and stable
under `ẽᵢ` and `f̃ᵢ`. -/
theorem exists_stable_tmul (hf₁ : ∀ y ∈ L₁, kashiwaraF R v M₁ hv h₁ i y ∈ L₁)
    (hf₂ : ∀ y ∈ L₂, kashiwaraF R v M₂ hv h₂ i y ∈ L₂) {μ₁ μ₂ : Y →+ ℤ}
    (he₁ : ∀ j : ℕ, ∀ y ∈ L₁, y ∈ weightSpace R v M₁ (μ₁ + j • R.root i) →
      kashiwaraE R v M₁ hv h₁ i y ∈ L₁)
    (he₂ : ∀ j : ℕ, ∀ y ∈ L₂, y ∈ weightSpace R v M₂ (μ₂ + j • R.root i) →
      kashiwaraE R v M₂ hv h₂ i y ∈ L₂)
    [IsLocalRing A] {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖv : algebraMap A k ϖ = v⁻¹)
    {x : M₁} {y : M₂} (hx : x ∈ L₁) (hxw : x ∈ weightSpace R v M₁ μ₁) (hy : y ∈ L₂)
    (hyw : y ∈ weightSpace R v M₂ μ₂) :
    ∃ N : Submodule A (TensorModule k M₁ M₂), mk M₁ M₂ (x ⊗ₜ[k] y) ∈ N ∧
      N ≤ lattice k A L₁ L₂ ∧
      (∀ z ∈ N, kashiwaraF R v _ hv (isIntegrable h₁ h₂) i z ∈ N) ∧
      (∀ z ∈ N, kashiwaraE R v _ hv (isIntegrable h₁ h₂) i z ∈ N) := by
  obtain ⟨N₁, η, hηw, hηE, hη2, -, rfl⟩ := exists_sum_dF_weight hv h₁ i hxw
  obtain ⟨N₂, ζ, hζw, hζE, hζ2, -, rfl⟩ := exists_sum_dF_weight hv h₂ i hyw
  exact exists_stable_tmul_of_strings hv h₁ h₂ i hf₁ hf₂ hϖ hϖv hηw hηE hη2 hζw hζE hζ2
    (mem_of_sum_mem_weight hv h₁ i hf₁ N₁ μ₁ η hηw hηE hη2 he₁ hx)
    (mem_of_sum_mem_weight hv h₂ i hf₂ N₂ μ₂ ζ hζw hζE hζ2 he₂ hy)

section Rule

variable (hf₁ : ∀ y ∈ L₁, kashiwaraF R v M₁ hv h₁ i y ∈ L₁)
  (hf₂ : ∀ y ∈ L₂, kashiwaraF R v M₂ hv h₂ i y ∈ L₂) {μ₁ μ₂ : Y →+ ℤ}
  (he₁ : ∀ j : ℕ, ∀ y ∈ L₁, y ∈ weightSpace R v M₁ (μ₁ + j • R.root i) →
    kashiwaraE R v M₁ hv h₁ i y ∈ L₁)
  (he₂ : ∀ j : ℕ, ∀ y ∈ L₂, y ∈ weightSpace R v M₂ (μ₂ + j • R.root i) →
    kashiwaraE R v M₂ hv h₂ i y ∈ L₂)
  [IsLocalRing A] {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖv : algebraMap A k ϖ = v⁻¹)
include hf₁ hf₂ he₁ he₂ hϖ hϖv

/-- `f̃ᵢ (x ⊗ y) ∈ L₁ ⊗ L₂` (cf. [HK] Lemma 5.3.2 (1)). -/
theorem kashiwaraF_tmul_mem {x : M₁} {y : M₂} (hx : x ∈ L₁) (hxw : x ∈ weightSpace R v M₁ μ₁)
    (hy : y ∈ L₂) (hyw : y ∈ weightSpace R v M₂ μ₂) :
    kashiwaraF R v _ hv (isIntegrable h₁ h₂) i (mk M₁ M₂ (x ⊗ₜ[k] y)) ∈ lattice k A L₁ L₂ := by
  obtain ⟨N, hN, hle, hf, -⟩ := exists_stable_tmul hv h₁ h₂ i hf₁ hf₂ he₁ he₂ hϖ hϖv hx hxw hy hyw
  exact hle (hf _ hN)

/-- `ẽᵢ (x ⊗ y) ∈ L₁ ⊗ L₂` (cf. [HK] Lemma 5.3.2 (1)). -/
theorem kashiwaraE_tmul_mem {x : M₁} {y : M₂} (hx : x ∈ L₁) (hxw : x ∈ weightSpace R v M₁ μ₁)
    (hy : y ∈ L₂) (hyw : y ∈ weightSpace R v M₂ μ₂) :
    kashiwaraE R v _ hv (isIntegrable h₁ h₂) i (mk M₁ M₂ (x ⊗ₜ[k] y)) ∈ lattice k A L₁ L₂ := by
  obtain ⟨N, hN, hle, -, he⟩ := exists_stable_tmul hv h₁ h₂ i hf₁ hf₂ he₁ he₂ hϖ hϖv hx hxw hy hyw
  exact hle (he _ hN)

end Rule

omit [DecidableEq I] [NeZero v] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁] in
/-- An element of `ϖ L ∩ M^μ` is `ϖ z` with `z ∈ L ∩ M^μ`. -/
lemma exists_smul_weight {ϖ : A} (hϖv : algebraMap A k ϖ ≠ 0) {S : Submodule k M₁}
    {z : M₁} (hz : z ∈ ϖ • L₁) (hzS : z ∈ S) : ∃ z₀ ∈ L₁, z₀ ∈ S ∧ z = ϖ • z₀ := by
  obtain ⟨z₀, hz₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
  refine ⟨z₀, hz₀, ?_, rfl⟩
  rw [← algebraMap_smul k] at hzS
  have := S.smul_mem (algebraMap A k ϖ)⁻¹ hzS
  rwa [smul_smul, inv_mul_cancel₀ hϖv, one_smul] at this

omit [IsScalarTower A k M₂] in
lemma pieceLattice_le_lattice (hf₁ : ∀ y ∈ L₁, kashiwaraF R v M₁ hv h₁ i y ∈ L₁)
    (hf₂ : ∀ y ∈ L₂, kashiwaraF R v M₂ hv h₂ i y ∈ L₂) {a b : ℕ} {u : M₁} {u' : M₂}
    (hu : u ∈ L₁) (hup : u ∈ (nodeSl2 R v M₁ hv h₁ i).prim a) (hu' : u' ∈ L₂)
    (hu'p : u' ∈ (nodeSl2 R v M₂ hv h₂ i).prim b) :
    pieceLattice hv h₁ h₂ i A a b u u' ≤ lattice k A L₁ L₂ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨s, t⟩, rfl⟩
  refine tmul_mem_lattice ?_ ?_
  · rw [← kashiwaraF_pow_of_primitive hv h₁ i hup.2 hup.1]
    exact kashiwaraF_pow_mem hv h₁ i hf₁ _ hu
  · rw [← kashiwaraF_pow_of_primitive hv h₂ i hu'p.2 hu'p.1]
    exact kashiwaraF_pow_mem hv h₂ i hf₂ _ hu'

omit [DecidableEq I] [NeZero v] in
lemma smul_le_smul_of_le {N : Type*} [AddCommGroup N] [Module A N] {P Q : Submodule A N}
    (h : P ≤ Q) (c : A) : c • P ≤ c • Q := by
  intro z hz
  obtain ⟨z₀, hz₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
  exact Submodule.smul_mem_pointwise_smul _ _ _ (h hz₀)

section StringRule

variable (hf₁ : ∀ y ∈ L₁, kashiwaraF R v M₁ hv h₁ i y ∈ L₁)
  (hf₂ : ∀ y ∈ L₂, kashiwaraF R v M₂ hv h₂ i y ∈ L₂) {μ₁ μ₂ : Y →+ ℤ}
  (he₁ : ∀ j : ℕ, ∀ y ∈ L₁, y ∈ weightSpace R v M₁ (μ₁ + j • R.root i) →
    kashiwaraE R v M₁ hv h₁ i y ∈ L₁)
  (he₂ : ∀ j : ℕ, ∀ y ∈ L₂, y ∈ weightSpace R v M₂ (μ₂ + j • R.root i) →
    kashiwaraE R v M₂ hv h₂ i y ∈ L₂)
  [IsLocalRing A] {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖv : algebraMap A k ϖ = v⁻¹)
  {x : M₁} {y : M₂} (hxw : x ∈ weightSpace R v M₁ μ₁) (hy : y ∈ L₂)
  (hyw : y ∈ weightSpace R v M₂ μ₂)
  {k₁ k₂ a b : ℕ} {u : M₁} {u' : M₂} (hu : u ∈ L₁)
  (huw : u ∈ weightSpace R v M₁ (μ₁ + k₁ • R.root i)) (huE : E R v i • u = 0)
  (hua : (a : ℤ) = μ₁ (R.coroot i) + 2 * k₁) (hu0 : u ≠ 0) (hk₁ : k₁ ≤ a)
  (hu' : u' ∈ L₂) (hu'w : u' ∈ weightSpace R v M₂ (μ₂ + k₂ • R.root i)) (hu'E : E R v i • u' = 0)
  (hu'b : (b : ℤ) = μ₂ (R.coroot i) + 2 * k₂) (hu'0 : u' ≠ 0) (hk₂ : k₂ ≤ b)
  (hxu : x - (nodeSl2 R v M₁ hv h₁ i).dF k₁ u ∈ ϖ • L₁)
  (hyu : y - (nodeSl2 R v M₂ hv h₂ i).dF k₂ u' ∈ ϖ • L₂)
include hf₁ hf₂ he₁ he₂ hϖ hϖv hxw hy hyw hu huw huE hua hu0 hk₁ hu' hu'w hu'E hu'b hu'0 hk₂
  hxu hyu

omit hf₁ hf₂ he₁ he₂ [IsLocalRing A] hϖ hy hu huE hua hu0 hk₁ hu' hu'E hu'b hu'0 hk₂ in
/-- The reduction of `x ⊗ y` to the string vectors: `x ⊗ y - Fᵢ^{(k₁)} u ⊗ Fᵢ^{(k₂)} u'` is
`ϖ (x₀ ⊗ y + Fᵢ^{(k₁)} u ⊗ y₀)` with `x₀`, `y₀` weight vectors of `L₁`, `L₂`. -/
lemma exists_tmul_decomp : ∃ x₀ ∈ L₁, x₀ ∈ weightSpace R v M₁ μ₁ ∧ ∃ y₀ ∈ L₂,
    y₀ ∈ weightSpace R v M₂ μ₂ ∧ mk M₁ M₂ (x ⊗ₜ[k] y) =
      mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF k₁ u ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF k₂ u') +
        ϖ • mk M₁ M₂ (x₀ ⊗ₜ[k] y) +
        ϖ • mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF k₁ u ⊗ₜ[k] y₀) := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨x₀, hx₀, hx₀w, hxe⟩ := exists_smul_weight hϖ0 hxu
    (sub_mem hxw (dF_mem_weightSpace hv h₁ i huw))
  obtain ⟨y₀, hy₀, hy₀w, hye⟩ := exists_smul_weight hϖ0 hyu
    (sub_mem hyw (dF_mem_weightSpace hv h₂ i hu'w))
  refine ⟨x₀, hx₀, hx₀w, y₀, hy₀, hy₀w, ?_⟩
  rw [sub_eq_iff_eq_add'] at hxe hye
  have hmk : ∀ (c : A) (z : M₁ ⊗[k] M₂), mk M₁ M₂ (c • z) = c • mk M₁ M₂ z := fun _ _ ↦ rfl
  have h2 : mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF k₁ u ⊗ₜ[k] y) =
      mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF k₁ u ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF k₂ u') +
        ϖ • mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF k₁ u ⊗ₜ[k] y₀) := by
    rw [hye, tmul_add, tmul_smul, map_add, hmk]
  have h1 : mk M₁ M₂ (x ⊗ₜ[k] y) = mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF k₁ u ⊗ₜ[k] y) +
      ϖ • mk M₁ M₂ (x₀ ⊗ₜ[k] y) := by
    rw [← hmk, smul_tmul', ← map_add, ← add_tmul, ← hxe]
  rw [h1, h2]
  abel

/-- **Tensor product rule for `f̃ᵢ`** with only local `ẽᵢ`-stability (cf. [HK] Lemma 5.3.2 (2)):
if `x ≡ Fᵢ^{(k₁)} u` and `y ≡ Fᵢ^{(k₂)} u'`, then modulo `ϖ (L₁ ⊗ L₂)`, `f̃ᵢ (x ⊗ y)` is
`Fᵢ^{(k₁)} u ⊗ Fᵢ^{(k₂+1)} u'` if `k₁ < b - k₂` and `Fᵢ^{(k₁+1)} u ⊗ Fᵢ^{(k₂)} u'` otherwise. -/
theorem kashiwaraF_tmul_sub_mem :
    kashiwaraF R v _ hv (isIntegrable h₁ h₂) i (mk M₁ M₂ (x ⊗ₜ[k] y)) -
      (if k₁ < b - k₂ then
        mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF k₁ u ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF (k₂ + 1) u')
      else
        mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF (k₁ + 1) u ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF k₂ u'))
      ∈ ϖ • lattice k A L₁ L₂ := by
  obtain ⟨x₀, hx₀, hx₀w, y₀, hy₀, hy₀w, he⟩ := exists_tmul_decomp hv h₁ h₂ i hϖv hxw hyw huw
    hu'w hxu hyu
  have hup : u ∈ (nodeSl2 R v M₁ hv h₁ i).prim a :=
    ⟨by rw [hua]; exact mem_nodeWt_of_mem_add_nsmul i huw, huE⟩
  have hu'p : u' ∈ (nodeSl2 R v M₂ hv h₂ i).prim b :=
    ⟨by rw [hu'b]; exact mem_nodeWt_of_mem_add_nsmul i hu'w, hu'E⟩
  have hFu : (nodeSl2 R v M₁ hv h₁ i).dF k₁ u ∈ L₁ := by
    rw [← kashiwaraF_pow_of_primitive hv h₁ i huE hup.1]
    exact kashiwaraF_pow_mem hv h₁ i hf₁ _ hu
  have hmain := kashiwaraF_piece_sub hv h₁ h₂ i hϖ hϖv hup hu'p hu0 hu'0 hk₁ hk₂
  have hle := smul_le_smul_of_le (pieceLattice_le_lattice hv h₁ h₂ i hf₁ hf₂ hu hup hu' hu'p) ϖ
  rw [he, map_add, map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
    add_sub_right_comm, add_sub_right_comm]
  refine add_mem (add_mem (hle hmain) ?_) ?_
  · exact Submodule.smul_mem_pointwise_smul _ _ _
      (kashiwaraF_tmul_mem hv h₁ h₂ i hf₁ hf₂ he₁ he₂ hϖ hϖv hx₀ hx₀w hy hyw)
  · exact Submodule.smul_mem_pointwise_smul _ _ _
      (kashiwaraF_tmul_mem hv h₁ h₂ i hf₁ hf₂ he₁ he₂ hϖ hϖv hFu
        (dF_mem_weightSpace hv h₁ i huw) hy₀ hy₀w)

/-- **Tensor product rule for `ẽᵢ`** with only local `ẽᵢ`-stability (cf. [HK] Lemma 5.3.2 (2)):
if `x ≡ Fᵢ^{(k₁)} u` and `y ≡ Fᵢ^{(k₂)} u'`, then modulo `ϖ (L₁ ⊗ L₂)`, `ẽᵢ (x ⊗ y)` is
`Fᵢ^{(k₁)} u ⊗ Fᵢ^{(k₂-1)} u'` (`0` if `k₂ = 0`) if `k₁ ≤ b - k₂` and
`Fᵢ^{(k₁-1)} u ⊗ Fᵢ^{(k₂)} u'` otherwise. -/
theorem kashiwaraE_tmul_sub_mem :
    kashiwaraE R v _ hv (isIntegrable h₁ h₂) i (mk M₁ M₂ (x ⊗ₜ[k] y)) -
      (if k₁ ≤ b - k₂ then
        (if k₂ = 0 then 0 else
          mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF k₁ u ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF (k₂ - 1) u'))
      else
        mk M₁ M₂ ((nodeSl2 R v M₁ hv h₁ i).dF (k₁ - 1) u ⊗ₜ[k] (nodeSl2 R v M₂ hv h₂ i).dF k₂ u'))
      ∈ ϖ • lattice k A L₁ L₂ := by
  obtain ⟨x₀, hx₀, hx₀w, y₀, hy₀, hy₀w, he⟩ := exists_tmul_decomp hv h₁ h₂ i hϖv hxw hyw huw
    hu'w hxu hyu
  have hup : u ∈ (nodeSl2 R v M₁ hv h₁ i).prim a :=
    ⟨by rw [hua]; exact mem_nodeWt_of_mem_add_nsmul i huw, huE⟩
  have hu'p : u' ∈ (nodeSl2 R v M₂ hv h₂ i).prim b :=
    ⟨by rw [hu'b]; exact mem_nodeWt_of_mem_add_nsmul i hu'w, hu'E⟩
  have hFu : (nodeSl2 R v M₁ hv h₁ i).dF k₁ u ∈ L₁ := by
    rw [← kashiwaraF_pow_of_primitive hv h₁ i huE hup.1]
    exact kashiwaraF_pow_mem hv h₁ i hf₁ _ hu
  have hmain := kashiwaraE_piece_sub hv h₁ h₂ i hϖ hϖv hup hu'p hu0 hu'0 hk₁ hk₂
  have hle := smul_le_smul_of_le (pieceLattice_le_lattice hv h₁ h₂ i hf₁ hf₂ hu hup hu' hu'p) ϖ
  rw [he, map_add, map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
    add_sub_right_comm, add_sub_right_comm]
  refine add_mem (add_mem (hle hmain) ?_) ?_
  · exact Submodule.smul_mem_pointwise_smul _ _ _
      (kashiwaraE_tmul_mem hv h₁ h₂ i hf₁ hf₂ he₁ he₂ hϖ hϖv hx₀ hx₀w hy hyw)
  · exact Submodule.smul_mem_pointwise_smul _ _ _
      (kashiwaraE_tmul_mem hv h₁ h₂ i hf₁ hf₂ he₁ he₂ hϖ hϖv hFu
        (dF_mem_weightSpace hv h₁ i huw) hy₀ hy₀w)

end StringRule

end TensorModule

end LieLean.QuantumGroup
