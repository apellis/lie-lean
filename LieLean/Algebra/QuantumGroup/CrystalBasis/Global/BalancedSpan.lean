/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.BalancedTriple

/-!
# Balanced triples: spanning (Kashiwara, Lemma 7.1.1 (i))

Let `V` be a vector space over `𝕂 = ℚ(v)`, `L₀` a lattice over the local ring `A` at `v = ∞`
(uniformizer `v⁻¹`), `L₁` a lattice over the local ring `Ā` at `v = 0` (uniformizer `v`) and
`M` an `𝒜`-submodule of `V`, `𝒜 = ℤ[v, v⁻¹]`, whose elements lie in `v^N L₀` and in
`v^{-N} L₁` for some `N`. Kashiwara's Lemma 7.1.1 (i) ([Kas91], with `q`
corresponding to `v⁻¹`) says: if `M ∩ L₀ ∩ L₁ → (M ∩ L₀)/(M ∩ v⁻¹L₀)` is an isomorphism, then
`M ≅ 𝒜 ⊗_ℤ (M ∩ L₀ ∩ L₁)`.

We prove the spanning part in basis form (`span_of_balanced`): if vectors `g_b ∈ M ∩ L₀ ∩ L₁`
are such that

* every `x ∈ M ∩ L₀` is congruent modulo `v⁻¹L₀` to a `ℤ`-combination of the `g_b`
  (surjectivity), and
* `M ∩ v⁻¹L₀ ∩ L₁ = 0` (injectivity),

then `M` is the `𝒜`-span of the `g_b`. Together with `balanced_coeff_int` and
`balanced_coeff_zero` (Lemma 7.1.1 (ii)) this gives Lemma 7.1.1 (i) for residue-independent
families. The proof follows Kashiwara's: one shows `M ∩ L₀ ⊆ Σ_{k ≤ n} ℤ v^{-k} E + M ∩ v^{-n-1}L₀`
by induction ((7.1.1) of [Kas91]) and concludes with the injectivity, as in the proof of (7.1.2).

We also prove the remaining part of Lemma 7.1.1 (ii) in basis form
(`exists_int_sub_mem_of_mem_span`): if the `g_b ∈ L₀` have independent residues, every element of
`L₀` in their `𝒜`-span is congruent modulo `v⁻¹L₀` to a `ℤ`-combination of the `g_b`.

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, §7.1.
-/

open Pointwise

noncomputable section

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)

variable {V : Type*} [AddCommGroup V] [Module 𝕂 V]

section Scalars

lemma uniformizer_smul_eq [Module InfinityLocalRing V] [IsScalarTower InfinityLocalRing 𝕂 V]
    (x : V) : InfinityLocalRing.uniformizer • x = (𝕧⁻¹ : 𝕂) • x := by
  rw [← algebraMap_smul 𝕂, InfinityLocalRing.algebraMap_uniformizer]

lemma localX_smul_eq [Module LocalRing V] [IsScalarTower LocalRing 𝕂 V] (x : V) :
    localX • x = (𝕧 : 𝕂) • x := by
  rw [← algebraMap_smul 𝕂, algebraMap_localX, inv_inv]

lemma X_smul_mem₁ [Module LocalRing V] [IsScalarTower LocalRing 𝕂 V]
    {L₁ : Submodule LocalRing V} {x : V} (hx : x ∈ L₁) : (𝕧 : 𝕂) • x ∈ L₁ := by
  rw [← localX_smul_eq]; exact L₁.smul_mem _ hx

variable [Module (LaurentPolynomial ℤ) V]
  (hsmul : ∀ (c : LaurentPolynomial ℤ) (x : V), c • x = integralLaurentEval c • x)

include hsmul in
lemma zpow_smul_mem_laurent {M : Submodule (LaurentPolynomial ℤ) V} (z : ℤ) {x : V}
    (hx : x ∈ M) : (𝕧 ^ z : 𝕂) • x ∈ M := by
  have := M.smul_mem (LaurentPolynomial.T z) hx
  rwa [hsmul, integralLaurentEval_T] at this

end Scalars

section Main

variable [Module InfinityLocalRing V] [IsScalarTower InfinityLocalRing 𝕂 V]
  [Module LocalRing V] [IsScalarTower LocalRing 𝕂 V] [Module (LaurentPolynomial ℤ) V]
  {ι : Type*} {L₀ : Submodule InfinityLocalRing V} {L₁ : Submodule LocalRing V} {g : ι → V}
  {M : Submodule (LaurentPolynomial ℤ) V}
  (hsmul : ∀ (c : LaurentPolynomial ℤ) (x : V), c • x = integralLaurentEval c • x)

include hsmul in
/-- The induction behind (7.1.1) of [Kas91]: every `x ∈ M ∩ L₀` is `y + v^{-n} r` with `y` in the
`𝒜`-span of the `g_b`, `vⁿ y ∈ v L₁` and `r ∈ M ∩ L₀`. -/
lemma exists_balanced_approx (hg : ∀ i, g i ∈ M) (hg₁ : ∀ i, g i ∈ L₁)
    (hsurj : ∀ x ∈ M, x ∈ L₀ →
      ∃ y ∈ Submodule.span ℤ (Set.range g), x - y ∈ InfinityLocalRing.uniformizer • L₀)
    (n : ℕ) {x : V} (hxM : x ∈ M) (hx₀ : x ∈ L₀) :
    ∃ y r : V, y ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range g) ∧
      (∃ l ∈ L₁, (𝕧 ^ n : 𝕂) • y = (𝕧 : 𝕂) • l) ∧ r ∈ M ∧ r ∈ L₀ ∧
      x = y + (𝕧⁻¹ ^ n : 𝕂) • r := by
  induction n with
  | zero => exact ⟨0, x, zero_mem _, ⟨0, zero_mem _, by simp⟩, hxM, hx₀, by simp⟩
  | succ n ih =>
    obtain ⟨y, r, hy, ⟨l, hl, hyl⟩, hrM, hr₀, rfl⟩ := ih
    obtain ⟨e, he, hre⟩ := hsurj r hrM hr₀
    obtain ⟨r', hr', hrr'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hre
    rw [uniformizer_smul_eq] at hrr'
    have heZ : e ∈ (Submodule.span (LaurentPolynomial ℤ) (Set.range g)).restrictScalars ℤ :=
      Submodule.span_le_restrictScalars ℤ (LaurentPolynomial ℤ) _ he
    have heL : e ∈ L₁.restrictScalars ℤ :=
      (Submodule.span_le (p := L₁.restrictScalars ℤ)).2
        (by rintro _ ⟨i, rfl⟩; exact hg₁ i) he
    have heM : e ∈ M.restrictScalars ℤ :=
      (Submodule.span_le (p := M.restrictScalars ℤ)).2 (by rintro _ ⟨i, rfl⟩; exact hg i) he
    have hr'eq : r' = (𝕧 : 𝕂) • (r - e) := by
      rw [← hrr', smul_smul, mul_inv_cancel₀ RatFunc.X_ne_zero, one_smul]
    refine ⟨y + (𝕧⁻¹ ^ n : 𝕂) • e, r', add_mem hy ?_, ⟨(𝕧 : 𝕂) • l + e, add_mem
      (X_smul_mem₁ hl) heL, ?_⟩, ?_, hr', ?_⟩
    · rw [← zpow_natCast, ← zpow_neg_one, ← zpow_mul]
      exact zpow_smul_mem_laurent hsmul _ heZ
    · have h1 : (𝕧 ^ (n + 1) : 𝕂) • ((𝕧⁻¹ ^ n : 𝕂) • e) = (𝕧 : 𝕂) • e := by
        rw [smul_smul, pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ RatFunc.X_ne_zero,
          one_pow, mul_one]
      have h2 : (𝕧 ^ (n + 1) : 𝕂) • y = (𝕧 : 𝕂) • ((𝕧 : 𝕂) • l) := by
        rw [pow_succ', mul_smul, hyl]
      rw [smul_add, h1, h2, smul_add]
    · rw [hr'eq]
      have := zpow_smul_mem_laurent hsmul 1 (sub_mem hrM heM)
      rwa [zpow_one] at this
    · rw [pow_succ, mul_smul, hrr', smul_sub]
      abel

include hsmul in
/-- **[Kas91] Lemma 7.1.1 (i)**, spanning part, in basis form: let `g_b ∈ M ∩ L₀ ∩ L₁`, assume
that every element of `M ∩ L₀` is congruent modulo `v⁻¹L₀` to a `ℤ`-combination of the `g_b`,
and that `M ∩ v⁻¹L₀ ∩ L₁ = 0`. Then `M` is the `𝒜`-span of the `g_b`. -/
theorem span_of_balanced (hg : ∀ i, g i ∈ M) (hg₁ : ∀ i, g i ∈ L₁)
    (hsurj : ∀ x ∈ M, x ∈ L₀ →
      ∃ y ∈ Submodule.span ℤ (Set.range g), x - y ∈ InfinityLocalRing.uniformizer • L₀)
    (hinj : ∀ x ∈ M, x ∈ InfinityLocalRing.uniformizer • L₀ → x ∈ L₁ → x = 0)
    (hfull₀ : ∀ x ∈ M, ∃ N : ℕ, (𝕧⁻¹ ^ N : 𝕂) • x ∈ L₀)
    (hfull₁ : ∀ x ∈ M, ∃ N : ℕ, (𝕧 ^ N : 𝕂) • x ∈ L₁) :
    M ≤ Submodule.span (LaurentPolynomial ℤ) (Set.range g) := by
  intro x hx
  obtain ⟨N, hN⟩ := hfull₀ x hx
  set x₀ := (𝕧⁻¹ ^ N : 𝕂) • x with hx₀
  clear_value x₀
  have hx₀M : x₀ ∈ M := by
    have := zpow_smul_mem_laurent hsmul (-(N : ℤ)) hx
    rwa [zpow_neg, zpow_natCast, ← inv_pow, ← hx₀] at this
  obtain ⟨m, hm⟩ := hfull₁ x₀ hx₀M
  obtain ⟨y, r, hy, ⟨l, hl, hyl⟩, hrM, hr₀, hxy⟩ :=
    exists_balanced_approx hsmul hg hg₁ hsurj (m + 1) hx₀M hN
  have hne : (𝕧 : 𝕂) ≠ 0 := RatFunc.X_ne_zero
  -- `v⁻¹ r = vᵐ x₀ - l`
  have hr : (𝕧⁻¹ : 𝕂) • r = (𝕧 ^ m : 𝕂) • x₀ - l := by
    have h1 : (𝕧 ^ (m + 1) : 𝕂) • x₀ = (𝕧 : 𝕂) • l + r := by
      rw [hxy, smul_add, hyl, smul_smul, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_smul]
    have h2 : (𝕧 ^ m : 𝕂) • x₀ = (𝕧⁻¹ : 𝕂) • ((𝕧 : 𝕂) • l + r) := by
      rw [← h1, smul_smul, inv_mul_eq_div, pow_succ, mul_div_assoc, div_self hne, mul_one]
    rw [h2, smul_add, smul_smul, inv_mul_cancel₀ hne, one_smul]
    abel
  have h0 : (𝕧⁻¹ : 𝕂) • r = 0 := by
    refine hinj _ ?_ ?_ ?_
    · have := zpow_smul_mem_laurent hsmul (-1) hrM
      rwa [zpow_neg_one] at this
    · rw [← uniformizer_smul_eq]; exact Submodule.smul_mem_pointwise_smul _ _ _ hr₀
    · rw [hr]; exact sub_mem hm hl
  have hr0 : r = 0 := by
    rwa [smul_eq_zero, or_iff_right (inv_ne_zero hne)] at h0
  have hxeq : x = (𝕧 ^ (N : ℤ) : 𝕂) • x₀ := by
    rw [hx₀, smul_smul, zpow_natCast, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_smul]
  rw [hxeq, hxy, hr0, smul_zero, add_zero]
  exact zpow_smul_mem_laurent hsmul _ hy

end Main

section Residue

variable [Module InfinityLocalRing V] [IsScalarTower InfinityLocalRing 𝕂 V]
  [Module (LaurentPolynomial ℤ) V] {ι : Type*} {L₀ : Submodule InfinityLocalRing V} {g : ι → V}
  (hsmul : ∀ (c : LaurentPolynomial ℤ) (x : V), c • x = integralLaurentEval c • x)

include hsmul in
/-- **[Kas91] Lemma 7.1.1 (ii)**, surjectivity of `E → M ∩ L₀/M ∩ v⁻¹L₀` in basis form: if the
`g_b ∈ L₀` have independent residues, every element of `L₀` in their `𝒜`-span is congruent
modulo `v⁻¹L₀` to a `ℤ`-combination of the `g_b` (its coefficients lie in `𝒜 ∩ A = ℤ[v⁻¹]`). -/
theorem exists_int_sub_mem_of_mem_span
    (h₀ : ResidueIndependent InfinityLocalRing L₀ InfinityLocalRing.uniformizer g) {x : V}
    (hx : x ∈ Submodule.span (LaurentPolynomial ℤ) (Set.range g)) (hx₀ : x ∈ L₀) :
    ∃ y ∈ Submodule.span ℤ (Set.range g), x - y ∈ InfinityLocalRing.uniformizer • L₀ := by
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hx
  have hc : (c.sum fun i a ↦ a • g i) = ∑ i ∈ c.support, integralLaurentEval (c i) • g i :=
    Finset.sum_congr rfl fun i _ ↦ hsmul _ _
  rw [hc] at hx₀ ⊢
  have ha := h₀.exists_eq_of_sum_mem InfinityLocalRing.injective_algebraMap
    (show InfinityLocalRing.uniformizer ≠ 0 from irreducible_localX.ne_zero)
    InfinityLocalRing.exists_pow_mul c.support _ hx₀
  choose! a ha using ha
  have hz : ∀ i ∈ c.support, ∃ (z : ℤ) (t : InfinityLocalRing),
      integralLaurentEval (c i) = z + algebraMap InfinityLocalRing 𝕂
        (InfinityLocalRing.uniformizer * t) := by
    intro i hi
    obtain ⟨z, hz⟩ := InfinityLocalRing.residue_integer_of_laurent (a i) (c i) (ha i hi).symm
    obtain ⟨t, ht⟩ := (residue_eq_zero_iff ((show LocalRing from a i) - z)).1
      (by rw [map_sub, hz, map_intCast, sub_self])
    have e : a i = (z : InfinityLocalRing) + InfinityLocalRing.uniformizer *
        (show InfinityLocalRing from t) := (sub_eq_iff_eq_add').1 ht
    exact ⟨z, t, by rw [ha i hi, e, map_add, map_intCast]⟩
  choose! z t hzt using hz
  refine ⟨∑ i ∈ c.support, z i • g i,
    Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i hi ↦ ?_
  rw [hzt i hi, add_smul, Int.cast_smul_eq_zsmul, add_sub_cancel_left, algebraMap_smul, mul_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (L₀.smul_mem _ (h₀.1 i))

end Residue

end LieLean.QuantumGroup
