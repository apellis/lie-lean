/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Lattice

/-!
# Comparing `F^{(a)}` with the Kashiwara operators on a Kashiwara-stable lattice

Let `M` be an integrable `U_q(𝔰𝔩₂)`-module, `L ⊆ M` a Kashiwara-stable `A`-lattice and `c ∈ A`.
Let `x = Σⱼ F^{(j)} ηⱼ ∈ Mⁿ` be a string decomposition (the `ηⱼ` primitive). If the components
`ηⱼ`, `j ≥ 1`, are small in the sense that `[b+j, b] ηⱼ ∈ c L` for `b ≤ a + 1`, then
`f̃ F^{(a)} x ≡ F^{(a+1)} x` and (for `a < n`) `ẽ F^{(a+1)} x ≡ F^{(a)} x` modulo `c L`, even if
`x ∉ L` (`IntegrableSl2.IsKashiwaraStable.fTilde_dF_sub_mem`,
`IntegrableSl2.IsKashiwaraStable.eTilde_dF_sub_mem`). The smallness of the components follows from
that of `E^{(j)} x`: if `t E^{(j)} x ∈ c L` then `t [n + 2j, j] ηⱼ ∈ c L`
(`IntegrableSl2.IsKashiwaraStable.smul_mem_of_smul_dE_mem`).

This is the mechanism behind [Jan] 10.5: for `u ∈ U⁻` and `⟨i, λ⟩ ≫ 0` the vector `u v_λ` has
small string components, so `Fᵢ`-divided powers of it are compatible with Kashiwara's operators
modulo `ϖ L(λ)`. Our formulation (in terms of the components) is our own.

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 10.5.
-/

open Finset Pointwise

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  {V : IntegrableSl2 q M} {hq0 : q ≠ 0} {hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]
  {L : Submodule A M}

lemma IsKashiwaraStable.smul_dF_mem_smul (hL : V.IsKashiwaraStable hq0 hq L) (c : A) {p : ℤ}
    {η : M} (hη : η ∈ V.prim p) {κ : k} (hκ : κ • η ∈ c • L) (m : ℕ) :
    κ • V.dF m η ∈ c • L := by
  rw [← map_smul]
  exact (hL.smul c).dF_mem (Submodule.smul_mem _ κ hη) hκ m

omit [Module A M] [IsScalarTower A k M] in
lemma dF_sum (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (a N : ℕ) (η : ℕ → M) :
    V.dF a (∑ j ∈ range N, V.dF j (η j)) =
      ∑ j ∈ range N, qBinomial q (a + j) a • V.dF (a + j) (η j) := by
  rw [map_sum]
  exact sum_congr rfl fun j _ ↦ dF_dF hq0 hq a j (η j)

/-- If the string components `ηⱼ`, `j ≥ 1`, of `x` satisfy `[b+j, b] ηⱼ ∈ c L` for `b ≤ a + 1`,
then `f̃ F^{(a)} x ≡ F^{(a+1)} x` modulo `c L`. -/
theorem IsKashiwaraStable.fTilde_dF_sub_mem (hL : V.IsKashiwaraStable hq0 hq L) (c : A) {n : ℤ}
    {η : ℕ → M} (h1 : ∀ j : ℕ, η j ∈ V.prim (n + 2 * j)) (N a : ℕ)
    (hη : ∀ j, 1 ≤ j → ∀ b ≤ a + 1, qBinomial q (b + j) b • η j ∈ c • L) :
    V.fTilde hq0 hq (V.dF a (∑ j ∈ range N, V.dF j (η j))) -
      V.dF (a + 1) (∑ j ∈ range N, V.dF j (η j)) ∈ c • L := by
  rw [dF_sum hq0 hq, dF_sum hq0 hq, map_sum,
    ← sum_sub_distrib]
  refine sum_mem fun j _ ↦ ?_
  rcases j with _ | j
  · simp only [add_zero, qBinomial_self, one_smul]
    rw [fTilde_dF hq0 hq (h1 0).2 (h1 0).1, sub_self]
    exact zero_mem _
  · refine sub_mem ?_ (hL.smul_dF_mem_smul c (h1 _) (hη _ (by omega) _ le_rfl) _)
    exact (hL.smul c).fTilde_mem _
      (hL.smul_dF_mem_smul c (h1 _) (hη _ (by omega) _ (by omega)) _)

/-- If the string components `ηⱼ`, `j ≥ 1`, of `x ∈ Mⁿ` satisfy `[b+j, b] ηⱼ ∈ c L` for
`b ≤ a + 1`, and `a < n`, then `ẽ F^{(a+1)} x ≡ F^{(a)} x` modulo `c L`. -/
theorem IsKashiwaraStable.eTilde_dF_sub_mem (hL : V.IsKashiwaraStable hq0 hq L) (c : A) {n : ℤ}
    {η : ℕ → M} (h1 : ∀ j : ℕ, η j ∈ V.prim (n + 2 * j)) (N a : ℕ) (ha : (a : ℤ) < n)
    (hη : ∀ j, 1 ≤ j → ∀ b ≤ a + 1, qBinomial q (b + j) b • η j ∈ c • L) :
    V.eTilde hq0 hq (V.dF (a + 1) (∑ j ∈ range N, V.dF j (η j))) -
      V.dF a (∑ j ∈ range N, V.dF j (η j)) ∈ c • L := by
  rw [dF_sum hq0 hq, dF_sum hq0 hq, map_sum,
    ← sum_sub_distrib]
  refine sum_mem fun j _ ↦ ?_
  rcases j with _ | j
  · simp only [add_zero, qBinomial_self, one_smul]
    rw [eTilde_dF_succ hq0 hq (h1 0).2 (h1 0).1 (by simpa using ha), sub_self]
    exact zero_mem _
  · refine sub_mem ?_ (hL.smul_dF_mem_smul c (h1 _) (hη _ (by omega) _ (by omega)) _)
    exact (hL.smul c).eTilde_mem _
      (hL.smul_dF_mem_smul c (h1 _) (hη _ (by omega) _ le_rfl) _)

/-- The string components of `E^{(j)} x`: if `t E^{(j)} x ∈ c L` for `x = Σₗ F^{(l)} ηₗ ∈ Mⁿ`,
then `t [n + 2j, j] ηⱼ ∈ c L`. -/
theorem IsKashiwaraStable.smul_mem_of_smul_dE_mem (hL : V.IsKashiwaraStable hq0 hq L) (c : A)
    {n : ℤ} {η : ℕ → M} (h1 : ∀ j : ℕ, η j ∈ V.prim (n + 2 * j))
    (h2 : ∀ j : ℕ, η j ≠ 0 → 0 ≤ n + j) (N j : ℕ) (hjN : j < N) (t : k)
    (ht : t • V.dE j (∑ l ∈ range N, V.dF l (η l)) ∈ c • L) :
    (t * qBinomial q (n + 2 * j).toNat j) • η j ∈ c • L := by
  set η' : ℕ → M := fun m ↦ (t * qBinomial q (n + 2 * j + m).toNat j) • η (j + m) with hη'
  have hdE : t • V.dE j (∑ l ∈ range N, V.dF l (η l)) =
      ∑ m ∈ range (N - j), V.dF m (η' m) := by
    obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hjN.le
    rw [sum_range_add, map_add, map_sum, map_sum, show j + K - j = K by omega]
    have hz : ∀ l ∈ range j, V.dE j (V.dF l (η l)) = 0 := by
      intro l hl
      have hl := mem_range.1 hl
      by_cases h0 : η l = 0
      · rw [h0, map_zero, map_zero]
      have hp := h2 l h0
      obtain ⟨p, hp'⟩ : ∃ p : ℕ, (p : ℤ) = n + 2 * l := ⟨(n + 2 * l).toNat, by omega⟩
      have hlp : l ≤ p := by omega
      exact dE_dF_eq_zero_of_lt hq0 hq (hp' ▸ (h1 l).1) (h1 l).2 hlp hl
    rw [sum_eq_zero hz, zero_add, smul_sum]
    refine sum_congr rfl fun m _ ↦ ?_
    simp only [hη']
    by_cases h0 : η (j + m) = 0
    · simp [h0]
    have hp := h2 _ h0
    obtain ⟨p, hp'⟩ : ∃ p : ℕ, (p : ℤ) = n + 2 * (j + m : ℕ) := ⟨(n + 2 * (j + m : ℕ)).toNat,
      by push_cast at hp ⊢; omega⟩
    have hjp : j + m ≤ p := by push_cast at hp hp'; omega
    rw [dE_dF_of_primitive (p := p) hq0 hq (hp' ▸ (h1 _).1) (h1 _).2 (by omega) hjp, smul_smul,
      show j + m - j = m by omega, map_smul]
    congr 3
    push_cast at hp'
    omega
  rw [hdE] at ht
  have hprim : ∀ m : ℕ, η' m ∈ V.prim (n + 2 * j + 2 * m) := fun m ↦ by
    simp only [hη']
    refine Submodule.smul_mem _ _ ?_
    convert h1 (j + m) using 2
    push_cast; ring
  have hnorm : ∀ m : ℕ, η' m ≠ 0 → 0 ≤ n + 2 * j + m := fun m hm ↦ by
    have : η (j + m) ≠ 0 := fun h ↦ hm (by simp [hη', h])
    have := h2 _ this
    push_cast at this
    omega
  have := (hL.smul c).mem_of_sum_mem (N - j) (n + 2 * j) η' hprim hnorm ht 0 (by omega)
  simpa [hη'] using this

end IntegrableSl2

end LieLean.QuantumGroup
