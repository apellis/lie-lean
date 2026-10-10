/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.Independence
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.DividedPowers

/-!
# PBW monomials for the inverse symmetries `T'_{i,-1} = Tᵢ⁻¹`

For `v ≠ 0` not a root of unity, a Cartan datum and a reduced word `ω = i₁ ⋯ iₙ`, the root vectors
`T'_{i₁,-1} ⋯ T'_{iₘ₋₁,-1}(E_{iₘ})` lie in `U⁺` ([Lus] 40.1.3, second assertion:
`rootVector_symm_mem_adjoin_of_not_root`, from the first via the anti-automorphism `σ` of
[Lus] 37.2.4) and the ordered monomials `E_{i₁}^{c₁} T'_{i₁,-1}(E_{i₂}^{c₂}) ⋯` are linearly
independent (`linearIndependent_pbwMonomial_symm_of_isReduced`, cf. [Lus] 40.2.1 (b) for
`e = -1`). As for `Tᵢ` (`PBW/Independence.lean`), the proof is the induction of [Jan] 8.21 b):
`∑ₐ Eᵢᵃ Tᵢ⁻¹(uₐ) = 0` with `uₐ ∈ U⁺` gives, after applying `Tᵢ`, `∑ₐ (-Fᵢ K̃ᵢ)ᵃ uₐ = 0`, and the
triangular decomposition separates the summands (`eq_zero_of_sum_F_pow_K_mul`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 37.2.4, 40.1.3, 40.2.1.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Lemma 8.21.
-/

open LieLean CoxeterSystem

noncomputable section

namespace LieLean.QuantumGroup

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]

lemma braidReversal_one' : braidReversal (1 : QuantumGroup R v) = 1 := by
  simp [braidReversal]

/-- `σ` maps `U⁺` into itself. -/
lemma braidReversal_mem_adjoin {x : QuantumGroup R v}
    (hx : x ∈ Algebra.adjoin k (Set.range (E R v))) :
    braidReversal x ∈ Algebra.adjoin k (Set.range (E R v)) := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    rw [braidReversal_E]
    exact Algebra.subset_adjoin ⟨l, rfl⟩
  | algebraMap a =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, braidReversal_one']
    exact Subalgebra.smul_mem _ (one_mem _) _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [braidReversal_mul]; exact mul_mem hy hx

/-- `(-Fᵢ K̃ᵢ)ᵃ` is a nonzero multiple of `Fᵢᵃ K̃ᵢᵃ`. -/
lemma exists_neg_F_mul_Kt_pow (i : I) (a : ℕ) :
    ∃ c : k, c ≠ 0 ∧ (-(F R v i * Kt R v i)) ^ a = c • (F R v i ^ a * K R v (a • ktilde R i)) := by
  induction a with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | succ a ih =>
    obtain ⟨c, hc, h⟩ := ih
    refine ⟨-(c * v ^ (-R.root i (a • ktilde R i))),
      neg_ne_zero.2 (mul_ne_zero hc (zpow_ne_zero _ (NeZero.ne v))), ?_⟩
    have hK : K R v (a • ktilde R i) * Kt R v i = K R v ((a + 1) • ktilde R i) := by
      rw [Kt, K_add, succ_nsmul]
    rw [pow_succ, h, mul_neg, smul_mul_assoc, ← mul_assoc, mul_assoc (F R v i ^ a), K_mul_F,
      mul_smul_comm, ← mul_assoc, ← pow_succ, smul_mul_assoc, mul_assoc, hK, smul_smul, neg_smul]

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

include hv' in
/-- `T'_{i₁,-1} ⋯ T'_{iₙ,-1} = σ ∘ T''_{i₁,1} ⋯ T''_{iₙ,1} ∘ σ` ([Lus] 37.2.4). -/
lemma list_braidEquivOfNotRoot_symm_apply (ω : List I) (y : QuantumGroup R v) :
    (ω.map fun j ↦ (braidEquivOfNotRoot R hv' j).symm).prod y =
      braidReversal ((ω.map (braidEquivOfNotRoot R hv')).prod (braidReversal y)) := by
  induction ω generalizing y with
  | nil => simp [braidReversal_involutive y]
  | cons i ω ih =>
    simp only [List.map_cons, List.prod_cons, AlgEquiv.mul_apply]
    rw [ih, braidEquivOfNotRoot_symm_apply, braidReversal_involutive]

/-- **[Lus] 40.1.3**, second assertion (`T'_{i,-1} = Tᵢ⁻¹`): along a reduced word, the root vectors
`T'_{i₁,-1} ⋯ T'_{iₘ₋₁,-1}(E_{iₘ})` lie in `U⁺`. -/
theorem rootVector_symm_mem_adjoin_of_not_root {W : Type*} [Group W]
    {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W} {ω : List I} (hω : cs.IsReduced ω)
    (n : ℕ) (hn : n < ω.length) :
    rootVector (fun j ↦ (braidEquivOfNotRoot R hv' j).symm) (E R v) ω n hn ∈
      Algebra.adjoin k (Set.range (E R v)) := by
  have h := rootVector_mem_adjoin_of_not_root (R := R) hv' hω n hn
  simp only [rootVector] at h ⊢
  rw [list_braidEquivOfNotRoot_symm_apply, braidReversal_E]
  exact braidReversal_mem_adjoin h

/-- **The sum `∑ₐ Eᵢᵃ Tᵢ⁻¹(U⁺)` is direct.** -/
theorem eq_zero_of_sum_E_pow_mul_symm {i : I} (f : ℕ →₀ QuantumGroup R v)
    (hf : ∀ a, f a ∈ (plusHom R v).range)
    (h : (f.sum fun a x ↦ E R v i ^ a * (braidEquivOfNotRoot R hv' i).symm x) = 0) : f = 0 := by
  have HT := braidEquivOfNotRoot_hasImages hv' R i
  have hG : braidEquivOfNotRoot R hv' i (E R v i) = -(F R v i * Kt R v i) := by
    have := HT.map_E i
    simpa using this
  have h1 : (f.sum fun a x ↦ (-(F R v i * Kt R v i)) ^ a * x) = 0 := by
    apply (braidEquivOfNotRoot R hv' i).symm.injective
    rw [map_zero, ← h, Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [map_mul, map_pow, ← hG, AlgEquiv.symm_apply_apply]
  choose c hc hGc using fun a ↦ exists_neg_F_mul_Kt_pow (R := R) (v := v) i a
  refine eq_zero_of_sum_F_pow_K_mul (i := i) hv' c hc (fun a ↦ a • ktilde R i) f hf ?_
  rw [← h1]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [hGc]

/-- **Linear independence of the PBW monomials for `T'_{i,-1} = Tᵢ⁻¹`** (cf. [Lus] 40.2.1 (b),
`e = -1`; [Jan] Lemma 8.21 b)): for `v ≠ 0` not a root of unity and a reduced word `ω`, the
ordered monomials `E_{i₁}^{c₁} Tᵢ₁⁻¹(E_{i₂}^{c₂}) ⋯ Tᵢ₁⁻¹ ⋯ Tᵢₙ₋₁⁻¹(E_{iₙ}^{cₙ})` are linearly
independent, for every Cartan datum. -/
theorem linearIndependent_pbwMonomial_symm_of_isReduced {W : Type*} [Group W]
    {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W} {ω : List I} (hω : cs.IsReduced ω) :
    LinearIndependent k
      (pbwMonomial (fun j ↦ (braidEquivOfNotRoot R hv' j).symm) (E R v) ω) := by
  refine linearIndependent_pbwMonomial
    (S := Subalgebra.toSubmodule (Algebra.adjoin k (Set.range (E R v)))) ?_ ω ?_
  · intro i f hf h
    refine eq_zero_of_sum_E_pow_mul_symm hv' f (fun a ↦ ?_) h
    rw [range_plusHom]
    exact hf a
  · intro n c
    exact pbwMonomial_mem _ _
      (fun m hm ↦ rootVector_symm_mem_adjoin_of_not_root hv' (hω.drop n) m hm) c

end LieLean.QuantumGroup
