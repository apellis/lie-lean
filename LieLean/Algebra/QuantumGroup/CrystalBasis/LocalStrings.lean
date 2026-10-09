/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.HighestWeightLattice
import LieLean.Algebra.QuantumGroup.CrystalBasis.Lattice

/-!
# `i`-strings of weight vectors and lattices stable at given weights

For an integrable `U`-module `M` and `i ∈ I`, every weight vector `x ∈ M^μ` is a finite sum
`x = Σⱼ Fᵢ^{(j)} ηⱼ` with `ηⱼ ∈ M^{μ + j αᵢ}` killed by `Eᵢ`
(`QuantumGroup.exists_sum_dF_weight`). If an `A`-submodule `L` is stable under `f̃ᵢ`, and under `ẽᵢ`
on the weight spaces `M^{μ + j αᵢ}` (`j ≥ 0`) only, then `x ∈ L` forces every `ηⱼ ∈ L`
(`QuantumGroup.mem_of_sum_mem_weight`). This local form of [HK] Lemma 5.3.1 (1) is what the
grand-loop argument needs, where `ẽᵢ`-stability of `L(λ)` is only known in bounded depth.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
-/

open Finset

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  (hM : IsIntegrable R v M) (i : I)

omit [NeZero v] in
lemma mem_nodeWt_of_mem_add_nsmul {μ : Y →+ ℤ} {j : ℕ} {m : M}
    (hm : m ∈ weightSpace R v M (μ + j • R.root i)) :
    m ∈ nodeWt R v M i (μ (R.coroot i) + 2 * j) := by
  have := mem_nodeWt_of_mem (i := i) hm
  rwa [AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply, R.root_coroot, D.cartanMatrix_self,
    nsmul_eq_mul, mul_comm] at this

/-- The projection onto `M^Λ` after `Fᵢ` is `Fᵢ` after the projection onto `M^{Λ + αᵢ}`. -/
lemma weightSetProj_singleton_F_smul (Λ : Y →+ ℤ) (m : M) :
    weightSetProj hv hM {Λ} (F R v i • m) = F R v i • weightSetProj hv hM {Λ + R.root i} m := by
  have := ext_weightSpace hM (f := weightSetProj hv hM {Λ} ∘ₗ act R v M (F R v i))
    (g := act R v M (F R v i) ∘ₗ weightSetProj hv hM {Λ + R.root i}) fun Λ' m hm ↦ by
      classical
      simp only [LinearMap.comp_apply, Algebra.lsmul_apply]
      rw [weightSetProj_of_mem hv hM _ (F_smul_mem_weightSpace hm i),
        weightSetProj_of_mem hv hM _ hm]
      simp only [Set.mem_singleton_iff]
      by_cases h : Λ' = Λ + R.root i
      · subst h; simp
      · have h' : Λ' - R.root i ≠ Λ := fun h'' ↦ h (by rw [← h'']; abel)
        simp [h, h']
  exact LinearMap.congr_fun this m

/-- The projection onto `M^Λ` after `Eᵢ` is `Eᵢ` after the projection onto `M^{Λ - αᵢ}`. -/
lemma weightSetProj_singleton_E_smul (Λ : Y →+ ℤ) (m : M) :
    weightSetProj hv hM {Λ} (E R v i • m) = E R v i • weightSetProj hv hM {Λ - R.root i} m := by
  have := ext_weightSpace hM (f := weightSetProj hv hM {Λ} ∘ₗ act R v M (E R v i))
    (g := act R v M (E R v i) ∘ₗ weightSetProj hv hM {Λ - R.root i}) fun Λ' m hm ↦ by
      classical
      simp only [LinearMap.comp_apply, Algebra.lsmul_apply]
      rw [weightSetProj_of_mem hv hM _ (E_smul_mem_weightSpace hm i),
        weightSetProj_of_mem hv hM _ hm]
      simp only [Set.mem_singleton_iff]
      by_cases h : Λ' = Λ - R.root i
      · subst h; simp
      · have h' : Λ' + R.root i ≠ Λ := fun h'' ↦ h (by rw [← h'']; abel)
        simp [h, h']
  exact LinearMap.congr_fun this m

lemma weightSetProj_singleton_F_pow (Λ : Y →+ ℤ) (j : ℕ) (m : M) :
    weightSetProj hv hM {Λ} (((nodeSl2 R v M hv hM i).F ^ j) m) =
      ((nodeSl2 R v M hv hM i).F ^ j) (weightSetProj hv hM {Λ + j • R.root i} m) := by
  induction j generalizing Λ with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    change weightSetProj hv hM {Λ} (F R v i • _) = F R v i • _
    rw [weightSetProj_singleton_F_smul, ih, add_assoc, ← succ_nsmul']

lemma weightSetProj_singleton_dF (Λ : Y →+ ℤ) (j : ℕ) (m : M) :
    weightSetProj hv hM {Λ} ((nodeSl2 R v M hv hM i).dF j m) =
      (nodeSl2 R v M hv hM i).dF j (weightSetProj hv hM {Λ + j • R.root i} m) := by
  rw [IntegrableSl2.dF_apply, IntegrableSl2.dF_apply, map_smul, weightSetProj_singleton_F_pow]

/-- **String decomposition by weights**: a weight vector `x ∈ M^μ` is a finite sum
`Σⱼ Fᵢ^{(j)} ηⱼ` with `ηⱼ ∈ M^{μ + j αᵢ}`, `Eᵢ ηⱼ = 0`, and `ηⱼ = 0` unless `⟨i, μ⟩ + j ≥ 0`
(cf. [HK] Lemma 4.1.1). -/
theorem exists_sum_dF_weight {μ : Y →+ ℤ} {x : M} (hx : x ∈ weightSpace R v M μ) :
    ∃ (N : ℕ) (η : ℕ → M), (∀ j : ℕ, η j ∈ weightSpace R v M (μ + j • R.root i)) ∧
      (∀ j, E R v i • η j = 0) ∧ (∀ j : ℕ, η j ≠ 0 → 0 ≤ μ (R.coroot i) + j) ∧
      (∀ j, N ≤ j → η j = 0) ∧
      x = ∑ j ∈ range N, (nodeSl2 R v M hv hM i).dF j (η j) := by
  classical
  obtain ⟨N, η, hη, h2, hN, hsum⟩ := IntegrableSl2.exists_sum_dF (V := nodeSl2 R v M hv hM i)
    (pow_d_ne_zero i) (pow_d_ne_one hv i) (mem_nodeWt_of_mem (i := i) hx)
  refine ⟨N, fun j ↦ weightSetProj hv hM {μ + j • R.root i} (η j),
    fun j ↦ weightSetProj_singleton_mem hv hM _ _, fun j ↦ ?_, fun j hj ↦ ?_,
    fun j hj ↦ by simp [hN j hj], ?_⟩
  · have hE : E R v i • η j = 0 := (hη j).2
    have := weightSetProj_singleton_E_smul hv hM i (μ + (j + 1) • R.root i) (η j)
    rw [hE, map_zero, succ_nsmul, ← add_assoc, add_sub_cancel_right] at this
    exact this.symm
  · refine h2 j fun h0 ↦ hj ?_
    simp only [h0, map_zero]
  · have hP := weightSetProj_of_mem hv hM {μ} hx
    simp only [Set.mem_singleton_iff, ↓reduceIte] at hP
    rw [← hP, hsum, map_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [weightSetProj_singleton_dF]

/-- `ẽᵢ (Σ_{j ≤ N} Fᵢ^{(j)} ηⱼ) = Σ_{j < N} Fᵢ^{(j)} η_{j+1}` for a string decomposition by
weights. -/
lemma kashiwaraE_sum {μ : Y →+ ℤ} {η : ℕ → M}
    (h1 : ∀ j : ℕ, η j ∈ weightSpace R v M (μ + j • R.root i)) (hE : ∀ j, E R v i • η j = 0)
    (h2 : ∀ j : ℕ, η j ≠ 0 → 0 ≤ μ (R.coroot i) + j) (N : ℕ) :
    kashiwaraE R v M hv hM i (∑ j ∈ range (N + 1), (nodeSl2 R v M hv hM i).dF j (η j)) =
      ∑ j ∈ range N, (nodeSl2 R v M hv hM i).dF j (η (j + 1)) :=
  IntegrableSl2.eTilde_sum (V := nodeSl2 R v M hv hM i) (pow_d_ne_zero i) (pow_d_ne_one hv i)
    (fun j ↦ ⟨mem_nodeWt_of_mem_add_nsmul i (h1 j), hE j⟩) h2 N

lemma dF_mem_weightSpace {μ : Y →+ ℤ} {j : ℕ} {m : M}
    (hm : m ∈ weightSpace R v M (μ + j • R.root i)) :
    (nodeSl2 R v M hv hM i).dF j m ∈ weightSpace R v M μ := by
  rw [IntegrableSl2.dF_apply]
  refine Submodule.smul_mem _ _ ?_
  induction j generalizing μ with
  | zero => simpa using hm
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := ih (μ := μ + R.root i) (by rwa [add_assoc, ← succ_nsmul'])
    have h2 := F_smul_mem_weightSpace h i
    rw [add_sub_cancel_right] at h2
    exact h2

lemma sum_dF_mem_weightSpace {μ : Y →+ ℤ} {η : ℕ → M}
    (h1 : ∀ j : ℕ, η j ∈ weightSpace R v M (μ + j • R.root i)) (N : ℕ) :
    ∑ j ∈ range N, (nodeSl2 R v M hv hM i).dF j (η j) ∈ weightSpace R v M μ :=
  Submodule.sum_mem _ fun j _ ↦ dF_mem_weightSpace hv hM i (h1 j)

variable {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]
  {L : Submodule A M}

omit [Algebra A k] [IsScalarTower A k M] in
lemma kashiwaraF_pow_mem (hf : ∀ y ∈ L, kashiwaraF R v M hv hM i y ∈ L) (j : ℕ) {y : M}
    (hy : y ∈ L) : (kashiwaraF R v M hv hM i ^ j) y ∈ L := by
  induction j with
  | zero => simpa using hy
  | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact hf _ ih

omit [Algebra A k] [IsScalarTower A k M] in
/-- **Local form of [HK] Lemma 5.3.1 (1)**: if `L` is stable under `f̃ᵢ`, and under `ẽᵢ` on the
weight spaces `M^{μ + j αᵢ}`, then the vectors `ηⱼ` of the string decomposition by weights of an
element `Σⱼ Fᵢ^{(j)} ηⱼ ∈ L ∩ M^μ` lie in `L`. -/
theorem mem_of_sum_mem_weight (hf : ∀ y ∈ L, kashiwaraF R v M hv hM i y ∈ L) (N : ℕ) :
    ∀ (μ : Y →+ ℤ) (η : ℕ → M), (∀ j : ℕ, η j ∈ weightSpace R v M (μ + j • R.root i)) →
      (∀ j, E R v i • η j = 0) → (∀ j : ℕ, η j ≠ 0 → 0 ≤ μ (R.coroot i) + j) →
      (∀ j : ℕ, ∀ y ∈ L, y ∈ weightSpace R v M (μ + j • R.root i) →
        kashiwaraE R v M hv hM i y ∈ L) →
      ∑ j ∈ range N, (nodeSl2 R v M hv hM i).dF j (η j) ∈ L → ∀ j < N, η j ∈ L := by
  induction N with
  | zero => intro _ _ _ _ _ _ _ j hj; omega
  | succ N ih =>
    intro μ η h1 hE h2 he hu
    have hu' := he 0 _ hu (by simpa using sum_dF_mem_weightSpace hv hM i h1 (N + 1))
    rw [kashiwaraE_sum hv hM i h1 hE h2] at hu'
    have hsucc := ih (μ + R.root i) (fun j ↦ η (j + 1))
      (fun j ↦ by rw [add_assoc, ← succ_nsmul']; exact h1 (j + 1)) (fun j ↦ hE (j + 1))
      (fun j h ↦ by
        have := h2 _ h
        rw [AddMonoidHom.add_apply, R.root_coroot, D.cartanMatrix_self]
        push_cast at this ⊢; omega)
      (fun j y hy hyw ↦ he (j + 1) y hy (by rwa [succ_nsmul', ← add_assoc]))
      hu'
    intro j hj
    rcases j with _ | j
    · rw [sum_range_succ'] at hu
      have hrest : ∑ j ∈ range N, (nodeSl2 R v M hv hM i).dF (j + 1) (η (j + 1)) ∈ L := by
        refine Submodule.sum_mem _ fun j hj ↦ ?_
        rw [← kashiwaraF_pow_of_primitive hv hM i (hE (j + 1))
          (mem_nodeWt_of_mem_add_nsmul i (h1 (j + 1)))]
        exact kashiwaraF_pow_mem hv hM i hf _ (hsucc j (mem_range.1 hj))
      simpa using sub_mem hu hrest
    · exact hsucc j (by omega)

end LieLean.QuantumGroup
