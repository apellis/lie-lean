/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.PropDFG

/-!
# Kashiwara's grand loop

We assemble the inductive statements `A(r)`, …, `G(r)` of Kashiwara's grand-loop argument
([HK] §5.3) and prove them for all `r` by induction (`GrandLoop.allProp`). The setting: `v`
transcendental over `ℚ` in a field `k` of characteristic zero, an `X`-regular root datum with
fundamental weights, and a discrete valuation ring `A ⊆ k` with `k = A[ϖ⁻¹]` and `ϖ ↦ v⁻¹`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
-/

open Finset Pointwise LusztigF TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

section Base

variable [Finite I]

/-- `F(0)`. -/
theorem propF_zero : PropF hvt hR A 0 := by
  intro Λ₁ Λ₂ ν hν z hz hzw
  have hν0 : ν = 0 := by
    ext i
    have : ν i ≤ ν.degree := by
      rw [Finsupp.degree]
      by_cases hi : i ∈ ν.support
      · exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi
      · rw [Finsupp.notMem_support_iff.1 hi]; exact Nat.zero_le _
    simp; omega
  subst hν0
  refine mem_of_fW_tmul_mem Λ₁ Λ₂ 0
    ((lat hvt hR A (Λ₁ + Λ₂)).comap
      (((tensorProj hvt hR Λ₁.2 Λ₂.2).restrictScalars k).restrictScalars A))
    (fun w₁ w₂ hw ↦ ?_) hz hzw
  have h1 := congrArg Finsupp.degree hw
  rw [map_add, degree_wordWeight, degree_wordWeight, map_zero] at h1
  obtain rfl : w₁ = [] := List.length_eq_zero_iff.1 (by omega)
  obtain rfl : w₂ = [] := List.length_eq_zero_iff.1 (by omega)
  change tensorProj hvt hR Λ₁.2 Λ₂.2 _ ∈ lat hvt hR A (Λ₁ + Λ₂)
  have := tensorProj_fTw (hvt := hvt) (hR := hR) Λ₁ Λ₂ []
  rw [fTw_nil] at this
  rw [fW_nil, fW_nil, this]
  exact IrreducibleModule.fWord_mem_lattice hR _ (Λ₁ + Λ₂).2 A []

/-- `G(0)`. -/
theorem propG_zero : PropG hvt hR A ϖ 0 := by
  intro Λ₁ Λ₂ w₁ w₂ hw
  obtain rfl : w₁ = [] := List.length_eq_zero_iff.1 (by omega)
  obtain rfl : w₂ = [] := List.length_eq_zero_iff.1 (by omega)
  refine Or.inr ⟨[], ?_⟩
  have := tensorProj_fTw (hvt := hvt) (hR := hR) Λ₁ Λ₂ []
  rw [fTw_nil] at this
  rw [fW_nil, fW_nil, this, sub_self]
  exact zero_mem _

end Base

variable (hvt hR A ϖ) in
/-- All the statements of the grand loop in depth `r`. -/
def AllProp [Finite I] (r : ℕ) : Prop :=
  PropA hvt hR A r ∧ PropB hvt hR A ϖ r ∧ PropC hvt hR A ϖ r ∧ PropD hvt hR A ϖ r ∧
    PropE hvt hR A r ∧ PropF hvt hR A r ∧ PropG hvt hR A ϖ r

omit [CharZero k] [NeZero v] in
/-- From fundamental weights, a dominant `ρ` with `⟨i, ρ⟩ ≥ 1`. -/
lemma exists_rho [Finite I]
    (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0) :
    ∃ ρ : Dom R, ∀ i, 1 ≤ ρ.1 (R.coroot i) := by
  classical
  have := Fintype.ofFinite I
  choose Λf hΛf using hfund
  refine ⟨⟨∑ j, (Λf j).1, fun i ↦ ?_⟩, fun i ↦ ?_⟩
  · rw [AddMonoidHom.finsetSum_apply]
    exact Finset.sum_nonneg fun j _ ↦ (Λf j).2 i
  · change 1 ≤ (∑ j, (Λf j).1) (R.coroot i)
    rw [AddMonoidHom.finsetSum_apply]
    simp [hΛf]

/-- **Kashiwara's grand loop** ([HK] §5.3): `A(r)`, …, `G(r)` hold for all `r`. -/
theorem allProp [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
    (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖv : algebraMap A k ϖ = v⁻¹)
    (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
    (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0) :
    ∀ r, AllProp hvt hR A ϖ r := by
  have hϖu : ¬IsUnit ϖ := (IsLocalRing.mem_maximalIdeal ϖ).1 hϖ
  obtain ⟨ρ, hρ⟩ := exists_rho hfund
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  match r, ih with
  | 0, _ => exact ⟨propA_zero, propB_zero, propC_zero, propD_zero hinj hϖv, propE_zero,
      propF_zero, propG_zero⟩
  | 1, ih =>
    obtain ⟨-, -, -, hD0, hE0, hF0, hG0⟩ := ih 0 (by omega)
    have hA : ∀ s ≤ 1, PropA hvt hR A s := fun s hs ↦ by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with rfl | rfl
      · exact propA_zero
      · exact propA_one
    have hB : ∀ s ≤ 1, PropB hvt hR A ϖ s := fun s hs ↦ by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with rfl | rfl
      · exact propB_zero
      · exact propB_one
    have hC : ∀ s ≤ 1, PropC hvt hR A ϖ s := fun s hs ↦ by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with rfl | rfl
      · exact propC_zero
      · exact propC_one hϖv hinj hϖu
    have hF1 := propF_succ hϖ hϖv hk (r := 0) hA (hB 1 le_rfl) (hC 1 le_rfl) hD0 hF0
    exact ⟨hA 1 le_rfl, hB 1 le_rfl, hC 1 le_rfl,
      propD_succ hϖv (r := 0) hA (hB 1 le_rfl) (hC 1 le_rfl) hD0,
      propE_succ hϖ hϖv (r := 0) (fun s hs ↦ hA s (by omega)) hE0, hF1,
      propG_succ hϖ hϖv (r := 0) hA hB hC hD0 hF0 hF1 hG0⟩
  | n + 2, ih =>
    have hA' : ∀ s < n + 2, PropA hvt hR A s := fun s hs ↦ (ih s hs).1
    have hB' : ∀ s < n + 2, PropB hvt hR A ϖ s := fun s hs ↦ (ih s hs).2.1
    have hC' : ∀ s < n + 2, PropC hvt hR A ϖ s := fun s hs ↦ (ih s hs).2.2.1
    obtain ⟨-, -, -, hD1, hE1, hF1, hG1⟩ := ih (n + 1) (by omega)
    have hE2 := propE_succ hϖ hϖv (r := n + 1) (fun s hs ↦ hA' s (by omega)) hE1
    have hA2 := propA_add_two hϖ hϖv hinj hk hfund hA' hB' hC' hE1 hF1
    have hA : ∀ s ≤ n + 2, PropA hvt hR A s := fun s hs ↦ by
      rcases Nat.lt_or_ge s (n + 2) with h | h
      · exact hA' s h
      · obtain rfl : s = n + 2 := by omega
        exact hA2
    have hB2 := propB_add_two hϖ hϖv hinj hfund hA hB' hC' hE1 hF1 hG1
    have hE : ∀ s ≤ n + 2, PropE hvt hR A s := fun s hs ↦ by
      rcases Nat.lt_or_ge s (n + 2) with h | h
      · exact (ih s h).2.2.2.2.1
      · obtain rfl : s = n + 2 := by omega
        exact hE2
    have hC2 := propC_add_two hinj hϖ hϖv hk hfund ρ hρ hA (fun s hs ↦ hB' s (by omega))
      (fun s hs ↦ hC' s (by omega)) hE hF1
    have hB : ∀ s ≤ n + 2, PropB hvt hR A ϖ s := fun s hs ↦ by
      rcases Nat.lt_or_ge s (n + 2) with h | h
      · exact hB' s h
      · obtain rfl : s = n + 2 := by omega
        exact hB2
    have hC : ∀ s ≤ n + 2, PropC hvt hR A ϖ s := fun s hs ↦ by
      rcases Nat.lt_or_ge s (n + 2) with h | h
      · exact hC' s h
      · obtain rfl : s = n + 2 := by omega
        exact hC2
    have hF2 := propF_succ hϖ hϖv hk (r := n + 1) hA hB2 hC2 hD1 hF1
    exact ⟨hA2, hB2, hC2, propD_succ hϖv (r := n + 1) hA hB2 hC2 hD1, hE2, hF2,
      propG_succ hϖ hϖv (r := n + 1) hA hB hC hD1 hF1 hF2 hG1⟩

end GrandLoop

end LieLean.QuantumGroup
