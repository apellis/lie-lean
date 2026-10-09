/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.PropC

/-!
# Kashiwara's grand loop: the statements `D(r)`, `F(r)`, `G(r)`

* `D(r)` ([HK] Prop. 5.3.17): the classes of the `f̃_{i₁} ⋯ f̃_{iᵣ} v_λ` of a given weight are
  linearly independent in `L(λ)/ϖ L(λ)` (`GrandLoop.PropD`, `propD_zero`, `propD_succ`);
* [HK] Lemma 5.3.18: a vector of `L(λ)` of positive depth killed by all `ẽᵢ` modulo `ϖ` lies in
  `ϖ L(λ)` (`GrandLoop.mem_smul_lat_of_eK`), and `u ∈ V(λ)` with all `ẽᵢ u ∈ L(λ)` lies in `L(λ)`
  (`GrandLoop.mem_lat_of_eK`);
* `F(r)` ([HK] Prop. 5.3.19): `Ψ((L(λ₁) ⊗ L(λ₂))_{depth r}) ⊆ L(λ₁ + λ₂)` (`propF_succ`);
* `G(r)` ([HK] Prop. 5.3.21): `Ψ(B(λ₁) ⊗ B(λ₂)) ⊆ B(λ₁ + λ₂) ∪ {0}` (`propG_succ`).

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

variable (hvt hR A ϖ) in
/-- `D(r)`: classes of `f̃`-words of weight `λ - ν`, `|ν| = r`, that are pairwise distinct and
nonzero modulo `ϖ L(λ)` are linearly independent over `A/ϖA`. -/
def PropD (r : ℕ) : Prop :=
  ∀ (Λ : Dom R) (ν : I →₀ ℕ), ν.degree = r → ∀ S : Finset (List I),
    (∀ w ∈ S, wordWeight w = ν) → (∀ w ∈ S, fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ) →
    (∀ w₁ ∈ S, ∀ w₂ ∈ S, w₁ ≠ w₂ → fW hvt hR Λ w₁ - fW hvt hR Λ w₂ ∉ ϖ • lat hvt hR A Λ) →
    ∀ a : List I → A, ∑ w ∈ S, a w • fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ →
      ∀ w ∈ S, a w ∈ Ideal.span {ϖ}

section D

variable (hinj : Function.Injective (algebraMap A k)) (hϖv : algebraMap A k ϖ = v⁻¹)
include hinj hϖv

/-- `D(0)`. -/
theorem propD_zero : PropD hvt hR A ϖ 0 := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  intro Λ ν hν S hS _ _ a hsum w hw
  have hν0 : ν = 0 := by
    ext i
    have : ν i ≤ ν.degree := by
      rw [Finsupp.degree]
      by_cases hi : i ∈ ν.support
      · exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi
      · rw [Finsupp.notMem_support_iff.1 hi]; exact Nat.zero_le _
    simp; omega
  have hwords : ∀ w ∈ S, w = [] := fun w hw ↦ by
    have := congrArg Finsupp.degree (hS w hw)
    rw [degree_wordWeight, hν0] at this
    exact List.length_eq_zero_iff.1 (by simpa using this)
  have hS' : S = {[]} := by
    ext x
    simp only [Finset.mem_singleton]
    exact ⟨hwords x, fun h ↦ h ▸ (hwords w hw) ▸ hw⟩
  subst hS'
  obtain rfl := hwords w hw
  rw [Finset.sum_singleton, fW_nil] at hsum
  obtain ⟨z₀, hz₀, hz₀w, he⟩ := TensorModule.exists_smul_weight hϖ0 hsum
    (Submodule.smul_mem _ (algebraMap A k (a [])) (hwv_mem_wsp (R := R) (v := v) Λ))
  obtain ⟨c, rfl⟩ := exists_eq_smul_hwv hz₀ hz₀w
  refine Ideal.mem_span_singleton'.2 ⟨c, ?_⟩
  have h1 : (a [] - c * ϖ) • IrreducibleModule.hwv R v Λ.1 = 0 := by
    rw [sub_smul, mul_comm, mul_smul, ← he, sub_self]
  rw [← algebraMap_smul k, smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact (sub_eq_zero.1 (hinj (by rw [h1, map_zero]))).symm
  · exact absurd h1 (hwv_ne_zero hR (pow_ne_one_of_transcendental' hvt) Λ.1)

end D

/-! ### The key step: `ẽᵢ` on linear combinations of `B(λ)` -/

section Key

variable (hϖv : algebraMap A k ϖ = v⁻¹)
include hϖv

/-- **[HK] Prop. 5.3.17, key step**: if `Σ a_w ẽᵢ b_w ≡ 0` for pairwise distinct nonzero classes
`b_w` of depth `r + 1`, then `a_w ∈ ϖA` for every `w` beginning with `i`. -/
theorem coeff_mem_of_sum_eK {r : ℕ}
    (hB : PropB hvt hR A ϖ (r + 1)) (hC : PropC hvt hR A ϖ (r + 1)) (hD : PropD hvt hR A ϖ r)
    {Λ : Dom R} {ν : I →₀ ℕ} (hν : ν.degree = r + 1) (S : Finset (List I))
    (hS : ∀ w ∈ S, wordWeight w = ν) (hS0 : ∀ w ∈ S, fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ)
    (hSd : ∀ w₁ ∈ S, ∀ w₂ ∈ S, w₁ ≠ w₂ → fW hvt hR Λ w₁ - fW hvt hR Λ w₂ ∉ ϖ • lat hvt hR A Λ)
    (a : List I → A) (i : I)
    (h : ∑ w ∈ S, a w • eK hvt hR Λ i (fW hvt hR Λ w) ∈ ϖ • lat hvt hR A Λ) :
    ∀ u : List I, i :: u ∈ S → a (i :: u) ∈ Ideal.span {ϖ} := by
  classical
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  set hv' := pow_ne_one_of_transcendental' hvt
  intro u hu
  have hlen : ∀ w ∈ S, w.length = r + 1 := fun w hw ↦ by rw [← degree_wordWeight, hS w hw, hν]
  set T := S.filter fun w ↦ eK hvt hR Λ i (fW hvt hR Λ w) ∉ ϖ • lat hvt hR A Λ
  -- `i :: u ∈ T`
  have hu0 : eK hvt hR Λ i (fW hvt hR Λ (i :: u)) ∉ ϖ • lat hvt hR A Λ := by
    intro he
    have hulen : u.length + 1 = r + 1 := by simpa using hlen _ hu
    have hfu0 : fW hvt hR Λ u ∉ ϖ • lat hvt hR A Λ := fun hm ↦
      hS0 _ hu (by rw [fW_cons]; exact kashiwaraF_mem_smul_lat Λ i hm)
    have := (hC Λ i u (i :: u) hulen (hlen _ hu) hfu0 (hS0 _ hu)).1
      (by rw [fW_cons, sub_self]; exact zero_mem _)
    exact hfu0 (by simpa using add_mem this he)
  have huT : i :: u ∈ T := Finset.mem_filter.2 ⟨hu, hu0⟩
  -- the weight one step up
  obtain ⟨ν', hν'⟩ := exists_eq_add_single hR hv' Λ (i := i) (j := 1) (ν := ν)
    (by
      rw [one_smul, ← hS _ hu]
      exact kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ) i (fW_mem_wsp hvt hR Λ (i :: u)))
    (fun h0 ↦ hu0 (by rw [h0]; exact zero_mem _))
  have hdeg' : ν'.degree = r := by
    have := hν; rw [hν', map_add, Finsupp.degree_single] at this; omega
  have hew : ∀ w ∈ S, eK hvt hR Λ i (fW hvt hR Λ w) ∈ wsp Λ ν' := fun w hw ↦ by
    have := kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ) i (fW_mem_wsp hvt hR Λ w)
    rw [hS w hw] at this
    convert this using 2
    rw [hν', R.rootSum_add, R.rootSum_single, one_nsmul]; abel
  -- `ẽᵢ b_w ≡ b_{g w}` on `T`
  have hex : ∀ w ∈ T, ∃ w', eK hvt hR Λ i (fW hvt hR Λ w) - fW hvt hR Λ w' ∈
      ϖ • lat hvt hR A Λ := fun w hw ↦
    ((hB Λ w (hlen w (Finset.mem_filter.1 hw).1) i).resolve_left (Finset.mem_filter.1 hw).2)
  choose! g hg using hex
  have hg0 : ∀ w ∈ T, fW hvt hR Λ (g w) ∉ ϖ • lat hvt hR A Λ := fun w hw hm ↦
    (Finset.mem_filter.1 hw).2 (by simpa using add_mem (hg w hw) hm)
  have hgw : ∀ w ∈ T, wordWeight (g w) = ν' := fun w hw ↦
    wordWeight_eq_of_sub_mem hvt hR A ϖ Λ (hew w (Finset.mem_filter.1 hw).1)
      (Finset.mem_filter.1 hw).2 (hg w hw)
  have hglen : ∀ w ∈ T, (g w).length = r := fun w hw ↦ by
    rw [← degree_wordWeight, hgw w hw, hdeg']
  have hfg : ∀ w ∈ T, fK hvt hR Λ i (fW hvt hR Λ (g w)) - fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ :=
    fun w hw ↦ (hC Λ i (g w) w (by rw [hglen w hw]) (hlen w (Finset.mem_filter.1 hw).1)
      (hg0 w hw) (hS0 w (Finset.mem_filter.1 hw).1)).2
      (by have := neg_mem (hg w hw); rwa [neg_sub] at this)
  have hgd : ∀ w₁ ∈ T, ∀ w₂ ∈ T, w₁ ≠ w₂ →
      fW hvt hR Λ (g w₁) - fW hvt hR Λ (g w₂) ∉ ϖ • lat hvt hR A Λ := by
    intro w₁ h₁ w₂ h₂ hne hm
    refine hSd w₁ (Finset.mem_filter.1 h₁).1 w₂ (Finset.mem_filter.1 h₂).1 hne ?_
    have h3 := kashiwaraF_mem_smul_lat Λ i hm
    rw [map_sub] at h3
    have := add_mem (sub_mem h3 (hfg w₁ h₁)) (hfg w₂ h₂)
    convert this using 1
    abel
  have hinjg : Set.InjOn g T := fun w₁ h₁ w₂ h₂ he ↦ by
    by_contra hne
    exact hgd w₁ h₁ w₂ h₂ hne (by rw [he, sub_self]; exact zero_mem _)
  -- the sum over `T`
  have hsumT : ∑ w ∈ T, a w • fW hvt hR Λ (g w) ∈ ϖ • lat hvt hR A Λ := by
    have hsplit : ∑ w ∈ S, a w • eK hvt hR Λ i (fW hvt hR Λ w) =
        ∑ w ∈ T, a w • eK hvt hR Λ i (fW hvt hR Λ w) +
          ∑ w ∈ S.filter (fun w ↦ ¬ (eK hvt hR Λ i (fW hvt hR Λ w) ∉ ϖ • lat hvt hR A Λ)),
            a w • eK hvt hR Λ i (fW hvt hR Λ w) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    rw [hsplit] at h
    have h2 : ∑ w ∈ S.filter (fun w ↦ ¬ (eK hvt hR Λ i (fW hvt hR Λ w) ∉ ϖ • lat hvt hR A Λ)),
        a w • eK hvt hR Λ i (fW hvt hR Λ w) ∈ ϖ • lat hvt hR A Λ :=
      Submodule.sum_mem _ fun w hw ↦ Submodule.smul_of_tower_mem _ _
        (not_not.1 (Finset.mem_filter.1 hw).2)
    have h3 : ∑ w ∈ T, a w • (eK hvt hR Λ i (fW hvt hR Λ w) - fW hvt hR Λ (g w)) ∈
        ϖ • lat hvt hR A Λ :=
      Submodule.sum_mem _ fun w hw ↦ Submodule.smul_of_tower_mem _ _ (hg w hw)
    have := sub_mem (sub_mem h h2) h3
    simp only [smul_sub, Finset.sum_sub_distrib] at this
    convert this using 1
    abel
  -- apply `D(r)`
  set a' : List I → A := fun x ↦ a (Function.invFunOn g (T : Set (List I)) x)
  have ha' : ∀ w ∈ T, a' (g w) = a w := fun w hw ↦ by
    simp only [a']
    rw [hinjg.leftInvOn_invFunOn hw]
  have hsum' : ∑ x ∈ T.image g, a' x • fW hvt hR Λ x ∈ ϖ • lat hvt hR A Λ := by
    rw [Finset.sum_image hinjg]
    convert hsumT using 1
    exact Finset.sum_congr rfl fun w hw ↦ by rw [ha' w hw]
  have := hD Λ ν' hdeg' (T.image g)
    (fun x hx ↦ by obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx; exact hgw w hw)
    (fun x hx ↦ by obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx; exact hg0 w hw)
    (fun x₁ hx₁ x₂ hx₂ hne ↦ by
      obtain ⟨w₁, h₁, rfl⟩ := Finset.mem_image.1 hx₁
      obtain ⟨w₂, h₂, rfl⟩ := Finset.mem_image.1 hx₂
      exact hgd w₁ h₁ w₂ h₂ fun he ↦ hne (he ▸ rfl))
    a' hsum' (g (i :: u)) (Finset.mem_image_of_mem g huT)
  rwa [ha' _ huT] at this

/-- **`D(r + 1)`** ([HK] Prop. 5.3.17). -/
theorem propD_succ {r : ℕ} (hA : ∀ s ≤ r + 1, PropA hvt hR A s)
    (hB : PropB hvt hR A ϖ (r + 1)) (hC : PropC hvt hR A ϖ (r + 1)) (hD : PropD hvt hR A ϖ r) :
    PropD hvt hR A ϖ (r + 1) := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  intro Λ ν hν S hS hS0 hSd a hsum w hw
  obtain ⟨i, u, rfl⟩ : ∃ i u, w = i :: u := by
    rcases w with _ | ⟨i, u⟩
    · have := congrArg Finsupp.degree (hS _ hw)
      rw [degree_wordWeight, hν] at this
      simp at this
    · exact ⟨i, u, rfl⟩
  have hsw : ∑ w ∈ S, a w • fW hvt hR Λ w ∈ wsp Λ ν :=
    Submodule.sum_mem _ fun w hw ↦ Submodule.smul_of_tower_mem _ _
      (hS w hw ▸ fW_mem_wsp hvt hR Λ w)
  have he := localE_smul hA Λ hν i 0 hϖ0 hsum (by simpa using hsw)
  rw [map_sum] at he
  simp only [LinearMap.map_smul_of_tower] at he
  exact coeff_mem_of_sum_eK hϖv hB hC hD hν S hS hS0 hSd a i he u hw

end Key

/-! ### [HK] Lemma 5.3.18 -/

section Lemma5318

variable (hvt hR A ϖ) in
/-- Representatives of the distinct nonzero classes of a finite set of words modulo `ϖ L(λ)`. -/
lemma exists_reps (Λ : Dom R) (W : Finset (List I)) :
    ∃ S ⊆ W, (∀ s ∈ S, fW hvt hR Λ s ∉ ϖ • lat hvt hR A Λ) ∧
      (∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ →
        fW hvt hR Λ s₁ - fW hvt hR Λ s₂ ∉ ϖ • lat hvt hR A Λ) ∧
      ∀ w ∈ W, fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ ∨
        ∃ s ∈ S, fW hvt hR Λ w - fW hvt hR Λ s ∈ ϖ • lat hvt hR A Λ := by
  classical
  induction W using Finset.induction_on with
  | empty => exact ⟨∅, le_rfl, by simp, by simp, by simp⟩
  | insert w W hwW ih =>
    obtain ⟨S, hSW, hS0, hSd, hcov⟩ := ih
    by_cases h : fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ ∨
        ∃ s ∈ S, fW hvt hR Λ w - fW hvt hR Λ s ∈ ϖ • lat hvt hR A Λ
    · refine ⟨S, hSW.trans (Finset.subset_insert _ _), hS0, hSd, fun x hx ↦ ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact h
      · exact hcov x hx
    push Not at h
    refine ⟨insert w S, Finset.insert_subset_insert _ hSW, fun s hs ↦ ?_, fun s₁ h₁ s₂ h₂ hne ↦ ?_,
      fun x hx ↦ ?_⟩
    · rcases Finset.mem_insert.1 hs with rfl | hs
      · exact h.1
      · exact hS0 s hs
    · by_cases e₁ : s₁ = w
      · subst e₁
        exact h.2 s₂ (Finset.mem_of_mem_insert_of_ne h₂ (Ne.symm hne))
      by_cases e₂ : s₂ = w
      · subst e₂
        intro hm
        exact h.2 s₁ (Finset.mem_of_mem_insert_of_ne h₁ e₁)
          (by have := neg_mem hm; rwa [neg_sub] at this)
      exact hSd s₁ (Finset.mem_of_mem_insert_of_ne h₁ e₁) s₂
        (Finset.mem_of_mem_insert_of_ne h₂ e₂) hne
    · rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Or.inr ⟨x, Finset.mem_insert_self _ _, by rw [sub_self]; exact zero_mem _⟩
      · rcases hcov x hx with h' | ⟨s, hs, h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨s, Finset.mem_insert_of_mem hs, h'⟩

variable [Finite I] (hϖv : algebraMap A k ϖ = v⁻¹)
include hϖv

/-- **[HK] Lemma 5.3.18 (1)**: `u ∈ L(λ)` of depth `r + 1` with `ẽᵢ u ∈ ϖ L(λ)` for all `i` lies in
`ϖ L(λ)`. -/
theorem mem_smul_lat_of_eK {r : ℕ} (hA : ∀ s ≤ r + 1, PropA hvt hR A s)
    (hB : PropB hvt hR A ϖ (r + 1)) (hC : PropC hvt hR A ϖ (r + 1)) (hD : PropD hvt hR A ϖ r)
    {Λ : Dom R} {ν : I →₀ ℕ} (hν : ν.degree = r + 1) {u : IrreducibleModule R v Λ.1}
    (hu : u ∈ lat hvt hR A Λ) (huw : u ∈ wsp Λ ν)
    (he : ∀ i, eK hvt hR Λ i u ∈ ϖ • lat hvt hR A Λ) : u ∈ ϖ • lat hvt hR A Λ := by
  classical
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨S, hSW, hS0, hSd, hcov⟩ := exists_reps hvt hR A ϖ Λ (finite_words ν).toFinset
  have hSν : ∀ s ∈ S, wordWeight s = ν := fun s hs ↦ by
    simpa using hSW hs
  set N := Submodule.span A (fW hvt hR Λ '' (S : Set (List I))) ⊔ ϖ • lat hvt hR A Λ
  have hu' : u ∈ N := by
    refine mem_of_fW_mem Λ ν N (fun w hw ↦ ?_) hu huw
    rcases hcov w (by simpa using hw) with h' | ⟨s, hs, h'⟩
    · exact Submodule.mem_sup_right h'
    · have := Submodule.add_mem_sup
        (Submodule.subset_span (Set.mem_image_of_mem (fW hvt hR Λ) (Finset.mem_coe.2 hs))) h'
      rwa [add_sub_cancel] at this
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu'
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination A).1 hy
  have hlS : ∀ x : IrreducibleModule R v Λ.1 →ₗ[k] IrreducibleModule R v Λ.1,
      x (Finsupp.linearCombination A (fW hvt hR Λ) l) = ∑ s ∈ S, l s • x (fW hvt hR Λ s) := by
    intro x
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset l hl _ (by simp),
      map_sum]
    simp only [LinearMap.map_smul_of_tower]
  have hyw : Finsupp.linearCombination A (fW hvt hR Λ) l ∈ wsp Λ ν := by
    have := hlS LinearMap.id
    simp only [LinearMap.id_apply] at this
    rw [this]
    exact Submodule.sum_mem _ fun s hs ↦ Submodule.smul_of_tower_mem _ _
      (hSν s hs ▸ fW_mem_wsp hvt hR Λ s)
  have hzw : z ∈ wsp Λ ν := by
    have := sub_mem huw hyw
    rwa [add_sub_cancel_left] at this
  have hl0 : ∀ s ∈ S, l s ∈ Ideal.span {ϖ} := by
    intro s hs
    obtain ⟨i, u', rfl⟩ : ∃ i u', s = i :: u' := by
      rcases s with _ | ⟨i, u'⟩
      · have := congrArg Finsupp.degree (hSν _ hs)
        rw [degree_wordWeight, hν] at this
        simp at this
      · exact ⟨i, u', rfl⟩
    have h1 := he i
    have h2 := localE_smul hA Λ hν i 0 hϖ0 hz (by simpa using hzw)
    rw [map_add] at h1
    have h3 := sub_mem h1 h2
    rw [add_sub_cancel_right, hlS] at h3
    exact coeff_mem_of_sum_eK hϖv hB hC hD hν S hSν hS0 hSd l i h3 u' hs
  have hyL : Finsupp.linearCombination A (fW hvt hR Λ) l ∈ ϖ • lat hvt hR A Λ := by
    have := hlS LinearMap.id
    simp only [LinearMap.id_apply] at this
    rw [this]
    refine Submodule.sum_mem _ fun s hs ↦ ?_
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hl0 s hs)
    rw [← hc, mul_comm, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _
      (Submodule.smul_mem _ _ (IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A s))
  exact add_mem hyL hz

variable (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
include hk

/-- **[HK] Lemma 5.3.18 (2)**: `u ∈ V(λ)` of depth `r + 1` with `ẽᵢ u ∈ L(λ)` for all `i` lies in
`L(λ)`. -/
theorem mem_lat_of_eK {r : ℕ} (hA : ∀ s ≤ r + 1, PropA hvt hR A s)
    (hB : PropB hvt hR A ϖ (r + 1)) (hC : PropC hvt hR A ϖ (r + 1)) (hD : PropD hvt hR A ϖ r)
    {Λ : Dom R} {ν : I →₀ ℕ} (hν : ν.degree = r + 1) {u : IrreducibleModule R v Λ.1}
    (huw : u ∈ wsp Λ ν) (he : ∀ i, eK hvt hR Λ i u ∈ lat hvt hR A Λ) :
    u ∈ lat hvt hR A Λ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hspan : u ∈ Submodule.span k (lat hvt hR A Λ : Set (IrreducibleModule R v Λ.1)) := by
    change u ∈ Submodule.span k (Submodule.span A (Set.range (IrreducibleModule.fWord hR
      (pow_ne_one_of_transcendental' hvt) Λ.2)) : Set (IrreducibleModule R v Λ.1))
    rw [Submodule.span_span_of_tower, IrreducibleModule.span_fWord]
    trivial
  obtain ⟨N, hN⟩ := DualLattice.exists_pow_smul_mem hk hspan
  induction N with
  | zero => simpa using hN
  | succ N ih =>
    refine ih ?_
    have h1 := mem_smul_lat_of_eK hϖv hA hB hC hD hν hN
      (Submodule.smul_of_tower_mem _ _ huw) fun i ↦ by
        rw [LinearMap.map_smul_of_tower, pow_succ', mul_smul]
        exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.smul_mem _ _ (he i))
    obtain ⟨y, hy, hyu⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
    have : ϖ ^ N • u = y := by
      refine smul_right_injective _ hϖ0 ?_
      simp only [algebraMap_smul]
      rw [hyu, smul_smul, ← pow_succ']
    rw [this]
    exact hy

end Lemma5318

/-! ### `F(r)` and `G(r)` -/

section FG

variable [Finite I] [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)

omit [IsLocalRing A] in
/-- `Ψ` preserves weights. -/
lemma tensorProj_mem_wsp {Λ₁ Λ₂ : Dom R} {ν : I →₀ ℕ} {z : TM v Λ₁ Λ₂}
    (hzw : z ∈ weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum ν)) :
    tensorProj hvt hR Λ₁.2 Λ₂.2 z ∈ wsp (Λ₁ + Λ₂) ν := fun μ ↦ by
  rw [← LinearMap.map_smul, hzw μ, LinearMap.map_smul_of_tower]
  rfl

include hϖ hϖv

omit [Finite I] in
/-- The weight of `ẽᵢ z` one step above depth `r + 1`. -/
lemma exists_eT_weight {Λ₁ Λ₂ : Dom R} (i : I) {r : ℕ} {ν : I →₀ ℕ} (hν : ν.degree = r + 1)
    (hA : ∀ s ≤ r + 1, PropA hvt hR A s) {z : TM v Λ₁ Λ₂} (hz : z ∈ LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum ν))
    (h0 : eT hvt hR Λ₁ Λ₂ i z ≠ 0) :
    ∃ ν'', ν''.degree = r ∧ eT hvt hR Λ₁ Λ₂ i z ∈
      weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum ν'') := by
  have hew := kashiwaraE_mem_weightSpace (pow_ne_one_of_transcendental' hvt)
    (isIntT hvt hR Λ₁ Λ₂) i hzw
  obtain ⟨ν'', hν''⟩ := exists_rootSum_of_LL (eT_mem_LL hϖ hϖv hA i hν hz hzw) hew h0
  refine ⟨ν'', ?_, hν'' ▸ hew⟩
  have h1 : R.rootSum (ν'' + Finsupp.single i 1) = R.rootSum ν := by
    rw [R.rootSum_add, R.rootSum_single, one_nsmul, ← sub_eq_zero, ← sub_eq_zero.2 hν'']
    abel
  have := congrArg Finsupp.degree (LusztigCartanDatum.RootDatum.rootSum_injective hR h1)
  rw [map_add, Finsupp.degree_single, hν] at this
  omega

/-- `Ψ(ẽᵢ z) ∈ L` for `z` of depth `r + 1`, from `F(r)`. -/
lemma tensorProj_eT_mem {Λ₁ Λ₂ : Dom R} (i : I) {r : ℕ} {ν : I →₀ ℕ} (hν : ν.degree = r + 1)
    (hA : ∀ s ≤ r + 1, PropA hvt hR A s) (hF : PropF hvt hR A r) {z : TM v Λ₁ Λ₂}
    (hz : z ∈ LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum ν)) :
    tensorProj hvt hR Λ₁.2 Λ₂.2 (eT hvt hR Λ₁ Λ₂ i z) ∈ lat hvt hR A (Λ₁ + Λ₂) := by
  by_cases h0 : eT hvt hR Λ₁ Λ₂ i z = 0
  · rw [h0, map_zero]; exact zero_mem _
  obtain ⟨ν'', hd, hw⟩ := exists_eT_weight hϖ hϖv i hν hA hz hzw h0
  exact hF Λ₁ Λ₂ ν'' hd _ (eT_mem_LL hϖ hϖv hA i hν hz hzw) hw

/-- `Ψ(ẽᵢ z) ∈ ϖ L` if `ẽᵢ z ∈ ϖ (L ⊗ L)`, for `z` of depth `r + 1`, from `F(r)`. -/
lemma tensorProj_eT_mem_smul {Λ₁ Λ₂ : Dom R} (i : I) {r : ℕ} {ν : I →₀ ℕ}
    (hν : ν.degree = r + 1) (hA : ∀ s ≤ r + 1, PropA hvt hR A s) (hF : PropF hvt hR A r)
    {z : TM v Λ₁ Λ₂} (hz : z ∈ LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum ν))
    (hez : eT hvt hR Λ₁ Λ₂ i z ∈ ϖ • LL hvt hR A Λ₁ Λ₂) :
    tensorProj hvt hR Λ₁.2 Λ₂.2 (eT hvt hR Λ₁ Λ₂ i z) ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂) := by
  by_cases h0 : eT hvt hR Λ₁ Λ₂ i z = 0
  · rw [h0, map_zero]; exact zero_mem _
  obtain ⟨ν'', hd, hw⟩ := exists_eT_weight hϖ hϖv i hν hA hz hzw h0
  exact tensorProj_mem_smul_of hϖv (fun z' hz' hz'w ↦ hF Λ₁ Λ₂ ν'' hd z' hz' hz'w) hez hw

variable (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
include hk

/-- **`F(r + 1)`** ([HK] Prop. 5.3.19). -/
theorem propF_succ {r : ℕ} (hA : ∀ s ≤ r + 1, PropA hvt hR A s)
    (hB : PropB hvt hR A ϖ (r + 1)) (hC : PropC hvt hR A ϖ (r + 1)) (hD : PropD hvt hR A ϖ r)
    (hF : PropF hvt hR A r) : PropF hvt hR A (r + 1) := by
  intro Λ₁ Λ₂ ν hν z hz hzw
  refine mem_lat_of_eK hϖv hk hA hB hC hD hν (tensorProj_mem_wsp hzw) fun i ↦ ?_
  rw [← tensorProj_eT]
  exact tensorProj_eT_mem hϖ hϖv i hν hA hF hz hzw

omit hk in
/-- **`G(r + 1)`** ([HK] Prop. 5.3.21). -/
theorem propG_succ {r : ℕ} (hA : ∀ s ≤ r + 1, PropA hvt hR A s)
    (hB : ∀ s ≤ r + 1, PropB hvt hR A ϖ s) (hC : ∀ s ≤ r + 1, PropC hvt hR A ϖ s)
    (hD : PropD hvt hR A ϖ r) (hF : PropF hvt hR A r) (hF' : PropF hvt hR A (r + 1))
    (hG : PropG hvt hR A ϖ r) : PropG hvt hR A ϖ (r + 1) := by
  classical
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  set hv' := pow_ne_one_of_transcendental' hvt
  intro Λ₁ Λ₂ w₁ w₂ hw
  set x := fW hvt hR Λ₁ w₁
  set y := fW hvt hR Λ₂ w₂
  set z := TensorModule.mk (IrreducibleModule R v Λ₁.1) (IrreducibleModule R v Λ₂.1) (x ⊗ₜ[k] y)
  set ν := wordWeight w₁ + wordWeight w₂
  have hν : ν.degree = r + 1 := by rw [map_add, degree_wordWeight, degree_wordWeight, hw]
  have hzL : z ∈ LL hvt hR A Λ₁ Λ₂ := fW_tmul_mem_LL Λ₁ Λ₂ w₁ w₂
  have hzw : z ∈ weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum ν) :=
    fW_tmul_mem_weightSpace Λ₁ Λ₂ w₁ w₂
  have hΨL := hF' Λ₁ Λ₂ ν hν z hzL hzw
  by_cases hall : ∀ i, eT hvt hR Λ₁ Λ₂ i z ∈ ϖ • LL hvt hR A Λ₁ Λ₂
  · left
    refine mem_smul_lat_of_eK hϖv hA (hB (r + 1) le_rfl) (hC (r + 1) le_rfl) hD hν hΨL
      (tensorProj_mem_wsp hzw) fun i ↦ ?_
    rw [← tensorProj_eT]
    exact tensorProj_eT_mem_smul hϖ hϖv i hν hA hF hzL hzw (hall i)
  push Not at hall
  obtain ⟨i, hi⟩ := hall
  have hfe := fT_eT_tmul_sub hϖ hϖv (d := r) (e := r + 1) hA hB hC i (by omega) (by omega) hw hi
  have hxL : x ∈ lat hvt hR A Λ₁ := IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁
  have hyL : y ∈ lat hvt hR A Λ₂ := IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂
  have hsmul : z ∈ ϖ • LL hvt hR A Λ₁ Λ₂ → False := fun h ↦
    hi (eT_mem_smul_LL hϖ hϖv hA i hν h hzw)
  have hx0 : x ∉ ϖ • lat hvt hR A Λ₁ := fun h ↦ hsmul (tmul_mem_smul_left h hyL)
  have hy0 : y ∉ ϖ • lat hvt hR A Λ₂ := fun h ↦ hsmul (tmul_mem_smul_right hxL h)
  -- `ẽᵢ z ≡ f̃_a v ⊗ f̃_b v`
  have hpair : ∃ a b : List I, wordWeight a + wordWeight b + Finsupp.single i 1 = ν ∧
      eT hvt hR Λ₁ Λ₂ i z - TensorModule.mk _ _ (fW hvt hR Λ₁ a ⊗ₜ[k] fW hvt hR Λ₂ b) ∈
        ϖ • LL hvt hR A Λ₁ Λ₂ := by
    obtain ⟨k₁, a, uu, hxs⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
      (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ₁ i (degree_wordWeight w₁) hxL
      (fW_mem_wsp hvt hR Λ₁ w₁) (w := w₁) (by simp [x]) hx0
    obtain ⟨k₂, b, u', hys⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
      (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ₂ i (degree_wordWeight w₂) hyL
      (fW_mem_wsp hvt hR Λ₂ w₂) (w := w₂) (by simp [y]) hy0
    have hrule := eT_tmul hϖ hϖv (fun s hs ↦ hA s (by omega)) (fun s hs ↦ hA s (by omega))
      (degree_wordWeight w₁) (degree_wordWeight w₂) hxs hys
    split_ifs at hrule with hc
    · have hey0 : eK hvt hR Λ₂ i y ∉ ϖ • lat hvt hR A Λ₂ := fun h ↦
        hi (by simpa using add_mem hrule (tmul_mem_smul_right hxL h))
      rcases hB _ (by omega) Λ₂ w₂ rfl i with h | ⟨w₂', h⟩
      · exact absurd h hey0
      have hew := kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ₂) i (fW_mem_wsp hvt hR Λ₂ w₂)
      obtain ⟨ν₂', hν₂'⟩ := exists_eq_add_single hR hv' Λ₂ (i := i) (j := 1)
        (ν := wordWeight w₂) (by rw [one_smul]; exact hew)
        (fun h0 ↦ hey0 (by rw [h0]; exact zero_mem _))
      have hwt := wordWeight_eq_of_sub_mem hvt hR A ϖ Λ₂ (ν := ν₂')
        (by convert hew using 2; rw [hν₂', R.rootSum_add, R.rootSum_single, one_nsmul]; abel)
        hey0 h
      refine ⟨w₁, w₂', by rw [hwt, add_assoc, ← hν₂'], ?_⟩
      have := add_mem hrule (tmul_mem_smul_right hxL h)
      convert this using 1
      rw [tmul_sub, map_sub]
      abel
    · have hex0 : eK hvt hR Λ₁ i x ∉ ϖ • lat hvt hR A Λ₁ := fun h ↦
        hi (by simpa using add_mem hrule (tmul_mem_smul_left h hyL))
      rcases hB _ (by omega) Λ₁ w₁ rfl i with h | ⟨w₁', h⟩
      · exact absurd h hex0
      have hew := kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ₁) i (fW_mem_wsp hvt hR Λ₁ w₁)
      obtain ⟨ν₁', hν₁'⟩ := exists_eq_add_single hR hv' Λ₁ (i := i) (j := 1)
        (ν := wordWeight w₁) (by rw [one_smul]; exact hew)
        (fun h0 ↦ hex0 (by rw [h0]; exact zero_mem _))
      have hwt := wordWeight_eq_of_sub_mem hvt hR A ϖ Λ₁ (ν := ν₁')
        (by convert hew using 2; rw [hν₁', R.rootSum_add, R.rootSum_single, one_nsmul]; abel)
        hex0 h
      refine ⟨w₁', w₂, by change _ = wordWeight w₁ + wordWeight w₂; rw [hwt, hν₁']; abel, ?_⟩
      have := add_mem hrule (tmul_mem_smul_left h hyL)
      convert this using 1
      rw [sub_tmul, map_sub]
      abel
  obtain ⟨a, b, hab, hsub⟩ := hpair
  have hdab : (wordWeight a + wordWeight b).degree = r := by
    have := hν; rw [← hab, map_add, Finsupp.degree_single] at this; omega
  have hEw : eT hvt hR Λ₁ Λ₂ i z - TensorModule.mk _ _ (fW hvt hR Λ₁ a ⊗ₜ[k] fW hvt hR Λ₂ b) ∈
      weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum (wordWeight a + wordWeight b)) := by
    refine sub_mem ?_ (fW_tmul_mem_weightSpace Λ₁ Λ₂ a b)
    convert kashiwaraE_mem_weightSpace hv' (isIntT hvt hR Λ₁ Λ₂) i hzw using 2
    rw [← hab]; simp only [R.rootSum_add, R.rootSum_single, one_nsmul]; abel
  have h1 := tensorProj_mem_smul_of hϖv
    (fun z' hz' hz'w ↦ hF Λ₁ Λ₂ _ hdab z' hz' hz'w) hsub hEw
  rw [map_sub] at h1
  have hfew : fT hvt hR Λ₁ Λ₂ i (eT hvt hR Λ₁ Λ₂ i z) - z ∈
      weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum ν) := by
    refine sub_mem ?_ hzw
    have := kashiwaraF_mem_weightSpace hv' (isIntT hvt hR Λ₁ Λ₂) i
      (kashiwaraE_mem_weightSpace hv' (isIntT hvt hR Λ₁ Λ₂) i hzw)
    rwa [add_sub_cancel_right] at this
  have h2 := tensorProj_mem_smul_of hϖv (fun z' hz' hz'w ↦ hF' Λ₁ Λ₂ ν hν z' hz' hz'w) hfe hfew
  rw [map_sub, map_kashiwaraF hv' (isIntT hvt hR Λ₁ Λ₂) i (isInt hvt hR (Λ₁ + Λ₂))] at h2
  have h3 := kashiwaraF_mem_smul_lat (Λ₁ + Λ₂) i h1
  rw [map_sub] at h3
  rcases hG Λ₁ Λ₂ a b (by rw [← degree_wordWeight, ← degree_wordWeight, ← map_add, hdab]) with
    h4 | ⟨w, h4⟩
  · left
    have h5 := kashiwaraF_mem_smul_lat (Λ₁ + Λ₂) i h4
    have := sub_mem (add_mem h3 h5) h2
    convert this using 1
    abel
  · right
    refine ⟨i :: w, ?_⟩
    have h5 := kashiwaraF_mem_smul_lat (Λ₁ + Λ₂) i h4
    rw [map_sub, ← fW_cons] at h5
    have := sub_mem (add_mem h3 h5) h2
    convert this using 1
    abel

end FG

end GrandLoop

end LieLean.QuantumGroup
