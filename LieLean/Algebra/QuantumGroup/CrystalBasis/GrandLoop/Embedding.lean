/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Tensor

/-!
# Kashiwara's grand loop: `ẽᵢ`, `f̃ᵢ` on `L(λ₁) ⊗ L(λ₂)` and the statement `E(r)`

* `ẽᵢ`, `f̃ᵢ` preserve `L(λ₁) ⊗ L(λ₂)` on weights of depth `d` once `A` holds up to depth `d`
  (`QuantumGroup.GrandLoop.fT_mem_LL`, `QuantumGroup.GrandLoop.eT_mem_LL`; [HK] Lemma 5.3.2 (1)).
* `E(r)`: `Φ_{λ₁,λ₂} (L(λ₁ + λ₂)_{depth r}) ⊆ L(λ₁) ⊗ L(λ₂)` (`QuantumGroup.GrandLoop.PropE`),
  proved from `E(r - 1)` and `A` up to depth `r - 1` (`QuantumGroup.GrandLoop.propE_succ`;
  [HK] Prop. 5.3.3).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
-/

open Finset Pointwise TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

namespace TensorModule

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁]
  [AddCommGroup M₂] [Module k M₂] [Module (QuantumGroup R v) M₂]
  [IsScalarTower k (QuantumGroup R v) M₂]
  (h₁ : IsIntegrable R v M₁) (h₂ : IsIntegrable R v M₂)
  {A : Type*} [CommRing A] [Algebra A k] [Module A M₁] [IsScalarTower A k M₁]
  [Module A M₂] [IsScalarTower A k M₂] {L₁ : Submodule A M₁} {L₂ : Submodule A M₂}

omit [IsScalarTower A k M₂] in
/-- The weight-`μ` component of an element of `L₁ ⊗ L₂` lies in every `A`-submodule containing the
`x ⊗ y` with `x ∈ L₁ ∩ M₁^a`, `y ∈ L₂ ∩ M₂^b`, `a + b = μ` (for graded `L₁`, `L₂`). -/
theorem weightSetProj_singleton_mem_of (hL₁ : ∀ S, ∀ m ∈ L₁, weightSetProj hv h₁ S m ∈ L₁)
    (hL₂ : ∀ S, ∀ m ∈ L₂, weightSetProj hv h₂ S m ∈ L₂) (μ : Y →+ ℤ)
    (N : Submodule A (TensorModule k M₁ M₂))
    (hN : ∀ a b : Y →+ ℤ, a + b = μ → ∀ x ∈ L₁, x ∈ weightSpace R v M₁ a → ∀ y ∈ L₂,
      y ∈ weightSpace R v M₂ b → mk M₁ M₂ (x ⊗ₜ[k] y) ∈ N)
    {z : TensorModule k M₁ M₂} (hz : z ∈ lattice k A L₁ L₂) :
    weightSetProj hv (isIntegrable h₁ h₂) {μ} z ∈ N := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    beta_reduce
    obtain ⟨s, hs, hsw⟩ := exists_sum_weightSetProj hv h₁ x
    obtain ⟨s', hs', hsw'⟩ := exists_sum_weightSetProj hv h₂ y
    have e : mk M₁ M₂ (x ⊗ₜ[k] y) = ∑ Λ ∈ s, ∑ Λ' ∈ s',
        mk M₁ M₂ (weightSetProj hv h₁ {Λ} x ⊗ₜ[k] weightSetProj hv h₂ {Λ'} y) := by
      conv_lhs => rw [← hs, ← hs']
      simp only [sum_tmul, tmul_sum, map_sum]
      exact Finset.sum_comm
    rw [e, map_sum]
    refine Submodule.sum_mem _ fun Λ _ ↦ ?_
    rw [map_sum]
    refine Submodule.sum_mem _ fun Λ' _ ↦ ?_
    rw [weightSetProj_of_mem hv (isIntegrable h₁ h₂) _ (tmul_mem_weightSpace (hsw Λ) (hsw' Λ'))]
    split_ifs with h
    · exact hN Λ Λ' h _ (hL₁ _ _ hx) (hsw Λ) _ (hL₂ _ _ hy) (hsw' Λ')
    · exact zero_mem _
  | zero => simp
  | add z z' _ _ h h' => rw [map_add]; exact add_mem h h'
  | smul a z _ h => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a h

end TensorModule

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k]

section Stable

variable [IsLocalRing A] {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹) {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s) {Λ₁ Λ₂ : Dom R}
  (i : I) {ν : I →₀ ℕ} (hν : ν.degree = d)
include hϖ hϖv hA hν

/-- The pure tensors of weight vectors of `L(λ₁) ⊗ L(λ₂)` of total depth `d` are preserved by `f̃ᵢ`
and `ẽᵢ` (given `A` up to depth `d`). -/
lemma kashiwara_tmul_mem {a b : Y →+ ℤ} (hab : a + b = Λ₁.1 + Λ₂.1 - R.rootSum ν)
    {x : IrreducibleModule R v Λ₁.1} (hx : x ∈ lat hvt hR A Λ₁) (hxw : x ∈ weightSpace R v _ a)
    {y : IrreducibleModule R v Λ₂.1} (hy : y ∈ lat hvt hR A Λ₂) (hyw : y ∈ weightSpace R v _ b) :
    fT hvt hR Λ₁ Λ₂ i (TensorModule.mk _ _ (x ⊗ₜ[k] y)) ∈ LL hvt hR A Λ₁ Λ₂ ∧
      eT hvt hR Λ₁ Λ₂ i (TensorModule.mk _ _ (x ⊗ₜ[k] y)) ∈ LL hvt hR A Λ₁ Λ₂ := by
  by_cases h0 : x = 0 ∨ y = 0
  · rcases h0 with h0 | h0 <;> simp [h0]
  push Not at h0
  obtain ⟨ν₁, rfl⟩ :=
    IrreducibleModule.exists_eq_sub_rootSum (pow_ne_one_of_transcendental' hvt) hxw h0.1
  obtain ⟨ν₂, rfl⟩ :=
    IrreducibleModule.exists_eq_sub_rootSum (pow_ne_one_of_transcendental' hvt) hyw h0.2
  have hνν : ν = ν₁ + ν₂ := by
    refine LusztigCartanDatum.RootDatum.rootSum_injective hR ?_
    rw [R.rootSum_add]
    have := congrArg (fun μ ↦ Λ₁.1 + Λ₂.1 - μ) hab
    simp only [sub_sub_cancel] at this
    rw [← this]
    abel
  have h1 : ν₁.degree ≤ d := by rw [← hν, hνν, map_add]; omega
  have h2 : ν₂.degree ≤ d := by rw [← hν, hνν, map_add]; omega
  have hA₁ : ∀ s ≤ ν₁.degree, PropA hvt hR A s := fun s hs ↦ hA s (by omega)
  have hA₂ : ∀ s ≤ ν₂.degree, PropA hvt hR A s := fun s hs ↦ hA s (by omega)
  exact ⟨TensorModule.kashiwaraF_tmul_mem _ _ _ i (fun _ hy ↦ kashiwaraF_mem_lat Λ₁ i hy)
      (fun _ hy ↦ kashiwaraF_mem_lat Λ₂ i hy) (localE hA₁ Λ₁ rfl i) (localE hA₂ Λ₂ rfl i) hϖ
      hϖv hx hxw hy hyw,
    TensorModule.kashiwaraE_tmul_mem _ _ _ i (fun _ hy ↦ kashiwaraF_mem_lat Λ₁ i hy)
      (fun _ hy ↦ kashiwaraF_mem_lat Λ₂ i hy) (localE hA₁ Λ₁ rfl i) (localE hA₂ Λ₂ rfl i) hϖ
      hϖv hx hxw hy hyw⟩

/-- `f̃ᵢ` preserves `L(λ₁) ⊗ L(λ₂)` in depth `d` ([HK] Lemma 5.3.2 (1)). -/
theorem fT_mem_LL {z : TM v Λ₁ Λ₂} (hz : z ∈ LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν)) :
    fT hvt hR Λ₁ Λ₂ i z ∈ LL hvt hR A Λ₁ Λ₂ := by
  classical
  have hP := TensorModule.weightSetProj_singleton_mem_of _ (isInt hvt hR Λ₁) (isInt hvt hR Λ₂)
    (fun S _ hm ↦ weightSetProj_mem_lat hvt hR A Λ₁ S hm)
    (fun S _ hm ↦ weightSetProj_mem_lat hvt hR A Λ₂ S hm) (Λ₁.1 + Λ₂.1 - R.rootSum ν)
    ((LL hvt hR A Λ₁ Λ₂).comap ((fT hvt hR Λ₁ Λ₂ i).restrictScalars A))
    (fun a b hab x hx hxw y hy hyw ↦
      (kashiwara_tmul_mem hϖ hϖv hA i hν hab hx hxw hy hyw).1) hz
  rw [weightSetProj_of_mem _ _ _ hzw] at hP
  simpa using hP

/-- `ẽᵢ` preserves `L(λ₁) ⊗ L(λ₂)` in depth `d` ([HK] Lemma 5.3.2 (1)). -/
theorem eT_mem_LL {z : TM v Λ₁ Λ₂} (hz : z ∈ LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν)) :
    eT hvt hR Λ₁ Λ₂ i z ∈ LL hvt hR A Λ₁ Λ₂ := by
  classical
  have hP := TensorModule.weightSetProj_singleton_mem_of _ (isInt hvt hR Λ₁) (isInt hvt hR Λ₂)
    (fun S _ hm ↦ weightSetProj_mem_lat hvt hR A Λ₁ S hm)
    (fun S _ hm ↦ weightSetProj_mem_lat hvt hR A Λ₂ S hm) (Λ₁.1 + Λ₂.1 - R.rootSum ν)
    ((LL hvt hR A Λ₁ Λ₂).comap ((eT hvt hR Λ₁ Λ₂ i).restrictScalars A))
    (fun a b hab x hx hxw y hy hyw ↦
      (kashiwara_tmul_mem hϖ hϖv hA i hν hab hx hxw hy hyw).2) hz
  rw [weightSetProj_of_mem _ _ _ hzw] at hP
  simpa using hP

end Stable

/-- An `A`-submodule containing the `f̃_w v_λ` of weight `λ - ν` contains `L(λ)_{λ-ν}`. -/
lemma mem_of_fW_mem (Λ : Dom R) (ν : I →₀ ℕ) (N : Submodule A (IrreducibleModule R v Λ.1))
    (hN : ∀ w : List I, LusztigF.wordWeight w = ν → fW hvt hR Λ w ∈ N)
    {x : IrreducibleModule R v Λ.1} (hx : x ∈ lat hvt hR A Λ) (hxw : x ∈ wsp Λ ν) : x ∈ N := by
  classical
  set P := weightSetProj (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ)
    {Λ.1 - R.rootSum ν}
  have key : ∀ y ∈ lat hvt hR A Λ, P y ∈ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      rw [weightSetProj_of_mem _ _ _ (fW_mem_wsp hvt hR Λ w)]
      split_ifs with h
      · exact hN w (LusztigCartanDatum.RootDatum.rootSum_injective hR
          (sub_right_injective (Set.mem_singleton_iff.1 h)))
      · exact zero_mem _
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c ha
  have := key x hx
  rw [weightSetProj_of_mem _ _ _ hxw] at this
  simpa using this

section PropE

variable [Finite I] (hvt hR A)

/-- `E(r)`: `Φ_{λ₁,λ₂}(L(λ₁ + λ₂)_{depth r}) ⊆ L(λ₁) ⊗ L(λ₂)`. -/
def PropE (r : ℕ) : Prop :=
  ∀ (Λ₁ Λ₂ : Dom R) (ν : I →₀ ℕ), ν.degree = r → ∀ x ∈ lat hvt hR A (Λ₁ + Λ₂),
    x ∈ wsp (Λ₁ + Λ₂) ν → tensorEmb hvt hR Λ₁.2 Λ₂.2 x ∈ LL hvt hR A Λ₁ Λ₂

variable {hvt hR A}

/-- `E(0)`. -/
theorem propE_zero : PropE hvt hR A 0 := by
  intro Λ₁ Λ₂ ν hν x hx hxw
  have hν0 : ν = 0 := (Finsupp.degree_eq_zero_iff ν).1 hν
  subst hν0
  refine mem_of_fW_mem (Λ₁ + Λ₂) 0
    ((LL hvt hR A Λ₁ Λ₂).comap (((tensorEmb hvt hR Λ₁.2 Λ₂.2).restrictScalars k).restrictScalars A))
    (fun w hw ↦ ?_) hx hxw
  have hw' : w = [] := by
    have := degree_wordWeight w
    rw [hw, map_zero] at this
    exact List.eq_nil_of_length_eq_zero this.symm
  subst hw'
  change tensorEmb hvt hR Λ₁.2 Λ₂.2 (IrreducibleModule.hwv R v (Λ₁.1 + Λ₂.1)) ∈ LL hvt hR A Λ₁ Λ₂
  rw [tensorEmb_hwv]
  exact TensorModule.tmul_mem_lattice (IrreducibleModule.hwv_mem_lattice hR _ Λ₁.2 A)
    (IrreducibleModule.hwv_mem_lattice hR _ Λ₂.2 A)

/-- `E(r) ∧ A(≤ r) → E(r + 1)` ([HK] Prop. 5.3.3). -/
theorem propE_succ [IsLocalRing A] {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖv : algebraMap A k ϖ = v⁻¹) {r : ℕ} (hA : ∀ s ≤ r, PropA hvt hR A s)
    (hE : PropE hvt hR A r) : PropE hvt hR A (r + 1) := by
  intro Λ₁ Λ₂ ν hν x hx hxw
  refine mem_of_fW_mem (Λ₁ + Λ₂) ν
    ((LL hvt hR A Λ₁ Λ₂).comap (((tensorEmb hvt hR Λ₁.2 Λ₂.2).restrictScalars k).restrictScalars A))
    (fun w hw ↦ ?_) hx hxw
  rcases w with _ | ⟨i, w⟩
  · have := degree_wordWeight ([] : List I)
    rw [hw, hν] at this
    simp at this
  have hw' : (LusztigF.wordWeight w).degree = r := by
    rw [degree_wordWeight]
    have := degree_wordWeight (i :: w)
    rw [hw, hν, List.length_cons] at this
    omega
  have hmem := hE Λ₁ Λ₂ _ hw' _ (IrreducibleModule.fWord_mem_lattice hR _ (Λ₁ + Λ₂).2 A w)
    (fW_mem_wsp hvt hR (Λ₁ + Λ₂) w)
  have hwt : tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) w) ∈
      weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum (LusztigF.wordWeight w)) :=
    map_mem_weightSpace _ (fW_mem_wsp hvt hR (Λ₁ + Λ₂) w)
  change tensorEmb hvt hR Λ₁.2 Λ₂.2 (fK hvt hR (Λ₁ + Λ₂) i (fW hvt hR (Λ₁ + Λ₂) w)) ∈
    LL hvt hR A Λ₁ Λ₂
  rw [map_kashiwaraF (pow_ne_one_of_transcendental' hvt) (isInt hvt hR (Λ₁ + Λ₂)) i
    (isIntT hvt hR Λ₁ Λ₂)]
  exact fT_mem_LL hϖ hϖv hA i hw' hmem hwt

end PropE

end GrandLoop

end LieLean.QuantumGroup

end
