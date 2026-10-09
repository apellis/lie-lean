/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.PropA

/-!
# Kashiwara's grand loop: the statement `B(r)`

We prove `B(r)`: `ẽᵢ B(λ)_{depth r} ⊆ B(λ) ∪ {0}` ([HK] Lemma 5.3.11, Prop. 5.3.12). As for `A(r)`,
the auxiliary weight is a fundamental weight `Λ_j` (`j` the second-to-last letter of the word)
instead of an unspecified `μ ≫ 0`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
-/

open Finset Pointwise TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

section Helpers

variable [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖv : algebraMap A k ϖ = v⁻¹)
include hϖ hϖv

/-- `ẽᵢ` preserves `ϖ (L(λ₁) ⊗ L(λ₂))` in depth `d`. -/
lemma eT_mem_smul_LL {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s) {Λ₁ Λ₂ : Dom R} (i : I)
    {ν : I →₀ ℕ} (hν : ν.degree = d) {z : TM v Λ₁ Λ₂} (hz : z ∈ ϖ • LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν)) :
    eT hvt hR Λ₁ Λ₂ i z ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨z₀, hz₀, hz₀w, rfl⟩ := TensorModule.exists_smul_weight hϖ0 hz hzw
  rw [LinearMap.map_smul_of_tower]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (eT_mem_LL hϖ hϖv hA i hν hz₀ hz₀w)

/-- `f̃`-words preserve `L(λ₁) ⊗ L(λ₂)`. -/
lemma fTw_mem_LL {Λ₁ Λ₂ : Dom R} (u : List I) {ν : I →₀ ℕ}
    (hA : ∀ s < ν.degree + u.length, PropA hvt hR A s) {z : TM v Λ₁ Λ₂}
    (hz : z ∈ LL hvt hR A Λ₁ Λ₂) (hzw : z ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν)) :
    fTw hvt hR Λ₁ Λ₂ u z ∈ LL hvt hR A Λ₁ Λ₂ := by
  induction u with
  | nil => simpa using hz
  | cons i u ih =>
    rw [fTw_cons]
    refine fT_mem_LL hϖ hϖv (d := (ν + LusztigF.wordWeight u).degree)
      (fun s hs ↦ hA s ?_) i rfl (ih fun s hs ↦ hA s (by simp only [List.length_cons]; omega))
      (fTw_mem_weightSpace Λ₁ Λ₂ u hzw)
    rw [map_add, degree_wordWeight] at hs
    simp only [List.length_cons]
    omega

/-- `S f̃_w (v ⊗ v) ≡ f̃_w v` ([HK] Lemma 5.3.6 (2), iterated). -/
lemma Sh_fTw_sub {Λ₁ Λ₂ : Dom R} :
    ∀ w : List I, (∀ s < w.length, PropA hvt hR A s) → (∀ s < w.length, PropB hvt hR A ϖ s) →
      (∀ s < w.length, PropC hvt hR A ϖ s) →
      Sh hvt hR Λ₁ Λ₂ (fTw hvt hR Λ₁ Λ₂ w (TensorModule.mk _ _
        (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k] IrreducibleModule.hwv R v Λ₂.1))) -
        fW hvt hR Λ₂ w ∈ ϖ • lat hvt hR A Λ₂ := by
  have hvvw : TensorModule.mk _ _ (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k]
      IrreducibleModule.hwv R v Λ₂.1) ∈ weightSpace R v (TM v Λ₁ Λ₂)
        (Λ₁.1 + Λ₂.1 - R.rootSum 0) := by
    simpa using fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ [] []
  intro w
  induction w with
  | nil =>
    intro _ _ _
    simp [Sh_tmul]
  | cons i w ih =>
    intro hA hB hC
    simp only [List.length_cons] at hA hB hC
    have hih := ih (fun s hs ↦ hA s (by omega)) (fun s hs ↦ hB s (by omega))
      (fun s hs ↦ hC s (by omega))
    have hmem := fTw_mem_LL hϖ hϖv (Λ₁ := Λ₁) (Λ₂ := Λ₂) w (ν := 0)
      (fun s hs ↦ hA s (by simp at hs; omega)) (fW_tmul_mem_LL Λ₁ Λ₂ [] []) hvvw
    have hS := Sh_fT_sub_mem hϖ hϖv (d := w.length) (fun s hs ↦ hA s (by omega))
      (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) i
      (ν := LusztigF.wordWeight w) (degree_wordWeight w) hmem
      (by simpa using fTw_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ w hvvw)
    have hf := kashiwaraF_mem_smul_lat Λ₂ i hih
    rw [map_sub] at hf
    rw [fTw_cons, fW_cons]
    simpa using add_mem hS hf

end Helpers

section Maps

variable [Finite I]

variable (hvt hR A ϖ) in
/-- `G(r)`: `Ψ_{λ₁,λ₂}(B(λ₁) ⊗ B(λ₂))_{depth r} ⊆ B(λ₁ + λ₂) ∪ {0}`. -/
def PropG (r : ℕ) : Prop :=
  ∀ (Λ₁ Λ₂ : Dom R) (w₁ w₂ : List I), w₁.length + w₂.length = r →
    tensorProj hvt hR Λ₁.2 Λ₂.2 (TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂)) ∈
      ϖ • lat hvt hR A (Λ₁ + Λ₂) ∨
    ∃ w : List I, tensorProj hvt hR Λ₁.2 Λ₂.2
      (TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂)) - fW hvt hR (Λ₁ + Λ₂) w ∈
      ϖ • lat hvt hR A (Λ₁ + Λ₂)

variable (hϖv : algebraMap A k ϖ = v⁻¹)
include hϖv

omit hϖv in
lemma smul_tensorProj (Λ₁ Λ₂ : Dom R) (c : A) (z : TM v Λ₁ Λ₂) :
    tensorProj hvt hR Λ₁.2 Λ₂.2 (c • z) = c • tensorProj hvt hR Λ₁.2 Λ₂.2 z := by
  rw [← algebraMap_smul k c z, LinearMap.map_smul_of_tower, algebraMap_smul]

omit hϖv in
lemma smul_tensorEmb (Λ₁ Λ₂ : Dom R) (c : A) (x : IrreducibleModule R v (Λ₁ + Λ₂).1) :
    tensorEmb hvt hR Λ₁.2 Λ₂.2 (c • x) = c • tensorEmb hvt hR Λ₁.2 Λ₂.2 x := by
  rw [← algebraMap_smul k c x, LinearMap.map_smul_of_tower, algebraMap_smul]

/-- `Ψ (ϖ (L ⊗ L)) ⊆ ϖ L` one step above depth `n + 2`, from `F(n + 1)`. -/
lemma tensorProj_mem_smul {n : ℕ} (hF : PropF hvt hR A (n + 1)) {Λ₁ Λ₂ : Dom R} (i : I)
    {ν : I →₀ ℕ} (hν : ν.degree = n + 2) {z : TM v Λ₁ Λ₂} (hz : z ∈ ϖ • LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν + R.root i)) :
    tensorProj hvt hR Λ₁.2 Λ₂.2 z ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂) := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨z₀, hz₀, hz₀w, rfl⟩ := TensorModule.exists_smul_weight hϖ0 hz hzw
  rw [smul_tensorProj]
  refine Submodule.smul_mem_pointwise_smul _ _ _ ?_
  by_cases h0 : z₀ = 0
  · rw [h0, map_zero]; exact zero_mem _
  obtain ⟨ν', hν'⟩ := exists_rootSum_of_LL hz₀ hz₀w h0
  have hνν : ν = ν' + Finsupp.single i 1 := by
    refine LusztigCartanDatum.RootDatum.rootSum_injective hR ?_
    rw [R.rootSum_add, R.rootSum_single, one_nsmul]
    calc R.rootSum ν = Λ₁.1 + Λ₂.1 - (Λ₁.1 + Λ₂.1 - R.rootSum ν + R.root i) + R.root i := by
          abel
      _ = Λ₁.1 + Λ₂.1 - (Λ₁.1 + Λ₂.1 - R.rootSum ν') + R.root i := by rw [hν']
      _ = R.rootSum ν' + R.root i := by abel
  have hd : ν'.degree = n + 1 := by
    have := hν; rw [hνν, map_add, Finsupp.degree_single] at this; omega
  exact hF Λ₁ Λ₂ ν' hd _ hz₀ (hν' ▸ hz₀w)

/-- `Φ (ϖ L) ⊆ ϖ (L ⊗ L)` one step above depth `n + 2`, from `E(n + 1)`. -/
lemma tensorEmb_mem_smul {n : ℕ} (hE : PropE hvt hR A (n + 1)) {Λ₁ Λ₂ : Dom R} (i : I)
    {ν : I →₀ ℕ} (hν : ν.degree = n + 2) {x : IrreducibleModule R v (Λ₁ + Λ₂).1}
    (hx : x ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂))
    (hxw : x ∈ weightSpace R v _ ((Λ₁ + Λ₂).1 - R.rootSum ν + R.root i)) :
    tensorEmb hvt hR Λ₁.2 Λ₂.2 x ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨x₀, hx₀, hx₀w, rfl⟩ := TensorModule.exists_smul_weight hϖ0 hx hxw
  rw [smul_tensorEmb]
  refine Submodule.smul_mem_pointwise_smul _ _ _ ?_
  by_cases h0 : x₀ = 0
  · rw [h0, map_zero]; exact zero_mem _
  obtain ⟨ν', hν'⟩ := exists_eq_add_single hR (pow_ne_one_of_transcendental' hvt) (Λ₁ + Λ₂)
    (j := 1) (by rwa [one_smul]) h0
  have hd : ν'.degree = n + 1 := by
    have := hν; rw [hν', map_add, Finsupp.degree_single] at this; omega
  refine hE Λ₁ Λ₂ ν' hd _ hx₀ ?_
  convert hx₀w using 2
  rw [hν', R.rootSum_add, R.rootSum_single, one_nsmul]
  abel

end Maps

section StepB

variable [Finite I] [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹) (hinj : Function.Injective (algebraMap A k))
include hϖ hϖv hinj

/-- **[HK] Lemma 5.3.11 (2)** (library order, with `λ = λ₁ + Λ_j`): `ẽᵢ` maps `f̃_{u j i'} v_λ`
into `B(λ) ∪ {0}` modulo `ϖ L(λ)`. -/
theorem stepB {n : ℕ} (hA : ∀ s ≤ n + 2, PropA hvt hR A s)
    (hB : ∀ s < n + 2, PropB hvt hR A ϖ s) (hC : ∀ s < n + 2, PropC hvt hR A ϖ s)
    (hF : PropF hvt hR A (n + 1)) (hG : PropG hvt hR A ϖ (n + 1)) {Λ₁ Λ₂ : Dom R} {j : I}
    (hj : ∀ i, Λ₂.1 (R.coroot i) = if i = j then 1 else 0) (u : List I) (hu : u.length = n)
    (i' i : I) :
    eK hvt hR (Λ₁ + Λ₂) i (fW hvt hR (Λ₁ + Λ₂) (u ++ [j, i'])) ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂) ∨
      ∃ w' : List I, eK hvt hR (Λ₁ + Λ₂) i (fW hvt hR (Λ₁ + Λ₂) (u ++ [j, i'])) -
        fW hvt hR (Λ₁ + Λ₂) w' ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂) := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  set hv' := pow_ne_one_of_transcendental' hvt
  set w := u ++ [j, i']
  have hwlen : w.length = n + 2 := by simp [w, hu]
  have hdeg : (LusztigF.wordWeight w).degree = n + 2 := by rw [degree_wordWeight, hwlen]
  obtain ⟨w₁, w₂, h1, h2, h3, h5, h4⟩ := fTw_fund hϖ hϖv hinj hj u i'
    (fun s hs ↦ hA s (by omega)) (by rwa [hu]) (by rwa [hu])
  set vv := TensorModule.mk (IrreducibleModule R v Λ₁.1) (IrreducibleModule R v Λ₂.1)
    (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k] IrreducibleModule.hwv R v Λ₂.1)
  set W := fTw hvt hR Λ₁ Λ₂ w vv
  have hvvw : vv ∈ weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum 0) := by
    simpa using fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ [] []
  have hWw : W ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum (LusztigF.wordWeight w)) := by
    simpa using fTw_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ w hvvw
  have hmw : TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈
      weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum (LusztigF.wordWeight w)) := by
    rw [← h5]; exact fW_tmul_mem_weightSpace Λ₁ Λ₂ w₁ w₂
  have hEw : eT hvt hR Λ₁ Λ₂ i W ∈
      weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum (LusztigF.wordWeight w) + R.root i) :=
    kashiwaraE_mem_weightSpace hv' (isIntT hvt hR Λ₁ Λ₂) i hWw
  have hΨ : tensorProj hvt hR Λ₁.2 Λ₂.2 (eT hvt hR Λ₁ Λ₂ i W) =
      eK hvt hR (Λ₁ + Λ₂) i (fW hvt hR (Λ₁ + Λ₂) w) := by
    rw [tensorProj_eT, tensorProj_fTw]
  have he1 : eT hvt hR Λ₁ Λ₂ i W -
      eT hvt hR Λ₁ Λ₂ i (TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂)) ∈
      ϖ • LL hvt hR A Λ₁ Λ₂ := by
    rw [← map_sub]; exact eT_mem_smul_LL hϖ hϖv hA i hdeg h4 (sub_mem hWw hmw)
  -- the conclusion from a congruence of `ẽᵢ W`
  have hleft : eT hvt hR Λ₁ Λ₂ i W ∈ ϖ • LL hvt hR A Λ₁ Λ₂ →
      eK hvt hR (Λ₁ + Λ₂) i (fW hvt hR (Λ₁ + Λ₂) w) ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂) ∨
        ∃ w' : List I, eK hvt hR (Λ₁ + Λ₂) i (fW hvt hR (Λ₁ + Λ₂) w) -
          fW hvt hR (Λ₁ + Λ₂) w' ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂) := fun h ↦ Or.inl
    (hΨ ▸ tensorProj_mem_smul hϖv hF i hdeg h hEw)
  have htail : ∀ w₁' w₂' : List I, LusztigF.wordWeight w₁' + LusztigF.wordWeight w₂' +
      Finsupp.single i 1 = LusztigF.wordWeight w →
      eT hvt hR Λ₁ Λ₂ i W -
        TensorModule.mk _ _ (fW hvt hR Λ₁ w₁' ⊗ₜ[k] fW hvt hR Λ₂ w₂') ∈ ϖ • LL hvt hR A Λ₁ Λ₂ →
      eK hvt hR (Λ₁ + Λ₂) i (fW hvt hR (Λ₁ + Λ₂) w) ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂) ∨
        ∃ w' : List I, eK hvt hR (Λ₁ + Λ₂) i (fW hvt hR (Λ₁ + Λ₂) w) -
          fW hvt hR (Λ₁ + Λ₂) w' ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂) := by
    intro w₁' w₂' hww hcong
    have hzw : TensorModule.mk _ _ (fW hvt hR Λ₁ w₁' ⊗ₜ[k] fW hvt hR Λ₂ w₂') ∈
        weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum (LusztigF.wordWeight w) + R.root i) := by
      convert fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ w₁' w₂' using 2
      rw [← hww, R.rootSum_add, R.rootSum_single, one_nsmul]
      abel
    have hk := tensorProj_mem_smul hϖv hF i hdeg hcong (sub_mem hEw hzw)
    rw [map_sub, hΨ] at hk
    have hlen' : w₁'.length + w₂'.length = n + 1 := by
      have := congrArg Finsupp.degree hww
      rw [map_add, map_add, degree_wordWeight, degree_wordWeight, Finsupp.degree_single, hdeg]
        at this
      omega
    rcases hG Λ₁ Λ₂ w₁' w₂' hlen' with hg | ⟨w', hg⟩
    · exact Or.inl (by simpa using add_mem hk hg)
    · exact Or.inr ⟨w', by simpa using add_mem hk hg⟩
  -- degenerate factors
  by_cases hx0 : fW hvt hR Λ₁ w₁ ∈ ϖ • lat hvt hR A Λ₁
  · refine hleft ?_
    have := eT_mem_smul_LL hϖ hϖv hA i hdeg (tmul_mem_smul_left hx0
      (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂)) hmw
    simpa using add_mem he1 this
  by_cases hy0 : fW hvt hR Λ₂ w₂ ∈ ϖ • lat hvt hR A Λ₂
  · refine hleft ?_
    have := eT_mem_smul_LL hϖ hϖv hA i hdeg (tmul_mem_smul_right
      (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁) hy0) hmw
    simpa using add_mem he1 this
  have hd₁ : w₁.length < n + 2 := by omega
  have hd₂ : w₂.length < n + 2 := by omega
  obtain ⟨k₁, a, u₁, hxs⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ₁ i (degree_wordWeight w₁)
    (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁) (fW_mem_wsp hvt hR Λ₁ w₁)
    (w := w₁) (by simp) hx0
  obtain ⟨k₂, b, u₂, hys⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ₂ i (degree_wordWeight w₂)
    (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂) (fW_mem_wsp hvt hR Λ₂ w₂)
    (w := w₂) (by simp) hy0
  have hrule := eT_tmul hϖ hϖv (fun s hs ↦ hA s (by omega)) (fun s hs ↦ hA s (by omega))
    (degree_wordWeight w₁) (degree_wordWeight w₂) hxs hys
  have hc1 := add_mem he1 hrule
  split_ifs at hc1 with hc
  · -- `ẽᵢ` acts on the second factor
    by_cases hey : eK hvt hR Λ₂ i (fW hvt hR Λ₂ w₂) ∈ ϖ • lat hvt hR A Λ₂
    · refine hleft ?_
      simpa using add_mem hc1 (tmul_mem_smul_right
        (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁) hey)
    obtain ⟨w₂', hw₂'⟩ := (hB w₂.length hd₂ Λ₂ w₂ rfl i).resolve_left hey
    have hew₂ := kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ₂) i
      (fW_mem_wsp hvt hR Λ₂ w₂)
    obtain ⟨ν₂, hν₂⟩ := exists_eq_add_single hR hv' Λ₂ (j := 1) (by rwa [one_smul])
      (fun h ↦ hey (by rw [h]; exact zero_mem _))
    have hw₂ν : LusztigF.wordWeight w₂' = ν₂ := wordWeight_eq_of_sub_mem hvt hR A ϖ Λ₂
      (by
        have := kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ₂) i (fW_mem_wsp hvt hR Λ₂ w₂)
        convert this using 2
        rw [hν₂, R.rootSum_add, R.rootSum_single, one_nsmul]; abel) hey hw₂'
    refine htail w₁ w₂' (by rw [hw₂ν, add_assoc, ← hν₂, h5]) ?_
    have := add_mem hc1 (tmul_mem_smul_right (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁)
      hw₂')
    convert this using 1
    rw [tmul_sub, map_sub]
    abel
  · -- `ẽᵢ` acts on the first factor
    by_cases hex : eK hvt hR Λ₁ i (fW hvt hR Λ₁ w₁) ∈ ϖ • lat hvt hR A Λ₁
    · refine hleft ?_
      simpa using add_mem hc1 (tmul_mem_smul_left hex
        (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂))
    obtain ⟨w₁', hw₁'⟩ := (hB w₁.length hd₁ Λ₁ w₁ rfl i).resolve_left hex
    have hew₁ := kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ₁) i
      (fW_mem_wsp hvt hR Λ₁ w₁)
    obtain ⟨ν₁, hν₁⟩ := exists_eq_add_single hR hv' Λ₁ (j := 1) (by rwa [one_smul])
      (fun h ↦ hex (by rw [h]; exact zero_mem _))
    have hw₁ν : LusztigF.wordWeight w₁' = ν₁ := wordWeight_eq_of_sub_mem hvt hR A ϖ Λ₁
      (by
        have := kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ₁) i (fW_mem_wsp hvt hR Λ₁ w₁)
        convert this using 2
        rw [hν₁, R.rootSum_add, R.rootSum_single, one_nsmul]; abel) hex hw₁'
    refine htail w₁' w₂ (by rw [hw₁ν, add_right_comm, ← hν₁, h5]) ?_
    have := add_mem hc1 (tmul_mem_smul_left hw₁'
      (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂))
    convert this using 1
    rw [sub_tmul, map_sub]
    abel

end StepB

/-! ### `B(r)` -/

lemma transportB {ν ν' : Dom R} (h : ν.1 = ν'.1) (i : I) (w : List I)
    (hmem : eK hvt hR ν i (fW hvt hR ν w) ∈ ϖ • lat hvt hR A ν ∨
      ∃ w' : List I, eK hvt hR ν i (fW hvt hR ν w) - fW hvt hR ν w' ∈ ϖ • lat hvt hR A ν) :
    eK hvt hR ν' i (fW hvt hR ν' w) ∈ ϖ • lat hvt hR A ν' ∨
      ∃ w' : List I, eK hvt hR ν' i (fW hvt hR ν' w) - fW hvt hR ν' w' ∈ ϖ • lat hvt hR A ν' := by
  obtain ⟨a, ha⟩ := ν
  obtain ⟨b, hb⟩ := ν'
  simp only at h
  subst h
  exact hmem

/-- `ẽᵢ f̃_j v_λ` is `0` or `v_λ`. -/
lemma eK_fW_single (Λ : Dom R) (i j : I) :
    eK hvt hR Λ i (fW hvt hR Λ [j]) = 0 ∨
      eK hvt hR Λ i (fW hvt hR Λ [j]) = IrreducibleModule.hwv R v Λ.1 := by
  set hv' := pow_ne_one_of_transcendental' hvt
  have hvn := mem_nodeWt_of_mem (i := j)
    (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := v) (Λ := Λ.1))
  have hf : fW hvt hR Λ [j] =
      dFV (hvt := hvt) (hR := hR) Λ j 1 (IrreducibleModule.hwv R v Λ.1) := by
    have := kashiwaraF_dF (hvt := hvt) (hR := hR) hvn (IrreducibleModule.E_smul_hwv j) 0
    rw [IntegrableSl2.dF_zero] at this
    rw [fW_cons, fW_nil]
    exact this
  by_cases hij : i = j
  · subst hij
    rw [hf]
    by_cases hp : (0 : ℤ) < Λ.1 (R.coroot i)
    · have := IntegrableSl2.eTilde_dF_succ (pow_d_ne_zero i) (pow_d_ne_one hv' i)
        (V := nodeSl2 R v _ hv' (isInt hvt hR Λ) i) (IrreducibleModule.E_smul_hwv i) hvn
        (j := 0) (by simpa using hp)
      change eK hvt hR Λ i _ = _ at this
      rw [this, IntegrableSl2.dF_zero]
      exact Or.inr rfl
    · rw [IntegrableSl2.dF_eq_zero_of_primitive (pow_d_ne_zero i) (pow_d_ne_one hv' i) hvn
        (IrreducibleModule.E_smul_hwv i) (by push_cast; omega), map_zero]
      exact Or.inl rfl
  · have hE : E R v i • fW hvt hR Λ [j] = 0 := by
      rw [hf, IntegrableSl2.dF_apply, smul_comm, pow_one]
      change _ • (E R v i • F R v j • IrreducibleModule.hwv R v Λ.1) = 0
      have h := E_mul_F_sub R v i j
      simp only [hij, ↓reduceIte, sub_eq_zero] at h
      rw [← mul_smul, h, mul_smul, IrreducibleModule.E_smul_hwv, smul_zero, smul_zero]
    exact Or.inl (IntegrableSl2.eTilde_of_primitive (pow_d_ne_zero i) (pow_d_ne_one hv' i)
      (V := nodeSl2 R v _ hv' (isInt hvt hR Λ) i) hE
      (mem_nodeWt_of_mem (fW_mem_wsp hvt hR Λ [j])))

/-- `B(0)`. -/
theorem propB_zero : PropB hvt hR A ϖ 0 := by
  intro Λ w hw i
  rw [List.length_eq_zero_iff] at hw
  subst hw
  left
  have : eK hvt hR Λ i (fW hvt hR Λ []) = 0 :=
    IntegrableSl2.eTilde_of_primitive (pow_d_ne_zero i)
      (pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) (IrreducibleModule.E_smul_hwv i)
      (mem_nodeWt_of_mem (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := v) (Λ := Λ.1)))
  rw [this]
  exact zero_mem _

/-- `B(1)`. -/
theorem propB_one : PropB hvt hR A ϖ 1 := by
  intro Λ w hw i
  obtain ⟨j, rfl⟩ : ∃ j, w = [j] := by
    rcases w with _ | ⟨j, _ | ⟨_, _⟩⟩ <;> simp at hw; exact ⟨j, rfl⟩
  rcases eK_fW_single (hvt := hvt) (hR := hR) Λ i j with h | h
  · left; rw [h]; exact zero_mem _
  · right; exact ⟨[], by rw [h, fW_nil, sub_self]; exact zero_mem _⟩

/-- **`B(r)`** for `r ≥ 2` ([HK] Prop. 5.3.12). -/
theorem propB_add_two [Finite I] [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖv : algebraMap A k ϖ = v⁻¹) (hinj : Function.Injective (algebraMap A k))
    (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0) {n : ℕ}
    (hA : ∀ s ≤ n + 2, PropA hvt hR A s) (hB : ∀ s < n + 2, PropB hvt hR A ϖ s)
    (hC : ∀ s < n + 2, PropC hvt hR A ϖ s) (hE : PropE hvt hR A (n + 1))
    (hF : PropF hvt hR A (n + 1)) (hG : PropG hvt hR A ϖ (n + 1)) :
    PropB hvt hR A ϖ (n + 2) := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  set hv' := pow_ne_one_of_transcendental' hvt
  choose Λf hΛf using hfund
  intro Λ w hw i
  have hdeg : (LusztigF.wordWeight w).degree = n + 2 := by rw [degree_wordWeight, hw]
  by_cases hw0 : fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ
  · exact Or.inl (localE_smul hA Λ hdeg i 0 hϖ0 hw0 (by simpa using fW_mem_wsp hvt hR Λ w))
  obtain ⟨u, a, b, rfl⟩ : ∃ u a b, w = u ++ [a, b] := by
    have hl : (w.drop n).length = 2 := by simp; omega
    obtain ⟨a, b, hab⟩ : ∃ a b, w.drop n = [a, b] := by
      match w.drop n, hl with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    exact ⟨w.take n, a, b, by rw [← hab, List.take_append_drop]⟩
  set w := u ++ [a, b]
  set Λj := Λf a
  have hu : u.length = n := by simp [w] at hw; omega
  have hSB := transportB (ν := Λ + Λj) (ν' := Λj + Λ) (by simp [add_comm]) i w
    (stepB hϖ hϖv hinj hA hB hC hF hG (hΛf a) u hu b i)
  set vv := TensorModule.mk (IrreducibleModule R v Λj.1) (IrreducibleModule R v Λ.1)
    (IrreducibleModule.hwv R v Λj.1 ⊗ₜ[k] IrreducibleModule.hwv R v Λ.1)
  set W := fTw hvt hR Λj Λ w vv
  have hvvw : vv ∈ weightSpace R v (TM v Λj Λ) (Λj.1 + Λ.1 - R.rootSum 0) := by
    simpa using fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λj Λ [] []
  have hWw : W ∈ weightSpace R v _ (Λj.1 + Λ.1 - R.rootSum (LusztigF.wordWeight w)) := by
    simpa using fTw_mem_weightSpace (hvt := hvt) (hR := hR) Λj Λ w hvvw
  have hmw : TensorModule.mk _ _ (IrreducibleModule.hwv R v Λj.1 ⊗ₜ[k] fW hvt hR Λ w) ∈
      weightSpace R v (TM v Λj Λ) (Λj.1 + Λ.1 - R.rootSum (LusztigF.wordWeight w)) := by
    simpa using fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λj Λ [] w
  have hd := fTw_hwv_tmul hϖ hϖv hinj (Λ₁ := Λj) (Λ₂ := Λ) w (fun s hs ↦ hA s (by omega))
    (by rwa [hw]) (by rwa [hw]) hw0
  have hE1 : eT hvt hR Λj Λ i W - eT hvt hR Λj Λ i (TensorModule.mk _ _
      (IrreducibleModule.hwv R v Λj.1 ⊗ₜ[k] fW hvt hR Λ w)) ∈ ϖ • LL hvt hR A Λj Λ := by
    rw [← map_sub]; exact eT_mem_smul_LL hϖ hϖv hA i hdeg hd (sub_mem hWw hmw)
  have hP0 : PropAN hvt hR A ϖ (n + 2) 0 Λ := fun i' w' hw' ↦ by
    simpa using hA (n + 2) le_rfl Λ _ (by rw [degree_wordWeight, hw']) i' _
      (IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A w') (fW_mem_wsp hvt hR Λ w')
  obtain ⟨M, ζ, hζw, hζE, hζ2, hye, hζL⟩ := exists_strings_negLat (fun s hs ↦ hA s (by omega))
    hP0 i hdeg (IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A w) (fW_mem_wsp hvt hR Λ w)
  have hE2 := eT_hwv_tmul_sub (Λ₁ := Λj) hϖ hϖv i hζw hζE hζ2 hζL
  rw [← hye] at hE2
  have hLL : TensorModule.lattice k A (lat hvt hR A Λj) (negLat (lat hvt hR A Λ) ϖ 0) ≤
      LL hvt hR A Λj Λ := fun z hz ↦ by simpa using lattice_negLat_right hz
  have hcong : eT hvt hR Λj Λ i W - TensorModule.mk _ _ (IrreducibleModule.hwv R v Λj.1 ⊗ₜ[k]
      eK hvt hR Λ i (fW hvt hR Λ w)) ∈ ϖ • LL hvt hR A Λj Λ := by
    simpa using add_mem hE1 (TensorModule.smul_le_smul_of_le hLL ϖ hE2)
  have hΦW : tensorEmb hvt hR Λj.2 Λ.2 (eK hvt hR (Λj + Λ) i (fW hvt hR (Λj + Λ) w)) =
      eT hvt hR Λj Λ i W := by rw [tensorEmb_eK, tensorEmb_fW]
  have hSapp : ∀ z, TensorModule.mk _ _ (IrreducibleModule.hwv R v Λj.1 ⊗ₜ[k]
      eK hvt hR Λ i (fW hvt hR Λ w)) - z ∈ ϖ • LL hvt hR A Λj Λ →
      eK hvt hR Λ i (fW hvt hR Λ w) - Sh hvt hR Λj Λ z ∈ ϖ • lat hvt hR A Λ := by
    intro z hz
    have := Sh_mem_smul hz
    rwa [map_sub, Sh_tmul, IrreducibleModule.form_hwv, one_smul] at this
  have hew := kashiwaraE_mem_weightSpace hv' (isInt hvt hR (Λj + Λ)) i
    (fW_mem_wsp hvt hR (Λj + Λ) w)
  -- the left alternative of `stepB`
  have hleft : eK hvt hR (Λj + Λ) i (fW hvt hR (Λj + Λ) w) ∈ ϖ • lat hvt hR A (Λj + Λ) →
      eK hvt hR Λ i (fW hvt hR Λ w) ∈ ϖ • lat hvt hR A Λ := by
    intro h
    have h1 := tensorEmb_mem_smul hϖv hE i hdeg h hew
    rw [hΦW] at h1
    simpa using hSapp 0 (by simpa using sub_mem h1 hcong)
  rcases hSB with h | ⟨w', hw'⟩
  · exact Or.inl (hleft h)
  by_cases h0 : eK hvt hR (Λj + Λ) i (fW hvt hR (Λj + Λ) w) ∈ ϖ • lat hvt hR A (Λj + Λ)
  · exact Or.inl (hleft h0)
  obtain ⟨ν', hν'⟩ := exists_eq_add_single hR hv' (Λj + Λ) (j := 1) (by rwa [one_smul])
    (fun h ↦ h0 (by rw [h]; exact zero_mem _))
  have hew' : eK hvt hR (Λj + Λ) i (fW hvt hR (Λj + Λ) w) ∈ wsp (Λj + Λ) ν' := by
    convert hew using 2
    rw [hν', R.rootSum_add, R.rootSum_single, one_nsmul]; abel
  have hw'ν := wordWeight_eq_of_sub_mem hvt hR A ϖ (Λj + Λ) hew' h0 hw'
  have hw'len : w'.length = n + 1 := by
    rw [← degree_wordWeight, hw'ν]
    have := hdeg; rw [hν', map_add, Finsupp.degree_single] at this; omega
  have h1 := tensorEmb_mem_smul hϖv hE i hdeg hw' (sub_mem hew (by
    convert fW_mem_wsp hvt hR (Λj + Λ) w' using 2
    rw [hw'ν, hν', R.rootSum_add, R.rootSum_single, one_nsmul]; abel))
  rw [map_sub, hΦW, tensorEmb_fW] at h1
  have h2 := hSapp _ (by simpa using sub_mem h1 hcong)
  have h3 := Sh_fTw_sub hϖ hϖv (Λ₁ := Λj) (Λ₂ := Λ) w' (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega))
  exact Or.inr ⟨w', by simpa using add_mem h2 h3⟩

end GrandLoop

end LieLean.QuantumGroup

end
