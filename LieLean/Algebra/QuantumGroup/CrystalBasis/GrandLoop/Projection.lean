/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Purity

/-!
# Kashiwara's grand loop: `Ψ(L(λ₁) ⊗ L(λ₂)) ⊆ L(λ₁ + λ₂)` for `λ₁` large

In library order, `L(λ₁) ⊗ L(λ₂)` in depth `r` is spanned modulo `ϖ` by the vectors
`f̃ᵢ z` (`z` of depth `r - 1`) and `L(λ₁) ⊗ v_{λ₂}` ([HK] Prop. 5.3.5; for the generators
`f̃_{w₁} v ⊗ f̃_{i u} v` see `GrandLoop.fW_tmul_cons_sub_mem`). With `F(r - 1)` and
`Ψ(L(λ₁) ⊗ v_{λ₂}) ⊆ L(λ₁ + λ₂)` for `λ₁` large (`GrandLoop.tensorProj_tmul_hwv_mem`),
Nakayama's lemma gives **[HK] Lemma 5.3.15**: `Ψ((L(λ₁) ⊗ L(λ₂))_{λ₁+λ₂-ν}) ⊆ L(λ₁ + λ₂)` for
`λ₁` large (`GrandLoop.tensorProj_mem_lat_of_large`).

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

section Generators

variable [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖv : algebraMap A k ϖ = v⁻¹)
include hϖ hϖv

/-- **The generators `f̃_{w₁} v ⊗ f̃_{i u} v`** ([HK] Lemma 5.3.2 (4), (5), library order):
`f̃_{w₁} v ⊗ f̃ᵢ f̃_u v ≡ f̃ᵢ z` modulo `ϖ (L(λ₁) ⊗ L(λ₂))` for some `z ∈ L(λ₁) ⊗ L(λ₂)` of
weight `λ₁ + λ₂ - wt(w₁) - wt(u)`, given `A`, `B`, `C` up to the depth of `z`. -/
theorem fW_tmul_cons_sub_mem {d : ℕ} (hA : ∀ s ≤ d + 1, PropA hvt hR A s)
    (hB : ∀ s ≤ d, PropB hvt hR A ϖ s) (hC : ∀ s ≤ d, PropC hvt hR A ϖ s) {Λ₁ Λ₂ : Dom R}
    (i : I) (w₁ u : List I) (hd : w₁.length + u.length = d) :
    ∃ z ∈ LL hvt hR A Λ₁ Λ₂,
      z ∈ weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum (wordWeight w₁ + wordWeight u)) ∧
      TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ (i :: u)) -
        fT hvt hR Λ₁ Λ₂ i z ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  set x := fW hvt hR Λ₁ w₁
  set y := fW hvt hR Λ₂ u
  have hxL : x ∈ lat hvt hR A Λ₁ := IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁
  have hyL : y ∈ lat hvt hR A Λ₂ := IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A u
  have h0 : (0 : TM v Λ₁ Λ₂) ∈ weightSpace R v (TM v Λ₁ Λ₂)
      (Λ₁.1 + Λ₂.1 - R.rootSum (wordWeight w₁ + wordWeight u)) := zero_mem _
  rw [fW_cons]
  by_cases hx0 : x ∈ ϖ • lat hvt hR A Λ₁
  · exact ⟨0, zero_mem _, h0, by
      rw [map_zero, sub_zero]; exact tmul_mem_smul_left hx0 (kashiwaraF_mem_lat Λ₂ i hyL)⟩
  by_cases hy0 : y ∈ ϖ • lat hvt hR A Λ₂
  · exact ⟨0, zero_mem _, h0, by
      rw [map_zero, sub_zero]; exact tmul_mem_smul_right hxL (kashiwaraF_mem_smul_lat Λ₂ i hy0)⟩
  have hd₁ : w₁.length ≤ d := by omega
  have hd₂ : u.length ≤ d := by omega
  obtain ⟨k₁, a, uu, hxs⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ₁ i (degree_wordWeight w₁) hxL
    (fW_mem_wsp hvt hR Λ₁ w₁) (w := w₁) (by simp [x]) hx0
  obtain ⟨k₂, b, u', hys⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ₂ i (degree_wordWeight u) hyL
    (fW_mem_wsp hvt hR Λ₂ u) (w := u) (by simp [y]) hy0
  by_cases ha : k₁ < b - k₂
  · have hr := fT_tmul hϖ hϖv (fun s hs ↦ hA s (by omega)) (fun s hs ↦ hA s (by omega))
      (degree_wordWeight w₁) (degree_wordWeight u) hxs hys
    simp only [ha, ↓reduceIte] at hr
    refine ⟨TensorModule.mk _ _ (x ⊗ₜ[k] y), TensorModule.tmul_mem_lattice hxL hyL, ?_, ?_⟩
    · convert TensorModule.tmul_mem_weightSpace hxs.x_wt hys.x_wt using 2
      rw [R.rootSum_add]; abel
    · have := neg_mem hr
      rwa [neg_sub] at this
  by_cases hb : k₂ = b
  · exact ⟨0, zero_mem _, h0, by
      rw [map_zero, sub_zero]; exact tmul_mem_smul_right hxL (hys.kashiwaraF_mem hb)⟩
  have hk1 : 1 ≤ k₁ := by have := hys.le; omega
  obtain ⟨ν₁', hν₁'⟩ := hxs.exists_pred hk1
  have hdeg₁ : ν₁'.degree = w₁.length - 1 := by
    have := degree_wordWeight w₁
    rw [hν₁', map_add, Finsupp.degree_single] at this
    omega
  have hdeg₂ : (wordWeight u + Finsupp.single i 1).degree = u.length + 1 := by
    rw [map_add, Finsupp.degree_single, degree_wordWeight]
  have hx' := hxs.kashiwaraE (fun s hs ↦ hA s (by omega)) (degree_wordWeight w₁) hϖ0 hν₁' hk1
  have hy' := hys.kashiwaraF (show k₂ + 1 ≤ b by have := hys.le; omega)
  have hr := fT_tmul hϖ hϖv (fun s hs ↦ hA s (by omega)) (fun s hs ↦ hA s (by omega)) hdeg₁
    hdeg₂ hx' hy'
  simp only [show ¬(k₁ - 1 < b - (k₂ + 1)) by omega, ↓reduceIte] at hr
  have hfx := (hx'.kashiwaraF (by have := hxs.le; omega)).sub
  rw [Nat.sub_add_cancel hk1] at hfx
  have hd : fK hvt hR Λ₁ i (eK hvt hR Λ₁ i x) - x ∈ ϖ • lat hvt hR A Λ₁ := by
    have := sub_mem hfx hxs.sub
    rwa [sub_sub_sub_cancel_right] at this
  refine ⟨TensorModule.mk _ _ (eK hvt hR Λ₁ i x ⊗ₜ[k] fK hvt hR Λ₂ i y),
    TensorModule.tmul_mem_lattice hx'.mem_lat hy'.mem_lat, ?_, ?_⟩
  · convert TensorModule.tmul_mem_weightSpace hx'.x_wt hy'.x_wt using 2
    rw [hν₁', R.rootSum_add, R.rootSum_add, R.rootSum_add]; abel
  · have := sub_mem (neg_mem hr) (tmul_mem_smul_left hd hy'.mem_lat)
    convert this using 1
    rw [sub_tmul, map_sub]
    abel

end Generators

/-! ### [HK] Lemma 5.3.15 -/

section Main

variable (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
include hk

omit [CharZero k] [NeZero v] [DecidableEq I] hk in
lemma finite_pairs [Finite I] (ν : I →₀ ℕ) :
    {p : List I × List I | wordWeight p.1 + wordWeight p.2 = ν}.Finite := by
  refine ((List.finite_length_le I ν.degree).prod (List.finite_length_le I ν.degree)).subset ?_
  rintro ⟨w₁, w₂⟩ (h : wordWeight w₁ + wordWeight w₂ = ν)
  have := congrArg Finsupp.degree h
  rw [map_add, degree_wordWeight, degree_wordWeight] at this
  exact ⟨show w₁.length ≤ ν.degree by omega, show w₂.length ≤ ν.degree by omega⟩

/-- **[HK] Lemma 5.3.15** (library order): for `λ₁` large,
`Ψ((L(λ₁) ⊗ L(λ₂))_{λ₁+λ₂-ν}) ⊆ L(λ₁ + λ₂)`, given `A`, `B`, `C`, `E` and `F(r)` in the
relevant depths (`|ν| = r + 1`). -/
theorem tensorProj_mem_lat_of_large [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
    (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖv : algebraMap A k ϖ = v⁻¹) {r : ℕ} {ν : I →₀ ℕ} (hν : ν.degree = r + 1)
    (hA : ∀ s ≤ r + 1, PropA hvt hR A s) (hB : ∀ s ≤ r, PropB hvt hR A ϖ s)
    (hC : ∀ s ≤ r, PropC hvt hR A ϖ s) (hE : PropE hvt hR A (r + 1)) (hF : PropF hvt hR A r)
    (ρ : Dom R) (hρ : ∀ i, 1 ≤ ρ.1 (R.coroot i)) :
    ∃ Λs : Dom R, (∀ i, ((r + 1 : ℕ) : ℤ) ≤ Λs.1 (R.coroot i)) ∧ ∀ Λ Λ₂ : Dom R,
      ∀ z ∈ LL hvt hR A (Λ + Λs) Λ₂,
        z ∈ weightSpace R v (TM v (Λ + Λs) Λ₂) ((Λ + Λs).1 + Λ₂.1 - R.rootSum ν) →
        tensorProj hvt hR (Λ + Λs).2 Λ₂.2 z ∈ lat hvt hR A (Λ + Λs + Λ₂) := by
  classical
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨Λs, hΛs, hpur⟩ := tensorProj_tmul_hwv_mem hk hinj hϖv (ν := ν)
    (fun s hs ↦ hA s (by omega)) (hν ▸ hE) ρ hρ
  refine ⟨Λs, fun i ↦ by have := hΛs i; rwa [hν] at this, fun Λ Λ₂ ↦ ?_⟩
  let Ψ : TM v (Λ + Λs) Λ₂ →ₗ[A] IrreducibleModule R v (Λ + Λs + Λ₂).1 :=
    ((tensorProj hvt hR (Λ + Λs).2 Λ₂.2).restrictScalars k).restrictScalars A
  let W : Submodule A (TM v (Λ + Λs) Λ₂) :=
    (weightSpace R v (TM v (Λ + Λs) Λ₂) ((Λ + Λs).1 + Λ₂.1 - R.rootSum ν)).restrictScalars A
  let X : Submodule A (IrreducibleModule R v (Λ + Λs + Λ₂).1) :=
    (LL hvt hR A (Λ + Λs) Λ₂ ⊓ W).map Ψ
  -- `X` is finitely generated
  let G : Set (TM v (Λ + Λs) Λ₂) := (fun p : List I × List I ↦
    TensorModule.mk _ _ (fW hvt hR (Λ + Λs) p.1 ⊗ₜ[k] fW hvt hR Λ₂ p.2)) ''
      {p | wordWeight p.1 + wordWeight p.2 = ν}
  have hG : LL hvt hR A (Λ + Λs) Λ₂ ⊓ W ≤ Submodule.span A G := fun z hz ↦
    mem_of_fW_tmul_mem (Λ + Λs) Λ₂ ν (Submodule.span A G)
      (fun w₁ w₂ h ↦ Submodule.subset_span ⟨(w₁, w₂), h, rfl⟩) hz.1 hz.2
  have hXfg : X.FG := ((Submodule.fg_span ((finite_pairs ν).image _)).map Ψ).of_le
    (Submodule.map_mono hG)
  -- the generators
  have hgen : ∀ w₁ w₂ : List I, wordWeight w₁ + wordWeight w₂ = ν →
      Ψ (TensorModule.mk _ _ (fW hvt hR (Λ + Λs) w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂)) ∈
        lat hvt hR A (Λ + Λs + Λ₂) ⊔ ϖ • X := by
    intro w₁ w₂ hw
    rcases w₂ with _ | ⟨i, u⟩
    · refine Submodule.mem_sup_left ?_
      have hw₁ : wordWeight w₁ = ν := by simpa using hw
      exact hpur Λ Λ₂ _ (IrreducibleModule.fWord_mem_lattice hR _ (Λ + Λs).2 A w₁)
        (hw₁ ▸ fW_mem_wsp hvt hR (Λ + Λs) w₁)
    · have hlen : w₁.length + u.length = r := by
        have := congrArg Finsupp.degree hw
        rw [wordWeight_cons, map_add, map_add, Finsupp.degree_single, degree_wordWeight,
          degree_wordWeight, hν] at this
        omega
      obtain ⟨z, hz, hzw, hsub⟩ := fW_tmul_cons_sub_mem hϖ hϖv (d := r) hA hB hC
        (Λ₁ := Λ + Λs) (Λ₂ := Λ₂) i w₁ u hlen
      have hfz : Ψ (fT hvt hR (Λ + Λs) Λ₂ i z) ∈ lat hvt hR A (Λ + Λs + Λ₂) := by
        change tensorProj hvt hR (Λ + Λs).2 Λ₂.2 (fT hvt hR (Λ + Λs) Λ₂ i z) ∈ _
        rw [map_kashiwaraF (pow_ne_one_of_transcendental' hvt) (isIntT hvt hR (Λ + Λs) Λ₂) i
          (isInt hvt hR (Λ + Λs + Λ₂)) _ z]
        refine kashiwaraF_mem_lat _ i (hF (Λ + Λs) Λ₂ _ ?_ z hz hzw)
        rw [map_add, degree_wordWeight, degree_wordWeight, hlen]
      have hgw := fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) (Λ + Λs) Λ₂ w₁ (i :: u)
      rw [hw] at hgw
      have hfzw : fT hvt hR (Λ + Λs) Λ₂ i z ∈
          weightSpace R v (TM v (Λ + Λs) Λ₂) ((Λ + Λs).1 + Λ₂.1 - R.rootSum ν) := by
        have := kashiwaraF_mem_weightSpace (pow_ne_one_of_transcendental' hvt)
          (isIntT hvt hR (Λ + Λs) Λ₂) i hzw
        convert this using 2
        rw [← hw, wordWeight_cons, R.rootSum_add, R.rootSum_add, R.rootSum_add,
          R.rootSum_single, one_nsmul]
        abel
      obtain ⟨z₀, hz₀, hz₀w, he⟩ := TensorModule.exists_smul_weight hϖ0 hsub (sub_mem hgw hfzw)
      have : Ψ (TensorModule.mk _ _ (fW hvt hR (Λ + Λs) w₁ ⊗ₜ[k] fW hvt hR Λ₂ (i :: u))) =
          Ψ (fT hvt hR (Λ + Λs) Λ₂ i z) + ϖ • Ψ z₀ := by
        rw [← map_smul, ← he, ← map_add, add_sub_cancel]
      rw [this]
      exact Submodule.add_mem_sup hfz
        (Submodule.smul_mem_pointwise_smul _ _ _ ⟨z₀, ⟨hz₀, hz₀w⟩, rfl⟩)
  have hall : LL hvt hR A (Λ + Λs) Λ₂ ⊓ W ≤
      (lat hvt hR A (Λ + Λs + Λ₂) ⊔ ϖ • X).comap Ψ := fun z hz ↦
    mem_of_fW_tmul_mem (Λ + Λs) Λ₂ ν _ hgen hz.1 hz.2
  have hX : X ≤ lat hvt hR A (Λ + Λs + Λ₂) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hXfg (I := Ideal.span {ϖ})
      (((Ideal.span_singleton_le_iff_mem _).2 hϖ).trans
        (IsLocalRing.maximalIdeal_le_jacobson _)) ?_
    rw [Submodule.ideal_span_singleton_smul]
    rintro _ ⟨z, hz, rfl⟩
    exact hall hz
  exact fun z hz hzw ↦ hX ⟨z, ⟨hz, hzw⟩, rfl⟩

end Main

end GrandLoop

end LieLean.QuantumGroup
