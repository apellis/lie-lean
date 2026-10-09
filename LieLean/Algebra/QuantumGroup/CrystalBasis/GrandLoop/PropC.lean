/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Projection

/-!
# Kashiwara's grand loop: the statement `C(r)`

We prove `C(r)` ([HK] Prop. 5.3.16): for `b, b'` in `B(λ)` of depths `r - 1`, `r`,
`f̃ᵢ b = b' ↔ b = ẽᵢ b'` (`GrandLoop.propC_add_two`). The direction `⟹` is a string computation.
For `⟸` we follow [HK]: first for `λ = λ₁ + Λⱼ` with `λ₁` large and `Λⱼ` fundamental, using
[HK] Lemma 5.3.4 (`GrandLoop.fTw_fund`), the rule `f̃ᵢ ẽᵢ z ≡ z` on tensors with `ẽᵢ z ≢ 0`
(`GrandLoop.fT_eT_tmul_sub`, [HK] Lemma 5.3.2 (4)) and [HK] Lemma 5.3.15
(`GrandLoop.tensorProj_mem_lat_of_large`); then for arbitrary `λ` through `V(λ₁ + λ)` and the map
`S`.

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

section Helpers

variable [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖv : algebraMap A k ϖ = v⁻¹)
include hϖ hϖv

/-- `ẽᵢ (v_{λ₁} ⊗ y) ≡ v_{λ₁} ⊗ ẽᵢ y` for `y ∈ L(λ₂)` of depth `d`, given `A` up to `d`
([HK] Lemma 5.3.11 (1), library order). -/
lemma eT_hwv_tmul_mem {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s) {Λ₁ Λ₂ : Dom R} (i : I)
    {ν : I →₀ ℕ} (hν : ν.degree = d) {y : IrreducibleModule R v Λ₂.1}
    (hy : y ∈ lat hvt hR A Λ₂) (hyw : y ∈ wsp Λ₂ ν) :
    eT hvt hR Λ₁ Λ₂ i (TensorModule.mk _ _ (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k] y)) -
      TensorModule.mk _ _ (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k] eK hvt hR Λ₂ i y) ∈
      ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hv' := pow_ne_one_of_transcendental' hvt
  obtain ⟨N, η, h1, hE, h2, -, hsum⟩ := exists_sum_dF_weight hv' (isInt hvt hR Λ₂) i hyw
  have hη : ∀ j < N, η j ∈ lat hvt hR A Λ₂ :=
    mem_of_sum_mem_weight hv' (isInt hvt hR Λ₂) i (fun _ hy ↦ kashiwaraF_mem_lat Λ₂ i hy) N _ η
      h1 hE h2 (fun j y hy hyw ↦ localE hA Λ₂ hν i j hy hyw) (hsum ▸ hy)
  have h := eT_hwv_tmul_sub hϖ hϖv (Λ₁ := Λ₁) i (n := 0) h1 hE h2
    (fun j hj ↦ mem_negLat.2 (by simpa using hη j hj))
  rw [← hsum] at h
  obtain ⟨z₀, hz₀, he⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
  rw [← he]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (by simpa using lattice_negLat_right (n := 0) hz₀)

/-- **`f̃ᵢ ẽᵢ z ≡ z`** for `z = f̃_{w₁} v ⊗ f̃_{w₂} v` with `ẽᵢ z ∉ ϖ (L ⊗ L)` ([HK]
Lemma 5.3.2 (4), library order). -/
theorem fT_eT_tmul_sub {d e : ℕ} (hA : ∀ s ≤ d + 1, PropA hvt hR A s)
    (hB : ∀ s ≤ e, PropB hvt hR A ϖ s) (hC : ∀ s ≤ e, PropC hvt hR A ϖ s) {Λ₁ Λ₂ : Dom R}
    (i : I) {w₁ w₂ : List I} (h₁ : w₁.length ≤ e) (h₂ : w₂.length ≤ e)
    (hw : w₁.length + w₂.length = d + 1)
    (he : eT hvt hR Λ₁ Λ₂ i (TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂)) ∉
      ϖ • LL hvt hR A Λ₁ Λ₂) :
    fT hvt hR Λ₁ Λ₂ i (eT hvt hR Λ₁ Λ₂ i
        (TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂))) -
      TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  set x := fW hvt hR Λ₁ w₁
  set y := fW hvt hR Λ₂ w₂
  set z := TensorModule.mk (IrreducibleModule R v Λ₁.1) (IrreducibleModule R v Λ₂.1) (x ⊗ₜ[k] y)
  have hxL : x ∈ lat hvt hR A Λ₁ := IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁
  have hyL : y ∈ lat hvt hR A Λ₂ := IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂
  have hzw : z ∈ weightSpace R v (TM v Λ₁ Λ₂)
      (Λ₁.1 + Λ₂.1 - R.rootSum (wordWeight w₁ + wordWeight w₂)) :=
    fW_tmul_mem_weightSpace Λ₁ Λ₂ w₁ w₂
  have hdeg : (wordWeight w₁ + wordWeight w₂).degree = d + 1 := by
    rw [map_add, degree_wordWeight, degree_wordWeight, hw]
  have hsmul : z ∈ ϖ • LL hvt hR A Λ₁ Λ₂ → False := fun h ↦
    he (eT_mem_smul_LL hϖ hϖv hA i hdeg h hzw)
  have hx0 : x ∉ ϖ • lat hvt hR A Λ₁ := fun h ↦ hsmul (tmul_mem_smul_left h hyL)
  have hy0 : y ∉ ϖ • lat hvt hR A Λ₂ := fun h ↦ hsmul (tmul_mem_smul_right hxL h)
  obtain ⟨k₁, a, uu, hxs⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ₁ i (degree_wordWeight w₁) hxL
    (fW_mem_wsp hvt hR Λ₁ w₁) (w := w₁) (by simp [x]) hx0
  obtain ⟨k₂, b, u', hys⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ₂ i (degree_wordWeight w₂) hyL
    (fW_mem_wsp hvt hR Λ₂ w₂) (w := w₂) (by simp [y]) hy0
  have hrule := eT_tmul hϖ hϖv (fun s hs ↦ hA s (by omega)) (fun s hs ↦ hA s (by omega))
    (degree_wordWeight w₁) (degree_wordWeight w₂) hxs hys
  have hezw := kashiwaraE_mem_weightSpace (pow_ne_one_of_transcendental' hvt)
    (isIntT hvt hR Λ₁ Λ₂) i hzw
  split_ifs at hrule with hc
  · -- `ẽᵢ z ≡ x ⊗ ẽᵢ y`
    by_cases hk : k₂ = 0
    · exfalso
      have h0 := hys.eK_sub (fun s hs ↦ hA s (by omega)) (degree_wordWeight w₂) hϖ0
      simp only [hk, ↓reduceIte, sub_zero] at h0
      exact he (by simpa using add_mem hrule (tmul_mem_smul_right hxL h0))
    obtain ⟨ν₂', hν₂'⟩ := hys.exists_pred (by omega)
    have hdeg₂ : ν₂'.degree = w₂.length - 1 := by
      have := degree_wordWeight w₂
      rw [hν₂', map_add, Finsupp.degree_single] at this
      omega
    have hpos₂ : 1 ≤ w₂.length := by
      have := degree_wordWeight w₂
      rw [hν₂', map_add, Finsupp.degree_single] at this
      omega
    have hy'' := hys.kashiwaraE (fun s hs ↦ hA s (by omega)) (degree_wordWeight w₂) hϖ0 hν₂'
      (by omega)
    have hf := fT_tmul hϖ hϖv (fun s hs ↦ hA s (by omega)) (fun s hs ↦ hA s (by omega))
      (degree_wordWeight w₁) hdeg₂ hxs hy''
    simp only [show k₁ < b - (k₂ - 1) by have := hys.le; omega, ↓reduceIte] at hf
    have hfy := (hy''.kashiwaraF (by have := hys.le; omega)).sub
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k₂)] at hfy
    have hd : fK hvt hR Λ₂ i (eK hvt hR Λ₂ i y) - y ∈ ϖ • lat hvt hR A Λ₂ := by
      have := sub_mem hfy hys.sub
      rwa [sub_sub_sub_cancel_right] at this
    have hw' : eT hvt hR Λ₁ Λ₂ i z - TensorModule.mk _ _ (x ⊗ₜ[k] eK hvt hR Λ₂ i y) ∈
        weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum (wordWeight w₁ + ν₂')) := by
      refine sub_mem ?_ ?_
      · convert hezw using 2
        rw [hν₂', R.rootSum_add, R.rootSum_add, R.rootSum_add, R.rootSum_single, one_nsmul]
        abel
      · convert TensorModule.tmul_mem_weightSpace hxs.x_wt hy''.x_wt using 2
        rw [R.rootSum_add]; abel
    have h1 := fT_mem_smul_LL hϖ hϖv (d := d) (fun s hs ↦ hA s (by omega)) i
      (by rw [map_add, degree_wordWeight, hdeg₂]; omega) hrule hw'
    have h2 := tmul_mem_smul_right (Λ₁ := Λ₁) hxL hd
    have := add_mem (add_mem h1 hf) h2
    convert this using 1
    rw [map_sub, tmul_sub, map_sub]
    abel
  · -- `ẽᵢ z ≡ ẽᵢ x ⊗ y`
    have hk1 : 1 ≤ k₁ := by omega
    obtain ⟨ν₁', hν₁'⟩ := hxs.exists_pred hk1
    have hdeg₁ : ν₁'.degree = w₁.length - 1 := by
      have := degree_wordWeight w₁
      rw [hν₁', map_add, Finsupp.degree_single] at this
      omega
    have hpos₁ : 1 ≤ w₁.length := by
      have := degree_wordWeight w₁
      rw [hν₁', map_add, Finsupp.degree_single] at this
      omega
    have hx'' := hxs.kashiwaraE (fun s hs ↦ hA s (by omega)) (degree_wordWeight w₁) hϖ0 hν₁' hk1
    have hf := fT_tmul hϖ hϖv (fun s hs ↦ hA s (by omega)) (fun s hs ↦ hA s (by omega))
      hdeg₁ (degree_wordWeight w₂) hx'' hys
    simp only [show ¬(k₁ - 1 < b - k₂) by omega, ↓reduceIte] at hf
    have hfx := (hx''.kashiwaraF (by have := hxs.le; omega)).sub
    rw [Nat.sub_add_cancel hk1] at hfx
    have hd : fK hvt hR Λ₁ i (eK hvt hR Λ₁ i x) - x ∈ ϖ • lat hvt hR A Λ₁ := by
      have := sub_mem hfx hxs.sub
      rwa [sub_sub_sub_cancel_right] at this
    have hw' : eT hvt hR Λ₁ Λ₂ i z - TensorModule.mk _ _ (eK hvt hR Λ₁ i x ⊗ₜ[k] y) ∈
        weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum (ν₁' + wordWeight w₂)) := by
      refine sub_mem ?_ ?_
      · convert hezw using 2
        rw [hν₁', R.rootSum_add, R.rootSum_add, R.rootSum_add, R.rootSum_single, one_nsmul]
        abel
      · convert TensorModule.tmul_mem_weightSpace hx''.x_wt hys.x_wt using 2
        rw [R.rootSum_add]; abel
    have h1 := fT_mem_smul_LL hϖ hϖv (d := d) (fun s hs ↦ hA s (by omega)) i
      (by rw [map_add, degree_wordWeight, hdeg₁]; omega) hrule hw'
    have h2 := tmul_mem_smul_left (Λ₂ := Λ₂) hd hyL
    have := add_mem (add_mem h1 hf) h2
    convert this using 1
    rw [map_sub, sub_tmul, map_sub]
    abel

end Helpers

/-! ### `C(r)`, direction `⟹` -/

section Forward

variable (hϖv : algebraMap A k ϖ = v⁻¹)
include hϖv

/-- **`C(r)`, direction `⟹`**: `f̃ᵢ b ≡ b'` implies `b ≡ ẽᵢ b'`. -/
theorem propC_forward {d : ℕ} (hA : ∀ s ≤ d + 1, PropA hvt hR A s)
    (hB : ∀ s ≤ d, PropB hvt hR A ϖ s) (hC : ∀ s ≤ d, PropC hvt hR A ϖ s) (Λ : Dom R) (i : I)
    {w w' : List I} (hw : w.length = d) (hb0 : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ)
    (hb'0 : fW hvt hR Λ w' ∉ ϖ • lat hvt hR A Λ)
    (h : fK hvt hR Λ i (fW hvt hR Λ w) - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ) :
    fW hvt hR Λ w - eK hvt hR Λ i (fW hvt hR Λ w') ∈ ϖ • lat hvt hR A Λ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  set b := fW hvt hR Λ w
  set b' := fW hvt hR Λ w'
  have hbL : b ∈ lat hvt hR A Λ := IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A w
  obtain ⟨kk, a, u, hxs⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ i (degree_wordWeight w) hbL
    (fW_mem_wsp hvt hR Λ w) (w := w) (by simp [b]) hb0
  have hfb0 : fK hvt hR Λ i b ∉ ϖ • lat hvt hR A Λ := fun hf ↦ hb'0 (by
    have := sub_mem hf h; rwa [sub_sub_cancel] at this)
  by_cases hka : kk + 1 ≤ a
  swap
  · exact absurd (hxs.kashiwaraF_mem (by have := hxs.le; omega)) hfb0
  have hfb := hxs.kashiwaraF hka
  have hwt : wordWeight w' = wordWeight w + Finsupp.single i 1 :=
    wordWeight_eq_of_sub_mem hvt hR A ϖ Λ hfb.x_wt hfb0 h
  have hdeg : (wordWeight w + Finsupp.single i 1).degree = d + 1 := by
    rw [map_add, degree_wordWeight, Finsupp.degree_single, hw]
  have he := (hfb.kashiwaraE (fun s hs ↦ hA s hs) hdeg hϖ0 rfl (by omega)).sub
  rw [Nat.add_sub_cancel] at he
  have hb'w : b' ∈ wsp Λ (wordWeight w + Finsupp.single i 1) := hwt ▸ fW_mem_wsp hvt hR Λ w'
  have hl := localE_smul (fun s hs ↦ hA s hs) Λ hdeg i 0 hϖ0 h
    (by simpa using sub_mem hfb.x_wt hb'w)
  rw [map_sub] at hl
  have := add_mem (sub_mem hxs.sub he) hl
  convert this using 1
  abel

end Forward

/-! ### `C(r)`, direction `⟸`, for `λ = λ₁ + Λⱼ` with `λ₁` large -/

section BackwardLarge

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
include hinj hϖ hϖv

omit [IsDomain A] [IsDiscreteValuationRing A] hinj hϖ in
/-- `Ψ(ϖ (L ⊗ L)) ⊆ ϖ L` on a weight space where `Ψ(L ⊗ L) ⊆ L`. -/
lemma tensorProj_mem_smul_of {Λ₁ Λ₂ : Dom R} {μ : Y →+ ℤ}
    (hP : ∀ z ∈ LL hvt hR A Λ₁ Λ₂, z ∈ weightSpace R v (TM v Λ₁ Λ₂) μ →
      tensorProj hvt hR Λ₁.2 Λ₂.2 z ∈ lat hvt hR A (Λ₁ + Λ₂))
    {z : TM v Λ₁ Λ₂} (hz : z ∈ ϖ • LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v (TM v Λ₁ Λ₂) μ) :
    tensorProj hvt hR Λ₁.2 Λ₂.2 z ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂) := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨z₀, hz₀, hz₀w, rfl⟩ := TensorModule.exists_smul_weight hϖ0 hz hzw
  rw [smul_tensorProj]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (hP z₀ hz₀ hz₀w)

/-- **`C(r)`, direction `⟸`, for `λ₁ + Λⱼ`** with `Ψ` known on `L(λ₁) ⊗ L(Λⱼ)` in depth `r`
(e.g. `λ₁` large, [HK] Lemma 5.3.15), `Λⱼ` fundamental, and `j` the second letter of `b'`. -/
theorem propC_backward_of {n : ℕ} (hA : ∀ s ≤ n + 2, PropA hvt hR A s)
    (hB : ∀ s ≤ n + 1, PropB hvt hR A ϖ s) (hC : ∀ s ≤ n + 1, PropC hvt hR A ϖ s)
    (hF : PropF hvt hR A (n + 1)) {Λ₁ Λj : Dom R} {j : I}
    (hj : ∀ i, Λj.1 (R.coroot i) = if i = j then 1 else 0) (i₀ i : I) (u w : List I)
    (hu : u.length = n) (hw : w.length = n + 1)
    (hΨ : ∀ z ∈ LL hvt hR A Λ₁ Λj, z ∈ weightSpace R v (TM v Λ₁ Λj)
      (Λ₁.1 + Λj.1 - R.rootSum (wordWeight (u ++ [j, i₀]))) →
      tensorProj hvt hR Λ₁.2 Λj.2 z ∈ lat hvt hR A (Λ₁ + Λj))
    (hb0 : fW hvt hR (Λ₁ + Λj) w ∉ ϖ • lat hvt hR A (Λ₁ + Λj))
    (h : fW hvt hR (Λ₁ + Λj) w - eK hvt hR (Λ₁ + Λj) i (fW hvt hR (Λ₁ + Λj) (u ++ [j, i₀])) ∈
      ϖ • lat hvt hR A (Λ₁ + Λj)) :
    fK hvt hR (Λ₁ + Λj) i (fW hvt hR (Λ₁ + Λj) w) - fW hvt hR (Λ₁ + Λj) (u ++ [j, i₀]) ∈
      ϖ • lat hvt hR A (Λ₁ + Λj) := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  set w' := u ++ [j, i₀]
  set vv := TensorModule.mk (IrreducibleModule R v Λ₁.1) (IrreducibleModule R v Λj.1)
    (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k] IrreducibleModule.hwv R v Λj.1)
  set W := fTw hvt hR Λ₁ Λj w' vv
  have hlen : w'.length = n + 2 := by simp [w', hu]
  have hdeg : (wordWeight w').degree = n + 2 := by rw [degree_wordWeight, hlen]
  have hvvw : vv ∈ weightSpace R v (TM v Λ₁ Λj) (Λ₁.1 + Λj.1 - R.rootSum 0) := by
    simpa using fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λj [] []
  have hWw : W ∈ weightSpace R v (TM v Λ₁ Λj) (Λ₁.1 + Λj.1 - R.rootSum (wordWeight w')) := by
    simpa using fTw_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λj w' hvvw
  have hWL : W ∈ LL hvt hR A Λ₁ Λj := fTw_mem_LL hϖ hϖv w' (ν := 0)
    (fun s hs ↦ hA s (by simp at hs; omega)) (fW_tmul_mem_LL Λ₁ Λj [] []) hvvw
  obtain ⟨w₁, w₂, hw₁, hw₂, hw₁₂, hwt₁₂, hsub⟩ := fTw_fund hϖ hϖv hinj hj u i₀
    (fun s hs ↦ hA s (by omega)) (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega))
  set z := TensorModule.mk (IrreducibleModule R v Λ₁.1) (IrreducibleModule R v Λj.1)
    (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λj w₂)
  have hzw : z ∈ weightSpace R v (TM v Λ₁ Λj) (Λ₁.1 + Λj.1 - R.rootSum (wordWeight w')) := by
    have := fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λj w₁ w₂
    rwa [hwt₁₂] at this
  have hzL : z ∈ LL hvt hR A Λ₁ Λj := fW_tmul_mem_LL Λ₁ Λj w₁ w₂
  have hΨW : tensorProj hvt hR Λ₁.2 Λj.2 W = fW hvt hR (Λ₁ + Λj) w' := tensorProj_fTw Λ₁ Λj w'
  -- `ẽᵢ` on `W` and on `z`
  have heW : eT hvt hR Λ₁ Λj i W - eT hvt hR Λ₁ Λj i z ∈ ϖ • LL hvt hR A Λ₁ Λj := by
    rw [← map_sub]
    exact eT_mem_smul_LL hϖ hϖv hA i hdeg hsub (sub_mem hWw hzw)
  have hezw := kashiwaraE_mem_weightSpace (pow_ne_one_of_transcendental' hvt)
    (isIntT hvt hR Λ₁ Λj) i hzw
  have heWw := kashiwaraE_mem_weightSpace (pow_ne_one_of_transcendental' hvt)
    (isIntT hvt hR Λ₁ Λj) i hWw
  have hezL : eT hvt hR Λ₁ Λj i z ∈ LL hvt hR A Λ₁ Λj := eT_mem_LL hϖ hϖv hA i hdeg hzL hzw
  have heWL : eT hvt hR Λ₁ Λj i W ∈ LL hvt hR A Λ₁ Λj := eT_mem_LL hϖ hϖv hA i hdeg hWL hWw
  -- `ẽᵢ z ∉ ϖ (L ⊗ L)`
  have hez0 : eT hvt hR Λ₁ Λj i z ∉ ϖ • LL hvt hR A Λ₁ Λj := by
    intro hez
    have hW0 : eT hvt hR Λ₁ Λj i W ≠ 0 := by
      intro h0
      refine hb0 ?_
      have : eK hvt hR (Λ₁ + Λj) i (fW hvt hR (Λ₁ + Λj) w') = 0 := by
        rw [← hΨW, ← tensorProj_eT, h0, map_zero]
      simpa [this] using h
    obtain ⟨ν'', hν''⟩ := exists_rootSum_of_LL heWL heWw hW0
    have hd'' : ν''.degree = n + 1 := by
      have h1 : R.rootSum (ν'' + Finsupp.single i 1) = R.rootSum (wordWeight w') := by
        rw [R.rootSum_add, R.rootSum_single, one_nsmul, ← sub_eq_zero, ← sub_eq_zero.2 hν'']
        abel
      have := congrArg Finsupp.degree (LusztigCartanDatum.RootDatum.rootSum_injective hR h1)
      rw [map_add, Finsupp.degree_single, hdeg] at this
      omega
    have hEW : eT hvt hR Λ₁ Λj i W ∈ ϖ • LL hvt hR A Λ₁ Λj := by
      have := add_mem heW hez
      rwa [sub_add_cancel] at this
    have hΨe := tensorProj_mem_smul_of hϖv
      (fun z' hz' hz'w ↦ hF Λ₁ Λj ν'' hd'' z' hz' (hν'' ▸ hz'w)) hEW heWw
    rw [tensorProj_eT, hΨW] at hΨe
    have := add_mem h hΨe
    rw [sub_add_cancel] at this
    exact hb0 this
  -- `f̃ᵢ ẽᵢ z ≡ z`
  have hfe := fT_eT_tmul_sub hϖ hϖv (d := n + 1) (e := n + 1) hA hB hC i (by omega) (by omega)
    (by omega) hez0
  -- weights one step up
  have hez00 : eT hvt hR Λ₁ Λj i z ≠ 0 := fun h0 ↦ hez0 (by rw [h0]; exact zero_mem _)
  obtain ⟨ν'', hν''⟩ := exists_rootSum_of_LL hezL hezw hez00
  have hd'' : ν''.degree = n + 1 := by
    have h1 : R.rootSum (ν'' + Finsupp.single i 1) = R.rootSum (wordWeight w') := by
      rw [R.rootSum_add, R.rootSum_single, one_nsmul, ← sub_eq_zero, ← sub_eq_zero.2 hν'']
      abel
    have := congrArg Finsupp.degree (LusztigCartanDatum.RootDatum.rootSum_injective hR h1)
    rw [map_add, Finsupp.degree_single, hdeg] at this
    omega
  have hfW : fT hvt hR Λ₁ Λj i (eT hvt hR Λ₁ Λj i W) - fT hvt hR Λ₁ Λj i (eT hvt hR Λ₁ Λj i z) ∈
      ϖ • LL hvt hR A Λ₁ Λj := by
    rw [← map_sub]
    exact fT_mem_smul_LL hϖ hϖv (d := n + 1) (fun s hs ↦ hA s (by omega)) i hd'' heW
      (hν'' ▸ sub_mem heWw hezw)
  have htot : fT hvt hR Λ₁ Λj i (eT hvt hR Λ₁ Λj i W) - W ∈ ϖ • LL hvt hR A Λ₁ Λj := by
    have := add_mem (add_mem hfW hfe) (neg_mem hsub)
    convert this using 1
    abel
  have htotw : fT hvt hR Λ₁ Λj i (eT hvt hR Λ₁ Λj i W) - W ∈
      weightSpace R v (TM v Λ₁ Λj) (Λ₁.1 + Λj.1 - R.rootSum (wordWeight w')) := by
    refine sub_mem ?_ hWw
    have := kashiwaraF_mem_weightSpace (pow_ne_one_of_transcendental' hvt)
      (isIntT hvt hR Λ₁ Λj) i heWw
    rwa [add_sub_cancel_right] at this
  have hΨt := tensorProj_mem_smul_of hϖv hΨ htot htotw
  rw [map_sub, map_kashiwaraF (pow_ne_one_of_transcendental' hvt) (isIntT hvt hR Λ₁ Λj) i
    (isInt hvt hR (Λ₁ + Λj)), tensorProj_eT, hΨW] at hΨt
  have h2 := kashiwaraF_mem_smul_lat (Λ₁ + Λj) i h
  rw [map_sub] at h2
  have := add_mem h2 hΨt
  convert this using 1
  abel

end BackwardLarge

/-! ### `C(r)` -/

section Assembly

/-- `C(0)` (vacuous). -/
theorem propC_zero : PropC hvt hR A ϖ 0 := fun _ _ _ _ hw _ ↦ by omega

/-- `C(1)`. -/
theorem propC_one (hϖv : algebraMap A k ϖ = v⁻¹) (hinj : Function.Injective (algebraMap A k))
    (hϖu : ¬IsUnit ϖ) : PropC hvt hR A ϖ 1 := by
  intro Λ i w w' hw hw' hb0 hb'0
  obtain rfl : w = [] := List.length_eq_zero_iff.1 (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, w' = [j] := by
    rcases w' with _ | ⟨j, _ | ⟨_, _⟩⟩ <;> simp at hw'; exact ⟨j, rfl⟩
  constructor
  · exact propC_forward hϖv (d := 0) (fun s hs ↦ by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hs with rfl | rfl
      · exact propA_zero
      · exact propA_one) (fun s hs ↦ by obtain rfl : s = 0 := (by omega); exact propB_zero)
      (fun s hs ↦ by obtain rfl : s = 0 := (by omega); exact propC_zero) Λ i rfl hb0 hb'0
  · intro h
    by_cases hij : i = j
    · subst hij
      rw [← fW_cons, sub_self]; exact zero_mem _
    exfalso
    set hv' := pow_ne_one_of_transcendental' hvt
    have hvn := mem_nodeWt_of_mem (i := j)
      (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := v) (Λ := Λ.1))
    have hf : fW hvt hR Λ [j] =
        dFV (hvt := hvt) (hR := hR) Λ j 1 (IrreducibleModule.hwv R v Λ.1) := by
      have := kashiwaraF_dF (hvt := hvt) (hR := hR) hvn (IrreducibleModule.E_smul_hwv j) 0
      rw [IntegrableSl2.dF_zero] at this
      rw [fW_cons, fW_nil]
      exact this
    have hE : E R v i • fW hvt hR Λ [j] = 0 := by
      rw [hf, IntegrableSl2.dF_apply, smul_comm, pow_one]
      change _ • (E R v i • F R v j • IrreducibleModule.hwv R v Λ.1) = 0
      have h := E_mul_F_sub R v i j
      simp only [hij, ↓reduceIte, sub_eq_zero] at h
      rw [← mul_smul, h, mul_smul, IrreducibleModule.E_smul_hwv, smul_zero, smul_zero]
    have h0 : eK hvt hR Λ i (fW hvt hR Λ [j]) = 0 :=
      IntegrableSl2.eTilde_of_primitive (pow_d_ne_zero i) (pow_d_ne_one hv' i)
        (V := nodeSl2 R v _ hv' (isInt hvt hR Λ) i) hE
        (mem_nodeWt_of_mem (fW_mem_wsp hvt hR Λ [j]))
    rw [h0, sub_zero, fW_nil] at h
    exact hwv_notMem hinj hϖu Λ h

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
include hinj hϖ hϖv hk

/-- **`C(r)`** for `r ≥ 2` ([HK] Prop. 5.3.16). -/
theorem propC_add_two
    (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
    (ρ : Dom R) (hρ : ∀ i, 1 ≤ ρ.1 (R.coroot i)) {n : ℕ}
    (hA : ∀ s ≤ n + 2, PropA hvt hR A s) (hB : ∀ s ≤ n + 1, PropB hvt hR A ϖ s)
    (hC : ∀ s ≤ n + 1, PropC hvt hR A ϖ s) (hE : ∀ s ≤ n + 2, PropE hvt hR A s)
    (hF : PropF hvt hR A (n + 1)) : PropC hvt hR A ϖ (n + 2) := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  set hv' := pow_ne_one_of_transcendental' hvt
  choose Λf hΛf using hfund
  intro Λ i w w' hw0 hw' hb0 hb'0
  have hw : w.length = n + 1 := by omega
  constructor
  · exact propC_forward hϖv (d := n + 1) hA hB hC Λ i hw hb0 hb'0
  intro h
  obtain ⟨u, j, i₀, rfl⟩ : ∃ u j i₀, w' = u ++ [j, i₀] := by
    have hl : (w'.drop n).length = 2 := by simp; omega
    obtain ⟨a, b, hab⟩ : ∃ a b, w'.drop n = [a, b] := by
      match w'.drop n, hl with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    exact ⟨w'.take n, a, b, by rw [← hab, List.take_append_drop]⟩
  set w' := u ++ [j, i₀]
  have hu : u.length = n := by simp [w'] at hw'; omega
  have hdeg' : (wordWeight w').degree = n + 2 := by rw [degree_wordWeight, hw']
  have hdeg : (wordWeight w).degree = n + 1 := by rw [degree_wordWeight, hw]
  set Λj := Λf j
  obtain ⟨Λs, -, hlarge⟩ := tensorProj_mem_lat_of_large hk hinj hϖ hϖv (r := n + 1)
    (ν := wordWeight w') hdeg' hA hB hC (hE (n + 2) le_rfl) hF ρ hρ
  set μ' := Λs + Λj
  -- weights: `wt w' = wt w + αᵢ`
  have heb0 : eK hvt hR Λ i (fW hvt hR Λ w') ∉ ϖ • lat hvt hR A Λ := fun he ↦
    hb0 (by have := add_mem h he; rwa [sub_add_cancel] at this)
  have hebw := kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ) i (fW_mem_wsp hvt hR Λ w')
  obtain ⟨ν₀, hν₀⟩ := exists_eq_add_single hR hv' Λ (i := i) (j := 1) (ν := wordWeight w')
    (by rw [one_smul]; exact hebw) (fun h0 ↦ heb0 (by rw [h0]; exact zero_mem _))
  have hwt : wordWeight w = ν₀ := wordWeight_eq_of_sub_mem hvt hR A ϖ Λ
    (by
      have := kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ) i (fW_mem_wsp hvt hR Λ w')
      convert this using 2
      rw [hν₀, R.rootSum_add, R.rootSum_single, one_nsmul]; abel)
    heb0 (by have := neg_mem h; rwa [neg_sub] at this)
  have hww' : wordWeight w' = wordWeight w + Finsupp.single i 1 := by rw [hν₀, hwt]
  -- step (i): `ẽᵢ b' ≡ b` in `V(μ' + λ)`
  set vv := TensorModule.mk (IrreducibleModule R v μ'.1) (IrreducibleModule R v Λ.1)
    (IrreducibleModule.hwv R v μ'.1 ⊗ₜ[k] IrreducibleModule.hwv R v Λ.1)
  have hvvw : vv ∈ weightSpace R v (TM v μ' Λ) (μ'.1 + Λ.1 - R.rootSum 0) := by
    simpa using fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) μ' Λ [] []
  have hWw : ∀ x : List I, fTw hvt hR μ' Λ x vv ∈
      weightSpace R v (TM v μ' Λ) (μ'.1 + Λ.1 - R.rootSum (wordWeight x)) := fun x ↦ by
    simpa using fTw_mem_weightSpace (hvt := hvt) (hR := hR) μ' Λ x hvvw
  have hmw : ∀ x : List I, TensorModule.mk _ _ (IrreducibleModule.hwv R v μ'.1 ⊗ₜ[k]
      fW hvt hR Λ x) ∈ weightSpace R v (TM v μ' Λ) (μ'.1 + Λ.1 - R.rootSum (wordWeight x)) :=
    fun x ↦ by simpa using fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) μ' Λ [] x
  have hd' := fTw_hwv_tmul hϖ hϖv hinj (Λ₁ := μ') (Λ₂ := Λ) w' (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) hb'0
  have hd := fTw_hwv_tmul hϖ hϖv hinj (Λ₁ := μ') (Λ₂ := Λ) w (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) hb0
  have he1 : eT hvt hR μ' Λ i (fTw hvt hR μ' Λ w' vv) - eT hvt hR μ' Λ i
      (TensorModule.mk _ _ (IrreducibleModule.hwv R v μ'.1 ⊗ₜ[k] fW hvt hR Λ w')) ∈
      ϖ • LL hvt hR A μ' Λ := by
    rw [← map_sub]
    exact eT_mem_smul_LL hϖ hϖv hA i hdeg' hd' (sub_mem (hWw w') (hmw w'))
  have he2 := eT_hwv_tmul_mem hϖ hϖv (Λ₁ := μ') hA i hdeg'
    (IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A w') (fW_mem_wsp hvt hR Λ w')
  have he3 := tmul_mem_smul_right (Λ₁ := μ')
    (IrreducibleModule.hwv_mem_lattice hR hv' μ'.2 A) (by have := neg_mem h; rwa [neg_sub] at this)
  have htot : eT hvt hR μ' Λ i (fTw hvt hR μ' Λ w' vv) - fTw hvt hR μ' Λ w vv ∈
      ϖ • LL hvt hR A μ' Λ := by
    have := sub_mem (add_mem (add_mem he1 he2) he3) hd
    convert this using 1
    rw [tmul_sub, map_sub]
    abel
  have htotw : eT hvt hR μ' Λ i (fTw hvt hR μ' Λ w' vv) - fTw hvt hR μ' Λ w vv ∈
      weightSpace R v (TM v μ' Λ) (μ'.1 + Λ.1 - R.rootSum (wordWeight w)) := by
    refine sub_mem ?_ (hWw w)
    convert kashiwaraE_mem_weightSpace hv' (isIntT hvt hR μ' Λ) i (hWw w') using 2
    rw [hww', R.rootSum_add, R.rootSum_single, one_nsmul]; abel
  have hΨ := tensorProj_mem_smul_of hϖv (fun z hz hzw ↦ hF μ' Λ (wordWeight w) hdeg z hz hzw)
    htot htotw
  rw [map_sub, tensorProj_eT, tensorProj_fTw, tensorProj_fTw] at hΨ
  -- `b, b' ∉ ϖ L(μ' + λ)`
  have hnot : ∀ (x : List I) (m : ℕ), x.length = m + 1 → m ≤ n + 1 →
      fW hvt hR Λ x ∉ ϖ • lat hvt hR A Λ →
      fW hvt hR (μ' + Λ) x ∉ ϖ • lat hvt hR A (μ' + Λ) := by
    intro x m hx hm hx0 hmem
    have h1 := tensorEmb_mem_smul hϖv (n := m) (hE (m + 1) (by omega)) (Λ₁ := μ') (Λ₂ := Λ) i
      (ν := wordWeight x + Finsupp.single i 1)
      (by rw [map_add, degree_wordWeight, Finsupp.degree_single, hx]) hmem
      (by
        convert fW_mem_wsp hvt hR (μ' + Λ) x using 2
        rw [R.rootSum_add, R.rootSum_single, one_nsmul]; abel)
    rw [tensorEmb_fW] at h1
    have h2 := Sh_mem_smul h1
    have h3 := Sh_fTw_sub hϖ hϖv (Λ₁ := μ') (Λ₂ := Λ) x (fun s hs ↦ hA s (by omega))
      (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega))
    exact hx0 (by have := sub_mem h2 h3; rwa [sub_sub_cancel] at this)
  have hb0' := hnot w n hw (by omega) hb0
  have hb'0' := hnot w' (n + 1) hw' le_rfl hb'0
  -- step (ii), (iii): `f̃ᵢ b ≡ b'` in `V(λ + Λs + Λⱼ)`
  have e : μ' + Λ = (Λ + Λs) + Λj := Subtype.ext (by simp only [Dom.add_val, μ']; abel)
  have hbig := propC_backward_of hinj hϖ hϖv (n := n) hA hB hC hF (Λ₁ := Λ + Λs) (Λj := Λj)
    (hΛf j) i₀ i u w hu hw (hlarge Λ Λj) (e ▸ hb0')
    (by rw [← e]; have := neg_mem hΨ; rwa [neg_sub] at this)
  rw [← e] at hbig
  -- step (iv): back to `V(λ)` through `S ∘ Φ`
  have h1 := tensorEmb_mem_smul hϖv (n := n + 1) (hE (n + 2) le_rfl) (Λ₁ := μ') (Λ₂ := Λ) i
    (ν := wordWeight w' + Finsupp.single i 1)
    (by rw [map_add, degree_wordWeight, Finsupp.degree_single, hw']) hbig
    (by
      refine sub_mem ?_ ?_
      · convert kashiwaraF_mem_weightSpace hv' (isInt hvt hR (μ' + Λ)) i
          (fW_mem_wsp hvt hR (μ' + Λ) w) using 2
        rw [hww', R.rootSum_add, R.rootSum_add, R.rootSum_single, one_nsmul]; abel
      · convert fW_mem_wsp hvt hR (μ' + Λ) w' using 2
        rw [R.rootSum_add, R.rootSum_single, one_nsmul]; abel)
  rw [map_sub, ← fW_cons, tensorEmb_fW, tensorEmb_fW] at h1
  have h2 := Sh_mem_smul h1
  rw [map_sub] at h2
  have h3 := Sh_fTw_sub hϖ hϖv (Λ₁ := μ') (Λ₂ := Λ) (i :: w)
    (fun s hs ↦ hA s (by simp at hs; omega))
    (fun s hs ↦ hB s (by simp at hs; omega)) (fun s hs ↦ hC s (by simp at hs; omega))
  have h4 := Sh_fTw_sub hϖ hϖv (Λ₁ := μ') (Λ₂ := Λ) w' (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega))
  rw [← fW_cons]
  have := add_mem (sub_mem h2 h3) h4
  convert this using 1
  simp only [w']
  abel

end Assembly

end GrandLoop

end LieLean.QuantumGroup
