/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityBase

/-!
# `B(∞)` and `B(λ)`

For dominant `λ`, `π_λ : L(∞) → L(λ)` induces `π̄_λ : B(∞) → B(λ) ∪ {0}`,
`f̃_w 1 ↦ f̃_w v_λ` (`GrandLoop.evq_fWord_sub_fW_mem`). We show:

* `π̄_λ` commutes with `ẽᵢ` on the elements with `π̄_λ(b) ≠ 0`
  (`GrandLoop.evq_kE_fWi_sub_mem`; [Jan] Lemma 10.13);
* `π̄_λ` is injective on `{b ∈ B(∞) | π̄_λ(b) ≠ 0}` (`GrandLoop.fWi_sub_mem_of_fW_sub_mem`;
  [Jan] Prop. 10.14), so it is a bijection of this set onto `B(λ)`.

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 10.13, 10.14 (finite type).
-/

open Finset Pointwise LusztigF TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

section Base

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

/-- `S ∘ Φ_{μ,λ}` maps `ϖ L(μ + λ)` into `ϖ L(λ)`. -/
lemma Sh_tensorEmb_mem_smul {μ Λ : Dom R} {x : IrreducibleModule R v (μ + Λ).1}
    (hx : x ∈ ϖ • lat hvt hR A (μ + Λ)) :
    Sh hvt hR μ Λ (tensorEmb hvt hR μ.2 Λ.2 x) ∈ ϖ • lat hvt hR A Λ := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  obtain ⟨z₀, hz₀, -, hz⟩ := TensorModule.exists_smul_weight (S := ⊤)
    (by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)) hx Submodule.mem_top
  rw [hz]
  refine Sh_mem_smul ?_
  rw [smul_tensorEmb]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (tensorEmb_mem_LL hϖ hϖv (fun s ↦ (hall s).1) hz₀)

/-- **[Jan] Lemma 10.13**: if `f̃_w v_λ ∉ ϖ L(λ)` then
`π_λ(ẽᵢ f̃_w 1) ≡ ẽᵢ f̃_w v_λ` modulo `ϖ L(λ)`. -/
theorem evq_kE_fWi_sub_mem (i : I) {w : List I} {Λ : Dom R}
    (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ) :
    evq hvt Λ (kE hvt i (fWi hvt w)) - eK hvt hR Λ i (fW hvt hR Λ w) ∈ ϖ • lat hvt hR A Λ := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  obtain ⟨r, hr⟩ := exists_evq_kashiwara_sub_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund i
    (fWi_mem_Uw w)
  obtain ⟨Λi, hΛi⟩ := hfund i
  let μ : Dom R := ⟨(r.toNat : ℤ) • Λi.1, fun j ↦ by
    rw [AddMonoidHom.smul_apply]; exact smul_nonneg (by positivity) (Λi.2 j)⟩
  have hμ : r ≤ (μ + Λ).1 (R.coroot i) := by
    change r ≤ (r.toNat : ℤ) • Λi.1 (R.coroot i) + Λ.1 (R.coroot i)
    simp only [hΛi i, ↓reduceIte, smul_eq_mul, mul_one]
    have := Λ.2 i
    omega
  -- in `L(μ + λ)`
  have h1 := evq_kE_sub_eK_fW_mem (hR := hR) hinj hϖ hϖv hk hfund i w (hr (μ + Λ) hμ).2
  -- `T = S ∘ Φ`
  have hT1 : Sh hvt hR μ Λ (tensorEmb hvt hR μ.2 Λ.2 (evq hvt (μ + Λ) (kE hvt i (fWi hvt w)))) =
      evq hvt Λ (kE hvt i (fWi hvt w)) := evq_add μ Λ _
  have hT2 := Sh_tensorEmb_mem_smul hinj hϖ hϖv hk hfund h1
  rw [map_sub, map_sub, hT1] at hT2
  -- `Φ (ẽᵢ f̃_w v) ≡ v ⊗ ẽᵢ f̃_w v`
  have hΦ : tensorEmb hvt hR μ.2 Λ.2 (eK hvt hR (μ + Λ) i (fW hvt hR (μ + Λ) w)) =
      eT hvt hR μ Λ i (fTw hvt hR μ Λ w (TensorModule.mk _ _ (IrreducibleModule.hwv R v μ.1 ⊗ₜ[k]
        IrreducibleModule.hwv R v Λ.1))) := by
    rw [tensorEmb_eK, tensorEmb_fW]
  have hz := fTw_hwv_tmul hϖ hϖv hinj (Λ₁ := μ) (Λ₂ := Λ) w (fun s _ ↦ (hall s).1)
    (fun s _ ↦ (hall s).2.1) (fun s _ ↦ (hall s).2.2.1) hw
  have hzw : fTw hvt hR μ Λ w (TensorModule.mk _ _ (IrreducibleModule.hwv R v μ.1 ⊗ₜ[k]
        IrreducibleModule.hwv R v Λ.1)) -
      TensorModule.mk _ _ (IrreducibleModule.hwv R v μ.1 ⊗ₜ[k] fW hvt hR Λ w) ∈
      weightSpace R v _ (μ.1 + Λ.1 - R.rootSum (wordWeight w)) := by
    have h1 := fTw_mem_weightSpace (hvt := hvt) (hR := hR) μ Λ w
      (fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) μ Λ [] [])
    have h2 := fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) μ Λ [] w
    simp only [wordWeight_nil, zero_add] at h1 h2
    exact sub_mem h1 h2
  have hez := eT_mem_smul_LL hϖ hϖv (d := (wordWeight w).degree) (fun s _ ↦ (hall s).1) i rfl hz
    hzw
  have hev := eT_hwv_tmul_mem hϖ hϖv (Λ₁ := μ) (fun s _ ↦ (hall s).1) i rfl
    (IrreducibleModule.fWord_mem_lattice hR _ Λ.2 A w) (fW_mem_wsp hvt hR Λ w)
  have hsum := add_mem hez hev
  rw [map_sub, sub_add_sub_cancel] at hsum
  have hS := Sh_mem_smul (Λ₁ := μ) (Λ₂ := Λ) hsum
  rw [map_sub, Sh_tmul, IrreducibleModule.form_hwv, one_smul, ← hΦ] at hS
  have := add_mem hT2 hS
  convert this using 1
  abel

/-- `π_λ(ϖ L(∞)) ⊆ ϖ L(λ)`. -/
lemma evq_mem_smul_lat {u : Um D v} (hu : u ∈ ϖ • latInf hvt A) (Λ : Dom R) :
    evq hvt Λ u ∈ ϖ • lat hvt hR A Λ := by
  obtain ⟨u₀, hu₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hu
  rw [← algebraMap_smul k ϖ u₀, map_smul, algebraMap_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _
    (evq_mem_lat_of_mem_latticeInf hinj hϖ hϖv hk hfund hu₀ Λ)

/-- **[Jan] Prop. 10.14**: `π̄_λ` is injective on `{b ∈ B(∞) | π̄_λ(b) ≠ 0}`: if
`f̃_w v_λ ∉ ϖ L(λ)` and `f̃_w v_λ ≡ f̃_{w'} v_λ` then `f̃_w 1 ≡ f̃_{w'} 1` modulo `ϖ L(∞)`. -/
theorem fWi_sub_mem_of_fW_sub_mem {Λ : Dom R} :
    ∀ n (w w' : List I), (wordWeight w).degree = n → fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ →
      fW hvt hR Λ w - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ →
      fWi (D := D) hvt w - fWi hvt w' ∈ ϖ • latInf hvt A := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  have hL := isCrystalLattice_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ
  have heS : ∀ i x, x ∈ ϖ • lat hvt hR A Λ → eK hvt hR Λ i x ∈ ϖ • lat hvt hR A Λ :=
    fun i _ hx ↦ LinearMap.map_mem_smul_of_mem ϖ (fun m hm ↦ hL.kashiwaraE_mem i m hm) hx
  intro n
  induction n with
  | zero =>
    intro w w' hn hw h
    have hw' : wordWeight w' = wordWeight w :=
      wordWeight_eq_of_sub_mem hvt hR A ϖ Λ (fW_mem_wsp hvt hR Λ w) hw h
    have h0 : w = [] := List.eq_nil_of_length_eq_zero (by rw [← degree_wordWeight, hn])
    have h0' : w' = [] := List.eq_nil_of_length_eq_zero (by
      rw [← degree_wordWeight, hw', hn])
    subst h0 h0'
    simp
  | succ n ih =>
    intro w w' hn hw h
    have hw' : wordWeight w' = wordWeight w :=
      wordWeight_eq_of_sub_mem hvt hR A ϖ Λ (fW_mem_wsp hvt hR Λ w) hw h
    have hw'0 : fW hvt hR Λ w' ∉ ϖ • lat hvt hR A Λ := fun h' ↦ hw (by simpa using add_mem h h')
    obtain ⟨j, w₀, rfl⟩ : ∃ j w₀, w = j :: w₀ := by
      cases w with
      | nil => simp at hn
      | cons j w₀ => exact ⟨j, w₀, rfl⟩
    have hw₀ : fW hvt hR Λ w₀ ∉ ϖ • lat hvt hR A Λ := fun h' ↦
      hw (by rw [fW_cons]; exact kashiwaraF_mem_smul_lat Λ j h')
    have hn₀ : (wordWeight w₀).degree = n := by
      rw [wordWeight_cons, map_add, Finsupp.degree_single] at hn; omega
    -- `ẽⱼ f̃_{j w₀} v ≡ f̃_{w₀} v`
    have hE : eK hvt hR Λ j (fW hvt hR Λ (j :: w₀)) - fW hvt hR Λ w₀ ∈ ϖ • lat hvt hR A Λ :=
      (fK_sub_mem_iff (fun r ↦ (hall r).2.2.1) Λ j hw₀ hw).1 (by simp)
    have hE' : eK hvt hR Λ j (fW hvt hR Λ w') - fW hvt hR Λ w₀ ∈ ϖ • lat hvt hR A Λ := by
      have := heS j _ h
      rw [map_sub] at this
      simpa using sub_mem hE this
    -- the representatives of `ẽⱼ b`, `ẽⱼ b'`
    have key : ∀ u : List I, fW hvt hR Λ u ∉ ϖ • lat hvt hR A Λ →
        eK hvt hR Λ j (fW hvt hR Λ u) - fW hvt hR Λ w₀ ∈ ϖ • lat hvt hR A Λ →
        ∃ u₁, kE (D := D) hvt j (fWi hvt u) ∉ ϖ • latInf hvt A ∧
          kE (D := D) hvt j (fWi hvt u) - fWi hvt u₁ ∈ ϖ • latInf hvt A ∧
          fWi (D := D) hvt w₀ - fWi hvt u₁ ∈ ϖ • latInf hvt A := by
      intro u hu hEu
      have h13 := evq_kE_fWi_sub_mem hinj hϖ hϖv hk hfund j hu
      have hev : evq hvt Λ (kE (D := D) hvt j (fWi hvt u)) - fW hvt hR Λ w₀ ∈
          ϖ • lat hvt hR A Λ := by simpa using add_mem h13 hEu
      have hnot : kE (D := D) hvt j (fWi hvt u) ∉ ϖ • latInf hvt A := fun h' ↦
        hw₀ (by simpa using sub_mem (evq_mem_smul_lat hinj hϖ hϖv hk hfund h' Λ) hev)
      rcases kE_fWi_cases (hR := hR) hinj hϖ hϖv hk hfund j u with h' | ⟨u₁, hu₁⟩
      · exact absurd h' hnot
      refine ⟨u₁, hnot, hu₁, ?_⟩
      have h1 := evq_mem_smul_lat (hR := hR) hinj hϖ hϖv hk hfund hu₁ Λ
      rw [map_sub] at h1
      have h2 := evq_fWord_sub_fW_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund u₁ Λ
      have h3 : fW hvt hR Λ w₀ - fW hvt hR Λ u₁ ∈ ϖ • lat hvt hR A Λ := by
        have := sub_mem h2 (sub_mem hev h1)
        convert this using 1; abel
      exact ih w₀ u₁ hn₀ hw₀ h3
    obtain ⟨u₁, hu₁0, hu₁, hwu₁⟩ := key (j :: w₀) hw hE
    obtain ⟨u₁', hu₁'0, hu₁', hwu₁'⟩ := key w' hw'0 hE'
    have hc1 := fWi_sub_mem_of_kE (hR := hR) hinj hϖ hϖv hk hfund j hu₁0 hu₁
    have hc2 := fWi_sub_mem_of_kE (hR := hR) hinj hϖ hϖv hk hfund j hu₁'0 hu₁'
    have hd : fWi (D := D) hvt u₁ - fWi hvt u₁' ∈ ϖ • latInf hvt A := by
      have := sub_mem hwu₁' hwu₁
      convert this using 1; abel
    have hff : fWi (D := D) hvt (j :: u₁) - fWi hvt (j :: u₁') ∈ ϖ • latInf hvt A := by
      have := LinearMap.map_mem_smul_of_mem ϖ
        (fun m hm ↦ kashiwaraF_mem_latInf' (hvt := hvt) (A := A) j m hm) hd
      rwa [map_sub] at this
    have := add_mem (add_mem hc1 hff) (neg_mem hc2)
    convert this using 1
    abel

end Base

end GrandLoop

end LieLean.QuantumGroup
