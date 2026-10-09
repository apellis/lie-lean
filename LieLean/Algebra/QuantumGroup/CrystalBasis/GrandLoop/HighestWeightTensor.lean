/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.HighestWeightSimilarity
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorIndependence

/-!
# The embedding `B(λ₁ + λ₂) → B(λ₁) ⊗ B(λ₂)`

The embedding `Φ : V(λ₁ + λ₂) → V(λ₁) ⊗ V(λ₂)`, `v ↦ v ⊗ v`, maps `f̃_w v_{λ₁+λ₂}` to
`f̃_w (v ⊗ v) ≡ f̃_{w₁} v_{λ₁} ⊗ f̃_{w₂} v_{λ₂}` modulo `ϖ (L(λ₁) ⊗ L(λ₂))`
(`GrandLoop.fTw_fW_tmul`). This defines a strict embedding of crystals
`GrandLoop.tensorHW : B(λ₁ + λ₂) → B(λ₂) ⊗ B(λ₁)` (in the library's order of the tensor factors,
`Crystal.tensor`), `u_{λ₁+λ₂} ↦ u_{λ₂} ⊗ u_{λ₁}`.

## Proof

Well-definedness and injectivity on classes come from `TensorModule.mk_eq_of_tmul_sub_mem`; the
compatibility with `f̃ᵢ` is the tensor product rule `GrandLoop.fT_tmul` together with the
computation of `εᵢ`, `φᵢ` on `B(λ)` from string data (`GrandLoop.φ_crystalHW_of_isStr`).
-/

open LusztigF Pointwise TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}
  [Finite I]

lemma tensorEmb_fW_mem_weightSpace (Λ₁ Λ₂ : Dom R) (w : List I) :
    tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) w) ∈
      weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum (wordWeight w)) := by
  rw [tensorEmb_fW]
  simpa using fTw_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ w
    (fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ [] [])

variable [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

/-! ### `Φ` and `Ψ` on the lattices -/

/-- `Φ (ϖ L(λ₁ + λ₂)) ⊆ ϖ (L(λ₁) ⊗ L(λ₂))` on weight vectors. -/
lemma tensorEmb_mem_smul_LL {Λ₁ Λ₂ : Dom R} {ν : I →₀ ℕ} {x : IrreducibleModule R v (Λ₁ + Λ₂).1}
    (hx : x ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂)) (hxw : x ∈ wsp (Λ₁ + Λ₂) ν) :
    tensorEmb hvt hR Λ₁.2 Λ₂.2 x ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨x₀, hx₀, hx₀w, rfl⟩ := TensorModule.exists_smul_weight hϖ0 hx hxw
  rw [smul_tensorEmb]
  exact Submodule.smul_mem_pointwise_smul _ _ _
    ((allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund ν.degree).2.2.2.2.1 Λ₁ Λ₂ ν rfl x₀
      hx₀ hx₀w)

/-- `Ψ (ϖ (L(λ₁) ⊗ L(λ₂))) ⊆ ϖ L(λ₁ + λ₂)` on weight vectors. -/
lemma tensorProj_mem_smul_lat {Λ₁ Λ₂ : Dom R} {ν : I →₀ ℕ} {z : TM v Λ₁ Λ₂}
    (hz : z ∈ ϖ • LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν)) :
    tensorProj hvt hR Λ₁.2 Λ₂.2 z ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂) := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨z₀, hz₀, hz₀w, rfl⟩ := TensorModule.exists_smul_weight hϖ0 hz hzw
  rw [smul_tensorProj]
  exact Submodule.smul_mem_pointwise_smul _ _ _
    ((allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund ν.degree).2.2.2.2.2.1 Λ₁ Λ₂ ν rfl z₀
      hz₀ hz₀w)

/-- `Φ(f̃_w v) ≡ f̃_{w₁} v ⊗ f̃_{w₂} v` modulo `ϖ (L(λ₁) ⊗ L(λ₂))`. -/
lemma exists_tensorEmb_fW (Λ₁ Λ₂ : Dom R) (w : List I) :
    ∃ w₁ w₂ : List I, wordWeight w₁ + wordWeight w₂ = wordWeight w ∧
      tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) w) -
        TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  obtain ⟨w₁, w₂, -, -, -, h5, h4⟩ := fTw_fW_tmul hϖ hϖv (Λ₁ := Λ₁) (Λ₂ := Λ₂) w
    (w₁ := []) (w₂ := []) (fun s _ ↦ (hall s).1) (fun s _ ↦ (hall s).2.1)
    (fun s _ ↦ (hall s).2.2.1)
  refine ⟨w₁, w₂, by simpa using h5, ?_⟩
  rw [tensorEmb_fW]
  exact h4

/-- If `Φ(f̃_w v) ≡ z` modulo `ϖ (L(λ₁) ⊗ L(λ₂))` and `f̃_w v ∉ ϖ L(λ₁ + λ₂)`, then
`z ∉ ϖ (L(λ₁) ⊗ L(λ₂))`. -/
lemma notMem_of_tensorEmb_fW_sub {Λ₁ Λ₂ : Dom R} {w : List I}
    (hw : fW hvt hR (Λ₁ + Λ₂) w ∉ ϖ • lat hvt hR A (Λ₁ + Λ₂)) {z : TM v Λ₁ Λ₂}
    (h : tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) w) - z ∈ ϖ • LL hvt hR A Λ₁ Λ₂) :
    z ∉ ϖ • LL hvt hR A Λ₁ Λ₂ := fun hz ↦ by
  have h1 := add_mem h hz
  rw [sub_add_cancel] at h1
  have h2 := tensorProj_mem_smul_lat hinj hϖ hϖv hk hfund h1
    (tensorEmb_fW_mem_weightSpace Λ₁ Λ₂ w)
  rw [tensorProj_tensorEmb] at h2
  exact hw h2

/-- The factors of `Φ(f̃_w v) ≡ f̃_{w₁} v ⊗ f̃_{w₂} v` are not in `ϖ L`. -/
lemma notMem_of_tensorEmb_fW_sub_tmul {Λ₁ Λ₂ : Dom R} {w w₁ w₂ : List I}
    (hw : fW hvt hR (Λ₁ + Λ₂) w ∉ ϖ • lat hvt hR A (Λ₁ + Λ₂))
    (h : tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) w) -
      TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈ ϖ • LL hvt hR A Λ₁ Λ₂) :
    fW hvt hR Λ₁ w₁ ∉ ϖ • lat hvt hR A Λ₁ ∧ fW hvt hR Λ₂ w₂ ∉ ϖ • lat hvt hR A Λ₂ := by
  have h0 := notMem_of_tensorEmb_fW_sub hinj hϖ hϖv hk hfund hw h
  exact ⟨fun h₁ ↦ h0 (tmul_mem_smul_left h₁ (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂)),
    fun h₂ ↦ h0 (tmul_mem_smul_right (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁) h₂)⟩

/-! ### The map `B(λ₁ + λ₂) → B(λ₂) ⊗ B(λ₁)` -/

lemma exists_tensorHW (Λ₁ Λ₂ : Dom R)
    (b : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) (Λ₁ + Λ₂).2 A ϖ) :
    ∃ p : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ₂.2 A ϖ ×
        IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ₁.2 A ϖ,
      ∃ (w : List I) (hw : fW hvt hR (Λ₁ + Λ₂) w ∉ ϖ • lat hvt hR A (Λ₁ + Λ₂)) (w₁ w₂ : List I)
        (hw₁ : fW hvt hR Λ₁ w₁ ∉ ϖ • lat hvt hR A Λ₁)
        (hw₂ : fW hvt hR Λ₂ w₂ ∉ ϖ • lat hvt hR A Λ₂),
        b = mkHW hvt hR (Λ₁ + Λ₂) w hw ∧ p = (mkHW hvt hR Λ₂ w₂ hw₂, mkHW hvt hR Λ₁ w₁ hw₁) ∧
        tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) w) -
          TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈
          ϖ • LL hvt hR A Λ₁ Λ₂ := by
  obtain ⟨w, hw, rfl⟩ := exists_mkHW (hvt := hvt) (Λ₁ + Λ₂) b
  obtain ⟨w₁, w₂, -, h⟩ := exists_tensorEmb_fW hinj hϖ hϖv hk hfund Λ₁ Λ₂ w
  obtain ⟨hw₁, hw₂⟩ := notMem_of_tensorEmb_fW_sub_tmul hinj hϖ hϖv hk hfund hw h
  exact ⟨_, w, hw, w₁, w₂, hw₁, hw₂, rfl, rfl, h⟩

variable (hvt hR) in
/-- The map `B(λ₁ + λ₂) → B(λ₂) ⊗ B(λ₁)`, `[f̃_w v] ↦ [f̃_{w₂} v] ⊗ [f̃_{w₁} v]` where
`Φ(f̃_w v) ≡ f̃_{w₁} v ⊗ f̃_{w₂} v` (library order of the factors). -/
def tensorHW (Λ₁ Λ₂ : Dom R)
    (b : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) (Λ₁ + Λ₂).2 A ϖ) :
    IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ₂.2 A ϖ ×
      IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ₁.2 A ϖ :=
  (exists_tensorHW (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ₁ Λ₂ b).choose

/-- Characterization of `tensorHW`. -/
theorem tensorHW_mkHW {Λ₁ Λ₂ : Dom R} {w w₁ w₂ : List I}
    (hw : fW hvt hR (Λ₁ + Λ₂) w ∉ ϖ • lat hvt hR A (Λ₁ + Λ₂))
    (hw₁ : fW hvt hR Λ₁ w₁ ∉ ϖ • lat hvt hR A Λ₁) (hw₂ : fW hvt hR Λ₂ w₂ ∉ ϖ • lat hvt hR A Λ₂)
    (h : tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) w) -
      TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈ ϖ • LL hvt hR A Λ₁ Λ₂) :
    tensorHW hvt hR hinj hϖ hϖv hk hfund Λ₁ Λ₂ (mkHW hvt hR (Λ₁ + Λ₂) w hw) =
      (mkHW hvt hR Λ₂ w₂ hw₂, mkHW hvt hR Λ₁ w₁ hw₁) := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨w', hw', w₁', w₂', hw₁', hw₂', hb, hp, h'⟩ :=
    (exists_tensorHW hinj hϖ hϖv hk hfund Λ₁ Λ₂ (mkHW hvt hR (Λ₁ + Λ₂) w hw)).choose_spec
  rw [tensorHW, hp]
  have hd := (mkHW_eq_mkHW_iff (Λ₁ + Λ₂) hw hw').1 hb
  have hww : wordWeight w' = wordWeight w :=
    wordWeight_eq_of_sub_mem (hvt := hvt) (hR := hR) (A := A) (ϖ := ϖ) (Λ₁ + Λ₂)
      (fW_mem_wsp hvt hR (Λ₁ + Λ₂) w) hw hd
  have hdw : fW hvt hR (Λ₁ + Λ₂) w - fW hvt hR (Λ₁ + Λ₂) w' ∈ wsp (Λ₁ + Λ₂) (wordWeight w) :=
    sub_mem (fW_mem_wsp hvt hR _ w) (hww ▸ fW_mem_wsp hvt hR _ w')
  have hΦ := tensorEmb_mem_smul_LL hinj hϖ hϖv hk hfund (Λ₁ := Λ₁) (Λ₂ := Λ₂) hd hdw
  rw [map_sub] at hΦ
  have hdiff : TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) -
      TensorModule.mk _ _ (fW hvt hR Λ₁ w₁' ⊗ₜ[k] fW hvt hR Λ₂ w₂') ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
    have := add_mem (sub_mem h' h) hΦ
    convert this using 1
    abel
  have hL₁ := isCrystalLattice_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ₁
  have hL₂ := isCrystalLattice_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ₂
  have hB₁ := isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund Λ₁
  have hB₂ := isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund Λ₂
  have := hL₁.free
  have := hL₂.free
  obtain ⟨e₁, e₂⟩ := TensorModule.mk_eq_of_tmul_sub_mem hinj hϖ0 hk hL₁.span_eq_top
    hL₂.span_eq_top hB₁.linearIndependent hB₁.span_eq_top hB₂.linearIndependent hB₂.span_eq_top
    (x := fwL hvt hR A Λ₁ w₁) (x' := fwL hvt hR A Λ₁ w₁') (y := fwL hvt hR A Λ₂ w₂)
    (y' := fwL hvt hR A Λ₂ w₂') (mkHW hvt hR Λ₁ w₁ hw₁).2 (mkHW hvt hR Λ₁ w₁' hw₁').2
    (mkHW hvt hR Λ₂ w₂ hw₂).2 (mkHW hvt hR Λ₂ w₂' hw₂').2 hdiff
  exact Prod.ext (Subtype.ext e₂.symm) (Subtype.ext e₁.symm)

end GrandLoop

end LieLean.QuantumGroup
