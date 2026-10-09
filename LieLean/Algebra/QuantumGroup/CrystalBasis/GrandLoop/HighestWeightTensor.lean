/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.HighestWeightSimilarity
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorIndependence

/-!
# The embeddings `B(λ₁ + λ₂) → B(λ₂) ⊗ B(λ₁)` and `B((n + 1)λ) → B(λ)^{⊗(n+1)}`

The embedding `Φ : V(λ₁ + λ₂) → V(λ₁) ⊗ V(λ₂)`, `v ↦ v ⊗ v`, maps `f̃_w v_{λ₁+λ₂}` to
`f̃_w (v ⊗ v) ≡ f̃_{w₁} v_{λ₁} ⊗ f̃_{w₂} v_{λ₂}` modulo `ϖ (L(λ₁) ⊗ L(λ₂))`
(`GrandLoop.fTw_fW_tmul`). This defines a strict embedding of the crystals of the crystal bases
`B(λ₁ + λ₂) → B(λ₂) ⊗ B(λ₁)` (in the library's order of the tensor factors, `Crystal.tensor`),
`u_{λ₁+λ₂} ↦ u_{λ₂} ⊗ u_{λ₁}`. Iterating, and composing with the similarity
`S : B(λ) → B((n + 1)λ)` of [Kas96] Thm. 3.1, gives the injective similarities
`B(λ) → B(λ)^{⊗(n+1)}`, `u_λ ↦ u_λ ⊗ ⋯ ⊗ u_λ`, of [Kas96] proof of Thm. 4.1.

## Main definitions

* `GrandLoop.tensorHWHom`: the strict embedding `B(λ₁ + λ₂) → B(λ₂) ⊗ B(λ₁)`.
* `GrandLoop.powHW`: the strict embedding `B((n + 1)λ) → B(λ)^{⊗(n+1)}`.

## Main results

* `GrandLoop.tensorHW_mkHW`: `[f̃_w v] ↦ [f̃_{w₂} v] ⊗ [f̃_{w₁} v]` when
  `Φ(f̃_w v) ≡ f̃_{w₁} v ⊗ f̃_{w₂} v`.
* `GrandLoop.ε_crystalHW_of_isStr`, `GrandLoop.φ_crystalHW_of_isStr`: `εᵢ`, `φᵢ` on `B(λ)`
  from string data.
* `GrandLoop.exists_similarityPowHW`: the similarities `B(λ) → B(λ)^{⊗(n+1)}`.

## Proof

Well-definedness of the embedding on classes comes from `TensorModule.mk_eq_of_tmul_sub_mem`; the
compatibility with `f̃ᵢ` is the tensor product rule `GrandLoop.fT_tmul` together with the
computation of `εᵢ`, `φᵢ` from string data, and `Crystal.StrictHom.ofFMap`.

## References

* [Kas96] M. Kashiwara, *Similarity of crystal bases*, Contemp. Math. 194 (1996), 177–186.
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

/-! ### `εᵢ` and `φᵢ` on `B(λ)` from string data -/

/-- The `f̃ᵢ`-string through `[f̃_w v]` with string data `(k, a)` has `a - k` further elements. -/
lemma fIter_crystalHW_of_isStr (Λ : Dom R) (i : I) {a : ℕ} {u : IrreducibleModule R v Λ.1} :
    ∀ (j : ℕ) {w : List I} {ν : I →₀ ℕ} {kk : ℕ},
      IsStr hvt hR ϖ Λ i ν (fW hvt hR Λ w) kk a u →
      ∀ hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ,
      (j ≤ a - kk → ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).fIter i j
          (mkHW hvt hR Λ w hw)).isSome) ∧
        (a - kk < j → (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).fIter i j
          (mkHW hvt hR Λ w hw) = none) := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  intro j
  induction j with
  | zero => exact fun _ _ ↦ ⟨fun _ ↦ rfl, fun h ↦ absurd h (Nat.not_lt_zero _)⟩
  | succ j ih =>
    intro w ν kk hx hw
    by_cases hka : kk + 1 ≤ a
    · have hx' := hx.kashiwaraF hka
      rw [← fW_cons] at hx'
      have hiw : fW hvt hR Λ (i :: w) ∉ ϖ • lat hvt hR A Λ :=
        hx'.notMem_x (fun s _ ↦ (hall s).1) rfl hϖ0
      rw [Crystal.fIter_succ, f_crystalHW_mkHW hinj hϖ hϖv hk hfund Λ i hw hiw, Option.bind_some]
      obtain ⟨h1, h2⟩ := ih hx' hiw
      exact ⟨fun h ↦ h1 (by omega), fun h ↦ h2 (by omega)⟩
    · have hka' : kk = a := by have := hx.le; omega
      have hiw : fW hvt hR Λ (i :: w) ∈ ϖ • lat hvt hR A Λ := by
        have := hx.kashiwaraF_mem hka'
        rwa [← fW_cons] at this
      rw [Crystal.fIter_succ, f_crystalHW_mkHW_eq_none hinj hϖ hϖv hk hfund Λ i hw hiw]
      exact ⟨fun h ↦ by omega, fun _ ↦ rfl⟩

/-- `φᵢ([f̃_w v]) = a - k` for string data `(k, a)`. -/
lemma φ_crystalHW_of_isStr {Λ : Dom R} {i : I} {w : List I} {ν : I →₀ ℕ} {kk a : ℕ}
    {u : IrreducibleModule R v Λ.1} (hx : IsStr hvt hR ϖ Λ i ν (fW hvt hR Λ w) kk a u)
    (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ) :
    (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).φ i (mkHW hvt hR Λ w hw) = ((a - kk : ℕ) : ℤ) := by
  have hC := isSeminormal_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ
  obtain ⟨p, hp⟩ := hC.exists_φ_eq i (mkHW hvt hR Λ w hw)
  have h1 := (fIter_crystalHW_of_isStr hinj hϖ hϖv hk hfund Λ i (a - kk) hx hw).1 le_rfl
  have h2 := (fIter_crystalHW_of_isStr hinj hϖ hϖv hk hfund Λ i (a - kk + 1) hx hw).2
    (Nat.lt_succ_self _)
  rw [hC.isSome_fIter_iff, hp] at h1
  have h2' := mt (hC.isSome_fIter_iff (i := i) (b := mkHW hvt hR Λ w hw) (a - kk + 1)).2
    (by rw [h2]; simp)
  rw [hp] at h2' ⊢
  have e1 : a - kk ≤ p := by exact_mod_cast h1
  have e2 : ¬ a - kk + 1 ≤ p := fun h ↦ h2' (by exact_mod_cast h)
  have : p = a - kk := by omega
  rw [this]
  rfl

/-- `εᵢ([f̃_w v]) = k` for string data `(k, a)`. -/
lemma ε_crystalHW_of_isStr {Λ : Dom R} {i : I} {w : List I} {kk a : ℕ}
    {u : IrreducibleModule R v Λ.1}
    (hx : IsStr hvt hR ϖ Λ i (wordWeight w) (fW hvt hR Λ w) kk a u)
    (hw : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ) :
    (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).ε i (mkHW hvt hR Λ w hw) = (kk : ℤ) := by
  have hC := isSeminormal_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ
  have hφ := φ_crystalHW_of_isStr hinj hϖ hϖv hk hfund hx hw
  rw [Crystal.φ_eq, wt_mkHW, LusztigCartanDatum.RootDatum.crystalDatum_coroot] at hφ
  obtain ⟨e, he⟩ := hC.exists_ε_eq i (mkHW hvt hR Λ w hw)
  rw [he] at hφ ⊢
  have hn := hx.node
  have hle := hx.le
  rw [← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj] at hφ
  have : (e : ℤ) = kk := by push_cast [Nat.cast_sub hle] at hφ; omega
  rw [← WithBot.coe_natCast, this]

/-! ### `tensorHW` is a strict embedding -/

/-- `f̃_{w₁} v ⊗ f̃_{w₂} v ∉ ϖ (L(λ₁) ⊗ L(λ₂))` if both factors are not in `ϖ L`. -/
lemma fW_tmul_notMem {Λ₁ Λ₂ : Dom R} {w₁ w₂ : List I}
    (hw₁ : fW hvt hR Λ₁ w₁ ∉ ϖ • lat hvt hR A Λ₁) (hw₂ : fW hvt hR Λ₂ w₂ ∉ ϖ • lat hvt hR A Λ₂) :
    TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∉ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hL₁ := isCrystalLattice_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ₁
  have hL₂ := isCrystalLattice_lat (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund Λ₂
  have hB₁ := isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund Λ₁
  have hB₂ := isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund Λ₂
  have := hL₁.free
  have := hL₂.free
  exact TensorModule.mk_tmul_notMem hinj hϖ0 hk hL₁.span_eq_top hL₂.span_eq_top
    hB₁.linearIndependent hB₁.span_eq_top hB₂.linearIndependent hB₂.span_eq_top
    (not_isUnit_ϖ hϖ) (x := fwL hvt hR A Λ₁ w₁) (y := fwL hvt hR A Λ₂ w₂)
    (mkHW hvt hR Λ₁ w₁ hw₁).2 (mkHW hvt hR Λ₂ w₂ hw₂).2

/-- If `Φ(f̃_w v) ≡ z` with `z ∈ ϖ (L(λ₁) ⊗ L(λ₂))`, then `f̃_w v ∈ ϖ L(λ₁ + λ₂)`. -/
lemma fW_mem_of_tensorEmb_sub {Λ₁ Λ₂ : Dom R} {w : List I} {z : TM v Λ₁ Λ₂}
    (h : tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) w) - z ∈ ϖ • LL hvt hR A Λ₁ Λ₂)
    (hz : z ∈ ϖ • LL hvt hR A Λ₁ Λ₂) : fW hvt hR (Λ₁ + Λ₂) w ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂) := by
  by_contra hw
  exact notMem_of_tensorEmb_fW_sub hinj hϖ hϖv hk hfund hw h hz

/-- One step of `f_tensorHW`: if `Φ(f̃_{i w} v) ≡ f̃_{w₁} v ⊗ f̃_{w₂} v` with both factors outside
`ϖ L`, then `f̃ᵢ [f̃_w v] = [f̃_{i w} v]` is sent to `[f̃_{w₂} v] ⊗ [f̃_{w₁} v]`. -/
lemma map_f_mkHW_of_sub {Λ₁ Λ₂ : Dom R} (i : I) {w w₁ w₂ : List I}
    (hw : fW hvt hR (Λ₁ + Λ₂) w ∉ ϖ • lat hvt hR A (Λ₁ + Λ₂))
    (hw₁ : fW hvt hR Λ₁ w₁ ∉ ϖ • lat hvt hR A Λ₁) (hw₂ : fW hvt hR Λ₂ w₂ ∉ ϖ • lat hvt hR A Λ₂)
    (h : tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) (i :: w)) -
      TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈ ϖ • LL hvt hR A Λ₁ Λ₂) :
    ((crystalHW hvt hR hinj hϖ hϖv hk hfund (Λ₁ + Λ₂)).f i (mkHW hvt hR (Λ₁ + Λ₂) w hw)).map
        (tensorHW hvt hR hinj hϖ hϖv hk hfund Λ₁ Λ₂) =
      some (mkHW hvt hR Λ₂ w₂ hw₂, mkHW hvt hR Λ₁ w₁ hw₁) := by
  have hiw : fW hvt hR (Λ₁ + Λ₂) (i :: w) ∉ ϖ • lat hvt hR A (Λ₁ + Λ₂) := fun hm ↦
    fW_tmul_notMem hinj hϖ hϖv hk hfund hw₁ hw₂ (by
      have := sub_mem (tensorEmb_mem_smul_LL hinj hϖ hϖv hk hfund hm
        (fW_mem_wsp hvt hR _ (i :: w))) h
      simpa using this)
  rw [f_crystalHW_mkHW hinj hϖ hϖv hk hfund (Λ₁ + Λ₂) i hw hiw, Option.map_some]
  exact congrArg some (tensorHW_mkHW hinj hϖ hϖv hk hfund hiw hw₁ hw₂ h)

/-- The tensor product rule for `Φ(f̃_{i w} v)`, given string data of the factors. -/
lemma tensorEmb_fW_cons_sub {Λ₁ Λ₂ : Dom R} (i : I) {w w₁ w₂ : List I}
    (hww : wordWeight w₁ + wordWeight w₂ = wordWeight w)
    (h : tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) w) -
      TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈ ϖ • LL hvt hR A Λ₁ Λ₂)
    {k₁ a₁ k₂ a₂ : ℕ} {u₁ : IrreducibleModule R v Λ₁.1} {u₂ : IrreducibleModule R v Λ₂.1}
    (hx : IsStr hvt hR ϖ Λ₁ i (wordWeight w₁) (fW hvt hR Λ₁ w₁) k₁ a₁ u₁)
    (hy : IsStr hvt hR ϖ Λ₂ i (wordWeight w₂) (fW hvt hR Λ₂ w₂) k₂ a₂ u₂) :
    tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) (i :: w)) -
      (if k₁ < a₂ - k₂ then TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ (i :: w₂))
        else TensorModule.mk _ _ (fW hvt hR Λ₁ (i :: w₁) ⊗ₜ[k] fW hvt hR Λ₂ w₂)) ∈
      ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  have hAll : ∀ d, ∀ s ≤ d, PropA hvt hR A s := fun _ s _ ↦ (hall s).1
  have hrule := fT_tmul hϖ hϖv (hAll _) (hAll _) rfl rfl hx hy
  have hwt : tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) w) -
      TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈
      weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum (wordWeight w)) :=
    sub_mem (tensorEmb_fW_mem_weightSpace Λ₁ Λ₂ w)
      (hww ▸ fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ w₁ w₂)
  have hstep := fT_mem_smul_LL hϖ hϖv (hAll _) i rfl h hwt
  rw [map_sub] at hstep
  have hΦ : tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) (i :: w)) =
      fT hvt hR Λ₁ Λ₂ i (tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) w)) := by
    rw [tensorEmb_fW, tensorEmb_fW, fTw_cons]
  have hcong := add_mem hstep hrule
  rw [sub_add_sub_cancel, ← hΦ, ← fW_cons, ← fW_cons] at hcong
  exact hcong

/-- `tensorHW` commutes with the `f̃ᵢ` (the tensor product rule). -/
theorem f_tensorHW (Λ₁ Λ₂ : Dom R) (i : I)
    (b : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) (Λ₁ + Λ₂).2 A ϖ) :
    ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ₂).tensor
        (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ₁)).f i
        (tensorHW hvt hR hinj hϖ hϖv hk hfund Λ₁ Λ₂ b) =
      ((crystalHW hvt hR hinj hϖ hϖv hk hfund (Λ₁ + Λ₂)).f i b).map
        (tensorHW hvt hR hinj hϖ hϖv hk hfund Λ₁ Λ₂) := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  have hAll : ∀ d, ∀ s ≤ d, PropA hvt hR A s := fun _ s _ ↦ (hall s).1
  obtain ⟨w, hw, rfl⟩ := exists_mkHW (hvt := hvt) (Λ₁ + Λ₂) b
  obtain ⟨w₁, w₂, hww, h⟩ := exists_tensorEmb_fW hinj hϖ hϖv hk hfund Λ₁ Λ₂ w
  obtain ⟨hw₁, hw₂⟩ := notMem_of_tensorEmb_fW_sub_tmul hinj hϖ hϖv hk hfund hw h
  rw [tensorHW_mkHW hinj hϖ hϖv hk hfund hw hw₁ hw₂ h]
  obtain ⟨k₁, a₁, u₁, hx⟩ := exists_isStr hϖ0 (hAll _) (fun s _ ↦ (hall s).2.1)
    (fun s _ ↦ (hall s).2.2.1) Λ₁ i rfl (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁)
    (fW_mem_wsp hvt hR Λ₁ w₁) (w := w₁) (by rw [sub_self]; exact zero_mem _) hw₁
  obtain ⟨k₂, a₂, u₂, hy⟩ := exists_isStr hϖ0 (hAll _) (fun s _ ↦ (hall s).2.1)
    (fun s _ ↦ (hall s).2.2.1) Λ₂ i rfl (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂)
    (fW_mem_wsp hvt hR Λ₂ w₂) (w := w₂) (by rw [sub_self]; exact zero_mem _) hw₂
  have hcong := tensorEmb_fW_cons_sub hinj hϖ hϖv hk hfund i hww h hx hy
  rw [Crystal.tensor_f]
  dsimp only
  rw [ε_crystalHW_of_isStr hinj hϖ hϖv hk hfund hx hw₁,
    φ_crystalHW_of_isStr hinj hϖ hϖv hk hfund hy hw₂]
  by_cases hc : k₁ < a₂ - k₂
  · have hc' : ((k₁ : ℤ) : WithBot ℤ) < (((a₂ - k₂ : ℕ) : ℤ) : WithBot ℤ) := by exact_mod_cast hc
    simp only [hc, ↓reduceIte] at hcong
    simp only [hc', ↓reduceIte]
    have hy' := hy.kashiwaraF (by omega)
    rw [← fW_cons] at hy'
    have hiw₂ : fW hvt hR Λ₂ (i :: w₂) ∉ ϖ • lat hvt hR A Λ₂ :=
      hy'.notMem_x (hAll _) rfl hϖ0
    rw [f_crystalHW_mkHW hinj hϖ hϖv hk hfund Λ₂ i hw₂ hiw₂, Option.map_some]
    exact (map_f_mkHW_of_sub hinj hϖ hϖv hk hfund i hw hw₁ hiw₂ hcong).symm
  · have hc' : ¬ ((k₁ : ℤ) : WithBot ℤ) < (((a₂ - k₂ : ℕ) : ℤ) : WithBot ℤ) := by
      exact_mod_cast hc
    simp only [hc, ↓reduceIte] at hcong
    simp only [hc', ↓reduceIte]
    by_cases hka : k₁ + 1 ≤ a₁
    · have hx' := hx.kashiwaraF hka
      rw [← fW_cons] at hx'
      have hiw₁ : fW hvt hR Λ₁ (i :: w₁) ∉ ϖ • lat hvt hR A Λ₁ :=
        hx'.notMem_x (hAll _) rfl hϖ0
      rw [f_crystalHW_mkHW hinj hϖ hϖv hk hfund Λ₁ i hw₁ hiw₁, Option.map_some]
      exact (map_f_mkHW_of_sub hinj hϖ hϖv hk hfund i hw hiw₁ hw₂ hcong).symm
    · have hiw₁ : fW hvt hR Λ₁ (i :: w₁) ∈ ϖ • lat hvt hR A Λ₁ := by
        have := hx.kashiwaraF_mem (by have := hx.le; omega)
        rwa [← fW_cons] at this
      have hiw : fW hvt hR (Λ₁ + Λ₂) (i :: w) ∈ ϖ • lat hvt hR A (Λ₁ + Λ₂) :=
        fW_mem_of_tensorEmb_sub hinj hϖ hϖv hk hfund hcong (tmul_mem_smul_left hiw₁
          (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂))
      rw [f_crystalHW_mkHW_eq_none hinj hϖ hϖv hk hfund Λ₁ i hw₁ hiw₁,
        f_crystalHW_mkHW_eq_none hinj hϖ hϖv hk hfund (Λ₁ + Λ₂) i hw hiw]
      simp only [Option.map_none]

/-- `tensorHW` preserves weights. -/
theorem wt_tensorHW (Λ₁ Λ₂ : Dom R)
    (b : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) (Λ₁ + Λ₂).2 A ϖ) :
    ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ₂).tensor
        (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ₁)).wt
        (tensorHW hvt hR hinj hϖ hϖv hk hfund Λ₁ Λ₂ b) =
      (crystalHW hvt hR hinj hϖ hϖv hk hfund (Λ₁ + Λ₂)).wt b := by
  obtain ⟨w, hw, rfl⟩ := exists_mkHW (hvt := hvt) (Λ₁ + Λ₂) b
  obtain ⟨w₁, w₂, hww, h⟩ := exists_tensorEmb_fW hinj hϖ hϖv hk hfund Λ₁ Λ₂ w
  obtain ⟨hw₁, hw₂⟩ := notMem_of_tensorEmb_fW_sub_tmul hinj hϖ hϖv hk hfund hw h
  rw [tensorHW_mkHW hinj hϖ hϖv hk hfund hw hw₁ hw₂ h, Crystal.tensor_wt, wt_mkHW, wt_mkHW,
    wt_mkHW, ← hww, R.rootSum_add, Dom.add_val]
  abel

variable (hvt hR) in
/-- **The strict embedding** `B(λ₁ + λ₂) → B(λ₂) ⊗ B(λ₁)` (library order of the factors). -/
def tensorHWHom (Λ₁ Λ₂ : Dom R) :
    Crystal.StrictHom (crystalHW hvt hR hinj hϖ hϖv hk hfund (Λ₁ + Λ₂))
      ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ₂).tensor
        (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ₁)) :=
  Crystal.StrictHom.ofFMap (isSeminormal_crystalHW hvt hR hinj hϖ hϖv hk hfund _)
    ((isSeminormal_crystalHW hvt hR hinj hϖ hϖv hk hfund _).tensor
      (isSeminormal_crystalHW hvt hR hinj hϖ hϖv hk hfund _))
    (tensorHW hvt hR hinj hϖ hϖv hk hfund Λ₁ Λ₂) (wt_tensorHW hinj hϖ hϖv hk hfund Λ₁ Λ₂)
    (f_tensorHW hinj hϖ hϖv hk hfund Λ₁ Λ₂)

lemma tensorHWHom_apply (Λ₁ Λ₂ : Dom R)
    (b : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) (Λ₁ + Λ₂).2 A ϖ) :
    tensorHWHom hvt hR hinj hϖ hϖv hk hfund Λ₁ Λ₂ b =
      tensorHW hvt hR hinj hϖ hϖv hk hfund Λ₁ Λ₂ b := rfl

/-- `u_{λ₁+λ₂} ↦ u_{λ₂} ⊗ u_{λ₁}`. -/
theorem tensorHWHom_topHW (Λ₁ Λ₂ : Dom R) :
    tensorHWHom hvt hR hinj hϖ hϖv hk hfund Λ₁ Λ₂ (topHW hvt hR hinj hϖ (Λ₁ + Λ₂)) =
      (topHW hvt hR hinj hϖ Λ₂, topHW hvt hR hinj hϖ Λ₁) := by
  rw [tensorHWHom_apply, topHW]
  refine tensorHW_mkHW hinj hϖ hϖv hk hfund _ _ _ ?_
  rw [tensorEmb_fW]
  simp

/-! ### Tensor powers: `B(nλ) → B(λ)^{⊗n}` and the similarities `B(λ) → B(λ)^{⊗n}` -/

variable (hvt hR) in
/-- The identification `B(λ) = B(λ')` for `λ = λ'`. -/
def castHW {Λ Λ' : Dom R} (h : Λ = Λ') :
    Crystal.StrictHom (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ)
      (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ') := by
  subst h
  exact Crystal.StrictHom.id _

lemma castHW_topHW {Λ Λ' : Dom R} (h : Λ = Λ') :
    castHW hvt hR hinj hϖ hϖv hk hfund h (topHW hvt hR hinj hϖ Λ) = topHW hvt hR hinj hϖ Λ' := by
  subst h
  rfl

omit [DecidableEq I] [NeZero v] [CharZero k] [Finite I] [IsDomain A]
  [IsDiscreteValuationRing A] hinj hϖ hϖv hk hfund in
lemma nsmulDom_one (Λ : Dom R) : nsmulDom R 1 Λ = Λ := Subtype.ext (one_nsmul _)

omit [DecidableEq I] [NeZero v] [CharZero k] [Finite I] [IsDomain A]
  [IsDiscreteValuationRing A] hinj hϖ hϖv hk hfund in
lemma nsmulDom_succ (n : ℕ) (Λ : Dom R) : nsmulDom R (n + 1) Λ = nsmulDom R n Λ + Λ :=
  Subtype.ext (by rw [nsmulDom_val, Dom.add_val, nsmulDom_val, succ_nsmul])

variable (hvt hR) in
/-- The strict embedding `B((n + 1) λ) → B(λ)^{⊗(n+1)}`, `u ↦ u ⊗ ⋯ ⊗ u`. -/
def powHW (Λ : Dom R) : (n : ℕ) →
    Crystal.StrictHom (crystalHW hvt hR hinj hϖ hϖv hk hfund (nsmulDom R (n + 1) Λ))
      ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).tensorPow (n + 1))
  | 0 => ((Crystal.tensorUnit _).symm.toStrictHom).comp
      (castHW hvt hR hinj hϖ hϖv hk hfund (nsmulDom_one Λ))
  | n + 1 => ((Crystal.StrictHom.id _).tensorMap (powHW Λ n)).comp
      ((tensorHWHom hvt hR hinj hϖ hϖv hk hfund (nsmulDom R (n + 1) Λ) Λ).comp
        (castHW hvt hR hinj hϖ hϖv hk hfund (nsmulDom_succ (n + 1) Λ)))

theorem powHW_topHW (Λ : Dom R) : ∀ n : ℕ,
    powHW hvt hR hinj hϖ hϖv hk hfund Λ n (topHW hvt hR hinj hϖ (nsmulDom R (n + 1) Λ)) =
      Crystal.TPow.replicate (topHW hvt hR hinj hϖ Λ) (n + 1)
  | 0 => by
    have h := castHW_topHW (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund (nsmulDom_one Λ)
    change (Crystal.tensorUnit (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ)).symm
      (castHW hvt hR hinj hϖ hϖv hk hfund (nsmulDom_one Λ)
        (topHW hvt hR hinj hϖ (nsmulDom R 1 Λ))) = _
    rw [h]
    rfl
  | n + 1 => by
    have h := castHW_topHW (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund (nsmulDom_succ (n + 1) Λ)
    change ((tensorHWHom hvt hR hinj hϖ hϖv hk hfund (nsmulDom R (n + 1) Λ) Λ
        (castHW hvt hR hinj hϖ hϖv hk hfund (nsmulDom_succ (n + 1) Λ)
          (topHW hvt hR hinj hϖ (nsmulDom R (n + 2) Λ)))).1,
      powHW hvt hR hinj hϖ hϖv hk hfund Λ n
        (tensorHWHom hvt hR hinj hϖ hϖv hk hfund (nsmulDom R (n + 1) Λ) Λ
          (castHW hvt hR hinj hϖ hϖv hk hfund (nsmulDom_succ (n + 1) Λ)
            (topHW hvt hR hinj hϖ (nsmulDom R (n + 2) Λ)))).2) = _
    rw [h, tensorHWHom_topHW, powHW_topHW Λ n]
    rfl

/-- `u_λ` is a highest weight element. -/
lemma e_topHW (Λ : Dom R) (j : I) :
    (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).e j (topHW hvt hR hinj hϖ Λ) = none := by
  classical
  rw [Option.eq_none_iff_forall_ne_some]
  intro c hc
  have hw := (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).wt_e j _ _ hc
  obtain ⟨w, hw', rfl⟩ := exists_mkHW (hvt := hvt) Λ c
  rw [topHW, wt_mkHW, wt_mkHW] at hw
  have h1 : R.rootSum (wordWeight w + Finsupp.single j 1) = R.rootSum 0 := by
    rw [R.rootSum_add, R.rootSum_single, one_nsmul, R.rootSum_zero]
    simp only [wordWeight_nil, R.rootSum_zero, sub_zero,
      LusztigCartanDatum.RootDatum.crystalDatum_root] at hw
    have := congrArg (· - Λ.1) hw
    simp only [sub_sub_cancel_left, add_sub_cancel_left] at this
    rw [← neg_eq_iff_eq_neg.mpr this.symm]
    abel
  have h2 := congrArg (· j) (LusztigCartanDatum.RootDatum.rootSum_injective hR h1)
  simp at h2

/-- **The similarities `B(λ) → B(λ)^{⊗(n+1)}`** ([Kas96] proof of Thm. 4.1:
`G_{n+1} ∘ S_{n+1}`), `u_λ ↦ u_λ ⊗ ⋯ ⊗ u_λ`; they are injective. -/
theorem exists_similarityPowHW [IsFormallyReal (A ⧸ Ideal.span {ϖ})] (Λ : Dom R) (n : ℕ) :
    ∃ T : Crystal.Similarity (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ)
      ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).tensorPow (n + 1)) (n + 1),
      T (topHW hvt hR hinj hϖ Λ) = Crystal.TPow.replicate (topHW hvt hR hinj hϖ Λ) (n + 1) ∧
      Function.Injective T := by
  obtain ⟨S, hS⟩ := exists_similarityHW hinj hϖ hϖv hk hfund n.succ_pos Λ
  refine ⟨S.compStrictHom (powHW hvt hR hinj hϖ hϖv hk hfund Λ n), ?_, ?_⟩
  · rw [Crystal.Similarity.compStrictHom_apply, hS, powHW_topHW]
  · exact Crystal.Similarity.injective_of_fWord _
      (exists_fWord_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ)
      (e_topHW hinj hϖ hϖv hk hfund Λ)

end GrandLoop

end LieLean.QuantumGroup
