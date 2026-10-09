/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Embedding

/-!
# Kashiwara's grand loop: the highest weight vector, the map `S`, and words on `v ⊗ v`

* `v_λ ∉ ϖ L(λ)` and `v_λ` has string data `(0, ⟨i, λ⟩, v_λ)` at every `i`
  (`QuantumGroup.GrandLoop.hwv_notMem`, `QuantumGroup.GrandLoop.isStr_hwv`).
* `S = (v_{λ₁}, ·) ⊗ 1 : V(λ₁) ⊗ V(λ₂) → V(λ₂)` maps `L(λ₁) ⊗ L(λ₂)` into `L(λ₂)` and commutes with
  `f̃ᵢ` modulo `ϖ L(λ₂)` in bounded depth (`QuantumGroup.GrandLoop.Sh_mem`,
  `QuantumGroup.GrandLoop.Sh_fT_sub_mem`; [HK] Lemma 5.3.6).
* `f̃ᵢ (f̃_{w₁} v_{λ₁} ⊗ f̃_{w₂} v_{λ₂})` is `f̃_{i w₁} v_{λ₁} ⊗ f̃_{w₂} v_{λ₂}` or
  `f̃_{w₁} v_{λ₁} ⊗ f̃_{i w₂} v_{λ₂}` modulo `ϖ (L(λ₁) ⊗ L(λ₂))`
  (`QuantumGroup.GrandLoop.fT_fW_tmul`),
  and `f̃_w (v_{λ₁} ⊗ v_{λ₂}) ≡ v_{λ₁} ⊗ f̃_w v_{λ₂}` unless `f̃_w v_{λ₂} ∈ ϖ L(λ₂)`
  (`QuantumGroup.GrandLoop.fTword_hwv_tmul`; [HK] Lemma 5.3.2 (6), (7)).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
-/

open Finset Pointwise TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k]

/-! ### The highest weight vector -/

lemma fW_nil (Λ : Dom R) : fW hvt hR Λ [] = IrreducibleModule.hwv R v Λ.1 := rfl

lemma fW_cons (Λ : Dom R) (i : I) (w : List I) :
    fW hvt hR Λ (i :: w) = fK hvt hR Λ i (fW hvt hR Λ w) := rfl

/-- `L(λ)_λ = A v_λ`. -/
lemma exists_eq_smul_hwv {Λ : Dom R} {x : IrreducibleModule R v Λ.1} (hx : x ∈ lat hvt hR A Λ)
    (hxw : x ∈ wsp Λ 0) : ∃ a : A, x = a • IrreducibleModule.hwv R v Λ.1 := by
  have := mem_of_fW_mem (hvt := hvt) (hR := hR) Λ 0
    (Submodule.span A {IrreducibleModule.hwv R v Λ.1})
    (fun w hw ↦ by
      have h := degree_wordWeight w
      rw [hw, map_zero] at h
      rw [List.eq_nil_of_length_eq_zero h.symm]
      exact Submodule.mem_span_singleton_self _) hx hxw
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 this
  exact ⟨a, rfl⟩

omit [CharZero k] in
lemma hwv_ne_zero (hR' : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (Λ : Y →+ ℤ) :
    IrreducibleModule.hwv R v Λ ≠ 0 := by
  rw [IrreducibleModule.hwv, Ne, Submodule.Quotient.mk_eq_zero]
  exact VermaModule.hwv_notMem_maxSubmodule hR' hv'

omit [NeZero v] [CharZero k] in
lemma hwv_mem_wsp (Λ : Dom R) : IrreducibleModule.hwv R v Λ.1 ∈ wsp Λ 0 := by
  change _ ∈ weightSpace R v _ (Λ.1 - R.rootSum 0)
  rw [R.rootSum_zero, sub_zero]
  exact IrreducibleModule.hwv_mem_weightSpace

/-- `v_λ ∉ ϖ L(λ)` for a non-unit `ϖ` (with `A ⊆ k`). -/
lemma hwv_notMem (hinj : Function.Injective (algebraMap A k)) {ϖ : A} (hϖ : ¬IsUnit ϖ)
    (Λ : Dom R) : IrreducibleModule.hwv R v Λ.1 ∉ ϖ • lat hvt hR A Λ := by
  intro h
  by_cases hϖ0 : algebraMap A k ϖ = 0
  · have hϖ0' : ϖ = 0 := hinj (by rw [hϖ0, map_zero])
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
    rw [hϖ0', zero_smul] at hy
    exact hwv_ne_zero hR (pow_ne_one_of_transcendental' hvt) Λ.1 hy.symm
  obtain ⟨y, hy, hyw, he⟩ := TensorModule.exists_smul_weight hϖ0 h
    (hwv_mem_wsp Λ)
  obtain ⟨a, rfl⟩ := exists_eq_smul_hwv hy hyw
  rw [smul_smul, ← algebraMap_smul k, ← sub_eq_zero] at he
  have h1 : (1 - algebraMap A k (ϖ * a)) • IrreducibleModule.hwv R v Λ.1 = 0 := by
    rw [sub_smul, one_smul]; exact he
  rcases smul_eq_zero.1 h1 with h2 | h2
  · refine hϖ (isUnit_iff_exists_inv.2 ⟨a, hinj ?_⟩)
    rw [map_one]; exact (sub_eq_zero.1 h2).symm
  · exact hwv_ne_zero hR (pow_ne_one_of_transcendental' hvt) Λ.1 h2

variable {ϖ : A}

/-- String data of `v_λ`: `(0, ⟨i, λ⟩, v_λ)`. -/
lemma isStr_hwv (hinj : Function.Injective (algebraMap A k)) (hϖ : ¬IsUnit ϖ) (Λ : Dom R)
    (i : I) : IsStr hvt hR ϖ Λ i 0 (IrreducibleModule.hwv R v Λ.1) 0 (Λ.1 (R.coroot i)).toNat
      (IrreducibleModule.hwv R v Λ.1) where
  x_wt := hwv_mem_wsp Λ
  mem := IrreducibleModule.hwv_mem_lattice hR _ Λ.2 A
  wt := by simpa using IrreducibleModule.hwv_mem_weightSpace (R := R) (v := v) (Λ := Λ.1)
  E_smul := IrreducibleModule.E_smul_hwv (R := R) (v := v) (Λ := Λ.1) i
  node := by have := Λ.2 i; simp; omega
  notMem := hwv_notMem hinj hϖ Λ
  le := Nat.zero_le _
  sub := by simp

/-- At the top weight the string position is `0`. -/
lemma IsStr.eq_zero_of_top {Λ : Dom R} {i : I} {x : IrreducibleModule R v Λ.1} {kk a : ℕ}
    {u : IrreducibleModule R v Λ.1} (h : IsStr hvt hR ϖ Λ i 0 x kk a u) : kk = 0 := by
  obtain ⟨ν', hν'⟩ := exists_eq_add_single hR (pow_ne_one_of_transcendental' hvt) Λ h.wt h.ne_zero
  have := congrArg (fun ν ↦ ν i) hν'
  simp at this
  omega

/-! ### The map `S` -/

variable (hvt hR) in
/-- `S : V(λ₁) ⊗ V(λ₂) → V(λ₂)`, `x ⊗ y ↦ (v_{λ₁}, x) y`. -/
abbrev Sh (Λ₁ Λ₂ : Dom R) : TM v Λ₁ Λ₂ →ₗ[k] IrreducibleModule R v Λ₂.1 :=
  tensorHead hR (pow_ne_one_of_transcendental' hvt) Λ₁.1 (M := IrreducibleModule R v Λ₂.1)

/-- `(v_λ, f̃_w v_λ) = 0` for `w ≠ []`. -/
lemma form_hwv_fW (Λ : Dom R) {w : List I} (hw : w ≠ []) :
    IrreducibleModule.form Λ.1 hR (pow_ne_one_of_transcendental' hvt)
      (IrreducibleModule.hwv R v Λ.1) (fW hvt hR Λ w) = 0 := by
  have hne : Λ.1 - R.rootSum 0 ≠ Λ.1 - R.rootSum (LusztigF.wordWeight w) := by
    intro h
    have h2 := LusztigCartanDatum.RootDatum.rootSum_injective hR (sub_right_injective h)
    have h3 := degree_wordWeight w
    rw [← h2, map_zero] at h3
    exact hw (List.eq_nil_of_length_eq_zero h3.symm)
  exact (IrreducibleModule.isContravariant_form hR _).eq_zero_of_ne hne (hwv_mem_wsp Λ)
    (fW_mem_wsp hvt hR Λ w) (pow_ne_one_of_transcendental' hvt)

/-- `(v_λ, L(λ)) ⊆ A`. -/
lemma exists_form_hwv {Λ : Dom R} {x : IrreducibleModule R v Λ.1} (hx : x ∈ lat hvt hR A Λ) :
    ∃ a : A, IrreducibleModule.form Λ.1 hR (pow_ne_one_of_transcendental' hvt)
      (IrreducibleModule.hwv R v Λ.1) x = algebraMap A k a := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rcases w with _ | ⟨i, w⟩
    · exact ⟨1, by simp⟩
    · exact ⟨0, by rw [map_zero]; exact form_hwv_fW (hvt := hvt) Λ (List.cons_ne_nil i w)⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [← algebraMap_smul k, map_smul, ha, smul_eq_mul, map_mul]⟩

lemma Sh_tmul {Λ₁ Λ₂ : Dom R} (x : IrreducibleModule R v Λ₁.1) (y : IrreducibleModule R v Λ₂.1) :
    Sh hvt hR Λ₁ Λ₂ (TensorModule.mk _ _ (x ⊗ₜ[k] y)) =
      IrreducibleModule.form Λ₁.1 hR (pow_ne_one_of_transcendental' hvt)
        (IrreducibleModule.hwv R v Λ₁.1) x • y :=
  tensorHead_tmul _ _ _ x y

/-- `S (L(λ₁) ⊗ L(λ₂)) ⊆ L(λ₂)` ([HK] Lemma 5.3.6 (1)). -/
lemma Sh_mem {Λ₁ Λ₂ : Dom R} {z : TM v Λ₁ Λ₂} (hz : z ∈ LL hvt hR A Λ₁ Λ₂) :
    Sh hvt hR Λ₁ Λ₂ z ∈ lat hvt hR A Λ₂ := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    obtain ⟨a, ha⟩ := exists_form_hwv hx
    rw [Sh_tmul, ha, algebraMap_smul]
    exact Submodule.smul_mem _ a hy
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c ha

lemma Sh_mem_smul {Λ₁ Λ₂ : Dom R} {z : TM v Λ₁ Λ₂} (hz : z ∈ ϖ • LL hvt hR A Λ₁ Λ₂) :
    Sh hvt hR Λ₁ Λ₂ z ∈ ϖ • lat hvt hR A Λ₂ := by
  obtain ⟨z₀, hz₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
  rw [LinearMap.map_smul_of_tower]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (Sh_mem hz₀)

/-! ### Reduction to `f̃`-words -/

/-- An `A`-submodule of `V(λ₁) ⊗ V(λ₂)` containing the `f̃_{w₁} v_{λ₁} ⊗ f̃_{w₂} v_{λ₂}` of weight
`λ₁ + λ₂ - ν` contains `(L(λ₁) ⊗ L(λ₂))_{λ₁+λ₂-ν}`. -/
lemma mem_of_fW_tmul_mem (Λ₁ Λ₂ : Dom R) (ν : I →₀ ℕ) (N : Submodule A (TM v Λ₁ Λ₂))
    (hN : ∀ w₁ w₂ : List I, LusztigF.wordWeight w₁ + LusztigF.wordWeight w₂ = ν →
      TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈ N)
    {z : TM v Λ₁ Λ₂} (hz : z ∈ LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν)) : z ∈ N := by
  classical
  have hP := TensorModule.weightSetProj_singleton_mem_of (pow_ne_one_of_transcendental' hvt)
    (isInt hvt hR Λ₁) (isInt hvt hR Λ₂)
    (fun S _ hm ↦ weightSetProj_mem_lat hvt hR A Λ₁ S hm)
    (fun S _ hm ↦ weightSetProj_mem_lat hvt hR A Λ₂ S hm) (Λ₁.1 + Λ₂.1 - R.rootSum ν) N
    (fun a b hab x hx hxw y hy hyw ↦ ?_) hz
  · rw [weightSetProj_of_mem _ _ _ hzw] at hP
    simpa using hP
  by_cases h0 : x = 0 ∨ y = 0
  · rcases h0 with h0 | h0 <;> simp [h0]
  push Not at h0
  obtain ⟨ν₁, rfl⟩ :=
    IrreducibleModule.exists_eq_sub_rootSum (pow_ne_one_of_transcendental' hvt) hxw h0.1
  obtain ⟨ν₂, rfl⟩ :=
    IrreducibleModule.exists_eq_sub_rootSum (pow_ne_one_of_transcendental' hvt) hyw h0.2
  have hνν : ν₁ + ν₂ = ν := by
    refine LusztigCartanDatum.RootDatum.rootSum_injective hR ?_
    rw [R.rootSum_add]
    have := congrArg (fun μ ↦ Λ₁.1 + Λ₂.1 - μ) hab
    simp only [sub_sub_cancel] at this
    rw [← this]
    abel
  let mkR : IrreducibleModule R v Λ₂.1 → IrreducibleModule R v Λ₁.1 →ₗ[A] TM v Λ₁ Λ₂ :=
    fun y ↦ (((TensorModule.mk _ _).toLinearMap ∘ₗ
      (TensorProduct.mk k _ _).flip y)).restrictScalars A
  let mkL : IrreducibleModule R v Λ₁.1 → IrreducibleModule R v Λ₂.1 →ₗ[A] TM v Λ₁ Λ₂ :=
    fun x ↦ (((TensorModule.mk _ _).toLinearMap ∘ₗ (TensorProduct.mk k _ _) x)).restrictScalars A
  refine mem_of_fW_mem (hvt := hvt) (hR := hR) Λ₁ ν₁ (N.comap (mkR y)) (fun w₁ hw₁ ↦ ?_) hx hxw
  refine mem_of_fW_mem (hvt := hvt) (hR := hR) Λ₂ ν₂ (N.comap (mkL (fW hvt hR Λ₁ w₁)))
    (fun w₂ hw₂ ↦ ?_) hy hyw
  exact hN w₁ w₂ (by rw [hw₁, hw₂, hνν])

/-! ### `S` and `f̃ᵢ` -/

section ShF

variable [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖv : algebraMap A k ϖ = v⁻¹)
  {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s) (hB : ∀ s ≤ d, PropB hvt hR A ϖ s)
  (hC : ∀ s ≤ d, PropC hvt hR A ϖ s)
include hϖ hϖv hA hB hC

/-- `S f̃ᵢ ≡ f̃ᵢ S` modulo `ϖ L(λ₂)` on `L(λ₁) ⊗ L(λ₂)` in depth `d` ([HK] Lemma 5.3.6 (2)). -/
theorem Sh_fT_sub_mem {Λ₁ Λ₂ : Dom R} (i : I) {ν : I →₀ ℕ} (hν : ν.degree = d)
    {z : TM v Λ₁ Λ₂} (hz : z ∈ LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν)) :
    Sh hvt hR Λ₁ Λ₂ (fT hvt hR Λ₁ Λ₂ i z) - fK hvt hR Λ₂ i (Sh hvt hR Λ₁ Λ₂ z) ∈
      ϖ • lat hvt hR A Λ₂ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  let T : TM v Λ₁ Λ₂ →ₗ[k] IrreducibleModule R v Λ₂.1 :=
    Sh hvt hR Λ₁ Λ₂ ∘ₗ fT hvt hR Λ₁ Λ₂ i - fK hvt hR Λ₂ i ∘ₗ Sh hvt hR Λ₁ Λ₂
  -- `T` maps `L ⊗ L` (depth `d`) into `L`
  have hTL : ∀ z' ∈ LL hvt hR A Λ₁ Λ₂,
      z' ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν) → T z' ∈ lat hvt hR A Λ₂ := by
    intro z' hz' hz'w
    exact sub_mem (Sh_mem (fT_mem_LL hϖ hϖv hA i hν hz' hz'w))
      (kashiwaraF_mem_lat Λ₂ i (Sh_mem hz'))
  change T z ∈ ϖ • lat hvt hR A Λ₂
  refine mem_of_fW_tmul_mem (hvt := hvt) (hR := hR) Λ₁ Λ₂ ν
    ((ϖ • lat hvt hR A Λ₂).comap (T.restrictScalars A)) (fun w₁ w₂ hw ↦ ?_) hz hzw
  change T _ ∈ ϖ • lat hvt hR A Λ₂
  set x := fW hvt hR Λ₁ w₁
  set y := fW hvt hR Λ₂ w₂
  have hxyw : TensorModule.mk _ _ (x ⊗ₜ[k] y) ∈
      weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum ν) := by
    have := TensorModule.tmul_mem_weightSpace (fW_mem_wsp hvt hR Λ₁ w₁) (fW_mem_wsp hvt hR Λ₂ w₂)
    convert this using 2
    rw [← hw, R.rootSum_add]
    abel
  have hd₁ : (LusztigF.wordWeight w₁).degree ≤ d := by rw [← hν, ← hw, map_add]; omega
  have hd₂ : (LusztigF.wordWeight w₂).degree ≤ d := by rw [← hν, ← hw, map_add]; omega
  -- the degenerate cases
  by_cases hx0 : x ∈ ϖ • lat hvt hR A Λ₁
  · obtain ⟨z₀, hz₀, hz₀w, he⟩ := TensorModule.exists_smul_weight hϖ0
      (tmul_mem_smul_left hx0 (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂)) hxyw
    rw [he, LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (hTL z₀ hz₀ hz₀w)
  by_cases hy0 : y ∈ ϖ • lat hvt hR A Λ₂
  · obtain ⟨z₀, hz₀, hz₀w, he⟩ := TensorModule.exists_smul_weight hϖ0
      (tmul_mem_smul_right (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁) hy0) hxyw
    rw [he, LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (hTL z₀ hz₀ hz₀w)
  -- both are classes of `B`
  obtain ⟨k₁, a, u, hxs⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ₁ i rfl
    (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁) (fW_mem_wsp hvt hR Λ₁ w₁)
    (w := w₁) (by simp) hx0
  obtain ⟨k₂, b, u', hys⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ₂ i rfl
    (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂) (fW_mem_wsp hvt hR Λ₂ w₂)
    (w := w₂) (by simp) hy0
  have hrule := fT_tmul hϖ hϖv (fun s hs ↦ hA s (by omega)) (fun s hs ↦ hA s (by omega)) rfl rfl
    hxs hys
  have h1 := Sh_mem_smul hrule
  rw [map_sub] at h1
  change Sh hvt hR Λ₁ Λ₂ (fT hvt hR Λ₁ Λ₂ i _) - fK hvt hR Λ₂ i (Sh hvt hR Λ₁ Λ₂ _) ∈
    ϖ • lat hvt hR A Λ₂
  split_ifs at h1 with hc
  · rw [Sh_tmul] at h1
    rw [Sh_tmul, map_smul]
    exact h1
  · -- `f̃ᵢ` acts on the first factor
    rcases w₁ with _ | ⟨j, w₁⟩
    · -- `x = v_{λ₁}`: then `f̃ᵢ y ∈ ϖ L`
      have hk₁ : k₁ = 0 := hxs.eq_zero_of_top
      have hfy : fK hvt hR Λ₂ i y ∈ ϖ • lat hvt hR A Λ₂ :=
        hys.kashiwaraF_mem (by have := hys.le; omega)
      rw [Sh_tmul] at h1
      rw [Sh_tmul]
      have hf0 : IrreducibleModule.form Λ₁.1 hR (pow_ne_one_of_transcendental' hvt)
          (IrreducibleModule.hwv R v Λ₁.1) (fK hvt hR Λ₁ i x) = 0 :=
        form_hwv_fW (hvt := hvt) Λ₁ (w := [i]) (List.cons_ne_nil _ _)
      rw [hf0, zero_smul, sub_zero] at h1
      have hx1 : IrreducibleModule.form Λ₁.1 hR (pow_ne_one_of_transcendental' hvt)
          (IrreducibleModule.hwv R v Λ₁.1) x = 1 := IrreducibleModule.form_hwv _ _
      rw [hx1, one_smul]
      exact sub_mem h1 hfy
    · have hf1 : IrreducibleModule.form Λ₁.1 hR (pow_ne_one_of_transcendental' hvt)
          (IrreducibleModule.hwv R v Λ₁.1) x = 0 :=
        form_hwv_fW (hvt := hvt) Λ₁ (List.cons_ne_nil _ _)
      have hf2 : IrreducibleModule.form Λ₁.1 hR (pow_ne_one_of_transcendental' hvt)
          (IrreducibleModule.hwv R v Λ₁.1) (fK hvt hR Λ₁ i x) = 0 :=
        form_hwv_fW (hvt := hvt) Λ₁ (w := i :: j :: w₁) (List.cons_ne_nil _ _)
      rw [Sh_tmul] at h1
      rw [Sh_tmul, hf1, zero_smul, map_zero, sub_zero]
      rw [hf2, zero_smul, sub_zero] at h1
      exact h1

end ShF

/-! ### `f̃ᵢ` on tensor products of `f̃`-words -/

lemma fW_tmul_mem_weightSpace (Λ₁ Λ₂ : Dom R) (w₁ w₂ : List I) :
    TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈ weightSpace R v (TM v Λ₁ Λ₂)
      (Λ₁.1 + Λ₂.1 - R.rootSum (LusztigF.wordWeight w₁ + LusztigF.wordWeight w₂)) := by
  have := TensorModule.tmul_mem_weightSpace (fW_mem_wsp hvt hR Λ₁ w₁) (fW_mem_wsp hvt hR Λ₂ w₂)
  convert this using 2
  rw [R.rootSum_add]
  abel

lemma fW_tmul_mem_LL (Λ₁ Λ₂ : Dom R) (w₁ w₂ : List I) :
    TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈ LL hvt hR A Λ₁ Λ₂ :=
  TensorModule.tmul_mem_lattice (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁)
    (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂)

/-- On string data, `εᵢ ≤ νᵢ` where `λ - ν` is the weight. -/
lemma IsStr.le_coeff {Λ : Dom R} {i : I} {ν : I →₀ ℕ} {x : IrreducibleModule R v Λ.1}
    {kk a : ℕ} {u : IrreducibleModule R v Λ.1} (h : IsStr hvt hR ϖ Λ i ν x kk a u) :
    kk ≤ ν i := by
  obtain ⟨ν', hν'⟩ := exists_eq_add_single hR (pow_ne_one_of_transcendental' hvt) Λ h.wt h.ne_zero
  rw [hν', Finsupp.add_apply, Finsupp.single_eq_same]
  omega

section Words

variable [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖv : algebraMap A k ϖ = v⁻¹)
include hϖ hϖv

/-- `f̃ᵢ` preserves `ϖ (L(λ₁) ⊗ L(λ₂))` in depth `d`. -/
lemma fT_mem_smul_LL {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s) {Λ₁ Λ₂ : Dom R} (i : I)
    {ν : I →₀ ℕ} (hν : ν.degree = d) {z : TM v Λ₁ Λ₂} (hz : z ∈ ϖ • LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν)) :
    fT hvt hR Λ₁ Λ₂ i z ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  obtain ⟨z₀, hz₀, hz₀w, rfl⟩ := TensorModule.exists_smul_weight hϖ0 hz hzw
  rw [LinearMap.map_smul_of_tower]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (fT_mem_LL hϖ hϖv hA i hν hz₀ hz₀w)

/-- `f̃ᵢ (f̃_{w₁} v ⊗ f̃_{w₂} v)` is `f̃_{i w₁} v ⊗ f̃_{w₂} v` or `f̃_{w₁} v ⊗ f̃_{i w₂} v` modulo
`ϖ (L(λ₁) ⊗ L(λ₂))` ([HK] Lemma 5.3.2 (3)). -/
theorem fT_fW_tmul {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s) (hB : ∀ s ≤ d, PropB hvt hR A ϖ s)
    (hC : ∀ s ≤ d, PropC hvt hR A ϖ s) {Λ₁ Λ₂ : Dom R} (i : I) {w₁ w₂ : List I}
    (hw : w₁.length + w₂.length = d) :
    fT hvt hR Λ₁ Λ₂ i (TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂)) -
        TensorModule.mk _ _ (fW hvt hR Λ₁ (i :: w₁) ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈
        ϖ • LL hvt hR A Λ₁ Λ₂ ∨
      fT hvt hR Λ₁ Λ₂ i (TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂)) -
        TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ (i :: w₂)) ∈
        ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hν : (LusztigF.wordWeight w₁ + LusztigF.wordWeight w₂).degree = d := by
    rw [map_add, degree_wordWeight, degree_wordWeight, hw]
  have hfT := fun hmem ↦ fT_mem_smul_LL hϖ hϖv hA i hν hmem
    (fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ w₁ w₂)
  by_cases hx0 : fW hvt hR Λ₁ w₁ ∈ ϖ • lat hvt hR A Λ₁
  · left
    exact sub_mem
      (hfT (tmul_mem_smul_left hx0 (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂)))
      (tmul_mem_smul_left (kashiwaraF_mem_smul_lat Λ₁ i hx0)
        (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂))
  by_cases hy0 : fW hvt hR Λ₂ w₂ ∈ ϖ • lat hvt hR A Λ₂
  · right
    exact sub_mem
      (hfT (tmul_mem_smul_right (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁) hy0))
      (tmul_mem_smul_right (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁)
        (kashiwaraF_mem_smul_lat Λ₂ i hy0))
  have hd₁ : w₁.length ≤ d := by omega
  have hd₂ : w₂.length ≤ d := by omega
  obtain ⟨k₁, a, u, hxs⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ₁ i (degree_wordWeight w₁)
    (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁) (fW_mem_wsp hvt hR Λ₁ w₁)
    (w := w₁) (by simp) hx0
  obtain ⟨k₂, b, u', hys⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ₂ i (degree_wordWeight w₂)
    (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂) (fW_mem_wsp hvt hR Λ₂ w₂)
    (w := w₂) (by simp) hy0
  have hrule := fT_tmul hϖ hϖv (fun s hs ↦ hA s (by omega)) (fun s hs ↦ hA s (by omega))
    (degree_wordWeight w₁) (degree_wordWeight w₂) hxs hys
  split_ifs at hrule
  · exact Or.inr hrule
  · exact Or.inl hrule

end Words

/-! ### Words of Kashiwara operators on `V(λ₁) ⊗ V(λ₂)` -/

variable (hvt hR) in
/-- `f̃_{i₁} ⋯ f̃_{iᵣ}` on `V(λ₁) ⊗ V(λ₂)`. -/
def fTw (Λ₁ Λ₂ : Dom R) : List I → Module.End k (TM v Λ₁ Λ₂)
  | [] => 1
  | i :: w => fT hvt hR Λ₁ Λ₂ i * fTw Λ₁ Λ₂ w

@[simp] lemma fTw_nil (Λ₁ Λ₂ : Dom R) (z : TM v Λ₁ Λ₂) : fTw hvt hR Λ₁ Λ₂ [] z = z := rfl

@[simp] lemma fTw_cons (Λ₁ Λ₂ : Dom R) (i : I) (w : List I) (z : TM v Λ₁ Λ₂) :
    fTw hvt hR Λ₁ Λ₂ (i :: w) z = fT hvt hR Λ₁ Λ₂ i (fTw hvt hR Λ₁ Λ₂ w z) := rfl

lemma fTw_append (Λ₁ Λ₂ : Dom R) (u w : List I) (z : TM v Λ₁ Λ₂) :
    fTw hvt hR Λ₁ Λ₂ (u ++ w) z = fTw hvt hR Λ₁ Λ₂ u (fTw hvt hR Λ₁ Λ₂ w z) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp [ih]

lemma fTw_mem_weightSpace (Λ₁ Λ₂ : Dom R) (u : List I) {ν : I →₀ ℕ} {z : TM v Λ₁ Λ₂}
    (hz : z ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν)) :
    fTw hvt hR Λ₁ Λ₂ u z ∈
      weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum (ν + LusztigF.wordWeight u)) := by
  induction u with
  | nil => simpa using hz
  | cons i u ih =>
    have := kashiwaraF_mem_weightSpace (pow_ne_one_of_transcendental' hvt) (isIntT hvt hR Λ₁ Λ₂)
      i ih
    rw [fTw_cons]
    convert this using 2
    rw [LusztigF.wordWeight_cons, R.rootSum_add, R.rootSum_add, R.rootSum_add, R.rootSum_single,
      one_nsmul]
    abel

section WordsTensor

variable [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖv : algebraMap A k ϖ = v⁻¹)
include hϖ hϖv

/-- `f̃`-words preserve `ϖ (L(λ₁) ⊗ L(λ₂))`. -/
lemma fTw_mem_smul_LL {Λ₁ Λ₂ : Dom R} (u : List I) {ν : I →₀ ℕ}
    (hA : ∀ s < ν.degree + u.length, PropA hvt hR A s) {z : TM v Λ₁ Λ₂}
    (hz : z ∈ ϖ • LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν)) :
    fTw hvt hR Λ₁ Λ₂ u z ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  induction u with
  | nil => simpa using hz
  | cons i u ih =>
    rw [fTw_cons]
    refine fT_mem_smul_LL hϖ hϖv (d := (ν + LusztigF.wordWeight u).degree)
      (fun s hs ↦ hA s ?_) i rfl (ih fun s hs ↦ hA s (by simp only [List.length_cons]; omega))
      (fTw_mem_weightSpace Λ₁ Λ₂ u hzw)
    rw [map_add, degree_wordWeight] at hs
    simp only [List.length_cons]
    omega

/-- Iterating `fT_fW_tmul`: an `f̃`-word applied to `f̃_{w₁} v ⊗ f̃_{w₂} v` is congruent to some
`f̃_{w₁'} v ⊗ f̃_{w₂'} v` with `w₁'`, `w₂'` extending `w₁`, `w₂` in length. -/
theorem fTw_fW_tmul {Λ₁ Λ₂ : Dom R} (u : List I) {w₁ w₂ : List I}
    (hA : ∀ s < w₁.length + w₂.length + u.length, PropA hvt hR A s)
    (hB : ∀ s < w₁.length + w₂.length + u.length, PropB hvt hR A ϖ s)
    (hC : ∀ s < w₁.length + w₂.length + u.length, PropC hvt hR A ϖ s) :
    ∃ w₁' w₂' : List I, w₁.length ≤ w₁'.length ∧ w₂.length ≤ w₂'.length ∧
      w₁'.length + w₂'.length = w₁.length + w₂.length + u.length ∧
      LusztigF.wordWeight w₁' + LusztigF.wordWeight w₂' =
        LusztigF.wordWeight w₁ + LusztigF.wordWeight w₂ + LusztigF.wordWeight u ∧
      fTw hvt hR Λ₁ Λ₂ u (TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂)) -
        TensorModule.mk _ _ (fW hvt hR Λ₁ w₁' ⊗ₜ[k] fW hvt hR Λ₂ w₂') ∈
        ϖ • LL hvt hR A Λ₁ Λ₂ := by
  induction u with
  | nil => exact ⟨w₁, w₂, le_rfl, le_rfl, rfl, by simp, by simp⟩
  | cons i u ih =>
    simp only [List.length_cons] at hA hB hC
    obtain ⟨w₁', w₂', h1, h2, h3, h5, h4⟩ := ih (fun s hs ↦ hA s (by omega))
      (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega))
    have hw' := fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ w₁' w₂'
    have hwu := fTw_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ u
      (fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ w₁ w₂)
    have hdeg : (LusztigF.wordWeight w₁' + LusztigF.wordWeight w₂').degree =
        w₁.length + w₂.length + u.length := by
      rw [map_add, degree_wordWeight, degree_wordWeight, h3]
    have hsame : LusztigF.wordWeight w₁ + LusztigF.wordWeight w₂ + LusztigF.wordWeight u =
        LusztigF.wordWeight w₁' + LusztigF.wordWeight w₂' := h5.symm
    have hstep := fT_mem_smul_LL hϖ hϖv (d := w₁.length + w₂.length + u.length)
      (fun s hs ↦ hA s (by omega)) i hdeg h4 (sub_mem (hsame ▸ hwu) hw')
    rw [map_sub] at hstep
    rcases fT_fW_tmul hϖ hϖv (d := w₁.length + w₂.length + u.length)
      (fun s hs ↦ hA s (by omega)) (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) i
      (w₁ := w₁') (w₂ := w₂') h3 with h | h
    · refine ⟨i :: w₁', w₂', by simp; omega, h2, by simp; omega,
        by simp only [LusztigF.wordWeight_cons]; rw [add_assoc, h5]; abel, ?_⟩
      rw [fTw_cons]
      simpa using add_mem hstep h
    · refine ⟨w₁', i :: w₂', h1, by simp; omega, by simp; omega,
        by simp only [LusztigF.wordWeight_cons]; rw [add_left_comm, h5]; abel, ?_⟩
      rw [fTw_cons]
      simpa using add_mem hstep h

/-- `f̃_w (v_{λ₁} ⊗ v_{λ₂}) ≡ v_{λ₁} ⊗ f̃_w v_{λ₂}` unless `f̃_w v_{λ₂} ∈ ϖ L(λ₂)`
([HK] Lemma 5.3.2 (7), library order). -/
theorem fTw_hwv_tmul (hinj : Function.Injective (algebraMap A k)) {Λ₁ Λ₂ : Dom R} :
    ∀ w : List I, (∀ s < w.length, PropA hvt hR A s) → (∀ s < w.length, PropB hvt hR A ϖ s) →
      (∀ s < w.length, PropC hvt hR A ϖ s) → fW hvt hR Λ₂ w ∉ ϖ • lat hvt hR A Λ₂ →
      fTw hvt hR Λ₁ Λ₂ w (TensorModule.mk _ _ (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k]
        IrreducibleModule.hwv R v Λ₂.1)) -
      TensorModule.mk _ _ (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k] fW hvt hR Λ₂ w) ∈
        ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hϖu : ¬IsUnit ϖ := (IsLocalRing.mem_maximalIdeal ϖ).1 hϖ
  intro w
  induction w with
  | nil => intro _ _ _ _; simp
  | cons i w ih =>
    intro hA hB hC hw0
    simp only [List.length_cons] at hA hB hC
    have hw0' : fW hvt hR Λ₂ w ∉ ϖ • lat hvt hR A Λ₂ := fun h ↦
      hw0 (kashiwaraF_mem_smul_lat Λ₂ i h)
    have hih := ih (fun s hs ↦ hA s (by omega)) (fun s hs ↦ hB s (by omega))
      (fun s hs ↦ hC s (by omega)) hw0'
    have hwt : fTw hvt hR Λ₁ Λ₂ w (TensorModule.mk _ _ (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k]
        IrreducibleModule.hwv R v Λ₂.1)) -
        TensorModule.mk _ _ (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k] fW hvt hR Λ₂ w) ∈
        weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum (LusztigF.wordWeight w)) := by
      have h1 := fTw_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ w
        (fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ [] [])
      have h2 := fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ [] w
      simp only [LusztigF.wordWeight_nil, zero_add] at h1 h2
      exact sub_mem h1 h2
    have hstep := fT_mem_smul_LL hϖ hϖv (d := w.length) (fun s hs ↦ hA s (by omega)) i
      (degree_wordWeight w) hih hwt
    obtain ⟨k₂, b, u', hys⟩ := exists_isStr hϖ0 (fun s hs ↦ hA s (by omega))
      (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) Λ₂ i (degree_wordWeight w)
      (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w) (fW_mem_wsp hvt hR Λ₂ w)
      (w := w) (by simp) hw0'
    have hrule := fT_tmul hϖ hϖv (d₁ := 0) (fun s hs ↦ hA s (by omega))
      (fun s hs ↦ hA s (by omega)) (by simp) (degree_wordWeight w)
      (isStr_hwv hinj hϖu Λ₁ i) hys
    split_ifs at hrule with hc
    · rw [map_sub] at hstep
      rw [fTw_cons]
      simpa [fW_cons] using add_mem hstep hrule
    · exact absurd (hys.kashiwaraF_mem (by have := hys.le; omega)) hw0

/-- **[HK] Lemma 5.3.4** (library order): for `λ₂ = Λ_j` fundamental and any word ending in
`j, i`, `f̃_{u j i} (v_{λ₁} ⊗ v_{λ₂}) ≡ f̃_{w₁} v_{λ₁} ⊗ f̃_{w₂} v_{λ₂}` with `w₁`, `w₂`
nonempty. -/
theorem fTw_fund (hinj : Function.Injective (algebraMap A k)) {Λ₁ Λ₂ : Dom R} {j : I}
    (hj : ∀ i, Λ₂.1 (R.coroot i) = if i = j then 1 else 0) (u : List I) (i : I)
    (hA : ∀ s < u.length + 2, PropA hvt hR A s) (hB : ∀ s < u.length + 2, PropB hvt hR A ϖ s)
    (hC : ∀ s < u.length + 2, PropC hvt hR A ϖ s) :
    ∃ w₁ w₂ : List I, 1 ≤ w₁.length ∧ 1 ≤ w₂.length ∧ w₁.length + w₂.length = u.length + 2 ∧
      LusztigF.wordWeight w₁ + LusztigF.wordWeight w₂ = LusztigF.wordWeight (u ++ [j, i]) ∧
      fTw hvt hR Λ₁ Λ₂ (u ++ [j, i]) (TensorModule.mk _ _ (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k]
        IrreducibleModule.hwv R v Λ₂.1)) -
      TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hϖu : ¬IsUnit ϖ := (IsLocalRing.mem_maximalIdeal ϖ).1 hϖ
  have hA0 : ∀ s ≤ 0, PropA hvt hR A s := fun s hs ↦ hA s (by omega)
  have hA1 : ∀ s ≤ 1, PropA hvt hR A s := fun s hs ↦ hA s (by omega)
  have hB1 : ∀ s ≤ 1, PropB hvt hR A ϖ s := fun s hs ↦ hB s (by omega)
  have hC1 : ∀ s ≤ 1, PropC hvt hR A ϖ s := fun s hs ↦ hC s (by omega)
  set vv := TensorModule.mk (IrreducibleModule R v Λ₁.1) (IrreducibleModule R v Λ₂.1)
    (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k] IrreducibleModule.hwv R v Λ₂.1)
  -- the first two steps
  have hvvw : vv ∈ weightSpace R v (TM v Λ₁ Λ₂) (Λ₁.1 + Λ₂.1 - R.rootSum 0) := by
    simpa using fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ [] []
  have hFw : ∀ (w₁ w₂ : List I), TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) ∈
      weightSpace R v (TM v Λ₁ Λ₂)
        (Λ₁.1 + Λ₂.1 - R.rootSum (LusztigF.wordWeight w₁ + LusztigF.wordWeight w₂)) :=
    fun w₁ w₂ ↦ fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ w₁ w₂
  have r1 := fT_tmul hϖ hϖv hA0 hA0 (by simp) (by simp) (isStr_hwv hinj hϖu Λ₁ i)
    (isStr_hwv hinj hϖu Λ₂ i)
  have hwt1 : ∀ z, z ∈ weightSpace R v (TM v Λ₁ Λ₂)
      (Λ₁.1 + Λ₂.1 - R.rootSum (Finsupp.single i 1)) →
      fT hvt hR Λ₁ Λ₂ i vv - z ∈ weightSpace R v (TM v Λ₁ Λ₂)
        (Λ₁.1 + Λ₂.1 - R.rootSum (Finsupp.single i 1)) := fun z hz ↦ by
    refine sub_mem ?_ hz
    have := kashiwaraF_mem_weightSpace (pow_ne_one_of_transcendental' hvt) (isIntT hvt hR Λ₁ Λ₂)
      i hvvw
    convert this using 2
    simp
  have h2 : fTw hvt hR Λ₁ Λ₂ [j, i] vv -
      TensorModule.mk _ _ (fW hvt hR Λ₁ [i] ⊗ₜ[k] fW hvt hR Λ₂ [j]) ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
    simp only [fTw_cons, fTw_nil]
    by_cases hij : i = j
    · subst hij
      have hb : 0 < (Λ₂.1 (R.coroot i)).toNat - 0 := by rw [hj]; simp
      simp only [hb, ↓reduceIte] at r1
      have s2 := fT_mem_smul_LL hϖ hϖv hA1 i (ν := Finsupp.single i 1) (by simp) r1
        (hwt1 _ (by simpa using hFw [] [i]))
      rw [map_sub] at s2
      by_cases hy0 : fW hvt hR Λ₂ [i] ∈ ϖ • lat hvt hR A Λ₂
      · have e1 := fT_mem_smul_LL hϖ hϖv hA1 i (ν := Finsupp.single i 1) (by simp)
          (tmul_mem_smul_right (IrreducibleModule.hwv_mem_lattice hR _ Λ₁.2 A) hy0)
          (by simpa using hFw [] [i])
        have e2 := tmul_mem_smul_right (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A [i]) hy0
        simpa using add_mem s2 (sub_mem e1 e2)
      obtain ⟨k₂, b, u', hys⟩ := exists_isStr hϖ0 hA1 hB1 hC1 Λ₂ i (degree_wordWeight [i])
        (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A [i]) (fW_mem_wsp hvt hR Λ₂ [i])
        (w := [i]) (by simp) hy0
      have hk₂ : k₂ ≤ 1 := by simpa using hys.le_coeff
      have hb' := hys.node
      have hle := hys.le
      simp only [LusztigF.wordWeight_cons, LusztigF.wordWeight_nil, add_zero, R.rootSum_single,
        one_nsmul, AddMonoidHom.sub_apply, R.root_coroot, D.cartanMatrix_self, hj,
        ↓reduceIte] at hb'
      have r2 := fT_tmul hϖ hϖv hA0 hA1 (by simp) (degree_wordWeight [i])
        (isStr_hwv hinj hϖu Λ₁ i) hys
      have hc : ¬ (0 < b - k₂) := by omega
      simp only [hc, ↓reduceIte] at r2
      simpa using add_mem s2 r2
    · have hb : ¬ (0 < (Λ₂.1 (R.coroot i)).toNat - 0) := by rw [hj]; simp [hij]
      simp only [hb, ↓reduceIte] at r1
      have s2 := fT_mem_smul_LL hϖ hϖv hA1 j (ν := Finsupp.single i 1) (by simp) r1
        (hwt1 _ (by simpa using hFw [i] []))
      rw [map_sub] at s2
      by_cases hx0 : fW hvt hR Λ₁ [i] ∈ ϖ • lat hvt hR A Λ₁
      · have e1 := fT_mem_smul_LL hϖ hϖv hA1 j (ν := Finsupp.single i 1) (by simp)
          (tmul_mem_smul_left hx0 (IrreducibleModule.hwv_mem_lattice hR _ Λ₂.2 A))
          (by simpa using hFw [i] [])
        have e2 := tmul_mem_smul_left hx0 (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A [j])
        simpa using add_mem s2 (sub_mem e1 e2)
      obtain ⟨k₁, a, u, hxs⟩ := exists_isStr hϖ0 hA1 hB1 hC1 Λ₁ j (degree_wordWeight [i])
        (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A [i]) (fW_mem_wsp hvt hR Λ₁ [i])
        (w := [i]) (by simp) hx0
      have hk₁ : k₁ = 0 := by
        have := hxs.le_coeff
        simp [hij] at this
        omega
      subst hk₁
      have r2 := fT_tmul hϖ hϖv hA1 hA0 (degree_wordWeight [i]) (by simp) hxs
        (isStr_hwv hinj hϖu Λ₂ j)
      have hc : 0 < (Λ₂.1 (R.coroot j)).toNat - 0 := by rw [hj]; simp
      simp only [hc, ↓reduceIte] at r2
      simpa using add_mem s2 r2
  obtain ⟨w₁, w₂, h1, h2', h3, h5, h4⟩ := fTw_fW_tmul hϖ hϖv (Λ₁ := Λ₁) (Λ₂ := Λ₂) u
    (w₁ := [i]) (w₂ := [j]) (fun s hs ↦ hA s (by simpa [add_comm] using hs))
    (fun s hs ↦ hB s (by simpa [add_comm] using hs))
    (fun s hs ↦ hC s (by simpa [add_comm] using hs))
  refine ⟨w₁, w₂, h1, h2', by simp at h3; omega, ?_, ?_⟩
  · rw [h5]
    simp only [LusztigF.wordWeight_cons, LusztigF.wordWeight_nil, add_zero,
      LusztigF.wordWeight_append]
    abel
  · rw [fTw_append]
    have hwt : fTw hvt hR Λ₁ Λ₂ [j, i] vv -
        TensorModule.mk _ _ (fW hvt hR Λ₁ [i] ⊗ₜ[k] fW hvt hR Λ₂ [j]) ∈
        weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum (LusztigF.wordWeight [j, i])) := by
      refine sub_mem ?_ ?_
      · simpa using fTw_mem_weightSpace (hvt := hvt) (hR := hR) Λ₁ Λ₂ [j, i] hvvw
      · convert hFw [i] [j] using 3
        simp only [LusztigF.wordWeight_cons, LusztigF.wordWeight_nil, add_zero]
        abel_nf
    have := fTw_mem_smul_LL hϖ hϖv u (fun s hs ↦ hA s ?_) h2 hwt
    · rw [map_sub] at this
      simpa using add_mem this h4
    · rw [degree_wordWeight] at hs
      simp at hs
      omega

end WordsTensor

end GrandLoop

end LieLean.QuantumGroup

end
