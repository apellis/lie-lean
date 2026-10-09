/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Head

/-!
# Kashiwara's grand loop: the statement `A(r)`

We prove `A(r)`: `ẽᵢ L(λ)_{depth r} ⊆ L(λ)` ([HK] Prop. 5.3.9), by a descending induction on `N`
in `ẽᵢ L(μ)_{depth r} ⊆ ϖ^{-N} L(μ)` ([HK] Lemmas 5.3.7, 5.3.8). Our argument differs from [HK] in
one point: [HK] run the induction for all `μ ≫ 0` simultaneously, using a uniform bound justified by
an identification `Σ V(λ)_{λ-α} ≅ Σ V(μ)_{μ-α}` "commuting with `ẽᵢ`, `f̃ᵢ`", which does not hold
(already for `𝔰𝔩₂` the actions of `ẽ` differ). We run it instead on the finite set consisting of the
given weight and the fundamental weights, which is all that the two steps of [HK] Lemma 5.3.8 use.

## Main definitions

* `QuantumGroup.GrandLoop.negLat`: `ϖ^{-n} L = {x | ϖⁿ x ∈ L}`.
* `QuantumGroup.GrandLoop.PropAN`: `ẽᵢ L(μ)_{depth r} ⊆ ϖ^{-N} L(μ)`.

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

/-! ### `ϖ^{-n} L` -/

/-- `ϖ^{-n} L = {x | ϖⁿ x ∈ L}`. -/
def negLat {M : Type*} [AddCommGroup M] [Module A M] (L : Submodule A M) (ϖ : A) (n : ℕ) :
    Submodule A M :=
  L.comap ((ϖ ^ n) • LinearMap.id)

lemma mem_negLat {M : Type*} [AddCommGroup M] [Module A M] {L : Submodule A M} {n : ℕ} {x : M} :
    x ∈ negLat L ϖ n ↔ ϖ ^ n • x ∈ L := Iff.rfl

lemma le_negLat {M : Type*} [AddCommGroup M] [Module A M] (L : Submodule A M) (n : ℕ) :
    L ≤ negLat L ϖ n := fun _ hx ↦ mem_negLat.2 (Submodule.smul_mem _ _ hx)

omit [CharZero k] in
lemma lattice_negLat_left {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module A M₁]
    [IsScalarTower A k M₁] [AddCommGroup M₂] [Module k M₂] [Module A M₂] [IsScalarTower A k M₂]
    {L₁ : Submodule A M₁} {L₂ : Submodule A M₂} {n : ℕ} {z : TensorModule k M₁ M₂}
    (hz : z ∈ TensorModule.lattice k A (negLat L₁ ϖ n) L₂) :
    ϖ ^ n • z ∈ TensorModule.lattice k A L₁ L₂ := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    change TensorModule.mk _ _ (ϖ ^ n • (x ⊗ₜ[k] y)) ∈ _
    rw [smul_tmul']
    exact TensorModule.tmul_mem_lattice (mem_negLat.1 hx) hy
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

omit [CharZero k] in
lemma lattice_negLat_right {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module A M₁]
    [IsScalarTower A k M₁] [AddCommGroup M₂] [Module k M₂] [Module A M₂] [IsScalarTower A k M₂]
    {L₁ : Submodule A M₁} {L₂ : Submodule A M₂} {n : ℕ} {z : TensorModule k M₁ M₂}
    (hz : z ∈ TensorModule.lattice k A L₁ (negLat L₂ ϖ n)) :
    ϖ ^ n • z ∈ TensorModule.lattice k A L₁ L₂ := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    change TensorModule.mk _ _ (ϖ ^ n • (x ⊗ₜ[k] y)) ∈ _
    rw [← tmul_smul]
    exact TensorModule.tmul_mem_lattice hx (mem_negLat.1 hy)
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

/-! ### Local `ẽᵢ`-stability strictly above -/

/-- From `A(s)` for `s < d`: `ẽᵢ` preserves `L(λ)` on the weights `λ - ν + j αᵢ`, `j ≥ 1`. -/
lemma localE_succ {d : ℕ} (hA : ∀ s < d, PropA hvt hR A s) (Λ : Dom R) {ν : I →₀ ℕ}
    (hν : ν.degree = d) (i : I) (j : ℕ) (hj : 1 ≤ j) {y : IrreducibleModule R v Λ.1}
    (hy : y ∈ lat hvt hR A Λ)
    (hyw : y ∈ weightSpace R v _ (Λ.1 - R.rootSum ν + j • R.root i)) :
    eK hvt hR Λ i y ∈ lat hvt hR A Λ := by
  by_cases hy0 : y = 0
  · rw [hy0, map_zero]; exact zero_mem _
  obtain ⟨ν', rfl⟩ := exists_eq_add_single hR (pow_ne_one_of_transcendental' hvt) Λ hyw hy0
  have hyw' : y ∈ wsp Λ ν' := by
    convert hyw using 2
    rw [R.rootSum_add, R.rootSum_single]
    abel
  refine hA ν'.degree ?_ Λ ν' rfl i y hy hyw'
  rw [← hν, map_add, Finsupp.degree_single]
  omega

lemma kashiwaraF_mem_negLat (Λ : Dom R) (i : I) (n : ℕ) {y : IrreducibleModule R v Λ.1}
    (hy : y ∈ negLat (lat hvt hR A Λ) ϖ n) : fK hvt hR Λ i y ∈ negLat (lat hvt hR A Λ) ϖ n := by
  rw [mem_negLat, ← LinearMap.map_smul_of_tower]
  exact kashiwaraF_mem_lat Λ i (mem_negLat.1 hy)

lemma localE_succ_negLat {d : ℕ} (hA : ∀ s < d, PropA hvt hR A s) (Λ : Dom R) {ν : I →₀ ℕ}
    (hν : ν.degree = d) (i : I) (n j : ℕ) (hj : 1 ≤ j) {y : IrreducibleModule R v Λ.1}
    (hy : y ∈ negLat (lat hvt hR A Λ) ϖ n)
    (hyw : y ∈ weightSpace R v _ (Λ.1 - R.rootSum ν + j • R.root i)) :
    eK hvt hR Λ i y ∈ negLat (lat hvt hR A Λ) ϖ n := by
  rw [mem_negLat, ← LinearMap.map_smul_of_tower]
  exact localE_succ hA Λ hν i j hj (mem_negLat.1 hy) (Submodule.smul_mem _ _ hyw)

/-! ### The statement `ẽᵢ L(μ)_{depth r} ⊆ ϖ^{-N} L(μ)` -/

variable (hvt hR A ϖ) in
/-- `ẽᵢ L(μ)_{depth r} ⊆ ϖ^{-N} L(μ)`, on generators. -/
def PropAN (r N : ℕ) (Λ : Dom R) : Prop :=
  ∀ (i : I) (w : List I), w.length = r → ϖ ^ N • eK hvt hR Λ i (fW hvt hR Λ w) ∈ lat hvt hR A Λ

lemma PropAN.mem {r N : ℕ} {Λ : Dom R} (h : PropAN hvt hR A ϖ r N Λ) (i : I) {ν : I →₀ ℕ}
    (hν : ν.degree = r) {x : IrreducibleModule R v Λ.1} (hx : x ∈ lat hvt hR A Λ)
    (hxw : x ∈ wsp Λ ν) : ϖ ^ N • eK hvt hR Λ i x ∈ lat hvt hR A Λ :=
  mem_of_fW_mem Λ ν ((lat hvt hR A Λ).comap
    (((ϖ ^ N) • (eK hvt hR Λ i)).restrictScalars A))
    (fun w hw ↦ h i w (by rw [← degree_wordWeight, hw, hν])) hx hxw

/-- Under `ẽᵢ L(μ)_{depth r} ⊆ ϖ^{-N} L(μ)`, the string vectors of `y ∈ L(μ)_{depth r}` lie in
`ϖ^{-N} L(μ)` (cf. [HK] Exercise 5.9). -/
lemma exists_strings_negLat {r N : ℕ} (hA : ∀ s < r, PropA hvt hR A s) {Λ : Dom R}
    (hP : PropAN hvt hR A ϖ r N Λ) (i : I) {ν : I →₀ ℕ} (hν : ν.degree = r)
    {y : IrreducibleModule R v Λ.1} (hy : y ∈ lat hvt hR A Λ) (hyw : y ∈ wsp Λ ν) :
    ∃ (M : ℕ) (ζ : ℕ → IrreducibleModule R v Λ.1),
      (∀ j : ℕ, ζ j ∈ weightSpace R v _ (Λ.1 - R.rootSum ν + j • R.root i)) ∧
      (∀ j, E R v i • ζ j = 0) ∧ (∀ j : ℕ, ζ j ≠ 0 → 0 ≤ (Λ.1 - R.rootSum ν) (R.coroot i) + j) ∧
      y = ∑ j ∈ range M, dFV (hvt := hvt) (hR := hR) Λ i j (ζ j) ∧
      ∀ j < M, ζ j ∈ negLat (lat hvt hR A Λ) ϖ N := by
  obtain ⟨M, ζ, hζw, hζE, hζ2, -, hye⟩ :=
    exists_sum_dF_weight (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i hyw
  refine ⟨M, ζ, hζw, hζE, hζ2, hye, ?_⟩
  rcases M with _ | M
  · intro j hj; omega
  have he := hP.mem i hν hy hyw
  rw [hye, kashiwaraE_sum _ _ i hζw hζE hζ2] at he
  have hs := mem_of_sum_mem_weight (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i
    (L := negLat (lat hvt hR A Λ) ϖ N) (fun _ hy ↦ kashiwaraF_mem_negLat Λ i N hy) M _
    (fun j ↦ ζ (j + 1))
    (fun j ↦ by rw [add_assoc, ← succ_nsmul']; exact hζw (j + 1)) (fun j ↦ hζE (j + 1))
    (fun j h ↦ by
      have := hζ2 _ h
      rw [AddMonoidHom.add_apply, R.root_coroot, D.cartanMatrix_self]
      push_cast at this ⊢; omega)
    (fun j y hy hyw ↦ localE_succ_negLat hA Λ hν i N (j + 1) (by omega) hy
      (by rwa [succ_nsmul', ← add_assoc]))
    (mem_negLat.2 he)
  intro j hj
  rcases j with _ | j
  · have hrest : ∑ j ∈ range M, dFV (hvt := hvt) (hR := hR) Λ i (j + 1) (ζ (j + 1)) ∈
        negLat (lat hvt hR A Λ) ϖ N := by
      refine Submodule.sum_mem _ fun j hj ↦ ?_
      rw [← kashiwaraF_pow_of_primitive _ _ i (hζE (j + 1))
        (mem_nodeWt_of_mem_add_nsmul i (hζw (j + 1)))]
      exact kashiwaraF_pow_mem _ _ i (fun _ hy ↦ kashiwaraF_mem_negLat Λ i N hy) _
        (hs j (mem_range.1 hj))
    have := sub_mem (le_negLat _ N (hye ▸ hy)) hrest
    rw [sum_range_succ', IntegrableSl2.dF_zero, add_sub_cancel_left] at this
    exact this
  · exact hs j (by omega)

/-- The string decomposition of `v_λ`. -/
lemma hwv_strings (Λ : Dom R) (i : I) :
    let η : ℕ → IrreducibleModule R v Λ.1 := fun s ↦ if s = 0 then IrreducibleModule.hwv R v Λ.1
      else 0
    (∀ j : ℕ, η j ∈ weightSpace R v _ (Λ.1 + j • R.root i)) ∧ (∀ j, E R v i • η j = 0) ∧
      (∀ j : ℕ, η j ≠ 0 → 0 ≤ Λ.1 (R.coroot i) + j) ∧
      (∑ j ∈ range 1, dFV (hvt := hvt) (hR := hR) Λ i j (η j) = IrreducibleModule.hwv R v Λ.1) ∧
      (∀ j < 1, η j ∈ lat hvt hR A Λ) := by
  refine ⟨fun j ↦ ?_, fun j ↦ ?_, fun j hj ↦ ?_, by simp, fun j hj ↦ ?_⟩
  · beta_reduce
    split_ifs with h
    · subst h; simpa using IrreducibleModule.hwv_mem_weightSpace (R := R) (v := v) (Λ := Λ.1)
    · exact zero_mem _
  · beta_reduce
    split_ifs
    · exact IrreducibleModule.E_smul_hwv i
    · exact smul_zero _
  · beta_reduce at hj
    split_ifs at hj with h
    · subst h; have := Λ.2 i; simpa using this
    · exact absurd rfl hj
  · obtain rfl : j = 0 := by omega
    simpa using IrreducibleModule.hwv_mem_lattice hR _ Λ.2 A

/-- **[HK] Lemma 5.3.7**: if `ẽᵢ L(λᵢ)_{depth r} ⊆ ϖ^{-N} L(λᵢ)` for `i = 1, 2`, then
`ẽᵢ (L(λ₁) ⊗ L(λ₂))_{depth r} ⊆ ϖ^{-N} (L(λ₁) ⊗ L(λ₂))`. -/
theorem eT_smul_mem_LL [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖv : algebraMap A k ϖ = v⁻¹) {r N : ℕ} (hA : ∀ s < r, PropA hvt hR A s) {Λ₁ Λ₂ : Dom R}
    (hP₁ : PropAN hvt hR A ϖ r N Λ₁) (hP₂ : PropAN hvt hR A ϖ r N Λ₂) (i : I) {ν : I →₀ ℕ}
    (hν : ν.degree = r) {z : TM v Λ₁ Λ₂} (hz : z ∈ LL hvt hR A Λ₁ Λ₂)
    (hzw : z ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν)) :
    ϖ ^ N • eT hvt hR Λ₁ Λ₂ i z ∈ LL hvt hR A Λ₁ Λ₂ := by
  set hv' := pow_ne_one_of_transcendental' hvt
  refine mem_of_fW_tmul_mem Λ₁ Λ₂ ν ((LL hvt hR A Λ₁ Λ₂).comap
    (((ϖ ^ N) • eT hvt hR Λ₁ Λ₂ i).restrictScalars A)) (fun w₁ w₂ hw ↦ ?_) hz hzw
  change ϖ ^ N • eT hvt hR Λ₁ Λ₂ i _ ∈ LL hvt hR A Λ₁ Λ₂
  have hlen : w₁.length + w₂.length = r := by
    rw [← degree_wordWeight, ← degree_wordWeight, ← map_add, hw, hν]
  rcases w₁ with _ | ⟨j₁, w₁'⟩
  · -- `v_{λ₁} ⊗ f̃_{w₂} v_{λ₂}`
    simp only [List.length_nil, zero_add] at hlen
    have hw₂ : LusztigF.wordWeight w₂ = ν := by simpa using hw
    obtain ⟨M, ζ, hζw, hζE, hζ2, hye, hζL⟩ := exists_strings_negLat hA hP₂ i hν
      (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂) (hw₂ ▸ fW_mem_wsp hvt hR Λ₂ w₂)
    obtain ⟨hηw, hηE, hη2, hηs, hηL⟩ := hwv_strings (hvt := hvt) (hR := hR) (A := A) Λ₁ i
    obtain ⟨P, hP, hle, -, hPe⟩ := TensorModule.exists_stable_tmul_of_strings hv'
      (isInt hvt hR Λ₁) (isInt hvt hR Λ₂) i (L₁ := lat hvt hR A Λ₁)
      (L₂ := negLat (lat hvt hR A Λ₂) ϖ N) (fun _ hy ↦ kashiwaraF_mem_lat Λ₁ i hy)
      (fun _ hy ↦ kashiwaraF_mem_negLat Λ₂ i N hy) hϖ hϖv hηw hηE hη2 hζw hζE hζ2 hηL hζL
    rw [hηs, ← hye] at hP
    exact lattice_negLat_right (hle (hPe _ hP))
  rcases w₂ with _ | ⟨j₂, w₂'⟩
  · -- `f̃_{w₁} v_{λ₁} ⊗ v_{λ₂}`
    simp only [List.length_nil, add_zero] at hlen
    have hw₁ : LusztigF.wordWeight (j₁ :: w₁') = ν := by simpa using hw
    obtain ⟨M, η, hηw, hηE, hη2, hxe, hηL⟩ := exists_strings_negLat hA hP₁ i hν
      (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A _) (hw₁ ▸ fW_mem_wsp hvt hR Λ₁ _)
    obtain ⟨hζw, hζE, hζ2, hζs, hζL⟩ := hwv_strings (hvt := hvt) (hR := hR) (A := A) Λ₂ i
    obtain ⟨P, hP, hle, -, hPe⟩ := TensorModule.exists_stable_tmul_of_strings hv'
      (isInt hvt hR Λ₁) (isInt hvt hR Λ₂) i (L₁ := negLat (lat hvt hR A Λ₁) ϖ N)
      (L₂ := lat hvt hR A Λ₂) (fun _ hy ↦ kashiwaraF_mem_negLat Λ₁ i N hy)
      (fun _ hy ↦ kashiwaraF_mem_lat Λ₂ i hy) hϖ hϖv hηw hηE hη2 hζw hζE hζ2 hηL hζL
    rw [hζs, ← hxe] at hP
    exact lattice_negLat_left (hle (hPe _ hP))
  -- both factors of positive depth
  simp only [List.length_cons] at hlen
  have h₁ : ∀ s ≤ (j₁ :: w₁').length, PropA hvt hR A s := fun s hs ↦ hA s (by simp at hs ⊢; omega)
  have h₂ : ∀ s ≤ (j₂ :: w₂').length, PropA hvt hR A s := fun s hs ↦ hA s (by simp at hs ⊢; omega)
  exact Submodule.smul_mem _ _ (TensorModule.kashiwaraE_tmul_mem hv' (isInt hvt hR Λ₁)
    (isInt hvt hR Λ₂) i (fun _ hy ↦ kashiwaraF_mem_lat Λ₁ i hy)
    (fun _ hy ↦ kashiwaraF_mem_lat Λ₂ i hy) (localE h₁ Λ₁ (degree_wordWeight _) i)
    (localE h₂ Λ₂ (degree_wordWeight _) i) hϖ hϖv
    (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A _) (fW_mem_wsp hvt hR Λ₁ _)
    (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A _) (fW_mem_wsp hvt hR Λ₂ _))

/-! ### Weights of `L(λ₁) ⊗ L(λ₂)` -/

/-- A nonzero weight vector of `L(λ₁) ⊗ L(λ₂)` has weight `λ₁ + λ₂ - ν` for some `ν`. -/
lemma exists_rootSum_of_LL {Λ₁ Λ₂ : Dom R} {μ : Y →+ ℤ} {z : TM v Λ₁ Λ₂}
    (hz : z ∈ LL hvt hR A Λ₁ Λ₂) (hzw : z ∈ weightSpace R v _ μ) (hz0 : z ≠ 0) :
    ∃ ν, μ = Λ₁.1 + Λ₂.1 - R.rootSum ν := by
  classical
  by_contra hne
  push Not at hne
  refine hz0 ?_
  have hP := TensorModule.weightSetProj_singleton_mem_of (pow_ne_one_of_transcendental' hvt)
    (isInt hvt hR Λ₁) (isInt hvt hR Λ₂)
    (fun S _ hm ↦ weightSetProj_mem_lat hvt hR A Λ₁ S hm)
    (fun S _ hm ↦ weightSetProj_mem_lat hvt hR A Λ₂ S hm) μ ⊥
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
  exact absurd (by rw [← hab, R.rootSum_add]; abel) (hne (ν₁ + ν₂))

/-- Transport along an equality of dominant weights. -/
lemma transport {ν ν' : Dom R} (h : ν.1 = ν'.1) (n : ℕ) (i : I) (w : List I)
    (hmem : ϖ ^ n • eK hvt hR ν i (fW hvt hR ν w) ∈ lat hvt hR A ν) :
    ϖ ^ n • eK hvt hR ν' i (fW hvt hR ν' w) ∈ lat hvt hR A ν' := by
  obtain ⟨a, ha⟩ := ν
  obtain ⟨b, hb⟩ := ν'
  simp only at h
  subst h
  exact hmem

section TensorMaps

variable [Finite I]

variable (hvt hR A) in
/-- `F(r)`: `Ψ_{λ₁,λ₂}((L(λ₁) ⊗ L(λ₂))_{depth r}) ⊆ L(λ₁ + λ₂)`. -/
def PropF (r : ℕ) : Prop :=
  ∀ (Λ₁ Λ₂ : Dom R) (ν : I →₀ ℕ), ν.degree = r → ∀ z ∈ LL hvt hR A Λ₁ Λ₂,
    z ∈ weightSpace R v _ (Λ₁.1 + Λ₂.1 - R.rootSum ν) →
    tensorProj hvt hR Λ₁.2 Λ₂.2 z ∈ lat hvt hR A (Λ₁ + Λ₂)

/-- `Φ(f̃_w v) = f̃_w (v ⊗ v)`. -/
lemma tensorEmb_fW (Λ₁ Λ₂ : Dom R) (w : List I) :
    tensorEmb hvt hR Λ₁.2 Λ₂.2 (fW hvt hR (Λ₁ + Λ₂) w) =
      fTw hvt hR Λ₁ Λ₂ w (TensorModule.mk _ _ (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k]
        IrreducibleModule.hwv R v Λ₂.1)) := by
  induction w with
  | nil => exact tensorEmb_hwv hvt hR Λ₁.2 Λ₂.2
  | cons i w ih =>
    rw [fW_cons, fTw_cons, ← ih]
    exact map_kashiwaraF (pow_ne_one_of_transcendental' hvt) (isInt hvt hR (Λ₁ + Λ₂)) i
      (isIntT hvt hR Λ₁ Λ₂) _ _

/-- `Ψ(f̃_w (v ⊗ v)) = f̃_w v`. -/
lemma tensorProj_fTw (Λ₁ Λ₂ : Dom R) (w : List I) :
    tensorProj hvt hR Λ₁.2 Λ₂.2 (fTw hvt hR Λ₁ Λ₂ w (TensorModule.mk _ _
      (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k] IrreducibleModule.hwv R v Λ₂.1))) =
      fW hvt hR (Λ₁ + Λ₂) w := by
  rw [← tensorEmb_fW, tensorProj_tensorEmb]

lemma tensorProj_eT (Λ₁ Λ₂ : Dom R) (i : I) (z : TM v Λ₁ Λ₂) :
    tensorProj hvt hR Λ₁.2 Λ₂.2 (eT hvt hR Λ₁ Λ₂ i z) =
      eK hvt hR (Λ₁ + Λ₂) i (tensorProj hvt hR Λ₁.2 Λ₂.2 z) :=
  map_kashiwaraE (pow_ne_one_of_transcendental' hvt) (isIntT hvt hR Λ₁ Λ₂) i
    (isInt hvt hR (Λ₁ + Λ₂)) _ z

lemma tensorEmb_eK (Λ₁ Λ₂ : Dom R) (i : I) (x : IrreducibleModule R v (Λ₁ + Λ₂).1) :
    tensorEmb hvt hR Λ₁.2 Λ₂.2 (eK hvt hR (Λ₁ + Λ₂) i x) =
      eT hvt hR Λ₁ Λ₂ i (tensorEmb hvt hR Λ₁.2 Λ₂.2 x) :=
  map_kashiwaraE (pow_ne_one_of_transcendental' hvt) (isInt hvt hR (Λ₁ + Λ₂)) i
    (isIntT hvt hR Λ₁ Λ₂) _ x

end TensorMaps

/-! ### The two steps of [HK] Lemma 5.3.8 -/

section Steps

variable [Finite I] [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹) (hinj : Function.Injective (algebraMap A k))
include hϖ hϖv hinj

/-- **First step** ([HK] Lemma 5.3.8 (1)): for `λ₂ = Λ_j` fundamental and a word `u j i'` of length
`n + 2`, if `ẽ L(·)_{depth n+2} ⊆ ϖ^{-(N+1)} L(·)` holds for `λ₁` and `λ₂`, then
`ẽᵢ f̃_{u j i'} v_{λ₁+λ₂} ∈ ϖ^{-N} L(λ₁ + λ₂)`. -/
theorem step₁ {n N : ℕ} (hA : ∀ s < n + 2, PropA hvt hR A s)
    (hB : ∀ s < n + 2, PropB hvt hR A ϖ s) (hC : ∀ s < n + 2, PropC hvt hR A ϖ s)
    (hF : PropF hvt hR A (n + 1)) {Λ₁ Λ₂ : Dom R} {j : I}
    (hj : ∀ i, Λ₂.1 (R.coroot i) = if i = j then 1 else 0)
    (hP₁ : PropAN hvt hR A ϖ (n + 2) (N + 1) Λ₁) (hP₂ : PropAN hvt hR A ϖ (n + 2) (N + 1) Λ₂)
    (u : List I) (hu : u.length = n) (i' i : I) :
    ϖ ^ N • eK hvt hR (Λ₁ + Λ₂) i (fW hvt hR (Λ₁ + Λ₂) (u ++ [j, i'])) ∈
      lat hvt hR A (Λ₁ + Λ₂) := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  set w := u ++ [j, i']
  have hwlen : w.length = n + 2 := by simp [w, hu]
  obtain ⟨w₁, w₂, h1, h2, h3, h5, h4⟩ := fTw_fund hϖ hϖv hinj hj u i' (by rwa [hu])
    (by rwa [hu]) (by rwa [hu])
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
  obtain ⟨z₀, hz₀, hz₀w, he⟩ := TensorModule.exists_smul_weight hϖ0 h4 (sub_mem hWw hmw)
  have hdeg : (LusztigF.wordWeight w).degree = n + 2 := by rw [degree_wordWeight, hwlen]
  -- `ϖ^N ẽᵢ W ∈ L ⊗ L`
  have hA₁ : ∀ s ≤ w₁.length, PropA hvt hR A s := fun s hs ↦ hA s (by omega)
  have hA₂ : ∀ s ≤ w₂.length, PropA hvt hR A s := fun s hs ↦ hA s (by omega)
  have hm := TensorModule.kashiwaraE_tmul_mem (pow_ne_one_of_transcendental' hvt)
    (isInt hvt hR Λ₁) (isInt hvt hR Λ₂) i (fun _ hy ↦ kashiwaraF_mem_lat Λ₁ i hy)
    (fun _ hy ↦ kashiwaraF_mem_lat Λ₂ i hy) (localE hA₁ Λ₁ (degree_wordWeight w₁) i)
    (localE hA₂ Λ₂ (degree_wordWeight w₂) i) hϖ hϖv
    (IrreducibleModule.fWord_mem_lattice hR _ Λ₁.2 A w₁) (fW_mem_wsp hvt hR Λ₁ w₁)
    (IrreducibleModule.fWord_mem_lattice hR _ Λ₂.2 A w₂) (fW_mem_wsp hvt hR Λ₂ w₂)
  have hz := eT_smul_mem_LL hϖ hϖv (fun s hs ↦ hA s hs) hP₁ hP₂ i hdeg hz₀ hz₀w
  have hWL : ϖ ^ N • eT hvt hR Λ₁ Λ₂ i W ∈ LL hvt hR A Λ₁ Λ₂ := by
    have hWe : W = TensorModule.mk _ _ (fW hvt hR Λ₁ w₁ ⊗ₜ[k] fW hvt hR Λ₂ w₂) + ϖ • z₀ := by
      rw [← he, add_sub_cancel]
    rw [hWe, map_add, LinearMap.map_smul_of_tower, smul_add, smul_smul, ← pow_succ]
    exact add_mem (Submodule.smul_mem _ _ hm) hz
  -- apply `Ψ` and `F(n+1)`
  have hΨ : tensorProj hvt hR Λ₁.2 Λ₂.2 (ϖ ^ N • eT hvt hR Λ₁ Λ₂ i W) =
      ϖ ^ N • eK hvt hR (Λ₁ + Λ₂) i (fW hvt hR (Λ₁ + Λ₂) w) := by
    rw [← algebraMap_smul k (ϖ ^ N) (eT hvt hR Λ₁ Λ₂ i W), LinearMap.map_smul_of_tower,
      tensorProj_eT, tensorProj_fTw, algebraMap_smul]
  rw [← hΨ]
  by_cases h0 : ϖ ^ N • eT hvt hR Λ₁ Λ₂ i W = 0
  · rw [h0, map_zero]; exact zero_mem _
  have hew := Submodule.smul_mem (weightSpace R v (TM v Λ₁ Λ₂) _) ((algebraMap A k ϖ) ^ N)
    (kashiwaraE_mem_weightSpace (pow_ne_one_of_transcendental' hvt) (isIntT hvt hR Λ₁ Λ₂) i hWw)
  rw [← map_pow, algebraMap_smul] at hew
  obtain ⟨ν', hν'⟩ := exists_rootSum_of_LL hWL hew h0
  have hν : LusztigF.wordWeight w = ν' + Finsupp.single i 1 := by
    refine LusztigCartanDatum.RootDatum.rootSum_injective hR ?_
    rw [R.rootSum_add, R.rootSum_single, one_nsmul]
    calc R.rootSum (LusztigF.wordWeight w)
        = Λ₁.1 + Λ₂.1 - (Λ₁.1 + Λ₂.1 - R.rootSum (LusztigF.wordWeight w) + R.root i) +
          R.root i := by abel
      _ = Λ₁.1 + Λ₂.1 - (Λ₁.1 + Λ₂.1 - R.rootSum ν') + R.root i := by rw [hν']
      _ = R.rootSum ν' + R.root i := by abel
  have hd' : ν'.degree = n + 1 := by
    have := hdeg; rw [hν, map_add, Finsupp.degree_single] at this; omega
  exact hF Λ₁ Λ₂ ν' hd' _ hWL (hν' ▸ hew)

end Steps

/-- `ẽᵢ (v_{λ₁} ⊗ y) ≡ v_{λ₁} ⊗ ẽᵢ y` for a string decomposition of `y` with components in
`ϖ^{-n} L(λ₂)`. -/
lemma eT_hwv_tmul_sub [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖv : algebraMap A k ϖ = v⁻¹) {Λ₁ Λ₂ : Dom R} (i : I) {n M : ℕ} {μ : Y →+ ℤ}
    {ζ : ℕ → IrreducibleModule R v Λ₂.1}
    (hζw : ∀ j : ℕ, ζ j ∈ weightSpace R v _ (μ + j • R.root i)) (hζE : ∀ j, E R v i • ζ j = 0)
    (hζ2 : ∀ j : ℕ, ζ j ≠ 0 → 0 ≤ μ (R.coroot i) + j)
    (hζL : ∀ j < M, ζ j ∈ negLat (lat hvt hR A Λ₂) ϖ n) :
    eT hvt hR Λ₁ Λ₂ i (TensorModule.mk _ _ (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k]
        ∑ j ∈ range M, dFV (hvt := hvt) (hR := hR) Λ₂ i j (ζ j))) -
      TensorModule.mk _ _ (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k]
        eK hvt hR Λ₂ i (∑ j ∈ range M, dFV (hvt := hvt) (hR := hR) Λ₂ i j (ζ j))) ∈
      ϖ • TensorModule.lattice k A (lat hvt hR A Λ₁) (negLat (lat hvt hR A Λ₂) ϖ n) := by
  set hv' := pow_ne_one_of_transcendental' hvt
  rcases M with _ | M
  · simp
  rw [kashiwaraE_sum hv' (isInt hvt hR Λ₂) i hζw hζE hζ2, tmul_sum, tmul_sum, map_sum, map_sum,
    map_sum]
  have hv0 : IrreducibleModule.hwv R v Λ₁.1 ∈
      (nodeSl2 R v _ hv' (isInt hvt hR Λ₁) i).prim (Λ₁.1 (R.coroot i)).toNat :=
    ⟨by
      have := mem_nodeWt_of_mem (i := i)
        (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := v) (Λ := Λ₁.1))
      rwa [Int.toNat_of_nonneg (Λ₁.2 i)], IrreducibleModule.E_smul_hwv i⟩
  have key : ∀ t : ℕ, t < M + 1 → eT hvt hR Λ₁ Λ₂ i (TensorModule.mk _ _
      (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k] dFV (hvt := hvt) (hR := hR) Λ₂ i t (ζ t))) -
      (if t = 0 then 0 else TensorModule.mk _ _ (IrreducibleModule.hwv R v Λ₁.1 ⊗ₜ[k]
        dFV (hvt := hvt) (hR := hR) Λ₂ i (t - 1) (ζ t))) ∈
      ϖ • TensorModule.lattice k A (lat hvt hR A Λ₁) (negLat (lat hvt hR A Λ₂) ϖ n) := by
    intro t ht
    by_cases h0 : ζ t = 0
    · simp [h0]
    have hb := hζ2 t h0
    have hζp : ζ t ∈ (nodeSl2 R v _ hv' (isInt hvt hR Λ₂) i).prim
        (μ (R.coroot i) + 2 * t).toNat :=
      ⟨by rw [Int.toNat_of_nonneg (by omega)]; exact mem_nodeWt_of_mem_add_nsmul i (hζw t),
        hζE t⟩
    have h := TensorModule.kashiwaraE_piece_sub hv' (isInt hvt hR Λ₁) (isInt hvt hR Λ₂) i
      (A := A) hϖ hϖv hv0 hζp (hwv_ne_zero hR hv' Λ₁.1) h0 (Nat.zero_le _)
      (s := 0) (t := t) (by omega)
    simp only [IntegrableSl2.dF_zero, Nat.zero_le, ↓reduceIte] at h
    refine TensorModule.smul_le_smul_of_le (TensorModule.pieceLattice_le_lattice hv'
      (isInt hvt hR Λ₁) (isInt hvt hR Λ₂) i (fun _ hy ↦ kashiwaraF_mem_lat Λ₁ i hy)
      (fun _ hy ↦ kashiwaraF_mem_negLat Λ₂ i n hy)
      (IrreducibleModule.hwv_mem_lattice hR _ Λ₁.2 A) hv0 (hζL t ht) hζp) ϖ h
  have := Submodule.sum_mem _ fun t (ht : t ∈ range (M + 1)) ↦ key t (mem_range.1 ht)
  convert this using 1
  rw [sum_sub_distrib]
  congr 1
  rw [sum_range_succ']
  simp

section Step₂

variable [Finite I] [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹) (hinj : Function.Injective (algebraMap A k))
include hϖ hϖv hinj

/-- **Second step** ([HK] Lemma 5.3.8 (2), our version): if `ẽ L(·)_{depth n+2} ⊆
ϖ^{-(N+1)} L(·)` holds for `μ` and for a fundamental weight `Λ_j`, then
`ẽᵢ f̃_{u j i'} v_μ ∈ ϖ^{-N} L(μ)` for every word `u j i'` of length `n + 2`. -/
theorem step₂ {n N : ℕ} (hA : ∀ s < n + 2, PropA hvt hR A s)
    (hB : ∀ s < n + 2, PropB hvt hR A ϖ s) (hC : ∀ s < n + 2, PropC hvt hR A ϖ s)
    (hE : PropE hvt hR A (n + 1)) (hF : PropF hvt hR A (n + 1)) {μ Λj : Dom R} {j : I}
    (hj : ∀ i, Λj.1 (R.coroot i) = if i = j then 1 else 0)
    (hPμ : PropAN hvt hR A ϖ (n + 2) (N + 1) μ) (hPj : PropAN hvt hR A ϖ (n + 2) (N + 1) Λj)
    (u : List I) (hu : u.length = n) (i' i : I) :
    ϖ ^ N • eK hvt hR μ i (fW hvt hR μ (u ++ [j, i'])) ∈ lat hvt hR A μ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  set hv' := pow_ne_one_of_transcendental' hvt
  set w := u ++ [j, i']
  have hwlen : w.length = n + 2 := by simp [w, hu]
  have hdeg : (LusztigF.wordWeight w).degree = n + 2 := by rw [degree_wordWeight, hwlen]
  set y := fW hvt hR μ w
  have hyL : y ∈ lat hvt hR A μ := IrreducibleModule.fWord_mem_lattice hR _ μ.2 A w
  have hyw : y ∈ wsp μ (LusztigF.wordWeight w) := fW_mem_wsp hvt hR μ w
  by_cases hy0 : y ∈ ϖ • lat hvt hR A μ
  · obtain ⟨y₀, hy₀, hy₀w, he⟩ := TensorModule.exists_smul_weight hϖ0 hy0 hyw
    rw [he, LinearMap.map_smul_of_tower, smul_smul, ← pow_succ]
    exact hPμ.mem i hdeg hy₀ hy₀w
  -- `(a)`, `(b)`: the first step, transported to `Λ_j + μ`
  have h1 := step₁ hϖ hϖv hinj hA hB hC hF hj hPμ hPj u hu i' i
  have h2 := transport (ν := μ + Λj) (ν' := Λj + μ) (by simp [add_comm]) N i w h1
  -- `(c)`: apply `Φ_{Λ_j, μ}` and `E(n+1)`
  set vv := TensorModule.mk (IrreducibleModule R v Λj.1) (IrreducibleModule R v μ.1)
    (IrreducibleModule.hwv R v Λj.1 ⊗ₜ[k] IrreducibleModule.hwv R v μ.1)
  have hvvw : vv ∈ weightSpace R v (TM v Λj μ) (Λj.1 + μ.1 - R.rootSum 0) := by
    simpa using fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λj μ [] []
  have hWw := fTw_mem_weightSpace (hvt := hvt) (hR := hR) Λj μ w hvvw
  rw [zero_add] at hWw
  have hc : ϖ ^ N • eT hvt hR Λj μ i (fTw hvt hR Λj μ w vv) ∈ LL hvt hR A Λj μ := by
    have hΦ : tensorEmb hvt hR Λj.2 μ.2 (ϖ ^ N • eK hvt hR (Λj + μ) i (fW hvt hR (Λj + μ) w)) =
        ϖ ^ N • eT hvt hR Λj μ i (fTw hvt hR Λj μ w vv) := by
      rw [← algebraMap_smul k (ϖ ^ N), LinearMap.map_smul_of_tower, tensorEmb_eK, tensorEmb_fW,
        algebraMap_smul]
    rw [← hΦ]
    by_cases h0 : ϖ ^ N • eK hvt hR (Λj + μ) i (fW hvt hR (Λj + μ) w) = 0
    · rw [h0, map_zero]; exact zero_mem _
    have hew := Submodule.smul_mem (weightSpace R v (IrreducibleModule R v (Λj + μ).1) _)
      ((algebraMap A k ϖ) ^ N) (kashiwaraE_mem_weightSpace hv' (isInt hvt hR (Λj + μ)) i
        (fW_mem_wsp hvt hR (Λj + μ) w))
    rw [← map_pow, algebraMap_smul] at hew
    obtain ⟨ν', hν'⟩ := exists_eq_add_single hR hv' (Λj + μ) (j := 1)
      (by rwa [one_smul]) h0
    have hd' : ν'.degree = n + 1 := by
      have := hdeg; rw [hν', map_add, Finsupp.degree_single] at this; omega
    refine hE Λj μ ν' hd' _ h2 ?_
    convert hew using 2
    rw [hν', R.rootSum_add, R.rootSum_single, one_nsmul]
    abel
  -- `(d)`: replace `f̃_w (v ⊗ v)` by `v ⊗ f̃_w v`
  have hd := fTw_hwv_tmul hϖ hϖv hinj (Λ₁ := Λj) (Λ₂ := μ) w (by rwa [hwlen]) (by rwa [hwlen])
    (by rwa [hwlen]) hy0
  have hmw : TensorModule.mk _ _ (IrreducibleModule.hwv R v Λj.1 ⊗ₜ[k] y) ∈
      weightSpace R v (TM v Λj μ) (Λj.1 + μ.1 - R.rootSum (LusztigF.wordWeight w)) := by
    simpa using fW_tmul_mem_weightSpace (hvt := hvt) (hR := hR) Λj μ [] w
  obtain ⟨z₀, hz₀, hz₀w, he⟩ := TensorModule.exists_smul_weight hϖ0 hd (sub_mem hWw hmw)
  have hz := eT_smul_mem_LL hϖ hϖv (fun s hs ↦ hA s hs) hPj hPμ i hdeg hz₀ hz₀w
  have hvy : ϖ ^ N • eT hvt hR Λj μ i (TensorModule.mk _ _
      (IrreducibleModule.hwv R v Λj.1 ⊗ₜ[k] y)) ∈ LL hvt hR A Λj μ := by
    have e : TensorModule.mk _ _ (IrreducibleModule.hwv R v Λj.1 ⊗ₜ[k] y) =
        fTw hvt hR Λj μ w vv - ϖ • z₀ := by rw [← he, sub_sub_cancel]
    rw [e, map_sub, smul_sub, LinearMap.map_smul_of_tower, smul_smul, ← pow_succ]
    exact sub_mem hc hz
  -- `(e)`: `ẽᵢ (v ⊗ y) ≡ v ⊗ ẽᵢ y`
  obtain ⟨M, ζ, hζw, hζE, hζ2, hye, hζL⟩ := exists_strings_negLat hA hPμ i hdeg hyL hyw
  have he' := eT_hwv_tmul_sub (Λ₁ := Λj) hϖ hϖv i hζw hζE hζ2 hζL
  rw [← hye] at he'
  have hstep : ϖ ^ N • TensorModule.mk _ _ (IrreducibleModule.hwv R v Λj.1 ⊗ₜ[k]
      eK hvt hR μ i y) ∈ LL hvt hR A Λj μ := by
    obtain ⟨z₁, hz₁, hz₁e⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 he'
    have : ϖ ^ N • (eT hvt hR Λj μ i (TensorModule.mk _ _
        (IrreducibleModule.hwv R v Λj.1 ⊗ₜ[k] y)) - TensorModule.mk _ _
        (IrreducibleModule.hwv R v Λj.1 ⊗ₜ[k] eK hvt hR μ i y)) ∈ LL hvt hR A Λj μ := by
      rw [← hz₁e, smul_smul, ← pow_succ]
      exact lattice_negLat_right hz₁
    rw [smul_sub] at this
    simpa using sub_mem hvy this
  -- `(f)`: apply `S`
  have hS := Sh_mem hstep
  rwa [LinearMap.map_smul_of_tower, Sh_tmul, IrreducibleModule.form_hwv, one_smul] at hS

end Step₂

/-! ### `A(r)` -/

/-- `A(0)`. -/
theorem propA_zero : PropA hvt hR A 0 := by
  intro Λ ν hν i x hx hxw
  have hν0 : ν = 0 := (Finsupp.degree_eq_zero_iff ν).1 hν
  subst hν0
  obtain ⟨a, rfl⟩ := exists_eq_smul_hwv hx hxw
  rw [LinearMap.map_smul_of_tower]
  refine Submodule.smul_mem _ _ ?_
  have : eK hvt hR Λ i (IrreducibleModule.hwv R v Λ.1) = 0 :=
    IntegrableSl2.eTilde_of_primitive (pow_d_ne_zero i)
      (pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) (IrreducibleModule.E_smul_hwv i)
      (mem_nodeWt_of_mem (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := v) (Λ := Λ.1)))
  rw [this]
  exact zero_mem _

/-- `A(1)`. -/
theorem propA_one : PropA hvt hR A 1 := by
  set hv' := pow_ne_one_of_transcendental' hvt
  intro Λ ν hν i x hx hxw
  refine mem_of_fW_mem Λ ν ((lat hvt hR A Λ).comap ((eK hvt hR Λ i).restrictScalars A))
    (fun w hw ↦ ?_) hx hxw
  change eK hvt hR Λ i (fW hvt hR Λ w) ∈ lat hvt hR A Λ
  have hlen : w.length = 1 := by rw [← degree_wordWeight, hw, hν]
  obtain ⟨j, rfl⟩ : ∃ j, w = [j] := by
    rcases w with _ | ⟨j, _ | ⟨_, _⟩⟩ <;> simp at hlen; exact ⟨j, rfl⟩
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
      exact IrreducibleModule.hwv_mem_lattice hR _ Λ.2 A
    · rw [IntegrableSl2.dF_eq_zero_of_primitive (pow_d_ne_zero i) (pow_d_ne_one hv' i) hvn
        (IrreducibleModule.E_smul_hwv i) (by push_cast; omega), map_zero]
      exact zero_mem _
  · have hE : E R v i • fW hvt hR Λ [j] = 0 := by
      rw [hf, IntegrableSl2.dF_apply, smul_comm, pow_one]
      change _ • (E R v i • F R v j • IrreducibleModule.hwv R v Λ.1) = 0
      have h := E_mul_F_sub R v i j
      simp only [hij, ↓reduceIte, sub_eq_zero] at h
      rw [← mul_smul, h, mul_smul, IrreducibleModule.E_smul_hwv, smul_zero, smul_zero]
    have := IntegrableSl2.eTilde_of_primitive (pow_d_ne_zero i) (pow_d_ne_one hv' i)
      (V := nodeSl2 R v _ hv' (isInt hvt hR Λ) i) hE
      (mem_nodeWt_of_mem (fW_mem_wsp hvt hR Λ [j]))
    change eK hvt hR Λ i _ = _ at this
    rw [this]
    exact zero_mem _

/-- Every vector of `V(λ)` lies in `ϖ^{-m} L(λ)` for some `m`, if `k = A[ϖ⁻¹]`. -/
lemma exists_smul_mem_lat (hk : ∀ c : k, ∃ (m : ℕ) (a : A),
      algebraMap A k (ϖ ^ m) * c = algebraMap A k a) (Λ : Dom R)
    (x : IrreducibleModule R v Λ.1) : ∃ m : ℕ, ϖ ^ m • x ∈ lat hvt hR A Λ := by
  have hx : x ∈ Submodule.span k (lat hvt hR A Λ : Set (IrreducibleModule R v Λ.1)) := by
    rw [IrreducibleModule.span_lattice]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨m₁, h₁⟩ := ha
    obtain ⟨m₂, h₂⟩ := hb
    refine ⟨m₁ + m₂, ?_⟩
    rw [smul_add, pow_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ h₁
    · rw [mul_smul]; exact Submodule.smul_mem _ _ h₂
  | smul c a _ ha =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨m', b, hb⟩ := hk c
    refine ⟨m' + m, ?_⟩
    have : ϖ ^ (m' + m) • c • a = b • (ϖ ^ m • a) := by
      rw [← algebraMap_smul k (ϖ ^ (m' + m)), ← algebraMap_smul k b, ← algebraMap_smul k (ϖ ^ m),
        smul_smul, smul_smul, ← hb, pow_add, map_mul]
      ring_nf
    rw [this]
    exact Submodule.smul_mem _ _ hm

lemma PropAN.mono {r N N' : ℕ} {Λ : Dom R} (h : PropAN hvt hR A ϖ r N Λ) (hNN : N ≤ N') :
    PropAN hvt hR A ϖ r N' Λ := fun i w hw ↦ by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNN
  rw [pow_add, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ (h i w hw)

lemma exists_propAN [Finite I] (hk : ∀ c : k, ∃ (m : ℕ) (a : A),
      algebraMap A k (ϖ ^ m) * c = algebraMap A k a) (r : ℕ) (Λ : Dom R) :
    ∃ N, PropAN hvt hR A ϖ r N Λ := by
  classical
  have := Fintype.ofFinite I
  have hfin := List.finite_length_eq I r
  choose m hm using fun (p : I × List I) ↦
    exists_smul_mem_lat (hvt := hvt) (hR := hR) hk Λ (eK hvt hR Λ p.1 (fW hvt hR Λ p.2))
  refine ⟨(Finset.univ ×ˢ hfin.toFinset).sup m, fun i w hw ↦ ?_⟩
  have hle : m (i, w) ≤ (Finset.univ ×ˢ hfin.toFinset).sup m :=
    Finset.le_sup (f := m) (by simp [hw])
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, pow_add, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ (hm (i, w))

/-- **`A(r)`** for `r ≥ 2` ([HK] Prop. 5.3.9), given `A`, `B`, `C` below `r`, `E(r-1)`, `F(r-1)`,
fundamental weights, and `k = A[ϖ⁻¹]`. -/
theorem propA_add_two [Finite I] [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖv : algebraMap A k ϖ = v⁻¹) (hinj : Function.Injective (algebraMap A k))
    (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
    (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0) {n : ℕ}
    (hA : ∀ s < n + 2, PropA hvt hR A s) (hB : ∀ s < n + 2, PropB hvt hR A ϖ s)
    (hC : ∀ s < n + 2, PropC hvt hR A ϖ s) (hE : PropE hvt hR A (n + 1))
    (hF : PropF hvt hR A (n + 1)) : PropA hvt hR A (n + 2) := by
  classical
  have := Fintype.ofFinite I
  choose Λf hΛf using hfund
  intro μ ν hν i x hx hxw
  let Q : ℕ → Prop := fun N ↦ PropAN hvt hR A ϖ (n + 2) N μ ∧
    ∀ j, PropAN hvt hR A ϖ (n + 2) N (Λf j)
  have hstep : ∀ N, Q (N + 1) → Q N := by
    intro N hQ
    have key : ∀ ρ : Dom R, PropAN hvt hR A ϖ (n + 2) (N + 1) ρ →
        PropAN hvt hR A ϖ (n + 2) N ρ := by
      intro ρ hρ i w hw
      obtain ⟨u, a, b, rfl⟩ : ∃ u a b, w = u ++ [a, b] := by
        have hl : (w.drop n).length = 2 := by simp; omega
        obtain ⟨a, b, hab⟩ : ∃ a b, w.drop n = [a, b] := by
          match w.drop n, hl with
          | [a, b], _ => exact ⟨a, b, rfl⟩
        exact ⟨w.take n, a, b, by rw [← hab, List.take_append_drop]⟩
      exact step₂ hϖ hϖv hinj hA hB hC hE hF (hΛf a) hρ (hQ.2 a) u
        (by simp at hw; omega) b i
    exact ⟨key μ hQ.1, fun j ↦ key _ (hQ.2 j)⟩
  obtain ⟨N₀, hN₀⟩ := exists_propAN (hvt := hvt) (hR := hR) hk (n + 2) μ
  choose Nf hNf using fun j ↦ exists_propAN (hvt := hvt) (hR := hR) (ϖ := ϖ) hk (n + 2) (Λf j)
  set N₁ := max N₀ (Finset.univ.sup Nf)
  have hQ₁ : Q N₁ := ⟨hN₀.mono (le_max_left _ _), fun j ↦ (hNf j).mono
    ((Finset.le_sup (f := Nf) (Finset.mem_univ j)).trans (le_max_right _ _))⟩
  have hQ0 : Q 0 := by
    have : ∀ m N, N + m = N₁ → Q N := by
      intro m
      induction m with
      | zero => intro N h; simpa [← h] using hQ₁
      | succ m ih => intro N h; exact hstep N (ih (N + 1) (by omega))
    exact this N₁ 0 (by simp)
  simpa using hQ0.1.mem i hν hx hxw

end GrandLoop

end LieLean.QuantumGroup

end
