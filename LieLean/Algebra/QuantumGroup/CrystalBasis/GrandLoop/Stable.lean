/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.PropB
import LieLean.Algebra.QuantumGroup.CrystalBasis.DualLattice
import LieLean.Algebra.QuantumGroup.Faithful

/-!
# Kashiwara's grand loop: stable lattices in `U⁻`

For `λ` dominant let `ev_λ : 'f → V(λ)`, `y ↦ y⁻ v_λ`. For a weight `ν` of depth `r` let
`Λ_λ ⊆ U⁻_ν = ('f ⧸ J)_ν` be the set of `y` with `y v_λ ∈ L(λ)` (`GrandLoop.stLat`). Assuming
`A` up to depth `r - 1` and `E(r)`:

* `Fᵢ L(λ)_{λ-ν'} ⊆ ϖ^{-|ν'| dᵢ} L(λ)` (`GrandLoop.pow_smul_F_smul_mem`), hence
  `ϖ^C θ_{i₁} ⋯ θ_{iᵣ} ∈ Λ_λ` for all `λ`, with `C` independent of `λ`
  (`GrandLoop.pow_smul_mon_le_stLat`);
* `Λ_{λ' + λ} ⊆ Λ_λ` (`GrandLoop.stLat_add_le`), from `E(r)` and the map `S`;
* for `⟨i, λ⟩ ≥ r` the map `U⁻_ν → V(λ)` is injective, so `Λ_λ ⊆ ϖ^{-c} Σ A θ_{i₁} ⋯ θ_{iᵣ}`;
* hence, over a discrete valuation ring, `Λ_λ` does not depend on `λ` for `λ` large
  (`GrandLoop.exists_stLat_eq`).

This is the first step of our proof of [HK] Exercise 5.13; the argument is ours.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
-/

open Finset Pointwise LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]

/-! ### The map `y ↦ y⁻ v_λ` -/

section Ev

variable (R v) in
/-- `y ↦ y⁻ v_λ`, `'f → V(λ)`. -/
def ev (Λ : Y →+ ℤ) : LusztigF k I →ₗ[k] IrreducibleModule R v Λ :=
  ((VermaModule.maxSubmodule R v Λ).mkQ.restrictScalars k) ∘ₗ VermaModule.toVerma R v Λ

omit [NeZero v] [CharZero k] in
lemma ev_apply (Λ : Y →+ ℤ) (y : LusztigF k I) :
    ev R v Λ y = Submodule.Quotient.mk (VermaModule.toVerma R v Λ y) := rfl

omit [NeZero v] [CharZero k] in
@[simp] lemma ev_one (Λ : Y →+ ℤ) : ev R v Λ 1 = IrreducibleModule.hwv R v Λ := by
  rw [ev_apply, VermaModule.toVerma_one]

omit [NeZero v] [CharZero k] in
lemma ev_ι_mul (Λ : Y →+ ℤ) (j : I) (y : LusztigF k I) :
    ev R v Λ (FreeAlgebra.ι k j * y) = F R v j • ev R v Λ y := by
  rw [ev_apply, VermaModule.toVerma_ι_mul, Submodule.Quotient.mk_smul]; rfl

omit [NeZero v] [CharZero k] in
lemma ev_monomial_cons (Λ : Y →+ ℤ) (j : I) (w : List I) :
    ev R v Λ (monomial k (j :: w)) = F R v j • ev R v Λ (monomial k w) := by
  rw [← ev_ι_mul]; congr 1

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv'

omit [CharZero k] in
lemma ev_eq_zero_of_mem (Λ : Y →+ ℤ) {y : LusztigF k I} (hy : y ∈ serreIdeal D v) :
    ev R v Λ y = 0 := by
  rw [ev_apply, (VermaModule.toVerma_eq_zero_iff hv' y).2 hy, Submodule.Quotient.mk_zero]

omit [CharZero k] in
lemma ev_mem_weightSpace (hR : R.IsXRegular) (Λ : Y →+ ℤ) {ν : I →₀ ℕ} {y : LusztigF k I}
    (hy : y ∈ LusztigF.weightSpace k ν) :
    ev R v Λ y ∈ weightSpace R v (IrreducibleModule R v Λ) (Λ - R.rootSum ν) := by
  rw [VermaModule.weightSpace_quotient_eq_map hv' hR]
  exact ⟨y, hy, rfl⟩

omit [CharZero k] in
/-- `V(λ)_{λ-ν}` is the image of `'f_ν`. -/
lemma weightSpace_eq_map_ev (hR : R.IsXRegular) (Λ : Y →+ ℤ) (ν : I →₀ ℕ) :
    weightSpace R v (IrreducibleModule R v Λ) (Λ - R.rootSum ν) =
      (LusztigF.weightSpace k ν).map (ev R v Λ) :=
  VermaModule.weightSpace_quotient_eq_map hv' hR _ ν

omit hv' in
/-- For `⟨i, λ⟩ ≥ |ν|`, `ev_λ` is injective on `'f_ν` modulo `J`. -/
theorem mem_serreIdeal_of_ev_eq_zero [Finite I] (hvt : Transcendental ℚ v) (hR : R.IsXRegular)
    {Λ : Y →+ ℤ} (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) {ν : I →₀ ℕ}
    (hν : ∀ i, (ν.degree : ℤ) ≤ Λ (R.coroot i)) {y : LusztigF k I}
    (hy : y ∈ LusztigF.weightSpace k ν) (h : ev R v Λ y = 0) : y ∈ serreIdeal D v := by
  classical
  have hv' := pow_ne_one_of_transcendental' hvt
  rw [ev_apply, Submodule.Quotient.mk_eq_zero,
    VermaModule.maxSubmodule_eq_fPowSubmodule hvt hR hΛ] at h
  refine VermaModule.mem_serreIdeal_of_toVerma_mem_fPowSubmodule hv' hΛ (fun ν' hν' i ↦ ?_) h
  rw [weightProj_of_mem hy] at hν'
  have e : ν = ν' := by by_contra hne; exact hν' (by simp [hne])
  subst e
  have h1 : ν i ≤ ν.degree := by
    rw [Finsupp.degree]
    by_cases hi : i ∈ ν.support
    · exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi
    · rw [Finsupp.notMem_support_iff.1 hi]; exact Nat.zero_le _
  have := hν i
  omega

end Ev

/-! ### `Fᵢ` on the lattice -/

section FBound

omit [CharZero k] [DecidableEq I] in
/-- `ϖ^{j dᵢ} [j+1]_{vᵢ} ∈ A`. -/
lemma exists_qInt_mul {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}
    (hϖv : algebraMap A k ϖ = v⁻¹) (i : I) (j : ℕ) :
    ∃ a : A, algebraMap A k (ϖ ^ (j * D.d i)) * qInt (v ^ D.d i) (j + 1) = algebraMap A k a := by
  refine ⟨∑ s ∈ range (j + 1), (ϖ ^ D.d i) ^ (2 * s), ?_⟩
  have hv0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have ht : algebraMap A k ϖ ^ D.d i = (v ^ D.d i)⁻¹ := by rw [hϖv, inv_pow]
  rw [qInt, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hs : s ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [mul_comm (s + m), pow_mul, show s + m + 1 - 1 - s = m by omega]
  simp only [map_pow, ht]
  have h1 : (v ^ D.d i)⁻¹ ^ m * (v ^ D.d i) ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hv0, one_pow]
  rw [pow_add, two_mul, pow_add]
  linear_combination ((v ^ D.d i)⁻¹ ^ s * (v ^ D.d i)⁻¹ ^ s) * h1

variable {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k]

/-- **`Fᵢ L(λ) ⊆ ϖ^{-d dᵢ} L(λ)` in depth `d`**, from `A(s)` for `s ≤ d`: write
`x = Σⱼ Fᵢ^{(j)} ηⱼ` with `ηⱼ ∈ L(λ)` ([HK] Lemma 5.3.1 (1)), so
`Fᵢ x = Σⱼ [j+1]ᵢ f̃ᵢ^{j+1} ηⱼ` with `j ≤ d`. -/
theorem pow_smul_F_smul_mem {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s) {ϖ : A}
    (hϖv : algebraMap A k ϖ = v⁻¹) (Λ : Dom R) {ν : I →₀ ℕ} (hν : ν.degree = d) (i : I)
    {x : IrreducibleModule R v Λ.1} (hx : x ∈ lat hvt hR A Λ) (hxw : x ∈ wsp Λ ν) :
    ϖ ^ (d * D.d i) • (F R v i • x) ∈ lat hvt hR A Λ := by
  have hv' := pow_ne_one_of_transcendental' hvt
  have hM := isInt hvt hR Λ
  obtain ⟨N, η, h1, hE, h2, -, hsum⟩ := exists_sum_dF_weight hv' hM i hxw
  have hη : ∀ j < N, η j ∈ lat hvt hR A Λ :=
    mem_of_sum_mem_weight hv' hM i (fun y hy ↦ kashiwaraF_mem_lat Λ i hy) N _ η h1 hE h2
      (fun j y hy hyw ↦ localE hA Λ hν i j hy hyw) (hsum ▸ hx)
  rw [hsum, Finset.smul_sum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun j hj ↦ ?_
  have hj := Finset.mem_range.1 hj
  by_cases h0 : η j = 0
  · simp [h0]
  obtain ⟨ν', hν'⟩ := exists_eq_add_single hR hv' Λ (h1 j) h0
  have hjd : j ≤ d := by
    have := congrArg Finsupp.degree hν'
    rw [map_add, Finsupp.degree_single] at this
    omega
  change ϖ ^ (d * D.d i) • (nodeSl2 R v _ hv' hM i).F ((nodeSl2 R v _ hv' hM i).dF j (η j)) ∈ _
  rw [IntegrableSl2.F_dF (pow_d_ne_zero i) (pow_d_ne_one hv' i)]
  have hu := mem_nodeWt_of_mem_add_nsmul i (h1 j)
  have hy : (nodeSl2 R v _ hv' hM i).dF (j + 1) (η j) ∈ lat hvt hR A Λ := by
    rw [← kashiwaraF_pow_of_primitive hv' hM i (hE j) hu]
    exact kashiwaraF_pow_mem hv' hM i (fun y hy ↦ kashiwaraF_mem_lat Λ i hy) _ (hη j hj)
  obtain ⟨a, ha⟩ := exists_qInt_mul (A := A) hϖv i j
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hjd
  have : ϖ ^ (d * D.d i) • (qInt (v ^ D.d i) (j + 1) • (nodeSl2 R v _ hv' hM i).dF (j + 1) (η j)) =
      (ϖ ^ (e * D.d i) * a) • (nodeSl2 R v _ hv' hM i).dF (j + 1) (η j) := by
    rw [← algebraMap_smul k (ϖ ^ (d * D.d i)), smul_smul,
      ← algebraMap_smul k (ϖ ^ (e * D.d i) * a)]
    congr 1
    rw [he, add_mul, pow_add, map_mul, map_mul, ← ha]
    ring
  rw [this]
  exact Submodule.smul_mem _ _ hy

end FBound

/-! ### Monomials -/

section Monomials

/-- The exponent of `ϖ` needed to bring `θ_w v_λ` into `L(λ)`. -/
def expo : List I → ℕ
  | [] => 0
  | j :: w => expo w + w.length * D.d j

variable {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k]

omit [CharZero k] [DecidableEq I] in
lemma monomial_eq_wordBasis (w : List I) : monomial k w = FreeAlgebra.wordBasis k I w := by
  rw [FreeAlgebra.wordBasis_apply]; rfl

/-- `ϖ^{e(w)} θ_w v_λ ∈ L(λ)` for words of length `≤ n`, from `A(s)`, `s < n`. -/
theorem pow_expo_smul_ev_mem {n : ℕ} (hA : ∀ s < n, PropA hvt hR A s) {ϖ : A}
    (hϖv : algebraMap A k ϖ = v⁻¹) (Λ : Dom R) (w : List I) (hw : w.length ≤ n) :
    ϖ ^ expo (D := D) w • ev R v Λ.1 (FreeAlgebra.wordBasis k I w) ∈ lat hvt hR A Λ := by
  induction w with
  | nil =>
    simpa [expo] using
      IrreducibleModule.hwv_mem_lattice hR (pow_ne_one_of_transcendental' hvt) Λ.2 A
  | cons j w ih =>
    have hw' : w.length < n := by simp at hw; omega
    have h1 := ih hw'.le
    have hwt : ϖ ^ expo (D := D) w • ev R v Λ.1 (FreeAlgebra.wordBasis k I w) ∈
        wsp Λ (wordWeight w) := by
      refine Submodule.smul_of_tower_mem _ _ ?_
      rw [← monomial_eq_wordBasis]
      exact ev_mem_weightSpace (pow_ne_one_of_transcendental' hvt) hR Λ.1
        (monomial_mem_weightSpace w)
    have h2 := pow_smul_F_smul_mem (d := w.length) (fun s hs ↦ hA s (by omega)) hϖv Λ
      (degree_wordWeight w) j h1 hwt
    rw [← FreeAlgebra.ι_mul_wordBasis, ev_ι_mul]
    convert h2 using 1
    rw [expo, pow_add, mul_smul, ← algebraMap_smul k (ϖ ^ expo (D := D) w),
      ← algebraMap_smul k (ϖ ^ expo (D := D) w), mul_comm (w.length), smul_comm (F R v j)]
    exact smul_comm _ _ _

end Monomials

/-! ### `S ∘ Φ` on `ev` -/

section Head

variable {hvt : Transcendental ℚ v} {hR : R.IsXRegular}

/-- `S(Φ(y v_{λ₁+λ₂})) = y v_{λ₂}`. -/
lemma Sh_tensorEmb_ev [Finite I] (Λ₁ Λ₂ : Dom R) (y : LusztigF k I) :
    Sh hvt hR Λ₁ Λ₂ (tensorEmb hvt hR Λ₁.2 Λ₂.2 (ev R v (Λ₁ + Λ₂).1 y)) = ev R v Λ₂.1 y := by
  induction y using FreeAlgebra.induction_wordBasis with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add]
  | smul c a ha => rw [map_smul, LinearMap.map_smul_of_tower, map_smul, ha, map_smul]
  | word w =>
    induction w with
    | nil =>
      rw [FreeAlgebra.wordBasis_nil, ev_one, ev_one]
      erw [tensorEmb_hwv]
      rw [Sh_tmul, IrreducibleModule.form_hwv, one_smul]
    | cons j w ih =>
      rw [← FreeAlgebra.ι_mul_wordBasis, ev_ι_mul, ev_ι_mul, map_smul, Sh, tensorHead_F_smul]
      rw [Sh] at ih
      rw [ih]

end Head

/-! ### The lattices `Λ_λ` -/

section Lattice

variable (D v) in
/-- `U⁻ = 'f ⧸ J`, as a vector space. -/
abbrev Um : Type _ := LusztigF k I ⧸ serreSubmodule D v

variable (D v) in
/-- `U⁻_ν`. -/
def Uw (ν : I →₀ ℕ) : Submodule k (Um D v) :=
  (LusztigF.weightSpace k ν).map (serreSubmodule D v).mkQ

variable (hvt : Transcendental ℚ v) (hR : R.IsXRegular) (A : Type*) [CommRing A] [Algebra A k]

include hvt in
/-- `ev_λ` on `U⁻`. -/
def evq (Λ : Dom R) : Um D v →ₗ[k] IrreducibleModule R v Λ.1 :=
  (serreSubmodule D v).liftQ (ev R v Λ.1) fun _ hy ↦
    ev_eq_zero_of_mem (pow_ne_one_of_transcendental' hvt) Λ.1 (mem_serreSubmodule.1 hy)

@[simp] lemma evq_mk (Λ : Dom R) (y : LusztigF k I) :
    evq hvt Λ (Submodule.Quotient.mk y) = ev R v Λ.1 y := rfl

/-- `Λ_λ = {y ∈ U⁻_ν | y v_λ ∈ L(λ)}`. -/
def stLat (Λ : Dom R) (ν : I →₀ ℕ) : Submodule A (Uw D v ν) :=
  (lat hvt hR A Λ).comap (((evq hvt Λ).comp (Uw D v ν).subtype).restrictScalars A)

lemma mem_stLat {Λ : Dom R} {ν : I →₀ ℕ} {x : Uw D v ν} :
    x ∈ stLat hvt hR A Λ ν ↔ evq hvt Λ x ∈ lat hvt hR A Λ := Iff.rfl

omit [CharZero k] [NeZero v] [DecidableEq I] in
lemma mk_mem_Uw {ν : I →₀ ℕ} {y : LusztigF k I} (hy : y ∈ LusztigF.weightSpace k ν) :
    (Submodule.Quotient.mk y : Um D v) ∈ Uw D v ν := ⟨y, hy, rfl⟩

omit [CharZero k] [NeZero v] [DecidableEq I] in
lemma wordBasis_mem_weightSpace {ν : I →₀ ℕ} {w : List I} (hw : wordWeight w = ν) :
    FreeAlgebra.wordBasis k I w ∈ LusztigF.weightSpace k ν := by
  rw [← monomial_eq_wordBasis, ← hw]; exact monomial_mem_weightSpace w

variable (D v) in
/-- The class of `θ_w` in `U⁻_ν`. -/
def monVec (ν : I →₀ ℕ) (w : {w : List I // wordWeight w = ν}) : Uw D v ν :=
  ⟨Submodule.Quotient.mk (FreeAlgebra.wordBasis k I w.1), mk_mem_Uw (wordBasis_mem_weightSpace w.2)⟩

variable (D v) in
/-- `Σ A θ_w` in `U⁻_ν`. -/
def mon (ν : I →₀ ℕ) : Submodule A (Uw D v ν) := Submodule.span A (Set.range (monVec D v ν))

omit [CharZero k] [NeZero v] [DecidableEq I] in
lemma finite_words [Finite I] (ν : I →₀ ℕ) : {w : List I | wordWeight w = ν}.Finite :=
  (List.finite_length_eq I ν.degree).subset fun w (hw : wordWeight w = ν) ↦
    show w.length = ν.degree by rw [← hw, degree_wordWeight]

omit [CharZero k] [NeZero v] [DecidableEq I] in
lemma mon_fg [Finite I] (ν : I →₀ ℕ) : (mon D v A ν).FG := by
  have : Finite {w : List I // wordWeight w = ν} := (finite_words ν).to_subtype
  exact Submodule.fg_span (Set.finite_range _)

omit [CharZero k] [NeZero v] [DecidableEq I] in
/-- The `θ_w` span `U⁻_ν`. -/
lemma span_monVec (ν : I →₀ ℕ) : Submodule.span k (Set.range (monVec D v ν)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  obtain ⟨_, ⟨y, hy, rfl⟩⟩ := x
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    refine Submodule.subset_span ⟨⟨w, hw⟩, ?_⟩
    simp [monVec, monomial_eq_wordBasis]
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

omit [CharZero k] [NeZero v] [DecidableEq I] in
lemma span_mon (ν : I →₀ ℕ) :
    Submodule.span k (mon D v A ν : Set (Uw D v ν)) = ⊤ := by
  rw [mon, Submodule.span_span_of_tower, span_monVec]

variable {hvt hR A}

/-- **Lower bound**: `ϖ^C Σ A θ_w ⊆ Λ_λ` for all `λ`, with `C` independent of `λ`. -/
theorem exists_pow_smul_mon_le [Finite I] {ϖ : A} (hϖv : algebraMap A k ϖ = v⁻¹) {ν : I →₀ ℕ}
    (hA : ∀ s < ν.degree, PropA hvt hR A s) :
    ∃ C : ℕ, ∀ Λ : Dom R, ∀ x ∈ mon D v A ν, ϖ ^ C • x ∈ stLat hvt hR A Λ ν := by
  obtain ⟨C, hC⟩ := ((finite_words ν).image (expo (D := D))).bddAbove
  refine ⟨C, fun Λ x hx ↦ ?_⟩
  have hle : mon D v A ν ≤ (stLat hvt hR A Λ ν).comap ((ϖ ^ C) • LinearMap.id) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    have h1 : expo (D := D) w.1 ≤ C := hC ⟨w.1, w.2, rfl⟩
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le h1
    change ϖ ^ C • monVec D v ν w ∈ stLat hvt hR A Λ ν
    rw [mem_stLat, Submodule.coe_smul_of_tower, LinearMap.map_smul_of_tower]
    change ϖ ^ C • ev R v Λ.1 _ ∈ _
    rw [he, add_comm, pow_add, mul_smul]
    refine Submodule.smul_mem _ _ (pow_expo_smul_ev_mem hA hϖv Λ w.1 ?_)
    rw [← degree_wordWeight, w.2]
  exact hle hx

/-- **`Λ_{λ₁+λ₂} ⊆ Λ_{λ₂}`**, from `E(r)` and `S`. -/
theorem stLat_add_le [Finite I] {ν : I →₀ ℕ} (hE : PropE hvt hR A ν.degree) (Λ₁ Λ₂ : Dom R) :
    stLat hvt hR A (Λ₁ + Λ₂) ν ≤ stLat hvt hR A Λ₂ ν := by
  rintro ⟨_, y, hy, rfl⟩ hx
  rw [mem_stLat] at hx ⊢
  change ev R v (Λ₁ + Λ₂).1 y ∈ _ at hx
  change ev R v Λ₂.1 y ∈ _
  have h1 := hE Λ₁ Λ₂ ν rfl _ hx
    (ev_mem_weightSpace (pow_ne_one_of_transcendental' hvt) hR _ hy)
  have h2 := Sh_mem h1
  rwa [Sh_tensorEmb_ev] at h2

include hR in
/-- For `⟨i, λ⟩ ≥ |ν|`, `U⁻_ν → V(λ)` is injective. -/
lemma evq_injective [Finite I] {Λ : Dom R} {ν : I →₀ ℕ}
    (hΛ : ∀ i, (ν.degree : ℤ) ≤ Λ.1 (R.coroot i)) :
    Function.Injective ((evq hvt Λ).comp (Uw D v ν).subtype) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨_, y, hy, rfl⟩ h
  have := mem_serreIdeal_of_ev_eq_zero hvt hR Λ.2 hΛ hy h
  exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 (mem_serreSubmodule.2 this))

variable {ϖ : A}
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
include hk

/-- **Upper bound**: for `⟨i, λ⟩ ≥ |ν|`, `Λ_λ ⊆ ϖ^{-c} Σ A θ_w`. -/
theorem exists_pow_smul_mem_mon [Finite I] {Λ : Dom R} {ν : I →₀ ℕ}
    (hΛ : ∀ i, (ν.degree : ℤ) ≤ Λ.1 (R.coroot i)) :
    ∃ c : ℕ, ∀ x ∈ stLat hvt hR A Λ ν, ϖ ^ c • x ∈ mon D v A ν := by
  classical
  have hv' := pow_ne_one_of_transcendental' hvt
  set T := (evq hvt Λ).comp (Uw D v ν).subtype
  have hpre : ∀ w : List I, wordWeight w = ν → ∃ x : Uw D v ν, T x = fW hvt hR Λ w := by
    intro w hw
    have := fW_mem_wsp hvt hR Λ w
    rw [hw, wsp, weightSpace_eq_map_ev hv' hR] at this
    obtain ⟨y, hy, e⟩ := this
    exact ⟨⟨_, mk_mem_Uw hy⟩, e⟩
  choose! xw hxw using hpre
  have hm : ∀ w : List I, wordWeight w = ν → ∃ m : ℕ, ϖ ^ m • xw w ∈ mon D v A ν :=
    fun w _ ↦ DualLattice.exists_pow_smul_mem hk (Λ := mon D v A ν) (by rw [span_mon]; trivial)
  choose! m hm using hm
  obtain ⟨c, hc⟩ := ((finite_words ν).image m).bddAbove
  refine ⟨c, fun x hx ↦ ?_⟩
  set N : Submodule A (IrreducibleModule R v Λ.1) :=
    ((mon D v A ν).comap ((ϖ ^ c) • LinearMap.id)).map (T.restrictScalars A)
  have hxw' : T x ∈ wsp Λ ν := by
    obtain ⟨_, y, hy, rfl⟩ := x
    exact ev_mem_weightSpace hv' hR Λ.1 hy
  have hN : T x ∈ N := by
    refine mem_of_fW_mem Λ ν N (fun w hw ↦ ⟨xw w, ?_, hxw w hw⟩) hx hxw'
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (hc ⟨w, hw, rfl⟩ : m w ≤ c)
    change ϖ ^ c • xw w ∈ mon D v A ν
    rw [he, add_comm, pow_add, mul_smul]
    exact Submodule.smul_mem _ _ (hm w hw)
  obtain ⟨x', hx', e⟩ := hN
  rw [← evq_injective (hR := hR) hΛ e]
  exact hx'

/-- `Λ_λ` is finitely generated for `⟨i, λ⟩ ≥ |ν|`. -/
lemma stLat_fg [Finite I] [IsNoetherianRing A] (hϖ0 : algebraMap A k ϖ ≠ 0) {Λ : Dom R}
    {ν : I →₀ ℕ} (hΛ : ∀ i, (ν.degree : ℤ) ≤ Λ.1 (R.coroot i)) :
    (stLat hvt hR A Λ ν).FG := by
  obtain ⟨c, hc⟩ := exists_pow_smul_mem_mon (hvt := hvt) (hR := hR) hk hΛ
  have hinj : Function.Injective ((ϖ ^ c) • LinearMap.id : Uw D v ν →ₗ[A] Uw D v ν) := by
    intro x y h
    have h' : algebraMap A k (ϖ ^ c) • (x : Um D v) = algebraMap A k (ϖ ^ c) • (y : Um D v) := by
      rw [algebraMap_smul, algebraMap_smul]
      exact congrArg Subtype.val h
    exact Subtype.ext (smul_right_injective _ (by rw [map_pow]; exact pow_ne_zero _ hϖ0) h')
  refine Submodule.fg_of_fg_map_injective _ hinj ((mon_fg A ν).of_le ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact hc x hx

/-- **Stabilization**: over a discrete valuation ring, `Λ_λ` does not depend on `λ` for `λ`
large. -/
theorem exists_stLat_eq [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
    (hϖv : algebraMap A k ϖ = v⁻¹) {ν : I →₀ ℕ} (hA : ∀ s < ν.degree, PropA hvt hR A s)
    (hE : PropE hvt hR A ν.degree) (ρ : Dom R) (hρ : ∀ i, 1 ≤ ρ.1 (R.coroot i)) :
    ∃ Λ₁ : Dom R, (∀ i, (ν.degree : ℤ) ≤ Λ₁.1 (R.coroot i)) ∧
      ∀ Λ : Dom R, stLat hvt hR A (Λ + Λ₁) ν = stLat hvt hR A Λ₁ ν := by
  classical
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hϖ : ϖ ≠ 0 := fun h ↦ hϖ0 (by rw [h, map_zero])
  let nsm : ℕ → Dom R := fun n ↦
    ⟨n • ρ.1, fun i ↦ by rw [AddMonoidHom.nsmul_apply]; exact nsmul_nonneg (ρ.2 i) n⟩
  have hnsm : ∀ n, nsm (n + 1) = ρ + nsm n := fun n ↦ Subtype.ext (succ_nsmul' ρ.1 n)
  have hbig : ∀ n, ν.degree ≤ n → ∀ i, (ν.degree : ℤ) ≤ (nsm n).1 (R.coroot i) := by
    intro n hn i
    change (ν.degree : ℤ) ≤ (n • ρ.1) (R.coroot i)
    rw [AddMonoidHom.nsmul_apply, nsmul_eq_mul]
    have h1 := hρ i
    have h2 : (ν.degree : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  set r := ν.degree
  set s : ℕ → Submodule A (Uw D v ν) := fun n ↦ stLat hvt hR A (nsm (r + n)) ν
  have hs : Antitone s := antitone_nat_of_succ_le fun n ↦ by
    change stLat hvt hR A (nsm (r + n + 1)) ν ≤ stLat hvt hR A (nsm (r + n)) ν
    rw [hnsm]
    exact stLat_add_le hE ρ _
  obtain ⟨C, hC⟩ := exists_pow_smul_mon_le hϖv hA
  obtain ⟨c, hc⟩ := exists_pow_smul_mem_mon (hvt := hvt) (hR := hR) hk (hbig r le_rfl)
  obtain ⟨n₀, hn₀⟩ := DualLattice.exists_stable hϖ s hs
    (L₀ := (mon D v A ν).map ((ϖ ^ C) • LinearMap.id))
    (fun n ↦ by rintro _ ⟨x, hx, rfl⟩; exact hC _ x hx)
    (stLat_fg hk hϖ0 (hbig r le_rfl)) (N := C + c)
    (fun x hx ↦ ⟨ϖ ^ c • x, hc x hx, by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← pow_add]⟩)
  refine ⟨nsm (r + n₀), hbig _ (by omega), fun Λ ↦ le_antisymm (stLat_add_le hE Λ _) ?_⟩
  obtain ⟨M, hM⟩ := (Set.finite_range fun i ↦ (Λ.1 (R.coroot i)).toNat).bddAbove
  have hM' : ∀ i, Λ.1 (R.coroot i) ≤ M := fun i ↦ by
    have h1 : (Λ.1 (R.coroot i)).toNat ≤ M := hM ⟨i, rfl⟩
    have h2 := Int.self_le_toNat (Λ.1 (R.coroot i))
    omega
  let Λ' : Dom R := ⟨M • ρ.1 - Λ.1, fun i ↦ by
    rw [AddMonoidHom.sub_apply, AddMonoidHom.nsmul_apply, nsmul_eq_mul]
    have h1 := hρ i
    have h2 := hM' i
    nlinarith⟩
  have e : Λ' + (Λ + nsm (r + n₀)) = nsm (r + (n₀ + M)) := by
    refine Subtype.ext ?_
    change M • ρ.1 - Λ.1 + (Λ.1 + (r + n₀) • ρ.1) = (r + (n₀ + M)) • ρ.1
    simp only [add_nsmul]
    abel
  calc stLat hvt hR A (nsm (r + n₀)) ν = s (n₀ + M) := (hn₀ _ (by omega)).symm
    _ = stLat hvt hR A (Λ' + (Λ + nsm (r + n₀))) ν := by rw [e]
    _ ≤ stLat hvt hR A (Λ + nsm (r + n₀)) ν := stLat_add_le hE _ _

end Lattice

end GrandLoop

end LieLean.QuantumGroup
