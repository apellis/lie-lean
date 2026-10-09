/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Existence

/-!
# Uniqueness of crystal bases of `V(λ)`

Suppose `(L, B)` is a crystal base of `V(λ) = L_q(λ)` with `L_λ = A v_λ` and `v_λ + ϖ L ∈ B`. Then
`L = L(λ)` (`GrandLoop.eq_lat_of_isCrystalLattice`, [HK] Lemma 5.2.2 (2)) and `B = B(λ)`
(`GrandLoop.eq_base_of_isCrystalBase`), so the crystal base of `V(λ)` is unique up to the choice of
the highest weight vector ([HK] Lemma 5.2.3). The argument for `B` differs from [HK]: instead of
counting dimensions we use that `B(λ) ⊆ B` spans `L(λ)/ϖ L(λ)`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.2.
-/

open Finset Pointwise LusztigF TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

omit [CharZero k] in
/-- Every vector of an integrable module is the sum of finitely many of its weight components. -/
lemma exists_finset_eq_sum_weightSetProj {M : Type*} [AddCommGroup M] [Module k M]
    [Module (QuantumGroup R v) M] [IsScalarTower k (QuantumGroup R v) M]
    (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsIntegrable R v M) (x : M) :
    ∃ s : Finset (Y →+ ℤ), x = ∑ μ ∈ s, weightSetProj hv hM {μ} x := by
  classical
  have hx : x ∈ ⨆ μ, weightSpace R v M μ := by rw [hM.iSup_weightSpace_eq_top]; trivial
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  refine ⟨s, ?_⟩
  have hsum : weightSetProj hv hM (s : Set (Y →+ ℤ)) =
      ∑ μ ∈ s, weightSetProj hv hM {μ} := by
    refine ext_weightSpace hM fun ν m hm ↦ ?_
    rw [LinearMap.sum_apply, weightSetProj_of_mem hv hM _ hm]
    simp only [weightSetProj_of_mem hv hM _ hm, Set.mem_singleton_iff, Finset.mem_coe]
    rw [Finset.sum_ite_eq]
  have hid : ∀ y ∈ ⨆ μ ∈ s, weightSpace R v M μ, weightSetProj hv hM (s : Set (Y →+ ℤ)) y = y := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem μ y hy =>
      induction hy using Submodule.iSup_induction' with
      | mem hμ y hy =>
        rw [weightSetProj_of_mem hv hM _ hy]
        simp [hμ]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, ha, hb]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb]
  conv_lhs => rw [← hid x hs]
  rw [hsum, LinearMap.sum_apply]

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

/-- **[HK] Lemma 5.2.2 (2)**: a crystal lattice `L` of `V(λ)` with `L_λ = A v_λ` is `L(λ)`. -/
theorem eq_lat_of_isCrystalLattice (Λ : Dom R) {L : Submodule A (IrreducibleModule R v Λ.1)}
    (hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) L)
    (hvL : IrreducibleModule.hwv R v Λ.1 ∈ L)
    (hLtop : ∀ x ∈ L, x ∈ wsp Λ 0 → ∃ a : A, x = a • IrreducibleModule.hwv R v Λ.1) :
    L = lat hvt hR A Λ := by
  have hv' := pow_ne_one_of_transcendental' hvt
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · -- weight vectors of `L` lie in `L(λ)`, by induction on the depth
    have key : ∀ r (ν : I →₀ ℕ), ν.degree = r → ∀ x ∈ L, x ∈ wsp Λ ν → x ∈ lat hvt hR A Λ := by
      intro r
      induction r with
      | zero =>
        intro ν hν x hx hxw
        have hν0 : ν = 0 := by
          ext i
          have : ν i ≤ ν.degree := by
            rw [Finsupp.degree]
            by_cases hi : i ∈ ν.support
            · exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi
            · rw [Finsupp.notMem_support_iff.1 hi]; exact Nat.zero_le _
          simp; omega
        subst hν0
        obtain ⟨a, rfl⟩ := hLtop x hx hxw
        exact Submodule.smul_mem _ a (IrreducibleModule.hwv_mem_lattice hR hv' Λ.2 A)
      | succ r ih =>
        intro ν hν x hx hxw
        refine mem_lat_of_eK hϖv hk (fun s _ ↦ (hall s).1) (hall (r + 1)).2.1
          (hall (r + 1)).2.2.1 (hall r).2.2.2.1 hν hxw fun i ↦ ?_
        by_cases h0 : eK hvt hR Λ i x = 0
        · rw [h0]; exact zero_mem _
        have hew := kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ) i hxw
        obtain ⟨ν', hν'⟩ := exists_eq_add_single hR hv' Λ (i := i) (j := 1) (ν := ν)
          (by rw [one_smul]; exact hew) h0
        refine ih ν' (by have := hν; rw [hν', map_add, Finsupp.degree_single] at this; omega)
          _ (hL.kashiwaraE_mem i x hx) ?_
        convert hew using 2
        rw [hν', R.rootSum_add, R.rootSum_single, one_nsmul]; abel
    obtain ⟨s, hs⟩ := exists_finset_eq_sum_weightSetProj hv' (isInt hvt hR Λ) x
    rw [hs]
    refine Submodule.sum_mem _ fun μ _ ↦ ?_
    set y := weightSetProj hv' (isInt hvt hR Λ) {μ} x
    have hyL : y ∈ L := hL.weightSetProj_mem {μ} x hx
    have hyw : y ∈ weightSpace R v _ μ := weightSetProj_singleton_mem hv' (isInt hvt hR Λ) μ x
    by_cases hy0 : y = 0
    · rw [hy0]; exact zero_mem _
    obtain ⟨ν, rfl⟩ := IrreducibleModule.exists_eq_sub_rootSum hv' hyw hy0
    exact key _ ν rfl y hyL hyw
  · -- `L(λ) ⊆ L`
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      induction w with
      | nil => exact hvL
      | cons i w ih => exact hL.kashiwaraF_mem i _ ih
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul c a _ ha => exact Submodule.smul_mem _ c ha

/-- **Uniqueness of `B(λ)`** ([HK] Lemma 5.2.3): a crystal base `(L(λ), B)` of `V(λ)` with
`v_λ + ϖ L(λ) ∈ B` has `B = B(λ)`. -/
theorem eq_base_of_isCrystalBase (Λ : Dom R)
    (hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) (lat hvt hR A Λ))
    {B : Set (QL (hvt := hvt) (hR := hR) (A := A) (ϖ := ϖ) Λ)} (hB : IsCrystalBase hL ϖ B)
    (hvB : (Submodule.Quotient.mk (fwL hvt hR A Λ []) : QL (ϖ := ϖ) Λ) ∈ B) :
    B = IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ := by
  have hϖu : ¬IsUnit ϖ := (IsLocalRing.mem_maximalIdeal ϖ).1 hϖ
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  -- `B(λ) ⊆ B`
  have key : ∀ w, fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ →
      (Submodule.Quotient.mk (fwL hvt hR A Λ w) : QL (ϖ := ϖ) Λ) ∈ B := by
    intro w
    induction w with
    | nil => exact fun _ ↦ hvB
    | cons i w ih =>
      intro hw0
      have hw0' : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ := fun h ↦
        hw0 (kashiwaraF_mem_smul_lat Λ i h)
      rcases hB.fQ_mem i _ (ih hw0') with h | h
      · exact h
      · exact absurd ((IntegrableSl2.mk_eq_zero_iff ϖ _).1 h) hw0
  have hsub : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ ⊆ B := by
    intro b hb
    obtain ⟨w, hbw, hw0⟩ := (mem_base_iff (hvt := hvt) (hR := hR) (A := A) (ϖ := ϖ) Λ b).1 hb
    rw [hbw]
    exact key w hw0
  refine le_antisymm (fun b hb ↦ ?_) hsub
  by_contra hb'
  have : Nontrivial (A ⧸ Ideal.span {ϖ}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hspan : b ∈ Submodule.span (A ⧸ Ideal.span {ϖ})
      (Subtype.val '' {x : B | x ≠ ⟨b, hb⟩}) := by
    have h1 : b ∈ Submodule.span (A ⧸ Ideal.span {ϖ})
        (IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ) := by
      rw [span_base (hvt := hvt) (hR := hR) (A := A) (ϖ := ϖ) Λ]; trivial
    refine Submodule.span_mono (fun x hx ↦ ?_) h1
    refine ⟨⟨x, hsub hx⟩, fun h ↦ hb' ?_, rfl⟩
    have := congrArg Subtype.val h
    simp only at this
    rw [← this]; exact hx
  exact hB.linearIndependent.notMem_span_image (s := {x : B | x ≠ ⟨b, hb⟩})
    (x := ⟨b, hb⟩) (fun h ↦ h rfl) hspan

end GrandLoop

end LieLean.QuantumGroup
