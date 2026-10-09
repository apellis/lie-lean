/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Stable
import LieLean.Algebra.QuantumGroup.ShapovalovLimit

/-!
# Kashiwara's grand loop: stable dual lattices in `U⁻`

On `U⁻_ν = ('f ⧸ J)_ν` we have the forms `G_λ(x, y) = (x v_λ, y v_λ)` (the Shapovalov form of
`M_q(λ)`, `GrandLoop.gF`) and Lusztig's form `G_0 = ( , )` (`GrandLoop.g0`), which is
nondegenerate on `U⁻_ν` by quantum Gabber–Kac (`GrandLoop.nondegenerate_g0`). Since
`G_λ ≡ G_0` modulo `ϖ^m` on a fixed lattice once `⟨i, λ⟩ ≥ m`
(`VermaModule.exists_shapZ_sub_mem`), and the lattices `Λ_λ = {y | y v_λ ∈ L(λ)}` stabilize
(`GrandLoop.exists_stLat_eq`), the dual lattices of `Λ_λ` for `G_λ` stabilize too: for `λ`
large, `Λ_λ^∨` (for `G_λ`) is the dual of the stable lattice for `G_0`
(`GrandLoop.exists_dual_stLat_eq`). This is our proof of [HK] Exercise 5.13, which [HK] use in
Lemma 5.3.15.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
-/

open Finset Pointwise LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]

/-! ### Forms on `U⁻` -/

section Forms

variable (D v) in
/-- A bilinear form on `'f` vanishing on `J` (on both sides), as a form on `U⁻ = 'f ⧸ J`. -/
def formQ (B : LinearMap.BilinForm k (LusztigF k I))
    (h1 : ∀ x ∈ serreSubmodule D v, ∀ y, B x y = 0)
    (h2 : ∀ x, ∀ y ∈ serreSubmodule D v, B x y = 0) : LinearMap.BilinForm k (Um D v) :=
  (serreSubmodule D v).liftQ
    ((serreSubmodule D v).liftQ B.flip fun y hy ↦ LinearMap.ext fun x ↦ h2 x y hy).flip
    fun x hx ↦ LinearMap.ext fun y ↦ by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact h1 x hx y

omit [NeZero v] [CharZero k] [DecidableEq I] in
@[simp] lemma formQ_mk (B : LinearMap.BilinForm k (LusztigF k I)) (h1 h2) (x y : LusztigF k I) :
    formQ D v B h1 h2 (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B x y := rfl

variable (hvt : Transcendental ℚ v)
include hvt

variable (R) in
/-- `G_λ(x, y) = (x v_λ, y v_λ)` on `U⁻_ν`. -/
def gF (Λ : Y →+ ℤ) (ν : I →₀ ℕ) : LinearMap.BilinForm k (Uw D v ν) :=
  (formQ D v (VermaModule.shapF R (pow_ne_one_of_transcendental' hvt) Λ)
    (fun x hx y ↦ by
      rw [VermaModule.shapF_apply,
        (VermaModule.toVerma_eq_zero_iff (pow_ne_one_of_transcendental' hvt) x).2
          (mem_serreSubmodule.1 hx), map_zero, LinearMap.zero_apply])
    (fun x y hy ↦ by
      rw [VermaModule.shapF_apply,
        (VermaModule.toVerma_eq_zero_iff (pow_ne_one_of_transcendental' hvt) y).2
          (mem_serreSubmodule.1 hy), map_zero])).compl₁₂ (Uw D v ν).subtype (Uw D v ν).subtype

lemma gF_mk (Λ : Y →+ ℤ) {ν : I →₀ ℕ} {x y : LusztigF k I} (hx : x ∈ LusztigF.weightSpace k ν)
    (hy : y ∈ LusztigF.weightSpace k ν) :
    gF R hvt Λ ν ⟨_, mk_mem_Uw hx⟩ ⟨_, mk_mem_Uw hy⟩ =
      VermaModule.shapF R (pow_ne_one_of_transcendental' hvt) Λ x y := rfl

variable (D) in
/-- Lusztig's form `G_0 = ( , )` on `U⁻_ν`. -/
def g0 (ν : I →₀ ℕ) : LinearMap.BilinForm k (Uw D v ν) :=
  (formQ D v (LusztigF.form D v)
    (fun _ hx y ↦ (mem_radical_iff (D := D) (v := v)).1
      (serreIdeal_le_radical (NeZero.ne v) (pow_ne_one_of_transcendental' hvt)
        (mem_serreSubmodule.1 hx)) y)
    (fun x _ hy ↦ (mem_radical_iff' (D := D) (v := v)).1
      (serreIdeal_le_radical (NeZero.ne v) (pow_ne_one_of_transcendental' hvt)
        (mem_serreSubmodule.1 hy)) x)).compl₁₂ (Uw D v ν).subtype (Uw D v ν).subtype

lemma g0_mk {ν : I →₀ ℕ} {x y : LusztigF k I} (hx : x ∈ LusztigF.weightSpace k ν)
    (hy : y ∈ LusztigF.weightSpace k ν) :
    g0 D hvt ν ⟨_, mk_mem_Uw hx⟩ ⟨_, mk_mem_Uw hy⟩ = LusztigF.form D v x y := rfl

lemma g0_eq {ν : I →₀ ℕ} {x y : Uw D v ν} {P Q : LusztigF k I}
    (hx : (x : Um D v) = Submodule.Quotient.mk P) (hy : (y : Um D v) = Submodule.Quotient.mk Q) :
    g0 D hvt ν x y = LusztigF.form D v P Q := by
  simp only [g0, LinearMap.compl₁₂_apply, Submodule.subtype_apply]
  rw [hx, hy]
  rfl

lemma gF_eq (Λ : Y →+ ℤ) {ν : I →₀ ℕ} {x y : Uw D v ν} {P Q : LusztigF k I}
    (hx : (x : Um D v) = Submodule.Quotient.mk P) (hy : (y : Um D v) = Submodule.Quotient.mk Q) :
    gF R hvt Λ ν x y = VermaModule.shapF R (pow_ne_one_of_transcendental' hvt) Λ P Q := by
  simp only [gF, LinearMap.compl₁₂_apply, Submodule.subtype_apply]
  rw [hx, hy]
  rfl

/-- **`G_0` is nondegenerate on `U⁻_ν`** (quantum Gabber–Kac: the radical of `( , )` is `J`). -/
theorem nondegenerate_g0 [Finite I] (ν : I →₀ ℕ) : (g0 D hvt ν).Nondegenerate := by
  classical
  have hL : ∀ x : Uw D v ν, (∀ y, g0 D hvt ν x y = 0) → x = 0 := by
    rintro ⟨_, x, hx, rfl⟩ h
    have hrad : x ∈ radical D v := by
      rw [mem_radical_iff]
      intro y
      have hy : y ∈ ⨆ μ, LusztigF.weightSpace k (I := I) μ := by
        rw [iSup_weightSpace]; trivial
      induction hy using Submodule.iSup_induction' with
      | mem μ y hy =>
        by_cases hμ : ν = μ
        · subst hμ
          exact h ⟨_, mk_mem_Uw hy⟩
        · exact form_eq_zero_of_ne D v hμ hx hy
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    rw [radical_eq_serreIdeal D hvt] at hrad
    exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 (mem_serreSubmodule.2 hrad))
  have hs : ∀ x y : Uw D v ν, g0 D hvt ν x y = g0 D hvt ν y x := by
    rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    exact form_comm D v x y
  exact ⟨hL, fun y h ↦ hL y fun x ↦ by rw [hs]; exact h x⟩

end Forms

/-! ### Stable duals -/

section Dual

variable {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k]

omit [CharZero k] [NeZero v] [DecidableEq I] in
/-- Elements of `Σ A θ_w` lift to the lattice of words of length `≤ N`. -/
lemma exists_latN_of_mem_mon {ν : I →₀ ℕ} {N : ℕ} (hN : ν.degree ≤ N) {x : Uw D v ν}
    (hx : x ∈ mon D v A ν) :
    ∃ P ∈ VermaModule.latN k I A N, (x : Um D v) = Submodule.Quotient.mk P := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨FreeAlgebra.wordBasis k I w.1, Submodule.subset_span ⟨w.1, ?_, rfl⟩, rfl⟩
    change w.1.length ≤ N
    rw [← degree_wordWeight, w.2]
    exact hN
  | zero => exact ⟨0, zero_mem _, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP, e⟩ := hx
    obtain ⟨Q, hQ, e'⟩ := hy
    exact ⟨P + Q, add_mem hP hQ, by rw [Submodule.coe_add, e, e', Submodule.Quotient.mk_add]⟩
  | smul a x _ hx =>
    obtain ⟨P, hP, e⟩ := hx
    exact ⟨a • P, Submodule.smul_mem _ a hP, by
      rw [Submodule.coe_smul_of_tower, e, Submodule.Quotient.mk_smul]⟩

omit [DecidableEq I] [CharZero k] [NeZero v] in
/-- `zᵢ = vᵢ^{-2⟨i,λ⟩} = ϖ^{2 dᵢ ⟨i,λ⟩}`. -/
lemma zcoef_eq {ϖ : A} (hϖv : algebraMap A k ϖ = v⁻¹) (Λ : Y →+ ℤ) (i : I)
    (hΛ : 0 ≤ Λ (R.coroot i)) :
    VermaModule.zcoef R v Λ i = algebraMap A k (ϖ ^ (2 * D.d i * (Λ (R.coroot i)).toNat)) := by
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hΛ
  rw [VermaModule.zcoef, hn, Int.toNat_natCast, map_pow, hϖv, ← zpow_natCast, ← zpow_natCast,
    inv_zpow', ← zpow_mul]
  congr 1
  push_cast
  ring

variable {ϖ : A}
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
include hk

/-- **Stable duals** (our proof of [HK] Exercise 5.13): for `λ` large, `Λ_λ` is a fixed lattice
`Λ` and its dual for `G_λ` is its dual for Lusztig's form `G_0`. -/
theorem exists_dual_stLat_eq [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
    (hϖv : algebraMap A k ϖ = v⁻¹) {ν : I →₀ ℕ} (hA : ∀ s < ν.degree, PropA hvt hR A s)
    (hE : PropE hvt hR A ν.degree) (ρ : Dom R) (hρ : ∀ i, 1 ≤ ρ.1 (R.coroot i)) :
    ∃ Λ₁ : Dom R, (∀ i, (ν.degree : ℤ) ≤ Λ₁.1 (R.coroot i)) ∧ ∀ Λ : Dom R,
      stLat hvt hR A (Λ + Λ₁) ν = stLat hvt hR A Λ₁ ν ∧
      DualLattice.dual (gF R hvt (Λ + Λ₁).1 ν) (stLat hvt hR A Λ₁ ν) =
        DualLattice.dual (g0 D hvt ν) (stLat hvt hR A Λ₁ ν) := by
  classical
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have hpow : ∀ n : ℕ, algebraMap A k (ϖ ^ n) ≠ 0 := fun n ↦ by
    rw [map_pow]; exact pow_ne_zero _ hϖ0
  obtain ⟨Λ₀, hΛ₀, hst⟩ := exists_stLat_eq hk hϖv hA hE ρ hρ
  set St := stLat hvt hR A Λ₀ ν
  obtain ⟨C, hC⟩ := exists_pow_smul_mon_le (hvt := hvt) (hR := hR) hϖv hA
  obtain ⟨c, hc⟩ := exists_pow_smul_mem_mon (hvt := hvt) (hR := hR) hk hΛ₀
  obtain ⟨e₀, he₀⟩ := DualLattice.exists_pow_smul_mem_of_mem_dual hk (nondegenerate_g0 hvt ν)
    (mon_fg A ν) (span_mon A ν)
  set e := C + e₀ + C
  -- `St^∨ ⊆ ϖ^{-e} St` for `G_0`
  have hbound : ∀ x ∈ DualLattice.dual (g0 D hvt ν) St, ϖ ^ e • x ∈ St := by
    intro x hx
    have h1 : ϖ ^ C • x ∈ DualLattice.dual (g0 D hvt ν) (mon D v A ν) := by
      intro y hy
      rw [DualLattice.apply_smul_left_A]
      obtain ⟨a, ha⟩ := hx _ (hC Λ₀ y hy)
      exact ⟨a, by rw [ha, DualLattice.apply_smul_right_A]⟩
    have h2 := hC Λ₀ _ (he₀ _ h1)
    rwa [smul_smul, smul_smul, ← pow_add, ← pow_add] at h2
  have hfin : ∀ x, ∃ n : ℕ, ϖ ^ n • x ∈ DualLattice.dual (g0 D hvt ν) St :=
    DualLattice.exists_pow_smul_mem_dual hk _ (mon_fg A ν) hc
  -- the precision needed
  obtain ⟨Cs, hCs⟩ := VermaModule.exists_shapZ_sub_mem (D := D) (v := v) A hk ν.degree
  set m := e + 1 + 2 * c + Cs
  let mρ : Dom R := ⟨m • ρ.1, fun i ↦ by
    rw [AddMonoidHom.nsmul_apply]; exact nsmul_nonneg (ρ.2 i) m⟩
  refine ⟨mρ + Λ₀, fun i ↦ ?_, fun Λ ↦ ?_⟩
  · have h1 := hΛ₀ i
    have h2 := mρ.2 i
    change _ ≤ (mρ.1 + Λ₀.1) (R.coroot i)
    rw [AddMonoidHom.add_apply]
    omega
  have hSt : ∀ Λ' : Dom R, stLat hvt hR A (Λ' + Λ₀) ν = St := hst
  have e1 : Λ + (mρ + Λ₀) = (Λ + mρ) + Λ₀ := Subtype.ext (add_assoc _ _ _).symm
  rw [e1, hSt, hSt]
  refine ⟨rfl, ?_⟩
  set Γ := Λ + mρ + Λ₀
  have hΓ : ∀ i, (m : ℤ) ≤ Γ.1 (R.coroot i) := by
    intro i
    change (m : ℤ) ≤ (Λ.1 + m • ρ.1 + Λ₀.1) (R.coroot i)
    rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply, nsmul_eq_mul]
    have h1 := hρ i
    have h2 := Λ.2 i
    have h3 := Λ₀.2 i
    nlinarith
  have hz : ∀ i, ∃ a : A, VermaModule.zcoef R v Γ.1 i = algebraMap A k (ϖ ^ m * a) := by
    intro i
    have h0 : 0 ≤ Γ.1 (R.coroot i) := Γ.2 i
    rw [zcoef_eq hϖv _ i h0]
    have hle : m ≤ 2 * D.d i * (Γ.1 (R.coroot i)).toNat := by
      have := hΓ i
      have := D.d_pos i
      have : (m : ℤ) ≤ ((Γ.1 (R.coroot i)).toNat : ℤ) := by omega
      nlinarith
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
    exact ⟨ϖ ^ t, by rw [ht, pow_add]⟩
  refine DualLattice.dual_eq_of_sub hϖ0 (e := e) (m := e + 1) le_rfl hbound hfin ?_
  intro x hx y hy
  obtain ⟨P, hP, eP⟩ := exists_latN_of_mem_mon le_rfl (hc x hx)
  obtain ⟨Q, hQ, eQ⟩ := exists_latN_of_mem_mon le_rfl (hc y hy)
  obtain ⟨a, ha⟩ := hCs _ m hz P hP Q hQ
  have key : algebraMap A k (ϖ ^ (2 * c)) * (g0 D hvt ν x y - gF R hvt Γ.1 ν x y) =
      LusztigF.form D v P Q - VermaModule.shapF R (pow_ne_one_of_transcendental' hvt) Γ.1 P Q := by
    have h1 : g0 D hvt ν (ϖ ^ c • x) (ϖ ^ c • y) = LusztigF.form D v P Q := g0_eq hvt eP eQ
    have h2 : gF R hvt Γ.1 ν (ϖ ^ c • x) (ϖ ^ c • y) =
        VermaModule.shapF R (pow_ne_one_of_transcendental' hvt) Γ.1 P Q := gF_eq hvt _ eP eQ
    rw [← h1, ← h2, DualLattice.apply_smul_left_A, DualLattice.apply_smul_right_A,
      DualLattice.apply_smul_left_A, DualLattice.apply_smul_right_A, two_mul, pow_add, map_mul]
    ring
  rw [VermaModule.form_eq_shapZ_zero, VermaModule.shapF_eq_shapZ] at key
  have hm : m = Cs + 2 * c + (e + 1) := by omega
  rw [hm] at ha
  refine ⟨-a, mul_left_cancel₀ (hpow (Cs + 2 * c)) ?_⟩
  simp only [pow_add, map_mul, map_neg] at ha key ⊢
  linear_combination (algebraMap A k (ϖ ^ Cs)) * key - ha

end Dual

end GrandLoop

end LieLean.QuantumGroup
