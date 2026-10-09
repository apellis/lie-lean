/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Existence
import LieLean.Algebra.QuantumGroup.CrystalBasis.StringComparison
import LieLean.Algebra.QuantumGroup.CrystalBasis.Valuation
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorIntegrable

/-!
# Strings of `y⁻ v_λ` for `⟨i, λ⟩ ≫ 0`

Let `y ∈ 'f` with `ᵢr(y) ∈ J` (`J` the Serre ideal), i.e. the class of `y` in `U⁻` is killed by
Kashiwara's operator `e'ᵢ = ᵢr` (`LusztigF.bosonE`). For dominant `λ` and `x = y⁻ v_λ ∈ V(λ)`,
the Verma formula gives
`Eᵢ x = cᵢ (rᵢ y)⁻ v_λ`, `cᵢ = -(vᵢ - vᵢ⁻¹)⁻¹ vᵢ^{-⟨i,λ⟩}` (`GrandLoop.E_smul_ev_of_lDeriv`),
and since `ᵢr` and `rᵢ` commute (`LusztigF.lDeriv_rDeriv`), `Eᵢ^m x = cᵢ^m (rᵢ^m y)⁻ v_λ`.
So the higher string components of `x` are divisible by a high power of `ϖ = v⁻¹` when
`⟨i, λ⟩` is large, and `Fᵢ^{(a)} x` is compatible with Kashiwara's operators modulo `ϖ L(λ)`:
`f̃ᵢ Fᵢ^{(a)} x ≡ Fᵢ^{(a+1)} x` and `ẽᵢ Fᵢ^{(a+1)} x ≡ Fᵢ^{(a)} x`
(`GrandLoop.fK_dF_ev_sub_mem`, `GrandLoop.eK_dF_ev_sub_mem`), with an explicit bound on
`⟨i, λ⟩`. This is [Jan] Lemmas 10.4–10.6 (b) (stated there in finite type, with lattices at
`q = 0`), in the conventions of this library; the bookkeeping by string components
(`QuantumGroup.IntegrableSl2.IsKashiwaraStable.fTilde_dF_sub_mem`) is our own.

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 10.4–10.6.
* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.2.13.
-/

open Finset Pointwise LusztigF

noncomputable section

namespace LusztigF

variable {k I : Type*} [Field k] [DecidableEq I] {D : LusztigCartanDatum I} {v : k}

/-- The left and right skew derivations commute: `ᵢr ∘ rⱼ = rⱼ ∘ ᵢr`. -/
theorem lDeriv_rDeriv (i j : I) (x : LusztigF k I) :
    lDeriv D v i (rDeriv D v j x) = rDeriv D v j (lDeriv D v i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 l =>
    simp only [rDeriv_θ, lDeriv_θ, apply_ite, lDeriv_one, rDeriv_one, map_zero, ite_self]
  | mul a b ha hb =>
    simp only [rDeriv_mul, lDeriv_mul, map_add]
    rw [ha, hb, lDeriv_twist, rDeriv_twist, D.dot_comm j i]
    simp only [mul_smul_comm, smul_mul_assoc]
    abel
  | add a b ha hb => simp [ha, hb]

end LusztigF

namespace LieLean.QuantumGroup

/-! ### Orders of the coefficients -/

section Valuation

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra A k] {w : A}

lemma IsUnitPow.pow' (hw0 : algebraMap A k w ≠ 0) {e : ℤ} {κ : k} (h : IsUnitPow w e κ)
    (j : ℕ) : IsUnitPow w (j * e) (κ ^ j) := by
  induction j with
  | zero => simpa using isUnitPow_one
  | succ j ih =>
    rw [pow_succ]
    convert ih.mul hw0 h using 1
    push_cast; ring

variable [IsLocalRing A] (hw : w ∈ IsLocalRing.maximalIdeal A) (hw0 : algebraMap A k w ≠ 0)
include hw hw0

omit [IsLocalRing A] hw in
lemma isOnePow_qFactorial (j : ℕ) :
    IsOnePow w (-((∑ m ∈ range j, m : ℕ) : ℤ)) (qFactorial (algebraMap A k w) j) := by
  induction j with
  | zero => simpa [qFactorial] using isOnePow_one
  | succ j ih =>
    rw [qFactorial_succ]
    convert (isOnePow_qInt hw0 (Nat.succ_pos j)).mul hw0 ih using 1
    rw [sum_range_succ]; push_cast; ring

/-- The coefficient `[b+j, b] [P, j]⁻¹ [j]!⁻¹ cᵢ^j` with `cᵢ = -(q - q⁻¹)⁻¹ q^{-n}` lies in
`w^{s+1} A`, where `q⁻¹ = w`, `P = p + 2j` and `s + b ≤ n + p`. -/
lemma exists_coef_eq {q : k} (hqw : algebraMap A k w = q⁻¹) (hq0 : q ≠ 0)
    (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (n p : ℤ) (j b s : ℕ) (hj : 1 ≤ j) (hpj : 0 ≤ p + j)
    (hb : (s : ℤ) + b ≤ n + p) :
    ∃ c : A, qBinomial q (b + j) b * (qBinomial q (p + 2 * j).toNat j)⁻¹ * (qFactorial q j)⁻¹ *
      (-((q - q⁻¹)⁻¹ * (q ^ n)⁻¹)) ^ j = algebraMap A k (w ^ (s + 1) * c) := by
  have hinvq : q = (algebraMap A k w)⁻¹ := by rw [hqw, inv_inv]
  have hbin : ∀ N m, m ≤ N → qBinomial q N m = qBinomial (algebraMap A k w) N m := by
    intro N m hmN
    have hq0' : q⁻¹ ≠ 0 := inv_ne_zero hq0
    have hq' : ∀ n : ℕ, 0 < n → q⁻¹ ^ n ≠ 1 := fun n hn h ↦
      hq n hn (by rw [inv_pow, inv_eq_one] at h; exact h)
    have h1 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) hmN
    have h2 := qBinomial_mul_qFactorial_mul_qFactorial (v := q⁻¹) hmN
    rw [IntegrableSl2.qFactorial_inv, IntegrableSl2.qFactorial_inv,
      IntegrableSl2.qFactorial_inv] at h2
    rw [hqw]
    have hf := mul_ne_zero (qFactorial_ne_zero_of_pow_ne_one hq0 hq m)
      (qFactorial_ne_zero_of_pow_ne_one hq0 hq (N - m))
    apply mul_right_cancel₀ hf
    rw [← mul_assoc, h1, ← mul_assoc, h2]
  -- the four factors
  have h1 : IsUnitPow w (-((b * j : ℕ) : ℤ)) (qBinomial q (b + j) b) := by
    rw [hbin _ _ (by omega)]
    have := (isOnePow_qBinomial hw0 (show b ≤ b + j by omega)).isUnitPow hw
    simpa [Nat.add_sub_cancel_left] using this
  obtain ⟨P, hP⟩ : ∃ P : ℕ, (P : ℤ) = p + 2 * j := ⟨(p + 2 * j).toNat, by omega⟩
  have hPt : (p + 2 * j).toNat = P := by omega
  have h2 : IsUnitPow w ((j * (P - j) : ℕ) : ℤ) (qBinomial q (p + 2 * j).toNat j)⁻¹ := by
    rw [hPt, hbin _ _ (by omega)]
    have := ((isOnePow_qBinomial hw0 (show j ≤ P by omega)).isUnitPow hw).inv
    simpa using this
  have h3 : InPow w 0 (qFactorial q j)⁻¹ := by
    rw [hinvq, IntegrableSl2.qFactorial_inv]
    have := ((isOnePow_qFactorial hw0 j).inv hw).inPow
    exact this.mono hw0 (by simp only [neg_neg]; positivity)
  have hden : IsUnitPow w (-1) (q - q⁻¹) := by
    refine ⟨1 - w ^ 2, ?_, ?_⟩
    · have := isUnit_one_add_mul hw (-w)
      convert this using 1; ring
    · rw [hinvq, inv_inv, zpow_neg_one, map_sub, map_one, map_pow]
      field_simp
  have h4 : IsUnitPow w ((j : ℤ) * (1 + n)) ((-((q - q⁻¹)⁻¹ * (q ^ n)⁻¹)) ^ j) := by
    refine IsUnitPow.pow' hw0 ?_ j
    refine IsUnitPow.neg ?_
    have hqn : (q ^ n)⁻¹ = algebraMap A k w ^ n := by
      rw [hinvq, inv_zpow', zpow_neg, inv_inv]
    rw [hqn]
    have := hden.inv.mul hw0 (isUnitPow_zpow (ϖ := w) n)
    simpa using this
  have hall := ((h1.inPow.mul hw0 h2.inPow).mul hw0 h3).mul hw0 h4.inPow
  have hle : ((s + 1 : ℕ) : ℤ) ≤
      -((b * j : ℕ) : ℤ) + ((j * (P - j) : ℕ) : ℤ) + 0 + (j : ℤ) * (1 + n) := by
    have hPj : ((P - j : ℕ) : ℤ) = p + j := by omega
    push_cast [hPj, Nat.cast_sub (show j ≤ P by omega)]
    have hX : (0 : ℤ) ≤ n + p + 1 - b := by omega
    have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
    nlinarith
  obtain ⟨c, hc⟩ := hall.mono hw0 hle
  refine ⟨c, ?_⟩
  rw [hc, zpow_natCast, map_mul, map_pow]

end Valuation

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]

/-! ### `Eᵢ` on `y⁻ v_λ` -/

section E

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv'

/-- The Verma formula: `Eᵢ (y⁻ v_λ) = (vermaOpQ y)⁻ v_λ`. -/
lemma E_smul_ev (Λ : Y →+ ℤ) (i : I) (y : LusztigF k I) :
    E R v i • ev R v Λ y = ev R v Λ (vermaOpQ D v (fun j ↦ Λ (R.coroot j)) i y) := by
  have hq := qDenom_ne_zero (D := D) (NeZero.ne v) hv' i
  have hE : LusztigF.vermaOp i (qCoeff R v Λ i) = vermaOpQ D v (fun j ↦ Λ (R.coroot j)) i :=
    (vermaOpQ_eq_vermaOp D (NeZero.ne v) _ hq).symm
  rw [ev_apply, ev_apply, ← Submodule.Quotient.mk_smul, VermaModule.E_smul_toVerma hv', hE]

variable (R v) in
/-- `cᵢ = -(vᵢ - vᵢ⁻¹)⁻¹ vᵢ^{-⟨i,λ⟩}`. -/
def eCoef (Λ : Y →+ ℤ) (i : I) : k :=
  -((v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ * ((v ^ D.d i) ^ Λ (R.coroot i))⁻¹)

/-- If `ᵢr(y) ∈ J` then `Eᵢ (y⁻ v_λ) = cᵢ (rᵢ y)⁻ v_λ`. -/
lemma E_smul_ev_of_lDeriv (Λ : Y →+ ℤ) (i : I) {y : LusztigF k I}
    (hy : lDeriv D v i y ∈ serreIdeal D v) :
    E R v i • ev R v Λ y = eCoef R v Λ i • ev R v Λ (rDeriv D v i y) := by
  have ht : twist D v⁻¹ i (lDeriv D v i y) ∈ serreIdeal D v := by
    rw [twist_eq_diagTwist]; exact diagTwist_mem_serreIdeal _ hy
  rw [E_smul_ev hv', vermaOpQ_apply, map_smul, map_sub, map_smul, map_smul,
    ev_eq_zero_of_mem hv' Λ ht, smul_zero, zero_sub, smul_neg, smul_smul, eCoef, neg_smul]

omit [CharZero k] in
lemma lDeriv_rDeriv_pow_mem (i : I) {y : LusztigF k I} (hy : lDeriv D v i y ∈ serreIdeal D v)
    (m : ℕ) : lDeriv D v i ((rDeriv D v i ^ m) y) ∈ serreIdeal D v := by
  induction m with
  | zero => simpa using hy
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, lDeriv_rDeriv]
    exact rDeriv_mem_serreIdeal (NeZero.ne v) hv' i ih

/-- `Eᵢ^m (y⁻ v_λ) = cᵢ^m (rᵢ^m y)⁻ v_λ` if `ᵢr(y) ∈ J`. -/
lemma E_pow_ev_of_lDeriv {Λ : Y →+ ℤ} (hM : IsIntegrable R v (IrreducibleModule R v Λ)) (i : I)
    {y : LusztigF k I} (hy : lDeriv D v i y ∈ serreIdeal D v) (m : ℕ) :
    ((nodeSl2 R v _ hv' hM i).E ^ m) (ev R v Λ y) =
      eCoef R v Λ i ^ m • ev R v Λ ((rDeriv D v i ^ m) y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul]
    change eCoef R v Λ i ^ m • (E R v i • ev R v Λ ((rDeriv D v i ^ m) y)) = _
    rw [E_smul_ev_of_lDeriv hv' Λ i (lDeriv_rDeriv_pow_mem hv' i hy m), smul_smul, pow_succ,
      pow_succ', Module.End.mul_apply]

end E

/-! ### Comparison with Kashiwara's operators -/

section Compare

variable {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k]
  [IsLocalRing A] {ϖ : A}

/-- **Strings of `y⁻ v_λ` for `⟨i, λ⟩` large** ([Jan] 10.5, 10.6 (b)): let `y ∈ 'f_ν` with
`ᵢr(y) ∈ J`, and `s` with `ϖ^s (rᵢ^m y)⁻ v_λ ∈ L(λ)` for all `m`. If
`s + a + 1 + ⟨i, ν⟩ ≤ 2⟨i, λ⟩`, then the string components `ηⱼ` (`j ≥ 1`) of `x = y⁻ v_λ`
satisfy `[b+j, b] ηⱼ ∈ ϖ L(λ)` for all `b ≤ a + 1`. -/
theorem component_mem_of_large (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖv : algebraMap A k ϖ = v⁻¹) (Λ : Dom R)
    (hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) (lat hvt hR A Λ))
    (i : I) {ν : I →₀ ℕ} {y : LusztigF k I}
    (hy : lDeriv D v i y ∈ serreIdeal D v) (s : ℕ)
    (hs : ∀ m, ϖ ^ s • ev R v Λ.1 ((rDeriv D v i ^ m) y) ∈ lat hvt hR A Λ) (a : ℕ)
    (hΛ : (s : ℤ) + a + 1 + R.rootSum ν (R.coroot i) ≤ 2 * Λ.1 (R.coroot i))
    {N : ℕ} {η : ℕ → IrreducibleModule R v Λ.1}
    (h1 : ∀ j : ℕ, η j ∈ (nodeSl2 R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).prim
      (Λ.1 (R.coroot i) - R.rootSum ν (R.coroot i) + 2 * j))
    (h2 : ∀ j : ℕ, η j ≠ 0 → 0 ≤ Λ.1 (R.coroot i) - R.rootSum ν (R.coroot i) + j)
    (h3 : ∀ j, N ≤ j → η j = 0)
    (hx : ev R v Λ.1 y = ∑ j ∈ range N,
      (nodeSl2 R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF j (η j)) :
    ∀ j, 1 ≤ j → ∀ b ≤ a + 1, qBinomial (v ^ D.d i) (b + j) b • η j ∈ ϖ • lat hvt hR A Λ := by
  have hv' := pow_ne_one_of_transcendental' hvt
  set V := nodeSl2 R v _ hv' (isInt hvt hR Λ) i
  set n := Λ.1 (R.coroot i)
  set p := Λ.1 (R.coroot i) - R.rootSum ν (R.coroot i)
  have hq0 : v ^ D.d i ≠ 0 := pow_d_ne_zero i
  have hq := pow_d_ne_one (D := D) hv' i
  intro j hj b hb
  by_cases h0 : η j = 0
  · rw [h0, smul_zero]; exact zero_mem _
  have hjN : j < N := by by_contra h; exact h0 (h3 j (by omega))
  have hpj := h2 j h0
  -- the coefficient
  set w := ϖ ^ D.d i with hw_def
  have hw : w ∈ IsLocalRing.maximalIdeal A :=
    Ideal.pow_mem_of_mem _ hϖ _ (D.d_pos i)
  have hwv : algebraMap A k w = (v ^ D.d i)⁻¹ := by rw [map_pow, hϖv, inv_pow]
  have hw0 : algebraMap A k w ≠ 0 := by rw [hwv]; exact inv_ne_zero hq0
  have hn0 : 0 ≤ n := Λ.2 i
  obtain ⟨c, hc⟩ := exists_coef_eq hw hw0 hwv hq0 hq n p j b s hj hpj (by omega)
  set t := qBinomial (v ^ D.d i) (b + j) b * (qBinomial (v ^ D.d i) (p + 2 * j).toNat j)⁻¹
  have hdE : t • V.dE j (ev R v Λ.1 y) ∈ ϖ • lat hvt hR A Λ := by
    rw [IntegrableSl2.dE_apply, E_pow_ev_of_lDeriv hv' (isInt hvt hR Λ) i hy j, smul_smul,
      smul_smul]
    have e : t * (qFactorial (v ^ D.d i) j)⁻¹ * eCoef R v Λ.1 i ^ j =
        algebraMap A k (w ^ (s + 1) * c) := by
      rw [← hc, eCoef]
    rw [e, algebraMap_smul]
    have e2 : w ^ (s + 1) * c = ϖ * ((ϖ ^ ((D.d i - 1) * (s + 1)) * c) * ϖ ^ s) := by
      have hd := D.d_pos i
      rw [hw_def, ← pow_mul]
      obtain ⟨d', hd'⟩ : ∃ d', D.d i = d' + 1 := ⟨D.d i - 1, by omega⟩
      rw [hd', Nat.add_sub_cancel]
      ring
    rw [e2, mul_smul, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.smul_mem _ _ (hs j))
  rw [hx] at hdE
  have hKS := hL.isKashiwaraStable i
  have := hKS.smul_mem_of_smul_dE_mem ϖ h1 h2 N j hjN t hdE
  have hne : qBinomial (v ^ D.d i) (p + 2 * j).toNat j ≠ 0 :=
    qBinomial_ne_zero_of_pow_ne_one hq0 hq (by omega)
  simpa [t, mul_assoc, inv_mul_cancel₀ hne] using this

end Compare

end GrandLoop

end LieLean.QuantumGroup
