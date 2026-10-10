/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2MixedOne

/-!
# Boundary stability and one-sided mixed products in the integral G₂ span

The span is stable under left multiplication by first-root divided powers. The five mixed
pairs with one exponent equal to one belong to the span. Full multiplicative closure and
arbitrary two-exponent mixed straightening are not asserted.
-/

noncomputable section

namespace LieLean.QuantumGroup.G2Integral

open Finset

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]
  {q : k} {e A b C D f : B} {Λ : Subring k}

lemma smul_mem_orderedSpan {z : k} (hz : z ∈ Λ) {x : B}
    (hx : x ∈ orderedSpan q Λ e A b C D f) : z • x ∈ orderedSpan q Λ e A b C D f := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨z', hz', i, a, b', c, d, l, rfl⟩ := hx
    exact AddSubgroup.subset_closure
      ⟨z * z', mul_mem hz hz', i, a, b', c, d, l, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

lemma M6_mem_orderedSpan (i a b' c d l : ℕ) :
    M6 q e A b C D f i a b' c d l ∈ orderedSpan q Λ e A b C D f :=
  AddSubgroup.subset_closure ⟨1, one_mem _, i, a, b', c, d, l, by rw [one_smul]⟩

lemma one_mem_orderedSpan : (1 : B) ∈ orderedSpan q Λ e A b C D f := by
  simpa [M6, M5, P3, qDivPow_zero'] using
    M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
      (D := D) (f := f) 0 0 0 0 0 0

lemma mul_mem_orderedSpan_of_gen {z : B}
    (hz : ∀ i a b' c d l, z * M6 q e A b C D f i a b' c d l ∈ orderedSpan q Λ e A b C D f)
    {x : B} (hx : x ∈ orderedSpan q Λ e A b C D f) :
    z * x ∈ orderedSpan q Λ e A b C D f := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨z', hz', i, a, b', c, d, l, rfl⟩ := hx
    rw [mul_smul_comm]
    exact smul_mem_orderedSpan hz' (hz i a b' c d l)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

/-- Left multiplication by every first-root divided power preserves the ordered span. -/
theorem qDivPow_e_mul_mem (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hqΛ : q ∈ Λ) (hqΛ' : q⁻¹ ∈ Λ) (n : ℕ) {x : B}
    (hx : x ∈ orderedSpan q Λ e A b C D f) :
    qDivPow q n e * x ∈ orderedSpan q Λ e A b C D f := by
  refine mul_mem_orderedSpan_of_gen (fun i a b' c d l => ?_) hx
  rw [M6, ← mul_assoc, A2Integral.qDivPow_mul_qDivPow e n i
    (A2Integral.qFactorial_ne_zero_of_qInt hqi _), smul_mul_assoc]
  exact smul_mem_orderedSpan (A2Integral.qBinomial_mem hqΛ hqΛ' _ _)
    (M6_mem_orderedSpan _ _ _ _ _ _)

private lemma square_eq_divided (t : k) (x : B) (h2 : qInt t 2 ≠ 0) :
    x ^ 2 = qInt t 2 • qDivPow t 2 x := by
  have hh : qFactorial t 2 = qInt t 2 := by simp [qFactorial, qInt]
  simp [qDivPow, hh, smul_smul, h2]

variable (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0)
  (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
  (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
  (H : Rel q e A b C D f) (hqΛ : q ∈ Λ) (hqΛ' : q⁻¹ ∈ Λ)

include hq hd hqi hpi H hqΛ hqΛ' in
/-- Arbitrary last-root/first-root divided powers lie in the ordered integral span. -/
theorem qDivPow_f_mul_qDivPow_e_mem (r s : ℕ) :
    qDivPow (q ^ 3) s f * qDivPow q r e ∈ orderedSpan q Λ e A b C D f := by
  rw [qDivPow_f_mul_qDivPow_e_sum hq hd hqi hpi H]
  refine AddSubgroup.sum_mem _ fun n _ => AddSubgroup.sum_mem _ fun x _ => ?_
  exact smul_mem_orderedSpan (adjoint_straightening_coeff_mem Λ hqΛ hqΛ' _ _ _ _ _ _ _ _)
    (M6_mem_orderedSpan _ _ _ _ _ _)

include hq hqi H hqΛ hqΛ' in
/-- `D e^{(r)}` lies in the ordered integral span for every `r`. -/
theorem D_mul_qDivPow_e_mem (r : ℕ) : D * qDivPow q r e ∈ orderedSpan q Λ e A b C D f := by
  rw [D_mul_qDivPow_e hq hqi H]
  refine AddSubgroup.sum_mem _ fun n _ => smul_mem_orderedSpan
    (B2Integral.sCoef_mem hqΛ hqΛ' _ _ _) ?_
  rcases n with _ | (_ | (_ | n))
  · simpa [shortMixedAdjoint, M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) r 0 0 0 1 0
  · simp only [shortMixedAdjoint, mul_smul_comm]
    apply smul_mem_orderedSpan (mul_mem hqΛ (B2Integral.qInt_mem hqΛ hqΛ' 2))
    simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) (r - 1) 0 1 0 0 0
  · simp only [shortMixedAdjoint, mul_smul_comm]
    apply smul_mem_orderedSpan (B2Integral.qInt_mem hqΛ hqΛ' 3)
    simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) (r - 2) 1 0 0 0 0
  · simp [shortMixedAdjoint]

include hq hqi hpi H hqΛ hqΛ' in
/-- `C e^{(r)}` lies in the ordered integral span for every `r`. -/
theorem C_mul_qDivPow_e_mem (r : ℕ) : C * qDivPow q r e ∈ orderedSpan q Λ e A b C D f := by
  have hq2 : q ^ 2 - 1 ∈ Λ := sub_mem (pow_mem hqΛ _) (one_mem _)
  have hp : q ^ 3 ∈ Λ := pow_mem hqΛ _
  have hp' : (q ^ 3)⁻¹ ∈ Λ := by rw [← inv_pow]; exact pow_mem hqΛ' _
  rw [C_mul_qDivPow_e hq hqi H]
  refine AddSubgroup.sum_mem _ fun n _ => smul_mem_orderedSpan
    (B2Integral.sCoef_mem hqΛ hqΛ' _ _ _) ?_
  rcases n with _ | (_ | (_ | (_ | n)))
  · simpa [squareMixedAdjoint, M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) r 0 0 1 0 0
  · simp only [squareMixedAdjoint, square_eq_divided q b (hqi 2 (by decide)),
      mul_smul_comm, smul_smul]
    apply smul_mem_orderedSpan (mul_mem hq2 (B2Integral.qInt_mem hqΛ hqΛ' 2))
    simpa [M6, M5, P3, qDivPow_zero'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) (r - 1) 0 2 0 0 0
  · simp only [squareMixedAdjoint, mul_smul_comm]
    apply smul_mem_orderedSpan
      (mul_mem (mul_mem hq2 (pow_mem hqΛ' _)) (B2Integral.qInt_mem hqΛ hqΛ' 3))
    simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) (r - 2) 1 1 0 0 0
  · simp only [squareMixedAdjoint, square_eq_divided (q ^ 3) A (hpi 2 (by decide)),
      mul_smul_comm, smul_smul]
    apply smul_mem_orderedSpan (mul_mem
      (mul_mem (mul_mem hq2 (pow_mem hqΛ' _)) (B2Integral.qInt_mem hqΛ hqΛ' 3))
      (B2Integral.qInt_mem hp hp' 2))
    simpa [M6, M5, P3, qDivPow_zero'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) (r - 3) 2 0 0 0 0
  · simp [squareMixedAdjoint]

include hq hqi hpi H hqΛ hqΛ' in
/-- `f B^{(r)}` lies in the ordered integral span for every `r`. -/
theorem f_mul_qDivPow_b_mem (r : ℕ) : f * qDivPow q r b ∈ orderedSpan q Λ e A b C D f := by
  have hq2 : q ^ 2 - 1 ∈ Λ := sub_mem (pow_mem hqΛ _) (one_mem _)
  have hp : q ^ 3 ∈ Λ := pow_mem hqΛ _
  have hp' : (q ^ 3)⁻¹ ∈ Λ := by rw [← inv_pow]; exact pow_mem hqΛ' _
  rw [f_mul_qDivPow_b hq hqi H]
  refine AddSubgroup.sum_mem _ fun n _ => smul_mem_orderedSpan
    (B2Integral.sCoef_mem hqΛ hqΛ' _ _ _) ?_
  rcases n with _ | (_ | (_ | (_ | n)))
  · simpa [squareMixedAdjoint, M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one', mul_assoc] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) 0 0 r 0 0 1
  · simp only [squareMixedAdjoint, square_eq_divided q D (hqi 2 (by decide)),
      mul_smul_comm, smul_smul]
    apply smul_mem_orderedSpan (mul_mem hq2 (B2Integral.qInt_mem hqΛ hqΛ' 2))
    simpa [M6, M5, P3, qDivPow_zero'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) 0 0 (r - 1) 0 2 0
  · simp only [squareMixedAdjoint, mul_smul_comm]
    apply smul_mem_orderedSpan
      (mul_mem (mul_mem hq2 (pow_mem hqΛ' _)) (B2Integral.qInt_mem hqΛ hqΛ' 3))
    simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one', mul_assoc] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) 0 0 (r - 2) 1 1 0
  · simp only [squareMixedAdjoint, square_eq_divided (q ^ 3) C (hpi 2 (by decide)),
      mul_smul_comm, smul_smul]
    apply smul_mem_orderedSpan (mul_mem
      (mul_mem (mul_mem hq2 (pow_mem hqΛ' _)) (B2Integral.qInt_mem hqΛ hqΛ' 3))
      (B2Integral.qInt_mem hp hp' 2))
    simpa [M6, M5, P3, qDivPow_zero'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) 0 0 (r - 3) 2 0 0
  · simp [squareMixedAdjoint]

include hq hqi hpi H hqΛ hqΛ' in
/-- `D^{(r)} A` lies in the ordered integral span for every `r`. -/
theorem qDivPow_D_mul_A_mem (r : ℕ) : qDivPow q r D * A ∈ orderedSpan q Λ e A b C D f := by
  have hq2 : q ^ 2 - 1 ∈ Λ := sub_mem (pow_mem hqΛ _) (one_mem _)
  have hp : q ^ 3 ∈ Λ := pow_mem hqΛ _
  have hp' : (q ^ 3)⁻¹ ∈ Λ := by rw [← inv_pow]; exact pow_mem hqΛ' _
  rw [qDivPow_D_mul_A hq hqi H]
  refine AddSubgroup.sum_mem _ fun n _ => smul_mem_orderedSpan
    (B2Integral.sCoef_mem hqΛ hqΛ' _ _ _) ?_
  rcases n with _ | (_ | (_ | (_ | n)))
  · simpa [reverseSquareMixedAdjoint, M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) 0 1 0 0 r 0
  · simp only [reverseSquareMixedAdjoint, square_eq_divided q b (hqi 2 (by decide)),
      smul_mul_assoc, smul_smul]
    apply smul_mem_orderedSpan (mul_mem hq2 (B2Integral.qInt_mem hqΛ hqΛ' 2))
    simpa [M6, M5, P3, qDivPow_zero'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) 0 0 2 0 (r - 1) 0
  · simp only [reverseSquareMixedAdjoint, smul_mul_assoc]
    apply smul_mem_orderedSpan
      (mul_mem (mul_mem hq2 (pow_mem hqΛ' _)) (B2Integral.qInt_mem hqΛ hqΛ' 3))
    simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) 0 0 1 1 (r - 2) 0
  · simp only [reverseSquareMixedAdjoint, square_eq_divided (q ^ 3) C (hpi 2 (by decide)),
      smul_mul_assoc, smul_smul]
    apply smul_mem_orderedSpan (mul_mem
      (mul_mem (mul_mem hq2 (pow_mem hqΛ' _)) (B2Integral.qInt_mem hqΛ hqΛ' 3))
      (B2Integral.qInt_mem hp hp' 2))
    simpa [M6, M5, P3, qDivPow_zero'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) 0 0 0 2 (r - 3) 0
  · simp [reverseSquareMixedAdjoint]

include hq hqi hpi H hqΛ hqΛ' in
/-- `f A^{(r)}` lies in the ordered integral span for every `r`. -/
theorem f_mul_qDivPow_A_mem (r : ℕ) :
    f * qDivPow (q ^ 3) r A ∈ orderedSpan q Λ e A b C D f := by
  have hq2 : q ^ 2 - 1 ∈ Λ := sub_mem (pow_mem hqΛ _) (one_mem _)
  have hp : q ^ 3 ∈ Λ := pow_mem hqΛ _
  have hp' : (q ^ 3)⁻¹ ∈ Λ := by rw [← inv_pow]; exact pow_mem hqΛ' _
  rw [f_mul_qDivPow_A hq (hqi 2 (by decide)) (hqi 3 (by decide)) hpi H]
  refine AddSubgroup.sum_mem _ fun n _ => smul_mem_orderedSpan
    (B2Integral.sCoef_mem hp hp' _ _ _) ?_
  rcases n with _ | (_ | (_ | n))
  · simpa [longMixedAdjoint, M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) 0 r 0 0 0 1
  · simp only [longMixedAdjoint]
    rw [mul_sub, mul_smul_comm, mul_smul_comm]
    apply sub_mem
    · apply smul_mem_orderedSpan (mul_mem (pow_mem hqΛ _) hq2)
      simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one', mul_assoc] using
        M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
          (D := D) (f := f) 0 (r - 1) 1 0 1 0
    · apply smul_mem_orderedSpan (sub_mem (add_mem (pow_mem hqΛ _) (pow_mem hqΛ _)) (one_mem _))
      simpa [M6, M5, P3, qDivPow_zero', A2Integral.qDivPow_one'] using
        M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
          (D := D) (f := f) 0 (r - 1) 0 1 0 0
  · simp only [longMixedAdjoint, mul_smul_comm]
    apply smul_mem_orderedSpan (mul_mem (mul_mem hqΛ (pow_mem hq2 _))
      (B2Integral.qInt_mem hqΛ hqΛ' 2))
    simpa [M6, M5, P3, qDivPow_zero'] using
      M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
        (D := D) (f := f) 0 (r - 2) 3 0 0 0
  · simp [longMixedAdjoint]

end LieLean.QuantumGroup.G2Integral
