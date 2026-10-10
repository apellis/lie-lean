/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2RootMembership

/-!
# One-sided mixed G₂ divided-power straightening

Finite adjoint strings give the mixed-pair identities when one exponent is one and the
other is arbitrary. These are not the unrestricted two-exponent mixed-pair formulas.
-/

noncomputable section

namespace LieLean.QuantumGroup.G2Integral

open Finset

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- The length-two adjoint string of the fourth nonsimple root. -/
def shortMixedAdjoint (q : k) (A b D : B) : ℕ → B
  | 0 => D
  | 1 => (q * qInt q 2) • b
  | 2 => qInt q 3 • A
  | _ + 3 => 0

/-- The length-three adjoint string of a square-correction mixed pair. -/
def squareMixedAdjoint (q : k) (A b C : B) : ℕ → B
  | 0 => C
  | 1 => (q ^ 2 - 1) • b ^ 2
  | 2 => ((q ^ 2 - 1) * q⁻¹ ^ 3 * qInt q 3) • (A * b)
  | 3 => ((q ^ 2 - 1) * q⁻¹ ^ 4 * qInt q 3) • A ^ 2
  | _ + 4 => 0

variable {q : k} {e A b C D f : B}

lemma shortMixedAdjoint_e (hq : q ≠ 0) (H : Rel q e A b C D f) (n : ℕ) :
    shortMixedAdjoint q A b D n * e =
      (q ^ 1 * q⁻¹ ^ (2 * n)) • (e * shortMixedAdjoint q A b D n) -
        qInt q (n + 1) • shortMixedAdjoint q A b D (n + 1) := by
  rcases n with _ | (_ | (_ | n))
  · simpa [shortMixedAdjoint, qInt] using H.De
  · simp only [shortMixedAdjoint, smul_mul_assoc, H.Be, mul_smul_comm, smul_sub, smul_smul]
    norm_num only
    match_scalars <;> field_simp
  · simp only [shortMixedAdjoint, smul_mul_assoc, H.Ae, mul_smul_comm, smul_zero,
      sub_zero, smul_smul]
    norm_num only
    congr 1
    field_simp
  · simp [shortMixedAdjoint]

lemma squareMixedAdjoint_e (hq : q ≠ 0)
    (hAe : A * e = (q ^ 3)⁻¹ • (e * A))
    (hbe : b * e = q⁻¹ • (e * b) - (q⁻¹ * qInt q 3) • A)
    (hbA : b * A = (q ^ 3)⁻¹ • (A * b))
    (hCe : C * e = e * C - (q ^ 2 - 1) • b ^ 2) (n : ℕ) :
    squareMixedAdjoint q A b C n * e =
      (q ^ 0 * q⁻¹ ^ (2 * n)) • (e * squareMixedAdjoint q A b C n) -
        qInt q (n + 1) • squareMixedAdjoint q A b C (n + 1) := by
  have hbb : b ^ 2 * e = q⁻¹ ^ 2 • (e * b ^ 2) -
      (q⁻¹ ^ 3 * qInt q 3 * qInt q 2) • (A * b) := by
    rw [pow_two, mul_assoc, hbe, mul_sub, mul_smul_comm, mul_smul_comm,
      ← mul_assoc b e, hbe, hbA]
    simp only [sub_mul, smul_mul_assoc, mul_assoc, smul_smul]
    rw [qInt_two]
    match_scalars <;> field_simp
    ring
  rcases n with _ | (_ | (_ | (_ | n)))
  · simpa [squareMixedAdjoint, qInt] using hCe
  · simp only [squareMixedAdjoint, smul_mul_assoc, hbb, mul_smul_comm, smul_sub, smul_smul]
    norm_num only
    module
  · simp only [squareMixedAdjoint, smul_mul_assoc, mul_assoc A b e, hbe, mul_sub,
      mul_smul_comm, ← mul_assoc A e, hAe, smul_mul_assoc, mul_assoc, smul_smul,
      smul_sub, pow_two]
    norm_num only
    match_scalars <;> field_simp
  · have hAA := mul_pow_of_mul_eq_smul (B := Bᵐᵒᵖ) (by
      simpa only [MulOpposite.op_mul, MulOpposite.op_smul] using
        congrArg MulOpposite.op hAe) 2
    have hAA' : A ^ 2 * e = (q ^ 3)⁻¹ ^ 2 • (e * A ^ 2) := by
      simpa only [MulOpposite.unop_mul, MulOpposite.unop_pow, MulOpposite.unop_smul,
        MulOpposite.unop_op] using congrArg MulOpposite.unop hAA
    simp only [squareMixedAdjoint, smul_mul_assoc, hAA', mul_smul_comm,
      smul_zero, sub_zero, smul_smul]
    norm_num only
    congr 1
    field_simp
  · simp [squareMixedAdjoint]

/-- `D e^{(r)}` for arbitrary `r`, with a three-term adjoint string. -/
theorem D_mul_qDivPow_e (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0) (H : Rel q e A b C D f) (r : ℕ) :
    D * qDivPow q r e =
      ∑ n ∈ range (r + 1), B2Integral.sCoef q 1 r n •
        (qDivPow q (r - n) e * shortMixedAdjoint q A b D n) := by
  exact B2Integral.straighten hq hqi 1 (shortMixedAdjoint_e hq H) r

/-- `C e^{(r)}` for arbitrary `r`, with a four-term adjoint string. -/
theorem C_mul_qDivPow_e (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0) (H : Rel q e A b C D f) (r : ℕ) :
    C * qDivPow q r e =
      ∑ n ∈ range (r + 1), B2Integral.sCoef q 0 r n •
        (qDivPow q (r - n) e * squareMixedAdjoint q A b C n) := by
  exact B2Integral.straighten hq hqi 0 (squareMixedAdjoint_e hq H.Ae H.Be H.BA H.Ce) r

/-- `f B^{(r)}` for arbitrary `r`, by the same square-correction adjoint string. -/
theorem f_mul_qDivPow_b (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0) (H : Rel q e A b C D f) (r : ℕ) :
    f * qDivPow q r b =
      ∑ n ∈ range (r + 1), B2Integral.sCoef q 0 r n •
        (qDivPow q (r - n) b * squareMixedAdjoint q C D f n) := by
  exact B2Integral.straighten hq hqi 0 (squareMixedAdjoint_e hq H.CB H.DB H.DC H.fB) r

/-- The reversed square-correction string, used for `D^{(r)} A`. -/
def reverseSquareMixedAdjoint (q : k) (C b A : B) : ℕ → B
  | 0 => A
  | 1 => (q ^ 2 - 1) • b ^ 2
  | 2 => ((q ^ 2 - 1) * q⁻¹ ^ 3 * qInt q 3) • (b * C)
  | 3 => ((q ^ 2 - 1) * q⁻¹ ^ 4 * qInt q 3) • C ^ 2
  | _ + 4 => 0

/-- `D^{(r)} A` for arbitrary `r`, by reversal of the square-correction identity. -/
theorem qDivPow_D_mul_A (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0) (H : Rel q e A b C D f) (r : ℕ) :
    qDivPow q r D * A =
      ∑ n ∈ range (r + 1), B2Integral.sCoef q 0 r n •
        (reverseSquareMixedAdjoint q C b A n * qDivPow q (r - n) D) := by
  let op := MulOpposite.op (α := B)
  have hs := squareMixedAdjoint_e hq (e := op D) (A := op C) (b := op b) (C := op A)
    (by simpa only [op, MulOpposite.op_mul, MulOpposite.op_smul] using congrArg op H.DC)
    (by simpa only [op, MulOpposite.op_mul, MulOpposite.op_smul, MulOpposite.op_sub]
      using congrArg op H.DB)
    (by simpa only [op, MulOpposite.op_mul, MulOpposite.op_smul] using congrArg op H.CB)
    (by simpa only [op, MulOpposite.op_mul, MulOpposite.op_smul, MulOpposite.op_sub,
      MulOpposite.op_pow] using congrArg op H.DA)
  have hrev (n : ℕ) : MulOpposite.unop (squareMixedAdjoint q (op C) (op b) (op A) n) =
      reverseSquareMixedAdjoint q C b A n := by
    rcases n with _ | (_ | (_ | (_ | n))) <;>
      simp [squareMixedAdjoint, reverseSquareMixedAdjoint, op]
  have hh := congrArg MulOpposite.unop (B2Integral.straighten hq hqi 0 hs r)
  simpa only [show squareMixedAdjoint q (op C) (op b) (op A) 0 = op A from rfl,
    MulOpposite.unop_mul, Finset.unop_sum, MulOpposite.unop_smul, hrev, qDivPow,
    MulOpposite.unop_pow, op, MulOpposite.unop_op] using hh

/-- The length-two long-root mixed adjoint string, with divided middle-root cube. -/
def longMixedAdjoint (q : k) (b C D f : B) : ℕ → B
  | 0 => f
  | 1 => (q ^ 2 * (q ^ 2 - 1)) • (b * D) - (q ^ 4 + q ^ 2 - 1) • C
  | 2 => (q * (q ^ 2 - 1) ^ 2 * qInt q 2) • qDivPow q 3 b
  | _ + 3 => 0

lemma longMixedAdjoint_right (hq : q ≠ 0) (h2 : qInt q 2 ≠ 0) (h3 : qInt q 3 ≠ 0)
    (hbA : b * A = (q ^ 3)⁻¹ • (A * b))
    (hDA : D * A = A * D - (q ^ 2 - 1) • b ^ 2)
    (hCA : C * A = (q ^ 3)⁻¹ • (A * C) -
      ((q ^ 2 - 1) ^ 2 / (q ^ 2 * qInt q 3)) • b ^ 3)
    (hfA : f * A = q ^ 3 • (A * f) + (q ^ 4 + q ^ 2 - 1) • C -
      (q ^ 2 * (q ^ 2 - 1)) • (b * D)) (n : ℕ) :
    longMixedAdjoint q b C D f n * A =
      ((q ^ 3) ^ 1 * (q ^ 3)⁻¹ ^ (2 * n)) • (A * longMixedAdjoint q b C D f n) -
        qInt (q ^ 3) (n + 1) • longMixedAdjoint q b C D f (n + 1) := by
  have hp : 1 + q ^ 2 + q ^ 4 ≠ 0 := by
    intro hz
    apply h3
    rw [qInt_three hq]
    field_simp
    linear_combination hz
  have hW2 : (q * (q ^ 2 - 1) ^ 2 * qInt q 2) • qDivPow q 3 b =
      (q * (q ^ 2 - 1) ^ 2 / qInt q 3) • b ^ 3 := by
    simp only [qDivPow, qFactorial_three, smul_smul]
    congr 1
    field_simp
  rcases n with _ | (_ | (_ | n))
  · simp only [longMixedAdjoint]
    norm_num [qInt]
    rw [hfA]
    abel
  · simp only [longMixedAdjoint, hW2, sub_mul, smul_mul_assoc,
      mul_assoc b D A, hDA, mul_sub, ← mul_assoc b A, hbA, hCA,
      mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul]
    norm_num only
    rw [qInt_two, qInt_three hq]
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc]
    match_scalars <;> field_simp
    ring_nf
    field_simp
    ring
  · have hbb := mul_pow_of_mul_eq_smul (B := Bᵐᵒᵖ) (by
      simpa only [MulOpposite.op_mul, MulOpposite.op_smul] using
        congrArg MulOpposite.op hbA) 3
    have hbA : b ^ 3 * A = (q ^ 3)⁻¹ ^ 3 • (A * b ^ 3) := by
      simpa only [MulOpposite.unop_mul, MulOpposite.unop_pow, MulOpposite.unop_smul,
        MulOpposite.unop_op] using congrArg MulOpposite.unop hbb
    simp only [longMixedAdjoint, hW2, smul_mul_assoc, hbA, mul_smul_comm,
      smul_zero, sub_zero, smul_smul]
    norm_num only
    congr 1
    field_simp
  · simp [longMixedAdjoint]

/-- `f A^{(r)}` for arbitrary `r`, with a three-term integral adjoint string. -/
theorem f_mul_qDivPow_A (hq : q ≠ 0) (h2 : qInt q 2 ≠ 0) (h3 : qInt q 3 ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0) (H : Rel q e A b C D f) (r : ℕ) :
    f * qDivPow (q ^ 3) r A =
      ∑ n ∈ range (r + 1), B2Integral.sCoef (q ^ 3) 1 r n •
        (qDivPow (q ^ 3) (r - n) A * longMixedAdjoint q b C D f n) := by
  exact B2Integral.straighten (pow_ne_zero _ hq) hpi 1
    (longMixedAdjoint_right hq h2 h3 H.BA H.DA H.CA H.fA) r

/-- Reversal of the long-root mixed adjoint string. -/
def reverseLongMixedAdjoint (q : k) (b C D A : B) : ℕ → B
  | 0 => A
  | 1 => (q ^ 2 * (q ^ 2 - 1)) • (b * D) - (q ^ 4 + q ^ 2 - 1) • C
  | 2 => (q * (q ^ 2 - 1) ^ 2 * qInt q 2) • qDivPow q 3 D
  | _ + 3 => 0

/-- `f^{(r)} A` for arbitrary `r`, by reversal of the long-root mixed identity. -/
theorem qDivPow_f_mul_A (hq : q ≠ 0) (h2 : qInt q 2 ≠ 0) (h3 : qInt q 3 ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0) (H : Rel q e A b C D f) (r : ℕ) :
    qDivPow (q ^ 3) r f * A =
      ∑ n ∈ range (r + 1), B2Integral.sCoef (q ^ 3) 1 r n •
        (reverseLongMixedAdjoint q b C D A n * qDivPow (q ^ 3) (r - n) f) := by
  let op := MulOpposite.op (α := B)
  have hs := longMixedAdjoint_right hq h2 h3
    (A := op f) (b := op D) (C := op C) (D := op b) (f := op A)
    (by simpa only [op, MulOpposite.op_mul, MulOpposite.op_smul] using congrArg op H.fD)
    (by simpa only [op, MulOpposite.op_mul, MulOpposite.op_smul, MulOpposite.op_sub,
      MulOpposite.op_pow] using congrArg op H.fB)
    (by simpa only [op, MulOpposite.op_mul, MulOpposite.op_smul, MulOpposite.op_sub,
      MulOpposite.op_pow] using congrArg op H.fC)
    (by simpa only [op, MulOpposite.op_mul, MulOpposite.op_smul, MulOpposite.op_sub,
      MulOpposite.op_add] using congrArg op H.fA)
  have hrev (n : ℕ) : MulOpposite.unop (longMixedAdjoint q (op D) (op C) (op b) (op A) n) =
      reverseLongMixedAdjoint q b C D A n := by
    rcases n with _ | (_ | (_ | n)) <;>
      simp [longMixedAdjoint, reverseLongMixedAdjoint, op, qDivPow]
  have hh := congrArg MulOpposite.unop
    (B2Integral.straighten (pow_ne_zero _ hq) hpi 1 hs r)
  simpa only [show longMixedAdjoint q (op D) (op C) (op b) (op A) 0 = op A from rfl,
    MulOpposite.unop_mul, Finset.unop_sum, MulOpposite.unop_smul, hrev, qDivPow,
    MulOpposite.unop_pow, op, MulOpposite.unop_op] using hh

end LieLean.QuantumGroup.G2Integral
