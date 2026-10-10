/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.G2SquareIntegral

/-!
# Transport of the integral G₂ square kernel

The square kernel needs only five relations on a four-root interval. The shift to
`b, C, D, f` and the opposite interval `D, C, b, A` satisfy those relations at the
same parameter `q`. Neither construction asserts a symmetry of all six roots.

## Main results

* `qDivPow_f_mul_qDivPow_b_mem`: arbitrary divided powers of `f` and `b`.
* `qDivPow_D_mul_qDivPow_A_mem`: arbitrary divided powers of `D` and `A`.

Both conclusions use the original six-root ordered integral span. The proofs are
reconstructed directly from the normalized relations and the square coefficient theorem;
no multiplicative closure of the span is assumed.
-/

open Finset MulOpposite

noncomputable section

namespace LieLean.QuantumGroup.G2Integral

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]
  {q : k} {e A b C D f : B} {Λ : Subring k}

/-- Shift the square interval two places in the normalized root order. -/
theorem Rel.squareRel_shift (H : Rel q e A b C D f) : SquareRel q b C D f :=
  ⟨H.CB, H.DB, H.DC, H.fB, H.fD⟩

/-- Reverse the middle four roots in the opposite algebra. The parameter stays `q`.
The five fields are respectively `DC`, `DB`, `CB`, `DA`, and `BA`. -/
theorem Rel.squareRel_op (H : Rel q e A b C D f) :
    SquareRel q (op D) (op C) (op b) (op A) where
  Ae := by simpa only [op_mul, op_smul] using congrArg op H.DC
  Be := by simpa only [op_mul, op_smul, op_sub] using congrArg op H.DB
  BA := by simpa only [op_mul, op_smul] using congrArg op H.CB
  Ce := by simpa only [op_mul, op_smul, op_sub, op_pow] using congrArg op H.DA
  CB := by simpa only [op_mul, op_smul] using congrArg op H.BA

/-- Each coefficient of the square straightening sum is Laurent integral. -/
lemma square_straightening_coeff_mem (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ) (s r n : ℕ) (i : SquareIndex) :
    B2Integral.sCoefParam q 1 r n * squareCoeff q s n i ∈ Λ := by
  apply Λ.mul_mem _ (squareCoeff_mem hq hqi Λ hqΛ hqiΛ s n i)
  simpa only [B2Integral.sCoefParam, one_pow, mul_one] using
    Λ.mul_mem (Λ.pow_mem (Λ.neg_mem Λ.one_mem) n) (Λ.pow_mem hqiΛ (n * (r - n)))

/-- Arbitrary `f,b` divided powers belong to the original ordered integral span.
This is the shifted square kernel, not a closure argument. -/
theorem qDivPow_f_mul_qDivPow_b_mem (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ) (s r : ℕ) :
    qDivPow (q ^ 3) s f * qDivPow q r b ∈ orderedSpan q Λ e A b C D f := by
  rw [SquareRel.qDivPow_C_mul_qDivPow_e_field_sum hq hqi hpi H.squareRel_shift]
  refine AddSubgroup.sum_mem _ fun n _ ↦ AddSubgroup.sum_mem _ fun i _ ↦ ?_
  apply smul_mem_orderedSpan (square_straightening_coeff_mem hq hqi hqΛ hqiΛ s r n i)
  simpa [M6, M5, P3, qDivPow_zero', mul_assoc] using
    M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
      (D := D) (f := f) 0 0 (r - n) i.1 i.2.1 i.2.2

private lemma unop_qDivPow (t : k) (n : ℕ) (x : B) :
    unop (qDivPow t n (op x)) = qDivPow t n x := by
  simp only [qDivPow, unop_smul, unop_pow, unop_op]

/-- Arbitrary `D,A` divided powers belong to the original ordered integral span.
Opposite multiplication reverses the square formula and swaps its two external exponents. -/
theorem qDivPow_D_mul_qDivPow_A_mem (hq : q ≠ 0)
    (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
    (H : Rel q e A b C D f) (hqΛ : q ∈ Λ) (hqiΛ : q⁻¹ ∈ Λ) (s r : ℕ) :
    qDivPow q s D * qDivPow (q ^ 3) r A ∈ orderedSpan q Λ e A b C D f := by
  have h := congrArg unop
    (SquareRel.qDivPow_C_mul_qDivPow_e_field_sum hq hqi hpi H.squareRel_op r s)
  simp only [unop_mul, unop_sum, unop_smul, unop_qDivPow] at h
  rw [h]
  refine AddSubgroup.sum_mem _ fun n _ ↦ AddSubgroup.sum_mem _ fun i _ ↦ ?_
  apply smul_mem_orderedSpan (square_straightening_coeff_mem hq hqi hqΛ hqiΛ r s n i)
  simpa [M6, M5, P3, qDivPow_zero', mul_assoc] using
    M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b) (C := C)
      (D := D) (f := f) 0 i.2.2 i.2.1 i.1 (s - n) 0

end LieLean.QuantumGroup.G2Integral
