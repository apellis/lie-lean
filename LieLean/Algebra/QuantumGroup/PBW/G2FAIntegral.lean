/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.G2PrefixSpan
import LieLean.Algebra.QuantumGroup.PBW.G2ExtremeAdjoint

/-!
# Arbitrary integral G₂ last-root / second-root products

The extreme adjoint identity expresses `A^(r)` as integral `e,f,e` sandwiches.
Straighten `f,e` twice, merging equal last-root blocks between the expansions.
Only products of five-root prefixes need normalization. This reconstructed proof
uses no independence or multiplicative-closure hypothesis for the six-root span.

## Main results

* `qDivPow_f_mul_qDivPow_A_mem_all`: actual ordered-span membership for all exponents.
-/

open Finset
noncomputable section
namespace LieLean.QuantumGroup.G2Integral
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]
  {q : k} {Λ : Subring k} {e A b C D f : B}

lemma prefixSpan_mul_f_mem (l : ℕ) {x : B} (hx : x ∈ prefixSpan q Λ e A b C D) :
    x * qDivPow (q ^ 3) l f ∈ orderedSpan q Λ e A b C D f := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, i, a, j, c, d, rfl⟩ := hx
    rw [smul_mul_assoc]
    apply smul_mem_orderedSpan hw
    simpa only [prefixMonomial, M6, M5, P3, mul_assoc] using
      (M6_mem_orderedSpan (q := q) (Λ := Λ) (e := e) (A := A) (b := b)
        (C := C) (D := D) (f := f) i a j c d l)
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

variable (hq : q ≠ 0) (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
  (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
  (H : Rel q e A b C D f) (hqΛ : q ∈ Λ) (hiΛ : q⁻¹ ∈ Λ)

include hq hqi hpi H hqΛ hiΛ in
lemma prefixSpan_mul_orderedSpan {x y : B} (hx : x ∈ prefixSpan q Λ e A b C D)
    (hy : y ∈ orderedSpan q Λ e A b C D f) :
    x * y ∈ orderedSpan q Λ e A b C D f := by
  apply mul_mem_orderedSpan_of_gen _ hy
  intro i a j c d l
  have ht : M6 q e A b C D f i a j c d l =
      prefixMonomial q e A b C D i a j c d * qDivPow (q ^ 3) l f := by
    simp only [M6, M5, P3, prefixMonomial, mul_assoc]
  rw [ht, ← mul_assoc]
  exact prefixSpan_mul_f_mem l
    (prefixSpan_mul hq hqi hpi H hqΛ hiΛ hx (prefixMonomial_mem i a j c d))

include hpi hqΛ hiΛ in
lemma orderedSpan_mul_f (r : ℕ) {x : B} (hx : x ∈ orderedSpan q Λ e A b C D f) :
    x * qDivPow (q ^ 3) r f ∈ orderedSpan q Λ e A b C D f := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, i, a, j, c, d, l, rfl⟩ := hx
    rw [smul_mul_assoc]
    apply smul_mem_orderedSpan hw
    have ht : M6 q e A b C D f i a j c d l =
        prefixMonomial q e A b C D i a j c d * qDivPow (q ^ 3) l f := by
      simp only [M6, M5, P3, prefixMonomial, mul_assoc]
    rw [ht, mul_assoc, A2Integral.qDivPow_mul_qDivPow f l r
      (A2Integral.qFactorial_ne_zero_of_qInt hpi _), mul_smul_comm]
    have hp : (q ^ 3)⁻¹ ∈ Λ := by simpa only [← inv_pow] using pow_mem hiΛ 3
    exact smul_mem_orderedSpan (A2Integral.qBinomial_mem (pow_mem hqΛ 3) hp _ _)
      (prefixSpan_mul_f_mem (l + r) (prefixMonomial_mem i a j c d))
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

include hq hqi hpi H hqΛ hiΛ in
lemma orderedSpan_mul_e (r : ℕ) {x : B} (hx : x ∈ orderedSpan q Λ e A b C D f) :
    x * qDivPow q r e ∈ orderedSpan q Λ e A b C D f := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, i, a, j, c, d, l, rfl⟩ := hx
    rw [smul_mul_assoc]
    apply smul_mem_orderedSpan hw
    have ht : M6 q e A b C D f i a j c d l =
        prefixMonomial q e A b C D i a j c d * qDivPow (q ^ 3) l f := by
      simp only [M6, M5, P3, prefixMonomial, mul_assoc]
    rw [ht, mul_assoc]
    exact prefixSpan_mul_orderedSpan hq hqi hpi H hqΛ hiΛ (prefixMonomial_mem i a j c d)
      (qDivPow_f_mul_qDivPow_e_mem_all hq hqi hpi H hqΛ hiΛ r l)
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

include hq hqi hpi H hqΛ hiΛ in
/-- Every actual `f^(s) A^(r)` belongs to the ordered integral G₂ span.
The hypotheses include `q = 1` and `q = -1` whenever the positive quantum integers
are nonzero; no quantum integer is inverted in the coefficient subring. -/
theorem qDivPow_f_mul_qDivPow_A_mem_all (s r : ℕ) :
    qDivPow (q ^ 3) s f * qDivPow (q ^ 3) r A ∈ orderedSpan q Λ e A b C D f := by
  rw [qDivPow_A_eq_sum hq hqi hpi H, mul_sum]
  refine AddSubgroup.sum_mem _ fun j _ ↦ ?_
  rw [mul_smul_comm]
  apply smul_mem_orderedSpan
    (mul_mem (pow_mem (neg_mem (one_mem Λ)) j) (pow_mem hiΛ j))
  simp only [← mul_assoc]
  exact orderedSpan_mul_e hq hqi hpi H hqΛ hiΛ j
    (orderedSpan_mul_f hpi hqΛ hiΛ r
      (qDivPow_f_mul_qDivPow_e_mem_all hq hqi hpi H hqΛ hiΛ (3 * r - j) s))

end LieLean.QuantumGroup.G2Integral
