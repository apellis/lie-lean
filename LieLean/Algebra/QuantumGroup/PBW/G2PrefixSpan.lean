/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.G2DEIntegral
import LieLean.Algebra.QuantumGroup.PBW.G2SquareTransports

/-!
# Integral normalization of the five-root G₂ prefix

The divided monomials in `e,A,b,C,D` span a multiplicatively closed additive group
with Laurent coefficients. The proof uses only the ten pair kernels in this prefix.
It does not use the last-root / second-root straightening formula.

## Main results

* `prefixSpan_mul`: integral normalization of products of five-root divided prefixes.
-/

open Finset
noncomputable section
namespace LieLean.QuantumGroup.G2Integral
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- The ordered five-root divided monomial, with no last-root factor. -/
def prefixMonomial (q : k) (e A b C D : B) (i a j c d : ℕ) : B :=
  qDivPow q i e * qDivPow (q ^ 3) a A * qDivPow q j b *
    qDivPow (q ^ 3) c C * qDivPow q d D

/-- The integral span of the five-root divided prefix. -/
def prefixSpan (q : k) (Λ : Subring k) (e A b C D : B) : AddSubgroup B :=
  AddSubgroup.closure {x | ∃ z ∈ Λ, ∃ i a j c d,
    x = z • prefixMonomial q e A b C D i a j c d}

variable {q : k} {Λ : Subring k} {e A b C D f : B}

lemma prefixMonomial_mem (i a j c d : ℕ) :
    prefixMonomial q e A b C D i a j c d ∈ prefixSpan q Λ e A b C D :=
  AddSubgroup.subset_closure ⟨1, one_mem _, i, a, j, c, d, by rw [one_smul]⟩

lemma smul_mem_prefixSpan {z : k} (hz : z ∈ Λ) {x : B}
    (hx : x ∈ prefixSpan q Λ e A b C D) : z • x ∈ prefixSpan q Λ e A b C D := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, i, a, j, c, d, rfl⟩ := hx
    exact AddSubgroup.subset_closure
      ⟨z * w, mul_mem hz hw, i, a, j, c, d, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

lemma prefixSpan_mul_of_monomial {y : B}
    (hy : ∀ i a j c d, prefixMonomial q e A b C D i a j c d * y ∈
      prefixSpan q Λ e A b C D) {x : B} (hx : x ∈ prefixSpan q Λ e A b C D) :
    x * y ∈ prefixSpan q Λ e A b C D := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, i, a, j, c, d, rfl⟩ := hx
    rw [smul_mul_assoc]
    exact smul_mem_prefixSpan hw (hy i a j c d)
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

variable (hq : q ≠ 0) (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
  (hpi : ∀ n : ℕ, 0 < n → qInt (q ^ 3) n ≠ 0)
  (H : Rel q e A b C D f) (hqΛ : q ∈ Λ) (hiΛ : q⁻¹ ∈ Λ)

include hiΛ in
private lemma inv_cube_mem : (q ^ 3)⁻¹ ∈ Λ := by
  rw [← inv_pow]
  exact pow_mem hiΛ _

include hqi hqΛ hiΛ in
lemma prefixSpan_mul_D (r : ℕ) {x : B} (hx : x ∈ prefixSpan q Λ e A b C D) :
    x * qDivPow q r D ∈ prefixSpan q Λ e A b C D := by
  apply prefixSpan_mul_of_monomial _ hx
  intro i a j c d
  rw [prefixMonomial, mul_assoc, A2Integral.qDivPow_mul_qDivPow D d r
    (A2Integral.qFactorial_ne_zero_of_qInt hqi _), mul_smul_comm]
  exact smul_mem_prefixSpan (A2Integral.qBinomial_mem hqΛ hiΛ _ _)
    (prefixMonomial_mem i a j c (d + r))

include hpi H hqΛ hiΛ in
lemma prefixSpan_mul_C (r : ℕ) {x : B} (hx : x ∈ prefixSpan q Λ e A b C D) :
    x * qDivPow (q ^ 3) r C ∈ prefixSpan q Λ e A b C D := by
  apply prefixSpan_mul_of_monomial _ hx
  intro i a j c d
  rw [prefixMonomial, mul_assoc, Dd_Cd H, mul_smul_comm, ← mul_assoc,
    mul_assoc _ (qDivPow (q ^ 3) c C),
    A2Integral.qDivPow_mul_qDivPow C c r (A2Integral.qFactorial_ne_zero_of_qInt hpi _),
    mul_smul_comm, smul_mul_assoc]
  exact smul_mem_prefixSpan (pow_mem (inv_cube_mem hiΛ) _)
    (smul_mem_prefixSpan (A2Integral.qBinomial_mem (pow_mem hqΛ 3) (inv_cube_mem hiΛ) _ _)
      (prefixMonomial_mem i a j (c + r) d))

include hq hqi hpi H hqΛ hiΛ in
lemma prefixSpan_mul_b (r : ℕ) {x : B} (hx : x ∈ prefixSpan q Λ e A b C D) :
    x * qDivPow q r b ∈ prefixSpan q Λ e A b C D := by
  apply prefixSpan_mul_of_monomial _ hx
  intro i a j c d
  rw [prefixMonomial, mul_assoc, qDivPow_D_mul_qDivPow_b_all hq hqi hpi H, mul_sum]
  refine AddSubgroup.sum_mem _ fun n _ ↦ ?_
  by_cases hn : n ≤ d
  · simp only [shortW, hn, ite_true, mul_smul_comm, smul_smul]
    apply smul_mem_prefixSpan (short_pair_coeff_mem Λ hqΛ hiΛ d r n)
    rw [← mul_assoc, ← mul_assoc]
    apply prefixSpan_mul_D hqi hqΛ hiΛ
    apply prefixSpan_mul_C hpi H hqΛ hiΛ
    rw [mul_assoc, Cd_bd H, mul_smul_comm, ← mul_assoc,
      mul_assoc _ (qDivPow q j b),
      A2Integral.qDivPow_mul_qDivPow b j (r - n)
        (A2Integral.qFactorial_ne_zero_of_qInt hqi _), mul_smul_comm, smul_mul_assoc]
    apply smul_mem_prefixSpan (pow_mem (inv_cube_mem hiΛ) _)
    apply smul_mem_prefixSpan (A2Integral.qBinomial_mem hqΛ hiΛ _ _)
    simpa only [prefixMonomial, qDivPow_zero', mul_one] using
      (prefixMonomial_mem (q := q) (Λ := Λ) (e := e) (A := A) (b := b)
        (C := C) (D := D) i a (j + (r - n)) c 0)
  · simp [shortW, hn]

include hpi H hqΛ hiΛ in
private lemma prefix_three_mul_A (i a j r : ℕ) :
    (qDivPow q i e * qDivPow (q ^ 3) a A * qDivPow q j b) * qDivPow (q ^ 3) r A ∈
      prefixSpan q Λ e A b C D := by
  rw [mul_assoc, bd_Ad H, mul_smul_comm, ← mul_assoc,
    mul_assoc _ (qDivPow (q ^ 3) a A),
    A2Integral.qDivPow_mul_qDivPow A a r (A2Integral.qFactorial_ne_zero_of_qInt hpi _),
    mul_smul_comm, smul_mul_assoc]
  apply smul_mem_prefixSpan (pow_mem (inv_cube_mem hiΛ) _)
  apply smul_mem_prefixSpan (A2Integral.qBinomial_mem (pow_mem hqΛ 3) (inv_cube_mem hiΛ) _ _)
  simpa only [prefixMonomial, qDivPow_zero', mul_one] using
    (prefixMonomial_mem (q := q) (Λ := Λ) (e := e) (A := A) (b := b)
      (C := C) (D := D) i (a + r) j 0 0)

include hq hqi hpi H hqΛ hiΛ in
private lemma prefix_four_mul_A (i a j c r : ℕ) :
    (qDivPow q i e * qDivPow (q ^ 3) a A * qDivPow q j b * qDivPow (q ^ 3) c C) *
      qDivPow (q ^ 3) r A ∈ prefixSpan q Λ e A b C D := by
  rw [mul_assoc, qDivPow_C_mul_qDivPow_A_all hq hqi hpi H, mul_sum]
  refine AddSubgroup.sum_mem _ fun n _ ↦ ?_
  by_cases hn : n ≤ c
  · simp only [longW, hn, ite_true, mul_smul_comm, smul_smul]
    apply smul_mem_prefixSpan (long_pair_coeff_mem Λ hqΛ hiΛ c r n)
    rw [← mul_assoc, ← mul_assoc]
    apply prefixSpan_mul_C hpi H hqΛ hiΛ
    apply prefixSpan_mul_b hq hqi hpi H hqΛ hiΛ
    exact prefix_three_mul_A hpi H hqΛ hiΛ i a j (r - n)
  · simp [longW, hn]

include hq hqi hpi H hqΛ hiΛ in
lemma prefixSpan_mul_A (r : ℕ) {x : B} (hx : x ∈ prefixSpan q Λ e A b C D) :
    x * qDivPow (q ^ 3) r A ∈ prefixSpan q Λ e A b C D := by
  apply prefixSpan_mul_of_monomial _ hx
  intro i a j c d
  have ht := congrArg MulOpposite.unop
    (SquareRel.qDivPow_C_mul_qDivPow_e_field_sum hq hqi hpi H.squareRel_op r d)
  simp only [MulOpposite.unop_mul, unop_sum, MulOpposite.unop_smul,
    qDivPow, MulOpposite.unop_pow, MulOpposite.unop_op] at ht
  change qDivPow q d D * qDivPow (q ^ 3) r A = _ at ht
  rw [prefixMonomial, mul_assoc, ht, mul_sum]
  refine AddSubgroup.sum_mem _ fun n _ ↦ ?_
  rw [mul_sum]
  refine AddSubgroup.sum_mem _ fun v _ ↦ ?_
  rw [mul_smul_comm]
  apply smul_mem_prefixSpan (square_straightening_coeff_mem hq hqi hqΛ hiΛ r d n v)
  change (qDivPow q i e * qDivPow (q ^ 3) a A * qDivPow q j b *
    qDivPow (q ^ 3) c C) * (qDivPow (q ^ 3) v.2.2 A *
      (qDivPow q v.2.1 b * (qDivPow (q ^ 3) v.1 C * qDivPow q (d - n) D))) ∈ _
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  apply prefixSpan_mul_D hqi hqΛ hiΛ
  apply prefixSpan_mul_C hpi H hqΛ hiΛ
  apply prefixSpan_mul_b hq hqi hpi H hqΛ hiΛ
  exact prefix_four_mul_A hq hqi hpi H hqΛ hiΛ i a j c v.2.2

include hqi H hqΛ hiΛ in
private lemma prefix_two_mul_e (i a r : ℕ) :
    (qDivPow q i e * qDivPow (q ^ 3) a A) * qDivPow q r e ∈
      prefixSpan q Λ e A b C D := by
  rw [mul_assoc, Ad_ed H, mul_smul_comm, ← mul_assoc,
    A2Integral.qDivPow_mul_qDivPow e i r (A2Integral.qFactorial_ne_zero_of_qInt hqi _),
    smul_mul_assoc]
  apply smul_mem_prefixSpan (pow_mem (inv_cube_mem hiΛ) _)
  apply smul_mem_prefixSpan (A2Integral.qBinomial_mem hqΛ hiΛ _ _)
  simpa only [prefixMonomial, qDivPow_zero', mul_one] using
    (prefixMonomial_mem (q := q) (Λ := Λ) (e := e) (A := A) (b := b)
      (C := C) (D := D) (i + r) a 0 0 0)

include hq hqi hpi H hqΛ hiΛ in
private lemma prefix_three_mul_e (i a j r : ℕ) :
    (qDivPow q i e * qDivPow (q ^ 3) a A * qDivPow q j b) * qDivPow q r e ∈
      prefixSpan q Λ e A b C D := by
  rw [mul_assoc, qDivPow_b_mul_qDivPow_e_all hq hqi hpi H, mul_sum]
  refine AddSubgroup.sum_mem _ fun n _ ↦ ?_
  by_cases hn : n ≤ j
  · simp only [shortW, hn, ite_true, mul_smul_comm, smul_smul]
    apply smul_mem_prefixSpan (short_pair_coeff_mem Λ hqΛ hiΛ j r n)
    rw [← mul_assoc, ← mul_assoc]
    apply prefixSpan_mul_b hq hqi hpi H hqΛ hiΛ
    apply prefixSpan_mul_A hq hqi hpi H hqΛ hiΛ
    exact prefix_two_mul_e hqi H hqΛ hiΛ i a (r - n)
  · simp [shortW, hn]

include hq hqi hpi H hqΛ hiΛ in
private lemma prefix_four_mul_e (i a j c r : ℕ) :
    (qDivPow q i e * qDivPow (q ^ 3) a A * qDivPow q j b * qDivPow (q ^ 3) c C) *
      qDivPow q r e ∈ prefixSpan q Λ e A b C D := by
  rw [mul_assoc, qDivPow_C_mul_qDivPow_e_field_sum hq hqi hpi H, mul_sum]
  refine AddSubgroup.sum_mem _ fun n _ ↦ ?_
  rw [mul_sum]
  refine AddSubgroup.sum_mem _ fun v _ ↦ ?_
  rw [mul_smul_comm]
  apply smul_mem_prefixSpan (square_straightening_coeff_mem hq hqi hqΛ hiΛ c r n v)
  simp only [← mul_assoc]
  apply prefixSpan_mul_C hpi H hqΛ hiΛ
  apply prefixSpan_mul_b hq hqi hpi H hqΛ hiΛ
  apply prefixSpan_mul_A hq hqi hpi H hqΛ hiΛ
  exact prefix_three_mul_e hq hqi hpi H hqΛ hiΛ i a j (r - n)

include hq hqi hpi H hqΛ hiΛ in
lemma prefixSpan_mul_e (r : ℕ) {x : B} (hx : x ∈ prefixSpan q Λ e A b C D) :
    x * qDivPow q r e ∈ prefixSpan q Λ e A b C D := by
  apply prefixSpan_mul_of_monomial _ hx
  intro i a j c d
  rw [prefixMonomial, mul_assoc, qDivPow_D_mul_qDivPow_e hq hqi hpi H, mul_sum]
  refine AddSubgroup.sum_mem _ fun n _ ↦ ?_
  rw [mul_smul_comm]
  apply smul_mem_prefixSpan (B2Integral.sCoef_mem hqΛ hiΛ d r n)
  rw [deW_sum, mul_sum, mul_sum]
  refine AddSubgroup.sum_mem _ fun v _ ↦ ?_
  rw [mul_smul_comm, mul_smul_comm]
  apply smul_mem_prefixSpan (deCoeff_mem hq hqi Λ hqΛ hiΛ d n v)
  simp only [deMonomial, P3, ← mul_assoc]
  apply prefixSpan_mul_D hqi hqΛ hiΛ
  apply prefixSpan_mul_C hpi H hqΛ hiΛ
  apply prefixSpan_mul_b hq hqi hpi H hqΛ hiΛ
  apply prefixSpan_mul_A hq hqi hpi H hqΛ hiΛ
  exact prefix_four_mul_e hq hqi hpi H hqΛ hiΛ i a j c (r - n)

include hq hqi hpi H hqΛ hiΛ in
/-- Products of five-root divided prefixes normalize with Laurent coefficients.
This is reconstructed from the ten interval kernels, with no assumption of span closure. -/
theorem prefixSpan_mul {x y : B} (hx : x ∈ prefixSpan q Λ e A b C D)
    (hy : y ∈ prefixSpan q Λ e A b C D) : x * y ∈ prefixSpan q Λ e A b C D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨w, hw, i, a, j, c, d, rfl⟩ := hy
    rw [mul_smul_comm]
    apply smul_mem_prefixSpan hw
    simp only [prefixMonomial, ← mul_assoc]
    exact prefixSpan_mul_D hqi hqΛ hiΛ d
      (prefixSpan_mul_C hpi H hqΛ hiΛ c
        (prefixSpan_mul_b hq hqi hpi H hqΛ hiΛ j
          (prefixSpan_mul_A hq hqi hpi H hqΛ hiΛ a
            (prefixSpan_mul_e hq hqi hpi H hqΛ hiΛ i hx))))
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

end LieLean.QuantumGroup.G2Integral
