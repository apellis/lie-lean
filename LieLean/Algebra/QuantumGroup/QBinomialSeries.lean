/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.QBinomial
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Generating series of quantum binomial coefficients

Let `k` be a field and `q ∈ k`, `q ≠ 0`. With the symmetric quantum binomial coefficients
`[h, c] = [h, c]_q` (`QuantumGroup.qBinomial`) we consider the power series
* `P_h(x) = Σ_c [h, c] x^c` (`QuantumGroup.qBinomialSeries`), which is the product
  `Π_{t < h} (1 + q^{h-1-2t} x)`; we only use the functional equation
  `P_{h+1}(x) = (1 + q^h x) P_h(q⁻¹ x)` (`QuantumGroup.qBinomialSeries_succ`), which is the Pascal
  rule defining `[h, c]`;
* `Q_h(x) = Σ_c (-1)^c [h + c - 1, c] x^c` (`QuantumGroup.qBinomialInvSeries`), which satisfies
  `Q_{h+1}(x) (1 + q^h x) = Q_h(q⁻¹ x)` and hence `P_h Q_h = 1`
  (`QuantumGroup.qBinomialSeries_mul_qBinomialInvSeries`).

From these we derive the two identities needed to evaluate Lusztig's symmetries on the simple
`U_q(𝔰𝔩₂)`-modules ([Lus] 5.2.2, [Jan] 8.3): for `h, j ∈ ℕ`,
* `Σ_{c ≤ j} (-1)^c (q^{1-a})^c [h+c, c] [h+a, j-c] = 0` if `1 ≤ a ≤ j`
  (`QuantumGroup.sum_qBinomial_mul_qBinomial_eq_zero`);
* `Σ_{c ≤ j} (-1)^c q^c [h+c, c] [h, j-c] = (-q^{h+1})^j`
  (`QuantumGroup.sum_qBinomial_mul_qBinomial_zero`).

In terms of series: the left hand sides are the coefficients of `x^j` in
`Φ_a(x) = Q_{h+1}(q^{1-a} x) P_{h+a}(x)`, and `Φ_{a+1}(x) = (1 + q^{h+a} x) Φ_a(q⁻¹ x)`,
`Φ_1 = 1`; so `Φ_a` is a polynomial of degree `< a` for `a ≥ 1`, and `Φ_0 = 1/(1 + q^{h+1} x)`.
The arguments are our own; the identities are standard `q`-analogues of
`(1 + x)^{-h-1} (1 + x)^{h+a} = (1 + x)^{a-1}`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §1.3, §5.2.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, §0.2, §8.3.
-/

open PowerSeries Finset

namespace LieLean.QuantumGroup

variable {k : Type*} [Field k] (q : k)

/-- `P_h(x) = Σ_c [h, c]_q x^c`. -/
noncomputable def qBinomialSeries (h : ℕ) : PowerSeries k := mk (qBinomial q h)

/-- `Q_h(x) = Σ_c (-1)^c [h + c - 1, c]_q x^c`, the inverse of `P_h`. -/
noncomputable def qBinomialInvSeries (h : ℕ) : PowerSeries k :=
  mk fun c ↦ (-1) ^ c * qBinomial q (h + c - 1) c

@[simp] lemma coeff_qBinomialSeries (h n : ℕ) : coeff n (qBinomialSeries q h) = qBinomial q h n :=
  coeff_mk _ _

@[simp] lemma coeff_qBinomialInvSeries (h n : ℕ) :
    coeff n (qBinomialInvSeries q h) = (-1) ^ n * qBinomial q (h + n - 1) n :=
  coeff_mk _ _

variable {q}

lemma coeff_zero_one_add_mul (c : k) (φ : PowerSeries k) :
    coeff 0 ((1 + C c * X) * φ) = coeff 0 φ := by
  rw [add_mul, one_mul, map_add, mul_assoc, coeff_C_mul, coeff_zero_X_mul, mul_zero, add_zero]

lemma coeff_succ_one_add_mul (c : k) (φ : PowerSeries k) (n : ℕ) :
    coeff (n + 1) ((1 + C c * X) * φ) = coeff (n + 1) φ + c * coeff n φ := by
  rw [add_mul, one_mul, map_add, mul_assoc, coeff_C_mul, coeff_succ_X_mul]

/-- `P_{h+1}(x) = (1 + q^h x) P_h(q⁻¹ x)`: the Pascal rule. -/
theorem qBinomialSeries_succ (hq : q ≠ 0) (h : ℕ) :
    qBinomialSeries q (h + 1) = (1 + C (q ^ h) * X) * rescale q⁻¹ (qBinomialSeries q h) := by
  ext n
  cases n with
  | zero => rw [coeff_zero_one_add_mul, coeff_rescale]; simp
  | succ n =>
    rw [coeff_succ_one_add_mul, coeff_qBinomialSeries, coeff_rescale, coeff_rescale,
      coeff_qBinomialSeries, coeff_qBinomialSeries, qBinomial_succ_succ]
    congr 1
    rcases le_or_gt n h with hn | hn
    · rw [← mul_assoc, inv_pow, pow_sub₀ q hq hn]
    · rw [qBinomial_eq_zero_of_lt q hn]
      ring

/-- `Q_{h+1}(x) (1 + q^h x) = Q_h(q⁻¹ x)`: again the Pascal rule. -/
theorem qBinomialInvSeries_succ_mul (h : ℕ) :
    qBinomialInvSeries q (h + 1) * (1 + C (q ^ h) * X) = rescale q⁻¹ (qBinomialInvSeries q h) := by
  rw [mul_comm]
  ext n
  cases n with
  | zero => rw [coeff_zero_one_add_mul, coeff_rescale]; simp
  | succ n =>
    rw [coeff_succ_one_add_mul, coeff_qBinomialInvSeries, coeff_qBinomialInvSeries, coeff_rescale,
      coeff_qBinomialInvSeries, show h + 1 + (n + 1) - 1 = (h + n) + 1 by omega,
      show h + 1 + n - 1 = h + n by omega, show h + (n + 1) - 1 = h + n by omega,
      qBinomial_succ_succ, show h + n - n = h by omega]
    ring

@[simp] lemma qBinomialSeries_zero : qBinomialSeries q 0 = 1 := by
  ext n
  cases n <;> simp

@[simp] lemma qBinomialInvSeries_zero : qBinomialInvSeries q 0 = 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp

/-- `P_h Q_h = 1`. -/
theorem qBinomialSeries_mul_qBinomialInvSeries (hq : q ≠ 0) (h : ℕ) :
    qBinomialSeries q h * qBinomialInvSeries q h = 1 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [qBinomialSeries_succ hq, show ∀ a b c : PowerSeries k, a * b * c = b * (c * a) from
      fun a b c ↦ by ring, qBinomialInvSeries_succ_mul, ← map_mul, ih, map_one]

/-- The series `Φ_a(x) = Q_{h+1}(q^{1-a} x) P_{h+a}(x)`. -/
noncomputable def qBinomialPhi (q : k) (h a : ℕ) : PowerSeries k :=
  rescale (q * q⁻¹ ^ a) (qBinomialInvSeries q (h + 1)) * qBinomialSeries q (h + a)

lemma qBinomialPhi_one (hq : q ≠ 0) (h : ℕ) : qBinomialPhi q h 1 = 1 := by
  rw [qBinomialPhi, pow_one, mul_inv_cancel₀ hq, rescale_one, RingHom.id_apply, mul_comm,
    qBinomialSeries_mul_qBinomialInvSeries hq]

lemma qBinomialPhi_succ (hq : q ≠ 0) (h a : ℕ) :
    qBinomialPhi q h (a + 1) = (1 + C (q ^ (h + a)) * X) * rescale q⁻¹ (qBinomialPhi q h a) := by
  rw [qBinomialPhi, qBinomialPhi, ← add_assoc, qBinomialSeries_succ hq, map_mul,
    rescale_rescale, pow_succ, ← mul_assoc]
  ring_nf

lemma coeff_qBinomialPhi (h a j : ℕ) :
    coeff j (qBinomialPhi q h a) = ∑ c ∈ range (j + 1),
      (-1) ^ c * (q * q⁻¹ ^ a) ^ c * qBinomial q (h + c) c * qBinomial q (h + a) (j - c) := by
  rw [qBinomialPhi, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun c _ ↦ ?_
  simp only [coeff_rescale, coeff_qBinomialInvSeries, coeff_qBinomialSeries,
    show h + 1 + c - 1 = h + c by omega]
  ring

lemma coeff_qBinomialPhi_eq_zero (hq : q ≠ 0) (h : ℕ) {a j : ℕ} (ha : 1 ≤ a) (hj : a ≤ j) :
    coeff j (qBinomialPhi q h a) = 0 := by
  induction a, ha using Nat.le_induction generalizing j with
  | base =>
    rw [qBinomialPhi_one hq]
    simp [coeff_one, show j ≠ 0 by omega]
  | succ a ha ih =>
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [qBinomialPhi_succ hq, coeff_succ_one_add_mul, coeff_rescale, coeff_rescale,
      ih (by omega), ih (by omega)]
    ring

lemma coeff_qBinomialPhi_zero (hq : q ≠ 0) (h j : ℕ) :
    coeff j (qBinomialPhi q h 0) = (-q ^ (h + 1)) ^ j := by
  -- `(1 + q^{h+1} x) Φ₀(x) = 1`, obtained by rescaling `Φ₁ = (1 + q^h x) Φ₀(q⁻¹ x)` by `q`.
  have key : ∀ n, coeff (n + 1) (qBinomialPhi q h 0) + q ^ (h + 1) *
      coeff n (qBinomialPhi q h 0) = 0 := by
    intro n
    have e := congrArg (coeff (n + 1)) (qBinomialPhi_succ hq h 0)
    rw [zero_add, qBinomialPhi_one hq, coeff_succ_one_add_mul, coeff_rescale, coeff_rescale]
      at e
    simp only [coeff_one, Nat.add_one_ne_zero, ↓reduceIte] at e
    have hq' : q⁻¹ ^ (n + 1) ≠ 0 := pow_ne_zero _ (inv_ne_zero hq)
    refine (mul_eq_zero.1 ?_).resolve_left hq'
    have hh : q⁻¹ ^ (n + 1) * q ^ (h + 1) = q ^ h * q⁻¹ ^ n := by
      rw [pow_succ, pow_succ]
      field_simp
    linear_combination -e + coeff n (qBinomialPhi q h 0) * hh
  have h0 : coeff 0 (qBinomialPhi q h 0) = 1 := by
    rw [coeff_qBinomialPhi]
    simp
  induction j with
  | zero => simpa using h0
  | succ n ih => linear_combination key n - q ^ (h + 1) * ih

/-- `Σ_{c ≤ j} (-1)^c (q^{1-a})^c [h+c, c] [h+a, j-c] = 0` for `1 ≤ a ≤ j`. -/
theorem sum_qBinomial_mul_qBinomial_eq_zero (hq : q ≠ 0) (h : ℕ) {a j : ℕ} (ha : 1 ≤ a)
    (hj : a ≤ j) : ∑ c ∈ range (j + 1),
      (-1) ^ c * (q * q⁻¹ ^ a) ^ c * qBinomial q (h + c) c * qBinomial q (h + a) (j - c) = 0 := by
  rw [← coeff_qBinomialPhi, coeff_qBinomialPhi_eq_zero hq h ha hj]

/-- `Σ_{c ≤ j} (-1)^c q^c [h+c, c] [h, j-c] = (-q^{h+1})^j`. -/
theorem sum_qBinomial_mul_qBinomial_zero (hq : q ≠ 0) (h j : ℕ) : ∑ c ∈ range (j + 1),
    (-1) ^ c * q ^ c * qBinomial q (h + c) c * qBinomial q h (j - c) = (-q ^ (h + 1)) ^ j := by
  rw [← coeff_qBinomialPhi_zero hq h j, coeff_qBinomialPhi]
  simp

end LieLean.QuantumGroup
