/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.QBinomialSeries
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Gaussian binomial coefficients at roots of `1`

The Gaussian binomial coefficients `[a; t]` with integer top `a` ([Lus] 1.3.1) over a
commutative ring `R` with a unit `v`, and their values when `v` is a root of `1` ([Lus] 34.1.2).

## Main definitions

* `QuantumGroup.qBinomInt q a t` (over a field) and `QuantumGroup.gaussBinom v a t` (over a
  commutative ring, for a unit `v`): `[a; t]` for `a ∈ ℤ`, `t ∈ ℕ`. For `a ≥ 0` these are the
  coefficients `qBinomial`, `qBinomialU` defined by the Pascal rule, and
  `[a; t] = (-1)^t [-a + t - 1; t]` for `a < 0` ([Lus] 1.3.1).
* `QuantumGroup.qBinomIntSeries q a = Σ_t [a; t] xᵗ`.

## Main results

* `QuantumGroup.qBinomIntSeries_add_one`: `P_{a+1}(x) = (1 + qᵃ x) P_a(q⁻¹ x)` for all `a ∈ ℤ`.
* `QuantumGroup.qBinomInt_add`: the `q`-Vandermonde identity
  `[a + b; t] = Σ_{t' + t'' = t} q^{a t'' - b t'} [a; t'] [b; t'']` for `a, b ∈ ℤ` ([Lus] 1.3.1).
* [Lus] Lemma 34.1.2, for an integral domain `R` and a unit `v` with `v^{2l} = 1` and
  `v^{2t} ≠ 1` for `0 < t < l`:
  (a) `gaussBinom_eq_zero_of_not_dvd`: `[a; t] = 0` if `l ∣ a` and `l ∤ t`;
  (b) `gaussBinom_mul_mul`: `[l a₁; l t₁] = v^{l²(a₁+1)t₁} (a₁ choose t₁)`;
  (c) `gaussBinom_add_mul_add_mul`: `[a₀ + l a₁; t₀ + l t₁] =
  v^{(a₀t₁ - a₁t₀)l + (a₁+1)t₁l²} [a₀; t₀] (a₁ choose t₁)` for `0 ≤ a₀, t₀ < l`;
  (e) `pow_sq_add_eq`: `v^{l² + l} = (-1)^{l+1}`.
  Here `(a₁ choose t₁)` is the binomial coefficient `Ring.choose a₁ t₁` for `a₁ ∈ ℤ`.

## Proof

Generating series. The Pascal rule gives `P_{a+1}(x) = (1 + qᵃ x) P_a(q⁻¹ x)` for all `a ∈ ℤ`,
which yields the `q`-Vandermonde identity `P_{a+b}(x) = P_a(q^{-b} x) P_b(qᵃ x)` by induction on
`b ∈ ℤ` (series with constant term `1` are not zero divisors). At a root of `1` as above,
`P_l(x) = 1 + xˡ` (the middle coefficients `[l; t]` vanish since `[l] = 0`), so with
`ε = vˡ = ±1`, `P_{l(m+1)}(x) = P_{lm}(ε x) (1 + ε^{ml} xˡ)`. The series
`(1 + ε^{l(m+1)} xˡ)^m` (with the binomial series for `m < 0`) satisfies the same recursion, so
`P_{lm}(x) = (1 + ε^{l(m+1)} xˡ)^m`; this gives (a) and (b). Part (c) is the Vandermonde
identity for `a₀ + l a₁`, in which a single term survives (Lusztig's (d)). Lusztig proves (a),
(b) by induction on `a` and `a₁`; the series argument is our own.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.3.1, 34.1.1, 34.1.2.
-/

open PowerSeries Finset

noncomputable section

namespace LieLean.QuantumGroup

/-! ### Integer tops over a field -/

section Field

variable {k : Type*} [Field k] (q : k)

/-- The Gaussian binomial `[a; t]` for `a ∈ ℤ`: `qBinomial q a t` for `a ≥ 0` and
`(-1)^t [-a + t - 1; t]` for `a < 0` ([Lus] 1.3.1). -/
def qBinomInt : ℤ → ℕ → k
  | .ofNat n, t => qBinomial q n t
  | .negSucc n, t => (-1) ^ t * qBinomial q (n + t) t

@[simp] lemma qBinomInt_natCast (n t : ℕ) : qBinomInt q n t = qBinomial q n t := rfl

lemma qBinomInt_negSucc (n t : ℕ) :
    qBinomInt q (Int.negSucc n) t = (-1) ^ t * qBinomial q (n + t) t := rfl

@[simp] lemma qBinomInt_zero_right (a : ℤ) : qBinomInt q a 0 = 1 := by
  cases a <;> simp [qBinomInt]

lemma qBinomInt_inv (a : ℤ) (t : ℕ) : qBinomInt q⁻¹ a t = qBinomInt q a t := by
  cases a <;> simp [qBinomInt, qBinomial_inv]

/-- The generating series `P_a(x) = Σ_t [a; t] xᵗ`. -/
def qBinomIntSeries : ℤ → PowerSeries k
  | .ofNat n => qBinomialSeries q n
  | .negSucc n => qBinomialInvSeries q (n + 1)

@[simp] lemma coeff_qBinomIntSeries (a : ℤ) (t : ℕ) :
    coeff t (qBinomIntSeries q a) = qBinomInt q a t := by
  cases a with
  | ofNat n => simp [qBinomIntSeries, qBinomInt]
  | negSucc n =>
    simp only [qBinomIntSeries, coeff_qBinomialInvSeries, qBinomInt]
    rw [show n + 1 + t - 1 = n + t by omega]

@[simp] lemma qBinomIntSeries_zero : qBinomIntSeries q 0 = 1 := qBinomialSeries_zero

lemma qBinomialInvSeries_inv (h : ℕ) : qBinomialInvSeries q⁻¹ h = qBinomialInvSeries q h := by
  ext n; simp [qBinomial_inv]

variable {q}

lemma rescale_C' (a c : k) : rescale a (C c) = C c := by
  ext n
  cases n <;> simp [coeff_rescale, coeff_C]

/-- `P_{a+1}(x) = (1 + qᵃ x) P_a(q⁻¹ x)` for every `a ∈ ℤ`: the Pascal rule. -/
theorem qBinomIntSeries_add_one (hq : q ≠ 0) (a : ℤ) :
    qBinomIntSeries q (a + 1) = (1 + C (q ^ a) * X) * rescale q⁻¹ (qBinomIntSeries q a) := by
  rcases a with n | _ | n
  · rw [show (Int.ofNat n : ℤ) + 1 = Int.ofNat (n + 1) from rfl]
    simp only [qBinomIntSeries, Int.ofNat_eq_natCast, zpow_natCast]
    exact qBinomialSeries_succ hq n
  · -- `a = -1`
    have h := congrArg (rescale q⁻¹) (qBinomialInvSeries_succ_mul (q := q) 0)
    simp only [qBinomialInvSeries_zero, map_one, map_mul, map_add, rescale_X, pow_zero] at h
    change qBinomIntSeries q 0 =
      (1 + C (q ^ Int.negSucc 0) * X) * rescale q⁻¹ (qBinomialInvSeries q 1)
    rw [qBinomIntSeries_zero, zpow_negSucc, pow_one]
    linear_combination -h
  · have h := congrArg (rescale q⁻¹) (qBinomialInvSeries_succ_mul (q := q⁻¹) (n + 1))
    simp only [qBinomialInvSeries_inv, inv_inv, map_mul, map_add, map_one, rescale_X,
      rescale_C', rescale_rescale, mul_inv_cancel₀ hq, rescale_one,
      RingHom.id_apply] at h
    rw [show Int.negSucc (n + 1) + 1 = Int.negSucc n by omega]
    simp only [qBinomIntSeries]
    have hc : C (q ^ Int.negSucc (n + 1)) = (C (q⁻¹ ^ (n + 1)) * C q⁻¹ : PowerSeries k) := by
      rw [← map_mul, zpow_negSucc, ← pow_succ, inv_pow]
    rw [hc]
    linear_combination -h

lemma rescale_qBinomIntSeries_add_one (hq : q ≠ 0) (a b : ℤ) :
    rescale (q ^ (-(b + 1))) (qBinomIntSeries q a) * rescale (q ^ a) (qBinomIntSeries q (b + 1)) =
      (1 + C (q ^ (a + b)) * X) * rescale q⁻¹
        (rescale (q ^ (-b)) (qBinomIntSeries q a) * rescale (q ^ a) (qBinomIntSeries q b)) := by
  rw [qBinomIntSeries_add_one hq b]
  simp only [map_mul, map_add, map_one, rescale_X, rescale_C', rescale_rescale]
  have e1 : q ^ (-b) * q⁻¹ = q ^ (-(b + 1)) := by rw [neg_add, zpow_add₀ hq, zpow_neg_one]
  have e3 : C (q ^ (a + b)) = (C (q ^ b) * C (q ^ a) : PowerSeries k) := by
    rw [← map_mul, zpow_add₀ hq, mul_comm]
  rw [e1, e3, mul_comm q⁻¹ (q ^ a)]
  ring

/-- The `q`-Vandermonde identity `P_{a+b}(x) = P_a(q^{-b} x) P_b(qᵃ x)` for `a, b ∈ ℤ`. -/
theorem qBinomIntSeries_add (hq : q ≠ 0) (a b : ℤ) :
    qBinomIntSeries q (a + b) =
      rescale (q ^ (-b)) (qBinomIntSeries q a) * rescale (q ^ a) (qBinomIntSeries q b) := by
  induction b using Int.induction_on with
  | zero => simp [rescale_one]
  | succ i ih =>
    rw [← add_assoc, qBinomIntSeries_add_one hq, ih, rescale_qBinomIntSeries_add_one hq]
  | pred i ih =>
    obtain ⟨c, hc⟩ : ∃ c : ℤ, -(i : ℤ) = c + 1 := ⟨-(i : ℤ) - 1, by ring⟩
    rw [show -(i : ℤ) - 1 = c by omega]
    rw [hc, ← add_assoc, qBinomIntSeries_add_one hq, rescale_qBinomIntSeries_add_one hq] at ih
    have hne : (1 + C (q ^ (a + c)) * X : PowerSeries k) ≠ 0 := by
      intro h0
      have := congrArg constantCoeff h0
      simp at this
    have h2 := congrArg (rescale q) (mul_left_cancel₀ hne ih)
    simpa only [rescale_rescale, inv_mul_cancel₀ hq, rescale_one, RingHom.id_apply] using h2

/-- The `q`-Vandermonde identity
`[a + b; t] = Σ_{i ≤ t} q^{a(t-i) - bi} [a; i] [b; t - i]` for `a, b ∈ ℤ` ([Lus] 1.3.1). -/
theorem qBinomInt_add (hq : q ≠ 0) (a b : ℤ) (t : ℕ) :
    qBinomInt q (a + b) t = ∑ i ∈ range (t + 1),
      q ^ (a * (t - i : ℕ) - b * i) * qBinomInt q a i * qBinomInt q b (t - i) := by
  rw [← coeff_qBinomIntSeries, qBinomIntSeries_add hq, coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [coeff_rescale, coeff_qBinomIntSeries]
  have h : (q ^ (-b)) ^ i * (q ^ a) ^ (t - i) = q ^ (a * (t - i : ℕ) - b * i) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hq]
    ring_nf
  linear_combination (qBinomInt q a i * qBinomInt q b (t - i)) * h

end Field

/-! ### Roots of `1` over a field -/

section RootOfUnity

variable {k : Type*} [Field k] {q : k} {l : ℕ}

/-- `[l; t] = 0` for `0 < t < l` if `q^{2l} = 1` and `q^{2t} ≠ 1` for `0 < t < l`. -/
theorem qBinomial_eq_zero_of_root (hq : q ≠ 0) (hl : q ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → q ^ (2 * t) ≠ 1) {t : ℕ} (ht0 : 0 < t) (htl : t < l) :
    qBinomial q l t = 0 := by
  have key := qBinomial_mul_qFactorial_mul_qFactorial (v := q) htl.le
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have hsub : q - q⁻¹ ≠ 0 := by
    intro h
    apply hprim 1 one_pos (by omega)
    rw [sub_eq_zero] at h
    rw [mul_one, sq]
    nth_rewrite 2 [h]
    exact mul_inv_cancel₀ hq
  have hint : qInt q (l' + 1) = 0 := by
    have h := qInt_mul_sub (v := q) (l' + 1)
    have h2 : q⁻¹ ^ (l' + 1) = q ^ (l' + 1) := by
      rw [inv_pow, inv_eq_iff_eq_inv, eq_comm, inv_eq_of_mul_eq_one_left]
      rw [← pow_add, ← two_mul, hl]
    rw [h2, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_left hsub
  rw [qFactorial_succ, hint, zero_mul] at key
  have hf : ∀ n, n < l' + 1 → qFactorial q n ≠ 0 := fun n hn ↦
    qFactorial_ne_zero (v := q) hq fun m hm hmn ↦ hprim m hm (by omega)
  rcases mul_eq_zero.1 key with h | h
  · exact (mul_eq_zero.1 h).resolve_right (hf t htl)
  · exact absurd h (hf _ (by omega))

/-- At a root of `1` as above, `P_l(x) = 1 + xˡ`. -/
theorem qBinomIntSeries_eq_of_root (hq : q ≠ 0) (hl : q ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → q ^ (2 * t) ≠ 1) (hl0 : 0 < l) :
    qBinomIntSeries q l = 1 + X ^ l := by
  ext n
  rw [coeff_qBinomIntSeries, qBinomInt_natCast, map_add, coeff_one, coeff_X_pow]
  rcases Nat.lt_trichotomy n l with h | rfl | h
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hl0.ne]
    · simp [qBinomial_eq_zero_of_root hq hl hprim hn h, hn.ne', h.ne]
  · simp [hl0.ne']
  · simp [qBinomial_eq_zero_of_lt q h, h.ne', show n ≠ 0 by omega]

/-- `q^z = q^{z'}` if `q^{2l} = 1` and `2l ∣ z - z'`. -/
lemma zpow_eq_of_dvd (hq : q ≠ 0) (hl : q ^ (2 * l) = 1) {z z' : ℤ}
    (h : 2 * (l : ℤ) ∣ z - z') : q ^ z = q ^ z' := by
  obtain ⟨w, hw⟩ := h
  rw [show z = z' + 2 * l * w by omega, zpow_add₀ hq, zpow_mul, show (2 * (l : ℤ)) = (2 * l : ℕ)
    by push_cast; ring, zpow_natCast, hl, one_zpow, mul_one]

lemma rescale_expand (c : k) (f : PowerSeries k) (hl0 : 0 < l) :
    rescale c (expand l hl0.ne' f) = expand l hl0.ne' (rescale (c ^ l) f) := by
  ext n
  rw [coeff_rescale, coeff_expand, coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ hl0, coeff_rescale, pow_mul]
  · rw [mul_zero]

/-- The series `(1 + q^{l²(m+1)} xˡ)^m`, with the binomial series for `m < 0`. -/
def rootSeries (q : k) (l : ℕ) (hl0 : 0 < l) (m : ℤ) : PowerSeries k :=
  expand l hl0.ne' (rescale (q ^ ((l : ℤ) ^ 2 * (m + 1))) (binomialSeries k m))

lemma rootSeries_zero (hl0 : 0 < l) : rootSeries q l hl0 0 = 1 := by
  simp [rootSeries]

lemma rescale_one_add_X_pow (c : k) :
    rescale c (1 + X ^ l : PowerSeries k) = 1 + C (c ^ l) * X ^ l := by
  rw [map_add, map_one, map_pow, rescale_X, mul_pow, map_pow]

lemma rootSeries_add_one (hq : q ≠ 0) (hl : q ^ (2 * l) = 1) (hl0 : 0 < l) (m : ℤ) :
    rootSeries q l hl0 (m + 1) =
      rescale (q ^ (-(l : ℤ))) (rootSeries q l hl0 m) *
        (1 + C (q ^ ((l : ℤ) ^ 2 * m)) * X ^ l) := by
  have h1 : binomialSeries k ((1 : ℕ) : ℤ) = (1 + X : PowerSeries k) := by
    rw [binomialSeries_nat, pow_one]
  rw [Nat.cast_one] at h1
  simp only [rootSeries]
  rw [rescale_expand _ _ hl0, binomialSeries_add, h1, map_mul, map_mul, rescale_rescale,
    map_add, map_one, rescale_X, map_add, map_one, map_mul, expand_C, expand_X]
  congr 2
  · congr 1
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq]
    congr 1
    exact zpow_eq_of_dvd hq hl ⟨l, by ring⟩
  · rw [zpow_eq_of_dvd hq hl (z := (l : ℤ) ^ 2 * (m + 1 + 1)) (z' := (l : ℤ) ^ 2 * m)
      ⟨l, by ring⟩]

lemma qBinomIntSeries_mul_add_one (hq : q ≠ 0) (hl : q ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → q ^ (2 * t) ≠ 1) (hl0 : 0 < l) (m : ℤ) :
    qBinomIntSeries q (l * (m + 1)) = rescale (q ^ (-(l : ℤ))) (qBinomIntSeries q (l * m)) *
      (1 + C (q ^ ((l : ℤ) ^ 2 * m)) * X ^ l) := by
  rw [mul_add_one, qBinomIntSeries_add hq, qBinomIntSeries_eq_of_root hq hl hprim hl0,
    rescale_one_add_X_pow, ← zpow_natCast, ← zpow_mul]
  congr 4
  ring_nf

/-- `P_{lm}(x) = (1 + q^{l²(m+1)} xˡ)^m` at a root of `1`. -/
theorem qBinomIntSeries_mul_eq (hq : q ≠ 0) (hl : q ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → q ^ (2 * t) ≠ 1) (hl0 : 0 < l) (m : ℤ) :
    qBinomIntSeries q (l * m) = rootSeries q l hl0 m := by
  induction m using Int.induction_on with
  | zero => rw [mul_zero, qBinomIntSeries_zero, rootSeries_zero]
  | succ i ih =>
    rw [qBinomIntSeries_mul_add_one hq hl hprim hl0, ih, rootSeries_add_one hq hl hl0]
  | pred i ih =>
    obtain ⟨c, hc⟩ : ∃ c : ℤ, -(i : ℤ) = c + 1 := ⟨-(i : ℤ) - 1, by ring⟩
    rw [show -(i : ℤ) - 1 = c by omega]
    rw [hc, qBinomIntSeries_mul_add_one hq hl hprim hl0, rootSeries_add_one hq hl hl0] at ih
    have hne : (1 + C (q ^ ((l : ℤ) ^ 2 * c)) * X ^ l : PowerSeries k) ≠ 0 := by
      intro h0
      have := congrArg constantCoeff h0
      simp [hl0.ne'] at this
    have h2 := congrArg (rescale (q ^ (l : ℤ))) (mul_right_cancel₀ hne ih)
    simpa only [rescale_rescale, ← zpow_add₀ hq, neg_add_cancel, zpow_zero, rescale_one,
      RingHom.id_apply] using h2

/-- [Lus] 34.1.2 (a): `[a; t] = 0` if `l ∣ a` and `l ∤ t`. -/
theorem qBinomInt_eq_zero_of_not_dvd (hq : q ≠ 0) (hl : q ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → q ^ (2 * t) ≠ 1) (hl0 : 0 < l) {a : ℤ} (ha : (l : ℤ) ∣ a)
    {t : ℕ} (ht : ¬ l ∣ t) : qBinomInt q a t = 0 := by
  obtain ⟨m, rfl⟩ := ha
  rw [← coeff_qBinomIntSeries, qBinomIntSeries_mul_eq hq hl hprim hl0, rootSeries,
    coeff_expand_of_not_dvd _ _ _ ht]

/-- [Lus] 34.1.2 (b): `[l a₁; l t₁] = q^{l²(a₁+1)t₁} (a₁ choose t₁)` for `a₁ ∈ ℤ`. -/
theorem qBinomInt_mul_mul (hq : q ≠ 0) (hl : q ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → q ^ (2 * t) ≠ 1) (hl0 : 0 < l) (a₁ : ℤ) (t₁ : ℕ) :
    qBinomInt q (l * a₁) (l * t₁) =
      q ^ ((l : ℤ) ^ 2 * (a₁ + 1) * t₁) * ((Ring.choose a₁ t₁ : ℤ) : k) := by
  rw [← coeff_qBinomIntSeries, qBinomIntSeries_mul_eq hq hl hprim hl0, rootSeries,
    coeff_expand_mul, coeff_rescale, binomialSeries_coeff, ← zpow_natCast, ← zpow_mul,
    zsmul_eq_mul, mul_one]

/-- [Lus] 34.1.2 (d): `[a₀ + l a₁; t₀ + l t₁] = q^{l a₀ t₁ - l a₁ t₀} [a₀; t₀] [l a₁; l t₁]`
for `0 ≤ a₀, t₀ < l`. -/
theorem qBinomInt_add_mul_add_mul_eq (hq : q ≠ 0) (hl : q ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → q ^ (2 * t) ≠ 1) (hl0 : 0 < l) {a₀ t₀ : ℕ} (ha₀ : a₀ < l)
    (ht₀ : t₀ < l) (a₁ : ℤ) (t₁ : ℕ) :
    qBinomInt q (a₀ + l * a₁) (t₀ + l * t₁) =
      q ^ ((l : ℤ) * a₀ * t₁ - l * a₁ * t₀) * qBinomial q a₀ t₀ *
        qBinomInt q (l * a₁) (l * t₁) := by
  rw [qBinomInt_add hq, sum_eq_single t₀]
  · rw [qBinomInt_natCast, show t₀ + l * t₁ - t₀ = l * t₁ by omega]
    congr 3
    push_cast
    ring
  · intro i hi hit
    rcases lt_or_ge a₀ i with h | h
    · rw [qBinomInt_natCast, qBinomial_eq_zero_of_lt q h, mul_zero, zero_mul]
    · rw [qBinomInt_eq_zero_of_not_dvd hq hl hprim hl0 (dvd_mul_right _ _), mul_zero]
      rintro ⟨c, hc⟩
      have hi' : i ≤ t₀ + l * t₁ := Nat.lt_succ_iff.1 (mem_range.1 hi)
      have e : t₀ + l * t₁ = i + l * c := by omega
      have := congrArg (· % l) e
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht₀,
        Nat.mod_eq_of_lt (h.trans_lt ha₀)] at this
      exact hit this.symm
  · intro h
    exact absurd (mem_range.2 (by omega)) h

/-- [Lus] 34.1.2 (c): `[a₀ + l a₁; t₀ + l t₁] = q^{(a₀t₁ - a₁t₀)l + (a₁+1)t₁l²} [a₀; t₀]
(a₁ choose t₁)` for `0 ≤ a₀, t₀ < l`, `a₁ ∈ ℤ`, `t₁ ∈ ℕ`. -/
theorem qBinomInt_add_mul_add_mul (hq : q ≠ 0) (hl : q ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → q ^ (2 * t) ≠ 1) (hl0 : 0 < l) {a₀ t₀ : ℕ} (ha₀ : a₀ < l)
    (ht₀ : t₀ < l) (a₁ : ℤ) (t₁ : ℕ) :
    qBinomInt q (a₀ + l * a₁) (t₀ + l * t₁) =
      q ^ ((a₀ * t₁ - a₁ * t₀) * l + (a₁ + 1) * t₁ * (l : ℤ) ^ 2) * qBinomial q a₀ t₀ *
        ((Ring.choose a₁ t₁ : ℤ) : k) := by
  rw [qBinomInt_add_mul_add_mul_eq hq hl hprim hl0 ha₀ ht₀,
    qBinomInt_mul_mul hq hl hprim hl0]
  have : q ^ ((a₀ * t₁ - a₁ * t₀) * l + (a₁ + 1) * t₁ * (l : ℤ) ^ 2) =
      q ^ ((l : ℤ) * a₀ * t₁ - l * a₁ * t₀) * q ^ ((l : ℤ) ^ 2 * (a₁ + 1) * t₁) := by
    rw [← zpow_add₀ hq]
    ring_nf
  rw [this]
  ring

/-- [Lus] 34.1.2 (e): `q^{l² + l} = (-1)^{l+1}`. -/
theorem pow_sq_add_eq (hl : q ^ (2 * l) = 1) (hprim : ∀ t, 0 < t → t < l → q ^ (2 * t) ≠ 1)
    (hl0 : 0 < l) : q ^ (l ^ 2 + l) = (-1) ^ (l + 1) := by
  have hε : (q ^ l) ^ 2 = 1 := by rw [← pow_mul, mul_comm, hl]
  rw [show l ^ 2 + l = l * (l + 1) by ring, pow_mul]
  rcases Nat.even_or_odd l with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hm : q ^ (m + m) ≠ 1 := by
      rw [← two_mul]; exact hprim m (by omega) (by omega)
    have h1 : q ^ (m + m) = -1 := by
      have : (q ^ (m + m) - 1) * (q ^ (m + m) + 1) = 0 := by linear_combination hε
      exact eq_neg_of_add_eq_zero_left
        ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hm))
    rw [h1]
  · rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul, pow_mul, hε]
    simp

end RootOfUnity

/-! ### Integer tops over a commutative ring -/

section Ring

variable {R : Type*} [CommRing R] (v : Rˣ)

/-- The Gaussian binomial `[a; t]` for `a ∈ ℤ` and a unit `v` of a commutative ring:
`qBinomialU v a t` for `a ≥ 0` and `(-1)^t [-a + t - 1; t]` for `a < 0` ([Lus] 1.3.1). -/
def gaussBinom : ℤ → ℕ → R
  | .ofNat n, t => qBinomialU v n t
  | .negSucc n, t => (-1) ^ t * qBinomialU v (n + t) t

@[simp] lemma gaussBinom_natCast (n t : ℕ) : gaussBinom v n t = qBinomialU v n t := rfl

lemma qBinomialU_map {S : Type*} [CommRing S] (φ : R →+* S) (n t : ℕ) :
    φ (qBinomialU v n t) = qBinomialU (Units.map φ.toMonoidHom v) n t := by
  induction n generalizing t with
  | zero => cases t <;> simp [qBinomialU]
  | succ n ih =>
    cases t with
    | zero => simp [qBinomialU]
    | succ t =>
      simp [qBinomialU, ih, Units.coe_map_inv]

/-- Gaussian binomials commute with ring homomorphisms. -/
lemma map_gaussBinom {S : Type*} [CommRing S] (φ : R →+* S) (a : ℤ) (t : ℕ) :
    φ (gaussBinom v a t) = gaussBinom (Units.map φ.toMonoidHom v) a t := by
  cases a <;> simp [gaussBinom, qBinomialU_map]

/-- Gaussian binomials over a field are `qBinomInt`. -/
lemma map_gaussBinom_field {k : Type*} [Field k] (φ : R →+* k) (a : ℤ) (t : ℕ) :
    φ (gaussBinom v a t) = qBinomInt (φ v) a t := by
  cases a <;> simp [gaussBinom, qBinomInt, map_qBinomialU]

lemma map_units_zpow {k : Type*} [Field k] (φ : R →+* k) (z : ℤ) :
    φ ((v ^ z : Rˣ) : R) = φ v ^ z := by
  cases z with
  | ofNat n => simp
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc, map_units_inv, Units.val_pow_eq_pow_val, map_pow]

end Ring

/-! ### [Lus] 34.1.2 over an integral domain -/

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {v : Rˣ} {l : ℕ}

private lemma root_hyps (hl : (v : R) ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → (v : R) ^ (2 * t) ≠ 1) :
    algebraMap R (FractionRing R) v ≠ 0 ∧ algebraMap R (FractionRing R) v ^ (2 * l) = 1 ∧
      ∀ t, 0 < t → t < l → algebraMap R (FractionRing R) v ^ (2 * t) ≠ 1 := by
  have hinj := IsFractionRing.injective R (FractionRing R)
  refine ⟨(v.isUnit.map _).ne_zero, by rw [← map_pow, hl, map_one], fun t h0 ht h ↦ ?_⟩
  exact hprim t h0 ht (hinj (by rw [map_pow, h, map_one]))

/-- [Lus] 34.1.2 (a): if `v^{2l} = 1` and `v^{2t} ≠ 1` for `0 < t < l`, then `[a; t] = 0` for
`l ∣ a`, `l ∤ t`. -/
theorem gaussBinom_eq_zero_of_not_dvd (hl : (v : R) ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → (v : R) ^ (2 * t) ≠ 1) (hl0 : 0 < l) {a : ℤ}
    (ha : (l : ℤ) ∣ a) {t : ℕ} (ht : ¬ l ∣ t) : gaussBinom v a t = 0 := by
  obtain ⟨h0, h1, h2⟩ := root_hyps hl hprim
  apply IsFractionRing.injective R (FractionRing R)
  rw [map_gaussBinom_field, map_zero, qBinomInt_eq_zero_of_not_dvd h0 h1 h2 hl0 ha ht]

/-- [Lus] 34.1.2 (b): `[l a₁; l t₁] = v^{l²(a₁+1)t₁} (a₁ choose t₁)`. -/
theorem gaussBinom_mul_mul (hl : (v : R) ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → (v : R) ^ (2 * t) ≠ 1) (hl0 : 0 < l) (a₁ : ℤ) (t₁ : ℕ) :
    gaussBinom v (l * a₁) (l * t₁) =
      ((v ^ ((l : ℤ) ^ 2 * (a₁ + 1) * t₁) : Rˣ) : R) * ((Ring.choose a₁ t₁ : ℤ) : R) := by
  obtain ⟨h0, h1, h2⟩ := root_hyps hl hprim
  apply IsFractionRing.injective R (FractionRing R)
  rw [map_gaussBinom_field, map_mul, map_units_zpow, map_intCast,
    qBinomInt_mul_mul h0 h1 h2 hl0]

/-- [Lus] 34.1.2 (c): `[a₀ + l a₁; t₀ + l t₁] = v^{(a₀t₁ - a₁t₀)l + (a₁+1)t₁l²} [a₀; t₀]
(a₁ choose t₁)` for `0 ≤ a₀, t₀ < l`. -/
theorem gaussBinom_add_mul_add_mul (hl : (v : R) ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → (v : R) ^ (2 * t) ≠ 1) (hl0 : 0 < l) {a₀ t₀ : ℕ}
    (ha₀ : a₀ < l) (ht₀ : t₀ < l) (a₁ : ℤ) (t₁ : ℕ) :
    gaussBinom v (a₀ + l * a₁) (t₀ + l * t₁) =
      ((v ^ ((a₀ * t₁ - a₁ * t₀) * l + (a₁ + 1) * t₁ * (l : ℤ) ^ 2) : Rˣ) : R) *
        gaussBinom v a₀ t₀ * ((Ring.choose a₁ t₁ : ℤ) : R) := by
  obtain ⟨h0, h1, h2⟩ := root_hyps hl hprim
  apply IsFractionRing.injective R (FractionRing R)
  rw [map_gaussBinom_field, map_mul, map_mul, map_units_zpow, map_intCast,
    map_gaussBinom_field, qBinomInt_natCast, qBinomInt_add_mul_add_mul h0 h1 h2 hl0 ha₀ ht₀]

/-- [Lus] 34.1.2 (e): `v^{l² + l} = (-1)^{l+1}`. -/
theorem pow_sq_add_eq_of_root (hl : (v : R) ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → (v : R) ^ (2 * t) ≠ 1) (hl0 : 0 < l) :
    (v : R) ^ (l ^ 2 + l) = (-1) ^ (l + 1) := by
  obtain ⟨_, h1, h2⟩ := root_hyps hl hprim
  apply IsFractionRing.injective R (FractionRing R)
  rw [map_pow, pow_sq_add_eq h1 h2 hl0, map_pow, map_neg, map_one]

end Domain

end LieLean.QuantumGroup
