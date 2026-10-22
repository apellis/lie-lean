/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.RootOfUnity.GaussBinomial

/-!
# Products and sums of Gaussian binomials at roots of `1`

[Lus] 34.1.3 and 34.1.4: two identities for Gaussian binomial coefficients at a root of `1`
used in the construction of the quantum Frobenius map ([Lus] 35.1).

## Main results

* `QuantumGroup.sum_neg_one_pow_qBinomial`: the partial alternating sums
  `Σ_{s=0}^{k} (-1)^s q^{-sn} [n+1; s] = (-1)^k q^{-k(n+1)} [n; k]`, for any `q ≠ 0`. For
  `k = n + 1` this is the vanishing of [Lus] 1.3.4.
* `QuantumGroup.qFactorial_mul_eq`: `[lp]^! = (∏_{j=1}^{p} [lj; l]) ([l]^!)^p`, so that
  `∏_{j=1}^{p} [lj; l]` is the element `[lp]^!/([l]^!)^p` of [Lus] 34.1.3.
* [Lus] 34.1.3 (a), for a unit `v` of an integral domain with `v^{2l} = 1` and `v^{2t} ≠ 1`
  for `0 < t < l` (`prod_qBinomialU_mul_root`):
  `∏_{j=1}^{p} [lj; l] = p! v^{l² p(p-1)/2}`.
* [Lus] 34.1.4 (a), same hypotheses, `0 ≤ r ≤ a < l` (`sum_qBinomialU_root`):
  `Σ_{q=0}^{l-a-1} (-1)^{l-r+1+q} v^{-(l-r)(a-l+1+q)+q} [l-r; q] = v^{l(a-r)} [a; r]`.
* [Lus] 35.1.5 (a), same hypotheses (`gaussBinom_mul_mul_eq_pow`):
  `[l a₁; l t₁]_v = [a₁; t₁]_{v^{l²}}`.

## Proof

34.1.3 (a) follows from 34.1.2 (b), as in [Lus]. For 34.1.4 (a), the partial alternating sums
above telescope by the Pascal rule (our argument; Lusztig instead completes the sum by 1.3.4 and
evaluates the complementary part with 34.1.2 (c)). This turns the left hand side into
`(-1)^{a-r} [l-r-1; a-r]`, and `[l-r-1; a-r] = v^{l(a-r)} [-r-1; a-r] = (-1)^{a-r} v^{l(a-r)}
[a; r]` by the `q`-Vandermonde identity, since `[l; i] = 0` for `0 < i < l`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.3.4, 34.1.2–34.1.4, 35.1.5.
-/

open Finset

noncomputable section

namespace LieLean.QuantumGroup

section Field

variable {k : Type*} [Field k] {q : k}

/-- The partial alternating sums `Σ_{s=0}^{k} (-1)^s q^{-sn} [n+1; s] = (-1)^k q^{-k(n+1)}
[n; k]` (for `k = n + 1` this is [Lus] 1.3.4). -/
theorem sum_neg_one_pow_qBinomial (hq : q ≠ 0) (n m : ℕ) :
    ∑ s ∈ range (m + 1), (-1) ^ s * q ^ (-((s : ℤ) * n)) * qBinomial q (n + 1) s =
      (-1) ^ m * q ^ (-((m : ℤ) * (n + 1))) * qBinomial q n m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, qBinomial_succ_succ]
    rcases le_or_gt m n with h | h
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [show m + c - m = c by omega, inv_pow, ← zpow_natCast q c, ← zpow_natCast q (m + 1),
        ← zpow_neg]
      have e1 : q ^ (-(((m + 1 : ℕ) : ℤ) * ((m + c : ℕ) : ℤ))) * q ^ (-((m + 1 : ℕ) : ℤ)) =
          q ^ (-(((m + 1 : ℕ) : ℤ) * ((m + c : ℕ) + 1 : ℤ))) := by
        rw [← zpow_add₀ hq]; push_cast; ring_nf
      have e2 : q ^ (-(((m + 1 : ℕ) : ℤ) * ((m + c : ℕ) : ℤ))) * q ^ (c : ℤ) =
          q ^ (-((m : ℤ) * ((m + c : ℕ) + 1 : ℤ))) := by
        rw [← zpow_add₀ hq]; push_cast; ring_nf
      rw [pow_succ]
      linear_combination (-(-1) ^ m * qBinomial q (m + c) (m + 1)) * e1 +
        (-(-1) ^ m * qBinomial q (m + c) m) * e2
    · rw [qBinomial_eq_zero_of_lt q h, qBinomial_eq_zero_of_lt q (by omega : n < m + 1)]
      ring

/-- `[lp]^! = (∏_{j=1}^{p} [lj; l]) ([l]^!)^p`: the product `∏_{j=1}^{p} [lj; l]` is the element
`[lp]^!/([l]^!)^p` of [Lus] 34.1.3. -/
theorem qFactorial_mul_eq (q : k) (l p : ℕ) :
    qFactorial q (l * p) =
      (∏ j ∈ range p, qBinomial q (l * (j + 1)) l) * qFactorial q l ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h := qBinomial_mul_qFactorial_mul_qFactorial (v := q)
      (show l ≤ l * (p + 1) from Nat.le_mul_of_pos_right l (Nat.succ_pos p))
    rw [show l * (p + 1) - l = l * p by rw [Nat.mul_succ, Nat.add_sub_cancel], ih] at h
    rw [← h, prod_range_succ, pow_succ]
    ring

variable {l : ℕ}

/-- [Lus] 34.1.3 (a) over a field: `∏_{j=1}^{p} [lj; l] = p! q^{l² p(p-1)/2}` if `q^{2l} = 1`
and `q^{2t} ≠ 1` for `0 < t < l`. -/
theorem prod_qBinomial_mul_root (hq : q ≠ 0) (hl : q ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → q ^ (2 * t) ≠ 1) (hl0 : 0 < l) (p : ℕ) :
    ∏ j ∈ range p, qBinomial q (l * (j + 1)) l = (p.factorial : k) * q ^ (l ^ 2 * p.choose 2) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hb := qBinomInt_mul_mul hq hl hprim hl0 ((p + 1 : ℕ) : ℤ) 1
    rw [← Nat.cast_mul, mul_one, qBinomInt_natCast, Ring.choose_natCast, Nat.choose_one_right]
      at hb
    rw [prod_range_succ, ih, hb, Nat.factorial_succ, Nat.choose_succ_succ', Nat.choose_one_right]
    have e : q ^ ((l : ℤ) ^ 2 * (((p + 1 : ℕ) : ℤ) + 1) * ((1 : ℕ) : ℤ)) = q ^ (l ^ 2 * p) := by
      rw [← zpow_natCast]
      refine zpow_eq_of_dvd hq hl ⟨l, ?_⟩
      push_cast; ring
    rw [e]
    push_cast
    ring

/-- [Lus] 34.1.4 (a) over a field: for `0 ≤ r ≤ a < l`,
`Σ_{s=0}^{l-a-1} (-1)^{l-r+1+s} q^{-(l-r)(a-l+1+s)+s} [l-r; s] = q^{l(a-r)} [a; r]` if
`q^{2l} = 1` and `q^{2t} ≠ 1` for `0 < t < l`. -/
theorem sum_qBinomial_root (hq : q ≠ 0) (hl : q ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → q ^ (2 * t) ≠ 1) {r a : ℕ} (hra : r ≤ a) (hal : a < l) :
    ∑ s ∈ range (l - a), (-1) ^ (l - r + 1 + s) *
        q ^ (-(((l : ℤ) - r) * ((a : ℤ) - l + 1 + s)) + s) * qBinomial q (l - r) s =
      q ^ ((l : ℤ) * ((a : ℤ) - r)) * qBinomial q a r := by
  obtain ⟨n, hn⟩ : ∃ n, l - r = n + 1 := ⟨l - r - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, l - a = m + 1 := ⟨l - a - 1, by omega⟩
  have hlr : (l : ℤ) - r = n + 1 := by omega
  -- the left hand side is a partial alternating sum
  have hsum : ∑ s ∈ range (l - a), (-1) ^ (l - r + 1 + s) *
        q ^ (-(((l : ℤ) - r) * ((a : ℤ) - l + 1 + s)) + s) * qBinomial q (l - r) s =
      (-1) ^ n * q ^ (-(((n : ℤ) + 1) * ((a : ℤ) - l + 1))) *
        ∑ s ∈ range (m + 1), (-1) ^ s * q ^ (-((s : ℤ) * n)) * qBinomial q (n + 1) s := by
    rw [hm, mul_sum]
    refine sum_congr rfl fun s _ ↦ ?_
    rw [hn, hlr, show n + 1 + 1 + s = n + s + 2 by ring, pow_add, pow_add]
    have : q ^ (-(((n : ℤ) + 1) * ((a : ℤ) - l + 1 + s)) + s) =
        q ^ (-(((n : ℤ) + 1) * ((a : ℤ) - l + 1))) * q ^ (-((s : ℤ) * n)) := by
      rw [← zpow_add₀ hq]; ring_nf
    rw [this]
    ring
  rw [hsum, sum_neg_one_pow_qBinomial hq]
  -- `[l-r-1; l-a-1] = (-1)^{a-r} q^{l(a-r)} [a; r]`
  have hsymm : qBinomial q n m = qBinomial q n (a - r) := by
    rw [← qBinomial_symm q (show a - r ≤ n by omega), show n - (a - r) = m by omega]
  have hvd := qBinomInt_add hq (l : ℤ) (Int.negSucc r) (a - r)
  rw [show (l : ℤ) + Int.negSucc r = (n : ℕ) by rw [Int.negSucc_eq]; omega,
    qBinomInt_natCast, sum_eq_single 0] at hvd
  · rw [qBinomInt_negSucc, show r + (a - r - 0) = a by omega, Nat.sub_zero,
      qBinomial_symm q hra] at hvd
    rw [hsymm, hvd]
    simp only [Nat.cast_zero, mul_zero, sub_zero, qBinomInt_zero_right, mul_one]
    have e : q ^ (-(((n : ℤ) + 1) * ((a : ℤ) - l + 1))) * q ^ (-((m : ℤ) * (n + 1))) = 1 := by
      rw [← zpow_add₀ hq, ← zpow_zero q]
      congr 1
      have : (m : ℤ) = l - a - 1 := by omega
      rw [this]; ring
    have es : ((-1 : k) ^ n * (-1) ^ m * (-1) ^ (a - r)) = 1 := by
      rw [← pow_add, ← pow_add, show n + m + (a - r) = 2 * (l - r - 1) by omega, pow_mul]
      simp
    rw [Nat.cast_sub hra]
    linear_combination (q ^ ((l : ℤ) * ((a : ℤ) - r)) * qBinomial q a r) *
      ((-1) ^ n * (-1) ^ m * (-1) ^ (a - r) * e + es)
  · intro i hi hi0
    have hil : i < l := by have := mem_range.1 hi; omega
    rw [qBinomInt_natCast, qBinomial_eq_zero_of_root hq hl hprim (Nat.pos_of_ne_zero hi0) hil]
    ring
  · intro h
    exact absurd (mem_range.2 (Nat.succ_pos _)) h

end Field

/-! ### Over an integral domain -/

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {v : Rˣ} {l : ℕ}

private lemma root_hyps' (hl : (v : R) ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → (v : R) ^ (2 * t) ≠ 1) :
    algebraMap R (FractionRing R) v ≠ 0 ∧ algebraMap R (FractionRing R) v ^ (2 * l) = 1 ∧
      ∀ t, 0 < t → t < l → algebraMap R (FractionRing R) v ^ (2 * t) ≠ 1 := by
  have hinj := IsFractionRing.injective R (FractionRing R)
  refine ⟨(v.isUnit.map _).ne_zero, by rw [← map_pow, hl, map_one], fun t h0 ht h ↦ ?_⟩
  exact hprim t h0 ht (hinj (by rw [map_pow, h, map_one]))

/-- [Lus] 34.1.3 (a): if `v^{2l} = 1` and `v^{2t} ≠ 1` for `0 < t < l`, then
`∏_{j=1}^{p} [lj; l] = p! v^{l² p(p-1)/2}`; the left hand side is `[lp]^!/([l]^!)^p`
(`qFactorial_mul_eq`). -/
theorem prod_qBinomialU_mul_root (hl : (v : R) ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → (v : R) ^ (2 * t) ≠ 1) (hl0 : 0 < l) (p : ℕ) :
    ∏ j ∈ range p, qBinomialU v (l * (j + 1)) l =
      (p.factorial : R) * (v : R) ^ (l ^ 2 * p.choose 2) := by
  obtain ⟨h0, h1, h2⟩ := root_hyps' hl hprim
  apply IsFractionRing.injective R (FractionRing R)
  simp only [map_prod, map_qBinomialU, map_mul, map_natCast, map_pow]
  exact prod_qBinomial_mul_root h0 h1 h2 hl0 p

/-- [Lus] 34.1.4 (a): if `v^{2l} = 1` and `v^{2t} ≠ 1` for `0 < t < l`, then for
`0 ≤ r ≤ a < l`,
`Σ_{s=0}^{l-a-1} (-1)^{l-r+1+s} v^{-(l-r)(a-l+1+s)+s} [l-r; s] = v^{l(a-r)} [a; r]`. -/
theorem sum_qBinomialU_root (hl : (v : R) ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → (v : R) ^ (2 * t) ≠ 1) {r a : ℕ} (hra : r ≤ a)
    (hal : a < l) :
    ∑ s ∈ range (l - a), (-1) ^ (l - r + 1 + s) *
        ((v ^ (-(((l : ℤ) - r) * ((a : ℤ) - l + 1 + s)) + s) : Rˣ) : R) *
          qBinomialU v (l - r) s =
      ((v ^ ((l : ℤ) * ((a : ℤ) - r)) : Rˣ) : R) * qBinomialU v a r := by
  obtain ⟨h0, h1, h2⟩ := root_hyps' hl hprim
  apply IsFractionRing.injective R (FractionRing R)
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_units_zpow, map_qBinomialU]
  exact sum_qBinomial_root h0 h1 h2 hra hal

/-- [Lus] 35.1.5 (a): if `v^{2l} = 1` and `v^{2t} ≠ 1` for `0 < t < l`, then
`[l a₁; l t₁]_v = [a₁; t₁]_{v^{l²}}` for `a₁ ∈ ℤ`, `t₁ ∈ ℕ` (Lusztig states it for `v = vᵢ`,
`l = lᵢ`, with `vᵢ* = vᵢ^{lᵢ²}`). Part (b) of [Lus] 35.1.5 is `gaussBinom_eq_zero_of_not_dvd`. -/
theorem gaussBinom_mul_mul_eq_pow (hl : (v : R) ^ (2 * l) = 1)
    (hprim : ∀ t, 0 < t → t < l → (v : R) ^ (2 * t) ≠ 1) (hl0 : 0 < l) (a₁ : ℤ) (t₁ : ℕ) :
    gaussBinom v (l * a₁) (l * t₁) = gaussBinom (v ^ (l ^ 2)) a₁ t₁ := by
  have h1 : (((v ^ (l ^ 2) : Rˣ) : R)) ^ (2 * 1) = 1 := by
    rw [Units.val_pow_eq_pow_val, ← pow_mul, show l ^ 2 * (2 * 1) = 2 * l * l by ring, pow_mul,
      hl, one_pow]
  have h := gaussBinom_mul_mul (v := v ^ (l ^ 2)) h1 (fun t h0 ht ↦ by omega) one_pos a₁ t₁
  rw [Nat.cast_one, one_mul, one_mul] at h
  rw [h, gaussBinom_mul_mul hl hprim hl0, ← zpow_natCast, ← zpow_mul]
  push_cast
  ring_nf

end Domain

end LieLean.QuantumGroup
