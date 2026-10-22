/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.RootOfUnity.GaussBinomialSums

/-!
# The Serre relations for the quantum Frobenius splitting

At a root of `1`, the higher-order quantum Serre relations `f_{i,j;n,m;-1} = 0` imply the
Serre relations of the Frobenius Cartan datum between the divided powers `θᵢ^{(lᵢ)}`,
`θⱼ^{(lⱼ)}` ([Lus] 35.2.3 (b)). This file proves the computation in an abstract algebra: a
family `x n` behaving like the divided powers of one generator, an element `y`, and the
relations `f_{i,j;n,m;-1} = 0` for `an < m ≤ an + lᵢ`.

## Main results

* `QuantumGroup.sum_neg_one_pow_zpow_qBinomial`:
  `Σ_{t<L} (-1)^t q^{t(a-1)} [a; t] = δ_{a,0}` for `a < L` ([Lus] 1.3.4).
* `QuantumGroup.sum_frobSerreCoeff`: the coefficients `c_{r,s'}` of [Lus] 35.2.3.
* `QuantumGroup.sum_frobenius_serre`: [Lus] 35.2.3 (b),
  `Σ_{p+p' = N/L + 1} (-1)^p x(Lp) y x(Lp') = 0`.

## Proof

As in [Lus] 35.2.3: the combination `Σ_{t<L} (-1)^t q^{(N+L-1)t} f_{N+L-t} x(t)` (with
`f_m = Σ_{r+s=m} (-1)^r q^{r(L-1-t)} x(r) y x(s)`) equals `Σ_{r+s'=N+L} c_{r,s'} x(r) y x(s')`,
and `c_{r,s'} = (-1)^{r/L}` if `L ∣ r`, and `0` otherwise, by [Lus] 34.1.2 (c), (e) and 1.3.4.
The sign `(-1)^p` here and the sign `(-1)^{p'}` of [Lus] differ by `(-1)^{N/L+1}`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.3.4, 34.1.2, 35.2.3.
-/

open Finset

namespace LieLean.QuantumGroup

variable {k : Type*} [Field k] {q : k} {L : ℕ}

/-- [Lus] 1.3.4: `Σ_{t<L} (-1)^t q^{t(a-1)} [a; t] = δ_{a,0}` for `a < L`. -/
theorem sum_neg_one_pow_zpow_qBinomial (hq : q ≠ 0) {a : ℕ} (haL : a < L) :
    ∑ t ∈ range L, (-1) ^ t * q ^ ((t : ℤ) * ((a : ℤ) - 1)) * qBinomial q a t =
      if a = 0 then 1 else 0 := by
  rw [← sum_subset (range_subset_range.2 (show a + 1 ≤ L by omega))]
  · rcases a with _ | n
    · simp
    · have h := sum_neg_one_pow_qBinomial (inv_ne_zero hq) n (n + 1)
      rw [qBinomial_eq_zero_of_lt _ (Nat.lt_succ_self n), mul_zero] at h
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      rw [← h]
      refine sum_congr rfl fun t _ ↦ ?_
      rw [qBinomial_inv, inv_zpow', neg_neg]
      push_cast
      ring_nf
  · intro t _ ht
    rw [qBinomial_eq_zero_of_lt _ (by simpa using ht), mul_zero]

/-- `q^{L(L-1)} = (-1)^{L+1}` ([Lus] 34.1.2 (e)). -/
lemma zpow_mul_sub_one_eq (hq : q ≠ 0) (hl : q ^ (2 * L) = 1)
    (hprim : ∀ t, 0 < t → t < L → q ^ (2 * t) ≠ 1) (hL : 0 < L) :
    q ^ ((L : ℤ) * ((L : ℤ) - 1)) = (-1) ^ (L + 1) := by
  rw [← pow_sq_add_eq hl hprim hL, ← zpow_natCast]
  exact zpow_eq_of_dvd hq hl ⟨-1, by push_cast; ring⟩

/-- The coefficients of [Lus] 35.2.3: for `L ∣ N` and `r ≤ N + L`,
`Σ_{t<L} (-1)^t q^{(N+L-1)t} (-1)^r q^{r(L-1-t)} [N+L-r; t] = (-1)^{r/L}` if `L ∣ r`, and `0`
otherwise. -/
theorem sum_frobSerreCoeff (hq : q ≠ 0) (hl : q ^ (2 * L) = 1)
    (hprim : ∀ t, 0 < t → t < L → q ^ (2 * t) ≠ 1) (hL : 0 < L) {N : ℕ} (hN : L ∣ N)
    {r : ℕ} (hr : r ≤ N + L) :
    ∑ t ∈ range L, ((-1) ^ t * q ^ (((N : ℤ) + L - 1) * t)) *
        ((-1) ^ r * q ^ ((r : ℤ) * ((L : ℤ) - 1 - t)) * qBinomial q (N + L - r) t) =
      if L ∣ r then (-1) ^ (r / L) else 0 := by
  set s := N + L - r with hs
  set a := s % L
  set b := s / L
  have hsab : s = a + L * b := (Nat.mod_add_div s L).symm
  have haL : a < L := Nat.mod_lt s hL
  have key : ∀ t ∈ range L, ((-1) ^ t * q ^ (((N : ℤ) + L - 1) * t)) *
      ((-1) ^ r * q ^ ((r : ℤ) * ((L : ℤ) - 1 - t)) * qBinomial q s t) =
      ((-1) ^ r * q ^ ((r : ℤ) * ((L : ℤ) - 1))) *
        ((-1) ^ t * q ^ ((t : ℤ) * ((a : ℤ) - 1)) * qBinomial q a t) := by
    intro t ht
    have ht : t < L := mem_range.1 ht
    have hb := qBinomInt_add_mul_add_mul hq hl hprim hL haL ht (b : ℤ) 0
    rw [mul_zero, add_zero, ← Nat.cast_mul, ← Nat.cast_add, ← hsab, qBinomInt_natCast,
      Ring.choose_zero_right, Int.cast_one, mul_one] at hb
    rw [hb]
    have he : q ^ (((N : ℤ) + L - 1) * t) * q ^ ((r : ℤ) * ((L : ℤ) - 1 - t)) *
        q ^ (((a : ℤ) * ((0 : ℕ) : ℤ) - b * t) * L + (b + 1) * ((0 : ℕ) : ℤ) * (L : ℤ) ^ 2) =
        q ^ ((r : ℤ) * ((L : ℤ) - 1)) * q ^ ((t : ℤ) * ((a : ℤ) - 1)) := by
      rw [← zpow_add₀ hq, ← zpow_add₀ hq, ← zpow_add₀ hq]
      congr 1
      have : (s : ℤ) = N + L - r := by omega
      have h2 : (s : ℤ) = a + L * b := by exact_mod_cast hsab
      push_cast
      linear_combination (t : ℤ) * h2 - t * this
    linear_combination ((-1) ^ t * (-1) ^ r * qBinomial q a t) * he
  rw [sum_congr rfl key, ← mul_sum, sum_neg_one_pow_zpow_qBinomial hq haL]
  have hLr : L ∣ r ↔ a = 0 := by
    change L ∣ r ↔ s % L = 0
    rw [← Nat.dvd_iff_mod_eq_zero]
    have hNL : L ∣ N + L := dvd_add hN dvd_rfl
    constructor
    · exact fun h ↦ Nat.dvd_sub hNL h
    · intro h
      have := Nat.dvd_sub hNL h
      rwa [hs, Nat.sub_sub_self hr] at this
  by_cases h : L ∣ r
  · simp only [h, hLr.1 h, ↓reduceIte, mul_one]
    obtain ⟨p, rfl⟩ := h
    rw [Nat.mul_div_cancel_left p hL, pow_mul]
    have e : q ^ ((((L * p : ℕ)) : ℤ) * ((L : ℤ) - 1)) = (q ^ ((L : ℤ) * ((L : ℤ) - 1))) ^ p := by
      rw [← zpow_natCast, ← zpow_mul]; push_cast; ring_nf
    rw [e, zpow_mul_sub_one_eq hq hl hprim hL, ← mul_pow, ← pow_add,
      show L + (L + 1) = 2 * L + 1 by ring, pow_succ, pow_mul]
    simp
  · have ha : a ≠ 0 := fun h' ↦ h (hLr.2 h')
    simp [h, ha]

variable {A : Type*} [Ring A] [Algebra k A]

/-- **[Lus] 35.2.3 (b).** Let `x : ℕ → A` satisfy `x(r) x(s) = [r+s; r] x(r+s)` and let `y ∈ A`.
If `L ∣ N` and, for every `t < L`,
`Σ_{r+s=N+L-t} (-1)^r q^{r(L-1-t)} x(r) y x(s) = 0` (the relations `f_{i,j;n,N+L-t;-1} = 0` of
[Lus] 7.1.5 (b), with `N = an`), then `Σ_{p+p'=N/L+1} (-1)^p x(Lp) y x(Lp') = 0`. -/
theorem sum_frobenius_serre (hq : q ≠ 0) (hl : q ^ (2 * L) = 1)
    (hprim : ∀ t, 0 < t → t < L → q ^ (2 * t) ≠ 1) (hL : 0 < L) {N : ℕ} (hN : L ∣ N)
    (x : ℕ → A) (y : A) (hx : ∀ r s, x r * x s = qBinomial q (r + s) r • x (r + s))
    (hg : ∀ t < L, ∑ p ∈ antidiagonal (N + L - t),
      ((-1) ^ p.1 * q ^ ((p.1 : ℤ) * ((L : ℤ) - 1 - t))) • (x p.1 * y * x p.2) = 0) :
    ∑ p ∈ antidiagonal (N / L + 1), ((-1 : k) ^ p.1) • (x (L * p.1) * y * x (L * p.2)) = 0 := by
  set z : ℕ → A := fun r ↦ x r * y * x (N + L - r)
  set c : ℕ → ℕ → k := fun t r ↦ (-1) ^ t * q ^ (((N : ℤ) + L - 1) * t)
  set d : ℕ → ℕ → k := fun t r ↦ (-1) ^ r * q ^ ((r : ℤ) * ((L : ℤ) - 1 - t))
  -- each relation, multiplied on the right by `x t`
  have h1 : ∀ t ∈ range L, (∑ p ∈ antidiagonal (N + L - t), d t p.1 • (x p.1 * y * x p.2)) *
      x t = ∑ r ∈ range (N + L + 1), (d t r * qBinomial q (N + L - r) t) • z r := by
    intro t ht
    have ht : t < L := mem_range.1 ht
    rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_mul]
    rw [← sum_subset (range_subset_range.2 (show N + L - t + 1 ≤ N + L + 1 by omega))]
    · refine sum_congr rfl fun r hr ↦ ?_
      have hr : r ≤ N + L - t := Nat.lt_succ_iff.1 (mem_range.1 hr)
      simp only [z, smul_mul_assoc, mul_assoc, hx, mul_smul_comm, smul_smul]
      rw [show N + L - t - r + t = N + L - r by omega]
      congr 2
      rw [show N + L - t - r = (N + L - r) - t by omega]
      exact qBinomial_symm q (by omega)
    · intro r hr0 hr
      have : N + L - r < t := by simp at hr hr0; omega
      rw [qBinomial_eq_zero_of_lt _ this, mul_zero, zero_smul]
  have h2 : ∑ t ∈ range L, c t 0 • ((∑ p ∈ antidiagonal (N + L - t),
      d t p.1 • (x p.1 * y * x p.2)) * x t) = 0 :=
    sum_eq_zero fun t ht ↦ by rw [hg t (mem_range.1 ht), zero_mul, smul_zero]
  rw [sum_congr rfl fun t ht ↦ by rw [h1 t ht]] at h2
  simp only [smul_sum, smul_smul] at h2
  rw [sum_comm] at h2
  have h3 : ∑ r ∈ range (N + L + 1), (if L ∣ r then (-1 : k) ^ (r / L) else 0) • z r = 0 := by
    rw [← h2]
    refine sum_congr rfl fun r hr ↦ ?_
    rw [← sum_smul, ← sum_frobSerreCoeff hq hl hprim hL hN
      (Nat.lt_succ_iff.1 (mem_range.1 hr))]
  -- reindex `r = L p`
  obtain ⟨M, hM⟩ := hN
  have hML : N / L + 1 = M + 1 := by rw [hM, Nat.mul_div_cancel_left M hL]
  have hsub : (range (M + 2)).image (L * ·) ⊆ range (N + L + 1) := by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hr
    have hp : p ≤ M + 1 := Nat.lt_succ_iff.1 (mem_range.1 hp)
    refine mem_range.2 (Nat.lt_succ_iff.2 ?_)
    rw [hM]; nlinarith
  rw [hML, Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← h3, ← sum_subset hsub,
    sum_image fun a _ b _ h ↦ Nat.eq_of_mul_eq_mul_left hL h]
  · refine sum_congr rfl fun p hp ↦ ?_
    have hp : p ≤ M + 1 := Nat.lt_succ_iff.1 (mem_range.1 hp)
    simp only [dvd_mul_right L p, ↓reduceIte, Nat.mul_div_cancel_left p hL]
    simp only [z]
    congr 3
    rw [hM, Nat.mul_sub, mul_add, mul_one]
  · intro r hr hr'
    have hLr : ¬ L ∣ r := by
      rintro ⟨p, rfl⟩
      refine hr' (mem_image.2 ⟨p, mem_range.2 ?_, rfl⟩)
      have := Nat.lt_succ_iff.1 (mem_range.1 hr)
      rw [hM] at this
      have : L * p ≤ L * (M + 1) := by linarith
      have := Nat.le_of_mul_le_mul_left this hL
      omega
    simp [hLr]

end LieLean.QuantumGroup
