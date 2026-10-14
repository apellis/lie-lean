/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Rank1

/-!
# Kashiwara's string identity and the integral weight components of `U_q(𝔰𝔩₂)`-modules

Let `M` be an integrable `U_q(𝔰𝔩₂)`-module (`QuantumGroup.IntegrableSl2`, `q ≠ 0` not a root of
unity) and `u ∈ M^{-n}` with `n ≥ 1`. Kashiwara ([Kas91] Lemma 6.1.4) observes that
`u = Σ_{k ≥ n} (-1)^{k-n} [k-1, k-n] F^{(k)} E^{(k)} u`. Since the coefficients lie in
`ℤ[q, q⁻¹]`, a `ℤ[q, q⁻¹]`-form of `M` stable under the divided powers is spanned in weight `-n`
by the images `F^{(k)} x`, `k ≥ n`, of its vectors of weight `2k - n` ([Kas91] Prop. 6.1.3).

On a string `F^{(m)} η` (`η` primitive of weight `2m - n`) the right hand side is the scalar
`Σ_{k=n}^{m} (-1)^{k-n} [k-1, k-n] [2m-n-m+k, k] [m, k]` times `F^{(m)} η`, and the lemma amounts
to the identity ([Kas91] (6.1.19), up to `[a, b] = [a, a - b]`)
`Σ_{j=0}^{p} (-1)^j [h+j, j] [h+1+p+j, h+1+j] [h+1+p, h+1+j] = 1`
(`QuantumGroup.sum_qBinomial_string`, with `n = h + 1`, `m = n + p`, `k = n + j`). Kashiwara
derives it from an identity of Andrews; the proof here is our own, by generating series:
the `q`-Vandermonde identity `P_{a+b}(x) = P_a(q^{-b}x) P_b(q^a x)`
(`QuantumGroup.qBinomialSeries_add`) splits the middle factor, and both resulting sums are
leading coefficients of the polynomials `Φ_a` of `QuantumGroup.QBinomialSeries`
(`QuantumGroup.coeff_qBinomialPhi_self`), once for `q` and once for `q⁻¹`.

## Main results

* `QuantumGroup.qBinomial_add_eq_sum`: the `q`-Vandermonde identity.
* `QuantumGroup.sum_qBinomial_string`: [Kas91] (6.1.19).
* `QuantumGroup.IntegrableSl2.sum_dF_dE_eq`: [Kas91] Lemma 6.1.4.
* `QuantumGroup.IntegrableSl2.mem_integral_wt_iff`: [Kas91] Prop. 6.1.3, for one simple root.

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, §6.1.
-/

open PowerSeries Finset

namespace LieLean.QuantumGroup

variable {k : Type*} [Field k] {q : k}

/-! ### The `q`-Vandermonde identity -/

lemma rescale_C_eq (a c : k) : rescale a (C c) = C c := by
  ext n
  cases n <;> simp [coeff_rescale, coeff_C]

/-- The `q`-Vandermonde identity for generating series: `P_{a+b}(x) = P_a(q^{-b} x) P_b(q^a x)`. -/
theorem qBinomialSeries_add (hq : q ≠ 0) (a b : ℕ) :
    qBinomialSeries q (a + b) =
      rescale (q⁻¹ ^ b) (qBinomialSeries q a) * rescale (q ^ a) (qBinomialSeries q b) := by
  induction b with
  | zero => simp [rescale_one]
  | succ b ih =>
    rw [← add_assoc, qBinomialSeries_succ hq, ih, qBinomialSeries_succ hq b]
    simp only [map_mul, map_add, map_one, rescale_rescale, rescale_X, rescale_C_eq]
    rw [← pow_succ, mul_comm (q ^ a) q⁻¹, pow_add, map_mul]
    ring

/-- The `q`-Vandermonde identity:
`[a+b, c] = Σ_{i ≤ c} q^{-bi} q^{a(c-i)} [a, i] [b, c-i]`. -/
theorem qBinomial_add_eq_sum (hq : q ≠ 0) (a b c : ℕ) :
    qBinomial q (a + b) c = ∑ i ∈ range (c + 1),
      q⁻¹ ^ (b * i) * q ^ (a * (c - i)) * qBinomial q a i * qBinomial q b (c - i) := by
  rw [← coeff_qBinomialSeries, qBinomialSeries_add hq, coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [coeff_rescale, coeff_qBinomialSeries, ← pow_mul]
  ring

/-- The leading coefficient of `Φ_{a+1}`: `coeff_a Φ_{a+1} = q^{(h+1)a}`. -/
lemma coeff_qBinomialPhi_self (hq : q ≠ 0) (h a : ℕ) :
    coeff a (qBinomialPhi q h (a + 1)) = q ^ ((h + 1) * a) := by
  induction a with
  | zero => simp [qBinomialPhi_one hq]
  | succ a ih =>
    rw [qBinomialPhi_succ hq, coeff_succ_one_add_mul, coeff_rescale, coeff_rescale, ih,
      coeff_qBinomialPhi_eq_zero hq h (by omega) le_rfl, mul_zero, zero_add]
    have hinv : q ^ a * q⁻¹ ^ a = 1 := by rw [← mul_pow, mul_inv_cancel₀ hq, one_pow]
    linear_combination q ^ (h + 1) * q ^ ((h + 1) * a) * hinv

/-! ### Kashiwara's identity (6.1.19) -/

lemma pow_mul_inv_pow_eq (hq : q ≠ 0) (a b c d : ℕ) (h : (a : ℤ) - b = c - d) :
    q ^ a * q⁻¹ ^ b = q ^ c * q⁻¹ ^ d := by
  rw [inv_pow, inv_pow, ← div_eq_mul_inv, ← div_eq_mul_inv,
    div_eq_div_iff (pow_ne_zero _ hq) (pow_ne_zero _ hq), ← pow_add, ← pow_add]
  congr 1
  omega

section NotRoot

variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq0 hq

/-- `[h+j, j] [j, i] = [h+i, i] [h+j, j-i]` for `i ≤ j`. -/
lemma qBinomial_add_self_mul_qBinomial {h i j : ℕ} (hij : i ≤ j) :
    qBinomial q (h + j) j * qBinomial q j i =
      qBinomial q (h + i) i * qBinomial q (h + j) (j - i) := by
  have F1 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (show j ≤ h + j by omega)
  have F2 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) hij
  have F3 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (show i ≤ h + i by omega)
  have F4 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (show j - i ≤ h + j by omega)
  rw [show h + j - j = h by omega] at F1
  rw [show h + i - i = h by omega] at F3
  rw [show h + j - (j - i) = h + i by omega] at F4
  have hX : qFactorial q i * qFactorial q (j - i) * qFactorial q h ≠ 0 :=
    mul_ne_zero (mul_ne_zero (qFactorial_ne_zero_of_pow_ne_one hq0 hq i)
      (qFactorial_ne_zero_of_pow_ne_one hq0 hq (j - i)))
      (qFactorial_ne_zero_of_pow_ne_one hq0 hq h)
  refine mul_right_cancel₀ hX ?_
  linear_combination (qBinomial q (h + j) j * qFactorial q h) * F2 + F1 -
    (qBinomial q (h + j) (j - i) * qFactorial q (j - i)) * F3 - F4

/-- [Kas91] (6.1.19): `Σ_{j ≤ p} (-1)^j [h+j, j] [h+1+p+j, h+1+j] [h+1+p, h+1+j] = 1`
(with `n = h + 1`, `m = p`; the middle factor is written there as `[h+1+p+j, p]`).
Kashiwara deduces it from an identity of Andrews; the proof here is our own (see the module
docstring). -/
theorem sum_qBinomial_string (h p : ℕ) :
    ∑ j ∈ range (p + 1), (-1) ^ j * qBinomial q (h + j) j *
      qBinomial q (h + 1 + p + j) (h + 1 + j) * qBinomial q (h + 1 + p) (h + 1 + j) = 1 := by
  have hqi : q⁻¹ ≠ 0 := inv_ne_zero hq0
  obtain ⟨N, hN⟩ : ∃ N, h + 1 + p = N := ⟨_, rfl⟩
  -- expand the middle factor by `q`-Vandermonde
  have step1 : ∀ j ∈ range (p + 1), (-1) ^ j * qBinomial q (h + j) j *
      qBinomial q (h + 1 + p + j) (h + 1 + j) * qBinomial q (h + 1 + p) (h + 1 + j) =
      ∑ i ∈ range (p + 1), (-1) ^ j * qBinomial q (h + j) j * qBinomial q N (p - j) *
        (q⁻¹ ^ (N * i) * q ^ (j * (p - i)) * qBinomial q j i * qBinomial q N (p - i)) := by
    intro j hj
    rw [mem_range] at hj
    subst hN
    rw [← mul_sum, ← qBinomial_add_eq_sum hq0,
      ← qBinomial_symm q (show h + 1 + j ≤ h + 1 + p + j by omega),
      ← qBinomial_symm q (show h + 1 + j ≤ h + 1 + p by omega),
      show h + 1 + p + j - (h + 1 + j) = p by omega,
      show h + 1 + p - (h + 1 + j) = p - j by omega, add_comm j (h + 1 + p)]
    ring
  rw [sum_congr rfl step1, sum_comm]
  -- the inner sums are leading coefficients of `Φ` for `q⁻¹`
  have step2 : ∀ i ∈ range (p + 1), ∑ j ∈ range (p + 1), (-1) ^ j * qBinomial q (h + j) j *
      qBinomial q N (p - j) * (q⁻¹ ^ (N * i) * q ^ (j * (p - i)) * qBinomial q j i *
        qBinomial q N (p - i)) =
      q⁻¹ ^ ((h + 1) * p) * ((-1) ^ i * (q * q⁻¹ ^ (p + 1)) ^ i * qBinomial q (h + i) i *
        qBinomial q (h + (p + 1)) (p - i)) := by
    intro i hi
    rw [mem_range] at hi
    obtain ⟨r, rfl⟩ : ∃ r, p = i + r := ⟨p - i, by omega⟩
    rw [show i + r + 1 = i + (r + 1) by omega, sum_range_add,
      sum_eq_zero (s := range i) fun j hj ↦ by
        rw [qBinomial_eq_zero_of_lt q (mem_range.1 hj)]; ring, zero_add]
    have hPhi := coeff_qBinomialPhi_self hqi (h + i) r
    rw [coeff_qBinomialPhi] at hPhi
    simp only [qBinomial_inv, inv_inv] at hPhi
    have hterm : ∀ l ∈ range (r + 1), (-1) ^ (i + l) * qBinomial q (h + (i + l)) (i + l) *
        qBinomial q N (i + r - (i + l)) * (q⁻¹ ^ (N * i) * q ^ ((i + l) * (i + r - i)) *
          qBinomial q (i + l) i * qBinomial q N (i + r - i)) =
        ((-1) ^ i * qBinomial q (h + i) i * qBinomial q N r * q⁻¹ ^ (N * i) * q ^ (i * r)) *
          ((-1) ^ l * (q⁻¹ * q ^ (r + 1)) ^ l * qBinomial q (h + i + l) l *
            qBinomial q (h + i + (r + 1)) (r - l)) := by
      intro l hl
      have e := qBinomial_add_self_mul_qBinomial hq0 hq (h := h) (show i ≤ i + l by omega)
      rw [show i + l - i = l by omega, show h + (i + l) = h + i + l by omega] at e
      rw [show i + r - (i + l) = r - l by omega, show i + r - i = r by omega,
        show h + (i + l) = h + i + l by omega, show h + i + (r + 1) = N by omega,
        show q⁻¹ * q ^ (r + 1) = q ^ r by field_simp; ring]
      linear_combination ((-1) ^ (i + l) * qBinomial q N (r - l) * q⁻¹ ^ (N * i) *
        q ^ ((i + l) * r) * qBinomial q N r) * e
    rw [sum_congr rfl hterm, ← mul_sum, hPhi, show h + (i + (r + 1)) = N by omega]
    have hrN : i + r - i = r := by omega
    rw [hrN]
    subst hN
    have key : q⁻¹ ^ ((h + 1 + (i + r)) * i) * q ^ (i * r) * q⁻¹ ^ ((h + i + 1) * r) =
        q⁻¹ ^ ((h + 1) * (i + r)) * (q * q⁻¹ ^ (i + (r + 1))) ^ i := calc
      _ = q ^ (i * r) * q⁻¹ ^ ((h + 1 + (i + r)) * i + (h + i + 1) * r) := by ring
      _ = q ^ i * q⁻¹ ^ ((h + 1) * (i + r) + (i + (r + 1)) * i) :=
        pow_mul_inv_pow_eq hq0 _ _ _ _ (by push_cast; ring)
      _ = _ := by ring
    linear_combination ((-1) ^ i * qBinomial q (h + i) i * qBinomial q (h + 1 + (i + r)) r) * key
  rw [sum_congr rfl step2, ← mul_sum, ← coeff_qBinomialPhi, coeff_qBinomialPhi_self hq0,
    ← mul_pow, inv_mul_cancel₀ hq0, one_pow]

end NotRoot

namespace IntegrableSl2

variable {M : Type*} [AddCommGroup M] [Module k M] {V : IntegrableSl2 q M}
variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq0 hq

/-- [Kas91] Lemma 6.1.4: for `u ∈ M^{-(h+1)}`,
`u = Σ_j (-1)^j [h+j, j] F^{(h+1+j)} E^{(h+1+j)} u`, the sum being finite. -/
theorem sum_dF_dE_eq {h : ℕ} {u : M} (hu : u ∈ V.wt (-((h + 1 : ℕ) : ℤ))) :
    ∃ N, ∀ N' ≥ N, ∑ j ∈ range N', ((-1) ^ j * qBinomial q (h + j) j) •
      V.dF (h + 1 + j) (V.dE (h + 1 + j) u) = u := by
  refine wt_induction hq0 hq (P := fun u ↦ ∃ N, ∀ N' ≥ N, ∑ j ∈ range N',
    ((-1) ^ j * qBinomial q (h + j) j) • V.dF (h + 1 + j) (V.dE (h + 1 + j) u) = u)
    ⟨0, fun _ _ ↦ by simp⟩ ?_ ?_ ?_ hu
  · rintro x y ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    refine ⟨max N₁ N₂, fun N' hN' ↦ ?_⟩
    simp only [map_add, smul_add, sum_add_distrib]
    rw [h₁ N' (le_of_max_le_left hN'), h₂ N' (le_of_max_le_right hN')]
  · rintro c x ⟨N, hN⟩
    refine ⟨N, fun N' hN' ↦ ?_⟩
    simp_rw [map_smul, smul_comm _ c]
    rw [← smul_sum, hN N' hN']
  · rintro p j η hjp hpj hη hE
    obtain ⟨r, rfl⟩ : ∃ r, j = h + 1 + r := ⟨j - (h + 1), by omega⟩
    obtain rfl : p = h + 1 + 2 * r := by omega
    refine ⟨r + 1, fun N' hN' ↦ ?_⟩
    obtain ⟨s, rfl⟩ : ∃ s, N' = r + 1 + s := ⟨N' - (r + 1), by omega⟩
    rw [sum_range_add, sum_eq_zero (s := range s) fun l _ ↦ by
      rw [dE_dF_eq_zero_of_lt hq0 hq hη hE (by omega) (by omega), map_zero, smul_zero],
      add_zero]
    have hterm : ∀ l ∈ range (r + 1), ((-1) ^ l * qBinomial q (h + l) l) •
        V.dF (h + 1 + l) (V.dE (h + 1 + l) (V.dF (h + 1 + r) η)) =
        ((-1) ^ l * qBinomial q (h + l) l * qBinomial q (h + 1 + r + l) (h + 1 + l) *
          qBinomial q (h + 1 + r) (h + 1 + l)) • V.dF (h + 1 + r) η := by
      intro l hl
      rw [mem_range] at hl
      rw [dE_dF_of_primitive hq0 hq hη hE (by omega) (by omega), map_smul, dF_dF hq0 hq,
        show h + 1 + l + (h + 1 + r - (h + 1 + l)) = h + 1 + r by omega,
        show h + 1 + 2 * r - (h + 1 + r) + (h + 1 + l) = h + 1 + r + l by omega,
        smul_smul, smul_smul]
    rw [sum_congr rfl hterm, ← sum_smul, sum_qBinomial_string hq0 hq h r, one_smul]

/-- [Kas91] Prop. 6.1.3, for one simple root: let `L ⊆ M` be a module over a ring `R` acting
on `M` through `φ : R → k` (e.g. `R = ℤ[q, q⁻¹]`), stable under the divided powers, such that
the `q`-binomial coefficients come from `R`. Then the vectors of `L` of weight `-(h+1)` are
the `R`-linear combinations of vectors `F^{(h+1+j)} y` with `y ∈ L` of weight `h+1+2j`. -/
theorem mem_integral_wt_iff {R : Type*} [CommRing R] [Module R M] (φ : R →+* k)
    (hφ : ∀ (r : R) (x : M), r • x = φ r • x) (L : Submodule R M)
    (hLE : ∀ a, ∀ x ∈ L, V.dE a x ∈ L) (hLF : ∀ a, ∀ x ∈ L, V.dF a x ∈ L)
    (hcoef : ∀ n j, ∃ r, φ r = qBinomial q n j) (h : ℕ) (u : M) :
    u ∈ L ∧ u ∈ V.wt (-((h + 1 : ℕ) : ℤ)) ↔ u ∈ Submodule.span R
      {x | ∃ (j : ℕ) (y : M), y ∈ L ∧ y ∈ V.wt ((h + 1 + 2 * j : ℕ) : ℤ) ∧
        x = V.dF (h + 1 + j) y} := by
  constructor
  · rintro ⟨huL, hu⟩
    obtain ⟨N, hN⟩ := sum_dF_dE_eq hq0 hq (V := V) hu
    rw [← hN N le_rfl]
    refine sum_mem fun j _ ↦ ?_
    obtain ⟨c, hc⟩ := hcoef (h + j) j
    rw [← hc, show ((-1) ^ j * φ c) = φ ((-1) ^ j * c) by simp, ← hφ]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, _, hLE _ _ huL, ?_, rfl⟩)
    convert dE_mem hu (h + 1 + j) using 2
    push_cast
    ring
  · intro hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, y, hyL, hy, rfl⟩ := hx
      refine ⟨hLF _ _ hyL, ?_⟩
      convert dF_mem hy (h + 1 + j) using 2
      push_cast
      ring
    | zero => exact ⟨zero_mem _, zero_mem _⟩
    | add x y _ _ hx hy => exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | smul r x _ hx =>
      refine ⟨L.smul_mem r hx.1, ?_⟩
      rw [hφ]
      exact Submodule.smul_mem _ _ hx.2

end IntegrableSl2

end LieLean.QuantumGroup
