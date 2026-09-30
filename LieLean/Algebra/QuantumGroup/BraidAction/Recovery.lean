/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.Diagonal
import LieLean.Algebra.QuantumGroup.BraidAction.A2

/-!
# Recovering `Eⱼ`, `Fⱼ` from the braid images, and centre-first Serre relations

For `j ≠ i`, `r = -aᵢⱼ`, `q = vᵢ`, the candidate inverse `Tᵢ⁻¹` is the conjugate of `Tᵢ` by
the product-reversal anti-automorphism (`braidReversal`); its value on `Eⱼ` is the reversal of
`Tᵢ(Eⱼ)`, which is `[r]!⁻¹ (-1)^r q^{-r} serreAux q q r Eᵢ Eⱼ` (`braidReversal_braidEj`). We prove
that `Tᵢ` sends it back to `Eⱼ` (and likewise for `Fⱼ`), in every degree:

* `QuantumGroup.serreAux_braidEi_braidEj`:
  `[r]!⁻¹ (-1)^r q^{-r} serreAux q q r (Tᵢ Eᵢ) (Tᵢ Eⱼ) = Eⱼ`;
* `QuantumGroup.serreAux_braidFi_braidFj`: `[r]!⁻¹ serreAux q q r (Tᵢ Fᵢ) (Tᵢ Fⱼ) = Fⱼ`;
* `QuantumGroup.qSerre_braidEi_braidEj`, `QuantumGroup.qSerre_braidFi_braidFj`: the
  centre-first transformed Serre relations `S_{1-aᵢⱼ}(Tᵢ Eᵢ, Tᵢ Eⱼ) = 0`, in every degree.

## Method

With `X n` the twisted commutators of `BraidAction/Diagonal.lean` (`Tᵢ(Eⱼ) = [r]!⁻¹ X r`) and
`A = Tᵢ(Eᵢ) = -Fᵢ K̃ᵢ`, the relation `Fᵢ X (n+1) = X (n+1) Fᵢ + c X n K̃ᵢ⁻¹` gives
`A X (n+1) - s (n+1) X (n+1) A = -s (n+1) c X n` (`BraidDiagonal.Hyp.stepE`). A rescaled Serre
element `serreAux` is a product of such twisted commutators (`BraidDiagonal.serreAux_iter`), so
`serreAux q q r A (X r) = (-1)^r q^r ([r]!)² Eⱼ`, and one more twisted commutator kills `Eⱼ`,
which gives the centre-first Serre relation. The `F`-side is the same computation with
`Tᵢ(Fᵢ) = -K̃ᵢ⁻¹ Eᵢ`.

## References

Reconstructed from the quotient presentation; this computation was not taken from a source
(compare [Lus] §37.1 (check), [Jan] Ch. 8 (check)).
-/

noncomputable section

open Finset

namespace QuantumGroup

namespace BraidDiagonal

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B] {q Q : k}

lemma serreAux_smul_right (c : k) (m : ℕ) (a b : B) (μ : k) :
    serreAux q c m a (μ • b) = μ • serreAux q c m a b := by
  simp only [serreAux, smul_sum, mul_smul_comm, smul_mul_assoc]
  exact sum_congr rfl fun _ _ ↦ smul_comm _ _ _

/-- Iterating twisted commutators with `A` lowers `Z (n + m + 1)` to `Z n`. -/
lemma serreAux_iter (hq : q ≠ 0) (A : B) (Z : ℕ → B) (γ : ℕ → k)
    (hZ : ∀ n, A * Z (n + 1) - shift q Q (n + 1) • (Z (n + 1) * A) = γ (n + 1) • Z n)
    (m n : ℕ) :
    serreAux q (shift q Q (n + m + 1) * q⁻¹ ^ m) (m + 1) A (Z (n + m + 1)) =
      (∏ t ∈ range (m + 1), γ (n + m + 1 - t)) • Z n := by
  induction m generalizing n with
  | zero =>
    rw [serreAux_succ hq]
    simp [serreAux, hZ]
  | succ m ih =>
    rw [serreAux_succ hq, show n + (m + 1) + 1 = n + m + 1 + 1 by ring]
    have e1 : shift q Q (n + m + 1 + 1) * q⁻¹ ^ (m + 1) * q ^ (m + 1) =
        shift q Q (n + m + 1 + 1) := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hq, one_pow, mul_one]
    have e2 : shift q Q (n + m + 1 + 1) * q⁻¹ ^ (m + 1) * q⁻¹ =
        shift q Q (n + m + 1) * q⁻¹ ^ m := by
      have e : q ^ 2 * q⁻¹ * q⁻¹ = 1 := by field_simp
      rw [shift_succ, pow_succ]
      linear_combination (shift q Q (n + m + 1) * q⁻¹ ^ m) * e
    rw [e1, hZ, e2, serreAux_smul_right, ih, smul_smul, prod_range_succ' _ (m + 1)]
    congr 1
    rw [mul_comm]
    congr 1
    refine prod_congr rfl fun t _ ↦ ?_
    congr 1
    omega

lemma prod_reflect_succ (γ : ℕ → k) (r : ℕ) :
    ∏ t ∈ range r, γ (r - t) = ∏ t ∈ range r, γ (t + 1) := by
  rw [← prod_range_reflect]
  refine prod_congr rfl fun t ht ↦ ?_
  rw [show r - (r - 1 - t) = t + 1 by have := mem_range.1 ht; omega]

lemma prod_E (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0) (r : ℕ) :
    ∏ t ∈ range r, -(shift q (q ^ r) (r - t) * cc q (q ^ r) (r - t)) =
      (-1) ^ r * q ^ r * qFactorial q r ^ 2 := by
  have h := coefB_pow hq hd (1 : k) r
  rw [coefB_eq_prod, mul_one, mul_one] at h
  rw [prod_reflect_succ (fun n ↦ -(shift q (q ^ r) n * cc q (q ^ r) n))]
  have e : ∏ t ∈ range r, -(shift q (q ^ r) (t + 1) * cc q (q ^ r) (t + 1)) =
      (∏ t ∈ range r, q ^ 2) * ∏ t ∈ range r, -(shift q (q ^ r) t * cc q (q ^ r) (t + 1)) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun t _ ↦ ?_
    rw [shift_succ]; ring
  rw [e, h, prod_const, card_range, ← pow_mul]
  have e2 : q ^ (2 * r) * q⁻¹ ^ r = q ^ r := by
    rw [two_mul, pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ hq, one_pow, mul_one]
  linear_combination ((-1) ^ r * qFactorial q r ^ 2) * e2

lemma prod_F (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0) (r : ℕ) :
    ∏ t ∈ range r, -(shift q (q ^ r) (r - t - 1) * cc q (q ^ r) (r - t)) =
      (-1) ^ r * q⁻¹ ^ r * qFactorial q r ^ 2 := by
  have h := coefB_pow hq hd (1 : k) r
  rw [coefB_eq_prod, mul_one, mul_one] at h
  rw [← h, ← prod_range_reflect]
  refine prod_congr rfl fun t ht ↦ ?_
  have := mem_range.1 ht
  rw [show r - (r - 1 - t) - 1 = t by omega, show r - (r - 1 - t) = t + 1 by omega]

lemma shift_pow_mul (hq : q ≠ 0) (m : ℕ) :
    shift q (q ^ (m + 1)) (0 + m + 1) * q⁻¹ ^ m = q := by
  simp only [shift, zero_add, inv_pow]
  field_simp
  ring

namespace Hyp

variable {c : k} {E F K K' L L' x y : B}

/-- Lowering `X (n+1)` by `Tᵢ(Eᵢ) = -F K`. -/
lemma stepE (h : Hyp q Q c E F K K' L L' x y) (hK'K : K' * K = 1) (n : ℕ) :
    -(F * K) * X q Q E x (n + 1) - shift q Q (n + 1) • (X q Q E x (n + 1) * -(F * K)) =
      (-(shift q Q (n + 1) * cc q Q (n + 1))) • X q Q E x n := by
  have hF := F_mul_X h.q_ne h.EF h.KE h.K'E h.xF h.Kx h.K'x n
  have hK := K_mul_X (q := q) (Q := Q) h.KE h.Kx (n + 1)
  calc -(F * K) * X q Q E x (n + 1) - shift q Q (n + 1) • (X q Q E x (n + 1) * -(F * K))
      = -(F * (K * X q Q E x (n + 1))) +
          shift q Q (n + 1) • (X q Q E x (n + 1) * F * K) := by
        simp only [neg_mul, mul_neg, mul_assoc, smul_neg, sub_neg_eq_add]
    _ = -(shift q Q (n + 1) • ((F * X q Q E x (n + 1)) * K)) +
          shift q Q (n + 1) • (X q Q E x (n + 1) * F * K) := by
        rw [hK, mul_smul_comm, ← mul_assoc F]
    _ = (-(shift q Q (n + 1) * cc q Q (n + 1))) • (X q Q E x n * (K' * K)) := by
        rw [hF]
        simp only [add_mul, smul_mul_assoc, mul_assoc, smul_add, neg_add, smul_smul]
        module
    _ = _ := by rw [hK'K, mul_one]

/-- Lowering `Y (n+1)` by `Tᵢ(Fᵢ) = -K' E`. -/
lemma stepF (h : Hyp q Q c E F K K' L L' x y) (hK'K : K' * K = 1) (n : ℕ) :
    -(K' * E) * X q Q F y (n + 1) - shift q Q (n + 1) • (X q Q F y (n + 1) * -(K' * E)) =
      (-(shift q Q n * cc q Q (n + 1))) • X q Q F y n := by
  have hE := h.E_mul_Y n
  have hK (m : ℕ) : K' * X q Q F y m = shift q Q m • (X q Q F y m * K') := by
    rw [mul_X h.K'F h.K'y, shift, ← pow_mul, mul_comm]
  calc -(K' * E) * X q Q F y (n + 1) - shift q Q (n + 1) • (X q Q F y (n + 1) * -(K' * E))
      = -(K' * (E * X q Q F y (n + 1))) +
          shift q Q (n + 1) • (X q Q F y (n + 1) * K' * E) := by
        simp only [neg_mul, mul_neg, mul_assoc, smul_neg, sub_neg_eq_add]
    _ = -((K' * X q Q F y (n + 1)) * E) - cc q Q (n + 1) • ((K' * X q Q F y n) * K) +
          shift q Q (n + 1) • (X q Q F y (n + 1) * K' * E) := by
        rw [hE]
        simp only [mul_add, mul_smul_comm, mul_assoc, neg_add]
        abel
    _ = (-(shift q Q n * cc q Q (n + 1))) • (X q Q F y n * (K' * K)) := by
        rw [hK, hK]
        simp only [smul_mul_assoc, mul_assoc, smul_smul]
        module
    _ = _ := by rw [hK'K, mul_one]

/-- `serreAux q q r (Tᵢ Eᵢ) (X r) = (-1)^r q^r ([r]!)² x`. -/
theorem serreAux_E {r : ℕ} (h : Hyp q (q ^ r) c E F K K' L L' x y) (hK'K : K' * K = 1) :
    serreAux q q r (-(F * K)) (X q (q ^ r) E x r) =
      ((-1) ^ r * q ^ r * qFactorial q r ^ 2) • x := by
  cases r with
  | zero => simp [serreAux, X, qFactorial]
  | succ m =>
    have H := serreAux_iter h.q_ne (-(F * K)) (X q (q ^ (m + 1)) E x)
      (fun n ↦ -(shift q (q ^ (m + 1)) n * cc q (q ^ (m + 1)) n)) (h.stepE hK'K) m 0
    rw [shift_pow_mul h.q_ne, zero_add] at H
    rw [H, prod_E h.q_ne h.sub_ne]
    rfl

/-- `serreAux q q r (Tᵢ Fᵢ) (Y r) = (-1)^r q^{-r} ([r]!)² y`. -/
theorem serreAux_F {r : ℕ} (h : Hyp q (q ^ r) c E F K K' L L' x y) (hK'K : K' * K = 1) :
    serreAux q q r (-(K' * E)) (X q (q ^ r) F y r) =
      ((-1) ^ r * q⁻¹ ^ r * qFactorial q r ^ 2) • y := by
  cases r with
  | zero => simp [serreAux, X, qFactorial]
  | succ m =>
    have H := serreAux_iter h.q_ne (-(K' * E)) (X q (q ^ (m + 1)) F y)
      (fun n ↦ -(shift q (q ^ (m + 1)) (n - 1) * cc q (q ^ (m + 1)) n))
      (fun n ↦ by simpa using h.stepF hK'K n) m 0
    rw [shift_pow_mul h.q_ne, zero_add] at H
    rw [H, prod_F h.q_ne h.sub_ne]
    rfl

/-- The **centre-first transformed Serre relation** in every degree:
`serreAux q 1 (r+1) (Tᵢ Eᵢ) (X r) = 0`. The `r` lowering steps reach `x`, which the last
twisted commutator kills. -/
theorem serreAux_centre_E {r : ℕ} (h : Hyp q (q ^ r) c E F K K' L L' x y) (hK'K : K' * K = 1) :
    serreAux q 1 (r + 1) (-(F * K)) (X q (q ^ r) E x r) = 0 := by
  let Z : ℕ → B := fun n ↦ Nat.casesOn n 0 fun n ↦ X q (q ^ r) E x n
  have hs (n : ℕ) : shift q (q ^ 2 * q ^ r) (n + 1) = shift q (q ^ r) n := by
    have := h.q_ne
    simp only [shift]
    field_simp
    ring
  have hZ (n : ℕ) : -(F * K) * Z (n + 1) -
      shift q (q ^ 2 * q ^ r) (n + 1) • (Z (n + 1) * -(F * K)) =
      (-(shift q (q ^ r) n * cc q (q ^ r) n)) • Z n := by
    rw [hs]
    cases n with
    | zero =>
      change -(F * K) * x - shift q (q ^ r) 0 • (x * -(F * K)) =
        (-(shift q (q ^ r) 0 * cc q (q ^ r) 0)) • (0 : B)
      rw [smul_zero, neg_mul, mul_neg, smul_neg, sub_neg_eq_add, mul_assoc, h.Kx, mul_smul_comm,
        ← mul_assoc F x, ← h.xF, shift, mul_zero, pow_zero, one_mul]
      simp only [mul_assoc]
      abel
    | succ n => exact h.stepE hK'K n
  have H := serreAux_iter h.q_ne (-(F * K)) Z
    (fun n ↦ -(shift q (q ^ r) (n - 1) * cc q (q ^ r) (n - 1))) hZ r 0
  have e : shift q (q ^ 2 * q ^ r) (0 + r + 1) * q⁻¹ ^ r = 1 := by
    have := h.q_ne
    simp only [shift, zero_add, inv_pow]
    field_simp
    ring
  rw [e] at H
  simpa [Z] using H

/-- The centre-first transformed Serre relation for the `F`-images, in every degree. -/
theorem serreAux_centre_F {r : ℕ} (h : Hyp q (q ^ r) c E F K K' L L' x y) (hK'K : K' * K = 1) :
    serreAux q 1 (r + 1) (-(K' * E)) (X q (q ^ r) F y r) = 0 := by
  let Z : ℕ → B := fun n ↦ Nat.casesOn n 0 fun n ↦ X q (q ^ r) F y n
  have hs (n : ℕ) : shift q (q ^ 2 * q ^ r) (n + 1) = shift q (q ^ r) n := by
    have := h.q_ne
    simp only [shift]
    field_simp
    ring
  have hZ (n : ℕ) : -(K' * E) * Z (n + 1) -
      shift q (q ^ 2 * q ^ r) (n + 1) • (Z (n + 1) * -(K' * E)) =
      (-(shift q (q ^ r) (n - 1) * cc q (q ^ r) n)) • Z n := by
    rw [hs]
    cases n with
    | zero =>
      change -(K' * E) * y - shift q (q ^ r) 0 • (y * -(K' * E)) =
        (-(shift q (q ^ r) (0 - 1) * cc q (q ^ r) 0)) • (0 : B)
      rw [smul_zero, neg_mul, mul_neg, smul_neg, sub_neg_eq_add, mul_assoc, h.Ey, ← mul_assoc,
        h.K'y, shift, mul_zero, pow_zero, one_mul]
      simp only [smul_mul_assoc, mul_assoc]
      abel
    | succ n => simpa using h.stepF hK'K n
  have H := serreAux_iter h.q_ne (-(K' * E)) Z
    (fun n ↦ -(shift q (q ^ r) (n - 2) * cc q (q ^ r) (n - 1))) hZ r 0
  have e : shift q (q ^ 2 * q ^ r) (0 + r + 1) * q⁻¹ ^ r = 1 := by
    have := h.q_ne
    simp only [shift, zero_add, inv_pow]
    field_simp
    ring
  rw [e] at H
  simpa [Z] using H

end Hyp

/-- Reversing the words of a rescaled Serre element: `Σ_t (-1)^t [m t] cᵗ aᵗ b a^{m-t}` is
`(-1)^m c^m serreAux q c⁻¹ m a b`. -/
lemma sum_reverse_serreAux {c : k} (hc : c ≠ 0) (m : ℕ) (a b : B) :
    ∑ t ∈ range (m + 1), ((-1) ^ t * qBinomial q m t * c ^ t) • (a ^ t * b * a ^ (m - t)) =
      ((-1) ^ m * c ^ m) • serreAux q c⁻¹ m a b := by
  rw [serreAux, smul_sum, ← sum_range_reflect]
  refine sum_congr rfl fun t ht ↦ ?_
  have ht := Nat.lt_succ_iff.1 (mem_range.1 ht)
  rw [show m + 1 - 1 - t = m - t by omega, show m - (m - t) = t by omega,
    qBinomial_symm q ht, smul_smul]
  congr 1
  have h1 : (-1 : k) ^ m = (-1) ^ (m - t) * (-1) ^ t := by rw [← pow_add, Nat.sub_add_cancel ht]
  have h2 : c ^ m = c ^ (m - t) * c ^ t := by rw [← pow_add, Nat.sub_add_cancel ht]
  have h3 : (-1 : k) ^ t * (-1) ^ t = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  rw [h1, h2, inv_pow]
  field_simp
  linear_combination (-(qBinomial q m t)) * h3

end BraidDiagonal

/-! ### Recovery in the quantum group -/

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k}

lemma braidReversal_pow [NeZero v] (a : QuantumGroup R v) (n : ℕ) :
    braidReversal (a ^ n) = braidReversal a ^ n := by
  induction n with
  | zero => simp only [pow_zero]; simpa using braidReversal_K (R := R) (v := v) 0
  | succ n ih => rw [pow_succ, braidReversal_mul, ih, pow_succ']

/-- Product reversal of a rescaled Serre element in two generators fixed by reversal. -/
lemma braidReversal_serreAux [NeZero v] {q c : k} (hc : c ≠ 0) (m : ℕ) {a b : QuantumGroup R v}
    (ha : braidReversal a = a) (hb : braidReversal b = b) :
    braidReversal (serreAux q c m a b) = ((-1) ^ m * c ^ m) • serreAux q c⁻¹ m a b := by
  rw [← BraidDiagonal.sum_reverse_serreAux hc, serreAux, map_sum]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [map_smul, braidReversal_mul, braidReversal_mul, braidReversal_pow, braidReversal_pow,
    ha, hb, ← mul_assoc]

variable (R v) in
/-- The inverse candidate `Tᵢ⁻¹(Eⱼ)`: product reversal of `Tᵢ(Eⱼ)`. -/
lemma braidReversal_braidEj [NeZero v] (i j : I) :
    braidReversal (braidEj R v i j) =
      ((qFactorial (v ^ D.d i) (negA D i j))⁻¹ * ((-1) ^ negA D i j * (v ^ D.d i)⁻¹ ^ negA D i j)) •
        serreAux (v ^ D.d i) (v ^ D.d i) (negA D i j) (E R v i) (E R v j) := by
  have hq : (v ^ D.d i)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (NeZero.ne v))
  rw [braidEj, map_smul, braidReversal_serreAux hq _ (braidReversal_E i) (braidReversal_E j),
    inv_inv, smul_smul]

variable (R v) in
/-- The inverse candidate `Tᵢ⁻¹(Fⱼ)`: product reversal of `Tᵢ(Fⱼ)`. -/
lemma braidReversal_braidFj [NeZero v] (i j : I) :
    braidReversal (braidFj R v i j) =
      (qFactorial (v ^ D.d i) (negA D i j))⁻¹ •
        serreAux (v ^ D.d i) (v ^ D.d i) (negA D i j) (F R v i) (F R v j) := by
  have hq : (v ^ D.d i)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (NeZero.ne v))
  rw [braidFj, map_smul, braidReversal_serreAux hq _ (braidReversal_F i) (braidReversal_F j),
    inv_inv, smul_smul]
  congr 1
  have e1 : ((-1 : k) ^ negA D i j) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have e2 : (v ^ D.d i) ^ negA D i j * (v ^ D.d i)⁻¹ ^ negA D i j = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (pow_ne_zero _ (NeZero.ne v)), one_pow]
  have e : ((-1 : k) ^ negA D i j) ^ 2 * ((v ^ D.d i) ^ negA D i j * (v ^ D.d i)⁻¹ ^ negA D i j)
      = 1 := by rw [e1, e2, one_mul]
  linear_combination (qFactorial (v ^ D.d i) (negA D i j))⁻¹ * e

/-- **Recovery of `Eⱼ`** in every degree: applying `Tᵢ` to the reversed image gives back `Eⱼ`,
i.e. `[r]!⁻¹ (-1)^r q^{-r} serreAux q q r (Tᵢ Eᵢ) (Tᵢ Eⱼ) = Eⱼ`. -/
theorem serreAux_braidEi_braidEj [NeZero v] {i j : I} (hij : i ≠ j)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) (hr : qFactorial (v ^ D.d i) (negA D i j) ≠ 0) :
    ((qFactorial (v ^ D.d i) (negA D i j))⁻¹ * ((-1) ^ negA D i j * (v ^ D.d i)⁻¹ ^ negA D i j)) •
        serreAux (v ^ D.d i) (v ^ D.d i) (negA D i j) (braidEi R i) (braidEj R v i j) =
      E R v j := by
  have hv := NeZero.ne v
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  have hQ : (v ^ D.d i) ^ negA D i j ≠ 0 := pow_ne_zero _ hq0
  have hH := braidDiagonal_hyp R v hv hij hq
  have hc : (v ^ D.d i) ^ negA D i j * (v ^ D.d i * (v ^ D.d i) ^ negA D i j)⁻¹ =
      (v ^ D.d i)⁻¹ := by field_simp
  have hX : braidEj R v i j = (qFactorial (v ^ D.d i) (negA D i j))⁻¹ •
      BraidDiagonal.X (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (E R v i) (E R v j) (negA D i j) := by
    rw [BraidDiagonal.X_eq_serreAux hq0 hQ, hc]; rfl
  rw [hX, BraidDiagonal.serreAux_smul_right, braidEi, hH.serreAux_E (K_neg_mul_Kt i), smul_smul,
    smul_smul]
  convert one_smul k (E R v j) using 2
  have e1 : (qFactorial (v ^ D.d i) (negA D i j))⁻¹ * qFactorial (v ^ D.d i) (negA D i j) = 1 :=
    inv_mul_cancel₀ hr
  have e2 : ((-1 : k) ^ negA D i j) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have e3 : (v ^ D.d i)⁻¹ ^ negA D i j * (v ^ D.d i) ^ negA D i j = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hq0, one_pow]
  set f := qFactorial (v ^ D.d i) (negA D i j)
  set s := (-1 : k) ^ negA D i j
  set a := (v ^ D.d i)⁻¹ ^ negA D i j
  set b := (v ^ D.d i) ^ negA D i j
  linear_combination (f⁻¹ * f + 1) * s ^ 2 * (a * b) * e1 + (a * b) * e2 + e3

/-- **Recovery of `Fⱼ`** in every degree: `[r]!⁻¹ serreAux q q r (Tᵢ Fᵢ) (Tᵢ Fⱼ) = Fⱼ`. -/
theorem serreAux_braidFi_braidFj [NeZero v] {i j : I} (hij : i ≠ j)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) (hr : qFactorial (v ^ D.d i) (negA D i j) ≠ 0) :
    (qFactorial (v ^ D.d i) (negA D i j))⁻¹ •
        serreAux (v ^ D.d i) (v ^ D.d i) (negA D i j) (braidFi R i) (braidFj R v i j) =
      F R v j := by
  have hv := NeZero.ne v
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  have hQ : (v ^ D.d i) ^ negA D i j ≠ 0 := pow_ne_zero _ hq0
  have hH := braidDiagonal_hyp R v hv hij hq
  have hc : (v ^ D.d i) ^ negA D i j * (v ^ D.d i * (v ^ D.d i) ^ negA D i j)⁻¹ =
      (v ^ D.d i)⁻¹ := by field_simp
  have hY : braidFj R v i j = ((qFactorial (v ^ D.d i) (negA D i j))⁻¹ * (-1) ^ negA D i j *
      (v ^ D.d i) ^ negA D i j) •
      BraidDiagonal.X (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (F R v i) (F R v j) (negA D i j) := by
    rw [BraidDiagonal.X_eq_serreAux hq0 hQ, hc]; rfl
  rw [hY, BraidDiagonal.serreAux_smul_right, braidFi, hH.serreAux_F (K_neg_mul_Kt i), smul_smul,
    smul_smul]
  convert one_smul k (F R v j) using 2
  have e1 : (qFactorial (v ^ D.d i) (negA D i j))⁻¹ * qFactorial (v ^ D.d i) (negA D i j) = 1 :=
    inv_mul_cancel₀ hr
  have e2 : ((-1 : k) ^ negA D i j) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have e3 : (v ^ D.d i)⁻¹ ^ negA D i j * (v ^ D.d i) ^ negA D i j = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hq0, one_pow]
  set f := qFactorial (v ^ D.d i) (negA D i j)
  set s := (-1 : k) ^ negA D i j
  set a := (v ^ D.d i)⁻¹ ^ negA D i j
  set b := (v ^ D.d i) ^ negA D i j
  linear_combination (f⁻¹ * f + 1) * s ^ 2 * (a * b) * e1 + (a * b) * e2 + e3

/-- **Centre-first transformed Serre relation in every degree**: for `j ≠ i`,
`S_{1-aᵢⱼ}(Tᵢ Eᵢ, Tᵢ Eⱼ) = 0`. Only `v ≠ 0` and `vᵢ - vᵢ⁻¹ ≠ 0` are assumed. -/
theorem qSerre_braidEi_braidEj [NeZero v] {i j : I} (hij : i ≠ j)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (braidEi R i) (braidEj R v i j) = 0 := by
  have hv := NeZero.ne v
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  have hc : (v ^ D.d i) ^ negA D i j * (v ^ D.d i * (v ^ D.d i) ^ negA D i j)⁻¹ =
      (v ^ D.d i)⁻¹ := by field_simp
  have hX : braidEj R v i j = (qFactorial (v ^ D.d i) (negA D i j))⁻¹ •
      BraidDiagonal.X (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (E R v i) (E R v j) (negA D i j) := by
    rw [BraidDiagonal.X_eq_serreAux hq0 (pow_ne_zero _ hq0), hc]; rfl
  rw [← serreAux_one, one_sub_cartanMatrix_toNat hij, hX, BraidDiagonal.serreAux_smul_right,
    braidEi, (braidDiagonal_hyp R v hv hij hq).serreAux_centre_E (K_neg_mul_Kt i), smul_zero]

/-- Centre-first transformed Serre relation for the `F`-images, in every degree. -/
theorem qSerre_braidFi_braidFj [NeZero v] {i j : I} (hij : i ≠ j)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat (braidFi R i) (braidFj R v i j) = 0 := by
  have hv := NeZero.ne v
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  have hc : (v ^ D.d i) ^ negA D i j * (v ^ D.d i * (v ^ D.d i) ^ negA D i j)⁻¹ =
      (v ^ D.d i)⁻¹ := by field_simp
  have hY : braidFj R v i j = ((qFactorial (v ^ D.d i) (negA D i j))⁻¹ * (-1) ^ negA D i j *
      (v ^ D.d i) ^ negA D i j) •
      BraidDiagonal.X (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (F R v i) (F R v j) (negA D i j) := by
    rw [BraidDiagonal.X_eq_serreAux hq0 (pow_ne_zero _ hq0), hc]; rfl
  rw [← serreAux_one, one_sub_cartanMatrix_toNat hij, hY, BraidDiagonal.serreAux_smul_right,
    braidFi, (braidDiagonal_hyp R v hv hij hq).serreAux_centre_F (K_neg_mul_Kt i), smul_zero]

end QuantumGroup
