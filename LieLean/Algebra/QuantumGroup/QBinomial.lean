/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Quantum integers, quantum binomial coefficients and quantum Serre elements

Let `k` be a field and `v ∈ k`. We define the (symmetric) quantum integers, factorials and binomial
coefficients ([Lus] §§1.3.1, 1.3.3, [Jan] §§0.1–0.2):
`[n]_v = Σ_{s < n} v^{n-1-2s} = (vⁿ - v⁻ⁿ)/(v - v⁻¹)`, `[n]_v! = [1]_v ⋯ [n]_v` and
`[n j]_v`, the latter defined through the Pascal rule
`[n+1, j+1]_v = v^{-(j+1)} [n, j+1]_v + v^{n-j} [n, j]_v`, so that they make sense for every `v`.

For elements `a, b` of a `k`-algebra `B`, the *quantum Serre element* is
`qSerre v m a b = Σ_{r=0}^{m} (-1)^r [m r]_v a^{m-r} b a^r`.

The main technical result is `qSerre_add`: if `w u = v² u w`, `w b = v^{-m} b w` and
`u b' = v^m b' u`, then
`qSerre v (m+1) (u + w) (b + b') = qSerre v (m+1) u b + qSerre v (m+1) w b'`.
This single identity yields the compatibility of the quantum Serre relations with Lusztig's
comultiplication `r` and with the skew derivations `rᵢ, ᵢr` of `'f` (cf. [Lus] 1.4.2–1.4.3),
and with the comultiplication of `U_q(𝔤)` ([Jan] Lemma 4.10). The proof is our own
reconstruction and avoids the usual expansion into `q`-multinomials: writing
`D_λ(b) = z b - λ b z`, the Serre element factors as `D_{λ_m} ∘ ⋯ ∘ D_{λ_0}` with
`λ_s = v^{m-2s}` (`serreAux_succ`, `serreAux_succ'`), and if `b` is a `w`-eigenvector
(`w b = λ b w`) then `D^{u+w}_λ(b) = D^u_λ(b)`, which is again a `w`-eigenvector.

## Main definitions

* `QuantumGroup.qInt`, `QuantumGroup.qFactorial`, `QuantumGroup.qBinomial`.
* `QuantumGroup.qSerre`: the quantum Serre element (in binomial form).
* `QuantumGroup.qIntU`, `QuantumGroup.qBinomialU`, `QuantumGroup.qSerreU`: the same with respect
  to a unit `q` of a commutative ring (`map_qBinomialU` relates them to `qBinomial`).

## Main results

* `QuantumGroup.qBinomial_mul_qFactorial_mul_qFactorial`: `[n j]! [j]! [n-j]! = [n]!`.
* `QuantumGroup.qBinomial_one`: at `v = 1` the quantum binomials are the binomial coefficients.
* `QuantumGroup.qInt_ne_zero`: `[n]_v ≠ 0` if `v^{2n} ≠ 1`.
* `QuantumGroup.qBinomial_symm`: `[n, n-k]_v = [n k]_v`.
* `QuantumGroup.qSerre_add`: the additivity of the Serre element described above.
* `QuantumGroup.qSerre_eq_zero_of_mul_eq_smul`: `S(a, b) = 0` if `b a = v^{-m} a b`
  (the identity [Lus] 1.3.4(a)).
* `QuantumGroup.qSerre_op`, `QuantumGroup.qSerre_mul_mul`: Serre elements in the opposite
  algebra and of `q`-twisted generators.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §1.3–1.4.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 0 and Ch. 4.
-/

open Finset

namespace LieLean.QuantumGroup

variable {k : Type*} [Field k]

/-! ### Quantum integers and binomial coefficients -/

/-- The symmetric quantum integer `[n]_v = Σ_{s < n} v^{n-1-2s}` ([Lus] 1.3.3); it equals
`(vⁿ - v⁻ⁿ)/(v - v⁻¹)` when `v² ≠ 1` (`qInt_mul_sub`). -/
def qInt (v : k) (n : ℕ) : k := ∑ s ∈ range n, v ^ (n - 1 - s) * v⁻¹ ^ s

/-- The quantum factorial `[n]_v! = [1]_v [2]_v ⋯ [n]_v` ([Lus] 1.3.3). -/
def qFactorial (v : k) : ℕ → k
  | 0 => 1
  | n + 1 => qInt v (n + 1) * qFactorial v n

/-- The quantum binomial coefficient `[n j]_v`, defined by the Pascal rule
`[n+1, j+1] = v^{-(j+1)} [n, j+1] + v^{n-j} [n, j]` ([Lus] 1.3.1(e)). It equals
`[n]!/([j]! [n-j]!)` whenever the factorials are nonzero
(`qBinomial_mul_qFactorial_mul_qFactorial`). -/
def qBinomial (v : k) : ℕ → ℕ → k
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, j + 1 => v⁻¹ ^ (j + 1) * qBinomial v n (j + 1) + v ^ (n - j) * qBinomial v n j

variable (v : k)

@[simp] lemma qInt_zero : qInt v 0 = 0 := by simp [qInt]

@[simp] lemma qFactorial_zero : qFactorial v 0 = 1 := rfl

lemma qFactorial_succ (n : ℕ) : qFactorial v (n + 1) = qInt v (n + 1) * qFactorial v n := rfl

@[simp] lemma qBinomial_zero_right (n : ℕ) : qBinomial v n 0 = 1 := by cases n <;> rfl

@[simp] lemma qBinomial_zero_succ (j : ℕ) : qBinomial v 0 (j + 1) = 0 := rfl

lemma qBinomial_succ_succ (n j : ℕ) : qBinomial v (n + 1) (j + 1) =
    v⁻¹ ^ (j + 1) * qBinomial v n (j + 1) + v ^ (n - j) * qBinomial v n j := rfl

lemma qBinomial_eq_zero_of_lt {n j : ℕ} (h : n < j) : qBinomial v n j = 0 := by
  induction n generalizing j with
  | zero => obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'; rfl
  | succ n ih =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [qBinomial_succ_succ, ih (by omega), ih (by omega)]
    ring

@[simp] lemma qBinomial_succ_self (n : ℕ) : qBinomial v n (n + 1) = 0 :=
  qBinomial_eq_zero_of_lt v (Nat.lt_succ_self n)

@[simp] lemma qBinomial_self (n : ℕ) : qBinomial v n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [qBinomial_succ_succ, ih]

/-- At `v = 1` the quantum binomial coefficients are the ordinary binomial coefficients. -/
theorem qBinomial_one (n j : ℕ) : qBinomial (1 : k) n j = n.choose j := by
  induction n generalizing j with
  | zero => cases j <;> simp
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j => simp [qBinomial_succ_succ, ih, Nat.choose_succ_succ', add_comm]

variable {v}

lemma qInt_add (a b : ℕ) :
    qInt v (a + b) = v⁻¹ ^ b * qInt v a + v ^ a * qInt v b := by
  rw [qInt, add_comm a b, Finset.sum_range_add, add_comm, qInt, qInt, Finset.mul_sum,
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun s hs ↦ ?_
    have hs := Finset.mem_range.1 hs
    rw [show b + a - 1 - (b + s) = a - 1 - s by omega, pow_add]
    ring
  · refine Finset.sum_congr rfl fun s hs ↦ ?_
    have hs := Finset.mem_range.1 hs
    rw [show b + a - 1 - s = a + (b - 1 - s) by omega, pow_add]
    ring

lemma qInt_succ (n : ℕ) : qInt v (n + 1) = v⁻¹ * qInt v n + v ^ n := by
  rw [qInt_add]; simp [qInt]

/-- `(v - v⁻¹) [n]_v = vⁿ - v⁻ⁿ`. -/
lemma qInt_mul_sub (n : ℕ) : (v - v⁻¹) * qInt v n = v ^ n - v⁻¹ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qInt_succ, mul_add, mul_left_comm, ih]
    ring

/-- `[n]_v ≠ 0` as soon as `v^{2n} ≠ 1`. -/
theorem qInt_ne_zero (hv : v ≠ 0) {n : ℕ} (h : v ^ (2 * n) ≠ 1) : qInt v n ≠ 0 := by
  intro h0
  have := qInt_mul_sub (v := v) n
  rw [h0, mul_zero, eq_comm, sub_eq_zero] at this
  apply h
  rw [two_mul, pow_add]
  nth_rewrite 2 [this]
  rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hv)]

theorem qFactorial_ne_zero (hv : v ≠ 0) {n : ℕ} (h : ∀ m, 0 < m → m ≤ n → v ^ (2 * m) ≠ 1) :
    qFactorial v n ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qFactorial_succ]
    exact mul_ne_zero (qInt_ne_zero hv (h _ n.succ_pos le_rfl))
      (ih fun m hm hmn ↦ h m hm (hmn.trans n.le_succ))

/-- `[n j]_v [j]_v! [n-j]_v! = [n]_v!` for `j ≤ n` ([Lus] 1.3.3). -/
theorem qBinomial_mul_qFactorial_mul_qFactorial {n j : ℕ} (hj : j ≤ n) :
    qBinomial v n j * qFactorial v j * qFactorial v (n - j) = qFactorial v n := by
  induction n generalizing j with
  | zero => obtain rfl : j = 0 := by omega
            simp
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j =>
      rcases Nat.eq_or_lt_of_le hj with h | h
      · obtain rfl : j = n := by omega
        simp
      · have h1 := ih (j := j + 1) (by omega)
        have h2 := ih (j := j) (by omega)
        rw [show n + 1 - (j + 1) = n - j by omega, qBinomial_succ_succ]
        rw [show n - j = (n - (j + 1)) + 1 by omega] at h2 ⊢
        have key : qInt v (n + 1) = v⁻¹ ^ (j + 1) * qInt v (n - (j + 1) + 1) +
            v ^ (n - (j + 1) + 1) * qInt v (j + 1) := by
          rw [← qInt_add, show n - (j + 1) + 1 + (j + 1) = n + 1 by omega]
        rw [qFactorial_succ v j] at h1
        rw [qFactorial_succ v (n - (j + 1))] at h2
        rw [qFactorial_succ v (n - (j + 1)), qFactorial_succ v j, qFactorial_succ v n]
        linear_combination (-qFactorial v n) * key +
          (v⁻¹ ^ (j + 1) * qInt v (n - (j + 1) + 1)) * h1 +
          (v ^ (n - (j + 1) + 1) * qInt v (j + 1)) * h2

variable (v) in
lemma qBinomial_one_right (n : ℕ) : qBinomial v n 1 = qInt v n := by
  induction n with
  | zero => simp
  | succ n ih => rw [qBinomial_succ_succ, ih, qInt_succ]; simp

variable (v) in
/-- `(v^{n-k} - v^{k-n}) [n k]_v = (v^{k+1} - v^{-k-1}) [n, k+1]_v`, i.e. `[n-k] [n k] = [k+1]
[n, k+1]` up to the factor `v - v⁻¹`. -/
theorem qBinomial_mul_sub (n k : ℕ) :
    (v ^ (n - k) - v⁻¹ ^ (n - k)) * qBinomial v n k =
      (v ^ (k + 1) - v⁻¹ ^ (k + 1)) * qBinomial v n (k + 1) := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp [qBinomial_one_right, qInt_mul_sub]
    | succ k =>
      rcases le_or_gt n k with hnk | hnk
      · rw [qBinomial_eq_zero_of_lt v (by omega : n + 1 < k + 1 + 1),
          show n + 1 - (k + 1) = 0 by omega]
        simp
      · obtain ⟨p, hp⟩ : ∃ p, n - k = p + 1 := ⟨n - k - 1, by omega⟩
        have h1 := ih k
        have h2 := ih (k + 1)
        rw [hp] at h1
        rw [show n - (k + 1) = p by omega] at h2
        rw [show n + 1 - (k + 1) = p + 1 by omega, qBinomial_succ_succ, qBinomial_succ_succ, hp,
          show n - (k + 1) = p by omega]
        linear_combination (v ^ (p + 1)) * h1 + (v⁻¹ ^ (k + 2)) * h2

variable (v) in
/-- The symmetry `[n, n-k]_v = [n k]_v` of quantum binomial coefficients. -/
theorem qBinomial_symm {n k : ℕ} (hk : k ≤ n) : qBinomial v n (n - k) = qBinomial v n k := by
  induction n generalizing k with
  | zero => obtain rfl : k = 0 := by omega
            simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rcases Nat.eq_or_lt_of_le hk with h | h
      · obtain rfl : k = n := by omega
        simp
      · obtain ⟨p, hp⟩ : ∃ p, n - k = p + 1 := ⟨n - k - 1, by omega⟩
        rw [show n + 1 - (k + 1) = p + 1 by omega, qBinomial_succ_succ, qBinomial_succ_succ,
          show n - p = k + 1 by omega, hp]
        have e1 : qBinomial v n (p + 1) = qBinomial v n k := by rw [← hp]; exact ih (by omega)
        have e2 : qBinomial v n p = qBinomial v n (k + 1) := by
          rw [show p = n - (k + 1) by omega]; exact ih (by omega)
        have h1 := qBinomial_mul_sub v n k
        rw [hp] at h1
        rw [e1, e2]
        linear_combination -h1

variable (v) in
/-- The quantum binomial coefficients are invariant under `v ↦ v⁻¹`. -/
theorem qBinomial_inv (n k : ℕ) : qBinomial v⁻¹ n k = qBinomial v n k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [qBinomial_succ_succ, qBinomial_succ_succ, ih, ih, inv_inv]
      linear_combination -qBinomial_mul_sub v n k

/-! ### Quantum Serre elements -/

variable {B : Type*} [Ring B] [Algebra k B]

variable (v) in
/-- The quantum Serre element `Σ_{r=0}^{m} (-1)^r [m r]_v a^{m-r} b a^r` ([Jan] 4.3 (R6));
up to the factor `[m]_v!` this is Lusztig's divided-power form `qSerreDiv` (`qSerreDiv_eq`). -/
def qSerre (m : ℕ) (a b : B) : B :=
  ∑ r ∈ range (m + 1), ((-1) ^ r * qBinomial v m r) • (a ^ (m - r) * b * a ^ r)

variable (v) in
/-- The divided power `a^{(n)} = a^n / [n]_v!` ([Lus] 1.4.1). -/
def qDivPow (n : ℕ) (a : B) : B := (qFactorial v n)⁻¹ • a ^ n

variable (v) in
/-- The quantum Serre element in Lusztig's divided-power form
`Σ_{r+s=m} (-1)^r a^{(s)} b a^{(r)}` ([Lus] 1.4.3). -/
def qSerreDiv (m : ℕ) (a b : B) : B :=
  ∑ r ∈ range (m + 1), (-1 : k) ^ r • (qDivPow v (m - r) a * b * qDivPow v r a)

/-- If `[m]_v! ≠ 0`, the divided-power Serre element is `[m]_v!⁻¹` times the binomial one. -/
theorem qSerreDiv_eq {m : ℕ} (hm : qFactorial v m ≠ 0) (a b : B) :
    qSerreDiv v m a b = (qFactorial v m)⁻¹ • qSerre v m a b := by
  simp only [qSerreDiv, qSerre, qDivPow, Finset.smul_sum, smul_smul, smul_mul_assoc,
    mul_smul_comm]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hr : r ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  have h := qBinomial_mul_qFactorial_mul_qFactorial (v := v) hr
  have h1 : qFactorial v r ≠ 0 := fun h0 ↦ hm (by rw [← h, h0]; ring)
  have h2 : qFactorial v (m - r) ≠ 0 := fun h0 ↦ hm (by rw [← h, h0]; ring)
  have h3 : qBinomial v m r ≠ 0 := fun h0 ↦ hm (by rw [← h, h0]; ring)
  congr 1
  rw [← h]
  field_simp

variable (v) in
/-- An auxiliary rescaled Serre element `Σ_r (-1)^r [m r]_v c^r a^{m-r} b a^r`, used to set up the
induction in `qSerre_add`. -/
def serreAux (c : k) (m : ℕ) (a b : B) : B :=
  ∑ r ∈ range (m + 1), ((-1) ^ r * qBinomial v m r * c ^ r) • (a ^ (m - r) * b * a ^ r)

lemma serreAux_one (m : ℕ) (a b : B) : serreAux v 1 m a b = qSerre v m a b := by
  simp [serreAux, qSerre]

@[simp] lemma qSerre_zero (a b : B) : qSerre v 0 a b = b := by simp [qSerre]

lemma map_serreAux {B' : Type*} [Ring B'] [Algebra k B'] (f : B →ₐ[k] B') (c : k) (m : ℕ)
    (a b : B) : f (serreAux v c m a b) = serreAux v c m (f a) (f b) := by
  simp [serreAux, map_sum, map_smul, map_mul, map_pow]

lemma map_qSerre {B' : Type*} [Ring B'] [Algebra k B'] (f : B →ₐ[k] B') (m : ℕ)
    (a b : B) : f (qSerre v m a b) = qSerre v m (f a) (f b) := by
  simp [← serreAux_one, map_serreAux]

lemma serreAux_sub_smul (c : k) (m : ℕ) (a x y : B) (μ : k) :
    serreAux v c m a (x - μ • y) = serreAux v c m a x - μ • serreAux v c m a y := by
  simp only [serreAux, mul_sub, sub_mul, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum,
    mul_smul_comm, smul_mul_assoc]
  congr 1
  exact Finset.sum_congr rfl fun _ _ ↦ smul_comm _ _ _

lemma serreAux_mul_left (c : k) (m : ℕ) (a b : B) :
    serreAux v c m a (a * b) = a * serreAux v c m a b := by
  simp only [serreAux, Finset.mul_sum, mul_smul_comm]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  congr 1
  simp only [mul_assoc]
  rw [← mul_assoc a (a ^ (m - r)), (Commute.self_pow a _).eq, mul_assoc]

lemma serreAux_mul_right (c : k) (m : ℕ) (a b : B) :
    serreAux v c m a (b * a) = serreAux v c m a b * a := by
  simp only [serreAux, Finset.sum_mul, smul_mul_assoc]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  congr 1
  simp only [mul_assoc]
  rw [(Commute.self_pow a _).eq]

/-- The inner recursion for Serre elements: `D_{c vᵐ}` applied first. -/
theorem serreAux_succ (hv : v ≠ 0) (c : k) (m : ℕ) (a b : B) :
    serreAux v c (m + 1) a b = serreAux v (c * v⁻¹) m a (a * b - (c * v ^ m) • (b * a)) := by
  rw [serreAux_sub_smul]
  simp only [serreAux]
  rw [Finset.sum_range_succ' _ (m + 1)]
  simp only [qBinomial_succ_succ, pow_zero, mul_one, qBinomial_zero_right, one_smul,
    Nat.sub_zero, add_mul, mul_add, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  -- the sum over `[m, r+1]`
  have h1 : ∑ r ∈ range (m + 1), ((-1) ^ (r + 1) * (v⁻¹ ^ (r + 1) * qBinomial v m (r + 1)) *
        c ^ (r + 1)) • (a ^ (m + 1 - (r + 1)) * b * a ^ (r + 1)) + a ^ (m + 1) * b =
      ∑ r ∈ range (m + 1), ((-1) ^ r * qBinomial v m r * (c * v⁻¹) ^ r) •
        (a ^ (m - r) * (a * b) * a ^ r) := by
    conv_lhs => rw [Finset.sum_range_succ, qBinomial_succ_self]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [mul_zero, zero_mul, zero_smul, add_zero, pow_zero, qBinomial_zero_right,
      mul_one, one_smul, Nat.sub_zero]
    congr 1
    · refine Finset.sum_congr rfl fun r hr ↦ ?_
      have hr := Finset.mem_range.1 hr
      rw [show m + 1 - (r + 1) = m - (r + 1) + 1 by omega]
      congr 1
      · rw [mul_pow]; ring
      · rw [pow_succ, mul_assoc (a ^ (m - (r + 1))) a b]
    · rw [← mul_assoc, ← pow_succ]
  -- the sum over `[m, r]`
  have h2 : ∑ r ∈ range (m + 1), ((-1) ^ (r + 1) * (v ^ (m - r) * qBinomial v m r) *
        c ^ (r + 1)) • (a ^ (m + 1 - (r + 1)) * b * a ^ (r + 1)) =
      -∑ r ∈ range (m + 1), (c * v ^ m * ((-1) ^ r * qBinomial v m r * (c * v⁻¹) ^ r)) •
        (a ^ (m - r) * (b * a) * a ^ r) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r hr ↦ ?_
    have hr := Finset.mem_range.1 hr
    rw [← neg_smul]
    congr 1
    · have hvm : v ^ m = v ^ (m - r) * v ^ r := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      have hvr : v ^ r * v⁻¹ ^ r = 1 := by rw [← mul_pow, mul_inv_cancel₀ hv, one_pow]
      rw [hvm, mul_pow]
      linear_combination ((-1) ^ r * c ^ (r + 1) * v ^ (m - r) * qBinomial v m r) * hvr
    · simp only [Nat.add_sub_add_right, mul_assoc, ← pow_succ']
  rw [add_right_comm, h1, h2, sub_eq_add_neg]

/-- The outer recursion for Serre elements: `D_{c vᵐ}` applied last. -/
theorem serreAux_succ' (hv : v ≠ 0) (c : k) (m : ℕ) (a b : B) :
    serreAux v c (m + 1) a b = a * serreAux v (c * v⁻¹) m a b -
      (c * v ^ m) • (serreAux v (c * v⁻¹) m a b * a) := by
  rw [serreAux_succ hv, serreAux_sub_smul, serreAux_mul_left, serreAux_mul_right]

lemma mul_pow_of_mul_eq_smul {w a : B} {t : k} (h : w * a = t • (a * w)) (n : ℕ) :
    w * a ^ n = t ^ n • (a ^ n * w) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, h, mul_smul_comm, smul_smul,
      ← mul_assoc, pow_succ]

/-- Serre elements of `w`-eigenvectors are `w`-eigenvectors. -/
lemma mul_serreAux_of_mul_eq_smul {w a b : B} {t μ : k} (ha : w * a = t • (a * w))
    (hb : w * b = μ • (b * w)) (c : k) (m : ℕ) :
    w * serreAux v c m a b = (μ * t ^ m) • (serreAux v c m a b * w) := by
  have key : ∀ p r, w * (a ^ p * b * a ^ r) = (μ * t ^ (p + r)) • (a ^ p * b * a ^ r * w) := by
    intro p r
    calc w * (a ^ p * b * a ^ r) = (w * a ^ p) * b * a ^ r := by simp only [mul_assoc]
    _ = t ^ p • (a ^ p * (w * b) * a ^ r) := by
      rw [mul_pow_of_mul_eq_smul ha]; simp only [smul_mul_assoc, mul_assoc]
    _ = (t ^ p * μ) • (a ^ p * b * (w * a ^ r)) := by
      rw [hb]; simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    _ = (t ^ p * μ * t ^ r) • (a ^ p * b * a ^ r * w) := by
      rw [mul_pow_of_mul_eq_smul ha]
      simp only [mul_smul_comm, smul_smul, mul_assoc]
    _ = _ := by congr 1; rw [pow_add]; ring
  simp only [serreAux, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, mul_smul_comm,
    smul_mul_assoc]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  rw [key, Nat.sub_add_cancel (by simpa [Nat.lt_succ_iff] using hr), smul_comm]

/-- If `w u = v⁻² u w` and `w b = c vᵐ b w`, then the `w`-part does not contribute to the Serre
element of `u + w` and `b`. -/
theorem serreAux_add_left (hv : v ≠ 0) {u w : B} (hwu : w * u = v⁻¹ ^ 2 • (u * w)) (m : ℕ) :
    ∀ (c : k) (b : B), w * b = (c * v ^ m) • (b * w) →
      serreAux v c (m + 1) (u + w) b = serreAux v c (m + 1) u b := by
  induction m with
  | zero =>
    intro c b hb
    simp [serreAux, Finset.sum_range_succ, hb, add_mul, mul_add]
    abel
  | succ m ih =>
    intro c b hb
    have key : (u + w) * b - (c * v ^ (m + 1)) • (b * (u + w)) =
        u * b - (c * v ^ (m + 1)) • (b * u) := by
      rw [add_mul, mul_add, hb, smul_add]; abel
    rw [serreAux_succ hv, serreAux_succ hv c (m + 1) u b, key]
    apply ih
    set l := c * v ^ (m + 1)
    have e1 : w * (u * b) = (v⁻¹ ^ 2 * l) • (u * b * w) := by
      rw [← mul_assoc, hwu, smul_mul_assoc, mul_assoc, hb, mul_smul_comm, smul_smul, mul_assoc]
    have e2 : w * (b * u) = (l * v⁻¹ ^ 2) • (b * u * w) := by
      rw [← mul_assoc, hb, smul_mul_assoc, mul_assoc, hwu, mul_smul_comm, smul_smul, ← mul_assoc]
    have hvv : v⁻¹ * v = 1 := inv_mul_cancel₀ hv
    rw [mul_sub, mul_smul_comm, e1, e2, sub_mul, smul_mul_assoc, smul_sub, smul_smul, smul_smul]
    congr 2
    · simp only [l]; linear_combination (c * v⁻¹ * v ^ m) * hvv
    · simp only [l]; linear_combination (c * c * v ^ (2 * m + 1) * v⁻¹) * hvv

/-- If `w u = v² u w` and `w b = c v⁻ᵐ b w`, then the `w`-part does not contribute to the Serre
element of `u + w` and `b`. -/
theorem serreAux_add_right (hv : v ≠ 0) {u w : B} (hwu : w * u = v ^ 2 • (u * w)) (m : ℕ) :
    ∀ (c : k) (b : B), w * b = (c * v⁻¹ ^ m) • (b * w) →
      serreAux v c (m + 1) (u + w) b = serreAux v c (m + 1) u b := by
  induction m with
  | zero =>
    intro c b hb
    simp [serreAux, Finset.sum_range_succ, hb, add_mul, mul_add]
    abel
  | succ m ih =>
    intro c b hb
    have hb' : w * b = (c * v⁻¹ * v⁻¹ ^ m) • (b * w) := by rw [hb, mul_assoc, ← pow_succ']
    rw [serreAux_succ' hv, serreAux_succ' hv c (m + 1) u b, ih _ _ hb']
    have hX := mul_serreAux_of_mul_eq_smul (v := v) hwu hb' (c * v⁻¹) (m + 1)
    rw [add_mul, mul_add, hX, smul_add]
    have : c * v⁻¹ * v⁻¹ ^ m * (v ^ 2) ^ (m + 1) = c * v ^ (m + 1) := by
      have hvv : v⁻¹ ^ (m + 1) * v ^ (m + 1) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hv, one_pow]
      linear_combination (c * v ^ (m + 1)) * hvv
    rw [this]
    abel

/-- The additivity of quantum Serre elements: if `w u = v² u w`, `w b = v⁻ᵐ b w` and
`u b' = vᵐ b' u`, then `S(u + w, b + b') = S(u, b) + S(w, b')` for the Serre element `S` of
degree `m + 1`. It replaces the form computation of [Lus] 1.4.4–1.4.6 and is the core of
[Jan] Lemma 4.10; the proof (via the factorization of `S` into twisted commutators) is our own. -/
theorem qSerre_add (hv : v ≠ 0) {u w b b' : B} {m : ℕ} (hwu : w * u = v ^ 2 • (u * w))
    (hb : w * b = v⁻¹ ^ m • (b * w)) (hb' : u * b' = v ^ m • (b' * u)) :
    qSerre v (m + 1) (u + w) (b + b') = qSerre v (m + 1) u b + qSerre v (m + 1) w b' := by
  have huw : u * w = v⁻¹ ^ 2 • (w * u) := by
    rw [hwu, smul_smul, ← mul_pow, inv_mul_cancel₀ hv, one_pow, one_smul]
  have hadd : ∀ x y : B, qSerre v (m + 1) (u + w) (x + y) =
      qSerre v (m + 1) (u + w) x + qSerre v (m + 1) (u + w) y := by
    intro x y
    simp only [qSerre, mul_add, add_mul, smul_add, Finset.sum_add_distrib]
  rw [hadd, ← serreAux_one, ← serreAux_one, serreAux_add_right hv hwu m 1 b (by simpa using hb),
    add_comm u w, serreAux_add_left hv huw m 1 b' (by simpa using hb'), serreAux_one,
    serreAux_one]

@[simp] lemma qSerre_zero_right (m : ℕ) (a : B) : qSerre v m a 0 = 0 := by simp [qSerre]

lemma qSerre_add_right (m : ℕ) (a b b' : B) :
    qSerre v m a (b + b') = qSerre v m a b + qSerre v m a b' := by
  simp only [qSerre, mul_add, add_mul, smul_add, Finset.sum_add_distrib]

/-- `Σ_{r=0}^{m+1} (-1)^r [m+1, r]_v v^{-mr} = 0` ([Lus] 1.3.4(a)). -/
theorem sum_qBinomial_mul_inv_pow_eq_zero (hv : v ≠ 0) (m : ℕ) :
    ∑ r ∈ range (m + 2), (-1) ^ r * qBinomial v (m + 1) r * (v⁻¹ ^ m) ^ r = 0 := by
  have h := serreAux_succ (B := k) hv (v⁻¹ ^ m) m 1 1
  have h1 : v⁻¹ ^ m * v ^ m = 1 := by rw [← mul_pow, inv_mul_cancel₀ hv, one_pow]
  rw [h1, one_smul, mul_one, sub_self] at h
  simpa [serreAux] using h

/-- If `b a = v^{-m} a b`, then the Serre element `S(a, b)` of degree `m + 1` vanishes. -/
theorem qSerre_eq_zero_of_mul_eq_smul (hv : v ≠ 0) {m : ℕ} {a b : B}
    (h : b * a = v⁻¹ ^ m • (a * b)) : qSerre v (m + 1) a b = 0 := by
  have key : ∀ r ≤ m + 1, a ^ (m + 1 - r) * b * a ^ r = (v⁻¹ ^ m) ^ r • (a ^ (m + 1) * b) := by
    intro r hr
    rw [mul_assoc, mul_pow_of_mul_eq_smul h, mul_smul_comm, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel hr]
  calc qSerre v (m + 1) a b
      = ∑ r ∈ range (m + 2), ((-1) ^ r * qBinomial v (m + 1) r * (v⁻¹ ^ m) ^ r) •
          (a ^ (m + 1) * b) := by
        refine Finset.sum_congr rfl fun r hr ↦ ?_
        rw [key r (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)), smul_smul]
    _ = 0 := by rw [← Finset.sum_smul, sum_qBinomial_mul_inv_pow_eq_zero hv, zero_smul]

/-! ### Opposite algebras and twisted generators -/

/-- Serre elements in the opposite algebra: `S(aᵒᵖ, bᵒᵖ) = (-1)^m S(a, b)ᵒᵖ`. -/
theorem qSerre_op (m : ℕ) (a b : B) : qSerre v m (MulOpposite.op a) (MulOpposite.op b) =
    (-1 : k) ^ m • MulOpposite.op (qSerre v m a b) := by
  simp only [qSerre, ← MulOpposite.op_pow, ← MulOpposite.op_mul, Finset.op_sum,
    MulOpposite.op_smul, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hr : r ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  rw [show m + 1 - 1 - r = m - r by omega, show m - (m - r) = r by omega, qBinomial_symm v hr]
  rw [← mul_assoc (a ^ (m - r))]
  congr 1
  have h1 : (-1 : k) ^ m = (-1) ^ (m - r) * (-1) ^ r := by rw [← pow_add, Nat.sub_add_cancel hr]
  have h2 : (-1 : k) ^ r * (-1) ^ r = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  rw [h1]
  linear_combination (-((-1) ^ (m - r) * qBinomial v m r)) * h2

lemma pow_mul_pow_of_mul_eq_smul {w a : B} {t : k} (h : w * a = t • (a * w)) (m n : ℕ) :
    w ^ m * a ^ n = t ^ (m * n) • (a ^ n * w ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_assoc, mul_pow_of_mul_eq_smul h, mul_smul_comm, ← mul_assoc, ih,
      smul_mul_assoc, smul_smul, mul_assoc, ← pow_succ, ← pow_add, Nat.succ_mul, add_comm]

lemma mul_pow_eq_smul {g e : B} {t : k} (ht : t ≠ 0) (h : g * e = t • (e * g)) (n : ℕ) :
    (g * e) ^ n = t⁻¹ ^ n.choose 2 • (g ^ n * e ^ n) := by
  have heg : e * g = t⁻¹ • (g * e) := by rw [h, smul_smul, inv_mul_cancel₀ ht, one_smul]
  induction n with
  | zero => simp
  | succ n ih =>
    have hen : e ^ n * g = t⁻¹ ^ n • (g * e ^ n) := by
      simpa using pow_mul_pow_of_mul_eq_smul heg n 1
    calc (g * e) ^ (n + 1) = (g * e) ^ n * (g * e) := pow_succ _ _
      _ = t⁻¹ ^ n.choose 2 • (g ^ n * (e ^ n * g) * e) := by
        rw [ih]; simp only [smul_mul_assoc, mul_assoc]
      _ = (t⁻¹ ^ n.choose 2 * t⁻¹ ^ n) • (g ^ n * g * (e ^ n * e)) := by
        rw [hen]; simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
      _ = _ := by
        rw [← pow_succ, ← pow_succ, Nat.choose_succ_succ', Nat.choose_one_right,
          mul_comm (t⁻¹ ^ n.choose 2), ← pow_add]

private lemma choose_two_add (a b : ℕ) : (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, Nat.choose_succ_succ', Nat.choose_one_right, ih, Nat.choose_succ_succ',
      Nat.choose_one_right]
    ring

/-- Serre elements of twisted generators: if `g e = t e g`, `e h = s h e`, `f g = s g f` and
`g h = h g`, then `S(g e, h f) = t^{-C(M,2)} s^M g^M h S(e, f)`. -/
theorem qSerre_mul_mul {t s : k} (ht : t ≠ 0) {g e h f : B} (hge : g * e = t • (e * g))
    (heh : e * h = s • (h * e)) (hfg : f * g = s • (g * f)) (hgh : g * h = h * g) (M : ℕ) :
    qSerre v M (g * e) (h * f) = (t⁻¹ ^ M.choose 2 * s ^ M) • (g ^ M * h * qSerre v M e f) := by
  have heg : e * g = t⁻¹ • (g * e) := by rw [hge, smul_smul, inv_mul_cancel₀ ht, one_smul]
  simp only [qSerre, Finset.mul_sum, Finset.smul_sum, mul_smul_comm, smul_smul]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hr : r ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  have key : (g * e) ^ (M - r) * (h * f) * (g * e) ^ r =
      (t⁻¹ ^ M.choose 2 * s ^ M) • (g ^ M * h * (e ^ (M - r) * f * e ^ r)) := by
    rw [mul_pow_eq_smul ht hge, mul_pow_eq_smul ht hge]
    have e1 : e ^ (M - r) * h = s ^ (M - r) • (h * e ^ (M - r)) := by
      simpa using pow_mul_pow_of_mul_eq_smul heh (M - r) 1
    have e2 : f * g ^ r = s ^ r • (g ^ r * f) := by
      simpa using pow_mul_pow_of_mul_eq_smul hfg 1 r
    have e3 : e ^ (M - r) * g ^ r = t⁻¹ ^ ((M - r) * r) • (g ^ r * e ^ (M - r)) :=
      pow_mul_pow_of_mul_eq_smul heg (M - r) r
    have e4 : g ^ (M - r) * h * g ^ r = g ^ M * h := by
      rw [mul_assoc, ← ((Commute.pow_left hgh r).eq), ← mul_assoc, ← pow_add,
        Nat.sub_add_cancel hr]
    calc t⁻¹ ^ (M - r).choose 2 • (g ^ (M - r) * e ^ (M - r)) * (h * f) *
          t⁻¹ ^ r.choose 2 • (g ^ r * e ^ r)
        = (t⁻¹ ^ (M - r).choose 2 * t⁻¹ ^ r.choose 2) •
            (g ^ (M - r) * (e ^ (M - r) * h) * (f * g ^ r) * e ^ r) := by
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
          congr 1; ring
      _ = (t⁻¹ ^ (M - r).choose 2 * t⁻¹ ^ r.choose 2 * s ^ (M - r) * s ^ r) •
            (g ^ (M - r) * h * (e ^ (M - r) * g ^ r) * f * e ^ r) := by
          rw [e1, e2]
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
          congr 1; ring
      _ = (t⁻¹ ^ (M - r).choose 2 * t⁻¹ ^ r.choose 2 * s ^ (M - r) * s ^ r *
            t⁻¹ ^ ((M - r) * r)) • (g ^ (M - r) * h * g ^ r * e ^ (M - r) * f * e ^ r) := by
          rw [e3]
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
      _ = _ := by
          rw [e4]
          congr 1
          · have hM : M.choose 2 = (M - r).choose 2 + r.choose 2 + (M - r) * r := by
              rw [← choose_two_add, Nat.sub_add_cancel hr]
            have hs : s ^ M = s ^ (M - r) * s ^ r := by rw [← pow_add, Nat.sub_add_cancel hr]
            rw [hM, hs, pow_add, pow_add]
            ring
          · simp only [mul_assoc]
  rw [key, smul_smul, mul_comm ((-1) ^ r * qBinomial v M r)]

lemma qSerre_inv (m : ℕ) (a b : B) : qSerre v⁻¹ m a b = qSerre v m a b := by
  simp [qSerre, qBinomial_inv]

lemma qSerre_smul_smul (m : ℕ) (a b : B) (c d : k) :
    qSerre v m (c • a) (d • b) = (c ^ m * d) • qSerre v m a b := by
  simp only [qSerre, Finset.smul_sum, smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hr : r ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  congr 1
  rw [show c ^ m = c ^ (m - r) * c ^ r by rw [← pow_add, Nat.sub_add_cancel hr]]
  ring

lemma map_qSerreDiv {B' : Type*} [Ring B'] [Algebra k B'] (f : B →ₐ[k] B') (m : ℕ)
    (a b : B) : f (qSerreDiv v m a b) = qSerreDiv v m (f a) (f b) := by
  simp [qSerreDiv, qDivPow, map_sum, map_smul, map_mul, map_pow]

@[simp] lemma qSerreDiv_zero_right (m : ℕ) (a : B) : qSerreDiv v m a 0 = 0 := by
  simp [qSerreDiv]

lemma qSerreDiv_smul_smul (m : ℕ) (a b : B) (c d : k) :
    qSerreDiv v m (c • a) (d • b) = (c ^ m * d) • qSerreDiv v m a b := by
  simp only [qSerreDiv, qDivPow, Finset.smul_sum, smul_pow, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hr : r ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  congr 1
  rw [show c ^ m = c ^ (m - r) * c ^ r by rw [← pow_add, Nat.sub_add_cancel hr]]
  ring

end LieLean.QuantumGroup

namespace LieLean.QuantumGroup

/-! ### Quantum integers and binomial coefficients with respect to a unit of a ring

The quantities above over a commutative ring `R`, for a unit `q ∈ Rˣ`; they map to those of
`φ q` under a ring homomorphism `φ : R → k` to a field (`map_qNatU`, `map_qBinomialU`). -/

variable {R : Type*} [CommRing R] (q : Rˣ)

/-- The quantum integer `[n]_q = Σ_{s < n} q^{n-1-2s}` for a unit `q` of a commutative ring. -/
def qNatU (n : ℕ) : R := ∑ s ∈ range n, ((q ^ (n - 1 - s) * q⁻¹ ^ s : Rˣ) : R)

/-- The quantum integer `[n]_q` for `n ∈ ℤ`, with `[-n]_q = -[n]_q`. -/
def qIntU : ℤ → R
  | .ofNat n => qNatU q n
  | .negSucc n => -qNatU q (n + 1)

/-- The quantum binomial coefficient `[n j]_q` for a unit `q` of a commutative ring, by the Pascal
rule of `QuantumGroup.qBinomial`. -/
def qBinomialU : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, j + 1 => ((q⁻¹ ^ (j + 1) : Rˣ) : R) * qBinomialU n (j + 1) +
      ((q ^ (n - j) : Rˣ) : R) * qBinomialU n j

variable {B : Type*} [Ring B] [Algebra R B]

/-- The quantum Serre element `Σ_{r=0}^{m} (-1)^r [m r]_q a^{m-r} b a^r` for a unit `q`. -/
def qSerreU (m : ℕ) (a b : B) : B :=
  ∑ r ∈ range (m + 1), ((-1) ^ r * qBinomialU q m r) • (a ^ (m - r) * b * a ^ r)

variable {k : Type*} [Field k] (φ : R →+* k)

lemma map_units_val_pow_inv (a b : ℕ) :
    φ ((q ^ a * q⁻¹ ^ b : Rˣ) : R) = φ q ^ a * (φ q)⁻¹ ^ b := by
  rw [Units.val_mul, map_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    map_pow, map_units_inv φ q]

lemma map_qNatU (n : ℕ) : φ (qNatU q n) = qInt (φ q) n := by
  simp only [qNatU, map_sum, map_units_val_pow_inv, qInt]

lemma map_qBinomialU (n j : ℕ) : φ (qBinomialU q n j) = qBinomial (φ q) n j := by
  induction n generalizing j with
  | zero => cases j <;> simp [qBinomialU, qBinomial]
  | succ n ih =>
    cases j with
    | zero => simp [qBinomialU]
    | succ j =>
      rw [qBinomialU, qBinomial_succ_succ, map_add, map_mul, map_mul, ih, ih,
        Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow, map_units_inv φ q]

/-- `(q - q⁻¹) [n]_q = qⁿ - q⁻ⁿ` after mapping to a field, for `n ∈ ℤ`. -/
lemma sub_mul_map_qIntU (n : ℤ) :
    (φ q - (φ q)⁻¹) * φ (qIntU q n) = φ q ^ n - φ q ^ (-n) := by
  cases n with
  | ofNat n =>
    rw [qIntU, map_qNatU, qInt_mul_sub]
    simp [zpow_neg]
  | negSucc n =>
    rw [qIntU, map_neg, map_qNatU, mul_neg, qInt_mul_sub, Int.neg_negSucc, zpow_natCast,
      zpow_negSucc, inv_pow]
    ring

/-- At `q ↦ 1` the quantum integer `[n]_q` becomes `n`. -/
lemma map_qIntU_of_eq_one (hφ : φ q = 1) (n : ℤ) : φ (qIntU q n) = n := by
  cases n with
  | ofNat n => simp [qIntU, map_qNatU, hφ, qInt]
  | negSucc n =>
    rw [qIntU, map_neg, map_qNatU, hφ]
    simp [qInt, Int.negSucc_eq]

end LieLean.QuantumGroup
