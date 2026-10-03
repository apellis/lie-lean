/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Order.Preorder.Finite

/-!
# Canonical bases of bar involutions ("Lusztig's lemma")

Let `V` be a free `ℤ[v, v⁻¹]`-module with basis `(b_i)_{i ∈ I}` indexed by a partially ordered
set `I` in which every set `{j | j < i}` is finite, and let `ψ : V → V` be an additive involution
which is semilinear for the ring involution `v ↦ v⁻¹` and unitriangular:
`ψ(b_i) ∈ b_i + Σ_{j < i} ℤ[v, v⁻¹] b_j`. Then for every `i` there is a unique `ψ`-invariant
element
```
  c_i ∈ b_i + Σ_{j < i} v⁻¹ ℤ[v⁻¹] b_j
```
(`Module.Basis.IsBarTriangular.existsUnique_canonical`). This is the abstract form of the
existence and uniqueness of the Kazhdan–Lusztig basis ([KL] Thm. 1.1), of Deodhar's parabolic
Kazhdan–Lusztig bases ([Deo] §2–3), and of Lusztig's canonical bases ([Lus] Lemma 24.2.1,
[Du]).

If moreover the matrix of `ψ` is *graded* by a function `ℓ : I → ℤ` — the coefficient of `b_j` in
`ψ(b_i)` is supported in degrees `n` with `|n| ≤ ℓ(i) - ℓ(j)` and `n ≡ ℓ(i) - ℓ(j) (mod 2)`
(`LaurentPolynomial.IsBounded`) — then so is the coefficient of `b_j` in `c_i`. Together with
`c_i`'s coefficients lying in `v⁻¹ ℤ[v⁻¹]`, this says that the coefficient of `b_j` in `c_i` is
`v^{ℓ(j) - ℓ(i)} P(v²)` for a polynomial `P` with `2 deg P < ℓ(i) - ℓ(j)`: this is how
Kazhdan–Lusztig-type polynomials arise (`LaurentPolynomial.exists_eq_T_mul_aeval`).

## Proof

Uniqueness: a nonzero `ψ`-invariant element `x` with all coefficients in `v⁻¹ ℤ[v⁻¹]` is
impossible, since the coefficient of `b_j` in `ψ(x)` for `j` maximal in the support of `x` is
`x̄_j`, and `x_j = x̄_j ∈ v⁻¹ ℤ[v⁻¹] ∩ v ℤ[v] = 0`.

Existence: we fix the coefficients of `c_i` one index `j < i` at a time, going downwards: at each
stage the set `S` of fixed indices is upward closed in `{j | j < i}` and `ψ(c) - c` has no
component along `S ∪ {i}`. If `j` is a maximal unfixed index, the involutivity of `ψ` shows that
the coefficient `a` of `b_j` in `ψ(c) - c` satisfies `ā = -a`, so `a = p - p̄` with
`p ∈ v⁻¹ ℤ[v⁻¹]` (`LaurentPolynomial.eq_negPart_sub_invert_negPart`), and replacing `c` by
`c + p b_j` fixes the index `j`. (This element-wise formulation of the usual argument was written
by us.)

## Main definitions

* `LaurentPolynomial.IsNeg f`: `f ∈ v⁻¹ ℤ[v⁻¹]`.
* `LaurentPolynomial.IsBounded N f`: `f` is supported in degrees `n` with `|n| ≤ N` and
  `n ≡ N (mod 2)`.
* `LaurentPolynomial.negPart f`: the part of `f` in negative degrees.
* `Module.Basis.IsBarTriangular b ψ ℓ`: the hypotheses above.
* `Module.Basis.IsBarTriangular.canonical`: the canonical basis element `c_i`.

## Main results

* `Module.Basis.IsBarTriangular.eq_zero_of_apply_eq_self`: uniqueness.
* `Module.Basis.IsBarTriangular.existsUnique_canonical`: existence and uniqueness of `c_i`.
* `Module.Basis.IsBarTriangular.isBounded_repr_canonical`,
  `lt_of_repr_canonical_ne_zero`: support and grading of `c_i`.
* `LaurentPolynomial.exists_eq_T_mul_aeval`: extraction of polynomials in `v²`.

## References

* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184.
* [Deo] V. Deodhar, *On some geometric aspects of Bruhat orderings II. The parabolic analogue of
  Kazhdan–Lusztig polynomials*, J. Algebra **111** (1987), 483–506.
* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §24.2.
* [Du] J. Du, *IC bases and quantum linear groups*, Proc. Sympos. Pure Math. **56**, Part 2
  (1994), 135–148.
-/

open Module Polynomial

namespace LaurentPolynomial

/-! ### Laurent polynomials supported in negative or bounded degrees -/

/-- `f ∈ v⁻¹ ℤ[v⁻¹]`: all coefficients of `f` in degrees `≥ 0` vanish. -/
def IsNeg (f : ℤ[T;T⁻¹]) : Prop := ∀ n : ℤ, 0 ≤ n → f.coeff n = 0

/-- `f` is supported in degrees `n` with `-N ≤ n ≤ N` and `n ≡ N (mod 2)`. -/
def IsBounded (N : ℤ) (f : ℤ[T;T⁻¹]) : Prop :=
  ∀ n : ℤ, f.coeff n ≠ 0 → -N ≤ n ∧ n ≤ N ∧ Even (n + N)

theorem coeff_T_mul (k n : ℤ) (f : ℤ[T;T⁻¹]) : (T k * f).coeff n = f.coeff (n - k) := by
  rw [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, sub_eq_neg_add]

theorem isNeg_zero : IsNeg 0 := fun _ _ ↦ rfl

theorem IsNeg.add {f g : ℤ[T;T⁻¹]} (hf : f.IsNeg) (hg : g.IsNeg) : (f + g).IsNeg := fun n hn ↦ by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf n hn, hg n hn, add_zero]

theorem IsNeg.sub {f g : ℤ[T;T⁻¹]} (hf : f.IsNeg) (hg : g.IsNeg) : (f - g).IsNeg := fun n hn ↦ by
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hf n hn, hg n hn, sub_zero]

/-- A bar-invariant element of `v⁻¹ ℤ[v⁻¹]` is zero. -/
theorem IsNeg.eq_zero_of_invert_eq {f : ℤ[T;T⁻¹]} (hf : f.IsNeg) (h : invert f = f) : f = 0 := by
  ext n
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  rcases le_or_gt 0 n with hn | hn
  · exact hf n hn
  · rw [← h, invert_apply]
    exact hf _ (by omega)

theorem isBounded_zero (N : ℤ) : IsBounded N 0 := fun _ h ↦ absurd rfl h

theorem IsBounded.add {N : ℤ} {f g : ℤ[T;T⁻¹]} (hf : f.IsBounded N) (hg : g.IsBounded N) :
    (f + g).IsBounded N := fun n hn ↦ by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hn
  by_cases h : f.coeff n = 0
  · rw [h, zero_add] at hn
    exact hg n hn
  · exact hf n h

theorem IsBounded.neg {N : ℤ} {f : ℤ[T;T⁻¹]} (hf : f.IsBounded N) : (-f).IsBounded N :=
  fun n hn ↦ hf n (by simpa using hn)

theorem IsBounded.sub {N : ℤ} {f g : ℤ[T;T⁻¹]} (hf : f.IsBounded N) (hg : g.IsBounded N) :
    (f - g).IsBounded N := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem isBounded_sum {ι : Type*} {N : ℤ} (s : Finset ι) {f : ι → ℤ[T;T⁻¹]}
    (hf : ∀ i ∈ s, (f i).IsBounded N) : (∑ i ∈ s, f i).IsBounded N := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isBounded_zero N
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

theorem IsBounded.mul {N N' : ℤ} {f g : ℤ[T;T⁻¹]} (hf : f.IsBounded N) (hg : g.IsBounded N') :
    (f * g).IsBounded (N + N') := by
  classical
  intro n hn
  have hmem : n ∈ (f * g).coeff.support := Finsupp.mem_support_iff.mpr hn
  obtain ⟨a, ha, c, hc, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset f g hmem)
  obtain ⟨h1, h2, h3⟩ := hf a (Finsupp.mem_support_iff.mp ha)
  obtain ⟨h1', h2', h3'⟩ := hg c (Finsupp.mem_support_iff.mp hc)
  refine ⟨by omega, by omega, ?_⟩
  have := h3.add h3'
  rwa [show a + N + (c + N') = a + c + (N + N') by ring] at this

theorem IsBounded.invert {N : ℤ} {f : ℤ[T;T⁻¹]} (hf : f.IsBounded N) :
    (invert f).IsBounded N := fun n hn ↦ by
  rw [invert_apply] at hn
  obtain ⟨h1, h2, h3⟩ := hf _ hn
  refine ⟨by omega, by omega, ?_⟩
  have : n + N = (-n + N) + 2 * n := by ring
  rw [this]
  exact h3.add (even_two_mul n)

theorem isBounded_C_mul_T {N n : ℤ} (c : ℤ) (h1 : -N ≤ n) (h2 : n ≤ N) (h3 : Even (n + N)) :
    (C c * T n : ℤ[T;T⁻¹]).IsBounded N := fun m hm ↦ by
  classical
  rw [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at hm
  split_ifs at hm with h
  · subst h
    exact ⟨h1, h2, h3⟩
  · exact absurd rfl hm

theorem isBounded_T {N n : ℤ} (h1 : -N ≤ n) (h2 : n ≤ N) (h3 : Even (n + N)) :
    (T n : ℤ[T;T⁻¹]).IsBounded N := by
  simpa using isBounded_C_mul_T 1 h1 h2 h3

theorem isBounded_one : (1 : ℤ[T;T⁻¹]).IsBounded 0 := by
  simpa using isBounded_T (N := 0) (n := 0) le_rfl le_rfl ⟨0, by simp⟩

theorem IsBounded.of_eq {N N' : ℤ} {f : ℤ[T;T⁻¹]} (hf : f.IsBounded N) (h : N = N') :
    f.IsBounded N' := h ▸ hf

/-- `v^a P(v²)` is supported in degrees `a, a + 2, …, a + 2 deg P`. -/
theorem isBounded_T_mul_aeval {N a : ℤ} (P : ℤ[X]) (h1 : -N ≤ a)
    (h2 : a + 2 * P.natDegree ≤ N) (h3 : Even (a + N)) :
    (T a * aeval (T 2 : ℤ[T;T⁻¹]) P).IsBounded N := by
  rw [P.as_sum_range_C_mul_X_pow, map_sum, Finset.mul_sum]
  refine isBounded_sum _ fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  rw [map_mul, map_pow, aeval_X, aeval_C, T_pow, eq_intCast (algebraMap ℤ ℤ[T;T⁻¹]),
    ← map_intCast (C : ℤ →+* ℤ[T;T⁻¹]), Int.cast_id, mul_left_comm, ← T_add]
  refine isBounded_C_mul_T _ (by omega) (by omega) ?_
  rw [show a + ↑i * 2 + N = a + N + 2 * i by ring]
  exact h3.add (even_two_mul _)

/-- The part `Σ_{n < 0} f_n v^n` of `f` in negative degrees. -/
noncomputable def negPart (f : ℤ[T;T⁻¹]) : ℤ[T;T⁻¹] :=
  AddMonoidAlgebra.ofCoeff (f.coeff.filter (· < 0))

theorem coeff_negPart_apply (f : ℤ[T;T⁻¹]) (n : ℤ) :
    (negPart f).coeff n = if n < 0 then f.coeff n else 0 :=
  Finsupp.filter_apply _ _ _

theorem isNeg_negPart (f : ℤ[T;T⁻¹]) : (negPart f).IsNeg := fun n hn ↦ by
  rw [coeff_negPart_apply, ite_eq_right (by omega)]

theorem IsBounded.negPart {N : ℤ} {f : ℤ[T;T⁻¹]} (hf : f.IsBounded N) :
    (negPart f).IsBounded N := fun n hn ↦ by
  rw [coeff_negPart_apply] at hn
  split_ifs at hn
  · exact hf n hn
  · exact absurd rfl hn

/-- A bar-anti-invariant Laurent polynomial `a` (`ā = -a`) is `p - p̄` for `p` its negative part. -/
theorem eq_negPart_sub_invert_negPart {f : ℤ[T;T⁻¹]} (h : invert f = -f) :
    f = negPart f - invert (negPart f) := by
  ext n
  have hn := congrArg (fun g : ℤ[T;T⁻¹] ↦ g.coeff n) h
  simp only [invert_apply, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply] at hn
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, invert_apply, coeff_negPart_apply,
    coeff_negPart_apply]
  rcases lt_trichotomy n 0 with h' | rfl | h'
  · rw [ite_eq_left h', ite_eq_right (by omega), sub_zero]
  · rw [ite_eq_right (lt_irrefl 0), neg_zero, ite_eq_right (lt_irrefl 0), sub_zero]
    simp only [neg_zero] at hn
    omega
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), zero_sub, hn, neg_neg]

/-! ### Extracting polynomials in `v²` -/

/-- A Laurent polynomial supported in degrees `n ≥ a` with `n ≡ a (mod 2)` is `v^a P(v²)` for a
polynomial `P` with `P_k = f_{a + 2k}`. -/
theorem exists_eq_T_mul_aeval {a : ℤ} {f : ℤ[T;T⁻¹]}
    (hf : ∀ n, f.coeff n ≠ 0 → a ≤ n ∧ Even (n - a)) :
    ∃ P : ℤ[X], f = T a * aeval (T 2 : ℤ[T;T⁻¹]) P ∧
      ∀ k : ℕ, P.coeff k = f.coeff (a + 2 * k) := by
  classical
  refine ⟨∑ n ∈ f.coeff.support, monomial ((n - a) / 2).toNat (f.coeff n), ?_, ?_⟩
  · rw [map_sum, Finset.mul_sum]
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    obtain ⟨h1, k, hk⟩ := hf n (Finsupp.mem_support_iff.mp hn)
    have e : ((n - a) / 2).toNat = k.toNat := by omega
    rw [e, aeval_monomial, T_pow, single_eq_C_mul_T,
      eq_intCast (algebraMap ℤ ℤ[T;T⁻¹]), ← map_intCast (C : ℤ →+* ℤ[T;T⁻¹]), Int.cast_id,
      mul_left_comm, ← T_add]
    congr 2
    omega
  · intro k
    rw [finsetSum_coeff]
    by_cases hk : a + 2 * k ∈ f.coeff.support
    · rw [Finset.sum_eq_single_of_mem _ hk]
      · rw [coeff_monomial, ite_eq_left (by omega)]
      · intro n hn hne
        obtain ⟨h1, m, hm⟩ := hf n (Finsupp.mem_support_iff.mp hn)
        rw [coeff_monomial, ite_eq_right (by omega)]
    · rw [Finsupp.notMem_support_iff.mp hk]
      refine Finset.sum_eq_zero fun n hn ↦ ?_
      obtain ⟨h1, m, hm⟩ := hf n (Finsupp.mem_support_iff.mp hn)
      rw [coeff_monomial, ite_eq_right]
      intro he
      apply hk
      rwa [show a + 2 * k = n by omega]

end LaurentPolynomial

namespace Module.Basis

open LaurentPolynomial

variable {ι V : Type*} [PartialOrder ι] [AddCommGroup V] [Module ℤ[T;T⁻¹] V]

/-- The hypotheses of Lusztig's lemma: `ψ` is an additive involution of `V`, semilinear for
`v ↦ v⁻¹`, whose matrix in the basis `b` is unitriangular with respect to the partial order of
the index set (in which all sets `{j | j < i}` are finite) and graded by `ℓ`: the coefficient of
`b_j` in `ψ(b_i)` is supported in degrees `n` with `|n| ≤ ℓ(i) - ℓ(j)` and
`n ≡ ℓ(i) - ℓ(j) (mod 2)`. -/
structure IsBarTriangular (b : Basis ι ℤ[T;T⁻¹] V) (ψ : V →+ V) (ℓ : ι → ℤ) : Prop where
  /-- `ψ` is semilinear for `v ↦ v⁻¹`. -/
  map_smul (a : ℤ[T;T⁻¹]) (x : V) : ψ (a • x) = invert a • ψ x
  /-- `ψ` is an involution. -/
  involutive (x : V) : ψ (ψ x) = x
  /-- The diagonal coefficients are `1`. -/
  repr_self (i : ι) : b.repr (ψ (b i)) i = 1
  /-- Triangularity. -/
  le_of_repr_ne_zero {i j : ι} : b.repr (ψ (b i)) j ≠ 0 → j ≤ i
  /-- The grading. -/
  isBounded (i j : ι) : (b.repr (ψ (b i)) j).IsBounded (ℓ i - ℓ j)
  /-- The sets `{j | j < i}` are finite. -/
  finite_Iio (i : ι) : (Set.Iio i).Finite

namespace IsBarTriangular

variable {b : Basis ι ℤ[T;T⁻¹] V} {ψ : V →+ V} {ℓ : ι → ℤ} (h : IsBarTriangular b ψ ℓ)
include h

/-- The coefficients of `ψ(x)`: `[b_j] ψ(x) = Σ_k x̄_k [b_j] ψ(b_k)`. -/
theorem repr_apply (x : V) (j : ι) :
    b.repr (ψ x) j = (b.repr x).sum fun k a ↦ invert a * b.repr (ψ (b k)) j := by
  conv_lhs => rw [← b.linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, map_finsuppSum, map_finsuppSum, Finsupp.sum_apply]
  simp only [h.map_smul, _root_.map_smul, Finsupp.smul_apply, smul_eq_mul]

omit h [PartialOrder ι] in
theorem repr_sub_apply (x : V) (j : ι) :
    b.repr (ψ x - x) j = b.repr (ψ x) j - b.repr x j := by
  rw [map_sub, Finsupp.sub_apply]

/-- **Uniqueness in Lusztig's lemma**: a `ψ`-invariant element all of whose coefficients lie in
`v⁻¹ ℤ[v⁻¹]` is zero. -/
theorem eq_zero_of_apply_eq_self {x : V} (hx : ψ x = x) (hneg : ∀ j, (b.repr x j).IsNeg) :
    x = 0 := by
  classical
  by_contra hne
  have hsupp : (b.repr x).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact fun e ↦ hne (b.repr.map_eq_zero_iff.mp e)
  obtain ⟨j, hj⟩ := (b.repr x).support.exists_maximal hsupp
  have key : b.repr (ψ x) j = invert (b.repr x j) := by
    rw [h.repr_apply, Finsupp.sum, Finset.sum_eq_single_of_mem j hj.1, h.repr_self, mul_one]
    intro k hk hkj
    by_cases hr : b.repr (ψ (b k)) j = 0
    · rw [hr, mul_zero]
    · exact absurd (le_antisymm (hj.2 hk (h.le_of_repr_ne_zero hr)) (h.le_of_repr_ne_zero hr))
        hkj
  rw [hx] at key
  exact Finsupp.mem_support_iff.mp hj.1 ((hneg j).eq_zero_of_invert_eq key.symm)

/-- The inductive step of the construction: from an element in which the indices of `S` are
fixed, fix a minimal element `j` of `S`. -/
private theorem exists_step [DecidableEq ι] (i : ι) (S : Finset ι) (hSi : ∀ j ∈ S, j < i)
    (hSup : ∀ j ∈ S, ∀ k, j < k → k < i → k ∈ S) {j : ι} (hj : Minimal (· ∈ S) j) (c : V)
    (hci : b.repr c i = 1) (hc0 : ∀ k, k ≠ i → k ∉ S.erase j → b.repr c k = 0)
    (hcS : ∀ k ∈ S.erase j, (b.repr c k).IsNeg ∧ (b.repr c k).IsBounded (ℓ i - ℓ k))
    (hψc : ∀ k, b.repr (ψ c - c) k ≠ 0 → k < i ∧ k ∉ S.erase j) :
    ∃ c' : V, b.repr c' i = 1 ∧ (∀ k, k ≠ i → k ∉ S → b.repr c' k = 0) ∧
      (∀ k ∈ S, (b.repr c' k).IsNeg ∧ (b.repr c' k).IsBounded (ℓ i - ℓ k)) ∧
      (∀ k, b.repr (ψ c' - c') k ≠ 0 → k < i ∧ k ∉ S) := by
  have hji : j < i := hSi j hj.1
  have hjS' : j ∉ S.erase j := Finset.notMem_erase j S
  have hcj : b.repr c j = 0 := hc0 j hji.ne hjS'
  -- the minimality of `j`
  have hmin : ∀ k ∈ S, k ≤ j → k = j := fun k hk hkj ↦ le_antisymm hkj (hj.2 hk hkj)
  set a := b.repr (ψ c) j with ha
  -- `a` is anti-invariant
  have hanti : invert a = -a := by
    have e : ψ (ψ c - c) = -(ψ c - c) := by rw [map_sub, h.involutive]; abel
    have e' := congrArg (fun y ↦ b.repr y j) e
    rw [h.repr_apply, map_neg, Finsupp.neg_apply] at e'
    rw [Finsupp.sum, Finset.sum_eq_single j, h.repr_self, mul_one, repr_sub_apply, hcj,
      sub_zero] at e'
    · exact e'
    · intro k _ hkj
      by_cases hx : b.repr (ψ c - c) k = 0
      · rw [hx, map_zero, zero_mul]
      by_cases hr : b.repr (ψ (b k)) j = 0
      · rw [hr, mul_zero]
      exfalso
      obtain ⟨hki, hkS⟩ := hψc k hx
      have hjk : j < k := lt_of_le_of_ne (h.le_of_repr_ne_zero hr) (Ne.symm hkj)
      exact hkS (Finset.mem_erase.mpr ⟨hkj, hSup j hj.1 k hjk hki⟩)
    · intro hj'
      rw [Finsupp.notMem_support_iff.mp hj', map_zero, zero_mul]
  -- `a` is graded
  have hbd : a.IsBounded (ℓ i - ℓ j) := by
    rw [ha, h.repr_apply, Finsupp.sum]
    refine isBounded_sum _ fun k hk ↦ ?_
    by_cases hki : k = i
    · subst hki
      rw [hci, map_one, one_mul]
      exact h.isBounded k j
    · have hkS : k ∈ S.erase j := by
        by_contra hkS
        exact Finsupp.mem_support_iff.mp hk (hc0 k hki hkS)
      exact ((hcS k hkS).2.invert.mul (h.isBounded k j)).of_eq (by ring)
  set p := negPart a
  have hp : a = p - invert p := eq_negPart_sub_invert_negPart hanti
  have hrepr : ∀ k, b.repr (p • b j) k = if k = j then p else 0 := fun k ↦ by
    rw [_root_.map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hk : k = j
    · subst hk
      simp
    · rw [ite_eq_right (Ne.symm hk), ite_eq_right hk, smul_zero]
  refine ⟨c + p • b j, ?_, ?_, ?_, ?_⟩
  · rw [map_add, Finsupp.add_apply, hci, hrepr, ite_eq_right hji.ne', add_zero]
  · intro k hki hkS
    have hkj : k ≠ j := fun e ↦ hkS (e ▸ hj.1)
    rw [map_add, Finsupp.add_apply, hrepr, ite_eq_right hkj, add_zero]
    exact hc0 k hki fun h' ↦ hkS (Finset.mem_of_mem_erase h')
  · intro k hk
    rw [map_add, Finsupp.add_apply, hrepr]
    by_cases hkj : k = j
    · subst hkj
      rw [hcj, ite_eq_left rfl, zero_add]
      exact ⟨isNeg_negPart a, hbd.negPart⟩
    · rw [ite_eq_right hkj, add_zero]
      exact hcS k (Finset.mem_erase.mpr ⟨hkj, hk⟩)
  · intro k hk
    have e : b.repr (ψ (c + p • b j) - (c + p • b j)) k =
        b.repr (ψ c - c) k + (invert p * b.repr (ψ (b j)) k - if k = j then p else 0) := by
      rw [← hrepr, map_add, h.map_smul, map_sub, map_add, map_add, _root_.map_smul, map_sub]
      simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
      ring
    rw [e] at hk
    by_cases hkj : k = j
    · subst hkj
      exfalso
      apply hk
      rw [ite_eq_left rfl, h.repr_self, mul_one, repr_sub_apply, hcj, sub_zero, ← ha, hp]
      ring
    · rw [ite_eq_right hkj, sub_zero] at hk
      by_cases hx : b.repr (ψ c - c) k = 0
      · rw [hx, zero_add] at hk
        have hr : b.repr (ψ (b j)) k ≠ 0 := fun hr ↦ hk (by rw [hr, mul_zero])
        have hkj' : k < j := lt_of_le_of_ne (h.le_of_repr_ne_zero hr) hkj
        exact ⟨hkj'.trans hji, fun hkS ↦ hkj (hmin k hkS hkj'.le)⟩
      · obtain ⟨hki, hkS⟩ := hψc k hx
        exact ⟨hki, fun hkS' ↦ hkS (Finset.mem_erase.mpr ⟨hkj, hkS'⟩)⟩

/-- The construction of the canonical element, by induction over the set `S` of fixed indices. -/
private theorem exists_fixed (i : ι) (S : Finset ι) (hSi : ∀ j ∈ S, j < i)
    (hSup : ∀ j ∈ S, ∀ k, j < k → k < i → k ∈ S) :
    ∃ c : V, b.repr c i = 1 ∧ (∀ k, k ≠ i → k ∉ S → b.repr c k = 0) ∧
      (∀ k ∈ S, (b.repr c k).IsNeg ∧ (b.repr c k).IsBounded (ℓ i - ℓ k)) ∧
      (∀ k, b.repr (ψ c - c) k ≠ 0 → k < i ∧ k ∉ S) := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hS
  · refine ⟨b i, by simp, fun k hki _ ↦ ?_, by simp, fun k hk ↦ ⟨?_, Finset.notMem_empty k⟩⟩
    · rw [b.repr_self, Finsupp.single_apply, ite_eq_right (Ne.symm hki)]
    · rw [repr_sub_apply, b.repr_self, Finsupp.single_apply] at hk
      by_cases hki : k = i
      · subst hki
        simp [h.repr_self] at hk
      · rw [ite_eq_right (Ne.symm hki), sub_zero] at hk
        exact lt_of_le_of_ne (h.le_of_repr_ne_zero hk) hki
  obtain ⟨j, hj⟩ := S.exists_minimal hS
  have hmin : ∀ k ∈ S, k ≤ j → k = j := fun k hk hkj ↦ le_antisymm hkj (hj.2 hk hkj)
  obtain ⟨c, hci, hc0, hcS, hψc⟩ := ih (S.erase j) (Finset.erase_ssubset hj.1)
    (fun k hk ↦ hSi k (Finset.mem_of_mem_erase hk)) (fun k hk l hkl hli ↦ by
      have hk' := Finset.mem_of_mem_erase hk
      refine Finset.mem_erase.mpr ⟨fun hlj ↦ ?_, hSup k hk' l hkl hli⟩
      subst hlj
      exact (Finset.ne_of_mem_erase hk) (hmin k hk' hkl.le))
  exact h.exists_step i S hSi hSup hj c hci hc0 hcS hψc

/-- **Existence in Lusztig's lemma** ([KL] Thm. 1.1, [Lus] Lemma 24.2.1): there is a
`ψ`-invariant element `c ∈ b_i + Σ_{j < i} v⁻¹ ℤ[v⁻¹] b_j`, whose coefficients are moreover
graded by `ℓ`. -/
theorem exists_canonical (i : ι) : ∃ c : V, ψ c = c ∧ b.repr c i = 1 ∧
    ∀ j, j ≠ i → (b.repr c j).IsNeg ∧ (b.repr c j ≠ 0 → j < i) ∧
      (b.repr c j).IsBounded (ℓ i - ℓ j) := by
  classical
  set S := (h.finite_Iio i).toFinset
  have hS : ∀ j, j ∈ S ↔ j < i := fun j ↦ by simp [S]
  obtain ⟨c, hci, hc0, hcS, hψc⟩ := h.exists_fixed i S (fun j hj ↦ (hS j).mp hj)
    (fun _ _ k _ hk ↦ (hS k).mpr hk)
  refine ⟨c, ?_, hci, fun j hji ↦ ?_⟩
  · rw [← sub_eq_zero, b.ext_elem_iff]
    intro k
    rw [map_zero, Finsupp.zero_apply]
    by_contra hk
    obtain ⟨hki, hkS⟩ := hψc k hk
    exact hkS ((hS k).mpr hki)
  · by_cases hj : j < i
    · exact ⟨(hcS j ((hS j).mpr hj)).1, fun _ ↦ hj, (hcS j ((hS j).mpr hj)).2⟩
    · rw [hc0 j hji fun h' ↦ hj ((hS j).mp h')]
      exact ⟨isNeg_zero, fun h' ↦ absurd rfl h', isBounded_zero _⟩

/-- **Lusztig's lemma** ([KL] Thm. 1.1, [Deo] Prop. 3.2, [Lus] Lemma 24.2.1): for every
`i` there is a unique `ψ`-invariant element `c` with `[b_i] c = 1` and `[b_j] c ∈ v⁻¹ ℤ[v⁻¹]` for
`j ≠ i`. -/
theorem existsUnique_canonical (i : ι) :
    ∃! c : V, ψ c = c ∧ b.repr c i = 1 ∧ ∀ j, j ≠ i → (b.repr c j).IsNeg := by
  obtain ⟨c, hc, hci, hcj⟩ := h.exists_canonical i
  refine ⟨c, ⟨hc, hci, fun j hj ↦ (hcj j hj).1⟩, ?_⟩
  rintro c' ⟨hc', hci', hcj'⟩
  rw [← sub_eq_zero]
  refine h.eq_zero_of_apply_eq_self (by rw [map_sub, hc, hc']) fun j ↦ ?_
  rw [map_sub, Finsupp.sub_apply]
  by_cases hj : j = i
  · subst hj
    rw [hci, hci', sub_self]
    exact isNeg_zero
  · exact (hcj' j hj).sub (hcj j hj).1

/-- The canonical basis element `c_i` of Lusztig's lemma: the unique `ψ`-invariant element of
`b_i + Σ_{j < i} v⁻¹ ℤ[v⁻¹] b_j`. -/
noncomputable def canonical (i : ι) : V := (h.exists_canonical i).choose

theorem apply_canonical (i : ι) : ψ (h.canonical i) = h.canonical i :=
  (h.exists_canonical i).choose_spec.1

theorem repr_canonical_self (i : ι) : b.repr (h.canonical i) i = 1 :=
  (h.exists_canonical i).choose_spec.2.1

theorem isNeg_repr_canonical {i j : ι} (hj : j ≠ i) : (b.repr (h.canonical i) j).IsNeg :=
  ((h.exists_canonical i).choose_spec.2.2 j hj).1

theorem lt_of_repr_canonical_ne_zero {i j : ι} (hj : j ≠ i)
    (hne : b.repr (h.canonical i) j ≠ 0) : j < i :=
  ((h.exists_canonical i).choose_spec.2.2 j hj).2.1 hne

theorem le_of_repr_canonical_ne_zero {i j : ι} (hne : b.repr (h.canonical i) j ≠ 0) : j ≤ i := by
  rcases eq_or_ne j i with rfl | hj
  · exact le_rfl
  · exact (h.lt_of_repr_canonical_ne_zero hj hne).le

theorem isBounded_repr_canonical (i j : ι) :
    (b.repr (h.canonical i) j).IsBounded (ℓ i - ℓ j) := by
  rcases eq_or_ne j i with rfl | hj
  · rw [h.repr_canonical_self, sub_self]
    exact isBounded_one
  · exact ((h.exists_canonical i).choose_spec.2.2 j hj).2.2

/-- The canonical element is characterized by `ψ`-invariance and its normalization. -/
theorem eq_canonical {i : ι} {c : V} (hc : ψ c = c) (hci : b.repr c i = 1)
    (hcj : ∀ j, j ≠ i → (b.repr c j).IsNeg) : c = h.canonical i :=
  (h.existsUnique_canonical i).unique ⟨hc, hci, hcj⟩
    ⟨h.apply_canonical i, h.repr_canonical_self i, fun _ hj ↦ h.isNeg_repr_canonical hj⟩

end IsBarTriangular

end Module.Basis
