/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Lowest weighted components and derivations

For a weight `w : σ → ℕ`, a polynomial "has weight at least `k`" when all its coefficients
at monomials of weight `< k` vanish. This file records the multiplicative and differential
behaviour of this condition and the lowest component of a derivative, and deduces a
vanishing criterion used for Chevalley restriction injectivity.

## Main results

* `MvPolynomial.derivation_eq_sum_pderiv`: `D p = ∑ᵢ ∂ᵢ p · D (Xᵢ)` for finitely many variables.
* `MvPolynomial.weightedHomogeneousComponent_mul_of_lowWeight`: the lowest component of a
  product is the product of the lowest components.
* `MvPolynomial.weightedHomogeneousComponent_derivation_of_lowWeight`: for `0/1` weights,
  the component of `D p` just below the lowest weight of `p` is
  `∑ᵢ wᵢ • ∂ᵢ (p_k) · (D Xᵢ)₀`.
* `MvPolynomial.aeval_weight_zero_eq_weightedHomogeneousComponent`: setting all variables of
  positive weight to zero is the weight-zero component.
* `MvPolynomial.eq_zero_of_derivation_lowestWeight`: if `p₀ = 0` and, for each weight-one
  variable `Xᵢ`, some derivation killing `p` moves `Xᵢ` (and no other weight-one variable) to
  a nonzero weight-zero leading term, then `p = 0` (characteristic zero).

## References

The vanishing criterion is the infinitesimal form of the standard argument that the
restriction of an invariant polynomial to a Cartan subalgebra is injective
(Humphreys, *Introduction to Lie algebras and representation theory*, §23.1 (check);
Etingof, MIT 18.757 (Fall 2023), Lecture 10, Thm. 10.1(ii) (check)). The graded argument here
is reconstructed; it replaces density of semisimple elements by a lowest-term computation.
-/

open Finsupp

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

section Derivation

/-- A derivation of a polynomial ring in finitely many variables is determined by its values
on the variables: `D p = ∑ᵢ ∂ᵢ p · D (Xᵢ)`. -/
theorem derivation_eq_sum_pderiv [Fintype σ]
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (p : MvPolynomial σ R) :
    D p = ∑ i, pderiv i p * D (X i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [derivation_C]
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [Derivation.leibniz, hp]
    simp only [Derivation.leibniz, smul_eq_mul, pderiv_X, Pi.single_apply, mul_ite, mul_one,
      mul_zero, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

end Derivation

section LowWeight

variable (w : σ → ℕ)

/-- Products of polynomials of weight at least `a` and at least `b` have weight at least
`a + b`. -/
theorem coeff_mul_eq_zero_of_lowWeight {a b : ℕ} {p q : MvPolynomial σ R}
    (hp : ∀ d, weight w d < a → p.coeff d = 0) (hq : ∀ d, weight w d < b → q.coeff d = 0)
    (d : σ →₀ ℕ) (hd : weight w d < a + b) : (p * q).coeff d = 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  have he : weight w x.1 + weight w x.2 = weight w d := by rw [← map_add, hx]
  by_cases h : weight w x.1 < a
  · rw [hp _ h, zero_mul]
  · rw [hq _ (by omega), mul_zero]

/-- A weighted homogeneous polynomial of degree `n` has weight at least `n`. -/
theorem IsWeightedHomogeneous.coeff_eq_zero_of_lt {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsWeightedHomogeneous w n) (d : σ →₀ ℕ) (hd : weight w d < n) : p.coeff d = 0 :=
  hp.coeff_eq_zero d (Nat.ne_of_lt hd)

/-- Components below the lowest weight vanish. -/
theorem weightedHomogeneousComponent_eq_zero_of_lowWeight {a n : ℕ} {p : MvPolynomial σ R}
    (hp : ∀ d, weight w d < a → p.coeff d = 0) (hn : n < a) :
    weightedHomogeneousComponent w n p = 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with h
  · simpa using hp d (h ▸ hn)
  · simp

end LowWeight

section Ring

variable {R : Type*} [CommRing R] (w : σ → ℕ)

/-- Removing the lowest component raises the lowest weight. -/
theorem coeff_sub_weightedHomogeneousComponent_eq_zero {a : ℕ} {p : MvPolynomial σ R}
    (hp : ∀ d, weight w d < a → p.coeff d = 0) (d : σ →₀ ℕ) (hd : weight w d < a + 1) :
    (p - weightedHomogeneousComponent w a p).coeff d = 0 := by
  classical
  have hs : (p - weightedHomogeneousComponent w a p).coeff d =
      p.coeff d - (weightedHomogeneousComponent w a p).coeff d := by simp
  rw [hs, coeff_weightedHomogeneousComponent]
  split_ifs with h
  · exact sub_self _
  · rw [hp d (by omega), sub_zero]


/-- The lowest component of a product is the product of the lowest components. -/
theorem weightedHomogeneousComponent_mul_of_lowWeight {a b : ℕ} {p q : MvPolynomial σ R}
    (hp : ∀ d, weight w d < a → p.coeff d = 0) (hq : ∀ d, weight w d < b → q.coeff d = 0) :
    weightedHomogeneousComponent w (a + b) (p * q) =
      weightedHomogeneousComponent w a p * weightedHomogeneousComponent w b q := by
  set p₀ := weightedHomogeneousComponent w a p
  set q₀ := weightedHomogeneousComponent w b q
  have hp₀ : p₀.IsWeightedHomogeneous w a := weightedHomogeneousComponent_isWeightedHomogeneous _ _
  have hq₀ : q₀.IsWeightedHomogeneous w b := weightedHomogeneousComponent_isWeightedHomogeneous _ _
  have hp₁ : ∀ d, weight w d < a + 1 → (p - p₀).coeff d = 0 :=
    coeff_sub_weightedHomogeneousComponent_eq_zero w hp
  have hq₁ : ∀ d, weight w d < b + 1 → (q - q₀).coeff d = 0 :=
    coeff_sub_weightedHomogeneousComponent_eq_zero w hq
  have he : p * q = p₀ * q₀ + ((p - p₀) * q₀ + p₀ * (q - q₀) + (p - p₀) * (q - q₀)) := by ring
  have hr : ∀ d, weight w d < a + b + 1 →
      ((p - p₀) * q₀ + p₀ * (q - q₀) + (p - p₀) * (q - q₀)).coeff d = 0 := by
    intro d hd
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      coeff_mul_eq_zero_of_lowWeight w hp₁ (hq₀.coeff_eq_zero_of_lt w) d (by omega),
      coeff_mul_eq_zero_of_lowWeight w (hp₀.coeff_eq_zero_of_lt w) hq₁ d (by omega),
      coeff_mul_eq_zero_of_lowWeight w hp₁ hq₁ d (by omega), add_zero]
  rw [he, map_add, weightedHomogeneousComponent_eq_zero_of_lowWeight w hr (by omega), add_zero]
  exact (hp₀.mul hq₀).weightedHomogeneousComponent_same

/-- Partial derivatives lower the weight by the weight of the variable. -/
theorem coeff_pderiv_eq_zero_of_lowWeight {a : ℕ} {p : MvPolynomial σ R}
    (hp : ∀ d, weight w d < a → p.coeff d = 0) (i : σ) (d : σ →₀ ℕ)
    (hd : weight w d + w i < a) : (pderiv i p).coeff d = 0 := by
  rw [coeff_pderiv, hp, zero_mul]
  simpa [map_add, weight_single] using hd

/-- Partial derivatives commute with weighted components, shifting the degree. -/
theorem weightedHomogeneousComponent_pderiv (i : σ) (n : ℕ) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w n (pderiv i p) =
      pderiv i (weightedHomogeneousComponent w (n + w i) p) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_pderiv, coeff_pderiv,
    coeff_weightedHomogeneousComponent]
  have : weight w (d + single i 1) = weight w d + w i := by simp [map_add, weight_single]
  rw [this]
  by_cases h : weight w d = n
  · simp [h]
  · simp [h]

variable [Fintype σ]

/-- The component of a derivative just below the lowest weight, for weights in `{0, 1}`.
Only weight-one variables contribute, through the weight-zero part of their images. -/
theorem weightedHomogeneousComponent_derivation_of_lowWeight (hw : ∀ i, w i ≤ 1)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) {k : ℕ} {p : MvPolynomial σ R}
    (hp : ∀ d, weight w d < k + 1 → p.coeff d = 0) :
    weightedHomogeneousComponent w k (D p) =
      ∑ i, w i • (pderiv i (weightedHomogeneousComponent w (k + 1) p) *
        weightedHomogeneousComponent w 0 (D (X i))) := by
  rw [derivation_eq_sum_pderiv, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hD : ∀ d, weight w d < 0 → (D (X i)).coeff d = 0 := fun d hd => absurd hd (by omega)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hw i) with h | h
  · rw [h, zero_smul]
    have hi : ∀ d, weight w d < k + 1 → (pderiv i p).coeff d = 0 := fun d hd =>
      coeff_pderiv_eq_zero_of_lowWeight w hp i d (by omega)
    exact weightedHomogeneousComponent_eq_zero_of_lowWeight w
      (coeff_mul_eq_zero_of_lowWeight w hi hD) (by omega)
  · rw [h, one_smul]
    have hi : ∀ d, weight w d < k → (pderiv i p).coeff d = 0 := fun d hd =>
      coeff_pderiv_eq_zero_of_lowWeight w hp i d (by omega)
    have := weightedHomogeneousComponent_mul_of_lowWeight w hi hD
    rw [add_zero] at this
    rw [this, weightedHomogeneousComponent_pderiv, h]

end Ring

section Zero

variable (w : σ → ℕ)

/-- Setting every variable of positive weight to zero extracts the weight-zero component. -/
theorem aeval_weight_zero_eq_weightedHomogeneousComponent [DecidablePred fun i => w i = 0]
    (p : MvPolynomial σ R) :
    aeval (fun i => if w i = 0 then X i else 0) p = weightedHomogeneousComponent w 0 p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial d c =>
    have hm : (monomial d c).IsWeightedHomogeneous w (weight w d) :=
      isWeightedHomogeneous_monomial w d c rfl
    rw [aeval_monomial]
    by_cases h : weight w d = 0
    · have hs := hm.weightedHomogeneousComponent_same
      rw [h] at hs
      rw [hs, monomial_eq]
      congr 1
      apply Finsupp.prod_congr
      intro i hi
      have : w i = 0 := by
        rw [weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff] at h
        have := h i hi
        simpa [Finsupp.mem_support_iff.mp hi] using this
      simp [this]
    · rw [hm.weightedHomogeneousComponent_ne 0 (Ne.symm h)]
      rw [weight_apply, Finsupp.sum] at h
      obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have hw : w i ≠ 0 := fun h0 => hne (by simp [h0])
      rw [Finsupp.prod, Finset.prod_eq_zero hi (by simp [hw, Finsupp.mem_support_iff.mp hi]),
        mul_zero]

end Zero

section Field

variable {K : Type*} [Field K] [CharZero K] [Finite σ] (w : σ → ℕ)

/-- **Lowest-weight vanishing criterion.** Let `w` take values in `{0, 1}`. Suppose that the
weight-zero component of `p` vanishes and that, for every weight-one variable `Xᵢ`, there is
a derivation `D` with `D p = 0` such that the weight-zero part of `D Xᵢ` is nonzero while the
weight-zero parts of `D Xⱼ` vanish for the other weight-one variables `Xⱼ`. Then `p = 0`. -/
theorem eq_zero_of_derivation_lowestWeight (hw : ∀ i, w i ≤ 1) {p : MvPolynomial σ K}
    (h₀ : weightedHomogeneousComponent w 0 p = 0)
    (hD : ∀ i, w i = 1 → ∃ D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K),
      D p = 0 ∧ weightedHomogeneousComponent w 0 (D (X i)) ≠ 0 ∧
        ∀ j, j ≠ i → w j = 1 → weightedHomogeneousComponent w 0 (D (X j)) = 0) :
    p = 0 := by
  classical
  cases nonempty_fintype σ
  have key : ∀ k, ∀ d, weight w d < k → p.coeff d = 0 := by
    intro k
    induction k with
    | zero => intro d hd; omega
    | succ k ih =>
      have hk : weightedHomogeneousComponent w k p = 0 := by
        cases k with
        | zero => exact h₀
        | succ m =>
          set q := weightedHomogeneousComponent w (m + 1) p
          have hq : ∀ i, w i = 1 → pderiv i q = 0 := by
            intro i hi
            obtain ⟨D, hDp, hne, hother⟩ := hD i hi
            have he := weightedHomogeneousComponent_derivation_of_lowWeight w hw D ih
            rw [hDp, map_zero, Finset.sum_eq_single i] at he
            · rw [hi, one_smul] at he
              exact (mul_eq_zero.mp he.symm).resolve_right hne
            · intro j _ hji
              rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hw j) with h | h
              · rw [h, zero_smul]
              · rw [hother j hji h, mul_zero, smul_zero]
            · simp
          have heu := (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) (m + 1)
            p).sum_weight_X_mul_pderiv
          have hz : ∑ i, w i • (X i * pderiv i q) = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hw i) with h | h
            · rw [h, zero_smul]
            · rw [hq i h, mul_zero, smul_zero]
          rw [hz, ← Nat.cast_smul_eq_nsmul K, eq_comm, smul_eq_zero] at heu
          exact heu.resolve_left (by exact_mod_cast Nat.succ_ne_zero m)
      intro d hd
      by_cases h : weight w d < k
      · exact ih d h
      · have := congrArg (fun q => q.coeff d) hk
        simpa [coeff_weightedHomogeneousComponent, show weight w d = k by omega]
          using this
  ext d
  exact key _ d (Nat.lt_succ_self _)

end Field

end MvPolynomial
