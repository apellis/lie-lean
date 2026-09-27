/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import LieLean.LinearAlgebra.Matrix.Cartan.Symmetrizable

/-!
# Cartan data in the sense of Lusztig

A *Cartan datum* ([Lus] 1.1.1 (check)) is a set `I` together with a symmetric bilinear form
`ν, ν' ↦ ν · ν'` on `ℤ[I]` with values in `ℤ` such that `i · i ∈ {2, 4, 6, …}` for `i ∈ I` and
`2 (i · j)/(i · i) ∈ {0, -1, -2, …}` for `i ≠ j`. We record the form through its values
`i · j` on the basis `I`.

A Cartan datum determines the symmetrizable generalized Cartan matrix `aᵢⱼ = 2 (i·j)/(i·i)`
(`CartanDatum.cartanMatrix`), with symmetrizer `dᵢ = (i·i)/2`: `dᵢ aᵢⱼ = i · j`. Conversely,
every symmetrization of a generalized Cartan matrix (`Matrix.Symmetrization`, positive rationals
`εᵢ` with `εⱼ aᵢⱼ = εᵢ aⱼᵢ`) gives rise to a Cartan datum with the same Cartan matrix, by clearing
denominators in `dᵢ ∝ 1/εᵢ` (`CartanDatum.ofSymmetrization`).

## Main definitions

* `CartanDatum`: Lusztig's Cartan datum `(I, ·)`.
* `CartanDatum.d`: `dᵢ = (i·i)/2`, so that `vᵢ = v^{dᵢ}`.
* `CartanDatum.cartanMatrix`: the matrix `aᵢⱼ = 2 (i·j)/(i·i)`.
* `CartanDatum.weightDot`: the form `ν · μ` on weights `ν, μ ∈ ℕ[I]` (`I →₀ ℕ`).
* `CartanDatum.ofSymmetrization`: the Cartan datum of a symmetrized GCM.

## Main results

* `CartanDatum.isGeneralizedCartan_cartanMatrix`: `(aᵢⱼ)` is a generalized Cartan matrix.
* `CartanDatum.d_mul_cartanMatrix`: `dᵢ aᵢⱼ = i · j`.
* `CartanDatum.cartanMatrix_ofSymmetrization`: the bridge recovers the matrix.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §1.1.
-/

open Finset

/-- A Cartan datum in the sense of Lusztig ([Lus] 1.1.1 (check)): a symmetric `ℤ`-valued
bilinear form on `ℤ[I]`, given by its values `dot i j = i · j` on the basis, such that
`i · i` is even and positive, and `2 (i · j)/(i · i)` is a nonpositive integer for `i ≠ j`. -/
structure CartanDatum (I : Type*) where
  /-- The values `i · j` of the bilinear form on the basis `I` of `ℤ[I]`. -/
  dot : I → I → ℤ
  dot_comm : ∀ i j, dot i j = dot j i
  dot_self_pos : ∀ i, 0 < dot i i
  even_dot_self : ∀ i, Even (dot i i)
  dot_nonpos : ∀ i j, i ≠ j → dot i j ≤ 0
  dot_self_dvd : ∀ i j, dot i i ∣ 2 * dot i j

namespace CartanDatum

variable {I : Type*} (D : CartanDatum I)

/-- `dᵢ = (i · i)/2`, a positive integer ([Lus] 1.1.1 (check)); `vᵢ = v^{dᵢ}`. -/
def d (i : I) : ℕ := (D.dot i i / 2).toNat

lemma two_mul_d (i : I) : 2 * (D.d i : ℤ) = D.dot i i := by
  obtain ⟨m, hm⟩ := D.even_dot_self i
  have := D.dot_self_pos i
  simp only [d, hm]
  omega

lemma d_pos (i : I) : 0 < D.d i := by
  have h1 := D.two_mul_d i
  have h2 := D.dot_self_pos i
  omega

/-- The generalized Cartan matrix `aᵢⱼ = 2 (i · j)/(i · i)` of the Cartan datum
([Lus] 2.1.1 (check)). -/
def cartanMatrix : Matrix I I ℤ := Matrix.of fun i j ↦ 2 * D.dot i j / D.dot i i

/-- `dᵢ aᵢⱼ = i · j`. -/
lemma d_mul_cartanMatrix (i j : I) : (D.d i : ℤ) * D.cartanMatrix i j = D.dot i j := by
  obtain ⟨c, hc⟩ := D.dot_self_dvd i j
  have hpos := D.dot_self_pos i
  have h2 := D.two_mul_d i
  simp only [cartanMatrix, Matrix.of_apply, hc, Int.mul_ediv_cancel_left _ hpos.ne']
  have : 2 * ((D.d i : ℤ) * c) = 2 * D.dot i j := by rw [hc, ← h2]; ring
  omega

lemma cartanMatrix_self (i : I) : D.cartanMatrix i i = 2 := by
  simp [cartanMatrix, Int.mul_ediv_cancel _ (D.dot_self_pos i).ne']

lemma cartanMatrix_eq_zero_iff (i j : I) : D.cartanMatrix i j = 0 ↔ D.dot i j = 0 := by
  rw [← D.d_mul_cartanMatrix]
  have := D.d_pos i
  constructor
  · intro h; rw [h, mul_zero]
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · omega
    · exact h

/-- The matrix of a Cartan datum is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_cartanMatrix : D.cartanMatrix.IsGeneralizedCartan where
  diag := D.cartanMatrix_self
  offDiag_nonpos i j hij := by
    have h1 := D.d_mul_cartanMatrix i j
    have h2 := D.dot_nonpos i j hij
    have h3 := D.d_pos i
    by_contra h
    have : 0 < (D.d i : ℤ) * D.cartanMatrix i j := mul_pos (by omega) (not_le.1 h)
    omega
  zero_comm i j := by
    rw [D.cartanMatrix_eq_zero_iff, D.cartanMatrix_eq_zero_iff, D.dot_comm]

/-- The symmetrizer: `dᵢ aᵢⱼ = dⱼ aⱼᵢ`. -/
lemma d_mul_cartanMatrix_comm (i j : I) :
    (D.d i : ℤ) * D.cartanMatrix i j = D.d j * D.cartanMatrix j i := by
  rw [D.d_mul_cartanMatrix, D.d_mul_cartanMatrix, D.dot_comm]

/-- The bilinear form `ν · μ = Σ_{i,j} νᵢ μⱼ (i · j)` on weights `ν, μ ∈ ℕ[I]`. -/
def weightDot (ν μ : I →₀ ℕ) : ℤ :=
  ν.sum fun i a ↦ μ.sum fun j b ↦ (a * b : ℤ) * D.dot i j

@[simp] lemma weightDot_zero_left (μ : I →₀ ℕ) : D.weightDot 0 μ = 0 := by simp [weightDot]

@[simp] lemma weightDot_zero_right (ν : I →₀ ℕ) : D.weightDot ν 0 = 0 := by simp [weightDot]

lemma weightDot_add_left (ν ν' μ : I →₀ ℕ) :
    D.weightDot (ν + ν') μ = D.weightDot ν μ + D.weightDot ν' μ := by
  unfold weightDot
  rw [Finsupp.sum_add_index']
  · intro i; simp
  · intro i a b; simp [add_mul, Finsupp.sum_add]

lemma weightDot_add_right (ν μ μ' : I →₀ ℕ) :
    D.weightDot ν (μ + μ') = D.weightDot ν μ + D.weightDot ν μ' := by
  unfold weightDot
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun i _ ↦ ?_
  rw [Finsupp.sum_add_index']
  · intro j; simp
  · intro j a b; push_cast; ring

@[simp] lemma weightDot_single_single (i j : I) :
    D.weightDot (Finsupp.single i 1) (Finsupp.single j 1) = D.dot i j := by
  simp [weightDot]

lemma weightDot_comm (ν μ : I →₀ ℕ) : D.weightDot ν μ = D.weightDot μ ν := by
  unfold weightDot
  rw [Finsupp.sum_comm]
  refine Finsupp.sum_congr fun i _ ↦ Finsupp.sum_congr fun j _ ↦ ?_
  rw [D.dot_comm]; ring

/-! ### From a symmetrization of a generalized Cartan matrix -/

section Symmetrization

variable [Fintype I] [DecidableEq I] {A : Matrix I I ℤ}

/-- The integral symmetrizer `dᵢ = den(εᵢ) ∏_{k ≠ i} num(εₖ)`, proportional to `1/εᵢ`. -/
def symmetrizerOf (S : A.Symmetrization) (i : I) : ℤ :=
  (S.ε i).den * ∏ k ∈ univ.erase i, (S.ε k).num

lemma symmetrizerOf_pos (S : A.Symmetrization) (i : I) : 0 < symmetrizerOf S i :=
  mul_pos (by exact_mod_cast (S.ε i).den_pos)
    (prod_pos fun k _ ↦ Rat.num_pos.2 (S.ε_pos k))

lemma symmetrizerOf_mul_ε (S : A.Symmetrization) (i : I) :
    (symmetrizerOf S i : ℚ) * S.ε i = ∏ k, ((S.ε k).num : ℚ) := by
  rw [← mul_prod_erase univ (fun k ↦ ((S.ε k).num : ℚ)) (mem_univ i), symmetrizerOf]
  push_cast
  linear_combination (∏ k ∈ univ.erase i, ((S.ε k).num : ℚ)) * Rat.mul_den_eq_num (S.ε i)

lemma symmetrizerOf_mul_comm (S : A.Symmetrization) (i j : I) :
    symmetrizerOf S i * A i j = symmetrizerOf S j * A j i := by
  have hi := symmetrizerOf_mul_ε S i
  have hj := symmetrizerOf_mul_ε S j
  have h := S.ε_mul_comm i j
  have hεi := S.ε_ne_zero i
  have hεj := S.ε_ne_zero j
  have : ((symmetrizerOf S i * A i j : ℤ) : ℚ) = ((symmetrizerOf S j * A j i : ℤ) : ℚ) := by
    push_cast
    apply mul_right_cancel₀ (mul_ne_zero hεi hεj)
    calc (symmetrizerOf S i : ℚ) * A i j * (S.ε i * S.ε j)
        = ((symmetrizerOf S i : ℚ) * S.ε i) * (S.ε j * A i j) := by ring
      _ = ((symmetrizerOf S j : ℚ) * S.ε j) * (S.ε i * A j i) := by rw [hi, hj, h]
      _ = _ := by ring
  exact_mod_cast this

/-- The Cartan datum `i · j = dᵢ aᵢⱼ` of a generalized Cartan matrix `A` with a symmetrization
`S`, where `dᵢ = symmetrizerOf S i` is the integral symmetrizer proportional to `1/εᵢ`. -/
def ofSymmetrization (hA : A.IsGeneralizedCartan) (S : A.Symmetrization) : CartanDatum I where
  dot i j := symmetrizerOf S i * A i j
  dot_comm := symmetrizerOf_mul_comm S
  dot_self_pos i := by rw [hA.diag]; exact mul_pos (symmetrizerOf_pos S i) two_pos
  even_dot_self i := by rw [hA.diag]; exact even_two.mul_left _
  dot_nonpos i j hij := mul_nonpos_of_nonneg_of_nonpos (symmetrizerOf_pos S i).le
    (hA.offDiag_nonpos i j hij)
  dot_self_dvd i j := by rw [hA.diag]; exact ⟨A i j, by ring⟩

/-- The Cartan datum of a symmetrized generalized Cartan matrix has Cartan matrix `A`. -/
theorem cartanMatrix_ofSymmetrization (hA : A.IsGeneralizedCartan) (S : A.Symmetrization) :
    (ofSymmetrization hA S).cartanMatrix = A := by
  ext i j
  simp only [cartanMatrix, ofSymmetrization, Matrix.of_apply, hA.diag]
  rw [show 2 * (symmetrizerOf S i * A i j) = (symmetrizerOf S i * 2) * A i j by ring,
    Int.mul_ediv_cancel_left _ (mul_pos (symmetrizerOf_pos S i) two_pos).ne']

end Symmetrization

end CartanDatum
