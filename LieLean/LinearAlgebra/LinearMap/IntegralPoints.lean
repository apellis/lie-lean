/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Non-injectivity of affine families of linear maps at integral points

Let `g(y) = A + ∑ⱼ yⱼ Bⱼ` be a family of linear maps `N → V`, with `N` finite-dimensional over a
field of characteristic zero, depending affinely on `y ∈ K^ι`. If `g(y)` is not injective at
every integral point `y ∈ ℤ^ι` outside the zero set of a nonzero polynomial `D`, then `g(y)` is
not injective for every `y ∈ K^ι` (`LinearMap.not_injective_add_sum_smul_of_forall_int`).

This is the Zariski density argument of [HumO] §4.7, in a form that does not mention the Zariski
topology: for a left inverse `φ` of `g(y₀)`, the function `y ↦ det(φ ∘ g(y))` is a polynomial,
it vanishes at the integral points by hypothesis, and so it vanishes identically by the
Combinatorial Nullstellensatz (`MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`).

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §4.7.
-/

open MvPolynomial

namespace LinearMap

variable {ι K N V : Type*} [Fintype ι] [Field K] [CharZero K] [AddCommGroup N] [Module K N]
  [FiniteDimensional K N] [AddCommGroup V] [Module K V]

omit [Fintype ι] in
/-- A polynomial vanishing at all integral points (of a field of characteristic zero) is zero. -/
theorem _root_.MvPolynomial.eq_zero_of_eval_int_eq_zero [Finite ι] (P : MvPolynomial ι K)
    (h : ∀ y : ι → ℤ, eval (fun j ↦ (y j : K)) P = 0) : P = 0 := by
  classical
  cases nonempty_fintype ι
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun j ↦ (Finset.range (P.degreeOf j + 1)).image (fun k : ℕ ↦ (k : K))) (fun j ↦ ?_)
    (fun x hx ↦ ?_)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    omega
  · choose k hk using fun j ↦ Finset.mem_image.mp (hx j)
    have hxk : x = fun j ↦ ((k j : ℤ) : K) := funext fun j ↦ by simp [(hk j).2]
    rw [hxk]
    exact h _

/-- **Density of integral points** ([HumO] §4.7): if `A + ∑ⱼ yⱼ Bⱼ` is not injective at every
integral point `y` where a fixed nonzero polynomial `D` does not vanish, then it is not injective
at any point `y ∈ K^ι`. -/
theorem not_injective_add_sum_smul_of_forall_int (A : N →ₗ[K] V) (B : ι → N →ₗ[K] V)
    {D : MvPolynomial ι K} (hD : D ≠ 0)
    (h : ∀ y : ι → ℤ, eval (fun j ↦ (y j : K)) D ≠ 0 →
      ¬Function.Injective (A + ∑ j, (y j : K) • B j))
    (y : ι → K) : ¬Function.Injective (A + ∑ j, y j • B j) := by
  classical
  intro hinj
  obtain ⟨φ, hφ⟩ := (A + ∑ j, y j • B j).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  set b := Module.finBasis K N
  let M : Matrix _ _ (MvPolynomial ι K) :=
    (LinearMap.toMatrix b b (φ ∘ₗ A)).map C +
      ∑ j, (X j : MvPolynomial ι K) • (LinearMap.toMatrix b b (φ ∘ₗ B j)).map C
  have heval : ∀ z : ι → K,
      eval z M.det = LinearMap.det (φ ∘ₗ (A + ∑ j, z j • B j)) := by
    intro z
    have hc : φ ∘ₗ (A + ∑ j, z j • B j) = φ ∘ₗ A + ∑ j, z j • (φ ∘ₗ B j) := by
      ext m
      simp
    rw [hc, ← LinearMap.det_toMatrix b, RingHom.map_det]
    congr 1
    ext p q
    simp only [M, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, map_add, map_sum, map_mul, eval_C, eval_X, map_smul]
  have hint : ∀ z : ι → ℤ, eval (fun j ↦ (z j : K)) (M.det * D) = 0 := by
    intro z
    rw [map_mul, heval]
    by_cases hz : eval (fun j ↦ (z j : K)) D = 0
    · rw [hz, mul_zero]
    · refine mul_eq_zero_of_left ?_ _
      by_contra hdet
      have hu : IsUnit (φ ∘ₗ (A + ∑ j, (z j : K) • B j)) :=
        (LinearMap.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hdet)
      exact h z hz (Function.Injective.of_comp
        (f := φ) ((Module.End.isUnit_iff _).mp hu).injective)
  have h0 : M.det * D = 0 := MvPolynomial.eq_zero_of_eval_int_eq_zero _ hint
  have hM : M.det = 0 := (mul_eq_zero.mp h0).resolve_right hD
  have := heval y
  rw [hM, map_zero, hφ, LinearMap.det_id] at this
  exact zero_ne_one this

end LinearMap
