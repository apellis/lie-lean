/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroup
import LieLean.LinearAlgebra.Matrix.Cartan.Symmetrizable

/-!
# The Weyl group preserves the form on `𝔥*`

For a symmetrization `S` of a generalized Cartan matrix `A`, the Weyl group preserves the
symmetric bilinear form `(·|·)` on `𝔥*` ([Kac] Prop. 3.9). For positive integers `dᵢ` with
`diag(d) A` symmetric (e.g. those of a finite-type Cartan matrix, `Matrix.IsFiniteCartan`), the
symmetrization `εᵢ = 1 / dᵢ` has `(∑ kᵢ αᵢ | x) = ∑ kᵢ dᵢ ⟨x, αᵢ^∨⟩`; on the root lattice its
values are those of the integral quadratic form `kᵀ diag(d) A k`.

## Main definitions

* `Matrix.Symmetrization.ofDiagonal`: the symmetrization `εᵢ = 1 / dᵢ` of a matrix with
  `diag(d) A` symmetric.

## Main results

* `Matrix.Realization.dualBilinForm_weylGroup`: `(w μ | w μ') = (μ | μ')` for `w ∈ W`.
* `Matrix.Realization.dualBilinForm_ofDiagonal_rootOf`: `(∑ kᵢ αᵢ | x) = ∑ kᵢ dᵢ ⟨x, αᵢ^∨⟩`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Prop. 3.9.
-/

noncomputable section

open Module

namespace Matrix.Symmetrization

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ}

/-- The symmetrization `εᵢ = 1 / dᵢ` attached to positive integers `dᵢ` with `diag(d) A`
symmetric; its symmetric matrix is `diag(d) A`. -/
def ofDiagonal (d : ι → ℤ) (hd : ∀ i, 0 < d i) (hsymm : (diagonal d * A).IsSymm) :
    A.Symmetrization where
  ε i := 1 / d i
  ε_pos i := by have := hd i; positivity
  ε_mul_comm i j := by
    have h := congrFun (congrFun hsymm i) j
    simp only [transpose_apply, diagonal_mul] at h
    have hi : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
    have hj : (d j : ℚ) ≠ 0 := by exact_mod_cast (hd j).ne'
    have h' : (d j * A j i : ℚ) = d i * A i j := by exact_mod_cast h
    field_simp
    linarith

end Matrix.Symmetrization

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  [FiniteDimensional K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsGeneralizedCartan) (S : A.Symmetrization)

/-! ### `W`-invariance of the form on `𝔥*` -/

/-- The fundamental reflections preserve the form: `(rᵢ μ | rᵢ μ') = (μ | μ')`. -/
theorem dualBilinForm_reflection (i : ι) (μ μ' : Dual K H) :
    P.dualBilinForm S (P.reflection hA i μ) (P.reflection hA i μ') =
      P.dualBilinForm S μ μ' := by
  have h1 := P.dualBilinForm_root_right S μ i
  have h2 : P.dualBilinForm S (P.root i) μ' = μ' (P.coroot i) / S.ε i := by
    rw [(P.isSymm_dualBilinForm S).eq]
    exact P.dualBilinForm_root_right S μ' i
  have h3 := P.dualBilinForm_root_right S (P.root i) i
  rw [P.root_coroot, hA.diag] at h3
  have hε : (S.ε i : K) ≠ 0 := by exact_mod_cast S.ε_ne_zero i
  simp only [reflection_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, h1, h2, h3]
  push_cast
  field_simp
  ring

/-- The Weyl group preserves the form: `(w μ | w μ') = (μ | μ')` ([Kac] Prop. 3.9). -/
theorem dualBilinForm_weylGroup {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    (μ μ' : Dual K H) : P.dualBilinForm S (w μ) (w μ') = P.dualBilinForm S μ μ' := by
  refine P.weylGroup_induction hA (p := fun w ↦ ∀ μ μ',
    P.dualBilinForm S (w μ) (w μ') = P.dualBilinForm S μ μ') (fun _ _ ↦ rfl)
    (fun i w ih μ μ' ↦ ?_) hw μ μ'
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, dualBilinForm_reflection, ih]

variable [DecidableEq ι]

/-- For the symmetrization `εᵢ = 1 / dᵢ`, `(∑ kᵢ αᵢ | x) = ∑ kᵢ dᵢ ⟨x, αᵢ^∨⟩`. -/
theorem dualBilinForm_ofDiagonal_rootOf (d : ι → ℤ) (hd : ∀ i, 0 < d i)
    (hsymm : (diagonal d * A).IsSymm) (k : ι → ℤ) (x : Dual K H) :
    P.dualBilinForm (Symmetrization.ofDiagonal d hd hsymm) (P.rootOf k) x =
      ∑ i, ((k i * d i : ℤ) : K) * x (P.coroot i) := by
  rw [P.rootOf_apply, map_sum (P.dualBilinForm (Symmetrization.ofDiagonal d hd hsymm)),
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, (P.isSymm_dualBilinForm _).eq, dualBilinForm_root_right,
    smul_eq_mul]
  simp only [Symmetrization.ofDiagonal]
  push_cast
  have hi : (d i : K) ≠ 0 := by exact_mod_cast (hd i).ne'
  field_simp

end Matrix.Realization
