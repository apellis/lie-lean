/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Nondegeneracy of bilinear forms under extension of scalars

For a field `K`, a commutative `K`-algebra `L` and a bilinear form `B` on a `K`-vector space `M`
whose left radical is zero, the base change `B_L` on `L ⊗_K M` has zero left radical; in fact
`B_L(x, 1 ⊗ y) = 0` for all `y ∈ M` already forces `x = 0`. No finiteness is assumed. The proof
writes `x = Σᵢ bᵢ ⊗ mᵢ` along a `K`-basis `(bᵢ)` of `L`.

This is the transfer step used to deduce nondegeneracy of a form over a field `k` from
nondegeneracy over a subfield, for instance for Lusztig's form on the modified quantum group
`U̇` ([Lus] 26.3.1) from `ℚ(v)` to a field containing `ℚ(v)`.

## Main results

* `LinearMap.BilinForm.exists_eq_sum_tmul_basis`: `x = Σᵢ bᵢ ⊗ mᵢ` for a basis `(bᵢ)` of `L`.
* `LinearMap.BilinForm.eq_zero_of_baseChange_tmul_one_eq_zero`: the transfer lemma.
* `LinearMap.BilinForm.eq_zero_of_baseChange_equiv`: the same for a form on an `L`-module
  identified with `L ⊗_K M`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 26.3.1.
-/

open TensorProduct

namespace LinearMap.BilinForm

variable {K L M : Type*} [Field K] [CommRing L] [Algebra K L] [AddCommGroup M] [Module K M]

/-- Writing `x ∈ L ⊗_K M` as `Σ bᵢ ⊗ mᵢ` along a `K`-basis `b` of `L`. -/
theorem exists_eq_sum_tmul_basis {ι : Type*} (b : Module.Basis ι K L) (x : L ⊗[K] M) :
    ∃ f : ι →₀ M, x = f.sum fun i m ↦ b i ⊗ₜ m := by
  classical
  let e : L ⊗[K] M ≃ₗ[K] ι →₀ M :=
    (LinearEquiv.rTensor M b.repr).trans (finsuppScalarLeft K M ι)
  refine ⟨e x, e.injective ?_⟩
  rw [map_finsuppSum]
  conv_lhs => rw [← (e x).sum_single]
  refine Finsupp.sum_congr fun i _ ↦ ?_
  simp [e, finsuppScalarLeft_apply_tmul]

/-- If `(x, ·)` vanishes on `1 ⊗ M` for the base change of a left-separating form, then `x = 0`.
The proof writes `x = Σ bᵢ ⊗ mᵢ` with `(bᵢ)` linearly independent over `K`. -/
theorem eq_zero_of_baseChange_tmul_one_eq_zero (B : LinearMap.BilinForm K M)
    (hB : ∀ x, (∀ y, B x y = 0) → x = 0) {x : L ⊗[K] M}
    (hx : ∀ y : M, B.baseChange L x (1 ⊗ₜ y) = 0) : x = 0 := by
  classical
  let b := Module.Free.chooseBasis K L
  obtain ⟨f, rfl⟩ := exists_eq_sum_tmul_basis b x
  have hf : ∀ i, f i = 0 := by
    intro i
    by_cases hi : i ∈ f.support
    · refine hB _ fun y ↦ ?_
      have h := hx y
      rw [Finsupp.sum, map_sum, LinearMap.sum_apply] at h
      simp only [baseChange_tmul, mul_one] at h
      exact linearIndependent_iff'.mp b.linearIndependent f.support (fun i ↦ B (f i) y) h i hi
    · simpa using hi
  have hf0 : f = 0 := Finsupp.ext fun i ↦ by simpa using hf i
  simp [hf0]

/-- Transfer of left nondegeneracy along an identification `e : L ⊗_K M ≃ M'` matching a form
`B'` on `M'` with the base change of `B` on the vectors `1 ⊗ y`. -/
theorem eq_zero_of_baseChange_equiv {M' : Type*} [AddCommGroup M'] [Module L M']
    (B : LinearMap.BilinForm K M) (hB : ∀ x, (∀ y, B x y = 0) → x = 0)
    (B' : LinearMap.BilinForm L M') (e : L ⊗[K] M ≃ₗ[L] M')
    (he : ∀ x y, B' (e x) (e (1 ⊗ₜ y)) = B.baseChange L x (1 ⊗ₜ y)) {x' : M'}
    (hx' : ∀ y', B' x' y' = 0) : x' = 0 := by
  rw [← e.apply_symm_apply x', eq_zero_of_baseChange_tmul_one_eq_zero B hB
    (x := e.symm x') fun y ↦ by rw [← he, e.apply_symm_apply, hx'], map_zero]

end LinearMap.BilinForm
