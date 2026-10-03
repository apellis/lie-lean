/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.Specialization
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Base change of Iwahori–Hecke algebras

For an `R`-algebra `S`, the base change `S ⊗[R] 𝓗_q(W)` of the Iwahori–Hecke algebra is the
Iwahori–Hecke algebra `𝓗_{q'}(W)` over `S` with parameter `q'` the image of `q`
(`IwahoriHeckeAlgebra.baseChangeEquiv`). In particular, if `q` maps to `1` in `S`, then
`S ⊗[R] 𝓗_q(W) ≃ S[W]` (`IwahoriHeckeAlgebra.baseChangeEquivMonoidAlgebra`); for
`R = A[v, v⁻¹]`, `q = v²` and `S = A` with `v ↦ 1` this is the specialization `𝓗 ⊗ A ≃ A[W]`
at `v = 1` ([GP] 8.1.2, Remark 8.1.5).

## Main definitions

* `IwahoriHeckeAlgebra.equivOfEq`: `𝓗_q(W) ≃ 𝓗_{q'}(W)` for `q = q'`.
* `IwahoriHeckeAlgebra.baseChangeEquiv`: `S ⊗[R] 𝓗_q(W) ≃ₐ[S] 𝓗_{q'}(W)`.
* `IwahoriHeckeAlgebra.baseChangeEquivMonoidAlgebra`: `S ⊗[R] 𝓗_q(W) ≃ₐ[S] S[W]` if `q ↦ 1`.

## References

* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184.
* [GP] M. Geck, G. Pfeiffer, *Characters of finite Coxeter groups and Iwahori–Hecke algebras*,
  LMS Monographs 21, OUP 2000.
-/

open Module
open scoped TensorProduct

namespace IwahoriHeckeAlgebra

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {R : Type*} [CommRing R] (q : R)

/-- The Iwahori–Hecke algebras for equal parameters are isomorphic, `T_w ↦ T_w`. -/
noncomputable def equivOfEq {q' : R} (h : q = q') :
    IwahoriHeckeAlgebra cs q ≃ₐ[R] IwahoriHeckeAlgebra cs q' := by
  subst h
  exact AlgEquiv.refl

@[simp]
theorem equivOfEq_T {q' : R} (h : q = q') (w : W) : equivOfEq cs q h (T cs q w) = T cs q' w := by
  subst h
  rfl

variable (S : Type*) [CommRing S] [Algebra R S]

/-- The `S`-linear isomorphism `S ⊗[R] 𝓗_q(W) ≃ 𝓗_{q'}(W)`, `a ⊗ T_w ↦ a T_w`. -/
noncomputable def baseChangeLinearEquiv :
    S ⊗[R] IwahoriHeckeAlgebra cs q ≃ₗ[S] IwahoriHeckeAlgebra cs (algebraMap R S q) :=
  (Algebra.TensorProduct.basis S (basis cs q)).equiv (basis cs (algebraMap R S q)) (Equiv.refl W)

theorem baseChangeLinearEquiv_tmul (a : S) (h : IwahoriHeckeAlgebra cs q) :
    baseChangeLinearEquiv cs q S (a ⊗ₜ h) = a • map cs q (algebraMap R S) rfl h := by
  induction h using induction_on cs q generalizing a with
  | T w =>
    have : a ⊗ₜ[R] T cs q w = a • Algebra.TensorProduct.basis S (basis cs q) w := by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        basis_apply]
    rw [this, map_smul, baseChangeLinearEquiv, Basis.equiv_apply, map_T, Equiv.refl_apply,
      basis_apply]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add, smul_add]
  | smul r x hx =>
    rw [← TensorProduct.smul_tmul, hx, map_apply_smul, smul_smul]
    congr 1
    rw [Algebra.smul_def, mul_comm]

/-- Base change of Iwahori–Hecke algebras: `S ⊗[R] 𝓗_q(W) ≃ₐ[S] 𝓗_{q'}(W)` for an `R`-algebra
`S`, where `q'` is the image of `q` in `S`. -/
noncomputable def baseChangeEquiv :
    S ⊗[R] IwahoriHeckeAlgebra cs q ≃ₐ[S] IwahoriHeckeAlgebra cs (algebraMap R S q) :=
  AlgEquiv.ofLinearEquiv (baseChangeLinearEquiv cs q S)
    (by rw [Algebra.TensorProduct.one_def, baseChangeLinearEquiv_tmul, map_one, one_smul])
    (fun x y ↦ by
      induction x with
      | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
      | tmul a h =>
        induction y with
        | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
        | tmul b h' =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, baseChangeLinearEquiv_tmul,
            baseChangeLinearEquiv_tmul, baseChangeLinearEquiv_tmul, map_mul,
            smul_mul_smul_comm])

@[simp]
theorem baseChangeEquiv_tmul (a : S) (h : IwahoriHeckeAlgebra cs q) :
    baseChangeEquiv cs q S (a ⊗ₜ h) = a • map cs q (algebraMap R S) rfl h :=
  baseChangeLinearEquiv_tmul cs q S a h

/-- If `q` maps to `1` in the `R`-algebra `S`, then `S ⊗[R] 𝓗_q(W) ≃ₐ[S] S[W]`,
`a ⊗ T_w ↦ a w`. For `R = A[v, v⁻¹]`, `q = v²` and `S = A` via `v ↦ 1`, this is the
specialization of the generic Hecke algebra at `v = 1` ([GP] Remark 8.1.5). -/
noncomputable def baseChangeEquivMonoidAlgebra (hq : algebraMap R S q = 1) :
    S ⊗[R] IwahoriHeckeAlgebra cs q ≃ₐ[S] MonoidAlgebra S W :=
  ((baseChangeEquiv cs q S).trans (equivOfEq cs _ hq)).trans (equivMonoidAlgebra cs)

theorem baseChangeEquivMonoidAlgebra_tmul (hq : algebraMap R S q = 1) (a : S) (w : W) :
    baseChangeEquivMonoidAlgebra cs q S hq (a ⊗ₜ T cs q w) = a • MonoidAlgebra.of S W w := by
  simp [baseChangeEquivMonoidAlgebra]

end IwahoriHeckeAlgebra
