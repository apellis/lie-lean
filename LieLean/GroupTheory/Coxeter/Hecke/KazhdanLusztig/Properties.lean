/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig
import LieLean.GroupTheory.Coxeter.Hecke.Specialization

/-!
# Properties of Kazhdan–Lusztig polynomials

We continue with the Kazhdan–Lusztig basis `C'_w` and the Kazhdan–Lusztig polynomials `P_{y,w}`
of `LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig` (normalization of [KL]: `q = v²`,
`C'_w = v^{-ℓ(w)} Σ_{y ≤ w} P_{y,w}(q) T_y`).

## Main results

* `IwahoriHeckeAlgebra.T_simple_mul_klBasis`: if `sw < w`, then `T_s C'_w = q C'_w`
  ([KL] (2.3.c), stated there for the basis `C_w`).
* `IwahoriHeckeAlgebra.klPoly_simple_mul_left`: if `sw < w`, then `P_{sx,w} = P_{x,w}` for all
  `x` ([KL] (2.3.g)).
* `IwahoriHeckeAlgebra.coeff_zero_klPoly`: `P_{y,w}(0) = 1` for `y ≤ w`;
  in particular `P_{1,w}(0) = 1` (`coeff_zero_klPoly_one_left`) ([KL] Lemma 2.6(i)).
* `IwahoriHeckeAlgebra.klMu_eq_one`: `μ(y, w) = 1` if `y ≤ w` and `ℓ(w) = ℓ(y) + 1`.
* `IwahoriHeckeAlgebra.klPoly_eq_one_of_length_le_two`: `P_{y,w} = 1` for `y ≤ w` if
  `ℓ(w) ≤ 2`.
* `IwahoriHeckeAlgebra.specializeOne_klBasis`: at `v = 1`, `C'_w` specializes to
  `Σ_{y ≤ w} P_{y,w}(1) y ∈ ℤ[W]`; e.g. `C'_s ↦ 1 + s` (`specializeOne_klBasis_simple`).

The arguments are the standard ones; the proofs of `T_simple_mul_klBasis` (induction on `ℓ(w)`
through the multiplication formula `C'_s C'_v = C'_{sv} + Σ μ(z,v) C'_z`) and of
`coeff_zero_klPoly` (the recursion [KL] (2.2.c) at `q = 0`) were reconstructed by us.

## References

* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184, §2.
-/

open Finsupp

namespace IwahoriHeckeAlgebra

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "ℓ " => cs.length

local notation "𝓗" => IwahoriHeckeAlgebra cs (LaurentPolynomial.T 2 : LaurentPolynomial ℤ)

theorem T_simple_mul_klSimple (i : B) :
    T cs _ (s i) * klSimple cs i =
      (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) • klSimple cs i := by
  have e : T cs (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) (s i) * (T cs _ (s i) + 1) =
      (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) • (T cs _ (s i) + 1) := by
    rw [mul_add, T_simple_mul_self, mul_one, Algebra.algebraMap_eq_smul_one, smul_add,
      sub_smul, one_smul]
    abel
  rw [klSimple, mul_smul_comm, e, smul_comm]

variable {cs} in
theorem length_lt_of_mem_descentsBelow {i : B} {v z : W} (hv : ℓ v < ℓ (s i * v))
    (hz : z ∈ descentsBelow cs i v) : ℓ z < ℓ v := by
  obtain ⟨h1, h2⟩ := mem_descentsBelow.mp hz
  rcases h1.eq_or_length_lt with rfl | h
  · omega
  · exact h

/-- If `sw < w`, then `T_s C'_w = q C'_w` ([KL] (2.3.c), there for `C_w`). -/
theorem T_simple_mul_klBasis {i : B} {w : W} (hw : ℓ (s i * w) < ℓ w) :
    T cs _ (s i) * klBasis cs w =
      (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) • klBasis cs w := by
  induction hn : ℓ w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  subst hn
  have hv : ℓ (s i * w) < ℓ (s i * (s i * w)) := by
    rwa [CoxeterSystem.simple_mul_simple_cancel_left]
  have h := klSimple_mul_klBasis cs hv
  rw [CoxeterSystem.simple_mul_simple_cancel_left] at h
  rw [← sub_eq_of_eq_add h, mul_sub, ← mul_assoc, T_simple_mul_klSimple, smul_mul_assoc,
    Finset.mul_sum, smul_sub, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  rw [mul_smul_comm, smul_comm]
  congr 1
  have := length_lt_of_mem_descentsBelow hv hz
  exact ih (ℓ z) (by omega) (mem_descentsBelow.mp hz).2 rfl

/-- **Invariance of Kazhdan–Lusztig polynomials** ([KL] (2.3.g)): if `sw < w`, then
`P_{sx,w} = P_{x,w}` for all `x`. -/
theorem klPoly_simple_mul_left {i : B} {w : W} (hw : ℓ (s i * w) < ℓ w) (x : W) :
    klPoly cs (s i * x) w = klPoly cs x w := by
  have key : ∀ y, ℓ (s i * y) < ℓ y → klPoly cs (s i * y) w = klPoly cs y w := by
    intro y hy
    have := congrArg (fun h ↦ toFinsupp cs _ h y) (T_simple_mul_klBasis cs hw)
    simp only [toFinsupp_T_simple_mul, leftOp_apply, hy, ite_true, map_smul,
      Finsupp.smul_apply, smul_eq_mul] at this
    have e : toFinsupp cs _ (klBasis cs w) (s i * y) = toFinsupp cs _ (klBasis cs w) y := by
      linear_combination this
    rw [toFinsupp_klBasis_apply, toFinsupp_klBasis_apply] at e
    exact T_mul_aeval_T_two_injective _ e
  by_cases hx : ℓ (s i * x) < ℓ x
  · exact key x hx
  · have hx' : ℓ (s i * (s i * x)) < ℓ (s i * x) := by
      rw [CoxeterSystem.simple_mul_simple_cancel_left]
      rcases cs.length_simple_mul x i with h | h <;> omega
    have := key _ hx'
    rw [CoxeterSystem.simple_mul_simple_cancel_left] at this
    exact this.symm

/-- **The constant term of Kazhdan–Lusztig polynomials** ([KL] Lemma 2.6(i)): `P_{y,w}(0) = 1` if
`y ≤ w` (recall that `P_{y,w} = 0` otherwise, `klPoly_eq_zero_of_not_bruhatLE`). -/
theorem coeff_zero_klPoly {y w : W} (hyw : cs.BruhatLE y w) : (klPoly cs y w).coeff 0 = 1 := by
  classical
  induction hn : ℓ w using Nat.strong_induction_on generalizing y w with
  | _ n ih =>
  subst hn
  rcases eq_or_ne w 1 with rfl | hw
  · rw [hyw.eq_of_length_le (by simp), klPoly_self, Polynomial.coeff_one_zero]
  obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hw
  have hi' := hi
  rw [CoxeterSystem.isLeftDescent_iff] at hi
  have hv : ℓ (s i * w) < ℓ (s i * (s i * w)) := by
    rw [CoxeterSystem.simple_mul_simple_cancel_left]; omega
  have h := klPoly_simple_mul cs hv y
  rw [CoxeterSystem.simple_mul_simple_cancel_left] at h
  rw [h, Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Finset.sum_eq_zero, sub_zero]
  · split_ifs with hy
    · have hy' : cs.IsLeftDescent y i := hy
      rw [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, add_zero]
      exact ih _ (by omega) ((cs.simple_mul_bruhatLE_simple_mul_iff hy' hi').mpr hyw) rfl
    · have hy' : ¬cs.IsLeftDescent y i := hy
      rw [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, zero_add]
      exact ih _ (by omega) (hyw.lifting_left hi' hy').1 rfl
  · intro z hz
    have := length_lt_of_mem_descentsBelow hv hz
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega),
      mul_zero]

/-- `P_{1,w}(0) = 1` ([KL] Lemma 2.6(i)). -/
theorem coeff_zero_klPoly_one_left (w : W) : (klPoly cs 1 w).coeff 0 = 1 :=
  coeff_zero_klPoly cs (cs.one_bruhatLE w)

/-- If `ℓ(w) ≤ 2`, then `P_{y,w} = 1` for all `y ≤ w`. -/
theorem klPoly_eq_one_of_length_le_two {y w : W} (hyw : cs.BruhatLE y w) (hw : ℓ w ≤ 2) :
    klPoly cs y w = 1 := by
  rcases eq_or_ne y w with rfl | hne
  · exact klPoly_self cs y
  have hdeg := two_mul_natDegree_klPoly_add_length_lt cs hyw hne
  rw [Polynomial.eq_C_of_natDegree_eq_zero (p := klPoly cs y w) (by omega),
    coeff_zero_klPoly cs hyw, map_one]

/-- If `y ≤ w` and `ℓ(w) = ℓ(y) + 1`, then `μ(y, w) = 1`. -/
theorem klMu_eq_one {y w : W} (hyw : cs.BruhatLE y w) (hl : ℓ w = ℓ y + 1) : klMu cs y w = 1 := by
  rw [klMu, muCoeff, hl, show ℓ y + 1 - ℓ y = 1 by omega, ite_eq_left odd_one]
  exact coeff_zero_klPoly cs hyw

/-- `μ(y, w) = 0` unless `y ≤ w`. -/
theorem klMu_eq_zero_of_not_bruhatLE {y w : W} (h : ¬cs.BruhatLE y w) : klMu cs y w = 0 := by
  simp [klMu, muCoeff, klPoly_eq_zero_of_not_bruhatLE cs h]

/-- The evaluation `v ↦ 1` of `P(q)` is `P(1)`. -/
theorem eval₂_one_aeval_T_two (P : Polynomial ℤ) :
    LaurentPolynomial.eval₂ (RingHom.id ℤ) 1
      (Polynomial.aeval (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) P) = P.eval 1 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.eval_add]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, map_mul, map_pow, eval₂_one_T_two, one_pow, mul_one,
      Polynomial.eval_monomial, one_pow, mul_one, eq_intCast (algebraMap ℤ (LaurentPolynomial ℤ)),
      map_intCast, Int.cast_id]

/-- **Specialization of the Kazhdan–Lusztig basis at `v = 1`**: the image of `C'_w` in the group
ring `ℤ[W]` is `Σ_{y ≤ w} P_{y,w}(1) y`. -/
theorem specializeOne_klBasis (w : W) :
    specializeOne cs (klBasis cs w) = ∑ y ∈ (cs.finite_setOf_bruhatLE w).toFinset,
      (klPoly cs y w).eval 1 • MonoidAlgebra.of ℤ W y := by
  rw [klBasis_eq_sum, specializeOne_smul, map_sum, LaurentPolynomial.eval₂_T]
  simp only [one_zpow, Units.val_one, one_smul]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [specializeOne_smul, specializeOne_T, eval₂_one_aeval_T_two]

/-- At `v = 1`, `C'_s` specializes to `1 + s`. -/
theorem specializeOne_klBasis_simple (i : B) :
    specializeOne cs (klBasis cs (s i)) = 1 + MonoidAlgebra.of ℤ W (s i) := by
  rw [klBasis_simple, klSimple, specializeOne_smul, map_add, specializeOne_T, map_one,
    LaurentPolynomial.eval₂_T]
  simp [add_comm]

end IwahoriHeckeAlgebra
