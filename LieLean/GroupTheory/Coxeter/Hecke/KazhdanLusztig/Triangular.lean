/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Bruhat
import LieLean.GroupTheory.Coxeter.Hecke.RPolynomial

/-!
# Triangularity of the bar involution with respect to the Bruhat order

Let `𝓗 = 𝓗_q(W)` be the Iwahori–Hecke algebra (normalization `(T_s - q)(T_s + 1) = 0`). We combine
the subword description of the support of the `R`-polynomials
(`IwahoriHeckeAlgebra.exists_sublist_of_rPoly_ne_zero`) with the subword property of the Bruhat
order (`CoxeterSystem.IsReduced.bruhatLE_iff`) to get: `R_{y,w} ≠ 0 → y ≤ w`. Over `A[v, v⁻¹]`
with `q = v²` this says that the bar involution is unitriangular in the standard basis, up to the
factor `q^{-ℓ(w)}`:
```
  T̄_w ∈ q^{-ℓ(w)} T_w + Σ_{y < w} A[v, v⁻¹] T_y.
```
We deduce the lemma behind the uniqueness of the Kazhdan–Lusztig basis ([KL] proof of Thm. 1.1,
[Soe] Behauptung 2.4, in the proof of Thm. 2.1, up to `v ↦ v⁻¹`): with `H_y = v^{-ℓ(y)} T_y`,
a bar-invariant element of `Σ_y v⁻¹ A[v⁻¹] H_y` is `0`.

## Main results

* `IwahoriHeckeAlgebra.bruhatLE_of_rPoly_ne_zero`: `R_{y,w} ≠ 0 → y ≤ w` ([KL] §2,
  [BB] Thm. 5.1.1(i)).
* `IwahoriHeckeAlgebra.toFinsupp_barL_T_apply`, `toFinsupp_barL_T_self`,
  `bruhatLE_of_toFinsupp_barL_T_ne_zero`, `barL_T_sub_mem_span`: triangularity of the bar
  involution.
* `IwahoriHeckeAlgebra.eq_zero_of_barL_eq_self`: a bar-invariant element whose normalized
  coefficients all lie in `v⁻¹ A[v⁻¹]` is zero.

## References

* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184, §1–2.
* [BB] A. Björner, F. Brenti, *Combinatorics of Coxeter groups*, GTM 231, Springer 2005, §5.1, §6.1.
* [Soe] W. Soergel, *Kazhdan–Lusztig-Polynome und eine Kombinatorik für Kipp-Moduln*,
  Represent. Theory **1** (1997), 37–68, §2.
-/

open Finsupp

namespace IwahoriHeckeAlgebra

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "ℓ " => cs.length

section General

variable {R : Type*} [CommRing R] {q : R} (hq : IsUnit q)

/-- If `R_{y,w} ≠ 0` then `y ≤ w` in the Bruhat order ([KL] §2, [BB] Thm. 5.1.1(i)). -/
theorem bruhatLE_of_rPoly_ne_zero {y w : W} (h : rPoly cs hq y w ≠ 0) : cs.BruhatLE y w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  exact hω.bruhatLE_iff.mpr (exists_sublist_of_rPoly_ne_zero cs hq hω h)

theorem rPoly_eq_zero_of_not_bruhatLE {y w : W} (h : ¬cs.BruhatLE y w) : rPoly cs hq y w = 0 :=
  not_not.mp fun h' ↦ h (bruhatLE_of_rPoly_ne_zero cs hq h')

/-- Every element is the sum of its coefficients times the standard basis. -/
theorem eq_sum_toFinsupp (h : IwahoriHeckeAlgebra cs q) :
    h = (toFinsupp cs q h).sum fun x a ↦ a • T cs q x := by
  apply (toFinsupp cs q).injective
  rw [map_finsuppSum]
  simp_rw [map_smul, toFinsupp_T, smul_single_one]
  exact (Finsupp.sum_single _).symm

end General

section Laurent

variable {A : Type*} [CommRing A]

local notation "𝓗" => IwahoriHeckeAlgebra cs (LaurentPolynomial.T 2 : LaurentPolynomial A)

theorem isUnit_T_two : IsUnit (LaurentPolynomial.T 2 : LaurentPolynomial A) :=
  isUnit_of_mul_eq_one' invertHom invertHom_T_two_mul_T_two

/-- The coefficients of `T̄_w`: `[T_y] T̄_w = ε_y ε_w v^{-2ℓ(w)} R_{y,w}` ([KL] (2.0.a)). -/
theorem toFinsupp_barL_T_apply (y w : W) :
    toFinsupp cs _ (barL cs (T cs _ w)) y =
      (-1) ^ (ℓ y + ℓ w) * LaurentPolynomial.T (-(2 * ℓ w : ℤ)) *
        rPoly cs (isUnit_T_two (A := A)) y w := by
  rw [barL, toFinsupp_bar_T_apply, invertHom_apply, LaurentPolynomial.invert_T,
    LaurentPolynomial.T_pow]
  congr 3
  ring

/-- If `T_y` occurs in `T̄_w`, then `y ≤ w` in the Bruhat order. -/
theorem bruhatLE_of_toFinsupp_barL_T_ne_zero {y w : W}
    (h : toFinsupp cs _ (barL cs (T cs (LaurentPolynomial.T 2 : LaurentPolynomial A) w)) y ≠ 0) :
    cs.BruhatLE y w := by
  refine bruhatLE_of_rPoly_ne_zero cs (isUnit_T_two (A := A)) fun h' ↦ h ?_
  rw [toFinsupp_barL_T_apply, h', mul_zero]

/-- The coefficient of `T_w` in `T̄_w` is `q^{-ℓ(w)} = v^{-2ℓ(w)}`. -/
theorem toFinsupp_barL_T_self (w : W) :
    toFinsupp cs _ (barL cs (T cs (LaurentPolynomial.T 2 : LaurentPolynomial A) w)) w =
      LaurentPolynomial.T (-(2 * ℓ w : ℤ)) := by
  rw [toFinsupp_barL_T_apply, rPoly_self, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul,
    mul_one]

/-- **Triangularity of the bar involution** ([KL] §2, [BB] §6.1, Thm. 5.1.1):
`T̄_w ∈ q^{-ℓ(w)} T_w + Σ_{y < w} A[v, v⁻¹] T_y`. -/
theorem barL_T_sub_mem_span (w : W) :
    barL cs (T cs (LaurentPolynomial.T 2 : LaurentPolynomial A) w) -
        (LaurentPolynomial.T (-(2 * ℓ w : ℤ)) : LaurentPolynomial A) • T cs _ w ∈
      Submodule.span (LaurentPolynomial A)
        (T cs (LaurentPolynomial.T 2 : LaurentPolynomial A) '' {y | cs.BruhatLE y w ∧ y ≠ w}) := by
  set h := barL cs (T cs (LaurentPolynomial.T 2 : LaurentPolynomial A) w) -
    (LaurentPolynomial.T (-(2 * ℓ w : ℤ)) : LaurentPolynomial A) • T cs _ w
  rw [eq_sum_toFinsupp cs h]
  refine Submodule.finsuppSum_mem _ _ _ _ fun y hy ↦ Submodule.smul_mem _ _ ?_
  refine Submodule.subset_span ⟨y, ⟨?_, ?_⟩, rfl⟩
  · by_contra hyw
    apply hy
    have hne : y ≠ w := fun e ↦ hyw (e ▸ cs.bruhatLE_refl w)
    simp only [h, map_sub, map_smul, toFinsupp_T, Finsupp.sub_apply, Finsupp.smul_apply,
      single_eq_of_ne hne, smul_zero, sub_zero]
    exact not_not.mp fun h' ↦ hyw (bruhatLE_of_toFinsupp_barL_T_ne_zero cs h')
  · rintro rfl
    apply hy
    simp [h, toFinsupp_T, toFinsupp_barL_T_self]

/-- The coefficients of the image of an element under the bar involution. -/
theorem toFinsupp_barL_apply (h : 𝓗) (y : W) :
    toFinsupp cs _ (barL cs h) y = (toFinsupp cs _ h).sum fun x a ↦
      LaurentPolynomial.invert a * toFinsupp cs _ (barL cs (T cs _ x)) y := by
  conv_lhs => rw [eq_sum_toFinsupp cs h]
  rw [map_finsuppSum, map_finsuppSum, Finsupp.sum_apply]
  simp_rw [barL_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- **The uniqueness lemma for the Kazhdan–Lusztig basis** ([KL] proof of Thm. 1.1, [Soe]
Behauptung 2.4, up to `v ↦ v⁻¹`): let `h ∈ 𝓗` be bar invariant and such that, for every `y`, the
coefficient of `H_y = v^{-ℓ(y)} T_y` in `h` lies in `v⁻¹ A[v⁻¹]` (i.e. the coefficient of `v^n` in
`[T_y] h` vanishes for `n + ℓ(y) ≥ 0`). Then `h = 0`. -/
theorem eq_zero_of_barL_eq_self {h : 𝓗} (hbar : barL cs h = h)
    (hneg : ∀ y (n : ℤ), 0 ≤ n + ℓ y → (toFinsupp cs _ h y).coeff n = 0) : h = 0 := by
  by_contra hne
  have hsupp : (toFinsupp cs _ h).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact fun e ↦ hne ((toFinsupp cs _).map_eq_zero_iff.mp e)
  obtain ⟨y, hy, hmax⟩ := (toFinsupp cs _ h).support.exists_max_image cs.length hsupp
  -- The coefficient of `T_y` in `h̄` is `v^{-2ℓ(y)} ā_y`.
  have key : toFinsupp cs _ (barL cs h) y = LaurentPolynomial.invert (toFinsupp cs _ h y) *
      LaurentPolynomial.T (-(2 * ℓ y : ℤ)) := by
    rw [toFinsupp_barL_apply, Finsupp.sum, Finset.sum_eq_single y, toFinsupp_barL_T_self]
    · intro x hx hxy
      have hle := hmax x hx
      rw [toFinsupp_barL_T_apply]
      by_cases hr : rPoly cs (isUnit_T_two (A := A)) y x = 0
      · rw [hr, mul_zero, mul_zero]
      exfalso
      have h1 := length_le_of_rPoly_ne_zero cs _ hr
      exact hxy (eq_of_rPoly_ne_zero_of_length_eq cs _ hr (by omega)).symm
    · intro hy'
      exact absurd hy hy'
  rw [hbar] at key
  set a := toFinsupp cs _ h y
  have ha : a ≠ 0 := Finsupp.mem_support_iff.mp hy
  apply ha
  ext n
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hn : 0 ≤ n + ℓ y
  · exact hneg y n hn
  · have := congrArg (fun f ↦ f.coeff n) key
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_mul_single_apply,
      LaurentPolynomial.invert_apply, mul_one] at this
    rw [this]
    exact hneg y _ (by omega)

end Laurent

end IwahoriHeckeAlgebra
