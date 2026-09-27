/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.Properties

/-!
# Kazhdan–Lusztig polynomials and inversion

The `R`-linear map `𝓗 → 𝓗`, `T_w ↦ T_{w⁻¹}`, is an anti-involution of the Iwahori–Hecke algebra
(`IwahoriHeckeAlgebra.antiInvolution`), and over `ℤ[v, v⁻¹]` it commutes with the bar involution.
It maps `C'_w` to `C'_{w⁻¹}`, so that `P_{y⁻¹, w⁻¹} = P_{y,w}` ([KL] §2 (check), [HumC] §7.11
(check)). Combined with the left-handed invariance `klPoly_simple_mul_left` this gives the
right-handed one: `P_{xs,w} = P_{x,w}` if `ws < w` ([KL] (2.3.g) (check)).

## Main definitions

* `IwahoriHeckeAlgebra.antiInvolution`: the anti-involution `T_w ↦ T_{w⁻¹}`.

## Main results

* `IwahoriHeckeAlgebra.antiInvolution_mul`, `antiInvolution_antiInvolution`,
  `antiInvolution_barL`.
* `IwahoriHeckeAlgebra.antiInvolution_klBasis`: `C'_w ↦ C'_{w⁻¹}`.
* `IwahoriHeckeAlgebra.klPoly_inv_inv`: `P_{y⁻¹, w⁻¹} = P_{y,w}`.
* `IwahoriHeckeAlgebra.klPoly_mul_simple_right`: `P_{xs,w} = P_{x,w}` if `ws < w`.

## References

* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184, §2.
* [HumC] J. E. Humphreys, *Reflection groups and Coxeter groups*, CUP 1990, §7.
-/

open Finsupp

namespace IwahoriHeckeAlgebra

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "ℓ " => cs.length

section General

variable {R : Type*} [CommRing R] (q : R)

/-- The anti-involution `T_w ↦ T_{w⁻¹}` of the Iwahori–Hecke algebra (as an `R`-linear
equivalence; it reverses products, `antiInvolution_mul`). -/
noncomputable def antiInvolution : IwahoriHeckeAlgebra cs q ≃ₗ[R] IwahoriHeckeAlgebra cs q :=
  (toFinsupp cs q).trans ((Finsupp.domLCongr (Equiv.inv W)).trans (toFinsupp cs q).symm)

theorem antiInvolution_T (w : W) : antiInvolution cs q (T cs q w) = T cs q w⁻¹ := by
  simp [antiInvolution, T]

theorem toFinsupp_antiInvolution_apply (h : IwahoriHeckeAlgebra cs q) (y : W) :
    toFinsupp cs q (antiInvolution cs q h) y = toFinsupp cs q h y⁻¹ := by
  simp [antiInvolution, Finsupp.domLCongr_apply, Finsupp.equivMapDomain_apply]

theorem antiInvolution_one : antiInvolution cs q 1 = 1 := by
  rw [← T_one, antiInvolution_T, inv_one]

theorem antiInvolution_antiInvolution (h : IwahoriHeckeAlgebra cs q) :
    antiInvolution cs q (antiInvolution cs q h) = h := by
  apply (toFinsupp cs q).injective
  ext y
  rw [toFinsupp_antiInvolution_apply, toFinsupp_antiInvolution_apply, inv_inv]

theorem antiInvolution_mul_T_simple (h : IwahoriHeckeAlgebra cs q) (i : B) :
    antiInvolution cs q (h * T cs q (s i)) = T cs q (s i) * antiInvolution cs q h := by
  induction h using induction_on cs q with
  | T w =>
    have e : (w * s i)⁻¹ = s i * w⁻¹ := by rw [mul_inv_rev, CoxeterSystem.inv_simple]
    have h1 : ℓ (s i * w⁻¹) = ℓ (w * s i) := by rw [← e, cs.length_inv]
    rw [T_mul_T_simple, antiInvolution_T, T_simple_mul_T, cs.length_inv, h1]
    split_ifs
    · rw [antiInvolution_T, e]
    · rw [map_add, map_smul, map_smul, antiInvolution_T, antiInvolution_T, e]
  | add x y hx hy => rw [add_mul, map_add, hx, hy, map_add, mul_add]
  | smul a x hx => rw [smul_mul_assoc, map_smul, hx, map_smul, mul_smul_comm]

/-- The map `T_w ↦ T_{w⁻¹}` reverses products. -/
theorem antiInvolution_mul (x y : IwahoriHeckeAlgebra cs q) :
    antiInvolution cs q (x * y) = antiInvolution cs q y * antiInvolution cs q x := by
  induction y using induction_on cs q generalizing x with
  | T w =>
    induction w using cs.induction_mul_simple generalizing x with
    | one => simp [antiInvolution_one]
    | mul_simple w i hlt ih =>
      have hlen : ℓ (s i * w⁻¹) = ℓ (s i) + ℓ w⁻¹ := by
        have e : s i * w⁻¹ = (w * s i)⁻¹ := by rw [mul_inv_rev, CoxeterSystem.inv_simple]
        rw [e, cs.length_inv, cs.length_inv, cs.length_simple]
        rcases cs.length_mul_simple w i with h | h <;> omega
      rw [← T_mul_T_simple_of_lt cs q hlt, ← mul_assoc, antiInvolution_mul_T_simple, ih,
        antiInvolution_mul_T_simple, ← mul_assoc]
  | add y z hy hz => rw [mul_add, map_add, hy, hz, map_add, add_mul]
  | smul a y hy => rw [mul_smul_comm, map_smul, hy, map_smul, smul_mul_assoc]

end General

section Laurent

local notation "𝓗" => IwahoriHeckeAlgebra cs (LaurentPolynomial.T 2 : LaurentPolynomial ℤ)

theorem antiInvolution_TInv (w : W) :
    antiInvolution cs _ (TInv cs (isUnit_T_two (A := ℤ)) w) =
      TInv cs (isUnit_T_two (A := ℤ)) w⁻¹ := by
  have h1 : antiInvolution cs _ (TInv cs (isUnit_T_two (A := ℤ)) w) *
      T cs (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) w⁻¹ = 1 := by
    rw [← antiInvolution_T, ← antiInvolution_mul, T_mul_TInv, antiInvolution_one]
  calc antiInvolution cs _ (TInv cs (isUnit_T_two (A := ℤ)) w)
      = antiInvolution cs _ (TInv cs (isUnit_T_two (A := ℤ)) w) *
          (T cs _ w⁻¹ * TInv cs (isUnit_T_two (A := ℤ)) w⁻¹) := by rw [T_mul_TInv, mul_one]
    _ = TInv cs (isUnit_T_two (A := ℤ)) w⁻¹ := by rw [← mul_assoc, h1, one_mul]

/-- The anti-involution `T_w ↦ T_{w⁻¹}` commutes with the bar involution. -/
theorem antiInvolution_barL (h : 𝓗) :
    antiInvolution cs _ (barL cs h) = barL cs (antiInvolution cs _ h) := by
  induction h using induction_on cs _ with
  | T w =>
    rw [antiInvolution_T, barL, bar_T, bar_T, inv_inv]
    rw [antiInvolution_TInv, inv_inv]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | smul a x hx => rw [barL_smul, map_smul, hx, map_smul, barL_smul]

/-- The anti-involution maps `C'_w` to `C'_{w⁻¹}` ([KL] §2 (check)); in particular
`P_{y⁻¹,w⁻¹} = P_{y,w}`. -/
theorem isKLElement_antiInvolution_klBasis (w : W) :
    IsKLElement cs w⁻¹ (antiInvolution cs _ (klBasis cs w)) fun y ↦ klPoly cs y⁻¹ w where
  barL_eq := by rw [← antiInvolution_barL, barL_klBasis]
  toFinsupp_apply y := by
    rw [toFinsupp_antiInvolution_apply, toFinsupp_klBasis_apply, cs.length_inv]
  self := by rw [inv_inv, klPoly_self]
  bruhatLE {y} hy := by
    rw [← CoxeterSystem.bruhatLE_inv_iff, inv_inv]
    exact bruhatLE_of_klPoly_ne_zero cs hy
  coeff_eq_zero {y} hy k hk := by
    refine coeff_klPoly_eq_zero cs (fun h ↦ hy (by rw [← h, inv_inv])) ?_
    rw [cs.length_inv] at hk
    rwa [cs.length_inv]

/-- The anti-involution `T_w ↦ T_{w⁻¹}` maps `C'_w` to `C'_{w⁻¹}` ([KL] §2 (check)). -/
theorem antiInvolution_klBasis (w : W) :
    antiInvolution cs _ (klBasis cs w) = klBasis cs w⁻¹ :=
  (isKLElement_antiInvolution_klBasis cs w).eq_klBasis.1

/-- `P_{y⁻¹, w⁻¹} = P_{y,w}` ([KL] §2 (check), [HumC] §7.11 (check)). -/
theorem klPoly_inv_inv (y w : W) : klPoly cs y⁻¹ w⁻¹ = klPoly cs y w := by
  have := congrFun (isKLElement_antiInvolution_klBasis cs w).eq_klBasis.2 y⁻¹
  rw [inv_inv] at this
  exact this.symm

/-- **Right-handed invariance** ([KL] (2.3.g) (check)): if `ws < w`, then `P_{xs,w} = P_{x,w}`
for all `x`. -/
theorem klPoly_mul_simple_right {i : B} {w : W} (hw : ℓ (w * s i) < ℓ w) (x : W) :
    klPoly cs (x * s i) w = klPoly cs x w := by
  have hw' : ℓ (s i * w⁻¹) < ℓ w⁻¹ := by
    rwa [← CoxeterSystem.inv_simple cs i, ← mul_inv_rev, cs.length_inv, cs.length_inv]
  rw [← klPoly_inv_inv, mul_inv_rev, CoxeterSystem.inv_simple,
    klPoly_simple_mul_left cs hw', klPoly_inv_inv]

end Laurent

end IwahoriHeckeAlgebra
