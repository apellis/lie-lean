/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.Involutions
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.Properties

/-!
# Kazhdan–Lusztig polynomials and inversion

The `R`-linear map `𝓗 → 𝓗`, `T_w ↦ T_{w⁻¹}`, is an anti-involution of the Iwahori–Hecke algebra
(`IwahoriHeckeAlgebra.antiInvolutionSelf`, `Hecke/Involutions.lean`); over `ℤ[v, v⁻¹]` it
commutes with the bar involution. It maps `C'_w` to `C'_{w⁻¹}`, so that
`P_{y⁻¹, w⁻¹} = P_{y,w}` ([BB] Ch. 5, Exercise 12).
Combined with the left-handed invariance `klPoly_simple_mul_left` this gives the right-handed
one: `P_{xs,w} = P_{x,w}` if `ws < w` ([BB] Prop. 5.1.8; the mirror image of [KL] (2.3.g)).

## Main results

* `IwahoriHeckeAlgebra.antiInvolutionSelf_barL`: `T_w ↦ T_{w⁻¹}` commutes with the bar involution.
* `IwahoriHeckeAlgebra.antiInvolutionSelf_klBasis`: `C'_w ↦ C'_{w⁻¹}`.
* `IwahoriHeckeAlgebra.klPoly_inv_inv`: `P_{y⁻¹, w⁻¹} = P_{y,w}`.
* `IwahoriHeckeAlgebra.klPoly_mul_simple_right`: `P_{xs,w} = P_{x,w}` if `ws < w`.

## References

* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184, §2.
* [BB] A. Björner, F. Brenti, *Combinatorics of Coxeter groups*, GTM 231, Springer 2005, Ch. 5.
-/

open Finsupp

namespace IwahoriHeckeAlgebra

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "ℓ " => cs.length

section Laurent

local notation "𝓗" => IwahoriHeckeAlgebra cs (LaurentPolynomial.T 2 : LaurentPolynomial ℤ)

theorem antiInvolutionSelf_TInv (w : W) :
    antiInvolutionSelf cs _ (TInv cs (isUnit_T_two (A := ℤ)) w) =
      TInv cs (isUnit_T_two (A := ℤ)) w⁻¹ := by
  have h1 : antiInvolutionSelf cs _ (TInv cs (isUnit_T_two (A := ℤ)) w) *
      T cs (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) w⁻¹ = 1 := by
    rw [← antiInvolutionSelf_T, ← antiInvolutionSelf_mul, T_mul_TInv, antiInvolutionSelf_one]
  calc antiInvolutionSelf cs _ (TInv cs (isUnit_T_two (A := ℤ)) w)
      = antiInvolutionSelf cs _ (TInv cs (isUnit_T_two (A := ℤ)) w) *
          (T cs _ w⁻¹ * TInv cs (isUnit_T_two (A := ℤ)) w⁻¹) := by rw [T_mul_TInv, mul_one]
    _ = TInv cs (isUnit_T_two (A := ℤ)) w⁻¹ := by rw [← mul_assoc, h1, one_mul]

/-- The anti-involution `T_w ↦ T_{w⁻¹}` commutes with the bar involution. -/
theorem antiInvolutionSelf_barL (h : 𝓗) :
    antiInvolutionSelf cs _ (barL cs h) = barL cs (antiInvolutionSelf cs _ h) := by
  induction h using induction_on cs _ with
  | T w =>
    rw [antiInvolutionSelf_T, barL, bar_T, bar_T, inv_inv]
    rw [antiInvolutionSelf_TInv, inv_inv]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | smul a x hx => rw [barL_smul, map_smul, hx, map_smul, barL_smul]

/-- The anti-involution maps `C'_w` to `C'_{w⁻¹}`; in particular `P_{y⁻¹,w⁻¹} = P_{y,w}`
([BB] Ch. 5, Exercise 12). -/
theorem isKLElement_antiInvolution_klBasis (w : W) :
    IsKLElement cs w⁻¹ (antiInvolutionSelf cs _ (klBasis cs w)) fun y ↦ klPoly cs y⁻¹ w where
  barL_eq := by rw [← antiInvolutionSelf_barL, barL_klBasis]
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

/-- The anti-involution `T_w ↦ T_{w⁻¹}` maps `C'_w` to `C'_{w⁻¹}`. -/
theorem antiInvolutionSelf_klBasis (w : W) :
    antiInvolutionSelf cs _ (klBasis cs w) = klBasis cs w⁻¹ :=
  (isKLElement_antiInvolution_klBasis cs w).eq_klBasis.1

/-- `P_{y⁻¹, w⁻¹} = P_{y,w}` ([BB] Ch. 5, Exercise 12). -/
theorem klPoly_inv_inv (y w : W) : klPoly cs y⁻¹ w⁻¹ = klPoly cs y w := by
  have := congrFun (isKLElement_antiInvolution_klBasis cs w).eq_klBasis.2 y⁻¹
  rw [inv_inv] at this
  exact this.symm

/-- **Right-handed invariance** ([BB] Prop. 5.1.8; the mirror image of [KL] (2.3.g)): if
`ws < w`, then `P_{xs,w} = P_{x,w}` for all `x`. -/
theorem klPoly_mul_simple_right {i : B} {w : W} (hw : ℓ (w * s i) < ℓ w) (x : W) :
    klPoly cs (x * s i) w = klPoly cs x w := by
  have hw' : ℓ (s i * w⁻¹) < ℓ w⁻¹ := by
    rwa [← CoxeterSystem.inv_simple cs i, ← mul_inv_rev, cs.length_inv, cs.length_inv]
  rw [← klPoly_inv_inv, mul_inv_rev, CoxeterSystem.inv_simple,
    klPoly_simple_mul_left cs hw', klPoly_inv_inv]

end Laurent

end IwahoriHeckeAlgebra
