/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.GabberKac.MapCoeffs
import LieLean.Algebra.QuantumGroup.LusztigF.Form

/-!
# Lusztig's form on `'f` under change of coefficients

For a ring homomorphism `φ : K → L` of fields, the coefficient map `'f_K → 'f_L`
(`FreeAlgebra.mapCoeffs φ`, `θᵢ ↦ θᵢ`) intertwines the twists `σᵢ`, the skew derivations `rᵢ`
and Lusztig's form ([Lus] 1.2.3, 1.2.13) at the parameters `v` and `φ v`.

## Main results

* `LusztigF.twist_mapCoeffs`, `LusztigF.rDeriv_mapCoeffs`.
* `LusztigF.form_mapCoeffs`: `(φ_* x, φ_* y)_{φ v} = φ (x, y)_v`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.2.3, 1.2.13.
-/

noncomputable section

open FreeAlgebra

namespace LusztigF

variable {K L I : Type*} [Field K] [Field L] [DecidableEq I] (D : LusztigCartanDatum I) (v : K)
  (φ : K →+* L)

omit [DecidableEq I] in
theorem twist_mapCoeffs (i : I) (x : LusztigF K I) :
    twist D (φ v) i (mapCoeffs φ x) = mapCoeffs φ (twist D v i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 j => simp [mapCoeffs_smul, map_zpow₀]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem rDeriv_mapCoeffs (i : I) (x : LusztigF K I) :
    rDeriv D (φ v) i (mapCoeffs φ x) = mapCoeffs φ (rDeriv D v i x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 j => simp only [mapCoeffs_ι, rDeriv_θ]; split_ifs <;> simp
  | mul a b ha hb =>
    simp only [map_mul, rDeriv_mul, ha, hb, twist_mapCoeffs, map_add]
  | add a b ha hb => simp only [map_add, ha, hb]

omit [DecidableEq I] in
theorem thetaNorm_map (i : I) : φ (thetaNorm D v i) = thetaNorm D (φ v) i := by
  simp [thetaNorm, map_inv₀]

theorem formEnd_mapCoeffs (x y : LusztigF K I) :
    formEnd D (φ v) (mapCoeffs φ x) (mapCoeffs φ y) = mapCoeffs φ (formEnd D v x y) := by
  induction x using FreeAlgebra.induction generalizing y with
  | grade0 c => simp [Module.algebraMap_end_apply, mapCoeffs_smul]
  | grade1 i =>
    simp [formEnd, mapCoeffs_smul, rDeriv_mapCoeffs, thetaNorm_map]
  | mul a b ha hb => simp only [map_mul, Module.End.mul_apply, hb, ha]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

/-- Lusztig's form commutes with change of coefficients. -/
theorem form_mapCoeffs (x y : LusztigF K I) :
    form D (φ v) (mapCoeffs φ x) (mapCoeffs φ y) = φ (form D v x y) := by
  rw [form_apply, form_apply, formEnd_mapCoeffs]
  exact algebraMapInv_mapCoeffs φ _

end LusztigF
