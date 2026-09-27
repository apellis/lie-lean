/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Change of rings and the specialization `q = 1` of Iwahori–Hecke algebras

For a ring homomorphism `f : R → S` the Iwahori–Hecke algebra `𝓗_q(W)` over `R` maps to
`𝓗_{f(q)}(W)` over `S` by `a T_w ↦ f(a) T_w` (`IwahoriHeckeAlgebra.map`). For `q = 1` the
Iwahori–Hecke algebra is the group algebra: `𝓗_1(W) ≃ R[W]`, `T_w ↦ w`
(`IwahoriHeckeAlgebra.equivMonoidAlgebra`). Combining the two, the generic Hecke algebra over
`ℤ[v, v⁻¹]` (with `q = v²`) specializes at `v = 1` to `ℤ[W]` (`specializeOne`).

## Main definitions

* `IwahoriHeckeAlgebra.map`: change of rings.
* `IwahoriHeckeAlgebra.equivMonoidAlgebra`: `𝓗_1(W) ≃ₐ[R] R[W]` ([HumC] §7.1 (check)).
* `IwahoriHeckeAlgebra.specializeOne`: `𝓗_{v²}(W) → R[W]` over `R[v, v⁻¹]`, `v ↦ 1`, `T_w ↦ w`.

## References

* [HumC] J. E. Humphreys, *Reflection groups and Coxeter groups*, CUP 1990, §7.1.
* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184.
-/

open Finsupp

namespace IwahoriHeckeAlgebra

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {R S : Type*} [CommRing R] [CommRing S] (q : R)

local prefix:100 "s " => cs.simple
local prefix:100 "ℓ " => cs.length

section map

variable (f : R →+* S) {q' : S}

/-- The additive map underlying `IwahoriHeckeAlgebra.map`. -/
noncomputable def mapAddHom (q' : S) : IwahoriHeckeAlgebra cs q →+ IwahoriHeckeAlgebra cs q' :=
  (toFinsupp cs q').symm.toAddEquiv.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom f.toAddMonoidHom).comp
      (toFinsupp cs q).toAddEquiv.toAddMonoidHom)

theorem mapAddHom_smul (q' : S) (a : R) (h : IwahoriHeckeAlgebra cs q) :
    mapAddHom cs q f q' (a • h) = f a • mapAddHom cs q f q' h := by
  apply (toFinsupp cs q').injective
  ext w
  simp [mapAddHom]

theorem mapAddHom_T (q' : S) (w : W) : mapAddHom cs q f q' (T cs q w) = T cs q' w := by
  apply (toFinsupp cs q').injective
  simp [mapAddHom, toFinsupp_T]

theorem mapAddHom_mul_T_simple (hq : f q = q') (h : IwahoriHeckeAlgebra cs q) (i : B) :
    mapAddHom cs q f q' (h * T cs q (s i)) =
      mapAddHom cs q f q' h * mapAddHom cs q f q' (T cs q (s i)) := by
  rw [mapAddHom_T]
  induction h using induction_on cs q with
  | T w =>
    rw [T_mul_T_simple, mapAddHom_T, T_mul_T_simple]
    split_ifs <;> simp [mapAddHom_smul, mapAddHom_T, hq]
  | add x y hx hy => rw [add_mul, map_add, hx, hy, map_add, add_mul]
  | smul a x hx => rw [smul_mul_assoc, mapAddHom_smul, hx, mapAddHom_smul, smul_mul_assoc]

/-- Change of rings: for `f : R →+* S` with `f q = q'`, the ring homomorphism
`𝓗_q(W) → 𝓗_{q'}(W)`, `a T_w ↦ f(a) T_w`. -/
noncomputable def map (hq : f q = q') : IwahoriHeckeAlgebra cs q →+* IwahoriHeckeAlgebra cs q' where
  __ := mapAddHom cs q f q'
  map_one' := by rw [← T_one, ← T_one]; exact mapAddHom_T cs q f q' 1
  map_mul' := map_mul_of_map_mul_T_simple cs q f (mapAddHom cs q f q')
    (mapAddHom_smul cs q f q')
    (by rw [← T_one, ← T_one]; exact mapAddHom_T cs q f q' 1)
    (mapAddHom_mul_T_simple cs q f hq)

@[simp]
theorem map_T (hq : f q = q') (w : W) : map cs q f hq (T cs q w) = T cs q' w :=
  mapAddHom_T cs q f q' w

theorem map_apply_smul (hq : f q = q') (a : R) (h : IwahoriHeckeAlgebra cs q) :
    map cs q f hq (a • h) = f a • map cs q f hq h := mapAddHom_smul cs q f q' a h

end map

section one

/-- For `q = 1`, `T_x T_y = T_{xy}` for all `x, y`. -/
theorem T_mul_T_of_eq_one (x y : W) : T cs (1 : R) x * T cs (1 : R) y = T cs (1 : R) (x * y) := by
  induction y using cs.induction_mul_simple with
  | one => simp
  | mul_simple y i _ ih =>
    have key : ∀ w : W, T cs (1 : R) w * T cs 1 (s i) = T cs 1 (w * s i) := fun w ↦ by
      rw [T_mul_T_simple]
      split_ifs <;> simp
    rw [← key, ← mul_assoc, ih, key, mul_assoc]

/-- The standard basis of `𝓗_1(W)` as a monoid homomorphism `W →* 𝓗_1(W)`. -/
noncomputable def THom : W →* IwahoriHeckeAlgebra cs (1 : R) where
  toFun := T cs 1
  map_one' := T_one cs 1
  map_mul' x y := (T_mul_T_of_eq_one cs x y).symm

theorem lift_THom_ofCoeff (x : W →₀ R) :
    MonoidAlgebra.lift R (IwahoriHeckeAlgebra cs (1 : R)) W (THom cs) (MonoidAlgebra.ofCoeff x) =
      (toFinsupp cs 1).symm x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [MonoidAlgebra.ofCoeff_add, map_add, hx, hy, map_add]
  | single w a =>
    rw [MonoidAlgebra.ofCoeff_single, MonoidAlgebra.lift_single, ← smul_single_one,
      _root_.map_smul]
    rfl

/-- The specialization `q = 1`: the Iwahori–Hecke algebra `𝓗_1(W)` is the group algebra
`R[W]`, with `T_w ↦ w` ([HumC] §7.1 (check)). -/
noncomputable def equivMonoidAlgebra : IwahoriHeckeAlgebra cs (1 : R) ≃ₐ[R] MonoidAlgebra R W :=
  (AlgEquiv.ofBijective (MonoidAlgebra.lift R (IwahoriHeckeAlgebra cs (1 : R)) W (THom cs)) <| by
    have h : ∀ x, MonoidAlgebra.lift R (IwahoriHeckeAlgebra cs (1 : R)) W (THom cs) x =
        (toFinsupp cs 1).symm x.coeff := fun x ↦ lift_THom_ofCoeff cs x.coeff
    refine ⟨fun x y hxy ↦ ?_, fun h' ↦ ⟨MonoidAlgebra.ofCoeff (toFinsupp cs 1 h'), ?_⟩⟩
    · rw [h, h] at hxy
      exact MonoidAlgebra.coeff_injective ((toFinsupp cs 1).symm.injective hxy)
    · rw [h]
      rfl).symm

@[simp]
theorem equivMonoidAlgebra_T (w : W) :
    equivMonoidAlgebra cs (T cs (1 : R) w) = MonoidAlgebra.of R W w := by
  rw [eq_comm, ← AlgEquiv.symm_apply_eq]
  simp [equivMonoidAlgebra, THom]

end one

section Laurent

open LaurentPolynomial

theorem eval₂_one_T_two : eval₂ (RingHom.id R) 1 (LaurentPolynomial.T 2 : R[T;T⁻¹]) = 1 := by
  simp [eval₂_T]

/-- The specialization `v = 1` of the generic Iwahori–Hecke algebra `𝓗_{v²}(W)` over
`R[v, v⁻¹]`: the ring homomorphism to the group algebra `R[W]` with `T_w ↦ w` and `v ↦ 1`
([KL] §1 (check)). -/
noncomputable def specializeOne :
    IwahoriHeckeAlgebra cs (LaurentPolynomial.T 2 : R[T;T⁻¹]) →+* MonoidAlgebra R W :=
  (equivMonoidAlgebra cs).toRingEquiv.toRingHom.comp
    (map cs _ (eval₂ (RingHom.id R) 1) eval₂_one_T_two)

@[simp]
theorem specializeOne_T (w : W) :
    specializeOne cs (IwahoriHeckeAlgebra.T cs (LaurentPolynomial.T 2 : R[T;T⁻¹]) w) =
      MonoidAlgebra.of R W w := by
  simp [specializeOne]

theorem specializeOne_smul (a : R[T;T⁻¹])
    (h : IwahoriHeckeAlgebra cs (LaurentPolynomial.T 2 : R[T;T⁻¹])) :
    specializeOne cs (a • h) = eval₂ (RingHom.id R) 1 a • specializeOne cs h := by
  simp [specializeOne, map_apply_smul]

theorem specializeOne_surjective : Function.Surjective (specializeOne (R := R) cs) := by
  intro x
  obtain ⟨y, rfl⟩ := (equivMonoidAlgebra cs).surjective x
  induction y using induction_on cs (1 : R) with
  | T w => exact ⟨IwahoriHeckeAlgebra.T cs _ w, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  | smul c x hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨C c • a, ?_⟩
    rw [specializeOne_smul, ha, map_smul]
    simp

end Laurent

end IwahoriHeckeAlgebra
