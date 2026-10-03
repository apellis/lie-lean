/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.Bar
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The `R`-polynomials of a Coxeter system

Let `𝓗 = 𝓗_q(W)` be the Iwahori–Hecke algebra with `q` a unit (normalization
`T_s² = (q - 1) T_s + q`). Following [KL] (2.0.a) and [HumC] §7.4–7.5, the `R`-polynomials
`R_{y,w}` are defined by the expansion of the inverse of `T_{w⁻¹}` (that is, of the image `T̄_w` of
`T_w` under the bar involution) in the standard basis:
```
  T_{w⁻¹}⁻¹ = ε_w q_w⁻¹ Σ_y ε_y R_{y,w} T_y,        ε_w = (-1)^{ℓ(w)},  q_w = q^{ℓ(w)}.
```
Thus `R_{y,w} = ε_y ε_w q^{ℓ(w)} · [T_y] T_{w⁻¹}⁻¹` (`IwahoriHeckeAlgebra.rPoly`). We prove:

* the recursion ([BB] Thm. 5.1.1(iii), [KL] (2.0.b), [BB] Thm. 5.1.1(iii)): if
  `ℓ(ws) > ℓ(w)`, then
  `R_{y,ws} = R_{ys,w}` if `ℓ(ys) < ℓ(y)`, and `R_{y,ws} = (q - 1) R_{y,w} + q R_{ys,w}` otherwise
  (`rPoly_mul_simple`);
* `R_{y,1} = δ_{y,1}`, `R_{w,w} = 1` (`rPoly_one_right`, `rPoly_self`);
* triangularity without the Bruhat order: if `R_{y,w} ≠ 0` then for every reduced word `ω` of `w`,
  `y` is the product of a subword of `ω` (`exists_sublist_of_rPoly_ne_zero`); in particular
  `ℓ(y) ≤ ℓ(w)`, with equality only for `y = w`. By the subword property ([BB] Thm. 2.2.2) the
  first statement says `y ≤ w` in the Bruhat order;
* `R_{y,w}` is the value at `q` of a polynomial with integer coefficients of degree at most
  `ℓ(w) - ℓ(y)` (`exists_rPoly_eq_aeval_natDegree_le`);
* for the bar involution attached to `σ` with `σ(q) q = 1`:
  `T̄_w = Σ_y ε_y ε_w σ(q)^{ℓ(w)} R_{y,w} T_y` (`toFinsupp_bar_T_apply`).

## Main definitions

* `IwahoriHeckeAlgebra.invCoeff`: the coefficient `[T_y] T_{w⁻¹}⁻¹`.
* `IwahoriHeckeAlgebra.rPoly`: the `R`-polynomial `R_{y,w}` evaluated at `q`.

## Main results

* `IwahoriHeckeAlgebra.rPoly_mul_simple`: the recursion for `R`-polynomials.
* `IwahoriHeckeAlgebra.rPoly_self`, `IwahoriHeckeAlgebra.exists_sublist_of_rPoly_ne_zero`:
  `R_{w,w} = 1`, and `R_{y,w} ≠ 0` only if `y` is a subword of a reduced word of `w`.
* `IwahoriHeckeAlgebra.exists_rPoly_eq_aeval`: `R_{y,w}` is a polynomial in `q`.

## References

* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184, §2.
* [HumC] J. E. Humphreys, *Reflection groups and Coxeter groups*, CUP 1990, §7.4–7.5.
* [BB] A. Björner, F. Brenti, *Combinatorics of Coxeter groups*, GTM 231, §5.1, §6.1.
-/

open Finsupp

namespace IwahoriHeckeAlgebra

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {R : Type*} [CommRing R] (q : R)

local prefix:100 "s " => cs.simple
local prefix:100 "ℓ " => cs.length

section rightOp

theorem toFinsupp_mul_T_simple (h : IwahoriHeckeAlgebra cs q) (i : B) :
    toFinsupp cs q (h * T cs q (s i)) = rightOp cs q i (toFinsupp cs q h) := by
  rw [toFinsupp_mul_T, ← rightOp_single_one cs q, lmul_apply_rightOp, lmul_apply_single_one]

/-- The coefficients of `h T_s` in terms of those of `h`. -/
theorem rightOp_apply (i : B) (x : W →₀ R) (y : W) :
    rightOp cs q i x y = if ℓ (y * s i) < ℓ y then x (y * s i) + (q - 1) * x y
      else q * x (y * s i) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' =>
    rw [map_add, Finsupp.add_apply, hx, hx']
    split_ifs <;> simp only [Finsupp.add_apply] <;> ring
  | single w a =>
    have hne : ℓ (w * s i) ≠ ℓ w := cs.length_mul_simple_ne w i
    rw [← smul_single_one, map_smul, rightOp_single]
    rcases eq_or_ne y w with rfl | hyw
    · have h1 : y * s i ≠ y := fun h ↦ hne (by rw [h])
      by_cases hy : ℓ y < ℓ (y * s i)
      · simp [hy, h1, not_lt.mpr hy.le]
      · simp [hy, h1, lt_of_le_of_ne (not_lt.mp hy) hne, mul_comm]
    rcases eq_or_ne y (w * s i) with rfl | hyws
    · have h2 : w * s i * s i = w := CoxeterSystem.simple_mul_simple_cancel_right cs i
      by_cases hw : ℓ w < ℓ (w * s i)
      · simp [hw, h2, hyw.symm]
      · simp [hw, h2, hyw, mul_comm]
    · have h3 : y * s i ≠ w := fun h ↦
        hyws (by rw [← h, CoxeterSystem.simple_mul_simple_cancel_right])
      split_ifs <;> simp [hyw.symm, hyws.symm, h3.symm]

end rightOp

variable {q} (hq : IsUnit q)

/-- The coefficient `[T_y] T_{w⁻¹}⁻¹` of `T_y` in `T_{w⁻¹}⁻¹` (which is the image of `T_w` under
the bar involution). -/
noncomputable def invCoeff (y w : W) : R := toFinsupp cs q (TInv cs hq w⁻¹) y

/-- The `R`-polynomial `R_{y,w}` (evaluated at `q`), defined by
`T_{w⁻¹}⁻¹ = ε_w q_w⁻¹ Σ_y ε_y R_{y,w} T_y` ([KL] (2.0.a), [BB] §6.1). -/
noncomputable def rPoly (y w : W) : R := (-1) ^ (ℓ y + ℓ w) * q ^ ℓ w * invCoeff cs hq y w

theorem invCoeff_eq_rPoly (y w : W) :
    invCoeff cs hq y w = (-1) ^ (ℓ y + ℓ w) * hq.unit⁻¹.1 ^ ℓ w * rPoly cs hq y w := by
  have e : hq.unit⁻¹.1 * q = 1 := hq.val_inv_mul
  have h1 : ((-1 : R) ^ (ℓ y + ℓ w)) * (-1) ^ (ℓ y + ℓ w) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have h2 : hq.unit⁻¹.1 ^ ℓ w * q ^ ℓ w = 1 := by rw [← mul_pow, e, one_pow]
  rw [rPoly]
  linear_combination (-invCoeff cs hq y w * (hq.unit⁻¹.1 ^ ℓ w * q ^ ℓ w)) * h1 +
    (-invCoeff cs hq y w) * h2

/-- The expansion `T_{w⁻¹}⁻¹ = Σ_y ε_y ε_w q^{-ℓ(w)} R_{y,w} T_y`, coefficientwise
([KL] (2.0.a), [BB] §6.1). -/
theorem toFinsupp_TInv_inv_apply (y w : W) :
    toFinsupp cs q (TInv cs hq w⁻¹) y =
      (-1) ^ (ℓ y + ℓ w) * hq.unit⁻¹.1 ^ ℓ w * rPoly cs hq y w :=
  invCoeff_eq_rPoly cs hq y w

theorem invCoeff_one_right [DecidableEq W] (y : W) :
    invCoeff cs hq y 1 = if y = 1 then 1 else 0 := by
  rw [invCoeff, inv_one, TInv_one, ← T_one cs q, toFinsupp_T]
  rcases eq_or_ne y 1 with rfl | h
  · simp
  · simp [h]

/-- The recursion for the coefficients of `T_{w⁻¹}⁻¹`. -/
theorem invCoeff_mul_simple {w : W} {i : B} (hlt : ℓ w < ℓ (w * s i)) (y : W) :
    invCoeff cs hq y (w * s i) = if ℓ (y * s i) < ℓ y then hq.unit⁻¹.1 * invCoeff cs hq (y * s i) w
      else invCoeff cs hq (y * s i) w - (1 - hq.unit⁻¹.1) * invCoeff cs hq y w := by
  have e : hq.unit⁻¹.1 * q = 1 := hq.val_inv_mul
  have hlen : ℓ (s i * w⁻¹) = ℓ (s i) + ℓ w⁻¹ := by
    have : s i * w⁻¹ = (w * s i)⁻¹ := by rw [mul_inv_rev, CoxeterSystem.inv_simple]
    rw [this, cs.length_inv, cs.length_inv, cs.length_simple]
    rcases cs.length_mul_simple w i with h | h <;> omega
  rw [invCoeff, mul_inv_rev, CoxeterSystem.inv_simple, TInv_mul cs hq hlen, TInv_simple]
  simp only [mul_sub, mul_smul_comm, mul_one, map_sub, map_smul, toFinsupp_mul_T_simple,
    Finsupp.sub_apply, Finsupp.smul_apply, rightOp_apply, smul_eq_mul, invCoeff]
  split_ifs
  · linear_combination (toFinsupp cs q (TInv cs hq w⁻¹) y) * e
  · linear_combination (toFinsupp cs q (TInv cs hq w⁻¹) (y * s i)) * e

/-- The recursion for `R`-polynomials ([BB] Thm. 5.1.1(iii), [KL] (2.0.b),
[BB] Thm. 5.1.1(iii)): if
`ℓ(ws) > ℓ(w)`, then `R_{y,ws} = R_{ys,w}` if `ℓ(ys) < ℓ(y)` and
`R_{y,ws} = (q - 1) R_{y,w} + q R_{ys,w}` otherwise. -/
theorem rPoly_mul_simple {w : W} {i : B} (hlt : ℓ w < ℓ (w * s i)) (y : W) :
    rPoly cs hq y (w * s i) = if ℓ (y * s i) < ℓ y then rPoly cs hq (y * s i) w
      else (q - 1) * rPoly cs hq y w + q * rPoly cs hq (y * s i) w := by
  have e : hq.unit⁻¹.1 * q = 1 := hq.val_inv_mul
  have hw : ℓ (w * s i) = ℓ w + 1 := by
    rcases cs.length_mul_simple w i with h | h <;> omega
  simp only [rPoly, invCoeff_mul_simple cs hq hlt, hw]
  split_ifs with hy
  · have hy' : ℓ y = ℓ (y * s i) + 1 := by
      rcases cs.length_mul_simple y i with h | h <;> omega
    rw [hy']
    linear_combination ((-1) ^ (ℓ (y * s i) + ℓ w) * q ^ ℓ w * invCoeff cs hq (y * s i) w) * e
  · have hy' : ℓ (y * s i) = ℓ y + 1 := by
      rcases cs.length_mul_simple y i with h | h <;> omega
    rw [hy']
    linear_combination (-(-1) ^ (ℓ y + ℓ w) * q ^ ℓ w * invCoeff cs hq y w) * e

/-- The recursion for `R`-polynomials along a right descent ([BB] Thm. 5.1.1(iii)): if
`ℓ(ws) < ℓ(w)`, then `R_{y,w} = R_{ys,ws}` if `ℓ(ys) < ℓ(y)` and
`R_{y,w} = (q - 1) R_{y,ws} + q R_{ys,ws}` otherwise. -/
theorem rPoly_of_length_mul_simple_lt {w : W} {i : B} (hlt : ℓ (w * s i) < ℓ w) (y : W) :
    rPoly cs hq y w = if ℓ (y * s i) < ℓ y then rPoly cs hq (y * s i) (w * s i)
      else (q - 1) * rPoly cs hq y (w * s i) + q * rPoly cs hq (y * s i) (w * s i) := by
  have := rPoly_mul_simple cs hq (w := w * s i) (i := i)
    (by rwa [CoxeterSystem.simple_mul_simple_cancel_right]) y
  rwa [CoxeterSystem.simple_mul_simple_cancel_right] at this

theorem rPoly_one_right [DecidableEq W] (y : W) : rPoly cs hq y 1 = if y = 1 then 1 else 0 := by
  rw [rPoly, invCoeff_one_right]
  split_ifs with h
  · simp [h]
  · simp

theorem invCoeff_self (w : W) : invCoeff cs hq w w = hq.unit⁻¹.1 ^ ℓ w := by
  classical
  induction w using cs.induction_mul_simple with
  | one => simp [invCoeff_one_right]
  | mul_simple w i hlt ih =>
    have hw : ℓ (w * s i) = ℓ w + 1 := by
      rcases cs.length_mul_simple w i with h | h <;> omega
    rw [invCoeff_mul_simple cs hq hlt, CoxeterSystem.simple_mul_simple_cancel_right,
      ite_eq_left (by omega), ih, hw, pow_succ, mul_comm]

/-- `R_{w,w} = 1` ([BB] Thm. 5.1.1(ii)). -/
theorem rPoly_self (w : W) : rPoly cs hq w w = 1 := by
  have e : hq.unit⁻¹.1 * q = 1 := hq.val_inv_mul
  rw [rPoly, invCoeff_self, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, ← mul_pow,
    mul_comm, e, one_pow]

section Triangular

/-- The span of the `T_{π ω'}` for the subwords `ω'` of `ω`. -/
noncomputable def subwordSpan (ω : List B) : Submodule R (IwahoriHeckeAlgebra cs q) :=
  Submodule.span R ((fun ω' ↦ T cs q (cs.wordProd ω')) '' {ω' | ω'.Sublist ω})

variable {cs} in
theorem subwordSpan_mono {ω ω' : List B} (h : ω'.Sublist ω) :
    subwordSpan cs (q := q) ω' ≤ subwordSpan cs ω :=
  Submodule.span_mono (Set.image_mono fun _ h' ↦ List.Sublist.trans h' h)

theorem T_simple_mul_mem_subwordSpan (i : B) {ω : List B} {h : IwahoriHeckeAlgebra cs q}
    (hh : h ∈ subwordSpan cs ω) : T cs q (s i) * h ∈ subwordSpan cs (i :: ω) := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω', hω', rfl⟩ := hx
    have h1 : T cs q (cs.wordProd ω') ∈ subwordSpan cs (q := q) (i :: ω) :=
      Submodule.subset_span ⟨ω', List.Sublist.cons i hω', rfl⟩
    have h2 : T cs q (s i * cs.wordProd ω') ∈ subwordSpan cs (q := q) (i :: ω) :=
      Submodule.subset_span ⟨i :: ω', List.Sublist.cons_cons i hω', by simp [cs.wordProd_cons]⟩
    rw [T_simple_mul_T]
    split_ifs
    · exact h2
    · exact add_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem prod_TInv_mem_subwordSpan (ω : List B) :
    (ω.map fun i ↦ TInv cs hq (s i)).prod ∈ subwordSpan cs ω := by
  induction ω with
  | nil => exact Submodule.subset_span ⟨[], List.Sublist.slnil, by simp⟩
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, TInv_simple, sub_mul, smul_mul_assoc, smul_mul_assoc,
      one_mul]
    exact sub_mem (Submodule.smul_mem _ _ (T_simple_mul_mem_subwordSpan cs i ih))
      (Submodule.smul_mem _ _ (subwordSpan_mono (List.sublist_cons_self i ω) ih))

/-- For a reduced word `ω`, `T_{(π ω)⁻¹}⁻¹ = T_{s₁}⁻¹ ⋯ T_{sₖ}⁻¹`. -/
theorem TInv_wordProd_inv {ω : List B} (hω : cs.IsReduced ω) :
    TInv cs hq (cs.wordProd ω)⁻¹ = (ω.map fun i ↦ TInv cs hq (s i)).prod := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hlen : ℓ ((cs.wordProd ω)⁻¹ * s i) = ℓ (cs.wordProd ω)⁻¹ + ℓ (s i) := by
      have := hω.eq
      rw [cs.wordProd_cons, List.length_cons] at this
      have e1 : (cs.wordProd ω)⁻¹ * s i = (s i * cs.wordProd ω)⁻¹ := by
        rw [mul_inv_rev, CoxeterSystem.inv_simple]
      rw [e1, cs.length_inv, cs.length_inv, this, hω'.eq, cs.length_simple]
    rw [cs.wordProd_cons, mul_inv_rev, CoxeterSystem.inv_simple, ← CoxeterSystem.inv_simple cs i,
      TInv_mul cs hq (by rwa [CoxeterSystem.inv_simple]), CoxeterSystem.inv_simple, ih hω',
      List.map_cons, List.prod_cons]

/-- Triangularity of the bar involution without the Bruhat order: if `[T_y] T_{w⁻¹}⁻¹ ≠ 0`,
then `y` is the product of a subword of any reduced word `ω` of `w`. -/
theorem exists_sublist_of_invCoeff_ne_zero {ω : List B} (hω : cs.IsReduced ω) {y : W}
    (hy : invCoeff cs hq y (cs.wordProd ω) ≠ 0) : ∃ ω', ω'.Sublist ω ∧ cs.wordProd ω' = y := by
  have hmem := prod_TInv_mem_subwordSpan cs hq ω
  rw [← TInv_wordProd_inv cs hq hω] at hmem
  have key : ∀ h ∈ subwordSpan cs (q := q) ω, toFinsupp cs q h ∈
      Finsupp.supported R R (cs.wordProd '' {ω' | ω'.Sublist ω}) := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ω', hω', rfl⟩ := hx
      rw [toFinsupp_T]
      exact Finsupp.single_mem_supported R _ ⟨ω', hω', rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have := (Finsupp.mem_supported R _).mp (key _ hmem) (Finsupp.mem_support_iff.mpr hy)
  obtain ⟨ω', hω', rfl⟩ := this
  exact ⟨ω', hω', rfl⟩

/-- If `R_{y,w} ≠ 0`, then `y` is the product of a subword of any reduced word of `w` (by the
subword property, [BB] Thm. 2.2.2, this means `y ≤ w` in the Bruhat order; cf. [BB]
Thm. 5.1.1(i)). -/
theorem exists_sublist_of_rPoly_ne_zero {ω : List B} (hω : cs.IsReduced ω) {y : W}
    (hy : rPoly cs hq y (cs.wordProd ω) ≠ 0) : ∃ ω', ω'.Sublist ω ∧ cs.wordProd ω' = y := by
  refine exists_sublist_of_invCoeff_ne_zero cs hq hω fun h ↦ hy ?_
  rw [rPoly, h, mul_zero]

theorem length_le_of_rPoly_ne_zero {y w : W} (hy : rPoly cs hq y w ≠ 0) : ℓ y ≤ ℓ w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  obtain ⟨ω', hω', rfl⟩ := exists_sublist_of_rPoly_ne_zero cs hq hω hy
  exact (cs.length_wordProd_le ω').trans (hω'.length_le.trans hω.eq.ge)

theorem eq_of_rPoly_ne_zero_of_length_eq {y w : W} (hy : rPoly cs hq y w ≠ 0)
    (hl : ℓ y = ℓ w) : y = w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  obtain ⟨ω', hω', rfl⟩ := exists_sublist_of_rPoly_ne_zero cs hq hω hy
  have h1 := cs.length_wordProd_le ω'
  have h2 := hω'.length_le
  rw [hω'.eq_of_length (by rw [hω.eq] at hl; omega)]

end Triangular

/-- `R_{y,w}` is the value at `q` of a polynomial with integer coefficients of degree at most
`ℓ(w) - ℓ(y)`, which is `0` if `ℓ(y) > ℓ(w)` ([BB] Thm. 5.1.1, Prop. 5.1.3; the polynomial
depends only on
`(W, S)`, since it is produced by the recursion `rPoly_mul_simple`). -/
theorem exists_rPoly_eq_aeval_natDegree_le (y w : W) :
    ∃ p : Polynomial ℤ, rPoly cs hq y w = Polynomial.aeval q p ∧
      p.natDegree ≤ ℓ w - ℓ y ∧ (ℓ w < ℓ y → p = 0) := by
  classical
  induction w using cs.induction_mul_simple generalizing y with
  | one =>
    refine ⟨if y = 1 then 1 else 0, by rw [rPoly_one_right]; split_ifs <;> simp, ?_, ?_⟩
    · split_ifs <;> simp
    · intro h
      have hy : y ≠ 1 := by rintro rfl; simp at h
      simp [hy]
  | mul_simple w i hlt ih =>
    have hw : ℓ (w * s i) = ℓ w + 1 := by
      rcases cs.length_mul_simple w i with h | h <;> omega
    rw [rPoly_mul_simple cs hq hlt]
    obtain ⟨p, hp, hpd, hp0⟩ := ih y
    obtain ⟨p', hp', hpd', hp0'⟩ := ih (y * s i)
    split_ifs with hy
    · have hy' : ℓ y = ℓ (y * s i) + 1 := by
        rcases cs.length_mul_simple y i with h | h <;> omega
      exact ⟨p', hp', by omega, fun h ↦ hp0' (by omega)⟩
    · have hy' : ℓ (y * s i) = ℓ y + 1 := by
        rcases cs.length_mul_simple y i with h | h <;> omega
      refine ⟨(Polynomial.X - 1) * p + Polynomial.X * p', by simp [hp, hp'], ?_, ?_⟩
      · by_cases hyw : ℓ w < ℓ y
        · simp [hp0 hyw, hp0' (by omega)]
        have h1 : ((Polynomial.X : Polynomial ℤ) - 1).natDegree ≤ 1 :=
          (Polynomial.natDegree_sub_le _ _).trans (by simp)
        have h2 := Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℤ) - 1) (q := p)
        have h3 := Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℤ)) (q := p')
        have h4 := Polynomial.natDegree_add_le ((Polynomial.X - 1) * p) (Polynomial.X * p')
        have h5 : (Polynomial.X : Polynomial ℤ).natDegree ≤ 1 := Polynomial.natDegree_X_le
        omega
      · intro h
        simp [hp0 (by omega), hp0' (by omega)]

/-- `R_{y,w}` is the value at `q` of a polynomial with integer coefficients
([BB] Thm. 5.1.1). -/
theorem exists_rPoly_eq_aeval (y w : W) :
    ∃ p : Polynomial ℤ, rPoly cs hq y w = Polynomial.aeval q p :=
  (exists_rPoly_eq_aeval_natDegree_le cs hq y w).imp fun _ h ↦ h.1

section Bar

variable (σ : R →+* R) (hσ : σ q * q = 1)

/-- The expansion of `T̄_w` in the standard basis in terms of `R`-polynomials:
`T̄_w = Σ_y ε_y ε_w σ(q)^{ℓ(w)} R_{y,w} T_y` ([KL] (2.0.a), [BB] §6.1). -/
theorem toFinsupp_bar_T_apply (y w : W) :
    toFinsupp cs q (bar cs σ hσ (T cs q w)) y = (-1) ^ (ℓ y + ℓ w) * σ q ^ ℓ w *
      rPoly cs (isUnit_of_mul_eq_one' σ hσ) y w := by
  rw [bar_T, toFinsupp_TInv_inv_apply, val_inv_eq σ hσ]

end Bar

end IwahoriHeckeAlgebra
