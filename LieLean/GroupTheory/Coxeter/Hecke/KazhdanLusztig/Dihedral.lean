/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.Properties

/-!
# Kazhdan–Lusztig polynomials of dihedral groups

Let `(W, S)` be a Coxeter system of rank at most two, i.e. `W` is a (finite or infinite) dihedral
group, or of rank `≤ 1`. We show:

* **The Bruhat order of a dihedral group** ([BB] §2.2 (check), [HumC] §5.9 (check)):
  `y ≤ w` if and only if `ℓ(y) < ℓ(w)` or `y = w` (`CoxeterSystem.bruhatLE_iff_of_card_le_two`).
* **Kazhdan–Lusztig polynomials of dihedral groups** ([BB] Ch. 5, Exercises (check)):
  `P_{y,w} = 1` for all `y ≤ w` (`IwahoriHeckeAlgebra.klPoly_eq_one_of_card_le_two`),
  i.e. `C'_w = v^{-ℓ(w)} Σ_{y ≤ w} T_y` (`IwahoriHeckeAlgebra.klBasis_eq_sum_of_card_le_two`).

## Proof

The key combinatorial fact is that in rank `≤ 2` an element is determined by its length and the
information that a given simple reflection `t` is not a left descent
(`CoxeterSystem.eq_of_length_eq_of_not_isLeftDescent`): if `x ≠ 1` has no left descent `t`, its
left descents are the other simple reflection `s`, and `s x` has no left descent `s`. Hence two
elements of the same positive length with a common left descent agree
(`CoxeterSystem.eq_of_length_eq_of_isLeftDescent`). The description of the Bruhat order follows by
induction on `ℓ(w)` (for `ℓ(y) = ℓ(w) - 1`, with `t` a left descent of `w`: either `t` is a left
descent of `y` and `t y ≤ t w`, or `y = t w`). For the Kazhdan–Lusztig polynomials we use the
recursion `P_{x,sv} = q^{1-c} P_{sx,v} + q^c P_{x,v} - Σ_{z} μ(z,v) q^{(ℓ(sv)-ℓ(z))/2} P_{x,z}`
([KL] (2.2.c)): by induction all `P_{a,u}` with `ℓ(u) < ℓ(w)` are `1` on Bruhat intervals, so
`μ(z,v) ≠ 0` only for `ℓ(z) = ℓ(v) - 1`, and there is at most one such `z` with left descent `s`;
a case analysis on `ℓ(x)` gives `P_{x,w} = 1`. The arguments were written by us.

## Main results

* `CoxeterSystem.bruhatLE_iff_of_card_le_two`: the Bruhat order in rank `≤ 2`.
* `IwahoriHeckeAlgebra.klPoly_eq_one_of_card_le_two`: `P_{y,w} = 1` for `y ≤ w` in rank `≤ 2`.
* `IwahoriHeckeAlgebra.klBasis_eq_sum_of_card_le_two`: `C'_w = v^{-ℓ(w)} Σ_{y ≤ w} T_y`.

## References

* [KL] D. Kazhdan, G. Lusztig, *Representations of Coxeter groups and Hecke algebras*,
  Invent. Math. **53** (1979), 165–184.
* [BB] A. Björner, F. Brenti, *Combinatorics of Coxeter groups*, GTM 231, Springer 2005.
* [HumC] J. E. Humphreys, *Reflection groups and Coxeter groups*, CUP 1990.
-/

open Polynomial

/-- If a finite type has at most two elements, two elements different from a third one agree. -/
theorem eq_of_ne_of_ne_of_card_le_two {B : Type*} [Finite B] (hB : Nat.card B ≤ 2) {i j k : B}
    (hij : i ≠ j) (hik : i ≠ k) : j = k := by
  classical
  by_contra hjk
  have := Fintype.ofFinite B
  have h3 : ({i, j, k} : Finset B).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hij, hik]), Finset.card_pair hjk]
  have := Finset.card_le_univ ({i, j, k} : Finset B)
  rw [h3, ← Nat.card_eq_fintype_card] at this
  omega

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} {cs : CoxeterSystem M W}

local prefix:100 "s " => cs.simple
local prefix:100 "ℓ " => cs.length

variable [Finite B]

/-- In rank `≤ 2`, two elements of the same length that do not have `t` as a left descent are
equal. -/
theorem eq_of_length_eq_of_not_isLeftDescent (hB : Nat.card B ≤ 2) {x y : W} {t : B}
    (hl : ℓ x = ℓ y) (hx : ¬cs.IsLeftDescent x t) (hy : ¬cs.IsLeftDescent y t) : x = y := by
  induction hn : ℓ x generalizing x y t with
  | zero =>
    rw [hn] at hl
    rw [cs.length_eq_zero_iff.mp hn, cs.length_eq_zero_iff.mp hl.symm]
  | succ n ih =>
    have hx1 : x ≠ 1 := by rintro rfl; simp at hn
    have hy1 : y ≠ 1 := by rintro rfl; rw [hn] at hl; simp at hl
    obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hx1
    obtain ⟨i', hi'⟩ := cs.exists_leftDescent_of_ne_one hy1
    have hti : t ≠ i := fun h ↦ hx (h ▸ hi)
    have hti' : t ≠ i' := fun h ↦ hy (h ▸ hi')
    obtain rfl := eq_of_ne_of_ne_of_card_le_two hB hti hti'
    have e1 := cs.isLeftDescent_iff.mp hi
    have e2 := cs.isLeftDescent_iff.mp hi'
    have key := ih (x := s i * x) (y := s i * y) (t := i) (by omega)
      (by rw [IsLeftDescent, simple_mul_simple_cancel_left]; omega)
      (by rw [IsLeftDescent, simple_mul_simple_cancel_left]; omega) (by omega)
    simpa using congrArg (s i * ·) key

/-- In rank `≤ 2`, two elements of the same length with a common left descent are equal. -/
theorem eq_of_length_eq_of_isLeftDescent (hB : Nat.card B ≤ 2) {x y : W} {i : B}
    (hl : ℓ x = ℓ y) (hx : cs.IsLeftDescent x i) (hy : cs.IsLeftDescent y i) : x = y := by
  have e1 := cs.isLeftDescent_iff.mp hx
  have e2 := cs.isLeftDescent_iff.mp hy
  have key := eq_of_length_eq_of_not_isLeftDescent (cs := cs) hB (x := s i * x) (y := s i * y)
    (t := i)
    (by omega) (by rw [IsLeftDescent, simple_mul_simple_cancel_left]; omega)
    (by rw [IsLeftDescent, simple_mul_simple_cancel_left]; omega)
  simpa using congrArg (s i * ·) key

/-- In rank `≤ 2`, if `ℓ(y) < ℓ(w)` then `y ≤ w` in the Bruhat order. -/
theorem bruhatLE_of_length_lt (hB : Nat.card B ≤ 2) {y w : W} (h : ℓ y < ℓ w) :
    cs.BruhatLE y w := by
  induction hn : ℓ w using Nat.strong_induction_on generalizing y w with
  | _ n ih =>
  have hw1 : w ≠ 1 := by rintro rfl; simp at h
  obtain ⟨t, ht⟩ := cs.exists_leftDescent_of_ne_one hw1
  have ht' := cs.isLeftDescent_iff.mp ht
  rcases Nat.lt_or_ge (ℓ y + 1) (ℓ w) with h1 | h1
  · exact (ih _ (by omega) (y := y) (w := s t * w) (by omega) rfl).trans (cs.simple_mul_bruhatLE ht)
  · by_cases hy : cs.IsLeftDescent y t
    · have hy' := cs.isLeftDescent_iff.mp hy
      exact (cs.simple_mul_bruhatLE_simple_mul_iff hy ht).mp
        (ih _ (by omega) (y := s t * y) (w := s t * w) (by omega) rfl)
    · have hw' : ¬cs.IsLeftDescent (s t * w) t := by
        rw [IsLeftDescent, simple_mul_simple_cancel_left]; omega
      rw [eq_of_length_eq_of_not_isLeftDescent hB (by omega) hy hw']
      exact cs.simple_mul_bruhatLE ht

/-- **The Bruhat order of a dihedral group** ([BB] §2.2 (check), [HumC] §5.9 (check)): in a
Coxeter system of rank `≤ 2`, `y ≤ w` if and only if `ℓ(y) < ℓ(w)` or `y = w`. -/
theorem bruhatLE_iff_of_card_le_two (hB : Nat.card B ≤ 2) {y w : W} :
    cs.BruhatLE y w ↔ ℓ y < ℓ w ∨ y = w :=
  ⟨fun h ↦ h.eq_or_length_lt.symm,
    fun h ↦ h.elim (bruhatLE_of_length_lt hB) fun h ↦ h ▸ cs.bruhatLE_refl _⟩

end CoxeterSystem

namespace IwahoriHeckeAlgebra

open CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "ℓ " => cs.length

variable [Finite B]

/-- **Kazhdan–Lusztig polynomials of dihedral groups** ([BB] Ch. 5, Exercises (check)):
in a Coxeter system of rank `≤ 2`, `P_{y,w} = 1` for all `y ≤ w`. -/
theorem klPoly_eq_one_of_card_le_two (hB : Nat.card B ≤ 2) {y w : W} (h : cs.BruhatLE y w) :
    klPoly cs y w = 1 := by
  classical
  suffices key : ∀ n, ∀ w : W, ℓ w = n → ∀ x, cs.BruhatLE x w → klPoly cs x w = 1 from
    key _ w rfl y h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hn x hxw
  have char : ∀ a u : W, cs.BruhatLE a u ↔ ℓ a < ℓ u ∨ a = u := fun _ _ ↦
    bruhatLE_iff_of_card_le_two hB
  have IH : ∀ u a : W, ℓ u < n → klPoly cs a u = if cs.BruhatLE a u then 1 else 0 :=
    fun u a hu ↦ by
      split_ifs with h'
      · exact ih _ hu u rfl a h'
      · exact klPoly_eq_zero_of_not_bruhatLE cs h'
  rcases eq_or_ne x w with rfl | hxw'
  · exact klPoly_self cs x
  have hlx : ℓ x < ℓ w := hxw.eq_or_length_lt.resolve_left hxw'
  have hw1 : w ≠ 1 := by rintro rfl; simp at hlx
  obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hw1
  set v := s i * w with hv_def
  have hvl : ℓ v + 1 = ℓ w := cs.isLeftDescent_iff.mp hi
  have hw : w = s i * v := by rw [hv_def, simple_mul_simple_cancel_left]
  have hv : ℓ v < ℓ (s i * v) := by rw [← hw]; omega
  have hvi : ¬cs.IsLeftDescent v i := by rw [IsLeftDescent, ← hw]; omega
  rw [hw, klPoly_simple_mul cs hv x, ← hw]
  -- the `μ`-terms
  have hterm : ∀ z ∈ descentsBelow cs i v,
      C (klMu cs z v) * X ^ ((ℓ w - ℓ z) / 2) * klPoly cs x z =
        if ℓ z + 1 = ℓ v ∧ cs.BruhatLE x z then X else 0 := by
    intro z hz
    have hzv := (mem_descentsBelow.mp hz).1
    have hzl := length_lt_of_mem_descentsBelow hv hz
    rw [klMu, muCoeff, IH v z (by omega), ite_eq_left hzv, IH z x (by omega)]
    by_cases hzl' : ℓ z + 1 = ℓ v
    · have hd : ℓ v - ℓ z = 1 := by omega
      have h2 : (ℓ w - ℓ z) / 2 = 1 := by omega
      by_cases hxz : cs.BruhatLE x z <;> simp [hd, h2, hzl', hxz]
    · have hmu : (if Odd (ℓ v - ℓ z) then (1 : ℤ[X]).coeff ((ℓ v - ℓ z) / 2) else 0) = 0 := by
        split_ifs with hodd
        · rw [coeff_one]
          exact ite_eq_right (by have := Nat.odd_iff.mp hodd; omega)
        · rfl
      rw [hmu, map_zero, zero_mul, zero_mul,
        ite_eq_right (show ¬(ℓ z + 1 = ℓ v ∧ cs.BruhatLE x z) from fun h' ↦ hzl' h'.1)]
  have hsum : (∑ z ∈ descentsBelow cs i v,
      C (klMu cs z v) * X ^ ((ℓ w - ℓ z) / 2) * klPoly cs x z) =
        if ∃ z ∈ descentsBelow cs i v, ℓ z + 1 = ℓ v ∧ cs.BruhatLE x z then X else 0 := by
    rw [Finset.sum_congr rfl hterm]
    split_ifs with hex
    · obtain ⟨z₀, hz₀, hz₀'⟩ := hex
      rw [Finset.sum_eq_single_of_mem z₀ hz₀, ite_eq_left hz₀']
      intro z hz hne
      refine ite_eq_right fun hc ↦ hne ?_
      exact eq_of_length_eq_of_isLeftDescent hB (by omega) (mem_descentsBelow.mp hz).2
        (mem_descentsBelow.mp hz₀).2
    · exact Finset.sum_eq_zero fun z hz ↦ ite_eq_right fun hc ↦ hex ⟨z, hz, hc⟩
  -- existence of the element `z₀ = t v` of length `ℓ(v) - 1` with left descent `s`
  have hz₀ : 2 ≤ ℓ v → ∃ z ∈ descentsBelow cs i v, ℓ z + 1 = ℓ v := by
    intro h2
    have hv1 : v ≠ 1 := by
      intro h'
      rw [h', cs.length_one] at h2
      omega
    obtain ⟨t, ht⟩ := cs.exists_leftDescent_of_ne_one hv1
    have ht' := cs.isLeftDescent_iff.mp ht
    have hti : t ≠ i := fun h' ↦ hvi (h' ▸ ht)
    refine ⟨s t * v, mem_descentsBelow.mpr ⟨cs.simple_mul_bruhatLE ht, ?_⟩, ht'⟩
    by_contra hzi
    have hz1 : s t * v ≠ 1 := by
      intro h'
      rw [h', cs.length_one] at ht'
      omega
    obtain ⟨r, hr⟩ := cs.exists_leftDescent_of_ne_one hz1
    have htr : t ≠ r := by
      rintro rfl
      have := cs.isLeftDescent_iff.mp hr
      rw [simple_mul_simple_cancel_left] at this
      omega
    exact hzi (eq_of_ne_of_ne_of_card_le_two hB htr hti ▸ hr)
  have hDl : ∀ z ∈ descentsBelow cs i v, ℓ z < ℓ v := fun z hz ↦
    length_lt_of_mem_descentsBelow hv hz
  rw [hsum]
  by_cases hsx : ℓ (s i * x) < ℓ x
  · have hsxl : ℓ (s i * x) + 1 = ℓ x := by
      rcases cs.length_simple_mul x i with h' | h' <;> omega
    rw [ite_eq_left hsx, IH v (s i * x) (by omega),
      ite_eq_left ((char _ _).mpr (Or.inl (by omega))), IH v x (by omega)]
    rcases Nat.lt_or_ge (ℓ x) (ℓ v) with hxv | hxv
    · rw [ite_eq_left ((char _ _).mpr (Or.inl hxv)), ite_eq_left, mul_one, add_sub_cancel_right]
      rcases Nat.lt_or_ge (ℓ x + 1) (ℓ v) with hxv' | hxv'
      · obtain ⟨z, hz, hzl⟩ := hz₀ (by omega)
        exact ⟨z, hz, hzl, (char _ _).mpr (Or.inl (by omega))⟩
      · exact ⟨x, mem_descentsBelow.mpr ⟨(char _ _).mpr (Or.inl hxv), hsx⟩, by omega,
          cs.bruhatLE_refl x⟩
    · have hxv' : ¬cs.BruhatLE x v := fun h' ↦ by
        rcases (char _ _).mp h' with h'' | rfl
        · omega
        · exact hvi hsx
      rw [ite_eq_right hxv', mul_zero, add_zero,
        ite_eq_right fun ⟨z, hz, _, hxz⟩ ↦ by have := hxz.length_le; have := hDl z hz; omega,
        sub_zero]
  · have hsxl : ℓ (s i * x) = ℓ x + 1 := by
      rcases cs.length_simple_mul x i with h' | h' <;> omega
    rw [ite_eq_right hsx, IH v (s i * x) (by omega), IH v x (by omega)]
    rcases Nat.lt_or_ge (ℓ x + 1) (ℓ v) with hxv | hxv
    · rw [ite_eq_left ((char _ _).mpr (Or.inl (by omega))),
        ite_eq_left ((char _ _).mpr (Or.inl (by omega))), mul_one, ite_eq_left, add_sub_cancel_left]
      obtain ⟨z, hz, hzl⟩ := hz₀ (by omega)
      exact ⟨z, hz, hzl, (char _ _).mpr (Or.inl (by omega))⟩
    · have hsxv : ¬cs.BruhatLE (s i * x) v := fun h' ↦ by
        rcases (char _ _).mp h' with h'' | h''
        · omega
        · apply hxw'
          rw [hw, ← h'', simple_mul_simple_cancel_left]
      rw [ite_eq_right hsxv, mul_zero, zero_add]
      rcases Nat.lt_or_ge (ℓ x) (ℓ v) with hxv' | hxv'
      · rw [ite_eq_left ((char _ _).mpr (Or.inl hxv')), ite_eq_right, sub_zero]
        rintro ⟨z, hz, hzl, hxz⟩
        have hxz' := hxz.eq_of_length_le (by omega)
        apply hsx
        rw [hxz']
        exact (mem_descentsBelow.mp hz).2
      · have hxv'' : x = v := eq_of_length_eq_of_not_isLeftDescent hB (by omega)
          (by rw [IsLeftDescent]; omega) hvi
        rw [ite_eq_left ((char _ _).mpr (Or.inr hxv'')),
          ite_eq_right fun ⟨z, hz, _, hxz⟩ ↦ by have := hxz.length_le; have := hDl z hz; omega,
          sub_zero]

/-- In a Coxeter system of rank `≤ 2`, `C'_w = v^{-ℓ(w)} Σ_{y ≤ w} T_y`. -/
theorem klBasis_eq_sum_of_card_le_two (hB : Nat.card B ≤ 2) (w : W) :
    klBasis cs w = (LaurentPolynomial.T (-(ℓ w : ℤ)) : LaurentPolynomial ℤ) •
      ∑ y ∈ (cs.finite_setOf_bruhatLE w).toFinset,
        T cs (LaurentPolynomial.T 2 : LaurentPolynomial ℤ) y := by
  rw [klBasis_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  rw [klPoly_eq_one_of_card_le_two cs hB (by simpa using hy), map_one, one_smul]

end IwahoriHeckeAlgebra
