/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.Canonical
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Lusztig's lemma on systems of semilinear equations

Let `H` be a partially ordered set in which every interval `[h, h']` is finite, and let
`r_{h,h'} ∈ ℤ[v, v⁻¹]` (`h ≤ h'`) satisfy

* (a) `r_{h,h} = 1`,
* (b) `Σ_{h ≤ h'' ≤ h'} \bar r_{h,h''} r_{h'',h'} = δ_{h,h'}`,

where `f ↦ \bar f` is the ring involution `v ↦ v⁻¹`. Then there is a unique family
`p_{h,h'} ∈ ℤ[v, v⁻¹]` (`h ≤ h'`) such that

* (c) `p_{h,h} = 1`,
* (d) `p_{h,h'} ∈ v⁻¹ℤ[v⁻¹]` for `h < h'`,
* (e) `p_{h,h'} = Σ_{h ≤ h'' ≤ h'} \bar p_{h,h''} r_{h'',h'}`

([Lus] Lemma 24.2.1). Lusztig asks for finite open intervals `{h'' | h < h'' < h'}`, which is
equivalent to `LocallyFiniteOrder H`. Families are functions `H → H → ℤ[v, v⁻¹]`, of which
only the values at pairs `h ≤ h'` matter.

Unlike `Module.Basis.IsBarTriangular.existsUnique_canonical`, which produces canonical elements
of a free module and needs every set `{j | j < i}` to be finite, this form only needs finite
intervals: the coefficients `p_{h,h'}` of a "canonical element" may be nonzero for infinitely many
`h`.

## Main definitions

* `LaurentPolynomial.lusztigFamily r`: the family `p`, defined by recursion on the size of the
  interval `[h, h']`.

## Main results

* `LaurentPolynomial.IsLusztigFamily.existsUnique`: [Lus] Lemma 24.2.1.

## Proof

As in [Lus]: by induction on the interval, `q = Σ_{h ≤ h'' < h'} \bar p_{h,h''} r_{h'',h'}`
satisfies `\bar q = -q` by (b) and (e) on smaller intervals, so `q = p - \bar p` for a unique
`p ∈ v⁻¹ℤ[v⁻¹]` (`LaurentPolynomial.eq_negPart_sub_invert_negPart`), and this `p` is `p_{h,h'}`.
Lusztig inducts on the maximal length of a chain from `h` to `h'`; we induct on the cardinality
of `[h, h']`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §24.2.
-/

namespace LaurentPolynomial

variable {H : Type*} [PartialOrder H] [LocallyFiniteOrder H]

/-- Conditions (a), (b) of [Lus] Lemma 24.2.1 on `r_{h,h'}`, `h ≤ h'`. -/
structure IsLusztigMatrix (r : H → H → ℤ[T;T⁻¹]) : Prop where
  self (h : H) : r h h = 1
  inv [DecidableEq H] (h h' : H) (hh : h ≤ h') :
    ∑ x ∈ Finset.Icc h h', invert (r h x) * r x h' = if h = h' then 1 else 0

/-- Conditions (c), (d), (e) of [Lus] Lemma 24.2.1 on a family `p_{h,h'}`, `h ≤ h'`. -/
structure IsLusztigFamily (r p : H → H → ℤ[T;T⁻¹]) : Prop where
  self (h : H) : p h h = 1
  isNeg (h h' : H) (hh : h < h') : (p h h').IsNeg
  eq_sum (h h' : H) (hh : h ≤ h') : p h h' = ∑ x ∈ Finset.Icc h h', invert (p h x) * r x h'

open Classical in
/-- The family `p_{h,h'}` of [Lus] Lemma 24.2.1: `p_{h,h'} = 1` if `h' ≤ h`, and otherwise the
negative part of `Σ_{h ≤ x < h'} \bar p_{h,x} r_{x,h'}`. -/
noncomputable def lusztigFamily (r : H → H → ℤ[T;T⁻¹]) (h h' : H) : ℤ[T;T⁻¹] :=
  if h' ≤ h then 1 else
    negPart (∑ x ∈ (Finset.Ico h h').attach, invert (lusztigFamily r h x.1) * r x.1 h')
termination_by (Finset.Icc h h').card
decreasing_by
  obtain ⟨hx₁, hx₂⟩ := Finset.mem_Ico.1 x.2
  exact Finset.card_lt_card (Finset.Icc_ssubset_Icc_right (hx₁.trans hx₂.le) le_rfl hx₂)

theorem lusztigFamily_of_le (r : H → H → ℤ[T;T⁻¹]) {h h' : H} (hh : h' ≤ h) :
    lusztigFamily r h h' = 1 := by
  rw [lusztigFamily, ite_eq_left hh]

theorem lusztigFamily_of_not_le (r : H → H → ℤ[T;T⁻¹]) {h h' : H} (hh : ¬h' ≤ h) :
    lusztigFamily r h h' =
      negPart (∑ x ∈ Finset.Ico h h', invert (lusztigFamily r h x) * r x h') := by
  rw [lusztigFamily, ite_eq_right hh, Finset.sum_attach (Finset.Ico h h')
    (fun x ↦ invert (lusztigFamily r h x) * r x h')]

/-- Strong induction on the size of the interval `[h, h']`. -/
private theorem induction_Icc {h : H} {P : H → Prop}
    (ih : ∀ h', (∀ x, h ≤ x → x < h' → P x) → P h') (h' : H) : P h' := by
  suffices ∀ n h', (Finset.Icc h h').card = n → P h' from this _ h' rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rintro h' rfl
    exact ih h' fun x hx hx' ↦ IH _ (Finset.card_lt_card
      (Finset.Icc_ssubset_Icc_right (hx.trans hx'.le) le_rfl hx')) x rfl

/-- The key computation: if (e) holds on the intervals `[h, x]`, `x < h'`, then
`q = Σ_{h ≤ x < h'} \bar p_{h,x} r_{x,h'}` satisfies `\bar q = -q`. -/
theorem invert_sum_Ico {r p : H → H → ℤ[T;T⁻¹]} (hr : IsLusztigMatrix r) {h h' : H}
    (hp : ∀ x, h ≤ x → x < h' → p h x = ∑ y ∈ Finset.Icc h x, invert (p h y) * r y x) :
    invert (∑ x ∈ Finset.Ico h h', invert (p h x) * r x h') =
      -∑ x ∈ Finset.Ico h h', invert (p h x) * r x h' := by
  classical
  rw [eq_neg_iff_add_eq_zero, map_sum]
  simp only [map_mul, involutive_invert _]
  -- substitute (e) for `p_{h,x}` and exchange the order of summation
  have h2 : ∑ x ∈ Finset.Ico h h', p h x * invert (r x h') =
      ∑ y ∈ Finset.Ico h h', ∑ x ∈ Finset.Ico y h', invert (p h y) * r y x * invert (r x h') := by
    rw [Finset.sum_congr rfl fun x hx ↦ by
      rw [hp x (Finset.mem_Ico.1 hx).1 (Finset.mem_Ico.1 hx).2, Finset.sum_mul]]
    refine Finset.sum_comm' fun x y ↦ ?_
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hx, hx'⟩, hy, hyx⟩
      exact ⟨⟨hyx, hx'⟩, hy, hyx.trans_lt hx'⟩
    · rintro ⟨⟨hyx, hx'⟩, hy, -⟩
      exact ⟨⟨hy.trans hyx, hx'⟩, hy, hyx⟩
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun y hy ↦ ?_
  obtain ⟨hy, hy'⟩ := Finset.mem_Ico.1 hy
  have hδ := congrArg invert (hr.inv y h' hy'.le)
  rw [ite_eq_right hy'.ne, map_zero, map_sum, ← Finset.Ico_insert_right hy'.le,
    Finset.sum_insert Finset.right_notMem_Ico] at hδ
  simp only [map_mul, involutive_invert _, hr.self, mul_one] at hδ
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [← mul_add, add_comm, hδ, mul_zero]

theorem isLusztigFamily_lusztigFamily {r : H → H → ℤ[T;T⁻¹]} (hr : IsLusztigMatrix r) :
    IsLusztigFamily r (lusztigFamily r) := by
  classical
  have hlt : ∀ {h h' : H}, h < h' → lusztigFamily r h h' =
      negPart (∑ x ∈ Finset.Ico h h', invert (lusztigFamily r h x) * r x h') :=
    fun hh ↦ lusztigFamily_of_not_le r (not_le_of_gt hh)
  have he : ∀ h h', h ≤ h' → lusztigFamily r h h' =
      ∑ x ∈ Finset.Icc h h', invert (lusztigFamily r h x) * r x h' := by
    intro h
    refine induction_Icc (h := h) (P := fun h' ↦ h ≤ h' → lusztigFamily r h h' =
      ∑ x ∈ Finset.Icc h h', invert (lusztigFamily r h x) * r x h') (fun h' ih hh ↦ ?_)
    rw [← Finset.Ico_insert_right hh, Finset.sum_insert Finset.right_notMem_Ico, hr.self,
      mul_one]
    rcases hh.eq_or_lt with rfl | hh
    · rw [Finset.Ico_self, Finset.sum_empty, add_zero, lusztigFamily_of_le r le_rfl, map_one]
    · have hq := invert_sum_Ico hr fun x hx hx' ↦ ih x hx hx' hx
      have h' := eq_negPart_sub_invert_negPart hq
      rw [hlt hh]
      linear_combination -h'
  exact ⟨fun h ↦ lusztigFamily_of_le r le_rfl,
    fun h h' hh ↦ by rw [hlt hh]; exact isNeg_negPart _, he⟩

/-- Uniqueness in [Lus] Lemma 24.2.1. -/
theorem IsLusztigFamily.eq {r p p' : H → H → ℤ[T;T⁻¹]} (hr : IsLusztigMatrix r)
    (hp : IsLusztigFamily r p) (hp' : IsLusztigFamily r p') {h h' : H} (hh : h ≤ h') :
    p' h h' = p h h' := by
  revert hh
  refine induction_Icc (h := h) (P := fun h' ↦ h ≤ h' → p' h h' = p h h') (fun h' ih hh ↦ ?_) h'
  rcases hh.eq_or_lt with rfl | hh
  · rw [hp.self, hp'.self]
  · have hsplit : ∀ q : H → H → ℤ[T;T⁻¹], IsLusztigFamily r q →
        q h h' - invert (q h h') = ∑ x ∈ Finset.Ico h h', invert (q h x) * r x h' := by
      intro q hq
      classical
      have he := hq.eq_sum h h' hh.le
      rw [← Finset.Ico_insert_right hh.le, Finset.sum_insert Finset.right_notMem_Ico, hr.self,
        mul_one] at he
      linear_combination he
    have hs : p' h h' - invert (p' h h') = p h h' - invert (p h h') := by
      rw [hsplit p' hp', hsplit p hp]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      obtain ⟨hx, hx'⟩ := Finset.mem_Ico.1 hx
      rw [ih x hx hx' hx]
    have hd : invert (p' h h' - p h h') = p' h h' - p h h' := by
      rw [map_sub]
      linear_combination -hs
    exact sub_eq_zero.1 (((hp'.isNeg h h' hh).sub (hp.isNeg h h' hh)).eq_zero_of_invert_eq hd)

/-- **[Lus] Lemma 24.2.1.** If `r_{h,h'}` (`h ≤ h'`) satisfy (a) and (b), there is a family
`p_{h,h'}` (`h ≤ h'`) satisfying (c), (d) and (e), and it is unique: any two such families agree
at all pairs `h ≤ h'`. Lusztig works over a partially ordered set with finite open intervals,
which is `LocallyFiniteOrder H`. -/
theorem IsLusztigFamily.existsUnique {r : H → H → ℤ[T;T⁻¹]} (hr : IsLusztigMatrix r) :
    ∃ p, IsLusztigFamily r p ∧
      ∀ p', IsLusztigFamily r p' → ∀ h h', h ≤ h' → p' h h' = p h h' :=
  ⟨lusztigFamily r, isLusztigFamily_lusztigFamily hr,
    fun _ hp' _ _ hh ↦ IsLusztigFamily.eq hr (isLusztigFamily_lusztigFamily hr) hp' hh⟩

end LaurentPolynomial
