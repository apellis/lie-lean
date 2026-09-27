/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Bruhat
import Mathlib.Data.Fintype.Lattice

/-!
# The longest element of a finite Coxeter group

Let `cs : CoxeterSystem M W` be a Coxeter system with `W` finite. We define the longest element
`w₀` as an element of maximal length and prove its standard properties ([BB] §2.3,
[HumC] §1.8, §5.6): every reflection is a right inversion of `w₀`, hence
`ℓ(w₀ u) = ℓ(u w₀) = ℓ(w₀) - ℓ(u)` for all `u`; `w₀` is an involution; it is the unique element
having every simple reflection as a right descent (equivalently, the unique element of maximal
length); `ℓ(w₀)` is the number of reflections; every element is `≤ w₀` in the Bruhat order;
`u ↦ w₀ u` reverses the Bruhat order; conjugation by `w₀` permutes the simple reflections.

## Main definitions

* `CoxeterSystem.longestElement`: the longest element `w₀`.

## Main results

* `CoxeterSystem.length_mul_of_forall_isRightInversion`: if every reflection is a right inversion
  of `w`, then `ℓ(w u) = ℓ(w) - ℓ(u)` (no finiteness needed).
* `CoxeterSystem.length_longestElement_mul`, `CoxeterSystem.length_mul_longestElement`.
* `CoxeterSystem.longestElement_mul_self`, `CoxeterSystem.inv_longestElement`.
* `CoxeterSystem.eq_longestElement_iff_forall_isRightDescent`,
  `CoxeterSystem.eq_longestElement_of_forall_length_le`: uniqueness.
* `CoxeterSystem.length_longestElement_eq_ncard`: `ℓ(w₀) = |T|`.
* `CoxeterSystem.bruhatLE_longestElement`: `w ≤ w₀`.
* `CoxeterSystem.longestElement_mul_bruhatLE_longestElement_mul_iff`: `w₀ w ≤ w₀ u ↔ u ≤ w`.
* `CoxeterSystem.exists_longestElement_mul_simple_mul_eq`: `w₀ sᵢ w₀` is a simple reflection.

## Implementation notes

The formula for `ℓ(w₀ u)` is obtained by counting inversions: by the cocycle identity for the
parity `η`, the right inversions of `w₀ u` are the reflections that are not right inversions of
`u`. This argument was reconstructed by us; [BB] and [HumC] argue via the Bruhat order and the
root system, respectively.

## References

* [BB] A. Björner, F. Brenti, *Combinatorics of Coxeter groups*, GTM 231, Springer 2005, §2.3.
* [HumC] J. E. Humphreys, *Reflection groups and Coxeter groups*, CUP 1990, §1.8, §5.6.
-/

open List

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd
local prefix:100 "ℓ " => cs.length

private theorem zmod_two_eq_zero_of_ne_one {x : ZMod 2} (h : x ≠ 1) : x = 0 := by
  fin_cases x
  · rfl
  · exact absurd rfl h

variable {cs} in
/-- If every reflection is a right inversion of `w`, then the right inversions of `w u` are the
reflections that are not right inversions of `u`. -/
theorem isRightInversion_mul_iff_of_forall {w : W}
    (hw : ∀ t, cs.IsReflection t → cs.IsRightInversion w t) (u t : W) :
    cs.IsRightInversion (w * u) t ↔ cs.IsReflection t ∧ ¬cs.IsRightInversion u t := by
  classical
  by_cases ht : cs.IsReflection t
  · have h1 := (cs.isRightInversion_iff_inversionParity_eq_one).mp (hw _ (ht.conj u))
    rw [cs.isRightInversion_iff_inversionParity_eq_one,
      cs.isRightInversion_iff_inversionParity_eq_one, inversionParity_mul, h1]
    simp only [ht, true_and]
    constructor
    · intro h h'
      rw [h'] at h
      exact absurd h (by decide)
    · intro h
      rw [zmod_two_eq_zero_of_ne_one h, zero_add]
  · exact ⟨fun h ↦ absurd h.1 ht, fun h ↦ absurd h.1 ht⟩

variable {cs} in
/-- If every reflection is a right inversion of `w`, then `ℓ(w u) = ℓ(w) - ℓ(u)` for all `u`. -/
theorem length_mul_of_forall_isRightInversion {w : W}
    (hw : ∀ t, cs.IsReflection t → cs.IsRightInversion w t) (u : W) :
    ℓ (w * u) = ℓ w - ℓ u := by
  have hT : {t | cs.IsRightInversion w t} = {t | cs.IsReflection t} :=
    Set.ext fun t ↦ ⟨fun h ↦ h.1, hw t⟩
  have hwu : {t | cs.IsRightInversion (w * u) t} =
      {t | cs.IsReflection t} \ {t | cs.IsRightInversion u t} :=
    Set.ext fun t ↦ isRightInversion_mul_iff_of_forall hw u t
  have hsub : {t | cs.IsRightInversion u t} ⊆ {t | cs.IsReflection t} := fun t ht ↦ ht.1
  rw [← ncard_setOf_isRightInversion, hwu, Set.ncard_sdiff hsub
    (cs.finite_setOf_isRightInversion u), ← hT, ncard_setOf_isRightInversion,
    ncard_setOf_isRightInversion]

section Finite

variable [Finite W]

private theorem exists_max_length : ∃ w₀ : W, ∀ w, ℓ w ≤ ℓ w₀ :=
  Finite.exists_max cs.length

/-- The **longest element** `w₀` of a finite Coxeter group ([HumC] §1.8, §5.6 (check),
[BB] §2.3). -/
noncomputable def longestElement : W := (cs.exists_max_length).choose

/-- `w₀` has maximal length. -/
theorem length_le_length_longestElement (w : W) : ℓ w ≤ ℓ cs.longestElement :=
  (cs.exists_max_length).choose_spec w

/-- Every reflection is a right inversion of `w₀`. -/
theorem isRightInversion_longestElement {t : W} (ht : cs.IsReflection t) :
    cs.IsRightInversion cs.longestElement t := by
  refine ⟨ht, ?_⟩
  have := cs.length_le_length_longestElement (cs.longestElement * t)
  have := ht.length_mul_left_ne cs.longestElement
  omega

/-- `ℓ(w₀ u) = ℓ(w₀) - ℓ(u)` ([BB] Prop. 2.3.2 (check), [HumC] §1.8 (check)). -/
theorem length_longestElement_mul (u : W) :
    ℓ (cs.longestElement * u) = ℓ cs.longestElement - ℓ u :=
  length_mul_of_forall_isRightInversion (fun _ ht ↦ cs.isRightInversion_longestElement ht) u

/-- `w₀` is an involution. -/
theorem longestElement_mul_self : cs.longestElement * cs.longestElement = 1 := by
  rw [← length_eq_zero_iff, length_longestElement_mul, Nat.sub_self]

/-- `w₀⁻¹ = w₀`. -/
theorem inv_longestElement : cs.longestElement⁻¹ = cs.longestElement :=
  inv_eq_of_mul_eq_one_right cs.longestElement_mul_self

/-- `ℓ(u w₀) = ℓ(w₀) - ℓ(u)`. -/
theorem length_mul_longestElement (u : W) :
    ℓ (u * cs.longestElement) = ℓ cs.longestElement - ℓ u := by
  rw [← length_inv, mul_inv_rev, inv_longestElement, length_longestElement_mul, length_inv]

/-- `ℓ(w₀) = ℓ(w₀ u) + ℓ(u)`. -/
theorem length_longestElement_mul_add (u : W) :
    ℓ (cs.longestElement * u) + ℓ u = ℓ cs.longestElement := by
  rw [length_longestElement_mul]
  have := cs.length_le_length_longestElement u
  omega

/-- Every simple reflection is a right descent of `w₀`. -/
theorem isRightDescent_longestElement (i : B) : cs.IsRightDescent cs.longestElement i :=
  ((cs.isRightInversion_simple_iff_isRightDescent _ _).mp
    (cs.isRightInversion_longestElement (cs.isReflection_simple i)))

/-- Every simple reflection is a left descent of `w₀`. -/
theorem isLeftDescent_longestElement (i : B) : cs.IsLeftDescent cs.longestElement i := by
  rw [← isRightDescent_inv_iff, inv_longestElement]
  exact cs.isRightDescent_longestElement i

/-- **Uniqueness of `w₀`**: `w₀` is the only element having every simple reflection as a right
descent ([BB] Prop. 2.3.1 (check)). -/
theorem eq_longestElement_iff_forall_isRightDescent {w : W} :
    w = cs.longestElement ↔ ∀ i, cs.IsRightDescent w i := by
  refine ⟨fun h i ↦ h ▸ cs.isRightDescent_longestElement i, fun h ↦ ?_⟩
  by_contra hne
  set y := w⁻¹ * cs.longestElement
  have hy1 : y ≠ 1 := fun h' ↦ hne (inv_mul_eq_one.mp h')
  have hly : ℓ y = ℓ cs.longestElement - ℓ w := by
    rw [← length_inv, mul_inv_rev, inv_inv, inv_longestElement, length_longestElement_mul]
  obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hy1
  have h1 := (cs.isRightDescent_iff).mp (h i)
  have h2 := (cs.isLeftDescent_iff).mp hi
  have h3 : cs.longestElement = w * s i * (s i * y) := by
    simp [y, mul_assoc]
  have h4 := cs.length_mul_le (w * s i) (s i * y)
  rw [← h3] at h4
  have := cs.length_le_length_longestElement w
  omega

/-- `w₀` is the unique element of maximal length. -/
theorem eq_longestElement_of_forall_length_le {w : W} (h : ∀ u, ℓ u ≤ ℓ w) :
    w = cs.longestElement := by
  rw [eq_longestElement_iff_forall_isRightDescent]
  intro i
  have := h (w * s i)
  rcases cs.length_mul_simple w i with h' | h'
  · omega
  · rw [isRightDescent_iff]; exact h'

/-- `ℓ(w₀)` is the number of reflections ([BB] Prop. 2.3.2 (check)). -/
theorem length_longestElement_eq_ncard :
    ℓ cs.longestElement = {t | cs.IsReflection t}.ncard := by
  rw [← ncard_setOf_isRightInversion]
  congr 1
  exact Set.ext fun t ↦ ⟨fun h ↦ h.1, cs.isRightInversion_longestElement⟩

/-- Every element is below `w₀` in the Bruhat order ([BB] Prop. 2.3.1 (check)). -/
theorem bruhatLE_longestElement (w : W) : cs.BruhatLE w cs.longestElement := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  obtain ⟨ω', hω', he⟩ := cs.exists_isReduced ((π ω)⁻¹ * cs.longestElement)
  have hl : ℓ ((π ω)⁻¹ * cs.longestElement) = ℓ cs.longestElement - ℓ (π ω) := by
    rw [← length_inv, mul_inv_rev, inv_inv, inv_longestElement, length_longestElement_mul]
  have hred : cs.IsReduced (ω ++ ω') := by
    unfold IsReduced
    rw [wordProd_append, ← he, mul_inv_cancel_left, length_append, ← hω.eq, ← hω'.eq, ← he, hl]
    have := cs.length_le_length_longestElement (π ω)
    omega
  have := hred.bruhatLE_of_sublist (sublist_append_left ω ω')
  rwa [wordProd_append, ← he, mul_inv_cancel_left] at this

/-- Conjugation by `w₀` permutes the simple reflections ([BB] §2.3 (check)). -/
theorem exists_longestElement_mul_simple_mul_eq (i : B) :
    ∃ j, cs.longestElement * s i * cs.longestElement = s j := by
  rw [← length_eq_one_iff, mul_assoc, length_longestElement_mul]
  have := (cs.isLeftDescent_iff).mp (cs.isLeftDescent_longestElement i)
  omega

/-- Left multiplication by `w₀` reverses Bruhat steps. -/
theorem BruhatStep.longestElement_mul {u w : W} (h : cs.BruhatStep u w) :
    cs.BruhatStep (cs.longestElement * w) (cs.longestElement * u) := by
  refine ⟨?_, ?_⟩
  · have : (cs.longestElement * w)⁻¹ * (cs.longestElement * u) = (u⁻¹ * w)⁻¹ := by group
    rw [this]
    exact h.1.isReflection_inv
  · rw [length_longestElement_mul, length_longestElement_mul]
    have := h.2
    have := cs.length_le_length_longestElement w
    omega

/-- `u ≤ w ↔ w₀ w ≤ w₀ u`: left multiplication by `w₀` is an antiautomorphism of the Bruhat order
([BB] Prop. 2.3.4 (check)). -/
theorem longestElement_mul_bruhatLE_longestElement_mul_iff {u w : W} :
    cs.BruhatLE (cs.longestElement * w) (cs.longestElement * u) ↔ cs.BruhatLE u w := by
  have key : ∀ {u w : W}, cs.BruhatLE u w →
      cs.BruhatLE (cs.longestElement * w) (cs.longestElement * u) := by
    intro u w h
    induction h with
    | refl => rfl
    | tail _ hs ih => exact hs.longestElement_mul.bruhatLE.trans ih
  refine ⟨fun h ↦ ?_, key⟩
  have := key h
  rwa [← mul_assoc, ← mul_assoc, longestElement_mul_self, one_mul, one_mul] at this

/-- `u ≤ w ↔ w w₀ ≤ u w₀` ([BB] Prop. 2.3.4 (check)). -/
theorem mul_longestElement_bruhatLE_mul_longestElement_iff {u w : W} :
    cs.BruhatLE (w * cs.longestElement) (u * cs.longestElement) ↔ cs.BruhatLE u w := by
  rw [← bruhatLE_inv_iff, mul_inv_rev, mul_inv_rev, inv_longestElement,
    longestElement_mul_bruhatLE_longestElement_mul_iff, bruhatLE_inv_iff]

end Finite

end CoxeterSystem
