/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Normal

/-!
# Kashiwara's action of the simple reflections on a seminormal crystal

For a seminormal crystal `B` and `i ∈ I`, Kashiwara ([Kas] (11.1), [Kas94] §7)
defines `Sᵢ : B → B` by
`Sᵢ b = f̃ᵢ^{⟨wt b, αᵢ^∨⟩} b` if `⟨wt b, αᵢ^∨⟩ ≥ 0` and `Sᵢ b = ẽᵢ^{-⟨wt b, αᵢ^∨⟩} b` otherwise:
it reverses each `i`-string. We prove that `Sᵢ` is an involution with `wt (Sᵢ b) = rᵢ (wt b)`,
`εᵢ(Sᵢ b) = φᵢ(b)` and `φᵢ(Sᵢ b) = εᵢ(b)`. Consequently the number of elements of weight `μ`
equals the number of elements of weight `rᵢ μ`, the crystal analogue of the `W`-invariance of
characters of integrable modules.

For *normal* crystals the `Sᵢ` satisfy the braid relations and so define an action of the Weyl
group ([Kas94] Thm. 7.2.2); this is **not** proved here (the proof needs the
realizability of normal crystals by integrable modules), and for merely seminormal crystals it can
fail. Only the individual involutions `Sᵢ` are constructed.

## Main definitions

* `Crystal.reflection C i`: Kashiwara's map `Sᵢ` (for a seminormal crystal).
* `Crystal.IsSeminormal.reflectionPerm`: `Sᵢ` as a permutation of `B`.
* `Crystal.IsSeminormal.weightEquiv`: the bijection `{b | wt b = μ} ≃ {b | wt b = rᵢ μ}`.

## Main results

* `Crystal.IsSeminormal.reflection_reflection`: `Sᵢ² = id`.
* `Crystal.IsSeminormal.wt_reflection`: `wt (Sᵢ b) = rᵢ (wt b)`.
* `Crystal.IsSeminormal.ε_reflection`, `Crystal.IsSeminormal.φ_reflection`.
* `Crystal.IsSeminormal.card_wt_reflection`: `#{b | wt b = rᵢ μ} = #{b | wt b = μ}`.

## References

* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995).
* [Kas94] M. Kashiwara, *Crystal bases of modified quantized enveloping algebra*, Duke Math. J.
  **73** (1994), 383–413.
-/

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B : Type*}
  (C : Crystal D B) {i : ι} {b : B}

/-- Kashiwara's map `Sᵢ` ([Kas] (11.1), [Kas94] §7):
`Sᵢ b = f̃ᵢ^{⟨wt b, αᵢ^∨⟩} b` if `⟨wt b, αᵢ^∨⟩ ≥ 0` and `Sᵢ b = ẽᵢ^{-⟨wt b, αᵢ^∨⟩} b` otherwise.
For a seminormal crystal these iterates are never `0`; in general we use the junk value `b`
when they are. -/
def reflection (i : ι) (b : B) : B :=
  (if 0 ≤ D.coroot i (C.wt b) then C.fIter i (D.coroot i (C.wt b)).toNat b
    else C.eIter i (-D.coroot i (C.wt b)).toNat b).getD b

namespace IsSeminormal

variable {C}

private lemma withBot_le_of_eq {x y : WithBot ℤ} {k : ℤ} (hk : 0 ≤ k) (hy : 0 ≤ y)
    (h : x = y + k) : ((k.toNat : ℕ) : WithBot ℤ) ≤ x := by
  rw [h]
  induction y using WithBot.recBotCoe with
  | bot => simp at hy
  | coe a =>
    have ha : (0 : ℤ) ≤ a := by exact_mod_cast hy
    rw [← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_le_coe]
    omega

lemma fIter_reflection (hC : C.IsSeminormal) (h : 0 ≤ D.coroot i (C.wt b)) :
    C.fIter i (D.coroot i (C.wt b)).toNat b = some (C.reflection i b) := by
  have hs : (C.fIter i (D.coroot i (C.wt b)).toNat b).isSome :=
    hC.isSome_fIter_iff _ |>.mpr (withBot_le_of_eq h (hC.ε_nonneg i b) (C.φ_eq i b))
  simp only [reflection, h, ↓reduceIte]
  rw [← Option.some_get hs, Option.getD_some]

lemma eIter_reflection (hC : C.IsSeminormal) (h : D.coroot i (C.wt b) < 0) :
    C.eIter i (-D.coroot i (C.wt b)).toNat b = some (C.reflection i b) := by
  have hε : C.ε i b = C.φ i b + ((-D.coroot i (C.wt b) : ℤ) : WithBot ℤ) := by
    rw [C.φ_eq, add_assoc, ← WithBot.coe_add, add_neg_cancel, WithBot.coe_zero, add_zero]
  have hs : (C.eIter i (-D.coroot i (C.wt b)).toNat b).isSome :=
    hC.isSome_eIter_iff _ |>.mpr (withBot_le_of_eq (by omega) (hC.φ_nonneg i b) hε)
  simp only [reflection, not_le.mpr h, ↓reduceIte]
  rw [← Option.some_get hs, Option.getD_some]

/-- `wt (Sᵢ b) = rᵢ (wt b)` ([Kas] (11.2)). -/
theorem wt_reflection (hC : C.IsSeminormal) (i : ι) (b : B) :
    C.wt (C.reflection i b) = D.reflection i (C.wt b) := by
  rw [D.reflection_apply]
  by_cases h : 0 ≤ D.coroot i (C.wt b)
  · rw [C.wt_fIter (hC.fIter_reflection h), ← natCast_zsmul, Int.toNat_of_nonneg h]
  · rw [C.wt_eIter (hC.eIter_reflection (not_le.mp h)), ← natCast_zsmul,
      Int.toNat_of_nonneg (by omega), neg_smul, ← sub_eq_add_neg]

lemma coroot_wt_reflection (hC : C.IsSeminormal) (i : ι) (b : B) :
    D.coroot i (C.wt (C.reflection i b)) = -D.coroot i (C.wt b) := by
  rw [hC.wt_reflection, D.coroot_reflection]

/-- `Sᵢ² = id` ([Kas] §11). -/
theorem reflection_reflection (hC : C.IsSeminormal) (i : ι) (b : B) :
    C.reflection i (C.reflection i b) = b := by
  have hk := hC.coroot_wt_reflection i b
  rcases lt_trichotomy (D.coroot i (C.wt b)) 0 with h | h | h
  · have h' : 0 ≤ D.coroot i (C.wt (C.reflection i b)) := by omega
    have := hC.fIter_reflection h'
    rw [hk, C.fIter_eq_some_iff] at this
    have h₂ := (C.fIter_eq_some_iff _ _ _).mpr (hC.eIter_reflection h)
    rw [(C.fIter_eq_some_iff _ _ _).mpr this] at h₂
    exact Option.some_injective _ h₂
  · have h₀ := hC.fIter_reflection h.ge
    rw [h] at h₀
    simp only [Int.toNat_zero, fIter_zero, Option.some.injEq] at h₀
    rw [← h₀, ← h₀]
  · have h' : D.coroot i (C.wt (C.reflection i b)) < 0 := by omega
    have := hC.eIter_reflection h'
    rw [hk, neg_neg, ← C.fIter_eq_some_iff] at this
    have h₂ := (C.fIter_eq_some_iff _ _ _).mp (hC.fIter_reflection h.le)
    rw [(C.fIter_eq_some_iff _ _ _).mp this] at h₂
    exact Option.some_injective _ h₂

lemma reflection_involutive (hC : C.IsSeminormal) (i : ι) :
    Function.Involutive (C.reflection i) :=
  hC.reflection_reflection i

/-- `εᵢ(Sᵢ b) = φᵢ(b)`. -/
theorem ε_reflection (hC : C.IsSeminormal) (i : ι) (b : B) :
    C.ε i (C.reflection i b) = C.φ i b := by
  by_cases h : 0 ≤ D.coroot i (C.wt b)
  · rw [C.ε_fIter (hC.fIter_reflection h), C.φ_eq, ← WithBot.coe_natCast,
      Int.toNat_of_nonneg h]
  · have h' := C.ε_eIter (hC.eIter_reflection (not_le.mp h))
    rw [← WithBot.coe_natCast, Int.toNat_of_nonneg (by omega)] at h'
    rw [C.φ_eq, h', add_assoc, ← WithBot.coe_add, neg_add_cancel, WithBot.coe_zero, add_zero]

/-- `φᵢ(Sᵢ b) = εᵢ(b)`. -/
theorem φ_reflection (hC : C.IsSeminormal) (i : ι) (b : B) :
    C.φ i (C.reflection i b) = C.ε i b := by
  rw [C.φ_eq, hC.ε_reflection, hC.coroot_wt_reflection, C.φ_eq, add_assoc, ← WithBot.coe_add,
    add_neg_cancel, WithBot.coe_zero, add_zero]

/-- Kashiwara's involution `Sᵢ` of a seminormal crystal, as a permutation. -/
def reflectionPerm (hC : C.IsSeminormal) (i : ι) : Equiv.Perm B :=
  (hC.reflection_involutive i).toPerm

@[simp] lemma reflectionPerm_apply (hC : C.IsSeminormal) (i : ι) (b : B) :
    hC.reflectionPerm i b = C.reflection i b := rfl

/-- `Sᵢ` restricts to a bijection between the elements of weight `μ` and those of weight
`rᵢ μ`. -/
def weightEquiv (hC : C.IsSeminormal) (i : ι) (μ : X) :
    {b // C.wt b = μ} ≃ {b // C.wt b = D.reflection i μ} where
  toFun b := ⟨C.reflection i b, by rw [hC.wt_reflection, b.2]⟩
  invFun b := ⟨C.reflection i b, by rw [hC.wt_reflection, b.2, D.reflection_reflection]⟩
  left_inv b := Subtype.ext (hC.reflection_reflection i b)
  right_inv b := Subtype.ext (hC.reflection_reflection i b)

/-- In a seminormal crystal, the number of elements of weight `rᵢ μ` equals the number of
elements of weight `μ` (both may be infinite, in which case `Nat.card` is `0`): the crystal
analogue of the `W`-invariance of weight multiplicities ([Kas] §11, via `Sᵢ`). -/
theorem card_wt_reflection (hC : C.IsSeminormal) (i : ι) (μ : X) :
    Nat.card {b // C.wt b = D.reflection i μ} = Nat.card {b // C.wt b = μ} :=
  (Nat.card_congr (hC.weightEquiv i μ)).symm

end IsSeminormal

end Crystal
