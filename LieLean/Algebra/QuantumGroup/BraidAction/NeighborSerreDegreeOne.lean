/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.General

/-!
# Neighbor-first Serre relations for a degree-one braid image

Let `i ≠ j` with `aᵢⱼ = -1` and arbitrary reverse entry `aⱼᵢ = -s`; put `p = vⱼ`, so that
`vᵢ = pˢ` by the symmetrizer. The braid image `X = Tᵢ(Eⱼ) = EᵢEⱼ - vᵢ⁻¹EⱼEᵢ` has degree one,
and with `A = Tᵢ(Eᵢ) = -FᵢK̃ᵢ` one has `X A - vᵢ⁻¹ A X = Eⱼ`. The Serre element
`S_{s+1}(X, A)` is a product of twisted commutators with `X`, one of which has parameter
`p⁻ˢ = vᵢ⁻¹`; applying that one first shows that the neighbor-first Serre element is the
positive-part element `Σₜ (-1)ᵗ [s t]_p pᵗ X^{s-t} Eⱼ Xᵗ = serreAux p p s X Eⱼ`, which involves
only `Eᵢ` and `Eⱼ`. The negative relation follows from the positive one by the Chevalley
involution. Hence, for an exact two-node datum, Lusztig's `Tᵢ` at the node `i` is an algebra
automorphism as soon as this single identity in `U⁺` holds.

## Main results

* `QuantumGroup.qSerre_succ_eq_serreAux_of_mul_sub_inv_pow_smul`: in any algebra, if
  `x a - p⁻ˢ a x = b` then `S_{s+1}(x, a) = serreAux p p s x b`.
* `QuantumGroup.degreeOne_braidEj_mul_braidEi_sub`: `X A - vᵢ⁻¹ A X = Eⱼ`.
* `QuantumGroup.degreeOne_qSerre_braidEj_braidEi_eq_serreAux`: the neighbor-first Serre element
  equals `serreAux p p s X Eⱼ`.
* `QuantumGroup.degreeOne_qSerre_braidFj_braidFi`: the negative neighbor-first relation from the
  positive one.
* `QuantumGroup.degreeOne_transformedSerre`, `QuantumGroup.degreeOne_braidGeneric`,
  `QuantumGroup.degreeOneBraidEquiv`: for an exact two-node datum with `aᵢⱼ = -1`, `Tᵢ` is an
  algebra automorphism given `vᵢ - vᵢ⁻¹ ≠ 0` and the positive identity
  `serreAux p p s X Eⱼ = 0`.

The positive identity is the Serre relation itself for `s = 1`; for `s = 2` it is proved (in
an equivalent normalization) inside `DoubleEdgeOther.lean`, and for `s = 3` in
`TripleEdgeOther.lean`. It is not proved here for general `s`.

## References

Reconstructed from the quotient presentation (the statement that `Tᵢ` is an automorphism is
[Lus] Prop. 37.1.2, [Jan] Prop. 8.13, proved there differently).
-/

noncomputable section

namespace QuantumGroup

section Ring

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B]

/-- If `x a - p⁻ˢ a x = b`, then the Serre element `S_{s+1}(x, a)` equals
`serreAux p p s x b = Σₜ (-1)ᵗ [s t]_p pᵗ x^{s-t} b xᵗ`: the twisted commutator with parameter
`p⁻ˢ` may be applied first. -/
theorem qSerre_succ_eq_serreAux_of_mul_sub_inv_pow_smul {p : k} (hp : p ≠ 0) (s : ℕ)
    {x a b : B} (h : x * a - p⁻¹ ^ s • (a * x) = b) :
    qSerre p (s + 1) x a = serreAux p p s x b := by
  rw [← qSerre_inv, ← serreAux_one, serreAux_succ (inv_ne_zero hp), one_mul, one_mul, inv_inv,
    h]
  simp only [serreAux, qBinomial_inv]

end Ring

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j : I}

/-- For the degree-one image `X = Tᵢ(Eⱼ)` (`aᵢⱼ = -1`) and `A = Tᵢ(Eᵢ)`:
`X A - vᵢ⁻¹ A X = Eⱼ`. The reverse entry `aⱼᵢ` and the ambient rank are unrestricted. -/
theorem degreeOne_braidEj_mul_braidEi_sub [NeZero v] (h : D.cartanMatrix i j = -1)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    braidEj R v i j * braidEi R i - (v ^ D.d i)⁻¹ • (braidEi R i * braidEj R v i j) =
      E R v j := by
  have hv := NeZero.ne v
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have hKX : Kt R v i * braidEj R v i j = v ^ D.d i • (braidEj R v i j * Kt R v i) := by
    have ht := braidK_mul_braidEj (R := R) hv hij (-ktilde R i)
    rw [braidK_apply, reflY_neg_ktilde, map_neg, root_ktilde, h, mul_neg_one, neg_neg,
      zpow_natCast] at ht
    exact ht
  have hc := congrArg (fun z : QuantumGroup R v ↦ z * Kt R v i)
    (braidEj_mul_Fi_sub_of_cartanMatrix_eq_neg_one (R := R) h hq)
  simp only [sub_mul, neg_mul, mul_assoc, K_neg_mul_Kt, mul_one] at hc
  simp only [braidEi, neg_mul, mul_neg, mul_assoc, hKX, mul_smul_comm, smul_neg, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero (D.d i) hv), one_smul]
  linear_combination (norm := module) -hc

/-- **Reduction of the neighbor-first Serre relation to `U⁺`.** For `aᵢⱼ = -1` and arbitrary
`aⱼᵢ = -s`, with `p = vⱼ`, the neighbor-first Serre element `S_{s+1}(Tᵢ Eⱼ, Tᵢ Eᵢ)` equals
`serreAux p p s (Tᵢ Eⱼ) Eⱼ`, an element of the positive part. Reconstructed. -/
theorem degreeOne_qSerre_braidEj_braidEi_eq_serreAux [NeZero v] (h : D.cartanMatrix i j = -1)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j i).toNat (braidEj R v i j) (braidEi R i) =
      serreAux (v ^ D.d j) (v ^ D.d j) (negA D j i) (braidEj R v i j) (E R v j) := by
  have hv := NeZero.ne v
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have hd : v ^ D.d i = (v ^ D.d j) ^ negA D j i := by
    have hs := D.d_mul_cartanMatrix_comm i j
    rw [h, cartanMatrix_eq_neg_negA hij.symm] at hs
    have hz : (D.d i : ℤ) = D.d j * negA D j i := by linear_combination -hs
    rw [← pow_mul]
    exact congrArg (v ^ ·) (by exact_mod_cast hz)
  rw [one_sub_cartanMatrix_toNat hij.symm]
  apply qSerre_succ_eq_serreAux_of_mul_sub_inv_pow_smul (pow_ne_zero _ hv)
  rw [inv_pow, ← hd]
  exact degreeOne_braidEj_mul_braidEi_sub h hq

/-- The negative neighbor-first Serre relation follows from the positive one (in any degree
`n`) via the Chevalley involution, for `aᵢⱼ = -1` and arbitrary `aⱼᵢ`. -/
theorem degreeOne_qSerre_braidFj_braidFi [NeZero v] (h : D.cartanMatrix i j = -1) {n : ℕ}
    (hE : qSerre (v ^ D.d j) n (braidEj R v i j) (braidEi R i) = 0) :
    qSerre (v ^ D.d j) n (braidFj R v i j) (braidFi R i) = 0 := by
  have hv := NeZero.ne v
  have hc := congrArg (chevalley R v) hE
  rw [map_qSerre, map_zero, chevalley_braidEi hv,
    chevalley_braidEj_of_cartanMatrix_eq_neg_one hv h, qSerre_smul_smul] at hc
  exact (smul_eq_zero.mp hc).resolve_left
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hv))))
      (pow_ne_zero _ (pow_ne_zero _ hv)))

section TwoNode

variable [NeZero v] (hij : i ≠ j) (hall : ∀ l, l = i ∨ l = j) (h : D.cartanMatrix i j = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hT : serreAux (v ^ D.d j) (v ^ D.d j) (negA D j i) (braidEj R v i j) (E R v j) = 0)

include hij hall h hq hT in
/-- For an exact two-node datum with `aᵢⱼ = -1`, the transformed Serre relations at `i` follow
from the single positive identity `serreAux p p s (Tᵢ Eⱼ) Eⱼ = 0`, `p = vⱼ`, `s = -aⱼᵢ`. -/
theorem degreeOne_transformedSerre : TransformedSerre R v i := by
  have hE : qSerre (v ^ D.d j) (1 - D.cartanMatrix j i).toNat (braidEj R v i j)
      (braidEi R i) = 0 := by
    rw [degreeOne_qSerre_braidEj_braidEi_eq_serreAux h hq, hT]
  refine ⟨fun l m hlm hl ↦ ?_, fun l m hlm hl ↦ ?_⟩ <;>
    rcases hall l with rfl | rfl <;> rcases hall m with rfl | rfl
  any_goals exact (hlm rfl).elim
  any_goals exact (hl rfl).elim
  · simpa [braidImageE, hij.symm] using hE
  · simpa [braidImageF, hij.symm] using degreeOne_qSerre_braidFj_braidFi h hE

omit [DecidableEq I] [NeZero v] in
include hall h in
/-- At a node `i` with `aᵢⱼ = -1` of an exact two-node datum, the generic parameter
hypotheses reduce to `vᵢ - vᵢ⁻¹ ≠ 0` (the factorial `[1]ᵢ!` is `1`). -/
theorem degreeOne_braidGeneric (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) : BraidGeneric D v i where
  sub_ne := hq
  qFactorial_ne l hl := by
    rcases hall l with rfl | rfl
    · exact (hl rfl).elim
    · simp [negA, h, qFactorial, qInt]

/-- **Lusztig's braid automorphism at a node with `aᵢⱼ = -1`** of an exact two-node datum
(arbitrary `aⱼᵢ = -s`), given `vᵢ - vᵢ⁻¹ ≠ 0` and the positive identity
`serreAux p p s (Tᵢ Eⱼ) Eⱼ = 0`; the inverse is the reversal conjugate of `Tᵢ`. -/
def degreeOneBraidEquiv : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  braidEquiv (degreeOne_braidGeneric hall h hq) (degreeOne_transformedSerre hij hall h hq hT)

end TwoNode

end QuantumGroup
