/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.NeighborSerreGeneral
import LieLean.Algebra.QuantumGroup.BraidAction.TwoNodeBraid
import LieLean.Algebra.QuantumGroup.BraidAction.TripleEdgeOther

/-!
# Lusztig's `Tᵢ` at both nodes of every two-node Cartan datum

For an exact two-node Cartan datum `{i, j}` with arbitrary entries `aᵢⱼ = -r`, `aⱼᵢ = -s`
(every rank-two Cartan datum: `A₁ × A₁`, `A₂`, `B₂`, `G₂`, and all rank-two Kac–Moody data),
Lusztig's `Tᵢ` is an algebra automorphism of `U` with explicit reversal-conjugate inverse,
assuming `v ≠ 0`, `vᵢ - vᵢ⁻¹ ≠ 0` and `[(s+1) r - 2]ᵢ! ≠ 0`. Applied with the roles of `i`
and `j` exchanged, this gives both automorphisms. No hypothesis beyond `v ≠ 0` is needed when
`v` is not a root of unity.

## Main results

* `QuantumGroup.twoNode_transformedSerre`, `QuantumGroup.twoNode_braidGeneric`,
  `QuantumGroup.twoNodeBraidEquiv`: the automorphism at the node `i`.
* `QuantumGroup.twoNode_qFactorial_ne_zero_of_not_root`,
  `QuantumGroup.twoNodeBraidEquiv_of_not_root`: at a parameter that is not a root of unity.
* Comparisons with the earlier constructions, all by `rfl` (the transformed Serre relations are
  propositions): `shortNodeBraidEquiv_eq_twoNodeBraidEquiv` (`aⱼᵢ = -1`),
  `degreeOneBraidEquiv_eq_twoNodeBraidEquiv` (`aᵢⱼ = -1`, whose positive-part hypothesis is now
  proved as `degreeOne_serreAux_braidEj_eq_zero`), and
  `tripleEdgeOtherBraidEquiv_eq_twoNodeBraidEquiv` (long node of `G₂`).

## Hypotheses in the named cases

`[(s+1) r - 2]ᵢ! ≠ 0` is automatic for `A₁ × A₁` (`r = 0`), `A₂` and both nodes of `B₂`
(`[r]ᵢ! ≠ 0` suffices there, as `(s+1) r - 2 ≤ r`), and for `G₂` it is `[4]ᵢ! ≠ 0` at the short
node (`vᵢ⁴ + 1 ≠ 0` given `[3]ᵢ! ≠ 0`) and `[2]ᵢ! ≠ 0` at the long node (`vᵢ² + 1 ≠ 0`).

## References

Reconstructed from the quotient presentation; no primary source was consulted (the statement
that `Tᵢ` is an automorphism is [Lus] Thm. 37.1.2 (check), [Jan] Thm. 8.16 (check)).
-/

noncomputable section

namespace QuantumGroup

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  {i j : I} (hij : i ≠ j) (hall : ∀ l, l = i ∨ l = j)

include hij hall in
/-- The transformed quantum Serre relations at a node of any exact two-node datum. -/
theorem twoNode_transformedSerre (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hN : qFactorial (v ^ D.d i) ((negA D j i + 1) * negA D i j - 2) ≠ 0) :
    TransformedSerre R v i where
  serre_E l m hlm hl := by
    rcases hall l with rfl | rfl <;> rcases hall m with rfl | rfl
    · exact (hlm rfl).elim
    · exact (hl rfl).elim
    · simpa [braidImageE, hij.symm] using twoNode_qSerre_braidEj_braidEi (R := R) hij hq hN
    · exact (hlm rfl).elim
  serre_F l m hlm hl := by
    rcases hall l with rfl | rfl <;> rcases hall m with rfl | rfl
    · exact (hlm rfl).elim
    · exact (hl rfl).elim
    · simpa [braidImageF, hij.symm] using twoNode_qSerre_braidFj_braidFi (R := R) hij hq hN
    · exact (hlm rfl).elim

omit [DecidableEq I] [NeZero v] in
include hij hall in
/-- The generic hypotheses of `braidEquiv` at a node of an exact two-node datum follow from
`vᵢ - vᵢ⁻¹ ≠ 0` and `[(s+1) r - 2]ᵢ! ≠ 0`. -/
theorem twoNode_braidGeneric (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hN : qFactorial (v ^ D.d i) ((negA D j i + 1) * negA D i j - 2) ≠ 0) :
    BraidGeneric D v i where
  sub_ne := hq
  qFactorial_ne l hl := by
    rcases hall l with rfl | rfl
    · exact (hl rfl).elim
    · rcases le_or_gt (negA D i l) 1 with h | h
      · obtain h0 | h0 : negA D i l = 0 ∨ negA D i l = 1 := by omega
        · simp [h0]
        · simp [h0, qFactorial, qInt]
      · have hs := (twoNode_negA_pos (D := D) hij
          (by rw [cartanMatrix_eq_neg_negA hij]; omega)).2
        refine TwoNode.qFactorial_ne_zero_of_le (Nat.le_sub_of_add_le ?_) hN
        nlinarith

/-- **Lusztig's braid automorphism at a node of any exact two-node datum**, with explicit
reversal-conjugate inverse: for arbitrary entries `aᵢⱼ = -r`, `aⱼᵢ = -s`, given `v ≠ 0`,
`vᵢ - vᵢ⁻¹ ≠ 0` and `[(s+1) r - 2]ᵢ! ≠ 0`. With `i` and `j` exchanged it gives the
automorphism at the other node. -/
def twoNodeBraidEquiv (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hN : qFactorial (v ^ D.d i) ((negA D j i + 1) * negA D i j - 2) ≠ 0) :
    QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  braidEquiv (twoNode_braidGeneric hij hall hq hN) (twoNode_transformedSerre hij hall hq hN)

omit [DecidableEq I] in
/-- At a parameter that is not a root of unity, `[(s+1) r - 2]ᵢ! ≠ 0`. -/
theorem twoNode_qFactorial_ne_zero_of_not_root (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i j : I) :
    qFactorial (v ^ D.d i) ((negA D j i + 1) * negA D i j - 2) ≠ 0 := by
  classical
  exact LusztigF.qFactorial_ne_zero_of_not_root (NeZero.ne v) hv' i _

/-- **The automorphism at a node of any exact two-node datum at a generic parameter**: if `v`
is not a root of unity, `Tᵢ` is an automorphism for all Cartan entries. -/
def twoNodeBraidEquiv_of_not_root (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  twoNodeBraidEquiv hij hall (shortNode_braidGeneric_of_not_root hv' i).sub_ne
    (twoNode_qFactorial_ne_zero_of_not_root hv' i j)

/-! ### Comparison with the earlier constructions -/

omit [DecidableEq I] [NeZero v] in
/-- At a short node (`aⱼᵢ = -1`), the hypothesis `[2r-2, r-1]ᵢ ≠ 0` of
`shortNodeBraidEquiv` implies `[2r-2]ᵢ! ≠ 0`, given `[r]ᵢ! ≠ 0`. -/
theorem shortNode_qFactorial_ne_zero (h' : D.cartanMatrix j i = -1)
    (hr : qFactorial (v ^ D.d i) (negA D i j) ≠ 0)
    (hb : qBinomial (v ^ D.d i) (2 * negA D i j - 2) (negA D i j - 1) ≠ 0) :
    qFactorial (v ^ D.d i) ((negA D j i + 1) * negA D i j - 2) ≠ 0 := by
  have hji : negA D j i = 1 := by simp [negA, h']
  have hr' : qFactorial (v ^ D.d i) (negA D i j - 1) ≠ 0 :=
    TwoNode.qFactorial_ne_zero_of_le (by omega) hr
  have hm := qBinomial_mul_qFactorial_mul_qFactorial (v := v ^ D.d i)
    (show negA D i j - 1 ≤ 2 * negA D i j - 2 by omega)
  rw [show 2 * negA D i j - 2 - (negA D i j - 1) = negA D i j - 1 by omega] at hm
  rw [hji, show (1 + 1) * negA D i j - 2 = 2 * negA D i j - 2 by ring_nf, ← hm]
  exact mul_ne_zero (mul_ne_zero hb hr') hr'

/-- At a node with `aᵢⱼ = -1`, the positive-part identity `serreAux vⱼ vⱼ s (Tᵢ Eⱼ) Eⱼ = 0` of
`NeighborSerreDegreeOne.lean` holds for every `aⱼᵢ = -s`, given `vᵢ - vᵢ⁻¹ ≠ 0` and
`[s-1]ᵢ! ≠ 0`. -/
theorem degreeOne_serreAux_braidEj_eq_zero (h : D.cartanMatrix i j = -1)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) (hN : qFactorial (v ^ D.d i) (negA D j i - 1) ≠ 0) :
    serreAux (v ^ D.d j) (v ^ D.d j) (negA D j i) (braidEj R v i j) (E R v j) = 0 := by
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have hn : negA D i j = 0 + 1 := by simp [negA, h]
  have h1 := twoNode_serreAux_top (R := R) hij hq hn
    (by rwa [hn, zero_add, mul_one, show negA D j i + 1 - 2 = negA D j i - 1 by omega])
  rw [twoNode_braidEj_eq_X R v (NeZero.ne v) hn]
  simpa [qFactorial, qInt, BraidDiagonal.X] using h1

include hij hall in
/-- At a short node, `shortNodeBraidEquiv` is `twoNodeBraidEquiv`. -/
theorem shortNodeBraidEquiv_eq_twoNodeBraidEquiv (h' : D.cartanMatrix j i = -1)
    (hg : BraidGeneric D v i)
    (hb : qBinomial (v ^ D.d i) (2 * negA D i j - 2) (negA D i j - 1) ≠ 0) :
    shortNodeBraidEquiv (R := R) hij hall h' hg hb =
      twoNodeBraidEquiv hij hall hg.sub_ne
        (shortNode_qFactorial_ne_zero h' (hg.qFactorial_ne j hij.symm) hb) :=
  rfl

include hij hall in
/-- At a node with `aᵢⱼ = -1`, `degreeOneBraidEquiv` is `twoNodeBraidEquiv`. -/
theorem degreeOneBraidEquiv_eq_twoNodeBraidEquiv (h : D.cartanMatrix i j = -1)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) (hN : qFactorial (v ^ D.d i) (negA D j i - 1) ≠ 0) :
    degreeOneBraidEquiv (R := R) hij hall h hq (degreeOne_serreAux_braidEj_eq_zero h hq hN) =
      twoNodeBraidEquiv hij hall hq
        (by rwa [show negA D i j = 1 by simp [negA, h], mul_one,
          show negA D j i + 1 - 2 = negA D j i - 1 by omega]) :=
  rfl

include hij hall in
/-- At the long node of `G₂`, `tripleEdgeOtherBraidEquiv` is `twoNodeBraidEquiv`. -/
theorem tripleEdgeOtherBraidEquiv_eq_twoNodeBraidEquiv (h : D.cartanMatrix i j = -1)
    (h' : D.cartanMatrix j i = -3) (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (h2 : (v ^ D.d i) ^ 2 + 1 ≠ 0) (hN : qFactorial (v ^ D.d i) 2 ≠ 0) :
    tripleEdgeOtherBraidEquiv (R := R) hij hall h h' hq h2 =
      twoNodeBraidEquiv hij hall hq
        (by rwa [show negA D i j = 1 by simp [negA, h], show negA D j i = 3 by simp [negA, h']]) :=
  rfl

end QuantumGroup
