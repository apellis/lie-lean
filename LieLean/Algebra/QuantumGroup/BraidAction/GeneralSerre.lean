/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.TwoNodeGeneral

/-!
# All transformed Serre relations; Lusztig's `Tᵢ` at every node of every Cartan datum

For a node `i` and two further distinct nodes `l ≠ m` (both `≠ i`), with `q = vᵢ`,
`r = -aᵢₗ`, `t = -aᵢₘ` and `n = 1 - aₗₘ`, we prove the transformed Serre relation
`S_n(Tᵢ Eₗ, Tᵢ Eₘ) = 0` (and its `F`-analogue) in arbitrary rank, assuming only `v ≠ 0` and
`[n r + t]_q! ≠ 0`. Together with the neighbor-first relations of
`BraidAction/NeighborSerreGeneral.lean` this gives all relations `TransformedSerre` required by
`braidEquiv`, so Lusztig's `Tᵢ` is an algebra automorphism at every node of every Cartan datum
(arbitrary rank, field and root-datum lattice), under explicit q-factorial hypotheses, and with
no hypothesis beyond `v ≠ 0` when `v` is not a root of unity.

## Main results

* `QuantumGroup.outer_qSerre_braidEj_braidEj`, `QuantumGroup.outer_qSerre_braidFj_braidFj`: the
  transformed Serre relations between two nodes other than `i`.
* `QuantumGroup.BraidSerreGeneric`: the q-factorial hypotheses at the node `i`;
  `QuantumGroup.braidSerreGeneric_of_not_root`.
* `QuantumGroup.transformedSerre_of_braidSerreGeneric`,
  `QuantumGroup.braidGeneric_of_braidSerreGeneric`: `TransformedSerre` and `BraidGeneric`.
* `QuantumGroup.braidEquivOfGeneric`, `QuantumGroup.braidEquivOfNotRoot`: `Tᵢ` as an algebra
  automorphism with explicit reversal-conjugate inverse; the length-two/three relations of
  `BraidAction/GeneralRelations.lean` apply to it (it is a `braidEquiv`).
* `QuantumGroup.twoNodeBraidEquiv_eq_braidEquivOfGeneric`: agreement with the two-node case.

## Method

With `X k = (ad Eᵢ)ᵏ Eₗ`, `Y k = (ad Eᵢ)ᵏ Eₘ` (twists `c₀ = q⁻ʳ`, `c_Y = q⁻ᵗ`) we have
`X (r+1) = 0 = Y (t+1)` by the Serre relations at `i`, and the twists satisfy `c_Yʳ = c₀ᵗ`.
The Serre element `S_n(Eₗ, Eₘ)` is an iterated twisted commutator with `Eₗ`, so the iteration
lemma `TwoNode.dd_serreAux` (starting from `Z = Eₘ`, `M = t`) shows that `(ad Eᵢ)^{n r + t}` maps
it to a nonzero multiple of `S_n(X r, Y t)`. Since `S_n(Eₗ, Eₘ) = 0`, so is `S_n(X r, Y t)`.
Equivalently: in the Leibniz expansion only the term raising every factor to its top survives,
with the q-multinomial coefficient `[n r + t]! / ([r]!ⁿ [t]!)` (Gaussian in `q²`) and a twist
independent of the word.

## References

Reconstructed from the quotient presentation; no primary source was consulted (the statement
that `Tᵢ` is an automorphism is [Lus] Thm. 37.1.2 (check), [Jan] Thm. 8.16 (check), proved
there differently).
-/

noncomputable section

namespace QuantumGroup

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k}

variable (R v) in
/-- `Tᵢ(Eₗ) = [r]ᵢ!⁻¹ X r` (`r = -aᵢₗ`, any value including `0`). -/
lemma braidEj_eq_smul_X (hv : v ≠ 0) (i l : I) :
    braidEj R v i l = (qFactorial (v ^ D.d i) (negA D i l))⁻¹ •
      BraidDiagonal.X (v ^ D.d i) ((v ^ D.d i) ^ negA D i l) (E R v i) (E R v l)
        (negA D i l) := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  have hc : (v ^ D.d i) ^ negA D i l * (v ^ D.d i * (v ^ D.d i) ^ negA D i l)⁻¹ =
      (v ^ D.d i)⁻¹ := by
    field_simp
  rw [BraidDiagonal.X_eq_serreAux hq0 (pow_ne_zero _ hq0), hc, braidEj]

variable (R v) in
/-- The Serre relation `S_{r+1}(Eᵢ, Eₗ) = 0` as `X (r+1) = 0`, in the derivation form. -/
lemma dd_braidTop_eq_zero (hv : v ≠ 0) {i l : I} (hil : i ≠ l) :
    TwoNode.dd (v ^ D.d i) (E R v i) ((v ^ D.d i) ^ negA D i l)⁻¹ (negA D i l + 1)
      (E R v l) = 0 := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  have hc : (v ^ D.d i) ^ (negA D i l + 1) * (v ^ D.d i * (v ^ D.d i) ^ negA D i l)⁻¹ = 1 := by
    field_simp
    ring
  rw [← TwoNode.X_eq_dd, BraidDiagonal.X_eq_serreAux hq0 (pow_ne_zero _ hq0), hc,
    serreAux_one]
  have h := serre_E R v hil
  rwa [one_sub_cartanMatrix_toNat hil] at h

/-- **The transformed Serre relation between two nodes other than `i`**: for distinct
`l, m ≠ i`, `S_{1-aₗₘ}(Tᵢ Eₗ, Tᵢ Eₘ) = 0`, in arbitrary rank, assuming only `v ≠ 0` and
`[(1 - aₗₘ) r + t]ᵢ! ≠ 0` (`r = -aᵢₗ`, `t = -aᵢₘ`). Reconstructed. -/
theorem outer_qSerre_braidEj_braidEj [NeZero v] {i l m : I} (hil : i ≠ l) (him : i ≠ m)
    (hlm : l ≠ m)
    (hN : qFactorial (v ^ D.d i) ((1 - D.cartanMatrix l m).toNat * negA D i l + negA D i m)
      ≠ 0) :
    qSerre (v ^ D.d l) (1 - D.cartanMatrix l m).toNat (braidEj R v i l) (braidEj R v i m) =
      0 := by
  have hv := NeZero.ne v
  set q := v ^ D.d i with hqdef
  have hq0 : q ≠ 0 := pow_ne_zero _ hv
  set r := negA D i l
  set t := negA D i m
  set n := (1 - D.cartanMatrix l m).toNat
  rw [braidEj_eq_smul_X R v hv i l, braidEj_eq_smul_X R v hv i m, qSerre_smul_smul,
    TwoNode.X_eq_dd, TwoNode.X_eq_dd]
  have hX := dd_braidTop_eq_zero R v hv hil
  have hZ := dd_braidTop_eq_zero R v hv him
  have htw : ((q ^ t)⁻¹) ^ r = ((q ^ r)⁻¹) ^ t := by ring
  have hG : ∀ l' < n, ShortNode.gauss q (t + (l' + 1) * r) r ≠ 0 := by
    intro l' hl'
    rw [show t + (l' + 1) * r = (t + l' * r) + r by ring]
    refine TwoNode.gauss_ne_zero hq0 (TwoNode.qFactorial_ne_zero_of_le ?_ hN)
    nlinarith
  obtain ⟨K, hK, e0, -⟩ := TwoNode.dd_serreAux hq0 (inv_ne_zero (pow_ne_zero r hq0))
    (pow_ne_zero (D.d l) hv) hX n 1 _ t (E R v m) _ htw hZ rfl hG
  rw [serreAux_one, serreAux_one, serre_E R v hlm, TwoNode.dd_zero_right] at e0
  rw [(smul_eq_zero.1 e0.symm).resolve_left hK, smul_zero]

/-- The negative transformed Serre relation between two nodes other than `i`. -/
theorem outer_qSerre_braidFj_braidFj [NeZero v] {i l m : I} (hil : i ≠ l) (him : i ≠ m)
    (hlm : l ≠ m)
    (hN : qFactorial (v ^ D.d i) ((1 - D.cartanMatrix l m).toNat * negA D i l + negA D i m)
      ≠ 0) :
    qSerre (v ^ D.d l) (1 - D.cartanMatrix l m).toNat (braidFj R v i l) (braidFj R v i m) =
      0 := by
  have hv := NeZero.ne v
  have hs := congrArg (chevalley R v) (outer_qSerre_braidEj_braidEj (R := R) hil him hlm hN)
  rw [map_qSerre, map_zero, twoNode_chevalley_braidEj hv, twoNode_chevalley_braidEj hv,
    qSerre_smul_smul] at hs
  have hc (a : I) : ((-1 : k) ^ negA D i a * (v ^ D.d i)⁻¹ ^ negA D i a) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hv)))
  exact (smul_eq_zero.mp hs).resolve_left (mul_ne_zero (pow_ne_zero _ (hc l)) (hc m))

/-! ### `Tᵢ` at every node -/

variable (D v) in
/-- The q-factorial hypotheses at the node `i`: for every `j ≠ i`,
`[(1 - aⱼᵢ)(-aᵢⱼ) - 2]ᵢ! ≠ 0` (neighbor-first relations), and for distinct `l, m ≠ i`,
`[(1 - aₗₘ)(-aᵢₗ) + (-aᵢₘ)]ᵢ! ≠ 0`. -/
structure BraidSerreGeneric (i : I) : Prop where
  neighbor : ∀ j, j ≠ i → qFactorial (v ^ D.d i) ((negA D j i + 1) * negA D i j - 2) ≠ 0
  outer : ∀ l m, l ≠ m → l ≠ i → m ≠ i →
    qFactorial (v ^ D.d i) ((1 - D.cartanMatrix l m).toNat * negA D i l + negA D i m) ≠ 0

omit [DecidableEq I] in
/-- At a parameter that is not a root of unity, `BraidSerreGeneric` holds at every node. -/
theorem braidSerreGeneric_of_not_root [NeZero v] (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i : I) :
    BraidSerreGeneric D v i := by
  classical
  exact ⟨fun _ _ ↦ LusztigF.qFactorial_ne_zero_of_not_root (NeZero.ne v) hv' i _,
    fun _ _ _ _ _ ↦ LusztigF.qFactorial_ne_zero_of_not_root (NeZero.ne v) hv' i _⟩

variable {i : I}

omit [DecidableEq I] in
/-- The generic hypotheses of `braidEquiv` follow from `vᵢ - vᵢ⁻¹ ≠ 0` and
`BraidSerreGeneric`. -/
theorem braidGeneric_of_braidSerreGeneric (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (h : BraidSerreGeneric D v i) : BraidGeneric D v i where
  sub_ne := hq
  qFactorial_ne j hj := by
    have hN := h.neighbor j hj
    rcases le_or_gt (negA D i j) 1 with h1 | h1
    · obtain h0 | h0 : negA D i j = 0 ∨ negA D i j = 1 := by omega
      · simp [h0]
      · simp [h0, qFactorial, qInt]
    · have hs := (twoNode_negA_pos (D := D) (Ne.symm hj)
        (by rw [cartanMatrix_eq_neg_negA (Ne.symm hj)]; omega)).2
      refine TwoNode.qFactorial_ne_zero_of_le (Nat.le_sub_of_add_le ?_) hN
      nlinarith

/-- **All transformed Serre relations at the node `i`**, for any Cartan datum, given
`vᵢ - vᵢ⁻¹ ≠ 0` and `BraidSerreGeneric`. -/
theorem transformedSerre_of_braidSerreGeneric [NeZero v]
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) (h : BraidSerreGeneric D v i) :
    TransformedSerre R v i where
  serre_E l m hlm hl := by
    by_cases hm : m = i
    · subst hm
      simpa [braidImageE, hl] using
        twoNode_qSerre_braidEj_braidEi (R := R) (Ne.symm hl) hq (h.neighbor l hl)
    · simpa [braidImageE, hl, hm] using
        outer_qSerre_braidEj_braidEj (R := R) (Ne.symm hl) (Ne.symm hm) hlm
          (h.outer l m hlm hl hm)
  serre_F l m hlm hl := by
    by_cases hm : m = i
    · subst hm
      simpa [braidImageF, hl] using
        twoNode_qSerre_braidFj_braidFi (R := R) (Ne.symm hl) hq (h.neighbor l hl)
    · simpa [braidImageF, hl, hm] using
        outer_qSerre_braidFj_braidFj (R := R) (Ne.symm hl) (Ne.symm hm) hlm
          (h.outer l m hlm hl hm)

/-- **Lusztig's braid automorphism `Tᵢ` at any node of any Cartan datum** (arbitrary rank,
field and root-datum lattice), with explicit reversal-conjugate inverse, given `v ≠ 0`,
`vᵢ - vᵢ⁻¹ ≠ 0` and the q-factorial hypotheses `BraidSerreGeneric D v i`. -/
def braidEquivOfGeneric [NeZero v] (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (h : BraidSerreGeneric D v i) : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  braidEquiv (braidGeneric_of_braidSerreGeneric hq h) (transformedSerre_of_braidSerreGeneric hq h)

variable (R) in
/-- **Lusztig's `Tᵢ` at a generic parameter**: if `v` is not a root of unity, `Tᵢ` is an
algebra automorphism at every node of every Cartan datum. -/
def braidEquivOfNotRoot [NeZero v] (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i : I) :
    QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  braidEquivOfGeneric (shortNode_braidGeneric_of_not_root hv' i).sub_ne
    (braidSerreGeneric_of_not_root hv' i)

omit [DecidableEq I] in
/-- For an exact two-node datum, `BraidSerreGeneric` reduces to the neighbor condition. -/
theorem braidSerreGeneric_of_twoNode {j : I} (hij : i ≠ j) (hall : ∀ l, l = i ∨ l = j)
    (hN : qFactorial (v ^ D.d i) ((negA D j i + 1) * negA D i j - 2) ≠ 0) :
    BraidSerreGeneric D v i where
  neighbor l hl := by
    rcases hall l with rfl | rfl
    · exact (hl rfl).elim
    · exact hN
  outer l m hlm hl hm := by
    rcases hall l with rfl | rfl
    · exact (hl rfl).elim
    · rcases hall m with rfl | rfl
      · exact (hm rfl).elim
      · exact (hlm rfl).elim

/-- For an exact two-node datum, `twoNodeBraidEquiv` is `braidEquivOfGeneric`. -/
theorem twoNodeBraidEquiv_eq_braidEquivOfGeneric [NeZero v] {j : I} (hij : i ≠ j)
    (hall : ∀ l, l = i ∨ l = j) (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hN : qFactorial (v ^ D.d i) ((negA D j i + 1) * negA D i j - 2) ≠ 0) :
    twoNodeBraidEquiv (R := R) hij hall hq hN =
      braidEquivOfGeneric hq (braidSerreGeneric_of_twoNode hij hall hN) :=
  rfl

end QuantumGroup
