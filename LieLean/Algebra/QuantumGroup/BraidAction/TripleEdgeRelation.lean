/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.GeneralRelations
import LieLean.Algebra.QuantumGroup.BraidAction.NeighborSerreDegreeOne
import LieLean.Algebra.QuantumGroup.BraidAction.TripleEdgeOther
import LieLean.Algebra.QuantumGroup.BraidAction.TripleEdgeBraid

/-!
# The length-six braid relation for `G₂`

Let `{i, j}` be an exact two-node Cartan datum with `aᵢⱼ = -3`, `aⱼᵢ = -1` (type `G₂`, `i` the
short node), `q = vᵢ`, so that `vⱼ = q³`. For any algebra endomorphisms `Tᵢ`, `Tⱼ` of `U` with
Lusztig's generator formulas (`HasBraidGeneratorImages`), we prove
`Tᵢ Tⱼ Tᵢ Tⱼ Tᵢ Tⱼ = Tⱼ Tᵢ Tⱼ Tᵢ Tⱼ Tᵢ`, assuming only `v ≠ 0`, `q - q⁻¹ ≠ 0` and `[3]_q! ≠ 0`.

## Method

Since `sⱼ sᵢ sⱼ sᵢ sⱼ` fixes `αᵢ` and `sᵢ sⱼ sᵢ sⱼ sᵢ` fixes `αⱼ`, it suffices to prove the four
fixed-point identities `Tⱼ Tᵢ Tⱼ Tᵢ Tⱼ (Eᵢ) = Eᵢ`, `Tᵢ Tⱼ Tᵢ Tⱼ Tᵢ (Eⱼ) = Eⱼ` and their `F`
analogues; the six-fold words then agree on every generator (for `Eᵢ`:
`Tᵢ (Tⱼ Tᵢ Tⱼ Tᵢ Tⱼ Eᵢ) = Tᵢ Eᵢ = -Fᵢ K̃ᵢ = Tⱼ Tᵢ Tⱼ Tᵢ Tⱼ (Tᵢ Eᵢ)`), and on `K_μ` by the
reflection identity. No normal-ordering certificate is used: each step is an instance of the
lowering identity `X (n+1) Tᵢ(Eᵢ) - s(n+1)⁻¹ Tᵢ(Eᵢ) X (n+1) = cc (n+1) X n` for the twisted
commutators `X n = (ad Eᵢ)ⁿ Eⱼ` of `BraidAction/Diagonal.lean` (`Hyp.stepE`), or of the degree-one
identity `Y Tⱼ(Eⱼ) - vⱼ⁻¹ Tⱼ(Eⱼ) Y = Eᵢ` for `Y = Tⱼ(Eᵢ)` (`degreeOne_braidEj_mul_braidEi_sub`).
With `Z = Y Eᵢ - q⁻¹ Eᵢ Y = Tⱼ(X 2)` the root vectors move along the chains
`Eᵢ ↦ Y ↦ [2]⁻¹ X 2 ↦ [2]⁻¹ Z ↦ X 1 ↦ Eᵢ` and
`Eⱼ ↦ [3]!⁻¹ X 3 ↦ [3]!⁻¹ (Y Z - q Z Y) ↦ [3]!⁻¹ (X 2 X 1 - q X 1 X 2) ↦ [3]!⁻¹ (Z Eᵢ - q Eᵢ Z)
↦ Eⱼ`, and similarly for `F` with `Hyp.stepF`.

## Main results

* `QuantumGroup.tripleSix_Ei`, `QuantumGroup.tripleSix_Ej`, `QuantumGroup.tripleSix_Fi`,
  `QuantumGroup.tripleSix_Fj`: the fixed-point identities.
* `QuantumGroup.reflY_braid_six_of_triple_edge`: the length-six relation on the lattice.
* `QuantumGroup.HasBraidGeneratorImages.six_braid_of_triple_edge`: the length-six relation for
  algebra homomorphisms with the generator formulas.
* `QuantumGroup.braidEquiv_braid_six_of_triple_edge`,
  `QuantumGroup.tripleEdgeBraidEquiv_braid_six`: the relation for the constructed automorphisms.

## References

The statement is [Lus] 39.4.3, [Jan] 8.17, Remark (proved there by citing
[Lus] 39.2.2); the reduction to fixed points (as in [Jan] 8.16–8.17)
follows the standard argument. The chain computation is our own reconstruction.
-/

noncomputable section

namespace QuantumGroup

section Ring

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B]

/-- Reversing a twisted commutator: `A Z - s Z A = w` gives `Z A - s⁻¹ A Z = -s⁻¹ w`. -/
lemma tripleSix_flip {A Z w : B} {s : k} (hs : s ≠ 0) (h : A * Z - s • (Z * A) = w) :
    Z * A - s⁻¹ • (A * Z) = (-s⁻¹) • w := by
  rw [← h, smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hs]
  module

end Ring

section Scalars

variable {k : Type*} [Field k] {q : k}

open BraidDiagonal

lemma tripleSix_cc_one (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0) :
    cc q (q ^ 3) 1 = q ^ 2 + 1 + q⁻¹ ^ 2 := by
  apply mul_left_cancel₀ hd
  rw [cc_mul hq hd 0]
  simp only [qInt, Finset.sum_range_succ, Finset.sum_range_zero]
  field_simp
  ring

lemma tripleSix_cc_two (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0) :
    cc q (q ^ 3) 2 = (q + q⁻¹) ^ 2 := by
  apply mul_left_cancel₀ hd
  rw [cc_mul hq hd 1]
  simp only [qInt, Finset.sum_range_succ, Finset.sum_range_zero]
  field_simp
  ring

lemma tripleSix_cc_three (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0) :
    cc q (q ^ 3) 3 = q ^ 2 + 1 + q⁻¹ ^ 2 := by
  apply mul_left_cancel₀ hd
  rw [cc_mul hq hd 2]
  simp only [qInt, Finset.sum_range_succ, Finset.sum_range_zero]
  field_simp
  ring

lemma tripleSix_qFactorial_three (hq : q ≠ 0) :
    qFactorial q 3 = (q ^ 2 + 1 + q⁻¹ ^ 2) * (q + q⁻¹) := by
  simp only [qFactorial, qInt, Finset.sum_range_succ, Finset.sum_range_zero]
  field_simp
  ring

lemma tripleSix_shift_zero : shift q (q ^ 3) 0 = (q ^ 3)⁻¹ := by
  simp [shift]

lemma tripleSix_shift_one (hq : q ≠ 0) : shift q (q ^ 3) 1 = q⁻¹ := by
  simp only [shift]
  field_simp

lemma tripleSix_shift_two (hq : q ≠ 0) : shift q (q ^ 3) 2 = q := by
  simp only [shift]
  field_simp

lemma tripleSix_shift_three (hq : q ≠ 0) : shift q (q ^ 3) 3 = q ^ 3 := by
  simp only [shift]
  field_simp

/-- The scalar of the first fixed-point chain: `a² [2]² = 1` for `a = ([3][2])⁻¹ [3]`. -/
lemma tripleSix_scalar_one {x y : k} (hx : x ≠ 0) (hy : y ≠ 0) :
    (y * x)⁻¹ * y * ((y * x)⁻¹ * y * x ^ 2) = 1 := by
  field_simp

/-- The scalar of the second fixed-point chain. -/
lemma tripleSix_scalar_two {x y : k} (hx : x ≠ 0) (hy : y ≠ 0) :
    (y * x)⁻¹ * ((y * x)⁻¹ * y * ((y * x)⁻¹ * y * x ^ 2)) *
      ((y * x)⁻¹ * y * x ^ 2 * y) = 1 := by
  field_simp

end Scalars

open BraidDiagonal

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  {i j : I} {S T : QuantumGroup R v →ₐ[k] QuantumGroup R v}
  (HS : HasBraidGeneratorImages i S) (HT : HasBraidGeneratorImages j T)
  (hij : i ≠ j) (h : D.cartanMatrix i j = -3) (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) (h3 : qFactorial (v ^ D.d i) 3 ≠ 0)

omit [DecidableEq I] [NeZero v] in
include h3 in
lemma tripleSix_qInt_ne (hv : v ≠ 0) :
    v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0 ∧ (v ^ D.d i) ^ 2 + 1 + (v ^ D.d i)⁻¹ ^ 2 ≠ 0 := by
  rw [tripleSix_qFactorial_three (pow_ne_zero _ hv)] at h3
  exact ⟨right_ne_zero_of_mul h3, left_ne_zero_of_mul h3⟩

omit [DecidableEq I] in
include h h' hq h3 in
/-- The long-node denominator `vⱼ - vⱼ⁻¹ = (vᵢ - vᵢ⁻¹)[3]ᵢ` is nonzero. -/
lemma tripleSix_sub_ne : v ^ D.d j - (v ^ D.d j)⁻¹ ≠ 0 := by
  have hv := NeZero.ne v
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  rw [parameter_eq_cube_of_triple_edge h h']
  have e : (v ^ D.d i) ^ 3 - ((v ^ D.d i) ^ 3)⁻¹ =
      (v ^ D.d i - (v ^ D.d i)⁻¹) * ((v ^ D.d i) ^ 2 + 1 + (v ^ D.d i)⁻¹ ^ 2) := by
    field_simp
    ring
  rw [e]
  exact mul_ne_zero hq (tripleSix_qInt_ne h3 hv).2

omit [DecidableEq I] [NeZero v] in
lemma tripleSix_negA (h : D.cartanMatrix i j = -3) : negA D i j = 3 := by
  simp [negA, h]

include hij h hq in
/-- The relations of the abstract diagonal computation at the short node, with `Q = q³`. -/
lemma tripleSix_hyp :
    Hyp (v ^ D.d i) ((v ^ D.d i) ^ 3) (v ^ D.d j - (v ^ D.d j)⁻¹)⁻¹
      (E R v i) (F R v i) (Kt R v i) (K R v (-ktilde R i)) (Kt R v j) (K R v (-ktilde R j))
      (E R v j) (F R v j) := by
  have H := braidDiagonal_hyp R v (NeZero.ne v) hij hq
  rwa [tripleSix_negA h] at H

include hij h hq in
/-- `X (n+1) Tᵢ(Eᵢ) - s(n+1)⁻¹ Tᵢ(Eᵢ) X (n+1) = cc (n+1) X n`. -/
lemma tripleSix_lowerE (n : ℕ) :
    X (v ^ D.d i) ((v ^ D.d i) ^ 3) (E R v i) (E R v j) (n + 1) * braidEi R i -
        (shift (v ^ D.d i) ((v ^ D.d i) ^ 3) (n + 1))⁻¹ •
          (braidEi R i * X (v ^ D.d i) ((v ^ D.d i) ^ 3) (E R v i) (E R v j) (n + 1)) =
      cc (v ^ D.d i) ((v ^ D.d i) ^ 3) (n + 1) •
        X (v ^ D.d i) ((v ^ D.d i) ^ 3) (E R v i) (E R v j) n := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hs : shift (v ^ D.d i) ((v ^ D.d i) ^ 3) (n + 1) ≠ 0 := by
    simp [shift, hq0]
  rw [tripleSix_flip hs ((tripleSix_hyp hij h hq).stepE (K_neg_mul_Kt i) n), smul_smul]
  congr 1
  field_simp

include HS hij h in
lemma tripleSix_S_Ej : S (E R v j) = (qFactorial (v ^ D.d i) 3)⁻¹ •
    X (v ^ D.d i) ((v ^ D.d i) ^ 3) (E R v i) (E R v j) 3 := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hc : (v ^ D.d i) ^ 3 * (v ^ D.d i * (v ^ D.d i) ^ 3)⁻¹ = (v ^ D.d i)⁻¹ := by
    field_simp
  rw [HS.map_E, ite_eq_right hij.symm, X_eq_serreAux hq0 (pow_ne_zero _ hq0), hc]
  unfold braidEj
  rw [tripleSix_negA h]

omit [NeZero v] in
include HS in
lemma tripleSix_S_Ei : S (E R v i) = braidEi R i := by
  rw [HS.map_E, ite_eq_left rfl]

omit [NeZero v] in
include HT hij in
lemma tripleSix_T_Ei : T (E R v i) = braidEj R v j i := by
  rw [HT.map_E, ite_eq_right hij]

omit [NeZero v] in
include HT in
lemma tripleSix_T_Ej : T (E R v j) = braidEi R j := by
  rw [HT.map_E, ite_eq_left rfl]

omit [NeZero v] in
include HT hij in
lemma tripleSix_T_X_succ (n : ℕ) :
    T (X (v ^ D.d i) ((v ^ D.d i) ^ 3) (E R v i) (E R v j) (n + 1)) =
      braidEj R v j i * T (X (v ^ D.d i) ((v ^ D.d i) ^ 3) (E R v i) (E R v j) n) -
        shift (v ^ D.d i) ((v ^ D.d i) ^ 3) n •
          (T (X (v ^ D.d i) ((v ^ D.d i) ^ 3) (E R v i) (E R v j) n) * braidEj R v j i) := by
  rw [X_succ, map_sub, map_mul, map_smul, map_mul, tripleSix_T_Ei HT hij]

include HT hij h h' hq h3 in
lemma tripleSix_T_X_one :
    T (X (v ^ D.d i) ((v ^ D.d i) ^ 3) (E R v i) (E R v j) 1) = E R v i := by
  rw [tripleSix_T_X_succ HT hij, X, tripleSix_T_Ej HT, tripleSix_shift_zero,
    ← parameter_eq_cube_of_triple_edge h h']
  exact degreeOne_braidEj_mul_braidEi_sub (R := R) h' (tripleSix_sub_ne h h' hq h3)

local notation "Xg" n:max => X (v ^ D.d i) ((v ^ D.d i) ^ 3) (E R v i) (E R v j) n

include HS hij h h' hq in
/-- `Tᵢ(Tⱼ Eᵢ) = [2]ᵢ⁻¹ X 2`, written with the unsimplified scalar `[3]ᵢ!⁻¹ cc 3`. -/
lemma tripleSix_S_Yv : S (braidEj R v j i) =
    ((qFactorial (v ^ D.d i) 3)⁻¹ * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3) • Xg 2 := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have L : (Xg 3) * braidEi R i -
      (shift (v ^ D.d i) ((v ^ D.d i) ^ 3) 3)⁻¹ • (braidEi R i * Xg 3) =
      cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3 • Xg 2 := tripleSix_lowerE hij h hq 2
  rw [tripleSix_shift_three hq0] at L
  rw [braidEj_eq_of_cartanMatrix_eq_neg_one h', parameter_eq_cube_of_triple_edge h h',
    map_sub, map_mul, map_smul, map_mul, tripleSix_S_Ej HS hij h, tripleSix_S_Ei HS]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [smul_comm, ← smul_sub, L, smul_smul]

include HS HT hij h h' hq h3 in
/-- `Tᵢ(Tⱼ(X 2)) = [2]ᵢ X 1`, with unsimplified scalar. -/
lemma tripleSix_S_TX2 : S (T (Xg 2)) =
    ((qFactorial (v ^ D.d i) 3)⁻¹ * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3 *
      cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 2) • Xg 1 := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have L : (Xg 2) * braidEi R i -
      (shift (v ^ D.d i) ((v ^ D.d i) ^ 3) 2)⁻¹ • (braidEi R i * Xg 2) =
      cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 2 • Xg 1 := tripleSix_lowerE hij h hq 1
  rw [tripleSix_shift_two hq0] at L
  rw [tripleSix_T_X_succ HT hij 1, tripleSix_T_X_one HT hij h h' hq h3, map_sub, map_mul,
    map_smul, map_mul, tripleSix_S_Yv HS hij h h' hq, tripleSix_S_Ei HS,
    tripleSix_shift_one hq0]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [smul_comm, ← smul_sub, L, smul_smul]

include HS HT hij h h' hq h3 in
/-- **First fixed-point identity**: `Tⱼ Tᵢ Tⱼ Tᵢ Tⱼ (Eᵢ) = Eᵢ`. -/
theorem tripleSix_Ei : T (S (T (S (T (E R v i))))) = E R v i := by
  have hv := NeZero.ne v
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  have hd : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0 := hq
  rw [tripleSix_T_Ei HT hij, tripleSix_S_Yv HS hij h h' hq, map_smul, map_smul,
    tripleSix_S_TX2 HS HT hij h h' hq h3, map_smul, map_smul, tripleSix_T_X_one HT hij h h' hq h3,
    smul_smul, tripleSix_qFactorial_three hq0, tripleSix_cc_three hq0 hd,
    tripleSix_cc_two hq0 hd, tripleSix_scalar_one (tripleSix_qInt_ne h3 hv).1
      (tripleSix_qInt_ne h3 hv).2, one_smul]

include HS HT hij h h' hq h3 in
/-- **Second fixed-point identity**: `Tᵢ Tⱼ Tᵢ Tⱼ Tᵢ (Eⱼ) = Eⱼ`. -/
theorem tripleSix_Ej : S (T (S (T (S (E R v j))))) = E R v j := by
  have hv := NeZero.ne v
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  have hd : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0 := hq
  have L : (Xg 1) * braidEi R i -
      (shift (v ^ D.d i) ((v ^ D.d i) ^ 3) 1)⁻¹ • (braidEi R i * Xg 1) =
      cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 1 • Xg 0 := tripleSix_lowerE hij h hq 0
  rw [tripleSix_shift_one hq0, inv_inv] at L
  have h1 : S (T (Xg 3)) =
      ((qFactorial (v ^ D.d i) 3)⁻¹ * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3 *
        ((qFactorial (v ^ D.d i) 3)⁻¹ * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3 *
          cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 2)) •
      ((Xg 2) * (Xg 1) - v ^ D.d i • ((Xg 1) * (Xg 2))) := by
    rw [tripleSix_T_X_succ HT hij 2, tripleSix_shift_two hq0, map_sub, map_mul, map_smul,
      map_mul, tripleSix_S_Yv HS hij h h' hq, tripleSix_S_TX2 HS HT hij h h' hq h3]
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
    module
  have h2 : S (T ((Xg 2) * (Xg 1) - v ^ D.d i • ((Xg 1) * (Xg 2)))) =
      ((qFactorial (v ^ D.d i) 3)⁻¹ * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3 *
        cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 2 * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 1) •
        E R v j := by
    rw [map_sub, map_mul, map_smul, map_mul, tripleSix_T_X_one HT hij h h' hq h3, map_sub,
      map_mul, map_smul, map_mul, tripleSix_S_TX2 HS HT hij h h' hq h3, tripleSix_S_Ei HS]
    simp only [smul_mul_assoc, mul_smul_comm]
    rw [smul_comm, ← smul_sub, L, smul_smul]
    rfl
  rw [tripleSix_S_Ej HS hij h]
  simp only [map_smul]
  rw [h1]
  simp only [map_smul]
  rw [h2, smul_smul, smul_smul]
  convert one_smul k (E R v j) using 2
  rw [tripleSix_qFactorial_three hq0, tripleSix_cc_three hq0 hd, tripleSix_cc_two hq0 hd,
    tripleSix_cc_one hq0 hd]
  exact tripleSix_scalar_two (tripleSix_qInt_ne h3 hv).1 (tripleSix_qInt_ne h3 hv).2

/-! ### The negative chains -/

local notation "Yg" n:max => X (v ^ D.d i) ((v ^ D.d i) ^ 3) (F R v i) (F R v j) n

include hij h hq in
/-- `Y (n+1) Tᵢ(Fᵢ) - s(n+1)⁻¹ Tᵢ(Fᵢ) Y (n+1) = s(n+1)⁻¹ s(n) cc (n+1) Y n`. -/
lemma tripleSix_lowerF (n : ℕ) :
    (Yg (n + 1)) * braidFi R i -
        (shift (v ^ D.d i) ((v ^ D.d i) ^ 3) (n + 1))⁻¹ • (braidFi R i * Yg (n + 1)) =
      ((shift (v ^ D.d i) ((v ^ D.d i) ^ 3) (n + 1))⁻¹ *
        (shift (v ^ D.d i) ((v ^ D.d i) ^ 3) n * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) (n + 1))) •
        Yg n := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hs : shift (v ^ D.d i) ((v ^ D.d i) ^ 3) (n + 1) ≠ 0 := by
    simp [shift, hq0]
  rw [tripleSix_flip hs ((tripleSix_hyp hij h hq).stepF (K_neg_mul_Kt i) n), smul_smul]
  congr 1
  ring

include HS hij h in
lemma tripleSix_S_Fj : S (F R v j) =
    ((qFactorial (v ^ D.d i) 3)⁻¹ * (-1) ^ 3 * (v ^ D.d i) ^ 3) • Yg 3 := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hc : (v ^ D.d i) ^ 3 * (v ^ D.d i * (v ^ D.d i) ^ 3)⁻¹ = (v ^ D.d i)⁻¹ := by
    field_simp
  rw [HS.map_F, ite_eq_right hij.symm, X_eq_serreAux hq0 (pow_ne_zero _ hq0), hc]
  unfold braidFj
  rw [tripleSix_negA h]

omit [NeZero v] in
include HS in
lemma tripleSix_S_Fi : S (F R v i) = braidFi R i := by
  rw [HS.map_F, ite_eq_left rfl]

omit [NeZero v] in
include HT hij in
lemma tripleSix_T_Fi : T (F R v i) = braidFj R v j i := by
  rw [HT.map_F, ite_eq_right hij]

omit [NeZero v] in
include HT in
lemma tripleSix_T_Fj : T (F R v j) = braidFi R j := by
  rw [HT.map_F, ite_eq_left rfl]

omit [NeZero v] in
include HT hij in
lemma tripleSix_T_Y_succ (n : ℕ) :
    T (Yg (n + 1)) = braidFj R v j i * T (Yg n) -
      shift (v ^ D.d i) ((v ^ D.d i) ^ 3) n • (T (Yg n) * braidFj R v j i) := by
  rw [X_succ, map_sub, map_mul, map_smul, map_mul, tripleSix_T_Fi HT hij]

include HT hij h h' hq h3 in
lemma tripleSix_T_Y_one : T (Yg 1) = (-((v ^ D.d i) ^ 3)⁻¹) • F R v i := by
  have hv := NeZero.ne v
  have hj0 : v ^ D.d j ≠ 0 := pow_ne_zero _ hv
  have hc := congrArg (chevalley R v)
    (degreeOne_braidEj_mul_braidEi_sub (R := R) h' (tripleSix_sub_ne h h' hq h3))
  simp only [map_sub, map_mul, map_smul, chevalley_E,
    chevalley_braidEj_of_cartanMatrix_eq_neg_one hv h', chevalley_braidEi hv,
    smul_mul_assoc, mul_smul_comm, smul_smul] at hc
  rw [tripleSix_T_Y_succ HT hij 0, X, tripleSix_T_Fj HT, tripleSix_shift_zero,
    ← parameter_eq_cube_of_triple_edge h h', ← hc]
  match_scalars <;> field_simp

include HS hij h h' hq in
/-- `Tᵢ(Tⱼ Fᵢ)`, up to the factor `-vⱼ`: `Tᵢ(Tⱼ(Fᵢ)) = cF (-(q [3])) Y 2`. -/
lemma tripleSix_S_Wg : S (braidFj R v j i) =
    ((qFactorial (v ^ D.d i) 3)⁻¹ * (-1) ^ 3 * (v ^ D.d i) ^ 3 *
      -(v ^ D.d i * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3)) • Yg 2 := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have L : braidFi R i * Yg 3 - shift (v ^ D.d i) ((v ^ D.d i) ^ 3) 3 • ((Yg 3) * braidFi R i) =
      (-(shift (v ^ D.d i) ((v ^ D.d i) ^ 3) 2 * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3)) • Yg 2 :=
    (tripleSix_hyp hij h hq).stepF (K_neg_mul_Kt i) 2
  rw [tripleSix_shift_three hq0, tripleSix_shift_two hq0] at L
  rw [braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h',
    parameter_eq_cube_of_triple_edge h h', map_sub, map_mul, map_smul, map_mul,
    tripleSix_S_Fi HS, tripleSix_S_Fj HS hij h]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [smul_comm, ← smul_sub, L, smul_smul]

include HS HT hij h h' hq h3 in
lemma tripleSix_S_TY2 : S (T (Yg 2)) =
    (-((v ^ D.d i) ^ 3)⁻¹ * ((qFactorial (v ^ D.d i) 3)⁻¹ * (-1) ^ 3 * (v ^ D.d i) ^ 3 *
      -(v ^ D.d i * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3)) *
      ((v ^ D.d i)⁻¹ * ((v ^ D.d i)⁻¹ * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 2))) • Yg 1 := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have L : (Yg 2) * braidFi R i -
      (shift (v ^ D.d i) ((v ^ D.d i) ^ 3) 2)⁻¹ • (braidFi R i * Yg 2) =
      ((shift (v ^ D.d i) ((v ^ D.d i) ^ 3) 2)⁻¹ *
        (shift (v ^ D.d i) ((v ^ D.d i) ^ 3) 1 * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 2)) •
        Yg 1 := tripleSix_lowerF hij h hq 1
  rw [tripleSix_shift_two hq0, tripleSix_shift_one hq0] at L
  rw [tripleSix_T_Y_succ HT hij 1, tripleSix_T_Y_one HT hij h h' hq h3, tripleSix_shift_one hq0]
  simp only [map_sub, map_mul, map_smul]
  rw [tripleSix_S_Wg HS hij h h' hq, tripleSix_S_Fi HS]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  linear_combination (norm := module) (-((v ^ D.d i) ^ 3)⁻¹ *
    ((qFactorial (v ^ D.d i) 3)⁻¹ * (-1) ^ 3 * (v ^ D.d i) ^ 3 *
      -(v ^ D.d i * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3))) • L

include HS HT hij h h' hq h3 in
/-- **First negative fixed-point identity**: `Tⱼ Tᵢ Tⱼ Tᵢ Tⱼ (Fᵢ) = Fᵢ`. -/
theorem tripleSix_Fi : T (S (T (S (T (F R v i))))) = F R v i := by
  have hv := NeZero.ne v
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  have hd : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0 := hq
  rw [tripleSix_T_Fi HT hij, tripleSix_S_Wg HS hij h h' hq]
  simp only [map_smul]
  rw [tripleSix_S_TY2 HS HT hij h h' hq h3]
  simp only [map_smul]
  rw [tripleSix_T_Y_one HT hij h h' hq h3, smul_smul, smul_smul]
  convert one_smul k (F R v i) using 2
  rw [tripleSix_qFactorial_three hq0, tripleSix_cc_three hq0 hd, tripleSix_cc_two hq0 hd]
  obtain ⟨hx, hy⟩ := tripleSix_qInt_ne h3 hv
  generalize v ^ D.d i + (v ^ D.d i)⁻¹ = x at hx ⊢
  generalize (v ^ D.d i) ^ 2 + 1 + (v ^ D.d i)⁻¹ ^ 2 = y at hy ⊢
  generalize v ^ D.d i = q at hq0 ⊢
  field_simp

include HS HT hij h h' hq h3 in
/-- **Second negative fixed-point identity**: `Tᵢ Tⱼ Tᵢ Tⱼ Tᵢ (Fⱼ) = Fⱼ`. -/
theorem tripleSix_Fj : S (T (S (T (S (F R v j))))) = F R v j := by
  have hv := NeZero.ne v
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  have hd : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0 := hq
  have L : (Yg 1) * braidFi R i -
      (shift (v ^ D.d i) ((v ^ D.d i) ^ 3) 1)⁻¹ • (braidFi R i * Yg 1) =
      ((shift (v ^ D.d i) ((v ^ D.d i) ^ 3) 1)⁻¹ *
        (shift (v ^ D.d i) ((v ^ D.d i) ^ 3) 0 * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 1)) •
        Yg 0 := tripleSix_lowerF hij h hq 0
  rw [tripleSix_shift_one hq0, tripleSix_shift_zero, inv_inv] at L
  have h1 : S (T (Yg 3)) =
      ((qFactorial (v ^ D.d i) 3)⁻¹ * (-1) ^ 3 * (v ^ D.d i) ^ 3 *
        -(v ^ D.d i * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3) *
        (-((v ^ D.d i) ^ 3)⁻¹ * ((qFactorial (v ^ D.d i) 3)⁻¹ * (-1) ^ 3 * (v ^ D.d i) ^ 3 *
          -(v ^ D.d i * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3)) *
          ((v ^ D.d i)⁻¹ * ((v ^ D.d i)⁻¹ * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 2)))) •
      ((Yg 2) * (Yg 1) - v ^ D.d i • ((Yg 1) * (Yg 2))) := by
    rw [tripleSix_T_Y_succ HT hij 2, tripleSix_shift_two hq0, map_sub, map_mul, map_smul,
      map_mul, tripleSix_S_Wg HS hij h h' hq, tripleSix_S_TY2 HS HT hij h h' hq h3]
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
    module
  have h2 : S (T ((Yg 2) * (Yg 1) - v ^ D.d i • ((Yg 1) * (Yg 2)))) =
      (-((v ^ D.d i) ^ 3)⁻¹ * (-((v ^ D.d i) ^ 3)⁻¹ *
        ((qFactorial (v ^ D.d i) 3)⁻¹ * (-1) ^ 3 * (v ^ D.d i) ^ 3 *
          -(v ^ D.d i * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3)) *
        ((v ^ D.d i)⁻¹ * ((v ^ D.d i)⁻¹ * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 2))) *
        (v ^ D.d i * (((v ^ D.d i) ^ 3)⁻¹ * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 1))) •
        F R v j := by
    simp only [map_sub, map_mul, map_smul]
    rw [tripleSix_T_Y_one HT hij h h' hq h3]
    simp only [map_smul]
    rw [tripleSix_S_TY2 HS HT hij h h' hq h3, tripleSix_S_Fi HS]
    have L' : (Yg 1) * braidFi R i - v ^ D.d i • (braidFi R i * Yg 1) =
        (v ^ D.d i * (((v ^ D.d i) ^ 3)⁻¹ * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 1)) • F R v j := L
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    linear_combination (norm := module) (-((v ^ D.d i) ^ 3)⁻¹ * (-((v ^ D.d i) ^ 3)⁻¹ *
        ((qFactorial (v ^ D.d i) 3)⁻¹ * (-1) ^ 3 * (v ^ D.d i) ^ 3 *
          -(v ^ D.d i * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 3)) *
        ((v ^ D.d i)⁻¹ * ((v ^ D.d i)⁻¹ * cc (v ^ D.d i) ((v ^ D.d i) ^ 3) 2)))) • L'
  rw [tripleSix_S_Fj HS hij h]
  simp only [map_smul]
  rw [h1]
  simp only [map_smul]
  rw [h2, smul_smul, smul_smul]
  convert one_smul k (F R v j) using 2
  rw [tripleSix_qFactorial_three hq0, tripleSix_cc_three hq0 hd, tripleSix_cc_two hq0 hd,
    tripleSix_cc_one hq0 hd]
  obtain ⟨hx, hy⟩ := tripleSix_qInt_ne h3 hv
  generalize v ^ D.d i + (v ^ D.d i)⁻¹ = x at hx ⊢
  generalize (v ^ D.d i) ^ 2 + 1 + (v ^ D.d i)⁻¹ ^ 2 = y at hy ⊢
  generalize v ^ D.d i = q at hq0 ⊢
  field_simp

/-! ### The length-six relation -/

section Lattice

omit [DecidableEq I] [NeZero v]

include h h' in
/-- The length-six reflection relation on the whole lattice. -/
theorem reflY_braid_six_of_triple_edge (μ : Y) :
    reflY R i (reflY R j (reflY R i (reflY R j (reflY R i (reflY R j μ))))) =
      reflY R j (reflY R i (reflY R j (reflY R i (reflY R j (reflY R i μ))))) := by
  simp only [reflY_apply, map_sub, map_zsmul, R.root_coroot, h, h', D.cartanMatrix_self]
  module

include h h' in
/-- `sⱼ sᵢ sⱼ sᵢ sⱼ` fixes `ĩ`. -/
theorem reflY_five_ktilde_of_triple_edge_left :
    reflY R j (reflY R i (reflY R j (reflY R i (reflY R j (ktilde R i))))) = ktilde R i := by
  have hc : reflY R j (reflY R i (reflY R j (reflY R i (reflY R j (R.coroot i))))) =
      R.coroot i := by
    simp only [reflY_apply, map_sub, map_zsmul, R.root_coroot, h, h', D.cartanMatrix_self]
    module
  simpa only [ktilde, map_nsmul] using congrArg (fun μ : Y ↦ D.d i • μ) hc

include h h' in
/-- `sᵢ sⱼ sᵢ sⱼ sᵢ` fixes `j̃`. -/
theorem reflY_five_ktilde_of_triple_edge_right :
    reflY R i (reflY R j (reflY R i (reflY R j (reflY R i (ktilde R j))))) = ktilde R j := by
  have hc : reflY R i (reflY R j (reflY R i (reflY R j (reflY R i (R.coroot j))))) =
      R.coroot j := by
    simp only [reflY_apply, map_sub, map_zsmul, R.root_coroot, h, h', D.cartanMatrix_self]
    module
  simpa only [ktilde, map_nsmul] using congrArg (fun μ : Y ↦ D.d j • μ) hc

end Lattice

include HS HT hij h h' hq h3 in
/-- The six-fold words agree on `Eᵢ`. -/
theorem tripleSix_six_Ei : S (T (S (T (S (T (E R v i)))))) = T (S (T (S (T (S (E R v i)))))) := by
  rw [tripleSix_Ei HS HT hij h h' hq h3, tripleSix_S_Ei HS]
  simp only [braidEi, map_neg, map_mul, Kt, HS.map_K, HT.map_K,
    tripleSix_Fi HS HT hij h h' hq h3, reflY_five_ktilde_of_triple_edge_left h h']

include HS HT hij h h' hq h3 in
/-- The six-fold words agree on `Eⱼ`. -/
theorem tripleSix_six_Ej : S (T (S (T (S (T (E R v j)))))) = T (S (T (S (T (S (E R v j)))))) := by
  rw [tripleSix_Ej HS HT hij h h' hq h3, tripleSix_T_Ej HT]
  simp only [braidEi, map_neg, map_mul, Kt, HS.map_K, HT.map_K,
    tripleSix_Fj HS HT hij h h' hq h3, reflY_five_ktilde_of_triple_edge_right h h']

include HS HT hij h h' hq h3 in
/-- The six-fold words agree on `Fᵢ`. -/
theorem tripleSix_six_Fi : S (T (S (T (S (T (F R v i)))))) = T (S (T (S (T (S (F R v i)))))) := by
  rw [tripleSix_Fi HS HT hij h h' hq h3, tripleSix_S_Fi HS]
  simp only [braidFi, map_neg, map_mul, HS.map_K, HT.map_K, map_neg,
    tripleSix_Ei HS HT hij h h' hq h3, reflY_five_ktilde_of_triple_edge_left h h']

include HS HT hij h h' hq h3 in
/-- The six-fold words agree on `Fⱼ`. -/
theorem tripleSix_six_Fj : S (T (S (T (S (T (F R v j)))))) = T (S (T (S (T (S (F R v j)))))) := by
  rw [tripleSix_Fj HS HT hij h h' hq h3, tripleSix_T_Fj HT]
  simp only [braidFi, map_neg, map_mul, HS.map_K, HT.map_K,
    tripleSix_Ej HS HT hij h h' hq h3, reflY_five_ktilde_of_triple_edge_right h h']

include HS HT hij h h' hq h3 in
/-- **The length-six braid relation for `G₂`** for any algebra endomorphisms with Lusztig's
generator formulas at the two nodes of an exact two-node datum with entries `(-3, -1)`:
`Tᵢ Tⱼ Tᵢ Tⱼ Tᵢ Tⱼ = Tⱼ Tᵢ Tⱼ Tᵢ Tⱼ Tᵢ`. Only `v ≠ 0`, `vᵢ - vᵢ⁻¹ ≠ 0` and `[3]ᵢ! ≠ 0` are
assumed. -/
theorem HasBraidGeneratorImages.six_braid_of_triple_edge (hall : ∀ l, l = i ∨ l = j) :
    S.comp (T.comp (S.comp (T.comp (S.comp T)))) =
      T.comp (S.comp (T.comp (S.comp (T.comp S)))) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · rcases hall l with rfl | rfl
    · exact tripleSix_six_Ei HS HT hij h h' hq h3
    · exact tripleSix_six_Ej HS HT hij h h' hq h3
  · rcases hall l with rfl | rfl
    · exact tripleSix_six_Fi HS HT hij h h' hq h3
    · exact tripleSix_six_Fj HS HT hij h h' hq h3
  · simp only [AlgHom.comp_apply, HS.map_K, HT.map_K, reflY_braid_six_of_triple_edge h h']

include hij h h' hq h3 in
/-- The length-six relation for the general braid automorphisms `braidEquiv` at the two nodes
of an exact `G₂` datum (whatever transformed-Serre proofs they were built from). -/
theorem braidEquiv_braid_six_of_triple_edge (hall : ∀ l, l = i ∨ l = j)
    (hgi : BraidGeneric D v i) (hSi : TransformedSerre R v i)
    (hgj : BraidGeneric D v j) (hSj : TransformedSerre R v j) :
    braidEquiv hgi hSi * braidEquiv hgj hSj * braidEquiv hgi hSi * braidEquiv hgj hSj *
        braidEquiv hgi hSi * braidEquiv hgj hSj =
      braidEquiv hgj hSj * braidEquiv hgi hSi * braidEquiv hgj hSj * braidEquiv hgi hSi *
        braidEquiv hgj hSj * braidEquiv hgi hSi := by
  have H := (braidHom_hasBraidGeneratorImages hgi hSi).six_braid_of_triple_edge
    (braidHom_hasBraidGeneratorImages hgj hSj) hij h h' hq h3 hall
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun H x

/-- **The length-six braid relation for `G₂`**: for an exact two-node datum with entries
`aᵢⱼ = -3`, `aⱼᵢ = -1`, the automorphisms `Tᵢ = tripleEdgeBraidEquiv` (short node) and
`Tⱼ = tripleEdgeOtherBraidEquiv` (long node) satisfy `Tᵢ Tⱼ Tᵢ Tⱼ Tᵢ Tⱼ = Tⱼ Tᵢ Tⱼ Tᵢ Tⱼ Tᵢ`.
The hypotheses are those of the two constructions: `v ≠ 0`, `vᵢ - vᵢ⁻¹ ≠ 0`, `[3]ᵢ! ≠ 0`,
`vᵢ⁴ + 1 ≠ 0` and `vⱼ² + 1 ≠ 0` (the relation itself only uses the first three). -/
theorem tripleEdgeBraidEquiv_braid_six (hall : ∀ l, l = i ∨ l = j)
    (h4 : (v ^ D.d i) ^ 4 + 1 ≠ 0) (h2 : (v ^ D.d j) ^ 2 + 1 ≠ 0) :
    let Ti := tripleEdgeBraidEquiv (R := R) hij hall h h' hq h3 h4
    let Tj := tripleEdgeOtherBraidEquiv (R := R) hij.symm (fun l ↦ (hall l).symm) h' h
      (tripleSix_sub_ne h h' hq h3) h2
    Ti * Tj * Ti * Tj * Ti * Tj = Tj * Ti * Tj * Ti * Tj * Ti :=
  braidEquiv_braid_six_of_triple_edge hij h h' hq h3 hall _ _ _ _

end QuantumGroup
