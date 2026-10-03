/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.HigherSerreReverse
import LieLean.Algebra.QuantumGroup.BraidAction.Isolated
import LieLean.Algebra.QuantumGroup.BraidAction.TripleEdgeRelation
import LieLean.Algebra.QuantumGroup.PBW.RankTwoA2

/-!
# Root vectors of the rank-two quantum groups lie in `U⁺`

Let `{i, j}` be a two-node Cartan datum of finite type and let `S = Tᵢ`, `T = Tⱼ` be algebra
endomorphisms of `U = U_v(𝔤)` with Lusztig's generator formulas (`HasBraidGeneratorImages`;
e.g. the automorphisms `braidEquivOfGeneric`). Along the reduced expression `sᵢ sⱼ sᵢ ⋯` of the
longest element `w₀` of the Weyl group, the root vectors are
`E_{β₁} = Eᵢ, E_{β₂} = Tᵢ(Eⱼ), E_{β₃} = TᵢTⱼ(Eᵢ), …` ([Jan] 8.21,
[Lus] 40.1.1, 40.1.3). We prove that every root vector lies in `U⁺`, the subalgebra generated
by the `Eₗ`,
for the types `A₁ × A₁`, `A₂`, `B₂` and `G₂` (the index of `U⁺` is `Algebra.adjoin k (range E)`),
with explicit formulas in terms of the twisted commutators
`X 0 = Eⱼ`, `X (n+1) = Eᵢ X n - q^{2n} Q⁻¹ X n Eᵢ` (`BraidDiagonal.X`, `q = vᵢ`, `Q = q^{-aᵢⱼ}`).

For `B₂` we also obtain the fixed-point identity `TᵢTⱼTᵢ(Eⱼ) = Eⱼ` structurally, from the
lowering identities `BraidDiagonal.Hyp.stepE` (as was done for `G₂` in `TripleEdgeRelation.lean`).

## Main results

* `QuantumGroup.a1a1_rootVector_two`, `QuantumGroup.a2_rootVectors_mem_adjoin`: types `A₁ × A₁`
  and `A₂`.
* `QuantumGroup.b2_rootVector_two`, `b2_rootVector_three`, `b2_rootVector_four`,
  `QuantumGroup.b2_rootVectors_mem_adjoin`: type `B₂` (`aᵢⱼ = -2`, `aⱼᵢ = -1`), assuming
  `v ≠ 0`, `vᵢ - vᵢ⁻¹ ≠ 0` and `[2]ᵢ! ≠ 0`.
* `QuantumGroup.g2_rootVectors_mem_adjoin`: type `G₂` (`aᵢⱼ = -3`, `aⱼᵢ = -1`), assuming `v ≠ 0`,
  `vᵢ - vᵢ⁻¹ ≠ 0` and `[3]ᵢ! ≠ 0`.

The PBW basis itself (spanning and linear independence of the ordered monomials) is proved for
`A₂` in `RankTwoA2.lean` and for `B₂` in `RankTwoB2.lean`; for `G₂` it is not proved.

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, §8.18–8.24.
* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §39.2, §39.4, §40.1–40.2.

The computations are our own reconstruction from the lowering identities of the repository.
-/

noncomputable section

namespace QuantumGroup

open BraidDiagonal

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k}
  {i j : I} {S T : QuantumGroup R v →ₐ[k] QuantumGroup R v}

lemma E_mem_adjoin (l : I) : E R v l ∈ Algebra.adjoin k (Set.range (E R v)) :=
  Algebra.subset_adjoin ⟨l, rfl⟩

/-- The twisted commutators `X n` of `Eᵢ` with `Eⱼ` lie in `U⁺`. -/
lemma X_mem_adjoin (q Q : k) (n : ℕ) :
    X q Q (E R v i) (E R v j) n ∈ Algebra.adjoin k (Set.range (E R v)) := by
  induction n with
  | zero => exact E_mem_adjoin j
  | succ n ih =>
    rw [X_succ]
    exact sub_mem (mul_mem (E_mem_adjoin i) ih)
      (Subalgebra.smul_mem _ (mul_mem ih (E_mem_adjoin i)) _)

/-! ### Types `A₁ × A₁` and `A₂` -/

/-- Type `A₁ × A₁`: the second root vector `Tᵢ(Eⱼ)` is `Eⱼ`. -/
theorem a1a1_rootVector_two (hij : i ≠ j) (h : D.cartanMatrix i j = 0)
    (HS : HasBraidGeneratorImages i S) : S (E R v j) = E R v j := by
  rw [HS.map_E, ite_eq_right hij.symm, braidEj_eq_of_cartanMatrix_eq_zero h]

/-- Type `A₂`: the root vectors `Tᵢ(Eⱼ)` and `TᵢTⱼ(Eᵢ)` lie in `U⁺`. -/
theorem a2_rootVectors_mem_adjoin [NeZero v] (HS : HasBraidGeneratorImages i S)
    (HT : HasBraidGeneratorImages j T) (hij : i ≠ j) (h : D.cartanMatrix i j = -1)
    (h' : D.cartanMatrix j i = -1) (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    S (E R v j) ∈ Algebra.adjoin k (Set.range (E R v)) ∧
      S (T (E R v i)) ∈ Algebra.adjoin k (Set.range (E R v)) := by
  refine ⟨?_, ?_⟩
  · rw [a2_rootVector_two hij HS, braidEj_eq_of_cartanMatrix_eq_neg_one h]
    exact sub_mem (mul_mem (E_mem_adjoin i) (E_mem_adjoin j))
      (Subalgebra.smul_mem _ (mul_mem (E_mem_adjoin j) (E_mem_adjoin i)) _)
  · rw [a2_rootVector_three HS HT hij h h' hq]
    exact E_mem_adjoin j

/-! ### Type `B₂` -/

section B2

section Scalars

variable {q : k}

lemma b2_shift_zero : BraidDiagonal.shift q (q ^ 2) 0 = (q ^ 2)⁻¹ := by
  simp [BraidDiagonal.shift]

lemma b2_shift_one (hq : q ≠ 0) : BraidDiagonal.shift q (q ^ 2) 1 = 1 := by
  simp only [BraidDiagonal.shift]
  field_simp

lemma b2_shift_two (hq : q ≠ 0) : BraidDiagonal.shift q (q ^ 2) 2 = q ^ 2 := by
  simp only [BraidDiagonal.shift]
  field_simp

lemma b2_qFactorial_two (hq : q ≠ 0) : qFactorial q 2 = q + q⁻¹ := by
  simp only [qFactorial, qInt, Finset.sum_range_succ, Finset.sum_range_zero]
  field_simp
  ring

lemma b2_cc_one (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0) : cc q (q ^ 2) 1 = q + q⁻¹ := by
  apply mul_left_cancel₀ hd
  rw [cc_mul hq hd 0]
  simp only [qInt, Finset.sum_range_succ, Finset.sum_range_zero]
  field_simp
  ring

lemma b2_cc_two (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0) : cc q (q ^ 2) 2 = q + q⁻¹ := by
  apply mul_left_cancel₀ hd
  rw [cc_mul hq hd 1]
  simp only [qInt, Finset.sum_range_succ, Finset.sum_range_zero]
  field_simp
  ring

end Scalars

variable [NeZero v] (HS : HasBraidGeneratorImages i S) (HT : HasBraidGeneratorImages j T)
  (hij : i ≠ j) (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) (h2 : qFactorial (v ^ D.d i) 2 ≠ 0)

local notation "Xb" n:max => X (v ^ D.d i) ((v ^ D.d i) ^ 2) (E R v i) (E R v j) n

omit [DecidableEq I] [NeZero v] in
lemma b2_negA (h : D.cartanMatrix i j = -2) : negA D i j = 2 := by
  simp [negA, h]

omit [DecidableEq I] in
include h h' hq h2 in
/-- The long-node denominator `vⱼ - vⱼ⁻¹ = (vᵢ - vᵢ⁻¹)[2]ᵢ` is nonzero. -/
lemma b2_sub_ne : v ^ D.d j - (v ^ D.d j)⁻¹ ≠ 0 := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  rw [parameter_eq_square_of_double_edge h h']
  rw [b2_qFactorial_two hq0] at h2
  have e : (v ^ D.d i) ^ 2 - ((v ^ D.d i) ^ 2)⁻¹ =
      (v ^ D.d i - (v ^ D.d i)⁻¹) * (v ^ D.d i + (v ^ D.d i)⁻¹) := by
    field_simp
    ring
  rw [e]
  exact mul_ne_zero hq h2

include hij h hq in
/-- `X (n+1) Tᵢ(Eᵢ) - s(n+1)⁻¹ Tᵢ(Eᵢ) X (n+1) = cc (n+1) X n` at a double edge. -/
lemma b2_lowerE (n : ℕ) :
    (Xb (n + 1)) * braidEi R i -
        (BraidDiagonal.shift (v ^ D.d i) ((v ^ D.d i) ^ 2) (n + 1))⁻¹ •
          (braidEi R i * Xb (n + 1)) =
      cc (v ^ D.d i) ((v ^ D.d i) ^ 2) (n + 1) • Xb n := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hs : BraidDiagonal.shift (v ^ D.d i) ((v ^ D.d i) ^ 2) (n + 1) ≠ 0 := by
    simp [BraidDiagonal.shift, hq0]
  have H := braidDiagonal_hyp R v (NeZero.ne v) hij hq
  rw [b2_negA h] at H
  rw [tripleSix_flip hs (H.stepE (K_neg_mul_Kt i) n), smul_smul]
  congr 1
  field_simp

include HS hij h in
/-- The second root vector: `Tᵢ(Eⱼ) = [2]ᵢ!⁻¹ X 2`. -/
theorem b2_rootVector_two : S (E R v j) = (qFactorial (v ^ D.d i) 2)⁻¹ • Xb 2 := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hc : (v ^ D.d i) ^ 2 * (v ^ D.d i * (v ^ D.d i) ^ 2)⁻¹ = (v ^ D.d i)⁻¹ := by
    field_simp
  rw [HS.map_E, ite_eq_right hij.symm, X_eq_serreAux hq0 (pow_ne_zero _ hq0), hc]
  unfold braidEj
  rw [b2_negA h]

include HS HT hij h h' hq in
/-- The third root vector: `TᵢTⱼ(Eᵢ) = [2]ᵢ!⁻¹ cc 2 · X 1`. -/
theorem b2_rootVector_three : S (T (E R v i)) =
    ((qFactorial (v ^ D.d i) 2)⁻¹ * cc (v ^ D.d i) ((v ^ D.d i) ^ 2) 2) • Xb 1 := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have L : (Xb 2) * braidEi R i -
      (BraidDiagonal.shift (v ^ D.d i) ((v ^ D.d i) ^ 2) 2)⁻¹ • (braidEi R i * Xb 2) =
      cc (v ^ D.d i) ((v ^ D.d i) ^ 2) 2 • Xb 1 := b2_lowerE hij h hq 1
  rw [b2_shift_two hq0] at L
  rw [HT.map_E, ite_eq_right hij, braidEj_eq_of_cartanMatrix_eq_neg_one h',
    parameter_eq_square_of_double_edge h h', map_sub, map_mul, map_smul, map_mul,
    b2_rootVector_two HS hij h, HS.map_E, ite_eq_left rfl]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [smul_comm, ← smul_sub, L, smul_smul]

include HT hij h h' hq h2 in
lemma b2_T_X_one : T (Xb 1) = E R v i := by
  rw [X_succ (n := 0), map_sub, map_mul, map_smul, map_mul, HT.map_E, ite_eq_right hij, X,
    HT.map_E,
    ite_eq_left rfl, b2_shift_zero, ← parameter_eq_square_of_double_edge h h']
  exact degreeOne_braidEj_mul_braidEi_sub (R := R) h' (b2_sub_ne h h' hq h2)

include HS HT hij h h' hq h2 in
/-- The fourth root vector is `TᵢTⱼTᵢ(Eⱼ) = Eⱼ` ([Jan] 8.20). -/
theorem b2_rootVector_four : S (T (S (E R v j))) = E R v j := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have L : (Xb 1) * braidEi R i -
      (BraidDiagonal.shift (v ^ D.d i) ((v ^ D.d i) ^ 2) 1)⁻¹ • (braidEi R i * Xb 1) =
      cc (v ^ D.d i) ((v ^ D.d i) ^ 2) 1 • Xb 0 := b2_lowerE hij h hq 0
  rw [b2_shift_one hq0, inv_one] at L
  rw [b2_rootVector_two HS hij h, map_smul, map_smul, X_succ (n := 1), map_sub, map_mul,
    map_smul, map_mul, b2_T_X_one HT hij h h' hq h2, map_sub, map_mul, map_smul, map_mul,
    b2_rootVector_three HS HT hij h h' hq, HS.map_E, ite_eq_left rfl, b2_shift_one hq0]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [smul_comm, ← smul_sub, L, smul_smul, smul_smul, b2_qFactorial_two hq0,
    b2_cc_one hq0 hq, b2_cc_two hq0 hq]
  rw [b2_qFactorial_two hq0] at h2
  rw [inv_mul_cancel₀ h2, mul_one, inv_mul_cancel₀ h2, one_smul]
  rfl

include HS HT hij h h' hq h2 in
/-- **Type `B₂`**: all four root vectors `Eᵢ, Tᵢ(Eⱼ), TᵢTⱼ(Eᵢ), TᵢTⱼTᵢ(Eⱼ)` lie in `U⁺`. -/
theorem b2_rootVectors_mem_adjoin :
    E R v i ∈ Algebra.adjoin k (Set.range (E R v)) ∧
      S (E R v j) ∈ Algebra.adjoin k (Set.range (E R v)) ∧
      S (T (E R v i)) ∈ Algebra.adjoin k (Set.range (E R v)) ∧
      S (T (S (E R v j))) ∈ Algebra.adjoin k (Set.range (E R v)) := by
  refine ⟨E_mem_adjoin i, ?_, ?_, ?_⟩
  · rw [b2_rootVector_two HS hij h]
    exact Subalgebra.smul_mem _ (X_mem_adjoin _ _ 2) _
  · rw [b2_rootVector_three HS HT hij h h' hq]
    exact Subalgebra.smul_mem _ (X_mem_adjoin _ _ 1) _
  · rw [b2_rootVector_four HS HT hij h h' hq h2]
    exact E_mem_adjoin j

end B2

/-! ### Type `G₂` -/

section G2

variable [NeZero v] (HS : HasBraidGeneratorImages i S) (HT : HasBraidGeneratorImages j T)
  (hij : i ≠ j) (h : D.cartanMatrix i j = -3) (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) (h3 : qFactorial (v ^ D.d i) 3 ≠ 0)

include HS HT hij h h' hq h3 in
/-- **Type `G₂`**: all six root vectors
`Eᵢ, Tᵢ(Eⱼ), TᵢTⱼ(Eᵢ), TᵢTⱼTᵢ(Eⱼ), TᵢTⱼTᵢTⱼ(Eᵢ), TᵢTⱼTᵢTⱼTᵢ(Eⱼ)` lie in `U⁺`. Explicitly they
are nonzero multiples of `Eᵢ, X 3, X 2, X 2 X 1 - vᵢ X 1 X 2, X 1, Eⱼ` (`tripleSix_S_Ej`,
`tripleSix_S_Yv`, `tripleSix_S_TX2`, `tripleSix_Ej`). -/
theorem g2_rootVectors_mem_adjoin :
    E R v i ∈ Algebra.adjoin k (Set.range (E R v)) ∧
      S (E R v j) ∈ Algebra.adjoin k (Set.range (E R v)) ∧
      S (T (E R v i)) ∈ Algebra.adjoin k (Set.range (E R v)) ∧
      S (T (S (E R v j))) ∈ Algebra.adjoin k (Set.range (E R v)) ∧
      S (T (S (T (E R v i)))) ∈ Algebra.adjoin k (Set.range (E R v)) ∧
      S (T (S (T (S (E R v j))))) ∈ Algebra.adjoin k (Set.range (E R v)) := by
  refine ⟨E_mem_adjoin i, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tripleSix_S_Ej HS hij h]
    exact Subalgebra.smul_mem _ (X_mem_adjoin _ _ 3) _
  · rw [tripleSix_T_Ei HT hij, tripleSix_S_Yv HS hij h h' hq]
    exact Subalgebra.smul_mem _ (X_mem_adjoin _ _ 2) _
  · rw [tripleSix_S_Ej HS hij h, map_smul, map_smul, tripleSix_T_X_succ HT hij 2, map_sub,
      map_mul, map_smul, map_mul, tripleSix_S_Yv HS hij h h' hq,
      tripleSix_S_TX2 HS HT hij h h' hq h3]
    refine Subalgebra.smul_mem _ (sub_mem (mul_mem ?_ ?_) (Subalgebra.smul_mem _
      (mul_mem ?_ ?_) _)) _ <;>
      exact Subalgebra.smul_mem _ (X_mem_adjoin _ _ _) _
  · rw [tripleSix_T_Ei HT hij, tripleSix_S_Yv HS hij h h' hq, map_smul, map_smul,
      tripleSix_S_TX2 HS HT hij h h' hq h3]
    exact Subalgebra.smul_mem _ (Subalgebra.smul_mem _ (X_mem_adjoin (R := R) _ _ 1) _) _
  · rw [tripleSix_Ej HS HT hij h h' hq h3]
    exact E_mem_adjoin j

end G2

end QuantumGroup
