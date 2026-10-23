/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Frobenius.Modified

/-!
# The quantum Frobenius homomorphism `Fr : _R U̇ → _R U̇*`

**[Lus] 35.1.9**: for an `𝒜'`-algebra `S` satisfying [Lus] 35.1.2 (a) there is a unique
homomorphism of `S`-algebras `Fr : _S U̇ → _S U̇*` with `Fr(Eᵢ^{(n)} 1_ζ) = Eᵢ^{(n/lᵢ)} 1_ζ`,
`Fr(Fᵢ^{(n)} 1_ζ) = Fᵢ^{(n/lᵢ)} 1_ζ` if `lᵢ ∣ n` and `ζ ∈ X*`, `0` otherwise, and `Fr(1_ζ) = 1_ζ`
for `ζ ∈ X*`, `0` otherwise. Here `_S U̇ = S ⊗_𝒜 𝒜U̇` and `U̇` is non-unital, so `Fr` is a
homomorphism of non-unital `S`-algebras.

## Main results

* `Modified.frobA_mul`: `Fr : 𝒜U̇ → _S U̇*` (`Frobenius/Modified.lean`) is multiplicative.
* `Modified.frobR`: `Fr : _S U̇ → _S U̇*`, with values `frobR_oneA`, `frobR_eA`, `frobR_fA`.
* `Modified.eq_frobR`: uniqueness.

## Proof

Our argument. `𝒜U̇` is spanned by the `x⁻ 1_ζ x'⁺` with `x, x'` monomials in divided powers
([Lus] 23.2.2), so it suffices to check `Fr(u v) = Fr(u) Fr(v)` for `u` a generator `1_ζ`,
`Eᵢ^{(n)} 1_ζ`, `Fᵢ^{(n)} 1_ζ` of `𝒜U̇` and `v = x⁻ 1_ζ x'⁺`. For `Fᵢ^{(n)}` and `1_ζ` this is
the multiplicativity of `Fr` on `f`. For `Eᵢ^{(n)}` one commutes `Eᵢ^{(n)}` past `Fⱼ^{(m)}` by
[Lus] 23.1.3; for `i = j` the Gaussian binomials `[a; t]ᵢ` that appear vanish in `𝒜'` unless
`lᵢ ∣ t`, and `[lᵢ a; lᵢ t]ᵢ = [a; t]` there ([Lus] 34.1.2, 35.1.5).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.1.3, 23.2.2, 34.1.2,
  35.1.2, 35.1.5, 35.1.9.
-/

open LieLean LusztigF
open scoped TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

attribute [local instance] neZero_ratFunc_X
attribute [local instance] Modified.laurentAlgebraK Modified.laurentAlgebraU
  Modified.laurentTowerU

namespace Modified

section Frobenius

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) {l l' : ℕ} (hl0 : 0 < l) (hl' : l' = 2 * l ∨ (Odd l ∧ l' = l))
  (hA : ∀ i j, i ≠ j → 2 ≤ D.frobOrder l j → ∀ a : ℕ, D.cartanMatrix i j = -a →
    a < D.frobOrder l i)
  (S : Type*) [CommRing S] [Algebra 𝒜 S] [Algebra (CyclotomicQuotient l') S]
  [IsScalarTower 𝒜 (CyclotomicQuotient l') S]

local notation "Fr" => frobA R hl0 hl' hA S

open Classical in
lemma frobA_eA_mul_fA_of_ne_index (i j : I) (n m : ℕ) {μ ν : Y →+ ℤ}
    (hμ : μ ≠ ν + m • -R.root j) :
    frobA R hl0 hl' hA S (eA R i n μ * fA R j m ν) =
      frobA R hl0 hl' hA S (eA R i n μ) * frobA R hl0 hl' hA S (fA R j m ν) := by
  rw [eA_mul_fA_of_ne_index i j n m hμ, map_zero, frobA_eA, frobA_fA]
  by_cases h1 : μ ∈ R.frobWeights l ∧ D.frobOrder l i ∣ n
  · by_cases h2 : ν ∈ R.frobWeights l ∧ D.frobOrder l j ∣ m
    · have h : R.frobWt l μ ≠
          R.frobWt l ν + (m / D.frobOrder l j) • -(R.frobRootDatum hl0).root j :=
        fun h ↦ hμ (by
          rwa [← R.frobWt_add_nsmul_neg_root hl0 j h2.2 h2.1,
            R.frobWt_inj h1.1 ((R.add_nsmul_neg_root_mem_iff hl0 j h2.2).2 h2.1)] at h)
      simp only [h1, h2, and_self, ↓reduceIte, tmul_one_mul_tmul_one,
        eA_mul_fA_of_ne_index (R := R.frobRootDatum hl0) i j _ _ h, TensorProduct.tmul_zero]
    · simp only [h2, ↓reduceIte, mul_zero]
  · simp only [h1, ↓reduceIte, zero_mul]

lemma frobA_fA_mul_eA (j : I) (m : ℕ) (μ : Y →+ ℤ) (i : I) (n : ℕ) (ν : Y →+ ℤ) :
    frobA R hl0 hl' hA S (fA R j m μ * eA R i n ν) =
      frobA R hl0 hl' hA S (fA R j m μ) * frobA R hl0 hl' hA S (eA R i n ν) := by
  rw [eA_eq_triT, frobA_fA_mul_triT]

omit [Finite I] in
lemma tmul_eA_mul_fA_of_ne {i j : I} (hij : i ≠ j) (n m : ℕ)
    (ν : (R.frobWeights l →+ ℤ) →+ ℤ) :
    (1 : S) ⊗ₜ[𝒜] eA (R.frobRootDatum hl0) i n (ν + m • -(R.frobRootDatum hl0).root j) *
        (1 : S) ⊗ₜ[𝒜] fA (R.frobRootDatum hl0) j m ν =
      (1 : S) ⊗ₜ[𝒜] fA (R.frobRootDatum hl0) j m (ν + n • (R.frobRootDatum hl0).root i) *
        (1 : S) ⊗ₜ[𝒜] eA (R.frobRootDatum hl0) i n ν := by
  rw [tmul_one_mul_tmul_one, tmul_one_mul_tmul_one, eA_mul_fA_of_ne hij]

open Classical in
lemma frobA_eA_mul_fA_of_ne {i j : I} (hij : i ≠ j) (n m : ℕ) (ν : Y →+ ℤ) :
    frobA R hl0 hl' hA S (eA R i n (ν + m • -R.root j) * fA R j m ν) =
      frobA R hl0 hl' hA S (eA R i n (ν + m • -R.root j)) *
        frobA R hl0 hl' hA S (fA R j m ν) := by
  rw [eA_mul_fA_of_ne hij, frobA_fA_mul_eA, frobA_fA, frobA_eA, frobA_eA, frobA_fA]
  by_cases hν : ν ∈ R.frobWeights l
  · by_cases hn : D.frobOrder l i ∣ n
    · by_cases hm : D.frobOrder l j ∣ m
      · simp only [(R.add_nsmul_root_mem_iff hl0 i hn).2 hν,
          (R.add_nsmul_neg_root_mem_iff hl0 j hm).2 hν, hν, hn, hm, and_self, ↓reduceIte,
          R.frobWt_add_nsmul_root hl0 i hn hν, R.frobWt_add_nsmul_neg_root hl0 j hm hν]
        exact (tmul_eA_mul_fA_of_ne R hl0 S hij _ _ _).symm
      · simp only [hm, and_false, ↓reduceIte, zero_mul, mul_zero]
    · simp only [hn, and_false, ↓reduceIte, zero_mul, mul_zero]
  · simp only [hν, false_and, ↓reduceIte, mul_zero]

/-- `Fr(Eᵢ^{(n)} 1_μ Fⱼ^{(m)} 1_λ) = Fr(Eᵢ^{(n)} 1_μ) Fr(Fⱼ^{(m)} 1_λ)`. -/
lemma frobA_eA_mul_fA (i j : I) (n m : ℕ) (μ ν : Y →+ ℤ) :
    frobA R hl0 hl' hA S (eA R i n μ * fA R j m ν) =
      frobA R hl0 hl' hA S (eA R i n μ) * frobA R hl0 hl' hA S (fA R j m ν) := by
  by_cases hμ : μ = ν + m • -R.root j
  · subst hμ
    by_cases hij : i = j
    · subst hij
      exact frobA_eA_mul_fA_self R hl0 hl' hA S i n m ν
    · exact frobA_eA_mul_fA_of_ne R hl0 hl' hA S hij n m ν
  · exact frobA_eA_mul_fA_of_ne_index R hl0 hl' hA S i j n m hμ

/-- Multiplicativity against all of `𝒜U̇` follows from multiplicativity against the spanning
elements `F_w 1_λ E_{w'}`. -/
lemma frobA_mul_of_triT {x : aForm R}
    (h : ∀ ν w w', Fr (x * triT R ν w w') = Fr x * Fr (triT R ν w w')) (y : aForm R) :
    Fr (x * y) = Fr x * Fr y := by
  have hy : y ∈ Submodule.span 𝒜 {z | ∃ ν w w', z = triT R ν w w'} := mem_span_triA_thetaW y
  induction hy using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨ν, w, w', rfl⟩ := ha
    exact h ν w w'
  | zero => rw [mul_zero, map_zero, mul_zero]
  | add a b _ _ ha hb =>
    rw [mul_add, map_add, map_add, mul_add]
    exact congrArg₂ (· + ·) ha hb
  | smul c a _ ha =>
    rw [mul_smul_comm, map_smul, map_smul]
    exact (congrArg (c • ·) ha).trans (mul_smul_comm c _ _).symm

lemma frobA_oneA_mul (μ : Y →+ ℤ) (y : aForm R) : Fr (oneA R μ * y) = Fr (oneA R μ) * Fr y :=
  frobA_mul_of_triT R hl0 hl' hA S (fun ν w w' ↦ frobA_oneA_mul_triT R hl0 hl' hA S μ ν w w') y

lemma frobA_fA_mul (j : I) (m : ℕ) (μ : Y →+ ℤ) (y : aForm R) :
    Fr (fA R j m μ * y) = Fr (fA R j m μ) * Fr y :=
  frobA_mul_of_triT R hl0 hl' hA S
    (fun ν w w' ↦ frobA_fA_mul_triT R hl0 hl' hA S j m μ ν w w') y

/-- If `Fr(x T) = Fr(x) Fr(T)` for all `x` in a set closed under `Fr(Fⱼ^{(m)} 1_λ ·)`, ... the
form used below: from multiplicativity of `Eᵢ'^{(n')} 1_μ' ·` against `T`, that of
`Fⱼ^{(m)} 1_λ Eᵢ^{(n)} 1_μ ·` against `T`. -/
lemma frobA_fA_mul_eA_mul (j : I) (m : ℕ) (ν : Y →+ ℤ) (i : I) (n : ℕ) (μ : Y →+ ℤ)
    (T : aForm R) (hT : Fr (eA R i n μ * T) = Fr (eA R i n μ) * Fr T) :
    Fr (fA R j m ν * eA R i n μ * T) = Fr (fA R j m ν * eA R i n μ) * Fr T := by
  rw [mul_assoc]
  refine (frobA_fA_mul R hl0 hl' hA S j m ν _).trans ?_
  refine ((congrArg (Fr (fA R j m ν) * ·) hT).trans (mul_assoc _ _ _).symm).trans ?_
  exact congrArg (· * Fr T) (frobA_fA_mul R hl0 hl' hA S j m ν _).symm

lemma frobA_ite_smul_mul (p : Prop) [Decidable p] (c : 𝒜) (x T : aForm R)
    (h : Fr (x * T) = Fr x * Fr T) :
    Fr ((if p then c • x else 0) * T) = Fr (if p then c • x else 0) * Fr T := by
  split_ifs
  · simp only [smul_mul_assoc, map_smul]
    exact congrArg (c • ·) h
  · rw [zero_mul, map_zero, zero_mul]

/-- If `Fr(Eᵢ'^{(n')} 1_μ' T) = Fr(Eᵢ'^{(n')} 1_μ') Fr(T)` for all `i', n', μ'`, then
`Fr(Eᵢ^{(n)} 1_μ Fⱼ^{(m)} 1_λ T) = Fr(Eᵢ^{(n)} 1_μ Fⱼ^{(m)} 1_λ) Fr(T)`, by the commutation
formulas [Lus] 23.1.3. -/
lemma frobA_eA_mul_fA_mul (i j : I) (n m : ℕ) (μ ν : Y →+ ℤ) (T : aForm R)
    (hT : ∀ i' n' μ', Fr (eA R i' n' μ' * T) = Fr (eA R i' n' μ') * Fr T) :
    Fr (eA R i n μ * fA R j m ν * T) = Fr (eA R i n μ * fA R j m ν) * Fr T := by
  by_cases hμ : μ = ν + m • -R.root j
  swap
  · rw [eA_mul_fA_of_ne_index i j n m hμ, zero_mul, map_zero, zero_mul]
  subst hμ
  by_cases hij : i = j
  · subst hij
    rw [eA_mul_fA_self, Finset.sum_mul, map_sum, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ ↦ frobA_ite_smul_mul R hl0 hl' hA S _ _ _ T
      (frobA_fA_mul_eA_mul R hl0 hl' hA S _ _ _ _ _ _ T (hT _ _ _))
  · rw [eA_mul_fA_of_ne hij]
    exact frobA_fA_mul_eA_mul R hl0 hl' hA S _ _ _ _ _ _ T (hT _ _ _)

open Classical in
lemma frobA_eA_mul_triT_nil (i : I) (n : ℕ) (μ ν : Y →+ ℤ) (w' : List (I × ℕ)) :
    frobA R hl0 hl' hA S (eA R i n μ * triT R ν [] w') =
      frobA R hl0 hl' hA S (eA R i n μ) * frobA R hl0 hl' hA S (triT R ν [] w') := by
  rw [eA_mul_triT_nil, apply_ite (frobA R hl0 hl' hA S), map_zero, frobA_eA, frobA_triT,
    frobA_triT, frobDiv_cons, frobDivW_cons, frobDivW_nil]
  by_cases hn : D.frobOrder l i ∣ n
  swap
  · simp only [hn, false_and, and_false, ↓reduceIte, ite_self, zero_mul]
  by_cases hν : ν ∈ R.frobWeights l
  swap
  · simp only [(R.add_nsmul_root_mem_iff hl0 i hn), hν, false_and, ↓reduceIte, ite_self,
      mul_zero]
  by_cases hw' : FrobDiv D l w'
  swap
  · simp only [hw', and_false, ↓reduceIte, ite_self, mul_zero]
  by_cases hμ : μ ∈ R.frobWeights l
  swap
  · have : μ ≠ ν := fun h ↦ hμ (h ▸ hν)
    simp only [this, hμ, false_and, ↓reduceIte, zero_mul]
  simp only [(R.add_nsmul_root_mem_iff hl0 i hn), hn, hν, hw', hμ, frobDiv_nil, and_self,
    ↓reduceIte, tmul_one_mul_tmul_one, eA_mul_triT_nil, R.frobWt_add_nsmul_root hl0 i hn hν,
    R.frobWt_inj hμ hν]
  by_cases h : μ = ν
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, TensorProduct.tmul_zero]

lemma frobA_eA_mul_triT (i : I) (n : ℕ) (μ ν : Y →+ ℤ) (w w' : List (I × ℕ)) :
    Fr (eA R i n μ * triT R ν w w') = Fr (eA R i n μ) * Fr (triT R ν w w') := by
  induction w generalizing i n μ with
  | nil => exact frobA_eA_mul_triT_nil R hl0 hl' hA S i n μ ν w'
  | cons p w ih =>
    obtain ⟨j, m⟩ := p
    rw [triT_cons', ← mul_assoc]
    refine (frobA_eA_mul_fA_mul R hl0 hl' hA S i j n m μ _ _ ih).trans ?_
    refine (congrArg (· * Fr (triT R ν w w')) (frobA_eA_mul_fA R hl0 hl' hA S i j n m μ _)).trans ?_
    exact (mul_assoc _ _ _).trans
      (congrArg (Fr (eA R i n μ) * ·) (frobA_fA_mul R hl0 hl' hA S j m _ _).symm)

lemma frobA_eA_mul (i : I) (n : ℕ) (μ : Y →+ ℤ) (y : aForm R) :
    Fr (eA R i n μ * y) = Fr (eA R i n μ) * Fr y :=
  frobA_mul_of_triT R hl0 hl' hA S
    (fun ν w w' ↦ frobA_eA_mul_triT R hl0 hl' hA S i n μ ν w w') y

lemma frobA_add_mul {a b : aForm R} (ha : ∀ y, Fr (a * y) = Fr a * Fr y)
    (hb : ∀ y, Fr (b * y) = Fr b * Fr y) (y : aForm R) : Fr ((a + b) * y) = Fr (a + b) * Fr y := by
  rw [add_mul, map_add, map_add, add_mul]
  exact congrArg₂ (· + ·) (ha y) (hb y)

lemma frobA_mul_mul {a b : aForm R} (ha : ∀ y, Fr (a * y) = Fr a * Fr y)
    (hb : ∀ y, Fr (b * y) = Fr b * Fr y) (y : aForm R) : Fr (a * b * y) = Fr (a * b) * Fr y := by
  rw [mul_assoc]
  refine ((ha _).trans (congrArg (Fr a * ·) (hb y))).trans ?_
  exact (mul_assoc _ _ _).symm.trans (congrArg (· * Fr y) (ha b).symm)

lemma frobA_smul_mul (c : 𝒜) {a : aForm R} (ha : ∀ y, Fr (a * y) = Fr a * Fr y) (y : aForm R) :
    Fr ((c • a) * y) = Fr (c • a) * Fr y := by
  rw [smul_mul_assoc, map_smul, map_smul, smul_mul_assoc]
  exact congrArg (c • ·) (ha y)

lemma frobA_zero_mul (y : aForm R) : Fr (0 * y) = Fr 0 * Fr y := by
  rw [zero_mul, map_zero, zero_mul]

/-- `Fr : 𝒜U̇ → _S U̇*` is multiplicative. -/
theorem frobA_mul (x y : aForm R) : Fr (x * y) = Fr x * Fr y := by
  obtain ⟨x, hx⟩ := x
  revert y
  unfold aForm at hx
  induction hx using NonUnitalAlgebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨μ, rfl⟩ | ⟨i, n, μ, rfl | rfl⟩
    · exact frobA_oneA_mul R hl0 hl' hA S μ
    · exact frobA_eA_mul R hl0 hl' hA S i n μ
    · exact frobA_fA_mul R hl0 hl' hA S i n μ
  | add x x' hx hx' ih ih' =>
    exact frobA_add_mul R hl0 hl' hA S (a := ⟨x, hx⟩) (b := ⟨x', hx'⟩) ih ih'
  | zero => exact frobA_zero_mul R hl0 hl' hA S
  | mul x x' hx hx' ih ih' =>
    exact frobA_mul_mul R hl0 hl' hA S (a := ⟨x, hx⟩) (b := ⟨x', hx'⟩) ih ih'
  | smul c x hx ih => exact frobA_smul_mul R hl0 hl' hA S c (a := ⟨x, hx⟩) ih


section Unique

variable (φ : S ⊗[𝒜] aForm R →ₙₐ[S] S ⊗[𝒜] aForm (R.frobRootDatum hl0))

lemma eq_frobA_add {a b : aForm R} (ha : φ ((1 : S) ⊗ₜ a) = Fr a)
    (hb : φ ((1 : S) ⊗ₜ b) = Fr b) : φ ((1 : S) ⊗ₜ (a + b)) = Fr (a + b) := by
  rw [TensorProduct.tmul_add, map_add, map_add, ha, hb]

lemma eq_frobA_zero : φ ((1 : S) ⊗ₜ (0 : aForm R)) = Fr 0 := by
  rw [TensorProduct.tmul_zero, map_zero, map_zero]

lemma eq_frobA_mul {a b : aForm R} (ha : φ ((1 : S) ⊗ₜ a) = Fr a)
    (hb : φ ((1 : S) ⊗ₜ b) = Fr b) : φ ((1 : S) ⊗ₜ (a * b)) = Fr (a * b) := by
  rw [← tmul_one_mul_tmul_one, _root_.map_mul, ha, hb, frobA_mul]

lemma eq_frobA_smul (c : 𝒜) {a : aForm R} (ha : φ ((1 : S) ⊗ₜ a) = Fr a) :
    φ ((1 : S) ⊗ₜ (c • a)) = Fr (c • a) := by
  rw [TensorProduct.tmul_smul, ← algebraMap_smul S c, map_smul, algebraMap_smul, ha, map_smul]

end Unique

/-- `x ↦ φ(1 ⊗ x)` agrees with `Fr` on `𝒜U̇` when it is additive, `𝒜`-linear, multiplicative and
agrees with `Fr` on the generators `1_λ`, `Eᵢ^{(n)} 1_λ`, `Fᵢ^{(n)} 1_λ`. -/
lemma eq_frobA_of_forall (φ : S ⊗[𝒜] aForm R →ₙₐ[S] S ⊗[𝒜] aForm (R.frobRootDatum hl0))
    (h1 : ∀ μ, φ ((1 : S) ⊗ₜ oneA R μ) = Fr (oneA R μ))
    (hE : ∀ i n μ, φ ((1 : S) ⊗ₜ eA R i n μ) = Fr (eA R i n μ))
    (hF : ∀ i n μ, φ ((1 : S) ⊗ₜ fA R i n μ) = Fr (fA R i n μ)) (x : aForm R) :
    φ ((1 : S) ⊗ₜ x) = Fr x := by
  obtain ⟨x, hx⟩ := x
  unfold aForm at hx
  induction hx using NonUnitalAlgebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨μ, rfl⟩ | ⟨i, n, μ, rfl | rfl⟩
    · exact h1 μ
    · exact hE i n μ
    · exact hF i n μ
  | add x x' hx hx' ih ih' =>
    exact eq_frobA_add R hl0 hl' hA S φ (a := ⟨x, hx⟩) (b := ⟨x', hx'⟩) ih ih'
  | zero => exact eq_frobA_zero R hl0 hl' hA S φ
  | mul x x' hx hx' ih ih' =>
    exact eq_frobA_mul R hl0 hl' hA S φ (a := ⟨x, hx⟩) (b := ⟨x', hx'⟩) ih ih'
  | smul c x hx ih => exact eq_frobA_smul R hl0 hl' hA S φ c (a := ⟨x, hx⟩) ih


lemma frobR_mul_tmul (s t : S) (a b : aForm R) :
    LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) ((s ⊗ₜ[𝒜] a) * (t ⊗ₜ[𝒜] b)) =
      LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) (s ⊗ₜ[𝒜] a) *
        LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) (t ⊗ₜ[𝒜] b) :=
  (congrArg (LinearMap.liftBaseChange S (frobA R hl0 hl' hA S))
    (Algebra.TensorProduct.tmul_mul_tmul s t a b)).trans <|
    (congrArg ((s * t) • ·) (frobA_mul R hl0 hl' hA S a b)).trans
      (smul_mul_smul_comm s _ t _).symm

lemma frobR_mul_add_left (x x' y : S ⊗[𝒜] aForm R)
    (hx : LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) (x * y) =
      LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) x *
        LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) y)
    (hx' : LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) (x' * y) =
      LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) x' *
        LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) y) :
    LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) ((x + x') * y) =
      LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) (x + x') *
        LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) y :=
  (congrArg (LinearMap.liftBaseChange S (frobA R hl0 hl' hA S)) (add_mul x x' y)).trans <|
    ((LinearMap.liftBaseChange S (frobA R hl0 hl' hA S)).map_add (x * y) (x' * y)).trans <|
      (congrArg₂ (· + ·) hx hx').trans <| (add_mul _ _ _).symm.trans <|
        congrArg (· * LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) y)
          ((LinearMap.liftBaseChange S (frobA R hl0 hl' hA S)).map_add x x').symm

lemma frobR_mul_add_right (x y y' : S ⊗[𝒜] aForm R)
    (hy : LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) (x * y) =
      LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) x *
        LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) y)
    (hy' : LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) (x * y') =
      LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) x *
        LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) y') :
    LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) (x * (y + y')) =
      LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) x *
        LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) (y + y') :=
  (congrArg (LinearMap.liftBaseChange S (frobA R hl0 hl' hA S)) (mul_add x y y')).trans <|
    ((LinearMap.liftBaseChange S (frobA R hl0 hl' hA S)).map_add (x * y) (x * y')).trans <|
      (congrArg₂ (· + ·) hy hy').trans <| (mul_add _ _ _).symm.trans <|
        congrArg (LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) x * ·)
          ((LinearMap.liftBaseChange S (frobA R hl0 hl' hA S)).map_add y y').symm

lemma frobR_mul_aux (x y : S ⊗[𝒜] aForm R) :
    LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) (x * y) =
      LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) x *
        LinearMap.liftBaseChange S (frobA R hl0 hl' hA S) y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => exact frobR_mul_add_left R hl0 hl' hA S x x' y hx hx'
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => exact frobR_mul_add_right R hl0 hl' hA S _ y y' hy hy'
    | tmul t b => exact frobR_mul_tmul R hl0 hl' hA S s t a b

/-! ### `Fr` on `_S U̇` -/

/-- **[Lus] 35.1.9**: the quantum Frobenius homomorphism `Fr : _S U̇ → _S U̇*`, for an
`𝒜'`-algebra `S`, as a homomorphism of non-unital `S`-algebras. -/
def frobR : S ⊗[𝒜] aForm R →ₙₐ[S] S ⊗[𝒜] aForm (R.frobRootDatum hl0) where
  toFun := LinearMap.liftBaseChange S (frobA R hl0 hl' hA S)
  map_smul' := map_smul _
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := frobR_mul_aux R hl0 hl' hA S x y

lemma frobR_tmul (s : S) (x : aForm R) : frobR R hl0 hl' hA S (s ⊗ₜ x) = s • Fr x :=
  rfl

lemma frobR_one_tmul (x : aForm R) : frobR R hl0 hl' hA S ((1 : S) ⊗ₜ x) = Fr x := by
  rw [frobR_tmul, one_smul]

open Classical in
/-- **[Lus] 35.1.9**: `Fr(1_λ) = 1_{λ*}` if `λ ∈ X*`, and `0` otherwise. -/
theorem frobR_oneA (μ : Y →+ ℤ) :
    frobR R hl0 hl' hA S ((1 : S) ⊗ₜ oneA R μ) =
      if μ ∈ R.frobWeights l then (1 : S) ⊗ₜ oneA (R.frobRootDatum hl0) (R.frobWt l μ)
      else 0 := by
  rw [frobR_one_tmul, frobA_oneA]

open Classical in
/-- **[Lus] 35.1.9**: `Fr(Eᵢ^{(n)} 1_λ) = Eᵢ^{(n/lᵢ)} 1_{λ*}` if `lᵢ ∣ n` and `λ ∈ X*`, and `0`
otherwise. -/
theorem frobR_eA (i : I) (n : ℕ) (μ : Y →+ ℤ) :
    frobR R hl0 hl' hA S ((1 : S) ⊗ₜ eA R i n μ) =
      if μ ∈ R.frobWeights l ∧ D.frobOrder l i ∣ n then
        (1 : S) ⊗ₜ eA (R.frobRootDatum hl0) i (n / D.frobOrder l i) (R.frobWt l μ) else 0 := by
  rw [frobR_one_tmul, frobA_eA]

open Classical in
/-- **[Lus] 35.1.9**: `Fr(Fᵢ^{(n)} 1_λ) = Fᵢ^{(n/lᵢ)} 1_{λ*}` if `lᵢ ∣ n` and `λ ∈ X*`, and `0`
otherwise. -/
theorem frobR_fA (i : I) (n : ℕ) (μ : Y →+ ℤ) :
    frobR R hl0 hl' hA S ((1 : S) ⊗ₜ fA R i n μ) =
      if μ ∈ R.frobWeights l ∧ D.frobOrder l i ∣ n then
        (1 : S) ⊗ₜ fA (R.frobRootDatum hl0) i (n / D.frobOrder l i) (R.frobWt l μ) else 0 := by
  rw [frobR_one_tmul, frobA_fA]

/-- `Fr` is the unique homomorphism of non-unital `S`-algebras `_S U̇ → _S U̇*` with the values of
[Lus] 35.1.9 on the `1_λ`, `Eᵢ^{(n)} 1_λ` and `Fᵢ^{(n)} 1_λ`. -/
theorem eq_frobR (φ : S ⊗[𝒜] aForm R →ₙₐ[S] S ⊗[𝒜] aForm (R.frobRootDatum hl0))
    (h1 : ∀ μ, φ ((1 : S) ⊗ₜ oneA R μ) = frobR R hl0 hl' hA S ((1 : S) ⊗ₜ oneA R μ))
    (hE : ∀ i n μ, φ ((1 : S) ⊗ₜ eA R i n μ) = frobR R hl0 hl' hA S ((1 : S) ⊗ₜ eA R i n μ))
    (hF : ∀ i n μ, φ ((1 : S) ⊗ₜ fA R i n μ) = frobR R hl0 hl' hA S ((1 : S) ⊗ₜ fA R i n μ)) :
    φ = frobR R hl0 hl' hA S := by
  have key : ∀ x : aForm R, φ ((1 : S) ⊗ₜ x) = frobR R hl0 hl' hA S ((1 : S) ⊗ₜ x) := fun x ↦ by
    rw [frobR_one_tmul]
    refine eq_frobA_of_forall R hl0 hl' hA S φ (fun μ ↦ ?_) (fun i n μ ↦ ?_) (fun i n μ ↦ ?_) x
    · rw [h1, frobR_one_tmul]
    · rw [hE, frobR_one_tmul]
    · rw [hF, frobR_one_tmul]
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    rw [← mul_one s, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul, key]
  | add z z' hz hz' =>
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) hz hz'

end Frobenius

end Modified

end LieLean.QuantumGroup
