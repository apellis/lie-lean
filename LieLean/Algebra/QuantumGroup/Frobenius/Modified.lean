/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Frobenius.HomomorphismGeneral
import LieLean.Algebra.QuantumGroup.Frobenius.RootDatum
import LieLean.Algebra.QuantumGroup.Modified.TriangularMap

/-!
# The quantum Frobenius homomorphism `Fr : _R U̇ → _R U̇*`: construction

Let `l ≥ 1`, let `l'` be `2l`, or `l` if `l` is odd, let `𝒜' = 𝒜 / (f_{l'})` ([Lus] 35.1.3), and
let `R` be an `𝒜'`-algebra satisfying [Lus] 35.1.2 (a). Let `(Y*, X*)` be the root datum of
[Lus] 2.2.5 (`LusztigCartanDatum.RootDatum.frobRootDatum`), with `U̇*` its modified quantum group.
[Lus] 35.1.9 asserts that there is a unique `R`-algebra homomorphism `Fr : _R U̇ → _R U̇*` with
`Fr(Eᵢ^{(n)} 1_ζ) = Eᵢ^{(n/lᵢ)} 1_ζ` and `Fr(Fᵢ^{(n)} 1_ζ) = Fᵢ^{(n/lᵢ)} 1_ζ` if `lᵢ ∣ n` and
`ζ ∈ X*`, and `0` otherwise, and `Fr(1_ζ) = 1_ζ` for `ζ ∈ X*`, `0` otherwise.

This file constructs `Fr` on `𝒜U̇` as an `𝒜`-linear map `𝒜U̇ → _R U̇*`, using the triangular
description `𝒜U̇ = ⊕_ζ 𝒜f⁻ 1_ζ 𝒜f⁺` ([Lus] 23.2.2) and `Fr : 𝒜f → _R f*`
(`QuantumGroup.frobGeneral`, [Lus] 35.1.7): `x⁻ 1_ζ x'⁺ ↦ Fr(x)⁻ 1_ζ Fr(x')⁺` for `ζ ∈ X*`, `0`
otherwise. Multiplicativity and the extension to `_R U̇ = R ⊗ 𝒜U̇` are in
`Frobenius/ModifiedMul.lean`.

The library indexes the idempotents of `U̇*` by `Y* →+ ℤ` (the weights of `(Y*, X*)` in the
library's convention `X = Hom(Y, ℤ)`); `ζ ∈ X*` is sent to its evaluation `frobWt ζ`, which is
injective on `X*` (`frobEval_injective`). For `Y` free of finite rank this is Lusztig's `X*`.

## Main definitions

* `LusztigCartanDatum.RootDatum.frobWt`: `X* → Hom(Y*, ℤ)`.
* `Modified.oneA`, `Modified.eA`, `Modified.fA`: `1_ζ`, `Eᵢ^{(n)} 1_ζ`, `Fᵢ^{(n)} 1_ζ` in `𝒜U̇`.
* `Modified.frobA`: `Fr : 𝒜U̇ → _R U̇*`.

## Main results

* `Modified.frobA_oneA`, `Modified.frobA_fA`, `Modified.frobA_eA`: the values of `Fr`.
* `Modified.algebraMap_gaussBinom_mul_mul`: the Gaussian binomials `[lᵢ a; lᵢ t]ᵢ` in `𝒜'`
  ([Lus] 35.1.5 (a)).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 2.2.5, 23.2.2, 35.1.2,
  35.1.3, 35.1.5, 35.1.7, 35.1.9.
-/

open LieLean LusztigF
open scoped TensorProduct

noncomputable section

/-! ### The evaluation `X* → Hom(Y*, ℤ)` -/

namespace LusztigCartanDatum.RootDatum

variable {I Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum I} (R : D.RootDatum Y) (l : ℕ)

/-- `ζ ↦ (y ↦ y(ζ))`, `X* → Hom(Y*, ℤ)`. -/
def frobEval : R.frobWeights l →+ ((R.frobWeights l →+ ℤ) →+ ℤ) where
  toFun ζ :=
    { toFun := fun y ↦ y ζ
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

@[simp] lemma frobEval_apply (ζ : R.frobWeights l) (y : R.frobWeights l →+ ℤ) :
    R.frobEval l ζ y = y ζ := rfl

lemma frobEval_injective : Function.Injective (R.frobEval l) := by
  intro ζ η h
  refine Subtype.ext (AddMonoidHom.ext fun μ ↦ ?_)
  simpa using DFunLike.congr_fun h (R.frobDualHom l μ)

variable {l}

lemma frobEval_frobRoot (hl : 0 < l) (j : I) :
    R.frobEval l (R.frobRoot hl j) = (R.frobRootDatum hl).root j := rfl

variable (l) in
open Classical in
/-- The weight `λ ∈ X` seen in `Hom(Y*, ℤ)`: evaluation at `λ` for `λ ∈ X*`, and `0` otherwise. -/
def frobWt (ν : Y →+ ℤ) : (R.frobWeights l →+ ℤ) →+ ℤ :=
  if h : ν ∈ R.frobWeights l then R.frobEval l ⟨ν, h⟩ else 0

lemma frobWt_of_mem {ν : Y →+ ℤ} (h : ν ∈ R.frobWeights l) :
    R.frobWt l ν = R.frobEval l ⟨ν, h⟩ := by
  simp [frobWt, h]

lemma frobWt_add {ν μ : Y →+ ℤ} (hν : ν ∈ R.frobWeights l) (hμ : μ ∈ R.frobWeights l) :
    R.frobWt l (ν + μ) = R.frobWt l ν + R.frobWt l μ := by
  rw [R.frobWt_of_mem hν, R.frobWt_of_mem hμ, R.frobWt_of_mem (add_mem hν hμ), ← map_add]
  rfl

lemma frobWt_sub {ν μ : Y →+ ℤ} (hν : ν ∈ R.frobWeights l) (hμ : μ ∈ R.frobWeights l) :
    R.frobWt l (ν - μ) = R.frobWt l ν - R.frobWt l μ := by
  rw [R.frobWt_of_mem hν, R.frobWt_of_mem hμ, R.frobWt_of_mem (sub_mem hν hμ), ← map_sub]
  rfl

lemma frobWt_inj {ν μ : Y →+ ℤ} (hν : ν ∈ R.frobWeights l) (hμ : μ ∈ R.frobWeights l) :
    R.frobWt l ν = R.frobWt l μ ↔ ν = μ := by
  rw [R.frobWt_of_mem hν, R.frobWt_of_mem hμ, (R.frobEval_injective l).eq_iff, Subtype.mk.injEq]

/-- `n j' = (n/lⱼ) j*` for `lⱼ ∣ n`. -/
lemma nsmul_root_eq (hl : 0 < l) (j : I) {n : ℕ} (hn : D.frobOrder l j ∣ n) :
    n • R.root j = ((n / D.frobOrder l j : ℕ) • R.frobRoot hl j : R.frobWeights l) := by
  ext μ
  simp only [AddSubgroup.coe_nsmul, coe_frobRoot,
    AddMonoidHom.smul_apply, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  exact_mod_cast (Nat.div_mul_cancel hn).symm

lemma nsmul_root_mem (hl : 0 < l) (j : I) {n : ℕ} (hn : D.frobOrder l j ∣ n) :
    n • R.root j ∈ R.frobWeights l := by
  rw [R.nsmul_root_eq hl j hn]; exact SetLike.coe_mem _

lemma frobWt_nsmul_root (hl : 0 < l) (j : I) {n : ℕ} (hn : D.frobOrder l j ∣ n) :
    R.frobWt l (n • R.root j) = (n / D.frobOrder l j) • (R.frobRootDatum hl).root j := by
  rw [R.frobWt_of_mem (R.nsmul_root_mem hl j hn), ← frobEval_frobRoot, ← map_nsmul]
  congr 1
  exact Subtype.ext (R.nsmul_root_eq hl j hn)

lemma add_nsmul_root_mem_iff (hl : 0 < l) (j : I) {n : ℕ} (hn : D.frobOrder l j ∣ n)
    {μ : Y →+ ℤ} : μ + n • R.root j ∈ R.frobWeights l ↔ μ ∈ R.frobWeights l :=
  add_mem_cancel_right (R.nsmul_root_mem hl j hn)

lemma add_nsmul_neg_root_mem_iff (hl : 0 < l) (j : I) {n : ℕ} (hn : D.frobOrder l j ∣ n)
    {μ : Y →+ ℤ} : μ + n • -R.root j ∈ R.frobWeights l ↔ μ ∈ R.frobWeights l := by
  rw [smul_neg, ← sub_eq_add_neg]
  exact ⟨fun h ↦ by simpa using add_mem h (R.nsmul_root_mem hl j hn),
    fun h ↦ sub_mem h (R.nsmul_root_mem hl j hn)⟩

lemma frobWt_add_nsmul_root (hl : 0 < l) (j : I) {n : ℕ} (hn : D.frobOrder l j ∣ n)
    {μ : Y →+ ℤ} (hμ : μ ∈ R.frobWeights l) :
    R.frobWt l (μ + n • R.root j) =
      R.frobWt l μ + (n / D.frobOrder l j) • (R.frobRootDatum hl).root j := by
  rw [R.frobWt_add hμ (R.nsmul_root_mem hl j hn), R.frobWt_nsmul_root hl j hn]

lemma frobWt_add_nsmul_neg_root (hl : 0 < l) (j : I) {n : ℕ} (hn : D.frobOrder l j ∣ n)
    {μ : Y →+ ℤ} (hμ : μ ∈ R.frobWeights l) :
    R.frobWt l (μ + n • -R.root j) =
      R.frobWt l μ + (n / D.frobOrder l j) • -(R.frobRootDatum hl).root j := by
  rw [smul_neg, ← sub_eq_add_neg, R.frobWt_sub hμ (R.nsmul_root_mem hl j hn),
    R.frobWt_nsmul_root hl j hn, smul_neg, sub_eq_add_neg]

/-- `⟨i, λ⟩ = lᵢ ⟨i*, λ⟩` for `λ ∈ X*`. -/
lemma frobOrder_mul_frobWt_coroot (hl : 0 < l) (i : I) {μ : Y →+ ℤ}
    (hμ : μ ∈ R.frobWeights l) :
    (D.frobOrder l i : ℤ) * R.frobWt l μ ((R.frobRootDatum hl).coroot i) = μ (R.coroot i) := by
  rw [R.frobWt_of_mem hμ]
  exact R.frobOrder_mul_frobCoroot l i ⟨μ, hμ⟩

end LusztigCartanDatum.RootDatum

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

attribute [local instance] neZero_ratFunc_X
attribute [local instance] Modified.laurentAlgebraK Modified.laurentAlgebraU
  Modified.laurentTowerU


namespace Modified

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) {l : ℕ}

/-! ### Words divisible by the `lᵢ` -/

variable (D l) in
/-- All letters `(i, n)` of `w` have `lᵢ ∣ n`. -/
def FrobDiv (w : List (I × ℕ)) : Prop := ∀ p ∈ w, D.frobOrder l p.1 ∣ p.2

variable (D l) in
/-- `(i, n) ↦ (i, n/lᵢ)`. -/
def frobDivW (w : List (I × ℕ)) : List (I × ℕ) := w.map fun p ↦ (p.1, p.2 / D.frobOrder l p.1)

omit [DecidableEq I] in
@[simp] lemma frobDiv_nil : FrobDiv D l [] := fun _ h ↦ absurd h List.not_mem_nil

omit [DecidableEq I] in
lemma frobDiv_cons (p : I × ℕ) (w : List (I × ℕ)) :
    FrobDiv D l (p :: w) ↔ D.frobOrder l p.1 ∣ p.2 ∧ FrobDiv D l w :=
  List.forall_mem_cons

omit [DecidableEq I] in
@[simp] lemma frobDivW_nil : frobDivW D l [] = [] := rfl

omit [DecidableEq I] in
@[simp] lemma frobDivW_cons (p : I × ℕ) (w : List (I × ℕ)) :
    frobDivW D l (p :: w) = (p.1, p.2 / D.frobOrder l p.1) :: frobDivW D l w := rfl

omit [DecidableEq I] in
lemma wtW_mem_frobWeights (hl : 0 < l) {w : List (I × ℕ)} (hw : FrobDiv D l w) :
    wtW R w ∈ R.frobWeights l := by
  induction w with
  | nil => exact zero_mem _
  | cons p w ih =>
    rw [frobDiv_cons] at hw
    rw [wtW_cons]
    exact add_mem (R.nsmul_root_mem hl p.1 hw.1) (ih hw.2)

omit [DecidableEq I] in
lemma frobWt_wtW (hl : 0 < l) {w : List (I × ℕ)} (hw : FrobDiv D l w) :
    R.frobWt l (wtW R w) = wtW (R.frobRootDatum hl) (frobDivW D l w) := by
  induction w with
  | nil =>
    simp only [wtW, frobDivW_nil, List.map_nil, List.sum_nil, R.frobWt_of_mem (zero_mem _)]
    exact (R.frobEval l).map_zero
  | cons p w ih =>
    rw [frobDiv_cons] at hw
    rw [wtW_cons, frobDivW_cons, wtW_cons,
      R.frobWt_add (R.nsmul_root_mem hl p.1 hw.1) (wtW_mem_frobWeights R hl hw.2),
      R.frobWt_nsmul_root hl p.1 hw.1, ih hw.2]


omit [DecidableEq I] in
lemma sub_wtW_mem (hl : 0 < l) {ν : Y →+ ℤ} (hν : ν ∈ R.frobWeights l) {w : List (I × ℕ)}
    (hw : FrobDiv D l w) : ν - wtW R w ∈ R.frobWeights l :=
  sub_mem hν (wtW_mem_frobWeights R hl hw)

omit [DecidableEq I] in
lemma frobWt_sub_wtW (hl : 0 < l) {ν : Y →+ ℤ} (hν : ν ∈ R.frobWeights l) {w : List (I × ℕ)}
    (hw : FrobDiv D l w) :
    R.frobWt l (ν - wtW R w) = R.frobWt l ν - wtW (R.frobRootDatum hl) (frobDivW D l w) := by
  rw [R.frobWt_sub hν (wtW_mem_frobWeights R hl hw), frobWt_wtW R hl hw]

/-! ### Gaussian binomials in `𝒜'` ([Lus] 35.1.5) -/

section Coefficients

variable {I : Type*} (D : LusztigCartanDatum I) {l l' : ℕ} (hl0 : 0 < l)
  (hl' : l' = 2 * l ∨ (Odd l ∧ l' = l))

/-- The image of `vᵢ = v^{dᵢ}` in `𝒜'`. -/
def frobUnit (i : I) : (CyclotomicQuotient l')ˣ :=
  Units.map (algebraMap 𝒜 (CyclotomicQuotient l')).toMonoidHom (laurentTUnit (D.d i))

include hl0 hl' in
lemma frobUnit_pow_two_mul_eq_one_iff (i : I) (t : ℕ) :
    (frobUnit D (l' := l') i : CyclotomicQuotient l') ^ (2 * t) = 1 ↔ D.frobOrder l i ∣ t := by
  have := neZero_of_frobeniusLevel hl0 hl'
  have hT : (frobUnit D (l' := l') i : CyclotomicQuotient l') =
      algebraMap 𝒜 _ (LaurentPolynomial.T 1) ^ D.d i := by
    rw [← map_pow, LaurentPolynomial.T_pow, mul_one]; rfl
  rw [hT, ← pow_mul, ← (IsFractionRing.injective (CyclotomicQuotient l')
    (FractionRing (CyclotomicQuotient l'))).eq_iff, _root_.map_one, map_pow,
    ← IsScalarTower.algebraMap_apply, mul_comm (D.d i), mul_assoc,
    cyclotomicFraction_pow_two_mul_eq_one_iff hl', ← Int.natCast_dvd_natCast,
    ← Int.natCast_dvd_natCast (m := D.frobOrder l i), D.frobOrder_dvd_iff hl0, Nat.cast_mul]

include hl0 hl' in
/-- [Lus] 35.1.5 (b) in `𝒜'`: `[a; t]ᵢ = 0` for `lᵢ ∣ a`, `lᵢ ∤ t`. -/
lemma algebraMap_gaussBinom_eq_zero (i : I) {a : ℤ} (ha : (D.frobOrder l i : ℤ) ∣ a) {t : ℕ}
    (ht : ¬ D.frobOrder l i ∣ t) :
    algebraMap 𝒜 (CyclotomicQuotient l') (gaussBinom (laurentTUnit (D.d i)) a t) = 0 := by
  have := neZero_of_frobeniusLevel hl0 hl'
  rw [map_gaussBinom]
  exact gaussBinom_eq_zero_of_not_dvd
    ((frobUnit_pow_two_mul_eq_one_iff D hl0 hl' i _).2 dvd_rfl)
    (fun t h0 ht h ↦ Nat.not_dvd_of_pos_of_lt h0 ht
      ((frobUnit_pow_two_mul_eq_one_iff D hl0 hl' i t).1 h))
    (D.frobOrder_pos hl0 i) ha ht

include hl' in
/-- [Lus] 35.1.5 (a) in `𝒜'`: `[lᵢ a; lᵢ t]ᵢ = [a; t]ᵢ*`, with `vᵢ* = vᵢ^{lᵢ²}`. -/
lemma algebraMap_gaussBinom_mul_mul (i : I) (a : ℤ) (t : ℕ) :
    algebraMap 𝒜 (CyclotomicQuotient l')
        (gaussBinom (laurentTUnit (D.d i)) (D.frobOrder l i * a) (D.frobOrder l i * t)) =
      algebraMap 𝒜 (CyclotomicQuotient l')
        (gaussBinom (laurentTUnit ((D.frobenius hl0).d i)) a t) := by
  have := neZero_of_frobeniusLevel hl0 hl'
  rw [map_gaussBinom, map_gaussBinom]
  refine (gaussBinom_mul_mul_eq_pow
    ((frobUnit_pow_two_mul_eq_one_iff D hl0 hl' i _).2 dvd_rfl)
    (fun t h0 ht h ↦ Nat.not_dvd_of_pos_of_lt h0 ht
      ((frobUnit_pow_two_mul_eq_one_iff D hl0 hl' i t).1 h))
    (D.frobOrder_pos hl0 i) a t).trans ?_
  congr 1
  ext
  change algebraMap 𝒜 _ (LaurentPolynomial.T (D.d i)) ^ _ = algebraMap 𝒜 _ (LaurentPolynomial.T _)
  rw [← map_pow, LaurentPolynomial.T_pow, D.frobenius_d hl0]
  push_cast
  ring_nf

end Coefficients

/-! ### Generators of `𝒜U̇` as elements of `𝒜U̇` -/

section AForm

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y)

/-- `1_λ ∈ 𝒜U̇`. -/
def oneA (μ : Y →+ ℤ) : aForm R := ⟨one μ, one_mem_aForm μ⟩

/-- `Eᵢ^{(n)} 1_λ ∈ 𝒜U̇`. -/
def eA (i : I) (n : ℕ) (μ : Y →+ ℤ) : aForm R := ⟨divE R i n μ, divE_mem i n μ⟩

/-- `Fᵢ^{(n)} 1_λ ∈ 𝒜U̇`. -/
def fA (i : I) (n : ℕ) (μ : Y →+ ℤ) : aForm R := ⟨divF R i n μ, divF_mem i n μ⟩

variable {R}

lemma oneA_eq_triT (μ : Y →+ ℤ) : oneA R μ = triT R μ [] [] := Subtype.ext (one_eq_triT μ)

lemma fA_eq_triT (j : I) (m : ℕ) (μ : Y →+ ℤ) : fA R j m μ = triT R μ [(j, m)] [] :=
  Subtype.ext (divF_eq_triT j m μ)

lemma eA_eq_triT (i : I) (n : ℕ) (μ : Y →+ ℤ) :
    eA R i n μ = triT R (μ + n • R.root i) [] [(i, n)] :=
  Subtype.ext (divE_eq_triT i n μ)

open Classical in
lemma oneA_mul_triT (μ ν : Y →+ ℤ) (w w' : List (I × ℕ)) :
    oneA R μ * triT R ν w w' = if μ = ν - wtW R w then triT R ν w w' else 0 := by
  apply Subtype.ext
  rw [NonUnitalSubalgebra.coe_mul, oneA, one_mul_triT]
  split_ifs <;> rfl

open Classical in
lemma fA_mul_triT (j : I) (m : ℕ) (μ ν : Y →+ ℤ) (w w' : List (I × ℕ)) :
    fA R j m μ * triT R ν w w' = if μ = ν - wtW R w then triT R ν ((j, m) :: w) w' else 0 := by
  apply Subtype.ext
  rw [NonUnitalSubalgebra.coe_mul, fA, divF_mul_triT]
  split_ifs <;> rfl

open Classical in
lemma eA_mul_triT_nil (i : I) (n : ℕ) (μ ν : Y →+ ℤ) (w' : List (I × ℕ)) :
    eA R i n μ * triT R ν [] w' =
      if μ = ν then triT R (ν + n • R.root i) [] ((i, n) :: w') else 0 := by
  apply Subtype.ext
  rw [NonUnitalSubalgebra.coe_mul, eA, divE_mul_triT_nil]
  split_ifs <;> rfl

lemma triT_cons' (j : I) (m : ℕ) (ν : Y →+ ℤ) (w w' : List (I × ℕ)) :
    triT R ν ((j, m) :: w) w' = fA R j m (ν - wtW R w) * triT R ν w w' :=
  Subtype.ext (triT_cons j m ν w w')

omit [Finite I] in
lemma eA_mul_fA_of_ne_index (i j : I) (n m : ℕ) {μ ν : Y →+ ℤ} (h : μ ≠ ν + m • -R.root j) :
    eA R i n μ * fA R j m ν = 0 :=
  Subtype.ext (elt_mul_elt_of_ne h _ _)

omit [Finite I] in
lemma eA_mul_fA_of_ne {i j : I} (hij : i ≠ j) (n m : ℕ) (ν : Y →+ ℤ) :
    eA R i n (ν + m • -R.root j) * fA R j m ν = fA R j m (ν + n • R.root i) * eA R i n ν :=
  Subtype.ext (dE_mul_dF_of_ne hij n m ν)

omit [Finite I] in
/-- [Lus] 23.1.3 in `𝒜U̇`, with the coefficients `[⟨i, ν⟩ + n - m; t]ᵢ ∈ 𝒜`. -/
lemma eA_mul_fA_self (i : I) (n m : ℕ) (ν : Y →+ ℤ) :
    eA R i n (ν + m • -R.root i) * fA R i m ν =
      ∑ t ∈ Finset.range (n + 1), if t ≤ m then
        gaussBinom (laurentTUnit (D.d i)) (ν (R.coroot i) + n - m) t •
          (fA R i (m - t) (ν + (n - t) • R.root i) * eA R i (n - t) ν) else 0 := by
  apply Subtype.ext
  rw [NonUnitalSubalgebra.coe_mul]
  change dE R 𝕧 i n (ν + m • -R.root i) * dF R 𝕧 i m ν = _
  rw [dE_mul_dF (fun _ hn ↦ ratFunc_X_pow_ne_one hn), AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  split_ifs
  · rw [NonUnitalSubalgebra.coe_smul, laurent_smul,
      integralLaurentEval_gaussBinom _ (D.d_pos i)]
    rfl
  · rfl

end AForm

/-! ### `Fr` on `𝒜U̇` -/

section Frobenius

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) {l l' : ℕ} (hl0 : 0 < l) (hl' : l' = 2 * l ∨ (Odd l ∧ l' = l))
  (hA : ∀ i j, i ≠ j → 2 ≤ D.frobOrder l j → ∀ a : ℕ, D.cartanMatrix i j = -a →
    a < D.frobOrder l i)
  (S : Type*) [CommRing S] [Algebra 𝒜 S] [Algebra (CyclotomicQuotient l') S]
  [IsScalarTower 𝒜 (CyclotomicQuotient l') S]

/-- `x ↦ Fr(1 ⊗ x)`, `𝒜f → _S f*`. -/
def frobF : quotientIntegralForm D →ₗ[𝒜] S ⊗[𝒜] quotientIntegralForm (D.frobenius hl0) :=
  ((frobGeneral D hl0 hl' hA S).toLinearMap.restrictScalars 𝒜) ∘ₗ
    TensorProduct.mk 𝒜 S _ 1

lemma frobF_apply (x : quotientIntegralForm D) :
    frobF hl0 hl' hA S x = frobGeneral D hl0 hl' hA S ((1 : S) ⊗ₜ x) := rfl

open Classical in
/-- `Fr(θ_w) = θ_{w/l}` if all letters of `w` are divisible, and `0` otherwise. -/
lemma frobF_thetaW (w : List (I × ℕ)) :
    frobF hl0 hl' hA S (thetaW D w) =
      if FrobDiv D l w then (1 : S) ⊗ₜ thetaW (D.frobenius hl0) (frobDivW D l w) else 0 := by
  induction w with
  | nil =>
    rw [frobF_apply, thetaW_nil, ← Algebra.TensorProduct.one_def, _root_.map_one]
    simp [Algebra.TensorProduct.one_def]
  | cons p w ih =>
    rw [frobF_apply, thetaW_cons, ← one_mul (1 : S), ← Algebra.TensorProduct.tmul_mul_tmul,
      _root_.map_mul, frobGeneral_integralGenerator, ← frobF_apply, ih, frobValue, frobDiv_cons,
      frobDivW_cons, thetaW_cons]
    by_cases h1 : D.frobOrder l p.1 ∣ p.2 <;> by_cases h2 : FrobDiv D l w <;>
      simp [h1, h2, Algebra.TensorProduct.tmul_mul_tmul]

/-- The bilinear maps `(x, x') ↦ Fr(x)⁻ 1_{λ*} Fr(x')⁺` for `λ ∈ X*`, and `0` otherwise. -/
noncomputable def frobBil (ν : Y →+ ℤ) :
    quotientIntegralForm D →ₗ[𝒜] quotientIntegralForm D →ₗ[𝒜]
      S ⊗[𝒜] aForm (R.frobRootDatum hl0) :=
  open Classical in
  if ν ∈ R.frobWeights l then
    ((triS (R.frobRootDatum hl0) S (R.frobWt l ν)).restrictScalars₁₂ 𝒜 𝒜).compl₁₂
      (frobF hl0 hl' hA S) (frobF hl0 hl' hA S)
  else 0

/-- `Fr : 𝒜U̇ → _S U̇*`, `x⁻ 1_λ x'⁺ ↦ Fr(x)⁻ 1_{λ*} Fr(x')⁺` for `λ ∈ X*`, and `0` otherwise. -/
noncomputable def frobA : aForm R →ₗ[𝒜] S ⊗[𝒜] aForm (R.frobRootDatum hl0) :=
  (Finsupp.lsum ℕ fun ν ↦ TensorProduct.lift (frobBil R hl0 hl' hA S ν)) ∘ₗ
    (triSumEquiv R).symm.toLinearMap

lemma frobA_triSumEquiv (y : (Y →+ ℤ) →₀ quotientIntegralForm D ⊗[𝒜] quotientIntegralForm D) :
    frobA R hl0 hl' hA S (triSumEquiv R y) =
      Finsupp.lsum ℕ (fun ν ↦ TensorProduct.lift (frobBil R hl0 hl' hA S ν)) y :=
  congrArg (Finsupp.lsum ℕ fun ν ↦ TensorProduct.lift (frobBil R hl0 hl' hA S ν))
    ((triSumEquiv R).symm_apply_apply y)

lemma frobA_triA (ν : Y →+ ℤ) (x x' : quotientIntegralForm D) :
    frobA R hl0 hl' hA S (triA R ν x x') = frobBil R hl0 hl' hA S ν x x' := by
  rw [← triSumEquiv_single, frobA_triSumEquiv]
  exact (Finsupp.lsum_single ℕ _ ν _).trans (TensorProduct.lift.tmul _ _)

open Classical in
lemma frobA_triT (ν : Y →+ ℤ) (w w' : List (I × ℕ)) :
    frobA R hl0 hl' hA S (triT R ν w w') =
      if ν ∈ R.frobWeights l ∧ FrobDiv D l w ∧ FrobDiv D l w' then
        (1 : S) ⊗ₜ triT (R.frobRootDatum hl0) (R.frobWt l ν) (frobDivW D l w) (frobDivW D l w')
      else 0 := by
  rw [triT, frobA_triA, frobBil]
  by_cases hν : ν ∈ R.frobWeights l
  · simp only [hν, ↓reduceIte, true_and, LinearMap.compl₁₂_apply,
      LinearMap.restrictScalars₁₂_apply_apply, frobF_thetaW]
    by_cases h : FrobDiv D l w <;> by_cases h' : FrobDiv D l w' <;>
      simp [h, h', triS_tmul, triT]
  · simp [hν]

open Classical in
lemma frobA_oneA (μ : Y →+ ℤ) :
    frobA R hl0 hl' hA S (oneA R μ) =
      if μ ∈ R.frobWeights l then (1 : S) ⊗ₜ oneA (R.frobRootDatum hl0) (R.frobWt l μ) else 0 := by
  rw [oneA_eq_triT, frobA_triT, oneA_eq_triT]
  simp

open Classical in
lemma frobA_fA (j : I) (m : ℕ) (μ : Y →+ ℤ) :
    frobA R hl0 hl' hA S (fA R j m μ) =
      if μ ∈ R.frobWeights l ∧ D.frobOrder l j ∣ m then
        (1 : S) ⊗ₜ fA (R.frobRootDatum hl0) j (m / D.frobOrder l j) (R.frobWt l μ) else 0 := by
  rw [fA_eq_triT, frobA_triT, fA_eq_triT]
  simp [frobDiv_cons]

open Classical in
lemma frobA_eA (i : I) (n : ℕ) (μ : Y →+ ℤ) :
    frobA R hl0 hl' hA S (eA R i n μ) =
      if μ ∈ R.frobWeights l ∧ D.frobOrder l i ∣ n then
        (1 : S) ⊗ₜ eA (R.frobRootDatum hl0) i (n / D.frobOrder l i) (R.frobWt l μ) else 0 := by
  rw [eA_eq_triT, frobA_triT, eA_eq_triT]
  by_cases hn : D.frobOrder l i ∣ n
  · rw [R.add_nsmul_root_mem_iff hl0 i hn]
    by_cases hμ : μ ∈ R.frobWeights l
    · simp [hμ, hn, frobDiv_cons, R.frobWt_add_nsmul_root hl0 i hn hμ]
    · simp [hμ]
  · simp [hn, frobDiv_cons]

omit [Finite I] [DecidableEq I] in
lemma tmul_one_mul_tmul_one {A : Type*} [NonUnitalRing A] [Module 𝒜 A] [IsScalarTower 𝒜 A A]
    [SMulCommClass 𝒜 A A] (x y : A) :
    ((1 : S) ⊗ₜ[𝒜] x) * ((1 : S) ⊗ₜ[𝒜] y) = (1 : S) ⊗ₜ (x * y) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-! ### Multiplicativity on generators -/

lemma frobA_oneA_mul_triT (μ ν : Y →+ ℤ) (w w' : List (I × ℕ)) :
    frobA R hl0 hl' hA S (oneA R μ * triT R ν w w') =
      frobA R hl0 hl' hA S (oneA R μ) * frobA R hl0 hl' hA S (triT R ν w w') := by
  rw [oneA_mul_triT, apply_ite (frobA R hl0 hl' hA S), map_zero, frobA_oneA, frobA_triT]
  by_cases hΦ : ν ∈ R.frobWeights l ∧ FrobDiv D l w ∧ FrobDiv D l w'
  · obtain ⟨hν, hw, hw'⟩ := hΦ
    have hν' := sub_wtW_mem R hl0 hν hw
    by_cases hμ : μ ∈ R.frobWeights l
    · simp only [hν, hw, hw', hμ, and_self, ↓reduceIte, tmul_one_mul_tmul_one, oneA_mul_triT]
      have key : R.frobWt l μ = R.frobWt l ν - wtW (R.frobRootDatum hl0) (frobDivW D l w) ↔
          μ = ν - wtW R w := by rw [← frobWt_sub_wtW R hl0 hν hw, R.frobWt_inj hμ hν']
      by_cases h : μ = ν - wtW R w
      · simp only [key.2 h, ↓reduceIte]; simp [h]
      · simp only [mt key.1 h, ↓reduceIte]; simp [h]
    · have : μ ≠ ν - wtW R w := fun h ↦ hμ (h ▸ hν')
      simp [hμ, this]
  · simp [hΦ]

lemma frobA_fA_mul_triT (j : I) (m : ℕ) (μ ν : Y →+ ℤ) (w w' : List (I × ℕ)) :
    frobA R hl0 hl' hA S (fA R j m μ * triT R ν w w') =
      frobA R hl0 hl' hA S (fA R j m μ) * frobA R hl0 hl' hA S (triT R ν w w') := by
  rw [fA_mul_triT, apply_ite (frobA R hl0 hl' hA S), map_zero, frobA_fA, frobA_triT,
    frobA_triT, frobDiv_cons, frobDivW_cons]
  by_cases hΦ : ν ∈ R.frobWeights l ∧ FrobDiv D l w ∧ FrobDiv D l w'
  · obtain ⟨hν, hw, hw'⟩ := hΦ
    have hν' := sub_wtW_mem R hl0 hν hw
    by_cases hm : D.frobOrder l j ∣ m
    · by_cases hμ : μ ∈ R.frobWeights l
      · simp only [hν, hw, hw', hμ, hm, and_self, ↓reduceIte, tmul_one_mul_tmul_one,
          fA_mul_triT]
        have key : R.frobWt l μ = R.frobWt l ν - wtW (R.frobRootDatum hl0) (frobDivW D l w) ↔
            μ = ν - wtW R w := by rw [← frobWt_sub_wtW R hl0 hν hw, R.frobWt_inj hμ hν']
        by_cases h : μ = ν - wtW R w
        · simp only [key.2 h, ↓reduceIte]; simp [h]
        · simp only [mt key.1 h, ↓reduceIte]; simp [h]
      · have : μ ≠ ν - wtW R w := fun h ↦ hμ (h ▸ hν')
        simp [hμ, this]
    · simp [hm]
  · have : ¬ (ν ∈ R.frobWeights l ∧ (D.frobOrder l j ∣ m ∧ FrobDiv D l w) ∧ FrobDiv D l w') :=
      fun h ↦ hΦ ⟨h.1, h.2.1.2, h.2.2⟩
    simp only [this, hΦ, ↓reduceIte, mul_zero, ite_self]

omit [Finite I] [DecidableEq I] in
lemma smul_tmul_one_eq_zero {M : Type*} [AddCommGroup M] [Module 𝒜 M] {c : 𝒜}
    (h : algebraMap 𝒜 (CyclotomicQuotient l') c = 0) (y : M) :
    c • ((1 : S) ⊗ₜ[𝒜] y) = 0 := by
  rw [TensorProduct.smul_tmul', Algebra.smul_def,
    IsScalarTower.algebraMap_apply 𝒜 (CyclotomicQuotient l') S, h, map_zero, zero_mul,
    TensorProduct.zero_tmul]

omit [Finite I] [DecidableEq I] in
lemma smul_tmul_one_congr {M : Type*} [AddCommGroup M] [Module 𝒜 M] {c c' : 𝒜}
    (h : algebraMap 𝒜 (CyclotomicQuotient l') c = algebraMap 𝒜 (CyclotomicQuotient l') c')
    (y : M) : c • ((1 : S) ⊗ₜ[𝒜] y) = c' • ((1 : S) ⊗ₜ[𝒜] y) := by
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, Algebra.smul_def,
    IsScalarTower.algebraMap_apply 𝒜 (CyclotomicQuotient l') S c,
    IsScalarTower.algebraMap_apply 𝒜 (CyclotomicQuotient l') S c', h]

omit [Finite I] [DecidableEq I] in
include hl0 hl' in
/-- The coefficient `[⟨i, ν⟩ + n - m; t]ᵢ` of [Lus] 23.1.3 vanishes in `𝒜'` when `ν ∈ X*`,
`lᵢ ∣ n - t`, `lᵢ ∣ m - t` and `lᵢ ∤ t` ([Lus] 35.1.5 (b)). -/
lemma algebraMap_coeff_eq_zero (i : I) {ν : Y →+ ℤ} (hν : ν ∈ R.frobWeights l) {n m t : ℕ}
    (htn : t ≤ n) (htm : t ≤ m) (hn : D.frobOrder l i ∣ n - t) (hm : D.frobOrder l i ∣ m - t)
    (ht : ¬ D.frobOrder l i ∣ t) :
    algebraMap 𝒜 (CyclotomicQuotient l')
      (gaussBinom (laurentTUnit (D.d i)) (ν (R.coroot i) + n - m) t) = 0 := by
  refine algebraMap_gaussBinom_eq_zero D hl0 hl' i ?_ ht
  have h : (n : ℤ) - m = ((n - t : ℕ) : ℤ) - ((m - t : ℕ) : ℤ) := by
    rw [Nat.cast_sub htn, Nat.cast_sub htm]; ring
  rw [add_sub_assoc, h]
  exact dvd_add ⟨_, (R.frobOrder_mul_frobWt_coroot hl0 i hν).symm⟩
    (dvd_sub (Int.natCast_dvd_natCast.2 hn) (Int.natCast_dvd_natCast.2 hm))

open Classical in
lemma frob_term_eq_zero (i : I) (n m t : ℕ) (ν : Y →+ ℤ) (htn : t ≤ n)
    (h : ¬ (ν ∈ R.frobWeights l ∧ D.frobOrder l i ∣ n ∧ D.frobOrder l i ∣ m ∧
      D.frobOrder l i ∣ t)) :
    (if t ≤ m then gaussBinom (laurentTUnit (D.d i)) (ν (R.coroot i) + n - m) t •
        (frobA R hl0 hl' hA S (fA R i (m - t) (ν + (n - t) • R.root i)) *
          frobA R hl0 hl' hA S (eA R i (n - t) ν)) else 0) = 0 := by
  split_ifs with htm
  · rw [frobA_fA, frobA_eA]
    by_cases h1 : ν + (n - t) • R.root i ∈ R.frobWeights l ∧ D.frobOrder l i ∣ m - t
    · by_cases h2 : ν ∈ R.frobWeights l ∧ D.frobOrder l i ∣ n - t
      · have ht : ¬ D.frobOrder l i ∣ t := fun ht ↦ h ⟨h2.1,
          by simpa [Nat.sub_add_cancel htn] using Nat.dvd_add h2.2 ht,
          by simpa [Nat.sub_add_cancel htm] using Nat.dvd_add h1.2 ht, ht⟩
        simp only [h1, h2, and_self, ↓reduceIte, tmul_one_mul_tmul_one]
        exact smul_tmul_one_eq_zero S
          (algebraMap_coeff_eq_zero R hl0 hl' i h2.1 htn htm h2.2 h1.2 ht) _
      · simp [h2]
    · simp [h1]
  · rfl

open Classical in
lemma frobA_term (i : I) (n m t : ℕ) (ν : Y →+ ℤ) :
    frobA R hl0 hl' hA S (if t ≤ m then
        gaussBinom (laurentTUnit (D.d i)) (ν (R.coroot i) + n - m) t •
          (fA R i (m - t) (ν + (n - t) • R.root i) * eA R i (n - t) ν) else 0) =
      if t ≤ m then gaussBinom (laurentTUnit (D.d i)) (ν (R.coroot i) + n - m) t •
          (frobA R hl0 hl' hA S (fA R i (m - t) (ν + (n - t) • R.root i)) *
            frobA R hl0 hl' hA S (eA R i (n - t) ν)) else 0 := by
  split_ifs
  · rw [map_smul, eA_eq_triT i (n - t) ν, frobA_fA_mul_triT, ← eA_eq_triT]
  · exact map_zero _

open Classical in
lemma frobA_eA_mul_frobA_fA_eq_zero (i : I) (n m : ℕ) (ν : Y →+ ℤ)
    (h : ¬ (ν ∈ R.frobWeights l ∧ D.frobOrder l i ∣ n ∧ D.frobOrder l i ∣ m)) :
    frobA R hl0 hl' hA S (eA R i n (ν + m • -R.root i)) *
      frobA R hl0 hl' hA S (fA R i m ν) = 0 := by
  rw [frobA_eA, frobA_fA]
  by_cases h1 : ν + m • -R.root i ∈ R.frobWeights l ∧ D.frobOrder l i ∣ n
  · by_cases h2 : ν ∈ R.frobWeights l ∧ D.frobOrder l i ∣ m
    · exact absurd ⟨h2.1, h1.2, h2.2⟩ h
    · simp only [h2, ↓reduceIte, mul_zero]
  · simp only [h1, ↓reduceIte, zero_mul]

open Classical in
lemma frob_sum_eq_zero (i : I) (n m : ℕ) (ν : Y →+ ℤ)
    (h : ¬ (ν ∈ R.frobWeights l ∧ D.frobOrder l i ∣ n ∧ D.frobOrder l i ∣ m)) :
    ∑ t ∈ Finset.range (n + 1), (if t ≤ m then
        gaussBinom (laurentTUnit (D.d i)) (ν (R.coroot i) + n - m) t •
          (frobA R hl0 hl' hA S (fA R i (m - t) (ν + (n - t) • R.root i)) *
            frobA R hl0 hl' hA S (eA R i (n - t) ν)) else 0) = 0 :=
  Finset.sum_eq_zero fun t ht ↦ frob_term_eq_zero R hl0 hl' hA S i n m t ν
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)) fun h' ↦ h ⟨h'.1, h'.2.1, h'.2.2.1⟩

open Classical in
lemma frob_sum_reindex (i : I) (a b : ℕ) (ν : Y →+ ℤ) :
    ∑ t ∈ Finset.range (D.frobOrder l i * a + 1), (if t ≤ D.frobOrder l i * b then
        gaussBinom (laurentTUnit (D.d i))
            (ν (R.coroot i) + (D.frobOrder l i * a : ℕ) - (D.frobOrder l i * b : ℕ)) t •
          (frobA R hl0 hl' hA S
              (fA R i (D.frobOrder l i * b - t) (ν + (D.frobOrder l i * a - t) • R.root i)) *
            frobA R hl0 hl' hA S (eA R i (D.frobOrder l i * a - t) ν)) else 0) =
    ∑ t ∈ Finset.range (a + 1), (if D.frobOrder l i * t ≤ D.frobOrder l i * b then
        gaussBinom (laurentTUnit (D.d i))
            (ν (R.coroot i) + (D.frobOrder l i * a : ℕ) - (D.frobOrder l i * b : ℕ))
            (D.frobOrder l i * t) •
          (frobA R hl0 hl' hA S (fA R i (D.frobOrder l i * b - D.frobOrder l i * t)
              (ν + (D.frobOrder l i * a - D.frobOrder l i * t) • R.root i)) *
            frobA R hl0 hl' hA S (eA R i (D.frobOrder l i * a - D.frobOrder l i * t) ν))
        else 0) := by
  have hLpos := D.frobOrder_pos hl0 i
  have hsub : (Finset.range (a + 1)).image (D.frobOrder l i * ·) ⊆
      Finset.range (D.frobOrder l i * a + 1) := by
    intro t ht
    simp only [Finset.mem_image, Finset.mem_range] at ht ⊢
    obtain ⟨t', ht', rfl⟩ := ht
    exact Nat.lt_succ_of_le (Nat.mul_le_mul_left _ (Nat.lt_succ_iff.1 ht'))
  rw [← Finset.sum_subset hsub ?_, Finset.sum_image ?_]
  · exact fun x _ y _ h ↦ Nat.eq_of_mul_eq_mul_left hLpos h
  · intro t ht ht'
    refine frob_term_eq_zero R hl0 hl' hA S i _ _ t ν
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)) fun h ↦ ht' ?_
    obtain ⟨c, rfl⟩ := h.2.2.2
    refine Finset.mem_image.2 ⟨c, Finset.mem_range.2 (Nat.lt_succ_of_le ?_), rfl⟩
    exact (Nat.mul_le_mul_left_iff hLpos).1 (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht))

open Classical in
lemma frob_term_mul (i : I) (a b t : ℕ) {ν : Y →+ ℤ} (hν : ν ∈ R.frobWeights l) :
    (if D.frobOrder l i * t ≤ D.frobOrder l i * b then
        gaussBinom (laurentTUnit (D.d i))
            (ν (R.coroot i) + (D.frobOrder l i * a : ℕ) - (D.frobOrder l i * b : ℕ))
            (D.frobOrder l i * t) •
          (frobA R hl0 hl' hA S (fA R i (D.frobOrder l i * b - D.frobOrder l i * t)
              (ν + (D.frobOrder l i * a - D.frobOrder l i * t) • R.root i)) *
            frobA R hl0 hl' hA S (eA R i (D.frobOrder l i * a - D.frobOrder l i * t) ν))
        else 0) =
      (1 : S) ⊗ₜ (if t ≤ b then
        gaussBinom (laurentTUnit ((D.frobenius hl0).d i))
            (R.frobWt l ν ((R.frobRootDatum hl0).coroot i) + a - b) t •
          (fA (R.frobRootDatum hl0) i (b - t)
              (R.frobWt l ν + (a - t) • (R.frobRootDatum hl0).root i) *
            eA (R.frobRootDatum hl0) i (a - t) (R.frobWt l ν)) else 0) := by
  have hLpos := D.frobOrder_pos hl0 i
  rw [← Nat.mul_sub, ← Nat.mul_sub]
  simp only [Nat.mul_le_mul_left_iff hLpos]
  split_ifs with htb
  · rw [frobA_fA, frobA_eA]
    simp only [(R.add_nsmul_root_mem_iff hl0 i (dvd_mul_right _ (a - t))).2 hν, hν,
      dvd_mul_right, and_self, ↓reduceIte, tmul_one_mul_tmul_one,
      R.frobWt_add_nsmul_root hl0 i (dvd_mul_right _ (a - t)) hν,
      Nat.mul_div_cancel_left _ hLpos, TensorProduct.tmul_smul]
    refine smul_tmul_one_congr (l' := l') S ?_ _
    rw [← algebraMap_gaussBinom_mul_mul D hl0 hl' i]
    congr 2
    rw [← R.frobOrder_mul_frobWt_coroot hl0 i hν]
    push_cast
    ring
  · rw [TensorProduct.tmul_zero]

/-- `Fr(Eᵢ^{(n)} 1_{λ - mi'} Fᵢ^{(m)} 1_λ) = Fr(Eᵢ^{(n)} 1_{λ - mi'}) Fr(Fᵢ^{(m)} 1_λ)`, by
[Lus] 23.1.3 and 35.1.5. -/
lemma frobA_eA_mul_fA_self (i : I) (n m : ℕ) (ν : Y →+ ℤ) :
    frobA R hl0 hl' hA S (eA R i n (ν + m • -R.root i) * fA R i m ν) =
      frobA R hl0 hl' hA S (eA R i n (ν + m • -R.root i)) *
        frobA R hl0 hl' hA S (fA R i m ν) := by
  rw [eA_mul_fA_self, map_sum, Finset.sum_congr rfl fun t _ ↦ frobA_term R hl0 hl' hA S i n m t ν]
  by_cases hmain : ν ∈ R.frobWeights l ∧ D.frobOrder l i ∣ n ∧ D.frobOrder l i ∣ m
  swap
  · exact (frob_sum_eq_zero R hl0 hl' hA S i n m ν hmain).trans
      (frobA_eA_mul_frobA_fA_eq_zero R hl0 hl' hA S i n m ν hmain).symm
  obtain ⟨hν, ⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hmain
  have hLpos := D.frobOrder_pos hl0 i
  rw [frob_sum_reindex R hl0 hl' hA S i a b ν,
    Finset.sum_congr rfl fun t _ ↦ frob_term_mul R hl0 hl' hA S i a b t hν,
    ← TensorProduct.tmul_sum,
    ← eA_mul_fA_self (R := R.frobRootDatum hl0) i a b (R.frobWt l ν), ← tmul_one_mul_tmul_one,
    frobA_eA, frobA_fA]
  simp only [(R.add_nsmul_neg_root_mem_iff hl0 i (dvd_mul_right _ b)).2 hν, hν,
    dvd_mul_right, and_self, ↓reduceIte,
    R.frobWt_add_nsmul_neg_root hl0 i (dvd_mul_right _ b) hν, Nat.mul_div_cancel_left _ hLpos]

end Frobenius

end Modified

end LieLean.QuantumGroup
