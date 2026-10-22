/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Frobenius.SplittingKernel
import LieLean.Algebra.QuantumGroup.Frobenius.RadicalWords
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.RatFunc

/-!
# The quantum Frobenius homomorphism `Fr : _F f → _F f*`

Let `F` be a field of characteristic zero over `𝒜 = ℤ[v, v⁻¹]` in which the image `ε` of `v` is
a primitive `2l`-th root of `1` (the field of [Lus] 35.2.1), and assume [Lus] 35.1.2 (a). We
construct the `F`-algebra homomorphism `Fr : _F f → _F f*` of [Lus] Thm. 35.1.7, with
`Fr(θᵢ^{(n)}) = θᵢ^{(n/lᵢ)}` if `lᵢ ∣ n` and `0` otherwise, and prove that it is unique.

## Construction

Let `W` be the image of the splitting `Fr' : _F f* → _F f` ([Lus] 35.1.8, `frobSplit`) and let
`K` be the left ideal of `_F f` spanned by the products `x θᵢ w` with `lᵢ ≥ 2` and `w` a product
of elements `θⱼ^{(lⱼ)}` (`frobKer`). We show `_F f = W ⊕ K` (`isCompl_frobKer`) and that `Fr'`
is injective (`frobSplit_injective`). Then `Fr` is `Fr'⁻¹` composed with the projection onto `W`
along `K`. It is multiplicative because `K` is a left ideal containing every `θᵢ`, `lᵢ ≥ 2`,
times an element of `W`, and `W` is stable under left multiplication by the `θⱼ^{(lⱼ)}`; these
elements generate `_F f` ([Lus] 35.2.2). This is the argument of [Lus] 35.5.1, with left and
right interchanged.

`W + K = _F f` is the argument of [Lus] 35.3.2 (c) (`span_frobWords_sup_frobRad`). For
`W ∩ K = 0`, [Lus] uses the tensor product decomposition 35.4.2 (b), proved with the coproduct
and Verma modules. We use instead that `K` lies in the radical of the form of `Λ_λ` for every
dominant `λ` with `lᵢ ∣ ⟨i, λ⟩` (35.3.2 (d)), and the kernel of `Fr'` modulo that radical in
weights `ν ≤ ⟨i, λ⟩ / lᵢ` (`mem_serreSpan_of_frobPairBase_eq_zero`), applied to the
root datum `extendedRootDatum`, which has fundamental weights, and `λ` large. The weight
components are separated by the orthogonality of weight spaces for the contravariant form
(`frobPairBase_frobSplitHom_eq_zero_of_ne`). The argument is ours.

## Main results

* `frobPairBase_frobSplitHom_eq_zero_of_ne`: Frobenius images of different weights are
  orthogonal.
* `quasiClassicalHom_eq_zero_of_frobSplitHom_mem_frobRad_of_le`: the kernel of `Fr'` modulo the
  radical, for inhomogeneous elements.
* `isCompl_frobKer`, `frobSplit_injective`: `_F f = Fr'(_F f*) ⊕ K` and `Fr'` is injective.
* `frob`, `frob_baseGen`, `eq_frob`: **[Lus] Thm. 35.1.7** for the field of 35.2.1.
* `frob_comp_frobSplit`: `Fr ∘ Fr' = 1`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 35.1.2, 35.1.7, 35.1.8,
  35.2.1, 35.2.2, 35.3.2, 35.4.2, 35.5.1.
-/

open LieLean LusztigF _root_.LusztigF
open scoped TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop

local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

/-! ### Orthogonality of weights -/

section Orthogonal

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular) (Λ : Dom R)

omit [DecidableEq I] in
include hR in
/-- `μ ↦ Σⱼ μⱼ lⱼ j'` is injective for an `X`-regular root datum. -/
lemma frobRootSum_injective {l : ℕ} (hl0 : 0 < l) {μ ν : I →₀ ℕ}
    (h : frobRootSum D R l μ = frobRootSum D R l ν) : μ = ν := by
  have := Fintype.ofFinite I
  have key : ∀ μ : I →₀ ℕ,
      frobRootSum D R l μ = ∑ j, ((μ j * D.frobOrder l j : ℕ) : ℤ) • R.root j := by
    intro μ
    rw [frobRootSum, Finsupp.sum_fintype _ _ (by simp)]
    simp only [natCast_zsmul]
  rw [key, key] at h
  have h2 : ∑ j, (((μ j * D.frobOrder l j : ℕ) : ℤ) - ((ν j * D.frobOrder l j : ℕ) : ℤ)) •
      R.root j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have h3 := Fintype.linearIndependent_iff.1 hR _ h2
  ext j
  have hj := h3 j
  rw [sub_eq_zero, Nat.cast_inj] at hj
  exact Nat.eq_of_mul_eq_mul_right (D.frobOrder_pos hl0 j) hj

/-- Frobenius words of different weights are orthogonal for `frobPair`. -/
lemma frobPair_frobGen_eq_zero_of_ne {l : ℕ} (hl0 : 0 < l) {μ ν : I →₀ ℕ} (h : μ ≠ ν)
    {x y : FreeAlgebra 𝒜 I} (hx : x ∈ FreeAlgebra.wordSpan 𝒜 μ)
    (hy : y ∈ FreeAlgebra.wordSpan 𝒜 ν) :
    frobPair hR Λ (frobGen D l x) (frobGen D l y) = 0 := by
  refine integralLaurentEval_injective ?_
  rw [integralLaurentEval_frobPair_frobGen, map_zero]
  refine (IrreducibleModule.isContravariant_form hR
    (pow_ne_one_of_transcendental' hvt)).eq_zero_of_ne ?_ (frobVec_mem_weightSpace Λ l hx)
    (frobVec_mem_weightSpace Λ l hy)
    (pow_ne_one_of_transcendental' hvt)
  intro he
  exact h (frobRootSum_injective hR hl0 (sub_right_injective he))

/-- Images under `Fr'` of different weights are orthogonal for `frobPairBase`. -/
lemma frobPairBase_frobSplitHom_eq_zero_of_ne (k : Type*) [Field k] [Algebra 𝒜 k] {l : ℕ}
    (hl0 : 0 < l) {μ ν : I →₀ ℕ} (h : μ ≠ ν) {x y : LusztigF k I}
    (hx : x ∈ FreeAlgebra.wordSpan k μ) (hy : y ∈ FreeAlgebra.wordSpan k ν) :
    frobPairBase hR Λ k (frobSplitHom D k l x) (frobSplitHom D k l y) = 0 := by
  induction hx using FreeAlgebra.wordSpan_induction with
  | word u hu =>
    induction hy using FreeAlgebra.wordSpan_induction with
    | word w hw =>
      rw [frobSplitHom_wordBasis, frobSplitHom_wordBasis, frobPairBase_tmul,
        frobPair_frobGen_eq_zero_of_ne hR Λ hl0 h (hu ▸ FreeAlgebra.wordBasis_mem_wordSpan u)
          (hw ▸ FreeAlgebra.wordBasis_mem_wordSpan w), map_zero, zero_mul]
    | zero => rw [map_zero, map_zero]
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, add_zero]
    | smul c y _ hy => rw [map_smul, map_smul, hy, smul_zero]
  | zero => rw [map_zero, map_zero, LinearMap.zero_apply]
  | add x z _ _ hx hz => rw [map_add, map_add, LinearMap.add_apply, hx, hz, add_zero]
  | smul c x _ hx => rw [map_smul, map_smul, LinearMap.smul_apply, hx, smul_zero]

/-- Pairing `Fr'(y)` with the image of an element of weight `ν` only sees the weight-`ν`
component of `y`. -/
lemma frobPairBase_frobSplitHom_weightProj (k : Type*) [Field k] [Algebra 𝒜 k] {l : ℕ}
    (hl0 : 0 < l) {ν : I →₀ ℕ} (y : LusztigF k I) {z : LusztigF k I}
    (hz : z ∈ FreeAlgebra.wordSpan k ν) :
    frobPairBase hR Λ k (frobSplitHom D k l (FreeAlgebra.weightProj k ν y))
        (frobSplitHom D k l z) =
      frobPairBase hR Λ k (frobSplitHom D k l y) (frobSplitHom D k l z) := by
  induction y using FreeAlgebra.induction_wordBasis with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul c x hx => simp only [map_smul, LinearMap.smul_apply, hx]
  | word u =>
    rw [FreeAlgebra.weightProj_wordBasis]
    split_ifs with hu
    · rfl
    · simp only [map_zero, LinearMap.zero_apply]
      rw [frobPairBase_frobSplitHom_eq_zero_of_ne hR Λ k hl0 hu
        (FreeAlgebra.wordBasis_mem_wordSpan u) hz]

end Orthogonal

/-! ### The kernel of `Fr'` modulo the radical -/

section Kernel

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular) (Λ : Dom R)
  {k : Type*} [Field k] [Algebra 𝒜 k] [CharZero k] {l : ℕ} (hl0 : 0 < l)
  (hl : algebraMap 𝒜 k (LaurentPolynomial.T 1) ^ (2 * l) = 1)
  (hprim : ∀ t, 0 < t → t < l → algebraMap 𝒜 k (LaurentPolynomial.T 1) ^ (2 * t) ≠ 1)
  (hA : ∀ i j, i ≠ j → 2 ≤ D.frobOrder l j → ∀ a : ℕ, D.cartanMatrix i j = -a →
    a < D.frobOrder l i)
  (hΛ : ∀ i, 2 ≤ D.frobOrder l i → D.frobOrder l i ∣ (Λ.1 (R.coroot i)).toNat)

include hl0 hl hprim hA hΛ in
/-- **The kernel of `Fr'` modulo the radical**: if every word occurring in `y ∈ f_k` has weight
`ν` with `νᵢ ≤ nᵢ = ⟨i, λ⟩ / lᵢ` and `Fr'(y)` lies in the radical of the form of `Λ_λ`, then the
image of `y` in `_k f*` is zero. -/
theorem quasiClassicalHom_eq_zero_of_frobSplitHom_mem_frobRad_of_le {y : LusztigF k I}
    (hy : ∀ w ∈ ((FreeAlgebra.wordBasis k I).repr y).support, ∀ i,
      wordWeight w i ≤ frobTop Λ l i)
    (hrad : frobSplitHom D k l y ∈ frobRad hR Λ k) :
    quasiClassicalHom (D.frobenius hl0) k y = 0 := by
  have hq := sq_pow_frobenius_d D hl0 hl hprim (F := k)
  rw [← sum_weightProj y, map_sum]
  refine Finset.sum_eq_zero fun ν hν ↦ ?_
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hν
  refine (quasiClassicalHom_eq_zero_iff (D.frobenius hl0) k hq _).2
    (serreSpan_quasi_le_serreIdeal (D.frobenius hl0) k hq
      (mem_serreSpan_of_frobPairBase_eq_zero hR Λ hl0 hl hprim hA hΛ (hy w hw)
        (FreeAlgebra.weightProj_mem _ _) fun u ↦ ?_))
  by_cases hu : wordWeight u = wordWeight w
  · rw [frobPairBase_frobSplitHom_weightProj hR Λ k hl0 y
      (hu ▸ FreeAlgebra.wordBasis_mem_wordSpan u)]
    rw [frobRad, LinearMap.mem_ker] at hrad
    rw [hrad, LinearMap.zero_apply]
  · exact frobPairBase_frobSplitHom_eq_zero_of_ne hR Λ k hl0 (Ne.symm hu)
      (FreeAlgebra.weightProj_mem _ _) (FreeAlgebra.wordBasis_mem_wordSpan u)

end Kernel

/-! ### The dominant weights `N lᵢ` of the extended root datum -/

section FrobDom

variable {I : Type*} [Fintype I] [DecidableEq I] (D : LusztigCartanDatum I) (l N : ℕ)

/-- The weight `(y, z) ↦ Σⱼ N lⱼ yⱼ` of the extended root datum. -/
def frobDomHom : ((I → ℤ) × (I → ℤ)) →+ ℤ :=
  ∑ j, ((N * D.frobOrder l j : ℕ) : ℤ) •
    (Pi.evalAddMonoidHom (fun _ : I ↦ ℤ) j).comp (AddMonoidHom.fst _ _)

lemma frobDomHom_coroot (i : I) :
    frobDomHom D l N (D.extendedRootDatum.coroot i) = ((N * D.frobOrder l i : ℕ) : ℤ) := by
  simp [frobDomHom, AddMonoidHom.finsetSum_apply, Pi.single_apply]

/-- The dominant weight `λ` of the extended root datum with `⟨i, λ⟩ = N lᵢ`. -/
def frobDom : Dom D.extendedRootDatum :=
  ⟨frobDomHom D l N, fun i ↦ by rw [frobDomHom_coroot]; positivity⟩

lemma frobDom_dvd (i : I) :
    D.frobOrder l i ∣ ((frobDom D l N).1 (D.extendedRootDatum.coroot i)).toNat := by
  rw [frobDom, frobDomHom_coroot, Int.toNat_natCast]
  exact Dvd.intro_left _ rfl

lemma frobTop_frobDom (hl0 : 0 < l) (i : I) : frobTop (frobDom D l N) l i = N := by
  rw [frobTop, frobDom, frobDomHom_coroot, Int.toNat_natCast,
    Nat.mul_div_cancel _ (D.frobOrder_pos hl0 i)]

end FrobDom

/-! ### The decomposition `_F f = Fr'(_F f*) ⊕ K` -/

section Decomposition

variable {I : Type*} [DecidableEq I] (D : LusztigCartanDatum I) (F : Type*) [Field F]
  [Algebra 𝒜 F] (l : ℕ)

/-- The products of elements `θⱼ^{(lⱼ)}` of `_F f`. -/
abbrev frobWords : Submonoid (F ⊗[𝒜] quotientIntegralForm D) :=
  Submonoid.closure (Set.range fun j ↦ baseGen D F j (D.frobOrder l j))

/-- The left ideal of `_F f` spanned by the products `θᵢ w` with `lᵢ ≥ 2` and `w` a product of
elements `θⱼ^{(lⱼ)}`. -/
def frobKer : Submodule (F ⊗[𝒜] quotientIntegralForm D) (F ⊗[𝒜] quotientIntegralForm D) :=
  Submodule.span _
    {x | ∃ i, 2 ≤ D.frobOrder l i ∧ ∃ w ∈ frobWords D F l, x = baseGen D F i 1 * w}

variable {D F l}

lemma baseGen_one_mul_mem_frobKer {i : I} (hi : 2 ≤ D.frobOrder l i) {w}
    (hw : w ∈ frobWords D F l) : baseGen D F i 1 * w ∈ frobKer D F l :=
  Submodule.subset_span ⟨i, hi, w, hw, rfl⟩

lemma mul_mem_frobKer (z : F ⊗[𝒜] quotientIntegralForm D) {x : F ⊗[𝒜] quotientIntegralForm D}
    (hx : x ∈ frobKer D F l) : z * x ∈ frobKer D F l :=
  (frobKer D F l).smul_mem z hx

lemma smul_mem_frobKer (c : F) {x : F ⊗[𝒜] quotientIntegralForm D} (hx : x ∈ frobKer D F l) :
    c • x ∈ frobKer D F l := by
  rw [show c • x = algebraMap F _ c * x from Algebra.smul_def c x]
  exact mul_mem_frobKer _ hx

variable (D F l) in
/-- `frobKer` as an `F`-subspace. -/
abbrev frobKerF : Submodule F (F ⊗[𝒜] quotientIntegralForm D) :=
  (frobKer D F l).restrictScalars F

variable [Finite I] (hl0 : 0 < l) (hl : algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (2 * l) = 1)
  (hprim : ∀ t, 0 < t → t < l → algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (2 * t) ≠ 1)
  (hA : ∀ i j, i ≠ j → 2 ≤ D.frobOrder l j → ∀ a : ℕ, D.cartanMatrix i j = -a →
    a < D.frobOrder l i)

include hl0 hl hprim hA in
/-- `frobKer` lies in the radical of the form of `Λ_λ` whenever `lᵢ ∣ ⟨i, λ⟩` for `lᵢ ≥ 2`
([Lus] 35.3.2 (d)). -/
lemma frobKer_le_frobRad {Y : Type*} [AddCommGroup Y] {R : D.RootDatum Y} (hR : R.IsXRegular)
    (Λ : Dom R) (hΛ : ∀ i, 2 ≤ D.frobOrder l i → D.frobOrder l i ∣ (Λ.1 (R.coroot i)).toNat) :
    frobKerF D F l ≤ frobRad hR Λ F := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, w, hw, rfl⟩ := hx
    exact baseGen_one_mul_mem_frobRad hR Λ hl0 hl hprim hA hΛ hw i hi
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul z x _ hx => exact mul_mem_frobRad hR Λ F z hx

variable [CharZero F]

include hl0 hl hprim in
/-- The splitting composed with the quasi-classical map is `θᵢ ↦ θᵢ^{(lᵢ)}`. -/
lemma frobSplit_comp_quasiClassicalHom :
    (frobSplit D hl0 hl hprim).comp (quasiClassicalHom (D.frobenius hl0) F) =
      frobSplitHom D F l := by
  refine FreeAlgebra.hom_ext (funext fun i ↦ ?_)
  change frobSplit D hl0 hl hprim (quasiClassicalHom (D.frobenius hl0) F (θ F i)) =
    frobSplitHom D F l (θ F i)
  rw [quasiClassicalHom_θ, frobSplitHom_θ]
  exact frobSplit_integralGenerator_one D hl0 hl hprim i

include hl0 hl hprim in
/-- The image of `Fr'` is the span of the products of elements `θⱼ^{(lⱼ)}`. -/
lemma frobSplit_mem_span_frobWords (y : F ⊗[𝒜] quotientIntegralForm (D.frobenius hl0)) :
    frobSplit D hl0 hl hprim y ∈
      Submodule.span F (frobWords D F l : Set (F ⊗[𝒜] quotientIntegralForm D)) := by
  obtain ⟨y, rfl⟩ := quasiClassicalHom_surjective (D.frobenius hl0) F
    (sq_pow_frobenius_d D hl0 hl hprim) y
  rw [← AlgHom.comp_apply, frobSplit_comp_quasiClassicalHom, frobWords,
    ← Algebra.adjoin_eq_span, Subalgebra.mem_toSubmodule]
  induction y using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ c
  | grade1 j =>
    rw [← θ, frobSplitHom_θ]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y hx hy => rw [map_mul]; exact mul_mem hx hy

include hl0 hl hprim hA in
/-- `Fr'(_F f*)` meets `K` only in `0`, and `Fr'` is injective on it. -/
lemma eq_zero_of_frobSplit_mem_frobKer {y : F ⊗[𝒜] quotientIntegralForm (D.frobenius hl0)}
    (hy : frobSplit D hl0 hl hprim y ∈ frobKerF D F l) : y = 0 := by
  have := Fintype.ofFinite I
  obtain ⟨y, rfl⟩ := quasiClassicalHom_surjective (D.frobenius hl0) F
    (sq_pow_frobenius_d D hl0 hl hprim) y
  rw [← AlgHom.comp_apply, frobSplit_comp_quasiClassicalHom] at hy
  set N := ∑ w ∈ ((FreeAlgebra.wordBasis F I).repr y).support, ∑ i, wordWeight w i
  have hΛ : ∀ i, 2 ≤ D.frobOrder l i → D.frobOrder l i ∣
      ((frobDom D l N).1 (D.extendedRootDatum.coroot i)).toNat := fun i _ ↦ frobDom_dvd D l N i
  refine quasiClassicalHom_eq_zero_of_frobSplitHom_mem_frobRad_of_le
    D.isXRegular_extendedRootDatum (frobDom D l N) hl0 hl hprim hA hΛ (fun w hw i ↦ ?_)
    (frobKer_le_frobRad hl0 hl hprim hA D.isXRegular_extendedRootDatum _ hΛ hy)
  rw [frobTop_frobDom D l N hl0]
  exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans
    (Finset.single_le_sum (f := fun w ↦ ∑ i, wordWeight w i) (fun _ _ ↦ Nat.zero_le _) hw)

include hl0 hl hprim hA in
/-- `Fr'` is injective. -/
theorem frobSplit_injective : Function.Injective (frobSplit D hl0 hl hprim) :=
  (injective_iff_map_eq_zero _).2 fun _ hy ↦
    eq_zero_of_frobSplit_mem_frobKer hl0 hl hprim hA (hy ▸ zero_mem _)

include hl0 hl hprim in
lemma baseGen_frobOrder_eq_frobSplit (j : I) :
    baseGen D F j (D.frobOrder l j) =
      frobSplit D hl0 hl hprim ((1 : F) ⊗ₜ integralGenerator (D.frobenius hl0) j 1) :=
  (frobSplit_integralGenerator_one D hl0 hl hprim j).symm

include hl0 hl hprim in
lemma frobWords_le_range :
    (frobWords D F l : Set (F ⊗[𝒜] quotientIntegralForm D)) ⊆
      Set.range (frobSplit D hl0 hl hprim) := by
  intro x hx
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨_, (baseGen_frobOrder_eq_frobSplit hl0 hl hprim j).symm⟩
  | one => exact ⟨1, map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, map_mul _ _ _⟩

include hl0 hl hprim in
/-- `θᵢ x ∈ K` for `x ∈ Fr'(_F f*)` and `lᵢ ≥ 2`. -/
lemma baseGen_one_mul_frobSplit_mem_frobKer {i : I} (hi : 2 ≤ D.frobOrder l i)
    (y : F ⊗[𝒜] quotientIntegralForm (D.frobenius hl0)) :
    baseGen D F i 1 * frobSplit D hl0 hl hprim y ∈ frobKer D F l := by
  have h := frobSplit_mem_span_frobWords hl0 hl hprim y
  generalize frobSplit D hl0 hl hprim y = x at h ⊢
  induction h using Submodule.span_induction with
  | mem x hx => exact baseGen_one_mul_mem_frobKer hi hx
  | zero => rw [mul_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
  | smul c x _ hx => rw [mul_smul_comm]; exact smul_mem_frobKer c hx

omit [Finite I] [CharZero F] in
lemma baseGen_one_mem_frobKer {i : I} (hi : 2 ≤ D.frobOrder l i) :
    baseGen D F i 1 ∈ frobKer D F l := by
  simpa using baseGen_one_mul_mem_frobKer (D := D) (F := F) hi (one_mem _)

include hl0 hl hprim hA in
/-- **`_F f = Fr'(_F f*) ⊕ K`** (cf. [Lus] 35.3.2 (c), 35.4.2 (b)). -/
theorem isCompl_frobKer :
    IsCompl (LinearMap.range (frobSplit D hl0 hl hprim).toLinearMap) (frobKerF D F l) := by
  refine ⟨Submodule.disjoint_def.2 fun x hx hk ↦ ?_, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩
  · obtain ⟨y, rfl⟩ := hx
    rw [AlgHom.toLinearMap_apply] at hk ⊢
    rw [eq_zero_of_frobSplit_mem_frobKer hl0 hl hprim hA hk, map_zero]
  set S := LinearMap.range (frobSplit D hl0 hl hprim).toLinearMap ⊔ frobKerF D F l
  have hgen : ∀ g ∈ frobeniusGenerators D F l, ∀ z ∈ S, g * z ∈ S := by
    intro g hg z hz
    obtain ⟨w, ⟨y, rfl⟩, k, hk, rfl⟩ := Submodule.mem_sup.1 hz
    rw [mul_add]
    refine add_mem ?_ (Submodule.mem_sup_right (mul_mem_frobKer g hk))
    rw [AlgHom.toLinearMap_apply]
    rcases hg with ⟨j, rfl⟩ | ⟨i, hi, rfl⟩
    · refine Submodule.mem_sup_left
        ⟨((1 : F) ⊗ₜ integralGenerator (D.frobenius hl0) j 1) * y, ?_⟩
      rw [AlgHom.toLinearMap_apply, map_mul, ← baseGen_frobOrder_eq_frobSplit hl0 hl hprim]
    · exact Submodule.mem_sup_right (baseGen_one_mul_frobSplit_mem_frobKer hl0 hl hprim hi y)
  have hP : ∀ a, ∀ z ∈ S, a * z ∈ S := by
    intro a
    have ha : a ∈ Algebra.adjoin F (frobeniusGenerators D F l) := by
      rw [adjoin_frobeniusGenerators D hl0 hl hprim]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem g hg => exact hgen g hg
    | algebraMap c =>
      intro z hz
      rw [← Algebra.smul_def]
      exact S.smul_mem c hz
    | add a b _ _ ha hb => intro z hz; rw [add_mul]; exact add_mem (ha z hz) (hb z hz)
    | mul a b _ _ ha hb => intro z hz; rw [mul_assoc]; exact ha _ (hb z hz)
  intro x _
  have h1 : (1 : F ⊗[𝒜] quotientIntegralForm D) ∈ S :=
    Submodule.mem_sup_left ⟨1, by rw [AlgHom.toLinearMap_apply, map_one]⟩
  simpa using hP x 1 h1

/-! ### The homomorphism `Fr` -/

include hl0 hl hprim hA in
/-- The projection of `_F f` onto `Fr'(_F f*)` along `K`, followed by `Fr'⁻¹`. -/
def frobLin :
    F ⊗[𝒜] quotientIntegralForm D →ₗ[F] F ⊗[𝒜] quotientIntegralForm (D.frobenius hl0) :=
  LinearMap.linearProjOfIsCompl (frobKerF D F l) (frobSplit D hl0 hl hprim).toLinearMap
    (frobSplit_injective hl0 hl hprim hA) (isCompl_frobKer hl0 hl hprim hA)

include hA in
lemma frobLin_frobSplit (y : F ⊗[𝒜] quotientIntegralForm (D.frobenius hl0)) :
    frobLin hl0 hl hprim hA (frobSplit D hl0 hl hprim y) = y :=
  LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ y

include hA in
lemma frobLin_of_mem {x : F ⊗[𝒜] quotientIntegralForm D} (hx : x ∈ frobKer D F l) :
    frobLin hl0 hl hprim hA x = 0 :=
  LinearMap.linearProjOfIsCompl_apply_right' _ _ _ _ x hx

include hA in
lemma exists_eq_frobSplit_add (x : F ⊗[𝒜] quotientIntegralForm D) :
    ∃ y k, k ∈ frobKer D F l ∧ x = frobSplit D hl0 hl hprim y + k := by
  have hx : x ∈ LinearMap.range (frobSplit D hl0 hl hprim).toLinearMap ⊔ frobKerF D F l := by
    rw [(isCompl_frobKer hl0 hl hprim hA).sup_eq_top]; trivial
  obtain ⟨_, ⟨y, rfl⟩, k, hk, rfl⟩ := Submodule.mem_sup.1 hx
  exact ⟨y, k, hk, rfl⟩

lemma frobLin_mul_of_mem {g : F ⊗[𝒜] quotientIntegralForm D}
    (hg : g ∈ frobeniusGenerators D F l) (x : F ⊗[𝒜] quotientIntegralForm D) :
    frobLin hl0 hl hprim hA (g * x) = frobLin hl0 hl hprim hA g * frobLin hl0 hl hprim hA x := by
  obtain ⟨y, k, hk, rfl⟩ := exists_eq_frobSplit_add hl0 hl hprim hA x
  rw [map_add (frobLin hl0 hl hprim hA), frobLin_of_mem hl0 hl hprim hA hk, add_zero,
    frobLin_frobSplit, mul_add]
  rcases hg with ⟨j, rfl⟩ | ⟨i, hi, rfl⟩
  · dsimp only
    rw [baseGen_frobOrder_eq_frobSplit hl0 hl hprim, ← map_mul, map_add (frobLin hl0 hl hprim hA),
      frobLin_frobSplit, frobLin_frobSplit, frobLin_of_mem hl0 hl hprim hA (mul_mem_frobKer _ hk),
      add_zero]
  · rw [frobLin_of_mem hl0 hl hprim hA (baseGen_one_mem_frobKer hi), zero_mul,
      frobLin_of_mem hl0 hl hprim hA (add_mem
        (baseGen_one_mul_frobSplit_mem_frobKer hl0 hl hprim hi y) (mul_mem_frobKer _ hk))]

lemma frobLin_one : frobLin hl0 hl hprim hA 1 = 1 := by
  rw [← map_one (frobSplit D hl0 hl hprim), frobLin_frobSplit]

lemma frobLin_mul (a x : F ⊗[𝒜] quotientIntegralForm D) :
    frobLin hl0 hl hprim hA (a * x) = frobLin hl0 hl hprim hA a * frobLin hl0 hl hprim hA x := by
  have ha : a ∈ Algebra.adjoin F (frobeniusGenerators D F l) := by
    rw [adjoin_frobeniusGenerators D hl0 hl hprim]; trivial
  induction ha using Algebra.adjoin_induction generalizing x with
  | mem g hg => exact frobLin_mul_of_mem hl0 hl hprim hA hg x
  | algebraMap c =>
    rw [← Algebra.smul_def, map_smul, ← mul_one (algebraMap F _ c), ← Algebra.smul_def,
      map_smul, frobLin_one, smul_one_mul]
  | add a b _ _ ha hb => rw [add_mul, map_add, map_add, ha, hb, add_mul]
  | mul a b _ _ ha hb => rw [mul_assoc, ha, hb, ha, mul_assoc]

/-- **[Lus] Thm. 35.1.7** (for the field `F` of 35.2.1): the quantum Frobenius homomorphism
`Fr : _F f → _F f*`. -/
def frob :
    F ⊗[𝒜] quotientIntegralForm D →ₐ[F] F ⊗[𝒜] quotientIntegralForm (D.frobenius hl0) :=
  AlgHom.ofLinearMap (frobLin hl0 hl hprim hA) (frobLin_one hl0 hl hprim hA)
    (frobLin_mul hl0 hl hprim hA)

lemma frob_apply (x : F ⊗[𝒜] quotientIntegralForm D) :
    frob hl0 hl hprim hA x = frobLin hl0 hl hprim hA x := rfl

/-- `Fr ∘ Fr' = 1` ([Lus] 35.1.8). -/
theorem frob_frobSplit (y : F ⊗[𝒜] quotientIntegralForm (D.frobenius hl0)) :
    frob hl0 hl hprim hA (frobSplit D hl0 hl hprim y) = y :=
  frobLin_frobSplit hl0 hl hprim hA y

/-- `Fr ∘ Fr' = 1` ([Lus] 35.1.8). -/
theorem frob_comp_frobSplit : (frob hl0 hl hprim hA).comp (frobSplit D hl0 hl hprim) = 1 :=
  AlgHom.ext (frob_frobSplit hl0 hl hprim hA)

/-- **[Lus] Thm. 35.1.7**: `Fr(θᵢ^{(n)}) = θᵢ^{(n/lᵢ)}` if `lᵢ ∣ n`, and `0` otherwise. -/
theorem frob_baseGen (i : I) (n : ℕ) :
    frob hl0 hl hprim hA (baseGen D F i n) =
      if D.frobOrder l i ∣ n then baseGen (D.frobenius hl0) F i (n / D.frobOrder l i) else 0 := by
  have hL := D.frobOrder_pos hl0 i
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [← frobSplit_integralGenerator D hl0 hl hprim, frob_frobSplit,
      Nat.mul_div_cancel_left _ hL]
  · have hi : 2 ≤ D.frobOrder l i := by
      by_contra h2
      exact h (by rw [show D.frobOrder l i = 1 by omega]; exact one_dvd n)
    have ha : n % D.frobOrder l i < D.frobOrder l i := Nat.mod_lt _ hL
    have ha0 : n % D.frobOrder l i ≠ 0 := fun h0 ↦ h (Nat.dvd_of_mod_eq_zero h0)
    obtain ⟨c, hc, hmul⟩ := baseGen_mul_baseGen_frobOrder D hl0 hl hprim i ha
      (n / D.frobOrder l i)
    rw [Nat.mod_add_div] at hmul
    have h0 : frob hl0 hl hprim hA (baseGen D F i (n % D.frobOrder l i)) = 0 := by
      rw [baseGen_eq_smul_pow_of_lt D hl0 hl hprim i ha, map_smul, map_pow, frob_apply,
        frobLin_of_mem hl0 hl hprim hA (baseGen_one_mem_frobKer hi), zero_pow ha0, smul_zero]
    rw [← inv_smul_smul₀ hc (baseGen D F i n), ← hmul, map_smul, map_mul, h0, zero_mul,
      smul_zero]

/-- `Fr` is the unique `F`-algebra homomorphism `_F f → _F f*` with the values of
[Lus] Thm. 35.1.7 on the `θᵢ^{(n)}`. -/
theorem eq_frob
    (φ : F ⊗[𝒜] quotientIntegralForm D →ₐ[F] F ⊗[𝒜] quotientIntegralForm (D.frobenius hl0))
    (hφ : ∀ i n, φ (baseGen D F i n) =
      if D.frobOrder l i ∣ n then baseGen (D.frobenius hl0) F i (n / D.frobOrder l i)
      else 0) :
    φ = frob hl0 hl hprim hA := by
  refine AlgHom.ext_of_adjoin_eq_top (adjoin_baseChangeGenerator D F) ?_
  rintro _ ⟨⟨i, n⟩, rfl⟩
  exact (hφ i n).trans (frob_baseGen hl0 hl hprim hA i n).symm

end Decomposition

end LieLean.QuantumGroup
