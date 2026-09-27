/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.FreeAlgebra
import LieLean.Algebra.QuantumGroup.LusztigF.Basic

/-!
# Words in free algebras and change of coefficients

For a commutative ring `R`, the free algebra `FreeAlgebra R X` has the basis of words
`FreeAlgebra.wordBasis R X`, `[x₁, …, xₙ] ↦ x₁ ⋯ xₙ` (a reindexing of Mathlib's
`FreeAlgebra.basisFreeMonoid` by lists). A ring homomorphism `φ : R → S` induces the ring
homomorphism `FreeAlgebra.mapCoeffs φ : FreeAlgebra R X → FreeAlgebra S X`, `xᵢ ↦ xᵢ`, which acts
on coordinates in the word basis by `φ`.

We also record the subspaces `FreeAlgebra.wordSpan R μ` spanned by the words of weight `μ ∈ ℕ[X]`
(for a field these are the weight spaces `LusztigF.weightSpace` of Lusztig's algebra `'f`).

## Main definitions

* `FreeAlgebra.wordBasis R X`: the basis of words.
* `FreeAlgebra.mapCoeffs φ`: change of coefficients along `φ : R →+* S`.
* `FreeAlgebra.wordSpan R μ`: the span of the words of weight `μ`.

## Main results

* `FreeAlgebra.wordBasis_apply`, `FreeAlgebra.ι_mul_wordBasis`.
* `FreeAlgebra.mapCoeffs_wordBasis`, `FreeAlgebra.wordBasis_repr_mapCoeffs`,
  `FreeAlgebra.algebraMapInv_mapCoeffs`.

## References

Elementary; this is API for Mathlib's `FreeAlgebra` used in the proof of the quantum Gabber–Kac
theorem.
-/

noncomputable section

namespace FreeAlgebra

variable (R X : Type*) [CommRing R]

/-- The basis of `FreeAlgebra R X` given by the words `[x₁, …, xₙ] ↦ x₁ ⋯ xₙ`. -/
def wordBasis : Module.Basis (List X) R (FreeAlgebra R X) :=
  (basisFreeMonoid R X).reindex FreeMonoid.ofList.symm

variable {R X}

@[simp] lemma wordBasis_apply (w : List X) : wordBasis R X w = (w.map (ι R)).prod := by
  simp [wordBasis, basisFreeMonoid, equivMonoidAlgebraFreeMonoid, FreeMonoid.lift_apply]

@[simp] lemma wordBasis_nil : wordBasis R X [] = 1 := by simp

lemma ι_mul_wordBasis (x : X) (w : List X) :
    ι R x * wordBasis R X w = wordBasis R X (x :: w) := by
  simp

lemma wordBasis_append (w w' : List X) :
    wordBasis R X (w ++ w') = wordBasis R X w * wordBasis R X w' := by
  simp

lemma span_wordBasis : Submodule.span R (Set.range (wordBasis R X)) = ⊤ :=
  (wordBasis R X).span_eq

/-- Induction over the span of the words. -/
theorem induction_wordBasis {P : FreeAlgebra R X → Prop} (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y)) (smul : ∀ (c : R) x, P x → P (c • x))
    (word : ∀ w, P (wordBasis R X w)) (x : FreeAlgebra R X) : P x := by
  have hx : x ∈ Submodule.span R (Set.range (wordBasis R X)) := by
    rw [span_wordBasis]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨w, rfl⟩ := hy; exact word w
  | zero => exact zero
  | add y z _ _ hy hz => exact add y z hy hz
  | smul c y _ hy => exact smul c y hy

/-! ### Change of coefficients -/

variable {S : Type*} [CommRing S] (φ : R →+* S)

/-- The ring homomorphism `FreeAlgebra R X → FreeAlgebra S X`, `xᵢ ↦ xᵢ`, induced by a ring
homomorphism `φ : R → S` on coefficients. -/
def mapCoeffs : FreeAlgebra R X →+* FreeAlgebra S X :=
  letI : Algebra R (FreeAlgebra S X) := Algebra.compHom (FreeAlgebra S X) φ
  (lift R (ι S)).toRingHom

@[simp] lemma mapCoeffs_ι (x : X) : mapCoeffs φ (ι R x) = ι S x := by
  simp [mapCoeffs]

@[simp] lemma mapCoeffs_algebraMap (c : R) :
    mapCoeffs φ (algebraMap R (FreeAlgebra R X) c) = algebraMap S _ (φ c) := by
  let _ : Algebra R (FreeAlgebra S X) := Algebra.compHom (FreeAlgebra S X) φ
  exact (lift R (ι S)).commutes c

lemma mapCoeffs_smul (c : R) (x : FreeAlgebra R X) :
    mapCoeffs φ (c • x) = φ c • mapCoeffs φ x := by
  rw [Algebra.smul_def, map_mul, mapCoeffs_algebraMap, ← Algebra.smul_def]

@[simp] lemma mapCoeffs_wordBasis (w : List X) :
    mapCoeffs φ (wordBasis R X w) = wordBasis S X w := by
  simp [map_list_prod, Function.comp_def]

lemma mapCoeffs_eq_sum (x : FreeAlgebra R X) :
    mapCoeffs φ x = ((wordBasis R X).repr x).sum fun w c ↦ φ c • wordBasis S X w := by
  conv_lhs => rw [← (wordBasis R X).linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
  simp only [mapCoeffs_smul, mapCoeffs_wordBasis]

/-- `mapCoeffs φ` acts on the coordinates in the word basis by `φ`. -/
theorem wordBasis_repr_mapCoeffs (x : FreeAlgebra R X) (w : List X) :
    (wordBasis S X).repr (mapCoeffs φ x) w = φ ((wordBasis R X).repr x w) := by
  classical
  rw [mapCoeffs_eq_sum, Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.1 h, map_zero]

/-- The augmentation commutes with `mapCoeffs φ`. -/
theorem algebraMapInv_mapCoeffs (x : FreeAlgebra R X) :
    algebraMapInv (mapCoeffs φ x) = φ (algebraMapInv x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    rw [mapCoeffs_algebraMap]
    simp [algebraMapInv]
  | grade1 x => simp [algebraMapInv]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-! ### Weights of words -/

variable (R) in
/-- The span of the words of weight `μ ∈ ℕ[X]` in `FreeAlgebra R X`. -/
def wordSpan (μ : X →₀ ℕ) : Submodule R (FreeAlgebra R X) :=
  Submodule.span R ((fun w ↦ (w.map (ι R)).prod) '' {w | LusztigF.wordWeight w = μ})

lemma wordBasis_mem_wordSpan (w : List X) :
    wordBasis R X w ∈ wordSpan R (LusztigF.wordWeight w) := by
  rw [wordBasis_apply]
  exact Submodule.subset_span ⟨w, rfl, rfl⟩

lemma wordBasis_mem_wordSpan_of_eq {w : List X} {μ : X →₀ ℕ} (h : LusztigF.wordWeight w = μ) :
    wordBasis R X w ∈ wordSpan R μ :=
  h ▸ wordBasis_mem_wordSpan w

/-- Induction over `wordSpan R μ`. -/
theorem wordSpan_induction {μ : X →₀ ℕ} {P : (x : FreeAlgebra R X) → x ∈ wordSpan R μ → Prop}
    (word : ∀ w (hw : LusztigF.wordWeight w = μ),
      P (wordBasis R X w) (wordBasis_mem_wordSpan_of_eq hw))
    (zero : P 0 (zero_mem _))
    (add : ∀ x y hx hy, P x hx → P y hy → P (x + y) (add_mem hx hy))
    (smul : ∀ (c : R) x hx, P x hx → P (c • x) (Submodule.smul_mem _ c hx))
    {x : FreeAlgebra R X} (hx : x ∈ wordSpan R μ) : P x hx := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    have := word w hw
    simpa using this
  | zero => exact zero
  | add y z hy hz ihy ihz => exact add y z hy hz ihy ihz
  | smul c y hy ih => exact smul c y hy ih

lemma ι_mul_mem_wordSpan (x : X) {μ : X →₀ ℕ} {y : FreeAlgebra R X} (hy : y ∈ wordSpan R μ) :
    ι R x * y ∈ wordSpan R (Finsupp.single x 1 + μ) := by
  induction hy using wordSpan_induction with
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
  | word w hw =>
    rw [ι_mul_wordBasis]
    exact wordBasis_mem_wordSpan_of_eq (by rw [LusztigF.wordWeight_cons, hw])

lemma algebraMapInv_eq_zero_of_mem_wordSpan {μ : X →₀ ℕ} (hμ : μ ≠ 0) {y : FreeAlgebra R X}
    (hy : y ∈ wordSpan R μ) : algebraMapInv y = 0 := by
  induction hy using wordSpan_induction with
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]
  | word w hw =>
    cases w with
    | nil => exact absurd hw.symm (by simpa using hμ)
    | cons x w => simp [algebraMapInv]

end FreeAlgebra
