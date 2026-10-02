/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.RootVectorWeights
import LieLean.Algebra.QuantumGroup.PBW.Independence
import LieLean.Algebra.QuantumGroup.PBW.WeightDimension
import LieLean.Algebra.QuantumGroup.Weight
import LieLean.LinearAlgebra.Eigenspace.Weight
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Root-lattice homogeneity of quantum root vectors

The conjugation characters of `PBW/RootVectorWeights.lean` determine actual nonnegative
root-lattice degrees in finite type. This file proves membership in the existing
`plusWeightSpace`, the image of the homogeneous words in the positive free algebra.

## Main definitions / results

* `LusztigCartanDatum.RootDatum.isXRegular_of_isFiniteCartan`: character separation follows
  from the existing root-datum axioms and the nonzero integer Cartan determinant. No separate
  independence assumption on the roots and no characteristic-zero hypothesis are needed.
* `QuantumGroup.mem_plusWeightSpace_of_mem_adWeightSpace`: inside `U⁺`, a conjugation
  character determines the homogeneous piece when the root datum is `X`-regular.
* `QuantumGroup.rootVectorDegree`: the integer prefix-reflected simple root. The theorem
  `rootVectorDegree_eq_cartan_fold` identifies its reflection rule with
  `β ↦ β - (Σⱼ aᵢⱼ βⱼ) αᵢ`, independently of the root-datum realization.
* `QuantumGroup.rootVectorDegree_nonneg_of_isFiniteCartan`: reduced-word prefix degrees are
  nonnegative, derived from positive-subalgebra membership, character separation, and the
  nonvanishing of the actual braid root vector. Thus `positiveRootVectorDegree` does not
  silently discard negative coordinates in the main theorem.
* `QuantumGroup.rootVector_mem_plusWeightSpace_of_isFiniteCartan` and
  `QuantumGroup.pbwMonomial_mem_plusWeightSpace_of_isFiniteCartan`: actual root vectors and
  ordered monomials lie in their stated root-lattice pieces.

These results hold over any field at a nonzero parameter which is not a root of unity.
They prove homogeneity, not spanning. Independence is already proved in `PBW/Independence`.
The remaining dimension-based route must identify the prefix roots of a longest word with
all positive roots, with the correct Kostant partition count. The existing dimension theorem
requires a parameter transcendental over `ℚ`; this file does not extend that theorem.

## References

* J. C. Jantzen, *Lectures on quantum groups*, GSM 6, §§4.7, 8.21–8.24 (check).
* G. Lusztig, *Introduction to quantum groups*, §§2.2, 40.1–40.2 (check).

The proofs are reconstructed from the existing conjugation and positive-subalgebra results
and elementary independence of simultaneous eigenspaces; the printed sources were not consulted.
-/

noncomputable section
namespace LusztigCartanDatum.RootDatum
variable {I Y : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)

/-- Finite type implies `X`-regularity over the integer character lattice.
The proof evaluates a root relation on coroots and uses the nonzero Cartan determinant. -/
theorem isXRegular_of_isFiniteCartan (hA : D.cartanMatrix.IsFiniteCartan) :
    R.IsXRegular := by
  rw [IsXRegular, linearIndependent_iff]
  intro l hl
  have hz : D.cartanMatrix.mulVec (fun i ↦ l i) = 0 := by
    funext i
    have h := DFunLike.congr_fun hl (R.coroot i)
    simpa [Finsupp.linearCombination_apply, Finsupp.sum_fintype,
      map_sum, AddMonoidHom.smul_apply, R.root_coroot,
      Matrix.mulVec, dotProduct, mul_comm] using h
  have h := Matrix.mulVec_injective_of_det_ne_zero hA.det_pos.ne'
    (hz.trans (Matrix.mulVec_zero _).symm)
  ext i
  exact congr_fun h i
end LusztigCartanDatum.RootDatum

namespace QuantumGroup
variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]

private def adTorus : (Y →₀ k) →ₗ[k] Module.End k (QuantumGroup R v) :=
  Finsupp.linearCombination k fun μ ↦
    (LinearMap.mulRight k (K R v (-μ))).comp (LinearMap.mulLeft k (K R v μ))

private def weightFunctional (χ : Y →+ ℤ) : Module.Dual k (Y →₀ k) :=
  Finsupp.linearCombination k fun μ ↦ v ^ χ μ

omit [NeZero v] in
private lemma mem_weightSpaceOf_adTorus {χ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v χ) :
    x ∈ Module.End.weightSpaceOf (adTorus (R := R) (v := v)) (weightFunctional (v := v) χ) := by
  intro f
  simp only [adTorus, weightFunctional, Finsupp.linearCombination_apply,
    Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun μ _ ↦ by
    rw [conj_eq_of_mem_adWeightSpace hx μ, smul_smul, smul_eq_mul]

private lemma weightFunctional_injective (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    Function.Injective (weightFunctional (k := k) (v := v) (Y := Y)) := by
  intro χ ψ h
  ext μ
  have he : v ^ χ μ = v ^ ψ μ := by
    have := LinearMap.congr_fun h (Finsupp.single μ 1)
    simpa [weightFunctional] using this
  by_contra hn
  exact zpow_ne_one_of_not_root hv (sub_ne_zero.2 hn) (by
    rw [zpow_sub₀ (NeZero.ne v), he, div_self (zpow_ne_zero _ (NeZero.ne v))])

/-- Conjugation weight spaces for distinct characters are independent at a parameter
which is not a root of unity. Reconstructed by simultaneous-eigenspace separation. -/
theorem iSupIndep_adWeightSpace (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    iSupIndep (adWeightSpace R v) :=
  ((Module.End.iSupIndep_weightSpaceOf (adTorus (R := R) (v := v))).comp
    (weightFunctional_injective hv)).mono fun _ _ hx ↦ mem_weightSpaceOf_adTorus hx

/-- Conjugation characters add under multiplication. -/
lemma mul_mem_adWeightSpace {χ ψ : Y →+ ℤ} {x y : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v χ) (hy : y ∈ adWeightSpace R v ψ) :
    x * y ∈ adWeightSpace R v (χ + ψ) := by
  intro μ
  rw [← mul_assoc, hx μ, smul_mul_assoc, mul_assoc x, hy μ, mul_smul_comm,
    smul_smul, AddMonoidHom.add_apply, zpow_add₀ (NeZero.ne v), mul_assoc]

/-- Every homogeneous positive element has the corresponding conjugation character. -/
lemma plusWeightSpace_le_adWeightSpace (ν : I →₀ ℕ) :
    plusWeightSpace R v ν ≤ adWeightSpace R v (R.rootSum ν) := by
  rintro x ⟨y, hy, rfl⟩
  change plusHom R v y ∈ _
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl, rfl⟩ := hy
    induction w with
    | nil => simp [LusztigF.monomial, LusztigF.wordWeight, adWeightSpace]
    | cons i w ih =>
      simp only [LusztigF.monomial_cons, LusztigF.wordWeight_cons,
        R.rootSum_add, R.rootSum_single, one_smul, map_mul, plusHom_θ]
      exact mul_mem_adWeightSpace (E_mem_adWeightSpace i) ih
  | zero => simp
  | add y z _ _ hy hz => simpa only [map_add] using (adWeightSpace R v _).add_mem hy hz
  | smul c y _ hy => simpa only [map_smul] using (adWeightSpace R v _).smul_mem c hy

omit [NeZero v] in
/-- The root-lattice homogeneous pieces exhaust the positive subalgebra. -/
theorem iSup_plusWeightSpace :
    (⨆ ν, plusWeightSpace R v ν) =
      (Algebra.adjoin k (Set.range (E R v))).toSubmodule := by
  simp only [plusWeightSpace, ← Submodule.map_iSup, LusztigF.iSup_weightSpace,
    Submodule.map_top]
  exact congrArg Subalgebra.toSubmodule (range_plusHom R v)

private theorem mem_characterFiber (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {χ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ Algebra.adjoin k (Set.range (E R v))) (hχ : x ∈ adWeightSpace R v χ) :
    x ∈ ⨆ ν, ⨆ (_ : R.rootSum ν = χ), plusWeightSpace R v ν := by
  apply (iSupIndep_adWeightSpace hv).mem_of_mem_iSup_of_le
    (fun ψ ↦ (show (⨆ ν, ⨆ (_ : R.rootSum ν = ψ), plusWeightSpace R v ν) ≤
      adWeightSpace R v ψ from iSup_le fun ν ↦ iSup_le fun h ↦
        h ▸ plusWeightSpace_le_adWeightSpace ν)) hχ
  have hx' : x ∈ ⨆ ν, plusWeightSpace R v ν := by rwa [iSup_plusWeightSpace]
  apply (show (⨆ ν, plusWeightSpace R v ν) ≤
    ⨆ ψ, ⨆ ν, ⨆ (_ : R.rootSum ν = ψ), plusWeightSpace R v ν from ?_) hx'
  exact iSup_le fun ν ↦ le_iSup_of_le (R.rootSum ν)
    (le_iSup_of_le ν (le_iSup_of_le rfl le_rfl))

/-- In an `X`-regular root datum, a positive element with character `rootSum ν`
actually belongs to the root-lattice piece `U⁺_ν`. Reconstructed from eigenspace independence. -/
theorem mem_plusWeightSpace_of_mem_adWeightSpace (hR : R.IsXRegular)
    (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {ν : I →₀ ℕ} {x : QuantumGroup R v}
    (hx : x ∈ Algebra.adjoin k (Set.range (E R v)))
    (hχ : x ∈ adWeightSpace R v (R.rootSum ν)) : x ∈ plusWeightSpace R v ν := by
  have hf := mem_characterFiber hv hx hχ
  apply (show (⨆ μ, ⨆ (_ : R.rootSum μ = R.rootSum ν), plusWeightSpace R v μ) ≤
    plusWeightSpace R v ν from ?_) hf
  refine iSup_le fun μ ↦ iSup_le fun h ↦ ?_
  have hm : μ = ν := by
    by_contra hn
    obtain ⟨y, hy⟩ := R.exists_rootSum_ne hR hn
    exact hy (DFunLike.congr_fun h y)
  subst hm
  exact le_rfl

/-- A nonzero positive conjugation eigenvector has a nonnegative root-lattice degree. -/
theorem exists_degree_of_mem_adWeightSpace (hR : R.IsXRegular)
    (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {χ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ Algebra.adjoin k (Set.range (E R v)))
    (hχ : x ∈ adWeightSpace R v χ) (hx0 : x ≠ 0) :
    ∃ ν : I →₀ ℕ, R.rootSum ν = χ ∧ x ∈ plusWeightSpace R v ν := by
  have hex : ∃ ν, R.rootSum ν = χ := by
    by_contra! hn
    have hf := mem_characterFiber hv hx hχ
    simp only [hn, iSup_of_empty, iSup_bot, Submodule.mem_bot] at hf
    exact hx0 hf
  obtain ⟨ν, hν⟩ := hex
  exact ⟨ν, hν, mem_plusWeightSpace_of_mem_adWeightSpace hR hv hx (hν.symm ▸ hχ)⟩

/-- The simple positive generator is nonzero at a parameter not a root of unity.
Reconstructed from triangular decomposition and evaluation at one polynomial generator. -/
lemma E_ne_zero_of_not_root (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i : I) :
    E R v i ≠ 0 := by
  intro h
  have hs := (plusHom_eq_zero_iff R v hv (LusztigF.θ k i)).1 (by simpa using h)
  have he := LusztigF.nodeEval_eq_zero_of_mem_serreIdeal i hs
  rw [LusztigF.nodeEval_θ_self] at he
  exact Polynomial.X_ne_zero he

omit [NeZero v] in
/-- Integer root-lattice coordinates of a prefix-reflected simple root. -/
def rootVectorDegree (ω : List I) (n : ℕ) (hn : n < ω.length) : I →₀ ℤ :=
  (ω.take n).foldr (fun i β ↦
    β - (Finsupp.linearCombination ℤ R.root β) (R.coroot i) • Finsupp.single i 1)
    (Finsupp.single ω[n] 1)

omit [NeZero v] [DecidableEq I] in
/-- The simple coroot pairing is the corresponding Cartan-matrix row. -/
lemma linearCombination_coroot (β : I →₀ ℤ) (i : I) :
    (Finsupp.linearCombination ℤ R.root β) (R.coroot i) =
      β.sum (fun j a ↦ a * D.cartanMatrix i j) := by
  simp [Finsupp.linearCombination_apply, Finsupp.sum, R.root_coroot]

omit [NeZero v] [DecidableEq I] in
/-- The signed degree is exactly the usual Cartan root-lattice reflection recursion. -/
lemma rootVectorDegree_eq_cartan_fold (ω : List I) (n : ℕ) (hn : n < ω.length) :
    rootVectorDegree (R := R) ω n hn =
      (ω.take n).foldr (fun i β ↦
        β - (β.sum fun j a ↦ a * D.cartanMatrix i j) • Finsupp.single i 1)
        (Finsupp.single ω[n] 1) := by
  simp only [rootVectorDegree, linearCombination_coroot]

omit [NeZero v] [DecidableEq I] in
/-- The character associated to the signed prefix degree is the previously proved
root-vector conjugation character. -/
lemma rootVectorDegree_character (ω : List I) (n : ℕ) (hn : n < ω.length) :
    Finsupp.linearCombination ℤ R.root (rootVectorDegree (R := R) ω n hn) =
      rootVectorWeight R ω n hn := by
  unfold rootVectorDegree rootVectorWeight
  generalize ω.take n = w
  induction w with
  | nil => simp [wordWeightAction]
  | cons i w ih =>
    simp only [List.foldr_cons, map_sub, map_smul, Finsupp.linearCombination_single,
      one_smul, wordWeightAction]
    rw [← ih, comp_reflY_eq]

omit [NeZero v] [DecidableEq I] in
/-- Embedding nonnegative coordinates in the integer root lattice preserves their character. -/
lemma linearCombination_natCast (ν : I →₀ ℕ) :
    Finsupp.linearCombination ℤ R.root (ν.mapRange (fun n : ℕ ↦ (n : ℤ)) (by simp)) =
      R.rootSum ν := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
  simp only [LusztigCartanDatum.RootDatum.rootSum, natCast_zsmul]

omit [NeZero v] in
/-- Nonnegative coordinates of the prefix root. The theorem below proves that `toNat`
does not truncate any negative coordinate for a reduced word in finite type. -/
def positiveRootVectorDegree (ω : List I) (n : ℕ) (hn : n < ω.length) : I →₀ ℕ :=
  (rootVectorDegree (R := R) ω n hn).mapRange Int.toNat (by simp)

omit [NeZero v] in
/-- Simple generators have their simple-root degrees. -/
lemma E_mem_plusWeightSpace (i : I) : E R v i ∈ plusWeightSpace R v (Finsupp.single i 1) := by
  simpa using plusHom_mem_plusWeightSpace R v (LusztigF.θ_mem_weightSpace i)

omit [NeZero v] in
/-- The first actual root vector has the corresponding simple-root degree. -/
lemma rootVector_mem_plusWeightSpace_zero
    (T : I → QuantumGroup R v ≃ₐ[k] QuantumGroup R v)
    (ω : List I) (hω : 0 < ω.length) :
    CoxeterSystem.rootVector T (E R v) ω 0 hω ∈
      plusWeightSpace R v (Finsupp.single ω[0] 1) := by
  simpa [CoxeterSystem.rootVector] using (E_mem_plusWeightSpace (R := R) (v := v) ω[0])

omit [NeZero v] in
/-- The unit has degree zero. -/
lemma one_mem_plusWeightSpace : (1 : QuantumGroup R v) ∈ plusWeightSpace R v 0 := by
  simpa using plusHom_mem_plusWeightSpace R v LusztigF.one_mem_weightSpace

omit [NeZero v] in
/-- Root-lattice degrees add under multiplication in the positive algebra. -/
lemma mul_mem_plusWeightSpace {ν μ : I →₀ ℕ} {x y : QuantumGroup R v}
    (hx : x ∈ plusWeightSpace R v ν) (hy : y ∈ plusWeightSpace R v μ) :
    x * y ∈ plusWeightSpace R v (ν + μ) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a * b, LusztigF.mul_mem_weightSpace ha hb, map_mul (plusHom R v) a b⟩

omit [NeZero v] in
/-- Taking a power multiplies the root-lattice degree by its exponent. -/
lemma pow_mem_plusWeightSpace {ν : I →₀ ℕ} {x : QuantumGroup R v}
    (hx : x ∈ plusWeightSpace R v ν) (n : ℕ) : x ^ n ∈ plusWeightSpace R v (n • ν) := by
  induction n with
  | zero => simpa using (one_mem_plusWeightSpace (R := R) (v := v))
  | succ n ih => simpa [pow_succ, succ_nsmul] using mul_mem_plusWeightSpace ih hx

omit [NeZero v] in
private lemma list_prod_mem_plusWeightSpace (l : List ((I →₀ ℕ) × QuantumGroup R v))
    (hl : ∀ a ∈ l, a.2 ∈ plusWeightSpace R v a.1) :
    (l.map Prod.snd).prod ∈ plusWeightSpace R v (l.map Prod.fst).sum := by
  induction l with
  | nil => exact one_mem_plusWeightSpace
  | cons a l ih =>
    exact mul_mem_plusWeightSpace (hl a (by simp)) (ih fun b hb ↦ hl b (by simp [hb]))

omit [NeZero v] in
/-- The root-lattice degree of an ordered monomial is the sum of its factor degrees. -/
def pbwMonomialDegree (ω : List I) (c : Fin ω.length → ℕ) : I →₀ ℕ :=
  (List.ofFn fun n : Fin ω.length ↦ c n • positiveRootVectorDegree (R := R) ω n n.2).sum

variable [Fintype I] (hA : D.cartanMatrix.IsFiniteCartan)
  (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}

include hA in
/-- A reduced-word root vector in finite type lies in any nonnegative root-lattice
piece whose character is its prefix root. No homogeneous-membership premise is assumed. -/
theorem rootVector_mem_plusWeightSpace_of_character {ω : List I} (hω : cs.IsReduced ω)
    (n : ℕ) (hn : n < ω.length) {ν : I →₀ ℕ}
    (hν : R.rootSum ν = rootVectorWeight R ω n hn) :
    CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n hn ∈
      plusWeightSpace R v ν := by
  obtain ⟨hx, hχ⟩ :=
    rootVector_mem_adjoin_and_adWeightSpace_of_isFiniteCartan (R := R) hv hA hω n hn
  exact mem_plusWeightSpace_of_mem_adWeightSpace (R.isXRegular_of_isFiniteCartan hA)
    hv hx (hν.symm ▸ hχ)

include hA in
/-- The signed prefix root has nonnegative integer coordinates, and the actual braid
root vector lies in the corresponding positive homogeneous piece. Reconstructed from
nonvanishing and character separation, not an assumed positivity or grading property. -/
theorem exists_rootVector_degree_of_isFiniteCartan {ω : List I} (hω : cs.IsReduced ω)
    (n : ℕ) (hn : n < ω.length) :
    ∃ ν : I →₀ ℕ,
      ν.mapRange (fun a : ℕ ↦ (a : ℤ)) (by simp) = rootVectorDegree (R := R) ω n hn ∧
      CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n hn ∈
        plusWeightSpace R v ν := by
  obtain ⟨hx, hχ⟩ :=
    rootVector_mem_adjoin_and_adWeightSpace_of_isFiniteCartan (R := R) hv hA hω n hn
  have hx0 : CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n hn ≠ 0 := by
    exact fun h ↦ E_ne_zero_of_not_root hv ω[n]
      (((ω.take n).map (braidEquivOfNotRoot R hv)).prod.injective
        (h.trans (map_zero _).symm))
  obtain ⟨ν, hν, hm⟩ := exists_degree_of_mem_adWeightSpace
    (R.isXRegular_of_isFiniteCartan hA) hv hx hχ hx0
  refine ⟨ν, ?_, hm⟩
  apply (linearIndependent_iff_injective_finsuppLinearCombination.1
    (R.isXRegular_of_isFiniteCartan hA))
  rw [linearCombination_natCast, rootVectorDegree_character, hν]

include hA hv in
/-- Reduced-word prefix roots have nonnegative simple-root coordinates in finite type.
This proof uses the nonzero quantum root vector over the supplied non-root-of-unity field. -/
theorem rootVectorDegree_nonneg_of_isFiniteCartan {ω : List I} (hω : cs.IsReduced ω)
    (n : ℕ) (hn : n < ω.length) (i : I) :
    0 ≤ rootVectorDegree (R := R) ω n hn i := by
  obtain ⟨ν, hν, _⟩ := exists_rootVector_degree_of_isFiniteCartan (R := R) hA hv hω n hn
  rw [← hν]
  exact Int.natCast_nonneg _

include hA in
/-- **Root-vector homogeneity in finite type**: the actual braid root vector belongs to
`U⁺` in its prefix-reflected simple-root degree. See Jantzen §8.21 (check); reconstructed.
The hypotheses are finite type and a nonzero parameter not a root of unity, over any field. -/
theorem rootVector_mem_plusWeightSpace_of_isFiniteCartan {ω : List I}
    (hω : cs.IsReduced ω) (n : ℕ) (hn : n < ω.length) :
    CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n hn ∈
      plusWeightSpace R v (positiveRootVectorDegree (R := R) ω n hn) := by
  obtain ⟨ν, hν, hm⟩ := exists_rootVector_degree_of_isFiniteCartan (R := R) hA hv hω n hn
  have he : positiveRootVectorDegree (R := R) ω n hn = ν := by
    ext i
    simp [positiveRootVectorDegree, ← hν]
  rwa [he]

include hA hv in
/-- The nonnegative degree has exactly the prefix-root character; the conversion to
nonnegative coordinates has lost no information. -/
theorem positiveRootVectorDegree_character_of_isFiniteCartan {ω : List I}
    (hω : cs.IsReduced ω) (n : ℕ) (hn : n < ω.length) :
    R.rootSum (positiveRootVectorDegree (R := R) ω n hn) = rootVectorWeight R ω n hn := by
  rw [← linearCombination_natCast, ← rootVectorDegree_character]
  congr 1
  ext i
  exact Int.toNat_of_nonneg (rootVectorDegree_nonneg_of_isFiniteCartan hA hv hω n hn i)

include hA in
/-- **Ordered-monomial homogeneity**: the degree is the sum of exponent-weighted prefix
roots. See Jantzen §§8.21–8.24 (check); reconstructed from the product formula.
This supplies the homogeneous-membership input, not the counting or spanning step. -/
theorem pbwMonomial_mem_plusWeightSpace_of_isFiniteCartan {ω : List I}
    (hω : cs.IsReduced ω) (c : Fin ω.length → ℕ) :
    CoxeterSystem.pbwMonomial (braidEquivOfNotRoot R hv) (E R v) ω c ∈
      plusWeightSpace R v (pbwMonomialDegree (R := R) ω c) := by
  rw [CoxeterSystem.pbwMonomial_eq_prod]
  let l := List.ofFn fun n : Fin ω.length ↦
    (c n • positiveRootVectorDegree (R := R) ω n n.2,
      CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n n.2 ^ c n)
  have hl : ∀ a ∈ l, a.2 ∈ plusWeightSpace R v a.1 := by
    intro a ha
    obtain ⟨n, rfl⟩ := List.mem_ofFn.1 ha
    exact pow_mem_plusWeightSpace
      (rootVector_mem_plusWeightSpace_of_isFiniteCartan hA hv hω n n.2) _
  simpa [l, List.map_ofFn, Function.comp_def, pbwMonomialDegree] using
    list_prod_mem_plusWeightSpace l hl

include hA in
/-- A two-letter degree consumer: when `aᵢⱼ = -1`, the actual vector `Tᵢ(Eⱼ)` along
a reduced word `[i,j]` lies in degree `αᵢ + αⱼ`, not merely its conjugation eigenspace. -/
theorem braidEquiv_E_mem_plusWeightSpace_twoLetter {i j : I}
    (hω : cs.IsReduced [i, j]) (hij : D.cartanMatrix i j = -1) :
    braidEquivOfNotRoot R hv i (E R v j) ∈
      plusWeightSpace R v (Finsupp.single i 1 + Finsupp.single j 1) := by
  have hm := rootVector_mem_plusWeightSpace_of_character (R := R) hA hv hω 1 (by simp)
    (ν := Finsupp.single i 1 + Finsupp.single j 1) (by
      simp [rootVectorWeight, wordWeightAction, comp_reflY_eq, R.rootSum_add,
        R.root_coroot, hij, add_comm])
  simpa [CoxeterSystem.rootVector] using hm

end QuantumGroup
