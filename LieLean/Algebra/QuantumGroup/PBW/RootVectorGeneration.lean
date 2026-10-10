/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.KostantCounting
import LieLean.Algebra.QuantumGroup.PBW.RootVectorsNotRoot

/-!
# Longest-word root vectors generate the positive quantum algebra

## Main results

* `plusWeightSpace_single`: a simple-degree piece is spanned by its simple generator.
* `exists_rootVector_eq_smul_E`: every simple generator occurs up to a nonzero scalar among
  the root vectors of any longest reduced word.
* `adjoin_rootVector_of_isFiniteCartan`: these root vectors generate the actual `U⁺`.

The coefficient field is arbitrary and the parameter is nonzero and not a root of unity.
The auxiliary classical realization is over a characteristic-zero field. This is algebra
generation, not ordered PBW spanning: straightening products remains necessary.

## References

Reconstructed from the word grading, the proved longest-word positive-root enumeration,
and braid-root homogeneity. No printed theorem number or ordered-spanning claim is asserted.
-/

open LieLean

noncomputable section

namespace LusztigF
variable {I k : Type*} [Field k]

/-- A word of simple weight consists of exactly that letter. -/
lemma wordWeight_eq_single_one_iff (w : List I) (i : I) :
    wordWeight w = Finsupp.single i 1 ↔ w = [i] := by
  classical
  constructor
  · intro h
    have hl : w.length = 1 := by simpa [h] using length_eq_sum_wordWeight w
    obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hl
    have hj : j = i := by
      by_contra hji
      have := congrArg (fun ν : I →₀ ℕ ↦ ν j) h
      simp [wordWeight, hji] at this
    subst j
    rfl
  · rintro rfl
    simp [wordWeight]

/-- The simple-degree free-algebra piece is the span of its one-letter monomial. -/
lemma weightSpace_single_one (i : I) :
    weightSpace k (Finsupp.single i 1) = Submodule.span k {θ k i} := by
  rw [weightSpace]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, wordWeight_eq_single_one_iff,
    Set.mem_singleton_iff]
  simp [monomial, eq_comm]

end LusztigF

namespace LieLean.QuantumGroup
open Matrix.Realization.KacMoodyAlgebra

variable {I Y k : Type*} [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) [Field k] (v : k)

/-- Simple-degree homogeneity in the actual quantum group is scalar proportionality to `Eᵢ`.
This uses only the word grading, without any parameter restriction or dimension theorem. -/
theorem plusWeightSpace_single (i : I) :
    plusWeightSpace R v (Finsupp.single i 1) = Submodule.span k {E R v i} := by
  rw [plusWeightSpace, LusztigF.weightSpace_single_one, Submodule.map_span]
  simp

variable {v} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  [Fintype I] {K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  (P : Matrix.Realization D.cartanMatrix K H) (hD : D.cartanMatrix.IsFiniteCartan)
  {ω : List I} (hω : (P.coxeterSystem hD.isGeneralizedCartan).IsReduced ω)
  (hw : (P.coxeterSystem hD.isGeneralizedCartan).wordProd ω = finiteTypeLongest P hD)

include P hD hω hw in
/-- Each simple generator occurs up to a nonzero scalar among longest-word root vectors.
The proof uses enumeration and simple-degree homogeneity, not PBW spanning or a supplied basis. -/
theorem exists_rootVector_eq_smul_E (i : I) :
    ∃ (n : Fin ω.length) (a : k), a ≠ 0 ∧
      CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n n.isLt = a • E R v i := by
  let := P.finite_weylGroup hD
  have hm : P.root i ∈ P.prefixRoots hD.isGeneralizedCartan ω := by
    exact (congrArg (P.root i ∈ ·)
      (P.prefixRoots_set_of_longest hD.isGeneralizedCartan hω hw)).mpr
        ⟨root_mem_roots P i, P.root_mem_posWeights i⟩
  obtain ⟨n, hn, he⟩ := List.mem_iff_getElem.mp hm
  have hn' : n < ω.length := by simpa using hn
  have hd : rootVectorDegree (R := R) ω n hn' = Finsupp.single i 1 := by
    have hr := (rootVectorDegree_realization R P ω n hn').trans he
    have hs : P.rootOf (fun j ↦ (Finsupp.single i (1 : ℤ)) j) = P.root i := by
      convert P.rootOf_single i using 2
      ext j
      simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
    have hc := P.rootOf_injective (hr.trans hs.symm)
    ext j
    exact congrFun hc j
  have hp : positiveRootVectorDegree (R := R) ω n hn' = Finsupp.single i 1 := by
    simp [positiveRootVectorDegree, hd]
  have hx := rootVector_mem_plusWeightSpace_of_isFiniteCartan (R := R) hD hv hω n hn'
  rw [hp, plusWeightSpace_single] at hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  have hx0 : CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n hn' ≠ 0 := by
    intro hz
    exact E_ne_zero_of_not_root hv ω[n]
      (((ω.take n).map (braidEquivOfNotRoot R hv)).prod.injective
        (hz.trans (map_zero _).symm))
  refine ⟨⟨n, hn'⟩, a, ?_, ha.symm⟩
  intro ha0
  exact hx0 (ha.symm.trans (by simp [ha0]))

include P hD hω hw in
/-- Longest-word root vectors generate `U⁺` at any nonzero non-root-of-unity parameter.
This is an equality of subalgebras, not a spanning theorem for ordered monomials. -/
theorem adjoin_rootVector_of_isFiniteCartan :
    Algebra.adjoin k (Set.range (fun n : Fin ω.length ↦
      CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n n.isLt)) =
      Algebra.adjoin k (Set.range (E R v)) := by
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨n, rfl⟩
    exact rootVector_mem_adjoin_of_not_root hv hω n n.isLt
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    obtain ⟨n, a, ha, he⟩ := exists_rootVector_eq_smul_E R hv P hD hω hw i
    have hm := Algebra.subset_adjoin (R := k)
      (s := Set.range (fun n : Fin ω.length ↦
        CoxeterSystem.rootVector (braidEquivOfNotRoot R hv) (E R v) ω n n.isLt)) ⟨n, rfl⟩
    dsimp only at hm
    rw [he] at hm
    simpa [smul_smul, ha] using Subalgebra.smul_mem _ hm a⁻¹

end LieLean.QuantumGroup
