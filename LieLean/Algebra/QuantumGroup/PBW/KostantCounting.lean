/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.RootEnumeration
import LieLean.Algebra.Lie.KacMoody.CharacterAntiInvariant

/-!
# Counting prefix-root exponents by Kostant partitions

## Main definitions / results

* `prefixRootIndexEquiv`: longest-word positions are equivalent to the actual coloured
  root indices in the definition of Kostant's partition function. Finite-type multiplicity
  one and the proved prefix-root enumeration supply the equivalence.
* `prefixExponentFiberEquiv`: weight-preserving exponent-fiber equivalence.
* `card_prefixExponentFiber`: weighted prefix-root exponent counts are Kostant partitions.

These are classical combinatorial results, not quantum spanning or specialization results.

## References

Kac, *Infinite dimensional Lie algebras*, 3rd ed., Lemma 3.11, §9.7 and §10.5.
Proofs reconstructed using the existing root enumeration and root-multiplicity theorems.
-/

noncomputable section
open Module
namespace Matrix.Realization.KacMoodyAlgebra
variable {I K H : Type*} [Fintype I] [DecidableEq I] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

/-- The longest Weyl element, with finiteness derived from finite type. -/
def finiteTypeLongest : P.weylGroup hA.isGeneralizedCartan := by
  letI := P.finite_weylGroup hA
  exact (P.coxeterSystem hA.isGeneralizedCartan).longestElement

/-- A reduced-word position gives the unique colour of its positive root. -/
def prefixRootIndex {ω : List I} (hω : (P.coxeterSystem hA.isGeneralizedCartan).IsReduced ω)
    (n : Fin ω.length) : NegRootIndex P := by
  let μ := (P.prefixRoots hA.isGeneralizedCartan ω)[n.val]'
    (by simpa only [P.length_prefixRoots] using n.isLt)
  have hm : μ ∈ inversionSet P
      (((P.coxeterSystem hA.isGeneralizedCartan).wordProd ω)⁻¹ :
        P.weylGroup hA.isGeneralizedCartan) := by
    rw [← P.prefixRoots_set hA.isGeneralizedCartan hω]
    exact List.getElem_mem _
  exact ⟨⟨μ, hm.2.1⟩, ⟨0, by
    rw [finrank_rootSpace_of_mem_roots P hA (neg_mem_roots P hm.1)]
    exact Nat.zero_lt_one⟩⟩

@[simp] lemma root_prefixRootIndex {ω : List I}
    (hω : (P.coxeterSystem hA.isGeneralizedCartan).IsReduced ω) (n : Fin ω.length) :
    (prefixRootIndex P hA hω n).root =
      (P.prefixRoots hA.isGeneralizedCartan ω)[n.val]'
    (by simpa only [P.length_prefixRoots] using n.isLt) := rfl

include hA in
/-- Finite-type root indices have no nontrivial colour coordinate. -/
lemma negRootIndex_ext_of_root_eq {x y : NegRootIndex P} (h : x.root = y.root) : x = y := by
  have hx : x.2.val < 1 := lt_of_lt_of_eq x.2.isLt
    (finrank_rootSpace_of_mem_roots P hA (neg_mem_roots P x.root_mem_roots))
  have hy : y.2.val < 1 := lt_of_lt_of_eq y.2.isLt
    (finrank_rootSpace_of_mem_roots P hA (neg_mem_roots P y.root_mem_roots))
  exact NegRootIndex.ext h (by omega)

/-- Actual longest-word positions enumerate Kostant's root indices bijectively. -/
theorem bijective_prefixRootIndex {ω : List I}
    (hω : (P.coxeterSystem hA.isGeneralizedCartan).IsReduced ω)
    (hw : (P.coxeterSystem hA.isGeneralizedCartan).wordProd ω =
      finiteTypeLongest P hA) :
    Function.Bijective (prefixRootIndex P hA hω) := by
  let := P.finite_weylGroup hA
  refine ⟨?_, ?_⟩
  · intro n m h
    have he := congrArg NegRootIndex.root h
    simp only [root_prefixRootIndex] at he
    exact Fin.ext ((P.nodup_prefixRoots hA.isGeneralizedCartan hω).getElem_inj_iff.mp he)
  · intro x
    have hm : x.root ∈ P.prefixRoots hA.isGeneralizedCartan ω := by
      exact (congrArg (x.root ∈ ·)
        (P.prefixRoots_set_of_longest hA.isGeneralizedCartan hω hw)).mpr
          ⟨x.root_mem_roots, x.root_mem_posWeights⟩
    obtain ⟨n, hn, he⟩ := List.mem_iff_getElem.mp hm
    refine ⟨⟨n, by simpa using hn⟩, negRootIndex_ext_of_root_eq P hA ?_⟩
    exact he

/-- The root-index equivalence obtained from the proved longest-word enumeration. -/
def prefixRootIndexEquiv {ω : List I}
    (hω : (P.coxeterSystem hA.isGeneralizedCartan).IsReduced ω)
    (hw : (P.coxeterSystem hA.isGeneralizedCartan).wordProd ω =
      finiteTypeLongest P hA) :
    Fin ω.length ≃ NegRootIndex P :=
  Equiv.ofBijective _ (bijective_prefixRootIndex P hA hω hw)

/-- Exponents on the positions of a word, weighted by its actual prefix roots. -/
def prefixExponentWeight (ω : List I) (c : Fin ω.length → ℕ) : Dual K H :=
  ∑ n, c n • (P.prefixRoots hA.isGeneralizedCartan ω)[n.val]'
    (by simpa only [P.length_prefixRoots] using n.isLt)

/-- Transport an exponent vector to the Kostant root-index multiset. -/
def prefixExponentEquiv {ω : List I}
    (hω : (P.coxeterSystem hA.isGeneralizedCartan).IsReduced ω)
    (hw : (P.coxeterSystem hA.isGeneralizedCartan).wordProd ω =
      finiteTypeLongest P hA) :
    (Fin ω.length → ℕ) ≃ (NegRootIndex P →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm.trans
    (Finsupp.domCongr (prefixRootIndexEquiv P hA hω hw)).toEquiv

/-- Reindexing exponents preserves the weight used by Kostant's partition function. -/
theorem negRootWt_prefixExponentEquiv {ω : List I}
    (hω : (P.coxeterSystem hA.isGeneralizedCartan).IsReduced ω)
    (hw : (P.coxeterSystem hA.isGeneralizedCartan).wordProd ω =
      finiteTypeLongest P hA) (c : Fin ω.length → ℕ) :
    negRootWt P (prefixExponentEquiv P hA hω hw c) = prefixExponentWeight P hA ω c := by
  classical
  simp only [prefixExponentEquiv, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe,
    AddEquiv.coe_toEquiv, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain, negRootWt]
  rw [Finsupp.sum_mapDomain_index (h := fun (x : NegRootIndex P) (n : ℕ) ↦ n • x.root)
    (fun _ ↦ zero_nsmul _) (fun _ _ _ ↦ add_nsmul _ _ _)]
  simp [Finsupp.sum_fintype, prefixRootIndexEquiv, prefixExponentWeight]

/-- Weight fibers of longest-word exponents are exactly Kostant partition fibers. -/
def prefixExponentFiberEquiv {ω : List I}
    (hω : (P.coxeterSystem hA.isGeneralizedCartan).IsReduced ω)
    (hw : (P.coxeterSystem hA.isGeneralizedCartan).wordProd ω =
      finiteTypeLongest P hA) (β : Dual K H) :
    {c : Fin ω.length → ℕ // prefixExponentWeight P hA ω c = β} ≃
      {s : NegRootIndex P →₀ ℕ // negRootWt P s = β} :=
  (prefixExponentEquiv P hA hω hw).subtypeEquiv fun c ↦ by
    rw [negRootWt_prefixExponentEquiv]

/-- The cardinality of each weighted longest-word exponent fiber is Kostant's partition
function, with precisely the existing root-space multiplicity convention. -/
theorem card_prefixExponentFiber {ω : List I}
    (hω : (P.coxeterSystem hA.isGeneralizedCartan).IsReduced ω)
    (hw : (P.coxeterSystem hA.isGeneralizedCartan).wordProd ω =
      finiteTypeLongest P hA) (β : Dual K H) :
    Nat.card {c : Fin ω.length → ℕ // prefixExponentWeight P hA ω c = β} =
      kostantPartition P β :=
  Nat.card_congr (prefixExponentFiberEquiv P hA hω hw β)

omit [CharZero K] in
/-- In type A₂ the prefix order `[i,j,i]` gives the expected two simple-root
coordinates of every exponent vector. -/
theorem prefixExponentWeight_A2 {i j : I} (hij : A i j = -1) (hji : A j i = -1)
    (c : Fin 3 → ℕ) :
    prefixExponentWeight P hA [i, j, i] c =
      (c 0 + c 1) • P.root i + (c 1 + c 2) • P.root j := by
  simp only [prefixExponentWeight, P.prefixRoots_A2 hA.isGeneralizedCartan hij hji]
  simp [Fin.sum_univ_succ, smul_add, add_nsmul]
  abel

end Matrix.Realization.KacMoodyAlgebra

namespace QuantumGroup
open Matrix.Realization.KacMoodyAlgebra
variable {I Y K H : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)
  [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  (P : Matrix.Realization D.cartanMatrix K H) (hD : D.cartanMatrix.IsFiniteCartan)

omit [CharZero K] in
/-- Realizing the sum of the existing signed quantum prefix degrees gives exactly
Kostant's weight of the corresponding exponent vector. -/
theorem realize_sum_rootVectorDegree (ω : List I) (c : Fin ω.length → ℕ) :
    P.rootOf (fun j ↦ (∑ n : Fin ω.length, c n • rootVectorDegree (R := R) ω n n.isLt) j) =
      prefixExponentWeight P hD ω c := by
  have he : (fun j ↦ (∑ n : Fin ω.length,
      c n • rootVectorDegree (R := R) ω n n.isLt) j) =
      ∑ n : Fin ω.length, c n • (fun j ↦ rootVectorDegree (R := R) ω n n.isLt j) := by
    ext j
    simp
  rw [he, map_sum]
  simp only [map_nsmul, rootVectorDegree_realization, prefixExponentWeight]

/-- Actual quantum signed-degree exponent fibers, after realization, have Kostant's
partition cardinality. This is a counting statement, not a quantum dimension theorem. -/
theorem card_realized_rootVectorDegree_fiber {ω : List I}
    (hω : (P.coxeterSystem hD.isGeneralizedCartan).IsReduced ω)
    (hw : (P.coxeterSystem hD.isGeneralizedCartan).wordProd ω = finiteTypeLongest P hD)
    (β : Module.Dual K H) :
    Nat.card {c : Fin ω.length → ℕ //
      P.rootOf (fun j ↦ (∑ n : Fin ω.length, c n • rootVectorDegree (R := R) ω n n.isLt) j)
        = β} = kostantPartition P β := by
  simp only [realize_sum_rootVectorDegree R P hD]
  exact card_prefixExponentFiber P hD hω hw β

end QuantumGroup
