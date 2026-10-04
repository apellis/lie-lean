/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.RootVectorGrading
import LieLean.Algebra.Lie.KacMoody.WeylLength
import LieLean.Algebra.Lie.KacMoody.FiniteType
import LieLean.GroupTheory.Coxeter.Longest

/-!
# Prefix roots in the classical realization

The prefix roots are computed in the very realization used by Kostant's partition function.
Their enumeration is proved from the inversion-set recursion, not assumed.

## Main results

* `prefixRoots_set`: a reduced word enumerates the inversion set of its inverse.

## References

Kac, *Infinite dimensional Lie algebras*, 3rd ed., Lemma 3.11 (length criterion). The statement is
S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr. Math. 204,
Birkhäuser 2002, Lemma 1.3.14.
Our own proofs, from the existing inversion-set API.
-/

open LieLean

noncomputable section
open Module
namespace Matrix.Realization
variable {I K H : Type*} [Fintype I] [DecidableEq I] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (P : Realization A K H) (hA : A.IsGeneralizedCartan)

/-- The ordered prefix-reflected simple roots of a word. -/
def prefixRoots : List I → List (Dual K H)
  | [] => []
  | i :: ω => P.root i :: (prefixRoots ω).map (P.reflection hA i)

omit [DecidableEq I] [CharZero K] in
@[simp] lemma length_prefixRoots (ω : List I) :
    (P.prefixRoots hA ω).length = ω.length := by
  induction ω with
  | nil => rfl
  | cons i ω ih => simp [prefixRoots, ih]

omit [DecidableEq I] [CharZero K] in
/-- The entry at position `n` is the simple root acted on by the preceding prefix. -/
lemma getElem_prefixRoots (ω : List I) (n : ℕ) (hn : n < ω.length) :
    (P.prefixRoots hA ω)[n]'(by simpa using hn) =
      ((ω.take n).map (P.reflection hA)).prod (P.root ω[n]) := by
  induction ω generalizing n with
  | nil => simp at hn
  | cons i ω ih =>
    cases n with
    | zero => simp [prefixRoots]
    | succ n => simpa [prefixRoots, LinearEquiv.mul_apply] using
        congrArg (P.reflection hA i) (ih n (Nat.lt_of_succ_lt_succ hn))

open KacMoodyAlgebra

private lemma not_descent_inv_tail {i : I} {ω : List I}
    (hω : (P.coxeterSystem hA).IsReduced (i :: ω)) :
    ¬(P.coxeterSystem hA).IsRightDescent ((P.coxeterSystem hA).wordProd ω)⁻¹ i := by
  have ht : (P.coxeterSystem hA).IsReduced ω := by
    simpa using hω.drop 1
  rw [(P.coxeterSystem hA).not_isRightDescent_iff]
  rw [← (P.coxeterSystem hA).length_inv
    (((P.coxeterSystem hA).wordProd ω)⁻¹ * (P.coxeterSystem hA).simple i)]
  simpa [mul_inv_rev, CoxeterSystem.wordProd_cons, CoxeterSystem.IsReduced] using
    hω.trans (congrArg Nat.succ ht.symm)

/-- A reduced word lists exactly the positive roots made negative by its inverse.
Reconstructed from Kac Lemma 3.11, with no finite-type restriction; the statement is Kumar
Lemma 1.3.14. -/
theorem prefixRoots_set {ω : List I} (hω : (P.coxeterSystem hA).IsReduced ω) :
    {μ | μ ∈ P.prefixRoots hA ω} =
      inversionSet P (((P.coxeterSystem hA).wordProd ω)⁻¹ : P.weylGroup hA) := by
  induction ω with
  | nil => simp [prefixRoots, inversionSet_one]
  | cons i ω ih =>
    have ht : (P.coxeterSystem hA).IsReduced ω := by simpa using hω.drop 1
    have hd := P.not_descent_inv_tail hA hω
    have hnot : P.root i ∉ inversionSet P
        (((P.coxeterSystem hA).wordProd ω)⁻¹ : P.weylGroup hA) := by
      rw [root_mem_inversionSet_iff, P.apply_root_mem_negWeights_iff hA]
      exact hd
    have hmem : P.root i ∈ inversionSet P
        ((((P.coxeterSystem hA).wordProd ω)⁻¹ : P.weylGroup hA).val *
          P.reflection hA i) := by
      rw [root_mem_inversionSet_mul_reflection_iff, P.apply_root_mem_posWeights_iff hA]
      exact hd
    have himg := image_reflection_inversionSet_diff P hA
      (((P.coxeterSystem hA).wordProd ω)⁻¹ : P.weylGroup hA) i
    rw [Set.sdiff_singleton_eq_self hnot] at himg
    rw [CoxeterSystem.wordProd_cons, _root_.mul_inv_rev,
      CoxeterSystem.inv_simple, Subgroup.coe_mul, coxeterSystem_simple]
    rw [← Set.insert_sdiff_self_of_mem hmem, ← himg, ← ih ht]
    ext μ
    simp [prefixRoots, Set.mem_image]

/-- Prefix roots of a reduced word occur without repetition. -/
theorem nodup_prefixRoots {ω : List I} (hω : (P.coxeterSystem hA).IsReduced ω) :
    (P.prefixRoots hA ω).Nodup := by
  induction ω with
  | nil => simp [prefixRoots]
  | cons i ω ih =>
    have ht : (P.coxeterSystem hA).IsReduced ω := by simpa using hω.drop 1
    refine List.nodup_cons.mpr ⟨?_, (ih ht).map (P.reflection hA i).injective⟩
    rintro h
    obtain ⟨μ, hμ, he⟩ := List.mem_map.mp h
    have hp : μ ∈ P.posWeights :=
      (show μ ∈ inversionSet P
        (((P.coxeterSystem hA).wordProd ω)⁻¹ : P.weylGroup hA) from
          (congrArg (μ ∈ ·) (P.prefixRoots_set hA ht)).mp hμ).2.1
    have he' : μ = -P.root i := by
      simpa using congrArg (P.reflection hA i) he
    rw [he'] at hp
    exact Set.disjoint_left.mp P.disjoint_posWeights_negWeights hp
      ((P.neg_mem_negWeights_iff).mpr (P.root_mem_posWeights i))

/-- The longest Weyl element sends every positive weight to a negative weight. -/
theorem longestElement_apply_mem_negWeights [Finite (P.weylGroup hA)]
    {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    (((P.coxeterSystem hA).longestElement : P.weylGroup hA).val μ) ∈ P.negWeights := by
  let w := (P.coxeterSystem hA).longestElement
  have hs : ∀ i, -(w.val (P.root i)) ∈ AddSubmonoid.closure (Set.range P.root) := by
    intro i
    obtain ⟨k, hk, he⟩ := (P.isRightDescent_coxeterSystem_iff hA).mp
      ((P.coxeterSystem hA).isRightDescent_longestElement i)
    exact P.mem_closure_range_root_iff.mpr ⟨k, hk, by simp [w, he]⟩
  obtain ⟨k, hk, rfl⟩ := hμ
  have hc : P.rootOf k ∈ AddSubmonoid.closure (Set.range P.root) :=
    P.mem_closure_range_root_iff.mpr ⟨k, hk.1, rfl⟩
  have hn : -(w.val (P.rootOf k)) ∈ AddSubmonoid.closure (Set.range P.root) := by
    generalize P.rootOf k = x at hc ⊢
    induction hc using AddSubmonoid.closure_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hs i
    | zero => simp
    | add x y _ _ hx hy => simpa [map_add, add_comm] using add_mem hx hy
  obtain ⟨l, hl, he⟩ := P.mem_closure_range_root_iff.mp hn
  refine ⟨l, ⟨hl, ?_⟩, by simpa using congrArg Neg.neg he⟩
  intro hl0
  have hz : P.rootOf k = 0 := w.val.injective (by simpa [hl0] using he.symm)
  exact hk.2 (P.rootOf_injective (hz.trans (map_zero _).symm))

/-- A reduced expression for the longest Weyl element enumerates all positive roots,
without any assumed root enumeration. -/
theorem prefixRoots_set_of_longest [Finite (P.weylGroup hA)] {ω : List I}
    (hω : (P.coxeterSystem hA).IsReduced ω)
    (hw : (P.coxeterSystem hA).wordProd ω = (P.coxeterSystem hA).longestElement) :
    {μ | μ ∈ P.prefixRoots hA ω} = roots P ∩ P.posWeights := by
  rw [P.prefixRoots_set hA hω, hw, (P.coxeterSystem hA).inv_longestElement]
  ext μ
  exact ⟨fun h ↦ ⟨h.1, h.2.1⟩,
    fun h ↦ ⟨h.1, h.2, P.longestElement_apply_mem_negWeights hA h.2⟩⟩

omit [DecidableEq I] [CharZero K] in
/-- The two standard A₂ orders really yield the three positive roots, in prefix order.
This also checks the order of composition in `prefixRoots`. -/
theorem prefixRoots_A2 {i j : I} (hij : A i j = -1) (hji : A j i = -1) :
    P.prefixRoots hA [i, j, i] = [P.root i, P.root i + P.root j, P.root j] := by
  have h₁ : P.reflection hA i (P.root j) = P.root i + P.root j := by
    rw [P.reflection_root, hij]
    module
  have h₂ : P.reflection hA j (P.root i) = P.root i + P.root j := by
    rw [P.reflection_root, hji]
    module
  simp [prefixRoots, h₁, h₂, map_add]

end Matrix.Realization

namespace LieLean.QuantumGroup
variable {I Y K H : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)
  [Field K] [AddCommGroup H] [Module K H] (P : Matrix.Realization D.cartanMatrix K H)

omit [DecidableEq I] in
private lemma realize_cartan_reflection (i : I) (β : I →₀ ℤ) :
    P.rootOf (fun j ↦ (β - (β.sum fun j a ↦ a * D.cartanMatrix i j) •
      Finsupp.single i 1 : I →₀ ℤ) j) =
      P.reflection D.isGeneralizedCartan_cartanMatrix i (P.rootOf fun j ↦ β j) := by
  classical
  rw [P.reflection_rootOf]
  congr 1
  ext j
  simp [Finsupp.sum_fintype, Matrix.mulVec, dotProduct, mul_comm,
    Finsupp.single_apply, Pi.single_apply, eq_comm]

omit [DecidableEq I] in
/-- The integer degree used for quantum PBW homogeneity is the classical prefix root
in any realization of the same Cartan matrix. No positivity or enumeration is assumed. -/
theorem rootVectorDegree_realization (ω : List I) (n : ℕ) (hn : n < ω.length) :
    P.rootOf (fun j ↦ rootVectorDegree (R := R) ω n hn j) =
      (P.prefixRoots D.isGeneralizedCartan_cartanMatrix ω)[n]'(by simpa using hn) := by
  classical
  rw [P.getElem_prefixRoots _ ω n hn, rootVectorDegree_eq_cartan_fold]
  generalize ω.take n = w
  generalize ω[n] = i
  have hf : ∀ (w : List I) (β : I →₀ ℤ),
      P.rootOf (fun j ↦ (w.foldr (fun i β ↦
        β - (β.sum fun j a ↦ a * D.cartanMatrix i j) • Finsupp.single i 1) β) j) =
      (w.map (P.reflection D.isGeneralizedCartan_cartanMatrix)).prod
        (P.rootOf fun j ↦ β j) := by
    intro w β
    induction w with
    | nil => rfl
    | cons i w ih =>
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, LinearEquiv.mul_apply,
        realize_cartan_reflection, ih]
  rw [hf]
  congr 1
  convert P.rootOf_single i using 2
  ext j
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

end LieLean.QuantumGroup
