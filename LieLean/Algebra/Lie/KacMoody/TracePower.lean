/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.ChevalleyInvariance
import LieLean.Algebra.Lie.KacMoody.TensorProduct
import LieLean.Algebra.Lie.KacMoody.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Actual coordinate trace-power polynomials

## Main definitions

`LieModule.tracePowerPolynomial` is the trace of the power of the matrix whose entries
are the actual matrix-coefficient linear forms of the given finite-dimensional module.
Its coefficients lie in `SymmetricAlgebra K (Module.Dual K L)`.

## References

Etingof, MIT 18.757 (Fall 2023), Lecture 10, proof of Theorem 10.1(ii).
The source works over `ℂ` for semisimple `g`; trace-power invariance is proved here for
every Lie algebra over a field, the extension step for finite type in characteristic zero.
The commutator proof below is an algebraic reconstruction of the trace-invariance step.
-/

noncomputable section
open Module

namespace Derivation

variable {K R κ : Type*} [CommRing K] [CommRing R] [Algebra K R]
  [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- Entrywise differentiation obeys the matrix product rule. -/
theorem matrix_map_mul (D : Derivation K R R) (M N : Matrix κ κ R) :
    (M * N).map D = M.map D * N + M * N.map D := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- If differentiation is an inner commutator on a matrix, it is so on all its powers. -/
theorem matrix_map_pow_of_commutator (D : Derivation K R R) (M C : Matrix κ κ R)
    (hM : M.map D = M * C - C * M) (n : ℕ) :
    (M ^ n).map D = M ^ n * C - C * M ^ n := by
  induction n with
  | zero =>
    ext i j
    simp [Matrix.one_apply, apply_ite D]
  | succ n ih =>
    rw [pow_succ, matrix_map_mul, ih, hM]
    noncomm_ring

/-- Traces of powers are killed when the entrywise derivative is a commutator. -/
theorem trace_pow_eq_zero_of_commutator (D : Derivation K R R) (M C : Matrix κ κ R)
    (hM : M.map D = M * C - C * M) (n : ℕ) : D (Matrix.trace (M ^ n)) = 0 := by
  rw [AddMonoidHom.map_trace, matrix_map_pow_of_commutator D M C hM,
    Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

end Derivation

namespace LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type} {L V κ : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [Fintype κ] [DecidableEq κ]

/-- An actual matrix coefficient of the given Lie representation, as a linear form on `L`. -/
def matrixCoefficient (b : Basis κ K V) (i j : κ) : Dual K L where
  toFun x := LinearMap.toMatrix b b (toEnd K L V x) i j
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The matrix of universal linear coordinate functions of the representation. -/
def coordinateMatrix (b : Basis κ K V) : Matrix κ κ (SymmetricAlgebra K (Dual K L)) :=
  fun i j => SymmetricAlgebra.ι K (Dual K L) (matrixCoefficient b i j)

/-- Genuine trace-power coordinate polynomial, not a formal trace symbol. -/
def tracePowerPolynomial (b : Basis κ K V) (n : ℕ) : SymmetricAlgebra K (Dual K L) :=
  Matrix.trace (coordinateMatrix (L := L) b ^ n)

/-- The coadjoint derivative of the universal representation matrix is its commutator
with the constant representation matrix. The order records the contragredient minus sign. -/
theorem coordinateMatrix_derivation (b : Basis κ K V) (x : L) :
    (coordinateMatrix (L := L) b).map
      (SymmetricAlgebra.derivation (toEnd K L (Dual K L) x)) =
    coordinateMatrix (L := L) b *
      (LinearMap.toMatrix b b (toEnd K L V x)).map (algebraMap K _) -
      (LinearMap.toMatrix b b (toEnd K L V x)).map (algebraMap K _) *
      coordinateMatrix (L := L) b := by
  ext i j
  have hc : toEnd K L (Dual K L) x (matrixCoefficient b i j) =
      (∑ k, (LinearMap.toMatrix b b (toEnd K L V x) k j) • matrixCoefficient b i k) -
      ∑ k, (LinearMap.toMatrix b b (toEnd K L V x) i k) • matrixCoefficient b k j := by
    ext y
    simp only [toEnd_apply_apply, Module.Dual.lie_apply, matrixCoefficient,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [LieHom.map_lie, Ring.lie_def, map_sub, LinearMap.toMatrix_mul,
      LinearMap.toMatrix_mul]
    simp only [Matrix.sub_apply, Matrix.mul_apply]
    rw [neg_sub]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  simp only [Matrix.map_apply, coordinateMatrix, SymmetricAlgebra.derivation_ι, hc,
    map_sub, map_sum, map_smul, Matrix.sub_apply, Matrix.mul_apply, Algebra.smul_def]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- Actual infinitesimal invariance of every trace power, including degree zero.
This supplies Etingof Lecture 10, Thm. 10.1(ii)'s invariant-polynomial construction. -/
theorem tracePowerPolynomial_invariant (b : Basis κ K V) (n : ℕ) (x : L) :
    SymmetricAlgebra.derivation (toEnd K L (Dual K L) x)
      (tracePowerPolynomial b n) = 0 :=
  Derivation.trace_pow_eq_zero_of_commutator _ _ _ (coordinateMatrix_derivation b x) n

/-- Evaluation of the genuine polynomial is the ordinary trace of the representation power. -/
theorem eval_tracePowerPolynomial (b : Basis κ K V) (n : ℕ) (x : L) :
    SymmetricAlgebra.lift (Module.Dual.eval K L x) (tracePowerPolynomial b n) =
    LinearMap.trace K V (toEnd K L V x ^ n) := by
  let ev := SymmetricAlgebra.lift (Module.Dual.eval K L x)
  change ev (Matrix.trace (coordinateMatrix b ^ n)) = _
  rw [AddMonoidHom.map_trace]
  change Matrix.trace ((coordinateMatrix (L := L) b ^ n).map ev.toRingHom) = _
  rw [Matrix.map_pow]
  have he : (coordinateMatrix (L := L) b).map ev.toRingHom =
      LinearMap.toMatrix b b (toEnd K L V x) := by
    ext i j
    simp [coordinateMatrix, matrixCoefficient, ev]
  rw [he, LinearMap.trace_eq_matrix_trace K b]
  congr 1
  exact (map_pow (LinearMap.toMatrixAlgEquiv b) _ n).symm

/-- Each trace power belongs to the actual degree component used by the graded HC API. -/
theorem tracePowerPolynomial_homogeneous (b : Basis κ K V) (n : ℕ) :
    tracePowerPolynomial (L := L) b n ∈
      SymmetricAlgebra.homogeneousSubmodule n := by
  classical
  have hp (m : ℕ) (i j : κ) : (coordinateMatrix (L := L) b ^ m) i j ∈
      SymmetricAlgebra.homogeneousSubmodule m := by
    induction m generalizing i j with
    | zero =>
      simp only [pow_zero, Matrix.one_apply]
      split_ifs
      · simp [SymmetricAlgebra.homogeneousSubmodule]
      · exact Submodule.zero_mem _
    | succ m ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Submodule.sum_mem
      intro k _
      change _ ∈ LinearMap.range (SymmetricAlgebra.ι K (Dual K L)) ^ (m + 1)
      rw [pow_succ]
      exact Submodule.mul_mem_mul (ih i k) (LinearMap.mem_range_self _ _)
  exact Submodule.sum_mem _ fun i _ => hp n i i

end LieModule

namespace Matrix.Realization.KacMoodyAlgebra

open LieModule

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V κ : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [Fintype κ] [DecidableEq κ]

/-- Restriction of the universal representation matrix in an actual weight basis
is diagonal, with the actual weights on its diagonal. -/
theorem coordinateMatrix_cartanRestriction (b : Basis κ K V) (wt : κ → Dual K H)
    (hb : ∀ j, b j ∈ weightSpace P V (wt j)) :
    (coordinateMatrix (L := P.KacMoodyAlgebra) b).map (coordinateCartanRestriction P) =
      Matrix.diagonal (fun j => SymmetricAlgebra.ι K (Dual K H) (wt j)) := by
  ext i j
  have he : (h P).dualMap (matrixCoefficient b i j) =
      if i = j then wt j else 0 := by
    ext a
    simp only [LinearMap.dualMap_apply, matrixCoefficient, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.toMatrix_apply, toEnd_apply_apply]
    rw [hb j a]
    by_cases hij : i = j
    · subst i
      simp
    · simp [hij]
  simp only [Matrix.map_apply, coordinateMatrix, coordinateCartanRestriction,
    SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, he, Matrix.diagonal_apply]
  split_ifs <;> simp_all

/-- Cartan restriction of an invariant trace polynomial is the power sum of the actual
weight-basis weights. Repeated weights occur once per independent weight vector. -/
theorem coordinateCartanRestriction_tracePowerPolynomial (b : Basis κ K V)
    (wt : κ → Dual K H) (hb : ∀ j, b j ∈ weightSpace P V (wt j)) (n : ℕ) :
    coordinateCartanRestriction P (tracePowerPolynomial b n) =
      ∑ j, SymmetricAlgebra.ι K (Dual K H) (wt j) ^ n := by
  rw [tracePowerPolynomial, AddMonoidHom.map_trace]
  change Matrix.trace ((coordinateMatrix b ^ n).map
    (coordinateCartanRestriction P).toRingHom) = _
  rw [Matrix.map_pow]
  have he := coordinateMatrix_cartanRestriction P b wt hb
  change (coordinateMatrix b).map (coordinateCartanRestriction P).toRingHom = _ at he
  rw [he, Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

open Classical in
/-- Grouping equal weights gives precisely actual weight-space dimensions, not
postulated multiplicities. The finite sum is over the weights occurring in the basis. -/
theorem coordinateCartanRestriction_tracePowerPolynomial_multiplicity
    (b : Basis κ K V) (wt : κ → Dual K H)
    (hb : ∀ j, b j ∈ weightSpace P V (wt j)) (n : ℕ) :
    coordinateCartanRestriction P (tracePowerPolynomial b n) =
      ∑ μ ∈ Finset.univ.image wt,
        (finrank K (weightSpace P V μ) : K) •
          SymmetricAlgebra.ι K (Dual K H) μ ^ n := by
  classical
  rw [coordinateCartanRestriction_tracePowerPolynomial P b wt hb]
  rw [← Finset.sum_fiberwise_of_maps_to' (fun j (_ : j ∈ Finset.univ) =>
    Finset.mem_image_of_mem wt (Finset.mem_univ j))
    (fun μ => SymmetricAlgebra.ι K (Dual K H) μ ^ n)]
  apply Finset.sum_congr rfl
  intro μ _
  have hm := finrank_weightSpace_of_basis hb μ (Set.toFinite {j | wt j = μ})
  have hs : (Set.toFinite {j | wt j = μ}).toFinset =
      Finset.univ.filter (fun j => wt j = μ) := by ext j; simp
  rw [hs] at hm
  simp [hm, Algebra.smul_def]

/-- Basis-free expression of the restriction using the actual weight multiplicities.
The `finsum` has finite support, established from the finite weight basis. -/
theorem coordinateCartanRestriction_tracePowerPolynomial_finsum
    (b : Basis κ K V) (wt : κ → Dual K H)
    (hb : ∀ j, b j ∈ weightSpace P V (wt j)) (n : ℕ) :
    coordinateCartanRestriction P (tracePowerPolynomial b n) =
      ∑ᶠ μ : Dual K H, (finrank K (weightSpace P V μ) : K) •
        SymmetricAlgebra.ι K (Dual K H) μ ^ n := by
  classical
  rw [coordinateCartanRestriction_tracePowerPolynomial_multiplicity P b wt hb]
  symm
  apply finsum_eq_sum_of_support_subset
  intro μ hμ
  by_contra hn
  have hz : (Set.toFinite {j | wt j = μ}).toFinset = ∅ := by
    ext j
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.notMem_empty, iff_false]
    intro hj
    exact hn (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩)
  have hm := finrank_weightSpace_of_basis hb μ (Set.toFinite {j | wt j = μ})
  rw [hz, Finset.card_empty] at hm
  simp [Function.mem_support, hm] at hμ

omit [Fintype κ] [DecidableEq κ] in
/-- Etingof Lecture 10, Thm. 10.1(ii), trace-power extension step for every genuine
finite-dimensional module of the actual finite-type realization. Diagonalizability is
proved by the production finite-dimensional representation theory, not assumed.
No extension, character triangularity, or Chevalley surjectivity premise occurs. -/
theorem exists_invariant_tracePower_extension [CharZero K] [FiniteDimensional K H]
    [FiniteDimensional K V] (hA : A.IsFiniteCartan) (n : ℕ) :
    ∃ F : SymmetricAlgebra K (Dual K P.KacMoodyAlgebra),
      F ∈ SymmetricAlgebra.homogeneousSubmodule n ∧
      (∀ x : P.KacMoodyAlgebra,
        SymmetricAlgebra.derivation (toEnd K P.KacMoodyAlgebra
          (Dual K P.KacMoodyAlgebra) x) F = 0) ∧
      (∀ x : P.KacMoodyAlgebra,
        SymmetricAlgebra.lift (Module.Dual.eval K P.KacMoodyAlgebra x) F =
          LinearMap.trace K V (toEnd K P.KacMoodyAlgebra V x ^ n)) ∧
      coordinateCartanRestriction P F =
        ∑ᶠ μ : Dual K H, (finrank K (weightSpace P V μ) : K) •
          SymmetricAlgebra.ι K (Dual K H) μ ^ n := by
  classical
  let hV : IsCategoryO P V := isCategoryO_of_finiteDimensional hA
  let b := hV.weightBasis
  let := FiniteDimensional.fintypeBasisIndex b
  refine ⟨tracePowerPolynomial b n, tracePowerPolynomial_homogeneous b n,
    tracePowerPolynomial_invariant b n, eval_tracePowerPolynomial b n, ?_⟩
  exact coordinateCartanRestriction_tracePowerPolynomial_finsum P b Sigma.fst
    hV.weightBasis_mem n

omit [Fintype κ] [DecidableEq κ] in
/-- The invariant extensions needed for Etingof's character/orbit-sum argument, for
all dominant integral highest weights. Finite-dimensionality of `L(Λ)` is proved by the
production finite-type theorem, not made an additional premise. This theorem does not
assert that these power sums span the Weyl invariant polynomials. -/
theorem exists_dominant_tracePower_extension [CharZero K] [FiniteDimensional K H]
    (hA : A.IsFiniteCartan) (Λ : Dual K H) (hΛ : P.IsDominantIntegral Λ) (n : ℕ) :
    ∃ F : SymmetricAlgebra K (Dual K P.KacMoodyAlgebra),
      F ∈ SymmetricAlgebra.homogeneousSubmodule n ∧
      (∀ x : P.KacMoodyAlgebra,
        SymmetricAlgebra.derivation (toEnd K P.KacMoodyAlgebra
          (Dual K P.KacMoodyAlgebra) x) F = 0) ∧
      coordinateCartanRestriction P F =
        ∑ᶠ μ : Dual K H, (finrank K (weightSpace P (IrreducibleModule P Λ) μ) : K) •
          SymmetricAlgebra.ι K (Dual K H) μ ^ n := by
  have := IrreducibleModule.finiteDimensional (P := P) hA hΛ
  obtain ⟨F, hF, hi, _, hr⟩ :=
    exists_invariant_tracePower_extension P (V := IrreducibleModule P Λ) hA n
  exact ⟨F, hF, hi, hr⟩

end Matrix.Realization.KacMoodyAlgebra
