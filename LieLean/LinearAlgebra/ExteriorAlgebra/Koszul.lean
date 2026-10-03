/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Basis.Basic
import LieLean.RingTheory.MvPolynomial.EulerIdentity

/-!
# Concrete finite-support Koszul operators

## Main definitions

Contraction tensored with polynomial multiplication, and exterior multiplication tensored
with polynomial differentiation. Every sum is over an explicit finite set; the basis index
is arbitrary, not necessarily finite.

## Main results

* `term_anticommutator`: the coordinate anticommutator cancels the mixed terms.
* `anticommutator`: equality of actual tensor-product endomorphisms.
* `delta_sq`: the differential squares to zero over any commutative ring.
* `anticommutator_homogeneous`: the anticommutator is total-degree multiplication on the
  span of supported exterior basis words tensored with homogeneous polynomials.

A support-independent global operator is not constructed here. This file does not identify
the operators with a CE associated-graded differential and does not assert CE or BGG exactness.

## References

Reconstructed directly from the contraction and polynomial Leibniz identities in Mathlib.
-/

open scoped TensorProduct BigOperators

noncomputable section

namespace ExteriorAlgebra.Koszul

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Left multiplication by a basis vector in the exterior algebra. -/
def wedge (b : Module.Basis I R M) (i : I) :
    Module.End R (ExteriorAlgebra R M) :=
  LinearMap.mulLeft R (ι R (b i))

/-- Existing Clifford contraction at quadratic form zero, in basis coordinates. -/
def contract (b : Module.Basis I R M) (i : I) :
    Module.End R (ExteriorAlgebra R M) :=
  CliffordAlgebra.contractLeft (b.coord i)

/-- One summand of the polynomial Koszul differential. -/
def deltaTerm (b : Module.Basis I R M) (i : I) :
    Module.End R (ExteriorAlgebra R M ⊗[R] MvPolynomial I R) :=
  TensorProduct.map (contract b i) (LinearMap.mulLeft R (MvPolynomial.X i))

/-- One summand of the polynomial derivative homotopy. -/
def homotopyTerm (b : Module.Basis I R M) (i : I) :
    Module.End R (ExteriorAlgebra R M ⊗[R] MvPolynomial I R) :=
  TensorProduct.map (wedge b i) (MvPolynomial.pderiv i).toLinearMap

/-- Koszul differential summed over an explicit finite set of coordinates. -/
def delta (b : Module.Basis I R M) (s : Finset I) :
    Module.End R (ExteriorAlgebra R M ⊗[R] MvPolynomial I R) :=
  ∑ i ∈ s, deltaTerm b i

/-- Derivative homotopy summed over an explicit finite set of coordinates. -/
def homotopy (b : Module.Basis I R M) (s : Finset I) :
    Module.End R (ExteriorAlgebra R M ⊗[R] MvPolynomial I R) :=
  ∑ i ∈ s, homotopyTerm b i

/-- The exterior number operator on the specified finite coordinate subspace. -/
def exteriorNumber (b : Module.Basis I R M) (s : Finset I) :
    Module.End R (ExteriorAlgebra R M) :=
  ∑ i ∈ s, (wedge b i).comp (contract b i)

@[simp]
theorem wedge_apply (b : Module.Basis I R M) (i : I) (e : ExteriorAlgebra R M) :
    wedge b i e = ι R (b i) * e := rfl

@[simp]
theorem deltaTerm_tmul (b : Module.Basis I R M) (i : I)
    (e : ExteriorAlgebra R M) (p : MvPolynomial I R) :
    deltaTerm b i (e ⊗ₜ[R] p) = contract b i e ⊗ₜ[R] (MvPolynomial.X i * p) := rfl

@[simp]
theorem homotopyTerm_tmul (b : Module.Basis I R M) (i : I)
    (e : ExteriorAlgebra R M) (p : MvPolynomial I R) :
    homotopyTerm b i (e ⊗ₜ[R] p) = wedge b i e ⊗ₜ[R] MvPolynomial.pderiv i p := rfl

/-- Contraction and exterior multiplication satisfy the coordinate Clifford relation. -/
theorem contract_wedge (b : Module.Basis I R M) (i j : I) (e : ExteriorAlgebra R M) :
    contract b i (wedge b j e) = (b.coord i (b j)) • e - wedge b j (contract b i e) :=
  CliffordAlgebra.contractLeft_ι_mul _ _ _

/-- Off-diagonal mixed terms cancel, and diagonal terms are precisely the two number terms.
This is an identity of concrete tensor operators, not an assumed anticommutator relation. -/
theorem term_anticommutator (b : Module.Basis I R M) [DecidableEq I] (i j : I)
    (e : ExteriorAlgebra R M) (p : MvPolynomial I R) :
    deltaTerm b i (homotopyTerm b j (e ⊗ₜ[R] p)) +
      homotopyTerm b j (deltaTerm b i (e ⊗ₜ[R] p)) =
    if i = j then e ⊗ₜ[R] (MvPolynomial.X i * MvPolynomial.pderiv i p) +
      wedge b i (contract b i e) ⊗ₜ[R] p else 0 := by
  simp only [deltaTerm_tmul, homotopyTerm_tmul, contract_wedge,
    MvPolynomial.pderiv_mul, TensorProduct.sub_tmul, TensorProduct.tmul_add]
  by_cases h : i = j
  · subst j
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      one_smul, MvPolynomial.pderiv_X_self, one_mul, ite_true]
    abel
  · simp [Module.Basis.coord_apply, Module.Basis.repr_self, h]

/-- The finite-support Koszul anticommutator, before restricting either homogeneous degree. -/
theorem anticommutator_tmul (b : Module.Basis I R M) (s : Finset I)
    (e : ExteriorAlgebra R M) (p : MvPolynomial I R) :
    delta b s (homotopy b s (e ⊗ₜ[R] p)) +
      homotopy b s (delta b s (e ⊗ₜ[R] p)) =
    e ⊗ₜ[R] (∑ i ∈ s, MvPolynomial.X i * MvPolynomial.pderiv i p) +
      exteriorNumber b s e ⊗ₜ[R] p := by
  classical
  simp only [delta, homotopy, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_comm (f := fun j i =>
    deltaTerm b i (homotopyTerm b j (e ⊗ₜ[R] p)))]
  simp only [← Finset.sum_add_distrib, term_anticommutator]
  simp only [Finset.sum_ite_eq]
  simp [Finset.sum_add_distrib, TensorProduct.tmul_sum, exteriorNumber,
    LinearMap.sum_apply, TensorProduct.sum_tmul]

/-- Exterior multiplication operators anticommute. -/
theorem wedge_wedge (b : Module.Basis I R M) (i j : I) (e : ExteriorAlgebra R M) :
    wedge b i (wedge b j e) = -(wedge b j (wedge b i e)) := by
  simp only [wedge_apply, ← mul_assoc]
  rw [eq_neg_of_add_eq_zero_left (ι_add_mul_swap (b i) (b j)), neg_mul]

/-- One summand of the exterior number operator commutes past a generator. -/
theorem wedge_contract_wedge (b : Module.Basis I R M) (i j : I)
    (e : ExteriorAlgebra R M) :
    wedge b i (contract b i (wedge b j e)) =
      b.coord i (b j) • wedge b i e + wedge b j (wedge b i (contract b i e)) := by
  rw [contract_wedge, map_sub, map_smul, wedge_wedge, sub_neg_eq_add]

/-- On a generator in the summation set, exterior number increases by one. -/
theorem exteriorNumber_wedge (b : Module.Basis I R M) (s : Finset I)
    (j : I) (hj : j ∈ s) (e : ExteriorAlgebra R M) :
    exteriorNumber b s (wedge b j e) =
      wedge b j e + wedge b j (exteriorNumber b s e) := by
  classical
  simp only [exteriorNumber, LinearMap.sum_apply, LinearMap.comp_apply,
    wedge_contract_wedge, Finset.sum_add_distrib, map_sum]
  congr 1
  simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, hj]

/-- An ordered exterior monomial in the chosen basis. Repetitions are allowed and give zero. -/
def basisWord (b : Module.Basis I R M) (l : List I) : ExteriorAlgebra R M :=
  (l.map fun i => ι R (b i)).prod

/-- Exterior number counts the length of a basis word supported in the finite summation set. -/
theorem exteriorNumber_basisWord (b : Module.Basis I R M) (s : Finset I)
    (l : List I) (hl : ∀ i ∈ l, i ∈ s) :
    exteriorNumber b s (basisWord b l) = l.length • basisWord b l := by
  induction l with
  | nil => simp [basisWord, exteriorNumber, contract]
  | cons j l ih =>
    change exteriorNumber b s (wedge b j (basisWord b l)) =
      (l.length + 1) • wedge b j (basisWord b l)
    rw [exteriorNumber_wedge b s j (hl j (by simp)),
      ih (fun i hi => hl i (by simp [hi])), map_nsmul, add_smul, one_smul, add_comm]

/-- The polynomial-plus-exterior degree anticommutator on actual homogeneous tensors,
with arbitrary basis index type and a finite set containing both supports. -/
theorem anticommutator_basisWord (b : Module.Basis I R M) (s : Finset I)
    (l : List I) (hl : ∀ i ∈ l, i ∈ s) (p : MvPolynomial I R) (n : ℕ)
    (hp : p.IsHomogeneous n) (hs : p.vars ⊆ s) :
    delta b s (homotopy b s (basisWord b l ⊗ₜ[R] p)) +
      homotopy b s (delta b s (basisWord b l ⊗ₜ[R] p)) =
    (n + l.length) • (basisWord b l ⊗ₜ[R] p) := by
  rw [anticommutator_tmul, hp.sum_X_mul_pderiv_of_vars_subset s hs,
    exteriorNumber_basisWord b s l hl, TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul', ← add_smul]

/-- The anticommutator as an equality of endomorphisms on the entire tensor product. -/
theorem anticommutator (b : Module.Basis I R M) (s : Finset I) :
    (delta b s).comp (homotopy b s) + (homotopy b s).comp (delta b s) =
      TensorProduct.map LinearMap.id
        (∑ i ∈ s, (LinearMap.mulLeft R (MvPolynomial.X i)).comp
          (MvPolynomial.pderiv i).toLinearMap) +
      TensorProduct.map (exteriorNumber b s) LinearMap.id := by
  apply TensorProduct.ext'
  intro e p
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearMap.sum_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe] using
    anticommutator_tmul b s e p

/-- Each coordinate differential squares to zero, using the existing contraction theorem. -/
theorem deltaTerm_sq (b : Module.Basis I R M) (i : I) :
    deltaTerm b i * deltaTerm b i = 0 := by
  apply TensorProduct.ext'
  intro e p
  change deltaTerm b i (deltaTerm b i (e ⊗ₜ[R] p)) = 0
  simp [contract, CliffordAlgebra.contractLeft_contractLeft]

/-- Distinct coordinate differentials anticommute (the relation also holds on the diagonal). -/
theorem deltaTerm_anticomm (b : Module.Basis I R M) (i j : I) :
    deltaTerm b i * deltaTerm b j = -(deltaTerm b j * deltaTerm b i) := by
  apply TensorProduct.ext'
  intro e p
  change deltaTerm b i (deltaTerm b j (e ⊗ₜ[R] p)) =
    -(deltaTerm b j (deltaTerm b i (e ⊗ₜ[R] p)))
  simp only [deltaTerm_tmul, contract]
  rw [CliffordAlgebra.contractLeft_comm, TensorProduct.neg_tmul, mul_left_comm]

/-- The finite-coordinate Koszul operator is genuinely a differential, over any commutative ring.
No characteristic-two cancellation or invertibility assumption is used. -/
theorem delta_sq (b : Module.Basis I R M) (s : Finset I) :
    delta b s * delta b s = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [delta]
  | @insert i s hi ih =>
    have hc : deltaTerm b i * delta b s = -(delta b s * deltaTerm b i) := by
      simp only [delta, Finset.mul_sum, Finset.sum_mul]
      calc
        _ = ∑ j ∈ s, -(deltaTerm b j * deltaTerm b i) :=
          Finset.sum_congr rfl fun j _ => deltaTerm_anticomm b i j
        _ = _ := Finset.sum_neg_distrib (fun j => deltaTerm b j * deltaTerm b i)
    simp only [delta, Finset.sum_insert hi]
    change (deltaTerm b i + delta b s) * (deltaTerm b i + delta b s) = 0
    rw [add_mul, mul_add, mul_add, deltaTerm_sq, ih, hc]
    abel

/-- Homogeneous finite-support tensors: the span of degree-`q` basis words tensored with
homogeneous degree-`n` polynomials, with both sets of coordinates contained in `s`. -/
def homogeneousTensors (b : Module.Basis I R M) (s : Finset I) (n q : ℕ) :
    Submodule R (ExteriorAlgebra R M ⊗[R] MvPolynomial I R) :=
  Submodule.span R {z | ∃ (l : List I) (p : MvPolynomial I R),
    l.length = q ∧ (∀ i ∈ l, i ∈ s) ∧ p.IsHomogeneous n ∧ p.vars ⊆ s ∧
      z = basisWord b l ⊗ₜ[R] p}

/-- The actual Koszul differential and derivative homotopy have anticommutator
`(n + q) id` on every homogeneous finite-support tensor, not only on pure tensors. -/
theorem anticommutator_homogeneous (b : Module.Basis I R M) (s : Finset I) (n q : ℕ)
    (z : ExteriorAlgebra R M ⊗[R] MvPolynomial I R)
    (hz : z ∈ homogeneousTensors b s n q) :
    delta b s (homotopy b s z) + homotopy b s (delta b s z) = (n + q) • z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, p, hlq, hl, hp, hs, rfl⟩ := hz
    simpa only [hlq] using anticommutator_basisWord b s l hl p n hp hs
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [map_add, nsmul_add, add_add_add_comm] using congrArg₂ (· + ·) hx hy
  | smul a x _ hx =>
    simpa only [map_smul, smul_add, smul_comm a (n + q)] using congrArg (a • ·) hx

end ExteriorAlgebra.Koszul
