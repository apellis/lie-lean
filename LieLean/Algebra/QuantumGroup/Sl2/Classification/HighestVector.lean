/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Tactic

/-!
# Eigenvector strings for q-commuting endomorphisms

For endomorphisms satisfying `K * T = q • (T * K)`, applying `T` multiplies the
`K`-eigenvalue by `q`. If `q` has infinite multiplicative order, a string starting
at a nonzero eigenvalue terminates in finite dimension. Over an algebraically closed
field, injectivity of `K` therefore gives a nonzero eigenvector killed by `T`.

## Main results

* `Module.End.apply_pow_eq_smul_of_q_commute`: the eigenvalue along a string.
* `Module.End.exists_last_nonzero_pow_of_q_commute`: a finite nonzero string with
  a terminal vector killed by `T`.
* `Module.End.exists_highestWeight_of_q_commute`: existence of a highest vector.

## References

The elementary eigenvector and linear-independence arguments are reconstructed here;
no external source was consulted. No quantum-group structure is used.
-/

namespace Module.End

/-- Multiplying distinct powers of a nonzero scalar of infinite multiplicative order
by a nonzero scalar preserves distinctness. The elementary argument is reconstructed here. -/
theorem pow_mul_injective_of_forall_pow_ne_one
    {k : Type*} [GroupWithZero k] {q a : k} (hq0 : q ≠ 0)
    (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ha : a ≠ 0) :
    Function.Injective (fun n : ℕ => q ^ n * a) := by
  intro i j hij
  have hij' : q ^ i = q ^ j := mul_right_cancel₀ ha hij
  wlog hle : i ≤ j generalizing i j
  · exact (this hij.symm hij'.symm (by omega)).symm
  by_contra hne
  have hd : 0 < j - i := by omega
  apply hq (j - i) hd
  have he : q ^ i * q ^ (j - i) = q ^ i * 1 := by
    rw [← pow_add, Nat.add_sub_of_le hle, mul_one, hij']
  exact mul_left_cancel₀ (pow_ne_zero _ hq0) he

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {K T : Module.End R M} {q a : R} {m : M}

/-- Every iterate of a q-commuting map lies in the expected eigenspace, including
zero iterates. This induction is reconstructed here and does not require a field. -/
theorem apply_pow_eq_smul_of_q_commute (hcomm : K * T = q • (T * K))
    (hm : K m = a • m) (n : ℕ) :
    K ((T ^ n) m) = (q ^ n * a) • ((T ^ n) m) := by
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    have hc := congrArg (fun f : Module.End R M => f ((T ^ n) m)) hcomm
    simp only [Module.End.mul_apply, LinearMap.smul_apply, ih, map_smul] at hc
    simpa [pow_succ', Module.End.mul_apply, smul_smul, mul_assoc] using hc

/-- Eigenspace-membership form of `apply_pow_eq_smul_of_q_commute`. -/
theorem pow_mem_eigenspace_of_q_commute (hcomm : K * T = q • (T * K))
    (hm : m ∈ K.eigenspace a) (n : ℕ) :
    (T ^ n) m ∈ K.eigenspace (q ^ n * a) :=
  mem_eigenspace_iff.mpr
    (apply_pow_eq_smul_of_q_commute hcomm (mem_eigenspace_iff.mp hm) n)

end CommRing

section Field

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] {K T : Module.End k M} {q a : k} {m : M}

/-- In finite dimension, a q-commuting string with a nonzero initial eigenvalue
vanishes eventually if `q` has infinite multiplicative order. The proof by linear
independence of eigenvectors with distinct eigenvalues is reconstructed here. -/
theorem exists_pow_eq_zero_of_q_commute (hq0 : q ≠ 0)
    (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ha : a ≠ 0)
    (hcomm : K * T = q • (T * K)) (hm : K m = a • m) :
    ∃ n : ℕ, (T ^ n) m = 0 := by
  classical
  by_contra! h
  apply Module.Finite.not_linearIndependent_of_infinite (R := k) (fun n : ℕ => (T ^ n) m)
  exact K.eigenvectors_linearIndependent' _
    (pow_mul_injective_of_forall_pow_ne_one hq0 hq ha) _ fun n =>
      ⟨mem_eigenspace_iff.mpr (apply_pow_eq_smul_of_q_commute hcomm hm n), h n⟩

/-- A nonzero eigenvector of nonzero eigenvalue generates a finite q-commuting string:
all iterates through `n` are nonzero, the next is zero, and the last has eigenvalue
`q ^ n * a`. The least-vanishing-iterate argument is reconstructed here. -/
theorem exists_last_nonzero_pow_of_q_commute (hq0 : q ≠ 0)
    (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ha : a ≠ 0)
    (hcomm : K * T = q • (T * K)) (hm : K m = a • m) (hm0 : m ≠ 0) :
    ∃ n : ℕ, (∀ i ≤ n, (T ^ i) m ≠ 0) ∧ (T ^ (n + 1)) m = 0 ∧
      K ((T ^ n) m) = (q ^ n * a) • ((T ^ n) m) ∧ T ((T ^ n) m) = 0 := by
  classical
  have hex := exists_pow_eq_zero_of_q_commute hq0 hq ha hcomm hm
  let N := Nat.find hex
  have hN : (T ^ N) m = 0 := Nat.find_spec hex
  have hNpos : 0 < N := by
    by_contra! hn
    have : N = 0 := by omega
    simp [this, hm0] at hN
  have hsucc : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
  refine ⟨N - 1, ?_, ?_, apply_pow_eq_smul_of_q_commute hcomm hm _, ?_⟩
  · intro i hi
    exact Nat.find_min hex (show i < Nat.find hex by dsimp [N] at *; omega)
  · simpa only [hsucc] using hN
  · rw [← Module.End.mul_apply, ← pow_succ', hsucc]
    exact hN

/-- Over an algebraically closed field, an injective `K` q-commuting with `T`
has a nonzero eigenvector killed by `T`, provided `q` has infinite multiplicative
order. The elementary eigenvector proof is reconstructed here. -/
theorem exists_highestWeight_of_q_commute [IsAlgClosed k] [Nontrivial M]
    (K T : Module.End k M) (hK : Function.Injective K)
    (q : k) (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
    (hcomm : K * T = q • (T * K)) :
    ∃ (a₀ : k) (m : M), a₀ ≠ 0 ∧ m ≠ 0 ∧ K m = a₀ • m ∧ T m = 0 := by
  obtain ⟨a, ha⟩ := K.exists_eigenvalue
  obtain ⟨m, hm⟩ := ha.exists_hasEigenvector
  have ha0 : a ≠ 0 := by
    intro h
    apply hm.2
    apply hK
    simpa [h] using hm.apply_eq_smul
  obtain ⟨n, hn, _, heig, hlast⟩ :=
    exists_last_nonzero_pow_of_q_commute hq0 hq ha0 hcomm hm.apply_eq_smul hm.2
  exact ⟨q ^ n * a, (T ^ n) m, mul_ne_zero (pow_ne_zero _ hq0) ha0,
    hn n le_rfl, heig, hlast⟩

end Field

end Module.End
