/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Sl2.SimpleModule
import LieLean.Algebra.QuantumGroup.Sl2.Classification.HighestVector

/-!
# Highest vectors and finite strings for quantum sl₂

This file develops the exhaustion direction of the finite-dimensional simple-module
classification, without assuming type-1 weights or a highest vector.

## Main results

* `QuantumGroup.Sl2.exists_highestVector`: every nonzero finite-dimensional representation
  over an algebraically closed field has a highest vector when the parameter has infinite order.
* `QuantumGroup.Sl2.E_apply_F_pow_succ`: the raising action on an arbitrary highest string.
* `QuantumGroup.Sl2.exists_highestString`: the highest eigenvalue is `σ v^n`, where `σ² = 1`,
  and the lowering string has length `n+1`.
* `QuantumGroup.Sl2.F_string_linearIndependent`: the nonzero string vectors are independent.

The irreducible highest-string basis and exhaustion equivalence are proved in
`Classification.StringBasis` and `Classification.Equivalence`, respectively.

## References

Jantzen, *Lectures on quantum groups*, Ch. 2. The arguments here are reconstructed;
precise theorem numbering has not been checked against the source.
-/

noncomputable section

namespace QuantumGroup.Sl2

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] {v : k}

/-- The action of `K₁` in any representation is injective, since `K₋₁` is its inverse. -/
theorem K_injective (ρ : Sl2 v →ₐ[k] Module.End k M) :
    Function.Injective (ρ (K sl2RootDatum v 1)) := by
  intro x y h
  have hleft : ρ (K sl2RootDatum v (-1)) * ρ (K sl2RootDatum v 1) = 1 := by
    rw [← map_mul, K_neg_mul_K, map_one]
  have hh := congrArg (ρ (K sl2RootDatum v (-1))) h
  simpa only [← Module.End.mul_apply, hleft, Module.End.one_apply] using hh

/-- The `K₁,E` relation after applying a representation. -/
theorem rep_K_mul_E (ρ : Sl2 v →ₐ[k] Module.End k M) :
    ρ (K sl2RootDatum v 1) * ρ (E sl2RootDatum v ()) =
      v ^ 2 • (ρ (E sl2RootDatum v ()) * ρ (K sl2RootDatum v 1)) := by
  simpa using congrArg ρ (K_mul_E sl2RootDatum v 1 ())

/-- The `K₁,F` relation after applying a representation. -/
theorem rep_K_mul_F (ρ : Sl2 v →ₐ[k] Module.End k M) :
    ρ (K sl2RootDatum v 1) * ρ (F sl2RootDatum v ()) =
      v⁻¹ ^ 2 • (ρ (F sl2RootDatum v ()) * ρ (K sl2RootDatum v 1)) := by
  simpa [zpow_neg, inv_pow] using congrArg ρ (K_mul_F sl2RootDatum v 1 ())

private theorem sq_pow_ne_one (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1)
    (r : ℕ) (hr : 0 < r) : (v ^ 2) ^ r ≠ 1 := by
  rw [← pow_mul]
  exact hv' _ (by omega)

private theorem inv_sq_pow_ne_one (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1)
    (r : ℕ) (hr : 0 < r) : (v⁻¹ ^ 2) ^ r ≠ 1 := by
  intro h
  apply sq_pow_ne_one hv' r hr
  simpa only [inv_pow, inv_inv, inv_one] using congrArg Inv.inv h

/-- Existence of a highest vector in every nonzero finite-dimensional representation.
No irreducibility or weight decomposition is assumed. The argument uses a `K₁` eigenvector
and termination of its `E` string; it is reconstructed from the standard Ch. 2 argument. -/
theorem exists_highestVector [FiniteDimensional k M] [Nontrivial M] [IsAlgClosed k]
    (hv : v ≠ 0) (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1)
    (ρ : Sl2 v →ₐ[k] Module.End k M) :
    ∃ (a : k) (m : M), a ≠ 0 ∧ m ≠ 0 ∧
      ρ (K sl2RootDatum v 1) m = a • m ∧ ρ (E sl2RootDatum v ()) m = 0 := by
  exact Module.End.exists_highestWeight_of_q_commute _ _ (K_injective ρ) (v ^ 2)
    (pow_ne_zero _ hv) (sq_pow_ne_one hv') (rep_K_mul_E ρ)

/-- Every `F` iterate of a `K₁` eigenvector has its expected eigenvalue. -/
theorem K_apply_F_pow (ρ : Sl2 v →ₐ[k] Module.End k M) {a : k} {m : M}
    (hm : ρ (K sl2RootDatum v 1) m = a • m) (r : ℕ) :
    ρ (K sl2RootDatum v 1) ((ρ (F sl2RootDatum v ()) ^ r) m) =
      ((v⁻¹ ^ 2) ^ r * a) • ((ρ (F sl2RootDatum v ()) ^ r) m) :=
  Module.End.apply_pow_eq_smul_of_q_commute (rep_K_mul_F ρ) hm r

/-- Every nonzero `K₁` eigenvector generates a finite nonzero `F` string. -/
theorem exists_last_nonzero_F_pow [FiniteDimensional k M]
    (hv : v ≠ 0) (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1)
    (ρ : Sl2 v →ₐ[k] Module.End k M) {a : k} {m : M}
    (ha : a ≠ 0) (hm0 : m ≠ 0) (hm : ρ (K sl2RootDatum v 1) m = a • m) :
    ∃ n : ℕ, (∀ i ≤ n, (ρ (F sl2RootDatum v ()) ^ i) m ≠ 0) ∧
      (ρ (F sl2RootDatum v ()) ^ (n + 1)) m = 0 := by
  obtain ⟨n, hn, hz, _, _⟩ := Module.End.exists_last_nonzero_pow_of_q_commute
    (pow_ne_zero 2 (inv_ne_zero hv)) (inv_sq_pow_ne_one hv') ha (rep_K_mul_F ρ) hm hm0
  exact ⟨n, hn, hz⟩

/-- `K₋₁` acts on a nonzero-eigenvalue `K₁` eigenvector by the inverse eigenvalue. -/
theorem K_neg_apply_of_K_apply (ρ : Sl2 v →ₐ[k] Module.End k M) {a : k} {m : M}
    (ha : a ≠ 0) (hm : ρ (K sl2RootDatum v 1) m = a • m) :
    ρ (K sl2RootDatum v (-1)) m = a⁻¹ • m := by
  have h := congrArg (ρ (K sl2RootDatum v (-1))) hm
  have hleft : ρ (K sl2RootDatum v (-1)) * ρ (K sl2RootDatum v 1) = 1 := by
    rw [← map_mul, K_neg_mul_K, map_one]
  simp only [← Module.End.mul_apply, hleft, Module.End.one_apply, map_smul] at h
  calc
    _ = a⁻¹ • (a • ρ (K sl2RootDatum v (-1)) m) := by
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    _ = a⁻¹ • m := by rw [← h]

/-- The raising operator on an arbitrary highest-vector string, without a type-1 hypothesis.
This is the representation form of `QuantumGroup.E_mul_F_pow_sub`. -/
theorem E_apply_F_pow_succ (hv : v ≠ 0) (ρ : Sl2 v →ₐ[k] Module.End k M)
    {a : k} {m : M} (ha : a ≠ 0) (hm : ρ (K sl2RootDatum v 1) m = a • m)
    (hE : ρ (E sl2RootDatum v ()) m = 0) (r : ℕ) :
    ρ (E sl2RootDatum v ()) ((ρ (F sl2RootDatum v ()) ^ (r + 1)) m) =
      (qInt v (r + 1) * (v - v⁻¹)⁻¹ * (v⁻¹ ^ r * a - v ^ r * a⁻¹)) •
        ((ρ (F sl2RootDatum v ()) ^ r) m) := by
  have h := congrArg (fun u : Sl2 v => ρ u m)
    (E_mul_F_pow_sub (R := sl2RootDatum) hv () r)
  simpa only [map_sub, map_mul, map_pow, map_smul, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, sl2Datum_d, pow_one,
    Kt, sl2RootDatum_ktilde, hm, K_neg_apply_of_K_apply ρ ha hm, hE, map_zero,
    sub_zero, map_sub, map_smul, smul_smul, smul_sub, sub_smul, mul_assoc,
    mul_sub] using h

/-- The terminal relation quantizes the highest eigenvalue: its square is `v^(2n)`.
This standard finite-string argument (Jantzen, Ch. 2) is reconstructed here. -/
theorem highest_eigenvalue_sq (hv : v ≠ 0)
    (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1) (ρ : Sl2 v →ₐ[k] Module.End k M)
    {a : k} {m : M} (ha : a ≠ 0) (hm : ρ (K sl2RootDatum v 1) m = a • m)
    (hE : ρ (E sl2RootDatum v ()) m = 0) {n : ℕ}
    (hn : (ρ (F sl2RootDatum v ()) ^ n) m ≠ 0)
    (hz : (ρ (F sl2RootDatum v ()) ^ (n + 1)) m = 0) :
    a ^ 2 = (v ^ n) ^ 2 := by
  have hden : v - v⁻¹ ≠ 0 := by
    intro h
    apply hv' 2 two_pos
    have h' := sub_eq_zero.mp h
    calc
      v ^ 2 = v * v := pow_two v
      _ = v * v⁻¹ := by rw [← h']
      _ = 1 := mul_inv_cancel₀ hv
  have hq : qInt v (n + 1) ≠ 0 := qInt_ne_zero hv (hv' _ (by omega))
  have h := E_apply_F_pow_succ hv ρ ha hm hE n
  rw [hz, map_zero] at h
  have hc := (smul_eq_zero.mp h.symm).resolve_right hn
  have heq : v⁻¹ ^ n * a = v ^ n * a⁻¹ := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left
      (mul_ne_zero hq (inv_ne_zero hden)))
  rw [inv_pow] at heq
  field_simp at heq
  exact heq

/-- A highest vector in a finite-dimensional representation has eigenvalue `σ v^n`
with `σ² = 1`, and its nonzero `F` string has length `n+1`. Both signs are retained;
no type-1 hypothesis is imposed. The finite-string proof is reconstructed from Ch. 2. -/
theorem exists_highestString [FiniteDimensional k M] [Nontrivial M] [IsAlgClosed k]
    (hv : v ≠ 0) (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1)
    (ρ : Sl2 v →ₐ[k] Module.End k M) :
    ∃ (n : ℕ) (σ : k) (m : M), σ ^ 2 = 1 ∧ m ≠ 0 ∧
      ρ (K sl2RootDatum v 1) m = (σ * v ^ n) • m ∧
      ρ (E sl2RootDatum v ()) m = 0 ∧
      (∀ i ≤ n, (ρ (F sl2RootDatum v ()) ^ i) m ≠ 0) ∧
      (ρ (F sl2RootDatum v ()) ^ (n + 1)) m = 0 := by
  obtain ⟨a, m, ha, hm0, hm, hE⟩ := exists_highestVector hv hv' ρ
  obtain ⟨n, hn, hz⟩ := exists_last_nonzero_F_pow hv hv' ρ ha hm0 hm
  have ha2 := highest_eigenvalue_sq hv hv' ρ ha hm hE (hn n le_rfl) hz
  refine ⟨n, a / v ^ n, m, ?_, hm0, ?_, hE, hn, hz⟩
  · rw [div_pow, ha2, div_self (pow_ne_zero _ (pow_ne_zero _ hv))]
  · simpa only [div_mul_cancel₀ a (pow_ne_zero _ hv)] using hm

/-- The nonzero part of a finite `F` string is linearly independent because all
its `K₁` eigenvalues are distinct. This elementary argument is reconstructed here. -/
theorem F_string_linearIndependent (hv : v ≠ 0)
    (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1) (ρ : Sl2 v →ₐ[k] Module.End k M)
    {a : k} {m : M} (ha : a ≠ 0) (hm : ρ (K sl2RootDatum v 1) m = a • m)
    {n : ℕ} (hn : ∀ i ≤ n, (ρ (F sl2RootDatum v ()) ^ i) m ≠ 0) :
    LinearIndependent k (fun i : Fin (n + 1) => (ρ (F sl2RootDatum v ()) ^ (i : ℕ)) m) := by
  apply (ρ (K sl2RootDatum v 1)).eigenvectors_linearIndependent'
    (fun i : Fin (n + 1) => (v⁻¹ ^ 2) ^ (i : ℕ) * a)
  · exact (Module.End.pow_mul_injective_of_forall_pow_ne_one
      (pow_ne_zero _ (inv_ne_zero hv)) (inv_sq_pow_ne_one hv') ha).comp Fin.val_injective
  · intro i
    exact ⟨Module.End.mem_eigenspace_iff.mpr (K_apply_F_pow ρ hm i), hn i (by omega)⟩

end QuantumGroup.Sl2
