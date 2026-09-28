/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Sl2.Classification

/-!
# Highest-string bases for irreducible quantum sl₂ representations

## Main results

* `QuantumGroup.Sl2.exists_highestString_basis`: an irreducible finite-dimensional
  representation has a highest-string basis, without assuming type-1 weights.

## References

Jantzen, *Lectures on quantum groups*, Ch. 2. The arguments are reconstructed;
precise theorem numbering has not been checked against the source.
-/

noncomputable section

namespace QuantumGroup.Sl2

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] {v : k}

/-- All toral generators act on a `K₁` eigenvector by integral powers of its eigenvalue.
This elementary step in the Ch. 2 highest-string argument is reconstructed here. -/
theorem K_apply_of_K_apply (ρ : Sl2 v →ₐ[k] Module.End k M) {a : k} {m : M}
    (ha : a ≠ 0) (hm : ρ (K sl2RootDatum v 1) m = a • m) (μ : ℤ) :
    ρ (K sl2RootDatum v μ) m = a ^ μ • m := by
  induction μ using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [← K_add, map_mul, Module.End.mul_apply, hm, map_smul, ih,
      smul_smul, zpow_add₀ ha, zpow_one, mul_comm a]
  | pred i ih =>
    rw [sub_eq_add_neg, ← K_add, map_mul, Module.End.mul_apply,
      K_neg_apply_of_K_apply ρ ha hm, map_smul, ih, smul_smul,
      zpow_add₀ ha, zpow_neg_one, mul_comm a⁻¹]

/-- A terminated highest-vector string spans a subspace stable under the entire quantum group.
The proof by the generators is reconstructed from Jantzen, Ch. 2. -/
theorem F_string_span_stable (hv : v ≠ 0) (ρ : Sl2 v →ₐ[k] Module.End k M)
    {a : k} {m : M} (ha : a ≠ 0) (hm : ρ (K sl2RootDatum v 1) m = a • m)
    (hE : ρ (E sl2RootDatum v ()) m = 0) {n : ℕ}
    (hz : (ρ (F sl2RootDatum v ()) ^ (n + 1)) m = 0) :
    ∀ (u : Sl2 v) x,
      x ∈ Submodule.span k (Set.range
        (fun i : Fin (n + 1) => (ρ (F sl2RootDatum v ()) ^ (i : ℕ)) m)) →
      ρ u x ∈ Submodule.span k (Set.range
        (fun i : Fin (n + 1) => (ρ (F sl2RootDatum v ()) ^ (i : ℕ)) m)) := by
  let W := Submodule.span k (Set.range
    (fun i : Fin (n + 1) => (ρ (F sl2RootDatum v ()) ^ (i : ℕ)) m))
  have hmem (i : ℕ) (hi : i ≤ n) : (ρ (F sl2RootDatum v ()) ^ i) m ∈ W :=
    Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩
  have hstable (T : Module.End k M)
      (hT : ∀ i : Fin (n + 1), T ((ρ (F sl2RootDatum v ()) ^ (i : ℕ)) m) ∈ W) :
      ∀ x, x ∈ W → T x ∈ W := by
    intro x hx
    exact (Submodule.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      exact hT i) : W ≤ W.comap T) hx
  intro u
  induction u using QuantumGroup.induction_on with
  | algebraMap c =>
    intro x hx
    simpa using W.smul_mem c hx
  | E i =>
    obtain rfl := Subsingleton.elim i ()
    apply hstable
    intro i
    rcases Nat.eq_zero_or_pos i.val with hi | hi
    · simp [hi, hE, W]
    · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
      rw [hr, E_apply_F_pow_succ hv ρ ha hm hE]
      exact W.smul_mem _ (hmem r (by omega))
  | F i =>
    obtain rfl := Subsingleton.elim i ()
    apply hstable
    intro i
    rw [← Module.End.mul_apply, ← pow_succ']
    by_cases hi : i.val < n
    · exact hmem _ (by omega)
    · have heq : i.val = n := by omega
      rw [heq, hz]
      exact W.zero_mem
  | K μ =>
    apply hstable
    intro i
    rw [K_apply_of_K_apply ρ
      (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero hv))) ha)
      (K_apply_F_pow ρ hm i) μ]
    exact W.smul_mem _ (hmem i (by omega))
  | add u u' hu hu' =>
    intro x hx
    simpa using W.add_mem (hu x hx) (hu' x hx)
  | mul u u' hu hu' =>
    intro x hx
    simpa only [map_mul, Module.End.mul_apply] using hu _ (hu' x hx)

/-- In an irreducible representation, a nonzero terminated highest string spans the module.
The stable-subspace predicate is exactly that used by `simpleRep_irreducible`.
The argument is reconstructed from Jantzen, Ch. 2. -/
theorem F_string_span_eq_top (hv : v ≠ 0) (ρ : Sl2 v →ₐ[k] Module.End k M)
    (hρ : ∀ W : Submodule k M, (∀ (u : Sl2 v) x, x ∈ W → ρ u x ∈ W) →
      W = ⊥ ∨ W = ⊤)
    {a : k} {m : M} (ha : a ≠ 0) (hm0 : m ≠ 0)
    (hm : ρ (K sl2RootDatum v 1) m = a • m)
    (hE : ρ (E sl2RootDatum v ()) m = 0) {n : ℕ}
    (hz : (ρ (F sl2RootDatum v ()) ^ (n + 1)) m = 0) :
    Submodule.span k (Set.range
      (fun i : Fin (n + 1) => (ρ (F sl2RootDatum v ()) ^ (i : ℕ)) m)) = ⊤ := by
  rcases hρ _ (F_string_span_stable hv ρ ha hm hE hz) with hbot | htop
  · exfalso
    apply hm0
    have hmem : m ∈ Submodule.span k (Set.range
        (fun i : Fin (n + 1) => (ρ (F sl2RootDatum v ()) ^ (i : ℕ)) m)) := by
      exact Submodule.subset_span ⟨⟨0, by omega⟩, by simp⟩
    simpa [hbot] using hmem
  · exact htop

/-- Every nonzero finite-dimensional irreducible representation over an algebraically closed
field has a highest-string basis. Both signs `σ² = 1` are retained, and no highest vector or
weight/type-1 assumption is imposed. The proof is reconstructed from Jantzen, Ch. 2. -/
theorem exists_highestString_basis [FiniteDimensional k M] [Nontrivial M] [IsAlgClosed k]
    (hv : v ≠ 0) (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1)
    (ρ : Sl2 v →ₐ[k] Module.End k M)
    (hρ : ∀ W : Submodule k M, (∀ (u : Sl2 v) x, x ∈ W → ρ u x ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    ∃ (n : ℕ) (σ : k) (m : M), σ ^ 2 = 1 ∧ m ≠ 0 ∧
      ρ (K sl2RootDatum v 1) m = (σ * v ^ n) • m ∧
      ρ (E sl2RootDatum v ()) m = 0 ∧
      (∀ i ≤ n, (ρ (F sl2RootDatum v ()) ^ i) m ≠ 0) ∧
      (ρ (F sl2RootDatum v ()) ^ (n + 1)) m = 0 ∧
      ∃ b : Module.Basis (Fin (n + 1)) k M,
        ∀ i, b i = (ρ (F sl2RootDatum v ()) ^ (i : ℕ)) m := by
  obtain ⟨n, σ, m, hσ, hm0, hm, hE, hn, hz⟩ := exists_highestString hv hv' ρ
  have hσ0 : σ ≠ 0 := by
    intro h
    simp [h] at hσ
  have ha := mul_ne_zero hσ0 (pow_ne_zero n hv)
  have hli := F_string_linearIndependent hv hv' ρ ha hm hn
  have hsp := F_string_span_eq_top hv ρ hρ ha hm0 hm hE hz
  exact ⟨n, σ, m, hσ, hm0, hm, hE, hn, hz,
    Module.Basis.mk hli hsp.ge, Module.Basis.mk_apply hli hsp.ge⟩

end QuantumGroup.Sl2
