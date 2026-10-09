/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorModuleCrystal

/-!
# Pure tensors of basis classes

Let `A ⊆ k` with `k = A[ϖ⁻¹]`, `ϖ` not a unit, and let `L₁ ⊆ M₁`, `L₂ ⊆ M₂` be free `A`-lattices
spanning the `k`-vector spaces `M₁`, `M₂`, with `A/ϖA`-bases `B₁ ⊆ L₁/ϖL₁`, `B₂ ⊆ L₂/ϖL₂`. Then the
classes of the pure tensors `x ⊗ y` (`[x] ∈ B₁`, `[y] ∈ B₂`) in `(L₁ ⊗ L₂)/ϖ(L₁ ⊗ L₂)` are nonzero
and pairwise distinct (`TensorModule.mk_tmul_sub_mem_iff`, `TensorModule.mk_tmul_notMem`). No
finite-dimensionality is needed (compare `IntegrableSl2.IsCrystalBase.tmulQ_injective`).

## Proof

For `[x₀] ∈ B₁` the coordinate functional of `[x₀]` lifts (by projectivity of the free module
`L₁`) to `f : L₁ → A`, which extends `k`-linearly to `M₁` (an `A`-basis of `L₁` is a `k`-basis of
`M₁`). For a second such `g` on `M₂`, `F = f ⊗ g : M₁ ⊗ M₂ → k` maps `L₁ ⊗ L₂` into `A` and
`ϖ(L₁ ⊗ L₂)` into `ϖA`, and `F(x ⊗ y) ≡ δ_{[x],[x₀]} δ_{[y],[y₀]}` modulo `ϖ` (our argument).
-/

open TensorProduct Pointwise

noncomputable section

namespace LieLean.QuantumGroup

namespace TensorModule

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra A k]
  {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower A k M]
  {ϖ : A}

/-- An `A`-basis of a lattice `L ⊆ M` spanning `M` over `k = A[ϖ⁻¹]` is a `k`-basis of `M`. -/
lemma linearIndependent_coe_of_basis
    (hϖ0 : algebraMap A k ϖ ≠ 0)
    (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
    {L : Submodule A M} {κ : Type*} (e : Module.Basis κ A L) :
    LinearIndependent k (fun a ↦ (e a : M)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  choose m a ha using hk
  set N := s.sup fun j ↦ m (g j)
  have hN : ∀ j ∈ s, ∃ c : A, algebraMap A k (ϖ ^ N) * g j = algebraMap A k c := fun j hj ↦ by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := fun j ↦ m (g j)) hj)
    refine ⟨ϖ ^ d * a (g j), ?_⟩
    have hd' : N = m (g j) + d := hd
    rw [hd', pow_add, map_mul, map_mul, ← ha]
    ring
  choose c hc using hN
  let c' : κ → A := fun j ↦ if h : j ∈ s then c j h else 0
  have hc' : ∀ j ∈ s, algebraMap A k (c' j) = algebraMap A k (ϖ ^ N) * g j := fun j hj ↦ by
    simp only [c', hj, ↓reduceDIte, hc]
  have hsum : ∑ j ∈ s, c' j • e j = 0 := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_zero]
    have : ∑ j ∈ s, (c' j • e j : L).1 = algebraMap A k (ϖ ^ N) • ∑ j ∈ s, g j • (e j : M) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [Submodule.coe_smul, ← algebraMap_smul k (c' j), hc' j hj, mul_smul]
    rw [this, hg, smul_zero]
  have h0 := (linearIndependent_iff'.1 e.linearIndependent) s c' hsum i hi
  have h1 := hc' i hi
  rw [h0, map_zero, eq_comm, mul_eq_zero] at h1
  exact h1.resolve_left (by rw [map_pow]; exact pow_ne_zero _ hϖ0)

end TensorModule

end LieLean.QuantumGroup
