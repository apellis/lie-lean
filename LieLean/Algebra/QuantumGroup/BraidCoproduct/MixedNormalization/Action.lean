/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.MixedNormalization.Boundary
import LieLean.Algebra.QuantumGroup.BraidCoproduct.MixedCoproduct

/-!
# Positive-generator intertwining on Verma tensors

Uniform cutoffs eliminate the finite overflow on every original Verma tensor.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994),
37.3.1–37.3.2 and the proof of 38.1.8 (printed pp. 293, 297–299).
The finite-cutoff argument uses the actual quantum group and original Verma modules.
No restricted braid isometry or PBW norm conclusion is asserted here.
-/

open LieLean TensorProduct
open scoped TensorProduct
noncomputable section
namespace MixedNormalization
open QuantumGroup FiniteIntertwining MixedIntertwining
variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]
  (Λ₁ Λ₂ : Y →+ ℤ)

omit [NeZero v] in
/-- Any genuine uniform translated cutoff kills the explicit finite overflow. -/
theorem lowestPair_overflow_of_cutoff (i j : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) (N₀ N : ℕ) (hN : N₀ ≤ N)
    (hcut : ∀ m, N₀ ≤ m → ∀ b : QuantumGroup R v,
      lowestPair R v Λ₁ Λ₂ ((F R v i ^ m * Kt R v j) ⊗ₜ[k] b) z = 0) :
    lowestPair R v Λ₁ Λ₂ (overflow R v i j N) z = 0 := by
  simp only [overflow, map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro n _
  by_cases h : N < a + n
  · simp only [h, ite_true]
    simp only [mixedTerm, map_smul, LinearMap.smul_apply,
      hcut (a + n) (by omega) _, smul_zero]
  · simp only [h, ite_false, map_zero, LinearMap.zero_apply]

/-- The cutoff exists for each original Verma tensor vector, without assumed nilpotence. -/
theorem lowestPair_overflow_eventually (i j : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → lowestPair R v Λ₁ Λ₂ (overflow R v i j N) z = 0 := by
  obtain ⟨N₀, hcut⟩ := lowestPair_translated_uniform_cutoff R v Λ₁ Λ₂ i z (Kt R v j)
  exact ⟨N₀, fun N hN ↦ lowestPair_overflow_of_cutoff R v Λ₁ Λ₂ i j z N₀ N hN hcut⟩

/-- Off-diagonal E intertwining on every vector of the original Verma tensor action. -/
theorem lowestPair_intertwine_E_offdiag (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      lowestPair R v Λ₁ Λ₂ (braidDelta R v hv i (E R v j))
        (lowestPair R v Λ₁ Λ₂ (partialSum R v i N) z) =
      lowestPair R v Λ₁ Λ₂ (partialSum R v i N)
        (lowestPair R v Λ₁ Λ₂ (comul R v (E R v j)) z) := by
  obtain ⟨N₀, hN₀⟩ := lowestPair_overflow_eventually R v Λ₁ Λ₂ i j z
  refine ⟨N₀, fun N hN ↦ ?_⟩
  have h := congrArg (fun a ↦ lowestPair R v Λ₁ Λ₂ a z)
    (finite_E_offdiag_boundary R v hv hij N)
  simpa only [map_sub, map_mul, LinearMap.sub_apply, Module.End.mul_apply,
    hN₀ N hN, sub_eq_zero] using h

/-- All E generators, combining the diagonal and off-diagonal intertwining identities. -/
theorem lowestPair_intertwine_E_any (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i j : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      lowestPair R v Λ₁ Λ₂ (braidDelta R v hv i (E R v j))
        (lowestPair R v Λ₁ Λ₂ (partialSum R v i N) z) =
      lowestPair R v Λ₁ Λ₂ (partialSum R v i N)
        (lowestPair R v Λ₁ Λ₂ (comul R v (E R v j)) z) := by
  by_cases hij : i = j
  · subst j
    exact lowestPair_intertwine_E R v Λ₁ Λ₂ hv i z
  · exact lowestPair_intertwine_E_offdiag R v Λ₁ Λ₂ hv hij z

end MixedNormalization
