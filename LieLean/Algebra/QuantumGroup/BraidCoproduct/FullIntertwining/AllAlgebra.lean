/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.FullIntertwining.NegativeAction

/-!
# All-algebra finite intertwining

Every quantum-group element intertwines eventually on every twisted Verma tensor.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994),
37.3.1–37.3.2 and the proof of 38.1.8 (printed pp. 293, 297–299).
The finite-cutoff argument uses the actual quantum group and original Verma modules.
No restricted braid isometry or PBW norm conclusion is asserted here.
-/

open LieLean TensorProduct
open scoped TensorProduct
noncomputable section
namespace FullIntertwining
open QuantumGroup FiniteIntertwining MixedIntertwining MixedNormalization
variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]
  (Λ₁ Λ₂ : Y →+ ℤ)

/-- All elements of the actual quantum quotient intertwine eventually on each original tensor
vector. Product induction takes its left-factor bound at the right-factor-transformed vector. -/
theorem lowestPair_intertwine_all (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i : I)
    (u : QuantumGroup R v)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      lowestPair R v Λ₁ Λ₂ (braidDelta R v hv i u)
        (lowestPair R v Λ₁ Λ₂ (partialSum R v i N) z) =
      lowestPair R v Λ₁ Λ₂ (partialSum R v i N)
        (lowestPair R v Λ₁ Λ₂ (comul R v u) z) := by
  induction u using QuantumGroup.induction_on generalizing z with
  | algebraMap c =>
    refine ⟨0, fun N _ ↦ ?_⟩
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      LinearMap.smul_apply, Module.End.one_apply]
  | E j => exact lowestPair_intertwine_E_any R v Λ₁ Λ₂ hv i j z
  | F j => exact lowestPair_intertwine_F_any R v Λ₁ Λ₂ hv i j z
  | K μ =>
    refine ⟨0, fun N _ ↦ ?_⟩
    have h := congrArg (fun a ↦ lowestPair R v Λ₁ Λ₂ a z) (intertwine_K R v hv i μ N)
    simpa only [map_mul, Module.End.mul_apply] using h
  | add a b ha hb =>
    obtain ⟨M, hM⟩ := ha z
    obtain ⟨L, hL⟩ := hb z
    refine ⟨max M L, fun N hN ↦ ?_⟩
    simp only [map_add, LinearMap.add_apply]
    rw [hM N (le_trans (le_max_left _ _) hN), hL N (le_trans (le_max_right _ _) hN)]
  | mul a b ha hb =>
    obtain ⟨M, hM⟩ := hb z
    obtain ⟨L, hL⟩ := ha (lowestPair R v Λ₁ Λ₂ (comul R v b) z)
    refine ⟨max M L, fun N hN ↦ ?_⟩
    simp only [map_mul, Module.End.mul_apply]
    rw [hM N (le_trans (le_max_left _ _) hN), hL N (le_trans (le_max_right _ _) hN)]

end FullIntertwining
