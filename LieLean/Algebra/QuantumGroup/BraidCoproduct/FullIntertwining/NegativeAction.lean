/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.FullIntertwining.Negative

/-!
# Negative-generator intertwining on Verma tensors

Finite negative boundaries and their eventual vanishing on every tensor vector.

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

/-- Explicit negative overflow; the high first-leg power is on the right of a root prefix. -/
def overflowF (i j : I) (N : ℕ) : QuantumGroup R v ⊗[k] QuantumGroup R v :=
  ∑ a ∈ Finset.range (negA D i j + 1), ∑ n ∈ Finset.range (N + 1),
    if N < a + n then
      (coeff (v ^ D.d i) a * coeff (v ^ D.d i) n * (v ^ D.d i) ^ (negA D i j * n)) •
        ((chevalley R v (rankTwoXm R v i j a) * F R v i ^ n) ⊗ₜ[k]
          (E R v i ^ (a + n) * K R v (-ktilde R j))) else 0

omit [NeZero v] in
lemma flip_overflow (i j : I) (N : ℕ) :
    flipChevalley R v (overflow R v i j N) = overflowF R v i j N := by
  classical
  simp only [overflow, overflowF, map_sum, apply_ite, map_zero, mixedTerm,
    map_smul, flipChevalley_tmul, map_mul, map_pow, chevalley_E, chevalley_F, Kt,
    chevalley_K]

/-- Actual finite F intertwining, retaining every overflow index. -/
theorem finite_F_offdiag_boundary (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) (N : ℕ) :
    braidDelta R v hv i (F R v j) * partialSum R v i N -
      partialSum R v i N * comul R v (F R v j) = overflowF R v i j N := by
  have h := congrArg (flipChevalley R v) (finite_E_offdiag_boundary R v hv hij N)
  rw [map_sub, map_mul, map_mul, flipChevalley_partialSum,
    ← braidDelta_F_chevalley R v hv hij, ← comul_chevalley, chevalley_E,
    flip_overflow] at h
  exact h

variable (Λ₁ Λ₂ : Y →+ ℤ)

omit [NeZero v] in
lemma lowestPair_prefix_zero (i : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) (n : ℕ)
    (hcut : ∀ b : QuantumGroup R v, lowestPair R v Λ₁ Λ₂ ((F R v i ^ n) ⊗ₜ[k] b) z = 0)
    (a b : QuantumGroup R v) :
    lowestPair R v Λ₁ Λ₂ ((a * F R v i ^ n) ⊗ₜ[k] b) z = 0 := by
  have hf : (a * F R v i ^ n) ⊗ₜ[k] b =
      (a ⊗ₜ[k] (1 : QuantumGroup R v)) * ((F R v i ^ n) ⊗ₜ[k] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hf, map_mul, Module.End.mul_apply, hcut, map_zero]

/-- The finite negative root width shifts the genuine first-Verma cutoff by r. -/
theorem lowestPair_overflowF_eventually (i j : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → lowestPair R v Λ₁ Λ₂ (overflowF R v i j N) z = 0 := by
  obtain ⟨M, hM⟩ := lowestPair_uniform_second_cutoff R v Λ₁ Λ₂ i z
  refine ⟨M + negA D i j, fun N hN ↦ ?_⟩
  simp only [overflowF, map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro a ha
  have ha' := Finset.mem_range.mp ha
  apply Finset.sum_eq_zero
  intro n _
  by_cases h : N < a + n
  · simp only [h, ite_true, map_smul, LinearMap.smul_apply]
    rw [lowestPair_prefix_zero R v Λ₁ Λ₂ i z n (hM n (by omega)), smul_zero]
  · simp only [h, ite_false, map_zero, LinearMap.zero_apply]

/-- Off-diagonal F intertwining on the unchanged original Verma tensor action. -/
theorem lowestPair_intertwine_F_offdiag (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      lowestPair R v Λ₁ Λ₂ (braidDelta R v hv i (F R v j))
        (lowestPair R v Λ₁ Λ₂ (partialSum R v i N) z) =
      lowestPair R v Λ₁ Λ₂ (partialSum R v i N)
        (lowestPair R v Λ₁ Λ₂ (comul R v (F R v j)) z) := by
  obtain ⟨N₀, hN₀⟩ := lowestPair_overflowF_eventually R v Λ₁ Λ₂ i j z
  refine ⟨N₀, fun N hN ↦ ?_⟩
  have h := congrArg (fun a ↦ lowestPair R v Λ₁ Λ₂ a z)
    (finite_F_offdiag_boundary R v hv hij N)
  simpa only [map_sub, map_mul, LinearMap.sub_apply, Module.End.mul_apply,
    hN₀ N hN, sub_eq_zero] using h

/-- Both diagonal and off-diagonal negative generators. -/
theorem lowestPair_intertwine_F_any (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i j : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      lowestPair R v Λ₁ Λ₂ (braidDelta R v hv i (F R v j))
        (lowestPair R v Λ₁ Λ₂ (partialSum R v i N) z) =
      lowestPair R v Λ₁ Λ₂ (partialSum R v i N)
        (lowestPair R v Λ₁ Λ₂ (comul R v (F R v j)) z) := by
  by_cases hij : i = j
  · subst j
    exact lowestPair_intertwine_F R v Λ₁ Λ₂ hv i z
  · exact lowestPair_intertwine_F_offdiag R v Λ₁ Λ₂ hv hij z

end FullIntertwining
