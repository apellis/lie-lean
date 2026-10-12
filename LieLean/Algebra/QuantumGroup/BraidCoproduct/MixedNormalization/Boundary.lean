/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.MixedNormalization.OffDiagonal

/-!
# Finite off-diagonal boundaries

All overflow terms of the finite positive-generator intertwining identity.

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

lemma sum_triangle {B : Type*} [AddCommMonoid B] (f : ℕ → ℕ → B) (r N : ℕ) :
    (∑ a ∈ Finset.range (r + 1), ∑ n ∈ Finset.range (N + 1),
      if a + n ≤ N then f a n else 0) =
    ∑ m ∈ Finset.range (N + 1), ∑ a ∈ Finset.range (min r m + 1), f a (m - a) := by
  classical
  rw [← Finset.sum_product', ← Finset.sum_filter, Finset.sum_sigma']
  apply Finset.sum_bij (fun p _ ↦ (⟨p.1 + p.2, p.1⟩ : Σ _ : ℕ, ℕ))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · intro p hp p' hp' heq
    have h1 := congrArg Sigma.fst heq
    have h2 := congrArg Sigma.snd heq
    apply Prod.ext <;> dsimp at * <;> omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    refine ⟨(p.2, p.1 - p.2), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · have h : p.2 + (p.1 - p.2) = p.1 := by omega
      simp only [h]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]

def mixedTerm (i j : I) (a n : ℕ) : QuantumGroup R v ⊗[k] QuantumGroup R v :=
  (coeff (v ^ D.d i) a * coeff (v ^ D.d i) n * (v ^ D.d i) ^ (negA D i j * n)) •
    ((F R v i ^ (a + n) * Kt R v j) ⊗ₜ[k] (rankTwoXm R v i j a * E R v i ^ n))

def overflow (i j : I) (N : ℕ) : QuantumGroup R v ⊗[k] QuantumGroup R v :=
  ∑ a ∈ Finset.range (negA D i j + 1), ∑ n ∈ Finset.range (N + 1),
    if N < a + n then mixedTerm R v i j a n else 0

omit [NeZero v] in
lemma Kj_mul_Fi_pow {i j : I} (hij : i ≠ j) (n : ℕ) :
    Kt R v j * F R v i ^ n = (v ^ D.d i) ^ (negA D i j * n) •
      (F R v i ^ n * Kt R v j) := by
  have h : Kt R v j * F R v i = (v ^ D.d i) ^ negA D i j •
      (F R v i * Kt R v j) := by
    rw [Kt, K_mul_F, root_ktilde_comm, zpow_neg, zpow_root_ktilde_of_ne hij, inv_inv]
  simpa only [pow_mul] using mul_pow_of_mul_eq_smul h n

lemma left_product (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) (N : ℕ) :
    braidDelta R v hv i (E R v j) * partialSum R v i N =
      (E R v j ⊗ₜ[k] (1 : QuantumGroup R v)) * partialSum R v i N +
        ∑ a ∈ Finset.range (negA D i j + 1), ∑ n ∈ Finset.range (N + 1),
          mixedTerm R v i j a n := by
  rw [braidDelta_E_offdiag R v hv hij, add_mul]
  congr 1
  simp only [partialSum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro n _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_assoc, Kj_mul_Fi_pow R v hij n,
    mul_smul_comm, ← mul_assoc, ← pow_add, ← smul_tmul', smul_smul, smul_smul]
  simp [mixedTerm, mul_assoc, mul_left_comm]

lemma right_product (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) (N : ℕ) :
    partialSum R v i N * comul R v (E R v j) =
      (E R v j ⊗ₜ[k] (1 : QuantumGroup R v)) * partialSum R v i N +
        ∑ m ∈ Finset.range (N + 1), ∑ a ∈ Finset.range (min (negA D i j) m + 1),
          mixedTerm R v i j a (m - a) := by
  rw [comul_E, mul_add]
  congr 1
  · simp only [partialSum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [(Commute.pow_right (E_mul_F_of_ne (R := R) (v := v) hij.symm) n).eq]
  · simp only [partialSum, Finset.sum_mul, smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul]
    apply Finset.sum_congr rfl
    intro m _
    rw [← tmul_smul, rankTwoXm_convolution_truncated R v hv hij m, tmul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' := Finset.mem_range.mp ha
    simp only [mixedTerm, tmul_smul, show a + (m - a) = m by omega]

/-- Exact finite overflow; no module cutoff or intertwining hypothesis is used. -/
theorem finite_E_offdiag_boundary (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) (N : ℕ) :
    braidDelta R v hv i (E R v j) * partialSum R v i N -
      partialSum R v i N * comul R v (E R v j) = overflow R v i j N := by
  rw [left_product R v hv hij, right_product R v hv hij, ← sum_triangle]
  simp only [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, overflow]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : a + n ≤ N
  · simp [h, show ¬N < a + n by omega]
  · simp [h, show N < a + n by omega]

end MixedNormalization
