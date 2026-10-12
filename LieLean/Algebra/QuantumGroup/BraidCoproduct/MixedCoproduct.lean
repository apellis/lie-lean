/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.FiniteIntertwining
import LieLean.Algebra.QuantumGroup.BraidCoproduct.MixedIntertwining

/-!
# Negative coproducts and uniform Verma cutoffs

Chevalley transport of mixed coproducts and first-leg cutoffs uniform in the second algebra.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994),
37.3.1–37.3.2 and the proof of 38.1.8 (printed pp. 293, 297–299).
The finite-cutoff argument uses the actual quantum group and original Verma modules.
No restricted braid isometry or PBW norm conclusion is asserted here.
-/

open LieLean TensorProduct
open scoped TensorProduct
noncomputable section
namespace MixedIntertwining
open QuantumGroup FiniteIntertwining LusztigF
variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]

/-- The actual Chevalley homomorphism reverses the actual coproduct legs. -/
lemma comul_chevalley (x : QuantumGroup R v) :
    comul R v (chevalley R v x) = flipChevalley R v (comul R v x) := by
  have h : (comul R v).comp (chevalley R v) =
      (flipChevalley R v).comp (comul R v) := by
    apply hom_ext
    · intro j
      simp [flipChevalley_tmul, Kt, add_comm]
    · intro j
      simp [flipChevalley_tmul, Kt, add_comm]
    · intro μ
      simp [flipChevalley_tmul]
  exact DFunLike.congr_fun h x

/-- Negative-string coproduct, obtained without a new compatibility assumption. -/
theorem comul_negativeRootString {i j : I} (hij : i ≠ j) (m : ℕ) :
    comul R v (chevalley R v (rankTwoXp R v i j m)) =
      (1 : QuantumGroup R v) ⊗ₜ[k] chevalley R v (rankTwoXp R v i j m) +
        ∑ t ∈ Finset.range (m + 1),
          coproductCoeff (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) m t •
            (chevalley R v (rankTwoXp R v i j t) ⊗ₜ[k]
              (F R v i ^ (m - t) * (K R v (-ktilde R i) ^ t * K R v (-ktilde R j)))) := by
  rw [comul_chevalley, comul_rootString R v hij]
  simp [rootTerm, flipChevalley_tmul, Kt]

omit [NeZero v] in
lemma chevalley_rootString (i j : I) (m : ℕ) :
    chevalley R v (rankTwoXp R v i j m) =
      BraidDiagonal.X (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (F R v i) (F R v j) m := by
  induction m with
  | zero => simp [rankTwoXp_zero, BraidDiagonal.X]
  | succ m ih =>
    simp only [rankTwoXp_succ, map_sub, map_smul, map_mul, chevalley_E, ih,
      BraidDiagonal.X_succ]

/-- The F-braid generator uses the same complete coefficient row with Chevalley-swapped legs. -/
theorem comul_braid_F (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) :
    comul R v (braidEquivOfNotRoot R hv i (F R v j)) =
      ((qFactorial (v ^ D.d i) (negA D i j))⁻¹ * (-1) ^ negA D i j *
        (v ^ D.d i) ^ negA D i j) •
        ((1 : QuantumGroup R v) ⊗ₜ[k] chevalley R v (rankTwoXp R v i j (negA D i j)) +
          ∑ t ∈ Finset.range (negA D i j + 1),
            coproductCoeff (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (negA D i j) t •
              (chevalley R v (rankTwoXp R v i j t) ⊗ₜ[k]
                (F R v i ^ (negA D i j - t) *
                  (K R v (-ktilde R i) ^ t * K R v (-ktilde R j))))) := by
  have hq : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hc : (v ^ D.d i) ^ negA D i j *
      ((v ^ D.d i) * (v ^ D.d i) ^ negA D i j)⁻¹ = (v ^ D.d i)⁻¹ := by
    field_simp
  have hf : braidEquivOfNotRoot R hv i (F R v j) =
      ((qFactorial (v ^ D.d i) (negA D i j))⁻¹ * (-1) ^ negA D i j *
        (v ^ D.d i) ^ negA D i j) • chevalley R v (rankTwoXp R v i j (negA D i j)) := by
    have h := (braidEquivOfNotRoot_hasImages hv R i).map_F j
    change braidEquivOfNotRoot R hv i (F R v j) = _ at h
    rw [h, ite_eq_right hij.symm, chevalley_rootString,
      BraidDiagonal.X_eq_serreAux hq (pow_ne_zero _ hq), hc]
    rfl
  rw [hf, map_smul, comul_negativeRootString R v hij]

/-- The actual braid-conjugated coproduct has its complete off-diagonal expansion.
The inverse-braid root coefficients are intentionally retained, not presumed normalized. -/
theorem braidDelta_E_offdiag_expansion (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) :
    braidDelta R v hv i (E R v j) =
      (qFactorial (v ^ D.d i) (negA D i j))⁻¹ •
        (Algebra.TensorProduct.congr (braidEquivOfNotRoot R hv i)
          (braidEquivOfNotRoot R hv i)).symm
          (rankTwoXp R v i j (negA D i j) ⊗ₜ[k] (1 : QuantumGroup R v) +
            ∑ t ∈ Finset.range (negA D i j + 1),
              coproductCoeff (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (negA D i j) t •
                rootTerm R v i j (negA D i j) t) := by
  change (Algebra.TensorProduct.congr (braidEquivOfNotRoot R hv i)
    (braidEquivOfNotRoot R hv i)).symm
      (comul R v (braidEquivOfNotRoot R hv i (E R v j))) = _
  rw [comul_braid_E R v hv hij, map_smul]

/-- A first-leg cutoff works uniformly for *every* second-leg algebra element.
This stronger uniformity is needed for mixed-root boundary terms. -/
theorem lowestPair_uniform_second_cutoff (Λ₁ Λ₂ : Y →+ ℤ) (i : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ b : QuantumGroup R v,
      lowestPair R v Λ₁ Λ₂ ((F R v i ^ n) ⊗ₜ[k] b) z = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨N, hN⟩ := VermaModule.exists_E_pow_smul_eq_zero (R := R) (v := v) i x
    refine ⟨N, fun n hn b ↦ ?_⟩
    rw [lowestPair_tmul]
    simp only [map_pow, chevalley_F]
    have he : E R v i ^ n • x = 0 := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [add_comm N r, pow_add, mul_smul, hN, smul_zero]
    rw [he, zero_tmul]
  | add z w hz hw =>
    obtain ⟨N, hN⟩ := hz
    obtain ⟨M, hM⟩ := hw
    exact ⟨max N M, fun n hn b ↦ by
      rw [map_add, hN n (le_trans (le_max_left N M) hn) b,
        hM n (le_trans (le_max_right N M) hn) b, add_zero]⟩

/-- Arbitrary fixed first-leg translates keep a genuine uniform high-F cutoff. -/
theorem lowestPair_translated_uniform_cutoff (Λ₁ Λ₂ : Y →+ ℤ) (i : I)
    (z : VermaModule R v Λ₁ ⊗[k] VermaModule R v Λ₂) (a : QuantumGroup R v) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ b : QuantumGroup R v,
      lowestPair R v Λ₁ Λ₂ ((F R v i ^ n * a) ⊗ₜ[k] b) z = 0 := by
  obtain ⟨N, hN⟩ := lowestPair_uniform_second_cutoff R v Λ₁ Λ₂ i
    (lowestPair R v Λ₁ Λ₂ (a ⊗ₜ[k] (1 : QuantumGroup R v)) z)
  refine ⟨N, fun n hn b ↦ ?_⟩
  have h := hN n hn b
  simpa only [← Module.End.mul_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one] using h

end MixedIntertwining
