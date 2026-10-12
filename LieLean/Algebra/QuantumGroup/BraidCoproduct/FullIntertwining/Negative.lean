/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.MixedNormalization.Action

/-!
# Negative-generator braid coproduct

Chevalley transport with the noncommuting toral factors kept in order.

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

lemma braid_F_chevalley (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) :
    braidEquivOfNotRoot R hv i (F R v j) =
      ((-1) ^ negA D i j * (v ^ D.d i) ^ negA D i j) •
        chevalley R v (braidEquivOfNotRoot R hv i (E R v j)) := by
  have HT := braidEquivOfNotRoot_hasImages hv R i
  have he := HT.map_E j
  have hf := HT.map_F j
  change braidEquivOfNotRoot R hv i (E R v j) = _ at he
  change braidEquivOfNotRoot R hv i (F R v j) = _ at hf
  rw [he, hf, ite_eq_right hij.symm, ite_eq_right hij.symm,
    twoNode_chevalley_braidEj (NeZero.ne v), smul_smul]
  have hq : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hs : ((-1 : k) ^ negA D i j * (v ^ D.d i) ^ negA D i j) *
      ((-1) ^ negA D i j * (v ^ D.d i)⁻¹ ^ negA D i j) = 1 := by
    rw [← mul_pow, ← mul_pow]
    have h : (-1 : k) * v ^ D.d i * (-1 * (v ^ D.d i)⁻¹) = 1 := by
      field_simp
    rw [← mul_pow, h, one_pow]
  rw [hs, one_smul]

lemma braid_F_self_chevalley (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i : I) :
    braidEquivOfNotRoot R hv i (F R v i) = (v ^ D.d i)⁻¹ ^ 2 •
      chevalley R v (braidEquivOfNotRoot R hv i (E R v i)) := by
  have HT := braidEquivOfNotRoot_hasImages hv R i
  have he := HT.map_E i
  have hf := HT.map_F i
  change braidEquivOfNotRoot R hv i (E R v i) = _ at he
  change braidEquivOfNotRoot R hv i (F R v i) = _ at hf
  rw [he, hf, ite_eq_left rfl, ite_eq_left rfl, chevalley_braidEi (NeZero.ne v), smul_smul]
  rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ (NeZero.ne v))), one_smul]

lemma braid_E_self_chevalley (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i : I) :
    braidEquivOfNotRoot R hv i (E R v i) = (v ^ D.d i) ^ 2 •
      chevalley R v (braidEquivOfNotRoot R hv i (F R v i)) := by
  have h := congrArg (chevalley R v) (braid_F_self_chevalley R v hv i)
  have hi (x : QuantumGroup R v) : chevalley R v (chevalley R v x) = x :=
    DFunLike.congr_fun (chevalley_comp_chevalley R v) x
  simp only [map_smul, hi] at h
  rw [h, smul_smul]
  rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ (NeZero.ne v))), one_smul]

/-- Compatibility on the actual root string; no commuting-braid assumption. -/
lemma braid_negative_root (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) (a : ℕ) :
    braidEquivOfNotRoot R hv i (chevalley R v (rankTwoXm R v i j a)) =
      (((-1) ^ negA D i j * (v ^ D.d i) ^ negA D i j) *
        ((v ^ D.d i)⁻¹ ^ 2) ^ a) •
        chevalley R v (braidEquivOfNotRoot R hv i (rankTwoXm R v i j a)) := by
  induction a with
  | zero => simpa [rankTwoXm_zero] using braid_F_chevalley R v hv hij
  | succ a ih =>
    simp only [rankTwoXm_succ, map_sub, map_mul, map_smul, chevalley_E,
      braid_F_self_chevalley R v hv i, ih, smul_mul_assoc, mul_smul_comm,
      smul_smul, smul_sub, pow_succ]
    congr 1 <;> congr 1 <;> ring

lemma braid_positive_toral_leg (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    (i j : I) (a : ℕ) :
    braidEquivOfNotRoot R hv i (E R v i ^ a * K R v (-ktilde R j)) =
      ((v ^ D.d i) ^ 2) ^ a • chevalley R v
        (braidEquivOfNotRoot R hv i (F R v i ^ a * Kt R v j)) := by
  have hK : ∀ μ, braidEquivOfNotRoot R hv i (K R v μ) = K R v (reflY R i μ) :=
    (braidEquivOfNotRoot_hasImages hv R i).map_K
  simp only [map_mul, map_pow, braid_E_self_chevalley R v hv i, smul_pow,
    smul_mul_assoc, Kt, hK, chevalley_K, map_neg]

/-- The opposite root/torus factors have exactly cancelling braid-Chevalley weights. -/
lemma braid_flip_root_term (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) (a : ℕ) :
    (Algebra.TensorProduct.congr (braidEquivOfNotRoot R hv i)
      (braidEquivOfNotRoot R hv i))
      (flipChevalley R v ((F R v i ^ a * Kt R v j) ⊗ₜ[k] rankTwoXm R v i j a)) =
    ((-1) ^ negA D i j * (v ^ D.d i) ^ negA D i j) • flipChevalley R v
      ((Algebra.TensorProduct.congr (braidEquivOfNotRoot R hv i)
        (braidEquivOfNotRoot R hv i))
        ((F R v i ^ a * Kt R v j) ⊗ₜ[k] rankTwoXm R v i j a)) := by
  simp only [flipChevalley_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom]
  rw [show chevalley R v (F R v i ^ a * Kt R v j) =
      E R v i ^ a * K R v (-ktilde R j) by simp [Kt],
    braid_negative_root R v hv hij a, braid_positive_toral_leg R v hv i j a]
  simp only [← smul_tmul', tmul_smul, smul_smul]
  congr 1
  have hq : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hp : ((v ^ D.d i)⁻¹ ^ 2) ^ a * ((v ^ D.d i) ^ 2) ^ a = 1 := by
    rw [← mul_pow, ← mul_pow, inv_mul_cancel₀ hq, one_pow, one_pow]
  simpa only [mul_assoc, mul_left_comm, mul_comm, mul_one, one_mul] using
    congrArg (fun x : k ↦ ((-1) ^ negA D i j * (v ^ D.d i) ^ negA D i j) * x) hp

/-- Actual F-specific compatibility, proved with the noncommuting braid scalars retained. -/
theorem braidDelta_F_chevalley (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) :
    braidDelta R v hv i (F R v j) =
      flipChevalley R v (braidDelta R v hv i (E R v j)) := by
  let T := braidEquivOfNotRoot R hv i
  let TT := Algebra.TensorProduct.congr T T
  let c : k := (-1) ^ negA D i j * (v ^ D.d i) ^ negA D i j
  have hc : TT (flipChevalley R v (braidDelta R v hv i (E R v j))) =
      c • flipChevalley R v (TT (braidDelta R v hv i (E R v j))) := by
    rw [braidDelta_E_offdiag R v hv hij]
    simp only [map_add, map_sum, map_smul, smul_add, Finset.smul_sum]
    congr 1
    · simp only [flipChevalley_tmul, chevalley_E, map_one, TT,
        Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
        AlgEquiv.coe_toAlgHom, T, braid_F_chevalley R v hv hij, tmul_smul, c]
    · apply Finset.sum_congr rfl
      intro a _
      rw [show TT (flipChevalley R v
        ((F R v i ^ a * Kt R v j) ⊗ₜ[k] rankTwoXm R v i j a)) = _ from
          braid_flip_root_term R v hv hij a]
      exact smul_comm _ _ _
  apply TT.injective
  change TT (TT.symm (comul R v (T (F R v j)))) = _
  rw [AlgEquiv.apply_symm_apply, hc]
  change comul R v (T (F R v j)) =
    c • flipChevalley R v (TT (TT.symm (comul R v (T (E R v j)))))
  rw [AlgEquiv.apply_symm_apply, braid_F_chevalley R v hv hij,
    map_smul, comul_chevalley]

/-- The fully normalized negative-generator coproduct, with the actual factor ordering. -/
theorem braidDelta_F_offdiag (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) :
    braidDelta R v hv i (F R v j) = (1 : QuantumGroup R v) ⊗ₜ[k] F R v j +
      ∑ a ∈ Finset.range (negA D i j + 1), coeff (v ^ D.d i) a •
        (chevalley R v (rankTwoXm R v i j a) ⊗ₜ[k]
          (E R v i ^ a * K R v (-ktilde R j))) := by
  rw [braidDelta_F_chevalley R v hv hij, braidDelta_E_offdiag R v hv hij]
  simp only [map_add, map_sum, map_smul, flipChevalley_tmul, map_one, chevalley_E,
    map_mul, map_pow, chevalley_F, Kt, chevalley_K]

/-- Negative convolution in the actual quotient, including its Serre truncation. -/
theorem negative_convolution (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) (m : ℕ) :
    coeff (v ^ D.d i) m • (F R v i ^ m * F R v j) =
      ∑ a ∈ Finset.range (min (negA D i j) m + 1),
        (coeff (v ^ D.d i) a * coeff (v ^ D.d i) (m - a) *
          (v ^ D.d i) ^ (negA D i j * (m - a))) •
            (chevalley R v (rankTwoXm R v i j a) * F R v i ^ (m - a)) := by
  have h := congrArg (chevalley R v) (rankTwoXm_convolution_truncated R v hv hij m)
  simpa only [map_smul, map_mul, map_pow, chevalley_E, map_sum] using h

end FullIntertwining
