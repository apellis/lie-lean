/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.MixedNormalization.CoproductCoefficients

/-!
# Off-diagonal braid coproduct

The exact off-diagonal positive-generator expansion of the conjugated coproduct.

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
open QuantumGroup BraidDiagonal FiniteIntertwining MixedIntertwining
variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]

omit [NeZero v] in
lemma braidFi_pow_torus (i : I) (a t : ℕ) :
    braidFi (v := v) R i ^ a * Kt R v i ^ (a + t) =
      ((-1) ^ a * (v ^ D.d i)⁻¹ ^ (a * (a + 1))) •
        (E R v i ^ a * Kt R v i ^ t) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hp := mul_pow_of_mul_eq_smul (K_neg_ktilde_mul_E (R := R) (v := v) i) (a + 1)
    simp only [inv_pow, ← pow_mul] at hp
    rw [pow_succ', show a + 1 + t = a + t + 1 by omega, pow_succ, mul_assoc,
      ← mul_assoc (braidFi R i ^ a), ih, smul_mul_assoc, mul_smul_comm, ← mul_assoc]
    have ht : braidFi (v := v) R i * (E R v i ^ a * Kt R v i ^ t) * Kt R v i =
        (-((v ^ D.d i)⁻¹ ^ (2 * (a + 1)))) •
          (E R v i ^ (a + 1) * Kt R v i ^ t) := by
      calc
        _ = -(K R v (-ktilde R i) * E R v i ^ (a + 1) *
            (Kt R v i ^ t * Kt R v i)) := by
          rw [braidFi, pow_succ']
          noncomm_ring
        _ = _ := by
          rw [hp, smul_mul_assoc, mul_assoc, ← pow_succ, pow_succ' (Kt R v i),
            mul_assoc (E R v i ^ (a + 1)),
            ← mul_assoc (K R v (-ktilde R i)), K_neg_mul_Kt]
          simp [inv_pow, ← pow_mul]
    rw [ht, smul_smul]
    congr 1
    ring

lemma braid_firstLeg (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) (a : ℕ) (ha : a ≤ negA D i j) :
    braidEquivOfNotRoot R hv i (F R v i ^ a * Kt R v j) =
      ((-1) ^ a * (v ^ D.d i)⁻¹ ^ (a * (a + 1))) •
        (E R v i ^ a * (Kt R v i ^ (negA D i j - a) * Kt R v j)) := by
  have HT := braidEquivOfNotRoot_hasImages hv R i
  have hF : braidEquivOfNotRoot R hv i (F R v i) = braidFi R i := by
    simpa using HT.map_F i
  have hK : braidEquivOfNotRoot R hv i (Kt R v j) =
      Kt R v i ^ negA D i j * Kt R v j := by
    have hh : ∀ μ, braidEquivOfNotRoot R hv i (K R v μ) = K R v (reflY R i μ) := HT.map_K
    rw [Kt, hh, reflY_ktilde_of_ne hij, Kt, K_pow, K_add, add_comm]
  rw [map_mul, map_pow, hF, hK, ← mul_assoc,
    show negA D i j = a + (negA D i j - a) by omega, braidFi_pow_torus,
    smul_mul_assoc, mul_assoc, Nat.add_sub_cancel_left]

lemma triangle_square (a : ℕ) :
    (∑ h ∈ Finset.range a, h) + (∑ h ∈ Finset.range a, h) + a = a * a := by
  induction a with
  | zero => simp
  | succ a ih => rw [Finset.sum_range_succ]; nlinarith

lemma normalized_scalar {q : k} (hq : q ≠ 0)
    (hf : ∀ n, qFactorial q n ≠ 0) (a t : ℕ) :
    coeff q a * ((-1) ^ a * q⁻¹ ^ (a * (a + 1))) *
      ((-1) ^ a * q ^ (a * (t + 1)) * (qFactorial q a / qFactorial q t)) =
      (qFactorial q (t + a))⁻¹ * coproductCoeff q (q ^ (t + a)) (t + a) t := by
  rw [coproductCoeff_top hq hf, coeff_closed]
  have hn : (-1 : k) ^ a * (-1) ^ a = 1 := by
    rw [← mul_pow]; simp
  have hp : q ^ (∑ h ∈ Finset.range a, h) * q ^ (a * (t + 1)) *
      q ^ ((∑ h ∈ Finset.range a, h) + a) = q ^ (t * a) * q ^ (a * (a + 1)) := by
    simp only [← pow_add]
    congr 1
    have hs := triangle_square a
    nlinarith
  simp only [inv_pow]
  field_simp [hf]
  have hn2 : ((-1 : k) ^ a) ^ 2 = 1 := by rw [pow_two, hn]
  rw [hn2]
  linear_combination (((q ^ 2 - 1) / q) ^ a) * hp

/-- Normalized conjugated coproduct of the actual off-diagonal E generator. -/
theorem braidDelta_E_offdiag (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) :
    braidDelta R v hv i (E R v j) = E R v j ⊗ₜ[k] (1 : QuantumGroup R v) +
      ∑ a ∈ Finset.range (negA D i j + 1), coeff (v ^ D.d i) a •
        ((F R v i ^ a * Kt R v j) ⊗ₜ[k] rankTwoXm R v i j a) := by
  let T := braidEquivOfNotRoot R hv i
  apply (Algebra.TensorProduct.congr T T).injective
  change (Algebra.TensorProduct.congr T T)
    ((Algebra.TensorProduct.congr T T).symm (comul R v (T (E R v j)))) = _
  rw [AlgEquiv.apply_symm_apply, comul_braid_E R v hv hij]
  have hE : T (E R v j) =
      (qFactorial (v ^ D.d i) (negA D i j))⁻¹ •
        rankTwoXp R v i j (negA D i j) :=
    map_E_eq_rankTwoXp (braidEquivOfNotRoot_hasImages hv R i) hij
  simp only [map_add, map_sum, map_smul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, map_one,
    hE, smul_tmul', smul_add, Finset.smul_sum]
  congr 1
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ≤ negA D i j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  simp only [show negA D i j + 1 - 1 - a = negA D i j - a by omega, rootTerm]
  change _ = coeff (v ^ D.d i) a •
    ((T (F R v i ^ a * Kt R v j)) ⊗ₜ[k] T (rankTwoXm R v i j a))
  rw [braid_firstLeg R v hv hij a ha', braid_rankTwoXm R v hv hij a ha']
  simp only [← smul_tmul', tmul_smul, smul_smul, Nat.sub_sub_self ha']
  have hs := normalized_scalar (q := v ^ D.d i) (pow_ne_zero _ (NeZero.ne v))
    (fun n ↦ LusztigF.qFactorial_ne_zero_of_not_root (NeZero.ne v) hv i n)
    a (negA D i j - a)
  rw [show negA D i j - a + a = negA D i j by omega] at hs
  congr 1
  linear_combination -hs

end MixedNormalization
