/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PositiveComul
import LieLean.Algebra.QuantumGroup.TensorModule

/-!
# Mixed-root coproduct coefficients

The complete coproduct row of each positive root string.

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
open LieLean.QuantumGroup
open BraidDiagonal
variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k)

/-- The two transitions of a root-string coproduct coefficient, retaining every term. -/
def coproductCoeff (q Q : k) : ℕ → ℕ → k
  | 0, t => if t = 0 then 1 else 0
  | m + 1, 0 => (1 - q ^ (2 * m) * Q⁻¹ ^ 2) * coproductCoeff q Q m 0
  | m + 1, t + 1 =>
      (1 - q ^ (2 * (m + t + 1)) * Q⁻¹ ^ 2) * coproductCoeff q Q m (t + 1) +
        q ^ (2 * (m - t)) * coproductCoeff q Q m t

lemma coproductCoeff_above (q Q : k) {m t : ℕ} (h : m < t) :
    coproductCoeff q Q m t = 0 := by
  induction m generalizing t with
  | zero => simp [coproductCoeff, Nat.ne_of_gt h]
  | succ m ih =>
    cases t with
    | zero => omega
    | succ t => simp [coproductCoeff, ih (by omega : m < t), ih (by omega : m < t + 1)]

lemma coproductCoeff_diag (q Q : k) (m : ℕ) : coproductCoeff q Q m m = 1 := by
  induction m with
  | zero => simp [coproductCoeff]
  | succ m ih => simp [coproductCoeff, coproductCoeff_above q Q (Nat.lt_succ_self m), ih]

/-- A coproduct summand, with the original Cartan torus and actual root string. -/
def rootTerm (i j : I) (m t : ℕ) : QuantumGroup R v ⊗[k] QuantumGroup R v :=
  (E R v i ^ (m - t) * (Kt R v i ^ t * Kt R v j)) ⊗ₜ[k]
    rankTwoXp R v i j t

lemma root_weight {i j : I} (hij : i ≠ j) (t : ℕ) :
    Kt R v i * rankTwoXp R v i j t =
      shift (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) t •
        (rankTwoXp R v i j t * Kt R v i) := by
  apply K_mul_X (Kt_mul_E i)
  simpa only [Kt] using
    (show K R v (ktilde R i) * E R v j =
      ((v ^ D.d i) ^ negA D i j)⁻¹ • (E R v j * K R v (ktilde R i)) by
        rw [K_mul_E, zpow_root_ktilde_of_ne hij])

lemma torus_E {i j : I} (hij : i ≠ j) (t : ℕ) :
    (Kt R v i ^ t * Kt R v j) * E R v i =
      ((v ^ D.d i) ^ (2 * t) * ((v ^ D.d i) ^ negA D i j)⁻¹) •
        (E R v i * (Kt R v i ^ t * Kt R v j)) := by
  have hj : Kt R v j * E R v i =
      ((v ^ D.d i) ^ negA D i j)⁻¹ • (E R v i * Kt R v j) := by
    rw [Kt, K_mul_E, root_ktilde_comm, zpow_root_ktilde_of_ne hij]
  have hi : Kt R v i ^ t * E R v i =
      (v ^ D.d i) ^ (2 * t) • (E R v i * Kt R v i ^ t) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc, Kt_mul_E,
        smul_mul_assoc, smul_smul, mul_assoc, ← pow_succ', ← pow_add]
      congr 2
  rw [mul_assoc, hj, mul_smul_comm, ← mul_assoc, hi, smul_mul_assoc,
    smul_smul, mul_assoc, mul_comm (((v ^ D.d i) ^ negA D i j)⁻¹)]

lemma rootTerm_step {i j : I} (hij : i ≠ j) (m t : ℕ) (ht : t ≤ m) :
    (E R v i ⊗ₜ[k] (1 : QuantumGroup R v) + Kt R v i ⊗ₜ[k] E R v i) *
        rootTerm R v i j m t -
      shift (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) m •
        (rootTerm R v i j m t *
          (E R v i ⊗ₜ[k] (1 : QuantumGroup R v) + Kt R v i ⊗ₜ[k] E R v i)) =
      (1 - (v ^ D.d i) ^ (2 * (m + t)) *
        ((v ^ D.d i) ^ negA D i j)⁻¹ ^ 2) • rootTerm R v i j (m + 1) t +
      (v ^ D.d i) ^ (2 * (m - t)) • rootTerm R v i j (m + 1) (t + 1) := by
  have hK : (Kt R v i ^ t * Kt R v j) * Kt R v i =
      Kt R v i ^ (t + 1) * Kt R v j := by
    rw [mul_assoc, show Kt R v j * Kt R v i = Kt R v i * Kt R v j from
      K_comm R v _ _, ← mul_assoc, ← pow_succ]
  have hpow := mul_pow_of_mul_eq_smul (Kt_mul_E (R := R) (v := v) i) (m - t)
  rw [← pow_mul] at hpow
  have hleftE : E R v i * (E R v i ^ (m - t) * (Kt R v i ^ t * Kt R v j)) =
      E R v i ^ (m - t + 1) * (Kt R v i ^ t * Kt R v j) := by
    rw [← mul_assoc, ← pow_succ']
  have hrightE : (E R v i ^ (m - t) * (Kt R v i ^ t * Kt R v j)) * E R v i =
      shift (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) t •
        (E R v i ^ (m - t + 1) * (Kt R v i ^ t * Kt R v j)) := by
    rw [mul_assoc, torus_E R v hij t, mul_smul_comm, ← mul_assoc, ← pow_succ]
    rfl
  have hleftK : Kt R v i * (E R v i ^ (m - t) * (Kt R v i ^ t * Kt R v j)) =
      (v ^ D.d i) ^ (2 * (m - t)) •
        (E R v i ^ (m - t) * (Kt R v i ^ (t + 1) * Kt R v j)) := by
    rw [← mul_assoc, hpow, smul_mul_assoc, mul_assoc, ← mul_assoc (Kt R v i),
      ← pow_succ']
  have hrightK : (E R v i ^ (m - t) * (Kt R v i ^ t * Kt R v j)) * Kt R v i =
      E R v i ^ (m - t) * (Kt R v i ^ (t + 1) * Kt R v j) := by
    rw [mul_assoc, hK]
  have hmt : m + 1 - t = (m - t) + 1 := by omega
  have hmt' : m + 1 - (t + 1) = m - t := by omega
  have hs : shift (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) m =
      (v ^ D.d i) ^ (2 * (m - t)) *
        shift (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) t := by
    simp only [BraidDiagonal.shift]
    rw [← mul_assoc, ← pow_add, show 2 * (m - t) + 2 * t = 2 * m by omega]
  have hst : shift (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) m *
      shift (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) t =
      (v ^ D.d i) ^ (2 * (m + t)) * ((v ^ D.d i) ^ negA D i j)⁻¹ ^ 2 := by
    simp only [BraidDiagonal.shift, mul_add, pow_add]
    ring
  simp only [rootTerm, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul, smul_add, hmt, hmt', rankTwoXp_succ,
    hleftE, hrightE, hleftK, hrightK, tmul_sub, tmul_smul, smul_tmul',
    smul_sub, smul_smul, hst, sub_smul, one_smul]
  rw [hs]
  abel

section Sum
variable {M : Type*} [AddCommGroup M] [Module k M]
lemma coproductCoeff_sum (q Q : k) (m : ℕ) (f : ℕ → M) :
    (∑ t ∈ Finset.range (m + 2), coproductCoeff q Q (m + 1) t • f t) =
      ∑ t ∈ Finset.range (m + 1), coproductCoeff q Q m t •
        ((1 - q ^ (2 * (m + t)) * Q⁻¹ ^ 2) • f t +
          q ^ (2 * (m - t)) • f (t + 1)) := by
  have hf := Finset.sum_range_succ'
    (fun t ↦ ((1 - q ^ (2 * (m + t)) * Q⁻¹ ^ 2) * coproductCoeff q Q m t) • f t)
    (m + 1)
  rw [Finset.sum_range_succ, coproductCoeff_above q Q (Nat.lt_succ_self m)] at hf
  simp only [mul_zero, zero_smul, add_zero] at hf
  rw [Finset.sum_range_succ']
  simp only [coproductCoeff, add_smul, Finset.sum_add_distrib, smul_add, smul_smul]
  have hfirst : (∑ t ∈ Finset.range (m + 1),
      (coproductCoeff q Q m t * (1 - q ^ (2 * (m + t)) * Q⁻¹ ^ 2)) • f t) =
      (∑ t ∈ Finset.range (m + 1),
      ((1 - q ^ (2 * (m + t)) * Q⁻¹ ^ 2) * coproductCoeff q Q m t) • f t) := by
    apply Finset.sum_congr rfl; intro t _; rw [mul_comm]
  rw [hfirst, hf]
  simp only [Nat.add_assoc]
  have hb : (∑ t ∈ Finset.range (m + 1),
      (q ^ (2 * (m - t)) * coproductCoeff q Q m t) • f (t + 1)) =
      (∑ t ∈ Finset.range (m + 1),
      (coproductCoeff q Q m t * q ^ (2 * (m - t))) • f (t + 1)) := by
    apply Finset.sum_congr rfl; intro t _; rw [mul_comm]
  rw [hb]
  abel
end Sum

/-- Full finite coproduct of every actual adjoint root string, in arbitrary Cartan type. -/
theorem comul_rootString [NeZero v] {i j : I} (hij : i ≠ j) (m : ℕ) :
    comul R v (rankTwoXp R v i j m) =
      rankTwoXp R v i j m ⊗ₜ[k] (1 : QuantumGroup R v) +
        ∑ t ∈ Finset.range (m + 1),
          coproductCoeff (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) m t •
            rootTerm R v i j m t := by
  induction m with
  | zero => simp [rankTwoXp_zero, coproductCoeff, rootTerm]
  | succ m ih =>
    have hbase :
        (E R v i ⊗ₜ[k] (1 : QuantumGroup R v) + Kt R v i ⊗ₜ[k] E R v i) *
            (rankTwoXp R v i j m ⊗ₜ[k] (1 : QuantumGroup R v)) -
          shift (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) m •
            ((rankTwoXp R v i j m ⊗ₜ[k] (1 : QuantumGroup R v)) *
              (E R v i ⊗ₜ[k] (1 : QuantumGroup R v) + Kt R v i ⊗ₜ[k] E R v i)) =
          rankTwoXp R v i j (m + 1) ⊗ₜ[k] (1 : QuantumGroup R v) := by
      simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one, root_weight R v hij, smul_tmul', smul_add,
        rankTwoXp_succ, sub_tmul]
      abel
    conv_lhs => rw [rankTwoXp_succ]
    simp only [map_sub, map_smul, map_mul, comul_E, ih]
    rw [show m + 1 + 1 = m + 2 by omega, coproductCoeff_sum]
    have hh : ∑ t ∈ Finset.range (m + 1),
        coproductCoeff (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) m t •
          ((E R v i ⊗ₜ[k] (1 : QuantumGroup R v) + Kt R v i ⊗ₜ[k] E R v i) *
              rootTerm R v i j m t -
            shift (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) m •
              (rootTerm R v i j m t *
                (E R v i ⊗ₜ[k] (1 : QuantumGroup R v) + Kt R v i ⊗ₜ[k] E R v i))) =
        ∑ t ∈ Finset.range (m + 1),
          coproductCoeff (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) m t •
            ((1 - (v ^ D.d i) ^ (2 * (m + t)) *
              ((v ^ D.d i) ^ negA D i j)⁻¹ ^ 2) • rootTerm R v i j (m + 1) t +
              (v ^ D.d i) ^ (2 * (m - t)) • rootTerm R v i j (m + 1) (t + 1)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [rootTerm_step R v hij m t (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ht)]
    rw [← hh, ← hbase]
    simp only [smul_sub, Finset.sum_sub_distrib, smul_add, Finset.sum_add_distrib,
      smul_smul, add_mul, mul_add, mul_smul_comm, smul_mul_assoc,
      Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
    simp only [mul_comm (BraidDiagonal.shift _ _ _) _]
    module

/-- Termination is the actual defining quantum Serre relation, not a truncation premise. -/
lemma rootString_serre [NeZero v] {i j : I} (hij : i ≠ j) :
    rankTwoXp R v i j (negA D i j + 1) = 0 := by
  have hq : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  rw [rankTwoXp, X_eq_serreAux hq (pow_ne_zero _ hq)]
  rw [pow_succ', mul_inv_cancel₀ (mul_ne_zero hq (pow_ne_zero _ hq)), serreAux_one]
  simpa only [one_sub_cartanMatrix_toNat hij] using (serre_E (R := R) (v := v) hij)

/-- The entire mixed tensor expansion cancels at the Serre degree; no term is discarded. -/
theorem rootString_serre_coproduct [NeZero v] {i j : I} (hij : i ≠ j) :
    (∑ t ∈ Finset.range (negA D i j + 2),
      coproductCoeff (v ^ D.d i) ((v ^ D.d i) ^ negA D i j)
        (negA D i j + 1) t • rootTerm R v i j (negA D i j + 1) t) = 0 := by
  have h := comul_rootString R v hij (negA D i j + 1)
  rw [rootString_serre R v hij, map_zero, zero_tmul, zero_add] at h
  exact h.symm

/-- Coproduct of the actual off-diagonal braid image, with all string coefficients. -/
theorem comul_braid_E [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) :
    comul R v (braidEquivOfNotRoot R hv i (E R v j)) =
      (qFactorial (v ^ D.d i) (negA D i j))⁻¹ •
        (rankTwoXp R v i j (negA D i j) ⊗ₜ[k] (1 : QuantumGroup R v) +
          ∑ t ∈ Finset.range (negA D i j + 1),
            coproductCoeff (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (negA D i j) t •
              rootTerm R v i j (negA D i j) t) := by
  have h : braidEquivOfNotRoot R hv i (E R v j) =
      (qFactorial (v ^ D.d i) (negA D i j))⁻¹ • rankTwoXp R v i j (negA D i j) :=
    map_E_eq_rankTwoXp (braidEquivOfNotRoot_hasImages hv R i) hij
  rw [h, map_smul, comul_rootString R v hij]

end MixedIntertwining
