/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.FiniteIntertwining
import LieLean.Algebra.QuantumGroup.BraidCoproduct.MixedIntertwining

/-!
# Inverse-braid root normalization

Actual inverse-braid images of the mixed positive root strings.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994),
37.3.1–37.3.2 and the proof of 38.1.8 (printed pp. 293, 297–299).
The finite-cutoff argument uses the actual quantum group and original Verma modules.
No restricted braid isometry or PBW norm conclusion is asserted here.
-/

open LieLean
noncomputable section
namespace MixedNormalization
open QuantumGroup BraidDiagonal FiniteIntertwining

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]

/-- Exact lowering normalization, retaining the Laurent monomial separately. -/
theorem braid_rankTwoXm (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) (a : ℕ) (ha : a ≤ negA D i j) :
    braidEquivOfNotRoot R hv i (rankTwoXm R v i j a) =
      ((-1) ^ a * (v ^ D.d i) ^ (a * (negA D i j - a + 1)) *
        (qFactorial (v ^ D.d i) a / qFactorial (v ^ D.d i) (negA D i j - a))) •
          rankTwoXp R v i j (negA D i j - a) := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0 :=
    sub_inv_ne_zero_of_pow_ne_one hq0
      (fun n hn ↦ by rw [← pow_mul]; exact hv _ (Nat.mul_pos (D.d_pos i) hn))
  have hfac (n : ℕ) := LusztigF.qFactorial_ne_zero_of_not_root
    (D := D) (NeZero.ne v) hv i n
  have HT := braidEquivOfNotRoot_hasImages hv R i
  induction a with
  | zero => simpa [rankTwoXm_zero] using map_E_eq_rankTwoXp HT hij
  | succ a ih =>
    obtain ⟨n, hn⟩ : ∃ n, negA D i j - a = n + 1 := ⟨negA D i j - a - 1, by omega⟩
    have hn' : negA D i j - (a + 1) = n := by omega
    have hr : negA D i j = n + 1 + a := by omega
    have hs : shift (v ^ D.d i)⁻¹ ((v ^ D.d i)⁻¹ ^ negA D i j) a =
        shift (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (n + 1) := by
      simp only [BraidDiagonal.shift, inv_pow, inv_inv]
      rw [hr]
      field_simp
      ring
    have H := (braidDiagonal_hyp R v (NeZero.ne v) hij hq).stepE (K_neg_mul_Kt i) n
    change braidEi R i * rankTwoXp R v i j (n + 1) -
      shift (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (n + 1) •
        (rankTwoXp R v i j (n + 1) * braidEi R i) =
      (-(shift (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (n + 1) *
        cc (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (n + 1))) •
          rankTwoXp R v i j n at H
    have hc :
        ((-1) ^ a * (v ^ D.d i) ^ (a * (n + 1 + 1)) *
          (qFactorial (v ^ D.d i) a / qFactorial (v ^ D.d i) (n + 1))) *
          -(shift (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (n + 1) *
            cc (v ^ D.d i) ((v ^ D.d i) ^ negA D i j) (n + 1)) =
        (-1) ^ (a + 1) * (v ^ D.d i) ^ ((a + 1) * (n + 1)) *
          (qFactorial (v ^ D.d i) (a + 1) / qFactorial (v ^ D.d i) n) := by
      rw [cc_pow hq0 hq (by omega), show negA D i j - n = a + 1 by omega]
      have hqn : qInt (v ^ D.d i) (n + 1) ≠ 0 := by
        exact (mul_ne_zero_iff.mp (show qInt (v ^ D.d i) (n + 1) *
          qFactorial (v ^ D.d i) n ≠ 0 from hfac (n + 1))).1
      simp only [BraidDiagonal.shift, hr, qFactorial_succ, pow_succ (-1 : k)]
      field_simp [hfac, hqn]
      simp only [← pow_add]
      ring_nf
    have he := map_E_self HT
    change braidEquivOfNotRoot R hv i (E R v i) = _ at he
    rw [rankTwoXm_succ, map_sub, map_mul, map_smul, map_mul, ih (by omega), he,
      hn, hs, mul_smul_comm, smul_mul_assoc, smul_comm _
        ((-1) ^ a * (v ^ D.d i) ^ (a * (n + 1 + 1)) *
          (qFactorial (v ^ D.d i) a / qFactorial (v ^ D.d i) (n + 1))),
      ← smul_sub, H, smul_smul, hc, hn']

/-- The actual inverse braid on every bounded positive root string. -/
theorem inverse_braid_rankTwoXp (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    {i j : I} (hij : i ≠ j) (a : ℕ) (ha : a ≤ negA D i j) :
    (braidEquivOfNotRoot R hv i).symm (rankTwoXp R v i j (negA D i j - a)) =
      ((-1) ^ a * (v ^ D.d i) ^ (a * (negA D i j - a + 1)) *
        (qFactorial (v ^ D.d i) a / qFactorial (v ^ D.d i) (negA D i j - a)))⁻¹ •
          rankTwoXm R v i j a := by
  apply (braidEquivOfNotRoot R hv i).injective
  rw [AlgEquiv.apply_symm_apply, map_smul, braid_rankTwoXm R v hv hij a ha, smul_smul,
    inv_mul_cancel₀, one_smul]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (pow_ne_zero _ (pow_ne_zero _ (NeZero.ne v))))
      (div_ne_zero (LusztigF.qFactorial_ne_zero_of_not_root (NeZero.ne v) hv i a)
        (LusztigF.qFactorial_ne_zero_of_not_root (NeZero.ne v) hv i _))

end MixedNormalization
