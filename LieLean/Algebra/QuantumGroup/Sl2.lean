/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Hopf
import LieLean.Algebra.QuantumGroup.Weight

/-!
# `U_q(𝔰𝔩₂)`-calculus in `U_q(𝔤)`

For each `i ∈ I` the elements `Eᵢ, Fᵢ, K̃ᵢ^{±1}` of `U = U_q(𝔤)` satisfy the relations of
`U_{vᵢ}(𝔰𝔩₂)`, `vᵢ = v^{dᵢ}`. We prove the basic commutation formula ([Jan] Lemma 1.7 (check),
[Lus] 3.1.9 (check) in divided-power form)
`Eᵢ Fᵢ^{n+1} - Fᵢ^{n+1} Eᵢ = [n+1]ᵢ Fᵢⁿ (vᵢ⁻ⁿ K̃ᵢ - vᵢⁿ K̃ᵢ⁻¹)/(vᵢ - vᵢ⁻¹)`
and its consequences for weight vectors annihilated by `Eᵢ`: if `m ∈ M^Λ`, `Eᵢ m = 0`, then
`Eᵢ Fᵢ^{s+1} m = [s+1]ᵢ [⟨i, Λ⟩ - s]ᵢ Fᵢ^s m`; in particular `Fᵢ^{⟨i,Λ⟩+1} m` is again
annihilated by `Eᵢ` (and by all `Eⱼ`, `j ≠ i`) when `⟨i, Λ⟩ ≥ 0` ([Jan] 2.3, 5.6 (check)).

## Main results

* `QuantumGroup.E_mul_F_pow_sub`: the commutation formula above.
* `QuantumGroup.E_mul_qDivPow_F_sub`: its divided-power form
  `[Eᵢ, Fᵢ^{(n+1)}] = Fᵢ^{(n)} (vᵢ⁻ⁿ K̃ᵢ - vᵢⁿ K̃ᵢ⁻¹)/(vᵢ - vᵢ⁻¹)`.
* `QuantumGroup.E_smul_F_pow_smul`: `Eᵢ Fᵢ^{s+1} m` for a highest weight vector `m` (for `Eᵢ`).
* `QuantumGroup.E_smul_F_pow_smul_eq_zero`: `Eⱼ Fᵢ^{⟨i,Λ⟩+1} m = 0` for all `j`, if `m ∈ M^Λ` is
  annihilated by all `Eⱼ` and `⟨i, Λ⟩ ≥ 0`.

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 1–2, 5.
* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §3.1.
-/

noncomputable section

namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}

/-- `K̃ᵢ Fᵢ = vᵢ⁻² Fᵢ K̃ᵢ`. -/
lemma Kt_mul_F (i : I) :
    Kt R v i * F R v i = (v ^ D.d i)⁻¹ ^ 2 • (F R v i * Kt R v i) := by
  rw [Kt, K_mul_F, zpow_neg, zpow_root_ktilde_self, inv_pow]

/-- `K̃ᵢ⁻¹ Fᵢ = vᵢ² Fᵢ K̃ᵢ⁻¹`. -/
lemma K_neg_ktilde_mul_F (i : I) :
    K R v (-ktilde R i) * F R v i = (v ^ D.d i) ^ 2 • (F R v i * K R v (-ktilde R i)) := by
  rw [K_mul_F, map_neg, neg_neg, zpow_root_ktilde_self]

/-- `Eᵢ Fⱼ = Fⱼ Eᵢ` for `i ≠ j`. -/
lemma E_mul_F_of_ne {i j : I} (hij : i ≠ j) : E R v i * F R v j = F R v j * E R v i := by
  simpa [hij, sub_eq_zero] using E_mul_F_sub R v i j

lemma qInt_aux_inv {q : k} (hq : q ≠ 0) (c : k) (n : ℕ) :
    qInt q (n + 1) * c * q⁻¹ ^ n * q⁻¹ ^ 2 + c = qInt q (n + 1 + 1) * c * q⁻¹ ^ (n + 1) := by
  have h3 : q⁻¹ ^ (n + 1) * q ^ (n + 1) = 1 := by rw [← mul_pow, inv_mul_cancel₀ hq, one_pow]
  rw [qInt_succ (v := q) (n + 1)]
  linear_combination (-c) * h3

lemma qInt_aux {q : k} (hq : q ≠ 0) (c : k) (n : ℕ) :
    qInt q (n + 1) * c * q ^ n * q ^ 2 + c = qInt q (n + 1 + 1) * c * q ^ (n + 1) := by
  have h3 : q⁻¹ ^ (n + 1) * q ^ (n + 1) = 1 := by rw [← mul_pow, inv_mul_cancel₀ hq, one_pow]
  have h2 := qInt_mul_sub (v := q) (n + 1)
  rw [qInt_succ (v := q) (n + 1)]
  linear_combination (c * q ^ (n + 1)) * h2 - c * h3

/-- The commutation formula ([Jan] Lemma 1.7 (check)):
`Eᵢ Fᵢ^{n+1} - Fᵢ^{n+1} Eᵢ = [n+1]ᵢ Fᵢⁿ (vᵢ⁻ⁿ K̃ᵢ - vᵢⁿ K̃ᵢ⁻¹)/(vᵢ - vᵢ⁻¹)`. -/
theorem E_mul_F_pow_sub (hv : v ≠ 0) (i : I) (n : ℕ) :
    E R v i * F R v i ^ (n + 1) - F R v i ^ (n + 1) * E R v i =
      (qInt (v ^ D.d i) (n + 1) * (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹) •
        (F R v i ^ n * ((v ^ D.d i)⁻¹ ^ n • Kt R v i - (v ^ D.d i) ^ n •
          K R v (-ktilde R i))) := by
  set q := v ^ D.d i with hq
  set c := (q - q⁻¹)⁻¹
  have hq0 : q ≠ 0 := pow_ne_zero _ hv
  have hEF : E R v i * F R v i - F R v i * E R v i = c • (Kt R v i - K R v (-ktilde R i)) := by
    simp only [E_mul_F_sub, ↓reduceIte]; rfl
  induction n with
  | zero => simp [hEF, qInt]
  | succ n ih =>
    set Kp := Kt R v i
    set Km := K R v (-ktilde R i)
    set Fi := F R v i
    have e1 : E R v i * Fi ^ (n + 1 + 1) - Fi ^ (n + 1 + 1) * E R v i =
        (E R v i * Fi ^ (n + 1) - Fi ^ (n + 1) * E R v i) * Fi +
          Fi ^ (n + 1) * (E R v i * Fi - Fi * E R v i) := by
      rw [pow_succ Fi (n + 1)]; noncomm_ring
    have hp : Fi ^ n * Kp * Fi = q⁻¹ ^ 2 • (Fi ^ (n + 1) * Kp) := by
      rw [mul_assoc, Kt_mul_F, mul_smul_comm, ← mul_assoc, ← pow_succ]
    have hm : Fi ^ n * Km * Fi = q ^ 2 • (Fi ^ (n + 1) * Km) := by
      rw [mul_assoc, K_neg_ktilde_mul_F, mul_smul_comm, ← mul_assoc, ← pow_succ]
    have lhs : E R v i * Fi ^ (n + 1 + 1) - Fi ^ (n + 1 + 1) * E R v i =
        (qInt q (n + 1) * c * q⁻¹ ^ n * q⁻¹ ^ 2 + c) • (Fi ^ (n + 1) * Kp) -
          (qInt q (n + 1) * c * q ^ n * q ^ 2 + c) • (Fi ^ (n + 1) * Km) := by
      rw [e1, ih, hEF]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [hp, hm]
      module
    rw [lhs, qInt_aux_inv hq0, qInt_aux hq0]
    simp only [mul_sub, mul_smul_comm, smul_sub, smul_smul]

/-- The commutation formula in divided powers ([Lus] 3.1.9 (check)): if `[n+1]ᵢ ≠ 0`, then
`[Eᵢ, Fᵢ^{(n+1)}] = Fᵢ^{(n)} (vᵢ⁻ⁿ K̃ᵢ - vᵢⁿ K̃ᵢ⁻¹)/(vᵢ - vᵢ⁻¹)`. -/
theorem E_mul_qDivPow_F_sub (hv : v ≠ 0) (i : I) (n : ℕ) (hn : qInt (v ^ D.d i) (n + 1) ≠ 0) :
    E R v i * qDivPow (v ^ D.d i) (n + 1) (F R v i) -
        qDivPow (v ^ D.d i) (n + 1) (F R v i) * E R v i =
      (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (qDivPow (v ^ D.d i) n (F R v i) *
        ((v ^ D.d i)⁻¹ ^ n • Kt R v i - (v ^ D.d i) ^ n • K R v (-ktilde R i))) := by
  simp only [qDivPow, mul_smul_comm, smul_mul_assoc, ← smul_sub]
  rw [E_mul_F_pow_sub hv, smul_smul, smul_smul, qFactorial_succ, mul_inv]
  congr 1
  field_simp

section Module

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

/-- For a weight vector `m ∈ M^Λ` with `Eᵢ m = 0` ([Jan] 2.3 (check)):
`Eᵢ Fᵢ^{s+1} m = [s+1]ᵢ (vᵢ^{⟨i,Λ⟩-s} - vᵢ^{s-⟨i,Λ⟩})/(vᵢ - vᵢ⁻¹) Fᵢ^s m`. -/
theorem E_smul_F_pow_smul (hv : v ≠ 0) {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ)
    {i : I} (hE : E R v i • m = 0) (s : ℕ) :
    E R v i • (F R v i ^ (s + 1) • m) =
      (qInt (v ^ D.d i) (s + 1) * (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ *
        ((v ^ D.d i)⁻¹ ^ s * (v ^ D.d i) ^ Λ (R.coroot i) -
          (v ^ D.d i) ^ s * (v ^ D.d i) ^ (-Λ (R.coroot i)))) • (F R v i ^ s • m) := by
  have h := E_mul_F_pow_sub (R := R) hv i s
  rw [sub_eq_iff_eq_add] at h
  have hK : ((v ^ D.d i)⁻¹ ^ s • Kt R v i - (v ^ D.d i) ^ s • K R v (-ktilde R i)) • m =
      ((v ^ D.d i)⁻¹ ^ s * (v ^ D.d i) ^ Λ (R.coroot i) -
        (v ^ D.d i) ^ s * (v ^ D.d i) ^ (-Λ (R.coroot i))) • m := by
    rw [sub_smul, smul_assoc, smul_assoc, Kt_smul_of_mem_weightSpace hm,
      K_neg_ktilde_smul_of_mem_weightSpace hm, smul_smul, smul_smul, sub_smul]
  rw [← mul_smul, h, add_smul, mul_smul (F R v i ^ (s + 1)), hE, smul_zero, add_zero,
    smul_assoc, mul_smul (F R v i ^ s), hK, smul_comm (F R v i ^ s), smul_smul]

/-- If `m ∈ M^Λ` is annihilated by all `Eⱼ` and `⟨i, Λ⟩ = n ≥ 0`, then `Fᵢ^{n+1} m` is again
annihilated by all `Eⱼ` ([Jan] 5.6 (check); the standard argument). -/
theorem E_smul_F_pow_smul_eq_zero (hv : v ≠ 0) {Λ : Y →+ ℤ} {m : M}
    (hm : m ∈ weightSpace R v M Λ) (hE : ∀ j, E R v j • m = 0) {i : I} {n : ℕ}
    (hn : Λ (R.coroot i) = n) (j : I) : E R v j • (F R v i ^ (n + 1) • m) = 0 := by
  by_cases hij : j = i
  · subst hij
    rw [E_smul_F_pow_smul hv hm (hE j), hn]
    have hq : v ^ D.d j ≠ 0 := pow_ne_zero _ hv
    have : (v ^ D.d j)⁻¹ ^ n * (v ^ D.d j) ^ (n : ℤ) -
        (v ^ D.d j) ^ n * (v ^ D.d j) ^ (-(n : ℤ)) = 0 := by
      rw [zpow_neg, zpow_natCast, inv_pow]; field_simp; ring
    rw [this, mul_zero, zero_smul]
  · rw [← mul_smul, ((Commute.pow_right (E_mul_F_of_ne hij) (n + 1))).eq, mul_smul, hE,
      smul_zero]

end Module

end QuantumGroup
