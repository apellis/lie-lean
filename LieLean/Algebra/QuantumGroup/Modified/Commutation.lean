/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.Quotient

/-!
# Commutation of divided powers in `U̇`

The commutation formulas of [Lus] 23.1.3 in `U̇`:
`Eᵢ^{(a)} Fᵢ^{(b)} 1_λ = Σ_t [⟨i,λ⟩ + a - b; t]ᵢ Fᵢ^{(b-t)} Eᵢ^{(a-t)} 1_λ` and the analogue for
`Fᵢ^{(b)} Eᵢ^{(a)} 1_λ`, with the Gaussian binomials `[m; t]` for `m ∈ ℤ` of [Lus] 1.3.1, and
`Eᵢ^{(a)} Fⱼ^{(b)} = Fⱼ^{(b)} Eᵢ^{(a)}` for `i ≠ j`. (Lusztig writes the first formula as
`Eᵢ^{(a)} 1_{-λ} Fᵢ^{(b)} = Σ_t [a + b - ⟨i,λ⟩; t]ᵢ Fᵢ^{(b-t)} 1_{-λ+(a+b-t)i'} Eᵢ^{(a-t)}`; this is
the same identity with `λ` replaced by the weight on the right.)

The proof is by induction on `a`, carried out on a weight vector of an arbitrary `U`-module
(`qDivPow_E_smul_qDivPow_F_smul`), using [Lus] 3.1.9 for `a = 1` (`E_mul_qDivPow_F_sub`); it is
transferred to `U̇` through the left `U`-module `U / Σ_μ U (K_μ - v^{⟨μ,λ⟩})`
(`Modified.elt_eq_of_sub_mem_rightRel`).

## Main results

* `QuantumGroup.qBinomZ`: `[m; t] = ∏_{s=0}^{t-1} [m - s] / [t]!` for `m ∈ ℤ` ([Lus] 1.3.1).
* `QuantumGroup.qDivPow_E_smul_qDivPow_F_smul`: the formula on weight vectors of `U`-modules.
* `QuantumGroup.Modified.dE`, `Modified.dF`: `Eᵢ^{(n)} 1_λ`, `Fᵢ^{(n)} 1_λ` in `U̇`.
* `QuantumGroup.Modified.dE_mul_dF`, `Modified.dF_mul_dE`: **[Lus] 23.1.3** in `U̇`.
* `QuantumGroup.Modified.dE_mul_dF_of_ne`: `Eᵢ^{(a)} Fⱼ^{(b)} 1_λ = Fⱼ^{(b)} Eᵢ^{(a)} 1_λ`, `i ≠ j`.

All for `v ≠ 0` not a root of unity, over any field and root datum.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.3.1, 3.1.9, 23.1.3.
-/

open LieLean Finset

noncomputable section

namespace LieLean.QuantumGroup

/-! ### Gaussian binomials with integer top -/

section QBinomZ

variable {k : Type*} [Field k] (q : k)

/-- The Gaussian binomial `[m; t] = ∏_{s=0}^{t-1} [m - s] / ∏_{s=1}^{t} [s]` for `m ∈ ℤ`,
`t ∈ ℕ` ([Lus] 1.3.1), with `[n] = (qⁿ - q⁻ⁿ)/(q - q⁻¹)` (`qIntZ`). -/
def qBinomZ (m : ℤ) : ℕ → k
  | 0 => 1
  | t + 1 => qBinomZ m t * qIntZ q (m - t) / qIntZ q (t + 1)

variable {q}

@[simp] lemma qBinomZ_zero (m : ℤ) : qBinomZ q m 0 = 1 := rfl

lemma qBinomZ_succ (m : ℤ) (t : ℕ) :
    qBinomZ q m (t + 1) = qBinomZ q m t * qIntZ q (m - t) / qIntZ q (t + 1) := rfl

/-- `[m + 1; t + 1] = [m; t] [m + 1] / [t + 1]`. -/
lemma qBinomZ_succ_succ (m : ℤ) (t : ℕ) :
    qBinomZ q (m + 1) (t + 1) = qBinomZ q m t * qIntZ q (m + 1) / qIntZ q (t + 1) := by
  induction t with
  | zero => simp [qBinomZ_succ]
  | succ t ih =>
    rw [qBinomZ_succ, ih, qBinomZ_succ]
    have e : m + 1 - ((t + 1 : ℕ) : ℤ) = m - t := by push_cast; ring
    rw [e]
    push_cast
    ring

/-- `[x][y] - [x - s][y - s] = [s][x + y - s]`. -/
lemma qIntZ_mul_sub_mul (hq0 : q ≠ 0) (x y s : ℤ) :
    qIntZ q x * qIntZ q y - qIntZ q (x - s) * qIntZ q (y - s) =
      qIntZ q s * qIntZ q (x + y - s) := by
  by_cases hq : q - q⁻¹ = 0
  · simp [qIntZ, hq]
  simp only [qIntZ, sub_eq_add_neg, neg_add, neg_neg, zpow_add₀ hq0, zpow_neg]
  field_simp
  ring

/-- The recursion behind [Lus] 23.1.3:
`[N+1][m+1; t+1] = [N-t][m; t+1] + [m+N+1-t][m; t]`, if `[t+1] ≠ 0`. -/
lemma qIntZ_mul_qBinomZ_succ (hq0 : q ≠ 0) (m N : ℤ) (t : ℕ) (ht : qIntZ q (t + 1) ≠ 0) :
    qIntZ q (N + 1) * qBinomZ q (m + 1) (t + 1) =
      qIntZ q (N - t) * qBinomZ q m (t + 1) + qIntZ q (m + N + 1 - t) * qBinomZ q m t := by
  rw [qBinomZ_succ_succ, qBinomZ_succ]
  have h := qIntZ_mul_sub_mul hq0 (N + 1) (m + 1) (t + 1)
  have e1 : N + 1 - (t + 1) = N - t := by ring
  have e2 : m + 1 - (t + 1) = m - t := by ring
  have e3 : N + 1 + (m + 1) - (t + 1) = m + N + 1 - t := by ring
  rw [e1, e2, e3] at h
  field_simp
  linear_combination qBinomZ q m t * h

end QBinomZ

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}

/-! ### Divided powers -/

section DividedPowers

lemma qDivPow_zero' {B : Type*} [Ring B] [Algebra k B] (q : k) (x : B) : qDivPow q 0 x = 1 := by
  simp [qDivPow, qFactorial]

lemma mul_qDivPow (q : k) {B : Type*} [Ring B] [Algebra k B] (x : B) (n : ℕ)
    (hn : qInt q (n + 1) ≠ 0) : x * qDivPow q n x = qInt q (n + 1) • qDivPow q (n + 1) x := by
  simp only [qDivPow, mul_smul_comm, smul_smul, qFactorial_succ, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ hn, one_mul, pow_succ']

variable (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

omit [DecidableEq I] in
include hv in
lemma vd_pow_ne_one (i : I) : ∀ n : ℕ, 0 < n → (v ^ D.d i) ^ n ≠ 1 := fun n hn ↦ by
  rw [← pow_mul]; exact hv _ (Nat.mul_pos (D.d_pos i) hn)

variable [NeZero v]

omit [DecidableEq I] in
include hv in
lemma qInt_vd_ne_zero (i : I) {n : ℕ} (hn : 0 < n) : qInt (v ^ D.d i) n ≠ 0 :=
  qInt_ne_zero_of_pow_ne_one (pow_ne_zero _ (NeZero.ne v)) (vd_pow_ne_one hv i) hn

omit [DecidableEq I] in
include hv in
lemma qIntZ_vd_ne_zero (i : I) {n : ℤ} (hn : n ≠ 0) : qIntZ (v ^ D.d i) n ≠ 0 :=
  qIntZ_ne_zero (pow_ne_zero _ (NeZero.ne v)) (vd_pow_ne_one hv i) hn

end DividedPowers

lemma pow_mem_adWeightSpace' [NeZero v] {χ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v χ) (n : ℕ) : x ^ n ∈ adWeightSpace R v (n • χ) := by
  induction n with
  | zero => simpa using one_mem_adWeightSpace
  | succ n ih => rw [pow_succ, succ_nsmul]; exact mul_mem_adWeightSpace ih hx

/-! ### The formula on weight vectors -/

section Module

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

lemma pow_E_smul_mem_weightSpace {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ) (i : I)
    (n : ℕ) : E R v i ^ n • m ∈ weightSpace R v M (Λ + n • R.root i) := by
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    rw [pow_succ', mul_smul, succ_nsmul, ← add_assoc]
    exact E_smul_mem_weightSpace ih i

lemma qDivPow_E_smul_mem_weightSpace {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ)
    (i : I) (n : ℕ) :
    qDivPow (v ^ D.d i) n (E R v i) • m ∈ weightSpace R v M (Λ + n • R.root i) := by
  rw [qDivPow, smul_assoc]
  exact Submodule.smul_mem _ _ (pow_E_smul_mem_weightSpace hm i n)

include hv in
/-- `Eᵢ Fᵢ^{(n+1)} m = Fᵢ^{(n+1)} Eᵢ m + [⟨i,Λ⟩ - n]ᵢ Fᵢ^{(n)} m` for `m ∈ M^Λ` ([Lus] 3.1.9). -/
lemma E_smul_qDivPow_F_smul {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ) (i : I)
    (n : ℕ) :
    E R v i • (qDivPow (v ^ D.d i) (n + 1) (F R v i) • m) =
      qDivPow (v ^ D.d i) (n + 1) (F R v i) • (E R v i • m) +
        qIntZ (v ^ D.d i) (Λ (R.coroot i) - n) • (qDivPow (v ^ D.d i) n (F R v i) • m) := by
  set q := v ^ D.d i with hqdef
  have hq0 : q ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have h := E_mul_qDivPow_F_sub (R := R) (NeZero.ne v) i n (qInt_vd_ne_zero hv i n.succ_pos)
  rw [sub_eq_iff_eq_add] at h
  have hK : ((q)⁻¹ ^ n • Kt R v i - q ^ n • K R v (-ktilde R i)) • m =
      (q⁻¹ ^ n * q ^ Λ (R.coroot i) - q ^ n * q ^ (-Λ (R.coroot i))) • m := by
    rw [sub_smul, smul_assoc, smul_assoc, Kt_smul_of_mem_weightSpace hm,
      K_neg_ktilde_smul_of_mem_weightSpace hm, smul_smul, smul_smul, sub_smul]
  have hc : (q - q⁻¹)⁻¹ * (q⁻¹ ^ n * q ^ Λ (R.coroot i) - q ^ n * q ^ (-Λ (R.coroot i))) =
      qIntZ q (Λ (R.coroot i) - n) := by
    rw [qIntZ, div_eq_inv_mul, neg_sub, zpow_sub₀ hq0, zpow_sub₀ hq0, zpow_neg, zpow_natCast,
      inv_pow]
    ring
  rw [← mul_smul, h, add_smul, mul_smul, smul_assoc, mul_smul, hK, smul_comm _ (_ : k),
    smul_smul, hc]
  exact add_comm _ _

include hv in
/-- `Eᵢ Eᵢ^{(n)} = [n+1]ᵢ Eᵢ^{(n+1)}`. -/
lemma E_mul_qDivPow_E (i : I) (n : ℕ) :
    E R v i * qDivPow (v ^ D.d i) n (E R v i) =
      qInt (v ^ D.d i) (n + 1) • qDivPow (v ^ D.d i) (n + 1) (E R v i) :=
  mul_qDivPow _ _ n (qInt_vd_ne_zero hv i n.succ_pos)

variable (R v) in
/-- The summand of the commutation formula. -/
def efTerm (i : I) (h : ℤ) (N M' t : ℕ) (m : M) : M :=
  if t ≤ M' then qBinomZ (v ^ D.d i) (h + N - M') t •
    (qDivPow (v ^ D.d i) (M' - t) (F R v i) • qDivPow (v ^ D.d i) (N - t) (E R v i) • m)
  else 0

include hv in
/-- **The commutation formula on weight vectors** ([Lus] 3.1.9, 23.1.3): for `m ∈ M^Λ`,
`Eᵢ^{(N)} Fᵢ^{(M)} m = Σ_{t ≤ min(N, M)} [⟨i,Λ⟩ + N - M; t]ᵢ Fᵢ^{(M-t)} Eᵢ^{(N-t)} m`. -/
theorem qDivPow_E_smul_qDivPow_F_smul {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ)
    (i : I) (N M' : ℕ) :
    qDivPow (v ^ D.d i) N (E R v i) • qDivPow (v ^ D.d i) M' (F R v i) • m =
      ∑ t ∈ range (N + 1), efTerm R v i (Λ (R.coroot i)) N M' t m := by
  set h := Λ (R.coroot i)
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  induction N with
  | zero => simp [efTerm, qDivPow_zero']
  | succ N ih =>
    have hc : qInt (v ^ D.d i) (N + 1) ≠ 0 := qInt_vd_ne_zero hv i N.succ_pos
    have hcZ : qIntZ (v ^ D.d i) ((N : ℤ) + 1) = qInt (v ^ D.d i) (N + 1) := by
      rw [← qIntZ_natCast (sub_inv_ne_zero_of_pow_ne_one hq0 (vd_pow_ne_one hv i))]; push_cast; rfl
    refine smul_right_injective M hc ?_
    simp only
    have hL : qInt (v ^ D.d i) (N + 1) • (qDivPow (v ^ D.d i) (N + 1) (E R v i) •
        qDivPow (v ^ D.d i) M' (F R v i) • m) =
        ∑ t ∈ range (N + 1), E R v i • efTerm R v i h N M' t m := by
      rw [← smul_assoc, ← E_mul_qDivPow_E hv, mul_smul, ih, smul_sum]
    let g1 : ℕ → M := fun t ↦ if t ≤ M' then
      (qBinomZ (v ^ D.d i) (h + N - M') t * qIntZ (v ^ D.d i) (N + 1 - t)) •
        (qDivPow (v ^ D.d i) (M' - t) (F R v i) • qDivPow (v ^ D.d i) (N + 1 - t) (E R v i) • m)
      else 0
    let g2 : ℕ → M := fun t ↦ if t + 1 ≤ M' then
      (qBinomZ (v ^ D.d i) (h + N - M') t * qIntZ (v ^ D.d i) (h + N - M' + N + 1 - t)) •
        (qDivPow (v ^ D.d i) (M' - (t + 1)) (F R v i) •
          qDivPow (v ^ D.d i) (N + 1 - (t + 1)) (E R v i) • m) else 0
    have hT : ∀ t ∈ range (N + 1), E R v i • efTerm R v i h N M' t m = g1 t + g2 t := by
      intro t ht
      rw [mem_range] at ht
      have hx := qDivPow_E_smul_mem_weightSpace hm i (N - t)
      have hEx : E R v i • (qDivPow (v ^ D.d i) (N - t) (E R v i) • m) =
          qIntZ (v ^ D.d i) (N + 1 - t) • (qDivPow (v ^ D.d i) (N + 1 - t) (E R v i) • m) := by
        rw [← mul_smul, E_mul_qDivPow_E hv, smul_assoc,
          ← qIntZ_natCast (sub_inv_ne_zero_of_pow_ne_one hq0 (vd_pow_ne_one hv i)) (N - t + 1)]
        have e1 : (((N - t + 1 : ℕ) : ℤ)) = N + 1 - t := by omega
        have e2 : N - t + 1 = N + 1 - t := by omega
        rw [e1, e2]
      simp only [g1, g2, efTerm]
      by_cases h1 : t ≤ M'
      · simp only [h1, ↓reduceIte]
        by_cases h2 : t + 1 ≤ M'
        · simp only [h2, ↓reduceIte]
          obtain ⟨n, hn⟩ : ∃ n, M' - t = n + 1 := ⟨M' - t - 1, by omega⟩
          rw [show M' - (t + 1) = n by omega, show N + 1 - (t + 1) = N - t by omega, hn,
            smul_comm, E_smul_qDivPow_F_smul hv hx, hEx, smul_add, smul_comm _ (_ : k),
            smul_smul, smul_smul]
          have e3 : (Λ + (N - t) • R.root i) (R.coroot i) - n = h + N - M' + N + 1 - t := by
            simp only [AddMonoidHom.add_apply, AddMonoidHom.smul_apply, R.root_coroot,
              D.cartanMatrix_self, nsmul_eq_mul, h]
            push_cast [Nat.cast_sub (show t ≤ N by omega)]
            omega
          rw [e3, smul_smul]
        · simp only [h2, ↓reduceIte, add_zero]
          have ht' : M' - t = 0 := by omega
          rw [ht', qDivPow_zero', one_smul, smul_comm, hEx, smul_smul, one_smul]
      · have h1' : ¬ t + 1 ≤ M' := by omega
        simp only [h1, h1', ↓reduceIte, smul_zero, add_zero]
    rw [hL, sum_congr rfl hT, sum_add_distrib, smul_sum]
    have hs1 : ∑ t ∈ range (N + 1), g1 t = ∑ t ∈ range (N + 2), g1 t := by
      rw [sum_range_succ _ (N + 1)]
      simp only [g1]
      split_ifs <;> simp
    have hs2 : ∑ t ∈ range (N + 1), g2 t =
        ∑ t ∈ range (N + 2), (if t = 0 then 0 else g2 (t - 1)) := by
      rw [sum_range_succ' _ (N + 1)]
      simp
    rw [hs1, hs2, ← sum_add_distrib]
    refine sum_congr rfl fun t _ ↦ ?_
    rcases t with _ | s
    · simp only [g1, efTerm, zero_le, ↓reduceIte, qBinomZ_zero, one_mul, Nat.cast_zero, sub_zero,
        add_zero, one_smul, Nat.sub_zero, hcZ]
    · simp only [g1, g2, efTerm, Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte]
      by_cases hs : s + 1 ≤ M'
      · simp only [hs, ↓reduceIte]
        rw [← add_smul, smul_smul (qInt (v ^ D.d i) (N + 1))]
        congr 1
        have hsZ : qIntZ (v ^ D.d i) ((s : ℤ) + 1) ≠ 0 := qIntZ_vd_ne_zero hv i (by omega)
        have key := qIntZ_mul_qBinomZ_succ hq0 (h + N - M') N s hsZ
        have e1 : h + ((N + 1 : ℕ) : ℤ) - M' = h + N - M' + 1 := by push_cast; ring
        have e2 : (N : ℤ) + 1 - ((s + 1 : ℕ) : ℤ) = N - s := by push_cast; ring
        rw [e1, e2, ← hcZ]
        linear_combination -key
      · simp only [hs, ↓reduceIte, add_zero, smul_zero]

end Module


/-! ### Transfer to `U̇` -/

lemma map_qDivPow' {B B' : Type*} [Ring B] [Algebra k B] [Ring B'] [Algebra k B'] (f : B →ₐ[k] B')
    (q : k) (n : ℕ) (x : B) : f (qDivPow q n x) = qDivPow q n (f x) := by
  simp [qDivPow, map_smul, map_pow]

namespace Modified

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

variable (R v) in
/-- The relations `Σ_μ U (K_μ - v^{⟨μ,λ⟩})` (a left ideal of `U`). -/
def rightRel (l : Y →+ ℤ) : Submodule k (QuantumGroup R v) :=
  Submodule.span k {x | ∃ μ w, x = w * (K R v μ - algebraMap k _ (v ^ l μ))}

omit [NeZero v] in
lemma mul_mem_rightRel {l : Y →+ ℤ} (a : QuantumGroup R v) {x : QuantumGroup R v}
    (hx : x ∈ rightRel R v l) : a * x ∈ rightRel R v l := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, w, rfl⟩ := hx
    exact Submodule.subset_span ⟨μ, a * w, by rw [mul_assoc]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

variable (R v) in
/-- `rightRel` as a left ideal. -/
def rightRelU (l : Y →+ ℤ) : Submodule (QuantumGroup R v) (QuantumGroup R v) where
  carrier := rightRel R v l
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a _ hx := mul_mem_rightRel a hx

lemma rightRel_le (l₁ l₂ : Y →+ ℤ) :
    rightRel R v l₂ ≤ modRel R v l₁ l₂ ⊔ otherWeights R v (l₁ - l₂) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨μ, w, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1
    (show w ∈ adWeightSpace R v (l₁ - l₂) ⊔ otherWeights R v (l₁ - l₂) by
      rw [sup_otherWeights]; trivial)
  rw [add_mul]
  exact add_mem (Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨μ, a, ha, rfl⟩)))
    (Submodule.mem_sup_right (mul_mem_otherWeights_right hb (sub_mem_adWeightSpace_zero μ _)))

include hv in
/-- If `u, u' ∈ U_{λ'-λ''}` agree modulo `Σ_μ U (K_μ - v^{⟨μ,λ''⟩})`, then
`π_{λ',λ''}(u) = π_{λ',λ''}(u')`. -/
lemma elt_eq_of_sub_mem_rightRel {l₁ l₂ : Y →+ ℤ} {u u' : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v (l₁ - l₂)) (hu' : u' ∈ adWeightSpace R v (l₁ - l₂))
    (h : u - u' ∈ rightRel R v l₂) : elt l₁ l₂ u hu = elt l₁ l₂ u' hu' := by
  have hm : u - u' ∈ modRel R v l₁ l₂ := by
    have h1 : u - u' ∈ adWeightSpace R v (l₁ - l₂) ⊓
        (modRel R v l₁ l₂ ⊔ otherWeights R v (l₁ - l₂)) := ⟨sub_mem hu hu', rightRel_le l₁ l₂ h⟩
    rwa [inf_comm, sup_inf_assoc_of_le _ (modRel_le l₁ l₂), inf_comm, inf_otherWeights hv,
      sup_bot_eq] at h1
  rw [elt_congr (sub_add_cancel u u').symm hu (add_mem (sub_mem hu hu') hu'),
    elt_add _ _ (sub_mem hu hu') hu', elt_eq_zero _ hm, zero_add]

omit [NeZero v] in
lemma elt_sum {l₁ l₂ : Y →+ ℤ} {ι : Type*} (s : Finset ι) (f : ι → QuantumGroup R v)
    (hf : ∀ t, f t ∈ adWeightSpace R v (l₁ - l₂)) :
    elt l₁ l₂ (∑ t ∈ s, f t) (Submodule.sum_mem _ fun t _ ↦ hf t) =
      ∑ t ∈ s, elt l₁ l₂ (f t) (hf t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using elt_eq_zero (l₁ := l₁) (l₂ := l₂) (zero_mem _) (zero_mem _)
  | insert a s ha ih =>
    rw [elt_congr (sum_insert ha) _ (add_mem (hf a) (Submodule.sum_mem _ fun t _ ↦ hf t)),
      sum_insert ha, elt_add _ _ (hf a) (Submodule.sum_mem _ fun t _ ↦ hf t), ih]

omit [NeZero v] in
variable (R) in
/-- The left `U`-module `U / Σ_μ U (K_μ - v^{⟨μ,λ⟩})` and its generator of weight `λ`. -/
lemma mk_one_mem_weightSpace (l : Y →+ ℤ) :
    (Submodule.Quotient.mk 1 : QuantumGroup R v ⧸ rightRelU R v l) ∈
      weightSpace R v (QuantumGroup R v ⧸ rightRelU R v l) l := fun μ ↦ by
  have h : K R v μ - algebraMap k _ (v ^ l μ) ∈ rightRelU R v l :=
    Submodule.subset_span ⟨μ, 1, (one_mul _).symm⟩
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, ← sub_eq_zero,
    ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero,
    Algebra.smul_def, mul_one]
  exact h

include hv in
/-- [Lus] 3.1.9 modulo `Σ_μ U (K_μ - v^{⟨μ,λ⟩})`. -/
lemma qDivPow_E_mul_qDivPow_F_sub_mem (i : I) (N M' : ℕ) (l : Y →+ ℤ) :
    qDivPow (v ^ D.d i) N (E R v i) * qDivPow (v ^ D.d i) M' (F R v i) -
      ∑ t ∈ range (N + 1), (if t ≤ M' then qBinomZ (v ^ D.d i) (l (R.coroot i) + N - M') t •
        (qDivPow (v ^ D.d i) (M' - t) (F R v i) * qDivPow (v ^ D.d i) (N - t) (E R v i))
        else 0) ∈ rightRel R v l := by
  have h := qDivPow_E_smul_qDivPow_F_smul hv (mk_one_mem_weightSpace R l) i N M'
  have e : ∀ a : QuantumGroup R v,
      a • (Submodule.Quotient.mk 1 : QuantumGroup R v ⧸ rightRelU R v l) =
        Submodule.Quotient.mk a := fun a ↦ by
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  have e' : ∀ t, efTerm R v i (l (R.coroot i)) N M' t
      (Submodule.Quotient.mk 1 : QuantumGroup R v ⧸ rightRelU R v l) =
      Submodule.Quotient.mk (if t ≤ M' then qBinomZ (v ^ D.d i) (l (R.coroot i) + N - M') t •
        (qDivPow (v ^ D.d i) (M' - t) (F R v i) * qDivPow (v ^ D.d i) (N - t) (E R v i))
        else 0) := fun t ↦ by
    rw [efTerm]
    split_ifs
    · rw [← mul_smul, e, ← Submodule.Quotient.mk_smul]
    · rfl
  rw [← mul_smul, e, sum_congr rfl fun t _ ↦ e' t] at h
  simp only [← Submodule.mkQ_apply] at h
  rw [← map_sum, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  exact h

omit [NeZero v] in
lemma chevalley_mem_rightRel {l : Y →+ ℤ} {x : QuantumGroup R v} (hx : x ∈ rightRel R v l) :
    chevalley R v x ∈ rightRel R v (-l) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, w, rfl⟩ := hx
    refine Submodule.subset_span ⟨-μ, chevalley R v w, ?_⟩
    rw [_root_.map_mul, _root_.map_sub, chevalley_K, AlgHom.commutes, AddMonoidHom.neg_apply,
      map_neg, neg_neg]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

include hv in
/-- [Lus] 3.1.9 for `F^{(N)} E^{(M)}` modulo `Σ_μ U (K_μ - v^{⟨μ,λ⟩})`. -/
lemma qDivPow_F_mul_qDivPow_E_sub_mem (i : I) (N M' : ℕ) (l : Y →+ ℤ) :
    qDivPow (v ^ D.d i) N (F R v i) * qDivPow (v ^ D.d i) M' (E R v i) -
      ∑ t ∈ range (N + 1), (if t ≤ M' then qBinomZ (v ^ D.d i) (-l (R.coroot i) + N - M') t •
        (qDivPow (v ^ D.d i) (M' - t) (E R v i) * qDivPow (v ^ D.d i) (N - t) (F R v i))
        else 0) ∈ rightRel R v l := by
  have h := chevalley_mem_rightRel (qDivPow_E_mul_qDivPow_F_sub_mem (R := R) hv i N M' (-l))
  rw [neg_neg] at h
  convert h using 1
  simp only [_root_.map_sub, _root_.map_mul, map_qDivPow', chevalley_E, chevalley_F, map_sum,
    AddMonoidHom.neg_apply]
  congr 1
  refine sum_congr rfl fun t _ ↦ ?_
  split_ifs <;> simp [map_qDivPow']

/-! ### Divided powers in `U̇` -/

variable (R v) in
/-- `Eᵢ^{(n)} 1_λ`. -/
def dE (i : I) (n : ℕ) (l : Y →+ ℤ) : Modified R v :=
  elt (l + n • R.root i) l (qDivPow (v ^ D.d i) n (E R v i)) (by
    rw [add_sub_cancel_left, qDivPow]
    exact Submodule.smul_mem _ _ (pow_mem_adWeightSpace' (E_mem_adWeightSpace i) n))

variable (R v) in
/-- `Fᵢ^{(n)} 1_λ`. -/
def dF (i : I) (n : ℕ) (l : Y →+ ℤ) : Modified R v :=
  elt (l + n • -R.root i) l (qDivPow (v ^ D.d i) n (F R v i)) (by
    rw [add_sub_cancel_left, qDivPow]
    exact Submodule.smul_mem _ _ (pow_mem_adWeightSpace' (fun μ ↦ K_mul_F R v μ i) n))

lemma divPowE_mem (i : I) (n : ℕ) :
    qDivPow (v ^ D.d i) n (E R v i) ∈ adWeightSpace R v (n • R.root i) := by
  rw [qDivPow]
  exact Submodule.smul_mem _ _ (pow_mem_adWeightSpace' (E_mem_adWeightSpace i) n)

lemma divPowF_mem (i : I) (n : ℕ) :
    qDivPow (v ^ D.d i) n (F R v i) ∈ adWeightSpace R v (n • -R.root i) := by
  rw [qDivPow]
  exact Submodule.smul_mem _ _ (pow_mem_adWeightSpace' (fun μ ↦ K_mul_F R v μ i) n)

include hv in
lemma elt_eq_sum_of_sub_mem {L l : Y →+ ℤ} {u : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v (L - l)) (n : ℕ) (f : ℕ → QuantumGroup R v)
    (hf : ∀ t, f t ∈ adWeightSpace R v (L - l)) (h : u - ∑ t ∈ range n, f t ∈ rightRel R v l) :
    elt L l u hu = ∑ t ∈ range n, elt L l (f t) (hf t) := by
  rw [elt_eq_of_sub_mem_rightRel hv hu (Submodule.sum_mem _ fun t _ ↦ hf t) h, elt_sum]

/-- The character identity `(M - t)(-α) + (N - t)α = M(-α) + Nα` for `t ≤ M, N`. -/
lemma nsmul_neg_add_nsmul (α : Y →+ ℤ) {N M' t : ℕ} (h1 : t ≤ N) (h2 : t ≤ M') :
    (M' - t) • -α + (N - t) • α = M' • -α + N • α := by
  ext μ
  simp only [AddMonoidHom.add_apply, AddMonoidHom.smul_apply, AddMonoidHom.neg_apply,
    nsmul_eq_mul, Nat.cast_sub h1, Nat.cast_sub h2]
  ring

include hv in
/-- **[Lus] 23.1.3**: `Eᵢ^{(N)} Fᵢ^{(M)} 1_λ = Σ_t [⟨i,λ⟩ + N - M; t]ᵢ Fᵢ^{(M-t)} Eᵢ^{(N-t)} 1_λ`
(the sum over `t ≤ min(N, M)`). -/
theorem dE_mul_dF (i : I) (N M' : ℕ) (l : Y →+ ℤ) :
    dE R v i N (l + M' • -R.root i) * dF R v i M' l =
      ∑ t ∈ range (N + 1), if t ≤ M' then
        qBinomZ (v ^ D.d i) (l (R.coroot i) + N - M') t •
          (dF R v i (M' - t) (l + (N - t) • R.root i) * dE R v i (N - t) l) else 0 := by
  set L := l + M' • -R.root i + N • R.root i
  have hLl : L - l = M' • -R.root i + N • R.root i := by simp only [L]; abel
  let f : ℕ → QuantumGroup R v := fun t ↦ if t ≤ M' ∧ t ≤ N then
    qBinomZ (v ^ D.d i) (l (R.coroot i) + N - M') t •
      (qDivPow (v ^ D.d i) (M' - t) (F R v i) * qDivPow (v ^ D.d i) (N - t) (E R v i)) else 0
  have hFE : ∀ t, t ≤ M' → t ≤ N → qDivPow (v ^ D.d i) (M' - t) (F R v i) *
      qDivPow (v ^ D.d i) (N - t) (E R v i) ∈ adWeightSpace R v (L - l) := fun t h1 h2 ↦ by
    rw [hLl, ← nsmul_neg_add_nsmul (R.root i) h2 h1]
    exact mul_mem_adWeightSpace (divPowF_mem i _) (divPowE_mem i _)
  have hf : ∀ t, f t ∈ adWeightSpace R v (L - l) := fun t ↦ by
    simp only [f]
    split_ifs with h
    · exact Submodule.smul_mem _ _ (hFE t h.1 h.2)
    · exact zero_mem _
  have hEF : qDivPow (v ^ D.d i) N (E R v i) * qDivPow (v ^ D.d i) M' (F R v i) ∈
      adWeightSpace R v (L - l) := by
    rw [hLl, add_comm]
    exact mul_mem_adWeightSpace (divPowE_mem i _) (divPowF_mem i _)
  have hsum : ∑ t ∈ range (N + 1), f t = ∑ t ∈ range (N + 1), (if t ≤ M' then
      qBinomZ (v ^ D.d i) (l (R.coroot i) + N - M') t •
        (qDivPow (v ^ D.d i) (M' - t) (F R v i) * qDivPow (v ^ D.d i) (N - t) (E R v i))
      else 0) := sum_congr rfl fun t ht ↦ by
    have : t ≤ N := Nat.lt_succ_iff.1 (mem_range.1 ht)
    simp only [f, this, and_true]
  have h := qDivPow_E_mul_qDivPow_F_sub_mem (R := R) hv i N M' l
  rw [← hsum] at h
  have e : dE R v i N (l + M' • -R.root i) * dF R v i M' l = elt L l _ hEF := by
    rw [dE, dF, elt_mul_elt]
  rw [e, elt_eq_sum_of_sub_mem hv hEF (N + 1) f hf h]
  refine sum_congr rfl fun t ht ↦ ?_
  have htN : t ≤ N := Nat.lt_succ_iff.1 (mem_range.1 ht)
  by_cases htM : t ≤ M'
  · simp only [f, htM, htN, and_self, ↓reduceIte]
    rw [elt_smul _ _ _ (hFE t htM htN), dF, dE, elt_mul_elt]
    congr 1
    refine elt_index ?_ rfl rfl _ _
    simp only [L]
    rw [add_assoc, ← nsmul_neg_add_nsmul (R.root i) htN htM]
    abel
  · simp only [f, htM, false_and, ↓reduceIte]
    exact elt_eq_zero _ (zero_mem _)

include hv in
/-- **[Lus] 23.1.3**: `Fᵢ^{(N)} Eᵢ^{(M)} 1_λ = Σ_t [-⟨i,λ⟩ + N - M; t]ᵢ Eᵢ^{(M-t)} Fᵢ^{(N-t)} 1_λ`
(the sum over `t ≤ min(N, M)`). -/
theorem dF_mul_dE (i : I) (N M' : ℕ) (l : Y →+ ℤ) :
    dF R v i N (l + M' • R.root i) * dE R v i M' l =
      ∑ t ∈ range (N + 1), if t ≤ M' then
        qBinomZ (v ^ D.d i) (-l (R.coroot i) + N - M') t •
          (dE R v i (M' - t) (l + (N - t) • -R.root i) * dF R v i (N - t) l) else 0 := by
  set L := l + M' • R.root i + N • -R.root i
  have hLl : L - l = M' • R.root i + N • -R.root i := by simp only [L]; abel
  let f : ℕ → QuantumGroup R v := fun t ↦ if t ≤ M' ∧ t ≤ N then
    qBinomZ (v ^ D.d i) (-l (R.coroot i) + N - M') t •
      (qDivPow (v ^ D.d i) (M' - t) (E R v i) * qDivPow (v ^ D.d i) (N - t) (F R v i)) else 0
  have hEF : ∀ t, t ≤ M' → t ≤ N → qDivPow (v ^ D.d i) (M' - t) (E R v i) *
      qDivPow (v ^ D.d i) (N - t) (F R v i) ∈ adWeightSpace R v (L - l) := fun t h1 h2 ↦ by
    have e := nsmul_neg_add_nsmul (-R.root i) h2 h1
    rw [neg_neg] at e
    rw [hLl, ← e]
    exact mul_mem_adWeightSpace (divPowE_mem i _) (divPowF_mem i _)
  have hf : ∀ t, f t ∈ adWeightSpace R v (L - l) := fun t ↦ by
    simp only [f]
    split_ifs with h
    · exact Submodule.smul_mem _ _ (hEF t h.1 h.2)
    · exact zero_mem _
  have hFE : qDivPow (v ^ D.d i) N (F R v i) * qDivPow (v ^ D.d i) M' (E R v i) ∈
      adWeightSpace R v (L - l) := by
    rw [hLl, add_comm]
    exact mul_mem_adWeightSpace (divPowF_mem i _) (divPowE_mem i _)
  have hsum : ∑ t ∈ range (N + 1), f t = ∑ t ∈ range (N + 1), (if t ≤ M' then
      qBinomZ (v ^ D.d i) (-l (R.coroot i) + N - M') t •
        (qDivPow (v ^ D.d i) (M' - t) (E R v i) * qDivPow (v ^ D.d i) (N - t) (F R v i))
      else 0) := sum_congr rfl fun t ht ↦ by
    have : t ≤ N := Nat.lt_succ_iff.1 (mem_range.1 ht)
    simp only [f, this, and_true]
  have h := qDivPow_F_mul_qDivPow_E_sub_mem (R := R) hv i N M' l
  rw [← hsum] at h
  have e : dF R v i N (l + M' • R.root i) * dE R v i M' l = elt L l _ hFE := by
    rw [dE, dF, elt_mul_elt]
  rw [e, elt_eq_sum_of_sub_mem hv hFE (N + 1) f hf h]
  refine sum_congr rfl fun t ht ↦ ?_
  have htN : t ≤ N := Nat.lt_succ_iff.1 (mem_range.1 ht)
  by_cases htM : t ≤ M'
  · simp only [f, htM, htN, and_self, ↓reduceIte]
    rw [elt_smul _ _ _ (hEF t htM htN), dF, dE, elt_mul_elt]
    congr 1
    refine elt_index ?_ rfl rfl _ _
    have e := nsmul_neg_add_nsmul (R.root i) htM htN
    simp only [L]
    rw [add_assoc, add_comm (M' • R.root i), ← e]
    abel
  · simp only [f, htM, false_and, ↓reduceIte]
    exact elt_eq_zero _ (zero_mem _)

/-- `Eᵢ^{(a)} Fⱼ^{(b)} 1_λ = Fⱼ^{(b)} Eᵢ^{(a)} 1_λ` for `i ≠ j` ([Lus] 23.1.3). -/
theorem dE_mul_dF_of_ne {i j : I} (hij : i ≠ j) (a b : ℕ) (l : Y →+ ℤ) :
    dE R v i a (l + b • -R.root j) * dF R v j b l =
      dF R v j b (l + a • R.root i) * dE R v i a l := by
  rw [dE, dF, dF, dE, elt_mul_elt, elt_mul_elt]
  refine elt_index (by abel) rfl ?_ _ _
  simp only [qDivPow, smul_mul_smul_comm]
  rw [((Commute.pow_pow (E_mul_F_of_ne (R := R) (v := v) hij) a b)).eq, mul_comm (_ : k)]

end Modified

end LieLean.QuantumGroup
