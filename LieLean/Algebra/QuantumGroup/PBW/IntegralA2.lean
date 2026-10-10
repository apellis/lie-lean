/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.Commutation

/-!
# Integral straightening in type `A₂`

Let `α, β` satisfy the quantum Serre relations of type `A₂` (with parameter `q`) and set
`γ = αβ - q⁻¹βα` (this is `T''_{i,1}(E_j)` for `α = Eᵢ`, `β = Eⱼ`). Then `αγ = qγα`,
`qβγ = γβ` ([Lus] 42.1.2 (a)), and for the divided powers `x^{(n)} = xⁿ/[n]!`
`β^{(Q)} α^{(P)} = Σ_{n ≤ min(P,Q)} (-1)ⁿ q^{(P-n)(Q-n)+n} α^{(P-n)} γ^{(n)} β^{(Q-n)}`
(`A2Integral.dp_mul_dp_eq_sum`). This is the analogue, for the order `α γ β`, of
[Lus] 42.1.2 (b) (which treats the order `β γ α`); it follows from 42.1.2 (b) by the bar
involution and the anti-automorphism `σ`. We prove it directly by induction (our argument).

Hence the `ℤ[q, q⁻¹]`-combinations of the ordered monomials `α^{(a)} γ^{(b)} β^{(c)}` are stable
under left multiplication by all `α^{(n)}`, `β^{(n)}` (`A2Integral.dp_mul_mem_span`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 42.1.2.
-/

open Finset

noncomputable section

namespace LieLean.QuantumGroup

namespace A2Integral

variable {k B : Type*} [Field k] [Ring B] [Algebra k B] {q : k}

/-- `x^{(n)} x = [n+1] x^{(n+1)}`. -/
lemma qDivPow_mul_self (x : B) (n : ℕ) (hn : qInt q (n + 1) ≠ 0) :
    qDivPow q n x * x = qInt q (n + 1) • qDivPow q (n + 1) x := by
  rw [← mul_qDivPow q x n hn]
  simp only [qDivPow, smul_mul_assoc, mul_smul_comm, ← pow_succ, ← pow_succ']

lemma qDivPow_one' (x : B) : qDivPow q 1 x = x := by simp [qDivPow, qFactorial, qInt]

lemma qFactorial_ne_zero_of_qInt (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0) (n : ℕ) :
    qFactorial q n ≠ 0 := by
  induction n with
  | zero => simp [qFactorial]
  | succ n ih => rw [qFactorial_succ]; exact mul_ne_zero (hqi _ n.succ_pos) ih

/-- `x^{(n)} x^{(m)} = [n+m; n] x^{(n+m)}`. -/
lemma qDivPow_mul_qDivPow (x : B) (n m : ℕ) (h : qFactorial q (n + m) ≠ 0) :
    qDivPow q n x * qDivPow q m x = qBinomial q (n + m) n • qDivPow q (n + m) x := by
  have e := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (Nat.le_add_right n m)
  rw [Nat.add_sub_cancel_left] at e
  have hn : qFactorial q n ≠ 0 := fun h0 ↦ h (by rw [← e, h0]; ring)
  have hm : qFactorial q m ≠ 0 := fun h0 ↦ h (by rw [← e, h0]; ring)
  have hB : qBinomial q (n + m) n ≠ 0 := fun h0 ↦ h (by rw [← e, h0]; ring)
  simp only [qDivPow, smul_mul_smul_comm, ← pow_add, smul_smul]
  congr 1
  rw [← e]
  field_simp

variable (hq0 : q ≠ 0) (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0) {α β γ : B}
  (hβα : β * α = q • (α * β) - q • γ) (hαγ : α * γ = q • (γ * α))
  (hβγ : q • (β * γ) = γ * β)

include hq0 hqi hβα hαγ in
/-- `β α^{(P+1)} = q^{P+1} α^{(P+1)} β - q α^{(P)} γ`. -/
lemma mul_qDivPow_succ (P : ℕ) :
    β * qDivPow q (P + 1) α =
      q ^ (P + 1) • (qDivPow q (P + 1) α * β) - q • (qDivPow q P α * γ) := by
  induction P with
  | zero =>
    rw [qDivPow_one', qDivPow_zero', one_mul, zero_add, pow_one, hβα]
  | succ P ih =>
    have hc := hqi (P + 2) (by omega)
    refine smul_right_injective B hc ?_
    simp only
    have hq : q * qInt q (P + 2) = qInt q (P + 1) + q ^ (P + 2) := by
      have h := qInt_succ (v := q) (P + 1)
      rw [show P + 1 + 1 = P + 2 from rfl] at h
      rw [h, mul_add, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul, ← pow_succ']
    have e2 : qDivPow q P α * α = qInt q (P + 1) • qDivPow q (P + 1) α :=
      qDivPow_mul_self α P (hqi _ (by omega))
    have e3 : qDivPow q (P + 1) α * α = qInt q (P + 2) • qDivPow q (P + 2) α :=
      qDivPow_mul_self α (P + 1) hc
    set X := qDivPow q (P + 2) α * β
    set Y := qDivPow q (P + 1) α * γ
    calc qInt q (P + 2) • (β * qDivPow q (P + 1 + 1) α)
        = β * qDivPow q (P + 1) α * α := by
          rw [mul_assoc, e3, mul_smul_comm]
      _ = (q ^ (P + 1) • (qDivPow q (P + 1) α * β) - q • (qDivPow q P α * γ)) * α := by
          rw [ih]
      _ = q ^ (P + 1) • (qDivPow q (P + 1) α * (β * α)) -
            qDivPow q P α * (q • (γ * α)) := by
          simp only [sub_mul, smul_mul_assoc, mul_assoc, mul_smul_comm]
      _ = q ^ (P + 1) • (qDivPow q (P + 1) α * (q • (α * β) - q • γ)) -
            qDivPow q P α * (α * γ) := by
          rw [hβα, ← hαγ]
      _ = (q ^ (P + 1) * q) • (qDivPow q (P + 1) α * α * β) -
            (q ^ (P + 1) * q) • Y - qDivPow q P α * α * γ := by
          simp only [mul_sub, mul_smul_comm, smul_sub, smul_smul, mul_assoc, Y]
      _ = (q ^ (P + 1) * q * qInt q (P + 2)) • X - (q ^ (P + 1) * q) • Y -
            qInt q (P + 1) • Y := by
          rw [e3, e2, smul_mul_assoc, smul_mul_assoc, smul_smul]
      _ = qInt q (P + 2) • (q ^ (P + 1 + 1) • X - q • Y) := by
          linear_combination (norm := module) hq • Y

/-- The scalar identity `[b+1] + q^{b+s+2} [s+1] = q^{s+1} [s+b+2]`. -/
lemma qInt_identity (hq0 : q ≠ 0) (hq : q - q⁻¹ ≠ 0) (s b : ℕ) :
    qInt q (b + 1) + q ^ (b + s + 2) * qInt q (s + 1) = q ^ (s + 1) * qInt q (s + b + 2) := by
  rw [← qIntZ_natCast hq, ← qIntZ_natCast hq, ← qIntZ_natCast hq]
  simp only [qIntZ, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, zpow_add₀ hq0, zpow_neg,
    zpow_natCast, zpow_ofNat]
  field_simp
  ring

variable (q α β γ) in
/-- The summand of the straightening formula. -/
def sTerm (P Q n : ℕ) : B :=
  if n ≤ P then ((-1 : k) ^ n * q ^ ((P - n) * (Q - n) + n)) •
    (qDivPow q (P - n) α * qDivPow q n γ * qDivPow q (Q - n) β) else 0

include hq0 hqi hβα hαγ hβγ in
/-- **Integral straightening in type `A₂`**:
`β^{(Q)} α^{(P)} = Σ_{n ≤ min(P,Q)} (-1)ⁿ q^{(P-n)(Q-n)+n} α^{(P-n)} γ^{(n)} β^{(Q-n)}`
(cf. [Lus] 42.1.2 (b); our argument). -/
theorem qDivPow_mul_qDivPow_eq_sum (hqq : q - q⁻¹ ≠ 0) (P Q : ℕ) :
    qDivPow q Q β * qDivPow q P α = ∑ n ∈ range (Q + 1), sTerm q α β γ P Q n := by
  have hβγ' : β * γ = q⁻¹ • (γ * β) := by
    rw [hβγ.symm, smul_smul, inv_mul_cancel₀ hq0, one_smul]
  have hβdγ : ∀ n, β * qDivPow q n γ = q⁻¹ ^ n • (qDivPow q n γ * β) := fun n ↦ by
    rw [qDivPow, mul_smul_comm, mul_pow_of_mul_eq_smul hβγ' n, smul_mul_assoc, smul_comm]
  induction Q with
  | zero => simp [sTerm, qDivPow_zero']
  | succ Q ih =>
    have hc := hqi (Q + 1) (by omega)
    refine smul_right_injective B hc ?_
    simp only
    let coef : ℕ → k := fun n ↦ (-1 : k) ^ n * q ^ ((P - n) * (Q - n) + n)
    let M : ℕ → B := fun n ↦
      qDivPow q (P - n) α * qDivPow q n γ * qDivPow q (Q + 1 - n) β
    let g1 : ℕ → B := fun n ↦ if n ≤ P then
      (coef n * q ^ (P - n) * q⁻¹ ^ n * qInt q (Q + 1 - n)) • M n else 0
    let g2 : ℕ → B := fun n ↦ if n + 1 ≤ P then
      (-(coef n * q * qInt q (n + 1))) • M (n + 1) else 0
    have hL : qInt q (Q + 1) • (qDivPow q (Q + 1) β * qDivPow q P α) =
        ∑ n ∈ range (Q + 1), β * sTerm q α β γ P Q n := by
      rw [← smul_mul_assoc, ← mul_qDivPow q β Q hc, mul_assoc, ih, mul_sum]
    have hT : ∀ n ∈ range (Q + 1), β * sTerm q α β γ P Q n = g1 n + g2 n := by
      intro n hn
      have hnQ : n ≤ Q := Nat.lt_succ_iff.1 (mem_range.1 hn)
      have hββ : β * qDivPow q (Q - n) β = qInt q (Q + 1 - n) • qDivPow q (Q + 1 - n) β := by
        rw [mul_qDivPow q β _ (hqi _ (by omega)), show Q - n + 1 = Q + 1 - n by omega]
      simp only [sTerm, g1, g2]
      by_cases hP : n ≤ P
      · simp only [hP, ↓reduceIte]
        rw [mul_smul_comm, ← mul_assoc, ← mul_assoc]
        by_cases hP' : n + 1 ≤ P
        · simp only [hP', ↓reduceIte]
          obtain ⟨m, hm⟩ : ∃ m, P - n = m + 1 := ⟨P - n - 1, by omega⟩
          rw [hm, mul_qDivPow_succ hq0 hqi hβα hαγ m]
          simp only [sub_mul, smul_mul_assoc, mul_assoc]
          rw [← mul_assoc β (qDivPow q n γ), hβdγ, smul_mul_assoc, mul_assoc (qDivPow q n γ) β,
            hββ, ← mul_assoc γ (qDivPow q n γ), mul_qDivPow q γ n (hqi _ (by omega)),
            smul_mul_assoc]
          simp only [M, coef, hm, show P - (n + 1) = m by omega,
            show Q + 1 - (n + 1) = Q - n by omega, mul_smul_comm, smul_smul, mul_assoc]
          module
        · simp only [hP', ↓reduceIte, add_zero]
          have hPn : P - n = 0 := by omega
          rw [hPn, qDivPow_zero', mul_one, hβdγ, smul_mul_assoc, mul_assoc, hββ]
          simp only [M, coef, hPn, qDivPow_zero', one_mul, mul_smul_comm, smul_smul, mul_assoc]
          module
      · have hP' : ¬ n + 1 ≤ P := by omega
        simp only [hP, hP', ↓reduceIte, mul_zero, add_zero]
    rw [hL, sum_congr rfl hT, sum_add_distrib, smul_sum]
    have hs1 : ∑ n ∈ range (Q + 1), g1 n = ∑ n ∈ range (Q + 2), g1 n := by
      rw [sum_range_succ _ (Q + 1)]
      simp only [g1, Nat.sub_self, qInt, range_zero, sum_empty, mul_zero, zero_smul, ite_self,
        add_zero]
    have hs2 : ∑ n ∈ range (Q + 1), g2 n =
        ∑ n ∈ range (Q + 2), (if n = 0 then 0 else g2 (n - 1)) := by
      rw [sum_range_succ' _ (Q + 1)]
      simp
    rw [hs1, hs2, ← sum_add_distrib]
    refine sum_congr rfl fun t ht ↦ ?_
    have htQ : t ≤ Q + 1 := Nat.lt_succ_iff.1 (mem_range.1 ht)
    rcases t with _ | s
    · simp only [g1, sTerm, zero_le, ↓reduceIte, Nat.sub_zero, pow_zero, mul_one, one_mul,
        add_zero, smul_smul, M, coef]
      congr 1
      ring
    · simp only [g1, g2, sTerm, Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte]
      by_cases hsP : s + 1 ≤ P
      · simp only [hsP, ↓reduceIte, smul_smul, M, ← add_smul]
        congr 1
        obtain ⟨a, rfl⟩ : ∃ a, P = s + 1 + a := ⟨P - (s + 1), by omega⟩
        have e1 : s + 1 + a - (s + 1) = a := by omega
        have e2 : s + 1 + a - s = a + 1 := by omega
        have hsQ : s ≤ Q := by omega
        obtain ⟨b, rfl⟩ : ∃ b, Q = s + b := ⟨Q - s, by omega⟩
        simp only [coef, e1, e2, show s + b + 1 - (s + 1) = b by omega,
          show s + b - (s + 1) = b - 1 by omega, show s + b - s = b by omega]
        rcases b with _ | b
        · simp [qInt]
          ring
        · have hid := qInt_identity hq0 hqq s b
          simp only [Nat.add_sub_cancel, show s + (b + 1) + 1 = s + b + 2 by omega]
          have hqi' : q⁻¹ ^ (s + 1) * q ^ (s + 1) = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hq0, one_pow]
          linear_combination ((-1 : k) ^ (s + 1) * q ^ (a * b + a)) * hid +
            ((-1 : k) ^ (s + 1) * q ^ (a * b + a) * qInt q (b + 1)) * hqi'
      · simp only [hsP, ↓reduceIte, add_zero, smul_zero]

/-! ### Lusztig's form of the straightening ([Lus] 42.1.2 (b)) -/

section Lusztig

omit [Algebra k B] in
lemma qInt_inv' (n : ℕ) : qInt q⁻¹ n = qInt q n := by
  rw [qInt, qInt, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [Finset.mem_range] at hs
  rw [inv_inv, mul_comm]
  congr 2
  omega

omit [Algebra k B] in
lemma qFactorial_inv' (n : ℕ) : qFactorial q⁻¹ n = qFactorial q n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [qFactorial, qFactorial, ih, qInt_inv']

/-- Divided powers do not change under `q ↦ q⁻¹`. -/
lemma qDivPow_inv' (n : ℕ) (x : B) : qDivPow q⁻¹ n x = qDivPow q n x := by
  rw [qDivPow, qDivPow, qFactorial_inv']

/-- **[Lus] 42.1.2 (b), as printed**: if `α, β` satisfy `αγ = qγα` and `qβγ = γβ` for
`γ = αβ - q⁻¹βα` ([Lus] 42.1.2 (a), consequences of the `A₂` Serre relations), then
`α^{(p)} β^{(r)} = Σ_n q^{-(p-n)(r-n)} β^{(r-n)} γ^{(n)} α^{(p-n)}`. It follows from
`qDivPow_mul_qDivPow_eq_sum` at the parameter `q⁻¹`, for the pair `β, α` and `-qγ`. -/
theorem qDivPow_mul_qDivPow_eq_sum_lusztig (hq0 : q ≠ 0) (hqi : ∀ n : ℕ, 0 < n → qInt q n ≠ 0)
    (hqq : q - q⁻¹ ≠ 0) {α β γ : B} (hγ : γ = α * β - q⁻¹ • (β * α))
    (hαγ : α * γ = q • (γ * α)) (hβγ : q • (β * γ) = γ * β) (p r : ℕ) :
    qDivPow q p α * qDivPow q r β = ∑ n ∈ range (p + 1),
      if n ≤ r then q⁻¹ ^ ((p - n) * (r - n)) •
        (qDivPow q (r - n) β * qDivPow q n γ * qDivPow q (p - n) α) else 0 := by
  have hq0' : q⁻¹ ≠ 0 := inv_ne_zero hq0
  have hqi' : ∀ n : ℕ, 0 < n → qInt q⁻¹ n ≠ 0 := fun n hn ↦ by rw [qInt_inv']; exact hqi n hn
  have hqq' : q⁻¹ - q⁻¹⁻¹ ≠ 0 := by rw [inv_inv, ← neg_sub]; exact neg_ne_zero.2 hqq
  have h1 : α * β = q⁻¹ • (β * α) - q⁻¹ • ((-q) • γ) := by
    rw [hγ, smul_smul, mul_neg, inv_mul_cancel₀ hq0, neg_smul, one_smul]; abel
  have h2 : β * ((-q) • γ) = q⁻¹ • (((-q) • γ) * β) := by
    rw [mul_smul_comm, smul_mul_assoc, ← hβγ, smul_smul, smul_smul,
      show q⁻¹ * -q * q = -q by field_simp]
  have h3 : q⁻¹ • (α * ((-q) • γ)) = ((-q) • γ) * α := by
    rw [mul_smul_comm, smul_smul, mul_neg, inv_mul_cancel₀ hq0, neg_smul, one_smul, hαγ,
      smul_mul_assoc, neg_smul]
  have L := qDivPow_mul_qDivPow_eq_sum hq0' hqi' h1 h2 h3 hqq' r p
  rw [qDivPow_inv', qDivPow_inv'] at L
  rw [L]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp only [sTerm]
  split_ifs with hn
  · rw [qDivPow_inv', qDivPow_inv', qDivPow_inv',
      show qDivPow q n ((-q) • γ) = (qFactorial q n)⁻¹ • ((-q) • γ) ^ n from rfl, smul_pow,
      smul_smul, show qDivPow q n γ = (qFactorial q n)⁻¹ • γ ^ n from rfl]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
    congr 1
    have e1 : (-1 : k) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
    have e2 : q⁻¹ ^ n * q ^ n = 1 := by rw [← mul_pow, inv_mul_cancel₀ hq0, one_pow]
    calc (-1) ^ n * q⁻¹ ^ ((r - n) * (p - n) + n) * ((qFactorial q n)⁻¹ * (-q) ^ n)
        = ((-1) ^ n * (-1) ^ n) * (q⁻¹ ^ n * q ^ n) * (q⁻¹ ^ ((p - n) * (r - n)) *
            (qFactorial q n)⁻¹) := by
          rw [neg_pow, pow_add, mul_comm (r - n) (p - n)]; ring
      _ = _ := by rw [e1, e2, one_mul, one_mul]
  · rfl

end Lusztig

/-! ### Ordered spans -/

section Span

/-- The `L`-combinations of the ordered monomials `x^{(a)} z^{(b)} y^{(d)}` (for `x = α`,
`y = β`, `z = γ`). -/
def orderedSpan (L : Subring k) (t : k) (x y z : B) : AddSubgroup B :=
  AddSubgroup.closure {w | ∃ c ∈ L, ∃ a b d : ℕ,
    w = c • (qDivPow t a x * qDivPow t b z * qDivPow t d y)}

variable {Λ : Subring k} (hqΛ : q ∈ Λ) (hqΛ' : q⁻¹ ∈ Λ)

include hqΛ hqΛ' in
lemma qBinomial_mem (n j : ℕ) : qBinomial q n j ∈ Λ := by
  induction n generalizing j with
  | zero => cases j <;> simp [one_mem, zero_mem]
  | succ n ih =>
    cases j with
    | zero => simp [one_mem]
    | succ j =>
      rw [qBinomial_succ_succ]
      exact add_mem (mul_mem (pow_mem hqΛ' _) (ih _)) (mul_mem (pow_mem hqΛ _) (ih _))

lemma smul_mem_orderedSpan {c : k} (hc : c ∈ Λ) {x : B} (hx : x ∈ orderedSpan Λ q α β γ) :
    c • x ∈ orderedSpan Λ q α β γ := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c', hc', a, b, d, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨c * c', mul_mem hc hc', a, b, d, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

lemma monomial_mem_orderedSpan (a b d : ℕ) :
    qDivPow q a α * qDivPow q b γ * qDivPow q d β ∈ orderedSpan Λ q α β γ :=
  AddSubgroup.subset_closure ⟨1, one_mem _, a, b, d, (one_smul _ _).symm⟩

lemma one_mem_orderedSpan : (1 : B) ∈ orderedSpan Λ q α β γ := by
  simpa [qDivPow_zero'] using monomial_mem_orderedSpan (Λ := Λ) (q := q) (α := α) (β := β)
    (γ := γ) 0 0 0

lemma mul_mem_orderedSpan_of_gen {y : B}
    (hy : ∀ a b d : ℕ, y * (qDivPow q a α * qDivPow q b γ * qDivPow q d β) ∈
      orderedSpan Λ q α β γ) {x : B} (hx : x ∈ orderedSpan Λ q α β γ) :
    y * x ∈ orderedSpan Λ q α β γ := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, a, b, d, rfl⟩ := hx
    rw [mul_smul_comm]; exact smul_mem_orderedSpan hc (hy a b d)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

include hqΛ hqΛ' hqi in
lemma qDivPow_α_mul_mem (P : ℕ) {x : B} (hx : x ∈ orderedSpan Λ q α β γ) :
    qDivPow q P α * x ∈ orderedSpan Λ q α β γ := by
  refine mul_mem_orderedSpan_of_gen (fun a b d ↦ ?_) hx
  rw [← mul_assoc, ← mul_assoc, qDivPow_mul_qDivPow α P a
    (qFactorial_ne_zero_of_qInt hqi _), smul_mul_assoc, smul_mul_assoc]
  exact smul_mem_orderedSpan (qBinomial_mem hqΛ hqΛ' _ _) (monomial_mem_orderedSpan _ _ _)

include hqΛ hqΛ' hq0 hqi hβα hαγ hβγ in
lemma qDivPow_β_mul_mem (hqq : q - q⁻¹ ≠ 0) (Q : ℕ) {x : B}
    (hx : x ∈ orderedSpan Λ q α β γ) :
    qDivPow q Q β * x ∈ orderedSpan Λ q α β γ := by
  have hβγ' : β * γ = q⁻¹ • (γ * β) := by
    rw [hβγ.symm, smul_smul, inv_mul_cancel₀ hq0, one_smul]
  have hcomm : ∀ m b : ℕ, qDivPow q m β * qDivPow q b γ =
      q⁻¹ ^ (m * b) • (qDivPow q b γ * qDivPow q m β) := fun m b ↦ by
    simp only [qDivPow, smul_mul_smul_comm, pow_mul_pow_of_mul_eq_smul hβγ' m b, smul_smul,
      mul_comm]
  have hF : ∀ n, qFactorial q n ≠ 0 := qFactorial_ne_zero_of_qInt hqi
  refine mul_mem_orderedSpan_of_gen (fun a b d ↦ ?_) hx
  rw [← mul_assoc, ← mul_assoc, qDivPow_mul_qDivPow_eq_sum hq0 hqi hβα hαγ hβγ hqq, sum_mul,
    sum_mul]
  refine AddSubgroup.sum_mem _ fun n _ ↦ ?_
  simp only [sTerm]
  split_ifs
  · set m := Q - n
    have key : qDivPow q m β * qDivPow q b γ * qDivPow q d β =
        (q⁻¹ ^ (m * b) * qBinomial q (m + d) m) • (qDivPow q b γ * qDivPow q (m + d) β) := by
      rw [hcomm, smul_mul_assoc, mul_assoc, qDivPow_mul_qDivPow β m d (hF _), mul_smul_comm,
        smul_smul]
    have key2 : qDivPow q n γ * qDivPow q b γ = qBinomial q (n + b) n • qDivPow q (n + b) γ :=
      qDivPow_mul_qDivPow γ n b (hF _)
    have e : ((-1 : k) ^ n * q ^ ((a - n) * m + n)) •
        (qDivPow q (a - n) α * qDivPow q n γ * qDivPow q m β) * qDivPow q b γ * qDivPow q d β =
        ((-1 : k) ^ n * q ^ ((a - n) * m + n) * (q⁻¹ ^ (m * b) * qBinomial q (m + d) m) *
          qBinomial q (n + b) n) •
          (qDivPow q (a - n) α * qDivPow q (n + b) γ * qDivPow q (m + d) β) := by
      have : qDivPow q (a - n) α * qDivPow q n γ * qDivPow q m β * qDivPow q b γ *
          qDivPow q d β = qDivPow q (a - n) α * qDivPow q n γ *
            (qDivPow q m β * qDivPow q b γ * qDivPow q d β) := by noncomm_ring
      rw [smul_mul_assoc, smul_mul_assoc, this, key, mul_smul_comm, ← mul_assoc,
        mul_assoc (qDivPow q (a - n) α), key2, mul_smul_comm, smul_mul_assoc, smul_smul,
        smul_smul, ← mul_assoc]
    rw [e]
    refine smul_mem_orderedSpan ?_ (monomial_mem_orderedSpan _ _ _)
    refine mul_mem (mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) (pow_mem hqΛ _))
      (mul_mem (pow_mem hqΛ' _) (qBinomial_mem hqΛ hqΛ' _ _))) (qBinomial_mem hqΛ hqΛ' _ _)
  · simp only [zero_mul]; exact zero_mem _

end Span

end A2Integral

end LieLean.QuantumGroup
