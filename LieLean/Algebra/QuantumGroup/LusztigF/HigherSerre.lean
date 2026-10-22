/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.LusztigF.IntegralPairing
import LieLean.Algebra.QuantumGroup.LusztigF.Reverse

/-!
# Higher order quantum Serre relations

Over `𝕂 = ℚ(v)`, for `i ≠ j` in `I`, `e = ±1` and `n, m ∈ ℕ`, let
`f_{i,j;n,m;e} = Σ_{r+s=m} (-1)^r vᵢ^{er(an-m+1)} θᵢ^{(r)} θⱼ^{(n)} θᵢ^{(s)}`, where
`a = -⟨i, j'⟩ = -aᵢⱼ` ([Lus] 7.1.1; `higherSerre`). We prove [Lus] Prop. 7.1.5 (b): if
`m > an`, then `f_{i,j;n,m;e} = 0` in `f`, i.e. it lies in the radical of Lusztig's form
(`higherSerre_mem_radical`). For `n = 1`, `m = a + 1` these are the quantum Serre relations
([Lus] 7.1.6).

## Proof

Lusztig works in `U`, with the commutators of `f⁺_{n,m;e}` with `Eᵢ`, `Fᵢ`, `Fⱼ` (7.1.2, 7.1.4)
and the fact that an element of `U⁺` commuting with all `Fₕ` is a scalar (3.2.7 (a)). We use
the equivalent statements in `'f`, with the skew derivations `rₕ` in place of the commutators
with `Fₕ`: for `e = -1`,
* `rᵢ(f_{n,m+1}) = (vᵢ^m - vᵢ^{3m - 2an}) f_{n,m}` (`rDeriv_higherSerre_self`),
* `rⱼ(f_{n+1,m}) = vⱼ^n vᵢ^{-am} f_{n,m}`, `rⱼ(f_{0,m}) = 0` (`rDeriv_higherSerre_right`),
* `rₕ(f_{n,m}) = 0` for `h ≠ i, j`;
and an element without constant term whose derivations `rₕ` all lie in the radical lies in the
radical ([Lus] 1.2.15; `LusztigF.mem_radical_of_rDeriv_mem`). Induction on `n`, then on `m`,
gives the case `e = -1`, since the scalar in the first formula vanishes for `m = an`. The case
`e = 1` follows by the anti-automorphism `σ` (`LusztigF.rev`), which maps `f_{n,m;1}` to a
nonzero multiple of `f_{n,m;-1}` and preserves the radical. Unlike Lusztig's, this argument
uses only the derivations `rₕ`, not the `ᵢr`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.2.15, 7.1.1–7.1.6.
-/

open LieLean Finset
open scoped RatFunc

noncomputable section

namespace LieLean.QuantumGroup

open LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)

variable {I : Type*} [DecidableEq I] (D : LusztigCartanDatum I)

omit [DecidableEq I] in
lemma X_pow_pow (a b : ℕ) : ((𝕧 : 𝕂) ^ a) ^ b = 𝕧 ^ ((a : ℤ) * b) := by
  rw [← pow_mul, ← zpow_natCast]; push_cast; rfl

omit [DecidableEq I] in
lemma X_zpow_pow (a : ℤ) (b : ℕ) : ((𝕧 : 𝕂) ^ a) ^ b = 𝕧 ^ (a * b) := by
  rw [← zpow_natCast, ← zpow_mul]

omit [DecidableEq I] in
lemma X_pow_eq (a : ℕ) : ((𝕧 : 𝕂) ^ a) = 𝕧 ^ (a : ℤ) := (zpow_natCast _ _).symm

/-- Lusztig's `f_{i,j;n,m;e} = Σ_{r+s=m} (-1)^r vᵢ^{er(an-m+1)} θᵢ^{(r)} θⱼ^{(n)} θᵢ^{(s)}`,
`a = -⟨i, j'⟩` ([Lus] 7.1.1). The exponent is written `er(-(i·j) n - dᵢ (m - 1))`, which is
`dᵢ er(an - m + 1)` since `i·j = dᵢ ⟨i, j'⟩`. -/
def higherSerre (i j : I) (n m : ℕ) (e : ℤ) : LusztigF 𝕂 I :=
  ∑ p ∈ antidiagonal m, ((-1 : 𝕂) ^ p.1 *
      𝕧 ^ (e * p.1 * (-(D.dot i j) * n - D.d i * ((m : ℤ) - 1)))) •
    (fDivPow D i p.1 * fDivPow D j n * fDivPow D i p.2)

/-! ### Divided powers and the derivations -/

omit [DecidableEq I] in
lemma qInt_X_one (i : I) : qInt (𝕧 ^ D.d i) 1 = 1 := by simp [qInt]

omit [DecidableEq I] in
lemma fDivPow_one (i : I) : fDivPow D i 1 = θ 𝕂 i := by
  simp [fDivPow, qDivPow, qFactorial, qInt]

/-- `rᵢ(θᵢ^{(n+1)}) = vᵢ^n θᵢ^{(n)}`. -/
lemma rDeriv_fDivPow_succ (i : I) (n : ℕ) :
    rDeriv D 𝕧 i (fDivPow D i (n + 1)) = (𝕧 ^ D.d i) ^ n • fDivPow D i n := by
  have hq : (𝕧 ^ D.d i : 𝕂) ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  induction n with
  | zero => simp [fDivPow_one, fDivPow_zero]
  | succ n ih =>
    rw [fDivPow_succ D i (n + 1), map_smul, rDeriv_θ_mul, ih]
    simp only [↓reduceIte]
    rw [twist_fDivPow, mul_smul_comm, θ_mul_fDivPow, smul_smul, ← add_smul, smul_smul]
    congr 1
    have h := qInt_X_ne_zero D i (Nat.succ_pos (n + 1))
    have e : (𝕧 ^ D.d i : 𝕂) ^ n * qInt (𝕧 ^ D.d i) (n + 1) + ((𝕧 ^ D.d i) ^ 2) ^ (n + 1) =
        (𝕧 ^ D.d i) ^ (n + 1) * qInt (𝕧 ^ D.d i) (n + 1 + 1) := by
      rw [qInt_succ (n + 1)]; field_simp; ring
    rw [e, mul_comm, mul_assoc, mul_inv_cancel₀ h, mul_one]

lemma rDeriv_fDivPow_zero (h i : I) : rDeriv D 𝕧 h (fDivPow D i 0) = 0 := by
  rw [fDivPow_zero, rDeriv_one]

/-- `rₕ(θᵢ^{(n)}) = 0` for `h ≠ i`. -/
lemma rDeriv_fDivPow_of_ne {h i : I} (hhi : h ≠ i) (n : ℕ) :
    rDeriv D 𝕧 h (fDivPow D i n) = 0 := by
  have : ∀ m : ℕ, rDeriv D 𝕧 h (θ 𝕂 i ^ m) = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', rDeriv_θ_mul, ih, mul_zero, zero_add, ite_eq_right_iff]
      exact fun h ↦ absurd h hhi
  rw [fDivPow, qDivPow, map_smul, this, smul_zero]

omit [DecidableEq I] in
/-- `σₕ(θᵢ^{(n)}) = v^{n (h·i)} θᵢ^{(n)}`. -/
lemma twist_fDivPow' (h i : I) (n : ℕ) :
    twist D 𝕧 h (fDivPow D i n) = (𝕧 ^ D.dot h i) ^ n • fDivPow D i n := by
  simp only [fDivPow, qDivPow, map_smul, map_pow, twist_θ, smul_pow]
  exact smul_comm _ _ _

omit [DecidableEq I] in
lemma counit_fDivPow_succ (i : I) (n : ℕ) : LusztigF.counit (fDivPow D i (n + 1)) = 0 := by
  rw [fDivPow, qDivPow, map_smul, map_pow]
  simp

/-! ### Derivations of `f_{n,m;-1}` -/

variable {D}

/-- `rᵢ(f_{n,m+1;-1}) = (vᵢ^m - vᵢ^{3m} v^{2n(i·j)}) f_{n,m;-1}` ([Lus] 7.1.2 (b), as a
statement on `'f`); for `m = an` the scalar is `0`. -/
theorem rDeriv_higherSerre_self {i j : I} (hij : i ≠ j) (n m : ℕ) :
    rDeriv D 𝕧 i (higherSerre D i j n (m + 1) (-1)) =
      (𝕧 ^ ((D.d i : ℤ) * m) - 𝕧 ^ (2 * D.dot i j * n + 3 * D.d i * m)) •
        higherSerre D i j n m (-1) := by
  have hX : (𝕧 : 𝕂) ≠ 0 := RatFunc.X_ne_zero
  have key : ∀ r s : ℕ, rDeriv D 𝕧 i (fDivPow D i r * fDivPow D j n * fDivPow D i s) =
      fDivPow D i r * fDivPow D j n * rDeriv D 𝕧 i (fDivPow D i s) +
        ((𝕧 ^ D.dot i i) ^ s * (𝕧 ^ D.dot i j) ^ n) •
          (rDeriv D 𝕧 i (fDivPow D i r) * fDivPow D j n * fDivPow D i s) := by
    intro r s
    rw [rDeriv_mul, rDeriv_mul, rDeriv_fDivPow_of_ne D hij, mul_zero, zero_add,
      twist_fDivPow', twist_fDivPow']
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
  rw [higherSerre, map_sum]
  simp only [map_smul, key, smul_add, sum_add_distrib]
  rw [Nat.sum_antidiagonal_succ', Nat.sum_antidiagonal_succ]
  simp only [rDeriv_fDivPow_zero, mul_zero, zero_mul, smul_zero, zero_add,
    rDeriv_fDivPow_succ, mul_smul_comm, smul_mul_assoc, smul_smul]
  rw [higherSerre, smul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [smul_smul, ← add_smul]
  congr 1
  have hs : ((p.2 : ℤ)) = m - p.1 := by omega
  simp only [X_pow_pow, X_zpow_pow, pow_succ, sub_mul, mul_sub,
    show D.dot i i = 2 * D.d i from (D.two_mul_d i).symm]
  simp only [mul_assoc, ← zpow_add₀ hX, neg_mul, mul_neg]
  simp only [one_mul]
  rw [mul_left_comm _ ((-1 : 𝕂) ^ p.1), mul_left_comm _ ((-1 : 𝕂) ^ p.1),
    ← zpow_add₀ hX, ← zpow_add₀ hX, ← sub_eq_add_neg]
  congr 3 <;> (push_cast; rw [hs]; ring)

/-- `rⱼ(f_{n+1,m;-1}) = vⱼ^n v^{m(i·j)} f_{n,m;-1}` ([Lus] 7.1.4, as a statement on `'f`). -/
theorem rDeriv_higherSerre_right {i j : I} (hij : i ≠ j) (n m : ℕ) :
    rDeriv D 𝕧 j (higherSerre D i j (n + 1) m (-1)) =
      ((𝕧 ^ D.d j) ^ n * 𝕧 ^ (D.dot i j * m)) • higherSerre D i j n m (-1) := by
  have hX : (𝕧 : 𝕂) ≠ 0 := RatFunc.X_ne_zero
  rw [higherSerre, higherSerre, map_sum, smul_sum]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [map_smul, rDeriv_mul, rDeriv_mul, rDeriv_fDivPow_of_ne D hij.symm,
    rDeriv_fDivPow_of_ne D hij.symm, rDeriv_fDivPow_succ, twist_fDivPow', twist_fDivPow',
    D.dot_comm j i]
  simp only [mul_zero, zero_mul, zero_add, smul_zero, add_zero, mul_smul_comm, smul_mul_assoc,
    smul_smul]
  congr 1
  have hs : ((p.2 : ℤ)) = m - p.1 := by omega
  simp only [X_pow_pow, X_zpow_pow]
  simp only [mul_assoc, mul_left_comm _ ((-1 : 𝕂) ^ p.1)]
  simp only [← zpow_add₀ hX]
  congr 2
  push_cast; rw [hs]; ring

theorem rDeriv_higherSerre_right_zero {i j : I} (hij : i ≠ j) (m : ℕ) :
    rDeriv D 𝕧 j (higherSerre D i j 0 m (-1)) = 0 := by
  rw [higherSerre, map_sum]
  refine sum_eq_zero fun p _ ↦ ?_
  rw [map_smul, rDeriv_mul, rDeriv_mul, rDeriv_fDivPow_of_ne D hij.symm,
    rDeriv_fDivPow_of_ne D hij.symm, rDeriv_fDivPow_zero]
  simp

/-- `rₕ(f_{n,m;e}) = 0` for `h ≠ i, j`. -/
theorem rDeriv_higherSerre_of_ne {h i j : I} (hi : h ≠ i) (hj : h ≠ j) (n m : ℕ) (e : ℤ) :
    rDeriv D 𝕧 h (higherSerre D i j n m e) = 0 := by
  rw [higherSerre, map_sum]
  refine sum_eq_zero fun p _ ↦ ?_
  rw [map_smul, rDeriv_mul, rDeriv_mul, rDeriv_fDivPow_of_ne D hi, rDeriv_fDivPow_of_ne D hi,
    rDeriv_fDivPow_of_ne D hj]
  simp

omit [DecidableEq I] in
lemma counit_higherSerre (i j : I) (n m : ℕ) (e : ℤ) :
    LusztigF.counit (higherSerre D i j n (m + 1) e) = 0 := by
  rw [higherSerre, map_sum]
  refine sum_eq_zero fun p hp ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [map_smul, map_mul, map_mul]
  rcases p with ⟨_ | r, _ | s⟩
  · simp at hp
  · simp [counit_fDivPow_succ]
  · simp [counit_fDivPow_succ]
  · simp [counit_fDivPow_succ]

lemma smul_mem_radical (c : 𝕂) {x : LusztigF 𝕂 I} (hx : x ∈ radical D 𝕧) :
    c • x ∈ radical D 𝕧 :=
  (mem_radical_iff D 𝕧).2 fun y ↦ by simp [(mem_radical_iff D 𝕧).1 hx y]

/-- The induction on `m` in [Lus] 7.1.5 (b), for fixed `n`, given the statement for `rⱼ`. -/
lemma higherSerre_neg_one_mem_radical_aux {i j : I} (hij : i ≠ j) (n : ℕ)
    (hj : ∀ m : ℕ, -D.cartanMatrix i j * n < m →
      rDeriv D 𝕧 j (higherSerre D i j n m (-1)) ∈ radical D 𝕧) (m : ℕ)
    (h : -D.cartanMatrix i j * n < m) : higherSerre D i j n m (-1) ∈ radical D 𝕧 := by
  have ha : 0 ≤ -D.cartanMatrix i j := by
    have := D.isGeneralizedCartan_cartanMatrix.offDiag_nonpos i j hij; omega
  have hd := D.d_mul_cartanMatrix i j
  induction m with
  | zero => push_cast at h; nlinarith
  | succ m ihm =>
    refine mem_radical_of_rDeriv_mem D 𝕧 (counit_higherSerre _ _ _ _ _) fun k ↦ ?_
    by_cases hki : k = i
    · subst hki
      rw [rDeriv_higherSerre_self hij]
      by_cases hm : -D.cartanMatrix k j * n < (m : ℤ)
      · exact smul_mem_radical _ (ihm hm)
      · have hm' : (m : ℤ) = -D.cartanMatrix k j * n := by push_cast at h ⊢; omega
        rw [show (2 * D.dot k j * n + 3 * D.d k * m : ℤ) = D.d k * m by
          rw [hm', ← hd]; ring, sub_self, zero_smul]
        exact zero_mem _
    by_cases hkj : k = j
    · subst hkj
      exact hj _ h
    · rw [rDeriv_higherSerre_of_ne hki hkj]
      exact zero_mem _

/-- [Lus] Prop. 7.1.5 (b) for `e = -1`: `f_{n,m;-1} = 0` in `f` for `m > an`. -/
theorem higherSerre_neg_one_mem_radical {i j : I} (hij : i ≠ j) (n m : ℕ)
    (h : -D.cartanMatrix i j * n < m) : higherSerre D i j n m (-1) ∈ radical D 𝕧 := by
  have ha : 0 ≤ -D.cartanMatrix i j := by
    have := D.isGeneralizedCartan_cartanMatrix.offDiag_nonpos i j hij; omega
  induction n generalizing m with
  | zero =>
    refine higherSerre_neg_one_mem_radical_aux hij 0 (fun m _ ↦ ?_) m h
    rw [rDeriv_higherSerre_right_zero hij]
    exact zero_mem _
  | succ n ihn =>
    refine higherSerre_neg_one_mem_radical_aux hij (n + 1) (fun m hm ↦ ?_) m h
    rw [rDeriv_higherSerre_right hij]
    exact smul_mem_radical _ (ihn m (by push_cast at hm; nlinarith))

omit [DecidableEq I] in
/-- Word reversal exchanges `f_{n,m;e}` and `f_{n,m;-e}` up to a scalar. -/
lemma rev_higherSerre (i j : I) (n m : ℕ) (e : ℤ) :
    rev 𝕂 I (higherSerre D i j n m e) =
      ((-1 : 𝕂) ^ m * 𝕧 ^ (e * m * (-(D.dot i j) * n - D.d i * ((m : ℤ) - 1)))) •
        higherSerre D i j n m (-e) := by
  have hX : (𝕧 : 𝕂) ≠ 0 := RatFunc.X_ne_zero
  rw [higherSerre, higherSerre, map_sum, smul_sum, ← Finset.Nat.sum_antidiagonal_swap]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  simp only [Prod.fst_swap, Prod.snd_swap, map_smul, rev_mul, fDivPow, rev_qDivPow, smul_smul,
    mul_assoc]
  congr 1
  have hs : (p.2 : ℤ) = m - p.1 := by omega
  have hm : (-1 : 𝕂) ^ p.2 = (-1) ^ m * (-1) ^ p.1 := by
    have h2 : ((-1 : 𝕂) ^ p.1) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [← hp, pow_add]
    linear_combination (-(-1 : 𝕂) ^ p.2) * h2
  rw [hm, mul_assoc]
  congr 1
  rw [mul_left_comm (𝕧 ^ _ : 𝕂) ((-1 : 𝕂) ^ p.1), ← zpow_add₀ hX]
  congr 2
  rw [hs]; ring

lemma rev_mem_radical {x : LusztigF 𝕂 I} (hx : x ∈ radical D 𝕧) : rev 𝕂 I x ∈ radical D 𝕧 :=
  (mem_radical_iff D 𝕧).2 fun y ↦ by
    rw [← rev_rev y, form_rev, (mem_radical_iff D 𝕧).1 hx]

/-- [Lus] Prop. 7.1.5 (b) for `e = 1`: `f_{n,m;1} = 0` in `f` for `m > an`. -/
theorem higherSerre_one_mem_radical {i j : I} (hij : i ≠ j) (n m : ℕ)
    (h : -D.cartanMatrix i j * n < m) : higherSerre D i j n m 1 ∈ radical D 𝕧 := by
  have := rev_mem_radical (smul_mem_radical
    ((-1 : 𝕂) ^ m * 𝕧 ^ ((-1) * m * (-(D.dot i j) * n - D.d i * ((m : ℤ) - 1))))⁻¹
    (higherSerre_neg_one_mem_radical hij n m h))
  have hr := rev_higherSerre (D := D) i j n m (-1)
  rw [neg_neg] at hr
  rwa [map_smul, hr, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero (by simp) (zpow_ne_zero _ RatFunc.X_ne_zero)), one_smul] at this

/-- [Lus] Prop. 7.1.5 (b): for `e = ±1` and `m > an`, `f_{n,m;e}` lies in the radical of the
form, so it is `0` in `f`. -/
theorem higherSerre_mem_radical {i j : I} (hij : i ≠ j) (n m : ℕ) {e : ℤ}
    (he : e = 1 ∨ e = -1) (h : -D.cartanMatrix i j * n < m) :
    higherSerre D i j n m e ∈ radical D 𝕧 := by
  rcases he with rfl | rfl
  · exact higherSerre_one_mem_radical hij n m h
  · exact higherSerre_neg_one_mem_radical hij n m h

/-- [Lus] Prop. 7.1.5 (b) in `f`: `f_{n,m;e} = 0` for `e = ±1` and `m > an`. -/
theorem toQuotient_higherSerre {i j : I} (hij : i ≠ j) (n m : ℕ) {e : ℤ}
    (he : e = 1 ∨ e = -1) (h : -D.cartanMatrix i j * n < m) :
    toQuotient D 𝕧 (higherSerre D i j n m e) = 0 :=
  (toQuotient_eq_zero_iff D 𝕧).2 (higherSerre_mem_radical hij n m he h)

end LieLean.QuantumGroup
