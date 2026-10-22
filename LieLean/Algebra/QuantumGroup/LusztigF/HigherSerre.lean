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
([Lus] 7.1.6). Consequently ([Lus] Cor. 7.1.7, `toQuotient_fDivPow_mul_fDivPow`), for `m > an`,
`θᵢ^{(m)} θⱼ^{(n)} = Σ_{r+s=m, s ≥ m-an} γ_s θᵢ^{(r)} θⱼ^{(n)} θᵢ^{(s)}` in `f`, with
`γ_s = Σ_{q=0}^{m-an-1} (-1)^{s+1+q} vᵢ^{-s(an-m+1+q)+q} [s; q]ᵢ` (`higherSerreCoeff`); the proof
is Lusztig's, from 7.1.5 and [Lus] 1.3.4.

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

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.2.15, 1.3.4, 7.1.1–7.1.7.
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

/-! ### [Lus] Corollary 7.1.7 -/

omit [DecidableEq I] in
variable (D) in
lemma qFactorial_X_ne_zero (i : I) (M : ℕ) : qFactorial ((𝕧 : 𝕂) ^ D.d i) M ≠ 0 :=
  qFactorial_ne_zero_of_not_root RatFunc.X_ne_zero (fun _ hn ↦ ratFunc_X_pow_ne_one hn) i M

omit [DecidableEq I] in
variable (D) in
/-- `θᵢ^{(r)} θᵢ^{(s)} = [r + s; r]ᵢ θᵢ^{(r+s)}`. -/
lemma fDivPow_mul_fDivPow (i : I) (r s : ℕ) :
    fDivPow D i r * fDivPow D i s = qBinomial (𝕧 ^ D.d i) (r + s) r • fDivPow D i (r + s) := by
  have e := qBinomial_mul_qFactorial_mul_qFactorial (v := (𝕧 : 𝕂) ^ D.d i)
    (Nat.le_add_right r s)
  rw [Nat.add_sub_cancel_left] at e
  have hr := qFactorial_X_ne_zero D i r
  have hs := qFactorial_X_ne_zero D i s
  have hB : qBinomial ((𝕧 : 𝕂) ^ D.d i) (r + s) r ≠ 0 := fun h0 ↦
    qFactorial_X_ne_zero D i (r + s) (by rw [← e, h0]; ring)
  simp only [fDivPow, qDivPow, smul_mul_smul_comm, ← pow_add, smul_smul]
  congr 1
  rw [← e]
  field_simp

variable (D) in
/-- The coefficient `γ_s = Σ_{q=0}^{m-an-1} (-1)^{s+1+q} vᵢ^{-s(an-m+1+q)+q} [s; q]ᵢ` of
[Lus] Cor. 7.1.7. -/
def higherSerreCoeff (i : I) (a n m s : ℕ) : 𝕂 :=
  ∑ q ∈ range (m - a * n), (-1) ^ (s + 1 + q) *
    𝕧 ^ ((D.d i : ℤ) * (-(s : ℤ) * ((a : ℤ) * n - m + 1 + q) + q)) * qBinomial (𝕧 ^ D.d i) s q

/-- [Lus] Cor. 7.1.7: for `i ≠ j`, `a = -⟨i, j'⟩` and `m > an`,
`θᵢ^{(m)} θⱼ^{(n)} = Σ_{r+s=m, m-an ≤ s ≤ m} γ_s θᵢ^{(r)} θⱼ^{(n)} θᵢ^{(s)}` in `f`, with
`γ_s = higherSerreCoeff D i a n m s`. The sum is written over `r ≤ an`, `s = m - r`. -/
theorem toQuotient_fDivPow_mul_fDivPow {i j : I} (hij : i ≠ j) {a n m : ℕ}
    (ha : D.cartanMatrix i j = -a) (hm : a * n < m) :
    toQuotient D 𝕧 (fDivPow D i m * fDivPow D j n) =
      ∑ r ∈ range (a * n + 1), higherSerreCoeff D i a n m (m - r) •
        toQuotient D 𝕧 (fDivPow D i r * fDivPow D j n * fDivPow D i (m - r)) := by
  have hX : (𝕧 : 𝕂) ≠ 0 := RatFunc.X_ne_zero
  have hdot : D.dot i j = -((D.d i : ℤ) * a) := by rw [← D.d_mul_cartanMatrix, ha]; ring
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → Quotient D 𝕧,
      ∀ r, Y r = toQuotient D 𝕧 (fDivPow D i r * fDivPow D j n * fDivPow D i (m - r)) :=
    ⟨_, fun _ ↦ rfl⟩
  -- the coefficients of `f_{n,m-q;1}`
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → 𝕂, ∀ q r, c q r = (-1) ^ r *
      𝕧 ^ ((1 : ℤ) * (r : ℤ) * (-(D.dot i j) * n - D.d i * (((m - q : ℕ) : ℤ) - 1))) :=
    ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ → 𝕂, ∀ q, w q = (-1) ^ q * 𝕧 ^ ((D.d i : ℤ) * (-((m : ℤ) * q) + q)) :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ → 𝕂, ∀ r,
      C r = ∑ q ∈ range (m - a * n), w q * c q r * qBinomial (𝕧 ^ D.d i) (m - r) q :=
    ⟨_, fun _ ↦ rfl⟩
  -- `f_{n,m-q;1} θᵢ^{(q)}` in terms of the `Y r`
  have h2 : ∀ q ≤ m, toQuotient D 𝕧 (higherSerre D i j n (m - q) 1 * fDivPow D i q) =
      ∑ r ∈ range (m + 1), (c q r * qBinomial (𝕧 ^ D.d i) (m - r) q) • Y r := by
    intro q hq
    rw [higherSerre, sum_mul, map_sum, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      ← sum_subset (range_mono (by omega : m - q + 1 ≤ m + 1))
        (f := fun r ↦ (c q r * qBinomial (𝕧 ^ D.d i) (m - r) q) • Y r) ?_]
    · refine sum_congr rfl fun r hr ↦ ?_
      rw [mem_range] at hr
      dsimp only
      rw [smul_mul_assoc, mul_assoc (fDivPow D i r * fDivPow D j n), fDivPow_mul_fDivPow,
        mul_smul_comm, smul_smul, map_smul,
        show m - q - r + q = m - r by omega, show m - q - r = m - r - q by omega,
        qBinomial_symm _ (by omega : q ≤ m - r), hY, hc]
    · intro r hr' hr
      rw [mem_range, not_lt] at hr
      rw [mem_range] at hr'
      rw [qBinomial_eq_zero_of_lt _ (by omega : m - r < q), mul_zero, zero_smul]
  -- `g = Σ_q w_q f_{n,m-q;1} θᵢ^{(q)} = 0`
  have h3 : ∑ r ∈ range (m + 1), C r • Y r = 0 := by
    have : ∑ q ∈ range (m - a * n),
        w q • toQuotient D 𝕧 (higherSerre D i j n (m - q) 1 * fDivPow D i q) = 0 := by
      refine sum_eq_zero fun q hq ↦ ?_
      rw [mem_range] at hq
      have hq' : a * n < m - q := by omega
      rw [map_mul, toQuotient_higherSerre hij n (m - q) (Or.inl rfl)
        (by rw [ha, neg_neg]; exact_mod_cast hq'), zero_mul, smul_zero]
    calc ∑ r ∈ range (m + 1), C r • Y r
        = ∑ q ∈ range (m - a * n),
            w q • ∑ r ∈ range (m + 1), (c q r * qBinomial (𝕧 ^ D.d i) (m - r) q) • Y r := by
          simp only [hC, smul_sum, smul_smul, sum_smul]
          rw [sum_comm]
          refine sum_congr rfl fun r _ ↦ sum_congr rfl fun q _ ↦ ?_
          rw [mul_assoc]
      _ = _ := sum_congr rfl fun q hq ↦ by rw [h2 q (by rw [mem_range] at hq; omega)]
      _ = 0 := this
  -- the middle coefficients vanish ([Lus] 1.3.4)
  have hCzero : ∀ r, a * n < r → r < m → C r = 0 := by
    intro r hr1 hr2
    obtain ⟨t, ht⟩ : ∃ t, m - r = t + 1 := ⟨m - r - 1, by omega⟩
    have hmz : (m : ℤ) = r + t + 1 := by omega
    have h134 := sum_qBinomial_mul_inv_pow_eq_zero (v := (𝕧 : 𝕂) ^ D.d i)
      (pow_ne_zero _ hX) t
    rw [hC, ht, ← sum_subset (range_mono (by omega : t + 2 ≤ m - a * n))
      (f := fun q ↦ w q * c q r * qBinomial (𝕧 ^ D.d i) (t + 1) q) ?_]
    · rw [← mul_zero ((-1 : 𝕂) ^ r * 𝕧 ^ ((D.d i : ℤ) * (r * ((a : ℤ) * n - m + 1)))),
        ← h134, mul_sum]
      refine sum_congr rfl fun q hq ↦ ?_
      rw [mem_range] at hq
      have hqm : q ≤ m := by omega
      have hpow : (((𝕧 : 𝕂) ^ D.d i)⁻¹ ^ t) ^ q = 𝕧 ^ (-((D.d i : ℤ) * t * q)) := by
        rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, ← zpow_natCast, ← zpow_neg]
        push_cast; ring_nf
      have hexp : (𝕧 : 𝕂) ^ ((D.d i : ℤ) * (-((m : ℤ) * q) + q)) *
          𝕧 ^ ((1 : ℤ) * (r : ℤ) * (-(D.dot i j) * n - D.d i * (((m - q : ℕ) : ℤ) - 1))) =
          𝕧 ^ ((D.d i : ℤ) * (r * ((a : ℤ) * n - m + 1))) * 𝕧 ^ (-((D.d i : ℤ) * t * q)) := by
        rw [← zpow_add₀ hX, ← zpow_add₀ hX, hdot, Nat.cast_sub hqm]
        congr 1
        linear_combination (-(D.d i : ℤ) * q) * hmz
      rw [hw, hc, hpow]
      linear_combination ((-1 : 𝕂) ^ q * (-1) ^ r * qBinomial (𝕧 ^ D.d i) (t + 1) q) * hexp
    · intro q _ hq
      rw [mem_range, not_lt] at hq
      rw [qBinomial_eq_zero_of_lt _ (by omega : t + 1 < q), mul_zero]
  -- the top coefficient
  have hCm : C m = c 0 m := by
    rw [hC, sum_eq_single 0 (fun q _ hq ↦ by
        rw [Nat.sub_self, qBinomial_eq_zero_of_lt _ (by omega : 0 < q), mul_zero])
      (fun h ↦ absurd (mem_range.2 (by omega : 0 < m - a * n)) h),
      Nat.sub_self, qBinomial_zero_right, mul_one, hw]
    simp
  have hCm0 : C m ≠ 0 := by
    rw [hCm, hc]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (zpow_ne_zero _ hX)
  have hγ : ∀ r ≤ m, C m * higherSerreCoeff D i a n m (m - r) = -C r := by
    intro r hr
    obtain ⟨s, hs⟩ : ∃ s, m = r + s := ⟨m - r, by omega⟩
    have hmz : (m : ℤ) = r + s := by omega
    have hss : ((-1 : 𝕂) ^ s) * (-1) ^ s = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [hCm, higherSerreCoeff, hC, mul_sum, ← sum_neg_distrib, show m - r = s by omega]
    refine sum_congr rfl fun q hq ↦ ?_
    rw [mem_range] at hq
    have hqm : q ≤ m := by omega
    have hexp : (𝕧 : 𝕂) ^ ((1 : ℤ) * ((m : ℕ) : ℤ) *
          (-(D.dot i j) * n - D.d i * (((m - 0 : ℕ) : ℤ) - 1))) *
        𝕧 ^ ((D.d i : ℤ) * (-(s : ℤ) * ((a : ℤ) * n - m + 1 + q) + q)) =
        𝕧 ^ ((D.d i : ℤ) * (-((m : ℤ) * q) + q)) *
          𝕧 ^ ((1 : ℤ) * (r : ℤ) * (-(D.dot i j) * n - D.d i * (((m - q : ℕ) : ℤ) - 1))) := by
      rw [← zpow_add₀ hX, ← zpow_add₀ hX, hdot, Nat.cast_sub hqm, Nat.sub_zero]
      congr 1
      linear_combination ((D.d i : ℤ) * ((a : ℤ) * n + q + 1 - m)) * hmz
    rw [hc, hc, hw, hs, pow_add, pow_add, pow_add, pow_one, ← hs]
    linear_combination
      (-(-1 : 𝕂) ^ r * (-1) ^ q * qBinomial (𝕧 ^ D.d i) s q *
        𝕧 ^ ((1 : ℤ) * ((m : ℕ) : ℤ) * (-(D.dot i j) * n - D.d i * (((m - 0 : ℕ) : ℤ) - 1))) *
        𝕧 ^ ((D.d i : ℤ) * (-(s : ℤ) * ((a : ℤ) * n - m + 1 + q) + q))) * hss +
      (-(-1 : 𝕂) ^ r * (-1) ^ q * qBinomial (𝕧 ^ D.d i) s q) * hexp
  -- conclusion
  have hsplit : ∑ r ∈ range (m + 1), C r • Y r =
      ∑ r ∈ range (a * n + 1), C r • Y r + C m • Y m := by
    rw [sum_range_succ, ← sum_range_add_sum_Ico _ (by omega : a * n + 1 ≤ m),
      sum_eq_zero (s := Ico _ _) fun r hr ↦ by
        rw [mem_Ico] at hr; rw [hCzero r (by omega) hr.2, zero_smul], add_zero]
  have hYm : toQuotient D 𝕧 (fDivPow D i m * fDivPow D j n) = Y m := by
    rw [hY, Nat.sub_self, fDivPow_zero D, mul_one]
  rw [hYm]
  apply smul_right_injective _ hCm0
  dsimp only
  rw [smul_sum, sum_congr rfl fun r hr ↦ by
    rw [smul_smul, hγ r (by rw [mem_range] at hr; omega), neg_smul]]
  rw [sum_neg_distrib, eq_neg_iff_add_eq_zero, add_comm]
  simp only [← hY]
  rw [← hsplit, h3]

end LieLean.QuantumGroup
