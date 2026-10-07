/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Rank1

/-!
# A formula for `T''` on short strings

Let `M` be an integrable `U_q(𝔰𝔩₂)`-module (`QuantumGroup.IntegrableSl2`) with `q` nonzero and not
a root of unity, and let `T = T''_q` (`QuantumGroup.IntegrableSl2.T`). For `p, r ∈ ℕ` put
`Ψ_{p,r} = Σ_{s ≤ min(r, p)} (-1)^s q^{-s} E^{(r-s)} F^{(p-s)}` (`IntegrableSl2.psi`). We show
`T(w) = (-1)^p q^p Ψ_{p,r}(w)` for every `w ∈ M^{p-r}` in the span of the vectors `F^{(k)} ζ` with
`ζ` primitive and `k ≤ r` (`IntegrableSl2.T_eq_psi_of_mem`). On such a vector both sides are
multiples of `F^{(p+k-r)} ζ`, and the coefficients agree by the identity
`Σ_c (-1)^c q^c [h+c, c] [h, k-c] = (-q^{h+1})^k` of `QuantumGroup.QBinomialSeries`.

This is the rank-one computation behind the compatibility `T(Eⱼ m) = Tᵢ(Eⱼ) T(m)` of Lusztig's
symmetries of `U` and of its integrable modules ([Lus] 37.1.2; [Jan] 8.10, whose proof is
different): for a primitive vector `η ∈ Mᵖ` of an integrable `U`-module, `Tᵢ(Eⱼ) T(η)` equals
`(-1)^p q^p Ψ_{p,r}(Eⱼ η)` with `r = -aᵢⱼ`, and `Eⱼ η` lies in the span above. To control the
lengths of the strings we also show that a vector of `Mⁿ` killed by `E^N` (if `n ≥ 0`), resp. by
`F^N` (if `n ≤ 0`), is a sum of vectors `F^{(k)} ζ` with `k < N`, resp. `k < N - n`
(`IntegrableSl2.mem_stringsLT_of_nonneg`, `IntegrableSl2.mem_stringsLT_of_nonpos`).

The arguments are our own.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §5.2, §37.1.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, §8.10.
-/

open Finset

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  (V : IntegrableSl2 q M)

/-! ### Strings of bounded length -/

/-- The span of the vectors `F^{(j)} η` with `j < N` and `η ∈ M^{n+2j}` primitive. -/
def stringsLT (n : ℤ) (N : ℕ) : Submodule k M :=
  Submodule.span k
    {x | ∃ (j : ℕ) (η : M), j < N ∧ η ∈ V.wt (n + 2 * j) ∧ V.E η = 0 ∧ x = V.dF j η}

lemma stringsLT_mono {n : ℤ} {N N' : ℕ} (h : N ≤ N') : V.stringsLT n N ≤ V.stringsLT n N' :=
  Submodule.span_mono fun _ ⟨j, η, hj, hη, hE, hx⟩ ↦ ⟨j, η, by omega, hη, hE, hx⟩

lemma stringsLT_le_wt (n : ℤ) (N : ℕ) : V.stringsLT n N ≤ V.wt n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, η, -, hη, -, rfl⟩
  have := dF_mem hη j
  rwa [show n + 2 * (j : ℤ) - 2 * j = n by ring] at this

variable {V}

lemma dF_mem_stringsLT {n : ℤ} {N j : ℕ} {η : M} (hj : j < N) (hη : η ∈ V.wt (n + 2 * j))
    (hE : V.E η = 0) : V.dF j η ∈ V.stringsLT n N :=
  Submodule.subset_span ⟨j, η, hj, hη, hE, rfl⟩

variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq0 hq

/-- A vector of `Mⁿ`, `n ≥ 0`, killed by `E^N` is a sum of vectors `F^{(j)} η` with `j < N`. -/
theorem mem_stringsLT_of_nonneg {n : ℤ} (hn : 0 ≤ n) {N : ℕ} {m : M} (hm : m ∈ V.wt n)
    (hN : (V.E ^ N) m = 0) : m ∈ V.stringsLT n N := by
  have hpow : ∀ (N : ℕ) (m : M), (V.E ^ N) m = qFactorial q N • V.dE N m := fun N m ↦ by
    rw [dE_apply, smul_smul, mul_inv_cancel₀ (qFactorial_ne_zero_of_pow_ne_one hq0 hq N),
      one_smul]
  induction N generalizing m with
  | zero => simp only [pow_zero, Module.End.one_apply] at hN; rw [hN]; exact zero_mem _
  | succ N ih =>
    set y := V.dE N m
    have hy : y ∈ V.wt (n + 2 * N) := dE_mem hm N
    have hyE : V.E y = 0 := by
      have h1 : V.dE (N + 1) m = 0 := by
        rw [hpow] at hN
        exact (smul_eq_zero.1 hN).resolve_left (qFactorial_ne_zero_of_pow_ne_one hq0 hq _)
      rw [E_dE hq0 hq, h1, smul_zero]
    obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = n + 2 * N := ⟨(n + 2 * N).toNat, by omega⟩
    have hNp : N ≤ p := by omega
    set c := qBinomial q p N
    have hc : c ≠ 0 := qBinomial_ne_zero_of_pow_ne_one hq0 hq hNp
    set m' := m - c⁻¹ • V.dF N y
    have hy' : y ∈ V.wt (p : ℤ) := hp ▸ hy
    have hm' : m' ∈ V.wt n := by
      refine sub_mem hm (Submodule.smul_mem _ _ ?_)
      have := dF_mem hy N
      rwa [show n + 2 * (N : ℤ) - 2 * N = n by ring] at this
    have hEm' : (V.E ^ N) m' = 0 := by
      rw [hpow, map_sub, map_smul, dE_dF_of_primitive hq0 hq hy' hyE le_rfl hNp, Nat.sub_self,
        show p - N + N = p by omega, smul_smul, inv_mul_cancel₀ hc, one_smul, dF_zero, sub_self,
        smul_zero]
    have h1 := V.stringsLT_mono (Nat.le_succ N) (ih hm' hEm')
    have h2 : V.dF N y ∈ V.stringsLT n (N + 1) := dF_mem_stringsLT (Nat.lt_succ_self N) hy hyE
    have : m = m' + c⁻¹ • V.dF N y := by simp [m']
    rw [this]
    exact add_mem h1 (Submodule.smul_mem _ _ h2)

/-- A vector of `Mⁿ`, `n ≤ 0`, killed by `F^N` is a sum of vectors `F^{(j)} η` with
`j < N - n`. -/
theorem mem_stringsLT_of_nonpos {n : ℤ} (hn : n ≤ 0) {N : ℕ} {m : M} (hm : m ∈ V.wt n)
    (hN : (V.F ^ N) m = 0) : m ∈ V.stringsLT n (N + (-n).toNat) := by
  have h := mem_stringsLT_of_nonneg (V := V.flip) hq0 hq (n := -n) (by omega)
    (by simpa using hm) hN
  refine Submodule.span_le.2 ?_ h
  rintro _ ⟨j, ξ, hj, hξ, hFξ, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ, (P : ℤ) = 2 * j - n := ⟨(2 * j - n).toNat, by omega⟩
  have hjP : j ≤ P := by omega
  have hξ' : ξ ∈ V.flip.wt (P : ℤ) := by
    rw [flip_wt] at hξ ⊢
    convert hξ using 2
    omega
  obtain ⟨hη, hηE⟩ := flip_primitive (V := V.flip) hq0 hq hξ' hFξ
  have e := dF_eq_flip_dF (V := V.flip) hq0 hq hξ' hFξ hjP
  rw [flip_flip] at hη hηE e
  rw [e]
  refine dF_mem_stringsLT (by omega) ?_ hηE
  convert hη using 2
  omega

/-! ### The operator `Ψ_{p,r}` -/

omit hq0 hq in
lemma qBinomial_mul_qBinomial_eq' {a kk u : ℕ} (hka : kk ≤ a) (hu : u ≤ kk)
    (hf : ∀ n, qFactorial q n ≠ 0) :
    qBinomial q a kk * qBinomial q kk u = qBinomial q a u * qBinomial q (a - u) (kk - u) := by
  have h1 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) hka
  have h2 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) hu
  have h3 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (show u ≤ a by omega)
  have h4 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (show kk - u ≤ a - u by omega)
  rw [show a - u - (kk - u) = a - kk by omega] at h4
  have hX : qFactorial q u * qFactorial q (kk - u) * qFactorial q (a - kk) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hf _) (hf _)) (hf _)
  apply mul_right_cancel₀ hX
  linear_combination (qBinomial q a kk * qFactorial q (a - kk)) * h2 + h1 -
    (qBinomial q a u * qFactorial q u) * h4 - h3

/-- `[a, k] [k, u] = [a, u] [a - u, k - u]` for `u ≤ k`. -/
lemma qBinomial_mul_qBinomial_eq {a kk u : ℕ} (hu : u ≤ kk) :
    qBinomial q a kk * qBinomial q kk u = qBinomial q a u * qBinomial q (a - u) (kk - u) := by
  rcases le_or_gt kk a with hka | hka
  · exact qBinomial_mul_qBinomial_eq' hka hu (qFactorial_ne_zero_of_pow_ne_one hq0 hq)
  · rcases le_or_gt u a with hua | hua
    · rw [qBinomial_eq_zero_of_lt q hka,
        qBinomial_eq_zero_of_lt q (show a - u < kk - u by omega), zero_mul, mul_zero]
    · rw [qBinomial_eq_zero_of_lt q hka, qBinomial_eq_zero_of_lt q hua, zero_mul, zero_mul]

omit hq0 hq in
lemma neg_one_pow_sub {r u : ℕ} (h : u ≤ r) : (-1 : k) ^ (r - u) = (-1) ^ r * (-1) ^ u := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add, mul_comm ((-1 : k) ^ u), mul_assoc, ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]

omit hq in
lemma inv_pow_sub {r u : ℕ} (h : u ≤ r) : q⁻¹ ^ (r - u) = q⁻¹ ^ r * q ^ u := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have := pow_ne_zero u hq0
  simp only [Nat.add_sub_cancel_left, pow_add, inv_pow]
  field_simp

/-- The coefficient identity behind `T_eq_psi_of_mem`. -/
lemma psi_coeff {p r kk : ℕ} (hk : kk ≤ r) (hh : r ≤ p + kk) :
    (-1) ^ p * q ^ p * ∑ s ∈ range (r + 1), (if s ≤ p then (-1) ^ s * q⁻¹ ^ s else 0) *
      (qBinomial q (p - s + kk) (p - s) * qBinomial q kk (r - s)) =
      (-1) ^ (p + kk - r) * q ^ ((p + kk - r) * (kk + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨h, rfl⟩ : ∃ h, p = h + d := ⟨p - d, by omega⟩
  rw [show h + d + kk - (kk + d) = h by omega]
  -- reverse the summation: `s = r - u`
  rw [← sum_range_reflect]
  simp only [Nat.add_sub_cancel]
  -- only `u ≤ kk` contributes
  rw [← sum_subset (range_subset_range.2 (show kk + 1 ≤ kk + d + 1 by omega))]
  swap
  · intro u hu hu'
    simp only [mem_range, not_lt] at hu hu'
    rw [show kk + d - (kk + d - u) = u by omega, qBinomial_eq_zero_of_lt q (by omega : kk < u),
      mul_zero, mul_zero]
  have hterm : ∀ u ∈ range (kk + 1), (if kk + d - u ≤ h + d then
      (-1) ^ (kk + d - u) * q⁻¹ ^ (kk + d - u) else 0) *
      (qBinomial q (h + d - (kk + d - u) + kk) (h + d - (kk + d - u)) *
        qBinomial q kk (kk + d - (kk + d - u))) =
      (-1) ^ (kk + d) * q⁻¹ ^ (kk + d) *
        ((-1) ^ u * q ^ u * qBinomial q (h + u) u * qBinomial q h (kk - u)) := by
    intro u hu
    simp only [mem_range] at hu
    rw [show kk + d - (kk + d - u) = u by omega]
    split_ifs with hs
    · rw [show h + d - (kk + d - u) + kk = h + u by omega,
        show h + d - (kk + d - u) = h + u - kk by omega,
        qBinomial_symm q (show kk ≤ h + u by omega),
        qBinomial_mul_qBinomial_eq hq0 hq (show u ≤ kk by omega), Nat.add_sub_cancel,
        neg_one_pow_sub (show u ≤ kk + d by omega), inv_pow_sub hq0 (show u ≤ kk + d by omega)]
      ring
    · rw [qBinomial_eq_zero_of_lt q (show h < kk - u by omega)]
      ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_qBinomial_mul_qBinomial_zero hq0 h kk]
  rw [inv_pow, neg_pow (q ^ (h + 1)), ← pow_mul]
  have hqd : q ^ (kk + d) ≠ 0 := pow_ne_zero _ hq0
  field_simp
  have e1 : ((-1 : k) ^ d) ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  have e2 : ((-1 : k) ^ kk) ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  rw [pow_add (-1 : k) h d, pow_add (-1 : k) kk d]
  linear_combination ((-1 : k) ^ h * q ^ (h + d) * q ^ ((h + 1) * kk) * ((-1) ^ kk) ^ 2) * e1 +
    ((-1 : k) ^ h * q ^ (h + d) * q ^ ((h + 1) * kk)) * e2

variable (V) in
/-- `Ψ_{p,r} = Σ_{s ≤ min(r, p)} (-1)^s q^{-s} E^{(r-s)} F^{(p-s)}`. -/
noncomputable def psi (p r : ℕ) : Module.End k M :=
  ∑ s ∈ range (r + 1), (if s ≤ p then (-1) ^ s * q⁻¹ ^ s else 0) • (V.dE (r - s) * V.dF (p - s))

omit hq0 hq in
lemma psi_apply (p r : ℕ) (w : M) : V.psi p r w = ∑ s ∈ range (r + 1),
    (if s ≤ p then (-1) ^ s * q⁻¹ ^ s else 0) • V.dE (r - s) (V.dF (p - s) w) := by
  rw [psi, LinearMap.sum_apply]
  rfl

/-- `T''_q(w) = (-1)^p q^p Ψ_{p,r}(w)` for `w ∈ M^{p-r}` in the span of the vectors `F^{(k)} ζ`,
`ζ` primitive, `k ≤ r`. -/
theorem T_eq_psi_of_mem {p r : ℕ} {w : M} (hw : w ∈ V.stringsLT ((p : ℤ) - r) (r + 1)) :
    V.T q w = ((-1) ^ p * q ^ p) • V.psi p r w := by
  induction hw using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, map_smul, hx, smul_comm]
  | mem x hx =>
    obtain ⟨kk, ζ, hkk, hζ, hE, rfl⟩ := hx
    rcases lt_or_ge ((p : ℤ) - r + 2 * kk) 0 with hneg | hnn
    · rw [eq_zero_of_primitive_of_neg hq0 hq hζ hE hneg]
      simp
    obtain ⟨P, hP⟩ : ∃ P : ℕ, (P : ℤ) = p - r + 2 * kk := ⟨_, Int.toNat_of_nonneg hnn⟩
    rw [← hP] at hζ
    by_cases hkP : kk ≤ P
    swap
    · rw [dF_eq_zero_of_primitive hq0 hq hζ hE (by omega)]
      simp
    have hh : r ≤ p + kk := by omega
    rw [T_dF_of_primitive hq0 hq hq0 (fun _ _ ↦ rfl) hζ hE hkP, psi_apply]
    have hterm : ∀ s ∈ range (r + 1), (if s ≤ p then (-1) ^ s * q⁻¹ ^ s else 0) •
        V.dE (r - s) (V.dF (p - s) (V.dF kk ζ)) =
        ((if s ≤ p then (-1) ^ s * q⁻¹ ^ s else 0) *
          (qBinomial q (p - s + kk) (p - s) * qBinomial q kk (r - s))) • V.dF (P - kk) ζ := by
      intro s hs
      simp only [mem_range] at hs
      split_ifs with hsp
      swap
      · simp
      rw [dF_dF hq0 hq, map_smul]
      rcases le_or_gt (r - s) kk with hrs | hrs
      · rw [dE_dF_of_primitive hq0 hq hζ hE (show r - s ≤ p - s + kk by omega)
          (show p - s + kk ≤ P by omega), show P - (p - s + kk) + (r - s) = kk by omega,
          show p - s + kk - (r - s) = P - kk by omega, smul_smul, smul_smul, mul_assoc]
      · rw [dF_eq_zero_of_primitive hq0 hq hζ hE (show (P : ℤ) < (p - s + kk : ℕ) by omega),
          map_zero, smul_zero, smul_zero, qBinomial_eq_zero_of_lt q hrs, mul_zero, mul_zero,
          zero_smul]
    rw [sum_congr rfl hterm, ← sum_smul, smul_smul, psi_coeff hq0 hq (by omega) hh,
      show p + kk - r = P - kk by omega]

/-- On a lowest weight vector `ξ ∈ M^{-p}` (`F ξ = 0`), `T''_t(ξ) = E^{(p)} ξ`. -/
theorem T_of_lowest {t : k} (ht0 : t ≠ 0) (ht : ∀ n j, qBinomial t n j = qBinomial q n j)
    {p : ℕ} {ξ : M} (hξ : ξ ∈ V.wt (-p)) (hF : V.F ξ = 0) : V.T t ξ = V.dE p ξ := by
  have hξ' : ξ ∈ V.flip.wt p := by rwa [flip_wt]
  have h := T_dF_of_primitive (V := V.flip) hq0 hq ht0 ht hξ' hF (Nat.zero_le p)
  rw [flip_dF, dE_zero, Nat.sub_zero, zero_add, mul_one] at h
  rw [T_eq_zpow_smul_flip_T hq0 hq ht0 ht hξ, h, smul_smul, flip_dF]
  have hne : (-t) ^ p ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 ht0)
  rw [zpow_neg, zpow_natCast, ← neg_pow t, inv_mul_cancel₀ hne, one_smul]

/-- The flipped version of `T_eq_psi_of_mem`: `T''_q(w) = (-1)^r q^r Ψ'_{p,r}(w)` for `w` in the
span of the vectors `E^{(k)} ξ`, `ξ` lowest of weight `-(p - r + 2k)`, `k ≤ r`, where `Ψ'` is `Ψ`
with `E` and `F` interchanged. -/
theorem T_eq_flip_psi {p r : ℕ} {w : M} (hw : w ∈ V.flip.stringsLT ((p : ℤ) - r) (r + 1)) :
    V.T q w = ((-1) ^ r * q ^ r) • V.flip.psi p r w := by
  have hmem : w ∈ V.wt ((r : ℤ) - p) := by
    have := V.flip.stringsLT_le_wt _ _ hw
    rwa [flip_wt, neg_sub] at this
  rw [T_eq_zpow_smul_flip_T hq0 hq hq0 (fun _ _ ↦ rfl) hmem,
    T_eq_psi_of_mem (V := V.flip) hq0 hq hw, smul_smul]
  congr 1
  have hne : (-q) ^ p ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 hq0)
  rw [zpow_sub₀ (neg_ne_zero.2 hq0), zpow_natCast, zpow_natCast, ← neg_pow q p, ← neg_pow q r,
    div_mul_cancel₀ _ hne]

omit hq0 hq in
/-- An operator commuting with `F` commutes with its divided powers. -/
lemma comm_dF (Z : Module.End k M) (h : ∀ m, Z (V.F m) = V.F (Z m)) (n : ℕ) (x : M) :
    Z (V.dF n x) = V.dF n (Z x) := by
  have hc : ∀ (N : ℕ) m, Z ((V.F ^ N) m) = (V.F ^ N) (Z m) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => intro m; rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]
  rw [dF_apply, dF_apply, map_smul, hc]

omit hq0 hq in
/-- An operator commuting with `E` commutes with its divided powers. -/
lemma comm_dE (Z : Module.End k M) (h : ∀ m, Z (V.E m) = V.E (Z m)) (n : ℕ) (x : M) :
    Z (V.dE n x) = V.dE n (Z x) :=
  comm_dF (V := V.flip) Z h n x

/-- The induction behind `T(Eⱼ m) = Tᵢ(Eⱼ) T(m)` on integrable modules. Let `W` be `V` or its flip
and `T` a linear map with `T(w) = κ_p Ψ^W_{p,r}(w)` on the spans of short `W`-strings (as for
`T''_q`, by `T_eq_psi_of_mem`, `T_eq_flip_psi`). Let `Z` commute with `F_W`, shift `W`-weights
by `-r`, and satisfy `E_W^{r+1} Z η = 0` for `W`-primitive `η`; let `X`, `G` be commuting
operators with `T ∘ F_W = G ∘ T` and `X (T η) = κ_p Ψ^W_{p,r}(Z η)` for `W`-primitive
`η ∈ W^p`. Then `T ∘ Z = X ∘ T`. -/
theorem T_comp_eq_of_psi (W : IntegrableSl2 q M) (T Z X G : Module.End k M) (r : ℕ) (κ : ℕ → k)
    (hT : ∀ (p : ℕ) (w : M), w ∈ W.stringsLT ((p : ℤ) - r) (r + 1) → T w = κ p • W.psi p r w)
    (hZF : ∀ m, Z (W.F m) = W.F (Z m)) (hZwt : ∀ n, ∀ m ∈ W.wt n, Z m ∈ W.wt (n - r))
    (hZE : ∀ (p : ℕ) η, η ∈ W.wt p → W.E η = 0 → (W.E ^ (r + 1)) (Z η) = 0)
    (hX : ∀ (p : ℕ) η, η ∈ W.wt p → W.E η = 0 → X (T η) = κ p • W.psi p r (Z η))
    (hG : ∀ m, T (W.F m) = G (T m)) (hXG : ∀ m, X (G m) = G (X m)) (m : M) :
    T (Z m) = X (T m) := by
  have hstr : ∀ (p : ℕ) η, η ∈ W.wt p → W.E η = 0 → ∀ j,
      T (Z (W.dF j η)) = X (T (W.dF j η)) := by
    intro p η hη hE j
    induction j with
    | zero =>
      rw [dF_zero, hX p η hη hE]
      apply hT
      have hZη : Z η ∈ W.wt ((p : ℤ) - r) := hZwt _ η hη
      rcases le_or_gt (r : ℤ) p with hrp | hrp
      · exact mem_stringsLT_of_nonneg hq0 hq (by omega) hZη (hZE p η hη hE)
      · have hF : (W.F ^ (p + 1)) (Z η) = 0 := by
          have hc : ∀ (N : ℕ) m, (W.F ^ N) (Z m) = Z ((W.F ^ N) m) := by
            intro N
            induction N with
            | zero => simp
            | succ N ih => intro m; rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply,
                ih, hZF]
          have h0 := dF_eq_zero_of_primitive hq0 hq hη hE (show (p : ℤ) < (p + 1 : ℕ) by
            push_cast; omega)
          rw [dF_apply] at h0
          rw [hc, (smul_eq_zero.1 h0).resolve_left
            (inv_ne_zero (qFactorial_ne_zero_of_pow_ne_one hq0 hq _)), map_zero]
        have := mem_stringsLT_of_nonpos hq0 hq (by omega) hZη hF
        rwa [show p + 1 + (-((p : ℤ) - r)).toNat = r + 1 by omega] at this
    | succ j ih =>
      have hb := qInt_ne_zero_of_pow_ne_one hq0 hq (Nat.succ_pos j)
      have e : W.dF (j + 1) η = (qInt q (j + 1))⁻¹ • W.F (W.dF j η) := by
        rw [F_dF hq0 hq, smul_smul, inv_mul_cancel₀ hb, one_smul]
      rw [e, map_smul, map_smul, hZF, hG, ih, map_smul, map_smul, hG, hXG]
  have key := W.ext_wt (f := T ∘ₗ Z) (g := X ∘ₗ T) fun n m hm ↦
    eq_on_wt hq0 hq (T ∘ₗ Z) (X ∘ₗ T) (fun p j η _ _ hη hE ↦ hstr p η hη hE j) hm
  exact LinearMap.congr_fun key m

end IntegrableSl2

end LieLean.QuantumGroup
