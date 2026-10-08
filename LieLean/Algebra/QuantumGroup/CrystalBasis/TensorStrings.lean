/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorSl2
import LieLean.Algebra.QuantumGroup.CrystalBasis.Valuation

/-!
# Strings in a tensor product of two strings

Let `η ∈ M₁ᵃ`, `ζ ∈ M₂ᵇ` be primitive vectors of integrable `U_q(𝔰𝔩₂)`-modules and put
`uᵢ = F^{(i)} η`, `vⱼ = F^{(j)} ζ`. In `M₁ ⊗ M₂` (`QuantumGroup.IntegrableSl2.tensor`, Kashiwara's
coproduct) the vector
`w_s = Σ_{i ≤ s} cᵢ uᵢ ⊗ v_{s-i}`, `c₀ = 1`, `c_{i+1} = -cᵢ [b-s+i+1] q^{b-2s+2i+2} / [a-i]`
is primitive of weight `a + b - 2s` for `s ≤ a` (`QuantumGroup.IntegrableSl2.tensor_E_tensorHigh`),
and the vector
`z_s = Σ_{i ≤ s} dᵢ u_{a-s+i} ⊗ v_{b-i}`, `d₀ = 1`, `d_{i+1} = -dᵢ [a-s+i+1] q^{a-2s+2i+2} / [b-i]`
is killed by `F` for `s ≤ b` (`QuantumGroup.IntegrableSl2.tensor_F_tensorLow`).

Let `A` be a local ring with `ϖ ∈ A` a non-unit mapping to `q`, and `L` the `A`-span of the
`uᵢ ⊗ vⱼ`. Then modulo `ϖ L` (our own computation, via the orders of the coefficients):
* `F^{(r)} w_s ≡ u_r ⊗ v_s` for `r ≤ a - s` (`QuantumGroup.IntegrableSl2.tensor_dF_tensorHigh_sub`);
* `E^{(t)} z_s ≡ u_{a-s} ⊗ v_{b-t}` for `t ≤ b - s`
  (`QuantumGroup.IntegrableSl2.tensor_dE_tensorLow_sub`).
Every term other than the leading one has a coefficient in `ϖ A`: the term
`uᵢ ⊗ v_{s-i} ↦ u_{i+m} ⊗ v_{s-i+n}` of `F^{(r)} w_s` (`m + n = r`) has order
`i(a - s + 1 - r) + n(a - s - m)`. These are the two halves of the strings of the crystal
`B(a) ⊗ B(b)` through `u₀ ⊗ v_s`, which meet at `u_{a-s} ⊗ v_s`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.4
  (Thm. 4.4.3 is proved there by induction on `b` from the case `b = 1`).
* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §1.
-/

open TensorProduct Finset

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁]
  [AddCommGroup M₂] [Module k M₂] (V₁ : IntegrableSl2 q M₁) (V₂ : IntegrableSl2 q M₂)
  (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
  {a b : ℕ} {η : M₁} {ζ : M₂}

/-! ### The primitive vectors `w_s` -/

variable (q a b) in
/-- The coefficients `cᵢ` of `w_s`. -/
noncomputable def highCoeff (s : ℕ) : ℕ → k
  | 0 => 1
  | i + 1 => -highCoeff s i * qIntZ q ((b : ℤ) - s + i + 1) * q ^ ((b : ℤ) - 2 * s + 2 * i + 2) /
      qIntZ q ((a : ℤ) - i)

variable (η ζ a b) in
/-- `w_s = Σ_{i ≤ s} cᵢ uᵢ ⊗ v_{s-i}`. -/
noncomputable def tensorHigh (s : ℕ) : M₁ ⊗[k] M₂ :=
  ∑ i ∈ range (s + 1), highCoeff q a b s i • (V₁.dF i η ⊗ₜ V₂.dF (s - i) ζ)

include hq0 hq

lemma E_dF_prim {p : ℕ} {M : Type*} [AddCommGroup M] [Module k M] {V : IntegrableSl2 q M}
    {x : M} (hx : x ∈ V.prim p) (j : ℕ) :
    V.E (V.dF (j + 1) x) = qIntZ q ((p : ℤ) - j) • V.dF j x :=
  E_dF_succ_of_primitive hq0 hq hx.1 hx.2 j

/-- `w_s` is primitive: `E w_s = 0` for `s ≤ a`. -/
theorem tensor_E_tensorHigh (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) {s : ℕ} (hs : s ≤ a) :
    tensorE V₁ V₂ (tensorHigh V₁ V₂ a b η ζ s) = 0 := by
  rw [tensorHigh, map_sum]
  have hterm : ∀ i ∈ range (s + 1), tensorE V₁ V₂ (highCoeff q a b s i •
      (V₁.dF i η ⊗ₜ V₂.dF (s - i) ζ)) =
      (highCoeff q a b s i * q ^ (-((b : ℤ) - 2 * (s - i : ℕ)))) •
        (V₁.E (V₁.dF i η) ⊗ₜ V₂.dF (s - i) ζ) +
      highCoeff q a b s i • (V₁.dF i η ⊗ₜ V₂.E (V₂.dF (s - i) ζ)) := by
    intro i _
    rw [map_smul, tensorE_tmul _ (dF_mem hζ.1 (s - i)), smul_add, smul_smul]
  have hE1 : V₁.E η = 0 := hη.2
  have hE2 : V₂.E ζ = 0 := hζ.2
  rw [sum_congr rfl hterm, sum_add_distrib, sum_range_succ' _ s, sum_range_succ _ s]
  simp only [dF_zero, hE1, hE2, tmul_zero, zero_tmul, smul_zero, add_zero, Nat.sub_self]
  rw [← sum_add_distrib]
  refine sum_eq_zero fun i hi ↦ ?_
  have hi := mem_range.1 hi
  rw [E_dF_prim hq0 hq hη, show s - i = (s - (i + 1)) + 1 by omega, E_dF_prim hq0 hq hζ,
    show s - (i + 1 + 0) = s - (i + 1) by omega, ← smul_tmul', tmul_smul, smul_smul, smul_smul,
    ← add_smul]
  convert zero_smul k (V₁.dF i η ⊗ₜ V₂.dF (s - (i + 1)) ζ) using 2
  have hai : qIntZ q ((a : ℤ) - i) ≠ 0 := qIntZ_ne_zero hq0 hq (by omega)
  rw [highCoeff]
  field_simp
  have e1 : q ^ ((b : ℤ) - 2 * s + 2 * i + 2) * q ^ (-((b : ℤ) - 2 * ((s - (i + 1) : ℕ) : ℤ))) =
      1 := by
    rw [← zpow_add₀ hq0, show (b : ℤ) - 2 * s + 2 * i + 2 + -((b : ℤ) - 2 * ((s - (i + 1) : ℕ) : ℤ))
      = 0 by push_cast [show i + 1 ≤ s by omega]; ring, zpow_zero]
  have e2 : (b : ℤ) - ((s - (i + 1) : ℕ) : ℤ) = b - s + i + 1 := by
    push_cast [show i + 1 ≤ s by omega]; ring
  rw [mul_assoc (qIntZ _ _), e1, e2]
  ring

omit hq0 hq in
lemma F_dF_eq {M : Type*} [AddCommGroup M] [Module k M] {V : IntegrableSl2 q M} (hq0 : q ≠ 0)
    (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (j : ℕ) (x : M) :
    V.F (V.dF j x) = qIntZ q ((j : ℤ) + 1) • V.dF (j + 1) x := by
  rw [F_dF hq0 hq, ← qIntZ_natCast (sub_inv_ne_zero_of_pow_ne_one hq0 hq)]
  push_cast
  rfl

/-! ### The lowest vectors `z_s` -/

variable (q a b) in
/-- The coefficients `dᵢ` of `z_s`. -/
noncomputable def lowCoeff (s : ℕ) : ℕ → k
  | 0 => 1
  | i + 1 => -lowCoeff s i * qIntZ q ((a : ℤ) - s + i + 1) * q ^ ((a : ℤ) - 2 * s + 2 * i + 2) /
      qIntZ q ((b : ℤ) - i)

variable (η ζ a b) in
/-- `z_s = Σ_{i ≤ s} dᵢ u_{a-s+i} ⊗ v_{b-i}`. -/
noncomputable def tensorLow (s : ℕ) : M₁ ⊗[k] M₂ :=
  ∑ i ∈ range (s + 1), lowCoeff q a b s i • (V₁.dF (a - s + i) η ⊗ₜ V₂.dF (b - i) ζ)

/-- `z_s` is killed by `F`, for `s ≤ a` and `s ≤ b`. -/
theorem tensor_F_tensorLow (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) {s : ℕ} (hsa : s ≤ a)
    (hsb : s ≤ b) : tensorF V₁ V₂ (tensorLow V₁ V₂ a b η ζ s) = 0 := by
  rw [tensorLow, map_sum]
  have hterm : ∀ i ∈ range (s + 1), tensorF V₁ V₂ (lowCoeff q a b s i •
      (V₁.dF (a - s + i) η ⊗ₜ V₂.dF (b - i) ζ)) =
      (lowCoeff q a b s i * qIntZ q (((a - s + i : ℕ) : ℤ) + 1)) •
        (V₁.dF (a - s + i + 1) η ⊗ₜ V₂.dF (b - i) ζ) +
      (lowCoeff q a b s i * q ^ ((a : ℤ) - 2 * (a - s + i : ℕ)) *
        qIntZ q (((b - i : ℕ) : ℤ) + 1)) •
        (V₁.dF (a - s + i) η ⊗ₜ V₂.dF (b - i + 1) ζ) := by
    intro i _
    have hmem : V₁.dF (a - s + i) η ∈ V₁.wt ((a : ℤ) - 2 * (a - s + i : ℕ)) := dF_mem hη.1 _
    rw [map_smul, tensorF_tmul hmem, F_dF_eq hq0 hq, F_dF_eq hq0 hq, smul_add]
    simp only [← smul_tmul' (R' := k), tmul_smul (R' := k), smul_smul, mul_assoc]
  rw [sum_congr rfl hterm, sum_add_distrib, sum_range_succ _ s, sum_range_succ' _ s]
  have h1 : V₁.dF (a - s + s + 1) η = 0 :=
    dF_eq_zero_of_primitive hq0 hq hη.1 hη.2 (by push_cast; omega)
  have h2 : V₂.dF (b - 0 + 1) ζ = 0 :=
    dF_eq_zero_of_primitive hq0 hq hζ.1 hζ.2 (by push_cast; omega)
  rw [h1, h2]
  simp only [zero_tmul, tmul_zero, smul_zero, add_zero]
  rw [add_comm, ← sum_add_distrib]
  refine sum_eq_zero fun i hi ↦ ?_
  have hi := mem_range.1 hi
  rw [show a - s + (i + 1) = a - s + i + 1 by omega, show b - (i + 1) + 1 = b - i by omega,
    ← add_smul]
  convert zero_smul k (V₁.dF (a - s + i + 1) η ⊗ₜ V₂.dF (b - i) ζ) using 2
  have hbi : qIntZ q ((b : ℤ) - i) ≠ 0 := qIntZ_ne_zero hq0 hq (by omega)
  rw [lowCoeff]
  have e1 : q ^ ((a : ℤ) - 2 * s + 2 * i + 2) * q ^ ((a : ℤ) - 2 * ((a - s + i + 1 : ℕ) : ℤ)) =
      1 := by
    rw [← zpow_add₀ hq0, show (a : ℤ) - 2 * s + 2 * i + 2 + ((a : ℤ) - 2 *
      ((a - s + i + 1 : ℕ) : ℤ)) = 0 by push_cast [hsa]; ring, zpow_zero]
  have e2 : (((b - (i + 1) : ℕ) : ℤ) + 1) = b - i := by
    push_cast [show i + 1 ≤ b by omega]; ring
  have e3 : (((a - s + i : ℕ) : ℤ) + 1) = a - s + i + 1 := by push_cast [hsa]; ring
  rw [e2, e3]
  field_simp
  rw [e1]
  ring

/-! ### Divided powers of `w_s` and `z_s` -/

/-- `F^{(r)} w_s` as an explicit combination of the `u_{i+m} ⊗ v_{s-i+n}`. -/
theorem tensor_dF_tensorHigh (hη : η ∈ V₁.prim a) (s r : ℕ) :
    (tensor V₁ V₂ hq0 hq).dF r (tensorHigh V₁ V₂ a b η ζ s) =
      ∑ i ∈ range (s + 1), ∑ p ∈ antidiagonal r,
        (highCoeff q a b s i * q ^ ((p.2 : ℤ) * ((a : ℤ) - 2 * i) - p.1 * p.2) *
          qBinomial q (p.1 + i) p.1 * qBinomial q (p.2 + (s - i)) p.2) •
          (V₁.dF (p.1 + i) η ⊗ₜ V₂.dF (p.2 + (s - i)) ζ) := by
  rw [tensorHigh, map_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, tensor_dF_tmul hq0 hq (dF_mem hη.1 i), smul_sum]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [dF_dF hq0 hq, dF_dF hq0 hq]
  simp only [← smul_tmul' (R' := k), tmul_smul (R' := k), smul_smul]
  congr 1
  ring

/-- `E^{(t)} z_s` as an explicit combination; the terms with `n > a - s + i` vanish. -/
theorem tensor_dE_tensorLow (hζ : ζ ∈ V₂.prim b) (s t : ℕ) :
    (tensor V₁ V₂ hq0 hq).dE t (tensorLow V₁ V₂ a b η ζ s) =
      ∑ i ∈ range (s + 1), ∑ p ∈ antidiagonal t,
        (lowCoeff q a b s i * q ^ (-((p.1 : ℤ) * ((b : ℤ) - 2 * (b - i : ℕ))) - p.1 * p.2)) •
          (V₁.dE p.1 (V₁.dF (a - s + i) η) ⊗ₜ V₂.dE p.2 (V₂.dF (b - i) ζ)) := by
  rw [tensorLow, map_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, tensor_dE_tmul hq0 hq _ (dF_mem hζ.1 (b - i)), smul_sum]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [smul_smul]

omit hq0 hq in
lemma dE_dF_eq_smul {M : Type*} [AddCommGroup M] [Module k M] {V : IntegrableSl2 q M}
    (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) {p : ℕ} {x : M} (hx : x ∈ V.prim p)
    (n K : ℕ) (hK : K ≤ p) :
    V.dE n (V.dF K x) = (if n ≤ K then qBinomial q (p - K + n) n else 0) • V.dF (K - n) x := by
  split_ifs with h
  · exact dE_dF_of_primitive hq0 hq hx.1 hx.2 h hK
  · rw [zero_smul]; exact dE_dF_eq_zero_of_lt hq0 hq hx.1 hx.2 hK (by omega)

/-! ### Orders of the coefficients -/

section Orders

variable {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

omit hq0 hq in
lemma isUnitPow_qIntZ [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hq : ∀ n : ℕ, 0 < n → algebraMap A k ϖ ^ n ≠ 1) (hq0 : algebraMap A k ϖ ≠ 0) {n : ℤ}
    (hn : 0 < n) : IsUnitPow ϖ (1 - n) (qIntZ (algebraMap A k ϖ) n) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
  rw [qIntZ_natCast (sub_inv_ne_zero_of_pow_ne_one hq0 hq)]
  exact (isOnePow_qInt hq0 (by omega)).isUnitPow hϖ

omit hq0 hq in
lemma isUnitPow_qBinomial [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hq0 : algebraMap A k ϖ ≠ 0) {n m : ℕ} (hmn : m ≤ n) :
    IsUnitPow ϖ (-(m * (n - m) : ℕ)) (qBinomial (algebraMap A k ϖ) n m) :=
  (isOnePow_qBinomial hq0 hmn).isUnitPow hϖ

variable (k ϖ) in
/-- Sums of vectors `κ • g p` with `κ ∈ ϖ A`. -/
def smallSpan {M : Type*} [AddCommGroup M] [Module k M] (g : ℕ × ℕ → M) : AddSubmonoid M :=
  AddSubmonoid.closure {x | ∃ (κ : k) (p : ℕ × ℕ), InPow ϖ 1 κ ∧ x = κ • g p}

omit hq0 hq in
lemma smul_mem_smallSpan {M : Type*} [AddCommGroup M] [Module k M] (g : ℕ × ℕ → M) {κ : k}
    (hκ : InPow ϖ 1 κ) (p : ℕ × ℕ) : κ • g p ∈ smallSpan k ϖ g :=
  AddSubmonoid.subset_closure ⟨κ, p, hκ, rfl⟩

variable [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖq : algebraMap A k ϖ = q)
include hϖ hϖq

/-- `cᵢ ∈ q^{i(a-s+1)} A×`. -/
lemma isUnitPow_highCoeff {s : ℕ} (hsa : s ≤ a) (hsb : s ≤ b) :
    ∀ i ≤ s, IsUnitPow ϖ ((i : ℤ) * ((a : ℤ) - s + 1)) (highCoeff q a b s i) := by
  subst hϖq
  intro i
  induction i with
  | zero => intro _; simpa [highCoeff] using isUnitPow_one
  | succ i ih =>
    intro hi
    rw [highCoeff]
    have h := (((ih (by omega)).neg.mul hq0 (isUnitPow_qIntZ hϖ hq hq0
      (n := (b : ℤ) - s + i + 1) (by omega))).mul hq0
      (isUnitPow_zpow ((b : ℤ) - 2 * s + 2 * i + 2))).div hq0
      (isUnitPow_qIntZ hϖ hq hq0 (n := (a : ℤ) - i) (by omega))
    convert h using 1
    push_cast; ring

/-- `dᵢ ∈ q^{i(b-s+1)} A×`. -/
lemma isUnitPow_lowCoeff {s : ℕ} (hsa : s ≤ a) (hsb : s ≤ b) :
    ∀ i ≤ s, IsUnitPow ϖ ((i : ℤ) * ((b : ℤ) - s + 1)) (lowCoeff q a b s i) := by
  subst hϖq
  intro i
  induction i with
  | zero => intro _; simpa [lowCoeff] using isUnitPow_one
  | succ i ih =>
    intro hi
    rw [lowCoeff]
    have h := (((ih (by omega)).neg.mul hq0 (isUnitPow_qIntZ hϖ hq hq0
      (n := (a : ℤ) - s + i + 1) (by omega))).mul hq0
      (isUnitPow_zpow ((a : ℤ) - 2 * s + 2 * i + 2))).div hq0
      (isUnitPow_qIntZ hϖ hq hq0 (n := (b : ℤ) - i) (by omega))
    convert h using 1
    push_cast; ring

/-- `F^{(r)} w_s ≡ u_r ⊗ v_s` modulo `ϖ`, for `r ≤ a - s`. -/
theorem tensor_dF_tensorHigh_sub (hη : η ∈ V₁.prim a) {s : ℕ} (hsa : s ≤ a) (hsb : s ≤ b)
    {r : ℕ} (hr : r ≤ a - s) :
    (tensor V₁ V₂ hq0 hq).dF r (tensorHigh V₁ V₂ a b η ζ s) - V₁.dF r η ⊗ₜ V₂.dF s ζ ∈
      smallSpan k ϖ (fun p ↦ V₁.dF p.1 η ⊗ₜ V₂.dF p.2 ζ) := by
  classical
  rw [tensor_dF_tensorHigh V₁ V₂ hq0 hq hη, ← sum_product']
  have hlead : ((0 : ℕ), ((r, 0) : ℕ × ℕ)) ∈ range (s + 1) ×ˢ antidiagonal r := by
    simp
  rw [← add_sum_erase _ _ hlead]
  simp only [highCoeff, Nat.cast_zero, mul_zero, sub_zero, zero_mul, zpow_zero, mul_one,
    add_zero, qBinomial_self, Nat.sub_zero, zero_add, qBinomial_zero_right, one_smul,
    add_sub_cancel_left]
  refine AddSubmonoid.sum_mem _ fun t ht ↦ ?_
  obtain ⟨hne, ht⟩ := mem_erase.1 ht
  obtain ⟨i, m, n⟩ := t
  simp only [mem_product, mem_range, mem_antidiagonal] at ht
  obtain ⟨hi, hmn⟩ := ht
  refine smul_mem_smallSpan _ ?_ ((m + i, n + (s - i)) : ℕ × ℕ)
  subst hϖq
  have h := (((isUnitPow_highCoeff hq0 hq hϖ rfl hsa hsb i (by omega)).mul hq0
    (isUnitPow_zpow ((n : ℤ) * ((a : ℤ) - 2 * i) - m * n))).mul hq0
    (isUnitPow_qBinomial hϖ hq0 (Nat.le_add_right m i))).mul hq0
    (isUnitPow_qBinomial hϖ hq0 (Nat.le_add_right n (s - i)))
  refine h.inPow.mono hq0 ?_
  simp only [Nat.add_sub_cancel_left]
  push_cast [show i ≤ s by omega]
  have hk : (1 : ℤ) ≤ i * ((a : ℤ) - s + 1 - m - n) + n * ((a : ℤ) - s - m) := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have hn : 1 ≤ n := by
        by_contra h0
        have hn0 : n = 0 := by omega
        have hm : m = r := by omega
        exact hne (by rw [hn0, hm])
      have h1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
      have h2 : (1 : ℤ) ≤ (a : ℤ) - s - m := by omega
      push_cast
      nlinarith
    · have h3 : (1 : ℤ) ≤ i := by exact_mod_cast hi0
      have h4 : (1 : ℤ) ≤ (a : ℤ) - s + 1 - m - n := by omega
      have h2 : (0 : ℤ) ≤ n * ((a : ℤ) - s - m) :=
        mul_nonneg (by positivity) (by omega)
      nlinarith
  nlinarith [hk]

/-- `E^{(t)} z_s ≡ u_{a-s} ⊗ v_{b-t}` modulo `ϖ`, for `t ≤ b - s`. -/
theorem tensor_dE_tensorLow_sub (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) {s : ℕ}
    (hsa : s ≤ a) (hsb : s ≤ b) {t : ℕ} (ht : t ≤ b - s) :
    (tensor V₁ V₂ hq0 hq).dE t (tensorLow V₁ V₂ a b η ζ s) - V₁.dF (a - s) η ⊗ₜ V₂.dF (b - t) ζ ∈
      smallSpan k ϖ (fun p ↦ V₁.dF p.1 η ⊗ₜ V₂.dF p.2 ζ) := by
  classical
  rw [tensor_dE_tensorLow V₁ V₂ hq0 hq hζ s, ← sum_product']
  have hlead : ((0 : ℕ), ((0, t) : ℕ × ℕ)) ∈ range (s + 1) ×ˢ antidiagonal t := by simp
  rw [← add_sum_erase _ _ hlead]
  have hl : (lowCoeff q a b s 0 * q ^ (-(((0, t) : ℕ × ℕ).1 * ((b : ℤ) - 2 * (b - 0 : ℕ))) -
      ((0, t) : ℕ × ℕ).1 * ((0, t) : ℕ × ℕ).2)) •
      (V₁.dE ((0, t) : ℕ × ℕ).1 (V₁.dF (a - s + 0) η) ⊗ₜ[k]
        V₂.dE ((0, t) : ℕ × ℕ).2 (V₂.dF (b - 0) ζ)) = V₁.dF (a - s) η ⊗ₜ[k] V₂.dF (b - t) ζ := by
    simp only [lowCoeff, Nat.cast_zero, zero_mul, neg_zero, sub_self, zpow_zero, mul_one,
      one_smul, add_zero, Nat.sub_zero, dE_zero]
    rw [dE_dF_of_primitive hq0 hq hζ.1 hζ.2 (show t ≤ b by omega) le_rfl, Nat.sub_self, zero_add,
      qBinomial_self, one_smul]
  rw [hl, add_sub_cancel_left]
  refine AddSubmonoid.sum_mem _ fun x hx ↦ ?_
  obtain ⟨hne, hx⟩ := mem_erase.1 hx
  obtain ⟨i, n, m⟩ := x
  simp only [mem_product, mem_range, mem_antidiagonal] at hx
  obtain ⟨hi, hnm⟩ := hx
  dsimp only
  rw [dE_dF_eq_smul hq0 hq hη n (a - s + i) (by omega),
    dE_dF_eq_smul hq0 hq hζ m (b - i) (by omega), ← smul_tmul' (R' := k), tmul_smul (R' := k),
    smul_smul, smul_smul]
  refine smul_mem_smallSpan _ ?_ ((a - s + i - n, b - i - m) : ℕ × ℕ)
  split_ifs with h1 h2 h2
  · subst hϖq
    have h := ((((isUnitPow_lowCoeff hq0 hq hϖ rfl hsa hsb i (by omega)).mul hq0
      (isUnitPow_zpow (-((n : ℤ) * ((b : ℤ) - 2 * (b - i : ℕ))) - n * m))).mul hq0
      (isUnitPow_qBinomial hϖ hq0 (show n ≤ a - (a - s + i) + n by omega))).mul hq0
      (isUnitPow_qBinomial hϖ hq0 (show m ≤ b - (b - i) + m by omega)))
    have e : (b - (b - i) + m - m) = i := by omega
    have e' : (a - (a - s + i) + n - n) = s - i := by omega
    refine (h.inPow.mono hq0 ?_).congr_right ?_
    · rw [e, e']
      push_cast [show i ≤ s by omega, show i ≤ b by omega]
      have hk : (1 : ℤ) ≤ i * ((b : ℤ) - s + 1 - n - m) + n * ((b : ℤ) - s - m) := by
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · have hn : 1 ≤ n := by
            by_contra h0
            have hn0 : n = 0 := by omega
            have hm : m = t := by omega
            exact hne (by rw [hn0, hm])
          have h1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
          have h2 : (1 : ℤ) ≤ (b : ℤ) - s - m := by omega
          push_cast
          nlinarith
        · have h3 : (1 : ℤ) ≤ i := by exact_mod_cast hi0
          have h4 : (1 : ℤ) ≤ (b : ℤ) - s + 1 - n - m := by omega
          have h2 : (0 : ℤ) ≤ n * ((b : ℤ) - s - m) :=
            mul_nonneg (by positivity) (by omega)
          nlinarith
      nlinarith [hk]
    · ring
  all_goals simpa using inPow_zero 1

end Orders

end IntegrableSl2

end LieLean.QuantumGroup
