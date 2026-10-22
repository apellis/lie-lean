/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Frobenius.HighestWeight
import LieLean.Algebra.QuantumGroup.Frobenius.Generators

/-!
# `θᵢ` times a Frobenius word lies in the radical

Let `λ` be dominant with `lᵢ ∣ ⟨i, λ⟩` whenever `lᵢ ≥ 2`. A *Frobenius word* is a product of
elements `θⱼ^{(lⱼ)}` of `_F f`. We show that `θᵢ w` lies in the radical `frobRad` of the form of
`Λ_λ` for every Frobenius word `w` and every `i` with `lᵢ ≥ 2`. This is [Lus] 35.3.2 (d)
(`θᵢ⁻ M'_r = 0` for `lᵢ ≥ 2`), stated through the form: `M'_r` is spanned by the vectors `w⁻η`.

## Main results

* `QuantumGroup.integralGenerator_mul_integralGenerator_eq_sum_rev`: the mirror image of
  [Lus] Cor. 7.1.7 in `𝒜f` under the anti-automorphism `σ` of `f`.
* `QuantumGroup.baseGen_one_mul_baseGen_frobOrder_eq_sum`: the mirror image of
  [Lus] Prop. 35.3.1, `θⱼ θᵢ^{(lᵢ)} = Σ_{r ≤ a} vᵢ^{lᵢ(a-r)} [a; r]ᵢ θᵢ^{(lᵢ-r)} θⱼ θᵢ^{(r)}`.
* `QuantumGroup.baseGen_one_mul_mem_frobRad`: [Lus] 35.3.2 (d).
* `QuantumGroup.span_frobWords_sup_frobRad`: [Lus] 35.3.2 (c), `_F f` is spanned by the
  Frobenius words modulo the radical.

## Proof

As in [Lus]: induction on the length of the word. For `w = θⱼ^{(lⱼ)} w'` and `j ≠ i`, the mirror
of 35.3.1 rewrites `θᵢ θⱼ^{(lⱼ)}` as a combination of `θⱼ^{(lⱼ-r)} θᵢ θⱼ^{(r)}` with `r < lⱼ`; the
term `r = 0` is handled by induction, and for `r ≥ 1` the factor `θⱼ^{(r)}` is a multiple of
`θⱼ^r`, and `θⱼ w'` lies in the radical by induction. The hypothesis `lⱼ ≥ -⟨j, i'⟩ + 1` for
`lᵢ ≥ 2` is Lusztig's assumption 35.1.2 (a).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.2.8, 7.1.7, 35.1.2,
  35.3.1, 35.3.2.
-/

open LieLean Finset LusztigF
open scoped TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

section Mirror

variable {I : Type*} [DecidableEq I] (D : LusztigCartanDatum I)

omit [DecidableEq I] in
lemma rev_fDivPow (i : I) (n : ℕ) : rev 𝕂 I (fDivPow D i n) = fDivPow D i n :=
  rev_qDivPow _ _ _

lemma toQuotient_rev_eq {x y : LusztigF 𝕂 I} (h : toQuotient D 𝕧 x = toQuotient D 𝕧 y) :
    toQuotient D 𝕧 (rev 𝕂 I x) = toQuotient D 𝕧 (rev 𝕂 I y) := by
  rw [← sub_eq_zero, ← map_sub, toQuotient_eq_zero_iff] at h ⊢
  rw [← map_sub]
  exact rev_mem_radical h

/-- The mirror image of [Lus] Cor. 7.1.7 in `𝒜f`: for `i ≠ j`, `a = -⟨i, j'⟩` and `m > an`,
`θⱼ^{(n)} θᵢ^{(m)} = Σ_{r ≤ an} γ_{m-r} θᵢ^{(m-r)} θⱼ^{(n)} θᵢ^{(r)}`. -/
theorem integralGenerator_mul_integralGenerator_eq_sum_rev {i j : I} (hij : i ≠ j) {a n m : ℕ}
    (ha : D.cartanMatrix i j = -a) (hm : a * n < m) :
    integralGenerator D j n * integralGenerator D i m =
      ∑ r ∈ range (a * n + 1), laurentHigherSerreCoeff D i a n m (m - r) •
        (integralGenerator D i (m - r) * integralGenerator D j n * integralGenerator D i r) := by
  have h : toQuotient D 𝕧 (fDivPow D i m * fDivPow D j n) = toQuotient D 𝕧
      (∑ r ∈ range (a * n + 1), higherSerreCoeff D i a n m (m - r) •
        (fDivPow D i r * fDivPow D j n * fDivPow D i (m - r))) := by
    rw [toQuotient_fDivPow_mul_fDivPow hij ha hm, map_sum]
    simp only [map_smul]
  have h' := toQuotient_rev_eq D h
  simp only [map_sum, map_smul, rev_mul, rev_fDivPow] at h'
  apply Subtype.ext
  rw [MulMemClass.coe_mul, coe_integralGenerator, coe_integralGenerator, ← map_mul, h',
    AddSubmonoidClass.coe_finsetSum]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [coe_smul_integralForm, integralLaurentEval_laurentHigherSerreCoeff, MulMemClass.coe_mul,
    MulMemClass.coe_mul, coe_integralGenerator, coe_integralGenerator, coe_integralGenerator]
  simp only [map_mul, mul_assoc]

/-- Divided powers of one generator commute in `𝒜f`. -/
lemma integralGenerator_mul_comm (i : I) (r s : ℕ) :
    integralGenerator D i r * integralGenerator D i s =
      integralGenerator D i s * integralGenerator D i r := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, coe_integralGenerator, ← map_mul, fDivPow, qDivPow,
    smul_mul_smul_comm, pow_mul_comm]
  rw [mul_comm (qFactorial _ r)⁻¹]

variable {F : Type*} [Field F] [Algebra 𝒜 F] {l : ℕ}

local notation "ε" => algebraMap 𝒜 F (LaurentPolynomial.T 1)

lemma baseGen_mul_comm (i : I) (r s : ℕ) :
    baseGen D F i r * baseGen D F i s = baseGen D F i s * baseGen D F i r := by
  rw [baseGen, baseGen, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    integralGenerator_mul_comm]

variable (hl0 : 0 < l) (hl : algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (2 * l) = 1)
  (hprim : ∀ t, 0 < t → t < l → algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (2 * t) ≠ 1)
include hl0 hl hprim

/-- The mirror image of [Lus] Prop. 35.3.1: if `i ≠ j`, `a = -⟨i, j'⟩` and `lᵢ ≥ a + 1`, then in
`_F f`, `θⱼ θᵢ^{(lᵢ)} = Σ_{r=0}^{a} vᵢ^{lᵢ(a-r)} [a; r]ᵢ θᵢ^{(lᵢ-r)} θⱼ θᵢ^{(r)}`. -/
theorem baseGen_one_mul_baseGen_frobOrder_eq_sum {i j : I} (hij : i ≠ j) {a : ℕ}
    (ha : D.cartanMatrix i j = -a) (hal : a < D.frobOrder l i) :
    baseGen D F j 1 * baseGen D F i (D.frobOrder l i) =
      ∑ r ∈ range (a + 1), ((ε ^ D.d i) ^ ((D.frobOrder l i : ℤ) * ((a : ℤ) - r)) *
        qBinomial (ε ^ D.d i) a r) •
          (baseGen D F i (D.frobOrder l i - r) * baseGen D F j 1 * baseGen D F i r) := by
  simp only [baseGen]
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    integralGenerator_mul_integralGenerator_eq_sum_rev D hij ha (by omega), mul_one,
    TensorProduct.tmul_sum]
  refine sum_congr rfl fun r hr ↦ ?_
  rw [TensorProduct.tmul_smul, ← algebraMap_smul F,
    algebraMap_laurentHigherSerreCoeff D hl0 hl hprim i (by simpa [Nat.lt_succ_iff] using hr) hal,
    Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]

end Mirror

section Radical

open GrandLoop

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular) (Λ : Dom R)
  {F : Type*} [Field F] [Algebra 𝒜 F] {l : ℕ} (hl0 : 0 < l)
  (hl : algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (2 * l) = 1)
  (hprim : ∀ t, 0 < t → t < l → algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (2 * t) ≠ 1)
include hl0 hl hprim

/-- **[Lus] 35.3.2 (d)**: assume 35.1.2 (a) (`lⱼ ≥ -⟨j, i'⟩ + 1` whenever `i ≠ j` and
`lᵢ ≥ 2`) and `lᵢ ∣ ⟨i, λ⟩` whenever `lᵢ ≥ 2`. Then for every product `w` of elements
`θⱼ^{(lⱼ)}` and every `i` with `lᵢ ≥ 2`, `θᵢ w` lies in the radical of the form of `Λ_λ` on
`_F f`. -/
theorem baseGen_one_mul_mem_frobRad
    (hA : ∀ i j, i ≠ j → 2 ≤ D.frobOrder l j → ∀ a : ℕ, D.cartanMatrix i j = -a →
      a < D.frobOrder l i)
    (hΛ : ∀ i, 2 ≤ D.frobOrder l i → D.frobOrder l i ∣ (Λ.1 (R.coroot i)).toNat)
    {w : F ⊗[𝒜] quotientIntegralForm D}
    (hw : w ∈ Submonoid.closure (Set.range fun j ↦ baseGen D F j (D.frobOrder l j))) :
    ∀ i, 2 ≤ D.frobOrder l i → baseGen D F i 1 * w ∈ frobRad hR Λ F := by
  induction hw using Submonoid.closure_induction_left with
  | one =>
    intro i hi
    rw [mul_one]
    exact baseGen_one_mem_frobRad hR Λ hl0 hl hprim i hi (hΛ i hi)
  | mul_left s hs w _ ih =>
    obtain ⟨j, rfl⟩ := hs
    intro i hi
    by_cases hij : i = j
    · subst hij
      rw [← mul_assoc, baseGen_mul_comm, mul_assoc]
      exact mul_mem_frobRad hR Λ F _ (ih i hi)
    have hji : D.cartanMatrix j i ≤ 0 := by
      have h1 := D.dot_nonpos j i (Ne.symm hij)
      rw [← D.d_mul_cartanMatrix] at h1
      by_contra h2
      have : (0 : ℤ) < D.d j * D.cartanMatrix j i :=
        mul_pos (by exact_mod_cast D.d_pos j) (by omega)
      omega
    obtain ⟨a, ha⟩ : ∃ a : ℕ, D.cartanMatrix j i = -a := ⟨(-D.cartanMatrix j i).toNat, by omega⟩
    have hal := hA j i (Ne.symm hij) hi a ha
    rw [← mul_assoc, baseGen_one_mul_baseGen_frobOrder_eq_sum D hl0 hl hprim (Ne.symm hij) ha hal,
      sum_mul]
    refine Submodule.sum_mem _ fun r hr ↦ ?_
    rw [smul_mul_assoc]
    refine Submodule.smul_mem _ _ ?_
    rw [mem_range] at hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rw [show baseGen D F j 0 = 1 by
        rw [baseGen, integralGenerator_zero, ← Algebra.TensorProduct.one_def], mul_one, mul_assoc]
      exact mul_mem_frobRad hR Λ F _ (ih i hi)
    · have hj : 2 ≤ D.frobOrder l j := by omega
      obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      have hmem : baseGen D F j (r + 1) * w ∈ frobRad hR Λ F := by
        rw [show baseGen D F j (r + 1) = _ from
          baseGen_eq_smul_pow_of_lt D hl0 hl hprim j (show r + 1 < D.frobOrder l j by omega),
          smul_mul_assoc, pow_succ, mul_assoc]
        exact Submodule.smul_mem _ _ (mul_mem_frobRad hR Λ F _ (ih j hj))
      rw [mul_assoc]
      exact mul_mem_frobRad hR Λ F _ hmem

/-- **[Lus] 35.3.2 (c)**: under the hypotheses of `baseGen_one_mul_mem_frobRad` (and `F` of
characteristic zero, as in [Lus] 35.2.1), `_F f` is the sum of the span of the Frobenius words
and the radical of the form of `Λ_λ`. -/
theorem span_frobWords_sup_frobRad [CharZero F]
    (hA : ∀ i j, i ≠ j → 2 ≤ D.frobOrder l j → ∀ a : ℕ, D.cartanMatrix i j = -a →
      a < D.frobOrder l i)
    (hΛ : ∀ i, 2 ≤ D.frobOrder l i → D.frobOrder l i ∣ (Λ.1 (R.coroot i)).toNat) :
    Submodule.span F
        (Submonoid.closure (Set.range fun j ↦ baseGen D F j (D.frobOrder l j)) :
          Set (F ⊗[𝒜] quotientIntegralForm D)) ⊔ frobRad hR Λ F = ⊤ := by
  set W := Submonoid.closure (Set.range fun j ↦ baseGen D F j (D.frobOrder l j))
  set M := Submodule.span F (W : Set (F ⊗[𝒜] quotientIntegralForm D)) ⊔ frobRad hR Λ F
  have hgen : ∀ g ∈ frobeniusGenerators D F l, ∀ m ∈ M, g * m ∈ M := by
    intro g hg m hm
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hm
    clear hm
    rw [mul_add]
    refine add_mem ?_ (Submodule.mem_sup_right (mul_mem_frobRad hR Λ F g hz))
    induction hy using Submodule.span_induction with
    | mem w hw =>
      rcases hg with ⟨j, rfl⟩ | ⟨i, hi, rfl⟩
      · exact Submodule.mem_sup_left
          (Submodule.subset_span (W.mul_mem (Submonoid.subset_closure ⟨j, rfl⟩) hw))
      · exact Submodule.mem_sup_right (baseGen_one_mul_mem_frobRad hR Λ hl0 hl hprim hA hΛ hw i hi)
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact M.smul_mem c hx
  have key : ∀ x ∈ Algebra.adjoin F (frobeniusGenerators D F l), ∀ m ∈ M, x * m ∈ M := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem g hg => exact hgen g hg
    | algebraMap c =>
      intro m hm
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact M.smul_mem c hm
    | add x y _ _ hx hy => intro m hm; rw [add_mul]; exact add_mem (hx m hm) (hy m hm)
    | mul x y _ _ hx hy => intro m hm; rw [mul_assoc]; exact hx _ (hy m hm)
  rw [eq_top_iff]
  intro x _
  have h1 : (1 : F ⊗[𝒜] quotientIntegralForm D) ∈ M :=
    Submodule.mem_sup_left (Submodule.subset_span W.one_mem)
  simpa using key x (by rw [adjoin_frobeniusGenerators D hl0 hl hprim]; trivial) 1 h1

end Radical

end LieLean.QuantumGroup
