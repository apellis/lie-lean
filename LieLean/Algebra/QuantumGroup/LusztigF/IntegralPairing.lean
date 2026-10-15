/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.LusztigF.QuotientLattice
import LieLean.Algebra.QuantumGroup.LusztigF.IntegralForm
import Mathlib.RingTheory.LaurentSeries

/-!
# Integrality of the coproduct and of the form on `𝒜f`

Over `𝕂 = ℚ(v)`, `𝒜 = ℤ[v, v⁻¹]`, let `𝒜'f ⊆ 'f` be the `𝒜`-span of the monomials
`θ_{i₁}^{(n₁)} ⋯ θ_{iₖ}^{(nₖ)}` in the divided powers (`fIntegral`). We prove:

* [Lus] 1.4.2: `r(θᵢ^{(n)}) = Σ_{t + t' = n} vᵢ^{tt'} θᵢ^{(t)} ⊗ θᵢ^{(t')}` (`comul_fDivPow`);
* [Lus] 14.2.6 (a): `r(𝒜'f) ⊆ 𝒜'f ⊗ 𝒜'f`, as the `𝒜`-span of the `x ⊗ y` with `x`, `y`
  monomials (`comul_mem_fIntegralTensor`);
* [Lus] 14.2.6 (b): `(x, y) ∈ ℤ((v⁻¹)) ∩ ℚ(v)` for `x, y ∈ 𝒜'f` (`form_mem_intLaurentInf`), and
  the same on `𝒜f ⊆ f` (`quotientForm_mem_intLaurentInf`).

Here `ℤ[[v⁻¹]] ∩ ℚ(v)` (`intSeriesInf`) is the set of rational functions whose expansion at
`v = ∞` (`expandInf`, the Laurent expansion of `f(v⁻¹)` in `v`) is a power series with integer
coefficients, and `ℤ((v⁻¹)) ∩ ℚ(v)` (`intLaurentInf`) allows finitely many positive powers of
`v`.

Lusztig deduces 14.2.6 from the geometric construction (13.2). The proof here is our own and
algebraic: by 1.4.2 and the multiplicativity of `r`, `r(𝒜'f) ⊆ 𝒜'f ⊗ 𝒜'f`; by
`(θᵢ^{(n)} x, y) = (θᵢ^{(n)} ⊗ x, r(y))` ([Lus] 1.2.3 (c)) and induction on the number of
factors, the claim reduces to `(θᵢ^{(n)}, θᵢ^{(n)}) = ∏_{s=1}^n (1 - vᵢ^{-2s})⁻¹`
([Lus] 1.4.4; `coefU_mem_intSeriesInf`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.2.3, 1.4.2, 1.4.4,
  14.2.6.
-/

open LieLean TensorProduct Finset
open scoped RatFunc

noncomputable section

namespace LieLean.QuantumGroup

open LusztigF GrandLoop

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)

/-! ### `ℤ[[v⁻¹]] ∩ ℚ(v)` and `ℤ((v⁻¹)) ∩ ℚ(v)` -/

/-- The expansion at `v = ∞`: `f ↦` the Laurent series of `f(v⁻¹)`. -/
def expandInf : 𝕂 →+* LaurentSeries ℚ where
  toFun f := algebraMap 𝕂 (LaurentSeries ℚ) (RatFunc.bar f)
  map_one' := by simp
  map_mul' f g := by simp
  map_zero' := by simp
  map_add' f g := by simp

lemma expandInf_apply (f : 𝕂) :
    expandInf f = algebraMap 𝕂 (LaurentSeries ℚ) (RatFunc.bar f) := rfl

/-- Integer power series, as Laurent series over `ℚ`. -/
def intSeriesHom : PowerSeries ℤ →+* LaurentSeries ℚ :=
  (HahnSeries.ofPowerSeries ℤ ℚ).comp (PowerSeries.map (Int.castRingHom ℚ))

/-- `ℤ[[v⁻¹]] ∩ ℚ(v)`: rational functions whose expansion at `v = ∞` is an integer power series
in `v⁻¹`. -/
def intSeriesInf : Subring 𝕂 := intSeriesHom.range.comap expandInf

lemma mem_intSeriesInf {f : 𝕂} : f ∈ intSeriesInf ↔ ∃ g, intSeriesHom g = expandInf f :=
  Iff.rfl

lemma expandInf_inv_X : expandInf 𝕧⁻¹ = intSeriesHom PowerSeries.X := by
  simp [expandInf_apply, intSeriesHom, map_inv₀, RatFunc.bar_X, HahnSeries.ofPowerSeries_X]

lemma inv_X_mem_intSeriesInf : 𝕧⁻¹ ∈ intSeriesInf :=
  ⟨PowerSeries.X, expandInf_inv_X.symm⟩

/-- `(1 - v^{-m})⁻¹ ∈ ℤ[[v⁻¹]]` for `m > 0`. -/
lemma one_sub_inv_X_pow_inv_mem {m : ℕ} (hm : 0 < m) : (1 - 𝕧⁻¹ ^ m)⁻¹ ∈ intSeriesInf := by
  set g : PowerSeries ℤ := 1 - PowerSeries.X ^ m
  have hg : PowerSeries.constantCoeff g = ((1 : ℤˣ) : ℤ) := by
    simp [g, map_sub, map_pow, zero_pow hm.ne']
  refine ⟨PowerSeries.invOfUnit g 1, ?_⟩
  have h1 : expandInf (1 - 𝕧⁻¹ ^ m) = intSeriesHom g := by
    simp only [map_sub, map_one, map_pow, expandInf_inv_X, g]
  rw [map_inv₀, h1]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, mul_comm, PowerSeries.mul_invOfUnit g 1 hg, map_one]

/-- `ℤ((v⁻¹)) ∩ ℚ(v)`: rational functions whose expansion at `v = ∞` is an integer Laurent
series in `v⁻¹`. -/
def intLaurentInf : Subring 𝕂 where
  carrier := {f | ∃ n : ℕ, 𝕧⁻¹ ^ n * f ∈ intSeriesInf}
  mul_mem' := by
    rintro f g ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨n + m, by rw [pow_add]; convert mul_mem hn hm using 1; ring⟩
  one_mem' := ⟨0, by simp [one_mem]⟩
  add_mem' := by
    rintro f g ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have := add_mem (mul_mem (pow_mem inv_X_mem_intSeriesInf m) hn)
      (mul_mem (pow_mem inv_X_mem_intSeriesInf n) hm)
    convert this using 1; ring
  zero_mem' := ⟨0, by simp [zero_mem]⟩
  neg_mem' := by
    rintro f ⟨n, hn⟩
    exact ⟨n, by simpa [mul_neg] using neg_mem hn⟩

lemma intSeriesInf_le_intLaurentInf : intSeriesInf ≤ intLaurentInf :=
  fun f hf ↦ ⟨0, by simpa using hf⟩

lemma zpow_X_mem_intLaurentInf (k : ℤ) : 𝕧 ^ k ∈ intLaurentInf := by
  have hX : 𝕧 ∈ intLaurentInf :=
    ⟨1, by rw [pow_one, inv_mul_cancel₀ RatFunc.X_ne_zero]; exact one_mem _⟩
  rcases k with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast]; exact pow_mem hX k
  · rw [zpow_negSucc, ← inv_pow]
    exact intSeriesInf_le_intLaurentInf (pow_mem inv_X_mem_intSeriesInf _)

/-! ### `(θᵢ^{(n)}, θᵢ^{(n)})` ([Lus] 1.4.4) -/

variable {I : Type*} (D : LusztigCartanDatum I)

/-- The factor `[r+1]⁻¹ (θᵢ, θᵢ) vᵢ^r` of `coefU` is `(1 - vᵢ^{-2(r+1)})⁻¹`. -/
lemma coefU_factor (i : I) (r : ℕ) :
    (qInt (𝕧 ^ D.d i)⁻¹ (r + 1))⁻¹ * thetaNorm D 𝕧 i * ((𝕧 ^ D.d i) ^ r) =
      (1 - 𝕧⁻¹ ^ (2 * D.d i * (r + 1)))⁻¹ := by
  set q : 𝕂 := 𝕧 ^ D.d i with hq
  have hd := D.d_pos i
  have hq0 : q ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  have hpow : ∀ m : ℕ, 0 < m → q ^ m ≠ 1 := fun m hm ↦ by
    rw [hq, ← pow_mul]; exact ratFunc_X_pow_ne_one (Nat.mul_pos hd hm)
  have hint := qInt_mul_sub (v := q⁻¹) (r + 1)
  have hsub : q⁻¹ - q⁻¹⁻¹ ≠ 0 := by
    rw [inv_inv, sub_ne_zero]
    intro h
    exact hpow 2 two_pos (by rw [sq]; nth_rewrite 1 [← h]; exact inv_mul_cancel₀ hq0)
  have hn : q ^ (2 * (r + 1)) ≠ 1 := hpow _ (by omega)
  have hrhs : 𝕧⁻¹ ^ (2 * D.d i * (r + 1)) = q⁻¹ ^ (2 * (r + 1)) := by
    rw [hq, inv_pow, inv_pow, ← pow_mul, mul_comm 2 (D.d i), mul_assoc]
  have hint' : qInt q⁻¹ (r + 1) = (q⁻¹ ^ (r + 1) - q⁻¹⁻¹ ^ (r + 1)) / (q⁻¹ - q⁻¹⁻¹) :=
    eq_div_of_mul_eq hsub (by rw [mul_comm]; exact hint)
  rw [hrhs, thetaNorm, ← hq, hint']
  have h1 : 1 - q ^ 2 ≠ 0 := sub_ne_zero.2 (hpow 2 two_pos).symm
  have h3 : 1 - q ^ (2 * (r + 1)) ≠ 0 := sub_ne_zero.2 hn.symm
  have hr0 : q ^ (r + 1) ≠ 0 := pow_ne_zero _ hq0
  simp only [inv_inv, inv_pow]
  have e1 : (q ^ (r + 1))⁻¹ - q ^ (r + 1) = (1 - q ^ (2 * (r + 1))) / q ^ (r + 1) := by
    field_simp; ring
  have e2 : q⁻¹ - q = (1 - q ^ 2) / q := by field_simp
  have e3 : 1 - (q ^ 2)⁻¹ = -(1 - q ^ 2) / q ^ 2 := by field_simp; ring
  have e4 : 1 - (q ^ (2 * (r + 1)))⁻¹ = -(1 - q ^ (2 * (r + 1))) / q ^ (2 * (r + 1)) := by
    field_simp; ring
  rw [e1, e2, e3, e4]
  field_simp
  ring

/-- [Lus] 1.4.4: `(θᵢ^{(n)}, θᵢ^{(n)}) = ∏_{s=1}^n (1 - vᵢ^{-2s})⁻¹ ∈ ℤ[[v⁻¹]]`. -/
lemma coefU_mem_intSeriesInf (i : I) (n : ℕ) : coefU D 𝕧 i n ∈ intSeriesInf := by
  induction n with
  | zero => exact one_mem _
  | succ r ih =>
    rw [coefU, coefU_factor]
    exact mul_mem ih (one_sub_inv_X_pow_inv_mem (Nat.mul_pos (Nat.mul_pos two_pos
      (D.d_pos i)) r.succ_pos))

/-! ### Divided powers and monomials in `'f` -/

/-- The divided power `θᵢ^{(n)}` in `'f`. -/
abbrev fDivPow (i : I) (n : ℕ) : LusztigF 𝕂 I := qDivPow (𝕧 ^ D.d i) n (θ 𝕂 i)

/-- The monomial `θ_{i₁}^{(n₁)} ⋯ θ_{iₖ}^{(nₖ)}` in the divided powers. -/
def fDivMonomial : List (I × ℕ) → LusztigF 𝕂 I
  | [] => 1
  | p :: w => fDivPow D p.1 p.2 * fDivMonomial w

/-- The weight `Σ nₖ iₖ` of a divided-power monomial. -/
def divWeight : List (I × ℕ) → I →₀ ℕ
  | [] => 0
  | p :: w => p.2 • Finsupp.single p.1 1 + divWeight w

@[simp] lemma fDivMonomial_nil : fDivMonomial D [] = 1 := rfl

@[simp] lemma fDivMonomial_cons (p : I × ℕ) (w : List (I × ℕ)) :
    fDivMonomial D (p :: w) = fDivPow D p.1 p.2 * fDivMonomial D w := rfl

lemma fDivMonomial_append (w w' : List (I × ℕ)) :
    fDivMonomial D (w ++ w') = fDivMonomial D w * fDivMonomial D w' := by
  induction w with
  | nil => simp
  | cons p w ih => simp [ih, mul_assoc]

lemma fDivMonomial_singleton (i : I) (n : ℕ) : fDivMonomial D [(i, n)] = fDivPow D i n := by
  simp

lemma fDivPow_mem_weightSpace (i : I) (n : ℕ) :
    fDivPow D i n ∈ LusztigF.weightSpace 𝕂 (n • Finsupp.single i 1) := by
  refine Submodule.smul_mem _ _ ?_
  induction n with
  | zero => simpa using (one_mem_weightSpace (k := 𝕂) (I := I))
  | succ n ih => simpa [pow_succ, add_smul] using mul_mem_weightSpace ih (θ_mem_weightSpace i)

lemma fDivMonomial_mem_weightSpace (w : List (I × ℕ)) :
    fDivMonomial D w ∈ LusztigF.weightSpace 𝕂 (divWeight w) := by
  induction w with
  | nil => simpa [divWeight] using (one_mem_weightSpace (k := 𝕂) (I := I))
  | cons p w ih => exact mul_mem_weightSpace (fDivPow_mem_weightSpace D p.1 p.2) ih

lemma fDivPow_zero (i : I) : fDivPow D i 0 = 1 := by simp [qDivPow, qFactorial]

lemma qInt_X_ne_zero (i : I) {n : ℕ} (hn : 0 < n) : qInt (𝕧 ^ D.d i) n ≠ 0 :=
  qInt_ne_zero (pow_ne_zero _ RatFunc.X_ne_zero) (by
    rw [← pow_mul]; exact ratFunc_X_pow_ne_one (Nat.mul_pos (D.d_pos i) (by omega)))

lemma θ_mul_fDivPow (i : I) (n : ℕ) :
    θ 𝕂 i * fDivPow D i n = qInt (𝕧 ^ D.d i) (n + 1) • fDivPow D i (n + 1) := by
  simp only [fDivPow, qDivPow, qFactorial, mul_inv, smul_smul, mul_smul_comm]
  rw [← mul_assoc, mul_inv_cancel₀ (qInt_X_ne_zero D i n.succ_pos), one_mul, pow_succ']

lemma fDivPow_succ (i : I) (n : ℕ) :
    fDivPow D i (n + 1) = (qInt (𝕧 ^ D.d i) (n + 1))⁻¹ • (θ 𝕂 i * fDivPow D i n) := by
  rw [θ_mul_fDivPow, smul_smul, inv_mul_cancel₀ (qInt_X_ne_zero D i n.succ_pos), one_smul]

lemma counit_fDivPow_mem (i : I) (n : ℕ) : LusztigF.counit (fDivPow D i n) ∈ intSeriesInf := by
  rcases n with _ | n
  · rw [fDivPow_zero, map_one]; exact one_mem _
  · simp [fDivPow, qDivPow, zero_mem]

lemma counit_fDivMonomial_mem (w : List (I × ℕ)) :
    LusztigF.counit (fDivMonomial D w) ∈ intSeriesInf := by
  induction w with
  | nil => simp [one_mem]
  | cons p w ih => rw [fDivMonomial_cons, map_mul]; exact mul_mem (counit_fDivPow_mem D _ _) ih

/-! ### The integral form `𝒜'f` -/

/-- `𝒜'f`: the `𝒜`-span of the divided-power monomials, as the `ℤ`-span of their multiples by
the powers `v^k`. -/
def fIntegral : Submodule ℤ (LusztigF 𝕂 I) :=
  Submodule.span ℤ {x | ∃ (k : ℤ) (w : List (I × ℕ)), x = (𝕧 ^ k) • fDivMonomial D w}

lemma zpow_smul_mem_fIntegral (k : ℤ) {x : LusztigF 𝕂 I} (hx : x ∈ fIntegral D) :
    (𝕧 ^ k) • x ∈ fIntegral D := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, w, rfl⟩ := hx
    exact Submodule.subset_span ⟨k + l, w, by rw [smul_smul, ← zpow_add₀ RatFunc.X_ne_zero]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

lemma laurent_smul_mem_fIntegral (a : LaurentPolynomial ℤ) {x : LusztigF 𝕂 I}
    (hx : x ∈ fIntegral D) : integralLaurentEval a • x ∈ fIntegral D := by
  induction a using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, add_smul]; exact add_mem hp hq
  | C_mul_T n c =>
    have hC : integralLaurentEval (LaurentPolynomial.C c) = (c : 𝕂) := by
      simp [integralLaurentEval]
    rw [map_mul, hC, integralLaurentEval_T, mul_smul, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ c (zpow_smul_mem_fIntegral D n hx)

lemma mul_mem_fIntegral {x y : LusztigF 𝕂 I} (hx : x ∈ fIntegral D) (hy : y ∈ fIntegral D) :
    x * y ∈ fIntegral D := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, w, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, w', rfl⟩ := hy
      refine Submodule.subset_span ⟨k + l, w ++ w', ?_⟩
      rw [smul_mul_smul_comm, ← zpow_add₀ RatFunc.X_ne_zero, fDivMonomial_append]
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

lemma twist_fDivPow (i : I) (n : ℕ) :
    twist D 𝕧 i (fDivPow D i n) = ((𝕧 ^ D.d i) ^ 2) ^ n • fDivPow D i n := by
  simp only [fDivPow, qDivPow, map_smul, map_pow, twist_θ, smul_pow, zpow_dot_self]
  exact smul_comm _ _ _

/-- [Lus] 1.4.2: `r(θᵢ^{(n)}) = Σ_{t + t' = n} vᵢ^{tt'} θᵢ^{(t)} ⊗ θᵢ^{(t')}`. -/
theorem comul_fDivPow (i : I) (n : ℕ) :
    LusztigF.comul D 𝕧 (fDivPow D i n) = ∑ p ∈ antidiagonal n,
      ((𝕧 ^ D.d i) ^ (p.1 * p.2)) • (fDivPow D i p.1 ⊗ₜ[𝕂] fDivPow D i p.2) := by
  have hq0 : 𝕧 ^ D.d i ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  induction n with
  | zero => simp [fDivPow_zero]
  | succ n ih =>
    rw [fDivPow_succ, map_smul, comul_θ_mul, ih, map_sum, map_sum, ← sum_add_distrib]
    simp only [map_smul, LinearMap.rTensor_tmul, map_tmul, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply, θ_mul_fDivPow, twist_fDivPow, tmul_smul, smul_tmul',
      smul_smul, sum_add_distrib]
    set F : ℕ × ℕ → LusztigF 𝕂 I ⊗[𝕂] LusztigF 𝕂 I := fun p ↦
      (((𝕧 ^ D.d i) ^ ((p.1 - 1) * p.2) * qInt (𝕧 ^ D.d i) p.1) • fDivPow D i p.1) ⊗ₜ[𝕂]
        fDivPow D i p.2 with hFdef
    set G : ℕ × ℕ → LusztigF 𝕂 I ⊗[𝕂] LusztigF 𝕂 I := fun p ↦
      ((qInt (𝕧 ^ D.d i) p.2 * ((𝕧 ^ D.d i) ^ (p.1 * (p.2 - 1)) * ((𝕧 ^ D.d i) ^ 2) ^ p.1)) •
        fDivPow D i p.1) ⊗ₜ[𝕂] fDivPow D i p.2 with hGdef
    have hF := Finset.Nat.sum_antidiagonal_succ (f := F) (n := n)
    have hG := Finset.Nat.sum_antidiagonal_succ' (f := G) (n := n)
    simp only [F, G, qInt_zero, mul_zero, zero_mul, zero_smul, zero_tmul, zero_add,
      Nat.add_sub_cancel] at hF hG
    rw [← hF, ← hG, ← sum_add_distrib, smul_sum]
    refine sum_congr rfl fun p hp ↦ ?_
    rw [← add_tmul, ← add_smul, smul_tmul', smul_smul]
    congr 2
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨a, b⟩ := p
    simp only at hp ⊢
    have hc : qInt (𝕧 ^ D.d i) (n + 1) ≠ 0 := qInt_X_ne_zero D i n.succ_pos
    rcases a with _ | a
    · obtain rfl : b = n + 1 := by omega
      simp [inv_mul_cancel₀ hc]
    rcases b with _ | b
    · obtain rfl : a = n := by omega
      simp [inv_mul_cancel₀ hc]
    have h := qInt_add (v := 𝕧 ^ D.d i) (a + 1) (b + 1)
    rw [show a + 1 + (b + 1) = n + 1 by omega] at h
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
    rw [h] at hc
    rw [h]
    generalize 𝕧 ^ D.d i = q at hq0 hc ⊢
    generalize qInt q (a + 1) = A at hc ⊢
    generalize qInt q (b + 1) = B at hc ⊢
    have key : q⁻¹ ^ (b + 1) * q ^ ((a + 1) * (b + 1)) = q ^ (a * (b + 1)) := by
      rw [inv_pow, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero _ hq0), ← pow_add]
      congr 1
      ring
    rw [inv_mul_eq_iff_eq_mul₀ hc]
    linear_combination (-A) * key

/-! ### `r(𝒜'f) ⊆ 𝒜'f ⊗ 𝒜'f` -/

/-- `𝒜'f ⊗ 𝒜'f`, as the `ℤ`-span of the `v^k (x ⊗ y)`, `x`, `y` monomials. -/
def fIntegralTensor : Submodule ℤ (LusztigF 𝕂 I ⊗[𝕂] LusztigF 𝕂 I) :=
  Submodule.span ℤ {X | ∃ (k : ℤ) (w w' : List (I × ℕ)),
    X = (𝕧 ^ k) • (fDivMonomial D w ⊗ₜ[𝕂] fDivMonomial D w')}

lemma zpow_smul_mem_fIntegralTensor (k : ℤ) {X : LusztigF 𝕂 I ⊗[𝕂] LusztigF 𝕂 I}
    (hX : X ∈ fIntegralTensor D) : (𝕧 ^ k) • X ∈ fIntegralTensor D := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨l, w, w', rfl⟩ := hX
    exact Submodule.subset_span ⟨k + l, w, w', by
      rw [smul_smul, ← zpow_add₀ RatFunc.X_ne_zero]⟩
  | zero => simp
  | add X Y _ _ hX hY => rw [smul_add]; exact add_mem hX hY
  | smul c X _ hX =>
    rw [← Int.cast_smul_eq_zsmul 𝕂, smul_comm, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ c hX

lemma twistedMul_mem_fIntegralTensor {X Y : LusztigF 𝕂 I ⊗[𝕂] LusztigF 𝕂 I}
    (hX : X ∈ fIntegralTensor D) (hY : Y ∈ fIntegralTensor D) :
    twistedMul D 𝕧 X Y ∈ fIntegralTensor D := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨k, a, b, rfl⟩ := hX
    induction hY using Submodule.span_induction with
    | mem Y hY =>
      obtain ⟨l, c, d, rfl⟩ := hY
      rw [map_smul, map_smul, LinearMap.smul_apply,
        twistedMul_tmul_tmul D 𝕧 RatFunc.X_ne_zero (fDivMonomial_mem_weightSpace D b)
          (fDivMonomial_mem_weightSpace D c), ← fDivMonomial_append, ← fDivMonomial_append]
      refine zpow_smul_mem_fIntegralTensor D _ (zpow_smul_mem_fIntegralTensor D _
        (zpow_smul_mem_fIntegralTensor D _
          (Submodule.subset_span ⟨0, a ++ c, b ++ d, by simp⟩)))
    | zero => simp
    | add Y Y' _ _ hY hY' => rw [map_add]; exact add_mem hY hY'
    | smul c Y _ hY => rw [map_zsmul]; exact Submodule.smul_mem _ c hY
  | zero => simp
  | add X X' _ _ hX hX' => rw [map_add, LinearMap.add_apply]; exact add_mem hX hX'
  | smul c X _ hX =>
    rw [map_zsmul, LinearMap.smul_apply]; exact Submodule.smul_mem _ c hX

lemma comul_fDivPow_mem (i : I) (n : ℕ) :
    LusztigF.comul D 𝕧 (fDivPow D i n) ∈ fIntegralTensor D := by
  rw [comul_fDivPow]
  refine sum_mem fun p _ ↦ ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← fDivMonomial_singleton,
    ← fDivMonomial_singleton]
  exact Submodule.subset_span ⟨_, _, _, rfl⟩

lemma comul_fDivMonomial_mem (w : List (I × ℕ)) :
    LusztigF.comul D 𝕧 (fDivMonomial D w) ∈ fIntegralTensor D := by
  induction w with
  | nil => exact Submodule.subset_span ⟨0, [], [], by simp⟩
  | cons p w ih =>
    rw [fDivMonomial_cons, comul_mul]
    exact twistedMul_mem_fIntegralTensor D (comul_fDivPow_mem D p.1 p.2) ih

/-- [Lus] 14.2.6 (a): `r(𝒜'f) ⊆ 𝒜'f ⊗ 𝒜'f` (our own proof, from 1.4.2). -/
theorem comul_mem_fIntegralTensor {x : LusztigF 𝕂 I} (hx : x ∈ fIntegral D) :
    LusztigF.comul D 𝕧 x ∈ fIntegralTensor D := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, w, rfl⟩ := hx
    rw [map_smul]
    exact zpow_smul_mem_fIntegralTensor D k (comul_fDivMonomial_mem D w)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ c hx

/-! ### Integrality of the form -/

variable [DecidableEq I] [Finite I]

/-- `(θⱼ^{(m)}, θᵢ^{(t)}) ∈ ℤ[[v⁻¹]]`, by [Lus] 1.4.4. -/
lemma form_fDivPow_fDivPow_mem (i j : I) (m t : ℕ) :
    LusztigF.form D 𝕧 (fDivPow D j m) (fDivPow D i t) ∈ intSeriesInf := by
  by_cases hw : m • Finsupp.single j (1 : ℕ) = t • Finsupp.single i 1
  · have hmt : m = t := by
      simpa using congrArg (fun f : I →₀ ℕ ↦ f.sum fun _ n ↦ n) hw
    subst hmt
    rcases m.eq_zero_or_pos with h0 | hpos
    · subst h0
      rw [fDivPow_zero, fDivPow_zero, form_one_one]; exact one_mem _
    have hji : j = i := by
      have := congrArg (fun f : I →₀ ℕ ↦ f j) hw
      by_contra hne
      simp [hne, hpos.ne'] at this
    subst hji
    have h := quotientForm_integralGenerator D j m
    have hg : quotientIntegralGenerator D j m = toQuotient D 𝕧 (fDivPow D j m) := by
      simp [quotientIntegralGenerator, qDivPow]
    rw [hg, quotientForm_toQuotient] at h
    rw [h]
    exact coefU_mem_intSeriesInf D j m
  · rw [form_eq_zero_of_ne D 𝕧 hw (fDivPow_mem_weightSpace D j m)
      (fDivPow_mem_weightSpace D i t)]
    exact zero_mem _

/-- `(θ_w, θᵢ^{(n)}) ∈ ℤ((v⁻¹)) ∩ ℚ(v)` for a divided-power monomial `θ_w`. -/
lemma form_fDivMonomial_fDivPow_mem (w : List (I × ℕ)) (i : I) (n : ℕ) :
    LusztigF.form D 𝕧 (fDivMonomial D w) (fDivPow D i n) ∈ intLaurentInf := by
  induction w generalizing n with
  | nil =>
    rw [fDivMonomial_nil, LusztigF.form_comm, form_one_right]
    exact intSeriesInf_le_intLaurentInf (counit_fDivPow_mem D i n)
  | cons p w ih =>
    rw [fDivMonomial_cons, form_mul_left, comul_fDivPow, map_sum]
    refine sum_mem fun s _ ↦ ?_
    rw [map_smul, formTensor_tmul, smul_eq_mul]
    refine mul_mem ?_ (mul_mem (intSeriesInf_le_intLaurentInf
      (form_fDivPow_fDivPow_mem D _ _ _ _)) (ih _))
    rw [← pow_mul, ← zpow_natCast]
    exact zpow_X_mem_intLaurentInf _

/-- `(θ_w, θ_{w'}) ∈ ℤ((v⁻¹)) ∩ ℚ(v)` for divided-power monomials. -/
lemma form_fDivMonomial_mem (w w' : List (I × ℕ)) :
    LusztigF.form D 𝕧 (fDivMonomial D w) (fDivMonomial D w') ∈ intLaurentInf := by
  induction w generalizing w' with
  | nil =>
    rw [fDivMonomial_nil, LusztigF.form_comm, form_one_right]
    exact intSeriesInf_le_intLaurentInf (counit_fDivMonomial_mem D w')
  | cons p w ih =>
    rw [fDivMonomial_cons, form_mul_left]
    have key : ∀ X ∈ fIntegralTensor D,
        LusztigF.formTensor D 𝕧 (fDivPow D p.1 p.2 ⊗ₜ fDivMonomial D w) X ∈ intLaurentInf := by
      intro X hX
      induction hX using Submodule.span_induction with
      | mem X hX =>
        obtain ⟨k, a, b, rfl⟩ := hX
        rw [map_smul, formTensor_tmul, smul_eq_mul, LusztigF.form_comm]
        exact mul_mem (zpow_X_mem_intLaurentInf k)
          (mul_mem (form_fDivMonomial_fDivPow_mem D a _ _) (ih b))
      | zero => rw [map_zero]; exact zero_mem _
      | add X Y _ _ hX hY => rw [map_add]; exact add_mem hX hY
      | smul c X _ hX => rw [map_zsmul]; exact zsmul_mem hX c
    exact key _ (comul_fDivMonomial_mem D w')

/-- [Lus] 14.2.6 (b) on `'f`: `(x, y) ∈ ℤ((v⁻¹)) ∩ ℚ(v)` for `x, y ∈ 𝒜'f` (our own proof, from
1.4.2, 1.4.4 and 14.2.6 (a)). -/
theorem form_mem_intLaurentInf {x y : LusztigF 𝕂 I} (hx : x ∈ fIntegral D)
    (hy : y ∈ fIntegral D) : LusztigF.form D 𝕧 x y ∈ intLaurentInf := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, w, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, w', rfl⟩ := hy
      rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
      exact mul_mem (zpow_X_mem_intLaurentInf l)
        (mul_mem (zpow_X_mem_intLaurentInf k) (form_fDivMonomial_mem D w w'))
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy => rw [map_zsmul]; exact zsmul_mem hy c
  | zero => rw [map_zero, LinearMap.zero_apply]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add, LinearMap.add_apply]; exact add_mem hx hz
  | smul c x _ hx => rw [map_zsmul, LinearMap.smul_apply]; exact zsmul_mem hx c

/-! ### Passage to `f` -/

omit [Finite I] in
/-- Every element of the integral form `𝒜f` of `f` lifts to `𝒜'f`. -/
lemma exists_fIntegral_of_mem_quotientIntegralForm {x : Quotient D 𝕧}
    (hx : x ∈ quotientIntegralForm D) : ∃ x' ∈ fIntegral D, toQuotient D 𝕧 x' = x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, n, rfl⟩ := hx
    refine ⟨fDivPow D i n, ?_, by simp [quotientIntegralGenerator, qDivPow]⟩
    exact Submodule.subset_span ⟨0, [(i, n)], by simp⟩
  | algebraMap a =>
    refine ⟨integralLaurentEval a • 1, laurent_smul_mem_fIntegral D a
      (Submodule.subset_span ⟨0, [], by simp⟩), ?_⟩
    rw [map_smul, map_one, Algebra.smul_def, mul_one]
    rfl
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨x' + y', add_mem hx' hy', map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨x' * y', mul_mem_fIntegral D hx' hy', map_mul _ _ _⟩

/-- [Lus] 14.2.6 (b): `(x, y) ∈ ℤ((v⁻¹)) ∩ ℚ(v)` for `x, y` in the integral form `𝒜f` of `f`
(our own proof, see the module docstring). -/
theorem quotientForm_mem_intLaurentInf {x y : Quotient D 𝕧} (hx : x ∈ quotientIntegralForm D)
    (hy : y ∈ quotientIntegralForm D) : quotientForm D x y ∈ intLaurentInf := by
  obtain ⟨x', hx', rfl⟩ := exists_fIntegral_of_mem_quotientIntegralForm D hx
  obtain ⟨y', hy', rfl⟩ := exists_fIntegral_of_mem_quotientIntegralForm D hy
  rw [quotientForm_toQuotient]
  exact form_mem_intLaurentInf D hx' hy'

end LieLean.QuantumGroup
