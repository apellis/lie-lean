/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ChangeOfRings.QuasiClassical
import LieLean.Algebra.QuantumGroup.Frobenius.CartanDatum
import LieLean.Algebra.QuantumGroup.Frobenius.SerreIdentity
import LieLean.Algebra.QuantumGroup.LusztigF.HigherSerre

/-!
# The splitting `Fr' : _F f* → _F f` of the quantum Frobenius map

Let `l ≥ 1`, and let `F` be a field of characteristic zero over `𝒜 = ℤ[v, v⁻¹]` in which the
image `ε` of `v` satisfies `ε^{2l} = 1` and `ε^{2t} ≠ 1` for `0 < t < l` (so `ε²` has order
`l`; this is the field `K` of [Lus] 35.2.1). Let `(I, ∘)` be the Cartan datum attached to `l`
([Lus] 2.2.4, `LusztigCartanDatum.frobenius`), with `lᵢ = frobOrder l i`, and `f*` its algebra.
Then `_F f*` is quasi-classical, and there is a unique `F`-algebra homomorphism
`Fr' : _F f* → _F f` with `θᵢ ↦ θᵢ^{(lᵢ)}`; it maps `θᵢ^{(n)}` to `θᵢ^{(lᵢn)}` ([Lus] Thm.
35.1.8, for the field `F`).

## Main results

* `QuantumGroup.integralGenerator_mul_integralGenerator`: `θᵢ^{(r)} θᵢ^{(s)} = [r+s; r]ᵢ
  θᵢ^{(r+s)}` in `𝒜f`.
* `QuantumGroup.sum_integralGenerator_higherSerre`: [Lus] Prop. 7.1.5 (b) in `𝒜f`.
* `QuantumGroup.baseGen_frobOrder_pow`: `(θᵢ^{(lᵢ)})^n = [n]*ᵢ! θᵢ^{(lᵢn)}` in `_F f`
  ([Lus] 34.1.3).
* `QuantumGroup.sum_baseGen_frobenius_serre`: [Lus] 35.2.3 (b), the Serre relations of `(I, ∘)`
  between the `θᵢ^{(lᵢ)}` in `_F f`.
* `QuantumGroup.frobSplit`: `Fr' : _F f* → _F f` ([Lus] Thm. 35.1.8), with
  `frobSplit_integralGenerator`: `Fr'(θᵢ^{(n)}) = θᵢ^{(lᵢn)}`, and uniqueness `eq_frobSplit`.

## Proof

As in [Lus] 35.2.3: the Serre relations of `(I, ∘)` hold between the `θᵢ^{(lᵢ)}` by the higher
order Serre relations (`QuantumGroup.sum_frobenius_serre`), and `_F f*` is presented by its
Serre relations ([Lus] Prop. 33.2.2 (c), `quasiClassicalEquiv`). Lusztig's assumptions 35.1.2
(a), (b) are not used. The divided powers are matched by [Lus] 34.1.2 (b).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 2.2.4, 7.1.5, 33.2.2,
  34.1.2, 35.1.8, 35.2.1–35.2.3.
-/

open LieLean Finset LusztigF
open scoped TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

universe u

variable {I : Type u} [DecidableEq I] (D : LusztigCartanDatum I)

/-! ### Divided powers and higher order Serre relations in `𝒜f` -/

lemma coe_integralGenerator (i : I) (n : ℕ) :
    (integralGenerator D i n : LusztigF.Quotient D 𝕧) = toQuotient D 𝕧 (fDivPow D i n) := by
  simp [integralGenerator, quotientIntegralGenerator, fDivPow, qDivPow, map_smul, map_pow]

lemma integralLaurentEval_T (z : ℤ) : integralLaurentEval (LaurentPolynomial.T z) = 𝕧 ^ z := by
  simp [integralLaurentEval, LaurentPolynomial.eval₂_T]

@[simp] lemma integralGenerator_zero (i : I) : integralGenerator D i 0 = 1 := by
  apply Subtype.ext
  simp [coe_integralGenerator, fDivPow, qDivPow, qFactorial]

/-- `θᵢ^{(r)} θᵢ^{(s)} = [r+s; r]ᵢ θᵢ^{(r+s)}` in `𝒜f`. -/
lemma integralGenerator_mul_integralGenerator (i : I) (r s : ℕ) :
    integralGenerator D i r * integralGenerator D i s =
      qBinomialU (laurentTUnit (D.d i)) (r + s) r • integralGenerator D i (r + s) := by
  have hT : integralLaurentEval (laurentTUnit (D.d i) : 𝒜) = 𝕧 ^ D.d i := by
    simp [laurentTUnit]
  apply Subtype.ext
  rw [MulMemClass.coe_mul, coe_smul_integralForm, coe_integralGenerator, coe_integralGenerator,
    coe_integralGenerator, ← map_mul, fDivPow_mul_fDivPow, map_smul, map_qBinomialU, hT]

/-- [Lus] Prop. 7.1.5 (b) in `𝒜f`: `f_{i,j;n,m;-1} = 0` for `m > an`. -/
theorem sum_integralGenerator_higherSerre {i j : I} (hij : i ≠ j) (n m : ℕ)
    (h : -D.cartanMatrix i j * n < m) :
    ∑ p ∈ antidiagonal m, ((-1 : 𝒜) ^ p.1 * LaurentPolynomial.T ((-1) * p.1 *
        (-(D.dot i j) * n - D.d i * ((m : ℤ) - 1)))) •
      (integralGenerator D i p.1 * integralGenerator D j n * integralGenerator D i p.2) = 0 := by
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, ← toQuotient_higherSerre hij n m (Or.inr rfl) h, higherSerre,
    map_sum, AddSubmonoidClass.coe_finsetSum]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [coe_smul_integralForm, map_smul, MulMemClass.coe_mul, MulMemClass.coe_mul,
    coe_integralGenerator, coe_integralGenerator, coe_integralGenerator, map_mul, map_mul,
    map_mul, map_pow, map_neg, map_one, integralLaurentEval_T]

/-! ### Base change to a field at a root of `1` -/

variable (F : Type*) [Field F] [Algebra 𝒜 F]

/-- The image `ε` of `v` in `F`. -/
local notation "ε" => algebraMap 𝒜 F (LaurentPolynomial.T 1)

lemma algebraMap_T (z : ℤ) : algebraMap 𝒜 F (LaurentPolynomial.T z) = ε ^ z := by
  have hpow : ∀ m : ℕ, algebraMap 𝒜 F (LaurentPolynomial.T m) = ε ^ m := fun m ↦ by
    rw [← map_pow, LaurentPolynomial.T_pow, mul_one]
  rcases z with m | m
  · simpa using hpow m
  · have h : algebraMap 𝒜 F (LaurentPolynomial.T (Int.negSucc m)) * ε ^ (m + 1) = 1 := by
      rw [← hpow, ← map_mul, ← LaurentPolynomial.T_add, Int.negSucc_eq]
      push_cast
      rw [neg_add_cancel, LaurentPolynomial.T_zero, map_one]
    rw [zpow_negSucc, eq_inv_of_mul_eq_one_left h]

/-- `1 ⊗ θᵢ^{(n)} ∈ _F f`. -/
abbrev baseGen (i : I) (n : ℕ) : F ⊗[𝒜] quotientIntegralForm D :=
  (1 : F) ⊗ₜ integralGenerator D i n

lemma baseGen_mul_baseGen (i : I) (r s : ℕ) :
    baseGen D F i r * baseGen D F i s =
      qBinomial (ε ^ D.d i) (r + s) r • baseGen D F i (r + s) := by
  rw [baseGen, baseGen, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    integralGenerator_mul_integralGenerator, TensorProduct.tmul_smul, ← algebraMap_smul F,
    map_qBinomialU, algebraMap_laurentTUnit]

variable (l : ℕ)

/-- The algebra map `F⟨θᵢ⟩ → _F f`, `θᵢ ↦ θᵢ^{(lᵢ)}`. -/
def frobSplitHom : LusztigF F I →ₐ[F] F ⊗[𝒜] quotientIntegralForm D :=
  FreeAlgebra.lift F fun i ↦ baseGen D F i (D.frobOrder l i)

lemma frobSplitHom_θ (i : I) : frobSplitHom D F l (θ F i) = baseGen D F i (D.frobOrder l i) :=
  FreeAlgebra.lift_ι_apply _ _

variable {F} {l}

section Root

variable (hl0 : 0 < l) (hl : algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (2 * l) = 1)
  (hprim : ∀ t, 0 < t → t < l → algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (2 * t) ≠ 1)
include hl0 hl hprim

omit [DecidableEq I] in
lemma pow_two_mul_eq_one_iff (m : ℕ) : ε ^ (2 * m) = 1 ↔ l ∣ m := by
  constructor
  · intro h
    by_contra hm
    have hmod : ε ^ (2 * (m % l)) = 1 := by
      rw [show 2 * m = 2 * (m % l) + 2 * l * (m / l) by rw [mul_assoc, ← mul_add, Nat.mod_add_div],
        pow_add, pow_mul _ (2 * l), hl, one_pow, mul_one] at h
      exact h
    exact hprim (m % l) (Nat.pos_of_ne_zero fun h0 ↦ hm (Nat.dvd_of_mod_eq_zero h0))
      (Nat.mod_lt _ hl0) hmod
  · rintro ⟨c, rfl⟩
    rw [← mul_assoc, pow_mul, hl, one_pow]

omit [DecidableEq I] hprim in
lemma algebraMap_T_one_ne_zero : ε ≠ 0 := by
  rintro h
  rw [h, zero_pow (by omega)] at hl
  exact zero_ne_one hl

omit [DecidableEq I] in
/-- `qᵢ = ε^{dᵢ}` satisfies `qᵢ^{2lᵢ} = 1`. -/
lemma pow_d_pow_frobOrder (i : I) : (ε ^ D.d i) ^ (2 * D.frobOrder l i) = 1 := by
  rw [← pow_mul, show D.d i * (2 * D.frobOrder l i) = 2 * (D.frobOrder l i * D.d i) by ring,
    pow_two_mul_eq_one_iff hl0 hl hprim]
  exact D.dvd_frobOrder_mul_d hl0 i

omit [DecidableEq I] in
/-- `qᵢ^{2t} ≠ 1` for `0 < t < lᵢ`. -/
lemma pow_d_pow_ne_one (i : I) :
    ∀ t, 0 < t → t < D.frobOrder l i → (ε ^ D.d i) ^ (2 * t) ≠ 1 := by
  intro t ht0 ht h
  rw [← pow_mul, show D.d i * (2 * t) = 2 * (t * D.d i) by ring,
    pow_two_mul_eq_one_iff hl0 hl hprim] at h
  have h' : (D.frobOrder l i : ℤ) ∣ (t : ℤ) :=
    (D.frobOrder_dvd_iff hl0 i t).2 (by exact_mod_cast h)
  exact absurd (Nat.le_of_dvd ht0 (by exact_mod_cast h')) (by omega)

omit [DecidableEq I] in
/-- `(ε^{d*ᵢ})² = 1` for the Cartan datum `(I, ∘)`: `_F f*` is quasi-classical
([Lus] 35.2.1). -/
lemma sq_pow_frobenius_d (i : I) : (ε ^ (D.frobenius hl0).d i) ^ 2 = 1 := by
  rw [D.frobenius_d, ← pow_mul, show D.frobOrder l i ^ 2 * D.d i * 2 =
      2 * (D.frobOrder l i * (D.frobOrder l i * D.d i)) by ring,
    pow_two_mul_eq_one_iff hl0 hl hprim]
  exact (D.dvd_frobOrder_mul_d hl0 i).mul_left _

/-- `(θᵢ^{(lᵢ)})^n = [n]*ᵢ! θᵢ^{(lᵢn)}` in `_F f`, with `[n]*ᵢ!` taken at `ε^{d*ᵢ}`
([Lus] 34.1.3). -/
lemma baseGen_frobOrder_pow (i : I) (n : ℕ) :
    baseGen D F i (D.frobOrder l i) ^ n =
      qFactorial (ε ^ (D.frobenius hl0).d i) n • baseGen D F i (D.frobOrder l i * n) := by
  set L := D.frobOrder l i
  set q := ε ^ D.d i
  have hq : q ≠ 0 := pow_ne_zero _ (algebraMap_T_one_ne_zero hl0 hl)
  have hqL := pow_d_pow_frobOrder D hl0 hl hprim i
  have hqp := pow_d_pow_ne_one D hl0 hl hprim i
  have hL := D.frobOrder_pos hl0 i
  have hstar : ε ^ (D.frobenius hl0).d i = q ^ (L ^ 2) := by
    rw [D.frobenius_d, ← pow_mul, mul_comm]
  have hsq : (q ^ (L ^ 2)) ^ 2 = 1 := hstar ▸ sq_pow_frobenius_d D hl0 hl hprim i
  have hb : ∀ n : ℕ, qBinomial q (L * n + L) (L * n) = (q ^ (L ^ 2)) ^ n * (n + 1 : F) := by
    intro n
    have := qBinomInt_mul_mul hq hqL hqp hL ((n + 1 : ℕ) : ℤ) n
    rw [show (L : ℤ) * ((n + 1 : ℕ) : ℤ) = ((L * n + L : ℕ) : ℤ) by push_cast; ring,
      qBinomInt_natCast, Ring.choose_natCast, Nat.choose_succ_self_right] at this
    rw [this, ← pow_mul, ← zpow_natCast (n := L ^ 2 * n)]
    push_cast
    congr 1
    refine zpow_eq_of_dvd hq hqL ?_
    obtain ⟨c, hc⟩ := Nat.even_mul_succ_self n
    refine ⟨L * c, ?_⟩
    have hc' : ((n : ℤ) * (n + 1)) = c + c := by exact_mod_cast hc
    linear_combination (L : ℤ) ^ 2 * hc'
  induction n with
  | zero => simp [baseGen, Algebra.TensorProduct.one_def, integralGenerator_zero]
  | succ n ih =>
    rw [pow_succ, ih, smul_mul_assoc, baseGen_mul_baseGen, smul_smul, hb, hstar, qFactorial_succ,
      qInt_of_sq_eq_one hsq, show L * n + L = L * (n + 1) by ring]
    congr 1
    push_cast
    ring

/-- **[Lus] 35.2.3 (b)**: the Serre relations of `(I, ∘)` hold between the `θᵢ^{(lᵢ)}` in `_F f`:
`∑_{p + p' = 1 - a*ᵢⱼ} (-1)^p θᵢ^{(lᵢp)} θⱼ^{(lⱼ)} θᵢ^{(lᵢp')} = 0` for `i ≠ j`. -/
theorem sum_baseGen_frobenius_serre {i j : I} (hij : i ≠ j) :
    ∑ p ∈ antidiagonal (1 - (D.frobenius hl0).cartanMatrix i j).toNat, ((-1 : F) ^ p.1) •
      (baseGen D F i (D.frobOrder l i * p.1) * baseGen D F j (D.frobOrder l j) *
        baseGen D F i (D.frobOrder l i * p.2)) = 0 := by
  set L := D.frobOrder l i
  set M := D.frobOrder l j
  set q := algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ D.d i with hqdef
  have hq : q ≠ 0 := pow_ne_zero _ (algebraMap_T_one_ne_zero hl0 hl)
  have hqL := pow_d_pow_frobOrder D hl0 hl hprim i
  have hqp := pow_d_pow_ne_one D hl0 hl hprim i
  have hL := D.frobOrder_pos hl0 i
  have hdi := D.d_pos i
  have ha : D.cartanMatrix i j ≤ 0 := by
    have h1 := D.dot_nonpos i j hij
    rw [← D.d_mul_cartanMatrix] at h1
    by_contra h2
    have : (0 : ℤ) < D.d i * D.cartanMatrix i j := mul_pos (by exact_mod_cast hdi) (by omega)
    omega
  obtain ⟨α, hα⟩ : ∃ α : ℕ, D.cartanMatrix i j = -α := ⟨(-D.cartanMatrix i j).toNat, by omega⟩
  set N := M * α
  have hN : L ∣ N := by
    have h := D.frobOrder_dvd_mul_cartanMatrix hl0 i j
    rw [hα, mul_neg, dvd_neg] at h
    exact_mod_cast h
  have hm : (1 - (D.frobenius hl0).cartanMatrix i j).toNat = N / L + 1 := by
    have h := D.frobOrder_mul_cartanMatrix_frobenius hl0 i j
    obtain ⟨c, hc⟩ := hN
    have hc0 : (M : ℤ) * α = L * c := by exact_mod_cast hc
    have hc' : (L : ℤ) * (D.frobenius hl0).cartanMatrix i j = L * (-c) := by
      rw [h, hα]; linear_combination -hc0
    rw [mul_right_injective₀ (by exact_mod_cast hL.ne' : (L : ℤ) ≠ 0) hc', hc,
      Nat.mul_div_cancel_left _ hL]
    omega
  rw [hm]
  refine sum_frobenius_serre hq hqL hqp hL hN (fun r ↦ baseGen D F i r) (baseGen D F j M)
    (fun r s ↦ baseGen_mul_baseGen D F i r s) fun t ht ↦ ?_
  have h0 := congrArg (fun z ↦ (1 : F) ⊗ₜ[𝒜] z)
    (sum_integralGenerator_higherSerre D hij M (N + L - t)
      (by rw [hα, Nat.cast_sub (by omega)]; push_cast [N]; linarith))
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.tmul_zero] at h0
  rw [← h0]
  refine sum_congr rfl fun p _ ↦ ?_
  have hc : algebraMap 𝒜 F ((-1) ^ p.1 * LaurentPolynomial.T (-1 * p.1 *
      (-(D.dot i j) * M - D.d i * (((N + L - t : ℕ) : ℤ) - 1)))) =
      (-1) ^ p.1 * q ^ ((p.1 : ℤ) * ((L : ℤ) - 1 - t)) := by
    rw [hqdef, map_mul, map_pow, map_neg, map_one, algebraMap_T, ← D.d_mul_cartanMatrix, hα,
      ← zpow_natCast (n := D.d i), ← zpow_mul]
    congr 2
    push_cast [N, Nat.cast_sub (show t ≤ N + L by omega)]
    ring
  rw [show ∀ (c : 𝒜) (x : F ⊗[𝒜] quotientIntegralForm D), c • x = algebraMap 𝒜 F c • x from
    fun c x ↦ (algebraMap_smul F c x).symm, hc, baseGen, baseGen, baseGen,
    Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]

variable [CharZero F]

/-- `θᵢ^{(n)} ↦ θᵢ^{(lᵢn)}` ([Lus] 34.1.2 (b)), before passing to `_F f*`. -/
lemma frobSplitHom_qDivPow (i : I) (n : ℕ) :
    frobSplitHom D F l (qDivPow (algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (D.frobenius hl0).d i) n
      (θ F i)) = baseGen D F i (D.frobOrder l i * n) := by
  rw [qDivPow, map_smul, map_pow, frobSplitHom_θ, baseGen_frobOrder_pow D hl0 hl hprim, smul_smul,
    inv_mul_cancel₀ (qFactorial_ne_zero_of_sq_eq_one (sq_pow_frobenius_d D hl0 hl hprim i) n),
    one_smul]

/-- `θᵢ ↦ θᵢ^{(lᵢ)}` kills the Serre elements of `(I, ∘)` ([Lus] 35.2.3 (b)). -/
theorem frobSplitHom_serreElement {i j : I} (hij : i ≠ j) :
    frobSplitHom D F l
      (serreElement (D.frobenius hl0) (algebraMap 𝒜 F (LaurentPolynomial.T 1)) i j) = 0 := by
  set m := (1 - (D.frobenius hl0).cartanMatrix i j).toNat
  have h := sum_baseGen_frobenius_serre D hl0 hl hprim hij
  have key : ∑ p ∈ antidiagonal m, ((-1 : F) ^ p.2) •
      (baseGen D F i (D.frobOrder l i * p.1) * baseGen D F j (D.frobOrder l j) *
        baseGen D F i (D.frobOrder l i * p.2)) = 0 := by
    rw [← smul_zero ((-1 : F) ^ m), ← h, smul_sum]
    refine sum_congr rfl fun p hp ↦ ?_
    rw [smul_smul]
    congr 1
    have hp' : p.1 + p.2 = m := mem_antidiagonal.1 hp
    rw [← hp', pow_add, mul_comm ((-1 : F) ^ p.1), mul_assoc, ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow, mul_one]
  rw [← Nat.sum_antidiagonal_swap, Nat.sum_antidiagonal_eq_sum_range_succ_mk] at key
  rw [serreElement, qSerreDiv, map_sum]
  simp only [map_smul, map_mul, frobSplitHom_qDivPow D hl0 hl hprim, frobSplitHom_θ]
  simpa using key

lemma frobSplitHom_eq_zero_of_mem {x : LusztigF F I}
    (hx : x ∈ serreIdeal (D.frobenius hl0) (algebraMap 𝒜 F (LaurentPolynomial.T 1))) :
    frobSplitHom D F l x = 0 := by
  classical
  induction hx using TwoSidedIdeal.span_induction with
  | mem y hy =>
    obtain ⟨i, j, hij, rfl⟩ := hy
    exact frobSplitHom_serreElement D hl0 hl hprim hij
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | neg y _ hy => rw [map_neg, hy, neg_zero]
  | left_absorb a y _ hy => rw [map_mul, hy, mul_zero]
  | right_absorb b y _ hy => rw [map_mul, hy, zero_mul]

variable [Finite I]

/-- **[Lus] Thm. 35.1.8** (for the field `F` of 35.2.1): the `F`-algebra homomorphism
`Fr' : _F f* → _F f` with `θᵢ ↦ θᵢ^{(lᵢ)}`, where `f*` is the algebra of the Cartan datum
`(I, ∘)`. -/
def frobSplit :
    F ⊗[𝒜] quotientIntegralForm (D.frobenius hl0) →ₐ[F] F ⊗[𝒜] quotientIntegralForm D :=
  (RingCon.liftₐ (serreIdeal (D.frobenius hl0) (algebraMap 𝒜 F (LaurentPolynomial.T 1))).ringCon
    (frobSplitHom D F l) fun x y h ↦ by
      rw [RingCon.ker_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← sub_eq_zero, ← map_sub]
      exact frobSplitHom_eq_zero_of_mem D hl0 hl hprim ((TwoSidedIdeal.rel_iff _ _ _).1 h)).comp
    (quasiClassicalEquiv (D.frobenius hl0) F (sq_pow_frobenius_d D hl0 hl hprim)).symm.toAlgHom

lemma frobSplit_integralGenerator_one (i : I) :
    frobSplit D hl0 hl hprim ((1 : F) ⊗ₜ integralGenerator (D.frobenius hl0) i 1) =
      baseGen D F i (D.frobOrder l i) := by
  rw [frobSplit, AlgHom.comp_apply, ← quasiClassicalEquiv_θ (D.frobenius hl0) F
    (sq_pow_frobenius_d D hl0 hl hprim) i, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
  exact frobSplitHom_θ D F l i

omit [Finite I] in
/-- `θᵢ^{(n)} = ([n]*ᵢ!)⁻¹ θᵢⁿ` in the quasi-classical `_F f*`. -/
lemma baseGen_eq_smul_pow (i : I) (n : ℕ) :
    (1 : F) ⊗ₜ[𝒜] integralGenerator (D.frobenius hl0) i n =
      (qFactorial (algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (D.frobenius hl0).d i) n)⁻¹ •
        ((1 : F) ⊗ₜ[𝒜] integralGenerator (D.frobenius hl0) i 1) ^ n := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow, integralGenerator_pow, TensorProduct.tmul_smul,
    show ∀ (c : 𝒜) (x : F ⊗[𝒜] quotientIntegralForm (D.frobenius hl0)),
      c • x = algebraMap 𝒜 F c • x from fun c x ↦ (algebraMap_smul F c x).symm,
    map_laurentQFactorial, algebraMap_laurentTUnit, smul_smul,
    inv_mul_cancel₀ (qFactorial_ne_zero_of_sq_eq_one (sq_pow_frobenius_d D hl0 hl hprim i) n),
    one_smul]

/-- **[Lus] Thm. 35.1.8**: `Fr'(θᵢ^{(n)}) = θᵢ^{(lᵢn)}`. -/
theorem frobSplit_integralGenerator (i : I) (n : ℕ) :
    frobSplit D hl0 hl hprim ((1 : F) ⊗ₜ integralGenerator (D.frobenius hl0) i n) =
      baseGen D F i (D.frobOrder l i * n) := by
  have hF := qFactorial_ne_zero_of_sq_eq_one (sq_pow_frobenius_d D hl0 hl hprim i) n
  rw [baseGen_eq_smul_pow D hl0 hl hprim, map_smul, map_pow, frobSplit_integralGenerator_one,
    baseGen_frobOrder_pow D hl0 hl hprim, smul_smul, inv_mul_cancel₀ hF, one_smul]

/-- `Fr'` is the unique `F`-algebra homomorphism `_F f* → _F f` with `θᵢ ↦ θᵢ^{(lᵢ)}`
([Lus] 35.1.8). -/
theorem eq_frobSplit
    (φ : F ⊗[𝒜] quotientIntegralForm (D.frobenius hl0) →ₐ[F] F ⊗[𝒜] quotientIntegralForm D)
    (hφ : ∀ i, φ ((1 : F) ⊗ₜ integralGenerator (D.frobenius hl0) i 1) =
      baseGen D F i (D.frobOrder l i)) :
    φ = frobSplit D hl0 hl hprim := by
  refine AlgHom.ext_of_adjoin_eq_top (adjoin_baseChangeGenerator (D.frobenius hl0) F) ?_
  rintro _ ⟨⟨i, n⟩, rfl⟩
  dsimp only
  rw [baseGen_eq_smul_pow D hl0 hl hprim, map_smul, map_smul, map_pow, map_pow, hφ,
    frobSplit_integralGenerator_one]

end Root

end LieLean.QuantumGroup
