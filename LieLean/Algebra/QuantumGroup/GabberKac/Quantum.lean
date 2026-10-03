/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.GabberKac.Specialization
import LieLean.Algebra.QuantumGroup.GabberKac.VermaOperator
import LieLean.Algebra.QuantumGroup.LusztigF.Form

/-!
# The quantum Shapovalov pairing on `'f`

Let `(I, ·)` be a Cartan datum with Cartan matrix `(aᵢⱼ)`, `k` a field of characteristic zero,
`v ∈ k` nonzero with `vᵢ² ≠ 1` (`vᵢ = v^{dᵢ}`), and `n : I → ℤ` (the values `⟨Λ, αᵢ^∨⟩` of a
highest weight). On a quantum Verma module `M(Λ) = U⁻ v_Λ` the raising operators act by
([Lus] Prop. 3.1.6 (b), with our conventions for `rᵢ`, `ᵢr`):
`Eᵢ (y v_Λ) = ((vᵢ^{nᵢ} σᵢ⁻¹ ᵢr(y) - vᵢ^{-nᵢ} rᵢ(y)) / (vᵢ - vᵢ⁻¹)) v_Λ`, where `σᵢ` is the twist
`θⱼ ↦ v^{i·j} θⱼ` of `'f`. We take this formula as the *definition* of an operator
`LusztigF.vermaOpQ D v n i` on `'f` (no quantum group is needed) and prove:

* it satisfies the recursion `Eᵢ(θⱼ y) = θⱼ Eᵢ(y) + δᵢⱼ [nᵢ - ⟨μ, αᵢ^∨⟩]_{vᵢ} y` for `y ∈ 'f_μ`
  (`LusztigF.vermaOpQ_θ_mul`), i.e. it is the Verma-type operator `LusztigF.vermaOp` with the
  coefficients `[nᵢ - ⟨μ, αᵢ^∨⟩]_{vᵢ}` (`LusztigF.vermaOpQ_eq_vermaOp`); these coefficients are the
  images under `T ↦ v` of the Laurent polynomials `LusztigF.vermaCoeff D n i μ ∈ ℚ[T, T⁻¹]`, which
  specialize at `T = 1` to the classical values `nᵢ - ⟨μ, αᵢ^∨⟩`;
* it preserves the radical of Lusztig's form (`LusztigF.vermaOpQ_mem_radical`), since `rᵢ`, `ᵢr`
  do and the twists `θⱼ ↦ cⱼ θⱼ` are self-adjoint for the form (`LusztigF.form_diagTwist_left`).

Consequently the quantum Shapovalov pairing `S(w, y) = ε(E_w y)` vanishes on the radical in its
second argument (`LusztigF.vermaForm_eq_zero_of_mem_radical`). This is the input to the lower
bound `dim f_ν ≥ dim U(𝔫⁻)_ν` in the quantum Gabber–Kac theorem. The argument is our own
reconstruction.

## Main definitions

* `LusztigF.coPairing D i μ`: `⟨μ, αᵢ^∨⟩ = Σₖ μₖ aᵢₖ`.
* `LusztigF.vermaCoeff D n i μ`: the Laurent polynomial `[nᵢ - ⟨μ, αᵢ^∨⟩]_{T^{dᵢ}}`.
* `LusztigF.evalAt v hv`: evaluation `ℚ[T, T⁻¹] → k`, `T ↦ v`.
* `LusztigF.vermaOpQ D v n i`: the quantum raising operator on `'f`.

## Main results

* `LusztigF.vermaOpQ_θ_mul`, `LusztigF.vermaOpQ_eq_vermaOp`: the recursion.
* `LusztigF.vermaOpQ_mem_radical`, `LusztigF.vermaForm_eq_zero_of_mem_radical`: compatibility
  with the radical of Lusztig's form.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §1.2, §3.1.
-/

noncomputable section

open FreeAlgebra QuantumGroup

namespace LusztigCartanDatum

variable {I : Type*} (D : LusztigCartanDatum I)

/-- `⟨μ, αᵢ^∨⟩ = Σₖ μₖ aᵢₖ` for `μ ∈ ℕ[I]`. -/
def coPairing (i : I) (μ : I →₀ ℕ) : ℤ := μ.sum fun l m ↦ (m : ℤ) * D.cartanMatrix i l

lemma coPairing_single_add (i j : I) (μ : I →₀ ℕ) :
    D.coPairing i (Finsupp.single j 1 + μ) = D.cartanMatrix i j + D.coPairing i μ := by
  rw [coPairing, Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring)]
  simp [coPairing]

@[simp] lemma coPairing_zero (i : I) : D.coPairing i 0 = 0 := by simp [coPairing]

lemma coPairing_wordWeight_cons (i j : I) (w : List I) :
    D.coPairing i (LusztigF.wordWeight (j :: w)) =
      D.cartanMatrix i j + D.coPairing i (LusztigF.wordWeight w) := by
  rw [LusztigF.wordWeight_cons, coPairing_single_add]

/-- `i · μ = dᵢ ⟨μ, αᵢ^∨⟩`. -/
lemma weightDot_single_eq (i : I) (μ : I →₀ ℕ) :
    D.weightDot (Finsupp.single i 1) μ = D.d i * D.coPairing i μ := by
  simp only [LusztigCartanDatum.weightDot, coPairing, Finsupp.mul_sum]
  simp only [CharP.cast_eq_zero, zero_mul, Finsupp.sum_fun_zero, Finsupp.sum_single_index,
    Nat.cast_one, one_mul]
  refine Finsupp.sum_congr fun l _ ↦ ?_
  rw [← D.d_mul_cartanMatrix]; ring

end LusztigCartanDatum

namespace LusztigF

variable {I : Type*} (D : LusztigCartanDatum I)

/-- The unit `T` of `ℚ[T, T⁻¹]`. -/
def laurentT : (LaurentPolynomial ℚ)ˣ := (LaurentPolynomial.isUnit_T 1).unit

/-- The Laurent polynomial `[nᵢ - ⟨μ, αᵢ^∨⟩]_{T^{dᵢ}} ∈ ℚ[T, T⁻¹]`: the coefficient of the Verma
recursion, uniformly in `v` (`LusztigF.vermaOpQ_eq_vermaOp`) and at `v = 1`. -/
def vermaCoeff (n : I → ℤ) (i : I) (μ : I →₀ ℕ) : LaurentPolynomial ℚ :=
  qIntU (laurentT ^ D.d i) (n i - D.coPairing i μ)

variable {k : Type*} [Field k] [CharZero k]

/-- Evaluation `ℚ[T, T⁻¹] → k`, `T ↦ v`, at a nonzero `v`. -/
def evalAt (v : k) (hv : v ≠ 0) : LaurentPolynomial ℚ →+* k :=
  LaurentPolynomial.eval₂ (algebraMap ℚ k) (Units.mk0 v hv)

lemma evalAt_laurentT (v : k) (hv : v ≠ 0) : evalAt v hv (laurentT : LaurentPolynomial ℚ) = v := by
  have : ((laurentT : (LaurentPolynomial ℚ)ˣ) : LaurentPolynomial ℚ) = LaurentPolynomial.T 1 :=
    rfl
  rw [this, evalAt, LaurentPolynomial.eval₂_T, zpow_one, Units.val_mk0]

lemma evalAt_laurentT_pow (v : k) (hv : v ≠ 0) (d : ℕ) :
    evalAt v hv ((laurentT ^ d : (LaurentPolynomial ℚ)ˣ) : LaurentPolynomial ℚ) = v ^ d := by
  rw [Units.val_pow_eq_pow_val, map_pow, evalAt_laurentT]

/-- At `T = 1` the coefficients are the classical ones, `nᵢ - ⟨μ, αᵢ^∨⟩`. -/
lemma evalAt_one_vermaCoeff (n : I → ℤ) (i : I) (μ : I →₀ ℕ) :
    evalAt (1 : ℚ) one_ne_zero (vermaCoeff D n i μ) = ((n i - D.coPairing i μ : ℤ) : ℚ) := by
  rw [vermaCoeff, map_qIntU_of_eq_one]
  rw [evalAt_laurentT_pow, one_pow]

/-! ### Self-adjointness of the twists -/

variable [DecidableEq I] (v : k)

omit [CharZero k] in
/-- The diagonal twists `θⱼ ↦ cⱼ θⱼ` are self-adjoint for Lusztig's form. -/
theorem form_diagTwist_left (c : I → k) (y x : LusztigF k I) :
    form D v (diagTwist c y) x = form D v y (diagTwist c x) := by
  induction y using induction_right generalizing x with
  | algebraMap a => simp
  | smul a y hy => simp [hy]
  | add y z hy hz => simp [hy, hz]
  | mul_θ y j hy =>
    rw [map_mul, diagTwist_θ, mul_smul_comm, map_smul, LinearMap.smul_apply, form_mul_θ, hy,
      form_mul_θ, rDeriv_diagTwist, map_smul, smul_eq_mul]
    ring

omit [CharZero k] in
lemma diagTwist_mem_radical (c : I → k) {x : LusztigF k I} (hx : x ∈ radical D v) :
    diagTwist c x ∈ radical D v := by
  rw [mem_radical_iff']
  intro y
  rw [← form_diagTwist_left, (mem_radical_iff' D v).1 hx]

omit [CharZero k] in
lemma counit_eq_zero_of_mem_radical {x : LusztigF k I} (hx : x ∈ radical D v) : counit x = 0 := by
  rw [← form_one_right D v x]; exact (mem_radical_iff D v).1 hx 1

/-! ### The quantum raising operators -/

omit [CharZero k] [DecidableEq I] in
/-- `vᵢ - vᵢ⁻¹`. -/
abbrev qDenom (i : I) : k := v ^ D.d i - (v ^ D.d i)⁻¹

/-- The quantum raising operator `Eᵢ = (vᵢ^{nᵢ} σᵢ⁻¹ ∘ ᵢr - vᵢ^{-nᵢ} rᵢ)/(vᵢ - vᵢ⁻¹)` on `'f`,
the action of `Eᵢ` on the quantum Verma module of highest weight `n` pulled back to `'f`. -/
def vermaOpQ (n : I → ℤ) (i : I) : Module.End k (LusztigF k I) :=
  (qDenom D v i)⁻¹ • ((v ^ D.d i) ^ n i • ((twist D v⁻¹ i).toLinearMap ∘ₗ lDeriv D v i) -
    ((v ^ D.d i) ^ n i)⁻¹ • rDeriv D v i)

omit [CharZero k] in
lemma vermaOpQ_apply (n : I → ℤ) (i : I) (y : LusztigF k I) :
    vermaOpQ D v n i y = (qDenom D v i)⁻¹ • ((v ^ D.d i) ^ n i • twist D v⁻¹ i (lDeriv D v i y) -
      ((v ^ D.d i) ^ n i)⁻¹ • rDeriv D v i y) := rfl

variable {v}

omit [CharZero k] in
/-- The recursion `Eᵢ(θⱼ y) = θⱼ Eᵢ(y) + δᵢⱼ [nᵢ - ⟨μ, αᵢ^∨⟩]_{vᵢ} y` for `y ∈ 'f_μ`, with the
quantum integer written as `(vᵢ^N - vᵢ^{-N})/(vᵢ - vᵢ⁻¹)`. -/
theorem vermaOpQ_θ_mul (hv : v ≠ 0) (n : I → ℤ) (i j : I) {μ : I →₀ ℕ} {y : LusztigF k I}
    (hy : y ∈ weightSpace k μ) :
    vermaOpQ D v n i (θ k j * y) = θ k j * vermaOpQ D v n i y +
      if i = j then ((qDenom D v i)⁻¹ * ((v ^ D.d i) ^ (n i - D.coPairing i μ) -
        (v ^ D.d i) ^ (-(n i - D.coPairing i μ)))) • y else 0 := by
  have hvd : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  have hσ : twist D v⁻¹ i y = (v ^ D.d i) ^ (-D.coPairing i μ) • y := by
    rw [twist_of_mem (inv_ne_zero hv) i hy, D.weightDot_single_eq, inv_zpow', zpow_neg,
      zpow_neg, zpow_mul, zpow_natCast]
  have hσ' : twist D v i y = (v ^ D.d i) ^ D.coPairing i μ • y := by
    rw [twist_of_mem hv i hy, D.weightDot_single_eq, zpow_mul, zpow_natCast]
  rw [vermaOpQ_apply, vermaOpQ_apply, lDeriv_θ_mul, rDeriv_θ_mul, map_add, map_smul, map_mul,
    twist_θ]
  have e1 : v ^ D.dot i j • ((v⁻¹ ^ D.dot i j • θ k j) * twist D v⁻¹ i (lDeriv D v i y)) =
      θ k j * twist D v⁻¹ i (lDeriv D v i y) := by
    rw [smul_mul_assoc, smul_smul, inv_zpow', ← zpow_add₀ hv, add_neg_cancel, zpow_zero, one_smul]
  rw [e1]
  split_ifs with hij
  · subst hij
    rw [hσ, hσ']
    simp only [smul_add, mul_smul_comm, mul_sub, smul_sub, smul_smul]
    rw [zpow_sub₀ hvd, zpow_neg, zpow_neg, zpow_sub₀ hvd, inv_div]
    module
  · simp only [map_zero, zero_add, add_zero, smul_sub, mul_sub, mul_smul_comm]

omit [CharZero k] in
/-- The quantum raising operators preserve the radical of Lusztig's form. -/
theorem vermaOpQ_mem_radical (n : I → ℤ) {i : I} (hi : (v ^ D.d i) ^ 2 ≠ 1)
    {y : LusztigF k I} (hy : y ∈ radical D v) : vermaOpQ D v n i y ∈ radical D v := by
  have hθ := thetaNorm_ne_zero D v hi
  have hsm : ∀ (c : k) {z : LusztigF k I}, z ∈ radical D v → c • z ∈ radical D v :=
    fun c z hz ↦ by rw [Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hz
  rw [vermaOpQ_apply, twist_eq_diagTwist]
  exact hsm _ (TwoSidedIdeal.sub_mem _
    (hsm _ (diagTwist_mem_radical D v _ (lDeriv_mem_radical D v hθ hy)))
    (hsm _ (rDeriv_mem_radical D v hθ hy)))

omit [DecidableEq I] in
/-- The quantum coefficient `[nᵢ - ⟨μ, αᵢ^∨⟩]_{vᵢ}` is the image of `vermaCoeff D n i μ` under
`T ↦ v`. -/
lemma evalAt_vermaCoeff (hv : v ≠ 0) {i : I} (hi : qDenom D v i ≠ 0) (n : I → ℤ)
    (μ : I →₀ ℕ) :
    evalAt v hv (vermaCoeff D n i μ) = (qDenom D v i)⁻¹ *
      ((v ^ D.d i) ^ (n i - D.coPairing i μ) - (v ^ D.d i) ^ (-(n i - D.coPairing i μ))) := by
  have h := sub_mul_map_qIntU (laurentT ^ D.d i) (evalAt v hv) (n i - D.coPairing i μ)
  rw [evalAt_laurentT_pow] at h
  rw [vermaCoeff, eq_inv_mul_iff_mul_eq₀ hi]
  exact h

omit [DecidableEq I] [CharZero k] in
lemma wordSpan_eq_weightSpace (μ : I →₀ ℕ) : wordSpan k μ = weightSpace k μ := rfl

/-- The quantum raising operator `Eᵢ` is the Verma-type operator with coefficients
`[nᵢ - ⟨μ, αᵢ^∨⟩]_{vᵢ}`. -/
theorem vermaOpQ_eq_vermaOp (hv : v ≠ 0) (n : I → ℤ) {i : I} (hi : qDenom D v i ≠ 0) :
    vermaOpQ D v n i = vermaOp i fun μ ↦ evalAt v hv (vermaCoeff D n i μ) := by
  refine (wordBasis k I).ext fun w ↦ ?_
  induction w with
  | nil =>
    rw [vermaOp_wordBasis, wordBasis_nil, vermaOpQ_apply]
    simp [vermaOpWord]
  | cons j w ih =>
    have hw : wordBasis k I w ∈ weightSpace k (wordWeight w) := wordBasis_mem_wordSpan w
    rw [← ι_mul_wordBasis, vermaOp_ι_mul, ← ih, weightScale_wordBasis]
    erw [vermaOpQ_θ_mul D hv n i j hw]
    rw [evalAt_vermaCoeff D hv hi]

/-- The quantum Shapovalov pairing `S(w, y) = ε(E_w y)` on `'f` (with the Verma-type operators of
`LusztigF.vermaOpQ_eq_vermaOp`) vanishes when `y` lies in the radical of Lusztig's form. -/
theorem vermaForm_eq_zero_of_mem_radical (hv : v ≠ 0) (hv' : ∀ i, (v ^ D.d i) ^ 2 ≠ 1)
    (n : I → ℤ) (w : List I) {y : LusztigF k I} (hy : y ∈ radical D v) :
    vermaForm (fun i μ ↦ evalAt v hv (vermaCoeff D n i μ)) w y = 0 := by
  have hq : ∀ i, qDenom D v i ≠ 0 := fun i h0 ↦ by
    have hvd : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
    apply hv' i
    rw [qDenom, sub_eq_zero] at h0
    field_simp at h0
    exact h0
  suffices h : ∀ w (y : LusztigF k I), y ∈ radical D v →
      vermaWordOp (fun i μ ↦ evalAt v hv (vermaCoeff D n i μ)) w y ∈ radical D v by
    rw [vermaForm_apply]
    exact counit_eq_zero_of_mem_radical D v (h w y hy)
  intro w
  induction w with
  | nil => intro y hy; exact hy
  | cons i w ih =>
    intro y hy
    rw [vermaWordOp_cons]
    refine ih _ ?_
    rw [← vermaOpQ_eq_vermaOp D hv n (hq i)]
    exact vermaOpQ_mem_radical D n (hv' i) hy

end LusztigF
