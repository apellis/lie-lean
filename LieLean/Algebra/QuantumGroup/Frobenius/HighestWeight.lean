/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Frobenius.DividedPowerCommutation
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.HighestWeightInnerProduct
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorLattice

/-!
# The form of a highest weight module on `_F f` at a root of `1`

Let `λ` be a dominant weight and `( , )` the contravariant form of `Λ_λ = L_q(λ)` over `ℚ(v)` with
`(η, η) = 1`. On `𝒜f` the pairing `(x, y) ↦ (x⁻η, y⁻η)` takes values in `𝒜`
(`isLaurent_formL`); we write `frobPair` for this `𝒜`-bilinear form, `frobPairBase` for its
base change to `_F f = F ⊗_𝒜 𝒜f` and `frobRad` for the left radical of `frobPairBase`. In
[Lus] 35.3.2 the corresponding objects are the module `_F Λ_λ` and the annihilator of its
highest weight vector; the form lets us work in `_F f` directly.

## Main results

* `QuantumGroup.frobPair`: the `𝒜`-valued form on `𝒜f`, with
  `integralLaurentEval_frobPair : (frobPair x y : ℚ(v)) = (x⁻η, y⁻η)`.
* `QuantumGroup.mul_mem_frobRad`: `frobRad` is a left ideal of `_F f`.
* `QuantumGroup.baseGen_one_mem_frobRad`: if `lᵢ ≥ 2` and `lᵢ ∣ ⟨i, λ⟩`, then `θᵢ ∈ frobRad`
  (the image of `θᵢ⁻` annihilates the highest weight vector, cf. [Lus] 35.3.2 (b)).

## Proof

`(θᵢ x⁻η, y⁻η)`: by contravariance `ρ(y⁻)Fᵢη` is, modulo multiples of `Fᵢη` (which are
orthogonal to `η`), a multiple of `[⟨i, λ⟩]ᵢ` times an element of `V_ℤ(λ)`, since
`EᵢFᵢη = [⟨i, λ⟩]ᵢ η`. The quantum integer `[⟨i, λ⟩]ᵢ` vanishes at `vᵢ = ε^{dᵢ}` when
`lᵢ ∣ ⟨i, λ⟩` and `lᵢ ≥ 2`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 19.1.2, 19.3.3, 35.2.1,
  35.3.2.
-/

open LieLean Finset LusztigF
open scoped TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular) (Λ : Dom R)

/-! ### The form `frobPair` on `𝒜f` -/

section Pair

lemma quotientMinus_smul_hwv_mem_hwIntegral {z : Quotient D 𝕧}
    (hz : z ∈ quotientIntegralForm D) :
    quotientMinus R z • IrreducibleModule.hwv R 𝕧 Λ.1 ∈ hwIntegral Λ := by
  refine ⟨(negativeQuotientEquiv D).symm z, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_negIntegral, LinearEquiv.apply_symm_apply]; exact hz
  · rw [evq_eq_quotientMinus_smul, LinearEquiv.apply_symm_apply]

lemma isLaurent_frobPair (x y : quotientIntegralForm D) :
    Modified.IsLaurent (formL hvt hR Λ
      (quotientMinus R (x : Quotient D 𝕧) • IrreducibleModule.hwv R 𝕧 Λ.1)
      (quotientMinus R (y : Quotient D 𝕧) • IrreducibleModule.hwv R 𝕧 Λ.1)) :=
  isLaurent_formL hR Λ (quotientMinus_smul_hwv_mem_hwIntegral Λ x.2)
    (quotientMinus_smul_hwv_mem_hwIntegral Λ y.2)

/-- The values of `frobPair`. -/
def frobPairFun (x y : quotientIntegralForm D) : 𝒜 :=
  (isLaurent_frobPair hR Λ x y).choose

lemma integralLaurentEval_frobPairFun (x y : quotientIntegralForm D) :
    integralLaurentEval (frobPairFun hR Λ x y) =
      formL hvt hR Λ (quotientMinus R (x : Quotient D 𝕧) • IrreducibleModule.hwv R 𝕧 Λ.1)
        (quotientMinus R (y : Quotient D 𝕧) • IrreducibleModule.hwv R 𝕧 Λ.1) :=
  (isLaurent_frobPair hR Λ x y).choose_spec

/-- The `𝒜`-valued form `(x, y) ↦ (x⁻η, y⁻η)` on `𝒜f`. -/
def frobPair : LinearMap.BilinForm 𝒜 (quotientIntegralForm D) :=
  LinearMap.mk₂ 𝒜 (frobPairFun hR Λ)
    (fun x x' y ↦ integralLaurentEval_injective (by
      simp only [map_add, integralLaurentEval_frobPairFun, Subalgebra.coe_add, add_smul,
        LinearMap.add_apply]))
    (fun c x y ↦ integralLaurentEval_injective (by
      rw [smul_eq_mul, map_mul, integralLaurentEval_frobPairFun, integralLaurentEval_frobPairFun,
        coe_smul_integralForm, map_smul (quotientMinus R), smul_assoc, LinearMap.map_smul₂,
        smul_eq_mul]))
    (fun x y y' ↦ integralLaurentEval_injective (by
      simp only [map_add, integralLaurentEval_frobPairFun, Subalgebra.coe_add, add_smul]))
    (fun c x y ↦ integralLaurentEval_injective (by
      rw [smul_eq_mul, map_mul, integralLaurentEval_frobPairFun, integralLaurentEval_frobPairFun,
        coe_smul_integralForm, map_smul (quotientMinus R), smul_assoc, LinearMap.map_smul,
        smul_eq_mul]))

lemma integralLaurentEval_frobPair (x y : quotientIntegralForm D) :
    integralLaurentEval (frobPair hR Λ x y) =
      formL hvt hR Λ (quotientMinus R (x : Quotient D 𝕧) • IrreducibleModule.hwv R 𝕧 Λ.1)
        (quotientMinus R (y : Quotient D 𝕧) • IrreducibleModule.hwv R 𝕧 Λ.1) :=
  integralLaurentEval_frobPairFun hR Λ x y

/-- Left multiplication by `z ∈ 𝒜f` has an adjoint for `frobPair`: `(zx, y) = (x, w)`. -/
lemma exists_frobPair_mul_left (z y : quotientIntegralForm D) :
    ∃ w : quotientIntegralForm D, ∀ x, frobPair hR Λ (z * x) y = frobPair hR Λ x w := by
  obtain ⟨n, hn, hw⟩ := rho_quotientMinus_smul_mem_hwIntegral hR Λ z.2
    (quotientMinus_smul_hwv_mem_hwIntegral Λ y.2)
  rw [evq_eq_quotientMinus_smul] at hw
  refine ⟨⟨negativeQuotientEquiv D n, hn⟩, fun x ↦ integralLaurentEval_injective ?_⟩
  rw [integralLaurentEval_frobPair, integralLaurentEval_frobPair, Subalgebra.coe_mul, map_mul,
    mul_smul, IrreducibleModule.isContravariant_form hR (pow_ne_one_of_transcendental' hvt), ← hw]

end Pair

/-! ### `θᵢ` pairs into `[⟨i, λ⟩]ᵢ 𝒜` -/

section Theta

omit [Finite I] in
/-- `Eⱼ Fᵢ η = δᵢⱼ [⟨i, λ⟩]ᵢ η`. -/
lemma E_smul_F_smul_hwv (i j : I) :
    E R 𝕧 j • F R 𝕧 i • IrreducibleModule.hwv R 𝕧 Λ.1 =
      if j = i then qInt (𝕧 ^ D.d i) (Λ.1 (R.coroot i)).toNat • IrreducibleModule.hwv R 𝕧 Λ.1
      else 0 := by
  have hη := IrreducibleModule.E_smul_hwv (R := R) (v := 𝕧) (Λ := Λ.1) j
  rw [← mul_smul, ← sub_add_cancel (E R 𝕧 j * F R 𝕧 i) (F R 𝕧 i * E R 𝕧 j), add_smul,
    mul_smul (F R 𝕧 i), hη, smul_zero, add_zero, E_mul_F_sub]
  split_ifs with h
  · subst h
    have hq : 𝕧 ^ D.d j - (𝕧 ^ D.d j)⁻¹ ≠ 0 :=
      sub_inv_ne_zero_of_pow_ne_one (pow_ne_zero _ (NeZero.ne _)) fun n hn ↦ by
        rw [← pow_mul]
        exact pow_ne_one_of_transcendental' hvt _ (Nat.mul_pos (D.d_pos j) hn)
    have hN : Λ.1 (ktilde R j) = (D.d j : ℤ) * ((Λ.1 (R.coroot j)).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (Λ.2 j), ktilde, map_nsmul, nsmul_eq_mul]
    have key : (𝕧 ^ D.d j - (𝕧 ^ D.d j)⁻¹)⁻¹ *
        ((𝕧 ^ D.d j) ^ (Λ.1 (R.coroot j)).toNat - ((𝕧 ^ D.d j) ^ (Λ.1 (R.coroot j)).toNat)⁻¹) =
        qInt (𝕧 ^ D.d j) (Λ.1 (R.coroot j)).toNat := by
      rw [inv_mul_eq_iff_eq_mul₀ hq, qInt_mul_sub (v := 𝕧 ^ D.d j), inv_pow]
    rw [smul_assoc, sub_smul, Kt, hw_K_smul_hwv, hw_K_smul_hwv, map_neg, ← sub_smul, smul_smul,
      hN, zpow_neg, zpow_mul, zpow_natCast, zpow_natCast, key]
  · rw [zero_smul]

omit [Finite I] in
/-- `ρ(Fⱼ) Fᵢ η = δᵢⱼ vᵢ^{1-⟨i,λ⟩} [⟨i, λ⟩]ᵢ η`. -/
lemma rhoF_smul_F_smul_hwv (i j : I) :
    rhoF R 𝕧 j • F R 𝕧 i • IrreducibleModule.hwv R 𝕧 Λ.1 =
      if j = i then (𝕧 ^ ((D.d i : ℤ) - D.d i * (Λ.1 (R.coroot i)).toNat) *
        qInt (𝕧 ^ D.d i) (Λ.1 (R.coroot i)).toNat) • IrreducibleModule.hwv R 𝕧 Λ.1
      else 0 := by
  rw [rhoF, smul_assoc, mul_smul, E_smul_F_smul_hwv]
  split_ifs with h
  · subst h
    have hN : Λ.1 (-ktilde R j) = -((D.d j : ℤ) * ((Λ.1 (R.coroot j)).toNat : ℤ)) := by
      rw [map_neg, Int.toNat_of_nonneg (Λ.2 j), ktilde, map_nsmul, nsmul_eq_mul]
    rw [smul_comm (K R 𝕧 (-ktilde R j)) (qInt (𝕧 ^ D.d j) _), hw_K_smul_hwv, hN, smul_smul,
      smul_smul, sub_eq_add_neg, zpow_add₀ (NeZero.ne _), zpow_natCast]
    ring_nf
  · rw [smul_zero, smul_zero]

omit [Finite I] in
lemma integralLaurentEval_qNatU (d N : ℕ) :
    integralLaurentEval (qNatU (laurentTUnit d) N) = qInt (𝕧 ^ d) N := by
  rw [map_qNatU]
  congr 1
  change integralLaurentEval (LaurentPolynomial.T (d : ℤ)) = _
  rw [integralLaurentEval_T, zpow_natCast]

omit [Finite I] in
lemma laurent_smul_comm (u : QuantumGroup R 𝕧) (c : 𝒜) (m : IrreducibleModule R 𝕧 Λ.1) :
    u • c • m = c • u • m := by
  rw [hw_laurent_smul_eq, hw_laurent_smul_eq, smul_algebra_smul_comm]

include hR in
/-- For `y ∈ 𝒜f`, `ρ(y⁻) Fᵢ η ∈ [⟨i, λ⟩]ᵢ V_ℤ(λ) + 𝒜 Fᵢ η`. -/
lemma exists_rho_quotientMinus_smul_F_smul_hwv (i : I) {y : Quotient D 𝕧}
    (hy : y ∈ quotientIntegralForm D) :
    ∃ m ∈ hwIntegral Λ, ∃ a : 𝒜,
      rho R 𝕧 (quotientMinus R y) • F R 𝕧 i • IrreducibleModule.hwv R 𝕧 Λ.1 =
        qNatU (laurentTUnit (D.d i)) (Λ.1 (R.coroot i)).toNat • m +
          a • F R 𝕧 i • IrreducibleModule.hwv R 𝕧 Λ.1 := by
  set c := qNatU (laurentTUnit (D.d i)) (Λ.1 (R.coroot i)).toNat
  set φ := F R 𝕧 i • IrreducibleModule.hwv R 𝕧 Λ.1
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨j, n, rfl⟩ := hz
    rw [quotientIntegralGenerator, map_qDivPow', quotientMinus_θ, qDivPow, map_smul, rho_pow,
      rho_F, smul_assoc]
    rcases n with _ | n
    · exact ⟨0, zero_mem _, 1, by simp [qFactorial]⟩
    rw [pow_succ, mul_smul, rhoF_smul_F_smul_hwv]
    split_ifs with h
    · subst h
      rcases n with _ | n
      · refine ⟨LaurentPolynomial.T ((D.d j : ℤ) - D.d j * (Λ.1 (R.coroot j)).toNat) •
          IrreducibleModule.hwv R 𝕧 Λ.1, Submodule.smul_mem _ _ (hwv_mem_hwIntegral Λ), 0, ?_⟩
        rw [zero_smul, add_zero, hw_laurent_smul_eq, hw_laurent_smul_eq, integralLaurentEval_T,
          integralLaurentEval_qNatU]
        simp [qFactorial, qInt, smul_smul, mul_comm]
      · refine ⟨0, zero_mem _, 0, ?_⟩
        rw [smul_zero, zero_smul, add_zero, pow_succ, mul_smul,
          smul_comm (rhoF R 𝕧 j) (_ : 𝕂), rhoF_smul_hwv, smul_zero, smul_zero, smul_zero]
    · exact ⟨0, zero_mem _, 0, by simp⟩
  | algebraMap c' =>
    refine ⟨0, zero_mem _, c', ?_⟩
    rw [show algebraMap 𝒜 (Quotient D 𝕧) c' =
      algebraMap 𝕂 (Quotient D 𝕧) (integralLaurentEval c') from rfl, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, map_smul, rho_one, smul_assoc, one_smul,
      ← hw_laurent_smul_eq, smul_zero, zero_add]
  | add a b _ _ ha hb =>
    obtain ⟨m₁, hm₁, a₁, h₁⟩ := ha
    obtain ⟨m₂, hm₂, a₂, h₂⟩ := hb
    refine ⟨m₁ + m₂, add_mem hm₁ hm₂, a₁ + a₂, ?_⟩
    rw [map_add, map_add, add_smul, h₁, h₂, smul_add, add_smul]
    abel
  | mul a b _ hb' ha hb =>
    obtain ⟨m₁, hm₁, a₁, h₁⟩ := ha
    obtain ⟨m₂, hm₂, a₂, h₂⟩ := hb
    refine ⟨rho R 𝕧 (quotientMinus R b) • m₁ + a₁ • m₂,
      add_mem (rho_quotientMinus_smul_mem_hwIntegral hR Λ hb' hm₁) (Submodule.smul_mem _ _ hm₂),
      a₁ * a₂, ?_⟩
    rw [map_mul, rho_mul, mul_smul, h₁, smul_add, laurent_smul_comm, laurent_smul_comm, h₂,
      smul_add, smul_add, smul_comm a₁ c, smul_smul, add_assoc, smul_smul a₁ a₂]

/-- `(θᵢ, y) ∈ [⟨i, λ⟩]ᵢ 𝒜` for `y ∈ 𝒜f`. -/
theorem exists_frobPair_integralGenerator_one_eq (i : I) (y : quotientIntegralForm D) :
    ∃ a : 𝒜, frobPair hR Λ (integralGenerator D i 1) y =
      qNatU (laurentTUnit (D.d i)) (Λ.1 (R.coroot i)).toNat * a := by
  obtain ⟨m, hm, a, h⟩ := exists_rho_quotientMinus_smul_F_smul_hwv hR Λ i y.2
  obtain ⟨b, hb⟩ := isLaurent_formL_hwv hR Λ hm
  refine ⟨b, integralLaurentEval_injective ?_⟩
  have hθ : quotientMinus R (integralGenerator D i 1 : Quotient D 𝕧) = F R 𝕧 i := by
    change quotientMinus R (quotientIntegralGenerator D i 1) = F R 𝕧 i
    rw [quotientIntegralGenerator, map_qDivPow', quotientMinus_θ]
    simp [qDivPow, qFactorial, qInt]
  rw [integralLaurentEval_frobPair, map_mul, hb, hθ, IrreducibleModule.form_comm,
    IrreducibleModule.isContravariant_form hR (pow_ne_one_of_transcendental' hvt), h, map_add,
    hw_laurent_smul_eq (m := m), hw_laurent_smul_eq (m := F R 𝕧 i • _), map_smul, map_smul,
    IrreducibleModule.form_hwv_F_smul, smul_zero, add_zero, smul_eq_mul]

end Theta

/-! ### The radical of the form on `_F f` -/

section Radical

variable (F : Type*) [Field F] [Algebra 𝒜 F]

/-- The form `frobPair` on `_F f = F ⊗_𝒜 𝒜f`. -/
def frobPairBase : LinearMap.BilinForm F (F ⊗[𝒜] quotientIntegralForm D) :=
  (frobPair hR Λ).baseChange F

/-- The left radical of `frobPairBase`. -/
def frobRad : Submodule F (F ⊗[𝒜] quotientIntegralForm D) :=
  LinearMap.ker (frobPairBase hR Λ F)

lemma frobPairBase_tmul (a b : F) (x y : quotientIntegralForm D) :
    frobPairBase hR Λ F (a ⊗ₜ x) (b ⊗ₜ y) = algebraMap 𝒜 F (frobPair hR Λ x y) * (a * b) := by
  rw [frobPairBase, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]

lemma mem_frobRad_iff (X : F ⊗[𝒜] quotientIntegralForm D) :
    X ∈ frobRad hR Λ F ↔ ∀ y, frobPairBase hR Λ F X (1 ⊗ₜ y) = 0 := by
  refine ⟨fun h y ↦ by rw [frobRad, LinearMap.mem_ker] at h; rw [h, LinearMap.zero_apply],
    fun h ↦ ?_⟩
  rw [frobRad, LinearMap.mem_ker]
  refine LinearMap.ext fun Z ↦ ?_
  induction Z using TensorProduct.inductionOn with
  | tmul b y =>
    rw [show b ⊗ₜ[𝒜] y = b • ((1 : F) ⊗ₜ[𝒜] y) by rw [TensorProduct.smul_tmul', smul_eq_mul,
      mul_one], map_smul, h, smul_zero, LinearMap.zero_apply]
  | add Z Z' hZ hZ' => rw [map_add, hZ, hZ', map_add]

/-- `frobRad` is a left ideal of `_F f`. -/
theorem mul_mem_frobRad (Z : F ⊗[𝒜] quotientIntegralForm D) {X : F ⊗[𝒜] quotientIntegralForm D}
    (hX : X ∈ frobRad hR Λ F) : Z * X ∈ frobRad hR Λ F := by
  induction Z using TensorProduct.inductionOn with
  | tmul a z =>
    rw [show a ⊗ₜ[𝒜] z = a • ((1 : F) ⊗ₜ[𝒜] z) by rw [TensorProduct.smul_tmul', smul_eq_mul,
      mul_one], smul_mul_assoc]
    refine Submodule.smul_mem _ _ ((mem_frobRad_iff hR Λ F _).2 fun y ↦ ?_)
    obtain ⟨w, hw⟩ := exists_frobPair_mul_left hR Λ z y
    have key : ∀ X : F ⊗[𝒜] quotientIntegralForm D,
        frobPairBase hR Λ F ((1 ⊗ₜ z) * X) (1 ⊗ₜ y) = frobPairBase hR Λ F X (1 ⊗ₜ w) := by
      intro X
      induction X using TensorProduct.inductionOn with
      | tmul b x =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, frobPairBase_tmul, frobPairBase_tmul,
          hw x]
      | add X X' h h' => rw [mul_add, map_add, map_add, LinearMap.add_apply,
          LinearMap.add_apply, h, h']
    rw [key, (mem_frobRad_iff hR Λ F X).1 hX w]
  | add Z Z' hZ hZ' => rw [add_mul]; exact add_mem hZ hZ'

omit [Finite I] [DecidableEq I] [Algebra 𝒜 F] in
/-- `[N]_q = 0` when `q² ≠ 1` and `q^{2N} = 1`. -/
lemma qInt_eq_zero_of_pow_eq_one {q : F} (hq0 : q ≠ 0) (hq2 : q ^ 2 ≠ 1) {N : ℕ}
    (hN : q ^ (2 * N) = 1) : qInt q N = 0 := by
  have hq : q - q⁻¹ ≠ 0 := by
    intro h
    apply hq2
    rw [sub_eq_zero] at h
    rw [sq]
    nth_rw 2 [h]
    exact mul_inv_cancel₀ hq0
  have hNN : q ^ N - q⁻¹ ^ N = 0 := by
    rw [inv_pow, sub_eq_zero]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_add, ← two_mul, hN])
  have h := qInt_mul_sub (v := q) N
  rw [hNN] at h
  exact (mul_eq_zero.1 h).resolve_left hq

variable {F} {l : ℕ} (hl0 : 0 < l) (hl : algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (2 * l) = 1)
  (hprim : ∀ t, 0 < t → t < l → algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ (2 * t) ≠ 1)
include hl0 hl hprim

/-- If `lᵢ ≥ 2` and `lᵢ ∣ ⟨i, λ⟩`, then `θᵢ` lies in the radical: in the specialization of
`Λ_λ` the vector `θᵢ⁻η` is orthogonal to everything (cf. [Lus] 35.3.2 (b)). -/
theorem baseGen_one_mem_frobRad (i : I) (hi : 2 ≤ D.frobOrder l i)
    (hΛ : D.frobOrder l i ∣ (Λ.1 (R.coroot i)).toNat) :
    baseGen D F i 1 ∈ frobRad hR Λ F := by
  rw [mem_frobRad_iff]
  intro y
  obtain ⟨a, ha⟩ := exists_frobPair_integralGenerator_one_eq hR Λ i y
  have hq0 : algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ D.d i ≠ 0 :=
    pow_ne_zero _ (algebraMap_T_one_ne_zero hl0 hl)
  have hq2 := pow_d_pow_ne_one D hl0 hl hprim i 1 one_pos (by omega)
  rw [mul_one] at hq2
  obtain ⟨c, hc⟩ := hΛ
  have hN : (algebraMap 𝒜 F (LaurentPolynomial.T 1) ^ D.d i) ^ (2 * (Λ.1 (R.coroot i)).toNat) =
      1 := by
    rw [hc, ← mul_assoc, pow_mul, pow_d_pow_frobOrder D hl0 hl hprim i, one_pow]
  rw [baseGen, frobPairBase_tmul, ha, map_mul, map_qNatU, algebraMap_laurentTUnit,
    qInt_eq_zero_of_pow_eq_one F hq0 hq2 hN, zero_mul, zero_mul]

end Radical

end LieLean.QuantumGroup
