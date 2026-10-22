/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ChangeOfRings.Basic
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.CanonicalTriangular
import LieLean.Algebra.QuantumGroup.QuasiR.Basic

/-!
# The maps `(x, x') ↦ x⁻ 1_λ x'⁺` on `f`, `𝒜f` and `_S f`

Over `ℚ(v)`, for `λ ∈ X` the map `f × f → U̇`, `(x, x') ↦ x⁻ 1_λ x'⁺`, is bilinear. It maps
`𝒜f × 𝒜f` into `𝒜U̇`, and the elements `b⁻ 1_λ b'⁺` (`b, b' ∈ B`, `λ ∈ X`) form an `𝒜`-basis of
`𝒜U̇` ([Lus] 23.2.2 (b)). Hence `𝒜U̇ ≅ ⊕_λ 𝒜f ⊗_𝒜 𝒜f` as `𝒜`-modules, and for an `𝒜`-algebra
`S`, an `S`-linear map out of `_S U̇ = S ⊗_𝒜 𝒜U̇` may be defined by its values on the elements
`x⁻ 1_λ x'⁺`, `x, x' ∈ 𝒜f`. This is the form of the presentation of [Lus] 31.1.3 used for
the quantum Frobenius homomorphism of `U̇` ([Lus] 35.1.9).

## Main definitions

* `QuantumGroup.Modified.triK`: `(x, x') ↦ x⁻ 1_λ x'⁺`, `f × f → U̇`, over `ℚ(v)`.
* `QuantumGroup.Modified.triA`: its restriction `𝒜f × 𝒜f → 𝒜U̇`.
* `QuantumGroup.Modified.triSumEquiv`: `⊕_λ 𝒜f ⊗_𝒜 𝒜f ≃ 𝒜U̇`, `(λ, x ⊗ x') ↦ x⁻ 1_λ x'⁺`.
* `QuantumGroup.Modified.thetaW`: monomials `θ_{i₁}^{(n₁)} ⋯ θ_{iₖ}^{(nₖ)}` in `𝒜f`.

## Main results

* `triK_thetaW`: `θ_w⁻ 1_λ θ_{w'}⁺ = F_w 1_λ E_{w'}`.
* `triSumEquiv_single`: `triSumEquiv` is given by `triA` on each summand.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.2.1, 23.2.2, 31.1.3.
-/

open LieLean LusztigF
open scoped TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

attribute [local instance] neZero_ratFunc_X
attribute [local instance] Modified.laurentAlgebraK Modified.laurentAlgebraU
  Modified.laurentTowerU

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}

/-! ### Monomials in divided powers in `𝒜f` -/

variable (D) in
/-- `θ_w = θ_{i₁}^{(n₁)} ⋯ θ_{iₖ}^{(nₖ)} ∈ 𝒜f` for `w = [(i₁, n₁), …, (iₖ, nₖ)]`. -/
def thetaW (w : List (I × ℕ)) : quotientIntegralForm D :=
  (w.map fun p ↦ integralGenerator D p.1 p.2).prod

omit [Finite I] in
@[simp] lemma thetaW_nil : thetaW D [] = 1 := rfl

omit [Finite I] in
lemma thetaW_cons (p : I × ℕ) (w : List (I × ℕ)) :
    thetaW D (p :: w) = integralGenerator D p.1 p.2 * thetaW D w := by
  simp [thetaW]

omit [Finite I] in
lemma thetaW_append (w w' : List (I × ℕ)) :
    thetaW D (w ++ w') = thetaW D w * thetaW D w' := by
  simp [thetaW]

omit [Finite I] in
lemma mul_mem_span_thetaW {a b : quotientIntegralForm D}
    (ha : a ∈ Submodule.span 𝒜 (Set.range (thetaW D)))
    (hb : b ∈ Submodule.span 𝒜 (Set.range (thetaW D))) :
    a * b ∈ Submodule.span 𝒜 (Set.range (thetaW D)) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨w', rfl⟩ := hb
      exact Submodule.subset_span ⟨w ++ w', thetaW_append w w'⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add b c _ _ hb hc => rw [mul_add]; exact add_mem hb hc
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hb
  | zero => rw [zero_mul]; exact zero_mem _
  | add a c _ _ ha hc => rw [add_mul]; exact add_mem ha hc
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

omit [Finite I] in
/-- `𝒜f` is spanned over `𝒜` by the monomials `θ_w`. -/
theorem mem_span_thetaW (x : quotientIntegralForm D) :
    x ∈ Submodule.span 𝒜 (Set.range (thetaW D)) := by
  obtain ⟨x, hx⟩ := x
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, n, rfl⟩ := hx
    exact Submodule.subset_span ⟨[(i, n)], by simp [thetaW, integralGenerator]⟩
  | algebraMap a =>
    have : (⟨algebraMap 𝒜 _ a, Subalgebra.algebraMap_mem _ a⟩ : quotientIntegralForm D) =
        a • thetaW D [] := by
      apply Subtype.ext
      simp [Algebra.algebraMap_eq_smul_one]
    rw [this]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨[], rfl⟩)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem_span_thetaW hx hy

variable (R : D.RootDatum Y)

lemma quotientMinus_integralGenerator (i : I) (n : ℕ) :
    quotientMinus R (integralGenerator D i n : Quotient D 𝕧) =
      qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) := by
  simp [integralGenerator, quotientIntegralGenerator, map_qDivPow']

lemma quotientPlus_integralGenerator (i : I) (n : ℕ) :
    quotientPlus R (integralGenerator D i n : Quotient D 𝕧) =
      qDivPow (𝕧 ^ D.d i) n (E R 𝕧 i) := by
  simp [integralGenerator, quotientIntegralGenerator, map_qDivPow']

lemma quotientMinus_thetaW (w : List (I × ℕ)) :
    quotientMinus R (thetaW D w : Quotient D 𝕧) = Modified.fPow R w := by
  induction w with
  | nil => simp
  | cons p w ih =>
    rw [thetaW_cons, Subalgebra.coe_mul, map_mul, ih, quotientMinus_integralGenerator,
      Modified.fPow_cons]

lemma quotientPlus_thetaW (w : List (I × ℕ)) :
    quotientPlus R (thetaW D w : Quotient D 𝕧) = Modified.ePow R w := by
  induction w with
  | nil => simp
  | cons p w ih =>
    rw [thetaW_cons, Subalgebra.coe_mul, map_mul, ih, quotientPlus_integralGenerator,
      Modified.ePow_cons]

namespace Modified

/-! ### The map `(x, x') ↦ x⁻ 1_λ x'⁺` over `ℚ(v)` -/

/-- `(x, x') ↦ x⁻ 1_λ x'⁺`, `f × f → U̇`. -/
def triK (l : Y →+ ℤ) : Quotient D 𝕧 →ₗ[𝕂] Quotient D 𝕧 →ₗ[𝕂] Modified R 𝕧 :=
  ((leftAct R 𝕧 hvn_ratFunc).comp (quotientMinus R).toLinearMap).compl₂
    (((rightAct R 𝕧 hvn_ratFunc).flip (one l)).comp (quotientPlus R).toLinearMap)

lemma triK_apply (l : Y →+ ℤ) (x x' : Quotient D 𝕧) :
    triK R l x x' = leftAct R 𝕧 hvn_ratFunc (quotientMinus R x)
      (rightAct R 𝕧 hvn_ratFunc (quotientPlus R x') (one l)) :=
  rfl

variable {R}

lemma triK_eq_elt (l : Y →+ ℤ) {x x' : Quotient D 𝕧} {a b : Y →+ ℤ}
    (hx : quotientMinus R x ∈ adWeightSpace R 𝕧 (-a))
    (hx' : quotientPlus R x' ∈ adWeightSpace R 𝕧 b) :
    triK R l x x' = elt (l - a) (l - b) (quotientMinus R x * quotientPlus R x')
      (by
        rw [show l - a - (l - b) = -a + b by abel]
        exact mul_mem_adWeightSpace hx hx') := by
  rw [triK_apply, one, rightAct_elt _ hx', leftAct_elt _ hx]
  exact elt_index (by abel) rfl (by rw [one_mul]) _ _

lemma triK_thetaW (l : Y →+ ℤ) (w w' : List (I × ℕ)) :
    triK R l (thetaW D w) (thetaW D w') =
      elt (l - wtW R w) (l - wtW R w') (fPow R w * ePow R w')
        (by
          rw [show l - wtW R w - (l - wtW R w') = wtW R w' - wtW R w by abel]
          exact fPow_mul_ePow_mem w w') := by
  rw [triK_eq_elt l (a := wtW R w) (b := wtW R w') (by rw [quotientMinus_thetaW]; exact fPow_mem w)
    (by rw [quotientPlus_thetaW]; exact ePow_mem w')]
  exact elt_index rfl rfl (by rw [quotientMinus_thetaW, quotientPlus_thetaW]) _ _

lemma triK_thetaW_mem_aForm (l : Y →+ ℤ) (w w' : List (I × ℕ)) :
    triK R l (thetaW D w) (thetaW D w') ∈ aForm R := by
  rw [triK_thetaW]
  change _ ∈ (aForm R).toSubmodule
  rw [aForm_eq_aFormFE]
  exact elt_fPow_ePow_mem _

omit [Finite I] in
lemma coe_laurent_smul (a : 𝒜) (x : quotientIntegralForm D) :
    ((a • x : quotientIntegralForm D) : Quotient D 𝕧) =
      integralLaurentEval a • (x : Quotient D 𝕧) :=
  rfl

lemma triK_mem_aForm (l : Y →+ ℤ) (x x' : quotientIntegralForm D) :
    triK R l x x' ∈ aForm R := by
  have hx := mem_span_thetaW x
  have hx' := mem_span_thetaW x'
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, rfl⟩ := ha
    induction hx' using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨w', rfl⟩ := hb
      exact triK_thetaW_mem_aForm l w w'
    | zero => rw [ZeroMemClass.coe_zero, map_zero]; exact zero_mem _
    | add b c _ _ hb hc => rw [Subalgebra.coe_add, map_add]; exact add_mem hb hc
    | smul c b _ hb =>
      rw [coe_laurent_smul, map_smul]
      exact smul_mem_aForm ⟨c, rfl⟩ hb
  | zero => rw [ZeroMemClass.coe_zero, map_zero, LinearMap.zero_apply]; exact zero_mem _
  | add a c _ _ ha hc => rw [Subalgebra.coe_add, map_add, LinearMap.add_apply]; exact add_mem ha hc
  | smul c a _ ha =>
    rw [coe_laurent_smul, map_smul, LinearMap.smul_apply]
    exact smul_mem_aForm ⟨c, rfl⟩ ha

variable (R) in
/-- `(x, x') ↦ x⁻ 1_λ x'⁺`, `𝒜f × 𝒜f → 𝒜U̇`. -/
def triA (l : Y →+ ℤ) :
    quotientIntegralForm D →ₗ[𝒜] quotientIntegralForm D →ₗ[𝒜] aForm R :=
  LinearMap.mk₂ 𝒜 (fun x x' ↦ ⟨triK R l x x', triK_mem_aForm l x x'⟩)
    (fun x y x' ↦ Subtype.ext (by
      change triK R l (x + y : Quotient D 𝕧) x' = triK R l x x' + triK R l y x'
      rw [map_add, LinearMap.add_apply]))
    (fun a x x' ↦ Subtype.ext (by
      change triK R l (integralLaurentEval a • (x : Quotient D 𝕧)) x' =
        integralLaurentEval a • triK R l x x'
      rw [map_smul, LinearMap.smul_apply]))
    (fun x x' y' ↦ Subtype.ext (by
      change triK R l x (x' + y' : Quotient D 𝕧) = triK R l x x' + triK R l x y'
      rw [map_add]))
    (fun a x x' ↦ Subtype.ext (by
      change triK R l x (integralLaurentEval a • (x' : Quotient D 𝕧)) =
        integralLaurentEval a • triK R l x x'
      rw [map_smul]))

@[simp] lemma coe_triA (l : Y →+ ℤ) (x x' : quotientIntegralForm D) :
    (triA R l x x' : Modified R 𝕧) = triK R l x x' :=
  rfl

lemma triA_thetaW (l : Y →+ ℤ) (w w' : List (I × ℕ)) :
    (triA R l (thetaW D w) (thetaW D w') : Modified R 𝕧) =
      elt (l - wtW R w) (l - wtW R w') (fPow R w * ePow R w')
        (by
          rw [show l - wtW R w - (l - wtW R w') = wtW R w' - wtW R w by abel]
          exact fPow_mul_ePow_mem w w') :=
  triK_thetaW l w w'

/-! ### `𝒜U̇ ≅ ⊕_λ 𝒜f ⊗ 𝒜f` -/

lemma minusQ_eq_quotientMinus (x : GrandLoop.Um D 𝕧) :
    minusQ R hvn_ratFunc x = quotientMinus R (negativeQuotientEquiv D x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- `b⁻ 1_λ b'⁺` for `b, b' ∈ B` is the element of the triangular basis
`aTriangularBasisCanonical`. -/
lemma triA_integralCanonicalBasis (l : Y →+ ℤ) (b b' : canonicalBasis D) :
    triA R l (integralCanonicalBasis D b) (integralCanonicalBasis D b') =
      aTriangularBasisCanonical R (b, l, b') := by
  apply Subtype.ext
  rw [coe_triA, aTriangularBasisCanonical_apply, triangularBasisCanonical_apply,
    integralCanonicalBasis_apply, integralCanonicalBasis_apply]
  have hm := canonicalMinusBasis_mem (R := R) b
  have hp := canonicalPlusBasis_mem (R := R) b'
  rw [canonicalMinusBasis_apply, minusQ_eq_quotientMinus] at hm
  rw [canonicalPlusBasis_apply, plusQ_eq_quotientPlus] at hp
  rw [triK_eq_elt l hm hp]
  exact elt_index rfl rfl (by rw [canonicalMinusBasis_apply, canonicalPlusBasis_apply,
    minusQ_eq_quotientMinus, plusQ_eq_quotientPlus]) _ _

variable (D) in
/-- The reindexing `(λ, (b, b')) ↦ (b, λ, b')`. -/
def triIdx : (Σ _ : Y →+ ℤ, canonicalBasis D × canonicalBasis D) ≃
    canonicalBasis D × (Y →+ ℤ) × canonicalBasis D where
  toFun t := (t.2.1, t.1, t.2.2)
  invFun t := ⟨t.2.1, t.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (D) in
/-- The `𝒜`-basis `(λ, b ⊗ b')` of `⊕_λ 𝒜f ⊗ 𝒜f`. -/
def triSumBasis : Module.Basis (Σ _ : Y →+ ℤ, canonicalBasis D × canonicalBasis D) 𝒜
    ((Y →+ ℤ) →₀ quotientIntegralForm D ⊗[𝒜] quotientIntegralForm D) :=
  Finsupp.basis fun _ ↦ (integralCanonicalBasis D).tensorProduct (integralCanonicalBasis D)

variable (R) in
/-- **`𝒜U̇ ≅ ⊕_λ 𝒜f ⊗_𝒜 𝒜f`**, `(λ, x ⊗ x') ↦ x⁻ 1_λ x'⁺` ([Lus] 23.2.2 (b)). -/
def triSumEquiv :
    ((Y →+ ℤ) →₀ quotientIntegralForm D ⊗[𝒜] quotientIntegralForm D) ≃ₗ[𝒜] aForm R :=
  (triSumBasis D).equiv (aTriangularBasisCanonical R) (triIdx D)

theorem triSumEquiv_single (l : Y →+ ℤ) (x x' : quotientIntegralForm D) :
    triSumEquiv R (Finsupp.single l (x ⊗ₜ x')) = triA R l x x' := by
  have h : (TensorProduct.mk 𝒜 _ _).compr₂
      ((triSumEquiv R).toLinearMap ∘ₗ Finsupp.lsingle l) = triA R l := by
    refine (integralCanonicalBasis D).ext fun b ↦ (integralCanonicalBasis D).ext fun b' ↦ ?_
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.coe_comp,
      Function.comp_apply, Finsupp.lsingle_apply, LinearEquiv.coe_coe]
    rw [triA_integralCanonicalBasis]
    have : Finsupp.single l (integralCanonicalBasis D b ⊗ₜ integralCanonicalBasis D b') =
        triSumBasis D ⟨l, b, b'⟩ := by
      rw [triSumBasis, Finsupp.coe_basis]
      exact congrArg _ (Module.Basis.tensorProduct_apply _ _ _ _).symm
    rw [this, triSumEquiv, Module.Basis.equiv_apply]
    rfl
  exact LinearMap.congr_fun₂ h x x'

/-- `𝒜U̇` is spanned over `𝒜` by the elements `θ_w⁻ 1_λ θ_{w'}⁺`. -/
theorem mem_span_triA_thetaW (z : aForm R) :
    z ∈ Submodule.span 𝒜 {y | ∃ l w w', y = triA R l (thetaW D w) (thetaW D w')} := by
  set P := Submodule.span 𝒜 {y | ∃ l w w', y = triA R l (thetaW D w) (thetaW D w')}
  obtain ⟨y, rfl⟩ := (triSumEquiv R).surjective z
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add f g hf hg => rw [map_add]; exact add_mem hf hg
  | single l t =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => rw [Finsupp.single_add, map_add]; exact add_mem ht ht'
    | tmul x x' =>
      rw [triSumEquiv_single]
      have hx := mem_span_thetaW x
      have hx' := mem_span_thetaW x'
      induction hx using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨w, rfl⟩ := ha
        induction hx' using Submodule.span_induction with
        | mem b hb =>
          obtain ⟨w', rfl⟩ := hb
          exact Submodule.subset_span ⟨l, w, w', rfl⟩
        | zero => rw [map_zero]; exact zero_mem _
        | add b c _ _ hb hc => rw [map_add]; exact add_mem hb hc
        | smul c b _ hb => rw [map_smul]; exact Submodule.smul_mem _ c hb
      | zero => rw [map_zero, LinearMap.zero_apply]; exact zero_mem _
      | add a c _ _ ha hc => rw [map_add, LinearMap.add_apply]; exact add_mem ha hc
      | smul c a _ ha => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ c ha

/-! ### Base change -/

section BaseChange

variable (S : Type*) [CommRing S] [Algebra 𝒜 S]

variable (R) in
/-- `(x, x') ↦ x⁻ 1_λ x'⁺`, `_S f × _S f → _S U̇`, by change of rings. -/
def triS (l : Y →+ ℤ) : S ⊗[𝒜] quotientIntegralForm D →ₗ[S]
    S ⊗[𝒜] quotientIntegralForm D →ₗ[S] S ⊗[𝒜] aForm R :=
  LinearMap.liftBaseChange S (LinearMap.baseChangeHom 𝒜 S _ _) ∘ₗ (triA R l).baseChange S

lemma triS_tmul (l : Y →+ ℤ) (s s' : S) (x x' : quotientIntegralForm D) :
    triS R S l (s ⊗ₜ x) (s' ⊗ₜ x') = (s * s') ⊗ₜ triA R l x x' := by
  simp [triS, TensorProduct.smul_tmul']

end BaseChange

end Modified

end LieLean.QuantumGroup
