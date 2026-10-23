/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Frobenius.ModifiedMul

/-!
# The quantum Frobenius homomorphism and the braid group action

Let `l > 0`, let `𝒜' = 𝒜/(f_{l'})` be the cyclotomic quotient of [Lus] 35.1.3, and let `S` be an
`𝒜'`-algebra. Under Lusztig's assumption 35.1.2 (a), [Lus] 35.1.9 gives the quantum Frobenius
homomorphism `Fr : _S U̇ → _S U̇*` (`frobR`, `frobA` on `𝒜U̇`), where `U̇*` is the modified algebra
of the root datum `(Y*, X*)` of type `(I, ∘)` of [Lus] 2.2.5. This file proves [Lus] 41.1.9: `Fr`
intertwines the symmetries `T''_{i,1}` of `_S U̇` and of `_S U̇*` ([Lus] 41.1.8, `braidR`).

## Main results

* `Modified.braidA_eA_ne`, `braidA_fA_ne`, `braidA_eA_self`, `braidA_fA_self`, `braidA_oneA`:
  `T''_{i,1}` on the generators `Eⱼ^{(n)} 1_λ`, `Fⱼ^{(n)} 1_λ`, `1_λ` of `𝒜U̇`, from the
  divided-power formulas of [Lus] 37.1.3 and `T''_{i,1}(1_λ) = 1_{sᵢλ}`.
* `Modified.frobA_braidA`: `Fr ∘ T''_{i,1} = T''_{i,1} ∘ Fr` on `𝒜U̇` ([Lus] 41.1.9).
* `Modified.frobR_braidR`, `Modified.frobR_braidR_symm`: the same on `_S U̇`, for `T''_{i,1}` and
  its inverse `T'_{i,-1}`.

## Proof

As in [Lus] 41.1.9, both sides are multiplicative and `𝒜`-linear, so it suffices to compare them on
the generators. For `j ≠ i` the formula for `T''_{i,1}(Eⱼ^{(n)} 1_λ)` is a sum over `r ≤ -aᵢⱼ n` of
products `Eᵢ^{(-aᵢⱼn-r)} Eⱼ^{(n)} Eᵢ^{(r)} 1_{sᵢλ}`; `Fr` kills every term unless `lⱼ ∣ n` and
`lᵢ ∣ r`, and the surviving terms are the terms of `T''_{i,1}(Eⱼ^{(n/lⱼ)} 1_{λ*})` for
`(I, ∘)`: the Cartan entries satisfy `lᵢ (-a*ᵢⱼ) = lⱼ (-aᵢⱼ)` (`frobOrder_mul_negA_frobenius`),
and the scalar `(-1)^{lᵢr} vᵢ^{-lᵢr}` maps in `𝒜'` to the scalar `(-1)^r (vᵢ*)^{-r}` of `(I, ∘)`
(`algebraMap_braidCoeffE`). For `j = i` the scalars of `T''_{i,1}(Eᵢ^{(n)} 1_λ)` correspond in
the same way (`algebraMap_selfCoeffE`). Finally `sᵢ` preserves `X*` and commutes with `λ ↦ λ*`
(`frobWt_comp_reflY`). The corollary `frobR_braidR_symm` is the same statement for the inverse
symmetries `T'_{i,-1}`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993.
-/

open LieLean LusztigF Finset
open scoped TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

attribute [local instance] neZero_ratFunc_X
attribute [local instance] Modified.laurentAlgebraK Modified.laurentAlgebraU
  Modified.laurentTowerU

namespace Modified

/-! ### `Tᵢ` on the generators of `𝒜U̇` -/

section Generators

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

variable (D) in
/-- `(-1)^r vᵢ^{-r}`. -/
def braidCoeffE (i : I) (r : ℕ) : 𝒜 := (-1) ^ r * LaurentPolynomial.T (-((D.d i * r : ℕ) : ℤ))

variable (D) in
/-- `(-1)^r vᵢ^{r}`. -/
def braidCoeffF (i : I) (r : ℕ) : 𝒜 := (-1) ^ r * LaurentPolynomial.T ((D.d i * r : ℕ) : ℤ)

omit [Finite I] [DecidableEq I] in
lemma integralLaurentEval_braidCoeffE (i : I) (r : ℕ) :
    integralLaurentEval (braidCoeffE D i r) = (-1 : 𝕂) ^ r * (𝕧 ^ D.d i)⁻¹ ^ r := by
  rw [braidCoeffE, _root_.map_mul, map_pow, map_neg, _root_.map_one, integralLaurentEval_T,
    zpow_neg,
    zpow_natCast, inv_pow, pow_mul]

omit [Finite I] [DecidableEq I] in
lemma integralLaurentEval_braidCoeffF (i : I) (r : ℕ) :
    integralLaurentEval (braidCoeffF D i r) = (-1 : 𝕂) ^ r * (𝕧 ^ D.d i) ^ r := by
  rw [braidCoeffF, _root_.map_mul, map_pow, map_neg, _root_.map_one, integralLaurentEval_T,
    zpow_natCast, pow_mul]

omit [Finite I] in
/-- `Tᵢ(1_λ) = 1_{sᵢλ}`. -/
lemma braidA_oneA (i : I) (μ : Y →+ ℤ) : braidA i (oneA R μ) = oneA R (μ.comp (reflY R i)) :=
  Subtype.ext (braid_one ratFunc_X_not_root i μ)

omit [Finite I] in
lemma elt_sum_of_mem {l₁ l₂ : Y →+ ℤ} {ι : Type*} (s : Finset ι) (f : ι → QuantumGroup R 𝕧)
    (hf : ∀ t ∈ s, f t ∈ adWeightSpace R 𝕧 (l₁ - l₂)) :
    elt l₁ l₂ (∑ t ∈ s, f t) (Submodule.sum_mem _ hf) =
      ∑ t ∈ s.attach, elt l₁ l₂ (f t) (hf t t.2) := by
  have h := elt_sum (l₁ := l₁) (l₂ := l₂) s.attach (fun t ↦ f t) fun t ↦ hf t t.2
  rw [← h]
  exact elt_congr (Finset.sum_attach s f).symm _ _

omit [Finite I] in
lemma elt_smul_triple_E (c : 𝒜) {k : 𝕂} (hc : integralLaurentEval c = k) (i j : I) (a n r : ℕ)
    (w L : Y →+ ℤ) (e : w + r • R.root i + n • R.root j + a • R.root i = L)
    (h : k • (qDivPow (𝕧 ^ D.d i) a (E R 𝕧 i) * qDivPow (𝕧 ^ D.d j) n (E R 𝕧 j) *
      qDivPow (𝕧 ^ D.d i) r (E R 𝕧 i)) ∈ adWeightSpace R 𝕧 (L - w)) :
    elt L w (k • (qDivPow (𝕧 ^ D.d i) a (E R 𝕧 i) * qDivPow (𝕧 ^ D.d j) n (E R 𝕧 j) *
      qDivPow (𝕧 ^ D.d i) r (E R 𝕧 i))) h =
      c • (divE R i a (w + r • R.root i + n • R.root j) * divE R j n (w + r • R.root i) *
        divE R i r w) := by
  subst hc e
  rw [divE, divE, divE, elt_mul_elt, elt_mul_elt, laurent_smul, ← elt_smul]

omit [Finite I] in
lemma elt_smul_triple_F (c : 𝒜) {k : 𝕂} (hc : integralLaurentEval c = k) (i j : I) (a n r : ℕ)
    (w L : Y →+ ℤ) (e : w + a • -R.root i + n • -R.root j + r • -R.root i = L)
    (h : k • (qDivPow (𝕧 ^ D.d i) r (F R 𝕧 i) * qDivPow (𝕧 ^ D.d j) n (F R 𝕧 j) *
      qDivPow (𝕧 ^ D.d i) a (F R 𝕧 i)) ∈ adWeightSpace R 𝕧 (L - w)) :
    elt L w (k • (qDivPow (𝕧 ^ D.d i) r (F R 𝕧 i) * qDivPow (𝕧 ^ D.d j) n (F R 𝕧 j) *
      qDivPow (𝕧 ^ D.d i) a (F R 𝕧 i))) h =
      c • (divF R i r (w + a • -R.root i + n • -R.root j) * divF R j n (w + a • -R.root i) *
        divF R i a w) := by
  subst hc e
  rw [divF, divF, divF, elt_mul_elt, elt_mul_elt, laurent_smul, ← elt_smul]

omit [Finite I] in
/-- `Tᵢ(Eⱼ^{(n)} 1_λ) = Σ_r (-1)^r vᵢ^{-r} Eᵢ^{(an-r)} Eⱼ^{(n)} Eᵢ^{(r)} 1_{sᵢλ}` for `j ≠ i`,
`a = -⟨i, j'⟩` ([Lus] 37.1.3). -/
lemma braidA_eA_ne {i j : I} (hji : j ≠ i) (n : ℕ) (μ : Y →+ ℤ) :
    braidA i (eA R j n μ) = ∑ r ∈ range (negA D i j * n + 1), braidCoeffE D i r •
      (eA R i (negA D i j * n - r) (μ.comp (reflY R i) + r • R.root i + n • R.root j) *
        eA R j n (μ.comp (reflY R i) + r • R.root i) * eA R i r (μ.comp (reflY R i))) := by
  have hT : braidEquivOfNotRoot R ratFunc_X_not_root i (qDivPow (𝕧 ^ D.d j) n (E R 𝕧 j)) =
      ∑ r ∈ range (negA D i j * n + 1), ((-1 : 𝕂) ^ r * (𝕧 ^ D.d i)⁻¹ ^ r) •
        (qDivPow (𝕧 ^ D.d i) (negA D i j * n - r) (E R 𝕧 i) * qDivPow (𝕧 ^ D.d j) n (E R 𝕧 j) *
          qDivPow (𝕧 ^ D.d i) r (E R 𝕧 i)) :=
    braidEquivOfNotRoot_qDivPow_E_ne ratFunc_X_not_root R hji n
  have hmem : ∀ r ∈ range (negA D i j * n + 1),
      ((-1 : 𝕂) ^ r * (𝕧 ^ D.d i)⁻¹ ^ r) •
        (qDivPow (𝕧 ^ D.d i) (negA D i j * n - r) (E R 𝕧 i) * qDivPow (𝕧 ^ D.d j) n (E R 𝕧 j) *
          qDivPow (𝕧 ^ D.d i) r (E R 𝕧 i)) ∈
        adWeightSpace R 𝕧 ((μ + n • R.root j).comp (reflY R i) - μ.comp (reflY R i)) := by
    intro r hr
    have hr' : r ≤ negA D i j * n := by rw [mem_range] at hr; omega
    rw [comp_sub_comp, ← wt_E_ne hji n r hr']
    exact Submodule.smul_mem _ _ (mul_mem_adWeightSpace (mul_mem_adWeightSpace
      (qDivPow_E_mem _ i _) (qDivPow_E_mem _ j n)) (qDivPow_E_mem _ i r))
  apply Subtype.ext
  rw [braidA_apply, AddSubmonoidClass.coe_finsetSum]
  change braid ratFunc_X_not_root i (divE R j n μ) = _
  rw [divE, braid_elt ratFunc_X_not_root i _ _ _
      (by rw [hT]; exact Submodule.sum_mem _ hmem),
    elt_congr hT _ (Submodule.sum_mem _ hmem), elt_sum_of_mem _ _ hmem]
  conv_rhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hr' : (r : ℕ) ≤ negA D i j * n := by have := r.2; rw [mem_range] at this; omega
  refine (elt_smul_triple_E (braidCoeffE D i r) (integralLaurentEval_braidCoeffE i r) i j _ n r
    _ _ ?_ _).trans rfl
  rw [AddMonoidHom.add_comp, ← wt_E_ne hji n r hr']
  abel

omit [Finite I] in
/-- `Tᵢ(Fⱼ^{(n)} 1_λ) = Σ_r (-1)^r vᵢ^{r} Fᵢ^{(r)} Fⱼ^{(n)} Fᵢ^{(an-r)} 1_{sᵢλ}` for `j ≠ i`,
`a = -⟨i, j'⟩` ([Lus] 37.1.3). -/
lemma braidA_fA_ne {i j : I} (hji : j ≠ i) (n : ℕ) (μ : Y →+ ℤ) :
    braidA i (fA R j n μ) = ∑ r ∈ range (negA D i j * n + 1), braidCoeffF D i r •
      (fA R i r (μ.comp (reflY R i) + (negA D i j * n - r) • -R.root i + n • -R.root j) *
        fA R j n (μ.comp (reflY R i) + (negA D i j * n - r) • -R.root i) *
        fA R i (negA D i j * n - r) (μ.comp (reflY R i))) := by
  have hT : braidEquivOfNotRoot R ratFunc_X_not_root i (qDivPow (𝕧 ^ D.d j) n (F R 𝕧 j)) =
      ∑ r ∈ range (negA D i j * n + 1), ((-1 : 𝕂) ^ r * (𝕧 ^ D.d i) ^ r) •
        (qDivPow (𝕧 ^ D.d i) r (F R 𝕧 i) * qDivPow (𝕧 ^ D.d j) n (F R 𝕧 j) *
          qDivPow (𝕧 ^ D.d i) (negA D i j * n - r) (F R 𝕧 i)) :=
    braidEquivOfNotRoot_qDivPow_F_ne ratFunc_X_not_root R hji n
  have hmem : ∀ r ∈ range (negA D i j * n + 1),
      ((-1 : 𝕂) ^ r * (𝕧 ^ D.d i) ^ r) •
        (qDivPow (𝕧 ^ D.d i) r (F R 𝕧 i) * qDivPow (𝕧 ^ D.d j) n (F R 𝕧 j) *
          qDivPow (𝕧 ^ D.d i) (negA D i j * n - r) (F R 𝕧 i)) ∈
        adWeightSpace R 𝕧 ((μ + n • -R.root j).comp (reflY R i) - μ.comp (reflY R i)) := by
    intro r hr
    have hr' : r ≤ negA D i j * n := by rw [mem_range] at hr; omega
    rw [comp_sub_comp, ← wt_F_ne hji n r hr']
    exact Submodule.smul_mem _ _ (mul_mem_adWeightSpace (mul_mem_adWeightSpace
      (qDivPow_F_mem _ i r) (qDivPow_F_mem _ j n)) (qDivPow_F_mem _ i _))
  apply Subtype.ext
  rw [braidA_apply, AddSubmonoidClass.coe_finsetSum]
  change braid ratFunc_X_not_root i (divF R j n μ) = _
  rw [divF, braid_elt ratFunc_X_not_root i _ _ _
      (by rw [hT]; exact Submodule.sum_mem _ hmem),
    elt_congr hT _ (Submodule.sum_mem _ hmem), elt_sum_of_mem _ _ hmem]
  conv_rhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hr' : (r : ℕ) ≤ negA D i j * n := by have := r.2; rw [mem_range] at this; omega
  refine (elt_smul_triple_F (braidCoeffF D i r) (integralLaurentEval_braidCoeffF i r) i j _ n r
    _ _ ?_ _).trans rfl
  rw [AddMonoidHom.add_comp, ← wt_F_ne' hji n r hr']
  abel

variable (D) in
/-- `(-1)^n vᵢ^{-n(n-1) - nk}`, the coefficient of `Tᵢ(Eᵢ^{(n)} 1_λ)`, `k = ⟨i, λ⟩`. -/
def selfCoeffE (i : I) (n : ℕ) (k : ℤ) : 𝒜 :=
  (-1) ^ n * LaurentPolynomial.T (-((D.d i * (n * (n - 1)) : ℕ) : ℤ) - ((D.d i * n : ℕ) : ℤ) * k)

variable (D) in
/-- `(-1)^n vᵢ^{n(n-1) + nk - 2n²}`, the coefficient of `Tᵢ(Fᵢ^{(n)} 1_λ)`, `k = ⟨i, λ⟩`. -/
def selfCoeffF (i : I) (n : ℕ) (k : ℤ) : 𝒜 :=
  (-1) ^ n * LaurentPolynomial.T (((D.d i * (n * (n - 1)) : ℕ) : ℤ) + ((D.d i * n : ℕ) : ℤ) * k -
    2 * ((D.d i * (n * n) : ℕ) : ℤ))

omit [Finite I] [DecidableEq I] in
lemma comp_reflY_ktilde (i : I) (μ : Y →+ ℤ) (n : ℕ) :
    (μ.comp (reflY R i)) (n • ktilde R i) = -((D.d i * n : ℕ) : ℤ) * μ (R.coroot i) := by
  simp only [AddMonoidHom.comp_apply, reflY, ktilde, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
    AddMonoidHom.comp_apply, zmultiplesHom_apply, map_nsmul, map_sub, map_zsmul,
    R.root_coroot, D.cartanMatrix_self, smul_eq_mul]
  push_cast; ring

omit [Finite I] in
/-- `Tᵢ(Eᵢ^{(n)} 1_λ) = (-1)^n vᵢ^{-n(n-1) - n⟨i,λ⟩} Fᵢ^{(n)} 1_{sᵢλ}` ([Lus] 37.1.3). -/
lemma braidA_eA_self (i : I) (n : ℕ) (μ : Y →+ ℤ) :
    braidA i (eA R i n μ) = selfCoeffE D i n (μ (R.coroot i)) • fA R i n (μ.comp (reflY R i)) := by
  have hT := braidEquivOfNotRoot_qDivPow_E_self ratFunc_X_not_root R i n
  have hF := qDivPow_F_mem (R := R) (𝕧 ^ D.d i) i n
  have hm : ((-1 : 𝕂) ^ n * (𝕧 ^ D.d i)⁻¹ ^ (n * (n - 1))) •
      (qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) * K R 𝕧 (n • ktilde R i)) ∈
      adWeightSpace R 𝕧 ((μ + n • R.root i).comp (reflY R i) - μ.comp (reflY R i)) := by
    rw [comp_sub_comp, ← wt_E_self]
    exact Submodule.smul_mem _ _ (by
      simpa using mul_mem_adWeightSpace hF (K_mem_adWeightSpace (R := R) (v := 𝕧) _))
  apply Subtype.ext
  rw [braidA_apply]
  change braid ratFunc_X_not_root i (divE R i n μ) = _
  rw [divE, braid_elt ratFunc_X_not_root i _ _ _ (by rw [hT]; exact hm), elt_congr hT _ hm]
  have hl : (μ + n • R.root i).comp (reflY R i) = μ.comp (reflY R i) + n • -R.root i := by
    rw [AddMonoidHom.add_comp, ← wt_E_self]
  have hF' : qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) ∈ adWeightSpace R 𝕧
      ((μ + n • R.root i).comp (reflY R i) - μ.comp (reflY R i)) := by
    rw [hl, add_sub_cancel_left]; exact hF
  rw [elt_smul _ _ _ (by simpa using mul_mem_adWeightSpace hF' (K_mem_adWeightSpace (R := R)
      (v := 𝕧) (n • ktilde R i))), elt_mul_K _ _ _ hF', smul_smul]
  change _ = selfCoeffE D i n (μ (R.coroot i)) • divF R i n (μ.comp (reflY R i))
  rw [laurent_smul, divF]
  congr 1
  · rw [selfCoeffE, _root_.map_mul, map_pow, map_neg, _root_.map_one, integralLaurentEval_T,
      comp_reflY_ktilde, zpow_sub₀ (RatFunc.X_ne_zero), zpow_neg, zpow_natCast, neg_mul,
      zpow_neg, inv_pow, ← pow_mul, div_eq_mul_inv]
    ring
  · exact elt_index hl rfl rfl _ _

omit [Finite I] in
/-- `Tᵢ(Fᵢ^{(n)} 1_λ) = (-1)^n vᵢ^{n(n-1) + n⟨i,λ⟩ - 2n²} Eᵢ^{(n)} 1_{sᵢλ}` ([Lus] 37.1.3). -/
lemma braidA_fA_self (i : I) (n : ℕ) (μ : Y →+ ℤ) :
    braidA i (fA R i n μ) = selfCoeffF D i n (μ (R.coroot i)) • eA R i n (μ.comp (reflY R i)) := by
  have hT := braidEquivOfNotRoot_qDivPow_F_self ratFunc_X_not_root R i n
  have hE := qDivPow_E_mem (R := R) (𝕧 ^ D.d i) i n
  have hm : ((-1 : 𝕂) ^ n * (𝕧 ^ D.d i) ^ (n * (n - 1))) •
      (K R 𝕧 (n • -ktilde R i) * qDivPow (𝕧 ^ D.d i) n (E R 𝕧 i)) ∈
      adWeightSpace R 𝕧 ((μ + n • -R.root i).comp (reflY R i) - μ.comp (reflY R i)) := by
    rw [comp_sub_comp, ← wt_F_self]
    exact Submodule.smul_mem _ _ (by
      simpa using mul_mem_adWeightSpace (K_mem_adWeightSpace (R := R) (v := 𝕧) _) hE)
  apply Subtype.ext
  rw [braidA_apply]
  change braid ratFunc_X_not_root i (divF R i n μ) = _
  rw [divF, braid_elt ratFunc_X_not_root i _ _ _ (by rw [hT]; exact hm), elt_congr hT _ hm]
  have hl : (μ + n • -R.root i).comp (reflY R i) = μ.comp (reflY R i) + n • R.root i := by
    rw [AddMonoidHom.add_comp, ← wt_F_self]
  have hE' : qDivPow (𝕧 ^ D.d i) n (E R 𝕧 i) ∈ adWeightSpace R 𝕧
      ((μ + n • -R.root i).comp (reflY R i) - μ.comp (reflY R i)) := by
    rw [hl, add_sub_cancel_left]; exact hE
  have hw : ((μ + n • -R.root i).comp (reflY R i)) (n • -ktilde R i) =
      ((D.d i * n : ℕ) : ℤ) * μ (R.coroot i) - 2 * ((D.d i * (n * n) : ℕ) : ℤ) := by
    rw [hl, AddMonoidHom.add_apply, smul_neg, map_neg, map_neg, comp_reflY_ktilde,
      AddMonoidHom.nsmul_apply, map_nsmul, root_ktilde, D.cartanMatrix_self]
    simp only [nsmul_eq_mul]
    push_cast; ring
  rw [elt_smul _ _ _ (by simpa using mul_mem_adWeightSpace (K_mem_adWeightSpace (R := R)
      (v := 𝕧) (n • -ktilde R i)) hE'), elt_K_mul _ _ _ hE', smul_smul]
  change _ = selfCoeffF D i n (μ (R.coroot i)) • divE R i n (μ.comp (reflY R i))
  rw [laurent_smul, divE]
  congr 1
  · rw [selfCoeffF, _root_.map_mul, map_pow, map_neg, _root_.map_one, integralLaurentEval_T, hw,
      show ((D.d i * (n * (n - 1)) : ℕ) : ℤ) + ((D.d i * n : ℕ) : ℤ) * μ (R.coroot i) -
        2 * ((D.d i * (n * n) : ℕ) : ℤ) = ((D.d i * (n * (n - 1)) : ℕ) : ℤ) +
          (((D.d i * n : ℕ) : ℤ) * μ (R.coroot i) - 2 * ((D.d i * (n * n) : ℕ) : ℤ)) by ring,
      zpow_add₀ RatFunc.X_ne_zero, zpow_natCast, ← pow_mul]
    ring
  · exact elt_index hl rfl rfl _ _

end Generators

/-! ### Weights and `sᵢ` -/

section Weights

variable {I Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum I} (R : D.RootDatum Y) {l : ℕ}
  (hl0 : 0 < l)

lemma coroot_comp_reflY_apply (i j : I) (μ : Y →+ ℤ) :
    (μ.comp (reflY R i)) (R.coroot j) = μ (R.coroot j) - D.cartanMatrix j i * μ (R.coroot i) := by
  simp [reflY, R.root_coroot]

include hl0 in
lemma comp_reflY_mem_frobWeights (i : I) {μ : Y →+ ℤ} (hμ : μ ∈ R.frobWeights l) :
    μ.comp (reflY R i) ∈ R.frobWeights l := by
  intro j
  rw [coroot_comp_reflY_apply]
  obtain ⟨c, hc⟩ := hμ i
  obtain ⟨d, hd⟩ := D.frobOrder_dvd_mul_cartanMatrix hl0 j i
  refine dvd_sub (hμ j) ⟨d * c, ?_⟩
  rw [hc]
  linear_combination c * hd

include hl0 in
lemma comp_reflY_mem_frobWeights_iff (i : I) {μ : Y →+ ℤ} :
    μ.comp (reflY R i) ∈ R.frobWeights l ↔ μ ∈ R.frobWeights l := by
  refine ⟨fun h ↦ ?_, comp_reflY_mem_frobWeights R hl0 i⟩
  have h' := comp_reflY_mem_frobWeights R hl0 i h
  rwa [show (μ.comp (reflY R i)).comp (reflY R i) = μ by ext y; simp [reflY_reflY]] at h'

include hl0 in
/-- `(sᵢλ)* = sᵢ* λ*` for `λ ∈ X*`. -/
lemma frobWt_comp_reflY (i : I) {μ : Y →+ ℤ} (hμ : μ ∈ R.frobWeights l) :
    R.frobWt l (μ.comp (reflY R i)) =
      (R.frobWt l μ).comp (reflY (R.frobRootDatum hl0) i) := by
  have hs := comp_reflY_mem_frobWeights R hl0 i hμ
  have hsub : (⟨μ.comp (reflY R i), hs⟩ : R.frobWeights l) =
      ⟨μ, hμ⟩ - (R.frobCoroot l i ⟨μ, hμ⟩) • R.frobRoot hl0 i := by
    refine Subtype.ext (AddMonoidHom.ext fun y ↦ ?_)
    have h := R.frobOrder_mul_frobCoroot l i ⟨μ, hμ⟩
    simp only [AddMonoidHom.comp_apply, reflY, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
      zmultiplesHom_apply, map_sub, map_zsmul, smul_eq_mul, AddSubgroup.coe_sub,
      AddSubgroup.coe_zsmul, R.coe_frobRoot, AddMonoidHom.smul_apply] at h ⊢
    rw [← h]
    ring
  rw [R.frobWt_of_mem hs, R.frobWt_of_mem hμ, hsub]
  ext y
  simp only [R.frobEval_apply, map_sub, map_zsmul, AddMonoidHom.comp_apply, reflY_apply,
    R.frobRootDatum_root hl0, R.frobRootDatum_coroot hl0, AddMonoidHom.sub_apply,
    AddMonoidHom.smul_apply, smul_eq_mul]
  ring

end Weights

/-! ### Scalars at a root of unity -/

section Scalars

variable {I : Type*} (D : LusztigCartanDatum I) {l l' : ℕ} (hl0 : 0 < l)
  (hl' : l' = 2 * l ∨ (Odd l ∧ l' = l))

/-- `(-1)^{Le} x^{Le} = (-1)^e x^{L²e}` when `x^{2L} = 1` and `x^{L²+L} = (-1)^{L+1}`. -/
lemma neg_one_pow_mul_pow_of_root {A : Type*} [CommRing A] {x : A} {L : ℕ}
    (h1 : x ^ (2 * L) = 1) (h2 : x ^ (L ^ 2 + L) = (-1) ^ (L + 1)) (e : ℕ) :
    (-1 : A) ^ (L * e) * x ^ (L * e) = (-1) ^ e * x ^ (L ^ 2 * e) := by
  have key : (-1 : A) ^ L * x ^ L = -x ^ (L ^ 2) := by
    linear_combination (-(x ^ (L ^ 2))) * h1 + x ^ L * h2
  rw [pow_mul, pow_mul, ← mul_pow, key, pow_mul, neg_pow, mul_comm]

/-- The hypotheses of `neg_one_pow_mul_pow_of_root` for the inverse of a unit. -/
lemma inv_pow_of_root {A : Type*} [CommRing A] {u : Aˣ} {L : ℕ}
    (h1 : (u : A) ^ (2 * L) = 1) (h2 : (u : A) ^ (L ^ 2 + L) = (-1) ^ (L + 1)) :
    ((u⁻¹ : Aˣ) : A) ^ (2 * L) = 1 ∧ ((u⁻¹ : Aˣ) : A) ^ (L ^ 2 + L) = (-1) ^ (L + 1) := by
  have hN : ∀ N, ((u⁻¹ : Aˣ) : A) ^ N * (u : A) ^ N = 1 := fun N ↦ by
    rw [← mul_pow, Units.inv_mul, one_pow]
  have hc : ((-1 : A) ^ (L + 1)) * (-1) ^ (L + 1) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  refine ⟨?_, ?_⟩
  · linear_combination hN (2 * L) - ((u⁻¹ : Aˣ) : A) ^ (2 * L) * h1
  · linear_combination ((-1 : A) ^ (L + 1)) * hN (L ^ 2 + L) -
      ((-1 : A) ^ (L + 1)) * ((u⁻¹ : Aˣ) : A) ^ (L ^ 2 + L) * h2 -
      ((u⁻¹ : Aˣ) : A) ^ (L ^ 2 + L) * hc

include hl0 hl' in
lemma frobUnit_root (i : I) :
    (frobUnit D (l' := l') i : CyclotomicQuotient l') ^ (2 * D.frobOrder l i) = 1 ∧
      (frobUnit D (l' := l') i : CyclotomicQuotient l') ^ (D.frobOrder l i ^ 2 + D.frobOrder l i) =
        (-1) ^ (D.frobOrder l i + 1) := by
  have := neZero_of_frobeniusLevel hl0 hl'
  have h1 := (frobUnit_pow_two_mul_eq_one_iff D hl0 hl' i _).2 dvd_rfl
  exact ⟨h1, pow_sq_add_eq_of_root h1 (fun t h0 ht h ↦ Nat.not_dvd_of_pos_of_lt h0 ht
    ((frobUnit_pow_two_mul_eq_one_iff D hl0 hl' i t).1 h)) (D.frobOrder_pos hl0 i)⟩

lemma algebraMap_T_natCast_mul (i : I) (k : ℕ) :
    algebraMap 𝒜 (CyclotomicQuotient l') (LaurentPolynomial.T ((D.d i * k : ℕ) : ℤ)) =
      (frobUnit D (l' := l') i : CyclotomicQuotient l') ^ k := by
  rw [show ((D.d i * k : ℕ) : ℤ) = k * (D.d i : ℤ) by push_cast; ring, ← LaurentPolynomial.T_pow,
    map_pow]
  rfl

lemma algebraMap_T_neg_natCast_mul (i : I) (k : ℕ) :
    algebraMap 𝒜 (CyclotomicQuotient l') (LaurentPolynomial.T (-((D.d i * k : ℕ) : ℤ))) =
      (((frobUnit D (l' := l') i)⁻¹ : (CyclotomicQuotient l')ˣ) : CyclotomicQuotient l') ^ k := by
  rw [show -((D.d i * k : ℕ) : ℤ) = k * (-(D.d i : ℤ)) by push_cast; ring,
    ← LaurentPolynomial.T_pow, map_pow]
  rfl

include hl0 hl' in
/-- `(-1)^{lᵢ e} vᵢ^{m + lᵢ e} = (-1)^e vᵢ^{m + lᵢ² e}` in `𝒜'`. -/
lemma algebraMap_neg_one_pow_T_add (i : I) (m : ℤ) (e : ℕ) :
    algebraMap 𝒜 (CyclotomicQuotient l') ((-1) ^ (D.frobOrder l i * e) *
        LaurentPolynomial.T (m + ((D.d i * (D.frobOrder l i * e) : ℕ) : ℤ))) =
      algebraMap 𝒜 (CyclotomicQuotient l') ((-1) ^ e *
        LaurentPolynomial.T (m + ((D.d i * (D.frobOrder l i ^ 2 * e) : ℕ) : ℤ))) := by
  obtain ⟨h1, h2⟩ := frobUnit_root D hl0 hl' i
  rw [_root_.map_mul, _root_.map_mul, LaurentPolynomial.T_add, LaurentPolynomial.T_add,
    _root_.map_mul, _root_.map_mul, algebraMap_T_natCast_mul, algebraMap_T_natCast_mul, map_pow,
    map_pow, map_neg, _root_.map_one]
  linear_combination algebraMap 𝒜 (CyclotomicQuotient l') (LaurentPolynomial.T m) *
    neg_one_pow_mul_pow_of_root h1 h2 e

include hl0 hl' in
/-- `(-1)^{lᵢ e} vᵢ^{m - lᵢ e} = (-1)^e vᵢ^{m - lᵢ² e}` in `𝒜'`. -/
lemma algebraMap_neg_one_pow_T_sub (i : I) (m : ℤ) (e : ℕ) :
    algebraMap 𝒜 (CyclotomicQuotient l') ((-1) ^ (D.frobOrder l i * e) *
        LaurentPolynomial.T (m - ((D.d i * (D.frobOrder l i * e) : ℕ) : ℤ))) =
      algebraMap 𝒜 (CyclotomicQuotient l') ((-1) ^ e *
        LaurentPolynomial.T (m - ((D.d i * (D.frobOrder l i ^ 2 * e) : ℕ) : ℤ))) := by
  obtain ⟨h1, h2⟩ := inv_pow_of_root (frobUnit_root D hl0 hl' i).1 (frobUnit_root D hl0 hl' i).2
  rw [sub_eq_add_neg, sub_eq_add_neg, _root_.map_mul, _root_.map_mul, LaurentPolynomial.T_add,
    LaurentPolynomial.T_add, _root_.map_mul, _root_.map_mul, algebraMap_T_neg_natCast_mul,
    algebraMap_T_neg_natCast_mul, map_pow, map_pow, map_neg, _root_.map_one]
  linear_combination algebraMap 𝒜 (CyclotomicQuotient l') (LaurentPolynomial.T m) *
    neg_one_pow_mul_pow_of_root h1 h2 e

lemma natCast_mul_pred (a : ℕ) : ((a * (a - 1) : ℕ) : ℤ) = a * a - a := by
  cases a with
  | zero => simp
  | succ a => push_cast; ring

include hl0 hl' in
/-- The coefficient of `Tᵢ(Eᵢ^{(lᵢn)} 1_λ)` in `𝒜'` is that of `Tᵢ(Eᵢ^{(n)} 1_{λ*})`. -/
lemma algebraMap_selfCoeffE [Finite I] (i : I) (n : ℕ) (k : ℤ) :
    algebraMap 𝒜 (CyclotomicQuotient l')
        (selfCoeffE D i (D.frobOrder l i * n) (D.frobOrder l i * k)) =
      algebraMap 𝒜 (CyclotomicQuotient l') (selfCoeffE (D.frobenius hl0) i n k) := by
  have h := algebraMap_neg_one_pow_T_add D hl0 hl' i
    (-((D.d i : ℤ) * D.frobOrder l i ^ 2 * n * n) - (D.d i : ℤ) * D.frobOrder l i ^ 2 * n * k) n
  rw [selfCoeffE, selfCoeffE, D.frobenius_d hl0, Nat.cast_mul (D.d i), natCast_mul_pred,
    Nat.cast_mul _ (n * (n - 1)), natCast_mul_pred]
  convert h using 4 <;> push_cast <;> ring

include hl0 hl' in
/-- The coefficient of `Tᵢ(Fᵢ^{(lᵢn)} 1_λ)` in `𝒜'` is that of `Tᵢ(Fᵢ^{(n)} 1_{λ*})`. -/
lemma algebraMap_selfCoeffF [Finite I] (i : I) (n : ℕ) (k : ℤ) :
    algebraMap 𝒜 (CyclotomicQuotient l')
        (selfCoeffF D i (D.frobOrder l i * n) (D.frobOrder l i * k)) =
      algebraMap 𝒜 (CyclotomicQuotient l') (selfCoeffF (D.frobenius hl0) i n k) := by
  have h := algebraMap_neg_one_pow_T_sub D hl0 hl' i
    (-((D.d i : ℤ) * D.frobOrder l i ^ 2 * n * n) + (D.d i : ℤ) * D.frobOrder l i ^ 2 * n * k) n
  rw [selfCoeffF, selfCoeffF, D.frobenius_d hl0, Nat.cast_mul (D.d i), natCast_mul_pred,
    Nat.cast_mul _ (n * (n - 1)), natCast_mul_pred]
  convert h using 4 <;> push_cast <;> ring

include hl0 hl' in
/-- `(-1)^{lᵢr} vᵢ^{-lᵢr} = (-1)^r (vᵢ*)^{-r}` in `𝒜'`. -/
lemma algebraMap_braidCoeffE (i : I) (r : ℕ) :
    algebraMap 𝒜 (CyclotomicQuotient l') (braidCoeffE D i (D.frobOrder l i * r)) =
      algebraMap 𝒜 (CyclotomicQuotient l') (braidCoeffE (D.frobenius hl0) i r) := by
  have h := algebraMap_neg_one_pow_T_sub D hl0 hl' i 0 r
  rw [zero_sub, zero_sub] at h
  rw [braidCoeffE, braidCoeffE, D.frobenius_d hl0]
  convert h using 5
  push_cast; ring

include hl0 hl' in
/-- `(-1)^{lᵢr} vᵢ^{lᵢr} = (-1)^r (vᵢ*)^{r}` in `𝒜'`. -/
lemma algebraMap_braidCoeffF (i : I) (r : ℕ) :
    algebraMap 𝒜 (CyclotomicQuotient l') (braidCoeffF D i (D.frobOrder l i * r)) =
      algebraMap 𝒜 (CyclotomicQuotient l') (braidCoeffF (D.frobenius hl0) i r) := by
  have h := algebraMap_neg_one_pow_T_add D hl0 hl' i 0 r
  rw [zero_add, zero_add] at h
  rw [braidCoeffF, braidCoeffF, D.frobenius_d hl0]
  convert h using 4
  push_cast; ring

include hl0 in
/-- `lᵢ a*ᵢⱼ = lⱼ aᵢⱼ` for the entries `a = -⟨i, j'⟩` ([Lus] 2.2.4). -/
lemma frobOrder_mul_negA_frobenius {i j : I} (hij : i ≠ j) :
    D.frobOrder l i * negA (D.frobenius hl0) i j = D.frobOrder l j * negA D i j := by
  have h := D.frobOrder_mul_cartanMatrix_frobenius hl0 i j
  rw [cartanMatrix_eq_neg_negA hij, cartanMatrix_eq_neg_negA hij] at h
  have h' : ((D.frobOrder l i * negA (D.frobenius hl0) i j : ℕ) : ℤ) =
      ((D.frobOrder l j * negA D i j : ℕ) : ℤ) := by
    push_cast; linarith
  exact_mod_cast h'

/-- A sum over `r ≤ LN` whose terms vanish unless `L ∣ r` is a sum over `r' ≤ N`. -/
lemma sum_range_mul_of_dvd {M : Type*} [AddCommMonoid M] {L : ℕ} (hL : 0 < L) (N : ℕ)
    (f : ℕ → M) (hf : ∀ r, ¬ L ∣ r → f r = 0) :
    ∑ r ∈ range (L * N + 1), f r = ∑ r ∈ range (N + 1), f (L * r) := by
  have hsub : (range (N + 1)).image (L * ·) ⊆ range (L * N + 1) := by
    intro t ht
    simp only [Finset.mem_image, mem_range] at ht ⊢
    obtain ⟨t', ht', rfl⟩ := ht
    exact Nat.lt_succ_of_le (Nat.mul_le_mul_left _ (Nat.lt_succ_iff.1 ht'))
  rw [← Finset.sum_subset hsub ?_, Finset.sum_image fun x _ y _ h ↦ Nat.eq_of_mul_eq_mul_left hL h]
  intro t ht ht'
  refine hf t fun ⟨c, hc⟩ ↦ ht' ?_
  subst hc
  exact Finset.mem_image.2 ⟨c, mem_range.2 (Nat.lt_succ_of_le
    ((Nat.mul_le_mul_left_iff hL).1 (Nat.lt_succ_iff.1 (mem_range.1 ht)))), rfl⟩

/-- Reindexing `r = L r'` in a sum whose terms vanish unless `L ∣ r`. -/
lemma sum_range_eq_of_mul {M : Type*} [AddCommMonoid M] {L A N : ℕ} (hL : 0 < L)
    (hA : A = L * N) {g h : ℕ → M} (hg : ∀ r, ¬ L ∣ r → g r = 0)
    (hgh : ∀ r ∈ range (N + 1), g (L * r) = h r) :
    ∑ r ∈ range (A + 1), g r = ∑ r ∈ range (N + 1), h r := by
  subst hA
  rw [sum_range_mul_of_dvd hL N g hg]
  exact Finset.sum_congr rfl hgh

end Scalars

/-! ### `Fr ∘ Tᵢ = Tᵢ ∘ Fr` on generators -/

section Compat

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) {l l' : ℕ} (hl0 : 0 < l) (hl' : l' = 2 * l ∨ (Odd l ∧ l' = l))
  (hA : ∀ i j, i ≠ j → 2 ≤ D.frobOrder l j → ∀ a : ℕ, D.cartanMatrix i j = -a →
    a < D.frobOrder l i)
  (S : Type*) [CommRing S] [Algebra 𝒜 S] [Algebra (CyclotomicQuotient l') S]
  [IsScalarTower 𝒜 (CyclotomicQuotient l') S]

local notation "Fr" => frobA R hl0 hl' hA S

lemma frobA_braidA_oneA (i : I) (μ : Y →+ ℤ) :
    Fr (braidA i (oneA R μ)) = braidR S i (Fr (oneA R μ)) := by
  rw [braidA_oneA, frobA_oneA, frobA_oneA, comp_reflY_mem_frobWeights_iff R hl0 i]
  split_ifs with h
  · rw [braidR_tmul, braidA_oneA, frobWt_comp_reflY R hl0 i h]
  · rw [map_zero]

lemma frobA_braidA_eA_self (i : I) (n : ℕ) (μ : Y →+ ℤ) :
    Fr (braidA i (eA R i n μ)) = braidR S i (Fr (eA R i n μ)) := by
  rw [braidA_eA_self, map_smul, frobA_fA, frobA_eA, comp_reflY_mem_frobWeights_iff R hl0 i]
  split_ifs with h
  · obtain ⟨hμ, ⟨n', rfl⟩⟩ := h
    rw [braidR_tmul, braidA_eA_self, TensorProduct.tmul_smul, frobWt_comp_reflY R hl0 i hμ,
      Nat.mul_div_cancel_left _ (D.frobOrder_pos hl0 i)]
    refine smul_tmul_one_congr (l' := l') S ?_ _
    rw [← R.frobOrder_mul_frobWt_coroot hl0 i hμ]
    exact algebraMap_selfCoeffE D hl0 hl' i n' _
  · exact (smul_zero _).trans (LinearEquiv.map_zero _).symm

lemma frobA_braidA_fA_self (i : I) (n : ℕ) (μ : Y →+ ℤ) :
    Fr (braidA i (fA R i n μ)) = braidR S i (Fr (fA R i n μ)) := by
  rw [braidA_fA_self, map_smul, frobA_eA, frobA_fA, comp_reflY_mem_frobWeights_iff R hl0 i]
  split_ifs with h
  · obtain ⟨hμ, ⟨n', rfl⟩⟩ := h
    rw [braidR_tmul, braidA_fA_self, TensorProduct.tmul_smul, frobWt_comp_reflY R hl0 i hμ,
      Nat.mul_div_cancel_left _ (D.frobOrder_pos hl0 i)]
    refine smul_tmul_one_congr (l' := l') S ?_ _
    rw [← R.frobOrder_mul_frobWt_coroot hl0 i hμ]
    exact algebraMap_selfCoeffF D hl0 hl' i n' _
  · exact (smul_zero _).trans (LinearEquiv.map_zero _).symm

open Classical in
lemma frobA_triple_E (i j : I) (a n r : ℕ) (w : Y →+ ℤ) :
    Fr (eA R i a (w + r • R.root i + n • R.root j) * eA R j n (w + r • R.root i) * eA R i r w) =
      if w ∈ R.frobWeights l ∧ D.frobOrder l i ∣ a ∧ D.frobOrder l j ∣ n ∧ D.frobOrder l i ∣ r
      then (1 : S) ⊗ₜ (eA (R.frobRootDatum hl0) i (a / D.frobOrder l i)
          (R.frobWt l w + (r / D.frobOrder l i) • (R.frobRootDatum hl0).root i +
            (n / D.frobOrder l j) • (R.frobRootDatum hl0).root j) *
        eA (R.frobRootDatum hl0) j (n / D.frobOrder l j)
          (R.frobWt l w + (r / D.frobOrder l i) • (R.frobRootDatum hl0).root i) *
        eA (R.frobRootDatum hl0) i (r / D.frobOrder l i) (R.frobWt l w)) else 0 := by
  rw [frobA_mul, frobA_mul, frobA_eA, frobA_eA, frobA_eA]
  by_cases hw : w ∈ R.frobWeights l
  · by_cases hr : D.frobOrder l i ∣ r
    · have hw1 := (R.add_nsmul_root_mem_iff hl0 i hr).2 hw
      by_cases hn : D.frobOrder l j ∣ n
      · have hw2 := (R.add_nsmul_root_mem_iff hl0 j hn).2 hw1
        by_cases ha : D.frobOrder l i ∣ a
        · simp only [hw, hw1, hw2, hr, hn, ha, and_self, ↓reduceIte, tmul_one_mul_tmul_one,
            R.frobWt_add_nsmul_root hl0 j hn hw1, R.frobWt_add_nsmul_root hl0 i hr hw]
        · simp only [ha, and_false, false_and, ↓reduceIte, zero_mul]
      · simp only [hn, and_false, false_and, ↓reduceIte, zero_mul, mul_zero]
    · simp only [hr, and_false, ↓reduceIte, mul_zero]
  · simp only [hw, false_and, ↓reduceIte, mul_zero]

open Classical in
lemma frobA_triple_F (i j : I) (a n r : ℕ) (w : Y →+ ℤ) :
    Fr (fA R i r (w + a • -R.root i + n • -R.root j) * fA R j n (w + a • -R.root i) *
        fA R i a w) =
      if w ∈ R.frobWeights l ∧ D.frobOrder l i ∣ a ∧ D.frobOrder l j ∣ n ∧ D.frobOrder l i ∣ r
      then (1 : S) ⊗ₜ (fA (R.frobRootDatum hl0) i (r / D.frobOrder l i)
          (R.frobWt l w + (a / D.frobOrder l i) • -(R.frobRootDatum hl0).root i +
            (n / D.frobOrder l j) • -(R.frobRootDatum hl0).root j) *
        fA (R.frobRootDatum hl0) j (n / D.frobOrder l j)
          (R.frobWt l w + (a / D.frobOrder l i) • -(R.frobRootDatum hl0).root i) *
        fA (R.frobRootDatum hl0) i (a / D.frobOrder l i) (R.frobWt l w)) else 0 := by
  rw [frobA_mul, frobA_mul, frobA_fA, frobA_fA, frobA_fA]
  by_cases hw : w ∈ R.frobWeights l
  · by_cases ha : D.frobOrder l i ∣ a
    · have hw1 := (R.add_nsmul_neg_root_mem_iff hl0 i ha).2 hw
      by_cases hn : D.frobOrder l j ∣ n
      · have hw2 := (R.add_nsmul_neg_root_mem_iff hl0 j hn).2 hw1
        by_cases hr : D.frobOrder l i ∣ r
        · simp only [hw, hw1, hw2, hr, hn, ha, and_self, ↓reduceIte, tmul_one_mul_tmul_one,
            R.frobWt_add_nsmul_neg_root hl0 j hn hw1, R.frobWt_add_nsmul_neg_root hl0 i ha hw]
        · simp only [hr, and_false, ↓reduceIte, zero_mul]
      · simp only [hn, and_false, false_and, ↓reduceIte, zero_mul, mul_zero]
    · simp only [ha, and_false, false_and, ↓reduceIte, mul_zero]
  · simp only [hw, false_and, ↓reduceIte, mul_zero]

lemma frobA_eA_eq_zero {j : I} {n : ℕ} {μ : Y →+ ℤ}
    (h : ¬ (μ ∈ R.frobWeights l ∧ D.frobOrder l j ∣ n)) : Fr (eA R j n μ) = 0 := by
  classical
  rw [frobA_eA]
  exact ite_eq_right h

lemma frobA_fA_eq_zero {j : I} {n : ℕ} {μ : Y →+ ℤ}
    (h : ¬ (μ ∈ R.frobWeights l ∧ D.frobOrder l j ∣ n)) : Fr (fA R j n μ) = 0 := by
  classical
  rw [frobA_fA]
  exact ite_eq_right h

lemma smul_frobA_triple_E_eq_zero (c : 𝒜) (i j : I) (a n r : ℕ) (w : Y →+ ℤ)
    (h : ¬ (w ∈ R.frobWeights l ∧ D.frobOrder l i ∣ a ∧ D.frobOrder l j ∣ n ∧
      D.frobOrder l i ∣ r)) :
    c • Fr (eA R i a (w + r • R.root i + n • R.root j) * eA R j n (w + r • R.root i) *
      eA R i r w) = 0 := by
  classical
  rw [frobA_triple_E, ite_eq_right h]
  exact smul_zero _

lemma frobA_braid_term_E {i j : I} (hji : j ≠ i) {μ : Y →+ ℤ} (hμ : μ ∈ R.frobWeights l)
    (n' r : ℕ) :
    braidCoeffE D i (D.frobOrder l i * r) •
        Fr (eA R i (negA D i j * (D.frobOrder l j * n') - D.frobOrder l i * r)
            (μ.comp (reflY R i) + (D.frobOrder l i * r) • R.root i +
              (D.frobOrder l j * n') • R.root j) *
          eA R j (D.frobOrder l j * n') (μ.comp (reflY R i) + (D.frobOrder l i * r) • R.root i) *
          eA R i (D.frobOrder l i * r) (μ.comp (reflY R i))) =
      (1 : S) ⊗ₜ (braidCoeffE (D.frobenius hl0) i r •
        (eA (R.frobRootDatum hl0) i (negA (D.frobenius hl0) i j * n' - r)
            ((R.frobWt l μ).comp (reflY (R.frobRootDatum hl0) i) +
              r • (R.frobRootDatum hl0).root i + n' • (R.frobRootDatum hl0).root j) *
          eA (R.frobRootDatum hl0) j n' ((R.frobWt l μ).comp (reflY (R.frobRootDatum hl0) i) +
              r • (R.frobRootDatum hl0).root i) *
          eA (R.frobRootDatum hl0) i r ((R.frobWt l μ).comp (reflY (R.frobRootDatum hl0) i)))) := by
  classical
  have hLpos := D.frobOrder_pos hl0 i
  have hb : negA D i j * (D.frobOrder l j * n') =
      D.frobOrder l i * (negA (D.frobenius hl0) i j * n') := by
    rw [← mul_assoc, ← mul_assoc, frobOrder_mul_negA_frobenius D hl0 hji.symm,
      mul_comm (negA D i j)]
  rw [frobA_triple_E, hb, ← Nat.mul_sub, ite_eq_left ⟨comp_reflY_mem_frobWeights R hl0 i hμ,
    dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_right _ _⟩, TensorProduct.tmul_smul]
  refine (smul_tmul_one_congr (l' := l') S (algebraMap_braidCoeffE D hl0 hl' i r) _).trans ?_
  simp only [Nat.mul_div_cancel_left _ hLpos, Nat.mul_div_cancel_left _ (D.frobOrder_pos hl0 j),
    frobWt_comp_reflY R hl0 i hμ]

lemma braidR_frobA_eA_ne {i j : I} (hji : j ≠ i) {μ : Y →+ ℤ} (hμ : μ ∈ R.frobWeights l)
    (n' : ℕ) :
    braidR S i (Fr (eA R j (D.frobOrder l j * n') μ)) =
      ∑ r ∈ range (negA (D.frobenius hl0) i j * n' + 1),
        (1 : S) ⊗ₜ (braidCoeffE (D.frobenius hl0) i r •
          (eA (R.frobRootDatum hl0) i (negA (D.frobenius hl0) i j * n' - r)
              ((R.frobWt l μ).comp (reflY (R.frobRootDatum hl0) i) +
                r • (R.frobRootDatum hl0).root i + n' • (R.frobRootDatum hl0).root j) *
            eA (R.frobRootDatum hl0) j n' ((R.frobWt l μ).comp (reflY (R.frobRootDatum hl0) i) +
                r • (R.frobRootDatum hl0).root i) *
            eA (R.frobRootDatum hl0) i r
              ((R.frobWt l μ).comp (reflY (R.frobRootDatum hl0) i)))) := by
  classical
  rw [frobA_eA, ite_eq_left ⟨hμ, dvd_mul_right _ _⟩,
    Nat.mul_div_cancel_left _ (D.frobOrder_pos hl0 j), braidR_tmul, braidA_eA_ne hji,
    TensorProduct.tmul_sum]

lemma frobA_braidA_eA_ne {i j : I} (hji : j ≠ i) (n : ℕ) (μ : Y →+ ℤ) :
    Fr (braidA i (eA R j n μ)) = braidR S i (Fr (eA R j n μ)) := by
  have hLpos := D.frobOrder_pos hl0 i
  rw [braidA_eA_ne hji, map_sum]
  by_cases h : μ ∈ R.frobWeights l ∧ D.frobOrder l j ∣ n
  · obtain ⟨hμ, n', rfl⟩ := h
    have hb : negA D i j * (D.frobOrder l j * n') =
        D.frobOrder l i * (negA (D.frobenius hl0) i j * n') := by
      rw [← mul_assoc, ← mul_assoc, frobOrder_mul_negA_frobenius D hl0 hji.symm,
        mul_comm (negA D i j)]
    refine (sum_range_eq_of_mul hLpos hb (fun r hr ↦ ?_) fun r _ ↦ ?_).trans
      (braidR_frobA_eA_ne R hl0 hl' hA S hji hμ n').symm
    · exact (map_smul _ _ _).trans
        (smul_frobA_triple_E_eq_zero R hl0 hl' hA S _ i j _ _ r _ fun hc ↦ hr hc.2.2.2)
    · exact (map_smul _ _ _).trans (frobA_braid_term_E R hl0 hl' hA S hji hμ n' r)
  · refine (Finset.sum_eq_zero fun r _ ↦ ?_).trans ((congrArg (braidR S i)
      (frobA_eA_eq_zero R hl0 hl' hA S h)).trans (LinearEquiv.map_zero _)).symm
    exact (map_smul _ _ _).trans (smul_frobA_triple_E_eq_zero R hl0 hl' hA S _ i j _ _ r _
      fun hc ↦ h ⟨(comp_reflY_mem_frobWeights_iff R hl0 i).1 hc.1, hc.2.2.1⟩)

lemma smul_frobA_triple_F_eq_zero (c : 𝒜) (i j : I) (a n r : ℕ) (w : Y →+ ℤ)
    (h : ¬ (w ∈ R.frobWeights l ∧ D.frobOrder l i ∣ a ∧ D.frobOrder l j ∣ n ∧
      D.frobOrder l i ∣ r)) :
    c • Fr (fA R i r (w + a • -R.root i + n • -R.root j) * fA R j n (w + a • -R.root i) *
      fA R i a w) = 0 := by
  classical
  rw [frobA_triple_F, ite_eq_right h]
  exact smul_zero _

lemma frobA_braid_term_F {i j : I} (hji : j ≠ i) {μ : Y →+ ℤ} (hμ : μ ∈ R.frobWeights l)
    (n' r : ℕ) :
    braidCoeffF D i (D.frobOrder l i * r) •
        Fr (fA R i (D.frobOrder l i * r)
            (μ.comp (reflY R i) +
              (negA D i j * (D.frobOrder l j * n') - D.frobOrder l i * r) • -R.root i +
              (D.frobOrder l j * n') • -R.root j) *
          fA R j (D.frobOrder l j * n') (μ.comp (reflY R i) +
            (negA D i j * (D.frobOrder l j * n') - D.frobOrder l i * r) • -R.root i) *
          fA R i (negA D i j * (D.frobOrder l j * n') - D.frobOrder l i * r)
            (μ.comp (reflY R i))) =
      (1 : S) ⊗ₜ (braidCoeffF (D.frobenius hl0) i r •
        (fA (R.frobRootDatum hl0) i r
            ((R.frobWt l μ).comp (reflY (R.frobRootDatum hl0) i) +
              (negA (D.frobenius hl0) i j * n' - r) • -(R.frobRootDatum hl0).root i +
              n' • -(R.frobRootDatum hl0).root j) *
          fA (R.frobRootDatum hl0) j n' ((R.frobWt l μ).comp (reflY (R.frobRootDatum hl0) i) +
              (negA (D.frobenius hl0) i j * n' - r) • -(R.frobRootDatum hl0).root i) *
          fA (R.frobRootDatum hl0) i (negA (D.frobenius hl0) i j * n' - r)
            ((R.frobWt l μ).comp (reflY (R.frobRootDatum hl0) i)))) := by
  classical
  have hLpos := D.frobOrder_pos hl0 i
  have hb : negA D i j * (D.frobOrder l j * n') =
      D.frobOrder l i * (negA (D.frobenius hl0) i j * n') := by
    rw [← mul_assoc, ← mul_assoc, frobOrder_mul_negA_frobenius D hl0 hji.symm,
      mul_comm (negA D i j)]
  rw [frobA_triple_F, hb, ← Nat.mul_sub, ite_eq_left ⟨comp_reflY_mem_frobWeights R hl0 i hμ,
    dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_right _ _⟩, TensorProduct.tmul_smul]
  refine (smul_tmul_one_congr (l' := l') S (algebraMap_braidCoeffF D hl0 hl' i r) _).trans ?_
  simp only [Nat.mul_div_cancel_left _ hLpos, Nat.mul_div_cancel_left _ (D.frobOrder_pos hl0 j),
    frobWt_comp_reflY R hl0 i hμ]

lemma braidR_frobA_fA_ne {i j : I} (hji : j ≠ i) {μ : Y →+ ℤ} (hμ : μ ∈ R.frobWeights l)
    (n' : ℕ) :
    braidR S i (Fr (fA R j (D.frobOrder l j * n') μ)) =
      ∑ r ∈ range (negA (D.frobenius hl0) i j * n' + 1),
        (1 : S) ⊗ₜ (braidCoeffF (D.frobenius hl0) i r •
          (fA (R.frobRootDatum hl0) i r
              ((R.frobWt l μ).comp (reflY (R.frobRootDatum hl0) i) +
                (negA (D.frobenius hl0) i j * n' - r) • -(R.frobRootDatum hl0).root i +
                n' • -(R.frobRootDatum hl0).root j) *
            fA (R.frobRootDatum hl0) j n' ((R.frobWt l μ).comp (reflY (R.frobRootDatum hl0) i) +
                (negA (D.frobenius hl0) i j * n' - r) • -(R.frobRootDatum hl0).root i) *
            fA (R.frobRootDatum hl0) i (negA (D.frobenius hl0) i j * n' - r)
              ((R.frobWt l μ).comp (reflY (R.frobRootDatum hl0) i)))) := by
  classical
  rw [frobA_fA, ite_eq_left ⟨hμ, dvd_mul_right _ _⟩,
    Nat.mul_div_cancel_left _ (D.frobOrder_pos hl0 j), braidR_tmul, braidA_fA_ne hji,
    TensorProduct.tmul_sum]

lemma frobA_braidA_fA_ne {i j : I} (hji : j ≠ i) (n : ℕ) (μ : Y →+ ℤ) :
    Fr (braidA i (fA R j n μ)) = braidR S i (Fr (fA R j n μ)) := by
  have hLpos := D.frobOrder_pos hl0 i
  rw [braidA_fA_ne hji, map_sum]
  by_cases h : μ ∈ R.frobWeights l ∧ D.frobOrder l j ∣ n
  · obtain ⟨hμ, n', rfl⟩ := h
    have hb : negA D i j * (D.frobOrder l j * n') =
        D.frobOrder l i * (negA (D.frobenius hl0) i j * n') := by
      rw [← mul_assoc, ← mul_assoc, frobOrder_mul_negA_frobenius D hl0 hji.symm,
        mul_comm (negA D i j)]
    refine (sum_range_eq_of_mul hLpos hb (fun r hr ↦ ?_) fun r _ ↦ ?_).trans
      (braidR_frobA_fA_ne R hl0 hl' hA S hji hμ n').symm
    · exact (map_smul _ _ _).trans
        (smul_frobA_triple_F_eq_zero R hl0 hl' hA S _ i j _ _ r _ fun hc ↦ hr hc.2.2.2)
    · exact (map_smul _ _ _).trans (frobA_braid_term_F R hl0 hl' hA S hji hμ n' r)
  · refine (Finset.sum_eq_zero fun r _ ↦ ?_).trans ((congrArg (braidR S i)
      (frobA_fA_eq_zero R hl0 hl' hA S h)).trans (LinearEquiv.map_zero _)).symm
    exact (map_smul _ _ _).trans (smul_frobA_triple_F_eq_zero R hl0 hl' hA S _ i j _ _ r _
      fun hc ↦ h ⟨(comp_reflY_mem_frobWeights_iff R hl0 i).1 hc.1, hc.2.2.1⟩)

lemma frobA_braidA_eA (i j : I) (n : ℕ) (μ : Y →+ ℤ) :
    Fr (braidA i (eA R j n μ)) = braidR S i (Fr (eA R j n μ)) := by
  rcases eq_or_ne j i with rfl | hji
  · exact frobA_braidA_eA_self R hl0 hl' hA S j n μ
  · exact frobA_braidA_eA_ne R hl0 hl' hA S hji n μ

lemma frobA_braidA_fA (i j : I) (n : ℕ) (μ : Y →+ ℤ) :
    Fr (braidA i (fA R j n μ)) = braidR S i (Fr (fA R j n μ)) := by
  rcases eq_or_ne j i with rfl | hji
  · exact frobA_braidA_fA_self R hl0 hl' hA S j n μ
  · exact frobA_braidA_fA_ne R hl0 hl' hA S hji n μ

lemma frobA_braidA_add (i : I) {a b : aForm R}
    (ha : Fr (braidA i a) = braidR S i (Fr a)) (hb : Fr (braidA i b) = braidR S i (Fr b)) :
    Fr (braidA i (a + b)) = braidR S i (Fr (a + b)) :=
  ((congrArg Fr ((braidA i).map_add a b)).trans (LinearMap.map_add _ _ _)).trans
    ((congrArg₂ (· + ·) ha hb).trans (((braidR S i).map_add _ _).symm.trans
      (congrArg (braidR S i) (LinearMap.map_add _ a b).symm)))

lemma frobA_braidA_zero (i : I) : Fr (braidA i 0) = braidR S i (Fr 0) :=
  ((congrArg Fr (braidA i).map_zero).trans (LinearMap.map_zero _)).trans
    ((braidR S i).map_zero.symm.trans (congrArg (braidR S i) (LinearMap.map_zero _).symm))

lemma frobA_braidA_mul (i : I) {a b : aForm R}
    (ha : Fr (braidA i a) = braidR S i (Fr a)) (hb : Fr (braidA i b) = braidR S i (Fr b)) :
    Fr (braidA i (a * b)) = braidR S i (Fr (a * b)) :=
  ((congrArg Fr (braidA_mul i a b)).trans (frobA_mul R hl0 hl' hA S _ _)).trans
    ((congrArg₂ (· * ·) ha hb).trans ((braidR_mul S i _ _).symm.trans
      (congrArg (braidR S i) (frobA_mul R hl0 hl' hA S a b).symm)))

lemma frobA_braidA_smul (i : I) (c : 𝒜) {a : aForm R}
    (ha : Fr (braidA i a) = braidR S i (Fr a)) :
    Fr (braidA i (c • a)) = braidR S i (Fr (c • a)) := by
  have h (y : S ⊗[𝒜] aForm (R.frobRootDatum hl0)) : braidR S i (c • y) = c • braidR S i y := by
    rw [← algebraMap_smul S c y, LinearEquiv.map_smul, algebraMap_smul]
  exact ((congrArg Fr ((braidA i).map_smul c a)).trans (LinearMap.map_smul _ c _)).trans
    ((congrArg (c • ·) ha).trans ((h _).symm.trans
      (congrArg (braidR S i) (LinearMap.map_smul _ c a).symm)))

/-- **[Lus] 41.1.9**: the quantum Frobenius homomorphism `Fr : 𝒜U̇ → _S U̇*` intertwines the
braid group actions, `Fr ∘ T''_{i,1} = T''_{i,1} ∘ Fr`, where on the right `T''_{i,1}` is the
symmetry of `_S U̇*` for the Cartan datum `(I, ∘)`. -/
theorem frobA_braidA (i : I) (x : aForm R) : Fr (braidA i x) = braidR S i (Fr x) := by
  obtain ⟨x, hx⟩ := x
  unfold aForm at hx
  induction hx using NonUnitalAlgebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨μ, rfl⟩ | ⟨j, n, μ, rfl | rfl⟩
    · exact frobA_braidA_oneA R hl0 hl' hA S i μ
    · exact frobA_braidA_eA R hl0 hl' hA S i j n μ
    · exact frobA_braidA_fA R hl0 hl' hA S i j n μ
  | add x x' hx hx' ih ih' =>
    exact frobA_braidA_add R hl0 hl' hA S i (a := ⟨x, hx⟩) (b := ⟨x', hx'⟩) ih ih'
  | zero => exact frobA_braidA_zero R hl0 hl' hA S i
  | mul x x' hx hx' ih ih' =>
    exact frobA_braidA_mul R hl0 hl' hA S i (a := ⟨x, hx⟩) (b := ⟨x', hx'⟩) ih ih'
  | smul c x hx ih => exact frobA_braidA_smul R hl0 hl' hA S i c (a := ⟨x, hx⟩) ih

/-- **[Lus] 41.1.9** on `_S U̇`: `Fr ∘ T''_{i,1} = T''_{i,1} ∘ Fr` as maps `_S U̇ → _S U̇*`, for
every `𝒜'`-algebra `S`. -/
theorem frobR_braidR (i : I) (z : S ⊗[𝒜] aForm R) :
    frobR R hl0 hl' hA S (braidR S i z) = braidR S i (frobR R hl0 hl' hA S z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    rw [braidR_tmul, frobR_tmul, frobR_tmul, LinearEquiv.map_smul,
      frobA_braidA R hl0 hl' hA S i x]
  | add z z' hz hz' =>
    exact ((congrArg (frobR R hl0 hl' hA S) ((braidR S i).map_add z z')).trans
      (map_add _ _ _)).trans ((congrArg₂ (· + ·) hz hz').trans
        (((braidR S i).map_add _ _).symm.trans (congrArg (braidR S i) (map_add _ z z').symm)))

/-- **[Lus] 41.1.9** for the inverse symmetries `T'_{i,-1} = T''_{i,1}⁻¹` on `_S U̇`. -/
theorem frobR_braidR_symm (i : I) (z : S ⊗[𝒜] aForm R) :
    frobR R hl0 hl' hA S ((braidR S i).symm z) =
      (braidR S i).symm (frobR R hl0 hl' hA S z) := by
  refine (braidR (R := R.frobRootDatum hl0) S i).injective ?_
  rw [← frobR_braidR R hl0 hl' hA S i, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end Compat

end Modified

end LieLean.QuantumGroup
