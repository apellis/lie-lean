/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.IntegralPBWPreimage
import LieLean.Algebra.QuantumGroup.LusztigF.QuotientComul
import LieLean.Algebra.QuantumGroup.Modified.FormRight
import LieLean.Algebra.QuantumGroup.CrystalBasis.NegativePart
import LieLean.Algebra.QuantumGroup.Verma

/-!
# Weight spaces of `f`, dual bases and the commutators of `x^±` with `Eᵢ`, `Fᵢ`

Preliminaries for the quasi-R-matrix ([Lus] 4.1), over `𝕂 = ℚ(v)`:

* the weight spaces `f_ν` of Lusztig's algebra `f = 'f / I` (`quotientWeightSpace`), the
  restriction of the form `( , )` to `f_ν` and its nondegeneracy
  (`nondegenerate_quotientWeightForm`);
* the expansions `x = Σ_b (x, b*) b = Σ_b (x, b) b*` in a basis of `f_ν` and its dual basis
  (`eq_sum_dualBasis_left`, `eq_sum_dualBasis_right`);
* an exchange identity for adjoint maps, `Σ_b L(b) ⊗ b* = Σ_c c ⊗ M(c*)`
  (`sum_tmul_eq_sum_tmul_of_adjoint`), used to compare the sums in [Lus] 4.1.2 (b);
* the embedding `f → U`, `x ↦ x⁻` (`quotientMinus`), and the commutators
  `Eᵢ y⁻ - y⁻ Eᵢ`, `Fᵢ x⁺ - x⁺ Fᵢ` in terms of the skew derivations ([Lus] 3.1.6;
  `E_mul_quotientMinus_sub`, `F_mul_quotientPlus_sub`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.2.13, 3.1.6, 4.1.2.
-/

open LieLean TensorProduct

noncomputable section

/-! ### An exchange identity for adjoint maps -/

namespace LinearMap.BilinForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Let `(b, b*)`, `(c, c*)` be finite families with the expansions
`L(b_s) = Σ_t B(L b_s, c*_t) c_t` and `M(c*_t) = Σ_s B(M c*_t, b_s) b*_s`, and let `L`, `M` be
adjoint in the sense `B(L b_s, c*_t) = B(M c*_t, b_s)`. Then
`Σ_s L(b_s) ⊗ b*_s = Σ_t c_t ⊗ M(c*_t)`. -/
theorem sum_tmul_eq_sum_tmul_of_adjoint {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : LinearMap.BilinForm K V) {b bs : ι → V} {c cs : κ → V} (L M : V →ₗ[K] V)
    (hc : ∀ s, L (b s) = ∑ t, B (L (b s)) (cs t) • c t)
    (hbs : ∀ t, M (cs t) = ∑ s, B (M (cs t)) (b s) • bs s)
    (hLM : ∀ s t, B (L (b s)) (cs t) = B (M (cs t)) (b s)) :
    ∑ s, L (b s) ⊗ₜ[K] bs s = ∑ t, c t ⊗ₜ[K] M (cs t) := by
  calc ∑ s, L (b s) ⊗ₜ[K] bs s
      = ∑ s, ∑ t, B (L (b s)) (cs t) • (c t ⊗ₜ[K] bs s) := by
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        conv_lhs => rw [hc s]
        rw [TensorProduct.sum_tmul]
        simp only [TensorProduct.smul_tmul']
    _ = ∑ t, ∑ s, B (M (cs t)) (b s) • (c t ⊗ₜ[K] bs s) := by
        rw [Finset.sum_comm]; simp only [hLM]
    _ = ∑ t, c t ⊗ₜ[K] M (cs t) := by
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        conv_rhs => rw [hbs t]
        rw [TensorProduct.tmul_sum]
        simp only [TensorProduct.tmul_smul]

end LinearMap.BilinForm

namespace LieLean.QuantumGroup

open LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X

/-! ### Weight spaces of `f` -/

section Weight

variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- The weight space `f_ν` of Lusztig's algebra `f = 'f / I`. -/
abbrev quotientWeightSpace (ν : I →₀ ℕ) : Submodule 𝕂 (Quotient D 𝕧) :=
  (LusztigF.weightSpace 𝕂 ν).map (toQuotient D 𝕧).toLinearMap

instance (ν : I →₀ ℕ) : FiniteDimensional 𝕂 (quotientWeightSpace D ν) :=
  Module.Finite.map _ _

/-- The form `( , )` restricted to `f_ν`. -/
abbrev quotientWeightForm (ν : I →₀ ℕ) : LinearMap.BilinForm 𝕂 (quotientWeightSpace D ν) :=
  (quotientForm D).restrict (quotientWeightSpace D ν)

lemma quotientForm_eq_zero_of_ne {ν μ : I →₀ ℕ} (h : ν ≠ μ) {x y : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D ν) (hy : y ∈ quotientWeightSpace D μ) :
    quotientForm D x y = 0 := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  change quotientForm D (toQuotient D 𝕧 a) (toQuotient D 𝕧 b) = 0
  rw [quotientForm_toQuotient]
  exact form_eq_zero_of_ne D 𝕧 h ha hb

lemma isSymm_quotientWeightForm (ν : I →₀ ℕ) : (quotientWeightForm D ν).IsSymm :=
  ⟨fun x y ↦ quotientForm_comm D x y⟩

/-- The form on `f_ν` is nondegenerate. -/
theorem nondegenerate_quotientWeightForm (ν : I →₀ ℕ) :
    (quotientWeightForm D ν).Nondegenerate := by
  classical
  have key : ∀ x : quotientWeightSpace D ν, (∀ y, quotientWeightForm D ν x y = 0) → x = 0 := by
    intro x hx
    obtain ⟨x, ⟨a, ha, hax⟩⟩ := x
    apply Subtype.ext
    change x = 0
    apply quotientForm_separates D
    intro y
    obtain ⟨b, rfl⟩ := toQuotient_surjective D 𝕧 y
    subst hax
    change quotientForm D (toQuotient D 𝕧 a) (toQuotient D 𝕧 b) = 0
    rw [quotientForm_toQuotient]
    have hwa : FreeAlgebra.weightProj 𝕂 ν a = a := by
      rw [FreeAlgebra.weightProj_of_mem (R := 𝕂) ha]; simp
    rw [← hwa, form_weightProj, ← quotientForm_toQuotient]
    exact hx ⟨_, ⟨_, FreeAlgebra.weightProj_mem ν b, rfl⟩⟩
  refine ⟨key, fun y hy ↦ key y fun x ↦ ?_⟩
  rw [(isSymm_quotientWeightForm D ν).eq]
  exact hy x

variable {D}

/-- The basis of `f_ν` dual to `b` for the form `( , )`. -/
abbrev quotientDualBasis {ν : I →₀ ℕ} {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Module.Basis ι 𝕂 (quotientWeightSpace D ν)) :
    Module.Basis ι 𝕂 (quotientWeightSpace D ν) :=
  (quotientWeightForm D ν).dualBasis (nondegenerate_quotientWeightForm D ν) b

/-- Expansion in a basis of `f_ν`: `x = Σ_s (x, b*_s) b_s`. -/
theorem eq_sum_dualBasis_left {ν : I →₀ ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝕂 (quotientWeightSpace D ν)) {x : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D ν) :
    x = ∑ s, quotientForm D x (quotientDualBasis b s) • (b s : Quotient D 𝕧) := by
  set hB := nondegenerate_quotientWeightForm D ν
  have h := (b.sum_repr ⟨x, hx⟩).symm
  have hrepr : ∀ s, b.repr ⟨x, hx⟩ s =
      quotientWeightForm D ν ⟨x, hx⟩ ((quotientWeightForm D ν).dualBasis hB b s) := by
    intro s
    conv_lhs => rw [← LinearMap.BilinForm.dualBasis_dualBasis hB
      (isSymm_quotientWeightForm D ν) b]
    rw [LinearMap.BilinForm.dualBasis_repr_apply]
  have := congrArg Subtype.val h
  simp only [Submodule.coe_sum, Submodule.coe_smul, hrepr] at this
  exact this

/-- Expansion in the dual basis of `f_ν`: `x = Σ_s (x, b_s) b*_s`. -/
theorem eq_sum_dualBasis_right {ν : I →₀ ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝕂 (quotientWeightSpace D ν)) {x : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D ν) :
    x = ∑ s, quotientForm D x (b s) • (quotientDualBasis b s : Quotient D 𝕧) := by
  set hB := nondegenerate_quotientWeightForm D ν
  have h := (((quotientWeightForm D ν).dualBasis hB b).sum_repr ⟨x, hx⟩).symm
  have := congrArg Subtype.val h
  simp only [Submodule.coe_sum, Submodule.coe_smul,
    LinearMap.BilinForm.dualBasis_repr_apply] at this
  exact this

lemma quotientLDeriv_mem {μ : I →₀ ℕ} (i : I) {x : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D (μ + Finsupp.single i 1)) :
    quotientLDeriv D i x ∈ quotientWeightSpace D μ := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨_, LusztigF.lDeriv_mem_weightSpace D 𝕧 i ha, (quotientLDeriv_toQuotient D i a).symm⟩

lemma quotientRDeriv_mem {μ : I →₀ ℕ} (i : I) {x : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D (μ + Finsupp.single i 1)) :
    quotientRDeriv D i x ∈ quotientWeightSpace D μ := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨_, LusztigF.rDeriv_mem_weightSpace D 𝕧 i ha, (quotientRDeriv_toQuotient D i a).symm⟩

lemma quotientLDeriv_eq_zero {ν : I →₀ ℕ} (i : I) (hν : ν i = 0) {x : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D ν) : quotientLDeriv D i x = 0 := by
  obtain ⟨a, ha, rfl⟩ := hx
  change quotientLDeriv D i (toQuotient D 𝕧 a) = 0
  rw [quotientLDeriv_toQuotient, LusztigF.lDeriv_eq_zero_of_mem D 𝕧 i hν ha, map_zero]

lemma quotientRDeriv_eq_zero {ν : I →₀ ℕ} (i : I) (hν : ν i = 0) {x : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D ν) : quotientRDeriv D i x = 0 := by
  obtain ⟨a, ha, rfl⟩ := hx
  change quotientRDeriv D i (toQuotient D 𝕧 a) = 0
  rw [quotientRDeriv_toQuotient, LusztigF.rDeriv_eq_zero_of_mem D 𝕧 i hν ha, map_zero]

omit [Finite I] in
lemma θ_mul_mem_quotientWeightSpace {μ : I →₀ ℕ} (i : I) {x : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D μ) :
    toQuotient D 𝕧 (θ 𝕂 i) * x ∈ quotientWeightSpace D (μ + Finsupp.single i 1) := by
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨θ 𝕂 i * a, ?_, by simp⟩
  rw [add_comm]
  exact mul_mem_weightSpace (θ_mem_weightSpace i) ha

omit [Finite I] in
lemma mul_θ_mem_quotientWeightSpace {μ : I →₀ ℕ} (i : I) {x : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D μ) :
    x * toQuotient D 𝕧 (θ 𝕂 i) ∈ quotientWeightSpace D (μ + Finsupp.single i 1) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a * θ 𝕂 i, mul_mem_weightSpace ha (θ_mem_weightSpace i), by simp⟩

omit [Finite I] in
lemma one_mem_quotientWeightSpace_zero : (1 : Quotient D 𝕧) ∈ quotientWeightSpace D 0 :=
  ⟨1, by simpa [monomial] using monomial_mem_weightSpace (k := 𝕂) ([] : List I), by simp⟩

/-- `f_0 = 𝕂 · 1`, with the coefficient given by the form. -/
lemma eq_smul_one_of_mem_zero {x : Quotient D 𝕧} (hx : x ∈ quotientWeightSpace D 0) :
    x = quotientForm D x 1 • 1 := by
  obtain ⟨a, ha, rfl⟩ := hx
  change toQuotient D 𝕧 a = quotientForm D (toQuotient D 𝕧 a) 1 • 1
  rw [← map_one (toQuotient D 𝕧), quotientForm_toQuotient, form_one_right, map_one]
  conv_lhs => rw [eq_algebraMap_of_mem_weightSpace_zero ha]
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

omit [Finite I] [DecidableEq I] in
lemma thetaNorm_ratFunc_ne_zero (i : I) : thetaNorm D 𝕧 i ≠ 0 :=
  thetaNorm_ne_zero D 𝕧 (by
    rw [← pow_mul]
    exact ratFunc_X_not_root _ (Nat.mul_pos (D.d_pos i) (by decide)))

/-- The adjoint of `ᵢr` is left multiplication by `θᵢ / (θᵢ, θᵢ)` ([Lus] 1.2.13). -/
lemma quotientForm_lDeriv_eq (i : I) (x y : Quotient D 𝕧) :
    quotientForm D (quotientLDeriv D i x) y =
      quotientForm D ((thetaNorm D 𝕧 i)⁻¹ • (toQuotient D 𝕧 (θ 𝕂 i) * y)) x := by
  rw [LinearMap.map_smul₂, quotientForm_comm D (toQuotient D 𝕧 (θ 𝕂 i) * y) x,
    ← quotientForm_lDeriv, smul_eq_mul, inv_mul_cancel_left₀ (thetaNorm_ratFunc_ne_zero i)]

/-- The adjoint of `rᵢ` is right multiplication by `θᵢ / (θᵢ, θᵢ)` ([Lus] 1.2.13). -/
lemma quotientForm_rDeriv_eq (i : I) (x y : Quotient D 𝕧) :
    quotientForm D (quotientRDeriv D i x) y =
      quotientForm D ((thetaNorm D 𝕧 i)⁻¹ • (y * toQuotient D 𝕧 (θ 𝕂 i))) x := by
  rw [LinearMap.map_smul₂, quotientForm_comm D (y * toQuotient D 𝕧 (θ 𝕂 i)) x,
    ← quotientForm_rDeriv, smul_eq_mul, inv_mul_cancel_left₀ (thetaNorm_ratFunc_ne_zero i)]

/-- The exchange identity on weight spaces: if `L : f_ν → f_μ` and `M : f_μ → f_ν` are adjoint,
then `Σ_b L(b) ⊗ b* = Σ_c c ⊗ M(c*)` for bases `b` of `f_ν` and `c` of `f_μ`. -/
theorem sum_tmul_dualBasis_of_adjoint {ν μ : I →₀ ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis ι 𝕂 (quotientWeightSpace D ν))
    (c : Module.Basis κ 𝕂 (quotientWeightSpace D μ)) (L M : Module.End 𝕂 (Quotient D 𝕧))
    (hL : ∀ x ∈ quotientWeightSpace D ν, L x ∈ quotientWeightSpace D μ)
    (hM : ∀ y ∈ quotientWeightSpace D μ, M y ∈ quotientWeightSpace D ν)
    (hLM : ∀ x y, quotientForm D (L x) y = quotientForm D (M y) x) :
    ∑ s, L (b s) ⊗ₜ[𝕂] (quotientDualBasis b s : Quotient D 𝕧) =
      ∑ t, (c t : Quotient D 𝕧) ⊗ₜ[𝕂] M (quotientDualBasis c t) :=
  LinearMap.BilinForm.sum_tmul_eq_sum_tmul_of_adjoint (quotientForm D) L M
    (fun s ↦ eq_sum_dualBasis_left c (hL _ (b s).2))
    (fun t ↦ eq_sum_dualBasis_right b (hM _ (quotientDualBasis c t).2))
    (fun _ _ ↦ hLM _ _)

/-- The exchange identity with the legs swapped: `Σ_b b ⊗ L(b*) = Σ_c M(c) ⊗ c*`. -/
theorem sum_tmul_dualBasis_of_adjoint' {ν μ : I →₀ ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis ι 𝕂 (quotientWeightSpace D ν))
    (c : Module.Basis κ 𝕂 (quotientWeightSpace D μ)) (L M : Module.End 𝕂 (Quotient D 𝕧))
    (hL : ∀ x ∈ quotientWeightSpace D ν, L x ∈ quotientWeightSpace D μ)
    (hM : ∀ y ∈ quotientWeightSpace D μ, M y ∈ quotientWeightSpace D ν)
    (hLM : ∀ x y, quotientForm D (L x) y = quotientForm D (M y) x) :
    ∑ s, (b s : Quotient D 𝕧) ⊗ₜ[𝕂] L (quotientDualBasis b s) =
      ∑ t, M (c t) ⊗ₜ[𝕂] (quotientDualBasis c t : Quotient D 𝕧) := by
  have h := LinearMap.BilinForm.sum_tmul_eq_sum_tmul_of_adjoint (quotientForm D)
    (b := fun s ↦ (quotientDualBasis b s : Quotient D 𝕧)) (bs := fun s ↦ (b s : Quotient D 𝕧))
    (c := fun t ↦ (quotientDualBasis c t : Quotient D 𝕧)) (cs := fun t ↦ (c t : Quotient D 𝕧))
    L M (fun s ↦ eq_sum_dualBasis_right c (hL _ (quotientDualBasis b s).2))
    (fun t ↦ eq_sum_dualBasis_left b (hM _ (c t).2)) (fun _ _ ↦ hLM _ _)
  have := congrArg (TensorProduct.comm 𝕂 _ _) h
  simpa only [map_sum, TensorProduct.comm_tmul] using this

end Weight

/-! ### The embeddings `x ↦ x^±` and their commutators with `Eᵢ`, `Fᵢ` -/

section Embedding

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y)

/-- The negative embedding `f → U`, `x ↦ x⁻`, descended through the radical. -/
def quotientMinus : Quotient D 𝕧 →ₐ[𝕂] QuantumGroup R 𝕧 :=
  (radical D 𝕧).ringCon.liftₐ (minusHom R 𝕧) fun x y h ↦ by
    apply sub_eq_zero.mp
    change minusHom R 𝕧 x - minusHom R 𝕧 y = 0
    rw [← map_sub, minusHom_eq_zero_iff R 𝕧 ratFunc_X_not_root,
      ← radical_eq_serreIdeal_ratFunc]
    exact ((radical D 𝕧).rel_iff x y).mp h

@[simp] theorem quotientMinus_toQuotient (x : LusztigF 𝕂 I) :
    quotientMinus R (toQuotient D 𝕧 x) = minusHom R 𝕧 x := rfl

theorem quotientMinus_injective : Function.Injective (quotientMinus R) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  rw [toQuotient_eq_zero_iff, radical_eq_serreIdeal_ratFunc]
  exact (minusHom_eq_zero_iff R 𝕧 ratFunc_X_not_root x).mp hx

@[simp] lemma quotientPlus_θ (i : I) : quotientPlus R (toQuotient D 𝕧 (θ 𝕂 i)) = E R 𝕧 i := by
  simp

@[simp] lemma quotientMinus_θ (i : I) :
    quotientMinus R (toQuotient D 𝕧 (θ 𝕂 i)) = F R 𝕧 i := by
  simp

/-- [Lus] 3.1.6 for `x⁻`: `Eᵢ y⁻ - y⁻ Eᵢ = (K̃ᵢ ᵢr(y)⁻ - rᵢ(y)⁻ K̃₋ᵢ)/(vᵢ - vᵢ⁻¹)`. -/
theorem E_mul_quotientMinus_sub (i : I) (y : Quotient D 𝕧) :
    E R 𝕧 i * quotientMinus R y - quotientMinus R y * E R 𝕧 i =
      (𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹)⁻¹ •
        (K R 𝕧 (ktilde R i) * quotientMinus R (quotientLDeriv D i y) -
          quotientMinus R (quotientRDeriv D i y) * K R 𝕧 (-ktilde R i)) := by
  obtain ⟨a, rfl⟩ := toQuotient_surjective D 𝕧 y
  have h := congrArg (chevalley R 𝕧) (F_mul_plusHom (R := R) (v := 𝕧) i a)
  simp only [map_mul, map_sub, map_smul, chevalley_F, chevalley_plusHom, chevalley_K,
    neg_neg] at h
  simp only [quotientLDeriv_toQuotient, quotientRDeriv_toQuotient, quotientMinus_toQuotient]
  rw [h, smul_sub, smul_sub]
  abel

/-- [Lus] 3.1.6: `Fᵢ x⁺ - x⁺ Fᵢ = -(rᵢ(x)⁺ K̃ᵢ - K̃₋ᵢ ᵢr(x)⁺)/(vᵢ - vᵢ⁻¹)`. -/
theorem F_mul_quotientPlus_sub (i : I) (x : Quotient D 𝕧) :
    F R 𝕧 i * quotientPlus R x - quotientPlus R x * F R 𝕧 i =
      -((𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹)⁻¹ •
        (quotientPlus R (quotientRDeriv D i x) * K R 𝕧 (ktilde R i) -
          K R 𝕧 (-ktilde R i) * quotientPlus R (quotientLDeriv D i x))) := by
  obtain ⟨a, rfl⟩ := toQuotient_surjective D 𝕧 x
  simp only [quotientLDeriv_toQuotient, quotientRDeriv_toQuotient, quotientPlus_toQuotient]
  rw [F_mul_plusHom]
  abel

lemma K_mul_quotientPlus_of_mem (l : Y) {μ : I →₀ ℕ} {x : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D μ) :
    K R 𝕧 l * quotientPlus R x = 𝕧 ^ R.rootSum μ l • (quotientPlus R x * K R 𝕧 l) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact K_mul_plusHom_of_mem ha l

lemma K_mul_quotientMinus_of_mem (l : Y) {μ : I →₀ ℕ} {x : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D μ) :
    K R 𝕧 l * quotientMinus R x = 𝕧 ^ R.rootSum μ (-l) • (quotientMinus R x * K R 𝕧 l) := by
  obtain ⟨a, ha, rfl⟩ := hx
  have h := congrArg (chevalley R 𝕧) (K_mul_plusHom_of_mem (R := R) ha (-l))
  simp only [map_mul, map_smul, chevalley_K, chevalley_plusHom, neg_neg] at h
  exact h

end Embedding

end LieLean.QuantumGroup
