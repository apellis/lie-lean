/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ChangeOfRings.Basic
import LieLean.Algebra.QuantumGroup.GabberKac.SerreSpanSign
import LieLean.Algebra.QuantumGroup.PBW.KostantDimension

/-!
# The quasi-classical case: a presentation of `_F f`

Let `F` be a field of characteristic zero which is an `𝒜`-algebra, `𝒜 = ℤ[v, v⁻¹]`, such that
the image `ε` of `v` satisfies `ε^{dᵢ} = ±1` for all `i` (the quasi-classical case,
[Lus] 33.2.1). Then `_F f = F ⊗_𝒜 𝒜f` is presented by the generators `θᵢ` and the quantum Serre
relations with parameter `ε` ([Lus] Prop. 33.2.2 (c)): the map
`F⟨θᵢ⟩ / (Serre relations at ε) → _F f`, `θᵢ ↦ 1 ⊗ θᵢ`, is an isomorphism
(`quasiClassicalEquiv`).

Lusztig also assumes that the Cartan datum has no odd cycles; the argument below does not need
it.

## Main results

* `quasiClassicalHom_surjective`: `θᵢ ↦ 1 ⊗ θᵢ` maps `F⟨θᵢ⟩` onto `_F f`.
* `quasiClassicalHom_eq_zero_iff`: its kernel is the ideal of the quantum Serre relations.
* `quasiClassicalEquiv`: **[Lus] Prop. 33.2.2 (c)**.

## Proof

Our argument; Lusztig's goes through the algebras `A`, `A₀` of 33.2.1. The map
`Ψ : F⟨θᵢ⟩ → _F f` is surjective since `[n]ᵢ! = ±n! ≠ 0` at `ε^{dᵢ} = ±1`, and it kills the
quantum Serre elements since their `𝒜`-forms vanish in `𝒜f`. The canonical basis `1 ⊗ b`,
`b ∈ B` (`baseChangeCanonicalBasis`) is graded by weight, so the kernel of `Ψ` is the sum of its
weight components. On the words of weight `ν`, the kernel has dimension at most
`#{words} - #B_ν = dim Z_ν`, where `Z_ν` is the span of the classical Serre products of weight
`ν` (quantum Gabber–Kac, `mem_serreSpan_of_mem_radical_and_finrank_serreSpan`). The span of the
Serre products at the parameters `ε^{dᵢ} = ±1` has the same dimension
(`finrank_serreSpan_of_sq_eq_one`, a twist of the words by signs), so it is the whole kernel.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 33.2.1, 33.2.2.
-/

open scoped RatFunc TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF FreeAlgebra Module

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

universe u

variable {I : Type u} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-! ### Quantum integers at `±1` -/

lemma qInt_of_sq_eq_one {K : Type*} [Field K] {ε : K} (hε : ε ^ 2 = 1) (n : ℕ) :
    qInt ε n = n * ε ^ (n - 1) := by
  have hinv : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right (by rw [← sq, hε])
  rw [qInt, hinv]
  rw [Finset.sum_congr rfl fun s hs ↦ show ε ^ (n - 1 - s) * ε ^ s = ε ^ (n - 1) by
    rw [← pow_add, Nat.sub_add_cancel (by have := Finset.mem_range.1 hs; omega)]]
  simp

lemma qFactorial_ne_zero_of_sq_eq_one {K : Type*} [Field K] [CharZero K] {ε : K}
    (hε : ε ^ 2 = 1) (n : ℕ) : qFactorial ε n ≠ 0 := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qFactorial_succ, qInt_of_sq_eq_one hε]
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast n.succ_ne_zero) (pow_ne_zero _ hε0)) ih

/-! ### The weight components of the canonical basis -/

/-- The elements of `B_ν`, as indices of the canonical basis `B`. -/
def canonicalIndexAt (ν : I →₀ ℕ) : Set (canonicalBasis D) :=
  {b | (b : Um D 𝕧) ∈ canonicalBasisAt D ν}

lemma mem_Uw_of_mem_canonicalBasisAt {ν : I →₀ ℕ} {x : Um D 𝕧}
    (hx : x ∈ canonicalBasisAt D ν) : x ∈ Uw D 𝕧 ν := by
  rw [← span_canonicalBasisAt]
  exact Submodule.subset_span hx

lemma eq_of_mem_canonicalBasisAt {ν μ : I →₀ ℕ} {x : Um D 𝕧}
    (hν : x ∈ canonicalBasisAt D ν) (hμ : x ∈ canonicalBasisAt D μ) : ν = μ := by
  by_contra h
  have h0 : x ≠ 0 := by
    rw [canonicalBasisAt_eq_range] at hν
    obtain ⟨b, rfl⟩ := hν
    exact negGlobal_ne_zero D b
  have h1 := proj_of_mem_Uw (mem_Uw_of_mem_canonicalBasisAt D hν) (toZ ν)
  rw [proj_of_mem_Uw (mem_Uw_of_mem_canonicalBasisAt D hμ)] at h1
  have hne : toZ μ ≠ toZ ν := fun h' ↦ h (toZ_injective h').symm
  have hx0 : x = 0 := by simpa [hne, eq_comm] using h1
  exact h0 hx0

omit [Finite I] [DecidableEq I] in
lemma finiteDimensional_Uw (ν : I →₀ ℕ) : FiniteDimensional 𝕂 (Uw D 𝕧 ν) := by
  rw [Uw]; infer_instance

/-- `B_ν` is a basis of `f_ν`. -/
def canonicalBasisAtBasis (ν : I →₀ ℕ) :
    Module.Basis (canonicalBasisAt D ν) 𝕂 (Uw D 𝕧 ν) :=
  (Module.Basis.span (linearIndependent_canonicalBasisAt D ν)).map
    (LinearEquiv.ofEq _ _ (by rw [Subtype.range_coe]; exact span_canonicalBasisAt D ν))

lemma finite_canonicalBasisAt (ν : I →₀ ℕ) : Finite (canonicalBasisAt D ν) := by
  have := finiteDimensional_Uw D ν
  exact Module.Finite.finite_basis (canonicalBasisAtBasis D ν)

lemma natCard_canonicalBasisAt (ν : I →₀ ℕ) :
    Nat.card (canonicalBasisAt D ν) = finrank 𝕂 (Uw D 𝕧 ν) :=
  (Module.finrank_eq_nat_card_basis (canonicalBasisAtBasis D ν)).symm

omit [DecidableEq I] in
/-- `dim f_ν + dim Z_ν = #{words of weight ν}`, with `Z_ν` the span of the classical Serre
products of weight `ν` ([Lus] 33.1.3). -/
lemma finrank_Uw_add_finrank_serreSpan (ν : I →₀ ℕ) :
    finrank 𝕂 (Uw D 𝕧 ν) + finrank ℚ (serreSpan D (fun _ ↦ (1 : ℚ)) ν) =
      Fintype.card (Words ν) := by
  classical
  have := Fintype.ofFinite I
  have hv := transcendental_ratFunc_X
  have hv0 : (𝕧 : 𝕂) ≠ 0 := RatFunc.X_ne_zero
  have hvn : ∀ n : ℕ, 0 < n → (𝕧 : 𝕂) ^ n ≠ 1 := fun _ hn ↦ pow_ne_one_of_transcendental hv hn
  set V := LusztigF.weightSpace 𝕂 ν
  set f := (serreSubmodule D 𝕧).mkQ.domRestrict V
  have hrange : LinearMap.range f = Uw D 𝕧 ν := by
    rw [LinearMap.range_domRestrict]; rfl
  have hker : LinearMap.ker f = (serreSpan D (fun i ↦ 𝕧 ^ D.d i) ν).comap V.subtype := by
    ext y
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, f,
      LinearMap.domRestrict_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      mem_serreSubmodule]
    exact ⟨fun h ↦ (mem_serreSpan_of_mem_radical_and_finrank_serreSpan D hv ν).1 _
      (serreIdeal_le_radical hv0 hvn h) y.2, serreSpan_le_serreIdeal D hv0 hvn⟩
  have hSer : finrank 𝕂 ((serreSpan D (fun i ↦ 𝕧 ^ D.d i) ν).comap V.subtype) =
      finrank 𝕂 (serreSpan D (fun i ↦ 𝕧 ^ D.d i) ν) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
      inf_eq_right.2 (serreSpan_le_weightSpace D _ ν)]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker, hSer, finrank_weightSpace,
    (mem_serreSpan_of_mem_radical_and_finrank_serreSpan D hv ν).2] at hrn
  exact hrn

/-! ### Words in `𝒜f` -/

/-- The product `θ_w = θ_{w₁} ⋯ θ_{wₙ}` in `𝒜f`. -/
def integralWord (w : List I) : quotientIntegralForm D :=
  (w.map fun i ↦ integralGenerator D i 1).prod

omit [Finite I] in
lemma coe_integralGenerator_one (i : I) :
    (integralGenerator D i 1 : LusztigF.Quotient D 𝕧) = toQuotient D 𝕧 (θ 𝕂 i) := by
  simp [integralGenerator, quotientIntegralGenerator, qDivPow, qFactorial, qInt]

omit [Finite I] in
lemma coe_integralWord (w : List I) :
    (integralWord D w : LusztigF.Quotient D 𝕧) = toQuotient D 𝕧 (wordBasis 𝕂 I w) := by
  rw [integralWord, wordBasis_apply, map_list_prod, SubmonoidClass.coe_list_prod, List.map_map,
    List.map_map]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  exact coe_integralGenerator_one D i

lemma integralWord_mem_span (w : List I) :
    integralWord D w ∈ Submodule.span 𝒜
      (integralCanonicalBasis D '' canonicalIndexAt D (wordWeight w)) := by
  set ν := wordWeight w
  set x : Um D 𝕧 := Submodule.Quotient.mk (wordBasis 𝕂 I w)
  have hxw : x ∈ Uw D 𝕧 ν :=
    Submodule.mem_map_of_mem (wordBasis_mem_wordSpan (R := 𝕂) w)
  have hxi : x ∈ negIntegral D := by
    rw [mem_negIntegral]
    change negativeToQuotient D _ ∈ _
    rw [negativeToQuotient_mk, ← coe_integralWord]
    exact (integralWord D w).2
  have hx : x ∈ Submodule.span 𝒜 (canonicalBasisAt D ν) := by
    rw [span_canonicalBasisAt_laurent]; exact ⟨hxi, hxw⟩
  have key : ∀ y (hy : y ∈ Submodule.span 𝒜 (canonicalBasisAt D ν)), ∃ h : y ∈ negIntegral D,
      negIntegralEquiv D ⟨y, h⟩ ∈ Submodule.span 𝒜
        (integralCanonicalBasis D '' canonicalIndexAt D ν) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem b hb =>
      have hbi : b ∈ negIntegral D := by
        have := Submodule.subset_span (R := 𝒜) hb
        rw [span_canonicalBasisAt_laurent] at this
        exact this.1
      refine ⟨hbi, Submodule.subset_span ⟨⟨b, Set.mem_iUnion_of_mem ν hb⟩, hb, ?_⟩⟩
      exact Subtype.ext (integralCanonicalBasis_apply D _)
    | zero =>
      refine ⟨zero_mem _, ?_⟩
      rw [show (⟨0, zero_mem _⟩ : negIntegral D) = 0 from rfl, map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      obtain ⟨hy, hy'⟩ := hy
      obtain ⟨hz, hz'⟩ := hz
      refine ⟨add_mem hy hz, ?_⟩
      have : (⟨y + z, add_mem hy hz⟩ : negIntegral D) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add]
      exact add_mem hy' hz'
    | smul c y _ hy =>
      obtain ⟨hy, hy'⟩ := hy
      refine ⟨Submodule.smul_mem _ c hy, ?_⟩
      have : (⟨c • y, Submodule.smul_mem _ c hy⟩ : negIntegral D) = c • ⟨y, hy⟩ := rfl
      rw [this, map_smul]
      exact Submodule.smul_mem _ c hy'
  obtain ⟨h, hmem⟩ := key x hx
  convert hmem using 1
  refine Subtype.ext ?_
  rw [coe_integralWord]
  rfl

/-! ### The weight projections of `𝒜f` -/

open Classical in
/-- The projection of `𝒜f` onto the span of `B_ν`. -/
def canonicalProj (ν : I →₀ ℕ) : quotientIntegralForm D →ₗ[𝒜] quotientIntegralForm D :=
  (integralCanonicalBasis D).constr 𝒜 fun b ↦
    if b ∈ canonicalIndexAt D ν then integralCanonicalBasis D b else 0

lemma canonicalProj_of_mem {ν μ : I →₀ ℕ} {y : quotientIntegralForm D}
    (hy : y ∈ Submodule.span 𝒜 (integralCanonicalBasis D '' canonicalIndexAt D μ)) :
    canonicalProj D ν y = if μ = ν then y else 0 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, rfl⟩ := hz
    rw [canonicalProj, Module.Basis.constr_basis]
    by_cases h : μ = ν
    · subst h; simp [hb]
    · have hb' : b ∉ canonicalIndexAt D ν := fun h' ↦ h (eq_of_mem_canonicalBasisAt D hb h')
      simp [h, hb']
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, hy, hz]; split_ifs <;> simp
  | smul c y _ hy => rw [map_smul, hy]; split_ifs <;> simp

/-! ### The map `θᵢ ↦ 1 ⊗ θᵢ` -/

variable (F : Type*) [Field F] [Algebra 𝒜 F]

/-- The algebra map `F⟨θᵢ⟩ → _F f = F ⊗_𝒜 𝒜f`, `θᵢ ↦ 1 ⊗ θᵢ`. -/
def quasiClassicalHom : LusztigF F I →ₐ[F] F ⊗[𝒜] quotientIntegralForm D :=
  FreeAlgebra.lift F fun i ↦ (1 : F) ⊗ₜ integralGenerator D i 1

omit [Finite I] in
lemma quasiClassicalHom_θ (i : I) :
    quasiClassicalHom D F (θ F i) = Algebra.TensorProduct.includeRight (integralGenerator D i 1) :=
  FreeAlgebra.lift_ι_apply _ _

omit [Finite I] in
lemma quasiClassicalHom_wordBasis (w : List I) :
    quasiClassicalHom D F (wordBasis F I w) =
      Algebra.TensorProduct.includeRight (integralWord D w) := by
  rw [wordBasis_apply, map_list_prod, integralWord, map_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ quasiClassicalHom_θ D F i

lemma quasiClassicalHom_weightProj (ν : I →₀ ℕ) (x : LusztigF F I) :
    quasiClassicalHom D F (weightProj F ν x) =
      (canonicalProj D ν).baseChange F (quasiClassicalHom D F x) := by
  have : (quasiClassicalHom D F).toLinearMap ∘ₗ weightProj F ν =
      (canonicalProj D ν).baseChange F ∘ₗ (quasiClassicalHom D F).toLinearMap := by
    refine (wordBasis F I).ext fun w ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply, weightProj_wordBasis, quasiClassicalHom_wordBasis,
      Algebra.TensorProduct.includeRight_apply, LinearMap.baseChange_tmul,
      canonicalProj_of_mem D (integralWord_mem_span D w)]
    split_ifs
    · rw [quasiClassicalHom_wordBasis, Algebra.TensorProduct.includeRight_apply]
    · rw [map_zero, TensorProduct.tmul_zero]
  exact LinearMap.congr_fun this x

/-! ### The quantum Serre relations in `𝒜f` -/

/-- `T n ∈ 𝒜 = ℤ[v, v⁻¹]` (that is, `v^n`) as a unit. -/
def laurentTUnit (n : ℕ) : 𝒜ˣ where
  val := LaurentPolynomial.T n
  inv := LaurentPolynomial.T (-n)
  val_inv := by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
  inv_val := by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

omit [Finite I] in
lemma coe_smul_integralForm (c : 𝒜) (y : quotientIntegralForm D) :
    ((c • y : quotientIntegralForm D) : LusztigF.Quotient D 𝕧) =
      integralLaurentEval c • (y : LusztigF.Quotient D 𝕧) := rfl

omit [Finite I] in
/-- The quantum Serre elements vanish in `𝒜f`. -/
lemma qSerreU_integralGenerator {i j : I} (hij : i ≠ j) :
    qSerreU (laurentTUnit (D.d i)) (serreExp D i j) (integralGenerator D i 1)
      (integralGenerator D j 1) = 0 := by
  have hT : integralLaurentEval (laurentTUnit (D.d i) : 𝒜) = 𝕧 ^ D.d i := by
    simp [laurentTUnit]
  apply Subtype.ext
  have hcoe : ((qSerreU (laurentTUnit (D.d i)) (serreExp D i j) (integralGenerator D i 1)
      (integralGenerator D j 1) : quotientIntegralForm D) : LusztigF.Quotient D 𝕧) =
      toQuotient D 𝕧 (qSerre (𝕧 ^ D.d i) (serreExp D i j) (θ 𝕂 i) (θ 𝕂 j)) := by
    simp only [qSerreU, qSerre, AddSubmonoidClass.coe_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [coe_smul_integralForm, map_smul, map_mul, map_pow, map_neg, map_one,
      map_qBinomialU, hT]
    simp [coe_integralGenerator_one]
  rw [hcoe, ZeroMemClass.coe_zero, toQuotient_eq_zero_iff]
  exact serreIdeal_le_radical_ratFunc D (qSerre_mem_serreIdeal hij
    (qFactorial_ne_zero_of_not_root RatFunc.X_ne_zero (fun _ hn ↦ ratFunc_X_pow_ne_one hn) _ _))

lemma qFactorial_eq_prod {K : Type*} [Field K] (ε : K) (n : ℕ) :
    qFactorial ε n = ∏ m ∈ Finset.range n, qInt ε (m + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [qFactorial_succ, ih, Finset.prod_range_succ, mul_comm]

/-- `[n]ᵢ! ∈ 𝒜`, with `θᵢ^n = [n]ᵢ! θᵢ^{(n)}` in `𝒜f`. -/
def laurentQFactorial (d n : ℕ) : 𝒜 :=
  ∏ m ∈ Finset.range n, qNatU (laurentTUnit d) (m + 1)

lemma map_laurentQFactorial {K : Type*} [Field K] (φ : 𝒜 →+* K) (d n : ℕ) :
    φ (laurentQFactorial d n) = qFactorial (φ (laurentTUnit d : 𝒜)) n := by
  rw [laurentQFactorial, map_prod, qFactorial_eq_prod]
  exact Finset.prod_congr rfl fun m _ ↦ map_qNatU _ φ _

omit [Finite I] in
lemma integralGenerator_pow (i : I) (n : ℕ) :
    integralGenerator D i 1 ^ n = laurentQFactorial (D.d i) n • integralGenerator D i n := by
  have hT : integralLaurentEval (laurentTUnit (D.d i) : 𝒜) = 𝕧 ^ D.d i := by
    simp [laurentTUnit]
  apply Subtype.ext
  rw [coe_smul_integralForm, map_laurentQFactorial, hT, SubmonoidClass.coe_pow,
    coe_integralGenerator_one]
  simp only [integralGenerator, quotientIntegralGenerator, qDivPow, smul_smul]
  rw [mul_inv_cancel₀ (qFactorial_ne_zero_of_not_root RatFunc.X_ne_zero
    (fun _ hn ↦ ratFunc_X_pow_ne_one hn) _ _), one_smul]

/-! ### The presentation -/

/-- The parameters `qᵢ = ε^{dᵢ}`, where `ε ∈ F` is the image of `v`. -/
local notation "ε" => algebraMap 𝒜 F (LaurentPolynomial.T 1)

lemma algebraMap_laurentTUnit (n : ℕ) : algebraMap 𝒜 F (laurentTUnit n : 𝒜) = ε ^ n := by
  rw [← map_pow, LaurentPolynomial.T_pow, mul_one]
  rfl

omit [Finite I] in
lemma quasiClassicalHom_serreWord {i j : I} (hij : i ≠ j) :
    quasiClassicalHom D F (serreWord D (fun i ↦ ε ^ D.d i) i j) = 0 := by
  have h : quasiClassicalHom D F (serreWord D (fun i ↦ ε ^ D.d i) i j) =
      Algebra.TensorProduct.includeRight (qSerreU (laurentTUnit (D.d i)) (serreExp D i j)
        (integralGenerator D i 1) (integralGenerator D j 1)) := by
    simp only [serreWord, qSerre, qSerreU, map_sum, map_smul, map_mul, map_pow,
      quasiClassicalHom_θ]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    conv_rhs => rw [← algebraMap_smul F]
    rw [map_mul, map_pow, map_neg, map_one, map_qBinomialU, algebraMap_laurentTUnit]
  rw [h, qSerreU_integralGenerator D hij, map_zero]

variable [CharZero F]

omit [Finite I] in
/-- **The map `θᵢ ↦ 1 ⊗ θᵢ` is surjective** in the quasi-classical case. -/
theorem quasiClassicalHom_surjective (hε : ∀ i, (ε ^ D.d i) ^ 2 = 1) :
    Function.Surjective (quasiClassicalHom D F) := by
  rw [← AlgHom.range_eq_top, eq_top_iff, ← adjoin_baseChangeGenerator D F, Algebra.adjoin_le_iff]
  rintro _ ⟨⟨i, n⟩, rfl⟩
  have hc : algebraMap 𝒜 F (laurentQFactorial (D.d i) n) ≠ 0 := by
    rw [map_laurentQFactorial, algebraMap_laurentTUnit]
    exact qFactorial_ne_zero_of_sq_eq_one (hε i) n
  have h : (1 : F) ⊗ₜ[𝒜] integralGenerator D i n =
      (algebraMap 𝒜 F (laurentQFactorial (D.d i) n))⁻¹ •
        quasiClassicalHom D F (θ F i ^ n) := by
    rw [map_pow, quasiClassicalHom_θ, ← map_pow, integralGenerator_pow, map_smul,
      ← algebraMap_smul F (laurentQFactorial (D.d i) n), smul_smul, inv_mul_cancel₀ hc, one_smul,
      Algebra.TensorProduct.includeRight_apply]
  change (1 : F) ⊗ₜ[𝒜] integralGenerator D i n ∈ _
  rw [h]
  exact Subalgebra.smul_mem _ (AlgHom.mem_range_self _ _) _

omit [Finite I] [DecidableEq I] in
lemma serreSpan_quasi_le_serreIdeal (hε : ∀ i, (ε ^ D.d i) ^ 2 = 1) {ν : I →₀ ℕ}
    {y : LusztigF F I} (hy : y ∈ serreSpan D (fun i ↦ ε ^ D.d i) ν) : y ∈ serreIdeal D ε := by
  classical
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, ⟨hg, -⟩, rfl⟩ := hz
    refine TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ ?_)
    exact qSerre_mem_serreIdeal hg (qFactorial_ne_zero_of_sq_eq_one (hε _) _)
  | zero => exact (serreIdeal D ε).zero_mem
  | add y z _ _ hy hz => exact TwoSidedIdeal.add_mem _ hy hz
  | smul c y _ hy => exact smul_mem_serreIdeal c hy

omit [Finite I] [CharZero F] in
lemma quasiClassicalHom_serreSpan {ν : I →₀ ℕ} {y : LusztigF F I}
    (hy : y ∈ serreSpan D (fun i ↦ ε ^ D.d i) ν) : quasiClassicalHom D F y = 0 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, ⟨hg, -⟩, rfl⟩ := hz
    rw [serreProduct, map_mul, map_mul, quasiClassicalHom_serreWord D F hg, mul_zero, zero_mul]
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, hy, smul_zero]

omit [Finite I] [DecidableEq I] [CharZero F] in
/-- The symmetry `qᵢ^{-aᵢⱼ} = qⱼ^{-aⱼᵢ}` of the parameters `qᵢ = ε^{dᵢ}`. -/
lemma pow_serreExp_symm (i j : I) (hij : i ≠ j) :
    (ε ^ D.d i) ^ (serreExp D i j - 1) = (ε ^ D.d j) ^ (serreExp D j i - 1) := by
  rw [← pow_mul, ← pow_mul]
  congr 1
  have h1 := D.d_mul_cartanMatrix_comm i j
  have h2 := D.isGeneralizedCartan_cartanMatrix.offDiag_nonpos i j hij
  have h3 := D.isGeneralizedCartan_cartanMatrix.offDiag_nonpos j i hij.symm
  simp only [serreExp]
  zify [show 1 ≤ (1 - D.cartanMatrix i j).toNat by omega,
    show 1 ≤ (1 - D.cartanMatrix j i).toNat by omega]
  rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
  linarith

/-- The kernel of `θᵢ ↦ 1 ⊗ θᵢ` in weight `ν` is spanned by the quantum Serre products. -/
lemma mem_serreSpan_of_quasiClassicalHom_eq_zero (hε : ∀ i, (ε ^ D.d i) ^ 2 = 1)
    (ν : I →₀ ℕ) {y : LusztigF F I} (hy : y ∈ LusztigF.weightSpace F ν)
    (h0 : quasiClassicalHom D F y = 0) : y ∈ serreSpan D (fun i ↦ ε ^ D.d i) ν := by
  classical
  set V := LusztigF.weightSpace F ν
  set g := (quasiClassicalHom D F).toLinearMap.domRestrict V
  set S := (serreSpan D (fun i ↦ ε ^ D.d i) ν).comap V.subtype
  have hSg : S ≤ LinearMap.ker g := fun z hz ↦ quasiClassicalHom_serreSpan D F hz
  have hSer : finrank F S = finrank F (serreSpan D (fun i ↦ ε ^ D.d i) ν) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
      inf_eq_right.2 (serreSpan_le_weightSpace D _ ν)]
  -- the family `1 ⊗ b`, `b ∈ B_ν`, in the range of `g`
  set fam : canonicalIndexAt D ν → F ⊗[𝒜] quotientIntegralForm D :=
    fun b ↦ baseChangeCanonicalBasis D F b
  have hli : LinearIndependent F fam :=
    (baseChangeCanonicalBasis D F).linearIndependent.comp _ Subtype.val_injective
  have hfam : Set.range fam ⊆ LinearMap.range g := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨z, hz⟩ := quasiClassicalHom_surjective D F hε (fam b)
    refine ⟨⟨weightProj F ν z, weightProj_mem ν z⟩, ?_⟩
    rw [LinearMap.domRestrict_apply, AlgHom.toLinearMap_apply, quasiClassicalHom_weightProj, hz]
    simp only [fam, baseChangeCanonicalBasis_apply, LinearMap.baseChange_tmul]
    rw [canonicalProj_of_mem D (μ := ν) (Submodule.subset_span ⟨b, b.2, rfl⟩)]
    simp
  have e : canonicalIndexAt D ν ≃ canonicalBasisAt D ν :=
    { toFun := fun b ↦ ⟨b.1.1, b.2⟩
      invFun := fun x ↦ ⟨⟨x.1, Set.mem_iUnion_of_mem ν x.2⟩, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have := finite_canonicalBasisAt D ν
  have := Finite.of_equiv _ e.symm
  have := Fintype.ofFinite (canonicalIndexAt D ν)
  have hcard : Fintype.card (canonicalIndexAt D ν) ≤ finrank F (LinearMap.range g) := by
    rw [← finrank_span_eq_card hli]
    exact Submodule.finrank_mono (Submodule.span_le.2 hfam)
  have hnat : Fintype.card (canonicalIndexAt D ν) = finrank 𝕂 (Uw D 𝕧 ν) := by
    rw [← natCard_canonicalBasisAt, ← Nat.card_eq_fintype_card, Nat.card_congr e]
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  have hV : finrank F V = Fintype.card (Words ν) := finrank_weightSpace F ν
  have hsum := finrank_Uw_add_finrank_serreSpan D ν
  have hdim : finrank F (serreSpan D (fun i ↦ ε ^ D.d i) ν) =
      finrank ℚ (serreSpan D (fun _ ↦ (1 : ℚ)) ν) := by
    rw [finrank_serreSpan_of_sq_eq_one D hε (pow_serreExp_symm D F), finrank_serreSpan_one]
  have hSk : S = LinearMap.ker g :=
    Submodule.eq_of_le_of_finrank_le hSg (by omega)
  have : (⟨y, hy⟩ : V) ∈ LinearMap.ker g := h0
  rw [← hSk] at this
  exact this

/-- **The kernel of `θᵢ ↦ 1 ⊗ θᵢ`** is the ideal generated by the quantum Serre elements with
parameter `ε`. -/
theorem quasiClassicalHom_eq_zero_iff (hε : ∀ i, (ε ^ D.d i) ^ 2 = 1) (x : LusztigF F I) :
    quasiClassicalHom D F x = 0 ↔ x ∈ serreIdeal D ε := by
  constructor
  · intro hx
    rw [← sum_weightProj x]
    refine Finset.sum_induction _ (· ∈ serreIdeal D ε)
      (fun a b ha hb ↦ TwoSidedIdeal.add_mem _ ha hb) (serreIdeal D ε).zero_mem fun ν _ ↦ ?_
    refine serreSpan_quasi_le_serreIdeal D F hε
      (mem_serreSpan_of_quasiClassicalHom_eq_zero D F hε ν (weightProj_mem ν x) ?_)
    rw [quasiClassicalHom_weightProj, hx, map_zero]
  · intro hx
    induction hx using TwoSidedIdeal.span_induction with
    | mem y hy =>
      obtain ⟨i, j, hij, rfl⟩ := hy
      rw [serreElement, qSerreDiv_eq (qFactorial_ne_zero_of_sq_eq_one (hε i) _), map_smul]
      change _ • quasiClassicalHom D F (serreWord D (fun i ↦ ε ^ D.d i) i j) = 0
      rw [quasiClassicalHom_serreWord D F hij, smul_zero]
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | neg y _ hy => rw [map_neg, hy, neg_zero]
    | left_absorb a y _ hy => rw [map_mul, hy, mul_zero]
    | right_absorb b y _ hy => rw [map_mul, hy, zero_mul]

/-- **[Lus] Prop. 33.2.2 (c).** In the quasi-classical case (`F` of characteristic zero, the image
`ε` of `v` with `(ε^{dᵢ})² = 1`), the algebra with generators `θᵢ` and the quantum Serre relations
with parameter `ε` is isomorphic to `_F f = F ⊗_𝒜 𝒜f` by `θᵢ ↦ 1 ⊗ θᵢ`. Lusztig also assumes
that the Cartan datum has no odd cycles; this is not needed. -/
def quasiClassicalEquiv (hε : ∀ i, (ε ^ D.d i) ^ 2 = 1) :
    (serreIdeal D ε).ringCon.Quotient ≃ₐ[F] F ⊗[𝒜] quotientIntegralForm D :=
  AlgEquiv.ofBijective
    (RingCon.liftₐ (serreIdeal D ε).ringCon (quasiClassicalHom D F) fun x y h ↦ by
      rw [RingCon.ker_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← sub_eq_zero,
        ← map_sub, quasiClassicalHom_eq_zero_iff D F hε]
      exact (TwoSidedIdeal.rel_iff _ _ _).1 h)
    ⟨fun a b hab ↦ by
      induction a using Quotient.inductionOn' with | h x =>
      induction b using Quotient.inductionOn' with | h y =>
      refine Quotient.sound' ?_
      change (serreIdeal D ε).ringCon x y
      rw [TwoSidedIdeal.rel_iff, ← quasiClassicalHom_eq_zero_iff D F hε, map_sub,
        sub_eq_zero]
      exact hab,
    fun z ↦ by
      obtain ⟨x, rfl⟩ := quasiClassicalHom_surjective D F hε z
      exact ⟨x, rfl⟩⟩

lemma quasiClassicalEquiv_θ (hε : ∀ i, (ε ^ D.d i) ^ 2 = 1) (i : I) :
    quasiClassicalEquiv D F hε (θ F i) = (1 : F) ⊗ₜ integralGenerator D i 1 := by
  change quasiClassicalHom D F (θ F i) = _
  rw [quasiClassicalHom_θ, Algebra.TensorProduct.includeRight_apply]

end LieLean.QuantumGroup
