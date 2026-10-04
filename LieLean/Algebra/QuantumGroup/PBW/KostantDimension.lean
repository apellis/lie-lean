/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterVerma
import LieLean.Algebra.QuantumGroup.IrreducibleCharacter.Classical
import LieLean.Algebra.QuantumGroup.PBW.WeightDimension

/-!
# `dim U⁺_ν` is Kostant's partition function

Let `(I, ·)` be a Cartan datum with Cartan matrix `A`, `K` a field of characteristic zero,
`(𝔥, Π, Π^∨)` a realization of `A` over `K` and `M(Λ)` a Verma module of the Kac–Moody algebra
`𝔤(A)`. The map `Y_M : K⟨θᵢ⟩ → M(Λ)`, `y ↦ y(f) v_Λ` (`LusztigF.toVerma`), factors through the
associative Serre algebra `𝒮 ≅ U(𝔫₋)` (Gabber–Kac, [Kac] Thm. 9.11), so its kernel is the
classical Serre ideal, and it maps the words of weight `ν` onto `M(Λ)_{Λ - ν}`. Hence
(`LusztigF.kostantPartition_add_finrank_serreSpan`)

`K(ν) + dim Z_ν = #{words of weight ν}`,

where `K` is Kostant's partition function (`dim M(Λ)_{Λ - ν}`, [Kac] (10.5.2)) and `Z_ν` the span
of the classical Serre products of weight `ν`. Combined with the quantum Gabber–Kac dimension
count (`QuantumGroup.finrank_plusWeightSpace`) this gives, for `v` transcendental over `ℚ`,

`dim U⁺_ν = K(ν)` (`QuantumGroup.finrank_plusWeightSpace_eq_kostantPartition`),

the dimension formula behind the PBW theorem ([Jan] 5.19 a) and 8.24, Remark 3, both for finite
type; [Lus] 40.2.1–40.2.2), with `K` computed for any realization over any field of characteristic
zero (`dim Z_ν` does not depend on the field, `LusztigF.finrank_serreSpan_one`). Consequently a
family of `K(ν)` elements of `U⁺_ν` is linearly independent iff it spans `U⁺_ν`
(`QuantumGroup.linearIndependent_iff_span_eq_plusWeightSpace`).

## Main definitions / results

* `LusztigF.toVerma`: `y ↦ y(f) v_Λ`.
* `LusztigF.weightSpace_verma_eq_map`, `LusztigF.toVerma_eq_zero_iff_mem_serreSpan`.
* `LusztigF.kostantPartition_add_finrank_serreSpan`, `LusztigF.finrank_serreSpan_one`.
* `QuantumGroup.finrank_plusWeightSpace_eq_kostantPartition` (standard realization over `ℚ`) and
  `QuantumGroup.finrank_plusWeightSpace_eq_kostantPartition'` (any realization).
* `QuantumGroup.linearIndependent_iff_span_eq_plusWeightSpace`: the PBW criterion.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Thm. 9.11, (9.7.2).
* [Lus] G. Lusztig, *Introduction to quantum groups*, 33.1.3, 40.2.1–40.2.2.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 4.21, 5.19, 8.24.
-/

open LieLean

noncomputable section

open FreeAlgebra LieLean.QuantumGroup Matrix Matrix.Realization
open Matrix.Realization.KacMoodyAlgebra Module
  LieModule

namespace LusztigF

attribute [local instance 100] LieRing.ofAssociativeRing

variable {I K H : Type*} [Fintype I] [DecidableEq I] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] (D : LusztigCartanDatum I) (P : Realization D.cartanMatrix K H)
  (Λ : Module.Dual K H)

/-- The linear map `Y_M : K⟨θᵢ⟩ → M(Λ)`, `y ↦ y(f) v_Λ`, through `𝒮 ≅ U(𝔫₋) ≅ M(Λ)`. -/
def toVerma : LusztigF K I →ₗ[K] VermaModule P Λ :=
  (VermaModule.equivEnvNNeg P Λ).toLinearMap ∘ₗ
    (serreAssocAlgebraEquiv P D.isGeneralizedCartan_cartanMatrix
      D.isSymmetrizable_cartanMatrix).toLinearMap ∘ₗ
    (SerreAssocAlgebra.mkAlgHom K D.cartanMatrix).toLinearMap

lemma toVerma_apply (y : LusztigF K I) :
    toVerma D P Λ y = VermaModule.equivEnvNNeg P Λ (serreAssocAlgebraEquiv P
      D.isGeneralizedCartan_cartanMatrix D.isSymmetrizable_cartanMatrix
        (SerreAssocAlgebra.mkAlgHom K D.cartanMatrix y)) := rfl

lemma toVerma_one : toVerma D P Λ 1 = VermaModule.hwv P Λ := by
  rw [toVerma_apply, map_one, map_one, VermaModule.equivEnvNNeg_apply, map_one, one_smul]

lemma toVerma_θ_mul (j : I) (y : LusztigF K I) :
    toVerma D P Λ (θ K j * y) = ⁅f P j, toVerma D P Λ y⁆ := by
  rw [toVerma_apply, toVerma_apply, map_mul, map_mul, VermaModule.equivEnvNNeg_mul]
  change UniversalEnvelopingAlgebra.map (LieSubalgebra.incl (nNeg P))
    (serreAssocAlgebraEquiv P _ _ (SerreAssocAlgebra.θ K D.cartanMatrix j)) • _ = _
  rw [serreAssocAlgebraEquiv_θ, UniversalEnvelopingAlgebra.map_ι, ← VermaModule.lie_eq_smul]
  rfl

lemma toVerma_wordBasis (w : List I) :
    toVerma D P Λ (wordBasis K I w) = VermaModule.fWord P w • VermaModule.hwv P Λ := by
  induction w with
  | nil => rw [wordBasis_nil, toVerma_one, VermaModule.fWord_nil, one_smul]
  | cons j w ih =>
    rw [← ι_mul_wordBasis, toVerma_θ_mul, ih, VermaModule.fWord_smul_cons]

omit [DecidableEq I] [CharZero K] in
lemma wordWt_eq_rootOf (w : List I) :
    AuxLieAlgebra.wordWt P w = P.rootOf fun i ↦ (wordWeight w i : ℤ) := by
  classical
  induction w with
  | nil =>
    rw [AuxLieAlgebra.wordWt_nil, ← map_zero P.rootOf]
    congr 1
  | cons j w ih =>
    rw [AuxLieAlgebra.wordWt_cons, ih, ← rootOf_single, ← map_add]
    congr 1
    funext i
    by_cases h : i = j
    · subst h; simp [wordWeight_cons]
    · simp [wordWeight_cons, h]

/-- The weight space `M(Λ)_{Λ - ν}` is the image of the words of weight `ν`. -/
theorem weightSpace_verma_eq_map (ν : I →₀ ℕ) :
    VermaModule.weightSpace P Λ (Λ - P.rootOf fun i ↦ (ν i : ℤ)) =
      (weightSpace K ν).map (toVerma D P Λ) := by
  rw [VermaModule.weightSpace_eq_wordSpan, VermaModule.wordSpan, weightSpace_eq_span,
    Submodule.map_span, ← Set.range_comp]
  congr 1
  ext m
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : wordWeight w = ν := by
      have h1 : AuxLieAlgebra.wordWt P w = P.rootOf fun i ↦ (ν i : ℤ) :=
        sub_right_injective hw
      rw [wordWt_eq_rootOf] at h1
      have h2 := P.rootOf_injective h1
      ext i
      exact_mod_cast congr_fun h2 i
    exact ⟨⟨w, hw'⟩, (toVerma_wordBasis D P Λ w)⟩
  · rintro ⟨⟨w, hw⟩, rfl⟩
    refine ⟨w, ?_, (toVerma_wordBasis D P Λ w).symm⟩
    change Λ - AuxLieAlgebra.wordWt P w = _
    rw [wordWt_eq_rootOf, hw]

omit [Fintype I] [CharZero K] [DecidableEq I] in
/-- The classical Serre products lie in the classical Serre ideal. -/
lemma serreSpan_le_serreAssocIdeal (ν : I →₀ ℕ) {y : LusztigF K I}
    (hy : y ∈ serreSpan D (fun _ ↦ (1 : K)) ν) : y ∈ serreAssocIdeal K D.cartanMatrix := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, ⟨hg, -⟩, rfl⟩ := hz
    have hs : serreWord D (fun _ ↦ (1 : K)) g.2.1 g.2.2.1 ∈ serreAssocIdeal K D.cartanMatrix := by
      have h := serreAssocElem_eq_smul_serreWord (K := K) D hg
      have hmem : serreAssocElem K D.cartanMatrix g.2.1 g.2.2.1 ∈
          serreAssocIdeal K D.cartanMatrix :=
        TwoSidedIdeal.subset_span ⟨_, _, hg, rfl⟩
      have hu : ((-1 : K) ^ serreExp D g.2.1 g.2.2.1) *
          ((-1 : K) ^ serreExp D g.2.1 g.2.2.1) = 1 := by
        rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
      have : serreWord D (fun _ ↦ (1 : K)) g.2.1 g.2.2.1 =
          ((-1 : K) ^ serreExp D g.2.1 g.2.2.1) •
            serreAssocElem K D.cartanMatrix g.2.1 g.2.2.1 := by
        rw [h, smul_smul, hu, one_smul]
      rw [this, Algebra.smul_def]
      exact TwoSidedIdeal.mul_mem_left _ _ _ hmem
    exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _ hs)
  | zero => exact (serreAssocIdeal K D.cartanMatrix).zero_mem
  | add y z _ _ hy hz => exact TwoSidedIdeal.add_mem _ hy hz
  | smul c y _ hy =>
    rw [Algebra.smul_def]
    exact TwoSidedIdeal.mul_mem_left _ _ _ hy

/-- On the words of weight `ν`, the kernel of `Y_M` is the span of the classical Serre products
of weight `ν` (Gabber–Kac, [Kac] Thm. 9.11). -/
theorem toVerma_eq_zero_iff_mem_serreSpan {ν : I →₀ ℕ} {y : LusztigF K I}
    (hy : y ∈ weightSpace K ν) :
    toVerma D P Λ y = 0 ↔ y ∈ serreSpan D (fun _ ↦ (1 : K)) ν := by
  rw [toVerma_apply, LinearEquiv.map_eq_zero_iff, map_eq_zero_iff _ (AlgEquiv.injective _),
    SerreAssocAlgebra.mkAlgHom_eq_zero_iff]
  refine ⟨fun h ↦ ?_, serreSpan_le_serreAssocIdeal D ν⟩
  have := weightProj_mem_serreSpan D _ (serreAssocIdeal_le_span_serreWord D h) ν
  rwa [weightProj_self hy] at this

/-- **Kostant's partition function and the classical Serre relations**: `K(ν) + dim Z_ν` is the
number of words of weight `ν`, where `Z_ν` is the span of the classical Serre products of weight
`ν` in `K⟨θ⟩` ([Kac] Thm. 9.11, (9.7.2)). -/
theorem kostantPartition_add_finrank_serreSpan (ν : I →₀ ℕ) :
    kostantPartition P (P.rootOf fun i ↦ (ν i : ℤ)) +
      finrank K (serreSpan D (fun _ ↦ (1 : K)) ν) = Fintype.card (Words ν) := by
  set V := weightSpace K ν
  set g := (toVerma D P 0).domRestrict V
  have hrange : LinearMap.range g =
      VermaModule.weightSpace P 0 (0 - P.rootOf fun i ↦ (ν i : ℤ)) := by
    rw [LinearMap.range_domRestrict, weightSpace_verma_eq_map]
  have hker : LinearMap.ker g = (serreSpan D (fun _ ↦ (1 : K)) ν).comap V.subtype := by
    ext y
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    exact toVerma_eq_zero_iff_mem_serreSpan D P 0 y.2
  have hSer : finrank K ((serreSpan D (fun _ ↦ (1 : K)) ν).comap V.subtype) =
      finrank K (serreSpan D (fun _ ↦ (1 : K)) ν) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
      inf_eq_right.2 (serreSpan_le_weightSpace D _ ν)]
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, hker, hSer, finrank_weightSpace,
    VermaModule.finrank_weightSpace_sub] at hrn
  exact hrn

omit [Fintype I] [DecidableEq I] in
lemma mapCoeffs_serreProduct_one (g : List I × I × I × List I) :
    mapCoeffs (algebraMap ℚ K) (serreProduct D (fun _ ↦ (1 : ℚ)) g) =
      serreProduct D (fun _ ↦ (1 : K)) g := by
  simp only [serreProduct, serreWord, qSerre, map_mul, map_sum, mapCoeffs_smul, map_pow,
    mapCoeffs_wordBasis, θ, mapCoeffs_ι, qBinomial_one, map_neg, map_one, map_natCast]

omit [Fintype I] [DecidableEq I] in
/-- The dimension of the span of the classical Serre products of weight `ν` is the rank of their
coordinate vectors on the words of weight `ν`. -/
lemma finrank_serreSpan_one_eq_span_wordCoord (F : Type*) [Field F] (ν : I →₀ ℕ) :
    finrank F (serreSpan D (fun _ ↦ (1 : F)) ν) = finrank F (Submodule.span F
      (Set.range fun g : serreIndices D ν ↦
        wordCoord F ν (serreProduct D (fun _ ↦ (1 : F)) g.1))) := by
  classical
  set S := serreSpan D (fun _ ↦ (1 : F)) ν
  have hinj : Function.Injective ((wordCoord F ν).comp S.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact Subtype.ext (eq_zero_of_wordCoord_eq_zero (serreSpan_le_weightSpace D _ ν y.2) hy)
  have hmap : S.map (wordCoord F ν) = Submodule.span F
      (Set.range fun g : serreIndices D ν ↦
        wordCoord F ν (serreProduct D (fun _ ↦ (1 : F)) g.1)) := by
    change (Submodule.span F _).map _ = _
    rw [Submodule.map_span, Set.image_image, Set.image_eq_range]
  rw [(LinearEquiv.ofInjective _ hinj).finrank_eq, LinearMap.range_comp,
    Submodule.range_subtype, hmap]

omit [Fintype I] [DecidableEq I] in
/-- The dimension of the span of the classical Serre products of weight `ν` does not depend on
the field of characteristic zero. -/
theorem finrank_serreSpan_one (ν : I →₀ ℕ) :
    finrank K (serreSpan D (fun _ ↦ (1 : K)) ν) = finrank ℚ (serreSpan D (fun _ ↦ (1 : ℚ)) ν) := by
  classical
  have hc : ∀ g : serreIndices D ν, wordCoord K ν (serreProduct D (fun _ ↦ (1 : K)) g.1) =
      algebraMap ℚ K ∘ wordCoord ℚ ν (serreProduct D (fun _ ↦ (1 : ℚ)) g.1) := by
    intro g
    funext w
    rw [Function.comp_apply, wordCoord_apply, wordCoord_apply, ← mapCoeffs_serreProduct_one,
      wordBasis_repr_mapCoeffs]
  rw [finrank_serreSpan_one_eq_span_wordCoord D K, finrank_serreSpan_one_eq_span_wordCoord D ℚ,
    show (fun g : serreIndices D ν ↦
      wordCoord K ν (serreProduct D (fun _ ↦ (1 : K)) g.1)) = fun g ↦
      algebraMap ℚ K ∘ wordCoord ℚ ν (serreProduct D (fun _ ↦ (1 : ℚ)) g.1) from funext hc]
  refine le_antisymm (Submodule.finrank_span_algebraMap_comp_le _) ?_
  exact Submodule.finrank_span_le_of_comp_ratHom (RingHom.id ℚ) (algebraMap ℚ K)
    (algebraMap ℚ K).injective _

end LusztigF

namespace LieLean.QuantumGroup

open LusztigF

variable {k : Type*} [Field k] [CharZero k] {I Y : Type*} [Fintype I] [AddCommGroup Y]
  [DecidableEq I] {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]

/-- **`dim U⁺_ν` is Kostant's partition function** ([Lus] 33.1.3 with [Kac] (9.7.2)):
for `v` transcendental over `ℚ`, the weight space `U⁺_ν` has dimension `K(ν)`, the number of ways
of writing `ν` as a sum of positive roots of the Kac–Moody algebra of the Cartan matrix, counted
with multiplicities (computed for the standard realization over `ℚ`). -/
theorem finrank_plusWeightSpace_eq_kostantPartition (hv : Transcendental ℚ v) (ν : I →₀ ℕ) :
    finrank k (plusWeightSpace R v ν) =
      kostantPartition (Realization.std D.cartanMatrix ℚ)
        ((Realization.std D.cartanMatrix ℚ).rootOf fun i ↦ (ν i : ℤ)) := by
  have h1 := finrank_plusWeightSpace (R := R) hv ν
  have h2 := kostantPartition_add_finrank_serreSpan D (Realization.std D.cartanMatrix ℚ) ν
  omega

/-- **`dim U⁺_ν` is Kostant's partition function, for any realization** ([Lus] 33.1.3 with [Kac]
(9.7.2), (10.5.2)): for `v` transcendental over `ℚ` and any realization `P` of the Cartan matrix
over a field of characteristic zero, `dim U⁺_ν = K(ν)` computed for `P`. -/
theorem finrank_plusWeightSpace_eq_kostantPartition' (hv : Transcendental ℚ v) {K H : Type*}
    [Field K] [CharZero K] [AddCommGroup H] [Module K H] (P : Realization D.cartanMatrix K H)
    (ν : I →₀ ℕ) :
    finrank k (plusWeightSpace R v ν) = kostantPartition P (P.rootOf fun i ↦ (ν i : ℤ)) := by
  have h1 := finrank_plusWeightSpace (R := R) hv ν
  have h2 := kostantPartition_add_finrank_serreSpan D P ν
  rw [finrank_serreSpan_one] at h2
  omega

/-- **The PBW criterion** (cf. [Jan] 5.19 a), finite type): for `v` transcendental over `ℚ`,
a family of `K(ν)` elements of `U⁺_ν` (e.g. the ordered monomials of weight `ν` in the root vectors)
is linearly independent iff it spans `U⁺_ν`. -/
theorem linearIndependent_iff_span_eq_plusWeightSpace (hv : Transcendental ℚ v) {K H : Type*}
    [Field K] [CharZero K] [AddCommGroup H] [Module K H] (P : Realization D.cartanMatrix K H)
    (ν : I →₀ ℕ) {ι : Type*} [Fintype ι] (b : ι → QuantumGroup R v)
    (hb : ∀ a, b a ∈ plusWeightSpace R v ν)
    (hcard : Fintype.card ι = kostantPartition P (P.rootOf fun i ↦ (ν i : ℤ))) :
    LinearIndependent k b ↔ Submodule.span k (Set.range b) = plusWeightSpace R v ν := by
  have hV : FiniteDimensional k (weightSpace k ν) := by
    rw [weightSpace_eq_span]
    exact FiniteDimensional.span_of_finite k (Set.finite_range _)
  have hS : FiniteDimensional k (plusWeightSpace R v ν) := by
    unfold plusWeightSpace
    infer_instance
  have hdim := finrank_plusWeightSpace_eq_kostantPartition' (R := R) hv P ν
  constructor
  · intro hli
    refine Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.2 (Set.range_subset_iff.2 hb)) ?_
    rw [finrank_span_eq_card hli, hcard, hdim]
  · intro h
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, h, hdim, hcard]

end LieLean.QuantumGroup
