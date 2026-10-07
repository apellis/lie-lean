/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationUpperClosure
import LieLean.Algebra.Lie.KacMoody.TranslationNonintegral
import LieLean.Algebra.Lie.KacMoody.UpperClosureNonintegral

/-!
# Translation of simple modules for arbitrary weights: the upper-closure criterion

Humphreys, GSM 94, Theorem 7.9 for weights that need not be integral. Let `λ`, `μ` be
antidominant (`Matrix.Realization.IsAntidominant`), every positive root orthogonal to `λ + ρ`
orthogonal to `μ + ρ`, `ν = z (μ - λ)` dominant integral, and `T = T_λ^μ`. Then:

* `translation_irreducible_of_memUpperClosure_of_isAntidominant`: for every `w ∈ W`, if `w·μ`
  lies in the upper closure of the facet of `w·λ`, then `T L(w·λ) ≅ L(w·μ)`;
* `translation_irreducible_of_not_memUpperClosure_of_isAntidominant`: for `w ∈ W_[λ]`, otherwise
  `T L(w·λ) = 0`;
* `nonempty_equiv_translation_irreducible_iff_of_isAntidominant`: for `w ∈ W_[λ]`,
  `T L(w·λ) ≅ L(w·μ)` iff `w·μ` lies in the upper closure of the facet of `w·λ`.

The upper closure (`Matrix.Realization.MemUpperClosure`) only involves the roots integral for
`λ`, as in Humphreys, GSM 94, §7.4. The proof is that of the integral case
(`KacMoody/TranslationUpperClosure.lean`), with the combinatorics of
`KacMoody/UpperClosureNonintegral.lean` and the translation theorems of
`KacMoody/TranslationNonintegral.lean`. Reconstructed.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.3, §7.4, Theorem 7.9.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

omit [CharZero K] [FiniteDimensional K H] in
include hA in
/-- `λ - μ` is integral when `z (μ - λ)` is dominant integral. -/
theorem sub_rho_integral {lam μ ν : Dual K H} (hν : P.IsDominantIntegral ν)
    {z : Dual K H ≃ₗ[K] Dual K H} (hz : z ∈ P.weylGroup hA.isGeneralizedCartan)
    (hzν : z (μ - lam) = ν) :
    ∀ j, ∃ n : ℤ, ((lam + P.rho) - (μ + P.rho)) (P.coroot j) = n := by
  intro j
  have hνint : ∀ i, ∃ n : ℤ, ν (P.coroot i) = n := fun i ↦ by
    obtain ⟨n, hn⟩ := hν i; exact ⟨n, by rw [hn, Int.cast_natCast]⟩
  obtain ⟨k, hk⟩ := P.exists_apply_eq_add_rootOf hA.isGeneralizedCartan (inv_mem hz) hνint
  obtain ⟨n, hn⟩ := hνint j
  have e : (lam + P.rho) - (μ + P.rho) = -(z⁻¹ ν) := by
    rw [add_sub_add_right_eq_sub, ← hzν, ← neg_sub]
    congr 1
    exact (z.symm_apply_apply _).symm
  refine ⟨-(n + (A *ᵥ k) j), ?_⟩
  rw [e, hk, LinearMap.neg_apply, LinearMap.add_apply, hn, rootOf_apply_coroot]
  push_cast
  ring

variable [IsAlgClosed K]

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- If `[T_λ^μ L(η) : L(y)] ≠ 0`, then `η = w'·λ` with `w'·μ = y`, and `T_λ^μ L(η) ≠ 0`. -/
theorem exists_weylDot_of_multiplicity_translation_ne_zero_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν) {η y : Dual K H}
    (h : ((IrreducibleModule.isCategoryO P η).centralTranslation P
      (IrreducibleModule.isCategoryO P ν) (centralCharacter P lam)
      (centralCharacter P μ)).multiplicity y ≠ 0) :
    ∃ w' : P.weylGroup hA.isGeneralizedCartan, η = P.weylDot hA.isGeneralizedCartan w' lam ∧
      P.weylDot hA.isGeneralizedCartan w' μ = y ∧
      ¬Subsingleton (centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ) (IrreducibleModule P η)) := by
  classical
  have hA' := hA.isGeneralizedCartan
  have hns : ¬Subsingleton (centralTranslation P (IrreducibleModule P ν)
      (centralCharacter P lam) (centralCharacter P μ) (IrreducibleModule P η)) := fun hs ↦
    h (IsCategoryO.multiplicity_eq_zero_of_weightSpace_eq_bot _
      (eq_bot_iff.mpr fun v _ ↦ (Submodule.mem_bot K).mpr (Subsingleton.elim v 0)))
  by_cases hχ : centralCharacter P η = centralCharacter P lam
  · obtain ⟨w', hw', hw'e⟩ := (VermaModule.centralCharacter_eq_iff P hA lam η).mp hχ.symm
    have hη : η = P.weylDot hA' ⟨w', hw'⟩ lam := by
      rw [weylDot, hw'e, add_sub_cancel_right]
    subst hη
    refine ⟨⟨w', hw'⟩, rfl, ?_, hns⟩
    rcases translation_irreducible_of_isAntidominant P hA hlam hμ hfacet hν hz hzν ⟨w', hw'⟩ with
        hs | he
    · exact absurd hs hns
    · obtain ⟨e⟩ := he
      rw [← IsCategoryO.multiplicity_congr (IrreducibleModule.isCategoryO P _) _ e y,
        IrreducibleModule.multiplicity_eq] at h
      by_contra hne
      exact h (ite_eq_right fun hy ↦ hne hy.symm)
  · exfalso
    have hbot := centralBlock_irreducible_eq_bot P η (centralCharacter P lam) hχ
    refine h (IsCategoryO.multiplicity_eq_zero_of_weightSpace_eq_bot _
      (weightSpace_centralTranslation_eq_bot P (IrreducibleModule.isCategoryO P η)
        (IrreducibleModule.isCategoryO P ν) _ _
        (fun _ hw ↦ IrreducibleModule.mem_cone_of_weightSpace_ne_bot hw) fun μ' _ ↦
          eq_bot_iff.mpr fun v _ ↦ ?_))
    have hv : (v : IrreducibleModule P η) ∈
        (⊥ : LieSubmodule K P.KacMoodyAlgebra (IrreducibleModule P η)) := by
      rw [← hbot]
      exact v.2
    exact (Submodule.mem_bot K).mpr (Subtype.ext ((LieSubmodule.mem_bot _).mp hv))

include hA in
/-- The composition factor count for `T_λ^μ M(w·λ) ≅ M(w·μ)`: along a local composition series
of `M(w·λ)` for the weight `w·μ - ν`, `∑_η [T L(η) : L(w·μ)] = 1`. -/
private theorem sum_multiplicity_translation_eq_one_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan)
    {l : List (LieSubmodule K P.KacMoodyAlgebra
      (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam)) × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P (P.weylDot hA.isGeneralizedCartan w μ - ν) ⊥ l ⊤) :
    ((factorWeights l).map fun η ↦
      ((IrreducibleModule.isCategoryO P η).centralTranslation P
        (IrreducibleModule.isCategoryO P ν) (centralCharacter P lam)
        (centralCharacter P μ)).multiplicity
          (P.weylDot hA.isGeneralizedCartan w μ)).sum = 1 := by
  obtain ⟨e⟩ := translation_verma_equiv_of_isAntidominant P hA hlam hμ hfacet hν hz hzν w
  rw [← multiplicity_centralTranslation_eq_sum P (VermaModule.isCategoryO P _)
    (IrreducibleModule.isCategoryO P ν) _ _
    (fun _ hw ↦ IrreducibleModule.mem_cone_of_weightSpace_ne_bot hw) hl,
    ← IsCategoryO.multiplicity_congr (VermaModule.isCategoryO P _) _ e,
    VermaModule.multiplicity_self]

include hA in
/-- **Translation of simple modules, nonvanishing.** Under the hypotheses of
`translation_verma_of_isAntidominant`, for every `w ∈ W`, if no positive root `β` with `⟨w(μ + ρ),
β^∨⟩ = 0` has `⟨w(λ + ρ), β^∨⟩ > 0`, then `T_λ^μ L(w·λ) ≅ L(w·μ)`. -/
theorem translation_irreducible_of_upperClosureCondition_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan)
    (hC : P.UpperClosureCondition hA.isGeneralizedCartan (w.val (lam + P.rho))
      (w.val (μ + P.rho))) :
    Nonempty (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ)
        (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) := by
  classical
  have hA' := hA.isGeneralizedCartan
  rcases translation_irreducible_of_isAntidominant P hA hlam hμ hfacet hν hz hzν w with hsub | hne
  swap
  · exact hne
  exfalso
  obtain ⟨l, hl⟩ := (VermaModule.isCategoryO P
    (P.weylDot hA' w lam)).exists_isLocalCompositionSeries (P.weylDot hA' w μ - ν)
  have hsum := sum_multiplicity_translation_eq_one_of_isAntidominant P hA hlam hμ hfacet hν hz hzν
      w hl
  -- some factor `L(η)` of `M(w·λ)` has `[T L(η) : L(w·μ)] ≠ 0`
  obtain ⟨η, hηl, hη0⟩ := List.exists_mem_of_sum_map_eq_one hsum
  obtain ⟨w', rfl, hw'y, hns⟩ :=
      exists_weylDot_of_multiplicity_translation_ne_zero_of_isAntidominant P hA hlam hμ
    hfacet hν hz hzν hη0
  -- `w'·λ ≤ w·λ`
  obtain ⟨k, hk, hke⟩ := VermaModule.mem_cone_of_multiplicity_ne_zero
    (((VermaModule.isCategoryO P (P.weylDot hA' w lam)).multiplicity_ne_zero_iff
      (hl.mem_cone_of_mem_factorWeights hηl) hl).mpr hηl)
  -- `w·λ ≤ w'·λ` by minimality
  have hb' : w'.val (μ + P.rho) = w.val (μ + P.rho) := by
    rw [← P.weylDot_add_rho hA' w' μ, ← P.weylDot_add_rho hA' w μ, hw'y]
  obtain ⟨c, hc, hce⟩ := exists_apply_sub_eq_rootOf_of_upperClosureCondition_of_integral hA
    (sub_rho_integral P hA hν hz hzν) hlam hC hb'
  have h0 : P.rootOf (c + k) = 0 := by
    rw [map_add, ← hce]
    simp only [weylDot] at hke
    linear_combination (norm := abel) hke
  have hck : c + k = 0 := P.rootOf_injective (by rw [h0, map_zero])
  have hk0 : k = 0 := by
    ext j
    have h1 := hc j
    have h2 := hk j
    have h3 := congrFun hck j
    simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 h3 ⊢
    omega
  rw [hk0, map_zero, sub_zero] at hke
  have hxy : P.weylDot hA' w' lam = P.weylDot hA' w lam := by
    exact hke
  rw [hxy] at hns
  exact hns hsub

include hA in
/-- **Translation of simple modules, vanishing.** Under the hypotheses of
`translation_verma_of_isAntidominant`, for `w ∈ W_[λ]`, if some positive root `β` with `⟨w(μ + ρ),
β^∨⟩ = 0` has `⟨w(λ + ρ), β^∨⟩ > 0`, then `T_λ^μ L(w·λ) = 0`. -/
theorem translation_irreducible_of_not_upperClosureCondition_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan)
    (hw : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    (hC : ¬P.UpperClosureCondition hA.isGeneralizedCartan (w.val (lam + P.rho))
      (w.val (μ + P.rho))) :
    Subsingleton (centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
      (centralCharacter P μ)
      (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) := by
  classical
  have hA' := hA.isGeneralizedCartan
  -- descend to `w''` satisfying the condition
  have hwρ : w ∈ P.integralWeylGroup hA' (lam + P.rho) := by
    rwa [P.integralWeylGroup_eq_of_integral hA' (μ' := lam) fun j ↦ ⟨1, by simp⟩]
  obtain ⟨w'', -, hw''b, hw''U, hchain⟩ := exists_upperClosureCondition_of_integral hA
    (sub_rho_integral P hA hν hz hzν) hlam hwρ
  have hy : P.weylDot hA' w'' μ = P.weylDot hA' w μ := by
    simp only [weylDot, hw''b]
  have hne : P.weylDot hA' w lam ≠ P.weylDot hA' w'' lam := by
    intro h
    have h' : w''.val (lam + P.rho) = w.val (lam + P.rho) := by
      rw [← P.weylDot_add_rho hA' w'' lam, ← P.weylDot_add_rho hA' w lam, h]
    exact hC (h' ▸ hw''U)
  obtain ⟨e''⟩ := translation_irreducible_of_upperClosureCondition_of_isAntidominant P hA hlam hμ
      hfacet hν hz hzν
    w'' (by rw [hw''b]; exact hw''U)
  -- `L(w''·λ)` is a composition factor of `M(w·λ)`
  obtain ⟨d, hdpos, hpos⟩ := hA.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hpos.isHermitian
  have hKK : (VermaModule.isCategoryO P (P.weylDot hA' w lam)).multiplicity
      (P.weylDot hA' w'' lam) ≠ 0 :=
    (VermaModule.multiplicity_ne_zero_iff_reflTransGen P
      (Symmetrization.ofDiagonal d hdpos hsymm) hA' _ _).mpr
      (Relation.ReflTransGen.lift (fun ξ ↦ ξ - P.rho)
        (fun _ _ h ↦ kacKazhdanStep_of_wallStep P _ hA' h) _ _ hchain)
  -- the count along a local composition series
  obtain ⟨l, hl⟩ := (VermaModule.isCategoryO P
    (P.weylDot hA' w lam)).exists_isLocalCompositionSeries (P.weylDot hA' w μ - ν)
  have hsum := sum_multiplicity_translation_eq_one_of_isAntidominant P hA hlam hμ hfacet hν hz hzν
      w hl
  have hx : P.weylDot hA' w lam ∈ factorWeights l :=
    ((VermaModule.isCategoryO P (P.weylDot hA' w lam)).multiplicity_ne_zero_iff
      (weylDot_sub_mem_cone_weylDot P hA hν hz hzν w) hl).mp (by
        rw [VermaModule.multiplicity_self]
        exact one_ne_zero)
  have hx'' : P.weylDot hA' w'' lam ∈ factorWeights l :=
    ((VermaModule.isCategoryO P (P.weylDot hA' w lam)).multiplicity_ne_zero_iff
      (hy ▸ weylDot_sub_mem_cone_weylDot P hA hν hz hzν w'') hl).mp hKK
  have hle := List.add_le_sum_map_of_mem_of_ne hx hx'' hne fun η ↦
    ((IrreducibleModule.isCategoryO P η).centralTranslation P
      (IrreducibleModule.isCategoryO P ν) (centralCharacter P lam)
      (centralCharacter P μ)).multiplicity (P.weylDot hA' w μ)
  rw [hsum, ← IsCategoryO.multiplicity_congr (IrreducibleModule.isCategoryO P _) _ e'',
    IrreducibleModule.multiplicity_eq, ite_eq_left hy.symm] at hle
  rcases translation_irreducible_of_isAntidominant P hA hlam hμ hfacet hν hz hzν w with hsub | he
  · exact hsub
  · obtain ⟨e⟩ := he
    exfalso
    rw [← IsCategoryO.multiplicity_congr (IrreducibleModule.isCategoryO P _) _ e,
      IrreducibleModule.multiplicity_eq, ite_eq_left rfl] at hle
    omega

include hA in
/-- **Translation of simple modules** (Humphreys, GSM 94, Theorem 7.9; arbitrary weights, finite
type, algebraically closed field of characteristic zero). Under the hypotheses of
`translation_verma_of_isAntidominant`, for every `w ∈ W`, if `w·μ` lies in the upper closure of the
facet of `w·λ`, then `T_λ^μ L(w·λ) ≅ L(w·μ)`. -/
theorem translation_irreducible_of_memUpperClosure_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan)
    (hU : P.MemUpperClosure hA.isGeneralizedCartan (P.weylDot hA.isGeneralizedCartan w lam)
      (P.weylDot hA.isGeneralizedCartan w μ)) :
    Nonempty (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ)
        (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) :=
  translation_irreducible_of_upperClosureCondition_of_isAntidominant P hA hlam hμ hfacet hν hz hzν w
    ((memUpperClosure_weylDot_iff_of_isAntidominant hA hlam hμ
      (sub_rho_integral P hA hν hz hzν) hfacet w).mp hU)

include hA in
/-- **Translation of simple modules** (Humphreys, GSM 94, Theorem 7.9; arbitrary weights, finite
type, algebraically closed field of characteristic zero). Under the hypotheses of
`translation_verma_of_isAntidominant`, for `w ∈ W_[λ]`, if `w·μ` does not lie in the upper closure
of the facet of `w·λ`, then `T_λ^μ L(w·λ) = 0`. -/
theorem translation_irreducible_of_not_memUpperClosure_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan)
    (hw : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    (hU : ¬P.MemUpperClosure hA.isGeneralizedCartan (P.weylDot hA.isGeneralizedCartan w lam)
      (P.weylDot hA.isGeneralizedCartan w μ)) :
    Subsingleton (centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
      (centralCharacter P μ)
      (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) :=
  translation_irreducible_of_not_upperClosureCondition_of_isAntidominant P hA hlam hμ hfacet hν hz
      hzν w hw
    fun hC ↦
    hU ((memUpperClosure_weylDot_iff_of_isAntidominant hA hlam hμ
      (sub_rho_integral P hA hν hz hzν) hfacet w).mpr hC)

include hA in
/-- **The upper-closure criterion** (Humphreys, GSM 94, Theorem 7.9; arbitrary weights,
finite type, algebraically closed field of characteristic zero). Under the hypotheses of
`translation_verma_of_isAntidominant`, for `w ∈ W_[λ]`, `T_λ^μ L(w·λ) ≅ L(w·μ)` iff `w·μ` lies
in the upper closure of the facet of `w·λ`; otherwise `T_λ^μ L(w·λ) = 0`
(`translation_irreducible_of_not_memUpperClosure_of_isAntidominant`). -/
theorem nonempty_equiv_translation_irreducible_iff_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan)
    (hw : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam) :
    Nonempty (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ)
        (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) ↔
      P.MemUpperClosure hA.isGeneralizedCartan (P.weylDot hA.isGeneralizedCartan w lam)
        (P.weylDot hA.isGeneralizedCartan w μ) := by
  refine ⟨fun ⟨e⟩ ↦ ?_,
    translation_irreducible_of_memUpperClosure_of_isAntidominant P hA hlam hμ hfacet hν hz hzν w⟩
  by_contra hU
  have hs := translation_irreducible_of_not_memUpperClosure_of_isAntidominant P hA hlam hμ hfacet
      hν hz hzν w hw
    hU
  exact IrreducibleModule.hwv_ne_zero P _ (e.injective (Subsingleton.elim _ _))


end Matrix.Realization.KacMoodyAlgebra
