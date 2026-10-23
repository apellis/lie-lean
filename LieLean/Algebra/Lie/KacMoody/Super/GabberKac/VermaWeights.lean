/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Super.GabberKac.FreeGrading
import LieLean.Algebra.Lie.KacMoody.Super.GabberKac.WeightQuotient

/-!
# Weight spaces of the Verma modules of `G(A, τ)`

Let `M̄(Λ) = M(Λ) / U R v_Λ` be the Verma module of `G(A, τ)`, so that
`M̄(Λ) = T(V) / J`, `t ↦ f(t) v̄_Λ`, with `J = T(V) f⁻¹(R)` independent of `Λ`
(`GVerma.fAlg_smul_hwv_eq_zero_iff`). This file shows that `v̄_Λ ≠ 0`, that the weight space
`M̄(Λ)_{Λ - β}` is spanned by the vectors `f_w v̄_Λ` for the words `w` of weight `β`, hence is
finite-dimensional, and that its dimension depends only on `β` (`GVerma.finrank_modWeightSpace`):
`dim M̄(Λ)_{Λ - β} = dim M̄(0)_{-β}`. These are the inputs of the computation of the character of
`M̄(Λ)` ([Kac78] §2, cf. [Kac] §9.11).

## Main results

* `Matrix.Realization.SuperEnveloping.GVerma.hwv_ne_zero`: `v̄_Λ ≠ 0`.
* `Matrix.Realization.SuperEnveloping.GVerma.modWeightSpace_sub_eq`: the weight spaces of `M̄(Λ)`.
* `Matrix.Realization.SuperEnveloping.GVerma.finrank_modWeightSpace`:
  `dim M̄(Λ)_μ = vermaDim (Λ - μ)`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.2–2.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.11.
-/

open Module

noncomputable section

namespace Matrix.Realization.SuperEnveloping

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H} {p : ι → ZMod 2} [CharZero K]

/-- The enveloping superalgebra `U(G̃(A, τ))`. -/
local notation "𝒰" => SuperEnveloping P p

variable (P) in
/-- Only finitely many words have a given weight. -/
lemma finite_setOf_rootOf_wordVec_eq (β : Dual K H) :
    {w : List ι | P.rootOf (wordVec w) = β}.Finite := by
  classical
  by_cases hβ : ∃ d, P.rootOf d = β
  · refine (List.finite_length_eq (α := ι) (n := (∑ i, hβ.choose i).toNat)).subset fun w hw ↦ ?_
    have : wordVec w = hβ.choose := P.rootOf_injective (hw.trans hβ.choose_spec.symm)
    simp only [Set.mem_ofPred_eq]
    rw [← this, sum_wordVec, Int.toNat_natCast]
  · exact Set.Finite.subset Set.finite_empty fun w hw ↦ hβ ⟨_, hw⟩

lemma weightProj_zero_eq_zero_of_mem_fPre {t : FreeAlgebra K ι} (ht : t ∈ fPre P p) :
    FreeAlgebra.weightProj K 0 t = 0 := by
  apply fAlg_injective P p
  rw [map_zero, ← wProj_fAlg]
  have h0 : -P.rootOf (natVec (0 : ι →₀ ℕ)) = 0 := by
    have : natVec (0 : ι →₀ ℕ) = 0 := by funext i; simp [natVec]
    rw [this, map_zero, neg_zero]
  rw [h0]
  have hle : (⨆ μ ∈ {μ : Dual K H | μ ≠ 0}, weightSpace P p μ) ≤ LinearMap.ker (wProj P p 0) :=
    iSup₂_le fun μ hμ y hy ↦ LinearMap.mem_ker.2 (wProj_of_mem_ne P p hμ hy)
  exact LinearMap.mem_ker.1 (hle (maxIdeal_le_iSup_ne_zero P p ((mem_fPre).1 ht)))

/-- The weight-zero component of an element of `J = T(V) f⁻¹(R)` vanishes. -/
lemma weightProj_zero_eq_zero_of_mem_gIdeal {t : FreeAlgebra K ι} (ht : t ∈ gIdeal P p) :
    FreeAlgebra.weightProj K 0 t = 0 := by
  induction ht using Submodule.span_induction with
  | mem x hx => exact weightProj_zero_eq_zero_of_mem_fPre hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx =>
    rw [smul_eq_mul]
    induction a using FreeAlgebra.induction_wordBasis with
    | zero => simp
    | add y z hy hz => rw [add_mul, map_add, hy, hz, add_zero]
    | smul c y hy => rw [smul_mul_assoc, map_smul, hy, smul_zero]
    | word w =>
      rw [FreeAlgebra.weightProj_wordBasis_mul]
      split_ifs with h
      · rw [nonpos_iff_eq_zero.1 h, tsub_zero, hx, mul_zero]
      · rfl

lemma one_notMem_gIdeal : (1 : FreeAlgebra K ι) ∉ gIdeal P p := by
  intro h
  have := weightProj_zero_eq_zero_of_mem_gIdeal h
  rw [← FreeAlgebra.word_nil (R := K) (X := ι), word_eq_wordBasis,
    FreeAlgebra.weightProj_wordBasis] at this
  simp only [LusztigF.wordWeight_nil, ↓reduceIte] at this
  rw [← word_eq_wordBasis, FreeAlgebra.word_nil] at this
  exact one_ne_zero this

namespace GVerma

variable (P p) (Λ : Dual K H)

/-- The highest weight vector of `M̄(Λ)` is nonzero. -/
theorem hwv_ne_zero : hwv P p Λ ≠ 0 := by
  intro h0
  refine one_notMem_gIdeal (P := P) (p := p) ((fAlg_smul_hwv_eq_zero_iff (Λ := Λ)).1 ?_)
  rw [map_one, one_smul, h0]

/-- The vector `f_w v̄_Λ` of `M̄(Λ)`. -/
def wordVector (w : List ι) : GVerma P p Λ := fAlg P p (FreeAlgebra.word w) • hwv P p Λ

variable {P p Λ}

lemma wordVector_nil : wordVector P p Λ [] = hwv P p Λ := by
  simp [wordVector, FreeAlgebra.word_nil]

lemma wordVector_mem (w : List ι) :
    wordVector P p Λ w ∈ modWeightSpace P p (GVerma P p Λ) (Λ - P.rootOf (wordVec w)) :=
  fAlg_word_smul_hwv_mem w

variable (P p Λ) in
/-- The vectors `f_w v̄_Λ` span `M̄(Λ)`. -/
lemma span_wordVector : Submodule.span K (Set.range (wordVector P p Λ)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun v ↦ ?_
  obtain ⟨t, rfl⟩ := exists_eq_fAlg_smul_hwv v
  have ht : t ∈ Submodule.span K (Set.range (FreeAlgebra.basisFreeMonoid K ι)) := by
    rw [Basis.span_eq]; trivial
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    exact Submodule.subset_span ⟨FreeMonoid.toList w, by simp [wordVector, FreeAlgebra.word]⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, add_smul]; exact add_mem hy hz
  | smul c y _ hy => rw [map_smul, smul_assoc]; exact Submodule.smul_mem _ c hy

variable (P p Λ) in
/-- The weight space `M̄(Λ)_{Λ - β}` is spanned by the `f_w v̄_Λ` with `w` of weight `β`. -/
theorem modWeightSpace_sub_eq (β : Dual K H) :
    modWeightSpace P p (GVerma P p Λ) (Λ - β) =
      Submodule.span K (wordVector P p Λ '' {w | P.rootOf (wordVec w) = β}) := by
  refine le_antisymm (fun v hv ↦ ?_) (Submodule.span_le.2 ?_)
  · have hG : ∀ g ∈ Set.range (wordVector P p Λ), ∃ ν, g ∈ modWeightSpace P p (GVerma P p Λ) ν :=
      fun g ⟨w, hw⟩ ↦ ⟨_, hw ▸ wordVector_mem w⟩
    have := (iSupIndep_modWeightSpace (GVerma P p Λ)).mem_span_inter hG
      (span_wordVector P p Λ ▸ Submodule.mem_top) hv
    rw [← Submodule.span_insert_zero (R := K)]
    refine Submodule.span_mono ?_ this
    rintro g ⟨⟨w, rfl⟩, hg⟩
    by_cases h0 : wordVector P p Λ w = 0
    · exact Or.inl h0
    · refine Or.inr ⟨w, ?_, rfl⟩
      by_contra hne
      refine h0 (Submodule.disjoint_def.1
        ((iSupIndep_modWeightSpace (GVerma P p Λ)).pairwiseDisjoint
          (fun h ↦ hne (sub_right_injective h))) _ (wordVector_mem w) hg)
  · rintro _ ⟨w, hw, rfl⟩
    exact hw ▸ wordVector_mem w

instance finiteDimensional_modWeightSpace (μ : Dual K H) :
    FiniteDimensional K (modWeightSpace P p (GVerma P p Λ) μ) := by
  have := modWeightSpace_sub_eq P p Λ (Λ - μ)
  rw [sub_sub_cancel] at this
  rw [this]
  exact FiniteDimensional.span_of_finite K
    ((finite_setOf_rootOf_wordVec_eq P (Λ - μ)).image _)

/-! ### Independence of `Λ` -/

variable (P p Λ) in
/-- The surjection `T(V) → M̄(Λ)`, `t ↦ f(t) v̄_Λ`. -/
def ofTensor : FreeAlgebra K ι →ₗ[K] GVerma P p Λ where
  toFun t := fAlg P p t • hwv P p Λ
  map_add' s t := by rw [map_add, add_smul]
  map_smul' c t := by rw [map_smul, smul_assoc, RingHom.id_apply]

lemma ofTensor_apply (t : FreeAlgebra K ι) : ofTensor P p Λ t = fAlg P p t • hwv P p Λ := rfl

lemma ker_ofTensor : LinearMap.ker (ofTensor P p Λ) = (gIdeal P p).restrictScalars K := by
  ext t
  rw [LinearMap.mem_ker, ofTensor_apply, fAlg_smul_hwv_eq_zero_iff, Submodule.restrictScalars_mem]

lemma surjective_ofTensor : Function.Surjective (ofTensor P p Λ) :=
  fun v ↦ exists_eq_fAlg_smul_hwv v

variable (P p) in
/-- The linear isomorphism `M̄(Λ) ≃ M̄(Λ')`, `f(t) v̄_Λ ↦ f(t) v̄_Λ'`. -/
def shiftEquiv (Λ Λ' : Dual K H) : GVerma P p Λ ≃ₗ[K] GVerma P p Λ' :=
  ((ofTensor P p Λ).quotKerEquivOfSurjective surjective_ofTensor).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_ofTensor.trans ker_ofTensor.symm)).trans
      ((ofTensor P p Λ').quotKerEquivOfSurjective surjective_ofTensor))

lemma shiftEquiv_fAlg_smul_hwv (Λ' : Dual K H) (t : FreeAlgebra K ι) :
    shiftEquiv P p Λ Λ' (fAlg P p t • hwv P p Λ) = fAlg P p t • hwv P p Λ' := by
  have : ((ofTensor P p Λ).quotKerEquivOfSurjective surjective_ofTensor).symm
      (fAlg P p t • hwv P p Λ) = Submodule.Quotient.mk t := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [shiftEquiv, LinearEquiv.trans_apply, this, Submodule.quotEquivOfEq_mk]
  rfl

lemma shiftEquiv_wordVector (Λ' : Dual K H) (w : List ι) :
    shiftEquiv P p Λ Λ' (wordVector P p Λ w) = wordVector P p Λ' w :=
  shiftEquiv_fAlg_smul_hwv Λ' _

lemma map_shiftEquiv_modWeightSpace (Λ' β : Dual K H) :
    (modWeightSpace P p (GVerma P p Λ) (Λ - β)).map (shiftEquiv P p Λ Λ').toLinearMap =
      modWeightSpace P p (GVerma P p Λ') (Λ' - β) := by
  rw [modWeightSpace_sub_eq, modWeightSpace_sub_eq, Submodule.map_span, Set.image_image]
  simp only [LinearEquiv.coe_coe, shiftEquiv_wordVector]

variable (P p) in
/-- `dim M̄(0)_{-β}`: the dimension of the weight space `M̄(Λ)_{Λ - β}` for every `Λ`
(`GVerma.finrank_modWeightSpace`). -/
def vermaDim (β : Dual K H) : ℕ := finrank K (modWeightSpace P p (GVerma P p 0) (-β))

/-- `dim M̄(Λ)_μ = vermaDim (Λ - μ)`. -/
theorem finrank_modWeightSpace (μ : Dual K H) :
    finrank K (modWeightSpace P p (GVerma P p Λ) μ) = vermaDim P p (Λ - μ) := by
  rw [vermaDim, ← LinearEquiv.finrank_map_eq (shiftEquiv P p Λ 0), ← zero_sub,
    ← map_shiftEquiv_modWeightSpace, sub_sub_cancel]

lemma vermaDim_zero : vermaDim P p 0 = 1 := by
  have h := modWeightSpace_sub_eq P p 0 0
  rw [sub_zero] at h
  rw [vermaDim, neg_zero, h]
  have : wordVector P p 0 '' {w | P.rootOf (wordVec w) = 0} = {hwv P p 0} := by
    ext v
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [← map_zero P.rootOf] at hw
      rw [wordVec_eq_zero_iff.1 (P.rootOf_injective hw), wordVector_nil]
    · rintro rfl
      exact ⟨[], by simp, wordVector_nil⟩
  rw [this, finrank_span_singleton (hwv_ne_zero P p 0)]

/-- `vermaDim β = 0` unless `β ∈ Q₊`. -/
lemma exists_eq_rootOf_of_vermaDim_ne_zero {β : Dual K H} (hβ : vermaDim P p β ≠ 0) :
    ∃ d : ι → ℤ, 0 ≤ d ∧ β = P.rootOf d := by
  by_contra hne
  push Not at hne
  apply hβ
  have h := modWeightSpace_sub_eq P p 0 β
  rw [zero_sub] at h
  rw [vermaDim, h]
  have : wordVector P p 0 '' {w | P.rootOf (wordVec w) = β} = ∅ := by
    refine Set.image_eq_empty.2 (Set.eq_empty_iff_forall_notMem.2 fun w hw ↦ ?_)
    exact hne _ (wordVec_nonneg w) hw.symm
  rw [this, Submodule.span_empty, finrank_bot]

end GVerma

end Matrix.Realization.SuperEnveloping
