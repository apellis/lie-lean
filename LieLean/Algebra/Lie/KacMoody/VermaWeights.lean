/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Verma

/-!
# Weights of Verma modules

Let `M(Λ)` be the Verma module over the Kac–Moody algebra `𝔤(A)`. We show that `M(Λ)` is spanned
by the vectors `f_{j₁} ⋯ f_{jₖ} v_Λ`; as `f_{j₁} ⋯ f_{jₖ} v_Λ` has weight
`Λ - (α_{j₁} + ⋯ + α_{jₖ})`, this gives the weight space decomposition
`M(Λ) = ⊕_{β ∈ Q₊} M(Λ)_{Λ - β}` with finite-dimensional weight spaces, and
`M(Λ)_Λ = K v_Λ` ([Kac] §9.2 (check)).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.fWord`: the element `f_{j₁} ⋯ f_{jₖ}` of
  `U(𝔤)` attached to a word `j₁ ⋯ jₖ`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.weightSpace`: the weight space `M(Λ)_μ`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.span_fWord_smul_eq_top`: `M(Λ)` is spanned by
  the `f_{j₁} ⋯ f_{jₖ} v_Λ`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.iSup_weightSpace_eq_top`:
  `M(Λ) = ⨆_{β ∈ Q₊} M(Λ)_{Λ - β}`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.weightSpace_eq_bot`: `M(Λ)_μ = 0` unless
  `μ ∈ Λ - Q₊`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.finiteDimensional_weightSpace`: the weight
  spaces of `M(Λ)` are finite-dimensional.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.weightSpace_self`: `M(Λ)_Λ = K v_Λ`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.2.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (Λ : Dual K H)

local notation "𝓤" => UniversalEnvelopingAlgebra K (KacMoodyAlgebra P)
local notation "ιᵤ" => UniversalEnvelopingAlgebra.ι K
local notation "wt" => AuxLieAlgebra.wordWt P

lemma f_mem_rootSpace (i : ι) : f P i ∈ rootSpace P (-P.root i) := fun a ↦ by
  rw [lie_h_f, LinearMap.neg_apply, neg_smul]

namespace VermaModule

/-- The element `f_{j₁} ⋯ f_{jₖ}` of `U(𝔤)` attached to a word `j₁ ⋯ jₖ`. -/
def fWord (w : List ι) : 𝓤 := (w.map fun i ↦ ιᵤ (f P i)).prod

@[simp] lemma fWord_nil : fWord P [] = 1 := rfl

lemma fWord_cons (j : ι) (w : List ι) : fWord P (j :: w) = ιᵤ (f P j) * fWord P w := by
  simp [fWord]

/-- The weight space `M(Λ)_μ`. -/
abbrev weightSpace (μ : Dual K H) : Submodule K (VermaModule P Λ) :=
  weightSpaceOfMap (VermaModule P Λ) (h P) μ

lemma hwv_mem_weightSpace : hwv P Λ ∈ weightSpace P Λ Λ := fun a ↦ lie_h_hwv P Λ a

lemma fWord_smul_cons (j : ι) (w : List ι) :
    fWord P (j :: w) • hwv P Λ = ⁅f P j, fWord P w • hwv P Λ⁆ := by
  rw [fWord_cons, mul_smul, lie_eq_smul]

/-- `f_{j₁} ⋯ f_{jₖ} v_Λ` has weight `Λ - (α_{j₁} + ⋯ + α_{jₖ})`. -/
lemma fWord_smul_mem_weightSpace (w : List ι) :
    fWord P w • hwv P Λ ∈ weightSpace P Λ (Λ - wt w) := by
  induction w with
  | nil => simpa using hwv_mem_weightSpace P Λ
  | cons j w ih =>
    rw [fWord_smul_cons]
    convert lie_mem_weightSpaceOfMap (h P) (f_mem_rootSpace P j) ih using 2
    rw [AuxLieAlgebra.wordWt_cons]
    abel

/-- The span of the vectors `f_{j₁} ⋯ f_{jₖ} v_Λ` of weight `μ`. -/
def wordSpan (μ : Dual K H) : Submodule K (VermaModule P Λ) :=
  Submodule.span K ((fun w ↦ fWord P w • hwv P Λ) '' {w | Λ - wt w = μ})

lemma wordSpan_le_weightSpace (μ : Dual K H) : wordSpan P Λ μ ≤ weightSpace P Λ μ := by
  rw [wordSpan, Submodule.span_le]
  rintro _ ⟨w, rfl, rfl⟩
  exact fWord_smul_mem_weightSpace P Λ w

lemma lie_mem_span_of_forall {M : Type*} [AddCommGroup M] [Module K M]
    [LieRingModule P.KacMoodyAlgebra M] [LieModule K P.KacMoodyAlgebra M] {s : Set M}
    {y : P.KacMoodyAlgebra} (hs : ∀ m ∈ s, ⁅y, m⁆ ∈ Submodule.span K s) :
    ∀ m ∈ Submodule.span K s, ⁅y, m⁆ ∈ Submodule.span K s := by
  intro m hm
  induction hm using Submodule.span_induction with
  | mem m hm => exact hs m hm
  | zero => simp
  | add m n _ _ hm hn => rw [lie_add]; exact add_mem hm hn
  | smul c m _ hm => rw [lie_smul]; exact Submodule.smul_mem _ c hm

/-- The span of all `f_{j₁} ⋯ f_{jₖ} v_Λ`. -/
abbrev fWordSpan : Submodule K (VermaModule P Λ) :=
  Submodule.span K (Set.range fun w ↦ fWord P w • hwv P Λ)

lemma lie_h_mem_fWordSpan (a : H) :
    ∀ m ∈ fWordSpan P Λ, ⁅h P a, m⁆ ∈ fWordSpan P Λ := by
  refine lie_mem_span_of_forall P ?_
  rintro _ ⟨w, rfl⟩
  rw [fWord_smul_mem_weightSpace P Λ w a]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)

lemma lie_f_mem_fWordSpan (i : ι) :
    ∀ m ∈ fWordSpan P Λ, ⁅f P i, m⁆ ∈ fWordSpan P Λ := by
  refine lie_mem_span_of_forall P ?_
  rintro _ ⟨w, rfl⟩
  rw [← fWord_smul_cons]
  exact Submodule.subset_span ⟨i :: w, rfl⟩

lemma lie_e_mem_fWordSpan (i : ι) :
    ∀ m ∈ fWordSpan P Λ, ⁅e P i, m⁆ ∈ fWordSpan P Λ := by
  refine lie_mem_span_of_forall P ?_
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => simp
  | cons j w ih =>
    dsimp only at ih ⊢
    rw [fWord_smul_cons, leibniz_lie, lie_e_f]
    refine add_mem ?_ (lie_f_mem_fWordSpan P Λ j _ ih)
    split_ifs
    · exact lie_h_mem_fWordSpan P Λ _ _ (Submodule.subset_span ⟨w, rfl⟩)
    · rw [zero_lie]; exact zero_mem _

/-- `M(Λ)` is spanned by the vectors `f_{j₁} ⋯ f_{jₖ} v_Λ` ([Kac] §9.2 (check)). -/
theorem span_fWord_smul_eq_top : fWordSpan P Λ = ⊤ := by
  let N : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ) :=
    { fWordSpan P Λ with
      lie_mem := fun {x m} hm ↦ lie_mem_of_generators P (fWordSpan P Λ)
        (lie_e_mem_fWordSpan P Λ) (lie_f_mem_fWordSpan P Λ) (lie_h_mem_fWordSpan P Λ) x m hm }
  have hN : N = ⊤ := eq_top_of_hwv_mem P Λ (Submodule.subset_span ⟨[], by simp⟩)
  exact congrArg LieSubmodule.toSubmodule hN

lemma fWordSpan_le_iSup_wordSpan : fWordSpan P Λ ≤ ⨆ μ, wordSpan P Λ μ := by
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact Submodule.mem_iSup_of_mem (Λ - wt w) (Submodule.subset_span ⟨w, rfl, rfl⟩)

/-- The weight space `M(Λ)_μ` is spanned by the vectors `f_{j₁} ⋯ f_{jₖ} v_Λ` of weight `μ`. -/
theorem weightSpace_le_wordSpan (μ : Dual K H) : weightSpace P Λ μ ≤ wordSpan P Λ μ := by
  intro m hm
  refine mem_of_mem_iSup_of_le (h P) (wordSpan P Λ) (wordSpan_le_weightSpace P Λ) hm ?_
  exact fWordSpan_le_iSup_wordSpan P Λ (by rw [span_fWord_smul_eq_top]; trivial)

theorem weightSpace_eq_wordSpan (μ : Dual K H) : weightSpace P Λ μ = wordSpan P Λ μ :=
  le_antisymm (weightSpace_le_wordSpan P Λ μ) (wordSpan_le_weightSpace P Λ μ)

omit [Fintype ι] in
lemma counts_nonneg (w : List ι) : 0 ≤ AuxLieAlgebra.counts w := fun _ ↦ Int.natCast_nonneg _

/-- `M(Λ) = ⨆_{β ∈ Q₊} M(Λ)_{Λ - β}` ([Kac] §9.2 (check)). -/
theorem iSup_weightSpace_eq_top :
    ⨆ (k : ι → ℤ) (_ : 0 ≤ k), weightSpace P Λ (Λ - P.rootOf k) = ⊤ := by
  rw [eq_top_iff, ← span_fWord_smul_eq_top, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  have := fWord_smul_mem_weightSpace P Λ w
  rw [AuxLieAlgebra.wordWt_eq_rootOf] at this
  exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (counts_nonneg w) this)

/-- `M(Λ)_μ = 0` unless `μ ∈ Λ - Q₊` ([Kac] §9.2 (check)). -/
theorem weightSpace_eq_bot {μ : Dual K H} (hμ : ∀ k : ι → ℤ, 0 ≤ k → μ ≠ Λ - P.rootOf k) :
    weightSpace P Λ μ = ⊥ := by
  rw [weightSpace_eq_wordSpan, wordSpan, Submodule.span_eq_bot]
  rintro _ ⟨w, hw, rfl⟩
  refine absurd ?_ (hμ (AuxLieAlgebra.counts w) (counts_nonneg w))
  rw [← hw, AuxLieAlgebra.wordWt_eq_rootOf]

variable [CharZero K]

omit [DecidableEq ι] in
lemma finite_setOf_wordWt_eq (ν : Dual K H) : {w : List ι | wt w = ν}.Finite := by
  classical
  by_cases hν : ∃ w₀, wt w₀ = ν
  · obtain ⟨w₀, rfl⟩ := hν
    refine (List.finite_length_eq ι w₀.length).subset fun w hw ↦ ?_
    have hw' : AuxLieAlgebra.counts w = AuxLieAlgebra.counts w₀ := by
      apply P.rootOf_injective
      rw [← AuxLieAlgebra.wordWt_eq_rootOf, ← AuxLieAlgebra.wordWt_eq_rootOf]
      exact hw
    have h1 := AuxLieAlgebra.sum_counts w
    rw [hw', AuxLieAlgebra.sum_counts] at h1
    change w.length = w₀.length
    exact_mod_cast h1.symm
  · convert Set.finite_empty
    ext w
    simpa using fun h ↦ hν ⟨w, h⟩

/-- The weight spaces of `M(Λ)` are finite-dimensional ([Kac] §9.2 (check)). -/
theorem finiteDimensional_weightSpace (μ : Dual K H) :
    FiniteDimensional K (weightSpace P Λ μ) := by
  have hfin : (wordSpan P Λ μ).FG := by
    refine Submodule.fg_def.mpr ⟨_, Set.Finite.image _ ?_, rfl⟩
    refine (finite_setOf_wordWt_eq P (Λ - μ)).subset fun w hw ↦ ?_
    simp only [Set.mem_ofPred_eq] at hw ⊢
    rw [← hw, sub_sub_cancel]
  have : FiniteDimensional K (wordSpan P Λ μ) := Module.Finite.iff_fg.mpr hfin
  exact Submodule.finiteDimensional_of_le (weightSpace_le_wordSpan P Λ μ)

/-- The highest weight space of `M(Λ)` is `M(Λ)_Λ = K v_Λ` ([Kac] §9.2 (check)). -/
theorem weightSpace_self : weightSpace P Λ Λ = K ∙ hwv P Λ := by
  refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr
    (hwv_mem_weightSpace P Λ))
  rw [weightSpace_eq_wordSpan, wordSpan]
  refine Submodule.span_mono ?_
  rintro _ ⟨w, hw, rfl⟩
  have hw' : P.rootOf (AuxLieAlgebra.counts w) = P.rootOf 0 := by
    rw [← AuxLieAlgebra.wordWt_eq_rootOf, map_zero]
    simpa using hw
  have h1 := AuxLieAlgebra.sum_counts w
  rw [P.rootOf_injective hw'] at h1
  simp only [Pi.zero_apply, Finset.sum_const_zero] at h1
  obtain rfl : w = [] := List.length_eq_zero_iff.mp (by exact_mod_cast h1.symm)
  simp

end VermaModule

end Matrix.Realization.KacMoodyAlgebra

end
