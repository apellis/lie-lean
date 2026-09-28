/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.Minimality
import LieLean.Algebra.Lie.KacMoody.WeightBasis
import LieLean.Algebra.Lie.KacMoody.Character

/-!
# Bounded-weight Nakayama

## Main results

A Cartan-diagonalizable module whose weights lie in a finite union of upper cones
is zero if its actual negative-nilradical coinvariants vanish. No finite-dimensionality
of the module or weight spaces, nor finite-type assumption, is used.

## References

Proof reconstructed from the weight decomposition, Dickson's lemma (`WeightOrd.isPWO_iff`),
and the simple-generator presentation of the negative nilradical. This is a supporting
Nakayama step, not a proof of detection of actual BGG syzygy generators or exactness.
-/

open Module LieModule
noncomputable section
namespace Matrix.Realization.KacMoodyAlgebra.BGGMinimality

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {V : Type*} [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]

omit [CharZero K] in
/-- A subspace containing every simple negative-generator action contains the actual
negative-nilradical action span. -/
lemma nNegActionSpan_le_of_lie_f (S : Submodule K V)
    (hS : ∀ i (v : V), ⁅f P i, v⁆ ∈ S) : nNegActionSpan P V ≤ S := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, v, rfl⟩
  obtain ⟨y, rfl⟩ := hx
  change ⁅fHom P y, v⁆ ∈ S
  induction y using FreeLieAlgebra.induction_on generalizing v with
  | of i => simpa only [fHom_of] using hS i v
  | zero => simp
  | add x y hx hy => rw [map_add, add_lie]; exact S.add_mem (hx v) (hy v)
  | smul c x hx => rw [map_smul, smul_lie]; exact S.smul_mem c (hx v)
  | lie x y hx hy => rw [LieHom.map_lie, lie_lie]; exact S.sub_mem (hx _) (hy _)

omit [CharZero K] in
/-- A maximal occupied weight cannot meet the negative action span. The finite-support
weight decomposition is supplied by the existing diagonalizable weight basis. -/
lemma disjoint_weightSpace_nNegActionSpan (hV : IsHDiagonalizable P V)
    (μ : Dual K H) (hμ : ∀ i, weightSpace P V (μ + P.root i) = ⊥) :
    Disjoint (weightSpace P V μ) (nNegActionSpan P V) := by
  classical
  let S : Submodule K V := ⨆ ν, ⨆ (_ : ν ≠ μ), weightSpace P V ν
  have hS : nNegActionSpan P V ≤ S := by
    apply nNegActionSpan_le_of_lie_f
    intro i v
    induction (diagWeightBasis hV).mem_span v using Submodule.span_induction with
    | zero => simp
    | add v w _ _ hv hw => rw [lie_add]; exact S.add_mem hv hw
    | smul c v _ hv => rw [lie_smul]; exact S.smul_mem c hv
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      by_cases hj : j.1 - P.root i = μ
      · have heq : j.1 = μ + P.root i := sub_eq_iff_eq_add.mp hj
        have hz := diagWeightBasis_mem hV j
        rw [heq, hμ i, Submodule.mem_bot] at hz
        simp [hz]
      · have hle : weightSpace P V (j.1 - P.root i) ≤ S :=
          le_iSup_of_le (j.1 - P.root i) (le_iSup_of_le hj le_rfl)
        exact hle (toEnd_f_mem_weightSpace i (diagWeightBasis_mem hV j))
  exact ((iSupIndep_weightSpaceOfMap (M := V) (h P)) μ).mono_right hS

/-- Bounded-weight Nakayama: a diagonalizable module bounded above by finitely many cones
has zero underlying module if its negative-nilradical action span is the whole module.
The boundedness and diagonalizability are explicit; weight spaces may be infinite-dimensional.
Proof reconstructed using the existing partially well-ordered weight-support API. -/
theorem subsingleton_of_nNegActionSpan_eq_top (hV : IsHDiagonalizable P V)
    (hb : ∃ s : Finset (Dual K H), ∀ μ, weightSpace P V μ ≠ ⊥ →
      ∃ Λ ∈ s, μ ∈ cone P Λ)
    (hspan : nNegActionSpan P V = ⊤) : Subsingleton V := by
  classical
  by_contra hn
  let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hn
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ, weightSpace P V μ ≠ ⊥ := by
    by_contra! hz
    have ht : (⨆ μ, weightSpace P V μ) = ⊤ := hV
    simp only [hz, iSup_bot] at ht
    exact bot_ne_top ht
  let T : Set P.WeightOrd := {μ | weightSpace P V (WeightOrd.ofWeightOrd P μ) ≠ ⊥}
  have hT : T.IsPWO := by
    apply (WeightOrd.isPWO_iff P).mpr
    obtain ⟨s, hs⟩ := hb
    exact ⟨s, fun μ hμ ↦ hs _ hμ⟩
  obtain ⟨μ, -, hmin⟩ := hT.exists_le_minimal
    (show WeightOrd.toWeightOrd P μ₀ ∈ T from hμ₀)
  have habove : ∀ i, weightSpace P V (WeightOrd.ofWeightOrd P μ + P.root i) = ⊥ := by
    intro i
    by_contra hi
    let ν := WeightOrd.toWeightOrd P (WeightOrd.ofWeightOrd P μ + P.root i)
    have hν : ν ≤ μ := by
      refine ⟨Pi.single i 1, Pi.single_nonneg.mpr zero_le_one, ?_⟩
      simp only [ν, WeightOrd.ofWeightOrd_toWeightOrd, add_sub_cancel_left, rootOf_single]
    have heq : ν = μ := le_antisymm hν (hmin.2 hi hν)
    have hr : P.root i = 0 := by
      have := congrArg (WeightOrd.ofWeightOrd P) heq
      simpa only [ν, WeightOrd.ofWeightOrd_toWeightOrd, add_eq_left] using this
    have hs : (Pi.single i (1 : ℤ) : ι → ℤ) = 0 :=
      P.rootOf_injective (by rw [rootOf_single, hr, map_zero])
    have := congr_fun hs i
    simp at this
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmin.1
  exact hv0 (Submodule.disjoint_def.mp
    (disjoint_weightSpace_nNegActionSpan hV _ habove) v hv (hspan ▸ Submodule.mem_top))

/-- Actual coinvariant vanishing implies vanishing of a module in category `𝒪`.
This does not assert that any proposed syzygy map surjects on coinvariants. -/
theorem subsingleton_of_coinvariants (hV : IsCategoryO P V)
    [Subsingleton (V ⧸ nNegActionSpan P V)] : Subsingleton V := by
  apply subsingleton_of_nNegActionSpan_eq_top hV.iSup_weightSpaceOfMap_eq_top hV.exists_finset
  apply top_unique
  intro v _
  exact (Submodule.Quotient.mk_eq_zero _).mp
    (Subsingleton.elim (Submodule.Quotient.mk v) 0)

variable {U : Type*} [AddCommGroup U] [Module K U]
  [LieRingModule P.KacMoodyAlgebra U] [LieModule K P.KacMoodyAlgebra U]

/-- The actual map on negative-nilradical coinvariants induced by a Lie-module map. -/
def coinvariantsMap (φ : U →ₗ⁅K,P.KacMoodyAlgebra⁆ V) :
    (U ⧸ nNegActionSpan P U) →ₗ[K] (V ⧸ nNegActionSpan P V) :=
  (nNegActionSpan P U).mapQ (nNegActionSpan P V) φ.toLinearMap
    (fun _ hu ↦ map_mem_nNegActionSpan P φ hu)

/-- Surjectivity on actual coinvariants lifts to surjectivity of a genuine module map
with category-`𝒪` target. The source need not be in category `𝒪`. The proof applies
bounded-weight Nakayama to the genuine cokernel; it assumes neither surjectivity of
`φ` nor exactness of a complex. Argument reconstructed from the quotient definitions. -/
theorem surjective_of_coinvariantsMap (hV : IsCategoryO P V)
    (φ : U →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective (coinvariantsMap φ)) :
    Function.Surjective φ := by
  let q := LieSubmodule.Quotient.mk' φ.range
  have ht : nNegActionSpan P (V ⧸ φ.range) = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨v, rfl⟩ := LieSubmodule.Quotient.surjective_mk' φ.range z
    obtain ⟨u, hu⟩ := hφ (Submodule.Quotient.mk v)
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have hdiff : φ u - v ∈ nNegActionSpan P V :=
      (Submodule.Quotient.eq _).mp hu
    have hq := map_mem_nNegActionSpan P q hdiff
    have hzero : q (φ u) = 0 :=
      (LieSubmodule.Quotient.mk_eq_zero _).mpr ⟨u, rfl⟩
    rw [map_sub, hzero, zero_sub] at hq
    exact neg_mem_iff.mp hq
  have hQ := hV.quotient φ.range
  let : Subsingleton (V ⧸ φ.range) := subsingleton_of_nNegActionSpan_eq_top
    hQ.iSup_weightSpaceOfMap_eq_top hQ.exists_finset ht
  intro v
  exact (LieSubmodule.Quotient.mk_eq_zero φ.range).mp (Subsingleton.elim (q v) 0)

end Matrix.Realization.KacMoodyAlgebra.BGGMinimality
