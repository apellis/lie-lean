/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Data.List.Count
import Mathlib.Data.Set.Finite.List
import LieLean.Algebra.Lie.KacMoody.RootSpace
import LieLean.Algebra.Lie.Subalgebra

/-!
# Root spaces of `𝔤̃(A)`: spanning sets, finite-dimensionality, simple roots

For `α ∈ Q₊ \ {0}`, the root space `𝔤̃_α` is spanned by the iterated brackets
`[e_{i₁}, [e_{i₂}, ⋯ [e_{iₖ}, e_j] ⋯]]` with `α_{i₁} + ⋯ + α_{iₖ} + α_j = α` ([Kac] Thm. 1.2 (b),
(d) and its proof).

## Main definitions

* `Matrix.Realization.AuxLieAlgebra.posSpan`: the span of the iterated brackets
  `[e_{i₁}, [⋯ [e_{iₖ}, e_j] ⋯]]` of weight `μ`.

## Main results

* `Matrix.Realization.AuxLieAlgebra.rootSpace_le_posSpan`: `𝔤̃_α` is spanned by iterated brackets
  of weight `α`.
* `Matrix.Realization.AuxLieAlgebra.finiteDimensional_rootSpace`: `dim 𝔤̃_α < ∞` for `α ≠ 0`.
* `Matrix.Realization.AuxLieAlgebra.rootSpace_nsmul_root_eq_bot`: `𝔤̃_{k αᵢ} = 0` for `k ≥ 2`.
* `Matrix.Realization.AuxLieAlgebra.rootSpace_root`: `𝔤̃_{αᵢ} = K eᵢ`.
* Negative versions via the Chevalley involution.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Thm. 1.2, (1.3.3)
  (stated over `ℂ`).
-/

open FreeLieAlgebra Module LieModule LieAlgebra

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

namespace AuxLieAlgebra

/-- The letter counts of a word, as an element of the root lattice. -/
def counts (w : List ι) : ι → ℤ := fun i ↦ (w.count i : ℤ)

omit [Fintype ι] in
@[simp] lemma counts_nil : counts ([] : List ι) = 0 := by ext; simp [counts]

omit [Fintype ι] in
@[simp] lemma counts_cons (j : ι) (w : List ι) : counts (j :: w) = Pi.single j 1 + counts w := by
  ext i
  simp only [counts, List.count_cons, Pi.add_apply, Pi.single_apply, beq_iff_eq]
  split_ifs <;> subst_vars <;> simp_all; ring

lemma wordWt_eq_rootOf (w : List ι) : wordWt P w = P.rootOf (counts w) := by
  induction w with
  | nil => simp
  | cons j w ih => simp [ih, map_add]

omit [Fintype ι] in
lemma sum_counts (w : List ι) [Fintype ι] : ∑ i, counts w i = w.length := by
  induction w with
  | nil => simp
  | cons j w ih => simp [Finset.sum_add_distrib, ih, Pi.single_apply]; ring

/-- The span of the iterated brackets `[e_{i₁}, [⋯ [e_{iₖ}, e_j] ⋯]]` of weight `μ`. -/
def posSpan (μ : Dual K H) : Submodule K P.AuxLieAlgebra :=
  Submodule.span K {x | ∃ (j : ι) (l : List ι), wordWt P (j :: l) = μ ∧
    x = adProd (l.map (e P)) (e P j)}

lemma adProd_mem_rootSpace (j : ι) (l : List ι) :
    adProd (l.map (e P)) (e P j) ∈ rootSpace P (wordWt P (j :: l)) := by
  induction l with
  | nil => simpa using e_mem_rootSpace P j
  | cons i l ih =>
    rw [List.map_cons, adProd_cons]
    have := lie_mem_rootSpace P (e_mem_rootSpace P i) ih
    convert this using 2
    simp only [wordWt_cons]
    abel

lemma posSpan_le (μ : Dual K H) : posSpan P μ ≤ rootSpace P μ := by
  rw [posSpan, Submodule.span_le]
  rintro _ ⟨j, l, rfl, rfl⟩
  exact adProd_mem_rootSpace P j l

lemma eHom_mem_lieSpan (z : FreeLieAlgebra K ι) :
    eHom P z ∈ LieSubalgebra.lieSpan K P.AuxLieAlgebra (Set.range (e P)) := by
  induction z using FreeLieAlgebra.induction_on with
  | of i => exact LieSubalgebra.subset_lieSpan ⟨i, (eHom_of P i).symm⟩
  | zero => simp
  | add y z hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y hy => rw [map_smul]; exact LieSubalgebra.smul_mem _ c hy
  | lie y z hy hz => rw [LieHom.map_lie]; exact LieSubalgebra.lie_mem _ hy hz

omit [Fintype ι] [DecidableEq ι] in
lemma _root_.List.exists_map_eq_of_forall_mem_range {α β : Type*} {f : α → β} {l : List β}
    (hl : ∀ y ∈ l, y ∈ Set.range f) : ∃ l' : List α, l'.map f = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons y l ih =>
    obtain ⟨a, rfl⟩ := hl y (List.mem_cons_self ..)
    obtain ⟨l', rfl⟩ := ih fun z hz ↦ hl z (List.mem_cons_of_mem _ hz)
    exact ⟨a :: l', rfl⟩

lemma eHom_mem_iSup_posSpan (z : FreeLieAlgebra K ι) : eHom P z ∈ ⨆ μ, posSpan P μ := by
  have hz : eHom P z ∈ (LieSubalgebra.lieSpan K P.AuxLieAlgebra (Set.range (e P))).toSubmodule :=
    eHom_mem_lieSpan P z
  rw [LieSubalgebra.lieSpan_toSubmodule_eq_span_adProd] at hz
  refine (Submodule.span_le.mpr ?_) hz
  rintro _ ⟨l, hl, _, ⟨j, rfl⟩, rfl⟩
  obtain ⟨l', rfl⟩ := List.exists_map_eq_of_forall_mem_range hl
  exact Submodule.mem_iSup_of_mem (wordWt P (j :: l'))
    (Submodule.subset_span ⟨j, l', rfl, rfl⟩)

variable [CharZero K]

/-- For `α ∈ Q₊ \ {0}`, the root space `𝔤̃_α` is spanned by the iterated brackets
`[e_{i₁}, [⋯ [e_{iₖ}, e_j] ⋯]]` of weight `α`. -/
theorem rootSpace_le_posSpan {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    rootSpace P μ ≤ posSpan P μ := by
  intro x hx
  obtain ⟨z, rfl⟩ : ∃ z, eHom P z = x := rootSpace_pos_le P hμ hx
  exact mem_of_mem_iSup_of_le (h P) (posSpan P) (posSpan_le P) hx (eHom_mem_iSup_posSpan P z)

omit [DecidableEq ι] in
lemma finite_setOf_wordWt_eq (k : ι → ℤ) :
    {w : ι × List ι | wordWt P (w.1 :: w.2) = P.rootOf k}.Finite := by
  classical
  refine (Set.finite_univ.prod (List.finite_length_eq ι ((∑ i, k i).toNat - 1))).subset ?_
  rintro ⟨j, l⟩ hw
  simp only [Set.mem_ofPred_eq, wordWt_eq_rootOf, P.rootOf_injective.eq_iff] at hw
  have := sum_counts (j :: l)
  rw [hw] at this
  simp only [Set.mem_prod, Set.mem_univ, Set.mem_ofPred_eq, true_and]
  simp only [List.length_cons] at this
  omega

/-- The root spaces `𝔤̃_α`, `α ∈ Q₊ \ {0}`, are finite-dimensional ([Kac] Thm. 1.2 (d)). -/
theorem finiteDimensional_rootSpace {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    FiniteDimensional K (rootSpace P μ) := by
  obtain ⟨k, hk, rfl⟩ := hμ
  have hfin : (posSpan P (P.rootOf k) : Submodule K P.AuxLieAlgebra).FG := by
    rw [posSpan]
    refine Submodule.fg_def.mpr ⟨_, ((finite_setOf_wordWt_eq P k).image
      fun w ↦ adProd (w.2.map (e P)) (e P w.1)), ?_⟩
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Prod.exists]
    constructor
    · rintro ⟨j, l, h, rfl⟩; exact ⟨j, l, h, rfl⟩
    · rintro ⟨j, l, h, rfl⟩; exact ⟨j, l, h, rfl⟩
  have : FiniteDimensional K (posSpan P (P.rootOf k)) :=
    Module.Finite.iff_fg.mpr hfin
  exact Submodule.finiteDimensional_of_le (rootSpace_le_posSpan P ⟨k, hk, rfl⟩)

omit [Fintype ι] [DecidableEq ι] in
lemma adProd_replicate_self {L : Type*} [LieRing L] (x : L) (m : ℕ) :
    adProd (List.replicate (m + 1) x) x = 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, adProd_cons, ih, lie_zero]

omit [Fintype ι] in
lemma eq_replicate_of_counts_eq {j : ι} {l : List ι} {i : ι} {n : ℕ}
    (h : counts (j :: l) = n • Pi.single i 1) : j = i ∧ l = List.replicate (n - 1) i := by
  have hmem : ∀ b ∈ j :: l, b = i := by
    intro b hb
    by_contra hbi
    have := congr_fun h b
    simp only [counts, Pi.smul_apply, Pi.single_apply, hbi, ite_false, smul_zero,
      Nat.cast_eq_zero, List.count_eq_zero] at this
    exact this hb
  have hlen := congr_fun h i
  simp only [counts, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one] at hlen
  rw [List.count_eq_length.mpr fun b hb ↦ (hmem b hb).symm] at hlen
  refine ⟨hmem j (List.mem_cons_self ..), List.eq_replicate_iff.mpr ⟨?_, fun b hb ↦
    hmem b (List.mem_cons_of_mem _ hb)⟩⟩
  simp only [List.length_cons] at hlen
  omega

/-- `𝔤̃_{k αᵢ} = 0` for `k ≥ 2` ([Kac] (1.3.3), stated there for `𝔤(A)`; the same
argument applies to `𝔤̃(A)`). -/
theorem rootSpace_nsmul_root_eq_bot (i : ι) {n : ℕ} (hn : 2 ≤ n) :
    rootSpace P (n • P.root i) = ⊥ := by
  have hw : n • P.root i = P.rootOf (n • Pi.single i 1) := by rw [map_nsmul, rootOf_single]
  have hpos : n • P.root i ∈ P.posWeights := by
    refine ⟨n • Pi.single i 1, ⟨fun m ↦ ?_, fun h ↦ ?_⟩, hw.symm⟩
    · by_cases hm : m = i
      · subst hm; simp
      · simp [hm]
    · have := congr_fun h i; simp at this; omega
  refine eq_bot_iff.mpr ((rootSpace_le_posSpan P hpos).trans ?_)
  rw [posSpan, Submodule.span_le]
  rintro _ ⟨j, l, hjl, rfl⟩
  rw [hw, wordWt_eq_rootOf, P.rootOf_injective.eq_iff] at hjl
  obtain ⟨rfl, rfl⟩ := eq_replicate_of_counts_eq hjl
  obtain ⟨m, hm⟩ : ∃ m, n - 1 = m + 1 := ⟨n - 2, by omega⟩
  rw [hm, List.map_replicate, adProd_replicate_self]
  exact Submodule.zero_mem _

omit [CharZero K] in
lemma e_ne_zero (i : ι) : e P i ≠ 0 := by
  intro h
  have : FreeLieAlgebra.toFreeAlgebra K ι (FreeLieAlgebra.of K i) = 0 := by
    rw [← tensorRep_fHom_one P 0, fHom_of]
    have hω := congr_arg (chevalleyInvolution P) h
    rw [chevalleyInvolution_e, map_zero, neg_eq_zero] at hω
    simp [hω]
  simp only [FreeLieAlgebra.toFreeAlgebra_of] at this
  exact FreeAlgebra.ι_ne_zero i this

/-- `𝔤̃_{αᵢ} = K eᵢ` ([Kac] (1.3.3), stated there for `𝔤(A)`; the same argument
applies to `𝔤̃(A)`). -/
theorem rootSpace_root (i : ι) : rootSpace P (P.root i) = K ∙ e P i := by
  refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr (e_mem_rootSpace P i))
  have hw : P.root i = P.rootOf (Pi.single i 1) := by simp
  have hpos : P.root i ∈ P.posWeights := P.root_mem_posWeights i
  refine (rootSpace_le_posSpan P hpos).trans ?_
  rw [posSpan, Submodule.span_le]
  rintro _ ⟨j, l, hjl, rfl⟩
  rw [hw, wordWt_eq_rootOf, P.rootOf_injective.eq_iff, ← one_nsmul (Pi.single i 1)] at hjl
  obtain ⟨rfl, rfl⟩ := eq_replicate_of_counts_eq hjl
  exact Submodule.mem_span_singleton_self _

/-! ### Negative root spaces -/

omit [CharZero K] in
lemma chevalleyInvolution_mem_rootSpace {μ : Dual K H} {x : P.AuxLieAlgebra}
    (hx : x ∈ rootSpace P μ) : chevalleyInvolution P x ∈ rootSpace P (-μ) := by
  intro a
  have := congr_arg (chevalleyInvolution P) (hx (-a))
  simp only [LieHom.map_lie, map_neg, chevalleyInvolution_h, neg_neg, map_smul] at this
  rw [this, LinearMap.neg_apply, neg_smul]

omit [CharZero K] in
/-- `𝔤̃_{-μ} = ω(𝔤̃_μ)`, where `ω` is the Chevalley involution. -/
lemma rootSpace_neg_eq_map (μ : Dual K H) :
    rootSpace P (-μ) = (rootSpace P μ).map (chevalleyInvolution P).toLinearMap := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · refine ⟨chevalleyInvolution P x, ?_, by simp⟩
    simpa using chevalleyInvolution_mem_rootSpace P hx
  · rintro _ ⟨x, hx, rfl⟩
    exact chevalleyInvolution_mem_rootSpace P hx

/-- The root spaces `𝔤̃_{-α}`, `α ∈ Q₊ \ {0}`, are finite-dimensional. -/
theorem finiteDimensional_rootSpace_neg {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    FiniteDimensional K (rootSpace P (-μ)) := by
  have := finiteDimensional_rootSpace P hμ
  rw [rootSpace_neg_eq_map]
  infer_instance

/-- `𝔤̃_{-k αᵢ} = 0` for `k ≥ 2`. -/
theorem rootSpace_neg_nsmul_root_eq_bot (i : ι) {n : ℕ} (hn : 2 ≤ n) :
    rootSpace P (-(n • P.root i)) = ⊥ := by
  rw [rootSpace_neg_eq_map, rootSpace_nsmul_root_eq_bot P i hn, Submodule.map_bot]

/-- `𝔤̃_{-αᵢ} = K fᵢ`. -/
theorem rootSpace_neg_root (i : ι) : rootSpace P (-P.root i) = K ∙ f P i := by
  rw [rootSpace_neg_eq_map, rootSpace_root, Submodule.map_span, Set.image_singleton,
    LieHom.coe_toLinearMap, chevalleyInvolution_e, ← Set.neg_singleton, Submodule.span_neg]

end AuxLieAlgebra

end Matrix.Realization

end
