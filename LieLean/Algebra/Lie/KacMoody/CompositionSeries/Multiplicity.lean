/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CompositionSeries

/-!
# Multiplicities of irreducible factors in the category `𝒪`

Let `V` be a module in the category `𝒪` over the Kac–Moody algebra `𝔤(A)`. For `μ ∈ 𝔥*`, the
multiplicity `[V : L(μ)]` is the number of factors `L(μ)` in a local composition series of `V`
for some `ν ≤ μ` ([Kac] Lemma 9.6); it does not depend on the local composition series
nor on `ν` ([Kac] §9.6).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.multiplicity`: the multiplicity `[V : L(μ)]`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.finrank_weightSpace_self`:
  `dim L(μ)_μ = 1`.
* `Matrix.Realization.KacMoodyAlgebra.IsLocalCompositionSeries.finrank_weightSpace_eq`: along a
  local composition series for `ν`, `dim V_ξ = ∑_{j ∈ J} dim L(λ_j)_ξ` for every `ξ ≥ ν`.
* `Matrix.Realization.KacMoodyAlgebra.eq_of_forall_sum_finrank_weightSpace_eq`: a multiset of
  weights `≥ ν` is determined by the numbers `∑_{λ ∈ s} dim L(λ)_ξ`, `ξ ≥ ν`.
* `Matrix.Realization.KacMoodyAlgebra.IsLocalCompositionSeries.count_factorWeights_eq`,
  `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.count_factorWeights_eq_multiplicity`: the
  number of factors `L(μ)` in a local composition series for `ν ≤ μ` is `[V : L(μ)]`, independently
  of the series and of `ν` ([Kac] §9.6).

## Proof

See the module docstring of
`LieLean/Algebra/Lie/KacMoody/CompositionSeries.lean`: along a local composition series for `ν`,
`dim V_ξ = ∑_{j ∈ J} dim L(λ_j)_ξ` for `ξ ≥ ν`; for `ξ ≥ μ ≥ ν` only the `λ_j ≥ μ` contribute, and
the multiset of these `λ_j` is determined by these dimensions, by induction on its size, removing
a maximal element (for which `dim L(λ)_λ = 1`). The argument is standard; we wrote it out
ourselves.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.6.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

open WeightOrd

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-! ### Weight spaces of `L(μ)` -/

namespace IrreducibleModule

variable (P) in
/-- `dim L(μ)_μ = 1` ([Kac] §9.3). -/
theorem finrank_weightSpace_self (μ : Dual K H) :
    finrank K (weightSpace P (IrreducibleModule P μ) μ) = 1 := by
  rw [weightSpace, ← map_weightSpaceOfMap_quotient P _
    (VermaModule.isCategoryO P μ).iSup_weightSpaceOfMap_eq_top μ,
    show weightSpaceOfMap (VermaModule P μ) (h P) μ = K ∙ VermaModule.hwv P μ from
      VermaModule.weightSpace_self P μ, Submodule.map_span, Set.image_singleton]
  exact finrank_span_singleton (hwv_ne_zero P μ)

omit [CharZero K] in
/-- The weights of `L(μ)` are `≤ μ` ([Kac] §9.2–9.3). -/
theorem mem_cone_of_weightSpace_ne_bot {μ ξ : Dual K H}
    (hξ : weightSpace P (IrreducibleModule P μ) ξ ≠ ⊥) : ξ ∈ cone P μ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hξ
  exact VermaModule.exists_eq_sub_of_mem_weightSpace P μ _
    (LieSubmodule.Quotient.surjective_mk' _) hx hx0

omit [CharZero K] in
lemma mem_cone_of_finrank_weightSpace_ne_zero {μ ξ : Dual K H}
    (hξ : finrank K (weightSpace P (IrreducibleModule P μ) ξ) ≠ 0) : ξ ∈ cone P μ :=
  mem_cone_of_weightSpace_ne_bot fun hbot ↦ hξ (by rw [hbot, finrank_bot])

end IrreducibleModule

/-! ### Dimensions of weight spaces along a local composition series -/

namespace IsLocalCompositionSeries

variable (hV : IsCategoryO P V) {ν ξ : Dual K H}
include hV

omit [CharZero K] in
/-- Along a local composition series for `ν` from `N` to `M`,
`dim (M ∩ V_ξ) = dim (N ∩ V_ξ) + ∑_{j ∈ J} dim L(λ_j)_ξ` for `ξ ≥ ν`. -/
theorem finrank_inf_weightSpace_eq (hξ : ν ∈ cone P ξ)
    {N M : LieSubmodule K P.KacMoodyAlgebra V}
    {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P ν N l M) :
    finrank K ↥(M.toSubmodule ⊓ weightSpace P V ξ) =
      finrank K ↥(N.toSubmodule ⊓ weightSpace P V ξ) +
        ((factorWeights l).map
          fun μ ↦ finrank K (weightSpace P (IrreducibleModule P μ) ξ)).sum := by
  induction l generalizing N with
  | nil =>
    rw [nil_iff.mp hl, factorWeights_nil, List.map_nil, List.sum_nil, add_zero]
  | cons a l ih =>
    obtain ⟨N', o⟩ := a
    obtain ⟨hNN', hf, hl'⟩ := cons_iff.mp hl
    rw [ih hl', finrank_inf_weightSpace_eq_add hV hNN' ξ]
    cases o with
    | none =>
      rw [hf ξ hξ, finrank_bot, add_zero, factorWeights_cons_none]
    | some μ =>
      obtain ⟨-, ⟨e⟩⟩ := hf
      rw [weightSpace, finrank_weightSpaceOfMap_equiv P e ξ, factorWeights_cons_some,
        List.map_cons, List.sum_cons, add_assoc]

omit [CharZero K] in
/-- Along a local composition series for `ν` from `0` to `V`, `dim V_ξ = ∑_{j ∈ J} dim L(λ_j)_ξ`
for every `ξ ≥ ν` (cf. [Kac] §9.6 and the proof of Prop. 9.7). -/
theorem finrank_weightSpace_eq (hξ : ν ∈ cone P ξ)
    {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P ν ⊥ l ⊤) :
    finrank K (weightSpace P V ξ) =
      ((factorWeights l).map fun μ ↦ finrank K (weightSpace P (IrreducibleModule P μ) ξ)).sum := by
  have := hl.finrank_inf_weightSpace_eq hV hξ
  rwa [LieSubmodule.top_toSubmodule, top_inf_eq, LieSubmodule.bot_toSubmodule, bot_inf_eq,
    finrank_bot, zero_add] at this

end IsLocalCompositionSeries

/-! ### Uniqueness of the multiplicities -/

/-- A finite multiset `s` of weights `≥ ν` is determined by the numbers
`∑_{λ ∈ s} dim L(λ)_ξ` for `ξ ≥ ν`. -/
theorem eq_of_forall_sum_finrank_weightSpace_eq {ν : Dual K H} {s s' : Multiset (Dual K H)}
    (hs : ∀ μ ∈ s, ν ∈ cone P μ) (hs' : ∀ μ ∈ s', ν ∈ cone P μ)
    (h : ∀ ξ, ν ∈ cone P ξ →
      (s.map fun μ ↦ finrank K (weightSpace P (IrreducibleModule P μ) ξ)).sum =
        (s'.map fun μ ↦ finrank K (weightSpace P (IrreducibleModule P μ) ξ)).sum) :
    s = s' := by
  classical
  suffices H : ∀ n, ∀ s s' : Multiset (Dual K H), Multiset.card (s + s') ≤ n →
      (∀ μ ∈ s + s', ν ∈ cone P μ) → (∀ ξ, ν ∈ cone P ξ →
        (s.map fun μ ↦ finrank K (weightSpace P (IrreducibleModule P μ) ξ)).sum =
          (s'.map fun μ ↦ finrank K (weightSpace P (IrreducibleModule P μ) ξ)).sum) → s = s' from
    H _ s s' le_rfl (fun μ hμ ↦ (Multiset.mem_add.mp hμ).elim (hs μ) (hs' μ)) h
  intro n
  induction n with
  | zero =>
    intro s s' hn _ _
    rw [Nat.le_zero, Multiset.card_eq_zero, add_eq_zero] at hn
    rw [hn.1, hn.2]
  | succ n ih =>
  intro s s' hn hss' h
  by_cases h0 : s + s' = 0
  · rw [add_eq_zero] at h0
    rw [h0.1, h0.2]
  -- a maximal element `μ` of `s + s'` for the dominance order
  set T : Set P.WeightOrd := toWeightOrd P '' ((s + s').toFinset : Set (Dual K H))
  have hTfin : T.Finite := (Finset.finite_toSet _).image _
  obtain ⟨μ₀, hμ₀⟩ := Multiset.exists_mem_of_ne_zero h0
  have hTne : T.Nonempty := ⟨_, μ₀, by simpa using hμ₀, rfl⟩
  obtain ⟨_, ⟨μ, hμT, rfl⟩, hmin⟩ := hTfin.exists_minimal hTne
  have hμ : μ ∈ s + s' := by simpa using hμT
  have key (μ' : Dual K H) (hμ' : μ' ∈ s + s')
      (hne : finrank K (weightSpace P (IrreducibleModule P μ') μ) ≠ 0) : μ' = μ := by
    have hle : toWeightOrd P μ' ≤ toWeightOrd P μ :=
      (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr
        (IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero hne)
    exact (toWeightOrd P).injective (le_antisymm hle (hmin ⟨μ', by simpa using hμ', rfl⟩ hle))
  have hcount (t : Multiset (Dual K H)) (ht : t ≤ s + s') :
      (t.map fun μ' ↦ finrank K (weightSpace P (IrreducibleModule P μ') μ)).sum = t.count μ := by
    rw [Multiset.sum_map_eq_nsmul_single μ fun μ' hne hmem ↦ ?_,
      IrreducibleModule.finrank_weightSpace_self, smul_eq_mul, mul_one]
    by_contra h0
    exact hne (key μ' (Multiset.mem_of_le ht hmem) h0)
  have hc : s.count μ = s'.count μ := by
    rw [← hcount s (Multiset.le_add_right _ _), ← hcount s' (Multiset.le_add_left _ _)]
    exact h μ (hss' μ hμ)
  have hμs : μ ∈ s ∧ μ ∈ s' := by
    have := Multiset.count_pos.mpr hμ
    rw [Multiset.count_add] at this
    exact ⟨Multiset.count_pos.mp (by omega), Multiset.count_pos.mp (by omega)⟩
  rw [← Multiset.cons_erase hμs.1, ← Multiset.cons_erase hμs.2]
  congr 1
  refine ih _ _ ?_ (fun μ' hμ' ↦ ?_) fun ξ hξ ↦ ?_
  · have h1 := Multiset.card_erase_of_mem hμs.1
    have h2 := Multiset.card_erase_of_mem hμs.2
    have h3 := Multiset.card_pos_iff_exists_mem.mpr ⟨_, hμs.1⟩
    have h4 := Multiset.card_pos_iff_exists_mem.mpr ⟨_, hμs.2⟩
    rw [Multiset.card_add] at hn
    rw [Multiset.card_add, h1, h2, Nat.pred_eq_sub_one, Nat.pred_eq_sub_one]
    omega
  · rcases Multiset.mem_add.mp hμ' with hμ' | hμ'
    · exact hss' μ' (Multiset.mem_add.mpr (.inl (Multiset.mem_of_mem_erase hμ')))
    · exact hss' μ' (Multiset.mem_add.mpr (.inr (Multiset.mem_of_mem_erase hμ')))
  · have := h ξ hξ
    rw [← Multiset.cons_erase hμs.1, ← Multiset.cons_erase hμs.2, Multiset.map_cons,
      Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons] at this
    exact add_left_cancel this

omit [CharZero K] in
/-- For `μ ≤ ξ`, the weights `λ` in a multiset `t` with `μ ≰ λ` do not contribute to
`∑_{λ ∈ t} dim L(λ)_ξ`. -/
lemma sum_map_finrank_weightSpace_filter {μ ξ : Dual K H}
    [DecidablePred fun μ' : Dual K H ↦ μ ∈ cone P μ'] (hξ : μ ∈ cone P ξ)
    (t : Multiset (Dual K H)) :
    ((t.filter fun μ' ↦ μ ∈ cone P μ').map
      fun μ' ↦ finrank K (weightSpace P (IrreducibleModule P μ') ξ)).sum =
      (t.map fun μ' ↦ finrank K (weightSpace P (IrreducibleModule P μ') ξ)).sum := by
  conv_rhs => rw [← Multiset.filter_add_not (fun μ' ↦ μ ∈ cone P μ') t]
  rw [Multiset.map_add, Multiset.sum_add, left_eq_add]
  refine Multiset.sum_eq_zero fun d hd ↦ ?_
  obtain ⟨μ', hμ', rfl⟩ := Multiset.mem_map.mp hd
  by_contra hne
  exact (Multiset.mem_filter.mp hμ').2
    (mem_cone_trans hξ (IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero hne))

/-- **Independence of the multiplicities** ([Kac] §9.6): the number of factors `L(μ)` in
a local composition series of `V` for `ν ≤ μ` does not depend on the series nor on `ν`. -/
theorem IsLocalCompositionSeries.count_factorWeights_eq [DecidableEq (Dual K H)]
    (hV : IsCategoryO P V) {ν ν' μ : Dual K H} (hν : ν ∈ cone P μ) (hν' : ν' ∈ cone P μ)
    {l l' : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P ν ⊥ l ⊤) (hl' : IsLocalCompositionSeries P ν' ⊥ l' ⊤) :
    (factorWeights l).count μ = (factorWeights l').count μ := by
  classical
  have hsum {ν : Dual K H} (hν : ν ∈ cone P μ)
      {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
      (hl : IsLocalCompositionSeries P ν ⊥ l ⊤) (ξ : Dual K H) (hξ : μ ∈ cone P ξ) :
      (((factorWeights l : Multiset (Dual K H)).filter fun μ' ↦ μ ∈ cone P μ').map
        fun μ' ↦ finrank K (weightSpace P (IrreducibleModule P μ') ξ)).sum =
        finrank K (weightSpace P V ξ) := by
    rw [sum_map_finrank_weightSpace_filter hξ, hl.finrank_weightSpace_eq hV (mem_cone_trans hν hξ),
      Multiset.map_coe, Multiset.sum_coe]
  have heq := eq_of_forall_sum_finrank_weightSpace_eq
    (fun μ' hμ' ↦ (Multiset.mem_filter.mp hμ').2) (fun μ' hμ' ↦ (Multiset.mem_filter.mp hμ').2)
    fun ξ hξ ↦ (hsum hν hl ξ hξ).trans (hsum hν' hl' ξ hξ).symm
  have hc := congrArg (Multiset.count μ) heq
  rwa [Multiset.count_filter_of_pos (p := fun μ' ↦ μ ∈ cone P μ') (mem_cone_self μ),
    Multiset.count_filter_of_pos (p := fun μ' ↦ μ ∈ cone P μ') (mem_cone_self μ),
    Multiset.coe_count, Multiset.coe_count] at hc

namespace IsCategoryO

open scoped Classical in
/-- The multiplicity `[V : L(μ)]` of `L(μ)` in a module `V` in the category `𝒪`: the number of
factors isomorphic to `L(μ)` in a local composition series of `V` for `μ` ([Kac] §9.6).
By `IsCategoryO.count_factorWeights_eq_multiplicity`, any local composition series for any
`ν ≤ μ` gives the same number. -/
def multiplicity (hV : IsCategoryO P V) (μ : Dual K H) : ℕ :=
  (factorWeights (hV.exists_isLocalCompositionSeries μ).choose).count μ

/-- The multiplicity `[V : L(μ)]` is the number of factors `L(μ)` in any local composition series
of `V` for any `ν ≤ μ` ([Kac] §9.6). -/
theorem count_factorWeights_eq_multiplicity [DecidableEq (Dual K H)] (hV : IsCategoryO P V)
    {ν μ : Dual K H} (hν : ν ∈ cone P μ)
    {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P ν ⊥ l ⊤) :
    (factorWeights l).count μ = hV.multiplicity μ := by
  rw [multiplicity, hl.count_factorWeights_eq hV hν (mem_cone_self μ)
    (hV.exists_isLocalCompositionSeries μ).choose_spec]
  convert rfl

/-- `[V : L(μ)] ≠ 0` iff `L(μ)` occurs in some (equivalently, any) local composition series of
`V` for some (equivalently, any) `ν ≤ μ`. -/
theorem multiplicity_ne_zero_iff (hV : IsCategoryO P V) {ν μ : Dual K H} (hν : ν ∈ cone P μ)
    {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P ν ⊥ l ⊤) :
    hV.multiplicity μ ≠ 0 ↔ μ ∈ factorWeights l := by
  classical
  rw [← hV.count_factorWeights_eq_multiplicity hν hl, ne_eq, List.count_eq_zero, not_not]

end IsCategoryO

end Matrix.Realization.KacMoodyAlgebra
