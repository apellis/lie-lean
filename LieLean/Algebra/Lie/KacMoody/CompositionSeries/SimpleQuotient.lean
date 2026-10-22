/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterFormula
import LieLean.Algebra.Lie.KacMoody.TranslationMultiplicity

/-!
# Simple quotients of modules in `𝒪`

Facts about the simple quotients `L(λ)` of a module `V` in `𝒪` of finite length, used in the proof
of [HumO] Theorem 6.13.

## Main results

* `IsCategoryO.multiplicity_ne_zero_of_lieModuleHom`: a nonzero morphism `V → L(λ)` is
  surjective, so `[V : L(λ)] ≠ 0`.
* `IsLocalCompositionSeries.length_factorWeights_add_le`: a local composition series from `N` to
  `M` has at most `f M - f N` irreducible factors, for any strictly monotone `f : Sub(V) → ℕ`.
* `IsCategoryO.exists_minimal_of_multiplicity_ne_zero`: if `V` has finite length, every nonempty
  set of weights `λ` with `[V : L(λ)] ≠ 0` has a minimal element. Humphreys uses this for the set
  of `λ` with `Hom(V, L(λ)) ≠ 0`, which he notes is finite.
* `IsCategoryO.exists_subquotient_equiv_of_ne_bot`: if the submodules of `V` satisfy the ascending
  chain condition, every nonzero submodule `M` has a simple quotient `M / M' ≅ L(ν)`, and
  `[V : L(ν)] ≠ 0`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §6.13.
-/

noncomputable section

open Module LieModule

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

local notation "𝔤" => KacMoodyAlgebra P

omit [CharZero K] in
/-- The subquotient `N / N` is zero. -/
lemma subsingleton_subquotient_self (N : LieSubmodule K 𝔤 V) : Subsingleton (N.Subquotient N) :=
  ⟨fun a b ↦ by
    obtain ⟨a, rfl⟩ := LieSubmodule.Quotient.surjective_mk' (N.comap N.incl) a
    obtain ⟨b, rfl⟩ := LieSubmodule.Quotient.surjective_mk' (N.comap N.incl) b
    rw [(LieSubmodule.Quotient.mk_eq_zero (N := N.comap N.incl)).mpr
        (LieSubmodule.mem_comap.mpr a.2),
      (LieSubmodule.Quotient.mk_eq_zero (N := N.comap N.incl)).mpr
        (LieSubmodule.mem_comap.mpr b.2)]⟩

namespace IsLocalCompositionSeries

/-- A local composition series from `N` to `M` has at most `f M - f N` irreducible factors, for a
strictly monotone `f`: the steps with an irreducible factor are strict inclusions. -/
theorem length_factorWeights_add_le {ν : Dual K H} {f : LieSubmodule K 𝔤 V → ℕ}
    (hf : StrictMono f) {N M : LieSubmodule K 𝔤 V}
    {l : List (LieSubmodule K 𝔤 V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P ν N l M) : (factorWeights l).length + f N ≤ f M := by
  induction l generalizing N with
  | nil =>
    rw [← IsLocalCompositionSeries.nil_iff.mp hl]
    simp
  | cons a l ih =>
    obtain ⟨N', o⟩ := a
    obtain ⟨hle, hf', hl'⟩ := IsLocalCompositionSeries.cons_iff.mp hl
    have h := ih hl'
    cases o with
    | none =>
      have := hf.monotone hle
      simp only [factorWeights_cons_none]
      omega
    | some μ =>
      have hlt : N < N' := lt_of_le_of_ne hle fun hNN ↦ by
        subst hNN
        obtain ⟨-, ⟨ψ⟩⟩ := hf'
        have := subsingleton_subquotient_self N
        obtain ⟨x, y, hxy⟩ := exists_pair_ne (IrreducibleModule P μ)
        exact hxy (ψ.symm.injective (Subsingleton.elim _ _))
      have := hf hlt
      simp only [factorWeights_cons_some, List.length_cons]
      omega

end IsLocalCompositionSeries

namespace IsCategoryO

variable (hV : IsCategoryO P V)
include hV

/-- A nonzero morphism `V → L(λ)` is surjective, so `[V : L(λ)] ≠ 0`. -/
theorem multiplicity_ne_zero_of_lieModuleHom {lam : Dual K H}
    (φ : V →ₗ⁅K,𝔤⁆ IrreducibleModule P lam) (hφ : φ ≠ 0) : hV.multiplicity lam ≠ 0 := by
  have := IrreducibleModule.isIrreducible P lam
  have hs : Function.Surjective φ := by
    rw [← LieModuleHom.range_eq_top]
    refine (IsSimpleOrder.eq_bot_or_eq_top φ.range).resolve_left fun h0 ↦ hφ ?_
    ext y
    have : φ y ∈ φ.range := (LieModuleHom.mem_range _ _).mpr ⟨y, rfl⟩
    rw [h0, LieSubmodule.mem_bot] at this
    exact this
  have h := IsCategoryO.multiplicity_eq_add_of_exact (hV.lieSubmodule φ.ker) hV
    (IrreducibleModule.isCategoryO P lam) φ.ker.incl φ Subtype.val_injective
    φ.ker.range_incl.symm hs lam
  have h1 : (IrreducibleModule.isCategoryO P lam).multiplicity lam = 1 := by
    rw [IrreducibleModule.multiplicity_eq]
    simp
  omega

/-- If `V` has finite length (a strictly monotone `f : Sub(V) → ℕ`), every nonempty set `S` of
weights `λ` with `[V : L(λ)] ≠ 0` has a minimal element. The number of `κ ≥ μ` with
`[V : L(κ)] ≠ 0` is at most `f ⊤` and strictly increases as `μ` decreases in `S`. -/
theorem exists_minimal_of_multiplicity_ne_zero {f : LieSubmodule K 𝔤 V → ℕ} (hf : StrictMono f)
    {S : Set (Dual K H)} (hS : ∀ μ ∈ S, hV.multiplicity μ ≠ 0) (hne : S.Nonempty) :
    ∃ lam ∈ S, ∀ ν ∈ S, ν ∈ cone P lam → ν = lam := by
  classical
  let l : Dual K H → List (LieSubmodule K 𝔤 V × Option (Dual K H)) := fun μ ↦
    (hV.exists_isLocalCompositionSeries μ).choose
  have hl (μ : Dual K H) : IsLocalCompositionSeries P μ ⊥ (l μ) ⊤ :=
    (hV.exists_isLocalCompositionSeries μ).choose_spec
  let T : Dual K H → Finset (Dual K H) := fun μ ↦ (factorWeights (l μ)).toFinset
  have hT (μ κ : Dual K H) : κ ∈ T μ ↔ hV.multiplicity κ ≠ 0 ∧ μ ∈ cone P κ := by
    simp only [T, List.mem_toFinset]
    constructor
    · intro h
      have hc := (hl μ).mem_cone_of_mem_factorWeights h
      exact ⟨(hV.multiplicity_ne_zero_iff hc (hl μ)).mpr h, hc⟩
    · rintro ⟨hm, hc⟩
      exact (hV.multiplicity_ne_zero_iff hc (hl μ)).mp hm
  have hTle (μ : Dual K H) : (T μ).card ≤ f ⊤ := by
    have h1 := List.toFinset_card_le (factorWeights (l μ))
    have h2 := (hl μ).length_factorWeights_add_le hf
    simp only [T]
    omega
  have hTlt {μ ν : Dual K H} (hν : ν ∈ S) (hνμ : ν ∈ cone P μ) (hne : ν ≠ μ) :
      (T μ).card < (T ν).card := by
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun κ hκ ↦ ?_).mpr
      ⟨ν, (hT ν ν).mpr ⟨hS ν hν, mem_cone_self ν⟩, fun h ↦ hne ?_⟩)
    · obtain ⟨hm, hc⟩ := (hT μ κ).mp hκ
      exact (hT ν κ).mpr ⟨hm, mem_cone_trans hνμ hc⟩
    · exact eq_of_mem_cone_of_mem_cone hνμ ((hT μ ν).mp h).2
  suffices H : ∀ d, ∀ μ ∈ S, f ⊤ - (T μ).card = d → ∃ lam ∈ S, ∀ ν ∈ S, ν ∈ cone P lam → ν = lam by
    obtain ⟨μ, hμ⟩ := hne
    exact H _ μ hμ rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro μ hμ hd
  by_cases hmin : ∀ ν ∈ S, ν ∈ cone P μ → ν = μ
  · exact ⟨μ, hμ, hmin⟩
  push Not at hmin
  obtain ⟨ν, hν, hνμ, hne⟩ := hmin
  have h1 := hTlt hν hνμ hne
  have h2 := hTle ν
  exact ih _ (by omega) ν hν rfl

/-- If the submodules of `V` satisfy the ascending chain condition, every nonzero submodule `M`
has a simple quotient: there is `M' < M` with `M / M' ≅ L(ν)`, and then `[V : L(ν)] ≠ 0`. -/
theorem exists_subquotient_equiv_of_ne_bot [WellFoundedGT (LieSubmodule K 𝔤 V)]
    {M : LieSubmodule K 𝔤 V} (hM : M ≠ ⊥) :
    ∃ M' : LieSubmodule K 𝔤 V, M' < M ∧ ∃ ν : Dual K H, hV.multiplicity ν ≠ 0 ∧
      Nonempty (M'.Subquotient M ≃ₗ⁅K,𝔤⁆ IrreducibleModule P ν) := by
  -- a maximal submodule `M'` of `M`
  obtain ⟨M', hM'M : M' < M, hmax⟩ := (wellFounded_gt (α := LieSubmodule K 𝔤 V)).has_min
    {N | N < M} ⟨⊥, bot_lt_iff_ne_bot.mpr hM⟩
  have hmax' (N : LieSubmodule K 𝔤 V) (h₁ : M' ≤ N) (h₂ : N < M) : N = M' :=
    (eq_or_lt_of_le h₁).elim Eq.symm fun h ↦ absurd h (hmax N h₂)
  -- a weight `μ` of `M / M'`
  have hQ : IsCategoryO P (M'.Subquotient M) := (hV.lieSubmodule M).quotient _
  obtain ⟨m, hmM, hmM'⟩ := SetLike.exists_of_lt hM'M
  have hq0 : LieSubmodule.Quotient.mk' (M'.comap M.incl) ⟨m, hmM⟩ ≠ 0 := fun h ↦
    hmM' ((LieSubmodule.Quotient.mk_eq_zero (N := M'.comap M.incl)).mp h)
  obtain ⟨μ, hμ⟩ : ∃ μ, weightSpace P (M'.Subquotient M) μ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have htop : (⊤ : Submodule K (M'.Subquotient M)) = ⊥ := by
      rw [← hQ.iSup_weightSpaceOfMap_eq_top]
      exact iSup_eq_bot.mpr hcon
    have hmem : LieSubmodule.Quotient.mk' (M'.comap M.incl) ⟨m, hmM⟩ ∈
        (⊤ : Submodule K (M'.Subquotient M)) := Submodule.mem_top
    rw [htop, Submodule.mem_bot] at hmem
    exact hq0 hmem
  have hμ' : ¬ M.toSubmodule ⊓ weightSpace P V μ ≤ M'.toSubmodule := fun h ↦
    hμ ((hV.weightSpace_subquotient_eq_bot_iff M' M μ).mpr h)
  obtain ⟨M₁, M₂, ν, h₁, h₁₂, h₂, hlt, hfac⟩ :=
    hV.exists_isLocalFactor_some hM'M.le (mem_cone_self μ) hμ'
  have hne : M₁ ≠ M₂ := by
    rintro rfl
    exact lt_irrefl _ hlt
  have hM₁ : M₁ = M' := hmax' M₁ h₁ ((lt_of_le_of_ne h₁₂ hne).trans_le h₂)
  have hM₂ : M₂ = M := by
    by_contra h
    exact hne (hM₁.trans (hmax' M₂ (h₁.trans h₁₂) (lt_of_le_of_ne h₂ h)).symm)
  subst hM₁ hM₂
  obtain ⟨hμν, hψ⟩ := hfac
  refine ⟨M₁, hM'M, ν, ?_, hψ⟩
  -- `L(ν)` occurs in a local composition series through `M₁ ⊆ M₂`
  obtain ⟨l₁, hl₁⟩ := hV.exists_isLocalCompositionSeries_of_le μ (bot_le : ⊥ ≤ M₁)
  obtain ⟨l₂, hl₂⟩ := hV.exists_isLocalCompositionSeries_of_le μ (le_top : M₂ ≤ ⊤)
  have hl := hl₁.append (IsLocalCompositionSeries.cons_iff.mpr ⟨h₁₂, ⟨hμν, hψ⟩, hl₂⟩)
  refine (hV.multiplicity_ne_zero_iff hμν hl).mpr ?_
  simp [factorWeights, List.filterMap_append]

end IsCategoryO

end Matrix.Realization.KacMoodyAlgebra
