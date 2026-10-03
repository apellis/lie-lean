/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CasimirIrreducible
import LieLean.Algebra.Lie.KacMoody.Character

/-!
# Local composition series in the category `𝒪`

Let `V` be a module over the Kac–Moody algebra `𝔤 = 𝔤(A)` in the category `𝒪`, and let
`λ ∈ 𝔥*`. Modules in `𝒪` need not have finite composition series, but they have *local
composition series* ([Kac] Lemma 9.6): a filtration by submodules `0 = V₀ ⊆ V₁ ⊆ ⋯ ⊆ V_t = V` and a
subset `J ⊆ {1, …, t}` such that `V_j / V_{j-1} ≅ L(λ_j)` with `λ_j ≥ λ` for `j ∈ J`, and
`(V_j / V_{j-1})_μ = 0` for all `μ ≥ λ` when `j ∉ J`. Here `μ ≥ λ` means `μ - λ ∈ Q₊`, i.e.
`λ ∈ cone P μ`. The number of `j ∈ J` with `λ_j = μ` is the multiplicity `[V : L(μ)]`; it does not
depend on the local composition series, nor on `λ ≤ μ`.

## Design

A filtration `N = V₀ ⊆ V₁ ⊆ ⋯ ⊆ V_t = M` between two submodules `N ⊆ M` of `V` is encoded by the
list `[(V₁, o₁), …, (V_t, o_t)]`, where `o_j = some λ_j` if `j ∈ J` and `o_j = none` otherwise
(`Matrix.Realization.KacMoodyAlgebra.IsLocalCompositionSeries`). The list of the `λ_j`, `j ∈ J`,
is `Matrix.Realization.KacMoodyAlgebra.factorWeights`. The factor `V_j / V_{j-1}` is the Lie
module `LieSubmodule.Subquotient V_{j-1} V_j`.

## Main definitions

* `LieSubmodule.Subquotient N₁ N₂`: the subquotient `N₂ / N₁` of a Lie module.
* `Matrix.Realization.KacMoodyAlgebra.IsLocalFactor`: the condition on a factor of a local
  composition series.
* `Matrix.Realization.KacMoodyAlgebra.IsLocalCompositionSeries`: local composition series.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.exists_isLocalCompositionSeries`: local
  composition series exist ([Kac] Lemma 9.6).
* `Matrix.Realization.KacMoodyAlgebra.exists_subquotient_equiv_irreducibleModule`: a vector of
  weight `μ` that is primitive modulo a submodule `N₁` gives a subquotient `M₂ / M₁ ≅ L(μ)` with
  `N₁ ⊆ M₁`.

The multiplicities `[V : L(μ)]` are in `KacMoody/CompositionSeries/Multiplicity.lean`, and
the Casimir step of the proof of [Kac] Prop. 9.8 in `KacMoody/CompositionSeries/Casimir.lean`
(Prop. 9.8 itself, a character identity, in `KacMoody/CompositionSeries/Character.lean`).

## Proofs

*Existence* ([Kac] Lemma 9.6; written out by us). We prove more generally that for
submodules `N ⊆ M` of `V` there is a local composition series from `N` to `M`, by induction on
`a(M) - a(N)`, where `a(M) = ∑_{μ ≥ λ} dim (M ∩ V_μ)` (a finite sum, since only finitely many
weights of `V` are `≥ λ`); this is Kac's induction on `a(λ, M/N) = ∑_{μ ≥ λ} dim (M/N)_μ`. If
`M ∩ V_μ ⊆ N` for all `μ ≥ λ`, the one-step filtration `N ⊆ M` with `J = ∅` works, since
`(M/N)_μ` is the image of `M ∩ V_μ`. Otherwise choose `μ ≥ λ` maximal with `M ∩ V_μ ⊄ N` and
`w ∈ (M ∩ V_μ) \ N`; by maximality `eᵢ w ∈ N` for all `i`, so the image `w̄` of `w` in `V/N` is a
primitive vector, and there is a morphism `ψ : M(μ) → V/N` with `ψ(v_μ) = w̄`. Its image
`R = U(𝔤) w̄` and `R' = ψ(M'(μ))` satisfy `R/R' ≅ M(μ)/M'(μ) = L(μ)`, because `ker ψ ⊆ M'(μ)`
(`ker ψ` is proper). Let `U ⊇ U'` be the preimages of `R ⊇ R'` in `V`. Then `N ⊆ U' ⊆ U ⊆ M`,
`U/U' ≅ R/R' ≅ L(μ)`, and `w ∈ U \ U'`, so `a(U') < a(U)`; we conclude by applying the induction
hypothesis to `N ⊆ U'` and to `U ⊆ M`.

*Independence of the multiplicities* ([Kac] §9.6; written out by us). Along a local
composition series for `λ` from `0` to `V`, `dim V_ξ = ∑_{j ∈ J} dim L(λ_j)_ξ` for every `ξ ≥ λ`.
For `μ ≥ λ`, restricting to `ξ ≥ μ` only the `λ_j ≥ μ` contribute, and the multiset of these
`λ_j` is determined by the numbers `dim V_ξ`, `ξ ≥ μ`: if two multisets `s, s'` of weights
`≥ μ` give the same sums, take `λ'` maximal in `s + s'`; then `dim L(λ'')_{λ'} = 0` for
`λ'' ∈ s + s'` unless `λ'' = λ'`, and `dim L(λ')_{λ'} = 1`, so `λ'` occurs equally often in `s`
and `s'`, and we remove it from both and induct.

*[Kac] §9.8, proof of Prop. 9.8*. If `V` is a quotient of `M(Λ)`, the Casimir operator `Ω`
acts on `V`, hence on `V/N` for every submodule `N`, by `(Λ + 2ρ | Λ)`
(`IsStandardForm.casimir_eq_smul_of_surjective`). A primitive vector `w` of weight `μ` modulo
`N` gives a nonzero primitive vector of `V/N`, on which `Ω` acts by `(μ + 2ρ | μ)`
(`IsStandardForm.casimir_apply_of_lie_e_eq_zero`); and `μ ≤ Λ` since `μ` is a weight of the
quotient `V/N` of `M(Λ)`. A factor `V_j/V_{j-1} ≅ L(μ)` of a local composition series yields such
a `w` (a preimage in `V_j ∩ V_μ` of the highest-weight vector), with `N = V_{j-1}`. Finally
`(μ + ρ | μ + ρ) = (μ + 2ρ | μ) + (ρ | ρ)`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.5–2.6, §9.2–9.8
  (stated over `ℂ`).
-/

open Module LieModule

noncomputable section

/-! ### Subquotients of Lie modules -/

namespace LieSubmodule

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

/-- The subquotient `N₂ / N₁` of a Lie module `M`, for Lie submodules `N₁, N₂` of `M` (usually
`N₁ ≤ N₂`): the quotient of `N₂` by `N₁ ∩ N₂`. -/
abbrev Subquotient (N₁ N₂ : LieSubmodule R L M) : Type _ :=
  N₂ ⧸ N₁.comap N₂.incl

/-- A surjective morphism of Lie modules `f : M → M'` with kernel `N` induces an isomorphism
`M ⧸ N ≃ M'`. -/
theorem Quotient.nonempty_lieModuleEquiv_of_surjective {M' : Type*} [AddCommGroup M']
    [Module R M'] [LieRingModule L M'] [LieModule R L M'] (N : LieSubmodule R L M)
    (f : M →ₗ⁅R,L⁆ M') (hf : Function.Surjective f) (hN : f.ker = N) :
    Nonempty ((M ⧸ N) ≃ₗ⁅R,L⁆ M') := by
  let g := LieSubmodule.Quotient.lift N f hN.ge
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy ↦ ?_, LieSubmodule.Quotient.lift_surjective N f hN.ge hf⟩
    obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N x
    obtain ⟨y, rfl⟩ := LieSubmodule.Quotient.surjective_mk' N y
    rw [LieSubmodule.Quotient.lift_mk, LieSubmodule.Quotient.lift_mk] at hxy
    rw [← sub_eq_zero, ← map_sub, LieSubmodule.Quotient.mk_eq_zero, ← hN, LieModuleHom.mem_ker,
      map_sub, hxy, sub_self]
  exact ⟨LieModuleEquiv.ofBijective g hg⟩

end LieSubmodule

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-! ### The dominance order via cones -/

omit [DecidableEq ι] in
lemma mem_cone_self (μ : Dual K H) : μ ∈ cone P μ := ⟨0, le_rfl, by rw [map_zero, sub_zero]⟩

omit [DecidableEq ι] in
lemma mem_cone_trans {μ₁ μ₂ μ₃ : Dual K H} (h₁₂ : μ₁ ∈ cone P μ₂) (h₂₃ : μ₂ ∈ cone P μ₃) :
    μ₁ ∈ cone P μ₃ := by
  obtain ⟨k, hk, rfl⟩ := h₁₂
  obtain ⟨l, hl, rfl⟩ := h₂₃
  exact ⟨l + k, add_nonneg hl hk, by rw [map_add]; abel⟩

/-! ### Local composition series -/

variable (P) in
/-- The condition on the factor `N₂ / N₁` of a local composition series for `ν ∈ 𝔥*`
([Kac] Lemma 9.6): for `o = some μ`, `μ ≥ ν` and `N₂ / N₁ ≅ L(μ)`; for `o = none`, the
weight spaces `(N₂ / N₁)_μ` vanish for all `μ ≥ ν`. -/
def IsLocalFactor (ν : Dual K H) (N₁ N₂ : LieSubmodule K P.KacMoodyAlgebra V) :
    Option (Dual K H) → Prop
  | some μ => ν ∈ cone P μ ∧
      Nonempty (N₁.Subquotient N₂ ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P μ)
  | none => ∀ μ, ν ∈ cone P μ → weightSpace P (N₁.Subquotient N₂) μ = ⊥

variable (P) in
/-- `IsLocalCompositionSeries P ν N l M` says that the list `l = [(V₁, o₁), …, (V_t, o_t)]`
describes a *local composition series* for `ν` from `N` to `M` ([Kac] Lemma 9.6): the
filtration `N = V₀ ⊆ V₁ ⊆ ⋯ ⊆ V_t = M` has factors `V_j / V_{j-1}` satisfying
`IsLocalFactor P ν V_{j-1} V_j o_j`, i.e. `V_j / V_{j-1} ≅ L(λ_j)` with `λ_j ≥ ν` if
`o_j = some λ_j` (the indices `j ∈ J` of [Kac]), and `(V_j / V_{j-1})_μ = 0` for all `μ ≥ ν` if
`o_j = none`. -/
def IsLocalCompositionSeries (ν : Dual K H) :
    LieSubmodule K P.KacMoodyAlgebra V →
      List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H)) →
        LieSubmodule K P.KacMoodyAlgebra V → Prop
  | N, [], M => N = M
  | N, (N', o) :: l, M => N ≤ N' ∧ IsLocalFactor P ν N N' o ∧ IsLocalCompositionSeries ν N' l M

/-- The highest weights `λ_j`, `j ∈ J`, of the irreducible factors `L(λ_j)` of a local
composition series. -/
def factorWeights (l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))) :
    List (Dual K H) :=
  l.filterMap Prod.snd

omit [LieModule K P.KacMoodyAlgebra V] in
@[simp] lemma factorWeights_nil :
    factorWeights ([] : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))) = [] :=
  rfl

omit [LieModule K P.KacMoodyAlgebra V] in
@[simp] lemma factorWeights_cons_some (N : LieSubmodule K P.KacMoodyAlgebra V) (μ : Dual K H)
    (l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))) :
    factorWeights ((N, some μ) :: l) = μ :: factorWeights l :=
  rfl

omit [LieModule K P.KacMoodyAlgebra V] in
@[simp] lemma factorWeights_cons_none (N : LieSubmodule K P.KacMoodyAlgebra V)
    (l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))) :
    factorWeights ((N, none) :: l) = factorWeights l :=
  rfl

namespace IsLocalCompositionSeries

variable {ν : Dual K H}

@[simp] lemma nil_iff {N M : LieSubmodule K P.KacMoodyAlgebra V} :
    IsLocalCompositionSeries P ν N [] M ↔ N = M :=
  Iff.rfl

@[simp] lemma cons_iff {N N' M : LieSubmodule K P.KacMoodyAlgebra V} {o : Option (Dual K H)}
    {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))} :
    IsLocalCompositionSeries P ν N ((N', o) :: l) M ↔
      N ≤ N' ∧ IsLocalFactor P ν N N' o ∧ IsLocalCompositionSeries P ν N' l M :=
  Iff.rfl

/-- The filtration of a local composition series from `N` to `M` is increasing, so `N ≤ M`. -/
theorem le {N M : LieSubmodule K P.KacMoodyAlgebra V}
    {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P ν N l M) : N ≤ M := by
  induction l generalizing N with
  | nil => exact (nil_iff.mp hl).le
  | cons a l ih =>
    obtain ⟨N', o⟩ := a
    obtain ⟨h, -, hl⟩ := cons_iff.mp hl
    exact h.trans (ih hl)

/-- Local composition series can be concatenated. -/
theorem append {N₁ N₂ N₃ : LieSubmodule K P.KacMoodyAlgebra V}
    {l₁ l₂ : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (h₁ : IsLocalCompositionSeries P ν N₁ l₁ N₂) (h₂ : IsLocalCompositionSeries P ν N₂ l₂ N₃) :
    IsLocalCompositionSeries P ν N₁ (l₁ ++ l₂) N₃ := by
  induction l₁ generalizing N₁ with
  | nil =>
    rw [nil_iff] at h₁
    rwa [List.nil_append, h₁]
  | cons a l ih =>
    obtain ⟨N', o⟩ := a
    obtain ⟨h, hf, hl⟩ := cons_iff.mp h₁
    exact cons_iff.mpr ⟨h, hf, ih hl⟩

/-- Every irreducible factor `L(μ)` of a local composition series comes from a pair of
consecutive submodules `M₁ ≤ M₂` of the filtration with `M₂ / M₁ ≅ L(μ)` and `μ ≥ ν`. -/
theorem exists_of_mem_factorWeights {N M : LieSubmodule K P.KacMoodyAlgebra V}
    {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P ν N l M) {μ : Dual K H} (hμ : μ ∈ factorWeights l) :
    ∃ M₁ M₂ : LieSubmodule K P.KacMoodyAlgebra V, N ≤ M₁ ∧ M₁ ≤ M₂ ∧ M₂ ≤ M ∧
      IsLocalFactor P ν M₁ M₂ (some μ) := by
  induction l generalizing N with
  | nil => simp at hμ
  | cons a l ih =>
    obtain ⟨N', o⟩ := a
    obtain ⟨h, hf, hl'⟩ := cons_iff.mp hl
    clear hl
    cases o with
    | none =>
      obtain ⟨M₁, M₂, h₁, h₁₂, h₂, hf'⟩ := ih hl' (by simpa using hμ)
      exact ⟨M₁, M₂, h.trans h₁, h₁₂, h₂, hf'⟩
    | some μ' =>
      rcases List.mem_cons.mp (by simpa using hμ) with rfl | hμ
      · exact ⟨N, N', le_rfl, h, hl'.le, hf⟩
      · obtain ⟨M₁, M₂, h₁, h₁₂, h₂, hf'⟩ := ih hl' hμ
        exact ⟨M₁, M₂, h.trans h₁, h₁₂, h₂, hf'⟩

/-- The highest weights of the irreducible factors of a local composition series for `ν` are
`≥ ν`. -/
theorem mem_cone_of_mem_factorWeights {N M : LieSubmodule K P.KacMoodyAlgebra V}
    {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P ν N l M) {μ : Dual K H} (hμ : μ ∈ factorWeights l) :
    ν ∈ cone P μ := by
  obtain ⟨_, _, _, _, _, hf⟩ := hl.exists_of_mem_factorWeights hμ
  exact hf.1

end IsLocalCompositionSeries

variable [CharZero K]

/-- In a module in `𝒪`, only finitely many weights are `≥ ν`. -/
theorem IsCategoryO.finite_setOf_mem_cone (hV : IsCategoryO P V) (ν : Dual K H) :
    {μ | ν ∈ cone P μ ∧ weightSpace P V μ ≠ ⊥}.Finite := by
  refine (((hV.finite_setOf_weightSpace_add_ne_bot ν).image (· + ν)).insert ν).subset ?_
  rintro μ ⟨⟨k, hk, hνμ⟩, hμ⟩
  by_cases hk0 : k = 0
  · left
    rw [hνμ, hk0, map_zero, sub_zero]
  · right
    have hμ' : P.rootOf k + ν = μ := by rw [hνμ]; abel
    exact ⟨P.rootOf k, ⟨⟨k, ⟨hk, hk0⟩, rfl⟩, by rwa [hμ']⟩, hμ'⟩

/-! ### Weight spaces of subquotients -/

section Subquotient

variable (hV : IsCategoryO P V)
include hV

omit [CharZero K] in
lemma iSup_weightSpaceOfMap_lieSubmodule (N : LieSubmodule K P.KacMoodyAlgebra V) :
    ⨆ μ, weightSpaceOfMap N (h P) μ = ⊤ :=
  (hV.lieSubmodule N).iSup_weightSpaceOfMap_eq_top

omit [CharZero K] in
/-- For `V` in `𝒪`, the weight space `(N₂ / N₁)_μ` vanishes iff `N₂ ∩ V_μ ⊆ N₁`. -/
theorem weightSpace_subquotient_eq_bot_iff (N₁ N₂ : LieSubmodule K P.KacMoodyAlgebra V)
    (μ : Dual K H) :
    weightSpace P (N₁.Subquotient N₂) μ = ⊥ ↔
      N₂.toSubmodule ⊓ weightSpace P V μ ≤ N₁.toSubmodule := by
  rw [weightSpace, ← map_weightSpaceOfMap_quotient P _
    (iSup_weightSpaceOfMap_lieSubmodule hV N₂) μ, eq_bot_iff, Submodule.map_le_iff_le_comap,
    Submodule.comap_bot, ker_quotMk]
  constructor
  · rintro hle v ⟨hv₂, hv⟩
    exact hle ((mem_weightSpaceOfMap_lieSubmodule_iff (m := (⟨v, hv₂⟩ : N₂))).mpr hv)
  · intro hle m hm
    exact hle ⟨m.2, mem_weightSpaceOfMap_lieSubmodule_iff.mp hm⟩

omit [CharZero K] in
/-- `dim (N₂ ∩ V_μ) = dim (N₁ ∩ V_μ) + dim (N₂ / N₁)_μ` for submodules `N₁ ≤ N₂` of `V` in `𝒪`. -/
theorem finrank_inf_weightSpace_eq_add {N₁ N₂ : LieSubmodule K P.KacMoodyAlgebra V}
    (hN : N₁ ≤ N₂) (μ : Dual K H) :
    finrank K ↥(N₂.toSubmodule ⊓ weightSpace P V μ) =
      finrank K ↥(N₁.toSubmodule ⊓ weightSpace P V μ) +
        finrank K (weightSpace P (N₁.Subquotient N₂) μ) := by
  have := (hV.lieSubmodule N₂).finiteDimensional_weightSpaceOfMap μ
  have hadd := finrank_weightSpaceOfMap_eq_add P (N₁.comap N₂.incl)
    (iSup_weightSpaceOfMap_lieSubmodule hV N₂) μ
  rw [finrank_weightSpaceOfMap_lieSubmodule, finrank_weightSpaceOfMap_lieSubmodule] at hadd
  have hmap : ((N₁.comap N₂.incl).toSubmodule ⊓ weightSpaceOfMap N₂ (h P) μ).map
      (N₂.incl : N₂ →ₗ[K] V) = N₁.toSubmodule ⊓ weightSpace P V μ := by
    ext v
    constructor
    · rintro ⟨m, ⟨hm₁, hm⟩, rfl⟩
      exact ⟨hm₁, mem_weightSpaceOfMap_lieSubmodule_iff.mp hm⟩
    · rintro ⟨hv₁, hv⟩
      exact ⟨⟨v, hN hv₁⟩, ⟨hv₁, mem_weightSpaceOfMap_lieSubmodule_iff.mpr hv⟩, rfl⟩
  rw [hadd, (Submodule.equivMapOfInjective (N₂.incl : N₂ →ₗ[K] V) Subtype.val_injective
    _).finrank_eq, hmap]

end Subquotient

/-! ### Existence of local composition series -/

namespace IsCategoryO

variable (hV : IsCategoryO P V) (ν : Dual K H)

/-- The number `a(ν, N) = ∑_{μ ≥ ν} dim (N ∩ V_μ)` for a submodule `N` of a module `V` in `𝒪`,
used in the proof of [Kac] Lemma 9.6. -/
def finrankAbove (N : LieSubmodule K P.KacMoodyAlgebra V) : ℕ :=
  ∑ μ ∈ (hV.finite_setOf_mem_cone ν).toFinset, finrank K ↥(N.toSubmodule ⊓ weightSpace P V μ)

variable {ν}

lemma finrankAbove_mono {N₁ N₂ : LieSubmodule K P.KacMoodyAlgebra V} (h : N₁ ≤ N₂) :
    hV.finrankAbove ν N₁ ≤ hV.finrankAbove ν N₂ := by
  refine Finset.sum_le_sum fun μ _ ↦ ?_
  have := hV.finiteDimensional_weightSpaceOfMap μ
  have : FiniteDimensional K ↥(N₂.toSubmodule ⊓ weightSpace P V μ) :=
    Submodule.finiteDimensional_of_le inf_le_right
  exact Submodule.finrank_mono (inf_le_inf_right _ h)

lemma finrankAbove_lt {N₁ N₂ : LieSubmodule K P.KacMoodyAlgebra V} (h : N₁ ≤ N₂) {μ : Dual K H}
    (hνμ : ν ∈ cone P μ) {w : V} (hw : w ∈ weightSpace P V μ) (hw₂ : w ∈ N₂) (hw₁ : w ∉ N₁) :
    hV.finrankAbove ν N₁ < hV.finrankAbove ν N₂ := by
  refine Finset.sum_lt_sum (fun μ _ ↦ ?_) ⟨μ, ?_, ?_⟩
  · have := hV.finiteDimensional_weightSpaceOfMap μ
    have : FiniteDimensional K ↥(N₂.toSubmodule ⊓ weightSpace P V μ) :=
      Submodule.finiteDimensional_of_le inf_le_right
    exact Submodule.finrank_mono (inf_le_inf_right _ h)
  · rw [Set.Finite.mem_toFinset]
    refine ⟨hνμ, fun hbot ↦ hw₁ ?_⟩
    rw [hbot, Submodule.mem_bot] at hw
    rw [hw]
    exact N₁.zero_mem
  · have := hV.finiteDimensional_weightSpaceOfMap μ
    have : FiniteDimensional K ↥(N₂.toSubmodule ⊓ weightSpace P V μ) :=
      Submodule.finiteDimensional_of_le inf_le_right
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (inf_le_inf_right _ h) fun heq ↦ ?_)
    have : w ∈ N₁.toSubmodule ⊓ weightSpace P V μ := heq ▸ ⟨hw₂, hw⟩
    exact hw₁ this.1

end IsCategoryO

/-- Let `N₁ ≤ N₂` be submodules of `V` and let `w ∈ N₂ ∩ V_μ` be a primitive vector modulo `N₁`:
`w ∉ N₁` and `eᵢ w ∈ N₁` for all `i`. Then there are submodules `N₁ ≤ M₁ ≤ M₂ ≤ N₂` with
`w ∈ M₂ \ M₁` and `M₂ / M₁ ≅ L(μ)` (used in [Kac] Lemma 9.6). -/
theorem exists_subquotient_equiv_irreducibleModule {N₁ N₂ : LieSubmodule K P.KacMoodyAlgebra V}
    (hN : N₁ ≤ N₂) {μ : Dual K H} {w : V} (hw : w ∈ weightSpace P V μ) (hw₂ : w ∈ N₂)
    (hw₁ : w ∉ N₁) (he : ∀ i, ⁅e P i, w⁆ ∈ N₁) :
    ∃ M₁ M₂ : LieSubmodule K P.KacMoodyAlgebra V, N₁ ≤ M₁ ∧ M₁ ≤ M₂ ∧ M₂ ≤ N₂ ∧ w ∈ M₂ ∧
      w ∉ M₁ ∧ Nonempty (M₁.Subquotient M₂ ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P μ) := by
  set π := LieSubmodule.Quotient.mk' N₁
  have hw' : π w ∈ weightSpace P (V ⧸ N₁) μ := map_mem_weightSpaceOfMap P π hw
  have he' (i : ι) : ⁅e P i, π w⁆ = 0 := by
    rw [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero]
    exact he i
  set ψ := VermaModule.lift P (π w) (fun _ hx ↦ lie_eq_zero_of_mem_nPos he' hx) (fun a ↦ hw' a)
  have hψ : ψ (VermaModule.hwv P μ) = π w := VermaModule.lift_hwv P _ _ _
  set R := ψ.range
  set R' := (VermaModule.maxSubmodule P μ).map ψ
  have hker : ψ.ker ≤ VermaModule.maxSubmodule P μ := by
    refine (VermaModule.le_maxSubmodule_iff P μ _).mpr fun htop ↦ hw₁ ?_
    have : VermaModule.hwv P μ ∈ ψ.ker := htop ▸ LieSubmodule.mem_top _
    rwa [LieModuleHom.mem_ker, hψ, LieSubmodule.Quotient.mk_eq_zero] at this
  have hmem (m : VermaModule P μ) : ψ m ∈ R' ↔ m ∈ VermaModule.maxSubmodule P μ := by
    refine ⟨fun hm ↦ ?_, fun hm ↦ ⟨m, hm, rfl⟩⟩
    obtain ⟨m', hm', hmm'⟩ := (LieSubmodule.mem_map _).mp hm
    have : m - m' ∈ ψ.ker := by rw [LieModuleHom.mem_ker, map_sub, hmm', sub_self]
    simpa using add_mem (hker this) hm'
  have hRN₂ : R ≤ N₂.map π := by
    rw [show R = _ from VermaModule.range_eq_lieSpan ψ, LieSubmodule.lieSpan_le,
      Set.singleton_subset_iff, hψ]
    exact ⟨w, hw₂, rfl⟩
  -- the subquotient `R / R'` of `V / N₁` is isomorphic to `L(μ)`
  have e₁ : Nonempty (R'.Subquotient R ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P μ) := by
    let θ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ R'.Subquotient R :=
      (LieSubmodule.Quotient.mk' _).comp (ψ.codRestrict R fun m ↦ ⟨m, rfl⟩)
    have hθ : Function.Surjective θ := by
      intro q
      obtain ⟨⟨_, m, rfl⟩, rfl⟩ := LieSubmodule.Quotient.surjective_mk' _ q
      exact ⟨m, rfl⟩
    have hker : θ.ker = VermaModule.maxSubmodule P μ := by
      ext m
      rw [LieModuleHom.mem_ker, ← hmem]
      exact LieSubmodule.Quotient.mk_eq_zero _
    obtain ⟨e⟩ := LieSubmodule.Quotient.nonempty_lieModuleEquiv_of_surjective _ θ hθ hker
    exact ⟨e.symm⟩
  -- its preimage in `V` is isomorphic to it
  have e₂ : Nonempty ((R'.comap π).Subquotient (R.comap π) ≃ₗ⁅K,P.KacMoodyAlgebra⁆
      R'.Subquotient R) := by
    let θ : R.comap π →ₗ⁅K,P.KacMoodyAlgebra⁆ R'.Subquotient R :=
      (LieSubmodule.Quotient.mk' _).comp ((π.comp (R.comap π).incl).codRestrict R fun x ↦ x.2)
    have hθ : Function.Surjective θ := by
      intro q
      obtain ⟨r, rfl⟩ := LieSubmodule.Quotient.surjective_mk' _ q
      obtain ⟨x, hx⟩ := LieSubmodule.Quotient.surjective_mk' N₁ (r : V ⧸ N₁)
      exact ⟨⟨x, show π x ∈ R from hx ▸ r.2⟩,
        congrArg (LieSubmodule.Quotient.mk' (R'.comap R.incl)) (Subtype.ext hx)⟩
    have hker : θ.ker = (R'.comap π).comap (R.comap π).incl := by
      ext x
      rw [LieModuleHom.mem_ker]
      exact LieSubmodule.Quotient.mk_eq_zero _
    exact LieSubmodule.Quotient.nonempty_lieModuleEquiv_of_surjective _ θ hθ hker
  obtain ⟨e₁⟩ := e₁
  obtain ⟨e₂⟩ := e₂
  refine ⟨R'.comap π, R.comap π, fun x hx ↦ ?_,
    fun x hx ↦ LieSubmodule.map_le_range (N := VermaModule.maxSubmodule P μ) ψ hx, fun x hx ↦ ?_,
    ?_, ?_, ⟨e₂.trans e₁⟩⟩
  · rw [LieSubmodule.mem_comap, (LieSubmodule.Quotient.mk_eq_zero _).mpr hx]
    exact R'.zero_mem
  · obtain ⟨y, hy, hyx⟩ := (LieSubmodule.mem_map _).mp (hRN₂ (LieSubmodule.mem_comap.mp hx))
    have : x - y ∈ N₁ := by
      rw [← LieSubmodule.Quotient.mk_eq_zero, map_sub]
      exact sub_eq_zero.mpr hyx.symm
    simpa using add_mem (hN this) hy
  · exact LieSubmodule.mem_comap.mpr ⟨VermaModule.hwv P μ, hψ⟩
  · intro hw
    rw [LieSubmodule.mem_comap, ← hψ, hmem] at hw
    exact VermaModule.hwv_notMem_maxSubmodule P μ hw

namespace IsCategoryO

variable (hV : IsCategoryO P V) {ν : Dual K H}
include hV

/-- If `N₂ ∩ V_μ ⊄ N₁` for some `μ ≥ ν`, there is a factor `L(μ')`, `μ' ≥ ν`, between `N₁` and
`N₂` (the inductive step in [Kac] Lemma 9.6). -/
theorem exists_isLocalFactor_some {N₁ N₂ : LieSubmodule K P.KacMoodyAlgebra V} (hN : N₁ ≤ N₂)
    {μ : Dual K H} (hνμ : ν ∈ cone P μ)
    (hμ : ¬ N₂.toSubmodule ⊓ weightSpace P V μ ≤ N₁.toSubmodule) :
    ∃ (M₁ M₂ : LieSubmodule K P.KacMoodyAlgebra V) (μ' : Dual K H), N₁ ≤ M₁ ∧ M₁ ≤ M₂ ∧
      M₂ ≤ N₂ ∧ hV.finrankAbove ν M₁ < hV.finrankAbove ν M₂ ∧
        IsLocalFactor P ν M₁ M₂ (some μ') := by
  classical
  -- choose `μ' = μ + β ≥ μ` maximal with `N₂ ∩ V_{μ'} ⊄ N₁`
  set T : Set (ι → ℤ) :=
    {k | 0 ≤ k ∧ ¬ N₂.toSubmodule ⊓ weightSpace P V (μ + P.rootOf k) ≤ N₁.toSubmodule}
  have hTfin : T.Finite := by
    refine ((hV.finite_setOf_mem_cone ν).preimage
      (f := fun k ↦ μ + P.rootOf k) (fun k _ l _ hkl ↦ P.rootOf_injective
        (add_left_cancel hkl))).subset ?_
    rintro k ⟨hk, hkN⟩
    refine ⟨mem_cone_trans hνμ ⟨k, hk, (add_sub_cancel_right μ (P.rootOf k)).symm⟩,
      fun hbot ↦ hkN ?_⟩
    simp only at hbot
    rw [hbot, inf_bot_eq]
    exact bot_le
  have hTne : T.Nonempty := ⟨0, le_rfl, by rwa [map_zero, add_zero]⟩
  obtain ⟨k, ⟨hk, hkN⟩, hmax⟩ := hTfin.exists_maximal hTne
  obtain ⟨w, ⟨hw₂, hw⟩, hw₁⟩ := SetLike.not_le_iff_exists.mp hkN
  have he (i : ι) : ⁅e P i, w⁆ ∈ N₁ := by
    by_contra hne
    have hmem : k + Pi.single i 1 ∈ T := by
      refine ⟨add_nonneg hk (Pi.single_nonneg.mpr zero_le_one), fun hle ↦ hne (hle ⟨N₂.lie_mem hw₂,
        ?_⟩)⟩
      have := toEnd_e_mem_weightSpace i hw
      rwa [add_assoc, ← rootOf_single P i, ← map_add] at this
    have := hmax hmem (le_add_of_nonneg_right (Pi.single_nonneg.mpr zero_le_one)) i
    simp at this
  obtain ⟨M₁, M₂, h₁, h₁₂, h₂, hwM₂, hwM₁, he⟩ :=
    exists_subquotient_equiv_irreducibleModule hN hw hw₂ hw₁ he
  have hνμ' : ν ∈ cone P (μ + P.rootOf k) :=
    mem_cone_trans hνμ ⟨k, hk, (add_sub_cancel_right μ (P.rootOf k)).symm⟩
  exact ⟨M₁, M₂, μ + P.rootOf k, h₁, h₁₂, h₂, hV.finrankAbove_lt h₁₂ hνμ' hw hwM₂ hwM₁,
    hνμ', he⟩

/-- Local composition series exist between any two submodules `N₁ ≤ N₂` of a module in `𝒪`. -/
theorem exists_isLocalCompositionSeries_of_le (ν : Dual K H)
    {N₁ N₂ : LieSubmodule K P.KacMoodyAlgebra V} (h : N₁ ≤ N₂) :
    ∃ l, IsLocalCompositionSeries P ν N₁ l N₂ := by
  suffices H : ∀ n, ∀ N₁ N₂ : LieSubmodule K P.KacMoodyAlgebra V, N₁ ≤ N₂ →
      hV.finrankAbove ν N₂ - hV.finrankAbove ν N₁ = n →
        ∃ l, IsLocalCompositionSeries P ν N₁ l N₂ from H _ N₁ N₂ h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N₁ N₂ h hn
  by_cases hc : ∀ μ, ν ∈ cone P μ → N₂.toSubmodule ⊓ weightSpace P V μ ≤ N₁.toSubmodule
  · exact ⟨[(N₂, none)], h,
      fun μ hμ ↦ (weightSpace_subquotient_eq_bot_iff hV N₁ N₂ μ).mpr (hc μ hμ), rfl⟩
  obtain ⟨μ, hνμ, hμ⟩ : ∃ μ, ν ∈ cone P μ ∧
      ¬ N₂.toSubmodule ⊓ weightSpace P V μ ≤ N₁.toSubmodule := by
    simpa only [not_forall, exists_prop] using hc
  obtain ⟨M₁, M₂, μ', h₁, h₁₂, h₂, hlt, hf⟩ := hV.exists_isLocalFactor_some h hνμ hμ
  have hm₁ := hV.finrankAbove_mono (ν := ν) h₁
  have hm₂ := hV.finrankAbove_mono (ν := ν) h₂
  obtain ⟨l₁, hl₁⟩ := ih _ (by omega) N₁ M₁ h₁ rfl
  obtain ⟨l₂, hl₂⟩ := ih _ (by omega) M₂ N₂ h₂ rfl
  exact ⟨l₁ ++ (M₂, some μ') :: l₂, hl₁.append (IsLocalCompositionSeries.cons_iff.mpr
    ⟨h₁₂, hf, hl₂⟩)⟩

/-- **[Kac] Lemma 9.6**: a module `V` in the category `𝒪` has a local composition series
for every `ν ∈ 𝔥*`: a filtration `0 = V₀ ⊆ V₁ ⊆ ⋯ ⊆ V_t = V` and a subset `J ⊆ {1, …, t}` such
that `V_j / V_{j-1} ≅ L(λ_j)` with `λ_j ≥ ν` for `j ∈ J`, and `(V_j / V_{j-1})_μ = 0` for all
`μ ≥ ν` if `j ∉ J`. -/
theorem exists_isLocalCompositionSeries (ν : Dual K H) :
    ∃ l, IsLocalCompositionSeries P ν (⊥ : LieSubmodule K P.KacMoodyAlgebra V) l ⊤ :=
  hV.exists_isLocalCompositionSeries_of_le ν bot_le

end IsCategoryO

end Matrix.Realization.KacMoodyAlgebra
