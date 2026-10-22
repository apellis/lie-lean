/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Super.Casimir

/-!
# Weight modules of `U(G̃(A, τ))` and the Casimir operator

Let `V` be a module over `U = U(G̃(A, τ))`. This file collects the facts about weight spaces of `V`
used in the proof of the super Gabber–Kac theorem:

* the weight spaces of `V` are independent (`iSupIndep_modWeightSpace`), so an element of weight
  `μ` in the span of a set of weight vectors lies in the span of those of weight `μ`
  (`iSupIndep.mem_span_inter`);
* if `V` is spanned by weight vectors whose weights lie in finitely many cones `Λ - Q₊`
  (`SuperEnveloping.IsBounded`), then `V` satisfies the finiteness condition of the Casimir operator
  (`IsBounded.isPosFinite`); this holds for quotients and finite products;
* the Casimir operator commutes with module maps (`map_casimir`).

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §2.3.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.5, §9.11.
-/

open Module

/-- If `W` is an independent family of submodules, an element of `W μ` in the span of a set of
elements each lying in some `W ν` lies in the span of those lying in `W μ`. -/
lemma iSupIndep.mem_span_inter {R M κ : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {W : κ → Submodule R M} (hW : iSupIndep W) {G : Set M} (hG : ∀ g ∈ G, ∃ ν, g ∈ W ν)
    {v : M} (hv : v ∈ Submodule.span R G) {μ : κ} (hvμ : v ∈ W μ) :
    v ∈ Submodule.span R (G ∩ W μ) := by
  classical
  let N : κ → Submodule R M := fun ν ↦ Submodule.span R (G ∩ W ν)
  have hNW : ∀ ν, N ν ≤ W ν := fun ν ↦ Submodule.span_le.2 fun _ hg ↦ hg.2
  have hle : Submodule.span R G ≤ ⨆ ν, N ν := Submodule.span_le.2 fun g hg ↦ by
    obtain ⟨ν, hν⟩ := hG g hg
    exact Submodule.mem_iSup_of_mem ν (Submodule.subset_span ⟨hg, hν⟩)
  obtain ⟨c, hc, hcv⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (hle hv)
  have hw : v - c μ ∈ W μ ⊓ ⨆ ν, ⨆ (_ : ν ≠ μ), W ν := by
    refine ⟨sub_mem hvμ (hNW μ (hc μ)), ?_⟩
    have : v - c μ = (c.erase μ).sum fun _ x ↦ x := by
      rw [← hcv, ← Finsupp.add_sum_erase' c μ (fun _ x ↦ x) (fun _ ↦ rfl), add_sub_cancel_left]
    rw [this]
    refine Submodule.finsuppSum_mem _ _ _ _ fun ν hν ↦ ?_
    have hνμ : ν ≠ μ := fun h ↦ hν (h ▸ Finsupp.erase_same)
    rw [Finsupp.erase_ne hνμ]
    exact Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem hνμ (hNW ν (hc ν)))
  rw [(hW μ).eq_bot, Submodule.mem_bot, sub_eq_zero] at hw
  rw [hw]
  exact hc μ

noncomputable section

namespace Matrix.Realization.SuperEnveloping

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H} {p : ι → ZMod 2}

/-- The enveloping superalgebra `U(G̃(A, τ))`. -/
local notation "𝒰" => SuperEnveloping P p

section Module

variable (V : Type*) [AddCommGroup V] [Module K V] [Module (P.SuperEnveloping p) V]
  [IsScalarTower K (P.SuperEnveloping p) V]

lemma smul_mem_modWeightSpace {μ ν : Dual K H} {x : 𝒰} (hx : x ∈ weightSpace P p μ) {v : V}
    (hv : v ∈ modWeightSpace P p V ν) : x • v ∈ modWeightSpace P p V (μ + ν) := fun a ↦ by
  rw [smul_smul, hx a, add_smul, mul_smul, hv a, smul_comm, smul_assoc, LinearMap.add_apply,
    add_smul, add_comm]

lemma modWeightSpace_le_iInf (μ : Dual K H) :
    modWeightSpace P p V μ ≤ ⨅ a, (smulEnd P p V (h P p a)).maxGenEigenspace (μ a) := by
  intro v hv
  rw [Submodule.mem_iInf]
  refine fun a ↦ Module.End.eigenspace_le_maxGenEigenspace ?_
  rw [Module.End.mem_eigenspace_iff, smulEnd_apply, hv a]

/-- The weight spaces of a `U(G̃(A, τ))`-module are independent. -/
theorem iSupIndep_modWeightSpace : iSupIndep (modWeightSpace P p V) := by
  have hcomm : ∀ a b, Commute (smulEnd P p V (h P p a)) (smulEnd P p V (h P p b)) :=
    fun a b ↦ LinearMap.ext fun v ↦ by
      simp only [Module.End.mul_apply, smulEnd_apply, smul_smul, h_mul_h P p a b]
  have := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun a ↦ smulEnd P p V (h P p a))
    fun a b φ ↦ Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm b a) φ
  exact (this.comp DFunLike.coe_injective).mono (modWeightSpace_le_iInf V)

variable (P p) in
/-- The weight vectors of weights in the cones `Λ - Q₊`, `Λ ∈ Λs`. -/
def boundedVectors (Λs : Finset (Dual K H)) : Set V :=
  {w | ∃ Λ ∈ Λs, ∃ d : ι → ℤ, 0 ≤ d ∧ w ∈ modWeightSpace P p V (Λ - P.rootOf d)}

variable (P p) in
/-- `V` is spanned by weight vectors with weights in the cones `Λ - Q₊`, `Λ ∈ Λs`. -/
def IsBounded (Λs : Finset (Dual K H)) : Prop :=
  ∀ v : V, v ∈ Submodule.span K (boundedVectors P p V Λs)

variable {V}

variable [CharZero K]

omit [CharZero K] in
/-- In a bounded module, the weight of a nonzero weight vector lies in one of the cones. -/
lemma IsBounded.exists_eq_sub {Λs : Finset (Dual K H)} (hV : IsBounded P p V Λs) {ν : Dual K H}
    {w : V} (hw : w ∈ modWeightSpace P p V ν) (hw0 : w ≠ 0) :
    ∃ Λ ∈ Λs, ∃ d : ι → ℤ, 0 ≤ d ∧ ν = Λ - P.rootOf d := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hsub : boundedVectors P p V Λs ∩ modWeightSpace P p V ν ⊆ {0} := by
    rintro g ⟨⟨Λ, hΛ, d, hd, hg⟩, hgν⟩
    exact Submodule.disjoint_def.1 ((iSupIndep_modWeightSpace V).pairwiseDisjoint
      (Ne.symm (hne Λ hΛ d hd))) g hg hgν
  have := (iSupIndep_modWeightSpace V).mem_span_inter (G := boundedVectors P p V Λs)
    (fun g ⟨Λ, _, d, _, hg⟩ ↦ ⟨_, hg⟩) (hV w) hw
  have := Submodule.span_mono hsub this
  rw [Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at this
  exact hw0 this

omit [CharZero K] in
lemma IsBounded.of_surjective {W : Type*} [AddCommGroup W] [Module K W] [Module 𝒰 W]
    [IsScalarTower K 𝒰 W] {Λs : Finset (Dual K H)} (hV : IsBounded P p V Λs) (φ : V →ₗ[𝒰] W)
    (hφ : Function.Surjective φ) : IsBounded P p W Λs := by
  intro w
  obtain ⟨v, rfl⟩ := hφ w
  have : Submodule.map (φ.restrictScalars K) (Submodule.span K (boundedVectors P p V Λs)) ≤
      Submodule.span K (boundedVectors P p W Λs) := by
    rw [Submodule.map_span_le]
    rintro g ⟨Λ, hΛ, d, hd, hg⟩
    refine Submodule.subset_span ⟨Λ, hΛ, d, hd, fun a ↦ ?_⟩
    rw [LinearMap.restrictScalars_apply, ← map_smul, hg a, LinearMap.map_smul_of_tower]
  exact this ⟨v, hV v, rfl⟩

omit [CharZero K] in
/-- A finite product of bounded modules is bounded. -/
lemma isBounded_pi [DecidableEq (Dual K H)] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module K (M i)] [∀ i, Module 𝒰 (M i)] [∀ i, IsScalarTower K 𝒰 (M i)]
    {Λs : ι → Finset (Dual K H)} (hM : ∀ i, IsBounded P p (M i) (Λs i)) :
    IsBounded P p (∀ i, M i) (Finset.univ.biUnion Λs) := by
  intro v
  rw [← Finset.univ_sum_single v]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have : Submodule.map (LinearMap.single K M i)
      (Submodule.span K (boundedVectors P p (M i) (Λs i))) ≤
      Submodule.span K (boundedVectors P p (∀ i, M i) (Finset.univ.biUnion Λs)) := by
    rw [Submodule.map_span_le]
    rintro g ⟨Λ, hΛ, d, hd, hg⟩
    refine Submodule.subset_span ⟨Λ, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hΛ⟩, d, hd,
      fun a ↦ ?_⟩
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp [LinearMap.single_apply, hg a]
    · simp [LinearMap.single_apply, Pi.single_eq_of_ne hj]
  exact this ⟨v i, hM i (v i), rfl⟩

omit [DecidableEq ι] in
variable (P) in
/-- Only finitely many weights `α + ν`, `α ∈ Q₊ \ {0}`, occur in a bounded module. -/
lemma finite_setOf_add_eq_sub {Λs : Finset (Dual K H)} (Λ₀ : Dual K H) (d₀ : ι → ℤ) :
    {μ | μ ∈ P.posWeights ∧ ∃ Λ ∈ Λs, ∃ d : ι → ℤ, 0 ≤ d ∧
      μ + (Λ₀ - P.rootOf d₀) = Λ - P.rootOf d}.Finite := by
  classical
  let c : Dual K H → ι → ℤ := fun Λ ↦
    if hc : ∃ c, P.rootOf c = Λ - Λ₀ + P.rootOf d₀ then hc.choose else 0
  refine (Λs.finite_toSet.biUnion fun Λ _ ↦ ((Set.Finite.pi (t := fun i ↦ Set.Icc 0 (c Λ i))
    fun i ↦ Set.finite_Icc _ _).image P.rootOf)).subset ?_
  rintro _ ⟨⟨l, hl, rfl⟩, Λ, hΛ, d, hd, heq⟩
  have hld : P.rootOf (l + d) = Λ - Λ₀ + P.rootOf d₀ := by
    rw [map_add]
    linear_combination (norm := abel_nf) heq
  have hex : ∃ c, P.rootOf c = Λ - Λ₀ + P.rootOf d₀ := ⟨_, hld⟩
  have hc : c Λ = l + d := P.rootOf_injective (by
    simp only [c, hex, ↓reduceDIte]
    rw [hex.choose_spec, hld])
  refine Set.mem_biUnion hΛ ⟨l, fun i _ ↦ ⟨hl.1 i, ?_⟩, rfl⟩
  rw [hc, Pi.add_apply, le_add_iff_nonneg_right]
  exact hd i

/-- Bounded modules satisfy the finiteness condition of the Casimir operator. -/
theorem IsBounded.isPosFinite {Λs : Finset (Dual K H)} (hV : IsBounded P p V Λs) :
    IsPosFinite P p V := by
  intro v
  refine Submodule.span_induction (p := fun v _ ↦
    {μ | μ ∈ P.posWeights ∧ ∃ x ∈ gRoot P p μ, x • v ≠ 0}.Finite) ?_ ?_ ?_ ?_ (hV v)
  · rintro w ⟨Λ₀, -, d₀, -, hw⟩
    refine (finite_setOf_add_eq_sub P (Λs := Λs) Λ₀ d₀).subset ?_
    rintro μ ⟨hμ, x, hx, hxw⟩
    obtain ⟨Λ, hΛ, d, hd, heq⟩ := hV.exists_eq_sub (smul_mem_modWeightSpace V hx.2 hw) hxw
    exact ⟨hμ, Λ, hΛ, d, hd, heq⟩
  · simp
  · intro v w _ _ hv hw
    refine (hv.union hw).subset ?_
    rintro μ ⟨hμ, x, hx, hxv⟩
    by_cases h1 : x • v = 0
    · exact Or.inr ⟨hμ, x, hx, by rwa [smul_add, h1, zero_add] at hxv⟩
    · exact Or.inl ⟨hμ, x, hx, h1⟩
  · intro c v _ hv
    refine hv.subset ?_
    rintro μ ⟨hμ, x, hx, hxv⟩
    exact ⟨hμ, x, hx, fun h0 ↦ hxv (by rw [smul_comm, h0, smul_zero])⟩

end Module

/-! ### Naturality of the Casimir operator -/

section Naturality

variable {V W : Type*} [AddCommGroup V] [Module K V] [Module (P.SuperEnveloping p) V]
  [IsScalarTower K (P.SuperEnveloping p) V] [AddCommGroup W] [Module K W]
  [Module (P.SuperEnveloping p) W] [IsScalarTower K (P.SuperEnveloping p) W] [CharZero K]
  [FiniteDimensional K H] {S : A.Symmetrization}

lemma map_casimirTerm (φ : V →ₗ[𝒰] W) (μ : Dual K H) (v : V) :
    φ (casimirTerm P p V S μ v) = casimirTerm P p W S μ (φ v) := by
  simp only [casimirTerm_apply, casimirSum_def, map_sum, map_smul]

variable (S) in
/-- The Casimir operator commutes with module maps. -/
theorem map_casimir (hV : IsPosFinite P p V) (hW : IsPosFinite P p W) (φ : V →ₗ[𝒰] W) (v : V) :
    φ (casimir S hV v) = casimir S hW (φ v) := by
  rw [casimir_apply, casimir_apply, map_add, map_add, LinearMap.map_smul_of_tower, map_smul,
    map_casimirTerm, LinearMap.map_smul_of_tower]
  congr 2
  have := (φ.toAddMonoidHom).map_finsum_mem' (finite_casimirTerm (S := S) hV v)
  simp only [LinearMap.toAddMonoidHom_coe] at this
  rw [this]
  exact finsum_mem_congr rfl fun μ _ ↦ map_casimirTerm φ μ v

end Naturality

end Matrix.Realization.SuperEnveloping
