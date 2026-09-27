/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Concatenation
import LieLean.RepresentationTheory.Crystal.Path.Isomorphism
import LieLean.RepresentationTheory.Crystal.Path.LittlewoodRichardson
import LieLean.Algebra.Lie.KacMoody.TensorProduct

/-!
# The tensor product `B(λ) ⊗ B(μ)` of path crystals

Let `A` be a generalized Cartan matrix with a realization over a conditionally complete ordered
field (i.e. over `ℝ`), and `λ, μ` dominant integral weights. By Littelmann's tensor product rule
for concatenations (`LittelmannPath.e_concat_eq_tensor`), the concatenation `(η₁, η₂) ↦ η₁ * η₂`
identifies the tensor product crystal `B(λ) ⊗ B(μ)` with the set `B(λ) * B(μ)` of concatenated
paths, a subcrystal of the crystal of all paths ([Lit95] §10 (check)). We describe its highest
weight elements and relate their number to the tensor product multiplicities of integrable
modules.

## Main definitions

* `Crystal.sigma`: the disjoint union of a family of crystals.
* `Matrix.Realization.tensorPathCrystal`: the crystal `B(λ) ⊗ B(μ)`.
* `Matrix.Realization.concatHom`: the strict morphism `B(λ) ⊗ B(μ) → {paths}`,
  `η₁ ⊗ η₂ ↦ η₁ * η₂`.
* `Matrix.Realization.lrCount`: the number of `λ`-dominant `η ∈ B(μ)` with `λ + η(1) = ν`.

## Main results

* `LittelmannPath.concat_injective`: concatenation is injective.
* `Matrix.Realization.tensorPathCrystalEquiv`: `B(λ) ⊗ B(μ) ≅ B(λ) * B(μ)` (Littelmann).
* `Matrix.Realization.isHighestWeight_tensorPathCrystal_iff`: the highest weight elements of
  `B(λ) ⊗ B(μ)` are the `π_λ ⊗ η` with `η ∈ B(μ)` `λ`-dominant (no `hⱼ` of `η` reaches
  `-1 - ⟨λ, αⱼ^∨⟩`; equivalently `εⱼ(η) ≤ ⟨λ, αⱼ^∨⟩` for all `j`,
  `LittelmannPath.hitSet_eq_empty_iff`).
* `Matrix.Realization.exists_isHighestWeight_fWord_tensorPathCrystal`: every element of
  `B(λ) ⊗ B(μ)` is `f_{i₁} ⋯ f_{iₖ} (π_λ ⊗ η)` for some such `η`.
* `Matrix.Realization.multiplicity_tensorProduct`: **the Littlewood–Richardson rule for tensor
  product multiplicities** ([Lit94], [Lit95] §10 (check)): for symmetrizable `A`,
  `[L(λ) ⊗ L(μ) : L(ν)] = #{η ∈ B(μ) λ-dominant | λ + η(1) = ν}`.
* `Matrix.Realization.card_isHighestWeight_tensorPathCrystal`: the number of highest weight
  elements of weight `ν` in `B(λ) ⊗ B(μ)` is `[L(λ) ⊗ L(μ) : L(ν)]`.
* `Matrix.Realization.nonempty_equiv_sigma`: **the crystal-level decomposition**
  `B(λ) ⊗ B(μ) ≅ ⊔_{η ∈ B(μ) λ-dominant} B(λ + η(1))` ([Lit95] §10 (check)), *assuming*
  Littelmann's isomorphism theorem for the dominant paths `π_λ * η`
  (`Matrix.Realization.LRIsomorphismHypothesis`: `B(π_{λ + η(1)}) ≅ B(π_λ * η)`), which is not
  proved here (see `LieLean.RepresentationTheory.Crystal.Path.Isomorphism`).
* `LittelmannPath.concat_straightLine_self`: `π_λ * π_λ = π_{2λ}`; hence
  `LittelmannPath.componentIso_concat_straightLine_self`, the instance `λ = μ`, `η = π_λ` of the
  hypothesis (the Cartan component of `B(λ) ⊗ B(λ)`).

## References

* [Lit94] P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*,
  Invent. Math. **116** (1994), 329–346.
* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995).
-/

open Module Set

/-! ### Disjoint unions of families of crystals -/

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {α : Type*} {B : α → Type*}
  (C : ∀ a, Crystal D (B a)) {B' : Type*} {C' : Crystal D B'}

/-- The disjoint union `⊔_a B_a` of a family of crystals ([Kas] §7.2 (check)). -/
def sigma : Crystal D (Σ a, B a) where
  wt b := (C b.1).wt b.2
  ε i b := (C b.1).ε i b.2
  φ i b := (C b.1).φ i b.2
  e i b := ((C b.1).e i b.2).map (Sigma.mk b.1)
  f i b := ((C b.1).f i b.2).map (Sigma.mk b.1)
  φ_eq i b := (C b.1).φ_eq i b.2
  f_eq_some_iff i b b' := by
    obtain ⟨a, b⟩ := b
    obtain ⟨a', b'⟩ := b'
    constructor
    · intro h
      obtain ⟨c, hc, hcb⟩ := Option.map_eq_some_iff.mp h
      cases hcb
      change ((C a).e i c).map (Sigma.mk a) = _
      rw [((C a).f_eq_some_iff i b c).mp hc, Option.map_some]
    · intro h
      obtain ⟨c, hc, hcb⟩ := Option.map_eq_some_iff.mp h
      cases hcb
      change ((C a').f i c).map (Sigma.mk a') = _
      rw [((C a').f_eq_some_iff i c b').mpr hc, Option.map_some]
  wt_e i b b' h := by
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (C b.1).wt_e i b.2 c hc
  ε_e i b b' h := by
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (C b.1).ε_e i b.2 c hc
  e_eq_none_of_φ_eq_bot i b h := by
    rw [(C b.1).e_eq_none_of_φ_eq_bot i b.2 h, Option.map_none]

variable {C}

/-- A family of strict morphisms out of the members of a disjoint union. -/
def StrictHom.sigmaDesc (ψ : ∀ a, StrictHom (C a) C') : StrictHom (sigma C) C' where
  toFun b := ψ b.1 b.2
  wt_map b := (ψ b.1).wt_apply b.2
  ε_map i b := (ψ b.1).ε_apply i b.2
  e_map i b := by
    change C'.e i (ψ b.1 b.2) = (((C b.1).e i b.2).map (Sigma.mk b.1)).map _
    rw [(ψ b.1).e_apply, Option.map_map]
    rfl
  f_map i b := by
    change C'.f i (ψ b.1 b.2) = (((C b.1).f i b.2).map (Sigma.mk b.1)).map _
    rw [(ψ b.1).f_apply, Option.map_map]
    rfl

@[simp] lemma StrictHom.sigmaDesc_apply (ψ : ∀ a, StrictHom (C a) C') (b : Σ a, B a) :
    StrictHom.sigmaDesc ψ b = ψ b.1 b.2 := rfl

end Crystal

/-! ### Concatenation -/

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {D : CartanDatum ι X}
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

/-- Concatenation of paths is injective: `π₁ * π₂` determines `π₁` and `π₂`. -/
theorem concat_injective {π₁ π₂ π₁' π₂' : LittelmannPath S}
    (h : π₁.concat π₂ = π₁'.concat π₂') : π₁ = π₁' ∧ π₂ = π₂' := by
  have h₁ : π₁ = π₁' := ext_of_eqOn fun t ht ↦ by
    have ht2 : t / 2 ≤ 2⁻¹ := by linarith [ht.2]
    have := congrArg (· (t / 2)) h
    simp only [concat_apply_of_le ht2, mul_div_cancel₀ t two_ne_zero] at this
    exact this
  refine ⟨h₁, ext_of_eqOn fun t ht ↦ ?_⟩
  have ht2 : 2⁻¹ ≤ (t + 1) / 2 := by linarith [ht.1]
  have := congrArg (· ((t + 1) / 2)) h
  simp only [concat_apply_of_ge ht2, mul_div_cancel₀ (t + 1) two_ne_zero, add_sub_cancel_right,
    h₁, add_right_inj] at this
  exact this

/-- `π_λ * π_λ = π_{2λ}` (on the nose, with our parametrization of concatenations); so the
Cartan component of `B(λ) ⊗ B(λ)` is literally `B(2λ)`. -/
theorem concat_straightLine_self (μ : X) :
    (straightLine S μ).concat (straightLine S μ) = straightLine S (μ + μ) := by
  refine ext_of_eqOn fun t ht ↦ ?_
  rw [straightLine_apply, min_eq_right ht.2, max_eq_right ht.1, map_add]
  rcases le_total t 2⁻¹ with h | h
  · rw [concat_apply_of_le h, straightLine_apply, min_eq_right (by linarith),
      max_eq_right (by linarith [ht.1])]
    module
  · rw [concat_apply_of_ge h, straightLine_apply, straightLine_apply, min_eq_left le_rfl,
      max_eq_right zero_le_one, min_eq_right (by linarith [ht.2]), max_eq_right (by linarith)]
    module

variable [FloorRing 𝕜]

/-- The isomorphism property `B(π_{2λ}) ≅ B(π_λ * π_λ)` (the Cartan component of
`B(λ) ⊗ B(λ)`): the two paths are equal. -/
theorem componentIso_concat_straightLine_self (μ : X) :
    ComponentIso (straightLine S (μ + μ)) ((straightLine S μ).concat (straightLine S μ)) := by
  rw [concat_straightLine_self]
  exact ComponentIso.refl _

/-- `η` never reaches the levels `cⱼ` (i.e. all `hⱼ > cⱼ`) if and only if `εⱼ(η) ≤ -1 - cⱼ` for
all `j`. For `cⱼ = -1 - ⟨λ, αⱼ^∨⟩` this says that `η` is `λ`-dominant iff `εⱼ(η) ≤ ⟨λ, αⱼ^∨⟩`,
i.e. iff `π_λ ⊗ η` is a highest weight element of `B(λ) ⊗ B(μ)` (by the tensor product rule). -/
theorem hitSet_eq_empty_iff [Finite ι] (η : LittelmannPath S) (c : ι → ℤ) :
    η.hitSet c = ∅ ↔ ∀ j, ε j η ≤ ((-1 - c j : ℤ) : WithBot ℤ) := by
  simp only [ε, WithBot.coe_le_coe]
  constructor
  · intro h j
    have hlt : (c j : 𝕜) < η.minPairing j := by
      by_contra hle
      exact (Set.nonempty_iff_ne_empty.mp (hitSet_nonempty (not_lt.mp hle))) h
    rw [Int.floor_le_iff]
    push_cast
    linarith
  · intro h
    refine Set.eq_empty_of_forall_notMem fun t ⟨ht, j, hj⟩ ↦ ?_
    have h1 := h j
    rw [Int.floor_le_iff] at h1
    push_cast at h1
    linarith [η.minPairing_le (i := j) ht]

end LittelmannPath

/-! ### The crystal `B(λ) ⊗ B(μ)` -/

namespace Matrix.Realization

open LittelmannPath

variable {ι K H : Type*} [Fintype ι] [Field K] [ConditionallyCompleteLinearOrder K]
  [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] [FloorRing K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H} (hA : A.IsGeneralizedCartan)
  {Λ₁ Λ₂ : Dual K H} (hΛ₁ : P.IsDominantIntegral Λ₁) (hΛ₂ : P.IsDominantIntegral Λ₂)

/-- The paths of `B(λ)` are integral (they are Lakshmibai–Seshadri paths). -/
lemma isIntegral_of_mem_pathCrystal {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
    (b : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    b.1.IsIntegral := by
  classical
  exact fun i ↦
    ((component_straightLine_eq_fOrbit (hA := hA) hΛ).2 b.1 b.2).exists_int_minPairing i

/-- The tensor product crystal `B(λ) ⊗ B(μ)` (Kashiwara's convention, `Crystal.tensor`). -/
noncomputable abbrev tensorPathCrystal :=
  (P.pathCrystal hA hΛ₁).tensor (P.pathCrystal hA hΛ₂)

/-- Concatenation `η₁ ⊗ η₂ ↦ η₁ * η₂` is a strict morphism from `B(λ) ⊗ B(μ)` to the crystal of
all paths ([Lit95] §2 (check)): this is Littelmann's tensor product rule for concatenations of
integral paths (`LittelmannPath.e_concat_eq_tensor`, `LittelmannPath.f_concat_eq_tensor`). -/
noncomputable def concatHom :
    Crystal.StrictHom (tensorPathCrystal hA hΛ₁ hΛ₂) (crystal (P.pathSpace hA)) where
  toFun p := p.1.1.concat p.2.1
  wt_map _ := rfl
  ε_map _ _ := ε_concat
  e_map i p := by
    have h := ((Crystal.restrictHom (isStable_component _)).tensorMap
      (Crystal.restrictHom (isStable_component _))).e_apply i p
    rw [crystal_e, e_concat_eq_tensor (isIntegral_of_mem_pathCrystal hA hΛ₁ p.1)
      (isIntegral_of_mem_pathCrystal hA hΛ₂ p.2)]
    rw [show ((p.1 : LittelmannPath (P.pathSpace hA)), (p.2 : LittelmannPath (P.pathSpace hA))) =
      (Crystal.restrictHom (isStable_component _)).tensorMap
        (Crystal.restrictHom (isStable_component _)) p from rfl, h, Option.map_map]
    rfl
  f_map i p := by
    have h := ((Crystal.restrictHom (isStable_component _)).tensorMap
      (Crystal.restrictHom (isStable_component _))).f_apply i p
    rw [crystal_f, f_concat_eq_tensor (isIntegral_of_mem_pathCrystal hA hΛ₁ p.1)
      (isIntegral_of_mem_pathCrystal hA hΛ₂ p.2)]
    rw [show ((p.1 : LittelmannPath (P.pathSpace hA)), (p.2 : LittelmannPath (P.pathSpace hA))) =
      (Crystal.restrictHom (isStable_component _)).tensorMap
        (Crystal.restrictHom (isStable_component _)) p from rfl, h, Option.map_map]
    rfl

@[simp] lemma concatHom_apply
    (p : (straightLine (P.pathSpace hA) ⟨Λ₁, hΛ₁.mem_integralWeights⟩).component ×
      (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component) :
    concatHom hA hΛ₁ hΛ₂ p = p.1.1.concat p.2.1 := rfl

lemma concatHom_injective : Function.Injective (concatHom hA hΛ₁ hΛ₂) := fun p q h ↦ by
  obtain ⟨h₁, h₂⟩ := concat_injective h
  exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)

/-- **`B(λ) ⊗ B(μ) ≅ B(λ) * B(μ)`** ([Lit95] §10 (check)): concatenation identifies the tensor
product crystal with the subcrystal of concatenated paths `η₁ * η₂`. -/
noncomputable def tensorPathCrystalEquiv :
    Crystal.Equiv (tensorPathCrystal hA hΛ₁ hΛ₂)
      (Crystal.restrict (concatHom hA hΛ₁ hΛ₂).isStable_range) :=
  Crystal.Equiv.ofInjective _ (concatHom_injective hA hΛ₁ hΛ₂)

omit [TopologicalSpace K] [OrderTopology K] in
lemma neg_one_sub_shiftLevel (j : ι) :
    -1 - shiftLevel hA hΛ₁ j = (P.cartanDatum hA).coroot j ⟨Λ₁, hΛ₁.mem_integralWeights⟩ := by
  rw [shiftLevel]
  ring

/-- **The highest weight elements of `B(λ) ⊗ B(μ)`** ([Lit95] §10 (check)): `η₁ ⊗ η₂` is of
highest weight iff `η₁ = π_λ` and `η₂` is `λ`-dominant (no `hⱼ` of `η₂` reaches
`-1 - ⟨λ, αⱼ^∨⟩`; equivalently, `εⱼ(η₂) ≤ ⟨λ, αⱼ^∨⟩` for all `j`). By the tensor product rule,
`ẽᵢ(η₁ ⊗ η₂) = 0` iff `εᵢ(η₂) ≤ φᵢ(η₁)` and `ẽᵢ η₁ = 0`, and `π_λ` is the only highest weight
element of `B(λ)`. -/
theorem isHighestWeight_tensorPathCrystal_iff
    (p : (straightLine (P.pathSpace hA) ⟨Λ₁, hΛ₁.mem_integralWeights⟩).component ×
      (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component) :
    (tensorPathCrystal hA hΛ₁ hΛ₂).IsHighestWeight p ↔
      p.1 = pathCrystalTop hA hΛ₁ ∧ p.2.1.hitSet (shiftLevel hA hΛ₁) = ∅ := by
  have key : ∀ i, (tensorPathCrystal hA hΛ₁ hΛ₂).e i p = none ↔
      ((P.pathCrystal hA hΛ₂).ε i p.2 ≤ (P.pathCrystal hA hΛ₁).φ i p.1 ∧
        (P.pathCrystal hA hΛ₁).e i p.1 = none) := fun i ↦ by
    rw [Crystal.tensor_e]
    split_ifs with hc
    · simp [hc]
    · simp only [Option.map_eq_none_iff, hc, false_and, iff_false]
      intro h
      apply hc
      rw [(isSeminormal_pathCrystal hA hΛ₂).ε_eq_zero h]
      exact (isSeminormal_pathCrystal hA hΛ₁).φ_nonneg i p.1
  simp only [Crystal.IsHighestWeight, key, forall_and]
  rw [show (∀ i, (P.pathCrystal hA hΛ₁).e i p.1 = none) ↔ p.1 = pathCrystalTop hA hΛ₁ from
    isHighestWeight_pathCrystal_iff hA hΛ₁ p.1, hitSet_eq_empty_iff]
  constructor
  · rintro ⟨h, h1⟩
    refine ⟨h1, fun j ↦ ?_⟩
    rw [neg_one_sub_shiftLevel hA hΛ₁ j, ← φ_straightLine hA hΛ₁ j]
    have := h j
    rw [h1] at this
    exact this
  · rintro ⟨h1, h⟩
    refine ⟨fun j ↦ ?_, h1⟩
    rw [h1]
    have := h j
    rw [neg_one_sub_shiftLevel hA hΛ₁ j, ← φ_straightLine hA hΛ₁ j] at this
    exact this

/-- Every element of `B(λ) ⊗ B(μ)` is `f_{i₁} ⋯ f_{iₖ} (π_λ ⊗ η)` for some `λ`-dominant
`η ∈ B(μ)` (apply raising operators as long as possible; the depth in `λ + μ - Q₊` decreases). -/
theorem exists_isHighestWeight_fWord_tensorPathCrystal
    (p : (straightLine (P.pathSpace hA) ⟨Λ₁, hΛ₁.mem_integralWeights⟩).component ×
      (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component) :
    ∃ η : (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component,
      η.1.hitSet (shiftLevel hA hΛ₁) = ∅ ∧
        ∃ l, (tensorPathCrystal hA hΛ₁ hΛ₂).fWord l (pathCrystalTop hA hΛ₁, η) = some p := by
  obtain ⟨h, hh, l, hl⟩ := (tensorPathCrystal hA hΛ₁ hΛ₂).exists_isHighestWeight_fWord
    (fun q ↦ pathDepth hA hΛ₁ q.1 + pathDepth hA hΛ₂ q.2) (fun i q q' hq ↦ by
      rw [Crystal.tensor_e] at hq
      split_ifs at hq
      · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hq
        have := pathDepth_of_e_eq_some hA hΛ₁ hc
        dsimp only
        omega
      · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hq
        have := pathDepth_of_e_eq_some hA hΛ₂ hc
        dsimp only
        omega) p
  obtain ⟨h1, h2⟩ := (isHighestWeight_tensorPathCrystal_iff hA hΛ₁ hΛ₂ h).mp hh
  refine ⟨h.2, h2, l, ?_⟩
  rw [← hl, ← h1]

/-! ### Tensor product multiplicities -/

section Multiplicity

open KacMoodyAlgebra CharacterRing HahnSeries

/-- The set of `λ`-dominant paths `η ∈ B(μ)` with `λ + η(1) = ν`. -/
def lrSet (ν : Dual K H) :
    Set (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component :=
  {b | b.1.hitSet (shiftLevel hA hΛ₁) = ∅ ∧ Λ₁ + (b.1.wt : Dual K H) = ν}

lemma finite_lrSet (ν : Dual K H) : (lrSet hA hΛ₁ hΛ₂ ν).Finite :=
  (finite_fibre hA hΛ₂ (ν - Λ₁)).subset fun b hb ↦ by
    change (b.1.wt : Dual K H) = ν - Λ₁
    rw [← hb.2]
    abel

/-- The Littlewood–Richardson number `#{η ∈ B(μ) λ-dominant | λ + η(1) = ν}`. -/
noncomputable def lrCount (ν : Dual K H) : ℕ := Nat.card (lrSet hA hΛ₁ hΛ₂ ν)

/-- The formal sum `∑_{η ∈ B(μ) λ-dominant} e^{λ + η(1)} ∈ ℰ`. -/
noncomputable def lrMultiplicities : P.CharacterRing ℤ :=
  ofFun P (fun ν ↦ (lrCount hA hΛ₁ hΛ₂ ν : ℤ)) ⟨{Λ₁ + Λ₂}, fun ν hν ↦ by
    obtain ⟨⟨b, hb⟩⟩ : Nonempty (lrSet hA hΛ₁ hΛ₂ ν) := by
      by_contra h
      have := not_nonempty_iff.mp h
      exact hν (by rw [lrCount, Nat.card_of_isEmpty, Nat.cast_zero])
    obtain ⟨k, hk, hbk⟩ := exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ₂ b
    refine ⟨Λ₁ + Λ₂, Finset.mem_singleton_self _, k, hk, ?_⟩
    change (b.1.wt : Dual K H) = _ at hbk
    rw [← hb.2, hbk]
    abel⟩

@[simp] lemma coeffAt_lrMultiplicities (ν : Dual K H) :
    (lrMultiplicities hA hΛ₁ hΛ₂).coeffAt ν = lrCount hA hΛ₁ hΛ₂ ν := rfl

variable [DecidableEq ι]

/-- `∑_ν #{η λ-dominant | λ + η(1) = ν} ch L(ν) = ∑_{η λ-dominant} ch L(λ + η(1))`: regrouping
the Littlewood–Richardson sum `Matrix.Realization.lrFamily` by weights. -/
theorem sumIrreducibleCharacter_lrMultiplicities :
    sumIrreducibleCharacter P (lrMultiplicities hA hΛ₁ hΛ₂) = (lrFamily hA hΛ₁ hΛ₂).hsum := by
  classical
  ext ξ
  set F : Dual K H → ℤ := fun μ ↦ (finrank K (weightSpace P (IrreducibleModule P μ) ξ) : ℤ)
  set U := {μ | μ ∈ cone P (Λ₁ + Λ₂) ∧ ξ ∈ cone P μ}
  have hU : U.Finite := finite_setOf_mem_cone_and_mem_cone P (Λ₁ + Λ₂) ξ
  have hcone : ∀ b : (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component,
      Λ₁ + (b.1.wt : Dual K H) ∈ cone P (Λ₁ + Λ₂) := fun b ↦ by
    obtain ⟨k, hk, hbk⟩ := exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ₂ b
    change (b.1.wt : Dual K H) = _ at hbk
    exact ⟨k, hk, by rw [hbk]; abel⟩
  have hF : ∀ μ, F μ ≠ 0 → ξ ∈ cone P μ := fun μ h ↦
    IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero fun h0 ↦ h (by simp [F, h0])
  set T := ⋃ μ ∈ U, lrSet hA hΛ₁ hΛ₂ μ
  have hT : T.Finite := hU.biUnion fun μ _ ↦ finite_lrSet hA hΛ₁ hΛ₂ μ
  -- the left side
  have hL : (sumIrreducibleCharacter P (lrMultiplicities hA hΛ₁ hΛ₂)).coeffAt ξ =
      ∑ μ ∈ hU.toFinset, (lrCount hA hΛ₁ hΛ₂ μ : ℤ) * F μ := by
    rw [coeffAt_sumIrreducibleCharacter]
    refine finsum_eq_sum_of_support_subset _ fun μ hμ ↦ ?_
    rw [Function.mem_support] at hμ
    have h1 := left_ne_zero_of_mul hμ
    rw [coeffAt_lrMultiplicities, Nat.cast_ne_zero] at h1
    obtain ⟨⟨b, hb⟩⟩ : Nonempty (lrSet hA hΛ₁ hΛ₂ μ) := by
      by_contra h
      have := not_nonempty_iff.mp h
      exact h1 (by rw [lrCount, Nat.card_of_isEmpty])
    exact hU.mem_toFinset.mpr ⟨hb.2 ▸ hcone b, hF μ (right_ne_zero_of_mul hμ)⟩
  -- the right side
  have hR : CharacterRing.coeffAt (P := P) (lrFamily hA hΛ₁ hΛ₂).hsum ξ =
      ∑ b ∈ hT.toFinset, F (Λ₁ + (b.1.wt : Dual K H)) := by
    rw [coeffAt, SummableFamily.coeff_hsum]
    rw [finsum_eq_sum_of_support_subset _ (s := hT.toFinset) fun b hb ↦ ?_]
    · refine Finset.sum_congr rfl fun b hb ↦ ?_
      obtain ⟨μ, hμ, hbμ⟩ := Set.mem_iUnion₂.mp (hT.mem_toFinset.mp hb)
      rw [lrFamily_apply, ite_eq_left hbμ.1]
      exact IsCategoryO.coeffAt_character _ ξ
    · rw [Function.mem_support, lrFamily_apply] at hb
      by_cases hd : b.1.hitSet (shiftLevel hA hΛ₁) = ∅
      · rw [ite_eq_left hd] at hb
        have h2 : (IrreducibleModule.isCategoryO P (Λ₁ + (b.1.wt : Dual K H))).character.coeffAt
            ξ ≠ 0 := hb
        rw [IsCategoryO.coeffAt_character] at h2
        have hb' : F (Λ₁ + (b.1.wt : Dual K H)) ≠ 0 := h2
        exact hT.mem_toFinset.mpr (Set.mem_iUnion₂.mpr ⟨_, ⟨hcone b, hF _ hb'⟩, hd, rfl⟩)
      · rw [ite_eq_right hd, HahnSeries.coeff_zero] at hb
        exact absurd rfl hb
  change (sumIrreducibleCharacter P (lrMultiplicities hA hΛ₁ hΛ₂)).coeffAt ξ =
    CharacterRing.coeffAt (P := P) (lrFamily hA hΛ₁ hΛ₂).hsum ξ
  rw [hL, hR, ← Finset.sum_fiberwise_of_maps_to (t := hU.toFinset)
    (g := fun b : (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component ↦
      Λ₁ + (b.1.wt : Dual K H)) fun b hb ↦ ?_]
  · refine Finset.sum_congr rfl fun μ hμ ↦ ?_
    rw [Finset.sum_congr rfl fun b hb ↦ by rw [(Finset.mem_filter.mp hb).2], Finset.sum_const,
      nsmul_eq_mul]
    congr 1
    rw [lrCount, Nat.card_coe_set_eq,
      Set.ncard_eq_toFinset_card _ (finite_lrSet hA hΛ₁ hΛ₂ μ)]
    congr 2
    ext b
    rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    constructor
    · intro hb
      exact ⟨Set.mem_iUnion₂.mpr ⟨μ, hU.mem_toFinset.mp hμ, hb⟩, hb.2⟩
    · rintro ⟨hb, h⟩
      obtain ⟨μ', -, hbμ'⟩ := Set.mem_iUnion₂.mp hb
      exact ⟨hbμ'.1, h⟩
  · obtain ⟨μ, hμ, hbμ⟩ := Set.mem_iUnion₂.mp (hT.mem_toFinset.mp hb)
    rw [hbμ.2]
    exact hU.mem_toFinset.mpr hμ

/-- **Littelmann's Littlewood–Richardson rule for tensor product multiplicities** ([Lit94] Thm.
(check), [Lit95] §10 (check)): for a symmetrizable generalized Cartan matrix and dominant integral
weights `λ, μ`, the multiplicity of `L(ν)` in `L(λ) ⊗ L(μ)` (a direct sum of irreducible modules
`L(ν)`, `KacMoodyAlgebra.IrreducibleModule.exists_isInternal_tensorProduct`) is the number of
`λ`-dominant paths `η ∈ B(μ)` with `λ + η(1) = ν`. This follows from the character identity
`Matrix.Realization.character_mul_character` and the linear independence of the irreducible
characters (`KacMoodyAlgebra.sumIrreducibleCharacter_injective`). -/
theorem multiplicity_tensorProduct [FiniteDimensional K H] (hS : A.IsSymmetrizable)
    (ν : Dual K H) :
    ((IrreducibleModule.isCategoryO P Λ₁).tensorProduct
        (IrreducibleModule.isCategoryO P Λ₂)).multiplicity ν = lrCount hA hΛ₁ hΛ₂ ν := by
  have h := IsCategoryO.sumIrreducibleCharacter_multiplicities_tensorProduct
    (IrreducibleModule.isCategoryO P Λ₁) (IrreducibleModule.isCategoryO P Λ₂)
  rw [character_mul_character hA hΛ₁ hΛ₂ hS, ← sumIrreducibleCharacter_lrMultiplicities] at h
  have := congrArg (fun c ↦ c.coeffAt ν) (sumIrreducibleCharacter_injective h)
  simp only [IsCategoryO.coeffAt_multiplicities, coeffAt_lrMultiplicities, Nat.cast_inj] at this
  exact this

omit [DecidableEq ι] in
/-- The highest weight elements of weight `ν` of `B(λ) ⊗ B(μ)` are the `π_λ ⊗ η`, `η ∈ B(μ)`
`λ`-dominant with `λ + η(1) = ν`. -/
theorem card_isHighestWeight_tensorPathCrystal_eq_lrCount (ν : Dual K H) :
    Nat.card {p // (tensorPathCrystal hA hΛ₁ hΛ₂).IsHighestWeight p ∧
      ((tensorPathCrystal hA hΛ₁ hΛ₂).wt p : Dual K H) = ν} = lrCount hA hΛ₁ hΛ₂ ν := by
  refine Nat.card_congr
    { toFun p := ⟨p.1.2, ((isHighestWeight_tensorPathCrystal_iff hA hΛ₁ hΛ₂ p.1).mp p.2.1).2,
        ?_⟩
      invFun η := ⟨(pathCrystalTop hA hΛ₁, η.1),
        (isHighestWeight_tensorPathCrystal_iff hA hΛ₁ hΛ₂ _).mpr ⟨rfl, η.2.1⟩, η.2.2⟩
      left_inv p := ?_
      right_inv η := rfl }
  · have h1 := ((isHighestWeight_tensorPathCrystal_iff hA hΛ₁ hΛ₂ p.1).mp p.2.1).1
    refine Eq.trans ?_ p.2.2
    rw [Crystal.tensor_wt, AddSubgroup.coe_add, h1]
    rfl
  · obtain ⟨⟨p₁, p₂⟩, hp, -⟩ := p
    obtain ⟨rfl, -⟩ := (isHighestWeight_tensorPathCrystal_iff hA hΛ₁ hΛ₂ _).mp hp
    rfl

/-- **Highest weight elements of `B(λ) ⊗ B(μ)` count tensor product multiplicities**: for
symmetrizable `A`, the number of highest weight elements of weight `ν` in the crystal
`B(λ) ⊗ B(μ)` is `[L(λ) ⊗ L(μ) : L(ν)]`. -/
theorem card_isHighestWeight_tensorPathCrystal [FiniteDimensional K H] (hS : A.IsSymmetrizable)
    (ν : Dual K H) :
    Nat.card {p // (tensorPathCrystal hA hΛ₁ hΛ₂).IsHighestWeight p ∧
      ((tensorPathCrystal hA hΛ₁ hΛ₂).wt p : Dual K H) = ν} =
      ((IrreducibleModule.isCategoryO P Λ₁).tensorProduct
        (IrreducibleModule.isCategoryO P Λ₂)).multiplicity ν := by
  rw [card_isHighestWeight_tensorPathCrystal_eq_lrCount, multiplicity_tensorProduct hA hΛ₁ hΛ₂ hS]

end Multiplicity

/-! ### The crystal-level decomposition, assuming the isomorphism theorem -/

section Decomposition

/-- The `λ`-dominant paths `η ∈ B(μ)`, indexing the components of `B(λ) ⊗ B(μ)`. -/
abbrev LRIndex :=
  {b : (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component //
    b.1.hitSet (shiftLevel hA hΛ₁) = ∅}

/-- The crystals `B(λ + η(1))`, `η ∈ B(μ)` `λ`-dominant. -/
noncomputable abbrev lrCrystal (η : LRIndex hA hΛ₁ hΛ₂) :=
  P.pathCrystal hA (isDominantIntegral_add_wt hA hΛ₁ hΛ₂ η.1 η.2)

/-- The instances of Littelmann's isomorphism theorem needed for the decomposition of
`B(λ) ⊗ B(μ)`: for every `λ`-dominant `η ∈ B(μ)`, `B(π_{λ + η(1)}) ≅ B(π_λ * η)` with
`π_{λ + η(1)} ↦ π_λ * η` (both paths lie in the dominant chamber and end at `λ + η(1)`). Not
proved here; see `LieLean.RepresentationTheory.Crystal.Path.Isomorphism`. -/
def LRIsomorphismHypothesis : Prop :=
  ∀ η : LRIndex hA hΛ₁ hΛ₂, ComponentIso
    (straightLine (P.pathSpace hA) ⟨Λ₁ + (η.1.1.wt : Dual K H),
      (isDominantIntegral_add_wt hA hΛ₁ hΛ₂ η.1 η.2).mem_integralWeights⟩)
    ((straightLine (P.pathSpace hA) ⟨Λ₁, hΛ₁.mem_integralWeights⟩).concat η.1.1)

/-- **The crystal-level Littlewood–Richardson decomposition** ([Lit95] §10 (check)), assuming the
isomorphism theorem for the paths `π_λ * η` (`Matrix.Realization.LRIsomorphismHypothesis`):
`B(λ) ⊗ B(μ) ≅ ⊔_{η ∈ B(μ) λ-dominant} B(λ + η(1))`, with `π_λ ⊗ η ↦ π_{λ + η(1)}`.

Proof: concatenation embeds `B(λ) ⊗ B(μ)` into the crystal of paths
(`Matrix.Realization.tensorPathCrystalEquiv`); by hypothesis, the components `B(π_λ * η)` are
images of the `B(λ + η(1))`. They cover `B(λ) * B(μ)` since every element is
`f_{i₁} ⋯ f_{iₖ} (π_λ * η)` (`Matrix.Realization.exists_isHighestWeight_fWord_tensorPathCrystal`),
and they are disjoint since `π_λ * η'` is a highest weight element, while `π_λ * η` is the only
highest weight element of `B(π_λ * η) ≅ B(λ + η(1))`. -/
theorem nonempty_equiv_sigma (h : LRIsomorphismHypothesis hA hΛ₁ hΛ₂) :
    Nonempty (Crystal.Equiv (tensorPathCrystal hA hΛ₁ hΛ₂)
      (Crystal.sigma (lrCrystal hA hΛ₁ hΛ₂))) := by
  choose Φ hΦ using h
  let ψ : ∀ η, Crystal.StrictHom (lrCrystal hA hΛ₁ hΛ₂ η) (crystal (P.pathSpace hA)) :=
    fun η ↦ (Crystal.restrictHom (isStable_component _)).comp (Φ η).toStrictHom
  have hψ : ∀ η x, ψ η x = (Φ η x : LittelmannPath (P.pathSpace hA)) := fun _ _ ↦ rfl
  have hψtop : ∀ η, ψ η (pathCrystalTop hA (isDominantIntegral_add_wt hA hΛ₁ hΛ₂ η.1 η.2)) =
      (pathCrystalTop hA hΛ₁).1.concat η.1.1 := hΦ
  have hψmem : ∀ η x, ψ η x ∈ ((pathCrystalTop hA hΛ₁).1.concat η.1.1).component :=
    fun η x ↦ (Φ η x).2
  have hψsurj : ∀ η, ∀ y ∈ ((pathCrystalTop hA hΛ₁).1.concat η.1.1).component,
      ∃ x, ψ η x = y := fun η y hy ↦
    ⟨(Φ η).toEquiv.symm ⟨y, hy⟩, congrArg Subtype.val ((Φ η).toEquiv.apply_symm_apply _)⟩
  have hψinj : ∀ η, Function.Injective (ψ η) := fun η x x' hxx ↦
    (EquivLike.injective (Φ η)) (Subtype.ext hxx)
  set σ := Crystal.StrictHom.sigmaDesc ψ
  -- the concatenations `π_λ * η` are highest weight elements
  have hhw : ∀ η : LRIndex hA hΛ₁ hΛ₂,
      (crystal (P.pathSpace hA)).IsHighestWeight ((pathCrystalTop hA hΛ₁).1.concat η.1.1) := fun η ↦
    (concatHom hA hΛ₁ hΛ₂).isHighestWeight_apply_iff (b := (pathCrystalTop hA hΛ₁, η.1)) |>.mpr
      ((isHighestWeight_tensorPathCrystal_iff hA hΛ₁ hΛ₂ _).mpr ⟨rfl, η.2⟩)
  have hσinj : Function.Injective σ := by
    rintro ⟨η, x⟩ ⟨η', x'⟩ hxx
    change ψ η x = ψ η' x' at hxx
    have hmem : (pathCrystalTop hA hΛ₁).1.concat η'.1.1 ∈
        ((pathCrystalTop hA hΛ₁).1.concat η.1.1).component := by
      have h1 := hψmem η x
      rw [hxx] at h1
      exact Crystal.closure_singleton_subset h1
        (Crystal.mem_closure_singleton_comm (hψmem η' x'))
    obtain ⟨z, hz⟩ := hψsurj η _ hmem
    have hzhw := (ψ η).isHighestWeight_apply_iff.mp (hz ▸ hhw η')
    rw [isHighestWeight_pathCrystal_iff] at hzhw
    rw [hzhw, hψtop] at hz
    obtain rfl : η = η' := Subtype.ext (Subtype.ext (concat_injective hz).2)
    rw [hψinj η hxx]
  have hrange : Set.range (concatHom hA hΛ₁ hΛ₂) = Set.range σ := by
    apply subset_antisymm
    · rintro _ ⟨p, rfl⟩
      obtain ⟨η, hη, l, hl⟩ := exists_isHighestWeight_fWord_tensorPathCrystal hA hΛ₁ hΛ₂ p
      have h1 : concatHom hA hΛ₁ hΛ₂ p ∈ ((pathCrystalTop hA hΛ₁).1.concat η.1).component :=
        Crystal.mem_closure_of_fWord_eq_some (l := l) (by
          rw [show (pathCrystalTop hA hΛ₁).1.concat η.1 =
              concatHom hA hΛ₁ hΛ₂ (pathCrystalTop hA hΛ₁, η) from rfl,
            (concatHom hA hΛ₁ hΛ₂).fWord_apply, hl, Option.map_some])
      obtain ⟨x, hx⟩ := hψsurj ⟨η, hη⟩ _ h1
      exact ⟨⟨⟨η, hη⟩, x⟩, hx⟩
    · rintro _ ⟨⟨η, x⟩, rfl⟩
      refine Crystal.closure_subset (concatHom hA hΛ₁ hΛ₂).isStable_range
        (Set.singleton_subset_iff.mpr ⟨(pathCrystalTop hA hΛ₁, η.1), rfl⟩) (hψmem η x)
  exact ⟨(tensorPathCrystalEquiv hA hΛ₁ hΛ₂).trans
    (((crystal (P.pathSpace hA)).restrictEquivOfEq _ σ.isStable_range hrange).trans
      (Crystal.Equiv.ofInjective σ hσinj).symm)⟩

end Decomposition

end Matrix.Realization
