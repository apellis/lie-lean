/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Stretching
import LieLean.RepresentationTheory.Crystal.Path.GluingLinking
import LieLean.RepresentationTheory.Crystal.Path.Decomposition

/-!
# Littelmann's isomorphism theorem for concatenations of straight lines

## Main definitions

* `splitClock s`: the clock sending `s ↦ 1/2`, affine on `[0, s]` and `[s, 1]`; with it,
  `pauseReparam (splitClock s) (π₁ * π₂)` runs through `π₁` on `[0, s]` and `π₂` on `[s, 1]`.
* `IsDominantConcat π`: `π` is built from a dominant integral straight line by repeatedly
  concatenating a straight line `π_ν` (`ν` integral) at an arbitrary split time, such that all
  vertices are dominant. These are the dominant piecewise linear paths with integral vertices.

## Main results

* `componentIso_concat_left`: [Lit95] Lemma 2.9: `B(π₁) ≅ B(π₁')` (`π₁ ↦ π₁'`) gives
  `B(π₁ * π₂) ≅ B(π₁' * π₂)` (`π₁ * π₂ ↦ π₁' * π₂`), for components with the integrality
  property; the component of `π₁ * π₂` again has the integrality property (Remark 2.8).
* `IsDominantConcat.componentIso`: **[Lit95] Theorem 7.1** for such paths `π`:
  `B(π_{π(1)}) ≅ B(π)` with `π_{π(1)} ↦ π`, by induction on the number of pieces from
  Theorem 6.3 and Lemma 2.9, as in the source.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. (2) 142
(1995), no. 3, 499–525: §2.6–2.9 (pp. 505–506) and the proof of Theorem 7.1 (pp. 518–519).
The Lean proofs are reconstructed from the library's closed root-operator formulas; paths are
compared literally, the split clocks replacing the source's reparametrization. [Lit95] works
with rational paths and a symmetrizable Kac–Moody algebra; here the time parameter is real and
the generalized Cartan matrix need not be symmetrizable.
-/

open Set Module LittelmannPath

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- [Lit95] Lemma 2.9 (p. 506), with Remark 2.8: an isomorphism `B(π₁) ≅ B(π₁')` with
`π₁ ↦ π₁'` induces `B(π₁ * π₂) ≅ B(π₁' * π₂)` with `π₁ * π₂ ↦ π₁' * π₂`, provided the three
components have the integrality property. Both new components have it again. -/
theorem componentIso_concat_left {π₁ π₁' π₂ : LittelmannPath (P.pathSpace hA)}
    (h : ComponentIso π₁ π₁') (h₁ : ∀ ρ ∈ π₁.component, ρ.IsIntegral)
    (h₁' : ∀ ρ ∈ π₁'.component, ρ.IsIntegral) (h₂ : ∀ ρ ∈ π₂.component, ρ.IsIntegral) :
    ComponentIso (π₁.concat π₂) (π₁'.concat π₂) ∧
      (∀ ρ ∈ (π₁.concat π₂).component, ρ.IsIntegral) ∧
      ∀ ρ ∈ (π₁'.concat π₂).component, ρ.IsIntegral := by
  classical
  obtain ⟨g, hmaps, hinj, hg0, hg⟩ := ComponentIso.exists_map h
  have hφ : ∀ x ∈ π₁.component, ∀ i, φ i (g x) = φ i x := by
    intro x hx i
    have e1 := (crystal (P.pathSpace hA)).φ_eq i (g x)
    have e2 := (crystal (P.pathSpace hA)).φ_eq i x
    simp only [crystal_φ, crystal_ε, crystal_wt] at e1 e2
    rw [e1, e2, (hg x hx).1, (hg x hx).2.1 i]
  have hstep : ∀ x ∈ π₁.component, ∀ y ∈ π₂.component, ∀ a : ι ⊕ ι,
      (rootStep a (x.concat y) = none ↔ rootStep a ((g x).concat y) = none) ∧
      ∀ z, rootStep a (x.concat y) = some z → ∃ x' ∈ π₁.component, ∃ y' ∈ π₂.component,
        z = x'.concat y' ∧ rootStep a ((g x).concat y) = some ((g x').concat y') := by
    intro x hx y hy a
    have hxI := h₁ x hx
    have hgxI := h₁' (g x) (hmaps hx)
    have hyI := h₂ y hy
    have hgs := (hg x hx).2.2 a
    cases a with
    | inl i =>
      change e i (g x) = (e i x).map g at hgs
      change (e i (x.concat y) = none ↔ e i ((g x).concat y) = none) ∧
        ∀ z, e i (x.concat y) = some z → ∃ x' ∈ π₁.component, ∃ y' ∈ π₂.component,
          z = x'.concat y' ∧ e i ((g x).concat y) = some ((g x').concat y')
      rw [e_concat (hxI i) (hyI i), e_concat (hgxI i) (hyI i), hφ x hx i]
      split_ifs with hc
      · rw [hgs]
        refine ⟨by simp, fun z hz => ?_⟩
        obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hz
        refine ⟨x', π₁.isStable_component.e_mem i x x' hx hx', y, hy, rfl, ?_⟩
        rw [hx']
        rfl
      · refine ⟨by simp, fun z hz => ?_⟩
        obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.mp hz
        refine ⟨x, hx, y', π₂.isStable_component.e_mem i y y' hy hy', rfl, ?_⟩
        rw [hy']
        rfl
    | inr i =>
      change f i (g x) = (f i x).map g at hgs
      change (f i (x.concat y) = none ↔ f i ((g x).concat y) = none) ∧
        ∀ z, f i (x.concat y) = some z → ∃ x' ∈ π₁.component, ∃ y' ∈ π₂.component,
          z = x'.concat y' ∧ f i ((g x).concat y) = some ((g x').concat y')
      rw [f_concat (hxI i) (hyI i), f_concat (hgxI i) (hyI i), hφ x hx i]
      split_ifs with hc
      · rw [hgs]
        refine ⟨by simp, fun z hz => ?_⟩
        obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp hz
        refine ⟨x', π₁.isStable_component.f_mem i x x' hx hx', y, hy, rfl, ?_⟩
        rw [hx']
        rfl
      · refine ⟨by simp, fun z hz => ?_⟩
        obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.mp hz
        refine ⟨x, hx, y', π₂.isStable_component.f_mem i y y' hy hy', rfl, ?_⟩
        rw [hy']
        rfl
  have hword : ∀ u : List (ι ⊕ ι), ∀ x ∈ π₁.component, ∀ y ∈ π₂.component,
      (rootWord u (x.concat y) = none ↔ rootWord u ((g x).concat y) = none) ∧
      ∀ z, rootWord u (x.concat y) = some z → ∃ x' ∈ π₁.component, ∃ y' ∈ π₂.component,
        z = x'.concat y' ∧ rootWord u ((g x).concat y) = some ((g x').concat y') := by
    intro u
    induction u with
    | nil =>
      intro x hx y hy
      refine ⟨⟨fun h => (Option.some_ne_none _ h).elim, fun h => (Option.some_ne_none _ h).elim⟩,
        fun z hz => ?_⟩
      exact ⟨x, hx, y, hy, (Option.some_injective _ hz).symm, rfl⟩
    | cons a u ih =>
      intro x hx y hy
      obtain ⟨hn, hs⟩ := hstep x hx y hy a
      change ((rootStep a (x.concat y)).bind (rootWord u) = none ↔
          (rootStep a ((g x).concat y)).bind (rootWord u) = none) ∧
        ∀ z, (rootStep a (x.concat y)).bind (rootWord u) = some z →
          ∃ x' ∈ π₁.component, ∃ y' ∈ π₂.component, z = x'.concat y' ∧
            (rootStep a ((g x).concat y)).bind (rootWord u) = some ((g x').concat y')
      cases hr : rootStep a (x.concat y) with
      | none =>
        rw [hn.mp hr]
        exact ⟨by simp, fun z hz => by simp at hz⟩
      | some w =>
        obtain ⟨x', hx', y', hy', rfl, hr'⟩ := hs _ hr
        rw [hr']
        simp only [Option.bind_some]
        exact ih x' hx' y' hy'
  have hπ₁ := π₁.mem_component_self
  have hπ₂ := π₂.mem_component_self
  have hmain := fun u => hword u π₁ hπ₁ π₂ hπ₂
  rw [hg0] at hmain
  have hwt : π₁'.wt = π₁.wt := by rw [← hg0]; exact (hg π₁ hπ₁).1
  refine ⟨componentIso_of_rootWord (by simp [wt_concat, hwt]) (fun u => (hmain u).1)
    (fun u v => ?_), ?_, ?_⟩
  · rcases hu : rootWord u (π₁.concat π₂) with _ | zu <;>
      rcases hv : rootWord v (π₁.concat π₂) with _ | zv
    · rw [(hmain u).1.mp hu, (hmain v).1.mp hv]
    · obtain ⟨x', -, y', -, -, hv'⟩ := (hmain v).2 zv hv
      rw [(hmain u).1.mp hu, hv']
      simp
    · obtain ⟨x', -, y', -, -, hu'⟩ := (hmain u).2 zu hu
      rw [(hmain v).1.mp hv, hu']
      simp
    · obtain ⟨xu, hxu, yu, -, rfl, hu'⟩ := (hmain u).2 zu hu
      obtain ⟨xv, hxv, yv, -, rfl, hv'⟩ := (hmain v).2 zv hv
      rw [hu', hv', Option.some_inj, Option.some_inj]
      constructor
      · intro heq
        obtain ⟨h1, h2⟩ := concat_injective heq
        rw [h1, h2]
      · intro heq
        obtain ⟨h1, h2⟩ := concat_injective heq
        rw [hinj hxu hxv h1, h2]
  · intro ρ hρ
    obtain ⟨u, hu⟩ := (mem_component_iff_rootWord _ _).mp hρ
    obtain ⟨x', hx', y', hy', rfl, -⟩ := (hmain u).2 ρ hu
    exact (h₁ x' hx').concat (h₂ y' hy')
  · intro ρ hρ
    obtain ⟨u, hu⟩ := (mem_component_iff_rootWord _ _).mp hρ
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp (fun hn => by
      rw [(hmain u).1.mp hn] at hu
      cases hu)
    obtain ⟨x', hx', y', hy', -, hz'⟩ := (hmain u).2 z hz
    rw [hz'] at hu
    rw [← Option.some_injective _ hu]
    exact (h₁' (g x') (hmaps hx')).concat (h₂ y' hy')

/-- The clock with plateau-free pieces `[0, s] → [0, 1/2]` and `[s, 1] → [1/2, 1]`. -/
noncomputable def splitClock (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : PauseMap where
  toFun t := min t s / (2 * s) + max (t - s) 0 / (2 * (1 - s))
  continuous := by fun_prop
  monotone := by
    intro a b hab
    have h1 : (0 : ℝ) < 2 * s := by linarith
    have h2 : (0 : ℝ) < 2 * (1 - s) := by linarith
    dsimp
    gcongr
  zero := by
    rw [min_eq_left hs0.le, max_eq_right (by linarith)]
    simp
  one := by
    rw [min_eq_right hs1.le, max_eq_left (by linarith)]
    have h1 : s / (2 * s) = 2⁻¹ := by field_simp
    have h2 : (1 - s) / (2 * (1 - s)) = 2⁻¹ := by
      have : (1 : ℝ) - s ≠ 0 := by linarith
      field_simp
    rw [h1, h2]
    norm_num

theorem splitClock_of_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {t : ℝ} (ht : t ≤ s) :
    (splitClock s hs0 hs1).toFun t = t / (2 * s) := by
  change min t s / (2 * s) + max (t - s) 0 / (2 * (1 - s)) = _
  rw [min_eq_left ht, max_eq_right (by linarith)]
  simp

theorem splitClock_of_ge {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {t : ℝ} (ht : s ≤ t) :
    (splitClock s hs0 hs1).toFun t = 2⁻¹ + (t - s) / (2 * (1 - s)) := by
  change min t s / (2 * s) + max (t - s) 0 / (2 * (1 - s)) = _
  rw [min_eq_right ht, max_eq_left (by linarith)]
  have h1 : (2 : ℝ) * s ≠ 0 := by positivity
  field_simp

/-- Dominant piecewise linear paths with integral vertices, built by concatenating straight
lines at arbitrary split times ([Lit95] §7, the paths `π_{ν₁} * ⋯ * π_{ν_s}` of the proof of
Theorem 7.1, up to reparametrization). -/
inductive IsDominantConcat : LittelmannPath (P.pathSpace hA) → Prop
  | straight (ν : P.integralWeights) (hν : (ν : Dual ℝ H) ∈ P.dominantChamber) :
      IsDominantConcat (straightLine (P.pathSpace hA) ν)
  | snoc {π : LittelmannPath (P.pathSpace hA)} (hπ : IsDominantConcat π)
      (ν : P.integralWeights)
      (hν : ((π.wt + ν : P.integralWeights) : Dual ℝ H) ∈ P.dominantChamber)
      {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
      IsDominantConcat
        (pauseReparam (splitClock s hs0 hs1) (π.concat (straightLine (P.pathSpace hA) ν)))

/-- The endpoint of a dominant concatenation is dominant. -/
theorem IsDominantConcat.wt_mem_dominantChamber {π : LittelmannPath (P.pathSpace hA)}
    (h : IsDominantConcat π) : (π.wt : Dual ℝ H) ∈ P.dominantChamber := by
  induction h with
  | straight ν hν => exact hν
  | snoc _ ν hν _ _ _ => exact hν

/-- A positive-integer multiple of an integral weight is integral. -/
theorem natCast_smul_mem_integralWeights {x : Dual ℝ H} (hx : x ∈ P.integralWeights) (n : ℕ) :
    (n : ℝ) • x ∈ P.integralWeights := by
  have h := intCast_smul_mem_integralWeights hx n
  simpa using h

/-- The component of a straight line of an arbitrary integral weight has the integrality
property (its paths are LS paths of the orbit class of `ν`). -/
theorem straightLine_component_isIntegral (ν : P.integralWeights) :
    ∀ ρ ∈ (straightLine (P.pathSpace hA) ν).component, ρ.IsIntegral := by
  have h : (Presentation.straight (hA := hA) ν).path = straightLine (P.pathSpace hA) ν := by
    apply ext_of_eqOn
    intro t ht
    rw [Presentation.straight_path _ ht, straightLine_apply, pathSpace_embed,
      min_eq_right ht.2, max_eq_right ht.1]
  rw [← h]
  exact (Presentation.straight (hA := hA) ν).component_isIntegral

/-- **[Lit95] Theorem 7.1** for dominant concatenations of straight lines with integral
vertices: `B(π_{π(1)}) ≅ B(π)` with `π_{π(1)} ↦ π`, and `B(π)` has the integrality property
([Lit95] §7 Corollary 1 a)).
The induction on the number of pieces uses Theorem 6.3 (`π_{λ+ν} ↦ π_λ * π_ν`) and
Lemma 2.9, as in the source (pp. 518–519). -/
theorem IsDominantConcat.componentIso [FiniteDimensional ℝ H]
    {π : LittelmannPath (P.pathSpace hA)} (h : IsDominantConcat π) :
    ComponentIso (straightLine (P.pathSpace hA) π.wt) π ∧
      ∀ ρ ∈ π.component, ρ.IsIntegral := by
  induction h with
  | straight ν hν =>
    exact ⟨ComponentIso.refl _, straightLine_component_isIntegral ν⟩
  | @snoc π hπ ν hν s hs0 hs1 ih =>
    obtain ⟨hiso, hint⟩ := ih
    have hLd := hπ.wt_mem_dominantChamber
    have h63 := componentIso_straightLine_rationalConcat (hA := hA) (π.wt : Dual ℝ H)
      (ν : Dual ℝ H) 2 le_rfl (natCast_smul_mem_integralWeights π.wt.2 2)
      (natCast_smul_mem_integralWeights ν.2 2) (π.wt + ν).2 hLd hν
    rw [rationalConcat_eq_concat _ _ π.wt.2 ν.2] at h63
    obtain ⟨h29, -, hI⟩ := componentIso_concat_left hiso
      (straightLine_component_isIntegral π.wt) hint (straightLine_component_isIntegral ν)
    refine ⟨(h63.trans h29).trans (componentIso_pauseReparam _ _), ?_⟩
    exact (component_isIntegral_pauseReparam_iff _ _).mpr hI

end Matrix.Realization.LSGeneralClass
