/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingComponent
import LieLean.RepresentationTheory.Crystal.Path.Isomorphism

/-!
# Pause-allowing reparametrization

## Main definitions and results

`PauseMap` permits nontrivial constant intervals. Precomposition intertwines the
actual root operators, including failure, and is injective on paths. This is time
change, not spatial stretching: no root letter is replaced by a power.

## References

Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), §1 p. 502, §2 p. 504, Remark 5.1 pp. 513–514. Primary scans consulted.
The continuous real-path lemma extends the source rational piecewise-linear case.
-/

open Set Module

namespace LittelmannPath

/-- A continuous nondecreasing clock fixing the endpoints; plateaus are allowed.
Surjectivity on the unit interval follows, and is not an extra premise. -/
structure PauseMap where
  toFun : ℝ → ℝ
  continuous : Continuous toFun
  monotone : Monotone toFun
  zero : toFun 0 = 0
  one : toFun 1 = 1

namespace PauseMap

variable (τ : PauseMap)

/-- Every closed interval is mapped onto its endpoint interval, including plateaus. -/
theorem image_Icc {a b : ℝ} (h : a ≤ b) :
    τ.toFun '' Icc a b = Icc (τ.toFun a) (τ.toFun b) :=
  τ.continuous.continuousOn.image_Icc_of_monotoneOn h (τ.monotone.monotoneOn _)

/-- The clock is surjective on the unit interval. -/
theorem image_unit : τ.toFun '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
  rw [τ.image_Icc zero_le_one, τ.zero, τ.one]

/-- The clock preserves membership in the unit interval. -/
theorem mem_unit {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    τ.toFun t ∈ Icc (0 : ℝ) 1 := by
  have h := mem_image_of_mem τ.toFun ht
  rwa [τ.image_unit] at h

end PauseMap

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X}
  {V : Type*} [AddCommGroup V] [Module ℝ V] {S : D.PathSpace ℝ V}

/-- Reparametrize a path by a clock that can insert pauses. -/
noncomputable def pauseReparam (τ : PauseMap) (π : LittelmannPath S) : LittelmannPath S where
  toFun t := π (τ.toFun t)
  wt := π.wt
  toFun_of_nonpos' t ht := π.apply_of_nonpos (by rw [← τ.zero]; exact τ.monotone ht)
  toFun_of_one_le' t ht := π.apply_of_one_le (by rw [← τ.one]; exact τ.monotone ht)
  continuous_coroot' i := (π.continuous_pairing i).comp τ.continuous

variable (τ : PauseMap) (π : LittelmannPath S)

/-- The literal precomposition formula. -/
theorem pauseReparam_apply (t : ℝ) : pauseReparam τ π t = π (τ.toFun t) := rfl

/-- Time change preserves the integral endpoint weight. -/
@[simp] theorem wt_pauseReparam : (pauseReparam τ π).wt = π.wt := rfl

/-- Time change does not lose path information, even though the clock can pause. -/
theorem pauseReparam_injective : Function.Injective (pauseReparam (S := S) τ) := by
  intro π η h
  apply ext_of_eqOn
  intro t ht
  rw [← τ.image_unit] at ht
  obtain ⟨u, -, rfl⟩ := ht
  exact congrArg (fun ρ : LittelmannPath S => ρ u) h

/-- Prefix minima are transported exactly, not just global minima. -/
theorem runningMin_pauseReparam (i : ι) {t : ℝ} (ht : 0 ≤ t) :
    (pauseReparam τ π).runningMin i t = π.runningMin i (τ.toFun t) := by
  have hτt : 0 ≤ τ.toFun t := by rw [← τ.zero]; exact τ.monotone ht
  rw [runningMin_eq _ ht, runningMin_eq _ hτt]
  change sInf ((fun u => π.pairing i (τ.toFun u)) '' Icc 0 t) = _
  rw [← image_image (π.pairing i) τ.toFun, τ.image_Icc ht, τ.zero]

/-- Global minima are unchanged. -/
theorem minPairing_pauseReparam (i : ι) :
    (pauseReparam τ π).minPairing i = π.minPairing i := by
  unfold minPairing
  rw [runningMin_pauseReparam τ π i zero_le_one, τ.one]

/-- Pause insertion commutes with the actual raising operator, including failure. -/
theorem e_pauseReparam (i : ι) :
    e i (pauseReparam τ π) = (e i π).map (pauseReparam τ) := by
  classical
  by_cases h : π.minPairing i ≤ -1
  · have hτ : (pauseReparam τ π).minPairing i ≤ -1 := by
      rwa [minPairing_pauseReparam]
    rw [e_of_le hτ, e_of_le h, Option.map_some]
    congr 1
    apply ext_of_eqOn
    intro t ht
    simp only [eRaw_apply, pauseReparam_apply, eCoeff,
      runningMin_pauseReparam τ π i ht.1, minPairing_pauseReparam]
  · have hτ : ¬(pauseReparam τ π).minPairing i ≤ -1 := by
      rwa [minPairing_pauseReparam]
    simp only [e, dite_eq_right hτ, dite_eq_right h, Option.map_none]

/-- Pause insertion commutes with the actual lowering operator, including failure.
The successful case uses the proved inverse relation, not a surrogate operator. -/
theorem f_pauseReparam (i : ι) :
    f i (pauseReparam τ π) = (f i π).map (pauseReparam τ) := by
  cases hf : f i π with
  | none =>
    simp only [Option.map_none]
    apply f_eq_none_iff.mpr
    have h := f_eq_none_iff.mp hf
    simpa only [minPairing_pauseReparam, pairing_one, wt_pauseReparam] using h
  | some η =>
    simp only [Option.map_some]
    apply f_eq_some_iff.mpr
    rw [e_pauseReparam, f_eq_some_iff.mp hf, Option.map_some]

/-- Both signs of the existing mixed root alphabet commute with time change. -/
theorem rootStep_pauseReparam (a : ι ⊕ ι) :
    rootStep a (pauseReparam τ π) = (rootStep a π).map (pauseReparam τ) := by
  cases a with
  | inl i => exact e_pauseReparam τ π i
  | inr i => exact f_pauseReparam τ π i

/-- All existing mixed words commute with pause insertion as Option-valued maps. -/
theorem rootWord_pauseReparam (l : List (ι ⊕ ι)) :
    rootWord l (pauseReparam τ π) = (rootWord l π).map (pauseReparam τ) := by
  induction l generalizing π with
  | nil => rfl
  | cons a l ih =>
    simp only [rootWord, rootStep_pauseReparam]
    cases rootStep a π with
    | none => rfl
    | some η => exact ih η

/-- Root-word failure is preserved in both directions. -/
theorem rootWord_pauseReparam_eq_none_iff (l : List (ι ⊕ ι)) :
    rootWord l (pauseReparam τ π) = none ↔ rootWord l π = none := by
  rw [rootWord_pauseReparam, Option.map_eq_none_iff]

/-- Every relation between mixed root words is reflected as well as preserved. -/
theorem rootWord_pauseReparam_eq_iff (u v : List (ι ⊕ ι)) :
    rootWord u (pauseReparam τ π) = rootWord v (pauseReparam τ π) ↔
      rootWord u π = rootWord v π := by
  rw [rootWord_pauseReparam, rootWord_pauseReparam]
  exact (Option.map_injective (pauseReparam_injective τ)).eq_iff

/-- Global-minimum integrality is preserved and reflected. -/
theorem isIntegral_pauseReparam_iff : (pauseReparam τ π).IsIntegral ↔ π.IsIntegral := by
  simp only [IsIntegral, minPairing_pauseReparam]

/-- Pause insertion is a strict morphism of the existing path crystal. -/
noncomputable def pauseReparamHom :
    Crystal.StrictHom (crystal S) (crystal S) where
  toFun := pauseReparam τ
  wt_map _ := rfl
  ε_map i η := by simp only [crystal, ε, minPairing_pauseReparam]
  e_map i η := e_pauseReparam τ η i
  f_map i η := f_pauseReparam τ η i

end LittelmannPath

namespace Matrix.Realization.LSGeneralClass

open LittelmannPath

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- The entire existing component, not only its endpoint, transports onto the
component of the paused path. -/
theorem image_component_pauseReparam (τ : PauseMap)
    (π : LittelmannPath (P.pathSpace hA)) :
    pauseReparam τ '' π.component = (pauseReparam τ π).component := by
  ext η
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    obtain ⟨l, hl⟩ := (mem_component_iff_rootWord π ξ).mp hξ
    apply (mem_component_iff_rootWord _ _).mpr
    exact ⟨l, by rw [rootWord_pauseReparam, hl, Option.map_some]⟩
  · intro hη
    obtain ⟨l, hl⟩ := (mem_component_iff_rootWord _ _).mp hη
    rw [rootWord_pauseReparam] at hl
    obtain ⟨ξ, hξ, rfl⟩ := Option.map_eq_some_iff.mp hl
    exact ⟨ξ, (mem_component_iff_rootWord _ _).mpr ⟨l, hξ⟩, rfl⟩

/-- The existing component crystals are isomorphic under pause insertion, not
merely in weight or character. The underlying function is literal precomposition. -/
noncomputable def pauseComponentEquiv (τ : PauseMap)
    (π : LittelmannPath (P.pathSpace hA)) :
    Crystal.Equiv π.componentCrystal (pauseReparam τ π).componentCrystal := by
  have hb : Set.BijOn (pauseReparam τ) π.component (pauseReparam τ π).component := by
    rw [← image_component_pauseReparam]
    exact ⟨mapsTo_image _ _, (pauseReparam_injective _).injOn, surjOn_image _ _⟩
  refine {
    toEquiv := hb.equiv (pauseReparam τ)
    wt_map := fun _ => rfl
    ε_map := ?_
    e_map := ?_
    f_map := ?_ }
  · intro i b
    exact (pauseReparamHom τ).ε_apply i b.1
  · intro i b
    apply Option.map_injective Subtype.val_injective
    simp only [componentCrystal, Crystal.restrict_e, Option.map_map]
    change e i (pauseReparam τ b.1) =
      Option.map (pauseReparam τ ∘ Subtype.val) (π.componentCrystal.e i b)
    rw [← Option.map_map, componentCrystal, Crystal.restrict_e]
    exact e_pauseReparam τ b.1 i
  · intro i b
    apply Option.map_injective Subtype.val_injective
    simp only [componentCrystal, Crystal.restrict_f, Option.map_map]
    change f i (pauseReparam τ b.1) =
      Option.map (pauseReparam τ ∘ Subtype.val) (π.componentCrystal.f i b)
    rw [← Option.map_map, componentCrystal, Crystal.restrict_f]
    exact f_pauseReparam τ b.1 i

/-- The component equivalence has precisely the required pointwise action. -/
theorem pauseComponentEquiv_apply (τ : PauseMap)
    (π : LittelmannPath (P.pathSpace hA)) (b : π.component) :
    (pauseComponentEquiv τ π b : LittelmannPath (P.pathSpace hA)) =
      pauseReparam τ b.1 := rfl

/-- The marked original path maps to the marked paused path. -/
theorem componentIso_pauseReparam (τ : PauseMap)
    (π : LittelmannPath (P.pathSpace hA)) : ComponentIso π (pauseReparam τ π) :=
  ⟨pauseComponentEquiv τ π, rfl⟩

/-- Component integrality is preserved and reflected by pause insertion. -/
theorem component_isIntegral_pauseReparam_iff (τ : PauseMap)
    (π : LittelmannPath (P.pathSpace hA)) :
    (∀ η ∈ (pauseReparam τ π).component, η.IsIntegral) ↔
      ∀ η ∈ π.component, η.IsIntegral := by
  rw [← image_component_pauseReparam]
  constructor
  · intro h η hη
    exact (isIntegral_pauseReparam_iff τ η).mp (h _ ⟨η, hη, rfl⟩)
  · rintro h η ⟨ξ, hξ, rfl⟩
    exact (isIntegral_pauseReparam_iff τ ξ).mpr (h ξ hξ)

/-- The explicit denominator-clearing clock of Remark 5.1. Its plateau is
`[1/n, 1-1/n]`; it changes time only, not displacement or root-letter exponents. -/
noncomputable def twoPieceClock (n : ℕ) (hn : 2 ≤ n) : PauseMap where
  toFun t := (min ((n : ℝ) * t) 1 + max ((n : ℝ) * t - (n - 1)) 0) / 2
  continuous := by fun_prop
  monotone := by
    intro a b hab
    dsimp
    gcongr
  zero := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [mul_zero, min_eq_left (by norm_num),
      max_eq_right (by linarith : (0 : ℝ) - (n - 1) ≤ 0)]
    norm_num
  one := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [mul_one, min_eq_right (by linarith),
      max_eq_left (by linarith : (0 : ℝ) ≤ n - (n - 1))]
    ring

/-- The clock's three affine formulas; in particular it genuinely permits a pause. -/
theorem twoPieceClock_regions (n : ℕ) (hn : 2 ≤ n) :
    (∀ t ≤ (n : ℝ)⁻¹, (twoPieceClock n hn).toFun t = n * t / 2) ∧
    (∀ t ∈ Icc (n : ℝ)⁻¹ (1 - (n : ℝ)⁻¹),
      (twoPieceClock n hn).toFun t = 1 / 2) ∧
    (∀ t, 1 - (n : ℝ)⁻¹ ≤ t →
      (twoPieceClock n hn).toFun t = (n * t - (n - 2)) / 2) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hni : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have hnt : (n : ℝ) * t ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left ht hp.le]
    change (min _ _ + max _ _) / 2 = _
    rw [min_eq_left hnt, max_eq_right (by linarith)]
    ring
  · intro t ht
    have hnt : 1 ≤ (n : ℝ) * t := by
      nlinarith [mul_le_mul_of_nonneg_left ht.1 hp.le]
    have hnt' : (n : ℝ) * t ≤ n - 1 := by
      nlinarith [mul_le_mul_of_nonneg_left ht.2 hp.le]
    change (min _ _ + max _ _) / 2 = _
    rw [min_eq_right hnt, max_eq_right (by linarith)]
    norm_num
  · intro t ht
    have hnt : (n : ℝ) - 1 ≤ n * t := by
      nlinarith [mul_le_mul_of_nonneg_left ht hp.le]
    change (min _ _ + max _ _) / 2 = _
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    ring

/-- The literal rational two-piece concatenation. Only the SUM must be integral:
its individual displacements need not be endpoints of integral-weight paths. -/
noncomputable def rationalConcat (Λ μ : Dual ℝ H)
    (hsum : Λ + μ ∈ P.integralWeights) : LittelmannPath (P.pathSpace hA) where
  toFun t := min (max (2 * t) 0) 1 • Λ + min (max (2 * t - 1) 0) 1 • μ
  wt := ⟨Λ + μ, hsum⟩
  toFun_of_nonpos' t ht := by
    rw [max_eq_right (by linarith : 2 * t ≤ 0),
      max_eq_right (by linarith : 2 * t - 1 ≤ 0)]
    simp
  toFun_of_one_le' t ht := by
    rw [max_eq_left (by linarith : 0 ≤ 2 * t),
      max_eq_left (by linarith : 0 ≤ 2 * t - 1),
      min_eq_right (by linarith : 1 ≤ 2 * t),
      min_eq_right (by linarith : 1 ≤ 2 * t - 1)]
    simp only [one_smul]
    rfl
  continuous_coroot' i := by
    simp only [map_add, map_smul, smul_eq_mul]
    fun_prop

/-- The two usual concatenation regions from source §1, p. 502. -/
theorem rationalConcat_regions (Λ μ : Dual ℝ H)
    (hsum : Λ + μ ∈ P.integralWeights) :
    (∀ t ∈ Icc (0 : ℝ) (1 / 2), rationalConcat (hA := hA) Λ μ hsum t =
      (2 * t) • Λ) ∧
    (∀ t ∈ Icc (1 / 2 : ℝ) 1, rationalConcat (hA := hA) Λ μ hsum t =
      Λ + (2 * t - 1) • μ) := by
  constructor
  · rintro t ⟨ht0, ht1⟩
    change min (max _ _) _ • Λ + min (max _ _) _ • μ = _
    rw [max_eq_left (by linarith : 0 ≤ 2 * t),
      min_eq_left (by linarith : 2 * t ≤ 1),
      max_eq_right (by linarith : 2 * t - 1 ≤ 0)]
    simp
  · rintro t ⟨ht0, ht1⟩
    change min (max _ _) _ • Λ + min (max _ _) _ • μ = _
    rw [max_eq_left (by linarith : 0 ≤ 2 * t),
      min_eq_right (by linarith : 1 ≤ 2 * t),
      max_eq_left (by linarith : 0 ≤ 2 * t - 1),
      min_eq_left (by linarith : 2 * t - 1 ≤ 1), one_smul]

/-- On integral individual endpoints the new constructor agrees with the
existing concatenation of straight paths, rather than introducing a new operation. -/
theorem rationalConcat_eq_concat (Λ μ : Dual ℝ H)
    (hΛ : Λ ∈ P.integralWeights) (hμ : μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) :
    rationalConcat (hA := hA) Λ μ hsum =
      (straightLine (P.pathSpace hA) ⟨Λ, hΛ⟩).concat
        (straightLine (P.pathSpace hA) ⟨μ, hμ⟩) := by
  obtain ⟨hr₁, hr₂⟩ := rationalConcat_regions (hA := hA) Λ μ hsum
  apply ext_of_eqOn
  rintro t ⟨ht0, ht1⟩
  rcases le_or_gt t (1 / 2 : ℝ) with ht | ht
  · rw [hr₁ t ⟨ht0, ht⟩, concat_apply_of_le (by simpa using ht), straightLine_apply]
    rw [min_eq_right (by linarith : 2 * t ≤ 1),
      max_eq_right (by linarith : 0 ≤ 2 * t)]
    rfl
  · rw [hr₂ t ⟨ht.le, ht1⟩, concat_apply_of_ge (by simpa using ht.le),
      apply_one, straightLine_apply]
    rw [min_eq_right (by linarith : 2 * t - 1 ≤ 1),
      max_eq_right (by linarith : 0 ≤ 2 * t - 1)]
    rfl

/-- Remark 5.1 as a literal equality of paths after the explicit pause-allowing
clock. The source rational displacements are not required to be integral. -/
theorem twoPieceGluing_eq_pauseReparam (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights)
    (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ) :
    (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).path =
      pauseReparam (twoPieceClock n hn) (rationalConcat Λ μ hsum) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hni : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnpos.ne'
  obtain ⟨hg₁, hg₂, hg₃⟩ := twoPieceGluing_regions Λ μ n hn hΛ hμ hsum hp
  obtain ⟨hc₁, hc₂, hc₃⟩ := twoPieceClock_regions n hn
  obtain ⟨hr₁, hr₂⟩ := rationalConcat_regions (hA := hA) Λ μ hsum
  apply ext_of_eqOn
  intro t ht
  rcases le_or_gt t (n : ℝ)⁻¹ with htl | htl
  · have hnt : (n : ℝ) * t ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_left htl hnpos.le]
    rw [hg₁ t ⟨ht.1, htl⟩, pauseReparam_apply, hc₁ t htl,
      hr₁ _ ⟨div_nonneg (mul_nonneg hnpos.le ht.1) (by norm_num), by linarith⟩]
    congr 1
    ring
  rcases le_or_gt t (1 - (n : ℝ)⁻¹) with htr | htr
  · rw [hg₂ t ⟨htl.le, htr⟩, pauseReparam_apply, hc₂ t ⟨htl.le, htr⟩,
      hr₁ _ ⟨by norm_num, le_rfl⟩]
    norm_num
  · have hnt : (n : ℝ) - 1 ≤ n * t := by
      nlinarith [mul_le_mul_of_nonneg_left htr.le hnpos.le]
    have hnt' : (n : ℝ) * t ≤ n := by
      nlinarith [mul_le_mul_of_nonneg_left ht.2 hnpos.le]
    rw [hg₃ t ⟨htr.le, ht.2⟩, pauseReparam_apply, hc₃ t htr.le,
      hr₂ _ ⟨by linarith, by linarith⟩]
    congr 2
    ring

/-- The denominator-cleared gluing and rational concatenation have exactly the
same mixed-word failures and relations: an equality of Option-valued outputs. -/
theorem rootWord_twoPieceGluing (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights)
    (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ)
    (l : List (ι ⊕ ι)) :
    rootWord l (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).path =
      (rootWord l (rationalConcat Λ μ hsum)).map (pauseReparam (twoPieceClock n hn)) := by
  rw [twoPieceGluing_eq_pauseReparam, rootWord_pauseReparam]

/-- The actual rational-concatenation component has the integrality property of
source §2.6, derived from constructed gluing stability and time-change transport. -/
theorem rationalConcat_component_isIntegral (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights)
    (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ) :
    ∀ η ∈ (rationalConcat (hA := hA) Λ μ hsum).component, η.IsIntegral := by
  apply (component_isIntegral_pauseReparam_iff (twoPieceClock n hn) _).mp
  rw [← twoPieceGluing_eq_pauseReparam Λ μ n hn hΛ hμ hsum hp]
  exact twoPieceGluing_component_isIntegral Λ μ n hn hΛ hμ hsum hp

/-- Pause insertion bijects the actual rational concatenation and constructed
gluing components, preserving all root edges through `pauseReparamHom`. -/
theorem rationalConcat_gluing_bijOn (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights)
    (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ) :
    Set.BijOn (pauseReparam (twoPieceClock n hn))
      (rationalConcat (hA := hA) Λ μ hsum).component
      (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).path.component := by
  rw [twoPieceGluing_eq_pauseReparam, ← image_component_pauseReparam]
  exact ⟨mapsTo_image _ _, (pauseReparam_injective _).injOn, surjOn_image _ _⟩

/-- Source Remark 5.1 at the level of the marked genuine component crystal.
This does not identify that component with the straight path of the summed weight. -/
theorem rationalConcat_componentIso_gluing (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights)
    (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ) :
    ComponentIso (rationalConcat Λ μ hsum)
      (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).path := by
  rw [twoPieceGluing_eq_pauseReparam]
  exact componentIso_pauseReparam _ _

end Matrix.Realization.LSGeneralClass
