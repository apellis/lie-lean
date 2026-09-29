/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingStability
import LieLean.RepresentationTheory.Crystal.Path.Linking

/-!
# Finite mixed-word and connected-component gluing stability

## Main results

`GluingPair.exists_rootWord_gluing` constructs strict same-cut presentations in the
ORIGINAL two Weyl orbits for every successful finite mixed root word. A single Weyl
element transports both original auxiliary directions. `exists_component_gluing`
uses the existing path crystal component, not an assumed stable set.
`component_isIntegral` derives integrality of every simple-coroot global minimum
on that component. `twoPieceGluing` constructs the actual denominator-cleared
paused path of Remark 5.1 with slopes `nΛ,nμ`; its region formulas, endpoint `Λ+μ`,
and integral connected component are proved from the source data.

## References

Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), Proposition 5.6, pp. 515–516; Definition 5.3, p. 514. Primary scans consulted.
This proves the component statement for finite rational-breakpoint presentations
with integral directions. Neither source class need be dominant. Arbitrary rational
classes modulo pause-allowing reparametrization and Proposition 5.7 are NOT asserted.
-/

open Module Set LittelmannPath

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- Existing mixed words compose in their actual left-to-right order. -/
theorem rootWord_append (u v : List (ι ⊕ ι)) (π : LittelmannPath (P.pathSpace hA)) :
    rootWord (u ++ v) π = (rootWord u π).bind (rootWord v) := by
  induction u generalizing π with
  | nil => rfl
  | cons a u ih =>
    simp only [List.cons_append, rootWord]
    cases rootStep a π with
    | none => rfl
    | some ρ => exact ih ρ

/-- The existing crystal component is precisely successful finite mixed-word
reachability. No alternate component definition or integrality premise is used. -/
theorem mem_component_iff_rootWord (π η : LittelmannPath (P.pathSpace hA)) :
    η ∈ π.component ↔ ∃ l : List (ι ⊕ ι), rootWord l π = some η := by
  constructor
  · apply Crystal.closure_subset (S := {η | ∃ l, rootWord l π = some η})
    · constructor
      · intro i ξ ζ hξ he
        obtain ⟨l, hl⟩ := hξ
        change e i ξ = some ζ at he
        exact ⟨l ++ [.inl i], by
          rw [rootWord_append, hl]
          simp only [Option.bind_some, rootWord, rootStep, he]⟩
      · intro i ξ ζ hξ hf
        obtain ⟨l, hl⟩ := hξ
        change f i ξ = some ζ at hf
        exact ⟨l ++ [.inr i], by
          rw [rootWord_append, hl]
          simp only [Option.bind_some, rootWord, rootStep, hf]⟩
    · exact singleton_subset_iff.mpr ⟨[], rfl⟩
  · rintro ⟨l, hl⟩
    have go : ∀ (l : List (ι ⊕ ι)) (ξ ζ : LittelmannPath (P.pathSpace hA)),
        ξ ∈ π.component → rootWord l ξ = some ζ → ζ ∈ π.component := by
      intro l
      induction l with
      | nil =>
        intro ξ ζ hξ h
        cases h
        exact hξ
      | cons a l ih =>
        intro ξ ζ hξ h
        obtain ⟨ρ, hρ, hz⟩ := Option.bind_eq_some_iff.mp h
        exact ih ρ ζ (rootStep_mem π.isStable_component hξ hρ) hz
    exact go l π η π.mem_component_self hl

/-- Composition of all-direction orbit witnesses retains the ORIGINAL reference
weight, rather than resetting the orbit class after each operator. -/
theorem Presentation.orbit_trans {σ τ ρ : Presentation P hA}
    (hρ : ∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (τ.x 0))
    (hτ : ∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0)) :
    ∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (σ.x 0) := by
  intro j
  obtain ⟨u, hu⟩ := hρ j
  obtain ⟨v, hv⟩ := hτ 0
  exact ⟨u * v, by rw [hu, hv, Subgroup.coe_mul, LinearEquiv.mul_apply]⟩

namespace GluingPair

variable {σ δ : Presentation P hA} (g : GluingPair σ δ)

/-- Proposition 5.6, finite-word form in the integral-direction scope: strict
same-cut output, both ORIGINAL classes, a common Weyl transport of both auxiliaries,
and integral global minima for every simple root. The only step inputs are the
unconditional constructed raising/lowering theorems. -/
theorem exists_rootWord_gluing (l : List (ι ⊕ ι))
    {η : LittelmannPath (P.pathSpace hA)} (hl : rootWord l g.path = some η) :
    ∃ (τ ρ : Presentation P hA) (g' : GluingPair τ ρ),
      g'.path = η ∧ g'.s = g.s ∧ g'.s' = g.s' ∧
      (∃ w : P.weylGroup hA, g'.ν = w.1 g.ν ∧ g'.μ = w.1 g.μ) ∧
      (∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
      (∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (δ.x 0)) ∧
      η.IsIntegral := by
  classical
  induction l generalizing σ δ η with
  | nil =>
    cases hl
    exact ⟨σ, δ, g, rfl, rfl, rfl, ⟨1, rfl, rfl⟩, σ.orbit, δ.orbit, g.isIntegral⟩
  | cons a l ih =>
    obtain ⟨ξ, ha, hl⟩ := Option.bind_eq_some_iff.mp hl
    have hstep : ∃ (τ ρ : Presentation P hA) (g' : GluingPair τ ρ),
        g'.path = ξ ∧ g'.s = g.s ∧ g'.s' = g.s' ∧
        (∃ w : P.weylGroup hA, g'.ν = w.1 g.ν ∧ g'.μ = w.1 g.μ) ∧
        (∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
        (∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (δ.x 0)) := by
      have step (i : ι) (hh :
          ∃ (τ ρ : Presentation P hA) (g' : GluingPair τ ρ),
            g'.path = ξ ∧ g'.s = g.s ∧ g'.s' = g.s' ∧
            ((g'.ν = g.ν ∧ g'.μ = g.μ) ∨
              (g'.ν = P.reflection hA i g.ν ∧ g'.μ = P.reflection hA i g.μ)) ∧
            (∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
            (∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (δ.x 0)) ∧
            ξ.IsIntegral) :
          ∃ (τ ρ : Presentation P hA) (g' : GluingPair τ ρ),
            g'.path = ξ ∧ g'.s = g.s ∧ g'.s' = g.s' ∧
            (∃ w : P.weylGroup hA, g'.ν = w.1 g.ν ∧ g'.μ = w.1 g.μ) ∧
            (∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
            (∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (δ.x 0)) := by
        obtain ⟨τ, ρ, g', hp, hs, hs', haux, hoτ, hoρ, -⟩ := hh
        refine ⟨τ, ρ, g', hp, hs, hs', ?_, hoτ, hoρ⟩
        rcases haux with haux | haux
        · exact ⟨1, haux⟩
        · exact ⟨(P.coxeterSystem hA).simple i, haux⟩
      cases a with
      | inl i => exact step i (g.exists_e_gluing ha)
      | inr i => exact step i (g.exists_f_gluing ha)
    obtain ⟨τ, ρ, g', hp, hs, hs', ⟨u, hν, hμ⟩, hoτ, hoρ⟩ := hstep
    obtain ⟨υ, ψ, g'', hp'', hs'', hs''', ⟨v, hν', hμ'⟩, hoυ, hoψ, hi⟩ :=
      ih g' (by simpa only [hp] using hl)
    refine ⟨υ, ψ, g'', hp'', hs''.trans hs, hs'''.trans hs',
      ⟨v * u, ?_, ?_⟩, Presentation.orbit_trans hoυ hoτ,
      Presentation.orbit_trans hoψ hoρ, hi⟩
    · rw [hν', hν, Subgroup.coe_mul, LinearEquiv.mul_apply]
    · rw [hμ', hμ, Subgroup.coe_mul, LinearEquiv.mul_apply]

/-- Proposition 5.6 on the genuine existing connected component, with literal
same cuts and a single common Weyl element acting on the original auxiliary pair. -/
theorem exists_component_gluing {η : LittelmannPath (P.pathSpace hA)}
    (hη : η ∈ g.path.component) :
    ∃ (τ ρ : Presentation P hA) (g' : GluingPair τ ρ),
      g'.path = η ∧ g'.s = g.s ∧ g'.s' = g.s' ∧
      (∃ w : P.weylGroup hA, g'.ν = w.1 g.ν ∧ g'.μ = w.1 g.μ) ∧
      (∀ j, ∃ w : P.weylGroup hA, (τ.x j : Dual ℝ H) = w.1 (σ.x 0)) ∧
      (∀ j, ∃ w : P.weylGroup hA, (ρ.x j : Dual ℝ H) = w.1 (δ.x 0)) ∧
      η.IsIntegral := by
  obtain ⟨l, hl⟩ := (mem_component_iff_rootWord g.path η).mp hη
  exact g.exists_rootWord_gluing l hl

/-- The entire existing component has all-simple-root global-minimum integrality;
this is a conclusion, not a stability or component-integrality input. -/
theorem component_isIntegral : ∀ η ∈ g.path.component, η.IsIntegral := by
  intro η hη
  obtain ⟨τ, ρ, g', -, -, -, -, -, -, hi⟩ := g.exists_component_gluing hη
  exact hi

end GluingPair

namespace Presentation

/-- One genuine source piece, with no LS or endpoint integrality assumption. -/
def straight (x : P.integralWeights) : Presentation P hA where
  n := 0
  a j := j.val
  x _ := x
  mono := by
    intro j k h
    change (j.val : ℚ) < (k.val : ℚ)
    exact Nat.cast_lt.mpr h
  zero := rfl
  one := rfl
  chains j := Fin.elim0 j

/-- The actual affine formula of the one-piece presentation. -/
theorem straight_path (x : P.integralWeights) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (straight (hA := hA) x).path t = t • (x : Dual ℝ H) := by
  have ha : (straight (hA := hA) x).a (0 : Fin 1).succ = 1 :=
    (straight (hA := hA) x).one
  have hmem : t ∈ Icc (0 : ℝ) ((straight (hA := hA) x).a (0 : Fin 1).succ : ℝ) := by
    rw [ha, Rat.cast_one]
    exact ht
  exact (straight (hA := hA) x).first_piece t hmem

end Presentation

/-- Positive rescaling of BOTH auxiliaries preserves the source compatibility
condition, by linearity of every actual positive-real-root coroot. -/
theorem gluingPrecedes_smul {Λ μ : Dual ℝ H} (hp : P.GluingPrecedes hA Λ μ)
    {r : ℝ} (hr : 0 < r) : P.GluingPrecedes hA (r • Λ) (r • μ) := by
  intro u j hroot hneg
  simp only [map_smul, smul_eq_mul] at hneg ⊢
  have hx := (mul_neg_iff.mp hneg).resolve_right (by rintro ⟨h, -⟩; linarith)
  exact mul_nonpos_of_nonneg_of_nonpos hr.le (hp u j hroot hx.2)

/-- The actual denominator-cleared two-piece gluing object of Remark 5.1 (p. 513).
The source compatibility, integral sum and a supplied clearing denominator are assumed.
The pieces have slopes `nΛ,nμ`, with a literal pause between `1/n` and `1-1/n`.
This constructs the object needed before Proposition 5.7; it is NOT yet an
identification modulo reparametrization with a concatenation of rational paths. -/
noncomputable def twoPieceGluing (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights)
    (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ) :
    GluingPair (Presentation.straight (hA := hA) ⟨(n : ℝ) • Λ, hΛ⟩)
      (Presentation.straight (hA := hA) ⟨(n : ℝ) • μ, hμ⟩) := by
  have hnQ : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnposQ : (0 : ℚ) < n := by linarith
  have hnposR : (0 : ℝ) < n := by linarith
  have hsinv : (n : ℚ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hnposQ (by norm_num)]
    linarith
  have hpos : (0 : ℚ) < (n : ℚ)⁻¹ := inv_pos.mpr hnposQ
  refine {
    s := (n : ℚ)⁻¹
    s' := 1 - (n : ℚ)⁻¹
    pos := hpos
    le := by linarith
    lt_one := by linarith
    last_lt := hpos
    first_gt := by change 1 - (n : ℚ)⁻¹ < 1; linarith
    ν := (n : ℝ) • Λ
    μ := (n : ℝ) • μ
    left_chain := .refl
    right_chain := .refl
    precedes := gluingPrecedes_smul hp hnposR
    endpoint := ?_ }
  have hinvR : (n : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hnposR (by norm_num)]
    linarith
  have hiposR : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hnposR
  simp only [glueRaw, Rat.cast_inv, Rat.cast_natCast, Rat.cast_sub, Rat.cast_one,
    min_eq_right (show (n : ℝ)⁻¹ ≤ 1 by linarith),
    max_eq_left (show 1 - (n : ℝ)⁻¹ ≤ 1 by linarith)]
  rw [Presentation.straight_path _ ⟨hiposR.le, by linarith⟩,
    Presentation.straight_path _ ⟨zero_le_one, le_rfl⟩,
    Presentation.straight_path _ ⟨by linarith, by linarith⟩]
  simp only [smul_smul, inv_mul_cancel₀ hnposR.ne', one_smul, one_mul]
  have heq : Λ + (n : ℝ) • μ - ((1 - (n : ℝ)⁻¹) * n) • μ = Λ + μ := by
    rw [sub_mul, one_mul, inv_mul_cancel₀ hnposR.ne']
    module
  rwa [heq]

/-- The denominator-cleared two-piece path is a genuine integral-component
consumer of Proposition 5.6, not a caller-supplied gluing or stability hypothesis. -/
theorem twoPieceGluing_component_isIntegral (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights)
    (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ) :
    ∀ η ∈ (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).path.component, η.IsIntegral :=
  (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).component_isIntegral

/-- Literal three-region geometry of the denominator-cleared two-piece path:
its two displacements are exactly `Λ` and `μ`, not their scaled multiples. -/
theorem twoPieceGluing_regions (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights)
    (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ) :
    let g := twoPieceGluing Λ μ n hn hΛ hμ hsum hp
    (∀ t ∈ Icc (0 : ℝ) (n : ℝ)⁻¹, g.path t = ((n : ℝ) * t) • Λ) ∧
    (∀ t ∈ Icc (n : ℝ)⁻¹ (1 - (n : ℝ)⁻¹), g.path t = Λ) ∧
    (∀ t ∈ Icc (1 - (n : ℝ)⁻¹) 1,
      g.path t = Λ + ((n : ℝ) * t - ((n : ℝ) - 1)) • μ) := by
  let g := twoPieceGluing Λ μ n hn hΛ hμ hsum hp
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hi : (n : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hnpos (by norm_num)]
    linarith
  have hip : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hnpos
  have hs : (g.s : ℝ) = (n : ℝ)⁻¹ := by
    change (((n : ℚ)⁻¹ : ℚ) : ℝ) = _
    push_cast
    rfl
  have hs' : (g.s' : ℝ) = 1 - (n : ℝ)⁻¹ := by
    change ((1 - (n : ℚ)⁻¹ : ℚ) : ℝ) = _
    push_cast
    rfl
  have hcut : (Presentation.straight (hA := hA) ⟨(n : ℝ) • Λ, hΛ⟩).path g.s = Λ := by
    rw [hs, Presentation.straight_path _ ⟨hip.le, by linarith⟩, smul_smul,
      inv_mul_cancel₀ hnpos.ne', one_smul]
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [g.path_left (by simpa only [hs] using ht.2),
      Presentation.straight_path _ ⟨ht.1, by linarith [ht.2]⟩, smul_smul, mul_comm]
  · intro t ht
    rw [g.path_pause (by simpa only [hs, hs'] using ht), hcut]
  · intro t ht
    rw [g.path_right (by simpa only [hs'] using ht.1), hcut,
      Presentation.straight_path _ ⟨by linarith [ht.1], ht.2⟩, hs',
      Presentation.straight_path _ ⟨by linarith, by linarith⟩]
    simp only [smul_smul]
    rw [sub_mul, one_mul, inv_mul_cancel₀ hnpos.ne']
    module

/-- The source integral endpoint is exactly the sum of the two rational
weight displacements in Remark 5.1. -/
theorem twoPieceGluing_endpoint (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights)
    (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ) :
    (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).path 1 = Λ + μ := by
  have hh := (twoPieceGluing_regions Λ μ n hn hΛ hμ hsum hp).2.2 1
    ⟨sub_le_self _ (by positivity), le_rfl⟩
  simpa only [mul_one, sub_sub_cancel, one_smul] using hh

end Matrix.Realization.LSGeneralClass
