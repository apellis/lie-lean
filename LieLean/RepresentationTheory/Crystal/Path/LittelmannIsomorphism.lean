/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.ConcatIsomorphism

/-!
# Littelmann's isomorphism theorem for rational piecewise linear dominant paths

## Main definitions

* `restrictRescale Q c`: the path `t ↦ Q(c t)` (for `Q(c)` integral).

## Main results

* `isDominantConcat_of_pieces`: a path which is affine between breakpoints
  `0 = b₀ < b₁ < ⋯ < b_{m+1} = 1`, with integral dominant vertices `Q(b_j)`, is a dominant
  concatenation of straight lines (`IsDominantConcat`).
* `componentIso_straightLine_of_pieces`: **[Lit95] Theorem 7.1** for such paths.
* `componentIso_straightLine_of_rationalPieces`: **[Lit95] Theorem 7.1** for rational
  piecewise linear paths: breakpoints (real times), directions `N(Q(b_{j+1}) - Q(b_j))` integral
  for a common denominator `N`, dominant vertices and integral endpoint. This is the
  common-denominator interface: the stretched path `NQ` has integral vertices, and
  Lemma 2.5 b) descends the isomorphism back to `Q`.
* `exists_presentation_of_mem_component`: every path of `B(ν)` (`ν` integral) is the path of
  a finite presentation with rational breakpoints and integral directions (Proposition 4.7
  applied along root words).
* `lrIsomorphismHypothesis`: the instances `B(π_{λ+η(1)}) ≅ B(π_λ * η)` of Theorem 7.1 needed
  for the crystal-level Littlewood–Richardson rule, for every `λ`-dominant LS path
  `η ∈ B(μ)`.
* `nonempty_equiv_sigma_of_finiteDimensional`: the crystal-level Littlewood–Richardson
  decomposition `B(λ) ⊗ B(μ) ≅ ⊔_η B(λ + η(1))`, now unconditional (over `ℝ`, with
  finite-dimensional Cartan space).

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. (2) 142
(1995), no. 3, 499–525: Lemma 2.5 (pp. 504–505), Theorem 7.1 (p. 518) and its proof
(pp. 518–519), §10 (the Littlewood–Richardson rule). The Lean argument follows the printed
reduction: stretch to integral vertices (Lemma 2.5), then induct on the pieces
(Theorem 6.3 and Lemma 2.9). The parametrization is kept explicit instead of working modulo
reparametrization. [Lit95] works with rational paths and a symmetrizable Kac–Moody algebra;
here the time parameter is real and the generalized Cartan matrix need not be symmetrizable.
-/

open Set Module LittelmannPath

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- The rescaled initial segment `t ↦ Q(c t)` of a path, for `Q(c)` integral. -/
noncomputable def restrictRescale (Q : LittelmannPath (P.pathSpace hA)) (c : ℝ) (hc : 0 ≤ c)
    (hint : Q c ∈ P.integralWeights) : LittelmannPath (P.pathSpace hA) where
  toFun t := Q (c * min t 1)
  wt := ⟨Q c, hint⟩
  toFun_of_nonpos' t ht :=
    Q.apply_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hc ((min_le_left _ _).trans ht))
  toFun_of_one_le' t ht := by
    rw [min_eq_right ht, mul_one, pathSpace_embed]
  continuous_coroot' i :=
    (Q.continuous_pairing i).comp (continuous_const.mul (continuous_id.min continuous_const))

theorem restrictRescale_apply (Q : LittelmannPath (P.pathSpace hA)) {c : ℝ} (hc : 0 ≤ c)
    (hint : Q c ∈ P.integralWeights) (t : ℝ) :
    restrictRescale Q c hc hint t = Q (c * min t 1) := rfl

/-- A path which is affine between breakpoints `0 = b₀ < ⋯ < b_{m+1} = 1` with integral
dominant vertices is a dominant concatenation of straight lines. -/
theorem isDominantConcat_of_pieces (Q : LittelmannPath (P.pathSpace hA)) (m : ℕ)
    (b : Fin (m + 2) → ℝ) (hb : StrictMono b) (hb0 : b 0 = 0) (hb1 : b (Fin.last (m + 1)) = 1)
    (haff : ∀ j : Fin (m + 1), ∀ t ∈ Icc (b j.castSucc) (b j.succ),
      Q t = Q (b j.castSucc) +
        ((t - b j.castSucc) / (b j.succ - b j.castSucc)) • (Q (b j.succ) - Q (b j.castSucc)))
    (hint : ∀ j, Q (b j) ∈ P.integralWeights) (hdom : ∀ j, Q (b j) ∈ P.dominantChamber) :
    IsDominantConcat Q := by
  have hpos : ∀ j : Fin (m + 2), 0 ≤ b j := fun j => hb0 ▸ hb.monotone (Fin.zero_le j)
  have hQ0 : Q 0 = 0 := Q.apply_zero
  have key : ∀ j : Fin (m + 1),
      IsDominantConcat (restrictRescale Q (b j.succ) (hpos _) (hint _)) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      have h1 : (0 : ℝ) < b (0 : Fin (m + 1)).succ := by
        rw [← hb0]
        exact hb (Fin.castSucc_lt_succ (i := (0 : Fin (m + 1))))
      have heq : restrictRescale Q (b (0 : Fin (m + 1)).succ) (hpos _) (hint _) =
          straightLine (P.pathSpace hA) ⟨Q (b (0 : Fin (m + 1)).succ), hint _⟩ := by
        apply ext_of_eqOn
        intro t ht
        rw [restrictRescale_apply, straightLine_apply, pathSpace_embed, min_eq_left ht.2,
          min_eq_right ht.2, max_eq_right ht.1]
        have hh := haff 0 (b (0 : Fin (m + 1)).succ * t)
          ⟨by rw [Fin.castSucc_zero, hb0]; exact mul_nonneg h1.le ht.1,
            by nlinarith [ht.2]⟩
        rw [hh, Fin.castSucc_zero, hb0, hQ0, zero_add, sub_zero, sub_zero, sub_zero,
          mul_div_cancel_left₀ _ h1.ne']
      rw [heq]
      exact .straight _ (hdom _)
    | succ j ih =>
      set c₁ := b j.castSucc.succ with hc₁
      set c₂ := b j.succ.succ with hc₂
      have hc₁pos : 0 < c₁ := by
        rw [hc₁, ← hb0]
        exact hb (Fin.succ_pos _)
      have hc₁₂ : c₁ < c₂ := hb (Fin.succ_lt_succ_iff.mpr Fin.castSucc_lt_succ)
      have hc₂pos : 0 < c₂ := hc₁pos.trans hc₁₂
      set s := c₁ / c₂ with hs
      have hs0 : 0 < s := div_pos hc₁pos hc₂pos
      have hs1 : s < 1 := (div_lt_one hc₂pos).mpr hc₁₂
      let ν : P.integralWeights := ⟨Q c₂ - Q c₁, sub_mem (hint _) (hint _)⟩
      have haff' := haff j.succ
      have hcast : b (j.succ : Fin (m + 1)).castSucc = c₁ := by
        rw [hc₁, Fin.succ_castSucc]
      have heq : restrictRescale Q c₂ (hpos _) (hint _) =
          pauseReparam (splitClock s hs0 hs1)
            ((restrictRescale Q c₁ (hpos _) (hint _)).concat
              (straightLine (P.pathSpace hA) ν)) := by
        apply ext_of_eqOn
        intro t ht
        rw [restrictRescale_apply, min_eq_left ht.2, pauseReparam_apply]
        rcases le_total t s with hts | hts
        · rw [splitClock_of_le hs0 hs1 hts,
            concat_apply_of_le (by
              rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * s)]
              nlinarith),
            restrictRescale_apply]
          have hle : 2 * (t / (2 * s)) ≤ 1 := by
            rw [show 2 * (t / (2 * s)) = t / s by field_simp]
            exact (div_le_one hs0).mpr hts
          rw [min_eq_left hle]
          congr 1
          rw [hs]
          field_simp
        · rw [splitClock_of_ge hs0 hs1 hts,
            concat_apply_of_ge (by
              have : 0 ≤ (t - s) / (2 * (1 - s)) :=
                div_nonneg (by linarith) (by nlinarith)
              linarith),
            apply_one, straightLine_apply, pathSpace_embed, pathSpace_embed]
          have hcoef : 2 * (2⁻¹ + (t - s) / (2 * (1 - s))) - 1 = (t - s) / (1 - s) := by
            have : (1 : ℝ) - s ≠ 0 := by linarith
            field_simp
            ring
          have h01 : (t - s) / (1 - s) ∈ Icc (0 : ℝ) 1 :=
            ⟨div_nonneg (by linarith) (by linarith),
              (div_le_one (by linarith)).mpr (by linarith [ht.2])⟩
          rw [hcoef, min_eq_right h01.2, max_eq_right h01.1]
          have hmem : c₂ * t ∈ Icc (b (j.succ : Fin (m + 1)).castSucc)
              (b (j.succ : Fin (m + 1)).succ) := by
            rw [hcast]
            constructor
            · rw [hs, div_le_iff₀ hc₂pos] at hts
              linarith
            · nlinarith [ht.2]
          rw [haff' _ hmem, hcast]
          change Q c₁ + _ • (Q c₂ - Q c₁) = Q c₁ + _ • (Q c₂ - Q c₁)
          congr 2
          rw [hs, ← hc₂]
          have : c₂ - c₁ ≠ 0 := by linarith
          field_simp
      have hdomν : (((restrictRescale Q c₁ (hpos _) (hint _)).wt + ν : P.integralWeights) :
          Dual ℝ H) ∈ P.dominantChamber := by
        change Q c₁ + (Q c₂ - Q c₁) ∈ P.dominantChamber
        rw [add_sub_cancel]
        exact hdom _
      rw [heq]
      exact .snoc ih ν hdomν hs0 hs1
  have hlast := key (Fin.last m)
  have heq : restrictRescale Q (b (Fin.last m).succ) (hpos _) (hint _) = Q := by
    apply ext_of_eqOn
    intro t ht
    rw [restrictRescale_apply, min_eq_left ht.2, Fin.succ_last, hb1, one_mul]
  rwa [heq] at hlast

/-- Stretching a straight line stretches its endpoint. -/
theorem stretch_straightLine (N : ℕ) (x : P.integralWeights) :
    stretch N (straightLine (P.pathSpace hA) x) = straightLine (P.pathSpace hA) (N • x) := by
  apply ext_of_eqOn
  intro t _
  rw [stretch_apply, straightLine_apply, straightLine_apply, pathSpace_embed, pathSpace_embed,
    AddSubgroup.coe_nsmul, smul_comm]

/-- **[Lit95] Theorem 7.1** for dominant piecewise linear paths with integral vertices:
if `Q` is affine between breakpoints `0 = b₀ < ⋯ < b_{m+1} = 1` and all vertices `Q(b_j)` are
integral and dominant, then `B(π_{Q(1)}) ≅ B(Q)` with `π_{Q(1)} ↦ Q`. -/
theorem componentIso_straightLine_of_pieces [FiniteDimensional ℝ H]
    (Q : LittelmannPath (P.pathSpace hA)) (m : ℕ)
    (b : Fin (m + 2) → ℝ) (hb : StrictMono b) (hb0 : b 0 = 0) (hb1 : b (Fin.last (m + 1)) = 1)
    (haff : ∀ j : Fin (m + 1), ∀ t ∈ Icc (b j.castSucc) (b j.succ),
      Q t = Q (b j.castSucc) +
        ((t - b j.castSucc) / (b j.succ - b j.castSucc)) • (Q (b j.succ) - Q (b j.castSucc)))
    (hint : ∀ j, Q (b j) ∈ P.integralWeights) (hdom : ∀ j, Q (b j) ∈ P.dominantChamber) :
    ComponentIso (straightLine (P.pathSpace hA) Q.wt) Q :=
  (isDominantConcat_of_pieces Q m b hb hb0 hb1 haff hint hdom).componentIso.1

/-- **[Lit95] Theorem 7.1** for rational piecewise linear dominant paths, with an explicit
common denominator: if `Q` is affine between breakpoints `0 = b₀ < ⋯ < b_{m+1} = 1`, its
vertices are dominant, and `N Q(b_j)` is integral for a positive integer `N`, then
`B(π_{Q(1)}) ≅ B(Q)` with `π_{Q(1)} ↦ Q`. The stretched path `NQ` satisfies
`componentIso_straightLine_of_pieces`, and Lemma 2.5 b) descends the isomorphism. -/
theorem componentIso_straightLine_of_rationalPieces [FiniteDimensional ℝ H]
    (Q : LittelmannPath (P.pathSpace hA)) {N : ℕ} (hN : 0 < N) (m : ℕ)
    (b : Fin (m + 2) → ℝ) (hb : StrictMono b) (hb0 : b 0 = 0) (hb1 : b (Fin.last (m + 1)) = 1)
    (haff : ∀ j : Fin (m + 1), ∀ t ∈ Icc (b j.castSucc) (b j.succ),
      Q t = Q (b j.castSucc) +
        ((t - b j.castSucc) / (b j.succ - b j.castSucc)) • (Q (b j.succ) - Q (b j.castSucc)))
    (hint : ∀ j, (N : ℝ) • Q (b j) ∈ P.integralWeights)
    (hdom : ∀ j, Q (b j) ∈ P.dominantChamber) :
    ComponentIso (straightLine (P.pathSpace hA) Q.wt) Q := by
  have hS : ∀ t, stretch N Q t = (N : ℝ) • Q t := fun t => by
    rw [stretch_apply, Nat.cast_smul_eq_nsmul]
  have h := componentIso_straightLine_of_pieces (stretch N Q) m b hb hb0 hb1
    (fun j t ht => by
      rw [hS, hS, hS, haff j t ht]; module)
    (fun j => by rw [hS]; exact hint j)
    (fun j => by
      rw [hS]
      intro i
      rw [LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (Nat.cast_nonneg N) (hdom j i))
  rw [wt_stretch, ← stretch_straightLine] at h
  exact componentIso_of_componentIso_stretch hN h

/-- The one-piece presentation of `ν` has the straight line `π_ν` as its path. -/
theorem Presentation.straight_path_eq (ν : P.integralWeights) :
    (Presentation.straight (hA := hA) ν).path = straightLine (P.pathSpace hA) ν := by
  apply ext_of_eqOn
  intro t ht
  rw [Presentation.straight_path _ ht, straightLine_apply, pathSpace_embed,
    min_eq_right ht.2, max_eq_right ht.1]

/-- Root words preserve finite presentability: every path obtained from the path of a finite
presentation by root operators is again the path of a finite presentation (with rational
breakpoints and integral directions), by [Lit95] Proposition 4.7 as formalized in
`exists_f_presentation` and `exists_e_presentation`. -/
theorem Presentation.exists_of_rootWord (σ : Presentation P hA) (u : List (ι ⊕ ι))
    {ρ : LittelmannPath (P.pathSpace hA)} (h : rootWord u σ.path = some ρ) :
    ∃ τ : Presentation P hA, τ.path = ρ := by
  induction u generalizing σ with
  | nil => exact ⟨σ, Option.some_injective _ h⟩
  | cons a u ih =>
    obtain ⟨ρ₁, ha, hu⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨τ, hτ⟩ : ∃ τ : Presentation P hA, τ.path = ρ₁ := by
      cases a with
      | inl i =>
        obtain ⟨τ, hτ, -⟩ := σ.exists_e_presentation ha
        exact ⟨τ, hτ⟩
      | inr i =>
        obtain ⟨τ, hτ, -, -⟩ := σ.exists_f_presentation ha
        exact ⟨τ, hτ⟩
    subst hτ
    exact ih τ hu

/-- Every path of the component of a straight line `π_ν` (`ν` integral) is the path of a finite
presentation with rational breakpoints and integral directions. -/
theorem exists_presentation_of_mem_component (ν : P.integralWeights)
    {ρ : LittelmannPath (P.pathSpace hA)}
    (h : ρ ∈ (straightLine (P.pathSpace hA) ν).component) :
    ∃ σ : Presentation P hA, σ.path = ρ := by
  rw [← Presentation.straight_path_eq] at h
  obtain ⟨u, hu⟩ := (mem_component_iff_rootWord _ _).mp h
  exact Presentation.exists_of_rootWord _ u hu

/-- A positive common denominator of finitely many rationals. -/
theorem exists_common_denominator {n : ℕ} (a : Fin n → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ j, ∃ z : ℤ, (N : ℝ) * (a j : ℝ) = z := by
  refine ⟨∏ j, (a j).den, Finset.prod_pos fun j _ => (a j).den_pos, fun j => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j => (a j).den) (Finset.mem_univ j)
  refine ⟨k * (a j).num, ?_⟩
  have ha : ((a j : ℚ) : ℝ) = ((a j).num : ℝ) / ((a j).den : ℝ) := by
    exact_mod_cast (Rat.num_div_den (a j)).symm
  have hd : ((a j).den : ℝ) ≠ 0 := by exact_mod_cast (a j).den_pos.ne'
  rw [hk, ha]
  push_cast
  field_simp

/-- A `λ`-dominant path of `B(μ)` stays in the translated dominant chamber: `λ + η(t)` is
dominant for all `t`. The minima of `η` are integers (LS paths) exceeding `-1 - ⟨λ, αᵢ∨⟩`. -/
theorem add_apply_mem_dominantChamber_of_hitSet {Λ₁ Λ₂ : Dual ℝ H}
    (hΛ₁ : P.IsDominantIntegral Λ₁) (hΛ₂ : P.IsDominantIntegral Λ₂)
    (η : (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component)
    (hη : η.1.hitSet (Matrix.Realization.shiftLevel hA hΛ₁) = ∅)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Λ₁ + η.1 t ∈ P.dominantChamber := by
  intro i
  obtain ⟨n, hn⟩ := Matrix.Realization.isIntegral_of_mem_pathCrystal hA hΛ₂ η i
  have hlt : ¬η.1.minPairing i ≤ (Matrix.Realization.shiftLevel hA hΛ₁ i : ℝ) := fun h =>
    (Set.nonempty_iff_ne_empty.mp (hitSet_nonempty h)) hη
  obtain ⟨M, hM⟩ := hΛ₁ i
  rw [hn, Matrix.Realization.shiftLevel_cast, hM, not_le] at hlt
  have h1 : -(M : ℤ) ≤ n := by
    have : ((-1 - (M : ℤ) : ℤ) : ℝ) < n := by push_cast; linarith
    have : -1 - (M : ℤ) < n := by exact_mod_cast this
    omega
  have h2 := η.1.minPairing_le (i := i) ht
  simp only [pairing, pathSpace_coroot] at h2
  rw [hn] at h2
  have h1' : -(M : ℝ) ≤ n := by exact_mod_cast h1
  rw [LinearMap.add_apply, hM]
  linarith

/-- **The instances of Littelmann's Theorem 7.1 needed for the crystal-level
Littlewood–Richardson rule** ([Lit95] Theorem 7.1 and §10): for dominant integral `λ, μ` and
every `λ`-dominant LS path `η ∈ B(μ)`, `B(π_{λ + η(1)}) ≅ B(π_λ * η)` with
`π_{λ+η(1)} ↦ π_λ * η`. The path `η` is presented with rational breakpoints and integral
directions (`exists_presentation_of_mem_component`), a common denominator of the breakpoints
is chosen, and `componentIso_straightLine_of_rationalPieces` applies. -/
theorem lrIsomorphismHypothesis [FiniteDimensional ℝ H] {Λ₁ Λ₂ : Dual ℝ H}
    (hΛ₁ : P.IsDominantIntegral Λ₁) (hΛ₂ : P.IsDominantIntegral Λ₂) :
    Matrix.Realization.LRIsomorphismHypothesis hA hΛ₁ hΛ₂ := by
  intro η
  set ρ := η.1.1 with hρ
  obtain ⟨σ, hσ⟩ := exists_presentation_of_mem_component _ η.1.2
  have hσ' : σ.path = ρ := hσ
  have hdomρ : ∀ t ∈ Icc (0 : ℝ) 1, Λ₁ + ρ t ∈ P.dominantChamber := fun t ht =>
    add_apply_mem_dominantChamber_of_hitSet hΛ₁ hΛ₂ η.1 η.2 ht
  obtain ⟨N, hN, hNa⟩ := exists_common_denominator σ.a
  set πΛ := straightLine (P.pathSpace hA) ⟨Λ₁, hΛ₁.mem_integralWeights⟩ with hπΛ
  set Q := πΛ.concat ρ with hQ
  let b : Fin (σ.n + 3) → ℝ := Fin.cons 0 fun j => (1 + (σ.a j : ℝ)) / 2
  have hb0 : b 0 = 0 := rfl
  have hbs : ∀ j : Fin (σ.n + 2), b j.succ = (1 + (σ.a j : ℝ)) / 2 := fun j => rfl
  have ha0 : (σ.a 0 : ℝ) = 0 := by rw [σ.zero]; simp
  have ha1 : (σ.a (Fin.last (σ.n + 1)) : ℝ) = 1 := by rw [σ.one]; simp
  have hamono : StrictMono fun j => (σ.a j : ℝ) := fun i j hij => by
    change (σ.a i : ℝ) < σ.a j
    exact_mod_cast σ.mono hij
  have hanonneg : ∀ j, 0 ≤ (σ.a j : ℝ) := fun j => by
    rw [← ha0]; exact hamono.monotone (Fin.zero_le j)
  have hale1 : ∀ j, (σ.a j : ℝ) ≤ 1 := fun j => by
    rw [← ha1]; exact hamono.monotone (Fin.le_last j)
  have hb : StrictMono b := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    induction i using Fin.cases with
    | zero =>
      rw [Fin.castSucc_zero, hb0, hbs, ha0]
      norm_num
    | succ k =>
      rw [← Fin.succ_castSucc, hbs, hbs]
      have := hamono (Fin.castSucc_lt_succ (i := k))
      linarith
  have hb1 : b (Fin.last (σ.n + 2)) = 1 := by
    rw [← Fin.succ_last, hbs, ha1]
    norm_num
  -- Values of `Q`.
  have hQl : ∀ t ∈ Icc (0 : ℝ) 2⁻¹, Q t = (2 * t) • Λ₁ := by
    intro t ht
    rw [hQ, concat_apply_of_le ht.2, hπΛ, straightLine_apply, pathSpace_embed,
      min_eq_right (by linarith [ht.2]), max_eq_right (by linarith [ht.1])]
  have hQr : ∀ t, 2⁻¹ ≤ t → Q t = Λ₁ + ρ (2 * t - 1) := by
    intro t ht
    rw [hQ, concat_apply_of_ge ht, hπΛ, apply_one, pathSpace_embed]
    rfl
  have hQb : ∀ j : Fin (σ.n + 2), Q (b j.succ) = Λ₁ + ρ (σ.a j) := by
    intro j
    rw [hbs, hQr _ (by linarith [hanonneg j])]
    congr 2
    ring
  have hQ0 : Q (b 0) = 0 := by rw [hb0]; exact Q.apply_zero
  -- `N ρ(a_j)` is integral.
  have hρint : ∀ j : Fin (σ.n + 2), (N : ℝ) • ρ (σ.a j) ∈ P.integralWeights := by
    intro j
    induction j using Fin.lastCases with
    | last =>
      rw [ha1, ← hσ', σ.path.apply_one, pathSpace_embed]
      exact natCast_smul_mem_integralWeights σ.path.wt.2 N
    | cast k =>
      have hc := σ.congruence k (σ.a k.castSucc) ⟨le_rfl, by
        exact_mod_cast σ.mono.monotone Fin.castSucc_lt_succ.le⟩
      have hr := LSAChainBridge.rootLattice_le_integralWeights hc
      obtain ⟨z, hz⟩ := hNa k.castSucc
      have hsplit : (N : ℝ) • ρ (σ.a k.castSucc) =
          (N : ℝ) • (σ.path (σ.a k.castSucc) - (σ.a k.castSucc : ℝ) • (σ.x k : Dual ℝ H)) +
            (z : ℝ) • (σ.x k : Dual ℝ H) := by
        rw [← hz, ← hσ', smul_sub, smul_smul]
        abel
      rw [hsplit]
      exact add_mem (natCast_smul_mem_integralWeights hr N)
        (intCast_smul_mem_integralWeights (σ.x k).2 z)
  have hiso := componentIso_straightLine_of_rationalPieces Q hN (σ.n + 1) b hb hb0 hb1
    (fun j t ht => by
      induction j using Fin.cases with
      | zero =>
        rw [Fin.castSucc_zero, hb0, Fin.succ_zero_eq_one', hQ0] at *
        have hb1' : b 1 = 2⁻¹ := by
          rw [show (1 : Fin (σ.n + 3)) = (0 : Fin (σ.n + 2)).succ from rfl, hbs, ha0]
          norm_num
        rw [hb1'] at ht ⊢
        rw [hQl t ht, hQl 2⁻¹ ⟨by norm_num, le_rfl⟩]
        simp only [sub_zero, zero_add]
        rw [smul_smul]
        congr 1
        field_simp
      | succ k =>
        rw [← Fin.succ_castSucc] at ht ⊢
        rw [hQb, hQb]
        rw [hbs, hbs] at ht ⊢
        have hk1 : (σ.a k.castSucc : ℝ) < σ.a k.succ := hamono Fin.castSucc_lt_succ
        have hu : 2 * t - 1 ∈ Icc (σ.a k.castSucc : ℝ) (σ.a k.succ : ℝ) :=
          ⟨by linarith [ht.1], by linarith [ht.2]⟩
        rw [hQr t (by linarith [ht.1, hanonneg k.castSucc]), ← hσ', σ.piece k _ hu,
          σ.piece k _ ⟨le_rfl, hk1.le⟩, σ.piece k _ ⟨hk1.le, le_rfl⟩]
        have hne : (σ.a k.succ : ℝ) - σ.a k.castSucc ≠ 0 := by linarith
        have hcoef : (t - (1 + (σ.a k.castSucc : ℝ)) / 2) /
            ((1 + (σ.a k.succ : ℝ)) / 2 - (1 + (σ.a k.castSucc : ℝ)) / 2) *
            ((σ.a k.succ : ℝ) - σ.a k.castSucc) = 2 * t - 1 - σ.a k.castSucc := by
          rw [show (1 + (σ.a k.succ : ℝ)) / 2 - (1 + (σ.a k.castSucc : ℝ)) / 2 =
            ((σ.a k.succ : ℝ) - σ.a k.castSucc) / 2 by ring]
          field_simp
          ring
        rw [← hcoef]
        module)
    (fun j => by
      induction j using Fin.cases with
      | zero => rw [hQ0, smul_zero]; exact zero_mem _
      | succ k =>
        rw [hQb, smul_add]
        exact add_mem (natCast_smul_mem_integralWeights hΛ₁.mem_integralWeights N)
          (hρint k))
    (fun j => by
      induction j using Fin.cases with
      | zero => rw [hQ0]; intro i; simp
      | succ k =>
        rw [hQb]
        exact hdomρ _ ⟨hanonneg k, hale1 k⟩)
  convert hiso using 2
  exact Subtype.ext rfl

/-- **The crystal-level Littlewood–Richardson rule** ([Lit95] §10), now unconditional:
`B(λ) ⊗ B(μ) ≅ ⊔_{η ∈ B(μ) λ-dominant} B(λ + η(1))`, with `π_λ ⊗ η ↦ π_{λ + η(1)}`, for
dominant integral `λ, μ` of any generalized Cartan matrix over `ℝ`, with finite-dimensional
Cartan space. The hypothesis of `nonempty_equiv_sigma` is `lrIsomorphismHypothesis`. -/
theorem nonempty_equiv_sigma_of_finiteDimensional [FiniteDimensional ℝ H] {Λ₁ Λ₂ : Dual ℝ H}
    (hΛ₁ : P.IsDominantIntegral Λ₁) (hΛ₂ : P.IsDominantIntegral Λ₂) :
    Nonempty (Crystal.Equiv (Matrix.Realization.tensorPathCrystal hA hΛ₁ hΛ₂)
      (Crystal.sigma (Matrix.Realization.lrCrystal hA hΛ₁ hΛ₂))) :=
  Matrix.Realization.nonempty_equiv_sigma hA hΛ₁ hΛ₂ (lrIsomorphismHypothesis hΛ₁ hΛ₂)

end Matrix.Realization.LSGeneralClass
