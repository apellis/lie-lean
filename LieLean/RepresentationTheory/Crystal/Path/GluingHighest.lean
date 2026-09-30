/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingFibre

/-!
# Highest paths in the original endpoint fibre of a two-piece gluing

Let `Λ` be a dominant weight and `Λ + μ` a dominant weight, and let `π` be the
denominator-cleared two-piece gluing `π_{nΛ}^{1/n} ∘ θ ∘ π_{nμ, 1-1/n}` of
Remark 5.1 (`twoPieceGluing`). Proposition 5.7 of [Lit95] asserts that `π` is the
only path `π'` in its connected component `Aπ` with `π'(1) = Λ + μ` and `e_α π' = 0`
for all simple roots `α`.

## Main results

* `AChain.eq_of_mem_dominantChamber`, `Presentation.directions_eq_of_mem_dominantChamber`:
  a source chain starting at a dominant weight, and a finite presentation whose first
  direction is dominant, are constant (first-source straightness).
* `AChain.reflection_of_neg_of_nonneg`: Lemma 4.3 in the form used on p. 516: a chain
  `m → x` with `⟨m, α∨⟩ < 0 ≤ ⟨x, α∨⟩` gives a chain `s_α m → x` at the same time.
* `AChain.exists_stabilizer_normal`: the printed length reduction `s_α w < w`: inside
  the stabilizer of a dominant weight, the initial weight of a chain can be moved until
  it is dominant for all simple roots fixing that weight.
* `apply_eq_self_of_stabilizer_of_add_mem_dominantChamber`: such a normalized weight is
  the original one, when `Λ` and `Λ + μ` are dominant.
* `gluingPrecedes_of_mem_dominantChamber`: a dominant weight precedes every weight
  (p. 514), so the compatibility hypothesis of `twoPieceGluing` is automatic here.
* `twoPieceGluing_eq_of_mem_component`: a highest path in the component of the two-piece
  gluing with the original endpoint is the two-piece gluing itself.
* `twoPieceGluing_e_eq_none`: the two-piece gluing is itself highest.
* `twoPieceGluing_highest_iff`: **Proposition 5.7**, second assertion: `π` is the only
  path `π'` in `Aπ` with `π'(1) = Λ + μ` and `e_α π' = 0` for all simple roots. The first
  assertion is `twoPieceGluing_component_isIntegral`.

## Implementation notes

The printed proof fixes the gluing pair `(nλ, w(nμ))` with `w ∈ W_λ` and then replaces
`w` by `s_α w` while `⟨w(μ), α∨⟩ < 0`, for simple `α` with `⟨λ, α∨⟩ = 0`. We carry out
the same reduction on the source chain `w(nμ) → ν'₁` alone; termination is by the
integral increase of `ρ̌`, not by the Bruhat length, and the final equality
`w(nμ) = nμ` uses uniqueness of dominant representatives applied to `N nλ + nμ` for
large `N`, instead of the parabolic subgroup `W_λ`. The gluing-pair compatibility of the
reduced auxiliaries (`nλ ▷ s_α w(nμ)` in the source) is not needed for the conclusion.
Highestness is used only through integrality of the component
(`GluingPair.exists_component_gluing`), which turns `e_α π' = 0` into `π' ∈ P⁺`.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), Proposition 5.7 and its proof, printed p. 516; Lemma 4.3 (p. 509 (check)) and
Corollary 3 (p. 512). The printed pages 512–516 were consulted. The argument above is
the printed one with the reconstructed modifications recorded in the implementation notes.
-/

open Module Set LittelmannPath

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  [FiniteDimensional ℝ H] {A : Matrix ι ι ℤ} {P : Realization A ℝ H}
  {hA : A.IsGeneralizedCartan}

/-- A dominant weight maximizes `ρ̌` on its Weyl orbit. -/
theorem apply_rhoCheck_le_of_mem_dominantChamber {x : Dual ℝ H}
    (hx : x ∈ P.dominantChamber) (w : P.weylGroup hA) :
    w.1 x P.rhoCheck ≤ x P.rhoCheck := by
  obtain ⟨c, hc, he⟩ := P.exists_nonneg_sub_apply_eq_sum hA hx w.2
  have h := congrArg (fun z : Dual ℝ H => z P.rhoCheck) he
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, root_rhoCheck,
    smul_eq_mul, mul_one] at h
  have : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  linarith

/-- A source chain out of a dominant weight is constant: the chain strictly increases
`ρ̌` unless it is trivial, and stays in the orbit, where the dominant weight is maximal. -/
theorem AChain.eq_of_mem_dominantChamber {x y : Dual ℝ H} {a : ℝ}
    (h : AChain P hA a x y) (hx : x ∈ P.dominantChamber) : y = x := by
  obtain ⟨w, hw⟩ := h.eq_weyl
  rcases h.eq_or_rhoCheck_lt with he | hl
  · exact he.symm
  · have := apply_rhoCheck_le_of_mem_dominantChamber (hA := hA) hx w
    rw [← hw] at this
    linarith

/-- First-source straightness ([Lit95] Corollary 3, p. 512, as used on p. 516): if the
first direction of a finite source presentation is dominant, all directions equal it. -/
theorem Presentation.directions_eq_of_mem_dominantChamber (σ : Presentation P hA)
    (h0 : (σ.x 0 : Dual ℝ H) ∈ P.dominantChamber) (j : Fin (σ.n + 1)) :
    (σ.x j : Dual ℝ H) = σ.x 0 := by
  obtain ⟨w, hw⟩ := σ.orbit j
  rcases σ.aux_eq_or_rhoCheck_lt (μ := σ.x 0) (s := 0) .refl j with he | hl
  · exact he.symm
  · have := apply_rhoCheck_le_of_mem_dominantChamber (hA := hA) h0 w
    rw [← hw] at this
    linarith

omit [FiniteDimensional ℝ H] in
/-- [Lit95] Lemma 4.3 (check), in the form used in the proof of Proposition 5.7: a chain
from `m` to `x` with `⟨m, α∨⟩ < 0 ≤ ⟨x, α∨⟩` yields a chain from `s_α m` to `x` at the
same time. The first crossing step is `s_α` (Corollary 1); earlier steps are reflected. -/
theorem AChain.reflection_of_neg_of_nonneg {a : ℝ} {m x : Dual ℝ H} {i : ι}
    (h : AChain P hA a m x) (hint : m ∈ P.integralWeights)
    (hm : m (P.coroot i) < 0) (hx : 0 ≤ x (P.coroot i)) :
    AChain P hA a (P.reflection hA i m) x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => linarith
  | @head m z hmz hzx ih =>
    obtain ⟨c, hc, k, hk⟩ := hmz
    rcases lt_or_ge (z (P.coroot i)) 0 with hz | hz
    · refine Relation.ReflTransGen.head ⟨c ∘ₗ (P.reflection hA i).toLinearMap,
        hc.reflection_neg hint hm hz, k, ?_⟩ (ih (hc.1.integral_end hint) hz)
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, reflection_reflection] using hk
    · obtain ⟨-, rfl⟩ := hc.crossing (Or.inr ⟨hm, hz⟩)
      exact hzx

/-- The stabilizer reduction in the proof of Proposition 5.7 (p. 516). Let `Λ` be dominant,
`x` nonnegative on every simple coroot vanishing on `Λ`, and `u(m₀) → x` a chain with `u`
fixing `Λ`. Then some `v` fixing `Λ` gives a chain `v(m₀) → x` with `v(m₀)` nonnegative on
all those coroots. Each step replaces `u` by `s_α u` as in the source. -/
theorem AChain.exists_stabilizer_normal {a : ℝ} {Λ x m₀ : Dual ℝ H}
    (hm₀ : m₀ ∈ P.integralWeights)
    (hx : ∀ i, Λ (P.coroot i) = 0 → 0 ≤ x (P.coroot i))
    {u : P.weylGroup hA} (hu : u.1 Λ = Λ) (h : AChain P hA a (u.1 m₀) x) :
    ∃ v : P.weylGroup hA, v.1 Λ = Λ ∧ AChain P hA a (v.1 m₀) x ∧
      ∀ i, Λ (P.coroot i) = 0 → 0 ≤ v.1 m₀ (P.coroot i) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (x P.rhoCheck - u.1 m₀ P.rhoCheck)
  induction N generalizing u with
  | zero =>
    exfalso
    rcases h.eq_or_rhoCheck_lt with he | hl
    · rw [he] at hN
      simp at hN
    · simp only [Nat.cast_zero] at hN
      linarith
  | succ N ih =>
    by_cases hall : ∀ i, Λ (P.coroot i) = 0 → 0 ≤ u.1 m₀ (P.coroot i)
    · exact ⟨u, hu, h, hall⟩
    · push Not at hall
      obtain ⟨i, hi, hneg⟩ := hall
      have hint : u.1 m₀ ∈ P.integralWeights := fun j => exists_int_apply_coroot hm₀ u j
      have h' := h.reflection_of_neg_of_nonneg hint hneg (hx i hi)
      obtain ⟨z, hz⟩ := hint i
      have hz1 : (z : ℝ) ≤ -1 := by
        have : z < 0 := by exact_mod_cast hz ▸ hneg
        exact_mod_cast (show z ≤ -1 by omega)
      have hρ : P.reflection hA i (u.1 m₀) P.rhoCheck =
          u.1 m₀ P.rhoCheck - u.1 m₀ (P.coroot i) := by
        rw [reflection_apply]
        simp
      refine ih (u := (P.coxeterSystem hA).simple i * u) ?_ ?_ ?_
      · rw [coe_simple_mul_apply, hu, reflection_apply, hi, zero_smul, sub_zero]
      · rwa [coe_simple_mul_apply]
      · rw [coe_simple_mul_apply]
        push_cast at hN
        linarith

omit [FiniteDimensional ℝ H] in
/-- The final normalization in the proof of Proposition 5.7 (p. 516). If `Λ` and `Λ + μ`
are dominant, `v` fixes `Λ`, and `v μ` is nonnegative on every simple coroot vanishing
on `Λ`, then `v μ = μ`. Reconstructed: `N Λ + μ` and `v (N Λ + μ) = N Λ + v μ` are both
dominant for large `N`, so they coincide. -/
theorem apply_eq_self_of_stabilizer_of_add_mem_dominantChamber {Λ μ : Dual ℝ H}
    (hΛ : Λ ∈ P.dominantChamber) (hΛμ : Λ + μ ∈ P.dominantChamber)
    {v : P.weylGroup hA} (hv : v.1 Λ = Λ)
    (hm : ∀ i, Λ (P.coroot i) = 0 → 0 ≤ v.1 μ (P.coroot i)) : v.1 μ = μ := by
  set S : ℝ := ∑ i, |v.1 μ (P.coroot i)| / Λ (P.coroot i) with hS
  have hterm (i : ι) : 0 ≤ |v.1 μ (P.coroot i)| / Λ (P.coroot i) :=
    div_nonneg (abs_nonneg _) (hΛ i)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hterm i
  have hd1 : (1 + S) • Λ + μ ∈ P.dominantChamber := by
    intro i
    have h1 := hΛ i
    have h2 := hΛμ i
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h2 ⊢
    nlinarith [mul_nonneg hS0 h1]
  have hd2 : v.1 ((1 + S) • Λ + μ) ∈ P.dominantChamber := by
    rw [map_add, map_smul, hv]
    intro i
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le (hΛ i) with h0 | hpos
    · rw [← h0, mul_zero, zero_add]
      exact hm i h0.symm
    · have hle : |v.1 μ (P.coroot i)| / Λ (P.coroot i) ≤ S :=
        Finset.single_le_sum (f := fun j => |v.1 μ (P.coroot j)| / Λ (P.coroot j))
          (fun j _ => hterm j) (Finset.mem_univ i)
      have hmul : |v.1 μ (P.coroot i)| ≤ S * Λ (P.coroot i) := (div_le_iff₀ hpos).mp hle
      nlinarith [neg_abs_le (v.1 μ (P.coroot i))]
  have h := P.apply_eq_self_of_mem_dominantChamber hA hd1 v.2 hd2
  rw [map_add, map_smul, hv] at h
  exact add_left_cancel h

omit [FiniteDimensional ℝ H] in
/-- On an integral path, vanishing of every raising operator means the path stays in the
dominant chamber: the integral minimum exceeds `-1`, hence is nonnegative. -/
theorem apply_coroot_nonneg_of_e_eq_none {η : LittelmannPath (P.pathSpace hA)}
    (hη : η.IsIntegral) (he : ∀ i, LittelmannPath.e i η = none) (i : ι) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ (η t) (P.coroot i) := by
  have hm : -1 < η.minPairing i := e_eq_none_iff.mp (he i)
  obtain ⟨z, hz⟩ := hη i
  rw [hz] at hm
  have hz0 : (0 : ℝ) ≤ z := by
    have : (-1 : ℤ) < z := by exact_mod_cast hm
    exact_mod_cast (show (0 : ℤ) ≤ z by omega)
  have h := η.minPairing_le (i := i) ht
  rw [hz] at h
  simpa only [pairing, pathSpace_coroot] using hz0.trans h

/-- **Proposition 5.7** of [Lit95] (p. 516), uniqueness part, for the two-piece gluing
`π = π_{nΛ}^{1/n} ∘ θ ∘ π_{nμ,1-1/n}` of Remark 5.1 (`twoPieceGluing`). If `Λ` and
`Λ + μ` are dominant, every path `π'` in the connected component of `π` with
`π'(1) = Λ + μ` and `e_α π' = 0` for all simple roots is equal to `π`.

The weights are real; the denominator `n` with `nΛ, nμ` integral and `Λ + μ` integral is
the rational-weight hypothesis of the source. The compatibility `Λ ▷ μ` is a hypothesis of
`twoPieceGluing`; it holds automatically for dominant `Λ` in the source. -/
theorem twoPieceGluing_eq_of_mem_component (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights) (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ)
    (hΛd : Λ ∈ P.dominantChamber) (hνd : Λ + μ ∈ P.dominantChamber)
    {η : LittelmannPath (P.pathSpace hA)}
    (hη : η ∈ (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).path.component)
    (he : ∀ i, LittelmannPath.e i η = none) (hend : η 1 = Λ + μ) :
    η = (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).path := by
  set g := twoPieceGluing Λ μ n hn hΛ hμ hsum hp with hg
  obtain ⟨τ, ρ, g', hpath, hs, hs', ⟨w, hν, hμw⟩, hoτ, -, hint⟩ :=
    g.exists_component_gluing hη
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hgs : g.s = (n : ℚ)⁻¹ := rfl
  have hgs' : g.s' = 1 - (n : ℚ)⁻¹ := rfl
  have hsr : (g'.s : ℝ) = (n : ℝ)⁻¹ := by
    rw [hs, hgs, Rat.cast_inv, Rat.cast_natCast]
  have hs'r : (g'.s' : ℝ) = 1 - (n : ℝ)⁻¹ := by
    rw [hs', hgs', Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast]
  have hdom : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i, 0 ≤ (η t) (P.coroot i) :=
    fun t ht i => apply_coroot_nonneg_of_e_eq_none hint he i ht
  have hsmul (x : Dual ℝ H) (hx : x ∈ P.dominantChamber) :
      (n : ℝ) • x ∈ P.dominantChamber := fun i => by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg hnpos.le (hx i)
  have hnΛd := hsmul Λ hΛd
  -- First-source straightness: the first direction is dominant, hence `nΛ`.
  have hτ0 : (τ.x 0 : Dual ℝ H) ∈ P.dominantChamber := by
    have hs0 : (0 : ℝ) < g'.s := by exact_mod_cast g'.pos
    have ha1 : (0 : ℝ) < τ.a (0 : Fin (τ.n + 1)).succ := by
      have h := τ.mono (Fin.castSucc_lt_succ (i := (0 : Fin (τ.n + 1))))
      have h0 : τ.a (0 : Fin (τ.n + 1)).castSucc = 0 := τ.zero
      rw [h0] at h
      exact_mod_cast h
    set t₀ : ℝ := min (g'.s : ℝ) (τ.a (0 : Fin (τ.n + 1)).succ : ℝ) with ht₀
    have ht0 : 0 < t₀ := lt_min hs0 ha1
    have ht1 : t₀ ≤ 1 :=
      (min_le_left _ _).trans (by exact_mod_cast g'.le.trans g'.lt_one.le)
    have heq : η t₀ = t₀ • (τ.x 0 : Dual ℝ H) := by
      rw [← hpath, g'.path_left (min_le_left _ _),
        τ.first_piece t₀ ⟨ht0.le, min_le_right _ _⟩]
    intro i
    have h := hdom t₀ ⟨ht0.le, ht1⟩ i
    rw [heq, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_nonneg_iff_of_pos_left ht0).mp h
  have hτx0 : (τ.x 0 : Dual ℝ H) = (n : ℝ) • Λ := by
    obtain ⟨u, hu⟩ := hoτ 0
    exact (P.eq_of_apply_eq_of_mem_dominantChamber hA hnΛd hτ0 u.2 hu.symm).symm
  have hτall : ∀ j, (τ.x j : Dual ℝ H) = (n : ℝ) • Λ := fun j =>
    (τ.directions_eq_of_mem_dominantChamber hτ0 j).trans hτx0
  -- The left auxiliary is `nΛ`, so the common Weyl element fixes `nΛ`.
  have hν' : g'.ν = (n : ℝ) • Λ :=
    (g'.left_chain.eq_of_mem_dominantChamber (by rw [hτall]; exact hnΛd)).trans (hτall _)
  have hwΛ : w.1 ((n : ℝ) • Λ) = (n : ℝ) • Λ := by
    have h := hν
    rw [hν'] at h
    exact h.symm
  have hcut : τ.path g'.s = Λ := by
    rw [τ.path_eq_smul_of_directions_eq hτall
      ⟨by exact_mod_cast g'.pos.le, by exact_mod_cast g'.le.trans g'.lt_one.le⟩,
      hsr, smul_smul, inv_mul_cancel₀ hnpos.ne', one_smul]
  -- The first right direction is dominant for the simple roots fixing `Λ`.
  have hx1 : ∀ i, ((n : ℝ) • Λ) (P.coroot i) = 0 →
      0 ≤ (ρ.x 0 : Dual ℝ H) (P.coroot i) := by
    intro i hi
    have hi' : Λ (P.coroot i) = 0 := by
      simp only [LinearMap.smul_apply, smul_eq_mul] at hi
      exact (mul_eq_zero.mp hi).resolve_left hnpos.ne'
    have hst : (g'.s' : ℝ) < (ρ.a (0 : Fin (ρ.n + 1)).succ : ℝ) := by
      exact_mod_cast g'.first_gt
    have ht1 : (ρ.a (0 : Fin (ρ.n + 1)).succ : ℝ) ≤ 1 := by
      have h := ρ.mono.monotone (Fin.le_last (0 : Fin (ρ.n + 1)).succ)
      rw [ρ.one] at h
      exact_mod_cast h
    set t₁ : ℝ := (ρ.a (0 : Fin (ρ.n + 1)).succ : ℝ) with ht₁
    have hs'0 : (0 : ℝ) ≤ g'.s' := by exact_mod_cast g'.pos.le.trans g'.le
    have heq : η t₁ = Λ + (t₁ - g'.s') • (ρ.x 0 : Dual ℝ H) := by
      rw [← hpath, g'.path_right hst.le, hcut, ρ.first_piece t₁ ⟨hs'0.trans hst.le, le_rfl⟩,
        ρ.first_piece _ g'.right_cut_mem]
      module
    have h := hdom t₁ ⟨hs'0.trans hst.le, ht1⟩ i
    rw [heq, LinearMap.add_apply, hi', zero_add, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_nonneg_iff_of_pos_left (sub_pos.mpr hst)).mp h
  -- Weyl-stabilizer normalization of the right auxiliary.
  have hch : AChain P hA (g'.s' : ℝ) (w.1 g.μ) (ρ.x 0) := hμw ▸ g'.right_chain
  obtain ⟨v, hvΛ, hvch, hvJ⟩ := AChain.exists_stabilizer_normal hμ hx1 hwΛ hch
  have hsumd : (n : ℝ) • Λ + (n : ℝ) • μ ∈ P.dominantChamber := by
    rw [← smul_add]
    exact hsmul _ hνd
  have hvμ : v.1 ((n : ℝ) • μ) = (n : ℝ) • μ :=
    apply_eq_self_of_stabilizer_of_add_mem_dominantChamber hnΛd hsumd hvΛ hvJ
  have hr : AChain P hA (g'.s' : ℝ) ((n : ℝ) • μ) (ρ.x 0) := hvμ ▸ hvch
  -- Endpoint rigidity of the right source.
  have hfin := twoPieceGluing_fibre_eq_of_chain Λ μ n hn hΛ hμ hsum hp g'
    (hs.trans hgs) (hs'.trans hgs') hτall hr (by rw [hpath]; exact hend)
  rw [← hpath]
  exact hfin

omit [FiniteDimensional ℝ H] in
/-- [Lit95] p. 514: a dominant weight precedes every weight, `ν ▷ μ` ("obviously" in
the source). Reconstructed: for a positive real root `β = u αⱼ`, `ν - s_β ν = ⟨ν, β∨⟩ β`
is a nonnegative combination of simple roots, so `⟨ν, β∨⟩ ≥ 0`. -/
theorem gluingPrecedes_of_mem_dominantChamber {ν : Dual ℝ H}
    (hν : ν ∈ P.dominantChamber) (μ : Dual ℝ H) : P.GluingPrecedes hA ν μ := by
  classical
  rintro u j ⟨k, hk, hroot⟩ hneg
  exfalso
  obtain ⟨c, hc, he⟩ := P.exists_nonneg_sub_apply_eq_sum hA hν
    (u * (P.coxeterSystem hA).simple j * u⁻¹).2
  rw [LSAChainBridgeRoots.conjugate_apply, sub_sub_cancel, hroot, rootOf_apply,
    Finset.smul_sum] at he
  set r := LSAChainBridgeRoots.rootCoroot P hA u j ν
  have h0 := Fintype.linearIndependent_iff.mp P.linearIndependent_root
    (fun i => r * (k i : ℝ) - c i) (by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib]
      rw [he, sub_self])
  have hkne : k ≠ 0 := by
    rintro rfl
    have hr : u.1 (P.root j) = 0 := by simpa [rootOf_apply] using hroot
    exact P.linearIndependent_root.ne_zero j (u.1.injective (hr.trans (map_zero u.1).symm))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hkne
  have hki : (0 : ℝ) < k i := by
    have : 0 < k i := lt_of_le_of_ne (hk i) (Ne.symm hi)
    exact_mod_cast this
  have hci : r * (k i : ℝ) = c i := sub_eq_zero.mp (h0 i)
  have := hc i
  simp only [Pi.zero_apply] at this
  nlinarith

omit [FiniteDimensional ℝ H] in
/-- The two-piece gluing itself is highest when `Λ` and `Λ + μ` are dominant: it stays in
the dominant chamber, since its tail `Λ + cμ = (1 - c)Λ + c(Λ + μ)` for `c ∈ [0, 1]`. -/
theorem twoPieceGluing_e_eq_none (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights) (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ)
    (hΛd : Λ ∈ P.dominantChamber) (hνd : Λ + μ ∈ P.dominantChamber) (i : ι) :
    LittelmannPath.e i (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).path = none := by
  obtain ⟨h1, h2, h3⟩ := twoPieceGluing_regions Λ μ n hn hΛ hμ hsum hp
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hn1 : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnpos.ne'
  rw [e_eq_none_iff]
  have h0 : (0 : ℝ) ≤ (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).path.runningMin i 1 := by
    apply LittelmannPath.le_runningMin _ zero_le_one
    intro t ht
    simp only [pairing, pathSpace_coroot]
    rcases le_total t (n : ℝ)⁻¹ with hl | hl
    · rw [h1 t ⟨ht.1, hl⟩, LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (mul_nonneg hnpos.le ht.1) (hΛd i)
    · rcases le_total t (1 - (n : ℝ)⁻¹) with hm | hm
      · rw [h2 t ⟨hl, hm⟩]
        exact hΛd i
      · rw [h3 t ⟨hm, ht.2⟩]
        have hc0 : 0 ≤ (n : ℝ) * t - ((n : ℝ) - 1) := by
          have := mul_le_mul_of_nonneg_left hm hnpos.le
          rw [mul_sub, mul_one, hn1] at this
          linarith
        have hc1 : (n : ℝ) * t - ((n : ℝ) - 1) ≤ 1 := by
          nlinarith [ht.2]
        have hν := hνd i
        have hΛi := hΛd i
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hν ⊢
        nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hΛi, mul_nonneg hc0 hν]
  change (0 : ℝ) ≤ _ at h0
  exact lt_of_lt_of_le (by norm_num) h0

/-- **Proposition 5.7** of [Lit95] (p. 516), second assertion: when `Λ` and `Λ + μ` are
dominant, the two-piece gluing `π` is the ONLY path `π'` in its connected component with
`π'(1) = Λ + μ` and `e_α π' = 0` for all simple roots `α`. The first assertion
(integrality of the component) is `twoPieceGluing_component_isIntegral`. -/
theorem twoPieceGluing_highest_iff (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights) (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ)
    (hΛd : Λ ∈ P.dominantChamber) (hνd : Λ + μ ∈ P.dominantChamber)
    {η : LittelmannPath (P.pathSpace hA)}
    (hη : η ∈ (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).path.component) :
    ((∀ i, LittelmannPath.e i η = none) ∧ η 1 = Λ + μ) ↔
      η = (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).path := by
  refine ⟨fun h => twoPieceGluing_eq_of_mem_component Λ μ n hn hΛ hμ hsum hp hΛd hνd hη
    h.1 h.2, ?_⟩
  rintro rfl
  exact ⟨twoPieceGluing_e_eq_none Λ μ n hn hΛ hμ hsum hp hΛd hνd,
    twoPieceGluing_endpoint Λ μ n hn hΛ hμ hsum hp⟩

end Matrix.Realization.LSGeneralClass
