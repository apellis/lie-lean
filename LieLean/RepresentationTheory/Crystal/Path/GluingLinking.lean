/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.ComponentWords
import LieLean.RepresentationTheory.Crystal.Path.GluingHighest
import LieLean.RepresentationTheory.Crystal.Path.Stability

/-!
# The linking chain `π_ν ~ π_λ * π_μ` and Littelmann's Proposition 6.2

## Main results

* `rationalConcat_eq_of_mem_component`: Proposition 5.7 transported to the rational
  concatenation `π_Λ * π_μ` by the pause-allowing clock of Remark 5.1.
* `linkFamily`: the family `π_x = π_{xΛ} * π_{μ + (1-x)Λ}` of the Example on p. 517.
* `rootWord_straightLine_eq_none_iff`: **the Example on p. 517 with Lemma 6.1**: if `Λ ▷ μ`
  and `Λ + μ` is integral (with a common denominator), then for every mixed word `D`,
  `D π_{Λ+μ} = 0` iff `D (π_Λ * π_μ) = 0`. The linking chains are constructed.
* `rationalConcat_eq_of_mem_component_of_endpoint`: **Proposition 6.2**: if `Λ` and
  `Λ + μ` are dominant, `π_Λ * π_μ` is the only path of its connected component ending
  in `Λ + μ`.
* `eq_straightLine_of_mem_component_of_wt`: `π_ν` is the only path of `B(ν)` of weight `ν`
  (Corollary 3, p. 512).
* `componentIso_straightLine_rationalConcat`: **Theorem 6.3**: `π_ν ↦ π_Λ * π_μ` extends to
  an isomorphism of the connected components `B(π_ν) ≅ B(π_Λ * π_μ)`.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), §6, Lemma 6.1, the Example following it, Proposition 6.2 and Theorem 6.3,
pp. 517–518; Corollary 3, p. 512. The printed pages were consulted. The links use the fixed
parametrization of `LittelmannPath.IsLink` (with the factor `1 + 2c`), and integrality of the linked
components is derived from the gluing results rather than assumed. Paths are compared
literally, with the explicit pause clocks of `GluingPause.lean` standing in for the
source's "modulo reparametrization". [Lit95] assumes a symmetrizable Kac–Moody algebra; here
the generalized Cartan matrix need not be symmetrizable.
-/

open Module Set

namespace Matrix.Realization.LSGeneralClass

open LittelmannPath

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}

/-- The rational concatenation depends only on its two displacements. -/
theorem rationalConcat_congr {Λ μ Λ' μ' : Dual ℝ H} (hΛ : Λ = Λ') (hμ : μ = μ')
    (h : Λ + μ ∈ P.integralWeights) (h' : Λ' + μ' ∈ P.integralWeights) :
    rationalConcat (hA := hA) Λ μ h = rationalConcat Λ' μ' h' := by
  subst hΛ
  subst hμ
  rfl

/-- The literal formula of the rational concatenation. -/
theorem rationalConcat_apply (Λ μ : Dual ℝ H) (h : Λ + μ ∈ P.integralWeights) (t : ℝ) :
    rationalConcat (hA := hA) Λ μ h t =
      min (max (2 * t) 0) 1 • Λ + min (max (2 * t - 1) 0) 1 • μ := rfl

/-- The pause clock waiting on `[0, 1/2]`. -/
noncomputable def lateClock : PauseMap where
  toFun t := min (max (2 * t - 1) 0) 1
  continuous := by fun_prop
  monotone := by
    intro a b hab
    dsimp
    gcongr
  zero := by norm_num
  one := by norm_num

/-- With a zero first displacement, the rational concatenation is the paused straight
line (`π_0 * π_ν = π_ν` modulo reparametrization). -/
theorem rationalConcat_zero_eq_pauseReparam (ν : Dual ℝ H) (h : 0 + ν ∈ P.integralWeights)
    (h' : ν ∈ P.integralWeights) :
    rationalConcat (hA := hA) 0 ν h =
      pauseReparam lateClock (straightLine (P.pathSpace hA) ⟨ν, h'⟩) := by
  apply ext_of_eqOn
  intro t _
  rw [rationalConcat_apply, pauseReparam_apply, straightLine_apply, pathSpace_embed]
  change _ = max 0 (min 1 (min (max (2 * t - 1) 0) 1)) • ν
  have h0 : 0 ≤ min (max (2 * t - 1) 0) (1 : ℝ) := le_min (le_max_right _ _) zero_le_one
  have h1 : min (max (2 * t - 1) 0) (1 : ℝ) ≤ 1 := min_le_right _ _
  rw [min_eq_right h1, max_eq_right h0, smul_zero, zero_add]

/-- A dominance-free compatibility transfer for the Example on p. 517:
`Λ ▷ μ` implies `xΛ ▷ μ + (1 - x)Λ` for `x ∈ [0, 1]`. -/
theorem gluingPrecedes_linkFamily {Λ μ : Dual ℝ H} (hp : P.GluingPrecedes hA Λ μ)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    P.GluingPrecedes hA (x • Λ) (μ + (1 - x) • Λ) := by
  intro u j hroot hneg
  simp only [map_smul, map_add, smul_eq_mul] at hneg ⊢
  have hΛ : LSAChainBridgeRoots.rootCoroot P hA u j Λ < 0 := by
    by_contra h
    push Not at h
    nlinarith
  have hμ := hp u j hroot hΛ
  nlinarith

/-- The linking family `π_x = π_{xΛ} * π_{μ + (1 - x)Λ}` of the Example on p. 517. -/
noncomputable def linkFamily (Λ μ : Dual ℝ H) (hsum : Λ + μ ∈ P.integralWeights) (x : ℝ) :
    LittelmannPath (P.pathSpace hA) :=
  rationalConcat (x • Λ) (μ + (1 - x) • Λ) (by convert hsum using 1; module)

/-- The linking family has a common endpoint. -/
theorem wt_linkFamily (Λ μ : Dual ℝ H) (hsum : Λ + μ ∈ P.integralWeights) (x : ℝ) :
    (linkFamily (hA := hA) Λ μ hsum x).wt = ⟨Λ + μ, hsum⟩ := by
  apply Subtype.ext
  change x • Λ + (μ + (1 - x) • Λ) = Λ + μ
  module

/-- Uniform distance in the linking family: `|hᵢ^x(t) - hᵢ^y(t)| ≤ |x - y| ∑ⱼ |⟨Λ, αⱼ∨⟩|`. -/
theorem abs_pairing_linkFamily_sub_le (Λ μ : Dual ℝ H) (hsum : Λ + μ ∈ P.integralWeights)
    (x y : ℝ) (i : ι) (t : ℝ) :
    |(linkFamily (hA := hA) Λ μ hsum x).pairing i t -
        (linkFamily (hA := hA) Λ μ hsum y).pairing i t| ≤
      |x - y| * ∑ j, |Λ (P.coroot j)| := by
  set a : ℝ := min (max (2 * t) 0) 1
  set b : ℝ := min (max (2 * t - 1) 0) 1
  have hab : 0 ≤ a - b := by
    have : b ≤ a := by
      simp only [a, b]
      gcongr
      linarith
    linarith
  have hab1 : a - b ≤ 1 := by
    have ha : a ≤ 1 := min_le_right _ _
    have hb : 0 ≤ b := le_min (le_max_right _ _) zero_le_one
    linarith
  have heq : (linkFamily (hA := hA) Λ μ hsum x).pairing i t -
      (linkFamily (hA := hA) Λ μ hsum y).pairing i t = (x - y) * (a - b) * Λ (P.coroot i) := by
    simp only [pairing, pathSpace_coroot, linkFamily, rationalConcat_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, a, b]
    ring
  rw [heq, abs_mul, abs_mul, abs_of_nonneg hab]
  have hsingle : |Λ (P.coroot i)| ≤ ∑ j, |Λ (P.coroot j)| :=
    Finset.single_le_sum (f := fun j => |Λ (P.coroot j)|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  calc |x - y| * (a - b) * |Λ (P.coroot i)| ≤ |x - y| * 1 * ∑ j, |Λ (P.coroot j)| := by
        gcongr
    _ = |x - y| * ∑ j, |Λ (P.coroot j)| := by ring

/-- An integer multiple of an integral weight is integral. -/
theorem intCast_smul_mem_integralWeights {x : Dual ℝ H} (hx : x ∈ P.integralWeights) (z : ℤ) :
    (z : ℝ) • x ∈ P.integralWeights := by
  intro i
  obtain ⟨m, hm⟩ := hx i
  exact ⟨z * m, by rw [LinearMap.smul_apply, hm, smul_eq_mul]; push_cast; ring⟩

/-- Every member `x = k/N` of the linking family has an integral connected component,
derived from gluing stability with the denominator `nN`. -/
theorem linkFamily_component_isIntegral (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights) (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ)
    {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) :
    ∀ η ∈ (linkFamily (hA := hA) Λ μ hsum ((k : ℝ) / N)).component, η.IsIntegral := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hx0 : (0 : ℝ) ≤ (k : ℝ) / N := div_nonneg (Nat.cast_nonneg k) hNR.le
  have hx1 : (k : ℝ) / N ≤ 1 := (div_le_one hNR).mpr hkN
  have hnN : 2 ≤ n * N := le_mul_of_le_of_one_le hn hN
  apply rationalConcat_component_isIntegral _ _ (n * N) hnN
  · have he : ((n * N : ℕ) : ℝ) • (((k : ℝ) / N) • Λ) = ((k : ℤ) : ℝ) • ((n : ℝ) • Λ) := by
      rw [smul_smul, smul_smul]
      congr 1
      push_cast
      field_simp
    rw [he]
    exact intCast_smul_mem_integralWeights hΛ k
  · have hc : ((n * N : ℕ) : ℝ) * (1 - (k : ℝ) / N) = ((((N : ℤ) - k : ℤ)) : ℝ) * n := by
      push_cast
      field_simp
    have he : ((n * N : ℕ) : ℝ) • (μ + (1 - (k : ℝ) / N) • Λ) =
        ((N : ℤ) : ℝ) • ((n : ℝ) • μ) + ((((N : ℤ) - k : ℤ)) : ℝ) • ((n : ℝ) • Λ) := by
      rw [smul_add, smul_smul, hc, smul_smul, smul_smul]
      congr 1
      congr 1
      push_cast
      ring
    rw [he]
    exact add_mem (intCast_smul_mem_integralWeights hμ N)
      (intCast_smul_mem_integralWeights hΛ _)
  · exact gluingPrecedes_linkFamily hp hx0 hx1

/-- A uniform bound for all Cartan entries, as required by `LittelmannPath.IsLink`. -/
theorem abs_cartanMatrix_le_sum (i j : ι) :
    |((P.cartanDatum hA).cartanMatrix j i : ℝ)| ≤
      ∑ a, ∑ b, |((P.cartanDatum hA).cartanMatrix b a : ℝ)| := by
  calc |((P.cartanDatum hA).cartanMatrix j i : ℝ)|
      ≤ ∑ b, |((P.cartanDatum hA).cartanMatrix b i : ℝ)| :=
        Finset.single_le_sum (f := fun b => |((P.cartanDatum hA).cartanMatrix b i : ℝ)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ a, ∑ b, |((P.cartanDatum hA).cartanMatrix b a : ℝ)| :=
        Finset.single_le_sum
          (f := fun a => ∑ b, |((P.cartanDatum hA).cartanMatrix b a : ℝ)|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- **The linking chain of the Example on p. 517**: for every level `L`, the members
`x = 0` and `x = 1` of the linking family are joined by a chain of links of level `L`.
Consecutive members `k/N, (k+1)/N` are linked once `N` is large; the integrality of all
linked components is derived, not assumed. -/
theorem linkFamily_linked (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights) (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ) (L : ℕ) :
    Relation.ReflTransGen
      (IsLink (∑ a, ∑ b, |((P.cartanDatum hA).cartanMatrix b a : ℝ)|) L)
      (linkFamily (hA := hA) Λ μ hsum 0) (linkFamily (hA := hA) Λ μ hsum 1) := by
  set c : ℝ := ∑ a, ∑ b, |((P.cartanDatum hA).cartanMatrix b a : ℝ)| with hc
  set C : ℝ := ∑ j, |Λ (P.coroot j)| with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((1 + 2 * c) ^ L * C)
  set N : ℕ := N₀ + 1 with hNdef
  have hNpos : 0 < N := Nat.succ_pos N₀
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hsmall : (1 + 2 * c) ^ L * (C / N) < 1 := by
    rw [← mul_div_assoc, div_lt_one hNR]
    have : (N₀ : ℝ) < N := by exact_mod_cast Nat.lt_succ_self N₀
    linarith
  have hlink : ∀ k < N, IsLink c L (linkFamily (hA := hA) Λ μ hsum ((k : ℝ) / N))
      (linkFamily (hA := hA) Λ μ hsum (((k + 1 : ℕ) : ℝ) / N)) := by
    intro k hk
    refine ⟨(wt_linkFamily Λ μ hsum _).trans (wt_linkFamily Λ μ hsum _).symm,
      linkFamily_component_isIntegral Λ μ n hn hΛ hμ hsum hp hNpos hk.le,
      linkFamily_component_isIntegral Λ μ n hn hΛ hμ hsum hp hNpos hk,
      C / N, div_nonneg hC hNR.le, hsmall, ?_⟩
    intro j t _
    have hd : |(k : ℝ) / N - ((k + 1 : ℕ) : ℝ) / N| = 1 / N := by
      rw [← sub_div, abs_div, abs_of_pos hNR]
      congr 1
      rw [show (k : ℝ) - ((k + 1 : ℕ) : ℝ) = -1 by push_cast; ring, abs_neg, abs_one]
    calc _ ≤ |(k : ℝ) / N - ((k + 1 : ℕ) : ℝ) / N| * C :=
          abs_pairing_linkFamily_sub_le Λ μ hsum _ _ j t
      _ = C / N := by rw [hd]; ring
  have hchain : ∀ k ≤ N, Relation.ReflTransGen (IsLink c L)
      (linkFamily (hA := hA) Λ μ hsum 0) (linkFamily (hA := hA) Λ μ hsum ((k : ℝ) / N)) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.cast_zero, zero_div]
    | succ k ih =>
      intro hk
      exact (ih (by omega)).tail (hlink k (by omega))
  have h := hchain N le_rfl
  rwa [div_self hNR.ne'] at h

/-- **The Example on p. 517 with Lemma 6.1**: if `Λ ▷ μ` and `nΛ, nμ, Λ + μ` are integral,
then a mixed root word kills the straight line `π_{Λ+μ}` if and only if it kills the rational
concatenation `π_Λ * π_μ`. No dominance is assumed. -/
theorem rootWord_straightLine_eq_none_iff (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights) (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ)
    (l : List (ι ⊕ ι)) :
    rootWord l (straightLine (P.pathSpace hA) ⟨Λ + μ, hsum⟩) = none ↔
      rootWord l (rationalConcat (hA := hA) Λ μ hsum) = none := by
  have hc0 : (0 : ℝ) ≤ ∑ a, ∑ b, |((P.cartanDatum hA).cartanMatrix b a : ℝ)| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h := rootWord_eq_none_iff_of_linked hc0 abs_cartanMatrix_le_sum
    (linkFamily_linked Λ μ n hn hΛ hμ hsum hp l.length) l le_rfl
  have h0 : linkFamily (hA := hA) Λ μ hsum 0 =
      pauseReparam lateClock (straightLine (P.pathSpace hA) ⟨Λ + μ, hsum⟩) := by
    rw [linkFamily, rationalConcat_congr (zero_smul ℝ Λ)
      (show μ + (1 - (0 : ℝ)) • Λ = Λ + μ by rw [sub_zero, one_smul, add_comm]) _
      (by rw [zero_add]; exact hsum)]
    exact rationalConcat_zero_eq_pauseReparam _ _ _
  have h1 : linkFamily (hA := hA) Λ μ hsum 1 = rationalConcat Λ μ hsum :=
    rationalConcat_congr (one_smul ℝ Λ) (by rw [sub_self, zero_smul, add_zero]) _ _
  rw [h0, h1, rootWord_pauseReparam_eq_none_iff] at h
  exact h

/-- An integral weight in the dominant chamber is dominant integral. -/
theorem isDominantIntegral_of_mem_dominantChamber {ν : Dual ℝ H}
    (hν : ν ∈ P.integralWeights) (hd : ν ∈ P.dominantChamber) : P.IsDominantIntegral ν := by
  intro i
  obtain ⟨z, hz⟩ := hν i
  have h0 : (0 : ℤ) ≤ z := by
    have := hd i
    rw [hz] at this
    exact_mod_cast this
  refine ⟨z.toNat, ?_⟩
  rw [hz]
  exact_mod_cast (Int.toNat_of_nonneg h0).symm

/-- [Lit95] Corollary 3 (p. 512) in the form needed for Theorem 6.3: `π_ν` is the only path of
`B(ν)` of weight `ν`, by Littelmann's stability theorem `B(ν) = {f_{i₁} ⋯ f_{iₖ} π_ν}`. -/
theorem eq_straightLine_of_mem_component_of_wt {ν : Dual ℝ H}
    (hν : P.IsDominantIntegral ν) {ξ : LittelmannPath (P.pathSpace hA)}
    (hξ : ξ ∈ (straightLine (P.pathSpace hA) ⟨ν, hν.mem_integralWeights⟩).component)
    (hwt : ξ.wt = ⟨ν, hν.mem_integralWeights⟩) :
    ξ = straightLine (P.pathSpace hA) ⟨ν, hν.mem_integralWeights⟩ := by
  classical
  rw [(Matrix.Realization.component_straightLine_eq_fOrbit hν).1] at hξ
  obtain ⟨l, hl⟩ := hξ
  have h := wt_of_fWord hl
  rw [hwt, wt_straightLine] at h
  have hs : ((l : Multiset ι).map (P.cartanDatum hA).root).sum =
      ((0 : Multiset ι).map (P.cartanDatum hA).root).sum := by
    rw [Multiset.map_coe, Multiset.sum_coe, Multiset.map_zero, Multiset.sum_zero]
    exact (sub_eq_self.mp h.symm)
  have hl0 : l = [] := by
    simpa using Matrix.Realization.injective_sum_map_root hA hs
  subst hl0
  exact (Option.some_injective _ hl).symm

section FiniteDimensional

variable [FiniteDimensional ℝ H]

/-- Proposition 5.7 for the rational concatenation `π_Λ * π_μ` itself, transported through
the pause clock of Remark 5.1. The compatibility `Λ ▷ μ` is derived from dominance. -/
theorem rationalConcat_eq_of_mem_component (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights) (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights)
    (hΛd : Λ ∈ P.dominantChamber) (hνd : Λ + μ ∈ P.dominantChamber)
    {η : LittelmannPath (P.pathSpace hA)}
    (hη : η ∈ (rationalConcat (hA := hA) Λ μ hsum).component)
    (he : ∀ i, LittelmannPath.e i η = none) (hend : η 1 = Λ + μ) :
    η = rationalConcat Λ μ hsum := by
  have hp := gluingPrecedes_of_mem_dominantChamber (hA := hA) hΛd μ
  have hmem := (rationalConcat_gluing_bijOn Λ μ n hn hΛ hμ hsum hp).mapsTo hη
  have he' : ∀ i, LittelmannPath.e i (pauseReparam (twoPieceClock n hn) η) = none := by
    intro i
    rw [e_pauseReparam, he i]
    rfl
  have hend' : pauseReparam (twoPieceClock n hn) η 1 = Λ + μ := by
    rw [pauseReparam_apply, (twoPieceClock n hn).one, hend]
  have h := twoPieceGluing_eq_of_mem_component Λ μ n hn hΛ hμ hsum hp hΛd hνd hmem he' hend'
  rw [twoPieceGluing_eq_pauseReparam] at h
  exact pauseReparam_injective _ h

/-- **Proposition 6.2** of [Lit95] (p. 517): let `Λ` be dominant and `Λ + μ` an integral
dominant weight, with a common denominator `n` for `Λ, μ`. Then `π = π_Λ * π_μ` is the only
path in its connected component `Aπ` ending in `Λ + μ`. -/
theorem rationalConcat_eq_of_mem_component_of_endpoint (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights) (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights)
    (hΛd : Λ ∈ P.dominantChamber) (hνd : Λ + μ ∈ P.dominantChamber)
    {η : LittelmannPath (P.pathSpace hA)}
    (hη : η ∈ (rationalConcat (hA := hA) Λ μ hsum).component) (hend : η 1 = Λ + μ) :
    η = rationalConcat Λ μ hsum := by
  classical
  have hp := gluingPrecedes_of_mem_dominantChamber (hA := hA) hΛd μ
  obtain ⟨l, hl⟩ := (mem_component_iff_rootWord _ η).mp hη
  have hνDI := isDominantIntegral_of_mem_dominantChamber hsum hνd
  set πν := straightLine (P.pathSpace hA) (⟨Λ + μ, hsum⟩ : P.integralWeights) with hπν
  have hlink := rootWord_straightLine_eq_none_iff Λ μ n hn hΛ hμ hsum hp
  obtain ⟨ξ, hξ⟩ := Option.ne_none_iff_exists'.mp (fun h => by
    rw [(hlink l).mp h] at hl
    cases hl)
  have hηwt : η.wt = (⟨Λ + μ, hsum⟩ : P.integralWeights) := by
    apply Subtype.ext
    have h := η.apply_one
    rw [hend] at h
    exact h.symm
  have hξwt : ξ.wt = (⟨Λ + μ, hsum⟩ : P.integralWeights) := by
    have h := rootWord_wt_sub_eq hξ hl
    rw [hηwt] at h
    have h1 : πν.wt = (⟨Λ + μ, hsum⟩ : P.integralWeights) := rfl
    have h2 : (rationalConcat (hA := hA) Λ μ hsum).wt = (⟨Λ + μ, hsum⟩ : P.integralWeights) :=
      rfl
    rw [h1, h2, sub_self, sub_eq_zero] at h
    exact h
  have hξmem : ξ ∈ πν.component := (mem_component_iff_rootWord _ ξ).mpr ⟨l, hξ⟩
  -- Corollary 3: the only path of `B(Λ + μ)` of weight `Λ + μ` is highest.
  have hξe : ∀ i, LittelmannPath.e i ξ = none := by
    intro i
    by_contra hne
    obtain ⟨ξ', hξ'⟩ := Option.ne_none_iff_exists'.mp hne
    have hmem' : ξ' ∈ πν.component := (isStable_component πν).e_mem i ξ ξ' hξmem hξ'
    obtain ⟨k, hk, hwt⟩ :=
      Matrix.Realization.exists_wt_eq_sub_rootOf_pathCrystal hνDI ⟨ξ', hmem'⟩
    change (ξ'.wt : Dual ℝ H) = Λ + μ - P.rootOf k at hwt
    rw [wt_of_e_eq_some hξ', AddSubgroup.coe_add, hξwt, coe_root_cartanDatum] at hwt
    have h0 : P.rootOf (k + Pi.single i 1) = 0 := by
      rw [map_add, rootOf_single]
      calc P.rootOf k + P.root i = (Λ + μ + P.root i) - (Λ + μ - P.rootOf k) := by abel
        _ = 0 := by rw [hwt, sub_self]
    have h1 := congrFun (P.rootOf_injective (h0.trans (map_zero P.rootOf).symm)) i
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at h1
    have := hk i
    simp only [Pi.zero_apply] at this
    omega
  have hηe : ∀ i, LittelmannPath.e i η = none := by
    intro i
    have h1 : rootWord (l ++ [.inl i]) πν = none := by
      rw [rootWord_append, hξ]
      simp [rootWord, rootStep, hξe i]
    have h2 := (hlink _).mp h1
    rw [rootWord_append, hl] at h2
    simpa [rootWord, rootStep] using h2
  exact rationalConcat_eq_of_mem_component Λ μ n hn hΛ hμ hsum hΛd hνd hη hηe hend

omit [FiniteDimensional ℝ H] in
/-- For successful words, equality of the two outputs means that the first word followed by
the inverse of the second returns the path to itself. -/
theorem eq_iff_rootWord_append_invWord {π a b : LittelmannPath (P.pathSpace hA)}
    {u v : List (ι ⊕ ι)} (hu : rootWord u π = some a) (hv : rootWord v π = some b) :
    a = b ↔ rootWord (u ++ invWord v) π = some π := by
  rw [rootWord_append_eq_bind, hu, Option.bind_some, ← rootWord_invWord_eq_some_iff, hv]
  constructor
  · rintro rfl
    rfl
  · intro h
    exact (Option.some_injective _ h).symm

/-- **Theorem 6.3** of [Lit95] (pp. 517–518): let `Λ` be dominant and `ν = Λ + μ` an integral
dominant weight, with a common denominator `n` for `Λ, μ`. Then `π_ν ↦ π_Λ * π_μ` extends to
an isomorphism of crystals `B(π_ν) ≅ B(π_Λ * π_μ)`. As in the source, the zero pattern of all
mixed words agrees by linking (Lemma 6.1), and their relations agree by (6.2), using
Proposition 6.2 on one side and Corollary 3 on the other. -/
theorem componentIso_straightLine_rationalConcat (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights) (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights)
    (hΛd : Λ ∈ P.dominantChamber) (hνd : Λ + μ ∈ P.dominantChamber) :
    ComponentIso (straightLine (P.pathSpace hA) ⟨Λ + μ, hsum⟩)
      (rationalConcat (hA := hA) Λ μ hsum) := by
  classical
  have hp := gluingPrecedes_of_mem_dominantChamber (hA := hA) hΛd μ
  have hνDI := isDominantIntegral_of_mem_dominantChamber hsum hνd
  set πν := straightLine (P.pathSpace hA) (⟨Λ + μ, hsum⟩ : P.integralWeights) with hπν
  set π := rationalConcat (hA := hA) Λ μ hsum with hπ
  have hlink : ∀ u, rootWord u πν = none ↔ rootWord u π = none :=
    rootWord_straightLine_eq_none_iff Λ μ n hn hΛ hμ hsum hp
  -- (6.2): a word fixes `π_ν` if and only if it fixes `π_Λ * π_μ`.
  have hfix : ∀ w, rootWord w πν = some πν ↔ rootWord w π = some π := by
    intro w
    constructor
    · intro h
      obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp (fun hn => by
        rw [(hlink w).mpr hn] at h
        cases h)
      have hzmem : z ∈ π.component := (mem_component_iff_rootWord _ _).mpr ⟨w, hz⟩
      have hwt := rootWord_wt_sub_eq h hz
      rw [sub_self, eq_comm, sub_eq_zero] at hwt
      have hend : z 1 = Λ + μ := by
        rw [z.apply_one, hwt]
        rfl
      rw [hz, rationalConcat_eq_of_mem_component_of_endpoint Λ μ n hn hΛ hμ hsum hΛd hνd
        hzmem hend]
    · intro h
      obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp (fun hn => by
        rw [(hlink w).mp hn] at h
        cases h)
      have hzmem : z ∈ πν.component := (mem_component_iff_rootWord _ _).mpr ⟨w, hz⟩
      have hwt := rootWord_wt_sub_eq h hz
      rw [sub_self, eq_comm, sub_eq_zero] at hwt
      rw [hz, eq_straightLine_of_mem_component_of_wt hνDI hzmem hwt]
  refine componentIso_of_rootWord rfl hlink ?_
  intro u v
  rcases hu : rootWord u πν with _ | x <;> rcases hv : rootWord v πν with _ | y
  · rw [(hlink u).mp hu, (hlink v).mp hv]
  · obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.mp (fun hn => by
      rw [(hlink v).mpr hn] at hv
      cases hv)
    rw [(hlink u).mp hu, hy']
    simp
  · obtain ⟨x', hx'⟩ := Option.ne_none_iff_exists'.mp (fun hn => by
      rw [(hlink u).mpr hn] at hu
      cases hu)
    rw [(hlink v).mp hv, hx']
    simp
  · obtain ⟨x', hx'⟩ := Option.ne_none_iff_exists'.mp (fun hn => by
      rw [(hlink u).mpr hn] at hu
      cases hu)
    obtain ⟨y', hy'⟩ := Option.ne_none_iff_exists'.mp (fun hn => by
      rw [(hlink v).mpr hn] at hv
      cases hv)
    rw [hx', hy', Option.some.injEq, Option.some.injEq,
      eq_iff_rootWord_append_invWord hu hv, eq_iff_rootWord_append_invWord hx' hy', hfix]

end FiniteDimensional

end Matrix.Realization.LSGeneralClass
