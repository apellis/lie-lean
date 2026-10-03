/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.RootOperators

/-!
# Concatenation of Littelmann paths and the tensor product rule

The concatenation `π₁ * π₂` of two paths runs through `π₁` and then through `π₂` translated by
`π₁(1)`. Littelmann ([Lit95] §2, [Lit94]) observed that on integral paths the root
operators act on concatenations by Kashiwara's tensor product rule: `π₁ ⊗ π₂ ↦ π₁ * π₂` intertwines
the root operators of the tensor product crystal with those of the path crystal.

## Main definitions

* `LittelmannPath.concat π₁ π₂`: the concatenation `π₁ * π₂` (parametrized so that `π₁` is run
  through on `[0, 1/2]` and `π₂` on `[1/2, 1]`).
* `LittelmannPath.IsIntegral`: all the minima `mᵢ = min hᵢ` are integers ("integral paths").

## Main results

* `LittelmannPath.minPairing_concat`: `mᵢ(π₁ * π₂) = min(mᵢ(π₁), hᵢ^{π₁}(1) + mᵢ(π₂))`.
* `LittelmannPath.ε_concat`, `LittelmannPath.φ_concat`: `εᵢ` and `φᵢ` of a concatenation are given
  by the tensor product formulas.
* `LittelmannPath.e_concat`, `LittelmannPath.f_concat`: if the minima `mᵢ(π₁)`, `mᵢ(π₂)` are
  integers, then `eᵢ (π₁ * π₂)` and `fᵢ (π₁ * π₂)` are given by Kashiwara's tensor product rule
  (in the convention of `Crystal.tensor`).
* `LittelmannPath.e_concat_eq_tensor`, `LittelmannPath.f_concat_eq_tensor`: the same, as a
  compatibility of `(π₁, π₂) ↦ π₁ * π₂` with the tensor product crystal, for integral paths.
* `LittelmannPath.rev_concat`: `(π₁ * π₂)^∨ = π₂^∨ * π₁^∨`.

The proofs were reconstructed by us from the closed formulas for the root operators.

## References

* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
* [Lit94] P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*,
  Invent. Math. **116** (1994), 329–346.
-/

open Set

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {D : CartanDatum ι X}
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

section Concat

variable (π₁ π₂ : LittelmannPath S)

/-- The concatenation `π₁ * π₂` ([Lit95] §1): `π₁(2t)` for `t ≤ 1/2` and
`π₁(1) + π₂(2t - 1)` for `t ≥ 1/2`. -/
noncomputable def concat : LittelmannPath S where
  toFun t := if t ≤ 2⁻¹ then π₁ (2 * t) else π₁ 1 + π₂ (2 * t - 1)
  wt := π₁.wt + π₂.wt
  toFun_of_nonpos' t ht := by
    rw [ite_eq_left (ht.trans (by positivity)), π₁.apply_of_nonpos (by linarith)]
  toFun_of_one_le' t ht := by
    rw [ite_eq_right (by linarith [(by norm_num : (2 : 𝕜)⁻¹ < 1)]), π₁.apply_one,
      π₂.apply_of_one_le (by linarith), map_add]
  continuous_coroot' i := by
    have : (fun t ↦ S.coroot i (if t ≤ 2⁻¹ then π₁ (2 * t) else π₁ 1 + π₂ (2 * t - 1))) =
        fun t ↦ if t ≤ 2⁻¹ then π₁.pairing i (2 * t)
          else π₁.pairing i 1 + π₂.pairing i (2 * t - 1) := by
      funext t
      split_ifs <;> simp [pairing]
    rw [this]
    refine Continuous.if_le ((π₁.continuous_pairing i).comp (continuous_const.mul continuous_id))
      (continuous_const.add ((π₂.continuous_pairing i).comp
        ((continuous_const.mul continuous_id).sub continuous_const)))
      continuous_id continuous_const fun t ht ↦ ?_
    have ht : t = 2⁻¹ := ht
    rw [ht, mul_inv_cancel₀ two_ne_zero, sub_self, pairing_zero, add_zero]

variable {π₁ π₂} {i : ι} {t : 𝕜}

@[simp] lemma wt_concat : (π₁.concat π₂).wt = π₁.wt + π₂.wt := rfl

lemma concat_apply_of_le (ht : t ≤ 2⁻¹) : π₁.concat π₂ t = π₁ (2 * t) := ite_eq_left ht

lemma concat_apply_of_ge (ht : 2⁻¹ ≤ t) : π₁.concat π₂ t = π₁ 1 + π₂ (2 * t - 1) := by
  rcases ht.lt_or_eq with ht | rfl
  · exact ite_eq_right (not_le.mpr ht)
  · rw [concat_apply_of_le le_rfl, mul_inv_cancel₀ two_ne_zero, sub_self, apply_zero, add_zero]

lemma pairing_concat_of_le (ht : t ≤ 2⁻¹) : (π₁.concat π₂).pairing i t = π₁.pairing i (2 * t) := by
  rw [pairing, concat_apply_of_le ht, pairing]

lemma pairing_concat_of_ge (ht : 2⁻¹ ≤ t) :
    (π₁.concat π₂).pairing i t = π₁.pairing i 1 + π₂.pairing i (2 * t - 1) := by
  rw [pairing, concat_apply_of_ge ht, map_add, pairing, pairing]

lemma runningMin_concat_of_le (ht : t ∈ Icc (0 : 𝕜) 2⁻¹) :
    (π₁.concat π₂).runningMin i t = π₁.runningMin i (2 * t) := by
  have h2t : 0 ≤ 2 * t := by linarith [ht.1]
  apply le_antisymm
  · obtain ⟨s, hs, hs'⟩ := π₁.exists_runningMin i h2t
    have hs2 : s / 2 ∈ Icc 0 t := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have := (π₁.concat π₂).runningMin_le (i := i) hs2
    rwa [pairing_concat_of_le (hs2.2.trans ht.2), mul_div_cancel₀ _ two_ne_zero, hs'] at this
  · refine (π₁.concat π₂).le_runningMin ht.1 fun u hu ↦ ?_
    rw [pairing_concat_of_le (hu.2.trans ht.2)]
    exact π₁.runningMin_le ⟨by linarith [hu.1], by linarith [hu.2]⟩

lemma runningMin_concat_of_ge (ht : t ∈ Icc (2⁻¹ : 𝕜) 1) :
    (π₁.concat π₂).runningMin i t =
      min (π₁.minPairing i) (π₁.pairing i 1 + π₂.runningMin i (2 * t - 1)) := by
  have h2 : (0 : 𝕜) < 2⁻¹ := by positivity
  have h2t : 0 ≤ 2 * t - 1 := by
    have := mul_le_mul_of_nonneg_left ht.1 (zero_le_two (α := 𝕜))
    rw [mul_inv_cancel₀ two_ne_zero] at this
    linarith
  apply le_antisymm
  · refine le_min ?_ ?_
    · obtain ⟨s, hs, hs'⟩ := π₁.exists_minPairing i
      have hs2 : s / 2 ∈ Icc 0 t := ⟨by linarith [hs.1], by linarith [hs.2, ht.1]⟩
      have := (π₁.concat π₂).runningMin_le (i := i) hs2
      rwa [pairing_concat_of_le (by linarith [hs.2]), mul_div_cancel₀ _ two_ne_zero, hs'] at this
    · obtain ⟨s, hs, hs'⟩ := π₂.exists_runningMin i h2t
      have hs2 : (s + 1) / 2 ∈ Icc 0 t := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have := (π₁.concat π₂).runningMin_le (i := i) hs2
      rwa [pairing_concat_of_ge (by linarith [hs.1]), mul_div_cancel₀ _ two_ne_zero,
        add_sub_cancel_right, hs'] at this
  · refine (π₁.concat π₂).le_runningMin (h2.le.trans ht.1) fun u hu ↦ ?_
    rcases le_total u 2⁻¹ with hu2 | hu2
    · rw [pairing_concat_of_le hu2]
      refine (min_le_left _ _).trans (π₁.minPairing_le ⟨by linarith [hu.1], ?_⟩)
      have := mul_le_mul_of_nonneg_left hu2 (zero_le_two (α := 𝕜))
      rwa [mul_inv_cancel₀ two_ne_zero] at this
    · rw [pairing_concat_of_ge hu2]
      refine (min_le_right _ _).trans ?_
      have := mul_le_mul_of_nonneg_left hu2 (zero_le_two (α := 𝕜))
      rw [mul_inv_cancel₀ two_ne_zero] at this
      gcongr
      exact π₂.runningMin_le ⟨by linarith, by linarith [hu.2]⟩

/-- `mᵢ(π₁ * π₂) = min(mᵢ(π₁), hᵢ^{π₁}(1) + mᵢ(π₂))`. -/
theorem minPairing_concat :
    (π₁.concat π₂).minPairing i = min (π₁.minPairing i) (π₁.pairing i 1 + π₂.minPairing i) := by
  rw [minPairing, runningMin_concat_of_ge ⟨by norm_num, le_rfl⟩]
  norm_num
  rfl

lemma pairing_one_concat :
    (π₁.concat π₂).pairing i 1 = π₁.pairing i 1 + π₂.pairing i 1 := by
  rw [pairing_concat_of_ge (by norm_num)]
  norm_num

/-- The time reversal of a concatenation: `(π₁ * π₂)^∨ = π₂^∨ * π₁^∨`. -/
theorem rev_concat : (π₁.concat π₂).rev = π₂.rev.concat π₁.rev := by
  refine ext_of_eqOn fun t ht ↦ ?_
  rw [rev_apply, concat_apply_of_ge (by norm_num : (2 : 𝕜)⁻¹ ≤ 1)]
  rcases le_total t 2⁻¹ with h | h
  · rw [concat_apply_of_ge (by linarith : 2⁻¹ ≤ 1 - t), concat_apply_of_le h, rev_apply,
      show (2 : 𝕜) * (1 - t) - 1 = 1 - 2 * t by ring]
    norm_num
  · rw [concat_apply_of_le (by linarith : 1 - t ≤ 2⁻¹), concat_apply_of_ge h, rev_apply,
      rev_apply, show (1 : 𝕜) - (2 * t - 1) = 2 * (1 - t) by ring]
    norm_num
    abel

/-- A path is integral if all the minima `mᵢ = min hᵢ` are integers (cf. the integrality
property, [Lit95] 2.6). -/
def IsIntegral (π : LittelmannPath S) : Prop := ∀ i, ∃ n : ℤ, π.minPairing i = n

lemma exists_minPairing_rev_eq {π : LittelmannPath S} (h : ∃ n : ℤ, π.minPairing i = n) :
    ∃ n : ℤ, π.rev.minPairing i = n := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n - D.coroot i π.wt, by rw [minPairing_rev, hn, pairing_one]; push_cast; ring⟩

lemma IsIntegral.rev {π : LittelmannPath S} (h : π.IsIntegral) : π.rev.IsIntegral :=
  fun i ↦ exists_minPairing_rev_eq (h i)

lemma IsIntegral.concat (h₁ : π₁.IsIntegral) (h₂ : π₂.IsIntegral) :
    (π₁.concat π₂).IsIntegral := fun i ↦ by
  obtain ⟨n₁, hn₁⟩ := h₁ i
  obtain ⟨n₂, hn₂⟩ := h₂ i
  exact ⟨min n₁ (D.coroot i π₁.wt + n₂), by
    rw [minPairing_concat, hn₁, hn₂, pairing_one]
    push_cast
    rfl⟩

end Concat

/-! ### The tensor product rule -/

variable [FloorRing 𝕜] {π₁ π₂ : LittelmannPath S} {i : ι}

/-- `εᵢ(π₁ * π₂) = max(εᵢ(π₁), εᵢ(π₂) - ⟨wt π₁, αᵢ^∨⟩)`, the tensor product formula. -/
theorem ε_concat :
    ε i (π₁.concat π₂) = max (ε i π₁) (ε i π₂ + ((-D.coroot i π₁.wt : ℤ) : WithBot ℤ)) := by
  rw [ε, ε, ε, minPairing_concat, pairing_one, ← WithBot.coe_add, ← WithBot.coe_max]
  congr 1
  rw [← max_neg_neg, Int.floor_mono.map_max, neg_add, add_comm (-(D.coroot i π₁.wt : 𝕜)),
    ← Int.cast_neg, Int.floor_add_intCast]

/-- `φᵢ(π₁ * π₂) = max(φᵢ(π₂), φᵢ(π₁) + ⟨wt π₂, αᵢ^∨⟩)`, the tensor product formula. -/
theorem φ_concat :
    φ i (π₁.concat π₂) = max (φ i π₂) (φ i π₁ + (D.coroot i π₂.wt : WithBot ℤ)) := by
  rw [φ, φ, φ, minPairing_concat, pairing_one_concat, pairing_one, pairing_one,
    ← WithBot.coe_add, ← WithBot.coe_max]
  congr 1
  rw [← max_sub_sub_left, Int.floor_mono.map_max, max_comm]
  congr 1
  · congr 1
    ring
  · rw [show (D.coroot i π₁.wt : 𝕜) + D.coroot i π₂.wt - π₁.minPairing i =
      (D.coroot i π₁.wt - π₁.minPairing i) + (D.coroot i π₂.wt : ℤ) by ring,
      Int.floor_add_intCast]

omit [OrderTopology 𝕜] in
private lemma ε_le_φ_iff {n₁ n₂ : ℤ} (h₁ : π₁.minPairing i = n₁) (h₂ : π₂.minPairing i = n₂) :
    ε i π₂ ≤ φ i π₁ ↔ π₁.minPairing i ≤ π₁.pairing i 1 + π₂.minPairing i := by
  simp only [ε, φ, h₁, h₂, pairing_one]
  rw [← Int.cast_neg, Int.floor_intCast, ← Int.cast_sub, Int.floor_intCast, WithBot.coe_le_coe]
  constructor <;> intro h
  · exact_mod_cast (by linarith : n₁ ≤ D.coroot i π₁.wt + n₂)
  · have : n₁ ≤ D.coroot i π₁.wt + n₂ := by exact_mod_cast h
    linarith

/-- Kashiwara's tensor product rule for `eᵢ` on concatenations ([Lit95] §2): if the minima
`mᵢ(π₁)` and `mᵢ(π₂)` are integers, then `eᵢ (π₁ * π₂) = (eᵢ π₁) * π₂` if `εᵢ(π₂) ≤ φᵢ(π₁)` and
`eᵢ (π₁ * π₂) = π₁ * (eᵢ π₂)` otherwise. -/
theorem e_concat (h₁ : ∃ n : ℤ, π₁.minPairing i = n) (h₂ : ∃ n : ℤ, π₂.minPairing i = n) :
    e i (π₁.concat π₂) = if ε i π₂ ≤ φ i π₁ then (e i π₁).map (·.concat π₂)
      else (e i π₂).map (π₁.concat ·) := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  have hH : π₁.minPairing i ≤ π₁.pairing i 1 := π₁.minPairing_le_pairing_one i
  have hQ₁ := π₁.minPairing_nonpos i
  obtain ⟨H, hH'⟩ : ∃ H : ℤ, π₁.pairing i 1 = H := ⟨_, π₁.pairing_one i⟩
  by_cases hc : π₁.minPairing i ≤ π₁.pairing i 1 + π₂.minPairing i
  · rw [ite_eq_left ((ε_le_φ_iff hn₁ hn₂).mpr hc)]
    have hQ : (π₁.concat π₂).minPairing i = π₁.minPairing i := by
      rw [minPairing_concat, min_eq_left hc]
    by_cases hle : π₁.minPairing i ≤ -1
    · rw [e_of_le hle, e_of_le (hQ ▸ hle), Option.map_some]
      congr 1
      refine ext_of_eqOn fun t ht ↦ ?_
      rw [eRaw_apply, eCoeff, hQ]
      rcases le_total t 2⁻¹ with ht2 | ht2
      · rw [concat_apply_of_le ht2, concat_apply_of_le ht2, eRaw_apply, eCoeff,
          runningMin_concat_of_le ⟨ht.1, ht2⟩]
      · have h2t : 0 ≤ 2 * t - 1 := by
          have := mul_le_mul_of_nonneg_left ht2 (zero_le_two (α := 𝕜))
          rw [mul_inv_cancel₀ two_ne_zero] at this
          linarith
        rw [concat_apply_of_ge ht2, concat_apply_of_ge ht2, eRaw_apply,
          π₁.eCoeff_of_one_le i le_rfl, runningMin_concat_of_ge ⟨ht2, ht.2⟩,
          min_eq_left (show π₁.minPairing i ≤ π₁.pairing i 1 + π₂.runningMin i (2 * t - 1) by
            linarith [π₂.minPairing_le_runningMin (i := i) h2t]),
          min_eq_left (show π₁.minPairing i ≤ π₁.minPairing i + 1 by linarith)]
        module
    · rw [(e_eq_none_iff).mpr (not_le.mp hle), (e_eq_none_iff).mpr (hQ ▸ not_le.mp hle),
        Option.map_none]
  · rw [ite_eq_right (mt (ε_le_φ_iff hn₁ hn₂).mp hc)]
    replace hc := not_le.mp hc
    -- the minimum is attained in the second half, strictly (hence by `1`) below `mᵢ(π₁)`
    have hQ : (π₁.concat π₂).minPairing i = π₁.pairing i 1 + π₂.minPairing i := by
      rw [minPairing_concat, min_eq_right hc.le]
    have hc' : π₁.pairing i 1 + π₂.minPairing i + 1 ≤ π₁.minPairing i := by
      rw [hn₁, hn₂, hH'] at hc ⊢
      exact_mod_cast (by exact_mod_cast hc : H + n₂ < n₁)
    have hle : (π₁.concat π₂).minPairing i ≤ -1 := by rw [hQ]; linarith
    have hle₂ : π₂.minPairing i ≤ -1 := by linarith
    rw [e_of_le hle, e_of_le hle₂, Option.map_some]
    congr 1
    refine ext_of_eqOn fun t ht ↦ ?_
    rw [eRaw_apply, eCoeff, hQ]
    rcases le_total t 2⁻¹ with ht2 | ht2
    · rw [concat_apply_of_le ht2, concat_apply_of_le ht2, runningMin_concat_of_le ⟨ht.1, ht2⟩,
        min_eq_right ((by linarith : π₁.pairing i 1 + π₂.minPairing i + 1 ≤ π₁.minPairing i).trans
          (π₁.minPairing_le_runningMin (by linarith [ht.1])))]
      simp
    · rw [concat_apply_of_ge ht2, concat_apply_of_ge ht2, eRaw_apply, eCoeff,
        runningMin_concat_of_ge ⟨ht2, ht.2⟩]
      have : min (min (π₁.minPairing i) (π₁.pairing i 1 + π₂.runningMin i (2 * t - 1)))
          (π₁.pairing i 1 + π₂.minPairing i + 1) =
          π₁.pairing i 1 + min (π₂.runningMin i (2 * t - 1)) (π₂.minPairing i + 1) := by
        rw [min_assoc, min_eq_right ((min_le_right _ _).trans hc'), add_assoc, min_add_add_left]
      rw [this]
      module

/-- Kashiwara's tensor product rule for `fᵢ` on concatenations ([Lit95] §2): if the minima
`mᵢ(π₁)` and `mᵢ(π₂)` are integers, then `fᵢ (π₁ * π₂) = (fᵢ π₁) * π₂` if `εᵢ(π₂) < φᵢ(π₁)` and
`fᵢ (π₁ * π₂) = π₁ * (fᵢ π₂)` otherwise. -/
theorem f_concat (h₁ : ∃ n : ℤ, π₁.minPairing i = n) (h₂ : ∃ n : ℤ, π₂.minPairing i = n) :
    f i (π₁.concat π₂) = if ε i π₂ < φ i π₁ then (f i π₁).map (·.concat π₂)
      else (f i π₂).map (π₁.concat ·) := by
  rw [f, rev_concat, e_concat (exists_minPairing_rev_eq h₂) (exists_minPairing_rev_eq h₁),
    ε_rev, φ_rev]
  by_cases hc : ε i π₂ < φ i π₁
  · rw [ite_eq_right (not_le.mpr hc), ite_eq_left hc]
    simp only [f, Option.map_map, Function.comp_def, rev_concat, rev_rev]
  · rw [ite_eq_left (not_lt.mp hc), ite_eq_right hc]
    simp only [f, Option.map_map, Function.comp_def, rev_concat, rev_rev]

/-- For integral paths, `(π₁, π₂) ↦ π₁ * π₂` intertwines `eᵢ` on the tensor product of path
crystals with `eᵢ` on paths ([Lit95] §2). -/
theorem e_concat_eq_tensor (h₁ : π₁.IsIntegral) (h₂ : π₂.IsIntegral) (i : ι) :
    e i (π₁.concat π₂) =
      (((crystal S).tensor (crystal S)).e i (π₁, π₂)).map fun p ↦ p.1.concat p.2 := by
  rw [Crystal.tensor_e, e_concat (h₁ i) (h₂ i)]
  change _ = Option.map _ (if ε i π₂ ≤ φ i π₁ then (e i π₁).map (·, π₂) else (e i π₂).map (π₁, ·))
  split_ifs <;> simp [Option.map_map, Function.comp_def]

/-- For integral paths, `(π₁, π₂) ↦ π₁ * π₂` intertwines `fᵢ` on the tensor product of path
crystals with `fᵢ` on paths ([Lit95] §2). -/
theorem f_concat_eq_tensor (h₁ : π₁.IsIntegral) (h₂ : π₂.IsIntegral) (i : ι) :
    f i (π₁.concat π₂) =
      (((crystal S).tensor (crystal S)).f i (π₁, π₂)).map fun p ↦ p.1.concat p.2 := by
  rw [Crystal.tensor_f, f_concat (h₁ i) (h₂ i)]
  change _ = Option.map _ (if ε i π₂ < φ i π₁ then (f i π₁).map (·, π₂) else (f i π₂).map (π₁, ·))
  split_ifs <;> simp [Option.map_map, Function.comp_def]

/-- `(π₁, π₂) ↦ π₁ * π₂` preserves `εᵢ` (no integrality needed). -/
theorem ε_concat_eq_tensor (i : ι) :
    ε i (π₁.concat π₂) = ((crystal S).tensor (crystal S)).ε i (π₁, π₂) :=
  ε_concat

/-- `(π₁, π₂) ↦ π₁ * π₂` preserves `φᵢ` (no integrality needed). -/
theorem φ_concat_eq_tensor (i : ι) :
    φ i (π₁.concat π₂) = ((crystal S).tensor (crystal S)).φ i (π₁, π₂) :=
  φ_concat

end LittelmannPath
