/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.RootOperators

/-!
# The Pitman transform and the `A₂` identities for path crystals

For a Littelmann path `π` with integral minimum `mᵢ = min hᵢ`, raising all the way with `eᵢ`
gives the **Pitman transform** `Pᵢ π(t) = π(t) - (min_{[0,t]} hᵢ) αᵢ`
(`LittelmannPath.eIter_eq_pitman`); more generally `eᵢ^k π(t) = π(t) - (min(min_{[0,t]} hᵢ,
mᵢ + k) - mᵢ - k) αᵢ` (`LittelmannPath.eIter_eq_partialPitman`).

For two colours `i, j` with `⟨αⱼ, αᵢ^∨⟩ = ⟨αᵢ, αⱼ^∨⟩ = -1` (type `A₂`), write `X = hᵢ`, `Y = hⱼ`,
`M_X(t) = min_{[0,t]} X`. The basic identity (`LittelmannPath.runningMin_add_runningMin_eq`,
[BBO05] Lemma 2.5) `M_X(t) + min_{[0,t]} hᵢ(PⱼPᵢπ) = min_{[0,t]} hᵢ(Pⱼ π)` gives the formula
`PᵢPⱼPᵢ π = π - (min_{[0,t]} hᵢ(Pⱼπ)) αᵢ - (min_{[0,t]} hⱼ(Pᵢπ)) αⱼ`
(`LittelmannPath.pitman_three_apply`), which is symmetric in `i, j`: hence `PᵢPⱼPᵢ = PⱼPᵢPⱼ`,
the braid relation for the Pitman transforms ([BBO05] Theorem 2.6 for `n = 3`). The
string-parametrization identity `min hⱼ(π) + min hᵢ(π) = min(min hᵢ(Pⱼπ), min hⱼ(Pᵢπ))`
(`LittelmannPath.minPairing_add_minPairing_eq`) gives the `A₂` transition map of string
coordinates. These are used in `LieLean.RepresentationTheory.Crystal.Path.BraidA2`.

## References

* [BBO05] P. Biane, P. Bougerol, N. O'Connell, *Littelmann paths and Brownian paths*, Duke
  Math. J. **130** (2005), 127–167, §2 (Definition 2.1, Lemmas 2.4–2.5, Theorem 2.6 for
  `n = 3`).

The arguments are reconstructed from [BBO05] §2 and written for Littelmann paths.
-/

open Set

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {D : CartanDatum ι X}
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

/-! ### Iterates of `eᵢ` -/

section Partial

variable {π ξ : LittelmannPath S} {i : ι}

lemma minPairing_le_runningMin' (π : LittelmannPath S) (i : ι) (t : 𝕜) :
    π.minPairing i ≤ π.runningMin i t := by
  rcases le_total 0 t with ht | ht
  · exact π.minPairing_le_runningMin ht
  · rw [π.runningMin_of_nonpos ht]
    exact π.minPairing_nonpos i

omit [IsStrictOrderedRing 𝕜] in
lemma runningMin_le_zero' (π : LittelmannPath S) (i : ι) (t : 𝕜) : π.runningMin i t ≤ 0 := by
  rcases le_total 0 t with ht | ht
  · exact π.runningMin_le_zero ht
  · rw [π.runningMin_of_nonpos ht]

/-- The running minimum after a partial raising: if `hᵢ(ξ) = hᵢ(π) - 2(min(M, L) - L)` with
`M = min_{[0,·]} hᵢ(π)` and `L ≤ -1`, then
`min(min_{[0,t]} hᵢ(ξ), L + 1) = min(M(t), L + 1) - min(M(t), L) + L`. -/
theorem min_runningMin_partial {L : 𝕜} (hL : L ≤ -1)
    (hξ : ∀ s, ξ.pairing i s = π.pairing i s - 2 * (min (π.runningMin i s) L - L)) (t : 𝕜) :
    min (ξ.runningMin i t) (L + 1) =
      min (π.runningMin i t) (L + 1) - min (π.runningMin i t) L + L := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [ξ.runningMin_of_nonpos ht.le, π.runningMin_of_nonpos ht.le, min_eq_right (by linarith),
      min_eq_right (by linarith)]
    ring
  set M := π.runningMin i t with hM
  -- For `s ∈ [0,t]` with `L ≤ M(s)`, `ξ` and `π` have the same `hᵢ`.
  have hsame : ∀ s, L ≤ π.runningMin i s → ξ.pairing i s = π.pairing i s := fun s hs => by
    rw [hξ, min_eq_right hs, sub_self, mul_zero, sub_zero]
  rcases le_or_gt (L + 1) M with h1 | h1
  · -- `L + 1 ≤ M`
    have hle : L + 1 ≤ ξ.runningMin i t := ξ.le_runningMin ht fun s hs => by
      have hMs : M ≤ π.runningMin i s := π.runningMin_anti hs.1 hs.2
      rw [hsame s (by linarith)]
      exact h1.trans (hMs.trans (π.runningMin_le ⟨hs.1, le_rfl⟩))
    rw [min_eq_right hle, min_eq_right h1, min_eq_right (by linarith)]
    ring
  rcases le_or_gt L M with h2 | h2
  · -- `L ≤ M < L + 1`
    have heq : ξ.runningMin i t = M := by
      apply le_antisymm
      · obtain ⟨s₀, hs₀, hs₀M⟩ := π.exists_runningMin i ht
        have hL0 : L ≤ π.runningMin i s₀ := h2.trans (π.runningMin_anti hs₀.1 hs₀.2)
        calc ξ.runningMin i t ≤ ξ.pairing i s₀ := ξ.runningMin_le hs₀
          _ = M := by rw [hsame s₀ hL0, hs₀M]
      · exact ξ.le_runningMin ht fun s hs => by
          have hMs : M ≤ π.runningMin i s := π.runningMin_anti hs.1 hs.2
          rw [hsame s (h2.trans hMs)]
          exact hMs.trans (π.runningMin_le ⟨hs.1, le_rfl⟩)
    rw [heq, min_eq_left h1.le, min_eq_right h2]
    ring
  · -- `M < L`
    have heq : ξ.runningMin i t = L := by
      apply le_antisymm
      · obtain ⟨s₀, hs₀, hs₀M⟩ := π.exists_runningMin i ht
        obtain ⟨u, hu, huL, hlt⟩ := exists_first_eq (c := L) (π.continuous_pairing i) hs₀.1
          (by rw [π.pairing_zero]; linarith) (by rw [hs₀M]; exact h2.le)
        have hMu : π.runningMin i u = L := by
          apply le_antisymm
          · exact (π.runningMin_le ⟨hu.1, le_rfl⟩).trans huL.le
          · exact π.le_runningMin hu.1 fun v hv => by
              rcases hv.2.lt_or_eq with hvu | rfl
              · exact (hlt v ⟨hv.1, hvu⟩).le
              · exact huL.ge
        calc ξ.runningMin i t ≤ ξ.pairing i u := ξ.runningMin_le ⟨hu.1, hu.2.trans hs₀.2⟩
          _ = L := by rw [hsame u hMu.ge, huL]
      · exact ξ.le_runningMin ht fun s hs => by
          have hps := π.runningMin_le (i := i) ⟨hs.1, le_rfl⟩
          rw [hξ]
          rcases le_total L (π.runningMin i s) with h3 | h3
          · rw [min_eq_right h3]
            linarith
          · rw [min_eq_left h3]
            linarith
    rw [heq, min_eq_left (by linarith), min_eq_left (by linarith), min_eq_left h2.le]
    ring

variable [FloorRing 𝕜]

/-- **Partial Pitman formula**: `eᵢ^k π(t) = π(t) - (min(M(t), mᵢ + k) - (mᵢ + k)) αᵢ` for
`mᵢ + k ≤ 0`, where `M(t) = min_{[0,t]} hᵢ`. -/
theorem eIter_eq_partialPitman (π : LittelmannPath S) (i : ι) :
    ∀ k : ℕ, π.minPairing i + k ≤ 0 →
      ∃ ξ, (crystal S).eIter i k π = some ξ ∧ ∀ t, ξ t = π t -
        (min (π.runningMin i t) (π.minPairing i + k) - (π.minPairing i + k)) • S.root i := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨π, rfl, fun t => ?_⟩
    rw [Nat.cast_zero, add_zero, min_eq_right (π.minPairing_le_runningMin' i t), sub_self,
      zero_smul, sub_zero]
  | succ k ih =>
    intro hk
    push_cast at hk
    obtain ⟨ξ, hξ, hξt⟩ := ih (by linarith)
    set L := π.minPairing i + k with hL
    have hL1 : L ≤ -1 := by linarith
    have hpair : ∀ s, ξ.pairing i s = π.pairing i s - 2 * (min (π.runningMin i s) L - L) :=
      fun s => by
        simp only [pairing, hξt, map_sub, map_smul, S.coroot_root_self, smul_eq_mul]
        ring
    have hkey := min_runningMin_partial hL1 hpair
    have hmξ : ξ.minPairing i = L := by
      have h1 := hkey 1
      have hmL : π.minPairing i ≤ L := by rw [hL]; linarith [(Nat.cast_nonneg k : (0 : 𝕜) ≤ k)]
      rw [π.runningMin_of_one_le le_rfl,
        min_eq_left (show π.minPairing i ≤ L + 1 by linarith), min_eq_left hmL] at h1
      change ξ.runningMin i 1 = L
      rcases le_total (ξ.runningMin i 1) (L + 1) with h | h
      · rw [min_eq_left h] at h1
        linarith
      · rw [min_eq_right h] at h1
        linarith
    have hQ : ξ.minPairing i ≤ -1 := by rw [hmξ]; exact hL1
    refine ⟨ξ.eRaw i hQ, by rw [Crystal.eIter_succ', hξ, Option.bind_some]; exact e_of_le hQ,
      fun t => ?_⟩
    have e : π.minPairing i + ((k + 1 : ℕ) : 𝕜) = L + 1 := by push_cast; rw [hL]; ring
    rw [eRaw_apply, eCoeff, hmξ, hkey t, hξt, e]
    module

/-- **The Pitman transform** ([BBO05] Definition 2.1, (2.3)): if `mᵢ = z` is an integer, then
`eᵢ^{-z} π = Pᵢ π` with `Pᵢ π(t) = π(t) - (min_{[0,t]} hᵢ) αᵢ`. -/
theorem eIter_eq_pitman (π : LittelmannPath S) (i : ι) {z : ℤ} (hz : π.minPairing i = z) :
    ∃ ξ, (crystal S).eIter i (-z).toNat π = some ξ ∧
      ∀ t, ξ t = π t - π.runningMin i t • S.root i := by
  have hz0 : z ≤ 0 := by exact_mod_cast hz ▸ π.minPairing_nonpos i
  have hk : ((-z).toNat : 𝕜) = -z := by exact_mod_cast Int.toNat_of_nonneg (by omega)
  obtain ⟨ξ, hξ, hξt⟩ := π.eIter_eq_partialPitman i (-z).toNat (by rw [hk, hz]; ring_nf; rfl)
  refine ⟨ξ, hξ, fun t => ?_⟩
  rw [hξt, hk, hz, show (z : 𝕜) + -z = 0 by ring, sub_zero,
    min_eq_left (π.runningMin_le_zero' i t)]

omit [OrderTopology 𝕜] in
lemma ε_of_minPairing_eq {π : LittelmannPath S} {i : ι} {z : ℤ} (hz : π.minPairing i = z) :
    ε i π = ((-z : ℤ) : WithBot ℤ) := by
  rw [ε, hz, ← Int.cast_neg, Int.floor_intCast]

end Partial

/-! ### The `A₂` identities -/

section A2

variable {π π₁ π₂ π₃ ρ₁ : LittelmannPath S} {i j : ι}

/-- [BBO05] Lemma 2.4 (one direction): if `u ≤ t₀ ≤ t` where `hᵢ(t₀) = min_{[0,t]} hᵢ`, some
`s ∈ [u, t]` has `hᵢ(s) - 2 min_{[0,s]} hᵢ = - min_{[0,u]} hᵢ` (the first time after `u` at
which `hᵢ` reaches `min_{[0,u]} hᵢ`). -/
theorem exists_pairing_sub_two_runningMin (π : LittelmannPath S) (i : ι) {u t₀ t : 𝕜}
    (hu : 0 ≤ u) (hut : u ≤ t₀) (ht₀ : t₀ ≤ t) (hmin : π.pairing i t₀ = π.runningMin i t) :
    ∃ s ∈ Icc u t, π.pairing i s - 2 * π.runningMin i s = -π.runningMin i u := by
  obtain ⟨s, hs, hsc, hlt⟩ := exists_first_eq (c := π.runningMin i u) (π.continuous_pairing i)
    hut (π.runningMin_le ⟨hu, le_rfl⟩)
    (by rw [hmin]; exact π.runningMin_anti hu (hut.trans ht₀))
  have hMs : π.runningMin i s = π.runningMin i u := by
    apply le_antisymm
    · exact (π.runningMin_le ⟨hu.trans hs.1, le_rfl⟩).trans hsc.le
    · refine π.le_runningMin (hu.trans hs.1) fun v hv => ?_
      rcases le_or_gt v u with hvu | hvu
      · exact π.runningMin_le ⟨hv.1, hvu⟩
      rcases hv.2.lt_or_eq with hvs | rfl
      · exact (hlt v ⟨hvu.le, hvs⟩).le
      · exact hsc.ge
  exact ⟨s, ⟨hs.1, hs.2.trans ht₀⟩, by rw [hsc, hMs]; ring⟩

variable (hij : S.coroot i (S.root j) = -1) (hji : S.coroot j (S.root i) = -1)
  (h₁ : ∀ t, π₁ t = π t - π.runningMin i t • S.root i)
  (h₂ : ∀ t, π₂ t = π₁ t - π₁.runningMin j t • S.root j)
  (hρ : ∀ t, ρ₁ t = π t - π.runningMin j t • S.root j)

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] in
include hji h₁ in
lemma pairing_pitman_other (s : 𝕜) : π₁.pairing j s = π.pairing j s + π.runningMin i s := by
  simp only [pairing, h₁, map_sub, map_smul, hji, smul_eq_mul]
  ring

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] in
include h₁ in
lemma pairing_pitman_self (s : 𝕜) :
    π₁.pairing i s = π.pairing i s - 2 * π.runningMin i s := by
  simp only [pairing, h₁, map_sub, map_smul, S.coroot_root_self, smul_eq_mul]
  ring

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] in
include hij h₁ h₂ in
lemma pairing_pitman_two (s : 𝕜) :
    π₂.pairing i s = π.pairing i s - 2 * π.runningMin i s + π₁.runningMin j s := by
  have := pairing_pitman_self h₁ s
  simp only [pairing] at this ⊢
  rw [h₂, map_sub, map_smul, hij, this]
  simp only [smul_eq_mul]
  ring

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] in
include hij hρ in
lemma pairing_pitman_rho (s : 𝕜) : ρ₁.pairing i s = π.pairing i s + π.runningMin j s := by
  simp only [pairing, hρ, map_sub, map_smul, hij, smul_eq_mul]
  ring

include hij hji h₁ h₂ hρ in
/-- **The key `A₂` identity** ([BBO05] Lemma 2.5, reconstructed): with `π₁ = Pᵢ π`,
`π₂ = Pⱼ π₁` and `ρ₁ = Pⱼ π`,
`min_{[0,t]} hᵢ(π) + min_{[0,t]} hᵢ(π₂) = min_{[0,t]} hᵢ(ρ₁)`. -/
theorem runningMin_add_runningMin_eq (t : 𝕜) :
    π.runningMin i t + π₂.runningMin i t = ρ₁.runningMin i t := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [π.runningMin_of_nonpos ht.le, π₂.runningMin_of_nonpos ht.le,
      ρ₁.runningMin_of_nonpos ht.le, add_zero]
  have p1j := pairing_pitman_other hji h₁
  have p2i := pairing_pitman_two hij h₁ h₂
  have pρi := pairing_pitman_rho hij hρ
  obtain ⟨t₀, ht₀, ht₀M⟩ := π.exists_runningMin i ht
  have hflat : ∀ s, t₀ ≤ s → s ≤ t → π.runningMin i s = π.runningMin i t := fun s h1 h2 =>
    le_antisymm ((π.runningMin_le ⟨ht₀.1, h1⟩).trans ht₀M.le)
      (π.runningMin_anti (ht₀.1.trans h1) h2)
  apply le_antisymm
  · -- `≤`
    obtain ⟨s, hs, hsA⟩ := ρ₁.exists_runningMin i ht
    obtain ⟨u, hu, huY⟩ := π.exists_runningMin j hs.1
    rw [pρi, ← huY] at hsA
    have hXs := π.runningMin_le (i := i) hs
    by_cases hut : u ≤ t₀
    · obtain ⟨s', hs', hs'e⟩ := π.exists_pairing_sub_two_runningMin i hu.1 hut ht₀.2 ht₀M
      have hB := π₁.runningMin_le (i := j) (t := s') ⟨hu.1, hs'.1⟩
      rw [p1j] at hB
      have h2 := π₂.runningMin_le (i := i) ⟨hu.1.trans hs'.1, hs'.2⟩
      rw [p2i] at h2
      linarith
    · have hut' : t₀ < u := not_le.mp hut
      have e1 := hflat u hut'.le (hu.2.trans hs.2)
      have e2 := hflat s (hut'.le.trans hu.2) hs.2
      have hB := π₁.runningMin_le (i := j) (t := s) hu
      rw [p1j] at hB
      have h2 := π₂.runningMin_le (i := i) hs
      rw [p2i] at h2
      linarith
  · -- `≥`
    obtain ⟨s, hs, hsM⟩ := π₂.exists_runningMin i ht
    obtain ⟨u, hu, huB⟩ := π₁.exists_runningMin j hs.1
    rw [p2i] at hsM
    rw [p1j] at huB
    by_cases hut : u ≤ t₀
    · have hA := ρ₁.runningMin_le (i := i) ht₀
      rw [pρi] at hA
      have hY := π.runningMin_le (i := j) ⟨hu.1, hut⟩
      have hXs := π.runningMin_le (i := i) (t := s) ⟨hs.1, le_rfl⟩
      have hMu := π.runningMin_anti (i := i) hu.1 hu.2
      linarith
    · have hut' : t₀ < u := not_le.mp hut
      have e1 := hflat u hut'.le (hu.2.trans hs.2)
      have e2 := hflat s (hut'.le.trans hu.2) hs.2
      have hA := ρ₁.runningMin_le (i := i) hs
      rw [pρi] at hA
      have hY := π.runningMin_le (i := j) hu
      linarith

include hij hji h₁ hρ in
/-- **String-parametrization identity** ([BBO05] §2, reconstructed): with `π₁ = Pᵢ π` and
`ρ₁ = Pⱼ π`, `min hⱼ(π) + min hᵢ(π) = min(min hᵢ(ρ₁), min hⱼ(π₁))`. -/
theorem minPairing_add_minPairing_eq :
    π.minPairing j + π.minPairing i = min (ρ₁.minPairing i) (π₁.minPairing j) := by
  have p1j := pairing_pitman_other hji h₁
  have pρi := pairing_pitman_rho hij hρ
  refine (le_antisymm ?_ ?_).symm
  · obtain ⟨tx, htx, htxM⟩ := π.exists_minPairing i
    obtain ⟨ty, hty, htyM⟩ := π.exists_minPairing j
    rcases le_total ty tx with h | h
    · have hA := ρ₁.minPairing_le (i := i) htx
      rw [pρi] at hA
      have := π.runningMin_le (i := j) ⟨hty.1, h⟩
      exact le_trans (min_le_left _ _)
        (by linarith : ρ₁.minPairing i ≤ π.minPairing j + π.minPairing i)
    · have hB := π₁.minPairing_le (i := j) hty
      rw [p1j] at hB
      have := π.runningMin_le (i := i) ⟨htx.1, h⟩
      exact le_trans (min_le_right _ _)
        (by linarith : π₁.minPairing j ≤ π.minPairing j + π.minPairing i)
  · refine le_min (ρ₁.le_runningMin zero_le_one fun s hs => ?_)
      (π₁.le_runningMin zero_le_one fun s hs => ?_)
    · rw [pρi]
      have := π.minPairing_le (i := i) hs
      have : π.minPairing j ≤ π.runningMin j s := π.runningMin_anti hs.1 hs.2
      linarith
    · rw [p1j]
      have := π.minPairing_le (i := j) hs
      have : π.minPairing i ≤ π.runningMin i s := π.runningMin_anti hs.1 hs.2
      linarith

include hij hji h₁ h₂ hρ in
/-- **The `A₂` Pitman formula** ([BBO05] Theorem 2.6, `n = 3`, reconstructed):
`PᵢPⱼPᵢ π(t) = π(t) - (min_{[0,t]} hᵢ(Pⱼπ)) αᵢ - (min_{[0,t]} hⱼ(Pᵢπ)) αⱼ`. -/
theorem pitman_three_apply (h₃ : ∀ t, π₃ t = π₂ t - π₂.runningMin i t • S.root i) (t : 𝕜) :
    π₃ t = π t - ρ₁.runningMin i t • S.root i - π₁.runningMin j t • S.root j := by
  rw [h₃, h₂, h₁, ← runningMin_add_runningMin_eq hij hji h₁ h₂ hρ t]
  module

end A2

end LittelmannPath
