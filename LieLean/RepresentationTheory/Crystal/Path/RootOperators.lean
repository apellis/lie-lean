/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Basic

/-!
# Littelmann's root operators

Let `π` be a Littelmann path, `hᵢ(t) = ⟨π(t), αᵢ^∨⟩` and `mᵢ = min_{[0,1]} hᵢ`. Littelmann's root
operators ([Lit95] §1 (check)) are defined as follows.

* If `mᵢ > -1` then `eᵢ π = 0`. Otherwise let `t₁` be the first time with `hᵢ(t₁) = mᵢ` and
  `t₀ ≤ t₁` maximal with `hᵢ ≥ mᵢ + 1` on `[0, t₀]`; `eᵢ π` is obtained by
  keeping `π` on `[0, t₀]`, reflecting by `rᵢ` those pieces of `π|[t₀, t₁]` on which `hᵢ` attains
  a new running minimum, keeping (translated) the pieces between them, and translating
  `π|[t₁, 1]` by `+αᵢ`.
* `fᵢ` is defined symmetrically, using the minima from the right; if `hᵢ(1) - mᵢ < 1` then
  `fᵢ π = 0`.

Unwinding the definition, both operators have a closed form (our reformulation): with
`m(t) = min_{[0,t]} hᵢ` and `M(t) = min_{[t,1]} hᵢ`,
`eᵢ π(t) = π(t) - (min(m(t), mᵢ + 1) - mᵢ - 1) αᵢ` and
`fᵢ π(t) = π(t) - (min(M(t), mᵢ + 1) - mᵢ) αᵢ`.
(Indeed, the coefficient of `αᵢ` in `eᵢ π(t) - π(t)` changes only where the running minimum
`m(t) ∈ [mᵢ, mᵢ + 1]` decreases, i.e. on the reflected pieces, and there it changes like `-hᵢ`.)
We take the closed formula for `eᵢ` as the definition (the piecewise recipe is not formalized) and
define `fᵢ` through the time reversal `π^∨(t) = π(1 - t) - π(1)` by `fᵢ π = (eᵢ π^∨)^∨`
([Lit95] Lemma 2.1 (check)); `LittelmannPath.f_apply` recovers the closed formula for `fᵢ`.

## Main definitions

* `LittelmannPath.eRaw`, `LittelmannPath.e`: the root operator `eᵢ`.
* `LittelmannPath.f`: the root operator `fᵢ = ∨ ∘ eᵢ ∘ ∨`.
* `LittelmannPath.ε`, `LittelmannPath.φ`: `εᵢ(π) = ⌊-mᵢ⌋` and `φᵢ(π) = ⌊hᵢ(1) - mᵢ⌋`.
* `LittelmannPath.crystal S`: the crystal of all Littelmann paths.
* `Crystal.dual`: the dual crystal `B^∨` (weights negated, `ẽᵢ` and `f̃ᵢ` exchanged).
* `LittelmannPath.revEquiv`: the time reversal `π ↦ π^∨`, an isomorphism of `B` onto `B^∨`.

## Main results

* `LittelmannPath.minPairing_eRaw`: `eᵢ` raises the minimum `mᵢ` by `1`.
* `LittelmannPath.f_apply`: the closed formula for `fᵢ`.
* `LittelmannPath.f_eq_some_iff`: `fᵢ π = π'` if and only if `eᵢ π' = π` ([Lit95] Lemma 2.1
  (check)); in particular `eᵢ` and `fᵢ` are inverse to each other where defined.
* `LittelmannPath.isSeminormal_crystal`: the path crystal is seminormal: `εᵢ(π)` (resp. `φᵢ(π)`)
  is the maximal number of times `eᵢ` (resp. `fᵢ`) can be applied to `π`.

Littelmann works with paths whose minima `mᵢ` are integers ("integral paths", [Lit95] §2
(check)), for which `εᵢ = -mᵢ` and `φᵢ = hᵢ(1) - mᵢ`. With the definitions above (via the running
minima; reflecting the whole of `π|[t₀, t₁]` instead would need integrality hypotheses) no
integrality is needed: all paths with endpoint in `X` form a seminormal crystal, with
`εᵢ = ⌊-mᵢ⌋`. The proof that `eᵢ` and `fᵢ` are mutually inverse
(`LittelmannPath.min_rightMin_eRaw`) was reconstructed by us from the closed formulas.

## References

* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995).
-/

open Set

/-! ### The dual crystal -/

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B : Type*}

/-- The dual crystal `B^∨` ([Kas] §7.4 (check)): the same set, with `wt^∨ = -wt`, `εᵢ^∨ = φᵢ`,
`φᵢ^∨ = εᵢ`, `ẽᵢ^∨ = f̃ᵢ` and `f̃ᵢ^∨ = ẽᵢ`. -/
def dual (C : Crystal D B) : Crystal D B where
  wt b := -C.wt b
  ε := C.φ
  φ := C.ε
  e := C.f
  f := C.e
  φ_eq i b := by
    rw [C.φ_eq, map_neg]
    induction C.ε i b using WithBot.recBotCoe with
    | bot => rfl
    | coe a => rw [← WithBot.coe_add, ← WithBot.coe_add, add_neg_cancel_right]
  f_eq_some_iff i b b' := C.e_eq_some_iff
  wt_e i b b' h := by rw [C.wt_f h, neg_sub, sub_eq_neg_add]
  ε_e i b b' h := C.φ_f h
  e_eq_none_of_φ_eq_bot i b h := C.f_eq_none_of_ε_eq_bot h

variable (C : Crystal D B)

@[simp] lemma dual_wt (b : B) : C.dual.wt b = -C.wt b := rfl

@[simp] lemma dual_ε (i : ι) (b : B) : C.dual.ε i b = C.φ i b := rfl

@[simp] lemma dual_φ (i : ι) (b : B) : C.dual.φ i b = C.ε i b := rfl

@[simp] lemma dual_e (i : ι) (b : B) : C.dual.e i b = C.f i b := rfl

@[simp] lemma dual_f (i : ι) (b : B) : C.dual.f i b = C.e i b := rfl

end Crystal

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {D : CartanDatum ι X}
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

/-! ### The operator `eᵢ` -/

section eRaw

variable (π : LittelmannPath S) (i : ι) {t : 𝕜}

/-- The coefficient `c(t) = min(min_{[0,t]} hᵢ, mᵢ + 1) - (mᵢ + 1) ∈ [-1, 0]` in
`eᵢ π = π - c αᵢ`. -/
noncomputable def eCoeff (t : 𝕜) : 𝕜 :=
  min (π.runningMin i t) (π.minPairing i + 1) - (π.minPairing i + 1)

lemma continuous_eCoeff : Continuous (π.eCoeff i) :=
  ((π.continuous_runningMin i).min continuous_const).sub continuous_const

omit [OrderTopology 𝕜] in
lemma eCoeff_of_nonpos (hQ : π.minPairing i ≤ -1) (ht : t ≤ 0) : π.eCoeff i t = 0 := by
  rw [eCoeff, π.runningMin_of_nonpos ht, min_eq_right (by linarith), sub_self]

lemma eCoeff_of_one_le (ht : 1 ≤ t) : π.eCoeff i t = -1 := by
  rw [eCoeff, π.runningMin_of_one_le ht, min_eq_left (by linarith)]
  ring

/-- The path `eᵢ π(t) = π(t) - (min(min_{[0,t]} hᵢ, mᵢ + 1) - mᵢ - 1) αᵢ`, defined when
`mᵢ ≤ -1` ([Lit95] §1 (check)). -/
noncomputable def eRaw (hQ : π.minPairing i ≤ -1) : LittelmannPath S where
  toFun t := π t - π.eCoeff i t • S.root i
  wt := π.wt + D.root i
  toFun_of_nonpos' t ht := by
    rw [π.apply_of_nonpos ht, π.eCoeff_of_nonpos i hQ ht, zero_smul, sub_zero]
  toFun_of_one_le' t ht := by
    rw [π.apply_of_one_le ht, π.eCoeff_of_one_le i ht, map_add, CartanDatum.PathSpace.root]
    module
  continuous_coroot' j := by
    simp only [map_sub, map_smul, smul_eq_mul]
    exact (π.continuous_pairing j).sub ((π.continuous_eCoeff i).mul continuous_const)

variable (hQ : π.minPairing i ≤ -1)

lemma eRaw_apply (t : 𝕜) : π.eRaw i hQ t = π t - π.eCoeff i t • S.root i := rfl

@[simp] lemma wt_eRaw : (π.eRaw i hQ).wt = π.wt + D.root i := rfl

lemma pairing_eRaw (j : ι) (t : 𝕜) :
    (π.eRaw i hQ).pairing j t = π.pairing j t - π.eCoeff i t * D.cartanMatrix j i := by
  simp only [pairing, eRaw_apply, map_sub, map_smul, smul_eq_mul, S.coroot_root]

lemma pairing_eRaw_self (t : 𝕜) :
    (π.eRaw i hQ).pairing i t = π.pairing i t - 2 * π.eCoeff i t := by
  rw [pairing_eRaw, D.cartanMatrix_self]
  push_cast
  ring

lemma pairing_one_eRaw : (π.eRaw i hQ).pairing i 1 = π.pairing i 1 + 2 := by
  rw [pairing_eRaw_self, π.eCoeff_of_one_le i le_rfl]
  ring

/-- The key identity behind `eᵢ fᵢ = id` and `fᵢ eᵢ = id` (reconstructed from the closed
formulas): if `mᵢ ≤ -1` and `h = hᵢ(eᵢ π)`, then for `s ∈ [0,1]`,
`min(min_{[s,1]} h, mᵢ + 2) = 2mᵢ + 2 - min(min_{[0,s]} hᵢ, mᵢ + 1)`. -/
theorem min_rightMin_eRaw {s : 𝕜} (hs : s ∈ Icc (0 : 𝕜) 1) :
    min ((π.eRaw i hQ).rightMin i s) (π.minPairing i + 2) =
      2 * π.minPairing i + 2 - min (π.runningMin i s) (π.minPairing i + 1) := by
  have hg : ∀ u, (π.eRaw i hQ).pairing i u =
      π.pairing i u - 2 * (min (π.runningMin i u) (π.minPairing i + 1) - (π.minPairing i + 1)) :=
    fun u ↦ π.pairing_eRaw_self i hQ u
  apply le_antisymm
  · by_cases hc : min (π.runningMin i s) (π.minPairing i + 1) ≤ π.minPairing i
    · exact (min_le_right _ _).trans (by linarith)
    replace hc := not_le.mp hc
    have hcm : min (π.runningMin i s) (π.minPairing i + 1) ≤ π.runningMin i s := min_le_left _ _
    have hcQ : min (π.runningMin i s) (π.minPairing i + 1) ≤ π.minPairing i + 1 :=
      min_le_right _ _
    obtain ⟨u₀, hu₀, hu₀Q⟩ := π.exists_minPairing i
    have hsu₀ : s < u₀ := by
      by_contra h
      have := π.runningMin_le (i := i) ⟨hu₀.1, not_lt.mp h⟩
      linarith
    have hhs := hcm.trans (π.runningMin_le (i := i) ⟨hs.1, le_rfl⟩)
    obtain ⟨u, hu, huc, hlt⟩ :=
      exists_first_eq (π.continuous_pairing i) hsu₀.le hhs (by linarith)
    have hmu : min (π.runningMin i s) (π.minPairing i + 1) ≤ π.runningMin i u :=
      π.le_runningMin (hs.1.trans hu.1) fun p hp ↦ by
        rcases le_or_gt p s with hps | hps
        · exact hcm.trans (π.runningMin_le ⟨hp.1, hps⟩)
        rcases hp.2.lt_or_eq with hpu | rfl
        · exact (hlt p ⟨hps.le, hpu⟩).le
        · exact huc.ge
    have hcu : min (π.runningMin i u) (π.minPairing i + 1) =
        min (π.runningMin i s) (π.minPairing i + 1) :=
      le_antisymm (min_le_min_right _ (π.runningMin_anti hs.1 hu.1)) (le_min hmu hcQ)
    have := (π.eRaw i hQ).rightMin_le (i := i) (t := s) ⟨hu.1, hu.2.trans hu₀.2⟩
    rw [hg u, huc, hcu] at this
    exact (min_le_left _ _).trans (by linarith)
  · refine le_min ((π.eRaw i hQ).le_rightMin hs.2 fun u hu ↦ ?_) ?_
    · have hu0 : 0 ≤ u := hs.1.trans hu.1
      have hmu := π.runningMin_le (i := i) ⟨hu0, le_rfl⟩
      have hanti := min_le_min_right (π.minPairing i + 1) (π.runningMin_anti (i := i) hs.1 hu.1)
      rw [hg u]
      rcases le_total (π.runningMin i u) (π.minPairing i + 1) with h1 | h1
      · rw [min_eq_left h1] at hanti ⊢
        linarith
      · rw [min_eq_right h1] at hanti ⊢
        linarith [min_le_right (π.runningMin i s) (π.minPairing i + 1)]
    · have := le_min (π.minPairing_le_runningMin (i := i) hs.1)
        (by linarith : π.minPairing i ≤ π.minPairing i + 1)
      linarith

/-- `eᵢ` raises the minimum `mᵢ` by one. -/
theorem minPairing_eRaw : (π.eRaw i hQ).minPairing i = π.minPairing i + 1 := by
  have h := π.min_rightMin_eRaw i hQ ⟨le_rfl, zero_le_one⟩
  rw [rightMin_zero, π.runningMin_of_nonpos le_rfl,
    min_eq_right (by linarith : π.minPairing i + 1 ≤ 0)] at h
  rcases le_total ((π.eRaw i hQ).minPairing i) (π.minPairing i + 2) with h' | h'
  · rw [min_eq_left h'] at h
    linarith
  · rw [min_eq_right h'] at h
    linarith

lemma minPairing_rev_eRaw_le : (π.eRaw i hQ).rev.minPairing i ≤ -1 := by
  rw [minPairing_rev, minPairing_eRaw, pairing_one_eRaw]
  linarith [π.minPairing_le_pairing_one i]

/-- `eᵢ (eᵢ π)^∨ = π^∨`: the core of `fᵢ eᵢ = id` and `eᵢ fᵢ = id`. -/
theorem eRaw_rev_eRaw :
    (π.eRaw i hQ).rev.eRaw i (π.minPairing_rev_eRaw_le i hQ) = π.rev := by
  refine ext_of_eqOn fun t ht ↦ ?_
  have ht' : 1 - t ∈ Icc (0 : 𝕜) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have key : (π.eRaw i hQ).rev.eCoeff i t = -π.eCoeff i (1 - t) - 1 := by
    have h := π.min_rightMin_eRaw i hQ ht'
    rw [eCoeff, eCoeff, (π.eRaw i hQ).runningMin_rev ht, minPairing_rev, minPairing_eRaw,
      pairing_one_eRaw]
    have : min ((π.eRaw i hQ).rightMin i (1 - t) - (π.pairing i 1 + 2))
        (π.minPairing i + 1 - (π.pairing i 1 + 2) + 1) =
        min ((π.eRaw i hQ).rightMin i (1 - t)) (π.minPairing i + 2) - (π.pairing i 1 + 2) := by
      rw [← min_sub_sub_right]
      congr 1
      ring
    rw [this, h]
    ring
  rw [eRaw_apply, key, rev_apply, rev_apply, eRaw_apply, eRaw_apply, π.eCoeff_of_one_le i le_rfl]
  module

end eRaw

/-! ### The root operators -/

/-- Littelmann's root operator `eᵢ` ([Lit95] §1 (check)): `eᵢ π = 0` (modelled by `none`) if
`mᵢ > -1`, and otherwise `eᵢ π(t) = π(t) - (min(min_{[0,t]} hᵢ, mᵢ + 1) - mᵢ - 1) αᵢ`. -/
noncomputable def e (i : ι) (π : LittelmannPath S) : Option (LittelmannPath S) :=
  if hQ : π.minPairing i ≤ -1 then some (π.eRaw i hQ) else none

/-- Littelmann's root operator `fᵢ = ∨ ∘ eᵢ ∘ ∨` ([Lit95] §1, Lemma 2.1 (check)); explicitly,
`fᵢ π = 0` if `hᵢ(1) - mᵢ < 1` and otherwise
`fᵢ π(t) = π(t) - (min(min_{[t,1]} hᵢ, mᵢ + 1) - mᵢ) αᵢ`. -/
noncomputable def f (i : ι) (π : LittelmannPath S) : Option (LittelmannPath S) :=
  (e i π.rev).map rev

variable {i : ι} {π π' : LittelmannPath S}

lemma e_of_le (hQ : π.minPairing i ≤ -1) : e i π = some (π.eRaw i hQ) := by
  simp [e, hQ]

lemma e_eq_none_iff : e i π = none ↔ -1 < π.minPairing i := by
  rw [e]
  split_ifs with hQ
  · simp [hQ]
  · simpa using hQ

lemma e_eq_some_iff : e i π = some π' ↔ ∃ hQ, π.eRaw i hQ = π' := by
  rw [e]
  split_ifs with hQ
  · simp [hQ]
  · simp [hQ]

lemma f_eq_none_iff : f i π = none ↔ π.pairing i 1 - π.minPairing i < 1 := by
  rw [f, Option.map_eq_none_iff, e_eq_none_iff, minPairing_rev]
  constructor <;> intro h <;> linarith

lemma minPairing_of_e_eq_some (h : e i π = some π') :
    π'.minPairing i = π.minPairing i + 1 := by
  obtain ⟨hQ, rfl⟩ := e_eq_some_iff.mp h
  exact π.minPairing_eRaw i hQ

lemma wt_of_e_eq_some (h : e i π = some π') : π'.wt = π.wt + D.root i := by
  obtain ⟨hQ, rfl⟩ := e_eq_some_iff.mp h
  rfl

theorem e_rev_of_e_eq_some (h : e i π = some π') : e i π'.rev = some π.rev := by
  obtain ⟨hQ, rfl⟩ := e_eq_some_iff.mp h
  rw [e_of_le (π.minPairing_rev_eRaw_le i hQ), eRaw_rev_eRaw]

/-- `fᵢ π = π'` if and only if `eᵢ π' = π` ([Lit95] Lemma 2.1 (check)). -/
theorem f_eq_some_iff : f i π = some π' ↔ e i π' = some π := by
  constructor
  · intro h
    obtain ⟨ρ, hρ, rfl⟩ := Option.map_eq_some_iff.mp h
    simpa using e_rev_of_e_eq_some hρ
  · intro h
    rw [f, e_rev_of_e_eq_some h, Option.map_some, rev_rev]

lemma rev_f (i : ι) (π : LittelmannPath S) : (f i π).map rev = e i π.rev := by
  rw [f, Option.map_map]
  simp [Function.comp_def]

lemma f_rev (i : ι) (π : LittelmannPath S) : f i π.rev = (e i π).map rev := by
  rw [f, rev_rev]

@[simp] lemma pairing_one_rev (i : ι) (π : LittelmannPath S) :
    π.rev.pairing i 1 = -π.pairing i 1 := by
  rw [pairing_rev, sub_self, pairing_zero, zero_sub]

/-- The closed formula for `fᵢ` ([Lit95] §1 (check), in our reformulation): if `fᵢ π = π'` then
`π'(t) = π(t) - (min(min_{[t,1]} hᵢ, mᵢ + 1) - mᵢ) αᵢ` for `t ∈ [0,1]`. -/
theorem f_apply (h : f i π = some π') {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) :
    π' t = π t - (min (π.rightMin i t) (π.minPairing i + 1) - π.minPairing i) • S.root i := by
  obtain ⟨ρ, hρ, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hQ, rfl⟩ := e_eq_some_iff.mp hρ
  have ht' : 1 - t ∈ Icc (0 : 𝕜) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have key : min (π.rightMin i t - π.pairing i 1) (π.minPairing i - π.pairing i 1 + 1) =
      min (π.rightMin i t) (π.minPairing i + 1) - π.pairing i 1 := by
    rw [← min_sub_sub_right]
    congr 1
    ring
  rw [rev_apply, eRaw_apply, eRaw_apply, π.rev.eCoeff_of_one_le i le_rfl, eCoeff,
    π.runningMin_rev ht', sub_sub_cancel, minPairing_rev, key, rev_apply, rev_apply, sub_self,
    apply_zero, sub_sub_cancel]
  module

/-! ### The path crystal -/

variable [FloorRing 𝕜]

/-- `εᵢ(π) = ⌊-mᵢ⌋` (for integral paths, `-mᵢ`). -/
noncomputable def ε (i : ι) (π : LittelmannPath S) : WithBot ℤ := (⌊-π.minPairing i⌋ : ℤ)

/-- `φᵢ(π) = ⌊hᵢ(1) - mᵢ⌋` (for integral paths, `hᵢ(1) - mᵢ`). -/
noncomputable def φ (i : ι) (π : LittelmannPath S) : WithBot ℤ :=
  (⌊π.pairing i 1 - π.minPairing i⌋ : ℤ)

variable (S) in
/-- The crystal of Littelmann paths ([Lit95] §1–2 (check)): the set of all (parametrized)
Littelmann paths with endpoint in `X`, with `wt π = π(1)`, `εᵢ(π) = ⌊-mᵢ⌋`,
`φᵢ(π) = ⌊hᵢ(1) - mᵢ⌋` and Littelmann's root operators. -/
noncomputable def crystal : Crystal D (LittelmannPath S) where
  wt := wt
  ε := ε
  φ := φ
  e := e
  f := f
  φ_eq i π := by
    simp only [ε, φ, pairing_one]
    rw [show ((D.coroot i π.wt : ℤ) : 𝕜) - π.minPairing i =
      -π.minPairing i + (D.coroot i π.wt : ℤ) by ring, Int.floor_add_intCast, WithBot.coe_add]
  f_eq_some_iff _ _ _ := f_eq_some_iff
  wt_e _ _ _ h := wt_of_e_eq_some h
  ε_e i π π' h := by
    simp only [ε, minPairing_of_e_eq_some h]
    rw [neg_add, ← sub_eq_add_neg, Int.floor_sub_one, ← WithBot.coe_one, ← WithBot.coe_add,
      sub_add_cancel]
  e_eq_none_of_φ_eq_bot _ _ h := by simp [φ] at h

@[simp] lemma crystal_wt (π : LittelmannPath S) : (crystal S).wt π = π.wt := rfl

@[simp] lemma crystal_ε (i : ι) (π : LittelmannPath S) : (crystal S).ε i π = ε i π := rfl

@[simp] lemma crystal_φ (i : ι) (π : LittelmannPath S) : (crystal S).φ i π = φ i π := rfl

@[simp] lemma crystal_e (i : ι) (π : LittelmannPath S) : (crystal S).e i π = e i π := rfl

@[simp] lemma crystal_f (i : ι) (π : LittelmannPath S) : (crystal S).f i π = f i π := rfl

variable (S) in
/-- The crystal of Littelmann paths is seminormal: `εᵢ(π)` (resp. `φᵢ(π)`) is the maximal number
of times `eᵢ` (resp. `fᵢ`) can be applied to `π` ([Lit95] Lemma 2.1 (check)). -/
theorem isSeminormal_crystal : (crystal S).IsSeminormal := by
  rw [Crystal.isSeminormal_iff]
  intro i π
  simp only [crystal_ε, crystal_φ, crystal_e, crystal_f, ε, φ]
  have hQ := π.minPairing_nonpos i
  have h1 := π.minPairing_le_pairing_one i
  refine ⟨?_, ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · exact_mod_cast Int.floor_nonneg.mpr (by linarith)
  · exact_mod_cast Int.floor_nonneg.mpr (by linarith)
  · rw [e_eq_none_iff] at h
    rw [Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩]
    rfl
  · rw [f_eq_none_iff] at h
    rw [Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩]
    rfl

/-! ### Time reversal -/

lemma φ_rev (i : ι) (π : LittelmannPath S) : φ i π.rev = ε i π := by
  rw [φ, ε, pairing_one_rev, minPairing_rev]
  ring_nf

lemma ε_rev (i : ι) (π : LittelmannPath S) : ε i π.rev = φ i π := by
  rw [← φ_rev, rev_rev]

variable (S) in
/-- The time reversal `π ↦ π^∨`, `π^∨(t) = π(1 - t) - π(1)`, is an isomorphism from the path
crystal onto its dual ([Lit95] §1, Lemma 2.1 (check)): it negates weights, exchanges `εᵢ` and
`φᵢ`, and exchanges `eᵢ` and `fᵢ`. -/
noncomputable def revEquiv : Crystal.Equiv (crystal S) (crystal S).dual where
  toFun := rev
  invFun := rev
  left_inv := rev_rev
  right_inv := rev_rev
  wt_map π := by simp
  ε_map i π := φ_rev i π
  e_map i π := by simp [f_rev]
  f_map i π := by simp [rev_f]

end LittelmannPath
