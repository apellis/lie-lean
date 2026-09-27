/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.LS

/-!
# Littelmann's cancelling involution

For the path-model Weyl character formula ([Lit95] §9 (check)) and the Littlewood–Richardson
rule ([Lit94]) one pairs off the paths leaving a (shifted) dominant chamber. Fix integer levels
`cⱼ ≤ -1` (`cⱼ = -1` for the character formula, `cⱼ = -1 - ⟨ν, αⱼ^∨⟩` for the LR rule with
respect to `ν`). For a path `η` some of whose functions `hⱼ = ⟨η, αⱼ^∨⟩` reach `cⱼ`, let `τ` be the
first time at which this happens (`LittelmannPath.hitTime`) and `i` a chosen index with
`hᵢ(τ) = cᵢ` (`LittelmannPath.hitIndex`). With `n = ⟨wt η, αᵢ^∨⟩ - cᵢ`, the path
`η' = fᵢ^n η` (if `n ≥ 0`) or `eᵢ^{-n} η` (if `n < 0`) agrees with `η` up to `τ`: the root
operators only act after the last (for `fᵢ`) resp. before the first (for `eᵢ`) minimum of `hᵢ`,
and these lie after `τ` (`LittelmannPath.FirstHit.f_eqOn`, `LittelmannPath.FirstHit.e_eqOn`). Its
weight is `rᵢ(wt η) + cᵢ αᵢ` (for `cᵢ = -1`: `wt η' + ρ = rᵢ(wt η + ρ)`), it has the same `τ` and
`i`, and `η ↦ η'` is an involution (`LittelmannPath.exists_reflectAfter_hitIndex`). In
Littelmann's formulation, `η'` is obtained by applying the simple reflection `sᵢ` to the part of
`η` after `τ`; we use the root operators directly, which avoids cutting and reparametrizing
paths.

## Main definitions

* `LittelmannPath.FirstHit η i t₀ c`: `hᵢ > c` on `[0, t₀)` and `hᵢ(t₀) = c`.
* `LittelmannPath.reflectAfter η i c`: `fᵢ^n η` or `eᵢ^{-n} η`, `n = ⟨wt η, αᵢ^∨⟩ - c`.
* `LittelmannPath.hitTime`, `LittelmannPath.hitIndex`: the first time some `hⱼ` reaches `cⱼ`, and
  a chosen such index.

## Main results

* `LittelmannPath.FirstHit.reflectAfter`: the properties of `reflectAfter` under `FirstHit`.
* `LittelmannPath.exists_reflectAfter_hitIndex`: Littelmann's involution.

## References

* [Lit94] P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*,
  Invent. Math. **116** (1994), 329–346.
* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
-/

open Set

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [FloorRing 𝕜]
  {D : CartanDatum ι X} {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

/-! ### Root operators acting after a time `t₀` -/

section After

variable {η ξ ξ' : LittelmannPath S} {i : ι} {t₀ : 𝕜} {c : ℤ}

/-- The hypothesis on `η` for the operators `fᵢ` and `eᵢ` to leave `η|[0, t₀]` unchanged:
`hᵢ > c` on `[0, t₀)` and `hᵢ(t₀) = c`, for an integer level `c`. -/
def FirstHit (η : LittelmannPath S) (i : ι) (t₀ : 𝕜) (c : ℤ) : Prop :=
  t₀ ∈ Icc (0 : 𝕜) 1 ∧ (∀ t ∈ Ico 0 t₀, (c : 𝕜) < η.pairing i t) ∧ η.pairing i t₀ = c

omit [IsStrictOrderedRing 𝕜] [FloorRing 𝕜] in
lemma FirstHit.minPairing_le (h : η.FirstHit i t₀ c) : η.minPairing i ≤ c :=
  h.2.2 ▸ η.minPairing_le h.1

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] [FloorRing 𝕜] in
lemma FirstHit.of_eqOn (h : η.FirstHit i t₀ c) (heq : ∀ t ∈ Icc 0 t₀, ξ t = η t) :
    ξ.FirstHit i t₀ c :=
  ⟨h.1, fun t ht ↦ by rw [pairing, heq t ⟨ht.1, ht.2.le⟩]; exact h.2.1 t ht,
    by rw [pairing, heq t₀ ⟨h.1.1, le_rfl⟩]; exact h.2.2⟩

omit [FloorRing 𝕜] in
/-- Under `FirstHit`, `fᵢ` does not change the path on `[0, t₀]`. -/
lemma FirstHit.f_eqOn (h : η.FirstHit i t₀ c) (hf : f i η = some ξ) :
    ∀ t ∈ Icc 0 t₀, ξ t = η t := by
  intro t ht
  obtain ⟨p, hp, hpm⟩ := η.exists_minPairing i
  have hpt : t₀ ≤ p := by
    by_contra hlt
    have := h.2.1 p ⟨hp.1, not_le.mp hlt⟩
    linarith [h.minPairing_le]
  have hr : η.rightMin i t = η.minPairing i := le_antisymm
    ((η.rightMin_le ⟨ht.2.trans hpt, hp.2⟩).trans hpm.le)
    (η.le_rightMin (ht.2.trans h.1.2) fun u hu ↦ η.minPairing_le ⟨ht.1.trans hu.1, hu.2⟩)
  rw [f_apply hf ⟨ht.1, ht.2.trans h.1.2⟩, hr, min_eq_left (by linarith), sub_self, zero_smul,
    sub_zero]

omit [FloorRing 𝕜] in
/-- Under `FirstHit`, if `mᵢ + 1 ≤ c` then `eᵢ` does not change the path on `[0, t₀]`. -/
lemma FirstHit.e_eqOn (h : η.FirstHit i t₀ c) (hm : η.minPairing i + 1 ≤ c)
    (he : e i η = some ξ) : ∀ t ∈ Icc 0 t₀, ξ t = η t := by
  intro t ht
  obtain ⟨hQ, rfl⟩ := e_eq_some_iff.mp he
  have hr : η.minPairing i + 1 ≤ η.runningMin i t := η.le_runningMin ht.1 fun s hs ↦ by
    rcases eq_or_lt_of_le (hs.2.trans ht.2) with hst | hst
    · rw [hst, h.2.2]; linarith
    · linarith [h.2.1 s ⟨hs.1, hst⟩]
  rw [eRaw_apply, eCoeff, min_eq_right hr, sub_self, zero_smul, sub_zero]

omit [FloorRing 𝕜] in
lemma minPairing_of_f_eq_some (hf : f i η = some ξ) : ξ.minPairing i = η.minPairing i - 1 := by
  rw [minPairing_of_e_eq_some (f_eq_some_iff.mp hf)]
  ring

omit [FloorRing 𝕜] in
lemma wt_of_f_eq_some (hf : f i η = some ξ) : ξ.wt = η.wt - D.root i := by
  rw [wt_of_e_eq_some (f_eq_some_iff.mp hf), add_sub_cancel_right]

/-- Iterating `fᵢ` under `FirstHit`. -/
lemma FirstHit.fIter (h : η.FirstHit i t₀ c) :
    ∀ k : ℕ, (k : 𝕜) ≤ η.pairing i 1 - η.minPairing i →
      ∃ ξ, (crystal S).fIter i k η = some ξ ∧ (∀ t ∈ Icc 0 t₀, ξ t = η t) ∧
        ξ.wt = η.wt - k • D.root i ∧ ξ.minPairing i = η.minPairing i - k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨η, rfl, fun _ _ ↦ rfl, by simp, by simp⟩
  | succ k ih =>
    intro hk
    push_cast at hk
    obtain ⟨ξ, hξ, heq, hwt, hm⟩ := ih (by linarith)
    have hξ1 : ξ.pairing i 1 = η.pairing i 1 - 2 * k := by
      rw [pairing_one, pairing_one, hwt, map_sub, map_nsmul, D.coroot_root_self]
      simp
      ring
    obtain ⟨ξ', hξ'⟩ : ∃ ξ', f i ξ = some ξ' := by
      rw [← Option.ne_none_iff_exists', Ne, f_eq_none_iff, not_lt, hξ1, hm]
      linarith
    refine ⟨ξ', by rw [Crystal.fIter_succ', hξ, Option.bind_some]; exact hξ',
      fun t ht ↦ ((h.of_eqOn heq).f_eqOn hξ' t ht).trans (heq t ht), ?_, ?_⟩
    · rw [wt_of_f_eq_some hξ', hwt, succ_nsmul]
      abel
    · rw [minPairing_of_f_eq_some hξ', hm]
      push_cast
      ring

/-- Iterating `eᵢ` under `FirstHit`. -/
lemma FirstHit.eIter (h : η.FirstHit i t₀ c) (hc : c ≤ -1) :
    ∀ k : ℕ, η.minPairing i + k ≤ c →
      ∃ ξ, (crystal S).eIter i k η = some ξ ∧ (∀ t ∈ Icc 0 t₀, ξ t = η t) ∧
        ξ.wt = η.wt + k • D.root i ∧ ξ.minPairing i = η.minPairing i + k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨η, rfl, fun _ _ ↦ rfl, by simp, by simp⟩
  | succ k ih =>
    intro hk
    push_cast at hk
    obtain ⟨ξ, hξ, heq, hwt, hm⟩ := ih (by linarith)
    have hξm : ξ.minPairing i + 1 ≤ c := by rw [hm]; linarith
    have hc' : (c : 𝕜) ≤ -1 := by exact_mod_cast hc
    obtain ⟨ξ', hξ'⟩ : ∃ ξ', e i ξ = some ξ' := by
      rw [← Option.ne_none_iff_exists', Ne, e_eq_none_iff, not_lt]
      linarith
    refine ⟨ξ', by rw [Crystal.eIter_succ', hξ, Option.bind_some]; exact hξ',
      fun t ht ↦ ((h.of_eqOn heq).e_eqOn hξm hξ' t ht).trans (heq t ht), ?_, ?_⟩
    · rw [wt_of_e_eq_some hξ', hwt, succ_nsmul]
      abel
    · rw [minPairing_of_e_eq_some hξ', hm]
      push_cast
      ring

end After

/-! ### The involution -/

section Reflect

variable {η : LittelmannPath S} {i : ι} {t₀ : 𝕜} {c : ℤ}

/-- `Sᵢ'(η) = fᵢ^n η` if `n = ⟨wt η, αᵢ^∨⟩ - c ≥ 0` and `eᵢ^{-n} η` otherwise. Under `FirstHit`
at `t₀` with level `c` it only changes the part of `η` after `t₀`, which it reflects so that
`wt Sᵢ'(η) = rᵢ(wt η) + c αᵢ` (`LittelmannPath.FirstHit.reflectAfter`); for `c = -1`,
`wt Sᵢ'(η) + ρ = rᵢ (wt η + ρ)`. -/
noncomputable def reflectAfter (η : LittelmannPath S) (i : ι) (c : ℤ) :
    Option (LittelmannPath S) :=
  if 0 ≤ D.coroot i η.wt - c then (crystal S).fIter i (D.coroot i η.wt - c).toNat η
  else (crystal S).eIter i (-(D.coroot i η.wt - c)).toNat η

/-- Littelmann's reflection of the part of a path after its first hitting time of `hᵢ = c`
([Lit95] §9 (check); in our formulation): if `hᵢ > c` on `[0, t₀)` and `hᵢ(t₀) = c ≤ -1`, then
`reflectAfter η i c` is a path agreeing with `η` on `[0, t₀]`, of weight `rᵢ(wt η) + c αᵢ`, and
`reflectAfter · i c` is an involution on such paths. -/
theorem FirstHit.reflectAfter (h : η.FirstHit i t₀ c) (hc : c ≤ -1) :
    ∃ η', reflectAfter η i c = some η' ∧ (∀ t ∈ Icc 0 t₀, η' t = η t) ∧
      η'.wt = D.reflection i η.wt + c • D.root i ∧
      LittelmannPath.reflectAfter η' i c = some η := by
  have hm := h.minPairing_le
  have h1 : η.minPairing i ≤ η.pairing i 1 := η.minPairing_le_pairing_one i
  have hp1 : η.pairing i 1 = D.coroot i η.wt := η.pairing_one i
  set n := D.coroot i η.wt - c with hn
  rcases le_or_gt 0 n with hn0 | hn0
  · obtain ⟨η', hη', heq, hwt, -⟩ := h.fIter n.toNat (by
      rw [show ((n.toNat : ℕ) : 𝕜) = (n : 𝕜) by exact_mod_cast Int.toNat_of_nonneg hn0, hn]
      push_cast
      linarith)
    have hwt' : η'.wt = D.reflection i η.wt + c • D.root i := by
      rw [hwt, D.reflection_apply, ← natCast_zsmul, Int.toNat_of_nonneg hn0, hn, sub_smul]
      abel
    have hn' : D.coroot i η'.wt - c = -n := by
      rw [hwt', map_add, D.coroot_reflection, map_zsmul, D.coroot_root_self, hn, smul_eq_mul]
      ring
    refine ⟨η', by
      rw [LittelmannPath.reflectAfter, ite_eq_left (by rw [← hn]; exact hn0)]; exact hη',
      heq, hwt', ?_⟩
    rw [LittelmannPath.reflectAfter, hn']
    rcases eq_or_lt_of_le hn0 with hn00 | hn00
    · rw [← hn00, neg_zero, ite_eq_left le_rfl]
      rw [← hn00] at hη'
      simpa using hη'.symm
    · rw [ite_eq_right (by omega), neg_neg]
      exact ((crystal S).fIter_eq_some_iff _ _ _).mp hη'
  · obtain ⟨η', hη', heq, hwt, -⟩ := h.eIter hc (-n).toNat (by
      rw [show (((-n).toNat : ℕ) : 𝕜) = ((-n : ℤ) : 𝕜) by
        exact_mod_cast Int.toNat_of_nonneg (by omega), hn]
      push_cast
      linarith)
    have hwt' : η'.wt = D.reflection i η.wt + c • D.root i := by
      rw [hwt, D.reflection_apply, ← natCast_zsmul, Int.toNat_of_nonneg (by omega), hn, neg_sub,
        sub_smul]
      abel
    have hn' : D.coroot i η'.wt - c = -n := by
      rw [hwt', map_add, D.coroot_reflection, map_zsmul, D.coroot_root_self, hn, smul_eq_mul]
      ring
    refine ⟨η', by rw [LittelmannPath.reflectAfter, ite_eq_right (by rw [← hn]; omega)]; exact hη',
      heq, hwt', ?_⟩
    rw [LittelmannPath.reflectAfter, hn', ite_eq_left (by omega)]
    exact ((crystal S).fIter_eq_some_iff _ _ _).mpr hη'

/-- `reflectAfter η i` lies in the connected component of `η`. -/
lemma mem_component_of_reflectAfter {η' : LittelmannPath S}
    (h : reflectAfter η i c = some η') :
    η' ∈ η.component := by
  unfold LittelmannPath.reflectAfter at h
  split_ifs at h
  · exact Crystal.mem_closure_of_fIter_eq_some h
  · exact Crystal.mem_closure_singleton_comm
      (Crystal.mem_closure_of_fIter_eq_some (((crystal S).fIter_eq_some_iff _ _ _).mpr h))

end Reflect

/-! ### The first time some `hⱼ` reaches its level `cⱼ` -/

section Hit

variable [Finite ι] (η : LittelmannPath S) (c : ι → ℤ) {ξ : LittelmannPath S}

/-- The set of times `t ∈ [0, 1]` at which some `hⱼ(t) ≤ cⱼ`. -/
def hitSet : Set 𝕜 := {t ∈ Icc (0 : 𝕜) 1 | ∃ j, η.pairing j t ≤ c j}

/-- The first time at which some `hⱼ` reaches `cⱼ` (if it does). -/
noncomputable def hitTime : 𝕜 := sInf (η.hitSet c)

/-- The indices `j` with `hⱼ(τ) ≤ cⱼ` at the first hitting time `τ`. -/
def hitIndexSet : Set ι := {j | η.pairing j (η.hitTime c) ≤ c j}

omit [IsStrictOrderedRing 𝕜] [FloorRing 𝕜] in
lemma isClosed_hitSet : IsClosed (η.hitSet c) := by
  rw [show η.hitSet c = Icc 0 1 ∩ ⋃ j, {t | η.pairing j t ≤ c j} by ext; simp [hitSet]]
  exact isClosed_Icc.inter
    (isClosed_iUnion_of_finite fun j ↦ isClosed_le (η.continuous_pairing j) continuous_const)

variable {η c}

omit [Finite ι] [FloorRing 𝕜] in
lemma hitSet_nonempty {j : ι} (hj : η.minPairing j ≤ c j) : (η.hitSet c).Nonempty := by
  obtain ⟨s, hs, hsm⟩ := η.exists_minPairing j
  exact ⟨s, hs, j, hsm.trans_le hj⟩

omit [IsStrictOrderedRing 𝕜] [FloorRing 𝕜] in
lemma hitTime_mem (h : (η.hitSet c).Nonempty) : η.hitTime c ∈ η.hitSet c :=
  (η.isClosed_hitSet c).csInf_mem h ⟨0, fun _ ht ↦ ht.1.1⟩

omit [Finite ι] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] [FloorRing 𝕜] in
lemma lt_pairing_of_lt_hitTime {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) (hlt : t < η.hitTime c)
    (j : ι) : (c j : 𝕜) < η.pairing j t := by
  by_contra hle
  have hmem : t ∈ η.hitSet c := ⟨ht, j, not_lt.mp hle⟩
  exact absurd (csInf_le ⟨0, fun _ hs ↦ hs.1.1⟩ hmem) (not_le.mpr hlt)

omit [FloorRing 𝕜] in
lemma le_pairing_hitTime (hc : ∀ j, c j ≤ -1) (h : (η.hitSet c).Nonempty) (j : ι) :
    (c j : 𝕜) ≤ η.pairing j (η.hitTime c) := by
  have hτ := hitTime_mem h
  have hcj : (c j : 𝕜) ≤ -1 := by exact_mod_cast hc j
  by_contra hlt
  push Not at hlt
  obtain ⟨u, hu, hu', -⟩ := exists_first_eq (η.continuous_pairing j) hτ.1.1 (c := (c j : 𝕜))
    (by rw [pairing_zero]; linarith) hlt.le
  rcases eq_or_lt_of_le hu.2 with hu2 | hu2
  · rw [hu2] at hu'; linarith
  · exact absurd hu' (lt_pairing_of_lt_hitTime (t := u) ⟨hu.1, hu2.le.trans hτ.1.2⟩ hu2 j).ne'

omit [IsStrictOrderedRing 𝕜] [FloorRing 𝕜] in
lemma hitIndexSet_nonempty (h : (η.hitSet c).Nonempty) : (η.hitIndexSet c).Nonempty :=
  (hitTime_mem h).2

/-- A chosen index `j` with `hⱼ(τ) = cⱼ` at the first hitting time `τ`. -/
noncomputable def hitIndex (h : (η.hitSet c).Nonempty) : ι := (hitIndexSet_nonempty h).some

omit [FloorRing 𝕜] in
theorem firstHit_hitIndex (hc : ∀ j, c j ≤ -1) (h : (η.hitSet c).Nonempty) :
    η.FirstHit (hitIndex h) (η.hitTime c) (c (hitIndex h)) :=
  ⟨(hitTime_mem h).1, fun _ ht ↦ lt_pairing_of_lt_hitTime
    ⟨ht.1, ht.2.le.trans (hitTime_mem h).1.2⟩ ht.2 _,
    le_antisymm (hitIndexSet_nonempty h).some_mem (le_pairing_hitTime hc h _)⟩

omit [IsStrictOrderedRing 𝕜] [FloorRing 𝕜] in
/-- Paths agreeing up to the first hitting time have the same first hitting time and the same
hitting indices. -/
theorem hitTime_eq_of_eqOn (h : (η.hitSet c).Nonempty)
    (heq : ∀ t ∈ Icc 0 (η.hitTime c), ξ t = η t) :
    (ξ.hitSet c).Nonempty ∧ ξ.hitTime c = η.hitTime c ∧ ξ.hitIndexSet c = η.hitIndexSet c := by
  have hτ := hitTime_mem h
  have hpair : ∀ j, ∀ t ∈ Icc 0 (η.hitTime c), ξ.pairing j t = η.pairing j t := fun j t ht ↦ by
    rw [pairing, pairing, heq t ht]
  have hξτ : η.hitTime c ∈ ξ.hitSet c := by
    obtain ⟨j, hj⟩ := hτ.2
    exact ⟨hτ.1, j, by rw [hpair j _ ⟨hτ.1.1, le_rfl⟩]; exact hj⟩
  have heqτ : ξ.hitTime c = η.hitTime c := le_antisymm (csInf_le ⟨0, fun _ hs ↦ hs.1.1⟩ hξτ)
    (le_csInf ⟨_, hξτ⟩ fun t ht ↦ by
      by_contra hlt
      push Not at hlt
      obtain ⟨j, hj⟩ := ht.2
      rw [hpair j t ⟨ht.1.1, hlt.le⟩] at hj
      exact absurd hj (not_le.mpr (lt_pairing_of_lt_hitTime ht.1 hlt j)))
  refine ⟨⟨_, hξτ⟩, heqτ, ?_⟩
  ext j
  simp only [hitIndexSet, Set.mem_ofPred_eq, heqτ, hpair j _ ⟨hτ.1.1, le_rfl⟩]

omit [IsStrictOrderedRing 𝕜] [FloorRing 𝕜] in
theorem hitIndex_eq_of_eqOn (h : (η.hitSet c).Nonempty)
    (heq : ∀ t ∈ Icc 0 (η.hitTime c), ξ t = η t) :
    hitIndex (hitTime_eq_of_eqOn h heq).1 = hitIndex h := by
  have hs := (hitTime_eq_of_eqOn h heq).2.2
  unfold hitIndex
  congr 1

/-- **Littelmann's cancelling involution** ([Lit95] §9 (check); our formulation): let `cⱼ ≤ -1`
be integers and `η` a path some of whose `hⱼ` reaches `cⱼ`; let `τ` be the first such time and
`i` a chosen index with `hᵢ(τ) = cᵢ`. Then `η' = reflectAfter η i cᵢ` agrees with `η` up to `τ`
(so it has the same `τ` and `i`), has weight `rᵢ(wt η) + cᵢ αᵢ`, lies in the component of `η`,
and `reflectAfter η' i cᵢ = η`. For `c = -1` this is the involution of the path-model Weyl
character formula (`wt η' + ρ = rᵢ(wt η + ρ)`); for `cⱼ = -1 - ⟨λ, αⱼ^∨⟩` it is the involution of
the Littlewood–Richardson rule. -/
theorem exists_reflectAfter_hitIndex (hc : ∀ j, c j ≤ -1) (h : (η.hitSet c).Nonempty) :
    ∃ η', reflectAfter η (hitIndex h) (c (hitIndex h)) = some η' ∧ η' ∈ η.component ∧
      ∃ h' : (η'.hitSet c).Nonempty, hitIndex h' = hitIndex h ∧
        η'.wt = D.reflection (hitIndex h) η.wt + c (hitIndex h) • D.root (hitIndex h) ∧
        reflectAfter η' (hitIndex h) (c (hitIndex h)) = some η := by
  obtain ⟨η', hη', heq, hwt, hback⟩ := (firstHit_hitIndex hc h).reflectAfter (hc _)
  exact ⟨η', hη', mem_component_of_reflectAfter hη', (hitTime_eq_of_eqOn h heq).1,
    hitIndex_eq_of_eqOn h heq, hwt, hback⟩

end Hit

end LittelmannPath
