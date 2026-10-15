/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.ModifiedCanonicalForm

/-!
# A characterization of `B ∪ (-B)` in `U̇`

Over `ℚ(v)`, let `A = ℚ[[v⁻¹]] ∩ ℚ(v)` be the local ring at `v = ∞` (`InfinityLocalRing`) and
`B` the canonical basis of `U̇` ([Lus] 25.2.1, `Modified.modifiedCanonicalBasis`). [Lus]
Thm. 26.3.1 (b) states that `β ∈ U̇` lies in `B ∪ (-B)` if and only if `β ∈ 𝒜U̇`, `β̄ = β` and
`(β, β) ∈ 1 + v⁻¹A`.

## Main definitions

* `Modified.signedCanonicalBasis`: the set of `β ∈ U̇` with `β ∈ 𝒜U̇`, `β̄ = β` and
  `(β, β) ∈ 1 + v⁻¹A`.

## Main results

* `Modified.exists_repr_modifiedCanonicalBasis_eq_algebraMap`: if `(x, x) ∈ A`, the coordinates
  of `x` in the canonical basis lie in `A` (a consequence of 26.3.1 (a)).
* `Modified.mem_signedCanonicalBasis_iff`: **[Lus] Thm. 26.3.1 (b)**, the set above is
  `B ∪ (-B)`.

## Proof

The forward direction is 26.3.1 (a) together with 25.2.1 (a), (c). For the converse, the
coordinates `c_t` of `β` in `B` lie in `𝒜` (25.2.1 (d)); by almost orthonormality they lie in
`A`, hence in `𝒜 ∩ A = ℤ[v⁻¹]`, so `c_t = n_t + d_t` with `n_t ∈ ℤ`, `d_t ∈ v⁻¹ℤ[v⁻¹]`. Since `β`
and the elements of `B` are bar-invariant, so is `c_t`, which forces `d_t = 0`. Almost
orthonormality then gives `Σ_t n_t² ≡ 1` modulo `v⁻¹A`, so `Σ_t n_t² = 1` and `β = ±b` for a
single `b ∈ B`. This is Lusztig's argument (via 14.2.2 (b)), with the leading-coefficient
step replaced by the scaling argument of `Modified.eq_zero_of_forall_form_eq_zero`.

## Hypotheses

Lusztig states 26.3.1 with no assumption on the root datum. Here the root datum is `X`-regular
and satisfies `hY` (dominant `λ` with all `⟨i, λ⟩` arbitrarily large). Both are hypotheses of
the current route, inherited from the construction of `B` in 25.2.1
(`existsUnique_modifiedCanonical`); removing `hY` via [Lus] 25.2.2 is tracked in the roadmap.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 14.2.2, 25.2.1, 26.3.1.
-/

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop LusztigF Modified

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "A" => InfinityLocalRing
local notation "ϖ" => InfinityLocalRing.uniformizer

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

variable (R) in
/-- The subset of `U̇` characterized in [Lus] Thm. 26.3.1 (b): the `β ∈ 𝒜U̇` with `β̄ = β` and
`(β, β) ∈ 1 + v⁻¹A`, `A` the local ring at `v = ∞`. By `Modified.mem_signedCanonicalBasis_iff`
it is `B ∪ (-B)`. -/
def Modified.signedCanonicalBasis : Set (Modified R 𝕧) :=
  {x | x ∈ aForm R ∧ Modified.bar R x = x ∧
    ∃ a : A, Modified.form R 𝕧 hvn_ratFunc x x = algebraMap A 𝕂 (1 + ϖ * a)}

variable (hR : R.IsXRegular) (hY : ∀ N : ℕ, ∃ Λ : Dom R, ∀ i, (N : ℤ) ≤ Λ.1 (R.coroot i))

/-- **[Lus] Thm. 25.2.1 (a)** for the basis `modifiedCanonicalBasis`. -/
lemma Modified.modifiedCanonicalBasis_mem_aForm
    (t : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D) :
    modifiedCanonicalBasis hR hY t ∈ aForm R := by
  obtain ⟨ζ, b, b''⟩ := t
  rw [modifiedCanonicalBasis_apply]
  exact modifiedCanonical_mem_aForm hR hY ζ b.2 b''.2

/-- **[Lus] Thm. 25.2.1 (c)** for the basis `modifiedCanonicalBasis`. -/
lemma Modified.bar_modifiedCanonicalBasis (t : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D) :
    Modified.bar R (modifiedCanonicalBasis hR hY t) = modifiedCanonicalBasis hR hY t := by
  obtain ⟨ζ, b, b''⟩ := t
  rw [modifiedCanonicalBasis_apply]
  exact bar_modifiedCanonical hR hY ζ b.2 b''.2

lemma Modified.aModifiedCanonicalBasis_coe
    (t : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D) :
    (aModifiedCanonicalBasis hR hY t : Modified R 𝕧) = modifiedCanonicalBasis hR hY t := by
  obtain ⟨ζ, b, b''⟩ := t
  rw [aModifiedCanonicalBasis_apply, modifiedCanonicalBasis_apply]

/-- The `ℚ(v)`-coordinates of an element of `𝒜U̇` in the canonical basis are its
`𝒜`-coordinates. -/
lemma Modified.repr_modifiedCanonicalBasis_coe (x : (aForm R).toSubmodule)
    (t : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D) :
    (modifiedCanonicalBasis hR hY).repr x t =
      LusztigF.integralLaurentEval ((aModifiedCanonicalBasis hR hY).repr x t) := by
  have hx : (x : Modified R 𝕧) = Finsupp.linearCombination 𝕂 (modifiedCanonicalBasis hR hY)
      (((aModifiedCanonicalBasis hR hY).repr x).mapRange LusztigF.integralLaurentEval
        (map_zero _)) := by
    conv_lhs => rw [← (aModifiedCanonicalBasis hR hY).linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (by simp), Finsupp.sum, Finsupp.sum,
      Submodule.coe_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Submodule.coe_smul, aModifiedCanonicalBasis_coe, Modified.laurent_smul]
  rw [hx, Module.Basis.repr_linearCombination, Finsupp.mapRange_apply]

/-- The coordinates of `x̄` in the canonical basis are the bar conjugates of those of `x`. -/
lemma Modified.repr_bar_modifiedCanonicalBasis (x : Modified R 𝕧)
    (t : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D) :
    (modifiedCanonicalBasis hR hY).repr (Modified.bar R x) t =
      RatFunc.bar ((modifiedCanonicalBasis hR hY).repr x t) := by
  have h : Modified.bar R x = Finsupp.linearCombination 𝕂 (modifiedCanonicalBasis hR hY)
      (((modifiedCanonicalBasis hR hY).repr x).mapRange RatFunc.bar (map_zero _)) := by
    conv_lhs => rw [← (modifiedCanonicalBasis hR hY).linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (by simp), Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Modified.bar_smul, bar_modifiedCanonicalBasis]
  rw [h, Module.Basis.repr_linearCombination, Finsupp.mapRange_apply]

include hR hY in
/-- If `(x, x) ∈ A`, the coordinates of `x` in the canonical basis of `U̇` lie in `A`. This is
a consequence of the almost orthonormality [Lus] 26.3.1 (a) (our own deduction, by the scaling
argument of `Modified.eq_zero_of_forall_form_eq_zero`). Extra hypotheses `R.IsXRegular` and
`hY` (route hypotheses, from 25.2.1). -/
theorem Modified.exists_repr_modifiedCanonicalBasis_eq_algebraMap (x : Modified R 𝕧) {a₀ : A}
    (hxx : Modified.form R 𝕧 hvn_ratFunc x x = algebraMap A 𝕂 a₀)
    (s : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D) :
    ∃ a : A, (modifiedCanonicalBasis hR hY).repr x s = algebraMap A 𝕂 a := by
  classical
  set e := modifiedCanonicalBasis hR hY
  set c := e.repr x
  set S := c.support
  set F := Modified.form R 𝕧 hvn_ratFunc
  have hirr : Irreducible (ϖ : A) := irreducible_localX
  have hϖ0 : algebraMap A 𝕂 ϖ ≠ 0 := by
    rw [InfinityLocalRing.algebraMap_uniformizer]
    exact inv_ne_zero RatFunc.X_ne_zero
  by_cases hsS : s ∉ S
  · exact ⟨0, by rw [map_zero]; exact Finsupp.notMem_support_iff.1 hsS⟩
  rw [not_not] at hsS
  have hS : S.Nonempty := ⟨s, hsS⟩
  -- clear denominators
  choose m d hd using fun t ↦ InfinityLocalRing.exists_pow_mul (c t)
  set M := S.sup m
  have hd' : ∀ t ∈ S, algebraMap A 𝕂 (ϖ ^ M) * c t =
      algebraMap A 𝕂 (ϖ ^ (M - m t) * d t) := by
    intro t ht
    rw [_root_.map_mul, ← hd, ← mul_assoc, ← _root_.map_mul, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup ht)]
  have hd0 : ∀ t ∈ S, ϖ ^ (M - m t) * d t ≠ 0 := by
    intro t ht h
    have := hd' t ht
    rw [h, map_zero, mul_eq_zero, map_pow] at this
    rcases this with h1 | h1
    · exact pow_ne_zero _ hϖ0 h1
    · exact Finsupp.mem_support_iff.1 ht h1
  choose! n u hu using fun t (ht : t ∈ S) ↦
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hd0 t ht) hirr
  -- divide by the smallest power of `ϖ`
  obtain ⟨t₀, ht₀, hmin⟩ := S.exists_min_image n hS
  set f : (Y →+ ℤ) × canonicalBasis D × canonicalBasis D → A :=
    fun t ↦ (u t : A) * ϖ ^ (n t - n t₀)
  have hc : ∀ t ∈ S, algebraMap A 𝕂 (ϖ ^ M) * c t =
      algebraMap A 𝕂 (ϖ ^ n t₀) * algebraMap A 𝕂 (f t) := by
    intro t ht
    rw [hd' t ht, hu t ht, ← _root_.map_mul]
    congr 1
    rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' (hmin t ht)]
  have hM0 : algebraMap A 𝕂 (ϖ ^ M) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hϖ0
  -- if no negative power of `ϖ` occurs, we are done
  by_cases hle : M ≤ n t₀
  · refine ⟨ϖ ^ (n t₀ - M) * f s, mul_left_cancel₀ hM0 ?_⟩
    rw [hc s hsS, ← _root_.map_mul, ← _root_.map_mul]
    congr 1
    rw [show ϖ ^ M * (ϖ ^ (n t₀ - M) * f s) = ϖ ^ (M + (n t₀ - M)) * f s by ring,
      Nat.add_sub_cancel' hle]
  exfalso
  obtain ⟨k, hk⟩ : ∃ k, M = n t₀ + (k + 1) := ⟨M - n t₀ - 1, by omega⟩
  set y := ∑ t ∈ S, algebraMap A 𝕂 (f t) • e t
  have hy : algebraMap A 𝕂 (ϖ ^ n t₀) • y = algebraMap A 𝕂 (ϖ ^ M) • x := by
    conv_rhs => rw [← e.linearCombination_repr x, Finsupp.linearCombination_apply]
    rw [Finsupp.sum, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [smul_smul, smul_smul, hc t ht]
  have hyy : F y y = algebraMap A 𝕂 (ϖ * (ϖ ^ k * ϖ ^ (k + 1) * a₀)) := by
    have h := congrArg (fun z ↦ F z z) hy
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hxx] at h
    have h0 : algebraMap A 𝕂 (ϖ ^ n t₀) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero _ hϖ0
    apply mul_left_cancel₀ (mul_ne_zero h0 h0)
    rw [hk] at h
    simp only [map_pow, _root_.map_mul] at h ⊢
    linear_combination h
  -- `(y, y) ≡ Σ_t f_t²`
  choose a ha using form_modifiedCanonicalBasis_sub_mem hR hY
  have hF : ∀ t t', F (e t) (e t') =
      (if t = t' then 1 else 0) + algebraMap A 𝕂 (ϖ * a t t') := fun t t' ↦ by
    rw [← ha t t']
    ring
  have hexp : F y y = ∑ t ∈ S, ∑ t' ∈ S,
      algebraMap A 𝕂 (f t) * (algebraMap A 𝕂 (f t') * F (e t') (e t)) := by
    simp only [y, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
  have hsum : F y y = algebraMap A 𝕂 (∑ t ∈ S, f t ^ 2 +
      ϖ * ∑ t ∈ S, ∑ t' ∈ S, f t * f t' * a t' t) := by
    rw [hexp, _root_.map_add, map_sum, _root_.map_mul, map_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    simp only [hF, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', ht, ↓reduceIte, map_sum, Finset.mul_sum, _root_.map_mul, map_pow]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun t' _ ↦ by ring
  -- so `Σ_t f_t² ∈ ϖA`, and `ϖ ∣ f_{t₀} = u_{t₀}`, a unit
  rw [hyy] at hsum
  have hA := InfinityLocalRing.injective_algebraMap hsum
  have hmem : ∑ t ∈ S, f t ^ 2 ∈ Ideal.span {(ϖ : A)} := by
    rw [Ideal.mem_span_singleton]
    exact ⟨ϖ ^ k * ϖ ^ (k + 1) * a₀ - ∑ t ∈ S, ∑ t' ∈ S, f t * f t' * a t' t,
      by linear_combination -hA⟩
  have hsum' := Ideal.Quotient.eq_zero_iff_mem.2 hmem
  simp only [map_sum, map_pow] at hsum'
  have h₀ := eq_zero_of_sum_sq_eq_zero S _ hsum' t₀ ht₀
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h₀
  simp only [f, Nat.sub_self, pow_zero, mul_one] at h₀
  exact hirr.not_isUnit (isUnit_of_dvd_unit h₀ (u t₀).isUnit)

/-- **[Lus] Thm. 26.3.1 (b)**: `β ∈ U̇` lies in `B ∪ (-B)` if and only if `β ∈ 𝒜U̇`, `β̄ = β` and
`(β, β) ∈ 1 + v⁻¹A`, where `B` is the canonical basis `modifiedCanonicalBasis` of [Lus] 25.2.1
and `A` the local ring at `v = ∞`.

Lusztig states this with no assumption on the root datum. Here `R.IsXRegular` and `hY` are
hypotheses of the current route, inherited from the construction of `B`
(`existsUnique_modifiedCanonical`); removing `hY` via [Lus] 25.2.2 is tracked in the roadmap. -/
theorem Modified.mem_signedCanonicalBasis_iff (β : Modified R 𝕧) :
    β ∈ signedCanonicalBasis R ↔
      ∃ t, β = modifiedCanonicalBasis hR hY t ∨ β = -modifiedCanonicalBasis hR hY t := by
  classical
  constructor
  · rintro ⟨hβ, hbar, a₀, hform⟩
    -- the coordinates of `β` are integers
    have hint : ∀ t, ∃ n : ℤ, (modifiedCanonicalBasis hR hY).repr β t = n := by
      intro t
      obtain ⟨a, ha⟩ := exists_repr_modifiedCanonicalBasis_eq_algebraMap hR hY β hform t
      have hp : (modifiedCanonicalBasis hR hY).repr β t = _ :=
        repr_modifiedCanonicalBasis_coe hR hY ⟨β, hβ⟩ t
      obtain ⟨n, hn⟩ := (isIntInv_of_algebraMap_eq _ a (ha.symm.trans hp)).exists_int_sub
      rw [← hp] at hn
      refine ⟨n, sub_eq_zero.1 (hn.eq_zero_of_bar_eq ?_)⟩
      rw [map_sub, map_intCast, ← repr_bar_modifiedCanonicalBasis, hbar]
    choose n hn using hint
    set e := modifiedCanonicalBasis hR hY
    set S := (e.repr β).support
    set F := Modified.form R 𝕧 hvn_ratFunc
    have hβ' : β = ∑ t ∈ S, algebraMap A 𝕂 (n t) • e t := by
      conv_lhs => rw [← e.linearCombination_repr β]
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      rw [hn t, map_intCast]
    -- `(β, β) ≡ Σ_t n_t²`
    choose a ha using form_modifiedCanonicalBasis_sub_mem hR hY
    have hF : ∀ t t', F (e t) (e t') =
        (if t = t' then 1 else 0) + algebraMap A 𝕂 (ϖ * a t t') := fun t t' ↦ by
      rw [← ha t t']
      ring
    have hexp : F β β = ∑ t ∈ S, ∑ t' ∈ S,
        algebraMap A 𝕂 (n t) * (algebraMap A 𝕂 (n t') * F (e t') (e t)) := by
      conv_lhs => rw [hβ']
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        Finset.mul_sum]
    have hsum : F β β = algebraMap A 𝕂 (∑ t ∈ S, (n t : A) ^ 2 +
        ϖ * ∑ t ∈ S, ∑ t' ∈ S, (n t : A) * n t' * a t' t) := by
      rw [hexp, _root_.map_add, map_sum, _root_.map_mul, map_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t ht ↦ ?_
      simp only [hF, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', ht, ↓reduceIte, map_sum, Finset.mul_sum, _root_.map_mul, map_pow]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun t' _ ↦ by ring
    rw [hform] at hsum
    have hA := InfinityLocalRing.injective_algebraMap hsum
    -- hence `Σ_t n_t² = 1`, since `ℤ ∩ v⁻¹ℤ[v⁻¹] = 0`
    have hZ : ∑ t ∈ S, n t ^ 2 = 1 := by
      have hL : Modified.IsLaurent (((∑ t ∈ S, n t ^ 2 - 1 : ℤ)) : 𝕂) :=
        ⟨(∑ t ∈ S, n t ^ 2 - 1 : ℤ), map_intCast _ _⟩
      have hneg := isNegLaurent_of_isLaurent hL
        (a₀ - ∑ t ∈ S, ∑ t' ∈ S, (n t : A) * n t' * a t' t) (by
          rw [← map_intCast (algebraMap A 𝕂)]
          congr 1
          push_cast
          linear_combination -hA)
      have := hneg.eq_zero_of_intCast
      linarith
    -- so exactly one `n_t` is nonzero, and it is `±1`
    obtain ⟨t₀, ht₀, hne⟩ : ∃ t₀ ∈ S, n t₀ ≠ 0 := by
      by_contra hne
      have h : ∀ t ∈ S, n t = 0 := fun t ht ↦ by
        by_contra h''
        exact hne ⟨t, ht, h''⟩
      have h0 : ∑ t ∈ S, n t ^ 2 = 0 := Finset.sum_eq_zero fun t ht ↦ by rw [h t ht]; ring
      rw [h0] at hZ
      exact zero_ne_one hZ
    rw [← Finset.add_sum_erase S _ ht₀] at hZ
    have hrest : 0 ≤ ∑ t ∈ S.erase t₀, n t ^ 2 := Finset.sum_nonneg fun t _ ↦ sq_nonneg _
    have hpos : 0 < n t₀ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
    have h1 : n t₀ ^ 2 = 1 := by linarith
    have h0 : ∑ t ∈ S.erase t₀, n t ^ 2 = 0 := by linarith
    have hrest0 := (Finset.sum_eq_zero_iff_of_nonneg fun t _ ↦ sq_nonneg (n t)).1 h0
    have hrepr : e.repr β = Finsupp.single t₀ (n t₀ : 𝕂) := by
      ext t
      rw [hn t, Finsupp.single_apply]
      split_ifs with h
      · rw [h]
      · by_cases htS : t ∈ S
        · rw [(pow_eq_zero_iff two_ne_zero).1 (hrest0 t (Finset.mem_erase.2 ⟨Ne.symm h, htS⟩)),
            Int.cast_zero]
        · rw [← hn t]
          exact Finsupp.notMem_support_iff.1 htS
    have hβe : β = (n t₀ : 𝕂) • e t₀ := by
      rw [← Module.Basis.repr_symm_single, ← hrepr, LinearEquiv.symm_apply_apply]
    have hpm : (n t₀ - 1) * (n t₀ + 1) = 0 := by linear_combination h1
    refine ⟨t₀, ?_⟩
    rcases mul_eq_zero.1 hpm with h | h
    · left
      rw [hβe, show n t₀ = 1 by linarith, Int.cast_one, one_smul]
    · right
      rw [hβe, show n t₀ = -1 by linarith, Int.cast_neg, Int.cast_one, neg_smul, one_smul]
  · rintro ⟨t, rfl | rfl⟩
    · obtain ⟨a, ha⟩ := form_modifiedCanonicalBasis_sub_mem hR hY t t
      refine ⟨modifiedCanonicalBasis_mem_aForm hR hY t, bar_modifiedCanonicalBasis hR hY t, a, ?_⟩
      rw [_root_.map_add, _root_.map_one, ← ha]
      simp
    · obtain ⟨a, ha⟩ := form_modifiedCanonicalBasis_sub_mem hR hY t t
      refine ⟨neg_mem (modifiedCanonicalBasis_mem_aForm hR hY t), ?_, a, ?_⟩
      · rw [map_neg, bar_modifiedCanonicalBasis]
      · simp only [map_neg, LinearMap.neg_apply, neg_neg]
        rw [_root_.map_add, _root_.map_one, ← ha]
        simp

end LieLean.QuantumGroup
