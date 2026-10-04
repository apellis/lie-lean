/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationFacet
import LieLean.LinearAlgebra.Matrix.Cartan.TitsCone.Coroots

/-!
# Upper closures of facets (integral weights, finite type)

Let `A` be of finite type. The positive roots are the `β = v αᵢ ∈ Q₊` with `v ∈ W`, and the
pairing of a weight `ξ` with the coroot of `β` is `⟨ξ, β^∨⟩ = ⟨v⁻¹ ξ, αᵢ^∨⟩`. For integral weights
`x`, `y`, the weight `y` lies in the **upper closure** of the facet of `x` if, for every positive
root `β`, `⟨y + ρ, β^∨⟩` is `= 0`, `> 0`, `≤ 0` according as `⟨x + ρ, β^∨⟩` is `= 0`, `> 0`,
`< 0` (Humphreys, GSM 94, §7.3).

Fix `a = λ + ρ`, `b = μ + ρ` antidominant integral with every simple wall of `a` a wall of `b`.
For `w ∈ W`, `w·μ` lies in the upper closure of the facet of `w·λ` iff no positive root `β` with
`⟨w b, β^∨⟩ = 0` has `⟨w a, β^∨⟩ > 0` (`UpperClosureCondition`,
`memUpperClosure_weylDot_iff`). This file proves the two combinatorial facts about this
condition used for translation of simple modules (Humphreys, GSM 94, Theorem 7.9):

* if the condition holds at `w` and `w' b = w b`, then `w' a - w a ∈ Q₊`
  (`exists_apply_sub_eq_rootOf_of_upperClosureCondition`): `w a` is the least element of
  `{w' a | w' b = w b}`;
* for every `w` there are `w''` with `w'' b = w b` satisfying the condition and a chain of
  reflections `ξ ↦ ξ - ⟨ξ, β^∨⟩ β` in positive roots `β` orthogonal to `w b` with
  `⟨ξ, β^∨⟩ > 0`, from `w a` to `w'' a` (`exists_upperClosureCondition`).

## Main definitions

* `Matrix.Realization.MemUpperClosure`: `y` lies in the upper closure of the facet of `x`.
* `Matrix.Realization.UpperClosureCondition`: the reduced condition on `ρ`-shifted weights.
* `Matrix.Realization.WallStep`: one reflection step of the chain.

## Proofs

Reconstructed. For the first fact write `w = w₁ u₁` with `u₁ b = b` and `w₁ αᵢ > 0` for every
simple wall `i` of `b` (`exists_mul_eq_of_apply_eq`, by induction on the length). The
condition, applied to the positive roots `w₁ αᵢ`, says that `u₁ a` is antidominant on the walls
of `b`, hence `u₁ a = a` by a norm argument (`apply_eq_self_of_apply_eq_of_nonpos`). If
`v b = b` then `v a - a ∈ Q₊` is supported on the simple walls of `b`
(`exists_apply_sub_eq_rootOf_of_apply_eq`, since `(v a - a | b) = 0`), and `w₁` maps those simple
roots into `Q₊`. All comparisons are made in `ℤ`, so no order on `K` is needed.
-/

noncomputable section

open Module

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-! ### Definitions -/

section Defs

variable (hA : A.IsGeneralizedCartan)

/-- For integral weights `x`, `y`: `y` lies in the **upper closure of the facet** of `x`
(Humphreys, GSM 94, §7.3). For every positive root `β = v αᵢ`, with
`⟨ξ, β^∨⟩ = ⟨v⁻¹ ξ, αᵢ^∨⟩`: if `⟨x + ρ, β^∨⟩ = 0` then `⟨y + ρ, β^∨⟩ = 0`; if
`⟨x + ρ, β^∨⟩ > 0` then `⟨y + ρ, β^∨⟩ > 0`; if `⟨x + ρ, β^∨⟩ < 0` then `⟨y + ρ, β^∨⟩ ≤ 0`. The
signs are expressed through natural numbers, so the definition is meant for integral weights. -/
def MemUpperClosure (x y : Dual K H) : Prop :=
  ∀ v ∈ P.weylGroup hA, ∀ i, v (P.root i) ∈ P.posWeights →
    (v.symm (x + P.rho) (P.coroot i) = 0 → v.symm (y + P.rho) (P.coroot i) = 0) ∧
    ((∃ n : ℕ, 0 < n ∧ v.symm (x + P.rho) (P.coroot i) = n) →
      ∃ m : ℕ, 0 < m ∧ v.symm (y + P.rho) (P.coroot i) = m) ∧
    ((∃ n : ℕ, 0 < n ∧ v.symm (x + P.rho) (P.coroot i) = -(n : K)) →
      ∃ m : ℕ, v.symm (y + P.rho) (P.coroot i) = -(m : K))

/-- The condition "no positive root `β` with `⟨η, β^∨⟩ = 0` has `⟨ξ, β^∨⟩ > 0`" on (`ρ`-shifted,
integral) weights `ξ`, `η`: for every positive root `β = v αᵢ`, if `⟨v⁻¹ η, αᵢ^∨⟩ = 0` then
`⟨v⁻¹ ξ, αᵢ^∨⟩ ∈ -ℕ`. -/
def UpperClosureCondition (ξ η : Dual K H) : Prop :=
  ∀ v ∈ P.weylGroup hA, ∀ i, v (P.root i) ∈ P.posWeights →
    v.symm η (P.coroot i) = 0 → ∃ n : ℕ, v.symm ξ (P.coroot i) = -(n : K)

/-- One reflection step `ξ ↦ ξ' = ξ - n β` in a positive root `β = v αᵢ` with `⟨η, β^∨⟩ = 0` and
`⟨ξ, β^∨⟩ = n > 0`. -/
def WallStep (η ξ ξ' : Dual K H) : Prop :=
  ∃ v ∈ P.weylGroup hA, ∃ i, ∃ n : ℕ, v (P.root i) ∈ P.posWeights ∧ 0 < n ∧
    v.symm η (P.coroot i) = 0 ∧ v.symm ξ (P.coroot i) = n ∧ ξ' = ξ - n • v (P.root i)

end Defs

/-! ### Pairings with real coroots -/

omit [CharZero K] in
private lemma natCast_toNat {z : ℤ} (hz : 0 ≤ z) : ((z.toNat : ℕ) : K) = (z : K) := by
  rw [← Int.cast_natCast (R := K), Int.toNat_of_nonneg hz]

omit [DecidableEq ι] in
/-- For `u ∈ W` the functional `ξ ↦ ⟨u ξ, αᵢ^∨⟩` is, up to a global sign, a nonnegative integral
combination of the `⟨ξ, αⱼ^∨⟩`: it is the pairing with a real coroot, which is positive or
negative. -/
theorem exists_apply_coroot_eq_sum (hA : A.IsGeneralizedCartan)
    {u : Dual K H ≃ₗ[K] Dual K H} (hu : u ∈ P.weylGroup hA) (i : ι) :
    ∃ k : ι → ℤ, 0 ≤ k ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ ξ : Dual K H, u ξ (P.coroot i) = ε * ∑ j, (k j : K) * ξ (P.coroot j) := by
  obtain ⟨u', hu', huu'⟩ := P.exists_coweylGroup_apply_apply hA hu
  rcases P.mem_posRealCoroots_or_neg_mem hA ⟨u', hu', i, rfl⟩ with
    ⟨-, k, hk, hkc⟩ | ⟨-, k, hk, hkc⟩
  · refine ⟨k, hk, 1, Or.inl rfl, fun ξ ↦ ?_⟩
    rw [huu', ← hkc, P.apply_corootOf, Int.cast_one, one_mul]
  · refine ⟨k, hk, -1, Or.inr rfl, fun ξ ↦ ?_⟩
    rw [huu', ← P.apply_corootOf, hkc, map_neg]
    push_cast
    ring

omit [DecidableEq ι] in
/-- The pairing `⟨u a, αᵢ^∨⟩` for an antidominant integral weight `a` and `u ∈ W`, together with
the same pairing for a second antidominant integral weight `b`: both are `-ε s_a`, `-ε s_b` with
a common sign `ε` and `s_a = ∑ kⱼ n_a(j) ≥ 0`, `s_b = ∑ kⱼ n_b(j) ≥ 0` for a common `k ≥ 0`. -/
theorem exists_apply_coroot_eq_of_antidominant (hA : A.IsGeneralizedCartan) {a b : Dual K H}
    {na nb : ι → ℕ} (hna : ∀ i, a (P.coroot i) = -(na i : K))
    (hnb : ∀ i, b (P.coroot i) = -(nb i : K))
    {u : Dual K H ≃ₗ[K] Dual K H} (hu : u ∈ P.weylGroup hA) (i : ι) :
    ∃ k : ι → ℤ, 0 ≤ k ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      u a (P.coroot i) = ((-ε * ∑ j, k j * (na j : ℤ) : ℤ) : K) ∧
      u b (P.coroot i) = ((-ε * ∑ j, k j * (nb j : ℤ) : ℤ) : K) := by
  obtain ⟨k, hk, ε, hε, h⟩ := P.exists_apply_coroot_eq_sum hA hu i
  refine ⟨k, hk, ε, hε, ?_, ?_⟩
  · rw [h a]
    push_cast
    simp only [hna, mul_neg, Finset.sum_neg_distrib]
    ring
  · rw [h b]
    push_cast
    simp only [hnb, mul_neg, Finset.sum_neg_distrib]
    ring

/-! ### The upper closure and the reduced condition -/

omit [DecidableEq ι] in
/-- For `a = λ + ρ`, `b = μ + ρ` antidominant integral with every simple wall of `a` a wall of
`b`, and `w ∈ W`: `w·μ` lies in the upper closure of the facet of `w·λ` iff no positive root
`β` with `⟨w b, β^∨⟩ = 0` has `⟨w a, β^∨⟩ > 0`. -/
theorem memUpperClosure_weylDot_iff (hA : A.IsGeneralizedCartan) {lam μ : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (w : P.weylGroup hA) :
    P.MemUpperClosure hA (P.weylDot hA w lam) (P.weylDot hA w μ) ↔
      P.UpperClosureCondition hA (w.val (lam + P.rho)) (w.val (μ + P.rho)) := by
  choose na hna using hlam
  choose nb hnb using hμ
  have hfacet' : ∀ j, na j = 0 → nb j = 0 := fun j hj ↦ by
    have h := hfacet j (by rw [hna j, hj, Nat.cast_zero, neg_zero])
    rw [hnb j, neg_eq_zero] at h
    exact_mod_cast h
  -- the two pairings for a positive root `v αᵢ`
  have key : ∀ v ∈ P.weylGroup hA, ∀ i, ∃ sa sb : ℤ, 0 ≤ sa ∧ 0 ≤ sb ∧ (sa = 0 → sb = 0) ∧
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        v.symm (w.val (lam + P.rho)) (P.coroot i) = ((-ε * sa : ℤ) : K) ∧
        v.symm (w.val (μ + P.rho)) (P.coroot i) = ((-ε * sb : ℤ) : K) := by
    intro v hv i
    have hu : v⁻¹ * w.val ∈ P.weylGroup hA := mul_mem (inv_mem hv) w.property
    obtain ⟨k, hk, ε, hε, h1, h2⟩ := P.exists_apply_coroot_eq_of_antidominant hA hna hnb hu i
    refine ⟨∑ j, k j * (na j : ℤ), ∑ j, k j * (nb j : ℤ),
      Finset.sum_nonneg fun j _ ↦ mul_nonneg (hk j) (Int.natCast_nonneg _),
      Finset.sum_nonneg fun j _ ↦ mul_nonneg (hk j) (Int.natCast_nonneg _), fun h0 ↦ ?_,
      ε, hε, h1, h2⟩
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
      mul_nonneg (hk j) (Int.natCast_nonneg _)).mp h0
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rcases mul_eq_zero.mp (hz j (Finset.mem_univ j)) with h | h
    · rw [h, zero_mul]
    · rw [hfacet' j (by exact_mod_cast h), Nat.cast_zero, mul_zero]
  simp only [MemUpperClosure, UpperClosureCondition, weylDot_add_rho]
  constructor
  · intro hU v hv i hpos hb0
    obtain ⟨sa, sb, hsa, hsb, hab, ε, hε, h1, h2⟩ := key v hv i
    obtain ⟨-, hU2, -⟩ := hU v hv i hpos
    rw [h2] at hb0
    have hb0' : -ε * sb = 0 := by exact_mod_cast hb0
    rcases hε with rfl | rfl
    · exact ⟨sa.toNat, by rw [h1, natCast_toNat hsa]; push_cast; ring⟩
    · by_cases hsa0 : sa = 0
      · exact ⟨0, by rw [h1, hsa0]; simp⟩
      · obtain ⟨m, hm, hm'⟩ := hU2 ⟨sa.toNat, by omega, by
          rw [h1, natCast_toNat hsa]; push_cast; ring⟩
        rw [h2] at hm'
        have : - -1 * sb = (m : ℤ) := by exact_mod_cast hm'
        exfalso
        omega
  · intro hC v hv i hpos
    obtain ⟨sa, sb, hsa, hsb, hab, ε, hε, h1, h2⟩ := key v hv i
    have hC' := hC v hv i hpos
    refine ⟨fun h0 ↦ ?_, ?_, ?_⟩
    · rw [h1] at h0
      have h0' : -ε * sa = 0 := by exact_mod_cast h0
      have : sa = 0 := by rcases hε with rfl | rfl <;> omega
      rw [h2, hab this, mul_zero, Int.cast_zero]
    · rintro ⟨n, hn, hn'⟩
      rw [h1] at hn'
      have hn'' : -ε * sa = (n : ℤ) := by exact_mod_cast hn'
      rcases hε with rfl | rfl
      · exfalso
        omega
      · have hsb0 : sb ≠ 0 := fun h0 ↦ by
          obtain ⟨q, hq⟩ := hC' (by rw [h2, h0, mul_zero, Int.cast_zero])
          rw [h1] at hq
          have : - -1 * sa = -(q : ℤ) := by exact_mod_cast hq
          omega
        exact ⟨sb.toNat, by omega, by rw [h2, natCast_toNat hsb]; push_cast; ring⟩
    · rintro ⟨n, hn, hn'⟩
      rw [h1] at hn'
      have hn'' : -ε * sa = -(n : ℤ) := by exact_mod_cast hn'
      rcases hε with rfl | rfl
      · exact ⟨sb.toNat, by rw [h2, natCast_toNat hsb]; push_cast; ring⟩
      · exfalso
        omega

/-! ### Stabilizers of antidominant weights -/

section FiniteType

variable [FiniteDimensional K H]

/-- If `a`, `b` are antidominant integral and `v ∈ W` fixes `b`, then `v a - a ∈ Q₊` is supported
on the simple walls of `b`. -/
theorem exists_apply_sub_eq_rootOf_of_apply_eq (hA : A.IsFiniteCartan) {a b : Dual K H}
    (ha : ∀ i, ∃ n : ℕ, a (P.coroot i) = -n) (hb : ∀ i, ∃ n : ℕ, b (P.coroot i) = -n)
    {v : Dual K H ≃ₗ[K] Dual K H} (hv : v ∈ P.weylGroup hA.isGeneralizedCartan)
    (hvb : v b = b) :
    ∃ c : ι → ℤ, 0 ≤ c ∧ v a - a = P.rootOf c ∧ ∀ i, c i ≠ 0 → b (P.coroot i) = 0 := by
  have hA' := hA.isGeneralizedCartan
  obtain ⟨d, hdpos, hpos⟩ := hA.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hpos.isHermitian
  set S := Symmetrization.ofDiagonal d hdpos hsymm
  set B := P.dualBilinForm S
  obtain ⟨c, hc, hce⟩ := P.exists_sub_apply_eq_rootOf hA' (μ := -a)
    (fun i => by obtain ⟨n, hn⟩ := ha i; exact ⟨n, by simp [hn]⟩) ⟨v, hv⟩
  have hva : v a - a = P.rootOf c := by
    rw [← hce, map_neg]
    abel
  refine ⟨c, hc, hva, ?_⟩
  choose nb hnb using hb
  have hB1 : B (v a) b = B a b := by
    have := P.dualBilinForm_weylGroup hA' S hv a b
    rwa [hvb] at this
  have h0 : B (P.rootOf c) b = 0 := by
    rw [← hva, map_sub, LinearMap.sub_apply, hB1, sub_self]
  rw [P.dualBilinForm_ofDiagonal_rootOf d hdpos hsymm] at h0
  have hcast : ((∑ i, c i * d i * (nb i : ℤ) : ℤ) : K) = 0 := by
    have h1 : ((∑ i, c i * d i * (nb i : ℤ) : ℤ) : K) =
        -∑ i, ((c i * d i : ℤ) : K) * b (P.coroot i) := by
      push_cast
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hnb i]; ring
    rw [h1, h0, neg_zero]
  have hsum : ∑ i, c i * d i * (nb i : ℤ) = 0 := by exact_mod_cast hcast
  intro i hi
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
    mul_nonneg (mul_nonneg (hc j) (hdpos j).le) (Int.natCast_nonneg _)).mp hsum i
    (Finset.mem_univ i)
  have h' : nb i = 0 := by
    rcases mul_eq_zero.mp hterm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hi
      · exact absurd h (hdpos i).ne'
    · exact_mod_cast h
  rw [hnb i, h', Nat.cast_zero, neg_zero]

/-- If `a`, `b` are antidominant integral, `u ∈ W` fixes `b`, and `u a` is antidominant on the
simple walls of `b`, then `u a = a`. Norm argument for the `W`-invariant form of the positive
definite `diag(d) A`. -/
theorem apply_eq_self_of_apply_eq_of_nonpos (hA : A.IsFiniteCartan) {a b : Dual K H}
    (ha : ∀ i, ∃ n : ℕ, a (P.coroot i) = -n) (hb : ∀ i, ∃ n : ℕ, b (P.coroot i) = -n)
    {u : Dual K H ≃ₗ[K] Dual K H} (hu : u ∈ P.weylGroup hA.isGeneralizedCartan)
    (hub : u b = b)
    (hua : ∀ i, b (P.coroot i) = 0 → ∃ n : ℕ, u a (P.coroot i) = -(n : K)) : u a = a := by
  have hA' := hA.isGeneralizedCartan
  obtain ⟨c, hc, hce, hcb⟩ := P.exists_apply_sub_eq_rootOf_of_apply_eq hA ha hb hu hub
  obtain ⟨d, hdpos, hpos⟩ := hA.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hpos.isHermitian
  set S := Symmetrization.ofDiagonal d hdpos hsymm
  set B := P.dualBilinForm S
  have hB (k : ι → ℤ) (x : Dual K H) := P.dualBilinForm_ofDiagonal_rootOf d hdpos hsymm k x
  have hBsymm (x x' : Dual K H) : B x x' = B x' x := (P.isSymm_dualBilinForm S).eq x x'
  choose na hna using ha
  have hm : ∀ i, ∃ m : ℕ, c i ≠ 0 → u a (P.coroot i) = -(m : K) := fun i ↦ by
    by_cases hi : c i = 0
    · exact ⟨0, fun h ↦ absurd hi h⟩
    · obtain ⟨m, hm⟩ := hua i (hcb i hi)
      exact ⟨m, fun _ ↦ hm⟩
  choose m hm using hm
  -- `(u a - a | u a + a) = 0`
  have h1 : B (P.rootOf c) (u a + a) = 0 := by
    have hW : B (u a) (u a) = B a a := P.dualBilinForm_weylGroup hA' S hu a a
    rw [← hce]
    simp only [map_add, map_sub, LinearMap.sub_apply]
    rw [hBsymm a (u a)]
    linear_combination hW
  have hsum : ∑ i, c i * d i * ((m i : ℤ) + na i) = 0 := by
    have hcast : ((∑ i, c i * d i * ((m i : ℤ) + na i) : ℤ) : K) = 0 := by
      have h2 : ((∑ i, c i * d i * ((m i : ℤ) + na i) : ℤ) : K) =
          -∑ i, ((c i * d i : ℤ) : K) * (u a + a) (P.coroot i) := by
        push_cast
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        by_cases hi : c i = 0
        · simp [hi]
        · rw [LinearMap.add_apply, hm i hi, hna i]
          ring
      rw [h2, ← hB, h1, neg_zero]
    exact_mod_cast hcast
  have hterm (i : ι) : c i = 0 ∨ (m i = 0 ∧ na i = 0) := by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
      mul_nonneg (mul_nonneg (hc j) (hdpos j).le) (by positivity)).mp hsum i (Finset.mem_univ i)
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact absurd h (hdpos i).ne'
    · right
      constructor <;> omega
  -- `(u a - a | u a - a) = 0`
  have h3 : B (P.rootOf c) (u a - a) = 0 := by
    rw [hB]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    by_cases hi : c i = 0
    · simp [hi]
    · rcases hterm i with h | ⟨hm0, hn0⟩
      · exact absurd h hi
      · rw [LinearMap.sub_apply, hm i hi, hna i, hm0, hn0]
        simp
  rw [hce] at h3
  have hc0 : c = 0 := by
    by_contra hne
    have hq := hpos.dotProduct_mulVec_pos hne
    rw [hB] at h3
    have hcast : ((c ⬝ᵥ (diagonal d * A) *ᵥ c : ℤ) : K) = 0 := by
      rw [← h3, ← mulVec_mulVec, dotProduct]
      simp only [mulVec_diagonal]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [rootOf_apply_coroot]
      ring
    simp only [star_trivial] at hq
    exact hq.ne' (by exact_mod_cast hcast)
  rw [← sub_eq_zero, hce, hc0, map_zero]

end FiniteType

/-! ### Representatives which are positive on the walls -/

omit [DecidableEq ι] in
/-- Every `w ∈ W` factors as `w = w₁ u₁` with `u₁ b = b` and `w₁ αᵢ > 0` for every simple root
`αᵢ` orthogonal to `b` (a minimal-length representative modulo the stabilizer of `b`). -/
theorem exists_mul_eq_of_apply_eq (hA : A.IsGeneralizedCartan) (b : Dual K H)
    (w : P.weylGroup hA) :
    ∃ w₁ u₁ : P.weylGroup hA, w = w₁ * u₁ ∧ u₁.val b = b ∧
      ∀ i, b (P.coroot i) = 0 → w₁.val (P.root i) ∈ P.posWeights := by
  classical
  induction hn : (P.coxeterSystem hA).length w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  by_cases h : ∀ i, b (P.coroot i) = 0 → ¬(P.coxeterSystem hA).IsRightDescent w i
  · exact ⟨w, 1, (mul_one w).symm, rfl, fun i hi ↦
      (P.apply_root_mem_posWeights_iff hA).mpr (h i hi)⟩
  · push Not at h
    obtain ⟨i, hi, hdesc⟩ := h
    have hlt : (P.coxeterSystem hA).length (w * (P.coxeterSystem hA).simple i) < n := by
      rw [← hn]
      exact hdesc
    obtain ⟨w₁, u₁, hw, hu, hpos⟩ := ih _ hlt (w * (P.coxeterSystem hA).simple i) rfl
    refine ⟨w₁, u₁ * (P.coxeterSystem hA).simple i, ?_, ?_, hpos⟩
    · rw [← mul_assoc, ← hw, mul_assoc, (P.coxeterSystem hA).simple_mul_simple_self, mul_one]
    · change u₁.val (((P.coxeterSystem hA).simple i).val b) = b
      rw [coxeterSystem_simple, reflection_apply, hi, zero_smul, sub_zero, hu]

/-! ### Minimality and descent -/

section FiniteType

variable [FiniteDimensional K H]

/-- **Minimality.** Let `a`, `b` be antidominant integral and suppose no positive root `β` with
`⟨w b, β^∨⟩ = 0` has `⟨w a, β^∨⟩ > 0`. If `w' b = w b`, then `w' a - w a ∈ Q₊`. -/
theorem exists_apply_sub_eq_rootOf_of_upperClosureCondition (hA : A.IsFiniteCartan)
    {a b : Dual K H} (ha : ∀ i, ∃ n : ℕ, a (P.coroot i) = -n)
    (hb : ∀ i, ∃ n : ℕ, b (P.coroot i) = -n) {w w' : P.weylGroup hA.isGeneralizedCartan}
    (hU : P.UpperClosureCondition hA.isGeneralizedCartan (w.val a) (w.val b))
    (hb' : w'.val b = w.val b) :
    ∃ c : ι → ℤ, 0 ≤ c ∧ w'.val a - w.val a = P.rootOf c := by
  have hA' := hA.isGeneralizedCartan
  obtain ⟨w₁, u₁, rfl, hu₁b, hpos⟩ := P.exists_mul_eq_of_apply_eq hA' b w
  have hmul (x : Dual K H) : (w₁ * u₁ : P.weylGroup hA').val x = w₁.val (u₁.val x) := rfl
  have hsymm (x : Dual K H) : w₁.val.symm (w₁.val x) = x := w₁.val.symm_apply_apply x
  -- `u₁ a = a`
  have hu₁a : u₁.val a = a := by
    refine P.apply_eq_self_of_apply_eq_of_nonpos hA ha hb u₁.property hu₁b fun i hi ↦ ?_
    obtain ⟨n, hn⟩ := hU w₁.val w₁.property i (hpos i hi) (by rw [hmul, hsymm, hu₁b, hi])
    rw [hmul, hsymm] at hn
    exact ⟨n, hn⟩
  -- `v' = w₁⁻¹ w'` fixes `b`
  have hv'b : (w₁⁻¹ * w' : P.weylGroup hA').val b = b := by
    change w₁.val.symm (w'.val b) = b
    rw [hb', hmul, hsymm, hu₁b]
  obtain ⟨c, hc, hce, hcb⟩ := P.exists_apply_sub_eq_rootOf_of_apply_eq hA ha hb
    (w₁⁻¹ * w').property hv'b
  have hkey : w'.val a - (w₁ * u₁ : P.weylGroup hA').val a = w₁.val (P.rootOf c) := by
    rw [hmul, hu₁a, ← hce, map_sub]
    congr 1
    exact (w₁.val.apply_symm_apply (w'.val a)).symm
  have hk : ∀ i, ∃ k : ι → ℤ, 0 ≤ k ∧ (c i ≠ 0 → w₁.val (P.root i) = P.rootOf k) := fun i ↦ by
    by_cases hi : c i = 0
    · exact ⟨0, le_rfl, fun h ↦ absurd hi h⟩
    · obtain ⟨k, ⟨hk, -⟩, hk'⟩ := hpos i (hcb i hi)
      exact ⟨k, hk, fun _ ↦ hk'.symm⟩
  choose kk hkk0 hkk using hk
  refine ⟨∑ i, c i • kk i, Finset.sum_nonneg fun i _ ↦ smul_nonneg (hc i) (hkk0 i), ?_⟩
  rw [hkey, P.rootOf_apply c, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, map_zsmul]
  by_cases hi : c i = 0
  · simp [hi]
  · rw [hkk i hi]
    exact Int.cast_smul_eq_zsmul K (c i) (P.rootOf (kk i))

end FiniteType

/-! ### Descent -/

omit [DecidableEq ι] in
/-- **Descent.** Let `a`, `b` be antidominant integral. For every `w ∈ W` there is `w'' ∈ W` with
`w'' b = w b`, such that no positive root `β` with `⟨w b, β^∨⟩ = 0` has `⟨w'' a, β^∨⟩ > 0`, and
`w'' a` is reached from `w a` by a chain of reflections `ξ ↦ ξ - ⟨ξ, β^∨⟩ β` in positive roots
`β` orthogonal to `w b` with `⟨ξ, β^∨⟩ > 0`. -/
theorem exists_upperClosureCondition (hA' : A.IsGeneralizedCartan)
    {a b : Dual K H} (ha : ∀ i, ∃ n : ℕ, a (P.coroot i) = -n) (w : P.weylGroup hA') :
    ∃ w'' : P.weylGroup hA', w''.val b = w.val b ∧
      P.UpperClosureCondition hA' (w''.val a) (w.val b) ∧
      Relation.ReflTransGen (P.WallStep hA' (w.val b)) (w.val a) (w''.val a) := by
  choose na hna using ha
  have hc : ∀ w : P.weylGroup hA', ∃ c : ι → ℤ, 0 ≤ c ∧ w.val a - a = P.rootOf c := fun w ↦ by
    obtain ⟨c, hc, hce⟩ := P.exists_sub_apply_eq_rootOf hA' (μ := -a)
      (fun i => ⟨na i, by simp [hna i]⟩) w
    exact ⟨c, hc, by rw [← hce, map_neg]; abel⟩
  choose cc hcc0 hcc using hc
  induction hN : (∑ j, cc w j).toNat using Nat.strong_induction_on generalizing w with
  | _ N ih =>
  by_cases hU : P.UpperClosureCondition hA' (w.val a) (w.val b)
  · exact ⟨w, rfl, hU, .refl⟩
  · unfold UpperClosureCondition at hU
    push Not at hU
    obtain ⟨v, hv, i, hpos, hvb, hva⟩ := hU
    -- the pairing is a positive integer
    obtain ⟨n, hn0, hn⟩ : ∃ n : ℕ, 0 < n ∧ v.symm (w.val a) (P.coroot i) = n := by
      obtain ⟨k, hk⟩ := P.exists_apply_eq_add_rootOf hA' (mul_mem (inv_mem hv) w.property)
        (μ := a) fun j ↦ ⟨-(na j : ℤ), by simp [hna j]⟩
      obtain ⟨z, hz⟩ : ∃ z : ℤ, v.symm (w.val a) (P.coroot i) = z := by
        refine ⟨-(na i : ℤ) + (A *ᵥ k) i, ?_⟩
        change (v⁻¹ * w.val) a (P.coroot i) = _
        rw [hk, LinearMap.add_apply, hna i, rootOf_apply_coroot, Int.cast_add, Int.cast_neg,
          Int.cast_natCast]
      by_cases hz0 : 0 < z
      · exact ⟨z.toNat, by omega, by rw [hz, natCast_toNat hz0.le]⟩
      · refine absurd ?_ (hva (-z).toNat)
        rw [hz, natCast_toNat (by omega), Int.cast_neg, neg_neg]
    -- reflect in `β = v αᵢ`
    let s : P.weylGroup hA' := ⟨v * P.reflection hA' i * v⁻¹,
      mul_mem (mul_mem hv (P.reflection_mem_weylGroup hA' i)) (inv_mem hv)⟩
    have hs (x : Dual K H) : (s * w).val x =
        w.val x - v.symm (w.val x) (P.coroot i) • v (P.root i) := by
      change v (P.reflection hA' i (v.symm (w.val x))) = _
      rw [reflection_apply, map_sub, map_smul, LinearEquiv.apply_symm_apply]
    have hsb : (s * w).val b = w.val b := by rw [hs, hvb, zero_smul, sub_zero]
    have hsa : (s * w).val a = w.val a - n • v (P.root i) := by
      rw [hs, hn, Nat.cast_smul_eq_nsmul]
    have hstep : P.WallStep hA' (w.val b) (w.val a) ((s * w).val a) :=
      ⟨v, hv, i, n, hpos, hn0, hvb, hn, hsa⟩
    obtain ⟨k₁, hk₁, hk₁e⟩ := hpos
    have hcc' : cc (s * w) = cc w - n • k₁ := P.rootOf_injective (by
      rw [map_sub, map_nsmul, ← hcc, ← hcc, hsa, hk₁e]
      abel)
    have hlt : (∑ j, cc (s * w) j).toNat < N := by
      have h1 := KacMoodyAlgebra.sum_pos_of_mem_posCone hk₁
      have h2 : 0 ≤ ∑ j, cc (s * w) j := Finset.sum_nonneg fun j _ ↦ hcc0 (s * w) j
      have h3 : 0 < (n : ℤ) * ∑ j, k₁ j := mul_pos (by exact_mod_cast hn0) h1
      have h4 : ∑ j, cc (s * w) j = ∑ j, cc w j - (n : ℤ) * ∑ j, k₁ j := by
        rw [hcc', Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by simp
      omega
    obtain ⟨w'', hw''b, hw''U, hchain⟩ := ih _ hlt (s * w) rfl
    rw [hsb] at hw''b hw''U hchain
    exact ⟨w'', hw''b, hw''U, .head hstep hchain⟩

end Matrix.Realization
