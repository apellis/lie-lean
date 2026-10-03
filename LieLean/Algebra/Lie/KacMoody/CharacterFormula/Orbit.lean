/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterAntiInvariant
import LieLean.LinearAlgebra.Matrix.Cartan.Symmetrizable
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroupDominant

/-!
# Anti-invariant formal characters supported on a sphere

Let `A` be a symmetrizable generalized Cartan matrix with symmetrization `S`, `K` a field of
characteristic zero, and let `Λ₀ ∈ 𝔥*` be *regular dominant integral*: `⟨Λ₀, αᵢ^∨⟩ ∈ {1, 2, …}` for
all `i` (e.g. `Λ₀ = Λ + ρ` for `Λ` dominant integral). This file contains the combinatorial final
step of the proof of the Weyl–Kac character formula ([Kac] §10.4): if `X ∈ ℰ` is
`W`-anti-invariant, `X_{Λ₀} = 1`, and every `μ` with `X_μ ≠ 0` satisfies `Λ₀ - μ ∈ Q₊` and
`(μ | μ) = (Λ₀ | Λ₀)`, then `X = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w Λ₀}` coefficientwise.

## Proof

Let `X_μ ≠ 0`. By anti-invariance `X_{w μ} ≠ 0` for all `w ∈ W`, so `Λ₀ - w μ ∈ Q₊`; choose `w`
with `ν = w μ` of maximal height. Then `ν` is dominant integral: `⟨ν, αᵢ^∨⟩ = mᵢ ∈ ℤ` since
`ν ∈ Λ₀ + Q`, and `rᵢ ν = ν - mᵢ αᵢ` has height `≤` that of `ν`, so `mᵢ ≥ 0`. Writing
`Λ₀ - ν = ∑ kⱼ αⱼ` with `kⱼ ≥ 0`, we get
`0 = (Λ₀ | Λ₀) - (ν | ν) = (Λ₀ - ν | Λ₀ + ν) = ∑ⱼ kⱼ ⟨Λ₀ + ν, αⱼ^∨⟩ / εⱼ`, a sum of nonnegative
rationals with `⟨Λ₀ + ν, αⱼ^∨⟩ ≥ 1`, whence all `kⱼ = 0` and `μ = w⁻¹ Λ₀`. Moreover the stabilizer
of `Λ₀` in `W` is trivial ([Kac] Prop. 3.12 (a)): if `w ≠ 1` has a right descent `i`, then
`Λ₀ - w Λ₀ = (Λ₀ - (w rᵢ) Λ₀) + ⟨Λ₀, αᵢ^∨⟩ (w rᵢ) αᵢ` with `Λ₀ - (w rᵢ) Λ₀ ∈ Q₊`
(`Matrix.Realization.exists_sub_apply_eq_rootOf`) and `(w rᵢ) αᵢ ∈ Q₊ \ {0}`, so `w Λ₀ ≠ Λ₀`.
Hence `X_{w Λ₀} = (-1)^{ℓ(w)}` for the unique `w` with `w Λ₀ = μ`, and `X_μ = 0` if `μ ∉ W Λ₀`.
(This follows the argument of [Kac] §10.4; the details are written out by us.)

## Main results

* `Matrix.Realization.apply_ne_self_of_regular`, `Matrix.Realization.apply_injective_of_regular`:
  the stabilizer in `W` of a regular dominant integral weight is trivial.
* `Matrix.Realization.CharacterRing.exists_apply_eq_of_isWeylAntiInvariant`: the support of `X`
  lies in the orbit `W Λ₀`.
* `Matrix.Realization.CharacterRing.coeffAt_eq_finsum_of_isWeylAntiInvariant`:
  `X_μ = ∑_{w ∈ W, w Λ₀ = μ} (-1)^{ℓ(w)}`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Prop. 3.12, §10.4.
-/

open Module CoxeterSystem

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)

/-! ### The stabilizer of a regular dominant weight -/

omit [DecidableEq ι] in
/-- The stabilizer in `W` of a regular dominant integral weight `Λ₀` (`⟨Λ₀, αᵢ^∨⟩ ∈ {1, 2, …}`) is
trivial ([Kac] Prop. 3.12 (a)). -/
theorem apply_ne_self_of_regular {μ : Dual K H} (hμ : ∀ i, ∃ n : ℕ, μ (P.coroot i) = n + 1)
    {w : P.weylGroup hA} (hw : w ≠ 1) : (w : Dual K H ≃ₗ[K] Dual K H) μ ≠ μ := by
  classical
  set cs := P.coxeterSystem hA
  obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hw
  have hnd : ¬cs.IsRightDescent (w * cs.simple i) i := by
    rwa [← isRightDescent_iff_not_isRightDescent_mul]
  obtain ⟨l, hl, hwl⟩ := (P.not_isRightDescent_coxeterSystem_iff hA).mp hnd
  have hdom : ∀ i, ∃ n : ℕ, μ (P.coroot i) = n := fun i ↦ by
    obtain ⟨n, hn⟩ := hμ i
    exact ⟨n + 1, by rw [hn]; push_cast; rfl⟩
  obtain ⟨k, hk, hwk⟩ := P.exists_sub_apply_eq_rootOf hA hdom (w * cs.simple i)
  obtain ⟨m, hm⟩ := hμ i
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, coxeterSystem_simple, cs] at hwk hwl
  have hw' : (w : Dual K H ≃ₗ[K] Dual K H) μ =
      (w : Dual K H ≃ₗ[K] Dual K H) (P.reflection hA i μ) -
        ((m : K) + 1) • (w : Dual K H ≃ₗ[K] Dual K H) (P.reflection hA i (P.root i)) := by
    rw [reflection_apply P hA i μ, reflection_root_self, map_sub, map_smul, map_neg, hm]
    module
  have heq : μ - (w : Dual K H ≃ₗ[K] Dual K H) μ = P.rootOf (k + ((m : ℤ) + 1) • l) := by
    rw [hw', map_add, map_zsmul, ← Int.cast_smul_eq_zsmul K, ← hwk, ← hwl]
    push_cast
    abel
  intro h
  rw [h, sub_self, eq_comm, ← map_zero P.rootOf, P.rootOf_injective.eq_iff] at heq
  have hl0 : l = 0 := funext fun j ↦ by
    have h1 := congr_fun heq j
    have h2 := hk j
    have h3 := hl j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2 h3 ⊢
    nlinarith
  rw [hl0, map_zero, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at hwl
  exact P.linearIndependent_root.ne_zero i hwl

omit [DecidableEq ι] in
/-- The map `w ↦ w Λ₀` is injective on `W` for a regular dominant integral weight `Λ₀`
([Kac] Prop. 3.12 (a)). -/
theorem apply_injective_of_regular {μ : Dual K H} (hμ : ∀ i, ∃ n : ℕ, μ (P.coroot i) = n + 1) :
    Function.Injective fun w : P.weylGroup hA ↦ (w : Dual K H ≃ₗ[K] Dual K H) μ := by
  intro w w' h
  by_contra hne
  have h1 : w'⁻¹ * w ≠ 1 := fun h1 ↦ hne (inv_mul_eq_one.mp h1).symm
  refine P.apply_ne_self_of_regular hA hμ h1 ?_
  simp only at h
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, h, Subgroup.coe_inv]
  exact LinearEquiv.symm_apply_apply _ μ

/-! ### Anti-invariant elements supported on a sphere -/

namespace CharacterRing

variable {P hA} [FiniteDimensional K H]

/-- Let `X ∈ ℰ` be `W`-anti-invariant and `Λ₀` regular dominant integral, and suppose that every
`μ` with `X_μ ≠ 0` satisfies `Λ₀ - μ ∈ Q₊` and `(μ | μ) = (Λ₀ | Λ₀)`. Then the support of `X`
lies in the orbit `W Λ₀` ([Kac] §10.4). -/
theorem exists_apply_eq_of_isWeylAntiInvariant (S : A.Symmetrization) {X : P.CharacterRing ℤ}
    (hX : X.IsWeylAntiInvariant P hA) {Λ₀ : Dual K H}
    (hΛ₀ : ∀ i, ∃ n : ℕ, Λ₀ (P.coroot i) = n + 1)
    (hsupp : ∀ μ, X.coeffAt μ ≠ 0 → (∃ k : ι → ℤ, 0 ≤ k ∧ Λ₀ - μ = P.rootOf k) ∧
      P.dualBilinForm S μ μ = P.dualBilinForm S Λ₀ Λ₀)
    {μ : Dual K H} (hμ : X.coeffAt μ ≠ 0) :
    ∃ w : P.weylGroup hA, (w : Dual K H ≃ₗ[K] Dual K H) Λ₀ = μ := by
  classical
  have hXw : ∀ w : P.weylGroup hA, X.coeffAt ((w : Dual K H ≃ₗ[K] Dual K H) μ) ≠ 0 := by
    intro w
    rw [hX w μ]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hμ
  have hex : ∃ n : ℕ, ∃ w : P.weylGroup hA, ∃ k : ι → ℤ, 0 ≤ k ∧
      Λ₀ - (w : Dual K H ≃ₗ[K] Dual K H) μ = P.rootOf k ∧ height k = n := by
    obtain ⟨k, hk, hk'⟩ := (hsupp μ hμ).1
    refine ⟨(height k).toNat, 1, k, hk, by simpa using hk', ?_⟩
    exact (Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ ↦ hk i)).symm
  obtain ⟨w, k, hk, hwk, hht⟩ := Nat.find_spec hex
  set ν := (w : Dual K H ≃ₗ[K] Dual K H) μ with hν
  -- `ν` is dominant integral
  have hdom : ∀ i, ∃ m : ℕ, ν (P.coroot i) = m := by
    intro i
    obtain ⟨n, hn⟩ := hΛ₀ i
    set m : ℤ := n + 1 - (A *ᵥ k) i
    have hm : ν (P.coroot i) = m := by
      have : ν = Λ₀ - P.rootOf k := by rw [← hwk]; abel
      rw [this, LinearMap.sub_apply, hn, rootOf_apply_coroot]
      push_cast [m]
      ring
    -- the height of `rᵢ ν` is at most that of `ν`
    obtain ⟨k', hk', hwk'⟩ := (hsupp _ (hXw ((P.coxeterSystem hA).simple i * w))).1
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, coxeterSystem_simple, ← hν] at hwk'
    have hkk' : k' = k + m • Pi.single i 1 := by
      refine P.rootOf_injective ?_
      rw [← hwk', map_add, map_zsmul, rootOf_single, ← hwk, reflection_apply, hm,
        ← Int.cast_smul_eq_zsmul K]
      abel
    have hmin := Nat.find_min' hex ⟨(P.coxeterSystem hA).simple i * w, k', hk',
      by simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply, coxeterSystem_simple] using hwk',
      (Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ ↦ hk' j)).symm⟩
    have hht' : height k' = height k + m := by
      rw [hkk']
      simp [height, Finset.sum_add_distrib, Pi.single_apply]
    have hm0 : 0 ≤ m := by
      have h1 : ((height k').toNat : ℤ) = height k' :=
        Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ ↦ hk' j)
      have h2 : (Nat.find hex : ℤ) ≤ height k' := by rw [← h1]; exact_mod_cast hmin
      linarith
    exact ⟨m.toNat, by rw [hm]; exact_mod_cast (Int.toNat_of_nonneg hm0).symm⟩
  -- `(Λ₀ | Λ₀) = (ν | ν)` forces `k = 0`
  choose n hn using hΛ₀
  choose m hm using hdom
  have hsymm := (P.isSymm_dualBilinForm S).eq
  have hΛν : Λ₀ = ν + P.rootOf k := by rw [← hwk]; abel
  have h1 : P.dualBilinForm S (P.rootOf k) (Λ₀ + ν) = 0 := by
    have := (hsupp ν (hXw w)).2
    rw [hΛν] at this ⊢
    simp only [map_add, LinearMap.add_apply] at this ⊢
    rw [hsymm ν (P.rootOf k)] at this
    linear_combination -this
  have h2 : P.dualBilinForm S (P.rootOf k) (Λ₀ + ν) =
      ((∑ i, (k i : ℚ) * ((n i + m i + 1) / S.ε i) : ℚ) : K) := by
    rw [rootOf_apply, map_sum, LinearMap.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hsymm, dualBilinForm_root_right]
    simp only [LinearMap.add_apply, hn, hm]
    ring
  rw [h2, Rat.cast_eq_zero] at h1
  have hk0 : k = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ mul_nonneg
      (by exact_mod_cast hk i) (div_nonneg (by positivity) (S.ε_pos i).le)).mp h1
    ext i
    have hi := this i (Finset.mem_univ i)
    rw [mul_eq_zero, div_eq_zero_iff] at hi
    have : (n i : ℚ) + m i + 1 ≠ 0 := by positivity
    simpa [this, (S.ε_pos i).ne'] using hi
  refine ⟨w⁻¹, ?_⟩
  rw [hΛν, hk0, map_zero, add_zero, hν, Subgroup.coe_inv]
  exact LinearEquiv.symm_apply_apply _ μ

open Classical in
/-- **The final step of the proof of the Weyl–Kac character formula** ([Kac] §10.4): let
`X ∈ ℰ` be `W`-anti-invariant, `Λ₀` regular dominant integral, `X_{Λ₀} = 1`, and suppose that every
`μ` with `X_μ ≠ 0` satisfies `Λ₀ - μ ∈ Q₊` and `(μ | μ) = (Λ₀ | Λ₀)`. Then
`X = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w Λ₀}`, i.e. `X_μ = ∑_{w ∈ W, w Λ₀ = μ} (-1)^{ℓ(w)}` (a sum with at
most one nonzero term). -/
theorem coeffAt_eq_finsum_of_isWeylAntiInvariant (S : A.Symmetrization) {X : P.CharacterRing ℤ}
    (hX : X.IsWeylAntiInvariant P hA) {Λ₀ : Dual K H}
    (hΛ₀ : ∀ i, ∃ n : ℕ, Λ₀ (P.coroot i) = n + 1) (hX₀ : X.coeffAt Λ₀ = 1)
    (hsupp : ∀ μ, X.coeffAt μ ≠ 0 → (∃ k : ι → ℤ, 0 ≤ k ∧ Λ₀ - μ = P.rootOf k) ∧
      P.dualBilinForm S μ μ = P.dualBilinForm S Λ₀ Λ₀) (μ : Dual K H) :
    X.coeffAt μ = ∑ᶠ w : P.weylGroup hA,
      if (w : Dual K H ≃ₗ[K] Dual K H) Λ₀ = μ then (-1) ^ (P.coxeterSystem hA).length w else 0 := by
  classical
  by_cases h : ∃ w : P.weylGroup hA, (w : Dual K H ≃ₗ[K] Dual K H) Λ₀ = μ
  · obtain ⟨w, rfl⟩ := h
    rw [finsum_eq_single _ w fun w' hw' ↦ ite_eq_right fun h ↦ hw'
      (P.apply_injective_of_regular hA hΛ₀ h), ite_eq_left rfl, hX w Λ₀, hX₀, mul_one]
  · rw [finsum_eq_zero_of_forall_eq_zero fun w ↦ ite_eq_right fun h' ↦ h ⟨w, h'⟩]
    by_contra hμ
    exact h (exists_apply_eq_of_isWeylAntiInvariant S hX hΛ₀ hsupp hμ)

end CharacterRing

end Matrix.Realization
