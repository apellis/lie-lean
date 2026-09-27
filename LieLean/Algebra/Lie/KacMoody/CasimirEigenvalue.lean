/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.HighestWeight
import LieLean.LinearAlgebra.Matrix.Cartan.Symmetrizable

/-!
# Eigenvalues of the Casimir operator on dominant weights

Let `A` be a symmetrizable generalized Cartan matrix with a symmetrization `A = diag(ε) B`, let
`(𝔥, Π, Π^∨)` be a realization of `A` over a field `K` of characteristic zero, and let `(·|·)` be
the standard form on `𝔥*` ([Kac] §2.1). Let `ρ ∈ 𝔥*` with `⟨ρ, αᵢ^∨⟩ = 1` for all `i`. The
generalized Casimir operator acts on a highest-weight vector of weight `λ` by the scalar
`(λ + 2ρ | λ)` ([Kac] Cor. 2.6 (check)). We show that this scalar separates dominant integral
weights that are comparable for the order `μ ≤ Λ ↔ Λ - μ ∈ Q₊`: if `Λ, μ` are dominant integral
and `Λ = μ + β` with `β ∈ Q₊ \ {0}`, then `(Λ + 2ρ | Λ) - (μ + 2ρ | μ)` is a positive rational
number; in particular `(Λ + 2ρ | Λ) ≠ (μ + 2ρ | μ)`. This is the key input in the proof of complete
reducibility of integrable modules in the category `𝒪` ([Kac] Thm. 10.7 (check)).

## Main results

* `Matrix.Realization.dualBilinForm_add_two_smul_sub`: for `Λ = μ + β`,
  `(Λ + 2ρ | Λ) - (μ + 2ρ | μ) = (Λ + μ + 2ρ | β)`.
* `Matrix.Realization.exists_rat_pos_dualBilinForm_add_two_smul_sub`: for `Λ, μ` dominant
  integral with `Λ - μ ∈ Q₊ \ {0}`, `(Λ + 2ρ | Λ) - (μ + 2ρ | μ)` is a positive rational number.
* `Matrix.Realization.dualBilinForm_add_two_smul_ne`: in particular
  `(Λ + 2ρ | Λ) ≠ (μ + 2ρ | μ)`.

## Proof

Writing `β = Σ kᵢ αᵢ` with `kᵢ ∈ ℕ` not all zero, and `nᵢ = ⟨Λ, αᵢ^∨⟩`, `mᵢ = ⟨μ, αᵢ^∨⟩`, we have
`(Λ + 2ρ | Λ) - (μ + 2ρ | μ) = (Λ + μ + 2ρ | β) = Σ kᵢ (Λ + μ + 2ρ | αᵢ)
= Σ kᵢ (nᵢ + mᵢ + 2) / εᵢ > 0`, using `(ν | αᵢ) = ⟨ν, αᵢ^∨⟩ / εᵢ`. This is the computation of
[Kac] §10.3 (check) / proof of Thm. 10.7 (check), written out here.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.1, §2.5, §10.3.
-/

open Module

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (S : A.Symmetrization)

/-- For `Λ = μ + β`: `(Λ + 2ρ | Λ) - (μ + 2ρ | μ) = (Λ + μ + 2ρ | β)`, for any `ρ ∈ 𝔥*`. -/
theorem dualBilinForm_add_two_smul_sub (ρ μ β : Dual K H) :
    P.dualBilinForm S (μ + β + 2 • ρ) (μ + β) - P.dualBilinForm S (μ + 2 • ρ) μ =
      P.dualBilinForm S (μ + β + μ + 2 • ρ) β := by
  have hsymm := (P.isSymm_dualBilinForm S).eq β μ
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at *
  rw [hsymm]
  ring

variable {P S}

/-- `(ν | Σ kᵢ αᵢ) = Σ kᵢ ⟨ν, αᵢ^∨⟩ / εᵢ`. -/
lemma dualBilinForm_rootOf_right (ν : Dual K H) (k : ι → ℤ) :
    P.dualBilinForm S ν (P.rootOf k) = ∑ i, (k i : K) * (ν (P.coroot i) / S.ε i) := by
  simp [rootOf_apply, map_sum, dualBilinForm_root_right]

/-- If `Λ, μ` are dominant integral and `Λ = μ + Σ kᵢ αᵢ` with `kᵢ ≥ 0` not all zero, then
`(Λ + 2ρ | Λ) - (μ + 2ρ | μ)` is a positive rational number, for any `ρ` with `⟨ρ, αᵢ^∨⟩ = 1`
([Kac] §10.3 (check)). -/
theorem exists_rat_pos_dualBilinForm_add_two_smul_sub {ρ : Dual K H}
    (hρ : ∀ i, ρ (P.coroot i) = 1) {Λ μ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
    (hμ : P.IsDominantIntegral μ) {k : ι → ℤ} (hk : 0 ≤ k) (hk0 : k ≠ 0)
    (hΛμ : Λ = μ + P.rootOf k) :
    ∃ q : ℚ, 0 < q ∧
      P.dualBilinForm S (Λ + 2 • ρ) Λ - P.dualBilinForm S (μ + 2 • ρ) μ = q := by
  choose n hn using hΛ
  choose m hm using hμ
  refine ⟨∑ i, (k i : ℚ) * ((n i + m i + 2 : ℚ) / S.ε i), ?_, ?_⟩
  · obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
      by_contra! h
      exact hk0 (funext h)
    have hkj : (0 : ℚ) < k j := by exact_mod_cast lt_of_le_of_ne (hk j) (Ne.symm hj)
    have hpos : ∀ i, (0 : ℚ) < (n i + m i + 2 : ℚ) / S.ε i := fun i ↦
      div_pos (by positivity) (S.ε_pos i)
    refine Finset.sum_pos' (fun i _ ↦ mul_nonneg (by exact_mod_cast hk i) (hpos i).le)
      ⟨j, Finset.mem_univ j, mul_pos hkj (hpos j)⟩
  · rw [hΛμ, dualBilinForm_add_two_smul_sub, dualBilinForm_rootOf_right, ← hΛμ]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hn, hm, hρ, nsmul_eq_mul]
    push_cast
    ring

/-- The Casimir eigenvalue `(λ + 2ρ | λ)` separates comparable dominant integral weights: if
`Λ, μ` are dominant integral and `Λ - μ ∈ Q₊ \ {0}`, then `(Λ + 2ρ | Λ) ≠ (μ + 2ρ | μ)`, for any
`ρ` with `⟨ρ, αᵢ^∨⟩ = 1` ([Kac] proof of Thm. 10.7 (check)). -/
theorem dualBilinForm_add_two_smul_ne {ρ : Dual K H} (hρ : ∀ i, ρ (P.coroot i) = 1)
    {Λ μ : Dual K H} (hΛ : P.IsDominantIntegral Λ) (hμ : P.IsDominantIntegral μ) {k : ι → ℤ}
    (hk : 0 ≤ k) (hk0 : k ≠ 0) (hΛμ : Λ = μ + P.rootOf k) :
    P.dualBilinForm S (Λ + 2 • ρ) Λ ≠ P.dualBilinForm S (μ + 2 • ρ) μ := by
  obtain ⟨q, hq, hq'⟩ := exists_rat_pos_dualBilinForm_add_two_smul_sub (S := S) hρ hΛ hμ hk hk0 hΛμ
  rw [← sub_ne_zero, hq']
  exact_mod_cast hq.ne'

end Matrix.Realization
