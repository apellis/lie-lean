/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.IntegrableRoots
import LieLean.LinearAlgebra.Matrix.Cartan.FiniteType

/-!
# Kac–Moody algebras of finite type are finite-dimensional

Let `A` be a Cartan matrix of finite type (Mathlib's `Matrix.IsFiniteCartan`: `D A` is symmetric
positive definite for a positive diagonal integer matrix `D`), `K` a field of characteristic
zero and `(𝔥, Π, Π^∨)` a realization of `A` with `𝔥` finite-dimensional. We prove that every root
of `𝔤(A)` is real, that there are finitely many roots, each of multiplicity one, and hence that
`𝔤(A)` is finite-dimensional ([Kac] Prop. 4.9 and Prop. 5.10 (a) (check); Kac states these for
indecomposable `A`, which is not needed here).

## The argument

Write `q(k) = kᵀ D A k` for `k ∈ Q = ℤ^ι`; `q` is positive definite. Let `α = ∑ kⱼ αⱼ` be a
positive root. We show by induction on the height `∑ kⱼ` that `α` is real. If `α` is simple, this
is clear. Otherwise, if `⟨α, αᵢ^∨⟩ = (A k)ᵢ ≤ 0` for all `i`, then
`q(k) = ∑ᵢ kᵢ dᵢ (A k)ᵢ ≤ 0` since all `kᵢ ≥ 0`, contradicting positive definiteness. So
`(A k)ᵢ > 0` for some `i`; then `rᵢ α = α - (A k)ᵢ αᵢ` is a root (roots are `W`-invariant), it is
positive since `α ≠ αᵢ` ([Kac] Lemma 3.7 (check)), and it has smaller height. By induction
`rᵢ α` is real, hence so is `α = rᵢ (rᵢ α)`. Negative roots are the negatives of positive roots
(via the Chevalley involution), and `-Δ^re = Δ^re`.

This is the standard argument (cf. [Kac] §5.1–5.2 (check)); we reconstructed it rather than
following a specific printed proof.

Since the set of real roots is finite (`Matrix.Realization.finite_realRoots`) and real roots have
multiplicity one (`Matrix.Realization.KacMoodyAlgebra.rank_rootSpace_of_mem_realRoots`), the root
space decomposition `𝔤(A) = 𝔥 ⊕ ⨁_{α ∈ Δ} 𝔤_α` shows that `𝔤(A)` is finite-dimensional.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.neg_mem_roots`: `Δ = -Δ`.
* `Matrix.Realization.KacMoodyAlgebra.roots_eq_realRoots`: for `A` of finite type, `Δ = Δ^re`.
* `Matrix.Realization.KacMoodyAlgebra.finite_roots`: for `A` of finite type, `Δ` is finite.
* `Matrix.Realization.KacMoodyAlgebra.finrank_rootSpace_of_mem_roots`: all root spaces are
  one-dimensional.
* `Matrix.Realization.KacMoodyAlgebra.finiteDimensional`: `𝔤(A)` is finite-dimensional.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §3.7, §4.9, §5.1,
  Prop. 5.10.
-/

open Module LieModule LieAlgebra

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- The Chevalley involution maps `𝔤_μ` to `𝔤_{-μ}`. -/
lemma chevalleyInvolution_mem_rootSpace {μ : Dual K H} {x : P.KacMoodyAlgebra}
    (hx : x ∈ rootSpace P μ) : chevalleyInvolution P x ∈ rootSpace P (-μ) := by
  intro a
  have := congr_arg (chevalleyInvolution P) (hx (-a))
  simp only [LieHom.map_lie, map_neg, chevalleyInvolution_h, neg_neg, map_smul] at this
  rw [this, LinearMap.neg_apply, neg_smul]

/-- `Δ = -Δ` ([Kac] §1.3). -/
theorem neg_mem_roots {μ : Dual K H} (hμ : μ ∈ roots P) : -μ ∈ roots P := by
  refine ⟨neg_ne_zero.mpr hμ.1, ?_⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ.2
  refine Submodule.ne_bot_iff _ |>.mpr ⟨_, chevalleyInvolution_mem_rootSpace P hx, fun h ↦ hx0 ?_⟩
  rw [← chevalleyInvolution_chevalleyInvolution P x, h, map_zero]

variable (hA : A.IsFiniteCartan)
include hA

/-- For `A` of finite type, the positive root `∑ kⱼ αⱼ` of height `< n` is real (the induction
step of `Matrix.Realization.KacMoodyAlgebra.roots_eq_realRoots`). -/
lemma rootOf_mem_realRoots_of_height_lt (n : ℕ) : ∀ k : ι → ℤ, 0 ≤ k → height k < n →
    P.rootOf k ∈ roots P → P.rootOf k ∈ P.realRoots hA.isGeneralizedCartan := by
  set hA' := hA.isGeneralizedCartan
  have hheight : ∀ k : ι → ℤ, 0 ≤ k → 0 ≤ height k := fun k hk ↦
    Finset.sum_nonneg fun i _ ↦ hk i
  induction n with
  | zero =>
    intro k hk hkn _
    have := hheight k hk
    omega
  | succ n ih =>
  intro k hk hkn hroot
  by_cases hsimple : ∃ i, P.rootOf k = P.root i
  · obtain ⟨i, hi⟩ := hsimple
    rw [hi]
    exact P.root_mem_realRoots hA' i
  push Not at hsimple
  have hk0 : k ≠ 0 := fun h ↦ hroot.1 (by simp [h])
  -- some `⟨α, αᵢ^∨⟩` is positive, by positive definiteness
  obtain ⟨i, hi⟩ : ∃ i, 0 < (A *ᵥ k) i := by
    by_contra! h
    obtain ⟨d, hd, hpos⟩ := hA.exists_posDef
    have h1 := hpos.dotProduct_mulVec_pos hk0
    rw [star_trivial, ← mulVec_mulVec] at h1
    have h2 : k ⬝ᵥ diagonal d *ᵥ (A *ᵥ k) ≤ 0 := by
      refine Finset.sum_nonpos fun j _ ↦ ?_
      rw [mulVec_diagonal]
      exact mul_nonpos_of_nonneg_of_nonpos (hk j)
        (mul_nonpos_of_nonneg_of_nonpos (hd j).le (h j))
    exact absurd h1 (not_lt.mpr h2)
  set k' := k - (A *ᵥ k) i • Pi.single i 1 with hk'def
  have hr : P.reflection hA' i (P.rootOf k) = P.rootOf k' := P.reflection_rootOf hA' i k
  have hroot' : P.rootOf k' ∈ roots P :=
    hr ▸ apply_mem_roots P hA' (P.reflection_mem_weylGroup hA' i) hroot
  obtain ⟨k'', ⟨hk''0, -⟩, hk''⟩ : P.rootOf k' ∈ P.posWeights :=
    hr ▸ reflection_mem_posWeights P hA' hroot ⟨k, ⟨hk, hk0⟩, rfl⟩ (hsimple i)
  obtain rfl : k'' = k' := P.rootOf_injective hk''
  have hh : height k' < n := by
    have : height k' = height k - (A *ᵥ k) i := by
      simp [hk'def, height, Finset.sum_sub_distrib, Pi.single_apply]
    omega
  have hreal := ih k' hk''0 hh hroot'
  have : P.rootOf k = P.reflection hA' i (P.rootOf k') := by
    rw [← hr, reflection_reflection]
  rw [this]
  exact P.apply_mem_realRoots hA' (P.reflection_mem_weylGroup hA' i) hreal

/-- For `A` of finite type, every root of `𝔤(A)` is real: `Δ = Δ^re`
([Kac] Prop. 5.10 (a) (check), `Δ^im = ∅`). -/
theorem roots_eq_realRoots : roots P = P.realRoots hA.isGeneralizedCartan := by
  refine subset_antisymm (fun μ hμ ↦ ?_) (realRoots_subset_roots P hA.isGeneralizedCartan)
  rcases mem_posWeights_or_mem_negWeights P hμ with ⟨k, ⟨hk, -⟩, rfl⟩ | ⟨k, ⟨hk, -⟩, rfl⟩
  · exact rootOf_mem_realRoots_of_height_lt P hA ((height k).toNat + 1) k hk (by omega) hμ
  · have := rootOf_mem_realRoots_of_height_lt P hA ((height k).toNat + 1) k hk (by omega)
      (by simpa using neg_mem_roots P hμ)
    exact P.neg_mem_realRoots _ this

/-- For `A` of finite type, `𝔤(A)` has finitely many roots ([Kac] Prop. 4.9 (check)). -/
theorem finite_roots : (roots P).Finite := by
  rw [roots_eq_realRoots P hA]
  exact P.finite_realRoots hA

/-- For `A` of finite type, all root spaces of `𝔤(A)` are one-dimensional. -/
theorem finrank_rootSpace_of_mem_roots {μ : Dual K H} (hμ : μ ∈ roots P) :
    finrank K (rootSpace P μ) = 1 := by
  rw [roots_eq_realRoots P hA] at hμ
  exact finrank_eq_of_rank_eq (rank_rootSpace_of_mem_realRoots P hA.isGeneralizedCartan hμ)

/-- For `A` of finite type (and `𝔥` finite-dimensional), `𝔤(A)` is finite-dimensional
([Kac] Prop. 4.9 (check)). -/
theorem finiteDimensional [FiniteDimensional K H] : FiniteDimensional K P.KacMoodyAlgebra := by
  set S := insert 0 (roots P)
  have hS : S.Finite := (finite_roots P hA).insert 0
  have hfg : (⨆ μ ∈ hS.toFinset, rootSpace P μ).FG := by
    refine Submodule.fg_biSup _ _ fun μ hμ ↦ ?_
    rw [Set.Finite.mem_toFinset] at hμ
    rcases hμ with rfl | hμ
    · rw [rootSpace_zero, Submodule.fg_iff_finiteDimensional]
      infer_instance
    · rw [Submodule.fg_iff_finiteDimensional]
      exact Module.finite_of_finrank_eq_succ (finrank_rootSpace_of_mem_roots P hA hμ)
  have htop : (⊤ : Submodule K P.KacMoodyAlgebra) ≤ ⨆ μ ∈ hS.toFinset, rootSpace P μ := by
    rw [← iSup_rootSpace_eq_top P]
    refine iSup₂_le fun μ _ ↦ ?_
    by_cases h0 : μ = 0
    · exact le_iSup₂_of_le μ (by simp [S, h0]) le_rfl
    by_cases hb : rootSpace P μ = ⊥
    · rw [hb]
      exact bot_le
    · exact le_iSup₂_of_le μ (by simp [S, roots, h0, hb]) le_rfl
  exact Module.finite_def.mpr (top_le_iff.mp htop ▸ hfg)

end Matrix.Realization.KacMoodyAlgebra
