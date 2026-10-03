/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.IntegrableWeyl

/-!
# Roots and real roots of `𝔤(A)` and the Weyl group

Let `A` be a generalized Cartan matrix and `K` a field of characteristic zero. The set of roots
`Δ` of `𝔤(A)` is the set of nonzero `α ∈ 𝔥*` with `𝔤_α ≠ 0`; every root is either positive
(`α ∈ Q₊`) or negative (`α ∈ -Q₊`) ([Kac] §1.3). Since the adjoint module is integrable, `Δ` and
the root multiplicities are invariant under the Weyl group `W` ([Kac] Prop. 3.7 (b)).
Moreover the fundamental reflection `rᵢ` permutes `Δ₊ \ {αᵢ}` ([Kac] Lemma 3.7).

A root is real if it is `W`-conjugate to a simple root ([Kac] §5.1); real roots have
multiplicity one, and `-α` is real when `α` is.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.roots`: the set of roots `Δ`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.mem_allWeights_of_rootSpace_ne_bot`: `𝔤_α ≠ 0` implies
  `α ∈ -(Q₊ \ 0) ∪ {0} ∪ (Q₊ \ 0)`.
* `Matrix.Realization.KacMoodyAlgebra.apply_mem_roots`: `W Δ = Δ`.
* `Matrix.Realization.KacMoodyAlgebra.reflection_mem_posWeights`: `rᵢ (Δ₊ \ {αᵢ}) ⊆ Δ₊`
  ([Kac] Lemma 3.7).
* `Matrix.Realization.KacMoodyAlgebra.rank_rootSpace_of_mem_realRoots`: real roots have
  multiplicity one.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §1.3, §3.7, §5.1
  (stated over `ℂ`).
-/

open Module LieModule LieAlgebra

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

namespace KacMoodyAlgebra

/-- The set of roots `Δ` of `𝔤(A)`: the nonzero `α ∈ 𝔥*` with `𝔤_α ≠ 0` ([Kac] §1.3). -/
def roots : Set (Dual K H) := {μ | μ ≠ 0 ∧ rootSpace P μ ≠ ⊥}

/-- The root spaces `𝔤_α ≠ 0` all have `α ∈ -(Q₊ \ 0) ∪ {0} ∪ (Q₊ \ 0)` ([Kac] §1.3). -/
theorem mem_allWeights_of_rootSpace_ne_bot {μ : Dual K H} (hμ : rootSpace P μ ≠ ⊥) :
    μ ∈ AuxLieAlgebra.allWeights P := by
  by_contra hμ'
  refine hμ (eq_bot_iff.mpr fun x hx ↦ ?_)
  have hx' : x ∈ ⨆ ν ∈ AuxLieAlgebra.allWeights P, rootSpace P ν := by
    rw [iSup_rootSpace_eq_top]; trivial
  have := mem_of_mem_iSup_of_le (h P)
    (fun ν ↦ ⨆ (_ : ν ∈ AuxLieAlgebra.allWeights P), rootSpace P ν)
    (fun ν ↦ iSup_le fun _ ↦ le_rfl) hx hx'
  rwa [iSup_neg hμ'] at this

/-- Every root is positive or negative ([Kac] §1.3). -/
theorem mem_posWeights_or_mem_negWeights {μ : Dual K H} (hμ : μ ∈ roots P) :
    μ ∈ P.posWeights ∨ μ ∈ P.negWeights := by
  rcases mem_allWeights_of_rootSpace_ne_bot P hμ.2 with (h | h) | h
  · exact Or.inr h
  · exact absurd h hμ.1
  · exact Or.inl h

variable [CharZero K]

lemma root_mem_roots (i : ι) : P.root i ∈ roots P :=
  ⟨P.linearIndependent_root.ne_zero i, by
    rw [rootSpace_root, Ne, Submodule.span_singleton_eq_bot]; exact e_ne_zero P i⟩

variable (hA : A.IsGeneralizedCartan)
include hA

/-- The root multiplicities of `𝔤(A)` are `W`-invariant ([Kac] Prop. 3.7 (b)). -/
theorem rootSpace_apply_eq_bot_iff {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    (μ : Dual K H) : rootSpace P (w μ) = ⊥ ↔ rootSpace P μ = ⊥ :=
  weightSpace_weylGroup_eq_bot_iff hA (isIntegrable_adjoint P hA) hw μ

/-- The set of roots is `W`-invariant ([Kac] Prop. 3.7 (b)). -/
theorem apply_mem_roots {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    {μ : Dual K H} (hμ : μ ∈ roots P) : w μ ∈ roots P :=
  ⟨by rw [Ne, map_eq_zero_iff w w.injective]; exact hμ.1,
    by rw [Ne, rootSpace_apply_eq_bot_iff P hA hw]; exact hμ.2⟩

/-- The fundamental reflection `rᵢ` maps the positive roots other than `αᵢ` to positive roots
([Kac] Lemma 3.7). The proof: `α = ∑ kⱼ αⱼ ≠ αᵢ` has some `kⱼ > 0` with `j ≠ i`, since
`k αᵢ` is not a root for `k ≥ 2`; `rᵢ α` is a root with the same coefficient `kⱼ`, hence is
positive. -/
theorem reflection_mem_posWeights {i : ι} {μ : Dual K H} (hμ : μ ∈ roots P)
    (hμp : μ ∈ P.posWeights) (hne : μ ≠ P.root i) : P.reflection hA i μ ∈ P.posWeights := by
  have hr := apply_mem_roots P hA (P.reflection_mem_weylGroup hA i) hμ
  obtain ⟨k, ⟨hk0, hkne⟩, rfl⟩ := hμp
  rw [reflection_rootOf] at hr ⊢
  set k' := k - (A *ᵥ k) i • Pi.single i 1
  have hk' : ∀ j, j ≠ i → k' j = k j := fun j hj ↦ by simp [k', hj]
  rcases mem_posWeights_or_mem_negWeights P hr with h | ⟨l, ⟨hl0, -⟩, hl⟩
  · exact h
  exfalso
  -- `rᵢ α` negative forces `α = kᵢ αᵢ`
  have hkl : k' + l = 0 := P.rootOf_injective (by rw [map_add, ← hl, neg_add_cancel, map_zero])
  have hkj : ∀ j, j ≠ i → k j = 0 := fun j hj ↦ by
    have h1 := congr_fun hkl j
    have h2 := hk0 j
    have h3 := hl0 j
    simp only [Pi.add_apply, Pi.zero_apply, hk' j hj] at h1 h2 h3
    omega
  have hki : 0 ≤ k i := hk0 i
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k i = n := ⟨(k i).toNat, (Int.toNat_of_nonneg hki).symm⟩
  have hμ' : P.rootOf k = n • P.root i := by
    rw [P.rootOf_eq_smul_root_of_eq_zero hkj, hn, Int.cast_natCast, Nat.cast_smul_eq_nsmul]
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · interval_cases n
    · exact hkne (funext fun j ↦ by
        by_cases hj : j = i
        · subst hj; simpa using hn
        · simpa using hkj j hj)
    · exact hne (by rw [hμ', one_smul])
  · exact hμ.2 (by rw [hμ']; exact rootSpace_nsmul_root_eq_bot P i hn2)

/-! ### Real roots -/

/-- Real roots are roots ([Kac] §5.1). -/
theorem realRoots_subset_roots : P.realRoots hA ⊆ roots P := by
  rintro _ ⟨w, hw, i, rfl⟩
  exact apply_mem_roots P hA hw (root_mem_roots P i)

/-- Real roots have multiplicity one ([Kac] §5.1). -/
theorem rank_rootSpace_of_mem_realRoots {μ : Dual K H} (hμ : μ ∈ P.realRoots hA) :
    Module.rank K (rootSpace P μ) = 1 := by
  obtain ⟨w, hw, i, rfl⟩ := hμ
  rw [rank_rootSpace_weylGroup P hA hw, rootSpace_root, ← Module.finrank_eq_rank,
    finrank_span_singleton (e_ne_zero P i), Nat.cast_one]

end KacMoodyAlgebra

end Matrix.Realization
