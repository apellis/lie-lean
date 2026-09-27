/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroupCoxeter

/-!
# Dominant integral weights and the Weyl group

Let `A` be a generalized Cartan matrix with realization `(𝔥, Π, Π^∨)` over a field `K` of
characteristic zero, and `W` its Weyl group. A weight `λ ∈ 𝔥*` is dominant integral if
`⟨λ, αᵢ^∨⟩ ∈ ℤ₊` for all `i`. We prove that for dominant integral `λ` and `w ∈ W`,
`λ - w λ ∈ Q₊`, and deduce that the `W`-orbit of `λ` contains no other dominant integral weight.
These are the integral forms, for weights, of the statement that the fundamental chamber is a
fundamental domain for the action of `W` on the Tits cone ([Kac] Prop. 3.12 (b) (check)).

The proof is by induction on `ℓ(w)`: if `ℓ(w rᵢ) < ℓ(w)` then `(w rᵢ) αᵢ ∈ Q₊`
(`Matrix.Realization.not_isRightDescent_coxeterSystem_iff`) and
`λ - w λ = (λ - (w rᵢ) λ) + ⟨λ, αᵢ^∨⟩ (w rᵢ) αᵢ`.

## Main results

* `Matrix.Realization.exists_sub_apply_eq_rootOf`: `λ - w λ ∈ Q₊` for `λ` dominant integral.
* `Matrix.Realization.apply_eq_self_of_dominant`: if `λ` and `w λ` are both dominant integral,
  then `w λ = λ`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Prop. 3.12.
-/

open Module CoxeterSystem

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)

/-- For a dominant integral weight `λ` (`⟨λ, αᵢ^∨⟩ ∈ ℤ₊` for all `i`) and `w ∈ W`, `λ - w λ` lies
in `Q₊` ([Kac] Prop. 3.12 (b) (check), for weights). -/
theorem exists_sub_apply_eq_rootOf {μ : Dual K H} (hμ : ∀ i, ∃ n : ℕ, μ (P.coroot i) = n)
    (w : P.weylGroup hA) :
    ∃ k : ι → ℤ, 0 ≤ k ∧ μ - (w : Dual K H ≃ₗ[K] Dual K H) μ = P.rootOf k := by
  classical
  set cs := P.coxeterSystem hA
  generalize hn : cs.length w = n
  induction n using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  by_cases hw1 : w = 1
  · exact ⟨0, le_rfl, by simp [hw1]⟩
  obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hw1
  have hlen : cs.length (w * cs.simple i) < n := hn ▸ hi
  obtain ⟨k, hk, hwk⟩ := ih _ hlen (w * cs.simple i) rfl
  have hnd : ¬cs.IsRightDescent (w * cs.simple i) i := by
    rwa [← isRightDescent_iff_not_isRightDescent_mul]
  obtain ⟨l, hl, hwl⟩ := (P.not_isRightDescent_coxeterSystem_iff hA).mp hnd
  obtain ⟨m, hm⟩ := hμ i
  refine ⟨k + (m : ℤ) • l, add_nonneg hk (smul_nonneg (Int.natCast_nonneg m) hl), ?_⟩
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at hwk hwl
  have hw : (w : Dual K H ≃ₗ[K] Dual K H) μ =
      (w : Dual K H ≃ₗ[K] Dual K H) (P.reflection hA i μ) -
        (m : K) • (w : Dual K H ≃ₗ[K] Dual K H) (P.reflection hA i (P.root i)) := by
    rw [reflection_apply P hA i μ, reflection_root_self, map_sub, map_smul, map_neg, hm]
    module
  rw [hw, map_add, map_zsmul, ← Int.cast_smul_eq_zsmul K, ← hwk, ← hwl]
  push_cast
  abel

/-- If `λ` and `w λ` are both dominant integral weights, then `w λ = λ` ([Kac] Prop. 3.12 (b)
(check), for weights): the `W`-orbit of a dominant integral weight contains no other dominant
integral weight. -/
theorem apply_eq_self_of_dominant {μ : Dual K H} (hμ : ∀ i, ∃ n : ℕ, μ (P.coroot i) = n)
    {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    (hwμ : ∀ i, ∃ n : ℕ, w μ (P.coroot i) = n) : w μ = μ := by
  classical
  obtain ⟨k, hk, hwk⟩ := P.exists_sub_apply_eq_rootOf hA hμ ⟨w, hw⟩
  obtain ⟨l, hl, hwl⟩ := P.exists_sub_apply_eq_rootOf hA hwμ ⟨w, hw⟩⁻¹
  simp only [Inv.inv] at hwl
  rw [show w.symm (w μ) = μ from w.symm_apply_apply μ] at hwl
  have h0 := P.eq_zero_of_mem_closure_of_neg_mem
    ((P.mem_closure_range_root_iff).mpr ⟨k, hk, hwk.symm⟩)
    ((P.mem_closure_range_root_iff).mpr ⟨l, hl, by rw [← hwl]; change _ = -(μ - w μ); abel⟩)
  exact (sub_eq_zero.mp h0).symm

end Matrix.Realization
