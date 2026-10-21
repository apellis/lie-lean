/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.Matrix.Cartan.AffineWeylGroup

/-!
# Root lemmas for the induction in Shapovalov's theorem

The existence part of Shapovalov's theorem ([HumO] Thm. 4.12) is proved by induction on the height
of the positive root `γ`. For the induction step ([HumO] §4.13) one needs:

* `Matrix.Realization.exists_simple_descent`: for `A` of finite type and a positive root
  `γ = ∑ kₗ αₗ` of height `> 1`, there is a simple root `αⱼ` with `kⱼ > 0`, `⟨γ, αⱼ^∨⟩ > 0` and
  `sⱼ γ` positive;
* `Matrix.Realization.not_isPosRoot_of_forall_coroot_eq`: if `⟨x, αⱼ^∨⟩ = t ⟨x, γ^∨⟩` for all `x`,
  then `sⱼ γ` is negative. So in the induction step the two linear forms `⟨-, γ^∨⟩` and
  `⟨-, αⱼ^∨⟩` are not proportional, which is what the density argument of [HumO] §4.13 needs.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §4.13.
-/

open Module

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}

lemma simple_mul_apply_root (hA : A.IsGeneralizedCartan) (j : ι) (v : P.weylGroup hA) (i : ι) :
    (((P.coxeterSystem hA).simple j * v : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H)
        (P.root i) = P.reflection hA j ((v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) := by
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, coxeterSystem_simple]

/-- **Descent to a lower root** ([HumO] §4.13): for `A` of finite type and a positive root
`γ = v αᵢ = ∑ kₗ αₗ` of height `> 1`, there is `j` with `kⱼ > 0`, `⟨γ, αⱼ^∨⟩ > 0` and
`sⱼ γ = γ - ⟨γ, αⱼ^∨⟩ αⱼ` positive. -/
theorem exists_simple_descent (hfin : A.IsFiniteCartan) {v : P.weylGroup hfin.isGeneralizedCartan}
    {i : ι} {k : ι → ℤ} (hk : 0 ≤ k)
    (hvk : (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) = P.rootOf k) (hht : 1 < ∑ l, k l) :
    ∃ j, 0 < k j ∧ 0 < (A *ᵥ k) j ∧
      P.IsPosRoot hfin.isGeneralizedCartan
        ((P.coxeterSystem hfin.isGeneralizedCartan).simple j * v) i := by
  set hA := hfin.isGeneralizedCartan
  obtain ⟨d, hd, hpd⟩ := hfin.exists_posDef
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hht
  have hpos := hpd.dotProduct_mulVec_pos hk0
  rw [star_trivial, ← mulVec_mulVec] at hpos
  simp only [dotProduct, mulVec_diagonal] at hpos
  obtain ⟨j, hj⟩ : ∃ j, 0 < k j * (d j * (A *ᵥ k) j) := by
    by_contra! h
    exact hpos.not_ge (Finset.sum_nonpos fun j _ ↦ h j)
  have h1 : 0 < d j * (A *ᵥ k) j := pos_of_mul_pos_right hj (hk j)
  have h2 : 0 < (A *ᵥ k) j := pos_of_mul_pos_right h1 (hd j).le
  have h3 : 0 < k j := pos_of_mul_pos_left hj h1.le
  refine ⟨j, h3, h2, ?_⟩
  rcases P.isPosRoot_or ((P.coxeterSystem hA).simple j * v) i with h | h
  · exact h
  exfalso
  obtain ⟨k', hk', hk'eq⟩ := h
  rw [mul_simple_apply_root, simple_mul_apply_root, hvk, reflection_rootOf,
    ← map_neg P.rootOf] at hk'eq
  have hinj := P.rootOf_injective hk'eq
  have hkl : ∀ l, l ≠ j → k l = 0 := by
    intro l hl
    have h4 := congrFun hinj l
    simp [Pi.single_apply, hl] at h4
    have h5 : (0 : ℤ) ≤ k' l := hk' l
    have h6 : (0 : ℤ) ≤ k l := hk l
    omega
  have hγ : P.rootOf k = (k j : K) • P.root j := by
    rw [rootOf_apply, Finset.sum_eq_single j
      (fun l _ hl ↦ by rw [hkl l hl, Int.cast_zero, zero_smul]) (by simp)]
  obtain ⟨m, hm⟩ := P.mem_rootLattice.mp (P.apply_mem_rootLattice hA (v⁻¹).2
    (P.mem_rootLattice.mpr ⟨Pi.single j 1, P.rootOf_single j⟩))
  have hαi : P.rootOf (Pi.single i 1) = P.rootOf (k j • m) := by
    rw [rootOf_single, map_zsmul, hm, ← Int.cast_smul_eq_zsmul K, ← map_smul, ← hγ, ← hvk]
    exact (inv_apply_apply v (P.root i)).symm
  have h7 := congrFun (P.rootOf_injective hαi) i
  simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul] at h7
  have hkj : k j = 1 := Int.eq_one_of_mul_eq_one_right h3.le h7.symm
  have hsum : ∑ l, k l = 1 := by
    rw [Finset.sum_eq_single j (fun l _ hl ↦ hkl l hl) (by simp), hkj]
  omega

/-- **Non-proportional coroots** ([HumO] §4.13): for `A` of finite type, a positive root
`γ = v αᵢ` and `j`, if `⟨x, αⱼ^∨⟩ = t ⟨x, γ^∨⟩` for all `x`, then `sⱼ γ` is negative. (Then
`γ` is a multiple of `αⱼ`, so `sⱼ γ = -γ`.) -/
theorem not_isPosRoot_of_forall_coroot_eq [FiniteDimensional K H] (hfin : A.IsFiniteCartan)
    {v : P.weylGroup hfin.isGeneralizedCartan} {i j : ι}
    (hv : P.IsPosRoot hfin.isGeneralizedCartan v i) (t : K)
    (ht : ∀ x : Dual K H, x (P.coroot j) = t * P.corootPairing hfin.isGeneralizedCartan x v i) :
    ¬ P.IsPosRoot hfin.isGeneralizedCartan
      ((P.coxeterSystem hfin.isGeneralizedCartan).simple j * v) i := by
  set hA := hfin.isGeneralizedCartan
  intro hsv
  obtain ⟨S⟩ := isSymmetrizable_iff_nonempty_symmetrization.mp hfin.isSymmetrizable
  set γ := (v : Dual K H ≃ₗ[K] Dual K H) (P.root i)
  have hform : ∀ x, P.dualBilinForm S x γ = P.corootPairing hA x v i / S.ε i := by
    intro x
    rw [← P.dualBilinForm_weylGroup hA S (v⁻¹).2, inv_apply_apply, dualBilinForm_root_right]
    rfl
  have hεi : (S.ε i : K) ≠ 0 := by exact_mod_cast S.ε_ne_zero i
  have hεj : (S.ε j : K) ≠ 0 := by exact_mod_cast S.ε_ne_zero j
  have hzero : ∀ x, P.dualBilinForm S x ((S.ε j : K) • P.root j - (t * S.ε i) • γ) = 0 := by
    intro x
    rw [map_sub, map_smul, map_smul, dualBilinForm_root_right, hform, ht, smul_eq_mul,
      smul_eq_mul]
    field_simp
    ring
  have hrel : (S.ε j : K) • P.root j = (t * S.ε i) • γ := by
    rw [← sub_eq_zero]
    have h0 : (P.toDual S).symm ((S.ε j : K) • P.root j - (t * S.ε i) • γ) = 0 :=
      (Module.forall_dual_apply_eq_zero_iff K _).mp fun x ↦
        (P.dualBilinForm_apply_eq S x _).symm.trans (hzero x)
    simpa using h0
  have ht0 : t * S.ε i ≠ 0 := by
    intro h0
    rw [h0, zero_smul, smul_eq_zero] at hrel
    exact P.linearIndependent_root.ne_zero j (hrel.resolve_left hεj)
  have hγ : γ = ((t * S.ε i)⁻¹ * S.ε j) • P.root j := by
    rw [mul_smul, hrel, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  have hs : (((P.coxeterSystem hA).simple j * v : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H)
      (P.root i) = -γ := by
    rw [simple_mul_apply_root, hγ, map_smul, reflection_apply, P.root_coroot_self hA]
    module
  obtain ⟨k, hk, hk'⟩ := hsv
  exact not_isPosRoot_and hv ⟨k, hk, by rw [mul_simple_apply_root, ← hk', hs]⟩

end Matrix.Realization
