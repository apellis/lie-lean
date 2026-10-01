/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.BraidFolding

/-!
# Kashiwara's Weyl group action on the path crystals `B(Λ)`

For a realization of a generalized Cartan matrix over `ℝ` and a dominant integral weight `Λ`,
Kashiwara's reflections `Sᵢ` (`Crystal.reflection`) of the path crystal `B(Λ)` satisfy the
Coxeter relations of the Weyl group (`Matrix.Realization.pathBraidRelations`: lengths `3`, `4`,
`6` by the `A₂` computation and by folding; lengths `1`, `2`, `∞` by
`Matrix.Realization.isLiftable_pathReflectionPerm`). Hence they extend to an action of the Weyl
group.

## Main definitions

* `Matrix.Realization.pathWeylAction`: the homomorphism `W →* Perm B(Λ)` with `sᵢ ↦ Sᵢ`, for
  every generalized Cartan matrix (no hypothesis on the rank-two subdiagrams).

## Main results

* `Matrix.Realization.pathWeylAction_simple`: `sᵢ ↦ Sᵢ`.
* `Matrix.Realization.coe_wt_pathWeylAction`: `wt (w • b) = w (wt b)`.
* `Matrix.Realization.pathWeylAction_top`: `w • π_Λ = π_{wΛ}`.

## References

* [Kas94] M. Kashiwara, *Crystal bases of modified quantized enveloping algebra*, Duke Math. J.
  **73** (1994), 383–413, §7.
* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. (2)
  **142** (1995), 499–525, §8.
-/

open Set Module LittelmannPath

namespace Matrix.Realization

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} (hA : A.IsGeneralizedCartan) {Λ : Dual ℝ H}

variable (P) in
/-- **Kashiwara's action of the Weyl group on `B(Λ)`** ([Kas94] §7, [Lit95] §8
Thm. 8.1): for every generalized Cartan matrix, Kashiwara's reflections `Sᵢ` extend to a
homomorphism `W →* Perm B(Λ)` with `sᵢ ↦ Sᵢ` (they satisfy the braid relations,
`pathBraidRelations`). -/
noncomputable def pathWeylAction (hΛ : P.IsDominantIntegral Λ) :
    P.weylGroup hA →*
      Equiv.Perm (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component :=
  (isSeminormal_pathCrystal hA hΛ).weylAction (P.coxeterSystem hA)
    (isLiftable_pathReflectionPerm hA hΛ (pathBraidRelations hA hΛ))

theorem pathWeylAction_simple (hΛ : P.IsDominantIntegral Λ) (i : ι) :
    P.pathWeylAction hA hΛ ((P.coxeterSystem hA).simple i) = pathReflectionPerm P hA hΛ i :=
  Crystal.IsSeminormal.weylAction_simple _ _ _ i

/-- The action is compatible with weights: `wt (w • b) = w (wt b)`. -/
theorem coe_wt_pathWeylAction (hΛ : P.IsDominantIntegral Λ) (w : P.weylGroup hA)
    (b : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    ((P.pathWeylAction hA hΛ w b : LittelmannPath (P.pathSpace hA)).wt : Dual ℝ H) =
      (w : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) (b.1.wt : Dual ℝ H) := by
  refine (P.coxeterSystem hA).simple_induction_left
    (p := fun w => ∀ b, ((P.pathWeylAction hA hΛ w b : LittelmannPath (P.pathSpace hA)).wt :
      Dual ℝ H) = (w : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) (b.1.wt : Dual ℝ H)) w ?_ ?_ b
  · intro b
    simp
  · intro w i ih b
    rw [map_mul, Equiv.Perm.mul_apply, pathWeylAction_simple,
      Crystal.IsSeminormal.reflectionPerm_apply]
    have hw := (isSeminormal_pathCrystal hA hΛ).wt_reflection i (P.pathWeylAction hA hΛ w b)
    change ((P.pathCrystal hA hΛ).wt _ : Dual ℝ H) = _
    rw [hw, coe_reflection_cartanDatum]
    change P.reflection hA i (((P.pathWeylAction hA hΛ w b :
      LittelmannPath (P.pathSpace hA)).wt : Dual ℝ H)) = _
    rw [ih, Subgroup.coe_mul, coxeterSystem_simple, LinearEquiv.mul_apply]

/-- The action on the extremal paths: `w • π_Λ = π_{wΛ}`. -/
theorem pathWeylAction_top (hΛ : P.IsDominantIntegral Λ) (w : P.weylGroup hA) :
    ∃ hw : (w : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) Λ ∈ P.integralWeights,
      (P.pathWeylAction hA hΛ w ⟨_, mem_component_self _⟩ :
        LittelmannPath (P.pathSpace hA)) = straightLine (P.pathSpace hA) ⟨_, hw⟩ := by
  refine (P.coxeterSystem hA).simple_induction_left
    (p := fun w => ∃ hw : (w : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) Λ ∈ P.integralWeights,
      (P.pathWeylAction hA hΛ w ⟨_, mem_component_self _⟩ :
        LittelmannPath (P.pathSpace hA)) = straightLine (P.pathSpace hA) ⟨_, hw⟩) w ?_ ?_
  · exact ⟨hΛ.mem_integralWeights, by simp⟩
  · rintro w i ⟨hw, heq⟩
    set x := (P.cartanDatum hA).reflection i ⟨_, hw⟩ with hx
    have hxc : (x : Dual ℝ H) =
        (((P.coxeterSystem hA).simple i * w : P.weylGroup hA) : Dual ℝ H ≃ₗ[ℝ] Dual ℝ H) Λ := by
      rw [hx, coe_reflection_cartanDatum, Subgroup.coe_mul, coxeterSystem_simple,
        LinearEquiv.mul_apply]
    refine ⟨hxc ▸ x.2, ?_⟩
    rw [map_mul, Equiv.Perm.mul_apply, pathWeylAction_simple,
      Crystal.IsSeminormal.reflectionPerm_apply, coe_reflection_pathCrystal, heq,
      reflection_straightLine]
    exact congrArg _ (Subtype.ext hxc)

end Matrix.Realization
