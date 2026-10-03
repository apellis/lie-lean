/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.IntegrableRoots
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroupCoxeter

/-!
# The length function of the Weyl group and positive roots

Let `A` be a generalized Cartan matrix, `K` a field of characteristic zero and `W` the Weyl group,
a Coxeter group with simple reflections the fundamental reflections `rᵢ`
(`Matrix.Realization.coxeterSystem`), with length function `ℓ`. We prove [Kac] Exercise 3.6:
`ℓ(w)` is the number of positive roots `α ∈ Δ₊` of `𝔤(A)` with `w α < 0`, and [Kac] Lemma 3.11 (a):
`ℓ(w rᵢ) < ℓ(w)` if and only if `w αᵢ < 0`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.inversionSet`: the set `Δ₊ ∩ w⁻¹ Δ₋` of positive roots
  made negative by `w`.

## Main results

* `Matrix.Realization.apply_root_mem_negWeights_iff`: `w αᵢ < 0 ↔ ℓ(w rᵢ) < ℓ(w)`
  ([Kac] Lemma 3.11 (a)).
* `Matrix.Realization.apply_root_mem_posWeights_iff`: `w αᵢ > 0 ↔ ℓ(w rᵢ) > ℓ(w)`.
* `Matrix.Realization.KacMoodyAlgebra.ncard_inversionSet`: `ℓ(w) = |Δ₊ ∩ w⁻¹ Δ₋|`, and this set
  is finite ([Kac] Exercise 3.6).

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Lemma 3.7, Lemma 3.11,
  Exercise 3.6.
-/

open Module

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)

omit [DecidableEq ι] in
lemma neg_mem_negWeights_iff {μ : Dual K H} : -μ ∈ P.negWeights ↔ μ ∈ P.posWeights := by
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, neg_injective h⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩

namespace KacMoodyAlgebra

/-- The inversion set `Δ₊ ∩ w⁻¹ Δ₋` of `w`: the positive roots `α` of `𝔤(A)` with `w α < 0`
(cf. [Kac] Exercise 3.6). -/
def inversionSet (w : Dual K H ≃ₗ[K] Dual K H) : Set (Dual K H) :=
  {μ | μ ∈ roots P ∧ μ ∈ P.posWeights ∧ w μ ∈ P.negWeights}

lemma inversionSet_one [CharZero K] : inversionSet P 1 = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, h1, h2⟩ ↦
    Set.disjoint_left.mp P.disjoint_posWeights_negWeights h1 h2

end KacMoodyAlgebra

variable [CharZero K]

/-- [Kac] Lemma 3.11 (a): `w αᵢ < 0` if and only if `ℓ(w rᵢ) < ℓ(w)`. -/
theorem apply_root_mem_negWeights_iff {w : P.weylGroup hA} {i : ι} :
    (w : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∈ P.negWeights ↔
      (P.coxeterSystem hA).IsRightDescent w i := by
  rw [isRightDescent_coxeterSystem_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk.1, h.symm⟩
  · rintro ⟨k, hk, h⟩
    refine ⟨k, ⟨hk, fun hk0 ↦ ?_⟩, h.symm⟩
    rw [hk0, map_zero, neg_zero, LinearEquiv.map_eq_zero_iff] at h
    exact P.linearIndependent_root.ne_zero i h

/-- [Kac] Lemma 3.11 (a): `w αᵢ > 0` if and only if `ℓ(w rᵢ) > ℓ(w)`. -/
theorem apply_root_mem_posWeights_iff {w : P.weylGroup hA} {i : ι} :
    (w : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∈ P.posWeights ↔
      ¬(P.coxeterSystem hA).IsRightDescent w i := by
  rw [not_isRightDescent_coxeterSystem_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk.1, h.symm⟩
  · rintro ⟨k, hk, h⟩
    refine ⟨k, ⟨hk, fun hk0 ↦ ?_⟩, h.symm⟩
    rw [hk0, map_zero, LinearEquiv.map_eq_zero_iff] at h
    exact P.linearIndependent_root.ne_zero i h

namespace KacMoodyAlgebra

lemma root_mem_inversionSet_iff {w : Dual K H ≃ₗ[K] Dual K H} {i : ι} :
    P.root i ∈ inversionSet P w ↔ w (P.root i) ∈ P.negWeights :=
  ⟨fun h ↦ h.2.2, fun h ↦ ⟨root_mem_roots P i, P.root_mem_posWeights i, h⟩⟩

lemma root_mem_inversionSet_mul_reflection_iff {w : Dual K H ≃ₗ[K] Dual K H} {i : ι} :
    P.root i ∈ inversionSet P (w * P.reflection hA i) ↔ w (P.root i) ∈ P.posWeights := by
  rw [root_mem_inversionSet_iff, LinearEquiv.mul_apply, reflection_root_self, map_neg,
    neg_mem_negWeights_iff]

/-- `rᵢ` maps `Δ₊ ∩ w⁻¹ Δ₋ \ {αᵢ}` onto `Δ₊ ∩ (w rᵢ)⁻¹ Δ₋ \ {αᵢ}`; this uses that `rᵢ` permutes
`Δ₊ \ {αᵢ}` ([Kac] Lemma 3.7). -/
lemma image_reflection_inversionSet_diff (w : Dual K H ≃ₗ[K] Dual K H) (i : ι) :
    P.reflection hA i '' (inversionSet P w \ {P.root i}) =
      inversionSet P (w * P.reflection hA i) \ {P.root i} := by
  have hr := P.reflection_mem_weylGroup hA i
  have hneg : ∀ μ ∈ P.posWeights, P.reflection hA i μ ≠ P.root i := by
    intro μ hμ h
    have : μ = -P.root i := by rw [← P.reflection_reflection hA i μ, h, reflection_root_self]
    rw [this] at hμ
    exact Set.disjoint_left.mp P.disjoint_posWeights_negWeights hμ
      ((neg_mem_negWeights_iff P).mpr (P.root_mem_posWeights i))
  ext μ
  constructor
  · rintro ⟨γ, ⟨⟨h1, h2, h3⟩, hγ⟩, rfl⟩
    refine ⟨⟨apply_mem_roots P hA hr h1, reflection_mem_posWeights P hA h1 h2 hγ, ?_⟩,
      hneg γ h2⟩
    rwa [LinearEquiv.mul_apply, reflection_reflection]
  · rintro ⟨⟨h1, h2, h3⟩, hμ⟩
    refine ⟨P.reflection hA i μ, ⟨⟨apply_mem_roots P hA hr h1,
      reflection_mem_posWeights P hA h1 h2 hμ, h3⟩, hneg μ h2⟩, reflection_reflection _ _ _ _⟩

/-- **[Kac] Exercise 3.6**: the length `ℓ(w)` of `w ∈ W` equals the number of positive
roots `α ∈ Δ₊` of `𝔤(A)` with `w α < 0`; in particular this set is finite. -/
theorem finite_inversionSet_and_ncard_eq (w : P.weylGroup hA) :
    (inversionSet P (w : Dual K H ≃ₗ[K] Dual K H)).Finite ∧
      (inversionSet P (w : Dual K H ≃ₗ[K] Dual K H)).ncard = (P.coxeterSystem hA).length w := by
  induction w using (P.coxeterSystem hA).simple_induction_right with
  | one => simp [inversionSet_one]
  | mul_simple_right w i ih =>
    obtain ⟨hfin, hcard⟩ := ih
    have himg := image_reflection_inversionSet_diff P hA (w : Dual K H ≃ₗ[K] Dual K H) i
    simp only [Subgroup.coe_mul, coxeterSystem_simple]
    by_cases hd : (P.coxeterSystem hA).IsRightDescent w i
    · have h1 : P.root i ∈ inversionSet P w :=
        (root_mem_inversionSet_iff P).mpr ((apply_root_mem_negWeights_iff P hA).mpr hd)
      have h2 : P.root i ∉ inversionSet P (w * P.reflection hA i) := by
        rw [root_mem_inversionSet_mul_reflection_iff, apply_root_mem_posWeights_iff]
        exact not_not.mpr hd
      rw [Set.sdiff_singleton_eq_self h2] at himg
      rw [← himg, Set.ncard_image_of_injective _ (P.reflection hA i).injective,
        Set.ncard_sdiff_singleton_of_mem h1, hcard]
      refine ⟨hfin.sdiff.image _, ?_⟩
      rw [(P.coxeterSystem hA).isRightDescent_iff] at hd
      omega
    · have h1 : P.root i ∉ inversionSet P w := by
        rw [root_mem_inversionSet_iff, apply_root_mem_negWeights_iff]
        exact hd
      have h2 : P.root i ∈ inversionSet P (w * P.reflection hA i) := by
        rw [root_mem_inversionSet_mul_reflection_iff, apply_root_mem_posWeights_iff]
        exact hd
      rw [Set.sdiff_singleton_eq_self h1] at himg
      rw [← Set.insert_sdiff_self_of_mem h2, ← himg, Set.ncard_insert_of_notMem
        (fun h ↦ (himg ▸ h).2 rfl) (hfin.image _),
        Set.ncard_image_of_injective _ (P.reflection hA i).injective, hcard]
      refine ⟨(hfin.image _).insert _, ?_⟩
      rw [(P.coxeterSystem hA).not_isRightDescent_iff] at hd
      omega

/-- **[Kac] Exercise 3.6**: `ℓ(w) = |Δ₊ ∩ w⁻¹ Δ₋|`. -/
theorem ncard_inversionSet (w : P.weylGroup hA) :
    (inversionSet P (w : Dual K H ≃ₗ[K] Dual K H)).ncard = (P.coxeterSystem hA).length w :=
  (finite_inversionSet_and_ncard_eq P hA w).2

/-- The inversion set `Δ₊ ∩ w⁻¹ Δ₋` of `w ∈ W` is finite (cf. [Kac] Exercise 3.6). -/
theorem finite_inversionSet (w : P.weylGroup hA) :
    (inversionSet P (w : Dual K H ≃ₗ[K] Dual K H)).Finite :=
  (finite_inversionSet_and_ncard_eq P hA w).1

end KacMoodyAlgebra

end Matrix.Realization
