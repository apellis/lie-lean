/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CompositionSeries.Casimir
import LieLean.Algebra.Lie.KacMoody.Shapovalov
import LieLean.Algebra.Lie.KacMoody.VermaHom

/-!
# The Kac–Kazhdan criterion: the necessary condition and the simple roots

Let `𝔤 = 𝔤(A)` be the Kac–Moody algebra of a realization of `A` over a field `K` of characteristic
zero, `M(Λ)` the Verma module of highest weight `Λ ∈ 𝔥*` and `M'(Λ)` its maximal proper submodule,
the radical of the Shapovalov form (`VermaModule.mem_maxSubmodule_iff`). For `η ∈ Q₊` the
Shapovalov form is degenerate on `M(Λ)_{Λ - η}` iff `M'(Λ)_{Λ - η} ≠ 0`
(`VermaModule.nondegenerate_weightSpaceForm_iff`).

The **Kac–Kazhdan criterion** ([KK] Thm. 1 and Thm. 2 (check); [Kac] §9 (check)) states, for
symmetrizable `A`, that `M'(Λ)_{Λ - η} ≠ 0` iff there are a positive root `α` and an integer
`n ≥ 1` with `n α ≤ η` and `2 (Λ + ρ | α) = n (α | α)`; it follows from the Kac–Kazhdan
determinant formula. This file proves the two parts of it that do not need the determinant:

* **A necessary condition** (via the Casimir operator, [Kac] Prop. 9.8 (check)): if
  `M'(Λ)_{Λ - η} ≠ 0`, then there is `β ∈ Q₊ \ {0}` with `β ≤ η` and `2 (Λ + ρ | β) = (β | β)`,
  and in fact an embedding `M(Λ - β) ↪ M'(Λ)`. The criterion sharpens this to `β = n α`.
* **Sufficiency for simple roots**: if `2 (Λ + ρ | αᵢ) = n (αᵢ | αᵢ)`, i.e. `⟨Λ + ρ, αᵢ^∨⟩ = n`,
  for a positive integer `n` with `n αᵢ ≤ η`, then `M'(Λ)_{Λ - η} ≠ 0`, via the embedding
  `M(Λ - n αᵢ) ↪ M(Λ)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_primitiveVectors_of_inf_ne_bot`: if
  `M'(Λ)_{Λ - η} ≠ 0`, then `M'(Λ)` has a nonzero primitive vector of weight `Λ - β` with
  `0 < β ≤ η`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.mem_maxSubmodule_of_mem_primitiveVectors`: a
  primitive vector of weight `≠ Λ` lies in `M'(Λ)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.two_mul_dualBilinForm_eq_of_mem_primitiveVectors`:
  a nonzero primitive vector of weight `Λ - β` forces `2 (Λ + ρ | β) = (β | β)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_of_maxSubmodule_inf_weightSpace_ne_bot`,
  `Matrix.Realization.KacMoodyAlgebra.VermaModule.det_toMatrix_weightSpaceForm_ne_zero_of_forall`:
  the necessary condition, and the resulting sufficient condition for the nondegeneracy of the
  Shapovalov form on `M(Λ)_{Λ - η}`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.inf_weightSpace_ne_bot_of_coroot`,
  `Matrix.Realization.KacMoodyAlgebra.VermaModule.inf_weightSpace_ne_bot_of_two_mul_dualBilinForm`,
  `VermaModule.det_toMatrix_weightSpaceForm_eq_zero_of_two_mul_dualBilinForm`:
  the "if" direction of the criterion for `α` a simple root.

## Proof

For the necessary condition, choose `β ∈ Q₊` of minimal height with `β ≤ η` and
`M'(Λ)_{Λ - β} ≠ 0`. A nonzero `v ∈ M'(Λ)_{Λ - β}` is primitive: `eᵢ v ∈ M'(Λ)_{Λ - β + αᵢ}`, which
is zero by minimality. The Casimir operator acts on `M(Λ)` by `(Λ + 2ρ | Λ)` and on `U(𝔤) v`, a
quotient of `M(Λ - β)`, by `(Λ - β + 2ρ | Λ - β)` ([Kac] Cor. 2.6 (check)), which gives
`2 (Λ + ρ | β) = (β | β)`. For simple roots, `fᵢⁿ v_Λ` is a primitive vector and `U(𝔫₋)` is a
domain. These are the standard arguments (cf. [KK] §3 (check), [HumO] §4.2 (check)), written out
by us.

## References

* [KK] V. G. Kac, D. A. Kazhdan, *Structure of representations with highest weight of
  infinite-dimensional Lie algebras*, Adv. Math. 34 (1979), 97–108.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.4–9.8 (check).
* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, §4.2 (check).
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

namespace VermaModule

/-- `fⱼ` acts injectively on `M(Λ)`, since `U(𝔫₋)` is a domain. -/
theorem toEnd_f_injective (Λ : Dual K H) (j : ι) :
    Function.Injective (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P j)) := by
  have hf : UniversalEnvelopingAlgebra.ι K (⟨f P j, f_mem_nNeg P j⟩ : nNeg P) ≠ 0 := fun h0 ↦
    f_ne_zero P j (congrArg Subtype.val
      (UniversalEnvelopingAlgebra.ι_injective (R := K) (L := nNeg P)
        (h0.trans (map_zero _).symm)))
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨u, rfl⟩ := (equivEnvNNeg P Λ).surjective m
  have : toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P j) (equivEnvNNeg P Λ u) =
      equivEnvNNeg P Λ (UniversalEnvelopingAlgebra.ι K ⟨f P j, f_mem_nNeg P j⟩ * u) := by
    rw [equivEnvNNeg_mul, UniversalEnvelopingAlgebra.map_ι, toEnd_apply_apply, lie_eq_smul]
    rfl
  rw [this, LinearEquiv.map_eq_zero_iff] at hm
  rw [(mul_eq_zero.mp hm).resolve_left hf, map_zero]

/-- `M(Λ)_{Λ - γ} = 0` unless `γ ∈ Q₊`. -/
theorem weightSpace_sub_rootOf_eq_bot (Λ : Dual K H) {γ : ι → ℤ} (hγ : ¬ 0 ≤ γ) :
    weightSpace P Λ (Λ - P.rootOf γ) = ⊥ :=
  weightSpace_eq_bot P Λ fun _ hk h ↦ hγ (P.rootOf_injective (sub_right_injective h) ▸ hk)

/-- `M(Λ)_{Λ - γ} ≠ 0` for `γ ∈ Q₊`. -/
theorem weightSpace_sub_rootOf_ne_bot (Λ : Dual K H) {γ : ι → ℤ} (hγ : 0 ≤ γ) :
    weightSpace P Λ (Λ - P.rootOf γ) ≠ ⊥ := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, height γ = n := ⟨(height γ).toNat,
    (Int.toNat_of_nonneg (show 0 ≤ height γ from Finset.sum_nonneg fun i _ ↦ hγ i)).symm⟩
  induction n generalizing γ with
  | zero =>
    have : γ = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hγ i).mp (by simpa [height] using hn)
      exact funext fun i ↦ this i (Finset.mem_univ i)
    subst this
    rw [map_zero, sub_zero]
    exact fun h ↦ hwv_ne_zero P Λ ((Submodule.eq_bot_iff _).mp h _ (hwv_mem_weightSpace P Λ))
  | succ n ih =>
    obtain ⟨j, hj⟩ : ∃ j, 0 < γ j := by
      by_contra! h
      have : height γ = 0 := Finset.sum_eq_zero fun i _ ↦ le_antisymm (h i) (hγ i)
      omega
    set γ' := γ - Pi.single j 1
    have hγ' : 0 ≤ γ' := fun i ↦ by
      by_cases hij : i = j
      · subst hij; simp only [γ', Pi.sub_apply, Pi.single_eq_same, Pi.zero_apply]; omega
      · simpa [γ', hij] using hγ i
    have hn' : height γ' = n := by
      have : height γ' = height γ - 1 := by
        simp [height, γ', Finset.sum_sub_distrib]
      omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (ih hγ' hn')
    refine fun hbot ↦ hv0 (toEnd_f_injective P Λ j ?_)
    rw [map_zero, ← Submodule.mem_bot K, ← hbot]
    have := lie_mem_weightSpaceOfMap (h P) (f_mem_rootSpace P j) hv
    convert this using 2
    · simp only [γ', map_sub, rootOf_single]
      abel
    · rfl


/-- If `M'(Λ)` has a nonzero vector of weight `Λ - η`, then it contains a nonzero primitive vector
of weight `Λ - β` for some `β ∈ Q₊ \ {0}` with `β ≤ η` (take `β` minimal). -/
theorem exists_primitiveVectors_of_inf_ne_bot {Λ : Dual K H} {η : ι → ℤ}
    (hη : (maxSubmodule P Λ).toSubmodule ⊓ weightSpace P Λ (Λ - P.rootOf η) ≠ ⊥) :
    ∃ β : ι → ℤ, 0 ≤ β ∧ β ≠ 0 ∧ β ≤ η ∧
      ∃ v ∈ primitiveVectors P (VermaModule P Λ) (Λ - P.rootOf β), v ≠ 0 ∧
        v ∈ maxSubmodule P Λ := by
  classical
  set Q : (ι → ℤ) → Prop := fun β ↦ 0 ≤ β ∧ β ≤ η ∧
    (maxSubmodule P Λ).toSubmodule ⊓ weightSpace P Λ (Λ - P.rootOf β) ≠ ⊥
  have hη0 : 0 ≤ η := by
    by_contra h
    exact hη (by rw [weightSpace_sub_rootOf_eq_bot P Λ h, inf_bot_eq])
  obtain ⟨β, ⟨hβ0, hβη, hβ⟩, hmin⟩ :=
    exists_minimalFor_of_wellFoundedLT Q (fun β ↦ (height β).toNat) ⟨η, hη0, le_rfl, hη⟩
  obtain ⟨v, ⟨hvM, hv⟩, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hβ
  have hβne : β ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero, inf_weightSpace_self_eq_bot P Λ (hwv_notMem_maxSubmodule P Λ)] at hβ
    exact hβ rfl
  refine ⟨β, hβ0, hβne, hβη, v, mem_primitiveVectors.mpr ⟨hv, fun i ↦ ?_⟩, hv0, hvM⟩
  set β' := β - Pi.single i 1
  have hw : ⁅e P i, v⁆ ∈ weightSpace P Λ (Λ - P.rootOf β') := by
    have he : e P i ∈ rootSpace P (P.root i) := fun a ↦ lie_h_e P a i
    have := lie_mem_weightSpaceOfMap (h P) he hv
    convert this using 2
    simp only [β', map_sub, rootOf_single]
    abel
  have hwM : ⁅e P i, v⁆ ∈ maxSubmodule P Λ := (maxSubmodule P Λ).lie_mem hvM
  by_cases hβ' : 0 ≤ β'
  · by_contra hne
    have hle : β' ≤ β := sub_le_self β (Pi.single_nonneg.mpr zero_le_one)
    have hQ : Q β' := ⟨hβ', hle.trans hβη, fun hbot ↦ hne (by
      rw [← Submodule.mem_bot K, ← hbot]; exact ⟨hwM, hw⟩)⟩
    have hh : height β' = height β - 1 := by simp [β', height, Finset.sum_sub_distrib]
    have := hmin hQ (by simp only; omega)
    simp only at this
    have : 0 ≤ height β' := Finset.sum_nonneg fun j _ ↦ hβ' j
    omega
  · rw [weightSpace_sub_rootOf_eq_bot P Λ hβ'] at hw
    exact (Submodule.mem_bot K).mp hw

omit [CharZero K] in
/-- The image of a morphism `M(μ) → M(Λ)` lies in `M'(Λ)` if the image of `v_μ` does. -/
lemma map_mem_maxSubmodule {Λ μ : Dual K H}
    (φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ)
    (hφ : φ (hwv P μ) ∈ maxSubmodule P Λ) (m : VermaModule P μ) : φ m ∈ maxSubmodule P Λ := by
  obtain ⟨u, rfl⟩ := mk_surjective P μ m
  rw [mk_eq_smul, map_smul_eq_smul]
  exact smul_mem P Λ _ u hφ

/-- The morphism `M(μ) → M(Λ)` attached to a nonzero primitive vector is injective. -/
lemma injective_homEquiv_symm {Λ μ : Dual K H} {v : VermaModule P Λ}
    (hv : v ∈ primitiveVectors P (VermaModule P Λ) μ) (hv0 : v ≠ 0) :
    Function.Injective ((homEquiv P (VermaModule P Λ) μ).symm ⟨v, hv⟩) := by
  refine injective_of_ne_zero P fun h ↦ hv0 ?_
  have := congrArg Subtype.val ((homEquiv P (VermaModule P Λ) μ).apply_symm_apply ⟨v, hv⟩)
  rw [homEquiv_apply, h, _root_.zero_apply] at this
  exact this.symm

/-- If `M'(Λ)` has a nonzero vector of weight `Λ - η`, then for some `β ∈ Q₊ \ {0}` with
`β ≤ η` there is an embedding `M(Λ - β) ↪ M(Λ)` with image in `M'(Λ)`. -/
theorem exists_injective_of_inf_ne_bot {Λ : Dual K H} {η : ι → ℤ}
    (hη : (maxSubmodule P Λ).toSubmodule ⊓ weightSpace P Λ (Λ - P.rootOf η) ≠ ⊥) :
    ∃ β : ι → ℤ, 0 ≤ β ∧ β ≠ 0 ∧ β ≤ η ∧
      ∃ φ : VermaModule P (Λ - P.rootOf β) →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ,
        Function.Injective φ ∧ ∀ m, φ m ∈ maxSubmodule P Λ := by
  obtain ⟨β, hβ0, hβne, hβη, v, hv, hv0, hvM⟩ := exists_primitiveVectors_of_inf_ne_bot P hη
  refine ⟨β, hβ0, hβne, hβη, _, injective_homEquiv_symm P hv hv0,
    map_mem_maxSubmodule P _ ?_⟩
  rw [← homEquiv_apply, LinearEquiv.apply_symm_apply]
  exact hvM

/-- A primitive vector of `M(Λ)` of weight `μ ≠ Λ` lies in `M'(Λ)`: it is orthogonal to `M(Λ)`
for the Shapovalov form. -/
theorem mem_maxSubmodule_of_mem_primitiveVectors {Λ μ : Dual K H} (hμ : μ ≠ Λ)
    {v : VermaModule P Λ} (hv : v ∈ primitiveVectors P (VermaModule P Λ) μ) :
    v ∈ maxSubmodule P Λ := by
  obtain ⟨hvw, he⟩ := mem_primitiveVectors.mp hv
  have h := eq_smul_hwCoord P Λ (contravariantForm P Λ v) fun i m ↦ by
    rw [contravariantForm_lie_right, transpose_f, he, map_zero, LinearMap.zero_apply]
  rw [contravariantForm_eq_zero_of_ne P Λ hvw (hwv_mem_weightSpace P Λ) hμ, zero_smul] at h
  exact (mem_maxSubmodule_iff P Λ v).mpr fun w ↦ by rw [h, LinearMap.zero_apply]

/-! ### The necessary condition via the Casimir operator -/

section Casimir

variable [FiniteDimensional K H] (S : A.Symmetrization)

omit [DecidableEq ι] in
/-- `(Λ + 2ρ | Λ) = (Λ - β + 2ρ | Λ - β)` iff `2 (Λ + ρ | β) = (β | β)`. -/
lemma dualBilinForm_add_two_rho_eq_iff (Λ b : Dual K H) :
    P.dualBilinForm S (Λ + 2 • P.rho) Λ = P.dualBilinForm S (Λ - b + 2 • P.rho) (Λ - b) ↔
      2 * P.dualBilinForm S (Λ + P.rho) b = P.dualBilinForm S b b := by
  have hs := (P.isSymm_dualBilinForm S).eq b Λ
  simp only [two_nsmul, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at hs ⊢
  constructor <;> intro h
  · linear_combination h - hs
  · linear_combination h + hs

variable (hA : A.IsGeneralizedCartan)
include hA

/-- **The Casimir condition for primitive vectors** ([Kac] Prop. 9.8 (check), [KK]): if `M(Λ)` has
a nonzero primitive vector of weight `Λ - β`, then `2 (Λ + ρ | β) = (β | β)`. -/
theorem two_mul_dualBilinForm_eq_of_mem_primitiveVectors {Λ : Dual K H} {β : ι → ℤ}
    {v : VermaModule P Λ} (hv : v ∈ primitiveVectors P (VermaModule P Λ) (Λ - P.rootOf β))
    (hv0 : v ≠ 0) :
    2 * P.dualBilinForm S (Λ + P.rho) (P.rootOf β) =
      P.dualBilinForm S (P.rootOf β) (P.rootOf β) := by
  obtain ⟨hvw, he⟩ := mem_primitiveVectors.mp hv
  have := ((isStandardForm_invForm P S).mem_cone_and_eq_of_lie_e_eq_zero hA LieModuleHom.id
    Function.surjective_id hvw hv0 he).2
  exact (dualBilinForm_add_two_rho_eq_iff P S Λ _).mp this

/-- **Kac–Kazhdan: a necessary condition for degeneracy** ([KK] (check); via [Kac] Prop. 9.8
(check)). Let `A` be a symmetrizable generalized Cartan matrix. If the maximal submodule `M'(Λ)`
of `M(Λ)` has a nonzero vector of weight `Λ - η` (equivalently, the Shapovalov form is degenerate
on `M(Λ)_{Λ - η}`), then there is `β ∈ Q₊ \ {0}` with `β ≤ η` and `2 (Λ + ρ | β) = (β | β)`, and an
embedding `M(Λ - β) ↪ M(Λ)` with image in `M'(Λ)`.

The Kac–Kazhdan criterion sharpens `2 (Λ + ρ | β) = (β | β)` to: `2 (Λ + ρ | α) = n (α | α)` for
some positive root `α` and `n ≥ 1` with `n α ≤ η`. -/
theorem exists_of_maxSubmodule_inf_weightSpace_ne_bot {Λ : Dual K H} {η : ι → ℤ}
    (hη : (maxSubmodule P Λ).toSubmodule ⊓ weightSpace P Λ (Λ - P.rootOf η) ≠ ⊥) :
    ∃ β : ι → ℤ, 0 ≤ β ∧ β ≠ 0 ∧ β ≤ η ∧
      2 * P.dualBilinForm S (Λ + P.rho) (P.rootOf β) =
        P.dualBilinForm S (P.rootOf β) (P.rootOf β) ∧
      ∃ φ : VermaModule P (Λ - P.rootOf β) →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ,
        Function.Injective φ ∧ ∀ m, φ m ∈ maxSubmodule P Λ := by
  obtain ⟨β, hβ0, hβne, hβη, v, hv, hv0, hvM⟩ := exists_primitiveVectors_of_inf_ne_bot P hη
  refine ⟨β, hβ0, hβne, hβη, two_mul_dualBilinForm_eq_of_mem_primitiveVectors P S hA hv hv0, _,
    injective_homEquiv_symm P hv hv0, map_mem_maxSubmodule P _ ?_⟩
  rw [← homEquiv_apply, LinearEquiv.apply_symm_apply]
  exact hvM

/-- **Kac–Kazhdan: a sufficient condition for nondegeneracy of the Shapovalov form**
([KK] (check)). Let `A` be a symmetrizable generalized Cartan matrix. If `2 (Λ + ρ | β) ≠ (β | β)`
for all `β ∈ Q₊ \ {0}` with `β ≤ η`, then the Shapovalov form on `M(Λ)_{Λ - η}` is nondegenerate:
its determinant with respect to any basis is nonzero. -/
theorem det_toMatrix_weightSpaceForm_ne_zero_of_forall {Λ : Dual K H} {η : ι → ℤ}
    {n : Type*} [Fintype n] [DecidableEq n] (b : Basis n K (weightSpace P Λ (Λ - P.rootOf η)))
    (h : ∀ β : ι → ℤ, 0 ≤ β → β ≠ 0 → β ≤ η →
      2 * P.dualBilinForm S (Λ + P.rho) (P.rootOf β) ≠
        P.dualBilinForm S (P.rootOf β) (P.rootOf β)) :
    (LinearMap.BilinForm.toMatrix b (weightSpaceForm P Λ _)).det ≠ 0 := by
  rw [det_toMatrix_weightSpaceForm_ne_zero_iff]
  by_contra hη
  obtain ⟨β, hβ0, hβne, hβη, hβ, -⟩ := exists_of_maxSubmodule_inf_weightSpace_ne_bot P S hA hη
  exact h β hβ0 hβne hβη hβ

end Casimir

/-! ### The sufficient condition for simple roots -/

section Simple

variable (hA : A.IsGeneralizedCartan)
include hA

/-- **Degeneracy along the hyperplanes of the simple roots** ([KK] (check); [HumO] §4.2
(check)): if `⟨Λ + ρ, αᵢ^∨⟩ = n` is a positive integer and `n αᵢ ≤ η`, then `M'(Λ)` has a nonzero
vector of weight `Λ - η`. Indeed `M(Λ - n αᵢ) ↪ M'(Λ)` (`exists_injective_reflection`), and
`M(Λ - n αᵢ)_{Λ - η} ≠ 0`. -/
theorem inf_weightSpace_ne_bot_of_coroot {Λ : Dual K H} {η : ι → ℤ} {i : ι} {n : ℕ}
    (hn0 : 0 < n) (hn : (Λ + P.rho) (P.coroot i) = n) (hη : n • Pi.single i 1 ≤ η) :
    (maxSubmodule P Λ).toSubmodule ⊓ weightSpace P Λ (Λ - P.rootOf η) ≠ ⊥ := by
  obtain ⟨φ, hφ, hφv⟩ := exists_injective_reflection P hA hn0 hn
  have hμ : P.reflection hA i (Λ + P.rho) - P.rho = Λ - P.rootOf (n • Pi.single i 1) := by
    rw [P.reflection_add_rho_sub_rho hA hn, map_nsmul, rootOf_single]
  have hne : (n • Pi.single i 1 : ι → ℤ) ≠ 0 := fun h ↦ by
    have := congrFun h i
    simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, Pi.zero_apply] at this
    omega
  have hprim := toEnd_f_pow_hwv_mem_primitiveVectors P hA hn0 hn
  have hM : ∀ m, φ m ∈ maxSubmodule P Λ := map_mem_maxSubmodule P φ (hφv ▸
    mem_maxSubmodule_of_mem_primitiveVectors P
      (fun h ↦ P.rootOf_ne_zero hne (sub_eq_self.mp (hμ ▸ h))) hprim)
  set γ := η - n • Pi.single i 1
  have hγ : 0 ≤ γ := sub_nonneg.mpr hη
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (weightSpace_sub_rootOf_ne_bot P (P.reflection hA i (Λ + P.rho) - P.rho) hγ)
  intro hbot
  refine hw0 (hφ ?_)
  rw [map_zero, ← Submodule.mem_bot K, ← hbot]
  refine ⟨hM w, ?_⟩
  have hwt : Λ - P.rootOf η = (P.reflection hA i (Λ + P.rho) - P.rho) - P.rootOf γ := by
    rw [hμ, sub_sub, ← map_add]
    simp [γ]
  rw [hwt]
  exact map_mem_weightSpaceOfMap P φ hw

variable [FiniteDimensional K H] (S : A.Symmetrization)

omit [DecidableEq ι] in
/-- `2 (μ | αᵢ) = c (αᵢ | αᵢ)` iff `⟨μ, αᵢ^∨⟩ = c`. -/
lemma two_mul_dualBilinForm_root_eq_iff (μ : Dual K H) (i : ι) (c : K) :
    2 * P.dualBilinForm S μ (P.root i) = c * P.dualBilinForm S (P.root i) (P.root i) ↔
      μ (P.coroot i) = c := by
  have hε : (S.ε i : K) ≠ 0 := by exact_mod_cast S.ε_ne_zero i
  rw [dualBilinForm_root_right, dualBilinForm_root_self S hA]
  push_cast
  constructor <;> intro h
  · have h2 : (2 / (S.ε i : K)) * (μ (P.coroot i) - c) = 0 := by linear_combination h
    simpa [sub_eq_zero, hε] using h2
  · linear_combination (2 / (S.ε i : K)) * h

/-- **The Kac–Kazhdan condition for a simple root** ([KK] (check)): if
`2 (Λ + ρ | αᵢ) = n (αᵢ | αᵢ)` for a positive integer `n` with `n αᵢ ≤ η`, then `M'(Λ)` has a
nonzero vector of weight `Λ - η`. -/
theorem inf_weightSpace_ne_bot_of_two_mul_dualBilinForm {Λ : Dual K H} {η : ι → ℤ} {i : ι}
    {n : ℕ} (hn0 : 0 < n)
    (hn : 2 * P.dualBilinForm S (Λ + P.rho) (P.root i) =
      n * P.dualBilinForm S (P.root i) (P.root i))
    (hη : n • Pi.single i 1 ≤ η) :
    (maxSubmodule P Λ).toSubmodule ⊓ weightSpace P Λ (Λ - P.rootOf η) ≠ ⊥ :=
  inf_weightSpace_ne_bot_of_coroot P hA hn0
    ((two_mul_dualBilinForm_root_eq_iff P hA S _ i n).mp hn) hη

/-- **Vanishing of the Shapovalov determinant along the hyperplanes of the simple roots**
([KK] (check)): if `2 (Λ + ρ | αᵢ) = n (αᵢ | αᵢ)` for a positive integer `n` with `n αᵢ ≤ η`, the
determinant of the Shapovalov form on `M(Λ)_{Λ - η}` (with respect to any basis) vanishes. -/
theorem det_toMatrix_weightSpaceForm_eq_zero_of_two_mul_dualBilinForm {Λ : Dual K H}
    {η : ι → ℤ} {i : ι} {n : ℕ} (hn0 : 0 < n)
    (hn : 2 * P.dualBilinForm S (Λ + P.rho) (P.root i) =
      n * P.dualBilinForm S (P.root i) (P.root i))
    (hη : n • Pi.single i 1 ≤ η) {m : Type*} [Fintype m] [DecidableEq m]
    (b : Basis m K (weightSpace P Λ (Λ - P.rootOf η))) :
    (LinearMap.BilinForm.toMatrix b (weightSpaceForm P Λ _)).det = 0 := by
  by_contra h
  exact (det_toMatrix_weightSpaceForm_ne_zero_iff P Λ _ b).mp h
    |> (inf_weightSpace_ne_bot_of_two_mul_dualBilinForm P hA S hn0 hn hη ·)

end Simple

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
