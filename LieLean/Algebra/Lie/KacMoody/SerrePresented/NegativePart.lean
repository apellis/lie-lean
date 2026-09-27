/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.SerrePresented

/-!
# The negative part `𝔫̂₋` of the Serre-presented algebra

Let `A` be a generalized Cartan matrix, `K` a field of characteristic zero, `𝔤̂ = 𝔤̂(A)` the
Serre-presented algebra, `𝔫̂₋ ⊆ 𝔤̂` and `𝔫₋ ⊆ 𝔤(A)` the negative nilpotent subalgebras, and
`𝔯̂₋ = 𝔯̂ ∩ 𝔫̂₋`. This file collects facts about `𝔫̂₋` and the projection `𝔫̂₋ → 𝔫₋` used in the
proof of the Gabber–Kac theorem ([Kac] Thm. 9.11, [GK]; `KacMoody/GabberKac.lean`).

## Main definitions

* `Matrix.Realization.SerrePresentedAlgebra.negProj`: the surjection `𝔫̂₋ → 𝔫₋`.
* `LieModule.lieWeightSpan`: the span of brackets of weight vectors with prescribed weights.

## Main results

* `Matrix.Realization.SerrePresentedAlgebra.negProj_eq_zero_iff`: the kernel of `𝔫̂₋ → 𝔫₋` is
  `𝔯̂₋`.
* `Matrix.Realization.SerrePresentedAlgebra.radicalNeg_le_range_fHom`: `𝔯̂₋ ⊆ 𝔫̂₋`.
* `Matrix.Realization.SerrePresentedAlgebra.radical_inf_rootSpace_neg_root`: `𝔯̂` meets
  `𝔤̂_{-αᵢ}` trivially.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.11 (check).
* [GK] O. Gabber, V. G. Kac, *On defining relations of certain infinite-dimensional Lie
  algebras*, Bull. Amer. Math. Soc. (N.S.) **5** (1981), 185–189.
-/

open FreeLieAlgebra Module LieModule LieAlgebra

noncomputable section

/-! ### Brackets of weight vectors -/

namespace LieModule

variable {K H L : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  (φ : H →ₗ[K] L)

/-- The span of the brackets `[a, b]` with `a ∈ A ∩ L_μ`, `b ∈ B ∩ L_{μ'}`, `μ ∈ S`, `μ' ∈ T` and
`μ + μ' = ν`. -/
def lieWeightSpan (A B : Submodule K L) (S T : Set (Dual K H)) (ν : Dual K H) :
    Submodule K L :=
  Submodule.span K {x | ∃ a b, (∃ μ ∈ S, ∃ μ' ∈ T, μ + μ' = ν ∧
    a ∈ A ⊓ weightSpaceOfMap L φ μ ∧ b ∈ B ⊓ weightSpaceOfMap L φ μ') ∧ x = ⁅a, b⁆}

lemma lieWeightSpan_le (A B : Submodule K L) (S T : Set (Dual K H)) (ν : Dual K H) :
    lieWeightSpan φ A B S T ν ≤ weightSpaceOfMap L φ ν := by
  rw [lieWeightSpan, Submodule.span_le]
  rintro _ ⟨a, b, ⟨μ, -, μ', -, rfl, ⟨-, ha⟩, ⟨-, hb⟩⟩, rfl⟩
  exact lie_mem_weightSpaceOfMap φ ha hb

/-- If `A`, `B` are `φ(H)`-stable and contained in the sums of the weight spaces `L_μ`, `μ ∈ S`,
resp. `μ ∈ T`, then `[A, B]` is contained in the sum of the `lieWeightSpan φ A B S T ν`. -/
theorem span_lie_le_iSup_lieWeightSpan {A B : Submodule K L}
    (hA : ∀ a, ∀ x ∈ A, ⁅φ a, x⁆ ∈ A) (hB : ∀ a, ∀ x ∈ B, ⁅φ a, x⁆ ∈ B)
    {S T : Set (Dual K H)} (hAS : A ≤ ⨆ μ ∈ S, weightSpaceOfMap L φ μ)
    (hBT : B ≤ ⨆ μ ∈ T, weightSpaceOfMap L φ μ) :
    Submodule.span K {x | ∃ a b, (a ∈ A ∧ b ∈ B) ∧ x = ⁅a, b⁆} ≤
      ⨆ ν, lieWeightSpan φ A B S T ν := by
  rw [Submodule.span_le]
  rintro _ ⟨a, b, ⟨ha, hb⟩, rfl⟩
  have ha' : a ∈ ⨆ μ ∈ S, (A ⊓ weightSpaceOfMap L φ μ) :=
    inf_iSup_weightSpaceOfMap_le φ A hA S ⟨ha, hAS ha⟩
  have hb' : b ∈ ⨆ μ ∈ T, (B ⊓ weightSpaceOfMap L φ μ) :=
    inf_iSup_weightSpaceOfMap_le φ B hB T ⟨hb, hBT hb⟩
  rw [← iSup_subtype''] at ha' hb'
  refine Submodule.iSup_induction _ (motive := fun a ↦ ⁅a, b⁆ ∈ _) ha' (fun μ a ha ↦ ?_)
    (by simp) (fun a₁ a₂ h₁ h₂ ↦ by rw [add_lie]; exact Submodule.add_mem _ h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun b ↦ ⁅a, b⁆ ∈ _) hb' (fun μ' b hb ↦ ?_)
    (by simp) (fun b₁ b₂ h₁ h₂ ↦ by rw [lie_add]; exact Submodule.add_mem _ h₁ h₂)
  exact Submodule.mem_iSup_of_mem ((μ : Dual K H) + μ')
    (Submodule.subset_span ⟨a, b, ⟨μ, μ.2, μ', μ'.2, rfl, ha, hb⟩, rfl⟩)

/-- A weight vector of weight `ν` in `[A, B]` lies in `lieWeightSpan φ A B S T ν`. -/
theorem mem_lieWeightSpan_of_mem {A B : Submodule K L}
    (hA : ∀ a, ∀ x ∈ A, ⁅φ a, x⁆ ∈ A) (hB : ∀ a, ∀ x ∈ B, ⁅φ a, x⁆ ∈ B)
    {S T : Set (Dual K H)} (hAS : A ≤ ⨆ μ ∈ S, weightSpaceOfMap L φ μ)
    (hBT : B ≤ ⨆ μ ∈ T, weightSpaceOfMap L φ μ) {ν : Dual K H} {x : L}
    (hx : x ∈ Submodule.span K {x | ∃ a b, (a ∈ A ∧ b ∈ B) ∧ x = ⁅a, b⁆})
    (hxν : x ∈ weightSpaceOfMap L φ ν) : x ∈ lieWeightSpan φ A B S T ν :=
  mem_of_mem_iSup_of_le φ _ (lieWeightSpan_le φ A B S T) hxν
    (span_lie_le_iSup_lieWeightSpan φ hA hB hAS hBT hx)

end LieModule

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

omit [DecidableEq ι] in
lemma height_add (k l : ι → ℤ) : height (k + l) = height k + height l := by
  simp [height, Finset.sum_add_distrib]

omit [DecidableEq ι] in
lemma height_pos {k : ι → ℤ} (hk : k ∈ posCone ι) : 0 < height k := by
  obtain ⟨hk0, hk⟩ := hk
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra! h; exact hk (funext h)
  exact Finset.sum_pos' (fun j _ ↦ hk0 j) ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hk0 i) hi.symm⟩

namespace SerrePresentedAlgebra

/-! ### The subalgebra `𝔫̂₋` and the projection `𝔫̂₋ → 𝔫₋` -/

lemma lie_h_mem_range_fHom (a : H) {x : P.SerrePresentedAlgebra}
    (hx : x ∈ LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra)) :
    ⁅h P a, x⁆ ∈ LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra) := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y', hy'⟩ := AuxLieAlgebra.lie_h_fHom P a y
  refine ⟨y', ?_⟩
  change π P (AuxLieAlgebra.fHom P y') = ⁅π P (AuxLieAlgebra.h P a), π P (AuxLieAlgebra.fHom P y)⁆
  rw [← LieHom.map_lie, hy']

lemma range_fHom_le :
    LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra) ≤
      ⨆ μ ∈ P.negWeights, rootSpace P μ := by
  rintro _ ⟨y, rfl⟩; exact fHom_mem P y

/-- `𝔫̂₋` is spanned by the `fᵢ` and `[𝔫̂₋, 𝔫̂₋]`; more precisely, it is contained in the sum over
`ν` of the span of the `fᵢ` with `-αᵢ = ν` and of the brackets of weight vectors of `𝔫̂₋` of
total weight `ν`. -/
lemma range_fHom_le_iSup :
    LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra) ≤
      ⨆ ν, (Submodule.span K (f P '' {i | -P.root i = ν}) ⊔
        lieWeightSpan (h P)
          (LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra))
          (LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra))
          P.negWeights P.negWeights ν) := by
  rintro _ ⟨y, rfl⟩
  induction y using FreeLieAlgebra.induction_on with
  | of i =>
    refine Submodule.mem_iSup_of_mem (-P.root i) (Submodule.mem_sup_left ?_)
    exact Submodule.subset_span ⟨i, rfl, by simp⟩
  | zero => simp
  | add y z hy hz => simpa using Submodule.add_mem _ hy hz
  | smul c y hy => simpa using Submodule.smul_mem _ c hy
  | lie y z _ _ =>
    have := span_lie_le_iSup_lieWeightSpan (h P)
      (fun a x hx ↦ lie_h_mem_range_fHom P a hx) (fun a x hx ↦ lie_h_mem_range_fHom P a hx)
      (range_fHom_le P) (range_fHom_le P)
      (Submodule.subset_span ⟨fHom P y, fHom P z, ⟨⟨y, rfl⟩, ⟨z, rfl⟩⟩, rfl⟩)
    simp only [LieHom.coe_toLinearMap, LieHom.map_lie]
    exact SetLike.le_def.mp (iSup_mono fun ν ↦ le_sup_right) this

variable [CharZero K] (hA : A.IsGeneralizedCartan)

/-- The projection `𝔫̂₋ → 𝔫₋` induced by `𝔤̂(A) → 𝔤(A)`. -/
def negProj : (fHom P).range →ₗ⁅K⁆ (KacMoodyAlgebra.fHom P).range where
  toFun x := ⟨toKacMoody P hA x, by
    obtain ⟨y, hy⟩ := (LieHom.mem_range _ _).mp x.2
    exact ⟨y, by rw [← hy]; rfl⟩⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
  map_lie' {x y} := by ext; simp

@[simp] lemma coe_negProj (x : (fHom P).range) :
    (negProj P hA x : P.KacMoodyAlgebra) = toKacMoody P hA x := rfl

lemma negProj_surjective : Function.Surjective (negProj P hA) := by
  rintro ⟨_, y, rfl⟩
  exact ⟨⟨fHom P y, LieHom.mem_range_self _ y⟩, rfl⟩

lemma negProj_eq_zero_iff {x : (fHom P).range} :
    negProj P hA x = 0 ↔ (x : P.SerrePresentedAlgebra) ∈ radicalNeg P := by
  rw [← LieSubmodule.mem_toSubmodule, radicalNeg_toSubmodule P hA, Submodule.mem_inf,
    LieSubmodule.mem_toSubmodule, mem_radical_iff, ← coe_negProj, ZeroMemClass.coe_eq_zero]
  exact ⟨fun h ↦ ⟨h, x.2⟩, fun h ↦ h.1⟩

lemma toKacMoody_mem_rootSpace {μ : Dual K H} {x : P.SerrePresentedAlgebra}
    (hx : x ∈ rootSpace P μ) : toKacMoody P hA x ∈ KacMoodyAlgebra.rootSpace P μ := by
  intro a
  rw [← toKacMoody_h P hA, ← LieHom.map_lie, hx a, map_smul]

/-- `𝔯̂ ∩ 𝔤̂_{-αᵢ} = 0`. -/
lemma radical_inf_rootSpace_neg_root (i : ι) :
    (radical P hA).toSubmodule ⊓ rootSpace P (-P.root i) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  rw [rootSpace_neg_root] at hx'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx'
  have : c • KacMoodyAlgebra.f P i = 0 := by
    rw [← toKacMoody_f P hA, ← map_smul]; exact (mem_radical_iff P hA).mp hx
  rw [smul_eq_zero] at this
  rcases this with rfl | h
  · simp
  · exact absurd h (KacMoodyAlgebra.f_ne_zero P i)

include hA in
lemma radicalNeg_le_range_fHom :
    (radicalNeg P).toSubmodule ≤
      LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra) := by
  rw [radicalNeg_toSubmodule P hA]; exact inf_le_right

end SerrePresentedAlgebra

end Matrix.Realization

end
