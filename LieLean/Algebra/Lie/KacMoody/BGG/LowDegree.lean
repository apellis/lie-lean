/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.Verma
import LieLean.Algebra.Lie.KacMoody.CasimirIrreducible
import Mathlib.Algebra.Lie.DirectSum

/-!
# The BGG resolution in low degrees

Let `A` be a symmetrizable generalized Cartan matrix, `𝔤 = 𝔤(A)` over a field `K` of
characteristic zero and `Λ` a dominant integral weight. The BGG resolution of `L(Λ)` ends with
`⊕ᵢ M(rᵢ · Λ) → M(Λ) → L(Λ) → 0`, where the first map is the sum of the embeddings
`M(rᵢ · Λ) ↪ M(Λ)`, `v ↦ fᵢ^{⟨Λ, αᵢ^∨⟩ + 1} v_Λ`, and the second is the canonical projection
([HumO] §6.1; [Kum] Def. 9.2.17). We prove that this sequence is exact: this is the
presentation `L(Λ) = M(Λ) / ∑ᵢ U(𝔤) fᵢ^{⟨Λ, αᵢ^∨⟩+1} v_Λ` of [Kac] Cor. 10.4
(`Matrix.Realization.KacMoodyAlgebra.FPowQuotient.equivIrreducibleModule`).

## Main definitions

* `DirectSum.toLieModule`: the morphism `⊕ᵢ Mᵢ → N` of Lie modules defined by morphisms
  `Mᵢ → N`.
* `Matrix.Realization.KacMoodyAlgebra.bggDiffOne`: the map `⊕ᵢ M(rᵢ · Λ) → M(Λ)`.
* `Matrix.Realization.KacMoodyAlgebra.bggAug`: the augmentation `M(Λ) → L(Λ)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.range_bggDiffOne`: the image of `⊕ᵢ M(rᵢ · Λ) → M(Λ)` is
  the kernel of `M(Λ) → L(Λ)` (exactness at `M(Λ)`).
* `Matrix.Realization.KacMoodyAlgebra.bggAug_surjective`: `M(Λ) → L(Λ)` is surjective.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Thm. 2.6, §6.1.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Cor. 10.4.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §9.1–9.2.
-/

open Module LieModule DirectSum

noncomputable section

namespace DirectSum

variable {R ι L N : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [DecidableEq ι]
  {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, LieRingModule L (M i)] [∀ i, LieModule R L (M i)]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- The morphism of Lie modules `⊕ᵢ Mᵢ → N` defined by a family of morphisms `Mᵢ → N`. -/
def toLieModule (φ : ∀ i, M i →ₗ⁅R,L⁆ N) : (⨁ i, M i) →ₗ⁅R,L⁆ N where
  toLinearMap := DirectSum.toModule R ι N fun i ↦ (φ i : M i →ₗ[R] N)
  map_lie' {x m} := by
    let ψ : (⨁ i, M i) →ₗ[R] N := DirectSum.toModule R ι N fun i ↦ (φ i : M i →ₗ[R] N)
    change ψ ⁅x, m⁆ = ⁅x, ψ m⁆
    induction m using DirectSum.induction_on with
    | zero => rw [lie_zero, map_zero, lie_zero]
    | of i m =>
      have : ⁅x, DirectSum.of M i m⁆ = DirectSum.of M i ⁅x, m⁆ :=
        ((DirectSum.lieModuleOf R ι L M i).map_lie x m).symm
      rw [this, ← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof,
        DirectSum.toModule_lof]
      exact LieModuleHom.map_lie _ _ _
    | add m m' hm hm' => rw [lie_add, map_add, map_add, hm, hm', lie_add]

omit [LieAlgebra R L] [∀ i, LieModule R L (M i)] [LieModule R L N] in
@[simp] lemma toLieModule_of (φ : ∀ i, M i →ₗ⁅R,L⁆ N) (i : ι) (m : M i) :
    toLieModule φ (DirectSum.of M i m) = φ i m :=
  DirectSum.toModule_lof (M := M) R i m

omit [LieAlgebra R L] [∀ i, LieModule R L (M i)] [LieModule R L N] in
/-- The image of `⊕ᵢ Mᵢ → N` is the sum of the images of the `Mᵢ → N`. -/
theorem range_toLieModule (φ : ∀ i, M i →ₗ⁅R,L⁆ N) :
    (toLieModule φ).range = ⨆ i, (φ i).range := by
  refine le_antisymm ?_ (iSup_le fun i ↦ ?_)
  · rintro _ ⟨m, rfl⟩
    induction m using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | of i m =>
      rw [toLieModule_of]
      exact LieSubmodule.mem_iSup_of_mem i ⟨m, rfl⟩
    | add m m' hm hm' => rw [map_add]; exact add_mem hm hm'
  · rintro _ ⟨m, rfl⟩
    exact ⟨DirectSum.of M i m, toLieModule_of φ i m⟩

end DirectSum

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)
  {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)

omit [DecidableEq ι] [CharZero K] in
lemma add_rho_coroot_eq (i : ι) :
    (Λ + P.rho) (P.coroot i) = ((hΛ i).choose + 1 : ℕ) := by
  have := (hΛ i).choose_spec
  rw [LinearMap.add_apply, rho_coroot]
  push_cast
  linear_combination this

variable (Λ) in
/-- The first term `C₁ = ⊕ᵢ M(rᵢ · Λ)` of the BGG resolution. -/
abbrev BGGOne : Type _ :=
  ⨁ i : ι, VermaModule P (P.reflection hA i (Λ + P.rho) - P.rho)

/-- The first differential `C₁ = ⊕ᵢ M(rᵢ · Λ) → C₀ = M(Λ)` of the BGG resolution: the sum of the
embeddings `M(rᵢ · Λ) ↪ M(Λ)`, `v_{rᵢ · Λ} ↦ fᵢ^{⟨Λ, αᵢ^∨⟩ + 1} v_Λ`. -/
def bggDiffOne : BGGOne P hA Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ :=
  DirectSum.toLieModule fun i ↦
    reflectionHom hA (Nat.succ_pos _) (add_rho_coroot_eq P hΛ i)

/-- The augmentation `C₀ = M(Λ) → L(Λ)` of the BGG resolution. -/
def bggAug : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P Λ :=
  LieSubmodule.Quotient.mk' (maxSubmodule P Λ)

omit [CharZero K] in
theorem bggAug_surjective : Function.Surjective (bggAug P (Λ := Λ)) :=
  LieSubmodule.Quotient.surjective_mk' _

omit [CharZero K] in
theorem ker_bggAug : (bggAug P (Λ := Λ)).ker = maxSubmodule P Λ :=
  LieSubmodule.Quotient.mk'_ker _

/-- The image of `⊕ᵢ M(rᵢ · Λ) → M(Λ)` is the submodule generated by the `fᵢ^{nᵢ+1} v_Λ`,
`nᵢ = ⟨Λ, αᵢ^∨⟩`. -/
theorem range_bggDiffOne_eq_fPowSubmodule :
    (bggDiffOne P hA hΛ).range = fPowSubmodule P Λ fun i ↦ (hΛ i).choose := by
  rw [bggDiffOne, DirectSum.range_toLieModule]
  refine le_antisymm (iSup_le fun i ↦ ?_) (LieSubmodule.lieSpan_le.mpr ?_)
  · rw [VermaModule.range_eq_lieSpan, LieSubmodule.lieSpan_le, Set.singleton_subset_iff,
      reflectionHom_hwv]
    exact LieSubmodule.subset_lieSpan ⟨i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    refine LieSubmodule.mem_iSup_of_mem i ⟨hwv P _, ?_⟩
    rw [reflectionHom_hwv]

variable [FiniteDimensional K H] (hS : A.IsSymmetrizable)
include hS hA hΛ

/-- For symmetrizable `A`, the maximal proper submodule of `M(Λ)` is generated by the
`fᵢ^{⟨Λ, αᵢ^∨⟩+1} v_Λ` ([Kac] Cor. 10.4). -/
theorem maxSubmodule_eq_fPowSubmodule :
    maxSubmodule P Λ = fPowSubmodule P Λ fun i ↦ (hΛ i).choose := by
  have hn : ∀ i, Λ (P.coroot i) = (hΛ i).choose := fun i ↦ (hΛ i).choose_spec
  refine le_antisymm (fun x hx ↦ ?_) (fPowSubmodule_le_maxSubmodule P Λ hA hn)
  have := FPowQuotient.toIrreducibleModule_injective hS hA hn
    (a₁ := LieSubmodule.Quotient.mk' _ x) (a₂ := 0) (by
      rw [map_zero]
      change LieSubmodule.Quotient.mk' (maxSubmodule P Λ) x = 0
      rw [LieSubmodule.Quotient.mk'_apply, LieSubmodule.Quotient.mk_eq_zero']
      exact hx)
  rwa [LieSubmodule.Quotient.mk'_apply, LieSubmodule.Quotient.mk_eq_zero'] at this

/-- **Exactness of the BGG resolution at `C₀ = M(Λ)`** ([HumO] Thm. 2.6, [Kac] Cor. 10.4): for a
symmetrizable generalized Cartan matrix and `Λ` dominant integral, the image of
`⊕ᵢ M(rᵢ · Λ) → M(Λ)` is the kernel of the augmentation `M(Λ) → L(Λ)`. -/
theorem range_bggDiffOne : (bggDiffOne P hA hΛ).range = (bggAug P (Λ := Λ)).ker := by
  rw [ker_bggAug, maxSubmodule_eq_fPowSubmodule P hA hΛ hS,
    range_bggDiffOne_eq_fPowSubmodule]

end Matrix.Realization.KacMoodyAlgebra
