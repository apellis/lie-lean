/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationProjectiveCover
import LieLean.Algebra.Lie.KacMoody.TranslationEquivalence
import LieLean.Algebra.Lie.KacMoody.DualityHom
import LieLean.Algebra.Lie.KacMoody.EnoughInjectives

/-!
# A criterion for the self-duality of `P(λ)`

This is the final step of Irving's argument for Humphreys, GSM 94, Theorem 7.16 (a). Suppose
`X ∈ 𝒪` is finitely generated and projective and contains a self-dual submodule `Z ≅ Z^∨` such
that some morphism `X → L(λ)` does not vanish on `Z`. Then `P(λ) ≅ P(λ)^∨`. In Humphreys' proof
`X` is a wall-crossing `Θ_{s_1} ⋯ Θ_{s_k} M(λ°)` of the dominant Verma module in the linkage class
of the antidominant weight `λ`, and `Z` is a self-dual submodule.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.injective_of_surjective`: a surjective
  endomorphism of a module in `𝒪` is injective.
* `Matrix.Realization.KacMoodyAlgebra.IsProjectiveCover.exists_retract_of_comp_ne_zero`: a
  projective cover of `L(λ)` is a retract of `Z`.
* `Matrix.Realization.KacMoodyAlgebra.IsProjectiveCover.nonempty_equiv_restrictedDual_of_selfDual`
  and `ProjectiveCover.nonempty_equiv_restrictedDual_of_selfDual`:
  the criterion.

## Proof

Lift `π : P(λ) → L(λ)` along `f|_Z` to `q : P(λ) → Z` and `f` along `π` to `p : X → P(λ)`. Then
`π ∘ (p ∘ ι ∘ q) = π`, so `p ∘ ι ∘ q` is surjective, hence bijective, and `P(λ)` is a retract of
`Z`. Dually `P(λ)^∨` is a retract of `Z^∨ ≅ Z`; since `P(λ)^∨` is injective in `𝒪`, the
retraction extends along `Z ⊆ X`, so `P(λ)^∨` is a retract of `X` and hence finitely generated
and projective. It has the character of `P(λ)`, so `P(λ)^∨ ≅ P(λ)` (Corollary 3.10).
Reconstructed; Humphreys gives this step in a few lines.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.10, §7.16.
-/

noncomputable section

open Module LieModule

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

section Generic

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-- A surjective endomorphism of a module in `𝒪` is injective: its dual is injective, hence
bijective (the weight spaces are finite-dimensional), and `V^∨` separates the points of `V`. -/
theorem IsCategoryO.injective_of_surjective (hV : IsCategoryO P V)
    (a : V →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (ha : Function.Surjective a) : Function.Injective a := by
  have hO := isCategoryO_restrictedDual hV
  obtain ⟨-, hsurj⟩ := IsCategoryO.bijective_of_injective_of_character_eq P hO hO
    (restrictedDualMap P a) (injective_restrictedDualMap P a ha) rfl
  intro x y hxy
  rw [← sub_eq_zero]
  refine hV.eq_zero_of_forall_restrictedDual P fun φ ↦ ?_
  obtain ⟨ψ, rfl⟩ := hsurj φ
  rw [toDual_restrictedDualMap, map_sub, hxy, sub_self, map_zero]

end Generic

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

namespace IsProjectiveCover

variable {lam : Dual K H}
  {V X Z : Type (max u₁ u₂)} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [AddCommGroup X] [Module K X]
  [LieRingModule P.KacMoodyAlgebra X] [LieModule K P.KacMoodyAlgebra X]
  [AddCommGroup Z] [Module K Z] [LieRingModule P.KacMoodyAlgebra Z]
  [LieModule K P.KacMoodyAlgebra Z]
  {π : V →ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P lam}

omit [IsAlgClosed K] [FiniteDimensional K H] [LieModule K P.KacMoodyAlgebra X] in
/-- If `V` is a projective cover of `L(λ)`, `X ∈ 𝒪` is projective, `j : Z → X` is a morphism and
`f : X → L(λ)` does not vanish on the image of `j`, then `V` is a retract of `Z`. -/
theorem exists_retract_of_comp_ne_zero (hπ : IsProjectiveCover P V π)
    (hVp : IsProjectiveO.{max u₁ u₂} P V) (hXproj : IsProjectiveO.{max u₁ u₂} P X)
    (hZ : IsCategoryO P Z) (j : Z →ₗ⁅K,𝔤⁆ X) (f : X →ₗ⁅K,𝔤⁆ IrreducibleModule P lam)
    (hf : f.comp j ≠ 0) :
    ∃ (s : V →ₗ⁅K,𝔤⁆ Z) (r : Z →ₗ⁅K,𝔤⁆ V), r.comp s = LieModuleHom.id := by
  have hLO := IrreducibleModule.isCategoryO P lam
  obtain ⟨q, hq⟩ := hVp hZ hLO (f.comp j) (surjective_of_ne_zero_irreducibleModule P hf) π
  obtain ⟨p, hp⟩ := hXproj hπ.isCategoryO hLO π hπ.surjective f
  set a := (p.comp j).comp q with ha
  have hπa : π.comp a = π := by
    refine LieModuleHom.ext fun x ↦ ?_
    have h1 := LieModuleHom.congr_fun hp (j (q x))
    have h2 := LieModuleHom.congr_fun hq x
    simp only [ha, LieModuleHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
  have hsurj : Function.Surjective a := by
    rw [← LieModuleHom.range_eq_top]
    refine hπ.eq_top_of_not_le_ker _ fun hle ↦ ?_
    obtain ⟨x, hx⟩ := hπ.surjective (IrreducibleModule.hwv P lam)
    have h0 : a x ∈ π.ker := hle ((LieModuleHom.mem_range _ _).mpr ⟨x, rfl⟩)
    rw [LieModuleHom.mem_ker, ← LieModuleHom.comp_apply, hπa, hx] at h0
    exact IrreducibleModule.hwv_ne_zero P lam h0
  let e := LieModuleEquiv.ofBijective a
    ⟨IsCategoryO.injective_of_surjective P hπ.isCategoryO a hsurj, hsurj⟩
  refine ⟨q, (e.symm : V →ₗ⁅K,𝔤⁆ V).comp (p.comp j), LieModuleHom.ext fun x ↦ ?_⟩
  change e.symm (p (j (q x))) = x
  exact e.symm_apply_apply x

include hA in
/-- **Self-duality criterion for a projective cover** (the last step of Irving's proof of
Humphreys, GSM 94, Theorem 7.16 (a)). Let `V` be a projective cover of `L(λ)` in `𝒪`, `X ∈ 𝒪`
finitely generated and projective, `j : Z ↪ X` with `Z ∈ 𝒪` self-dual, and `f : X → L(λ)` with
`f ∘ j ≠ 0`. Then `V ≅ V^∨`. -/
theorem nonempty_equiv_restrictedDual_of_selfDual (hπ : IsProjectiveCover P V π)
    (hVp : IsProjectiveO.{max u₁ u₂} P V) (hXproj : IsProjectiveO.{max u₁ u₂} P X)
    (hX : IsCategoryO P X) {S : Finset X} (hS : LieSubmodule.lieSpan K 𝔤 (S : Set X) = ⊤)
    (hZ : IsCategoryO P Z) (eZ : Z ≃ₗ⁅K,𝔤⁆ restrictedDual P Z) (j : Z →ₗ⁅K,𝔤⁆ X)
    (hj : Function.Injective j) (f : X →ₗ⁅K,𝔤⁆ IrreducibleModule P lam) (hf : f.comp j ≠ 0) :
    Nonempty (V ≃ₗ⁅K,𝔤⁆ restrictedDual P V) := by
  classical
  have hVO := hπ.isCategoryO
  have hDO := isCategoryO_restrictedDual hVO
  obtain ⟨s, r, hrs⟩ := hπ.exists_retract_of_comp_ne_zero P hVp hXproj hZ j f hf
  -- `V^∨` is a retract of `Z`
  obtain ⟨b, c, hbc⟩ : ∃ (b : Z →ₗ⁅K,𝔤⁆ restrictedDual P V) (c : restrictedDual P V →ₗ⁅K,𝔤⁆ Z),
      b.comp c = LieModuleHom.id := by
    refine ⟨(restrictedDualMap P s).comp (eZ : Z →ₗ⁅K,𝔤⁆ restrictedDual P Z),
      (eZ.symm : restrictedDual P Z →ₗ⁅K,𝔤⁆ Z).comp (restrictedDualMap P r),
      LieModuleHom.ext fun φ ↦ ?_⟩
    have h1 : eZ (eZ.symm (restrictedDualMap P r φ)) = restrictedDualMap P r φ :=
      eZ.apply_symm_apply _
    have h2 : restrictedDualMap P s (restrictedDualMap P r φ) = φ :=
      LieModuleHom.congr_fun (congrArg (restrictedDualMap P) hrs) φ
    exact (congrArg (restrictedDualMap P s) h1).trans h2
  -- the retraction extends along `j`, since `V^∨` is injective in `𝒪`
  obtain ⟨ψ, hψ⟩ := hVp.isInjectiveO_restrictedDual P hVO.iSup_weightSpaceOfMap_eq_top
    (M := Z) (N := X) hZ hX j hj b
  have hψc : ψ.comp (j.comp c) = LieModuleHom.id := by
    refine LieModuleHom.ext fun φ ↦ ?_
    exact (LieModuleHom.congr_fun hψ (c φ)).trans (LieModuleHom.congr_fun hbc φ)
  have hDp : IsProjectiveO.{max u₁ u₂} P (restrictedDual P V) :=
    hXproj.of_retract (j.comp c) ψ hψc
  -- `V^∨` is finitely generated
  have hDS : LieSubmodule.lieSpan K 𝔤 (↑(S.image ψ) : Set (restrictedDual P V)) = ⊤ := by
    rw [eq_top_iff]
    intro φ _
    have hle : LieSubmodule.lieSpan K 𝔤 (S : Set X) ≤
        (LieSubmodule.lieSpan K 𝔤 (↑(S.image ψ) : Set (restrictedDual P V))).comap ψ := by
      rw [LieSubmodule.lieSpan_le]
      intro x hx
      exact LieSubmodule.subset_lieSpan (by simpa using ⟨x, hx, rfl⟩)
    have hx := hle (hS ▸ LieSubmodule.mem_top (j (c φ)))
    rw [LieSubmodule.mem_comap] at hx
    have hφ : ψ (j (c φ)) = φ := LieModuleHom.congr_fun hψc φ
    rwa [hφ] at hx
  obtain ⟨x₀, -, -, hx₀⟩ := hπ.exists_generator
  have hch : hVO.character = hDO.character := by
    rw [IsCategoryO.character_eq_iff]
    exact fun μ ↦ (multiplicity_restrictedDual hVO μ).symm
  exact IsProjectiveO.nonempty_equiv_of_character_eq P hA hVp hVO (S := {x₀})
    (by simpa using hx₀) hDp hDO hDS hch

end IsProjectiveCover

/-- **Self-duality criterion for `P(λ)`**:
`IsProjectiveCover.nonempty_equiv_restrictedDual_of_selfDual` for `P(λ)`. -/
theorem ProjectiveCover.nonempty_equiv_restrictedDual_of_selfDual {lam : Dual K H}
    {X Z : Type (max u₁ u₂)} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
    [LieModule K P.KacMoodyAlgebra X] [AddCommGroup Z] [Module K Z]
    [LieRingModule P.KacMoodyAlgebra Z] [LieModule K P.KacMoodyAlgebra Z]
    (hXproj : IsProjectiveO.{max u₁ u₂} P X)
    (hX : IsCategoryO P X) {S : Finset X} (hS : LieSubmodule.lieSpan K 𝔤 (S : Set X) = ⊤)
    (hZ : IsCategoryO P Z) (eZ : Z ≃ₗ⁅K,𝔤⁆ restrictedDual P Z) (j : Z →ₗ⁅K,𝔤⁆ X)
    (hj : Function.Injective j) (f : X →ₗ⁅K,𝔤⁆ IrreducibleModule P lam) (hf : f.comp j ≠ 0) :
    Nonempty (ProjectiveCover P hA lam ≃ₗ⁅K,𝔤⁆ restrictedDual P (ProjectiveCover P hA lam)) :=
  (ProjectiveCover.isProjectiveCover P lam hA).nonempty_equiv_restrictedDual_of_selfDual P hA
    (ProjectiveCover.isProjectiveO P hA lam) hXproj hX hS hZ eZ j hj f hf

end Matrix.Realization.KacMoodyAlgebra
