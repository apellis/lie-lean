/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.RelativeHom
import LieLean.Algebra.Lie.KacMoody.CategoryOExtVerma
import LieLean.Algebra.Lie.KacMoody.DualityFunctor
import LieLean.Algebra.Lie.KacMoody.EnoughInjectives
import LieLean.Algebra.Lie.KacMoody.RelativeVermaTensor

/-!
# Relative cohomology of `Hom_K(M, N^∨)` along standard filtrations

For `𝔤`-modules `M`, `N`, write `RelAcyclic P M N` for the vanishing of the relative cohomology
`Hⁿ(𝔤, 𝔥; Hom_K(M, N))` in all degrees `n > 0`. For `𝔫₋` finite-dimensional this holds for
`M = M(λ)` and `N = M(μ)^∨` (`relAcyclic_verma_restrictedDual`, from
`exists_δ_eq_relVerma`). Short exact sequences of weight modules give long exact sequences in
either variable (`LieModule.ChevalleyEilenberg.isZero_relCohomology_hom_of_shortExact_left`,
`_right`), and the restricted dual is exact, so the vanishing passes along standard filtrations
in both variables.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.RelAcyclic`: `Hⁿ(𝔤, 𝔥; Hom_K(M, N)) = 0` for `n > 0`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.relAcyclic_verma_restrictedDual`: for `M(λ)` and `M(μ)^∨`.
* `Matrix.Realization.KacMoodyAlgebra.RelAcyclic.of_isStdFiltered_left`,
  `Matrix.Realization.KacMoodyAlgebra.RelAcyclic.of_isStdFiltered_right`: propagation along a
  standard filtration of the first variable, resp. of `N` in `N^∨`.
* `Matrix.Realization.KacMoodyAlgebra.relAcyclic_restrictedDual_of_isStdFiltered`: for
  `N ⊆ X` and `N' ⊆ Y` with standard filtrations, `X`, `Y` in `𝒪`, the relative cohomology of
  `Hom_K(N, N'^∨)` vanishes in positive degrees.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Thm. 6.15 (a). Humphreys proves the comparison with `Extⁿ_𝒪` by the
  universal property of derived functors; the vanishing for modules with standard filtrations
  and duals of such is the acyclicity input of that argument (cf. Thm. 6.12).
-/

open CategoryTheory CategoryTheory.Limits Module LieModule LieModule.ChevalleyEilenberg

noncomputable section

universe u

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

variable (M N : Type u) [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M] [AddCommGroup N] [Module K N]
  [LieRingModule P.KacMoodyAlgebra N] [LieModule K P.KacMoodyAlgebra N]

/-- `RelAcyclic P M N`: the relative cohomology `Hⁿ(𝔤, 𝔥; Hom_K(M, N))` vanishes for `n > 0`. -/
def RelAcyclic : Prop :=
  ∀ n : ℕ, IsZero (relCohomology K P.KacMoodyAlgebra (M →ₗ[K] N) (Set.range (h P)) (n + 1))

variable {P M N}

omit [CharZero K] in
/-- `RelAcyclic` is invariant under isomorphisms in both variables. -/
theorem RelAcyclic.congr {M' N' : Type u} [AddCommGroup M'] [Module K M']
    [LieRingModule P.KacMoodyAlgebra M'] [LieModule K P.KacMoodyAlgebra M'] [AddCommGroup N']
    [Module K N'] [LieRingModule P.KacMoodyAlgebra N'] [LieModule K P.KacMoodyAlgebra N']
    (e : M ≃ₗ⁅K,P.KacMoodyAlgebra⁆ M') (e' : N ≃ₗ⁅K,P.KacMoodyAlgebra⁆ N')
    (hMN : RelAcyclic P M N) : RelAcyclic P M' N' :=
  fun n ↦ (hMN n).of_iso
    (relCohomologyCongr (Set.range (h P)) (LieModuleHom.homCongr e e') (n + 1)).symm

omit [CharZero K] in
/-- `RelAcyclic P M N` holds when `Hom_K(M, N) = 0`. -/
theorem relAcyclic_of_subsingleton [Subsingleton (M →ₗ[K] N)] : RelAcyclic P M N := fun _ ↦
  isZero_relCohomology_succ fun _ _ _ ↦ ⟨0, zero_mem _, Subsingleton.elim _ _⟩

variable (P) in
/-- **`Hⁿ(𝔤, 𝔥; Hom_K(M(λ), M(μ)^∨)) = 0` for `n > 0`**, for `𝔫₋` finite-dimensional. -/
theorem relAcyclic_verma_restrictedDual [Finite (NegRootIndex P)] (Λ μ : Dual K H) :
    RelAcyclic P (VermaModule P Λ) (restrictedDual P (VermaModule P μ)) := fun _ ↦
  isZero_relCohomology_succ fun _ hf hδ ↦ exists_δ_eq_relVerma P Λ μ hf hδ

/-! ### Standard filtrations -/

section Filtration

variable {X : Type u} [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]

omit [CharZero K] in
/-- A step `N₀ ⊆ N₁` of a standard filtration gives an exact sequence `N₀ → N₁ → M(μ)`. -/
theorem exact_inclusion_stdStepMap {N₀ N₁ : LieSubmodule K P.KacMoodyAlgebra X} {μ : Dual K H}
    (hle : N₀ ≤ N₁)
    (e : VermaModule P μ ≃ₗ⁅K,P.KacMoodyAlgebra⁆ N₁.map (LieSubmodule.Quotient.mk' N₀)) :
    Function.Exact (LieSubmodule.inclusion hle) (stdStepMap hle e) := fun y ↦ by
  rw [stdStepMap_eq_zero_iff]
  exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨x, rfl⟩; exact x.2⟩

/-- Propagation of `RelAcyclic` along a standard filtration of the first variable. -/
theorem RelAcyclic.of_isStdFiltered_left (hX : IsCategoryO P X)
    {N : LieSubmodule K P.KacMoodyAlgebra X}
    {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s)
    (hs : ∀ μ ∈ s, RelAcyclic P (VermaModule P μ) M) : RelAcyclic P N M := by
  induction hN with
  | bot =>
    have : Subsingleton (↥(⊥ : LieSubmodule K P.KacMoodyAlgebra X) →ₗ[K] M) :=
      ⟨fun f g ↦ LinearMap.ext fun x ↦ by
        rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
    exact relAcyclic_of_subsingleton
  | @step N₀ N₁ s₀ μ _ hle he ih =>
    obtain ⟨e⟩ := he
    refine fun n ↦ isZero_relCohomology_hom_of_shortExact_left (h P)
      (iSup_weightSpaceOfMap_lieSubmodule hX N₁)
      (VermaModule.isCategoryO P μ).iSup_weightSpaceOfMap_eq_top
      (LieSubmodule.inclusion_injective hle) (exact_inclusion_stdStepMap hle e)
      (surjective_stdStepMap hle e)
      (ih (fun ν hν ↦ hs ν (Multiset.mem_cons_of_mem hν)) n)
      (hs μ (Multiset.mem_cons_self _ _) n)

/-- Propagation of `RelAcyclic P M N^∨` along a standard filtration of `N`. -/
theorem RelAcyclic.of_isStdFiltered_right (hX : IsCategoryO P X)
    {N : LieSubmodule K P.KacMoodyAlgebra X}
    {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s)
    (hs : ∀ μ ∈ s, RelAcyclic P M (restrictedDual P (VermaModule P μ))) :
    RelAcyclic P M (restrictedDual P N) := by
  induction hN with
  | bot =>
    have : Subsingleton (restrictedDual P (⊥ : LieSubmodule K P.KacMoodyAlgebra X)) :=
      ⟨fun φ ψ ↦ restrictedDual_ext P fun x ↦ by
        rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
    have : Subsingleton (M →ₗ[K] restrictedDual P (⊥ : LieSubmodule K P.KacMoodyAlgebra X)) :=
      ⟨fun f g ↦ LinearMap.ext fun _ ↦ Subsingleton.elim _ _⟩
    exact relAcyclic_of_subsingleton
  | @step N₀ N₁ s₀ μ _ hle he ih =>
    obtain ⟨e⟩ := he
    have h₀ := iSup_weightSpaceOfMap_lieSubmodule hX N₀
    have h₁ := iSup_weightSpaceOfMap_lieSubmodule hX N₁
    have hV := (VermaModule.isCategoryO P μ).iSup_weightSpaceOfMap_eq_top
    refine fun n ↦ isZero_relCohomology_hom_of_shortExact_right (h P)
      (isCategoryO_restrictedDual (hX.lieSubmodule N₁)).iSup_weightSpaceOfMap_eq_top
      (isCategoryO_restrictedDual (hX.lieSubmodule N₀)).iSup_weightSpaceOfMap_eq_top
      (injective_restrictedDualMap P _ (surjective_stdStepMap hle e))
      (exact_restrictedDualMap P h₁ hV (exact_inclusion_stdStepMap hle e))
      (surjective_restrictedDualMap P h₀ h₁ _ (LieSubmodule.inclusion_injective hle))
      (hs μ (Multiset.mem_cons_self _ _) n)
      (ih (fun ν hν ↦ hs ν (Multiset.mem_cons_of_mem hν)) n)

variable (P) in
/-- **`Hⁿ(𝔤, 𝔥; Hom_K(N, N'^∨)) = 0` for `n > 0`** when `N ⊆ X` and `N' ⊆ Y` have standard
filtrations, `X`, `Y` in `𝒪` and `𝔫₋` finite-dimensional. -/
theorem relAcyclic_restrictedDual_of_isStdFiltered [Finite (NegRootIndex P)] {Y : Type u}
    [AddCommGroup Y] [Module K Y] [LieRingModule P.KacMoodyAlgebra Y]
    [LieModule K P.KacMoodyAlgebra Y] (hX : IsCategoryO P X) (hY : IsCategoryO P Y)
    {N : LieSubmodule K P.KacMoodyAlgebra X} {N' : LieSubmodule K P.KacMoodyAlgebra Y}
    {s s' : Multiset (Dual K H)} (hN : IsStdFiltered P N s) (hN' : IsStdFiltered P N' s') :
    RelAcyclic P N (restrictedDual P N') :=
  RelAcyclic.of_isStdFiltered_left hX hN fun Λ _ ↦
    RelAcyclic.of_isStdFiltered_right hY hN' fun μ _ ↦
      relAcyclic_verma_restrictedDual P Λ μ

end Filtration

end Matrix.Realization.KacMoodyAlgebra
