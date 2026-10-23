/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.RelativeCochain
import LieLean.Algebra.Lie.RelativeExt
import Mathlib.Algebra.Homology.HomologySequence

/-!
# Relative cohomology with coefficients in `Hom_K(M, N)`

Let `L` be a Lie algebra over a field `K` and `φ : H → L` a linear map; write `S = φ(H)`. For
`L`-modules `M` and `N`, `Hom_K(M, N)` is an `L`-module, and its relative cohomology
`H^n(L, S; Hom_K(M, N))` is functorial in both variables.

A short exact sequence `0 → M₁ → M₂ → M₃ → 0` of modules that are sums of their weight spaces
for `φ` splits `S`-equivariantly (`LieModule.ExtOne.exists_splitData`), hence so does
`0 → Hom(M₃, N) → Hom(M₂, N) → Hom(M₁, N) → 0`, and the relative cochains form a short exact
sequence of complexes. In particular vanishing of `H^n` in the outer terms gives vanishing in the
middle term, in either variable.

## Main definitions

* `LieModule.ChevalleyEilenberg.relCohomology`: `H^n(L, S; N)`.
* `LieModuleHom.homPrecomp`, `LieModuleHom.homPostcomp`: functoriality of `Hom_K(-, -)`.

## Main results

* `LieModule.ChevalleyEilenberg.homPrecomp_shortExact`,
  `LieModule.ChevalleyEilenberg.homPostcomp_shortExact`: the short exact sequences of relative
  cochain complexes.
* `LieModule.ChevalleyEilenberg.isZero_relCohomology_hom_of_shortExact_left`,
  `LieModule.ChevalleyEilenberg.isZero_relCohomology_hom_of_shortExact_right`: vanishing in the
  middle term.
* `LieModule.ChevalleyEilenberg.isZero_relCohomology_succ`: vanishing from solvability of
  `δ g = f` for relative cocycles.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Thm. 6.15 (a), where these are the dimension-shifting inputs.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w

/-! ### Functoriality of `Hom_K(-, -)` -/

namespace LieModuleHom

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
  {M₁ M₂ N₁ N₂ : Type*} [AddCommGroup M₁] [Module K M₁] [LieRingModule L M₁] [LieModule K L M₁]
  [AddCommGroup M₂] [Module K M₂] [LieRingModule L M₂] [LieModule K L M₂]
  [AddCommGroup N₁] [Module K N₁] [LieRingModule L N₁] [LieModule K L N₁]
  [AddCommGroup N₂] [Module K N₂] [LieRingModule L N₂] [LieModule K L N₂]

variable (N₁) in
/-- Precomposition `Hom_K(M₂, N) → Hom_K(M₁, N)`, `f ↦ f ∘ g`, as a morphism of `L`-modules. -/
def homPrecomp (g : M₁ →ₗ⁅K,L⁆ M₂) : (M₂ →ₗ[K] N₁) →ₗ⁅K,L⁆ (M₁ →ₗ[K] N₁) where
  toLinearMap := LinearMap.lcomp K N₁ (g : M₁ →ₗ[K] M₂)
  map_lie' {x f} := LinearMap.ext fun m ↦ by
    simp [LieHom.lie_apply]

@[simp] lemma homPrecomp_apply (g : M₁ →ₗ⁅K,L⁆ M₂) (f : M₂ →ₗ[K] N₁) :
    homPrecomp N₁ g f = f ∘ₗ (g : M₁ →ₗ[K] M₂) := rfl

variable (M₁) in
/-- Postcomposition `Hom_K(M, N₁) → Hom_K(M, N₂)`, `f ↦ g ∘ f`, as a morphism of `L`-modules. -/
def homPostcomp (g : N₁ →ₗ⁅K,L⁆ N₂) : (M₁ →ₗ[K] N₁) →ₗ⁅K,L⁆ (M₁ →ₗ[K] N₂) where
  toLinearMap := LinearMap.llcomp K M₁ N₁ N₂ (g : N₁ →ₗ[K] N₂)
  map_lie' {x f} := LinearMap.ext fun m ↦ by
    simp [LieHom.lie_apply]

@[simp] lemma homPostcomp_apply (g : N₁ →ₗ⁅K,L⁆ N₂) (f : M₁ →ₗ[K] N₁) :
    homPostcomp M₁ g f = (g : N₁ →ₗ[K] N₂) ∘ₗ f := rfl

/-- `Hom_K(M₁, N₁) ≅ Hom_K(M₂, N₂)` for isomorphisms `M₁ ≅ M₂`, `N₁ ≅ N₂`. -/
def homCongr (e : M₁ ≃ₗ⁅K,L⁆ M₂) (e' : N₁ ≃ₗ⁅K,L⁆ N₂) :
    (M₁ →ₗ[K] N₁) ≃ₗ⁅K,L⁆ (M₂ →ₗ[K] N₂) :=
  { LinearEquiv.arrowCongr (e : M₁ ≃ₗ[K] M₂) (e' : N₁ ≃ₗ[K] N₂) with
    map_lie' := fun {x f} ↦ LinearMap.ext fun m ↦ by
      have h : e.toLinearEquiv.symm ⁅x, m⁆ = ⁅x, e.toLinearEquiv.symm m⁆ := e.symm.map_lie x m
      change (e' : N₁ →ₗ[K] N₂) (⁅x, f⁆ (e.toLinearEquiv.symm m)) =
        ⁅x, e' (f (e.toLinearEquiv.symm m))⁆ - e' (f (e.toLinearEquiv.symm ⁅x, m⁆))
      rw [LieHom.lie_apply, h, map_sub]
      exact congrArg (· - _) (e'.map_lie x _) }

end LieModuleHom

namespace LieModule.ChevalleyEilenberg

open LieModuleHom

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

variable (K L) in
/-- The relative Lie algebra cohomology `H^n(L, S; N)`. -/
abbrev relCohomology (N : Type w) [AddCommGroup N] [Module K N] [LieRingModule L N]
    [LieModule K L N] (S : Set L) (n : ℕ) :=
  (relCochainComplex K L N S).homology n

section Vanishing

variable {N : Type w} [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  {S : Set L}

/-- If every relative cocycle of degree `k + 1` is the coboundary of a relative cochain, then
`H^{k+1}(L, S; N) = 0`. -/
theorem isZero_relCohomology_succ {k : ℕ}
    (h : ∀ f ∈ relCochains K L N S (k + 1), δ K L N (k + 1) f = 0 →
      ∃ g ∈ relCochains K L N S k, δ K L N k g = f) :
    IsZero (relCohomology K L N S (k + 1)) := by
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  rw [HomologicalComplex.exactAt_iff' _ k (k + 1) (k + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro f₀ hf
  let f : relCochains K L N S (k + 1) := f₀
  have h1 : relδ K L N S (k + 1) f = 0 := by
    have h := hf
    simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'_obj_g,
      relCochainComplex_d] at h
    exact h
  obtain ⟨g, hg, hgf⟩ := h f f.2 (congrArg Subtype.val h1)
  refine ⟨⟨g, hg⟩, ?_⟩
  have h2 : relδ K L N S k ⟨g, hg⟩ = f := Subtype.ext hgf
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'_obj_f,
    relCochainComplex_d]
  exact h2

end Vanishing

section Congr

variable {N N' : Type w} [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [AddCommGroup N'] [Module K N'] [LieRingModule L N'] [LieModule K L N'] (S : Set L)

/-- Isomorphic coefficients have isomorphic relative cohomology. -/
def relCohomologyCongr (e : N ≃ₗ⁅K,L⁆ N') (n : ℕ) :
    relCohomology K L N S n ≅ relCohomology K L N' S n :=
  HomologicalComplex.homologyMapIso
    { hom := relCochainComplexMap S e.toLieModuleHom
      inv := relCochainComplexMap S e.symm.toLieModuleHom
      hom_inv_id := by
        ext k f : 3
        exact Subtype.ext (LinearMap.ext fun ω ↦ e.symm_apply_apply _)
      inv_hom_id := by
        ext k f : 3
        exact Subtype.ext (LinearMap.ext fun ω ↦ e.apply_symm_apply _) } n

end Congr

/-! ### Short exact sequences in either variable -/

section ShortExact

variable {H : Type*} [AddCommGroup H] [Module K H] (φ : H →ₗ[K] L)

section Left

variable {M₁ M₂ M₃ N : Type w} [AddCommGroup M₁] [Module K M₁] [LieRingModule L M₁]
  [LieModule K L M₁] [AddCommGroup M₂] [Module K M₂] [LieRingModule L M₂] [LieModule K L M₂]
  [AddCommGroup M₃] [Module K M₃] [LieRingModule L M₃] [LieModule K L M₃]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  {g₁ : M₁ →ₗ⁅K,L⁆ M₂} {g₂ : M₂ →ₗ⁅K,L⁆ M₃}

/-- A short exact sequence `0 → M₁ → M₂ → M₃ → 0` of weight modules gives a short exact sequence
of relative cochain complexes with coefficients `Hom(M₃, N) → Hom(M₂, N) → Hom(M₁, N)`. -/
theorem homPrecomp_shortExact (hM₂ : ⨆ μ, weightSpaceOfMap M₂ φ μ = ⊤)
    (hM₃ : ⨆ μ, weightSpaceOfMap M₃ φ μ = ⊤) (hinj : Function.Injective g₁)
    (hex : Function.Exact g₁ g₂) (hsurj : Function.Surjective g₂) :
    (ShortComplex.mk (relCochainComplexMap (Set.range φ) (homPrecomp N g₂))
      (relCochainComplexMap (Set.range φ) (homPrecomp N g₁)) (by
        ext k f : 3
        refine Subtype.ext (LinearMap.ext fun ω ↦ LinearMap.ext fun m ↦ ?_)
        change (f.1 ω) (g₂ (g₁ m)) = 0
        rw [hex.apply_apply_eq_zero, map_zero])).ShortExact := by
  obtain ⟨T⟩ := ExtOne.exists_splitData φ hM₂ hM₃ hinj hsurj fun b ↦ (hex b).trans
    (by simp [eq_comm])
  refine relCochainComplex_shortExact (fun f f' hff' ↦ LinearMap.ext fun c ↦ ?_)
    (fun f ↦ ⟨fun hf ↦ ⟨f ∘ₗ T.s, LinearMap.ext fun m ↦ ?_⟩, ?_⟩)
    ((LinearMap.lcomp K N T.r)) (fun f ↦ LinearMap.ext fun m ↦ ?_) ?_
  · obtain ⟨m, rfl⟩ := hsurj c
    exact LinearMap.congr_fun hff' m
  · have h1 := T.i_r_add_s_p m
    have h2 : f (g₁ (T.r m)) = 0 := LinearMap.congr_fun hf (T.r m)
    change f (T.s (g₂ m)) = f m
    conv_rhs => rw [← h1]
    rw [map_add, h2, zero_add]
  · rintro ⟨f', rfl⟩
    exact LinearMap.ext fun m ↦ by
      change f' (g₂ (g₁ m)) = 0
      rw [hex.apply_apply_eq_zero, map_zero]
  · change f (T.r (g₁ m)) = f m
    rw [T.r_i]
  · rintro _ ⟨a, rfl⟩ f
    refine LinearMap.ext fun m ↦ ?_
    change ⁅φ a, f⁆ (T.r m) = ⁅φ a, f (T.r m)⁆ - f (T.r ⁅φ a, m⁆)
    rw [LieHom.lie_apply, T.r_mem a m]

/-- Vanishing of `H^n(L, S; Hom(-, N))` on the outer terms of a short exact sequence of weight
modules gives vanishing on the middle term. -/
theorem isZero_relCohomology_hom_of_shortExact_left (hM₂ : ⨆ μ, weightSpaceOfMap M₂ φ μ = ⊤)
    (hM₃ : ⨆ μ, weightSpaceOfMap M₃ φ μ = ⊤) (hinj : Function.Injective g₁)
    (hex : Function.Exact g₁ g₂) (hsurj : Function.Surjective g₂) {n : ℕ}
    (h₁ : IsZero (relCohomology K L (M₁ →ₗ[K] N) (Set.range φ) n))
    (h₃ : IsZero (relCohomology K L (M₃ →ₗ[K] N) (Set.range φ) n)) :
    IsZero (relCohomology K L (M₂ →ₗ[K] N) (Set.range φ) n) :=
  ((homPrecomp_shortExact (N := N) φ hM₂ hM₃ hinj hex hsurj).homology_exact₂ n).isZero_X₂
    (h₃.eq_of_src _ _) (h₁.eq_of_tgt _ _)

end Left

section Right

variable {M N₁ N₂ N₃ : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M]
  [LieModule K L M] [AddCommGroup N₁] [Module K N₁] [LieRingModule L N₁] [LieModule K L N₁]
  [AddCommGroup N₂] [Module K N₂] [LieRingModule L N₂] [LieModule K L N₂]
  [AddCommGroup N₃] [Module K N₃] [LieRingModule L N₃] [LieModule K L N₃]
  {g₁ : N₁ →ₗ⁅K,L⁆ N₂} {g₂ : N₂ →ₗ⁅K,L⁆ N₃}

/-- A short exact sequence `0 → N₁ → N₂ → N₃ → 0` of weight modules gives a short exact sequence
of relative cochain complexes with coefficients `Hom(M, N₁) → Hom(M, N₂) → Hom(M, N₃)`. -/
theorem homPostcomp_shortExact (hN₂ : ⨆ μ, weightSpaceOfMap N₂ φ μ = ⊤)
    (hN₃ : ⨆ μ, weightSpaceOfMap N₃ φ μ = ⊤) (hinj : Function.Injective g₁)
    (hex : Function.Exact g₁ g₂) (hsurj : Function.Surjective g₂) :
    (ShortComplex.mk (relCochainComplexMap (Set.range φ) (homPostcomp M g₁))
      (relCochainComplexMap (Set.range φ) (homPostcomp M g₂)) (by
        ext k f : 3
        refine Subtype.ext (LinearMap.ext fun ω ↦ LinearMap.ext fun m ↦ ?_)
        exact hex.apply_apply_eq_zero _)).ShortExact := by
  obtain ⟨T⟩ := ExtOne.exists_splitData φ hN₂ hN₃ hinj hsurj fun b ↦ (hex b).trans
    (by simp [eq_comm])
  refine relCochainComplex_shortExact (fun f f' hff' ↦ LinearMap.ext fun m ↦ hinj ?_)
    (fun f ↦ ⟨fun hf ↦ ⟨(T.r : N₂ →ₗ[K] N₁) ∘ₗ f, LinearMap.ext fun m ↦ ?_⟩, ?_⟩)
    (LinearMap.llcomp K M N₃ N₂ T.s) (fun f ↦ LinearMap.ext fun m ↦ T.p_s _) ?_
  · exact LinearMap.congr_fun hff' m
  · have hfm : g₂ (f m) = 0 := LinearMap.congr_fun hf m
    exact T.i_r_of_p_eq_zero hfm
  · rintro ⟨f', rfl⟩
    exact LinearMap.ext fun m ↦ hex.apply_apply_eq_zero _
  · rintro _ ⟨a, rfl⟩ f
    refine LinearMap.ext fun m ↦ ?_
    change T.s (⁅φ a, f⁆ m) = ⁅φ a, T.s (f m)⁆ - T.s (f ⁅φ a, m⁆)
    rw [LieHom.lie_apply, map_sub, T.s_mem a]

/-- Vanishing of `H^n(L, S; Hom(M, -))` on the outer terms of a short exact sequence of weight
modules gives vanishing on the middle term. -/
theorem isZero_relCohomology_hom_of_shortExact_right (hN₂ : ⨆ μ, weightSpaceOfMap N₂ φ μ = ⊤)
    (hN₃ : ⨆ μ, weightSpaceOfMap N₃ φ μ = ⊤) (hinj : Function.Injective g₁)
    (hex : Function.Exact g₁ g₂) (hsurj : Function.Surjective g₂) {n : ℕ}
    (h₁ : IsZero (relCohomology K L (M →ₗ[K] N₁) (Set.range φ) n))
    (h₃ : IsZero (relCohomology K L (M →ₗ[K] N₃) (Set.range φ) n)) :
    IsZero (relCohomology K L (M →ₗ[K] N₂) (Set.range φ) n) :=
  ((homPostcomp_shortExact (M := M) φ hN₂ hN₃ hinj hex hsurj).homology_exact₂ n).isZero_X₂
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

end Right

end ShortExact

end LieModule.ChevalleyEilenberg
