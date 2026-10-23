/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryODelorme
import LieLean.Algebra.Lie.KacMoody.EnoughInjectives
import LieLean.Algebra.Lie.KacMoody.InjectiveCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.HomologySequence

/-!
# `Extⁿ_𝒪(M(μ), N)` and `𝔫`-cohomology

[HumO] Prop. 6.15 (b): for `N` in `𝒪`, `Extⁿ_𝒪(M(μ), N) ≅ Hⁿ(𝔫, N)_μ`, where `𝔫 = 𝔫₊` and
`Hⁿ(𝔫, N)_μ` is the weight-`μ` part of Chevalley–Eilenberg cohomology (`nPosCohomology`).

The proof is by dimension shifting. Every `N` in `𝒪` embeds into an injective `I = Q^∨` of `𝒪`
(`exists_isInjectiveO_injective`), with `Hⁿ(𝔫, I)_μ = 0` for `n > 0`
(`isZero_nPosCohomology_restrictedDual_directSum`) and `Extⁿ_𝒪(M(μ), I) = 0` for `n > 0`
(`I` is injective in the abelian category `𝒪`, `CategoryO.injective_mk`). The long exact sequences
of `Ext_𝒪(M(μ), -)` and of weight cohomology along `0 → N → I → I/N → 0` then compare both sides
degree by degree, starting from `Hom_𝒪(M(μ), N) ≅ H⁰(𝔫, N)_μ` (`nPosCohomologyZeroEquiv`).
The comparison is of dimensions; both sides are finite-dimensional, which gives the isomorphism.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.CategoryO.injective_mk`: a module in `𝒪` which is injective
  against injections of modules in `𝒪` is injective in the abelian category `𝒪`.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.finrank_ext_verma_eq_finrank_nPosCohomology`:
  `dim Extⁿ_𝒪(M(μ), N) = dim Hⁿ(𝔫, N)_μ`, both finite.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.nonempty_ext_verma_linearEquiv_nPosCohomology`:
  **[HumO] Prop. 6.15 (b)**, `Extⁿ_𝒪(M(μ), N) ≅ Hⁿ(𝔫, N)_μ`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Prop. 6.15. Humphreys works over `ℂ`; here `K` is an algebraically closed
  field of characteristic zero and `𝔤` is of finite type. The isomorphism is obtained by
  comparing dimensions along the long exact sequences, not as a natural isomorphism.
-/

open CategoryTheory Limits LieModule Module LieModule.ChevalleyEilenberg
open scoped TensorProduct

noncomputable section

universe u w

/-! ### Exact sequences of vector spaces -/

section Dimension

variable {K A B C D : Type*} [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B]
  [Module K B] [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]

/-- For an exact sequence `0 → A → B → C → D → 0` of vector spaces with `B`, `C`
finite-dimensional, `dim A + dim C = dim B + dim D`. -/
theorem Module.finrank_add_finrank_of_exact_four [FiniteDimensional K B] [FiniteDimensional K C]
    (f : A →ₗ[K] B) (g : B →ₗ[K] C) (k : C →ₗ[K] D) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hgk : Function.Exact g k) (hk : Function.Surjective k) :
    finrank K A + finrank K C = finrank K B + finrank K D := by
  have hg := LinearMap.finrank_range_add_finrank_ker g
  have hk' := LinearMap.finrank_range_add_finrank_ker k
  rw [LinearMap.exact_iff.mp hfg, LinearMap.finrank_range_of_inj hf] at hg
  rw [LinearMap.exact_iff.mp hgk, LinearMap.range_eq_top.mpr hk, finrank_top] at hk'
  omega

end Dimension

namespace Matrix.Realization.KacMoodyAlgebra

/-! ### Weight cohomology along short exact sequences -/

section Cohomology

variable {ι H K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

variable {V W : Type w} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [AddCommGroup W] [Module K W]
  [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W]

omit [CharZero K] in
/-- A morphism of `𝔤`-modules is compatible with the actions of `𝔥` on `𝔫`-cochains. -/
theorem isEquivariant_nPosDerivAction (g : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) :
    DerivAction.IsEquivariant (nPosDerivAction P V) (nPosDerivAction P W)
      (g.restrictLie (nPos P)) where
  D_eq := rfl
  map_φ a v := g.map_lie (h P a) v

omit [CharZero K] in
/-- Isomorphic `𝔤`-modules have isomorphic weight cohomology `Hⁿ(𝔫, -)_μ`. -/
def nPosCohomologyCongr (e : V ≃ₗ⁅K,P.KacMoodyAlgebra⁆ W) (μ : Dual K H) (n : ℕ) :
    nPosCohomology P V μ n ≅ nPosCohomology P W μ n :=
  HomologicalComplex.homologyMapIso
    { hom := DerivAction.weightComplexMap (isEquivariant_nPosDerivAction P e.toLieModuleHom) μ
      inv := DerivAction.weightComplexMap
        (isEquivariant_nPosDerivAction P e.symm.toLieModuleHom) μ
      hom_inv_id := by
        ext k f : 3
        exact Subtype.ext (LinearMap.ext fun ω ↦ e.symm_apply_apply _)
      inv_hom_id := by
        ext k f : 3
        exact Subtype.ext (LinearMap.ext fun ω ↦ e.apply_symm_apply _) } n

variable {V₁ V₂ V₃ : Type w} [AddCommGroup V₁] [Module K V₁]
  [LieRingModule P.KacMoodyAlgebra V₁] [LieModule K P.KacMoodyAlgebra V₁] [AddCommGroup V₂]
  [Module K V₂] [LieRingModule P.KacMoodyAlgebra V₂] [LieModule K P.KacMoodyAlgebra V₂]
  [AddCommGroup V₃] [Module K V₃] [LieRingModule P.KacMoodyAlgebra V₃]
  [LieModule K P.KacMoodyAlgebra V₃]
  {g₁ : V₁ →ₗ⁅K,P.KacMoodyAlgebra⁆ V₂} {g₂ : V₂ →ₗ⁅K,P.KacMoodyAlgebra⁆ V₃}

/-- A short exact sequence `0 → V₁ → V₂ → V₃ → 0` of `𝔤`-modules, `V₂` a sum of weight spaces,
gives a short exact sequence of weight-`μ` cochain complexes of `𝔫`. -/
theorem nPosWeightComplex_shortExact (hinj : Function.Injective g₁) (hex : Function.Exact g₁ g₂)
    (hsurj : Function.Surjective g₂) (hV₂ : ⨆ ν, weightSpaceOfMap V₂ (h P) ν = ⊤)
    (μ : Dual K H) :
    (ShortComplex.mk (DerivAction.weightComplexMap (isEquivariant_nPosDerivAction P g₁) μ)
      (DerivAction.weightComplexMap (isEquivariant_nPosDerivAction P g₂) μ) (by
        ext k f : 3
        exact Subtype.ext (LinearMap.ext fun ω ↦ hex.apply_apply_eq_zero _))).ShortExact :=
  DerivAction.weightComplex_shortExact (bL := nPosBasis P) (γ := fun x ↦ x.root)
    (isEquivariant_nPosDerivAction P g₁) (isEquivariant_nPosDerivAction P g₂)
    (fun x ↦ nPosBasis_mem_weightSpaceOf P V₁ x) hinj hex
    (fun _ _ hx ↦ ExtOne.exists_mem_weightSpaceOfMap_of_surjective (h P) hV₂ hsurj hx) μ

end Cohomology

namespace CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P

/-! ### Injectives -/

/-- A module in `𝒪` which is injective in the sense of `IsInjectiveO` is injective in the abelian
category `𝒪`. -/
theorem injective_mk (M : Type u) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M] (hM : IsCategoryO P M)
    (hS : ∃ S : Finset M, LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤)
    (hinj : IsInjectiveO.{u} P M) : Injective (mk M hM hS) where
  factors {X Y} g f _ := by
    obtain ⟨ψ, hψ⟩ := hinj X.property.1 Y.property.1 (toLieModuleHom f.hom) (injective_of_mono f)
      ((ofLieEquiv (P := P) M).symm.toLieModuleHom.comp (toLieModuleHom g.hom))
    refine ⟨(IsObj.{u} P).homMk (ofLieModuleHom
      ((ofLieEquiv (P := P) M).toLieModuleHom.comp ψ)), ?_⟩
    ext m
    exact (congrArg (ofLieEquiv (P := P) M) (LieModuleHom.congr_fun hψ m)).trans
      ((ofLieEquiv (P := P) M).apply_symm_apply _)

variable (P) in
/-- Every object `Y` of `𝒪` sits in a short exact sequence `0 → Y → J → Z → 0` with `J` injective
in `𝒪` and `Hⁿ(𝔫, J)_μ = 0` for all `μ` and `n > 0`. -/
theorem exists_shortExact_injective (Y : CategoryO.{u} P) :
    ∃ (J Z : CategoryO.{u} P) (f : Y ⟶ J) (g : J ⟶ Z) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧ Injective J ∧
      (∀ (μ : Dual K H) (n : ℕ), 0 < n → IsZero (nPosCohomology P J.obj μ n)) ∧
      ∃ (g₁ : Y.obj →ₗ⁅K,𝔤⁆ J.obj) (g₂ : J.obj →ₗ⁅K,𝔤⁆ Z.obj), Function.Injective g₁ ∧
        Function.Exact g₁ g₂ ∧ Function.Surjective g₂ := by
  have hA : A.IsFiniteCartan := Fact.out
  obtain ⟨S, hS⟩ := Y.property.2
  obtain ⟨κ, _, _, τ, hIO, hIinj, hIfg, e, he⟩ :=
    exists_isInjectiveO_injective.{u, u} P hA Y.property.1 hS
  let I := restrictedDual P (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j))
  let J := mk I hIO hIfg
  let e' : Y.obj →ₗ⁅K,𝔤⁆ J.obj := (ofLieEquiv (P := P) I).toLieModuleHom.comp e
  have he' : Function.Injective e' := (ofLieEquiv (P := P) I).injective.comp he
  let N := e'.range
  have hex : Function.Exact e' (toQuotient J N) := fun x ↦
    (toQuotient_eq_zero_iff J N x).trans (e'.mem_range x)
  let f : Y ⟶ J := (IsObj.{u} P).homMk (ofLieModuleHom e')
  let g : J ⟶ ofQuotient J N := (IsObj.{u} P).homMk (ofLieModuleHom (toQuotient J N))
  have w : f ≫ g = 0 := by
    ext y
    exact hex.apply_apply_eq_zero y
  have hQ : IsCategoryO P (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j)) :=
    IsCategoryO.directSum _ fun j ↦ isCategoryO_projectiveCoverAmbient P hA _ _
  refine ⟨J, ofQuotient J N, f, g, w, shortExact_of_lie he' (surjective_toQuotient J N)
    (fun y hy ↦ (hex y).mp hy), injective_mk I hIO hIfg hIinj, fun μ n hn ↦ ?_,
    e', toQuotient J N, he', hex, surjective_toQuotient J N⟩
  -- the vanishing for `I`, first with `projectiveCoverAmbient'` unfolded
  have hI := isZero_nPosCohomology_restrictedDual_directSum P
    (fun j ↦ τ j + (projectiveCoverShift P hA (τ j) : K) • P.rho)
    (fun j ↦ Module.Dual K (IrreducibleModule P ((projectiveCoverShift P hA (τ j) : K) • P.rho)))
    hQ.iSup_weightSpaceOfMap_eq_top μ hn
  have hI' : IsZero (nPosCohomology P (restrictedDual P (DirectSum κ fun j ↦
      VermaModule P (τ j + (projectiveCoverShift P hA (τ j) : K) • P.rho) ⊗[K]
        Module.Dual K (IrreducibleModule P ((projectiveCoverShift P hA (τ j) : K) • P.rho))))
      μ n) := hI
  exact (show IsZero (nPosCohomology P I μ n) from hI').of_iso
    (nPosCohomologyCongr P (ofLieEquiv (P := P) I) μ n).symm

/-! ### Dimension shifting -/

variable (μ : Dual K H)

/-- `Ext⁰_𝒪(M(μ), Y) ≅ H⁰(𝔫, Y)_μ`: both are `Hom_𝔤(M(μ), Y)`. -/
def extZeroEquivNPosCohomology (Y : CategoryO.{u} P) :
    Abelian.Ext.{u} (verma P μ) Y 0 ≃ₗ[K] nPosCohomology P Y.obj μ 0 :=
  (Abelian.Ext.linearEquiv₀ (R := K)).trans ((homEquivLie (verma P μ) Y).trans
    ((lieModuleHomCongr P (ofLieEquiv (P := P) (VermaModule P μ)).symm LieModuleEquiv.refl).trans
      (nPosCohomologyZeroEquiv P Y.obj μ).symm))

/-- The weight-cohomology map `Hⁿ(𝔫, V)_μ → Hⁿ(𝔫, W)_μ` of a morphism of `𝔤`-modules. -/
abbrev nPosCohomologyMap {V W : Type u} [AddCommGroup V] [Module K V] [LieRingModule 𝔤 V]
    [LieModule K 𝔤 V] [AddCommGroup W] [Module K W] [LieRingModule 𝔤 W] [LieModule K 𝔤 W]
    (g : V →ₗ⁅K,𝔤⁆ W) (n : ℕ) : nPosCohomology P V μ n →ₗ[K] nPosCohomology P W μ n :=
  (HomologicalComplex.homologyMap
    (DerivAction.weightComplexMap (isEquivariant_nPosDerivAction P g) μ) n).hom

/-- **Dimension shifting.** For every `n` and every `Y` in `𝒪`, `Hⁿ(𝔫, Y)_μ` is
finite-dimensional, of the same dimension as `Extⁿ_𝒪(M(μ), Y)`. -/
theorem finiteDimensional_nPosCohomology_and_finrank_eq (n : ℕ) :
    ∀ Y : CategoryO.{u} P, FiniteDimensional K (nPosCohomology P Y.obj μ n) ∧
      finrank K (Abelian.Ext.{u} (verma P μ) Y n) = finrank K (nPosCohomology P Y.obj μ n) := by
  induction n with
  | zero =>
    intro Y
    exact ⟨LinearEquiv.finiteDimensional (extZeroEquivNPosCohomology μ Y),
      (extZeroEquivNPosCohomology μ Y).finrank_eq⟩
  | succ n ih =>
    intro Y
    obtain ⟨J, Z, f, g, w, hS, hJ, hJ0, g₁, g₂, hg₁, hex, hg₂⟩ := exists_shortExact_injective P Y
    have hT := nPosWeightComplex_shortExact P hg₁ hex hg₂
      J.property.1.iSup_weightSpaceOfMap_eq_top μ
    have hrel : (ComplexShape.up ℕ).Rel n (n + 1) := rfl
    let δ := (hT.δ n (n + 1) hrel).hom
    have := hJ
    have hJext : ∀ (m : ℕ) (x : Abelian.Ext.{u} (verma P μ) J (m + 1)), x = 0 :=
      fun m x ↦ Abelian.Ext.eq_zero_of_injective x
    -- `δ : Hⁿ(Z) → Hⁿ⁺¹(Y)` is surjective
    have hδ : Function.Surjective δ := (ModuleCat.epi_iff_surjective _).mp
      (hT.epi_δ n (n + 1) hrel (hJ0 μ (n + 1) n.succ_pos))
    have hfd : FiniteDimensional K (nPosCohomology P Y.obj μ (n + 1)) :=
      have := (ih Z).1
      Module.Finite.of_surjective δ hδ
    refine ⟨hfd, ?_⟩
    -- the connecting map of `Ext` is surjective
    have hc : Function.Surjective (connectingLinear (verma P μ) hS n) := fun x ↦
      (exact_connectingLinear_postcompLinear (verma P μ) hS n x).mp (hJext n _)
    cases n with
    | zero =>
      -- `0 → Hom(M, Y) → Hom(M, J) → Hom(M, Z) → Ext¹(M, Y) → 0`
      have hE := Module.finrank_add_finrank_of_exact_four (postcompLinear (verma P μ) f 0)
        (postcompLinear (verma P μ) g 0) (connectingLinear (verma P μ) hS 0)
        (injective_postcompLinear_zero (verma P μ) hS) (exact_postcompLinear (verma P μ) hS 0)
        (exact_connectingLinear (verma P μ) hS 0) hc
      -- `0 → H⁰(Y) → H⁰(J) → H⁰(Z) → H¹(Y) → 0`
      have hmono : Mono (HomologicalComplex.homologyMap
          (DerivAction.weightComplexMap (isEquivariant_nPosDerivAction P g₁) μ) 0) := by
        have := hT.mono_f
        have h := CochainComplex.isoHomologyπ₀_inv_naturality
          (DerivAction.weightComplexMap (isEquivariant_nPosDerivAction P g₁) μ)
        have : Mono (HomologicalComplex.homologyMap
            (DerivAction.weightComplexMap (isEquivariant_nPosDerivAction P g₁) μ) 0 ≫
              (CochainComplex.isoHomologyπ₀ _).inv) := by
          rw [h]
          infer_instance
        exact mono_of_mono _ (CochainComplex.isoHomologyπ₀ _).inv
      have := (ih J).1
      have := (ih Z).1
      have hH := Module.finrank_add_finrank_of_exact_four (nPosCohomologyMap μ g₁ 0)
        (nPosCohomologyMap μ g₂ 0) δ ((ModuleCat.mono_iff_injective _).mp hmono)
        (LinearMap.exact_iff.mpr ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
          (hT.homology_exact₂ 0)).symm)
        (LinearMap.exact_iff.mpr ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
          (hT.homology_exact₃ 0 1 hrel)).symm) hδ
      change _ + finrank K (nPosCohomology P Z.obj μ 0) =
        _ + finrank K (nPosCohomology P Y.obj μ (0 + 1)) at hH
      rw [(ih Y).2, (ih J).2, (ih Z).2] at hE
      change _ = _ + finrank K (Abelian.Ext.{u} (verma P μ) Y (0 + 1)) at hE
      omega
    | succ n =>
      -- `Extⁿ⁺¹(M, Z) ≅ Extⁿ⁺²(M, Y)` and `Hⁿ⁺¹(Z) ≅ Hⁿ⁺²(Y)`
      have hci : Function.Injective (connectingLinear (verma P μ) hS (n + 1)) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.exact_iff.mp (exact_connectingLinear _ hS _)]
        exact eq_bot_iff.mpr fun x ⟨y, hy⟩ ↦ by
          rw [← hy, hJext n y, map_zero]
          exact Submodule.zero_mem _
      have := hT.isIso_δ (n + 1) (n + 1 + 1) hrel (hJ0 μ (n + 1) n.succ_pos)
        (hJ0 μ (n + 1 + 1) (n + 1).succ_pos)
      rw [← (LinearEquiv.ofBijective _ ⟨hci, hc⟩).finrank_eq, (ih Z).2,
        (asIso (hT.δ (n + 1) (n + 1 + 1) hrel)).toLinearEquiv.finrank_eq]

/-- `dim Extⁿ_𝒪(M(μ), Y) = dim Hⁿ(𝔫, Y)_μ` ([HumO] Prop. 6.15 (b), dimension form). -/
theorem finrank_ext_verma_eq_finrank_nPosCohomology (Y : CategoryO.{u} P) (n : ℕ) :
    finrank K (Abelian.Ext.{u} (verma P μ) Y n) = finrank K (nPosCohomology P Y.obj μ n) :=
  (finiteDimensional_nPosCohomology_and_finrank_eq μ n Y).2

/-- **[HumO] Prop. 6.15 (b)**: `Extⁿ_𝒪(M(μ), N) ≅ Hⁿ(𝔫, N)_μ` for `N` in `𝒪`. -/
theorem nonempty_ext_verma_linearEquiv_nPosCohomology (Y : CategoryO.{u} P) (n : ℕ) :
    Nonempty (Abelian.Ext.{u} (verma P μ) Y n ≃ₗ[K] nPosCohomology P Y.obj μ n) :=
  have := (finiteDimensional_nPosCohomology_and_finrank_eq μ n Y).1
  ⟨LinearEquiv.ofFinrankEq _ _ (finrank_ext_verma_eq_finrank_nPosCohomology μ Y n)⟩

/-- [HumO] Prop. 6.15 (b) for a module `N` in `𝒪`: `Extⁿ_𝒪(M(μ), N) ≅ Hⁿ(𝔫, N)_μ`. -/
theorem nonempty_ext_verma_mk_linearEquiv_nPosCohomology (N : Type u) [AddCommGroup N]
    [Module K N] [LieRingModule 𝔤 N] [LieModule K 𝔤 N] (hN : IsCategoryO P N)
    (hS : ∃ S : Finset N, LieSubmodule.lieSpan K 𝔤 (S : Set N) = ⊤) (n : ℕ) :
    Nonempty (Abelian.Ext.{u} (verma P μ) (mk N hN hS) n ≃ₗ[K] nPosCohomology P N μ n) :=
  let ⟨e⟩ := nonempty_ext_verma_linearEquiv_nPosCohomology μ (mk N hN hS) n
  ⟨e.trans (nPosCohomologyCongr P (ofLieEquiv (P := P) N).symm μ n).toLinearEquiv⟩

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
