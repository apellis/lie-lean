/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOExtCohomology
import LieLean.Algebra.Lie.KacMoody.DimensionFormula
import LieLean.Algebra.Lie.KacMoody.ProjectiveStdFiltration
import LieLean.Algebra.Lie.KacMoody.RelativeStdFiltration

/-!
# `Extⁿ_𝒪(M, N)` and relative Lie algebra cohomology

[HumO] Thm. 6.15 (a): for `M`, `N` in `𝒪`, `Extⁿ_𝒪(M, N) ≅ Hⁿ(𝔤, 𝔥; Hom_K(M, N))`.

The proof is by dimension shifting in both variables.

* The injectives `I = Q^∨` of `exists_isInjectiveO_injective` (`Q` a finitely generated
  projective) are acyclic: `Hⁿ(𝔤, 𝔥; Hom_K(M, I)) = 0` for `n > 0` and every finitely generated
  `M` in `𝒪` (`relAcyclic_of_isInjectiveO`). For `M` projective both `M` and `Q` have standard
  filtrations, and the vanishing is `relAcyclic_restrictedDual_of_isStdFiltered`. A general `M` is
  a quotient `0 → K → P → M → 0` of a projective `P`; the long exact sequence in the first
  variable shifts the degree, and in degree one the dimensions of
  `0 → Hom_𝔤(M, I) → Hom_𝔤(P, I) → Hom_𝔤(K, I) → 0` (exact since `I` is injective) force
  `H¹(𝔤, 𝔥; Hom_K(M, I)) = 0`.
* For `N` in `𝒪`, embed `0 → N → I → I/N → 0` and compare the long exact sequences of
  `Ext_𝒪(M, -)` and of relative cohomology, starting from
  `Ext⁰_𝒪(M, N) = Hom_𝔤(M, N) = H⁰(𝔤, 𝔥; Hom_K(M, N))`, as for [HumO] Prop. 6.15 (b).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.relCohomologyZeroHomEquiv`:
  `H⁰(𝔤, 𝔥; Hom_K(M, N)) ≅ Hom_𝔤(M, N)`.
* `Matrix.Realization.KacMoodyAlgebra.relAcyclic_of_isInjectiveO`: an injective of `𝒪` which is
  acyclic against projectives is acyclic against every finitely generated module of `𝒪`.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.finrank_ext_eq_finrank_relCohomology`:
  `dim Extⁿ_𝒪(M, N) = dim Hⁿ(𝔤, 𝔥; Hom_K(M, N))`, both finite.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.nonempty_ext_linearEquiv_relCohomology`:
  **[HumO] Thm. 6.15 (a)**, `Extⁿ_𝒪(M, N) ≅ Hⁿ(𝔤, 𝔥; Hom_K(M, N))`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Thm. 6.15. Humphreys works over `ℂ` and identifies both sides as derived
  functors; here `K` is an algebraically closed field of characteristic zero, `𝔤` is of finite
  type, and the isomorphism is obtained by comparing dimensions along the long exact sequences,
  not as a natural isomorphism.
-/

open CategoryTheory Limits LieModule Module LieModule.ChevalleyEilenberg

noncomputable section

universe u

/-! ### Dimensions -/

section Dimension

variable {K A B C : Type*} [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B]
  [Module K B] [AddCommGroup C] [Module K C]

/-- If `0 → A → B → C → 0` is a complex with `A → B` injective and `B → C` surjective, and `B`
is finite-dimensional, then `dim A + dim C ≤ dim B`. -/
theorem Module.finrank_add_finrank_le_of_comp_eq_zero [FiniteDimensional K B] (f : A →ₗ[K] B)
    (g : B →ₗ[K] C) (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : g ∘ₗ f = 0) :
    finrank K A + finrank K C ≤ finrank K B := by
  have hrk := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.mpr hg, finrank_top] at hrk
  have hle : LinearMap.range f ≤ LinearMap.ker g := fun _ ⟨a, ha⟩ ↦ by
    rw [← ha, LinearMap.mem_ker, ← LinearMap.comp_apply, hfg, LinearMap.zero_apply]
  have := Submodule.finrank_mono hle
  rw [LinearMap.finrank_range_of_inj hf] at this
  omega

end Dimension

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-! ### Degree zero -/

section Zero

variable (M N : Type u) [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M] [AddCommGroup N] [Module K N]
  [LieRingModule P.KacMoodyAlgebra N] [LieModule K P.KacMoodyAlgebra N]

omit [CharZero K] in
/-- `H⁰(𝔤, 𝔥; Hom_K(M, N)) ≅ Hom_𝔤(M, N)`. -/
def relCohomologyZeroHomEquiv :
    relCohomology K P.KacMoodyAlgebra (M →ₗ[K] N) (Set.range (h P)) 0 ≃ₗ[K]
      (M →ₗ⁅K,P.KacMoodyAlgebra⁆ N) :=
  (relCohomologyZeroEquiv K P.KacMoodyAlgebra (M →ₗ[K] N) (Set.range (h P))).trans
    LieModule.maxTrivLinearMapEquivLieModuleHom

end Zero

/-! ### Acyclic injectives -/

section Acyclic

variable [IsAlgClosed K] [FiniteDimensional K H] (hA : A.IsFiniteCartan)

/-- The `𝔤`-module `⊤ ≅ V`. -/
def topLieEquiv (V : Type u) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
    [LieModule K P.KacMoodyAlgebra V] :
    (⊤ : LieSubmodule K P.KacMoodyAlgebra V) ≃ₗ⁅K,P.KacMoodyAlgebra⁆ V :=
  LieModuleEquiv.ofBijective (⊤ : LieSubmodule K P.KacMoodyAlgebra V).incl
    ⟨Subtype.val_injective, fun v ↦ ⟨⟨v, trivial⟩, rfl⟩⟩

variable {P}

include hA in
/-- A submodule of a finitely generated module in `𝒪` is finitely generated. -/
theorem exists_finset_lieSpan_lieSubmodule_eq_top {V : Type u} [AddCommGroup V] [Module K V]
    [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] (hV : IsCategoryO P V)
    {S : Finset V} (hS : LieSubmodule.lieSpan K P.KacMoodyAlgebra (S : Set V) = ⊤)
    (N : LieSubmodule K P.KacMoodyAlgebra V) :
    ∃ T : Finset N, LieSubmodule.lieSpan K P.KacMoodyAlgebra (T : Set N) = ⊤ := by
  have := hV.wellFoundedGT_lieSubmodule P hA hS
  have : WellFoundedGT (LieSubmodule K P.KacMoodyAlgebra N) :=
    (LieSubmodule.mapOrderEmbedding (f := N.incl) Subtype.val_injective).strictMono.wellFoundedGT
  exact LieSubmodule.exists_finset_lieSpan_eq_top

include hA in
/-- **Acyclic injectives.** Let `J` be finitely generated, in `𝒪` and injective in `𝒪`, with
`Hⁿ(𝔤, 𝔥; Hom_K(V, J)) = 0` for `n > 0` and every finitely generated projective `V` of `𝒪`.
Then `Hⁿ(𝔤, 𝔥; Hom_K(M, J)) = 0` for `n > 0` and every finitely generated `M` in `𝒪`. -/
theorem relAcyclic_of_isInjectiveO {J : Type u} [AddCommGroup J] [Module K J]
    [LieRingModule P.KacMoodyAlgebra J] [LieModule K P.KacMoodyAlgebra J]
    (hJinj : IsInjectiveO.{u} P J) (hJ : IsCategoryO P J)
    (hJS : ∃ S : Finset J, LieSubmodule.lieSpan K P.KacMoodyAlgebra (S : Set J) = ⊤)
    (hproj : ∀ (V : Type u) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
      [LieModule K P.KacMoodyAlgebra V], IsProjectiveO.{u} P V → IsCategoryO P V →
      (∃ S : Finset V, LieSubmodule.lieSpan K P.KacMoodyAlgebra (S : Set V) = ⊤) →
      RelAcyclic P V J)
    (n : ℕ) (M : Type u) [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
    [LieModule K P.KacMoodyAlgebra M] (hM : IsCategoryO P M)
    (hMS : ∃ S : Finset M, LieSubmodule.lieSpan K P.KacMoodyAlgebra (S : Set M) = ⊤) :
    IsZero (relCohomology K P.KacMoodyAlgebra (M →ₗ[K] J) (Set.range (h P)) (n + 1)) := by
  induction n generalizing M with
  | zero =>
    obtain ⟨S, hS⟩ := hMS
    obtain ⟨κ, _, _, τ, hQO, hQproj, ⟨T, hT⟩, π, hπ⟩ :=
      exists_isProjectiveO_surjective.{u, u} P hA hM hS
    let Kr := π.ker
    have hKO : IsCategoryO P Kr := hQO.lieSubmodule Kr
    obtain ⟨TK, hTK⟩ := exists_finset_lieSpan_lieSubmodule_eq_top hA hQO hT Kr
    obtain ⟨SJ, hSJ⟩ := hJS
    have hex : Function.Exact Kr.incl π := fun y ↦
      ⟨fun hy ↦ ⟨⟨y, LieModuleHom.mem_ker.mpr hy⟩, rfl⟩,
        by rintro ⟨x, rfl⟩; exact LieModuleHom.mem_ker.mp x.2⟩
    have hT' := homPrecomp_shortExact (N := J) (h P) hQO.iSup_weightSpaceOfMap_eq_top
      hM.iSup_weightSpaceOfMap_eq_top Subtype.val_injective hex hπ
    have hrel : (ComplexShape.up ℕ).Rel 0 1 := rfl
    let δ := (hT'.δ 0 1 hrel).hom
    have hδ : Function.Surjective δ := (ModuleCat.epi_iff_surjective _).mp
      (hT'.epi_δ 0 1 hrel (hproj _ hQproj hQO ⟨T, hT⟩ 0))
    -- the dimensions of the `Hom_𝔤(-, J)`
    have := hM.finiteDimensional_hom P hS hJ
    have := hQO.finiteDimensional_hom P hT hJ
    have := hKO.finiteDimensional_hom P hTK hJ
    have e₁ := relCohomologyZeroHomEquiv P M J
    have e₂ := relCohomologyZeroHomEquiv P
      (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j)) J
    have e₃ := relCohomologyZeroHomEquiv P Kr J
    have := e₁.symm.finiteDimensional
    have := e₂.symm.finiteDimensional
    have := e₃.symm.finiteDimensional
    have hfd : FiniteDimensional K
        (relCohomology K P.KacMoodyAlgebra (M →ₗ[K] J) (Set.range (h P)) (0 + 1)) :=
      Module.Finite.of_surjective δ hδ
    -- `0 → Hom_𝔤(M, J) → Hom_𝔤(Q, J) → Hom_𝔤(Kr, J) → 0`: dimension inequality
    let R : ((DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j))
          →ₗ⁅K,P.KacMoodyAlgebra⁆ J) →ₗ[K]
        (Kr →ₗ⁅K,P.KacMoodyAlgebra⁆ J) :=
      { toFun := fun φ ↦ φ.comp Kr.incl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hR : Function.Surjective R := fun ψ ↦
      let ⟨φ, hφ⟩ := hJinj hKO hQO Kr.incl Subtype.val_injective ψ
      ⟨φ, hφ⟩
    let I : (M →ₗ⁅K,P.KacMoodyAlgebra⁆ J) →ₗ[K]
        ((DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j)) →ₗ⁅K,P.KacMoodyAlgebra⁆ J) :=
      { toFun := fun ψ ↦ ψ.comp π
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hI : Function.Injective I := fun ψ ψ' hψ ↦ LieModuleHom.ext fun m ↦ by
      obtain ⟨q, rfl⟩ := hπ m
      exact LieModuleHom.congr_fun hψ q
    have hRI : R ∘ₗ I = 0 := LinearMap.ext fun ψ ↦ LieModuleHom.ext fun x ↦ by
      change ψ (π x) = 0
      rw [LieModuleHom.mem_ker.mp x.2, map_zero]
    have hle := Module.finrank_add_finrank_le_of_comp_eq_zero I R hI hR hRI
    -- `0 → H⁰(Hom(M, J)) → H⁰(Hom(Q, J)) → H⁰(Hom(Kr, J)) → H¹(Hom(M, J)) → 0`
    have hmono : Mono (HomologicalComplex.homologyMap
        (relCochainComplexMap (Set.range (h P)) (LieModuleHom.homPrecomp J π)) 0) := by
      have := hT'.mono_f
      have hnat := CochainComplex.isoHomologyπ₀_inv_naturality
        (relCochainComplexMap (Set.range (h P)) (LieModuleHom.homPrecomp J π))
      have : Mono (HomologicalComplex.homologyMap
          (relCochainComplexMap (Set.range (h P)) (LieModuleHom.homPrecomp J π)) 0 ≫
            (CochainComplex.isoHomologyπ₀ _).inv) := by
        rw [hnat]
        infer_instance
      exact mono_of_mono _ (CochainComplex.isoHomologyπ₀ _).inv
    have hH := Module.finrank_add_finrank_of_exact_four
      (HomologicalComplex.homologyMap
        (relCochainComplexMap (Set.range (h P)) (LieModuleHom.homPrecomp J π)) 0).hom
      (HomologicalComplex.homologyMap
        (relCochainComplexMap (Set.range (h P)) (LieModuleHom.homPrecomp J Kr.incl)) 0).hom
      δ ((ModuleCat.mono_iff_injective _).mp hmono)
      (LinearMap.exact_iff.mpr ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
        (hT'.homology_exact₂ 0)).symm)
      (LinearMap.exact_iff.mpr ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
        (hT'.homology_exact₃ 0 1 hrel)).symm) hδ
    have h₁ : finrank K (relCohomology K P.KacMoodyAlgebra (M →ₗ[K] J) (Set.range (h P)) 0) =
        finrank K (M →ₗ⁅K,P.KacMoodyAlgebra⁆ J) := e₁.finrank_eq
    have h₂ : finrank K (relCohomology K P.KacMoodyAlgebra
          ((DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j)) →ₗ[K] J) (Set.range (h P)) 0) =
        finrank K ((DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j))
          →ₗ⁅K,P.KacMoodyAlgebra⁆ J) :=
      e₂.finrank_eq
    have h₃ : finrank K (relCohomology K P.KacMoodyAlgebra (Kr →ₗ[K] J) (Set.range (h P)) 0) =
        finrank K (Kr →ₗ⁅K,P.KacMoodyAlgebra⁆ J) := e₃.finrank_eq
    have hH' : finrank K (relCohomology K P.KacMoodyAlgebra (M →ₗ[K] J) (Set.range (h P)) 0) +
        finrank K (relCohomology K P.KacMoodyAlgebra (Kr →ₗ[K] J) (Set.range (h P)) 0) =
        finrank K (relCohomology K P.KacMoodyAlgebra
          ((DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j)) →ₗ[K] J) (Set.range (h P)) 0) +
        finrank K (relCohomology K P.KacMoodyAlgebra (M →ₗ[K] J) (Set.range (h P)) (0 + 1)) :=
      hH
    have h0 : finrank K
        (relCohomology K P.KacMoodyAlgebra (M →ₗ[K] J) (Set.range (h P)) (0 + 1)) = 0 := by
      omega
    have : Subsingleton
        (relCohomology K P.KacMoodyAlgebra (M →ₗ[K] J) (Set.range (h P)) (0 + 1)) :=
      Module.finrank_zero_iff.mp h0
    exact ModuleCat.isZero_of_subsingleton _
  | succ n ih =>
    obtain ⟨S, hS⟩ := hMS
    obtain ⟨κ, _, _, τ, hQO, hQproj, ⟨T, hT⟩, π, hπ⟩ :=
      exists_isProjectiveO_surjective.{u, u} P hA hM hS
    let Kr := π.ker
    have hex : Function.Exact Kr.incl π := fun y ↦
      ⟨fun hy ↦ ⟨⟨y, LieModuleHom.mem_ker.mpr hy⟩, rfl⟩,
        by rintro ⟨x, rfl⟩; exact LieModuleHom.mem_ker.mp x.2⟩
    have hT' := homPrecomp_shortExact (N := J) (h P) hQO.iSup_weightSpaceOfMap_eq_top
      hM.iSup_weightSpaceOfMap_eq_top Subtype.val_injective hex hπ
    have hrel : (ComplexShape.up ℕ).Rel (n + 1) (n + 1 + 1) := rfl
    have := hT'.epi_δ (n + 1) (n + 1 + 1) hrel (hproj _ hQproj hQO ⟨T, hT⟩ (n + 1))
    exact IsZero.of_epi (hT'.δ (n + 1) (n + 1 + 1) hrel)
      (ih Kr (hQO.lieSubmodule Kr) (exists_finset_lieSpan_lieSubmodule_eq_top hA hQO hT Kr))

include hA in
/-- The injectives `(⊕ⱼ Qⱼ)^∨` of `exists_isInjectiveO_injective` are acyclic:
`Hⁿ(𝔤, 𝔥; Hom_K(M, (⊕ⱼ Qⱼ)^∨)) = 0` for `n > 0` and every finitely generated `M` in `𝒪`. -/
theorem relAcyclic_restrictedDual_projectiveCoverAmbient {κ : Type} [Finite κ]
    (τ : κ → Dual K H) (M : Type u) [AddCommGroup M] [Module K M]
    [LieRingModule P.KacMoodyAlgebra M] [LieModule K P.KacMoodyAlgebra M] (hM : IsCategoryO P M)
    (hMS : ∃ S : Finset M, LieSubmodule.lieSpan K P.KacMoodyAlgebra (S : Set M) = ⊤) :
    RelAcyclic P M
      (restrictedDual P (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j))) := by
  classical
  have := Fintype.ofFinite κ
  have : Finite (NegRootIndex P) := Finite.of_equiv _ (negRootIndexEquiv P hA).symm
  have hQO : IsCategoryO P (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j)) :=
    IsCategoryO.directSum _ fun j ↦ isCategoryO_projectiveCoverAmbient P hA _ _
  have hQproj : IsProjectiveO.{u} P (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j)) :=
    IsProjectiveO.directSum fun j ↦ isProjectiveO_projectiveCoverAmbient' P hA _
  obtain ⟨T, hT⟩ := exists_finset_lieSpan_directSum_eq_top fun j ↦
    exists_finset_lieSpan_projectiveCoverAmbient'_eq_top P hA (τ j)
  obtain ⟨s', hs'⟩ := IsProjectiveO.exists_isStdFiltered P hA hQproj hQO hT
  have hIO := isCategoryO_restrictedDual hQO
  have hIinj := hQproj.isInjectiveO_restrictedDual P hQO.iSup_weightSpaceOfMap_eq_top
  obtain ⟨fQ, hfQ⟩ := hQO.exists_strictMono_lieSubmodule P hA hT
  obtain ⟨FQ, hFQ⟩ := hQO.exists_strictMono_restrictedDual P hfQ
  have hIS := LieSubmodule.exists_finset_lieSpan_eq_top_of_strictMono hFQ
  exact fun n ↦ relAcyclic_of_isInjectiveO hA hIinj hIO hIS
    (fun V _ _ _ _ hVproj hVO ⟨S, hS⟩ ↦
      let ⟨s, hs⟩ := IsProjectiveO.exists_isStdFiltered P hA hVproj hVO hS
      (relAcyclic_restrictedDual_of_isStdFiltered P hVO hQO hs hs').congr
        (topLieEquiv P V) (restrictedDualEquiv (P := P) (topLieEquiv P _).symm)) n M hM hMS

end Acyclic

/-! ### Dimension shifting -/

namespace CategoryO

variable [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] {P}

/-- The relative cohomology map `Hⁿ(𝔤, 𝔥; Hom_K(M, V)) → Hⁿ(𝔤, 𝔥; Hom_K(M, W))` of a morphism
`V → W`. -/
abbrev relCohomologyPostcomp (M : Type u) [AddCommGroup M] [Module K M]
    [LieRingModule P.KacMoodyAlgebra M] [LieModule K P.KacMoodyAlgebra M] {V W : Type u}
    [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
    [LieModule K P.KacMoodyAlgebra V] [AddCommGroup W] [Module K W]
    [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W]
    (g : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (n : ℕ) :
    relCohomology K P.KacMoodyAlgebra (M →ₗ[K] V) (Set.range (h P)) n →ₗ[K]
      relCohomology K P.KacMoodyAlgebra (M →ₗ[K] W) (Set.range (h P)) n :=
  (HomologicalComplex.homologyMap
    (relCochainComplexMap (Set.range (h P)) (LieModuleHom.homPostcomp M g)) n).hom

variable (P) in
/-- Every object `Y` of `𝒪` sits in a short exact sequence `0 → Y → J → Z → 0` with `J` injective
in `𝒪` and `Hⁿ(𝔤, 𝔥; Hom_K(X, J)) = 0` for every `X` in `𝒪` and `n > 0`. -/
theorem exists_shortExact_injective_relAcyclic (Y : CategoryO.{u} P) :
    ∃ (J Z : CategoryO.{u} P) (f : Y ⟶ J) (g : J ⟶ Z) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧ Injective J ∧
      (∀ X : CategoryO.{u} P, RelAcyclic P X.obj J.obj) ∧
      ∃ (g₁ : Y.obj →ₗ⁅K,P.KacMoodyAlgebra⁆ J.obj) (g₂ : J.obj →ₗ⁅K,P.KacMoodyAlgebra⁆ Z.obj),
        Function.Injective g₁ ∧ Function.Exact g₁ g₂ ∧ Function.Surjective g₂ := by
  have hA : A.IsFiniteCartan := Fact.out
  obtain ⟨S, hS⟩ := Y.property.2
  obtain ⟨κ, _, _, τ, hIO, hIinj, hIfg, e, he⟩ :=
    exists_isInjectiveO_injective.{u, u} P hA Y.property.1 hS
  let I := restrictedDual P (DirectSum κ fun j ↦ projectiveCoverAmbient' P hA (τ j))
  let J := mk I hIO hIfg
  let e' : Y.obj →ₗ⁅K,P.KacMoodyAlgebra⁆ J.obj := (ofLieEquiv (P := P) I).toLieModuleHom.comp e
  have he' : Function.Injective e' := (ofLieEquiv (P := P) I).injective.comp he
  let N := e'.range
  have hex : Function.Exact e' (toQuotient J N) := fun x ↦
    (toQuotient_eq_zero_iff J N x).trans (e'.mem_range x)
  let f : Y ⟶ J := (IsObj.{u} P).homMk (ofLieModuleHom e')
  let g : J ⟶ ofQuotient J N := (IsObj.{u} P).homMk (ofLieModuleHom (toQuotient J N))
  have w : f ≫ g = 0 := by
    ext y
    exact hex.apply_apply_eq_zero y
  refine ⟨J, ofQuotient J N, f, g, w, shortExact_of_lie he' (surjective_toQuotient J N)
    (fun y hy ↦ (hex y).mp hy), injective_mk I hIO hIfg hIinj, fun X ↦ ?_,
    e', toQuotient J N, he', hex, surjective_toQuotient J N⟩
  exact (relAcyclic_restrictedDual_projectiveCoverAmbient hA τ X.obj X.property.1
    X.property.2).congr LieModuleEquiv.refl (ofLieEquiv (P := P) I)

/-- `Ext⁰_𝒪(X, Y) ≅ H⁰(𝔤, 𝔥; Hom_K(X, Y))`: both are `Hom_𝔤(X, Y)`. -/
def extZeroEquivRelCohomology (X Y : CategoryO.{u} P) :
    Abelian.Ext.{u} X Y 0 ≃ₗ[K]
      relCohomology K P.KacMoodyAlgebra (X.obj →ₗ[K] Y.obj) (Set.range (h P)) 0 :=
  (Abelian.Ext.linearEquiv₀ (R := K)).trans ((homEquivLie X Y).trans
    (relCohomologyZeroHomEquiv P X.obj Y.obj).symm)

/-- **Dimension shifting.** For `X`, `Y` in `𝒪` and every `n`, `Hⁿ(𝔤, 𝔥; Hom_K(X, Y))` is
finite-dimensional, of the same dimension as `Extⁿ_𝒪(X, Y)`. -/
theorem finiteDimensional_relCohomology_and_finrank_eq (X : CategoryO.{u} P) (n : ℕ) :
    ∀ Y : CategoryO.{u} P,
      FiniteDimensional K
        (relCohomology K P.KacMoodyAlgebra (X.obj →ₗ[K] Y.obj) (Set.range (h P)) n) ∧
      finrank K (Abelian.Ext.{u} X Y n) =
        finrank K (relCohomology K P.KacMoodyAlgebra (X.obj →ₗ[K] Y.obj) (Set.range (h P)) n) := by
  induction n with
  | zero =>
    intro Y
    exact ⟨LinearEquiv.finiteDimensional (extZeroEquivRelCohomology X Y),
      (extZeroEquivRelCohomology X Y).finrank_eq⟩
  | succ n ih =>
    intro Y
    obtain ⟨J, Z, f, g, w, hS, hJ, hJ0, g₁, g₂, hg₁, hex, hg₂⟩ :=
      exists_shortExact_injective_relAcyclic P Y
    have hT := homPostcomp_shortExact (M := X.obj) (h P)
      J.property.1.iSup_weightSpaceOfMap_eq_top Z.property.1.iSup_weightSpaceOfMap_eq_top
      hg₁ hex hg₂
    have hrel : (ComplexShape.up ℕ).Rel n (n + 1) := rfl
    let δ := (hT.δ n (n + 1) hrel).hom
    have := hJ
    have hJext : ∀ (m : ℕ) (x : Abelian.Ext.{u} X J (m + 1)), x = 0 :=
      fun m x ↦ Abelian.Ext.eq_zero_of_injective x
    -- `δ : Hⁿ(Hom(X, Z)) → Hⁿ⁺¹(Hom(X, Y))` is surjective
    have hδ : Function.Surjective δ := (ModuleCat.epi_iff_surjective _).mp
      (hT.epi_δ n (n + 1) hrel (hJ0 X n))
    have hfd : FiniteDimensional K
        (relCohomology K P.KacMoodyAlgebra (X.obj →ₗ[K] Y.obj) (Set.range (h P)) (n + 1)) :=
      have := (ih Z).1
      Module.Finite.of_surjective δ hδ
    refine ⟨hfd, ?_⟩
    -- the connecting map of `Ext` is surjective
    have hc : Function.Surjective (connectingLinear X hS n) := fun x ↦
      (exact_connectingLinear_postcompLinear X hS n x).mp (hJext n _)
    cases n with
    | zero =>
      -- `0 → Hom(X, Y) → Hom(X, J) → Hom(X, Z) → Ext¹(X, Y) → 0`
      have hE := Module.finrank_add_finrank_of_exact_four (postcompLinear X f 0)
        (postcompLinear X g 0) (connectingLinear X hS 0)
        (injective_postcompLinear_zero X hS) (exact_postcompLinear X hS 0)
        (exact_connectingLinear X hS 0) hc
      -- `0 → H⁰(Hom(X, Y)) → H⁰(Hom(X, J)) → H⁰(Hom(X, Z)) → H¹(Hom(X, Y)) → 0`
      have hmono : Mono (HomologicalComplex.homologyMap
          (relCochainComplexMap (Set.range (h P)) (LieModuleHom.homPostcomp X.obj g₁)) 0) := by
        have := hT.mono_f
        have hnat := CochainComplex.isoHomologyπ₀_inv_naturality
          (relCochainComplexMap (Set.range (h P)) (LieModuleHom.homPostcomp X.obj g₁))
        have : Mono (HomologicalComplex.homologyMap
            (relCochainComplexMap (Set.range (h P)) (LieModuleHom.homPostcomp X.obj g₁)) 0 ≫
              (CochainComplex.isoHomologyπ₀ _).inv) := by
          rw [hnat]
          infer_instance
        exact mono_of_mono _ (CochainComplex.isoHomologyπ₀ _).inv
      have := (ih J).1
      have := (ih Z).1
      have hH := Module.finrank_add_finrank_of_exact_four (relCohomologyPostcomp X.obj g₁ 0)
        (relCohomologyPostcomp X.obj g₂ 0) δ ((ModuleCat.mono_iff_injective _).mp hmono)
        (LinearMap.exact_iff.mpr ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
          (hT.homology_exact₂ 0)).symm)
        (LinearMap.exact_iff.mpr ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
          (hT.homology_exact₃ 0 1 hrel)).symm) hδ
      change _ + finrank K
          (relCohomology K P.KacMoodyAlgebra (X.obj →ₗ[K] Z.obj) (Set.range (h P)) 0) =
        _ + finrank K
          (relCohomology K P.KacMoodyAlgebra (X.obj →ₗ[K] Y.obj) (Set.range (h P)) (0 + 1))
        at hH
      rw [(ih Y).2, (ih J).2, (ih Z).2] at hE
      change _ = _ + finrank K (Abelian.Ext.{u} X Y (0 + 1)) at hE
      omega
    | succ n =>
      -- `Extⁿ⁺¹(X, Z) ≅ Extⁿ⁺²(X, Y)` and `Hⁿ⁺¹(Hom(X, Z)) ≅ Hⁿ⁺²(Hom(X, Y))`
      have hci : Function.Injective (connectingLinear X hS (n + 1)) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.exact_iff.mp (exact_connectingLinear _ hS _)]
        exact eq_bot_iff.mpr fun x ⟨y, hy⟩ ↦ by
          rw [← hy, hJext n y, map_zero]
          exact Submodule.zero_mem _
      have := hT.isIso_δ (n + 1) (n + 1 + 1) hrel (hJ0 X n) (hJ0 X (n + 1))
      rw [← (LinearEquiv.ofBijective _ ⟨hci, hc⟩).finrank_eq, (ih Z).2,
        (asIso (hT.δ (n + 1) (n + 1 + 1) hrel)).toLinearEquiv.finrank_eq]

/-- `dim Extⁿ_𝒪(X, Y) = dim Hⁿ(𝔤, 𝔥; Hom_K(X, Y))` ([HumO] Thm. 6.15 (a), dimension form). -/
theorem finrank_ext_eq_finrank_relCohomology (X Y : CategoryO.{u} P) (n : ℕ) :
    finrank K (Abelian.Ext.{u} X Y n) =
      finrank K (relCohomology K P.KacMoodyAlgebra (X.obj →ₗ[K] Y.obj) (Set.range (h P)) n) :=
  (finiteDimensional_relCohomology_and_finrank_eq X n Y).2

/-- **[HumO] Thm. 6.15 (a)**: `Extⁿ_𝒪(M, N) ≅ Hⁿ(𝔤, 𝔥; Hom_K(M, N))` for `M`, `N` in `𝒪`. -/
theorem nonempty_ext_linearEquiv_relCohomology (X Y : CategoryO.{u} P) (n : ℕ) :
    Nonempty (Abelian.Ext.{u} X Y n ≃ₗ[K]
      relCohomology K P.KacMoodyAlgebra (X.obj →ₗ[K] Y.obj) (Set.range (h P)) n) :=
  have := (finiteDimensional_relCohomology_and_finrank_eq X n Y).1
  ⟨LinearEquiv.ofFinrankEq _ _ (finrank_ext_eq_finrank_relCohomology X Y n)⟩

/-- [HumO] Thm. 6.15 (a) for modules `M`, `N` in `𝒪`:
`Extⁿ_𝒪(M, N) ≅ Hⁿ(𝔤, 𝔥; Hom_K(M, N))`. -/
theorem nonempty_ext_mk_linearEquiv_relCohomology (M N : Type u) [AddCommGroup M] [Module K M]
    [LieRingModule P.KacMoodyAlgebra M] [LieModule K P.KacMoodyAlgebra M] [AddCommGroup N]
    [Module K N] [LieRingModule P.KacMoodyAlgebra N] [LieModule K P.KacMoodyAlgebra N]
    (hM : IsCategoryO P M)
    (hMS : ∃ S : Finset M, LieSubmodule.lieSpan K P.KacMoodyAlgebra (S : Set M) = ⊤)
    (hN : IsCategoryO P N)
    (hNS : ∃ S : Finset N, LieSubmodule.lieSpan K P.KacMoodyAlgebra (S : Set N) = ⊤) (n : ℕ) :
    Nonempty (Abelian.Ext.{u} (mk M hM hMS) (mk N hN hNS) n ≃ₗ[K]
      relCohomology K P.KacMoodyAlgebra (M →ₗ[K] N) (Set.range (h P)) n) :=
  let ⟨e⟩ := nonempty_ext_linearEquiv_relCohomology (mk M hM hMS) (mk N hN hNS) n
  ⟨e.trans (relCohomologyCongr (Set.range (h P)) (LieModuleHom.homCongr
    (ofLieEquiv (P := P) M).symm (ofLieEquiv (P := P) N).symm) n).toLinearEquiv⟩

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
