/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.ProjectiveGenerator
import LieLean.Algebra.Lie.KacMoody.TranslationProjectiveCover
import LieLean.Algebra.Lie.KacMoody.EnoughInjectives

/-!
# Blocks of `𝒪` as modules over the endomorphism ring of a projective generator

Humphreys, GSM 94, Proposition 3.13: let `χ = χ_λ` be a central character and `P` a projective
generator of the block `𝒪_χ` (Humphreys takes `P = ⊕_w P(w·λ)^{n_w}`, `n_w > 0`, over coset
representatives `w` of the stabilizer of `λ`; summing `P(w·λ)` over all `w ∈ W` is such a module),
and let `E = End_𝒪(P)`, a finite-dimensional algebra. Then `M ↦ Hom_𝒪(P, M)` is an equivalence
of `𝒪_χ` with the category of finite-dimensional right `E`-modules.

The library has no bundled category `𝒪_χ`; the equivalence is stated as its two halves, for the
modules of `𝒪_χ` in the sense used throughout: finitely generated modules `M` in `𝒪`
(`IsCategoryO`) with `centralBlock P M χ = ⊤`. Right `E`-modules are modules over `Eᵐᵒᵖ`, and
`Hom(Q, M)` is one by precomposition (`LieModuleHom.homMap`).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsProjectiveGeneratorO P Q χ`: `Q` is a finitely generated
  projective module in `𝒪`, lies in the block `χ`, and maps nonzero to every `L(μ)` with
  `χ_μ = χ`.
* `Matrix.Realization.KacMoodyAlgebra.IsProjectiveGeneratorO.homMapEquiv`: the bijection
  `Hom_𝒪(M, N) ≃ Hom_E(Hom(Q, M), Hom(Q, N))`, `f ↦ f ∘ −`.

## Main results

* `IsProjectiveGeneratorO.exists_surjective`: every finitely generated `M` in `𝒪_χ` is a quotient
  of some `Qⁿ`.
* `IsProjectiveGeneratorO.homMap_bijective`: **full faithfulness** of `Hom(Q, −)` on `𝒪_χ`: for
  `M` in `𝒪_χ` and every module `N`, `f ↦ f ∘ −` is a bijection
  `Hom(M, N) → Hom_E(Hom(Q, M), Hom(Q, N))`.
* `IsProjectiveGeneratorO.exists_linearEquiv_homMap`: **essential surjectivity**: every
  finite-dimensional right `E`-module is `≅ Hom(Q, M)` for some `M` in `𝒪_χ`.
* `isProjectiveGeneratorO_directSum`, `isProjectiveGeneratorO_weylDot`: `⊕ᵢ P(μᵢ)` is a projective
  generator of `𝒪_χ` when the `μᵢ` exhaust the weights with `χ_μ = χ`; in particular
  `⊕_{w ∈ W} P(w·λ)` is one for `χ_λ`.

The functor lands in finite-dimensional modules by `IsFGProjectiveO.finiteDimensional_hom`.

## Proof notes

Humphreys refers to Bass's Morita theorem for abelian categories with a projective generator.
Here it is replaced by a direct argument (`LieLean/Algebra/Lie/ProjectiveGenerator.lean`): every
`M` in `𝒪_χ` is a quotient of some `Qⁿ` (if the images of all maps `Q → M` did not exhaust `M`,
a simple quotient `L(μ)` of the cokernel would lie in the block `χ`, and a nonzero map `Q → L(μ)`
would lift to `M`), with kernel again in `𝒪_χ`; full faithfulness follows from this presentation
and projectivity, and a finite presentation of a right `E`-module `X` gives the module `M` with
`Hom(Q, M) ≅ X` as a cokernel of a map `Qᵐ → Qⁿ`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.13.
-/

noncomputable section

open Module LieModule DirectSum MulOpposite

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule LieModuleHom

/-! ### Blocks of direct sums -/

section Block

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝓩" => Subalgebra.center K (UniversalEnvelopingAlgebra K P.KacMoodyAlgebra)

/-- A direct sum of modules in the block of `χ` lies in the block of `χ`. -/
theorem centralBlock_directSum_eq_top {κ : Type*} {Q : κ → Type*} [∀ j, AddCommGroup (Q j)]
    [∀ j, Module K (Q j)] [∀ j, LieRingModule P.KacMoodyAlgebra (Q j)]
    [∀ j, LieModule K P.KacMoodyAlgebra (Q j)] (χ : 𝓩 →ₐ[K] K)
    (h : ∀ j, centralBlock P (Q j) χ = ⊤) : centralBlock P (⨁ j, Q j) χ = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  induction x using DirectSum.induction_on with
  | zero => exact zero_mem _
  | of j q =>
    exact map_mem_centralBlock P (DirectSum.lieModuleOf K κ P.KacMoodyAlgebra Q j) χ
      (by rw [h j]; exact LieSubmodule.mem_top q)
  | add x y hx hy => exact add_mem hx hy

end Block

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓩" => Subalgebra.center K (UniversalEnvelopingAlgebra K P.KacMoodyAlgebra)

/-! ### Projective generators -/

/-- `Q` is a **projective generator of the block `𝒪_χ`**: a finitely generated projective module
in `𝒪`, lying in the block of `χ`, with a nonzero map to every simple module `L(μ)` of that block.
Then every finitely generated module of `𝒪_χ` is a quotient of some `Qⁿ`
(`IsProjectiveGeneratorO.exists_surjective`). -/
structure IsProjectiveGeneratorO (Q : Type (max u₁ u₂)) [AddCommGroup Q] [Module K Q]
    [LieRingModule P.KacMoodyAlgebra Q] [LieModule K P.KacMoodyAlgebra Q] (χ : 𝓩 →ₐ[K] K) :
    Prop where
  isFGProjectiveO : IsFGProjectiveO P Q
  centralBlock_eq_top : centralBlock P Q χ = ⊤
  exists_ne_zero : ∀ μ : Dual K H, centralCharacter P μ = χ →
    ∃ f : Q →ₗ⁅K,𝔤⁆ IrreducibleModule P μ, f ≠ 0

namespace IsProjectiveGeneratorO

variable {P} {Q : Type (max u₁ u₂)} [AddCommGroup Q] [Module K Q]
  [LieRingModule P.KacMoodyAlgebra Q] [LieModule K P.KacMoodyAlgebra Q]
  {χ : Subalgebra.center K (UniversalEnvelopingAlgebra K P.KacMoodyAlgebra) →ₐ[K] K}

include hA in
/-- Every finitely generated module `M` of `𝒪_χ` is a quotient of a finite direct sum of copies of
a projective generator `Q` of `𝒪_χ`. -/
theorem exists_surjective (hQ : IsProjectiveGeneratorO P Q χ) {M : Type (max u₁ u₂)}
    [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsCategoryO P M)
    {S : Finset M} (hS : LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤)
    (hMχ : centralBlock P M χ = ⊤) :
    ∃ n : ℕ, ∃ π : (⨁ _ : Fin n, Q) →ₗ⁅K,𝔤⁆ M, Function.Surjective π := by
  classical
  set N : LieSubmodule K 𝔤 M := ⨆ φ : Q →ₗ⁅K,𝔤⁆ M, φ.range with hNdef
  have hN : N = ⊤ := by
    by_contra hne
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hne)
    have : Nontrivial (M ⧸ N) := ⟨⟨LieSubmodule.Quotient.mk' N x, 0, fun h ↦ hx (by
      rwa [LieSubmodule.Quotient.mk'_apply, LieSubmodule.Quotient.mk_eq_zero'] at h)⟩⟩
    have hMN : IsCategoryO P (M ⧸ N) := hM.quotient N
    have hSN := lieSpan_image_eq_top_of_surjective (LieSubmodule.Quotient.mk' N)
      (LieSubmodule.Quotient.surjective_mk' N) hS
    rw [← Finset.coe_image] at hSN
    obtain ⟨μ, p, hp⟩ := hMN.exists_surjective_irreducibleModule P hA hSN
    set q := p.comp (LieSubmodule.Quotient.mk' N)
    have hq : Function.Surjective q := hp.comp (LieSubmodule.Quotient.surjective_mk' N)
    have hμ : centralCharacter P μ = χ := by
      by_contra hne'
      have h1 : centralBlock P (IrreducibleModule P μ) χ = ⊤ := eq_top_iff.2 fun y _ ↦ by
        obtain ⟨m, rfl⟩ := hq y
        exact map_mem_centralBlock P q χ (by rw [hMχ]; exact LieSubmodule.mem_top m)
      rw [centralBlock_eq_bot_of_ne P hne' (centralBlock_irreducible P μ)] at h1
      have : IrreducibleModule.hwv P μ ∈ (⊥ : LieSubmodule K 𝔤 (IrreducibleModule P μ)) :=
        h1 ▸ LieSubmodule.mem_top _
      exact IrreducibleModule.hwv_ne_zero P μ ((LieSubmodule.mem_bot _).1 this)
    obtain ⟨f, hf⟩ := hQ.exists_ne_zero μ hμ
    obtain ⟨φ, hφ⟩ := hQ.isFGProjectiveO.isProjectiveO hM (IrreducibleModule.isCategoryO P μ) q
      hq f
    apply hf
    rw [← hφ]
    refine LieModuleHom.ext fun v ↦ ?_
    have hv : φ v ∈ N := (le_iSup (fun φ : Q →ₗ⁅K,𝔤⁆ M ↦ φ.range) φ) ⟨v, rfl⟩
    change p (LieSubmodule.Quotient.mk' N (φ v)) = 0
    rw [LieSubmodule.Quotient.mk'_apply, LieSubmodule.Quotient.mk_eq_zero'.2 hv, map_zero]
  have := hM.wellFoundedGT_lieSubmodule P hA hS
  obtain ⟨t, ht, hts⟩ := WellFoundedGT.isSupFiniteCompact
    (Set.range fun φ : Q →ₗ⁅K,𝔤⁆ M ↦ φ.range)
  choose φ hφ using fun a : t ↦ ht a.2
  let e := t.equivFin
  refine ⟨t.card, toLieModule fun i ↦ φ (e.symm i), ?_⟩
  rw [← LieModuleHom.range_eq_top, range_toLieModule, e.symm.iSup_comp (g := fun a ↦ (φ a).range)]
  simp_rw [hφ]
  have ht' : (⨆ y : t, (y : LieSubmodule K 𝔤 M)) = t.sup _root_.id := by
    rw [Finset.sup_id_eq_sSup, sSup_eq_iSup']
    rfl
  rw [ht', ← hts, sSup_range, ← hNdef, hN]

include hA in
/-- **Full faithfulness of `Hom(Q, −)` on `𝒪_χ`** (Humphreys, GSM 94, Prop. 3.13, first half).
For a projective generator `Q` of `𝒪_χ`, a finitely generated `M` in `𝒪_χ` and any module `N`,
`f ↦ f ∘ −` is a bijection `Hom(M, N) → Hom_E(Hom(Q, M), Hom(Q, N))`, `E = End(Q)`. -/
theorem homMap_bijective (hQ : IsProjectiveGeneratorO P Q χ) {M : Type (max u₁ u₂)}
    [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsCategoryO P M)
    {S : Finset M} (hS : LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤)
    (hMχ : centralBlock P M χ = ⊤) (N : Type*) [AddCommGroup N] [Module K N]
    [LieRingModule 𝔤 N] [LieModule K 𝔤 N] :
    Function.Bijective (homMap (R := K) (L := 𝔤) (M := M) (N := N) Q) := by
  classical
  obtain ⟨n, π, hπ⟩ := hQ.exists_surjective hA hM hS hMχ
  have hQn : IsCategoryO P (⨁ _ : Fin n, Q) :=
    IsCategoryO.directSum _ fun _ ↦ hQ.isFGProjectiveO.isCategoryO
  have hQnχ : centralBlock P (⨁ _ : Fin n, Q) χ = ⊤ :=
    centralBlock_directSum_eq_top P χ fun _ ↦ hQ.centralBlock_eq_top
  refine LieModuleHom.homMap_bijective π hπ
    (fun φ ↦ hQ.isFGProjectiveO.isProjectiveO hQn hM π hπ φ) ?_
  obtain ⟨Sn, hSn⟩ := exists_finset_lieSpan_directSum_eq_top
    fun _ : Fin n ↦ hQ.isFGProjectiveO.fg
  obtain ⟨f, hf⟩ := hQn.exists_strictMono_lieSubmodule P hA hSn
  obtain ⟨T, hT⟩ := LieSubmodule.exists_finset_lieSpan_eq_top_of_strictMono
    (π.ker.strictMono_map_incl hf)
  have hKχ : centralBlock P π.ker χ = ⊤ := eq_top_iff.2 fun x _ ↦
    mem_centralBlock_of_injective P π.ker.incl Subtype.val_injective χ
      (by rw [hQnχ]; exact LieSubmodule.mem_top _)
  obtain ⟨m, σ, hσ⟩ := hQ.exists_surjective hA (hQn.lieSubmodule π.ker) hT hKχ
  intro x hx
  obtain ⟨y, hy⟩ := hσ ⟨x, hx⟩
  have hx' : x = π.ker.incl (σ y) := by rw [hy]; rfl
  rw [hx', ← DirectSum.sum_univ_of y, map_sum, map_sum]
  refine sum_mem fun j _ ↦ ?_
  set ψ := π.ker.incl.comp (σ.comp (lieModuleOf K (Fin m) 𝔤 (fun _ ↦ Q) j))
  have hψ : π.comp ψ = 0 := LieModuleHom.ext fun q ↦ (σ _).2
  exact LieSubmodule.mem_iSup_of_mem ψ (LieSubmodule.mem_iSup_of_mem hψ ⟨y j, rfl⟩)

/-- Under the hypotheses of `homMap_bijective`, `f ↦ f ∘ −` as a `K`-linear equivalence
`Hom_𝒪(M, N) ≃ Hom_E(Hom(Q, M), Hom(Q, N))`. -/
def homMapEquiv (hQ : IsProjectiveGeneratorO P Q χ) {M : Type (max u₁ u₂)}
    [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsCategoryO P M)
    {S : Finset M} (hS : LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤)
    (hMχ : centralBlock P M χ = ⊤) (N : Type*) [AddCommGroup N] [Module K N]
    [LieRingModule 𝔤 N] [LieModule K 𝔤 N] :
    (M →ₗ⁅K,𝔤⁆ N) ≃ₗ[K] ((Q →ₗ⁅K,𝔤⁆ M) →ₗ[(Q →ₗ⁅K,𝔤⁆ Q)ᵐᵒᵖ] (Q →ₗ⁅K,𝔤⁆ N)) :=
  LinearEquiv.ofBijective (homMapₗ Q M N) (hQ.homMap_bijective hA hM hS hMχ N)

theorem homMapEquiv_apply (hQ : IsProjectiveGeneratorO P Q χ) {M : Type (max u₁ u₂)}
    [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsCategoryO P M)
    {S : Finset M} (hS : LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤)
    (hMχ : centralBlock P M χ = ⊤) {N : Type*} [AddCommGroup N] [Module K N]
    [LieRingModule 𝔤 N] [LieModule K 𝔤 N] (f : M →ₗ⁅K,𝔤⁆ N) :
    hQ.homMapEquiv hA hM hS hMχ N f = homMap Q f :=
  rfl

omit [IsAlgClosed K] [FiniteDimensional K H] in
/-- **Essential surjectivity of `Hom(Q, −)`** (Humphreys, GSM 94, Prop. 3.13, second half). For a
projective generator `Q` of `𝒪_χ`, every finite-dimensional right `E`-module `X`, `E = End(Q)`, is
isomorphic to `Hom(Q, M)` for a finitely generated module `M` of `𝒪_χ`. -/
theorem exists_linearEquiv_homMap (hQ : IsProjectiveGeneratorO P Q χ) (X : Type*)
    [AddCommGroup X] [Module (Q →ₗ⁅K,𝔤⁆ Q)ᵐᵒᵖ X] [Module K X]
    [IsScalarTower K (Q →ₗ⁅K,𝔤⁆ Q)ᵐᵒᵖ X] [FiniteDimensional K X] :
    ∃ (M : Type (max u₁ u₂)) (_ : AddCommGroup M) (_ : Module K M) (_ : LieRingModule 𝔤 M)
      (_ : LieModule K 𝔤 M), IsCategoryO P M ∧
      (∃ S : Finset M, LieSubmodule.lieSpan K 𝔤 (S : Set M) = ⊤) ∧ centralBlock P M χ = ⊤ ∧
      Nonempty (X ≃ₗ[(Q →ₗ⁅K,𝔤⁆ Q)ᵐᵒᵖ] (Q →ₗ⁅K,𝔤⁆ M)) := by
  classical
  let n := finrank K X
  let bX : Basis (Fin n) K X := Module.finBasis K X
  have hx : Submodule.span (Q →ₗ⁅K,𝔤⁆ Q)ᵐᵒᵖ (Set.range bX) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ Submodule.span K (Set.range bX) := by rw [bX.span_eq]; trivial
    exact Submodule.span_le_restrictScalars K (Q →ₗ⁅K,𝔤⁆ Q)ᵐᵒᵖ _ hv
  have hQn : IsCategoryO P (⨁ _ : Fin n, Q) :=
    IsCategoryO.directSum _ fun _ ↦ hQ.isFGProjectiveO.isCategoryO
  have : FiniteDimensional K (Q →ₗ⁅K,𝔤⁆ ⨁ _ : Fin n, Q) :=
    hQ.isFGProjectiveO.finiteDimensional_hom hQn
  set F := homDirectSumToModule (R := K) (L := 𝔤) Q bX
  set Kr := (LinearMap.ker F).restrictScalars K
  let bK := Module.finBasis K Kr
  let y : Fin (finrank K Kr) → (Q →ₗ⁅K,𝔤⁆ ⨁ _ : Fin n, Q) := fun i ↦ (bK i : _)
  have hy : Submodule.span (Q →ₗ⁅K,𝔤⁆ Q)ᵐᵒᵖ (Set.range y) = LinearMap.ker F := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (bK i).2
    · intro v hv
      have h1 : (⟨v, hv⟩ : Kr) ∈ Submodule.span K (Set.range bK) := by rw [bK.span_eq]; trivial
      have h2 := Submodule.apply_mem_span_image_of_mem_span Kr.subtype h1
      have hr : Kr.subtype '' Set.range bK = Set.range y := by rw [← Set.range_comp]; rfl
      rw [hr] at h2
      exact Submodule.span_le_restrictScalars K (Q →ₗ⁅K,𝔤⁆ Q)ᵐᵒᵖ _ h2
  set α := toLieModule y
  have hQm : IsCategoryO P (⨁ _ : Fin (finrank K Kr), Q) :=
    IsCategoryO.directSum _ fun _ ↦ hQ.isFGProjectiveO.isCategoryO
  obtain ⟨e⟩ := nonempty_linearEquiv_homMap bX hx y hy
    (fun φ ↦ hQ.isFGProjectiveO.isProjectiveO hQn (hQn.quotient α.range)
      (LieSubmodule.Quotient.mk' α.range) (LieSubmodule.Quotient.surjective_mk' α.range) φ)
    (fun φ ↦ hQ.isFGProjectiveO.isProjectiveO hQm (hQn.lieSubmodule α.range) _
      (by rintro ⟨_, z, rfl⟩; exact ⟨z, rfl⟩) φ)
  obtain ⟨Sn, hSn⟩ := exists_finset_lieSpan_directSum_eq_top
    fun _ : Fin n ↦ hQ.isFGProjectiveO.fg
  have hQnχ : centralBlock P (⨁ _ : Fin n, Q) χ = ⊤ :=
    centralBlock_directSum_eq_top P χ fun _ ↦ hQ.centralBlock_eq_top
  refine ⟨_, inferInstance, inferInstance, inferInstance, inferInstance, hQn.quotient α.range,
    ⟨Sn.image (LieSubmodule.Quotient.mk' α.range), ?_⟩, ?_, ⟨e⟩⟩
  · rw [Finset.coe_image]
    exact lieSpan_image_eq_top_of_surjective _ (LieSubmodule.Quotient.surjective_mk' _) hSn
  · refine eq_top_iff.2 fun z _ ↦ ?_
    obtain ⟨v, rfl⟩ := LieSubmodule.Quotient.surjective_mk' α.range z
    exact map_mem_centralBlock P _ χ (by rw [hQnχ]; exact LieSubmodule.mem_top v)

end IsProjectiveGeneratorO

/-! ### Sums of projective covers -/

/-- `⊕ᵢ P(μᵢ)` is a projective generator of `𝒪_χ` when every `μᵢ` has central character `χ` and
every weight `μ` with `χ_μ = χ` is some `μᵢ`. -/
theorem isProjectiveGeneratorO_directSum {κ : Type u₂} [Finite κ] (μ : κ → Dual K H)
    {χ : 𝓩 →ₐ[K] K} (hμ : ∀ i, centralCharacter P (μ i) = χ)
    (hsurj : ∀ ν, centralCharacter P ν = χ → ∃ i, μ i = ν) :
    IsProjectiveGeneratorO P (⨁ i, ProjectiveCover P hA (μ i)) χ := by
  classical
  have h1 : IsProjectiveO.{max u₁ u₂} P (⨁ i, ProjectiveCover P hA (μ i)) :=
    IsProjectiveO.directSum fun i ↦ ProjectiveCover.isProjectiveO P hA (μ i)
  have h2 : IsCategoryO P (⨁ i, ProjectiveCover P hA (μ i)) :=
    IsCategoryO.directSum _ fun i ↦ ProjectiveCover.isCategoryO P hA (μ i)
  have h3 : ∃ S : Finset (⨁ i, ProjectiveCover P hA (μ i)),
      LieSubmodule.lieSpan K 𝔤 (S : Set (⨁ i, ProjectiveCover P hA (μ i))) = ⊤ :=
    exists_finset_lieSpan_directSum_eq_top fun i ↦ (ProjectiveCover.isFGProjectiveO P hA (μ i)).fg
  have h4 : centralBlock P (⨁ i, ProjectiveCover P hA (μ i)) χ = ⊤ :=
    centralBlock_directSum_eq_top P χ fun i ↦ by
      rw [← hμ i]; exact ProjectiveCover.centralBlock_eq_top P hA (μ i)
  have h5 : IsFGProjectiveO P (⨁ i, ProjectiveCover P hA (μ i)) := ⟨h1, h2, h3⟩
  refine ⟨h5, h4, fun ν hν ↦ ?_⟩
  clear h1 h2 h3 h4 h5
  obtain ⟨i, rfl⟩ := hsurj ν hν
  refine ⟨(ProjectiveCover.π P hA (μ i)).comp
    (lieModuleComponent K κ 𝔤 (fun i ↦ ProjectiveCover P hA (μ i)) i), fun h ↦ ?_⟩
  obtain ⟨x, hx⟩ := ProjectiveCover.surjective_π P hA (μ i) (IrreducibleModule.hwv P (μ i))
  apply IrreducibleModule.hwv_ne_zero P (μ i)
  have hc : lieModuleComponent K κ 𝔤 (fun i ↦ ProjectiveCover P hA (μ i)) i
      (DirectSum.of (fun i ↦ ProjectiveCover P hA (μ i)) i x) = x := by
    simp [lieModuleComponent, ← DirectSum.lof_eq_of K]
  rw [← hx]
  exact (congrArg (ProjectiveCover.π P hA (μ i)) hc.symm).trans
    ((LieModuleHom.congr_fun h _).trans (_root_.zero_apply _))

/-- **The projective generator of Humphreys, GSM 94, §3.13**: `⊕_{w ∈ W} P(w·λ)` is a projective
generator of the block of `χ_λ`. -/
theorem isProjectiveGeneratorO_weylDot (Λ : Dual K H) :
    IsProjectiveGeneratorO P
      (⨁ w : P.weylGroup hA.isGeneralizedCartan,
        ProjectiveCover P hA (P.weylDot hA.isGeneralizedCartan w Λ))
      (centralCharacter P Λ) := by
  have := P.finite_weylGroup hA
  refine isProjectiveGeneratorO_directSum P hA _ (fun w ↦ ?_) fun ν hν ↦ ?_
  · exact ((VermaModule.centralCharacter_eq_iff P hA _ _).2
      ⟨w, w.2, (P.weylDot_add_rho _ w Λ).symm⟩).symm
  · obtain ⟨w, hw, hwν⟩ := (VermaModule.centralCharacter_eq_iff P hA _ _).1 hν.symm
    exact ⟨⟨w, hw⟩, add_right_cancel ((P.weylDot_add_rho _ _ Λ).trans hwν)⟩

end Matrix.Realization.KacMoodyAlgebra
