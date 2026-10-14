/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.FiniteLength
import LieLean.Algebra.Lie.KacMoody.ProjectiveCoverHom
import LieLean.Algebra.Lie.KacMoody.CompositionSeries

/-!
# Indecomposable projectives in `𝒪`

Humphreys, GSM 94, Theorem 3.9 (a) and (b): every indecomposable projective module in `𝒪` is
isomorphic to some `P(λ)`, and in a decomposition of a projective module `Q ∈ 𝒪` into
indecomposables the number of summands isomorphic to `P(λ)` is `dim Hom(Q, L(λ))`.

## Main definitions

* `DirectSum.lieModuleHomEquiv`: morphisms out of a finite direct sum `⊕ᵢ Mᵢ` are families of
  morphisms out of the `Mᵢ`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.exists_surjective_irreducibleModule`: a nonzero
  finitely generated module in `𝒪` maps onto some `L(μ)`.
* `Matrix.Realization.KacMoodyAlgebra.ProjectiveCover.exists_nonempty_equiv_of_indecomposable`:
  **Theorem 3.9 (a)**: an indecomposable projective in `𝒪` is isomorphic to some `P(λ)`.
* `Matrix.Realization.KacMoodyAlgebra.ProjectiveCover.card_filter_nonempty_equiv_eq_finrank_hom`:
  **Theorem 3.9 (b)**.

## Implementation notes

Humphreys' `𝒪` consists of finitely generated modules; here finite generation is the hypothesis
`lieSpan S = ⊤` for a finite set `S`. "Indecomposable" is encoded as: nonzero, and every idempotent
endomorphism is `0` or the identity.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.9.
-/

noncomputable section

open Module LieModule Finset DirectSum

universe u₁ u₂

namespace DirectSum

variable {R ι L N : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [DecidableEq ι] [Fintype ι]
  {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, LieRingModule L (M i)] [∀ i, LieModule R L (M i)]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- Morphisms of Lie modules out of a finite direct sum `⊕ᵢ Mᵢ` are families of morphisms out of
the summands `Mᵢ`. -/
def lieModuleHomEquiv : ((⨁ i, M i) →ₗ⁅R,L⁆ N) ≃ₗ[R] ∀ i, M i →ₗ⁅R,L⁆ N where
  toFun f i := f.comp (lieModuleOf R ι L M i)
  invFun := toLieModule
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    ext x
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of j q => rw [toLieModule_of]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv φ := by
    funext i
    ext q
    exact toLieModule_of φ i q

end DirectSum

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- A nonzero finitely generated module in `𝒪` maps onto some `L(μ)` (used in Humphreys, GSM 94,
proof of Theorem 3.9 (a)). Humphreys works over `ℂ`. -/
theorem IsCategoryO.exists_surjective_irreducibleModule {W : Type*} [AddCommGroup W] [Module K W]
    [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W] [Nontrivial W]
    (hW : IsCategoryO P W) {S : Finset W} (hS : LieSubmodule.lieSpan K 𝔤 (S : Set W) = ⊤) :
    ∃ μ : Dual K H, ∃ φ : W →ₗ⁅K,𝔤⁆ IrreducibleModule P μ, Function.Surjective φ := by
  have hwf := hW.wellFoundedGT_lieSubmodule P hA hS
  have : IsCoatomic (LieSubmodule K 𝔤 W) := inferInstance
  have hbot : (⊥ : LieSubmodule K 𝔤 W) ≠ ⊤ := by
    intro h
    obtain ⟨x, y, hxy⟩ := exists_pair_ne W
    have hx : x ∈ (⊥ : LieSubmodule K 𝔤 W) := h ▸ LieSubmodule.mem_top x
    have hy : y ∈ (⊥ : LieSubmodule K 𝔤 W) := h ▸ LieSubmodule.mem_top y
    rw [LieSubmodule.mem_bot] at hx hy
    exact hxy (hx.trans hy.symm)
  obtain ⟨N, hN, -⟩ := (eq_top_or_exists_le_coatom (⊥ : LieSubmodule K 𝔤 W)).resolve_left hbot
  -- a nonzero primitive vector of `W / N`
  set q := LieSubmodule.Quotient.mk' N
  have hq : Function.Surjective q := LieSubmodule.Quotient.surjective_mk' N
  have hWN := hW.quotient N
  have hex : ∃ μ, weightSpace P (W ⧸ N) μ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ : ∃ w : W, w ∉ N := by
      by_contra hc
      push Not at hc
      exact hN.1 (eq_top_iff.mpr fun w _ ↦ hc w)
    have htop := hWN.iSup_weightSpaceOfMap_eq_top
    simp_rw [show ∀ μ, weightSpaceOfMap (W ⧸ N) (h P) μ = ⊥ from hcon, iSup_bot] at htop
    have : q w ∈ (⊥ : Submodule K (W ⧸ N)) := htop ▸ Submodule.mem_top
    rw [Submodule.mem_bot, LieSubmodule.Quotient.mk_eq_zero] at this
    exact hw this
  obtain ⟨μ, hμ⟩ := hex
  have hab : aboveSpan P (W ⧸ N) {μ} ≠ ⊥ := by
    refine fun h0 ↦ hμ (eq_bot_iff.mpr ?_)
    rw [← h0]
    refine le_iSup_of_le (⟨μ, Finset.mem_singleton_self μ⟩ : ({μ} : Finset (Dual K H)))
      (le_iSup₂_of_le 0 le_rfl ?_)
    rw [map_zero, add_zero]
  obtain ⟨ν, v, hv, hv0, -⟩ := hWN.exists_primitive_mem_aboveSpan P {μ} hab
  rw [mem_primitiveVectors] at hv
  have hmem : v ∈ weightSpaceOfMap (W ⧸ N) (h P) ν := hv.1
  rw [← map_weightSpace_of_surjective P hW.iSup_weightSpaceOfMap_eq_top q hq] at hmem
  obtain ⟨w, hw, rfl⟩ := hmem
  have hwN : w ∉ N := fun h ↦ hv0 (by
    change q w = 0
    rw [LieSubmodule.Quotient.mk_eq_zero]
    exact h)
  have he (i : ι) : ⁅e P i, w⁆ ∈ N := by
    have h0 := hv.2 i
    change ⁅e P i, q w⁆ = 0 at h0
    rw [← LieModuleHom.map_lie] at h0
    rwa [LieSubmodule.Quotient.mk_eq_zero] at h0
  obtain ⟨M₁, M₂, hNM₁, hM₁₂, -, hwM₂, hwM₁, ⟨e⟩⟩ :=
    exists_subquotient_equiv_irreducibleModule (le_top : N ≤ ⊤) hw (LieSubmodule.mem_top w)
      hwN he
  have hM₂ : M₂ = ⊤ := by
    rcases hN.le_iff.mp (hNM₁.trans hM₁₂) with h | h
    · exact h
    · exact absurd (h ▸ hwM₂) hwN
  let r : W →ₗ⁅K,𝔤⁆ M₂ :=
    LieModuleHom.codRestrict M₂ LieModuleHom.id fun x ↦ hM₂ ▸ LieSubmodule.mem_top x
  refine ⟨ν, e.toLieModuleHom.comp ((LieSubmodule.Quotient.mk' _).comp r), ?_⟩
  refine e.surjective.comp fun z ↦ ?_
  obtain ⟨⟨x, hx⟩, rfl⟩ := LieSubmodule.Quotient.surjective_mk' _ z
  exact ⟨x, rfl⟩

namespace ProjectiveCover

/-- **Humphreys, GSM 94, Theorem 3.9 (a).** In finite type over an algebraically closed field of
characteristic zero, every indecomposable projective module in `𝒪` (finitely generated, nonzero,
with only the idempotent endomorphisms `0` and `1`) is isomorphic to some projective cover
`P(λ)`. Humphreys works over `ℂ`. -/
theorem exists_nonempty_equiv_of_indecomposable {W : Type (max u₁ u₂)} [AddCommGroup W]
    [Module K W] [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W]
    [Nontrivial W] (hWproj : IsProjectiveO.{max u₁ u₂} P W) (hW : IsCategoryO P W) {S : Finset W}
    (hS : LieSubmodule.lieSpan K 𝔤 (S : Set W) = ⊤)
    (hind : ∀ a : W →ₗ⁅K,𝔤⁆ W, a.comp a = a → a = 0 ∨ a = LieModuleHom.id) :
    ∃ Λ : Dual K H, Nonempty (ProjectiveCover P hA Λ ≃ₗ⁅K,𝔤⁆ W) := by
  obtain ⟨Λ, φ, hφ⟩ := hW.exists_surjective_irreducibleModule P hA hS
  exact ⟨Λ, nonempty_equiv_of_indecomposable P Λ hA hWproj hW hind φ hφ⟩

/-- For an indecomposable projective `W ∈ 𝒪`, `dim Hom(W, L(λ))` is `1` if `W ≅ P(λ)` and `0`
otherwise. -/
theorem finrank_hom_irreducible_of_indecomposable {W : Type (max u₁ u₂)} [AddCommGroup W]
    [Module K W] [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W]
    [Nontrivial W] (hWproj : IsProjectiveO.{max u₁ u₂} P W) (hW : IsCategoryO P W) {S : Finset W}
    (hS : LieSubmodule.lieSpan K 𝔤 (S : Set W) = ⊤)
    (hind : ∀ a : W →ₗ⁅K,𝔤⁆ W, a.comp a = a → a = 0 ∨ a = LieModuleHom.id) (Λ : Dual K H)
    [Decidable (Nonempty (W ≃ₗ⁅K,𝔤⁆ ProjectiveCover P hA Λ))] :
    finrank K (W →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ) =
      if Nonempty (W ≃ₗ⁅K,𝔤⁆ ProjectiveCover P hA Λ) then 1 else 0 := by
  classical
  obtain ⟨μ, ⟨e⟩⟩ := exists_nonempty_equiv_of_indecomposable P hA hWproj hW hS hind
  have hfin (ν : Dual K H) : finrank K (W →ₗ⁅K,𝔤⁆ IrreducibleModule P ν) =
      if ν = μ then 1 else 0 := by
    rw [← (lieModuleHomCongr P e LieModuleEquiv.refl).finrank_eq]
    exact finrank_hom_irreducible P μ hA ν
  rw [hfin Λ]
  by_cases hΛ : Λ = μ
  · subst hΛ
    have hne : Nonempty (W ≃ₗ⁅K,𝔤⁆ ProjectiveCover P hA Λ) := ⟨e.symm⟩
    simp only [hne, ↓reduceIte]
  · have hne : ¬ Nonempty (W ≃ₗ⁅K,𝔤⁆ ProjectiveCover P hA Λ) := by
      rintro ⟨e'⟩
      have h1 := hfin Λ
      rw [← (lieModuleHomCongr P e'.symm LieModuleEquiv.refl).finrank_eq,
        finrank_hom_irreducible P Λ hA Λ] at h1
      simp [hΛ] at h1
    simp only [hΛ, hne, ↓reduceIte]

/-- **Humphreys, GSM 94, Theorem 3.9 (b).** In finite type over an algebraically closed field of
characteristic zero, let `V ∈ 𝒪` be a finitely generated projective module written as a finite
direct sum `V ≅ ⊕ⱼ Qⱼ` of indecomposable modules. Then the number of summands `Qⱼ` isomorphic to
`P(λ)` is `dim Hom(V, L(λ))`. Humphreys works over `ℂ`. -/
theorem card_filter_nonempty_equiv_eq_finrank_hom {V : Type (max u₁ u₂)} [AddCommGroup V]
    [Module K V] [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
    (hVproj : IsProjectiveO.{max u₁ u₂} P V) (hV : IsCategoryO P V) {S : Finset V}
    (hS : LieSubmodule.lieSpan K 𝔤 (S : Set V) = ⊤)
    {J : Type*} [Fintype J] {Q : J → Type (max u₁ u₂)}
    [∀ j, AddCommGroup (Q j)] [∀ j, Module K (Q j)] [∀ j, LieRingModule P.KacMoodyAlgebra (Q j)]
    [∀ j, LieModule K P.KacMoodyAlgebra (Q j)] [∀ j, Nontrivial (Q j)]
    (hind : ∀ j, ∀ a : Q j →ₗ⁅K,𝔤⁆ Q j, a.comp a = a → a = 0 ∨ a = LieModuleHom.id)
    (e : V ≃ₗ⁅K,𝔤⁆ ⨁ j, Q j) (Λ : Dual K H)
    [DecidablePred fun j ↦ Nonempty (Q j ≃ₗ⁅K,𝔤⁆ ProjectiveCover P hA Λ)] :
    #{j | Nonempty (Q j ≃ₗ⁅K,𝔤⁆ ProjectiveCover P hA Λ)} =
      finrank K (V →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ) := by
  classical
  -- each summand is a finitely generated projective module in `𝒪`
  let s (j : J) : Q j →ₗ⁅K,𝔤⁆ V :=
    e.symm.toLieModuleHom.comp (DirectSum.lieModuleOf K J 𝔤 Q j)
  let r (j : J) : V →ₗ⁅K,𝔤⁆ Q j :=
    (DirectSum.lieModuleComponent K J 𝔤 Q j).comp e.toLieModuleHom
  have hrs (j : J) : (r j).comp (s j) = LieModuleHom.id := by
    ext q
    simp [r, s, DirectSum.lieModuleComponent, DirectSum.lieModuleOf]
  have hr (j : J) : Function.Surjective (r j) := fun q ↦
    ⟨s j q, LieModuleHom.congr_fun (hrs j) q⟩
  have hproj (j : J) : IsProjectiveO.{max u₁ u₂} P (Q j) := hVproj.of_retract (s j) (r j) (hrs j)
  have hO (j : J) : IsCategoryO P (Q j) := by
    obtain ⟨f⟩ := LieSubmodule.Quotient.nonempty_lieModuleEquiv_of_surjective _ (r j) (hr j) rfl
    exact (hV.quotient _).of_equiv f
  have hfg (j : J) : LieSubmodule.lieSpan K 𝔤 ((S.image (r j) : Finset (Q j)) : Set (Q j)) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := hr j y
    have hle : LieSubmodule.lieSpan K 𝔤 (S : Set V) ≤
        (LieSubmodule.lieSpan K 𝔤 ((S.image (r j) : Finset (Q j)) : Set (Q j))).comap (r j) := by
      rw [LieSubmodule.lieSpan_le]
      intro x hx
      exact LieSubmodule.subset_lieSpan (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
    exact hle (hS ▸ LieSubmodule.mem_top x)
  -- count via `Hom(⊕ⱼ Qⱼ, L(λ)) ≅ ∏ⱼ Hom(Qⱼ, L(λ))`
  have hfin (j : J) : FiniteDimensional K (Q j →ₗ⁅K,𝔤⁆ IrreducibleModule P Λ) :=
    (hO j).finiteDimensional_hom P (hfg j) (IrreducibleModule.isCategoryO P Λ)
  rw [(lieModuleHomCongr P e LieModuleEquiv.refl).finrank_eq,
    (DirectSum.lieModuleHomEquiv (R := K) (L := 𝔤)).finrank_eq, Module.finrank_pi_fintype,
    Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact (finrank_hom_irreducible_of_indecomposable P hA (hproj j) (hO j) (hfg j) (hind j) Λ).symm

end ProjectiveCover

end Matrix.Realization.KacMoodyAlgebra
