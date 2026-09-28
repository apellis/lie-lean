/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CentralDecomposition
import LieLean.Algebra.Lie.KacMoody.TensorVermaFiltration

/-!
# Projecting tensor-Verma filtrations to full-central blocks

## Main results

* `centralBlockStepEquiv`: exact restriction of canonical successive quotient images.
* `map_centralBlockProjection_eq_inf`: restriction is the image of the actual projection.
* `exists_centralTensorVermaFiltration`: the projected finite tensor-Verma filtration,
  surviving shifted-Verma factors and retained weight multiplicities.

The projected filtration retains zero steps. Algebraic closure is used for exact block
restriction, not for central character classification. No finite-type, integrality,
dominance, Harish-Chandra, linkage or Humphreys Theorem 7.6 claim is made.

## References
Arguments reconstructed from the inspected Mathlib quotient API and the repository's
full-central exactness and tensor-Verma filtration results. No printed source consulted.
-/

open Module LieModule TensorProduct
noncomputable section

namespace LieSubmodule
variable {K L V : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]

/-- The canonical comparison of quotient images after intersecting both pieces with `C`.
No nesting assumption is needed: both factors are actual images in ambient quotients. -/
def infQuotientImageMap (N M C : LieSubmodule K L V) :
    (M ⊓ C).map (Quotient.mk' (N ⊓ C)) →ₗ⁅K,L⁆ M.map (Quotient.mk' N) := by
  let q := Quotient.lift (N ⊓ C) (Quotient.mk' N)
    (fun x hx => (Quotient.mk_eq_zero N).mpr hx.1)
  exact (q.comp ((M ⊓ C).map (Quotient.mk' (N ⊓ C))).incl).codRestrict _ (by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨x, hx.1, rfl⟩)

/-- The comparison is injective, since a central-restricted representative killed modulo
`N` already belongs to `N ∩ C`. This is a purely Lie-module quotient fact. -/
theorem infQuotientImageMap_injective (N M C : LieSubmodule K L V) :
    Function.Injective (infQuotientImageMap N M C) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨y, x, hx, rfl⟩ hy
  apply Subtype.ext
  apply (Quotient.mk_eq_zero (N ⊓ C)).mpr
  exact ⟨(Quotient.mk_eq_zero N).mp (congrArg Subtype.val hy), hx.2⟩

end LieSubmodule

namespace Matrix.Realization.KacMoodyAlgebra
open VermaModule
variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V : Type*} [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

/-- A finite-dimensional Cartan-diagonalizable module is in category O, without a
finite-type hypothesis. Its finite set of actual weights supplies the cone bounds. -/
theorem IsHDiagonalizable.isCategoryO_of_finite [FiniteDimensional K V]
    (hV : IsHDiagonalizable P V) : IsCategoryO P V where
  iSup_weightSpaceOfMap_eq_top := hV
  finiteDimensional_weightSpaceOfMap _ := inferInstance
  exists_finset := by
    classical
    have hind := iSupIndep_weightSpaceOfMap (M := V) (h P)
    have := hind.fintypeNeBotOfFiniteDimensional
    have hfin : {μ | weightSpaceOfMap V (h P) μ ≠ ⊥}.Finite :=
      Set.finite_coe_iff.mp (inferInstance : Finite {μ // weightSpaceOfMap V (h P) μ ≠ ⊥})
    exact ⟨hfin.toFinset, fun μ hμ =>
      ⟨μ, hfin.mem_toFinset.mpr hμ, 0, le_rfl, by simp⟩⟩

variable [IsAlgClosed K]

/-- The image of any category-O submodule under the actual full-central projection is
its intersection with the requested block. -/
theorem map_centralBlockProjection_eq_inf (hV : IsCategoryO P V)
    (N : LieSubmodule K P.KacMoodyAlgebra V) (χ : 𝓩 →ₐ[K] K) :
    N.map (centralBlockProjection P (hV.isCentralLocallyFinite P) χ) =
      N ⊓ centralBlock P V χ := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨?_, centralBlockProjection_mem P _ χ v⟩
    have hn := congrArg (fun f => f (⟨v, hv⟩ : N))
      (centralBlockProjection_natural P ((hV.lieSubmodule N).isCentralLocallyFinite P)
        (hV.isCentralLocallyFinite P) N.incl χ)
    exact hn ▸ (centralBlockProjection P ((hV.lieSubmodule N).isCentralLocallyFinite P)
      χ (⟨v, hv⟩ : N)).property
  · intro v hv
    exact ⟨v, hv.1, centralBlockProjection_self P _ χ hv.2⟩

/-- Canonical comparison from the restricted quotient image to the full-central block
of the original quotient image. -/
def centralBlockStepMap (N M : LieSubmodule K P.KacMoodyAlgebra V) (χ : 𝓩 →ₐ[K] K) :
    (M ⊓ centralBlock P V χ).map (LieSubmodule.Quotient.mk' (N ⊓ centralBlock P V χ))
      →ₗ⁅K,P.KacMoodyAlgebra⁆
    centralBlock P (M.map (LieSubmodule.Quotient.mk' N)) χ :=
  (LieSubmodule.infQuotientImageMap N M (centralBlock P V χ)).codRestrict _ (by
    rintro ⟨y, x, hx, rfl⟩
    apply mem_centralBlock_of_injective P (M.map (LieSubmodule.Quotient.mk' N)).incl
      Subtype.val_injective χ
    exact map_mem_centralBlock P (LieSubmodule.Quotient.mk' N) χ hx.2)

/-- Exactness of full-central restriction identifies actual canonical quotient images.
Only the upper piece needs category O; no projected filtration is assumed. -/
def centralBlockStepEquiv (N M : LieSubmodule K P.KacMoodyAlgebra V)
    (hM : IsCategoryO P M) (χ : 𝓩 →ₐ[K] K) :
    (M ⊓ centralBlock P V χ).map (LieSubmodule.Quotient.mk' (N ⊓ centralBlock P V χ))
      ≃ₗ⁅K,P.KacMoodyAlgebra⁆
    centralBlock P (M.map (LieSubmodule.Quotient.mk' N)) χ := by
  apply LieModuleEquiv.ofBijective (centralBlockStepMap P N M χ)
  constructor
  · intro x y hxy
    exact LieSubmodule.infQuotientImageMap_injective N M (centralBlock P V χ)
      (congrArg Subtype.val hxy)
  · let f : M →ₗ⁅K,P.KacMoodyAlgebra⁆ M.map (LieSubmodule.Quotient.mk' N) :=
      ((LieSubmodule.Quotient.mk' N).comp M.incl).codRestrict _
        (fun m => ⟨m.val, m.property, rfl⟩)
    have hf : Function.Surjective f := by
      rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    intro w
    obtain ⟨m, hm⟩ := hM.surjective_centralBlockMap P f hf χ w
    refine ⟨⟨LieSubmodule.Quotient.mk' _ m.val.val,
      m.val.val, ⟨m.val.property, map_mem_centralBlock P M.incl χ m.property⟩, rfl⟩, ?_⟩
    exact hm

/-- The equivalence of quotient images sends the class of a restricted representative to
its original quotient class. This certifies its canonical quotient-map normalization. -/
theorem centralBlockStepEquiv_apply_mk (N M : LieSubmodule K P.KacMoodyAlgebra V)
    (hM : IsCategoryO P M) (χ : 𝓩 →ₐ[K] K) {v : V}
    (hv : v ∈ M ⊓ centralBlock P V χ) :
    ((centralBlockStepEquiv P N M hM χ
      ⟨LieSubmodule.Quotient.mk' _ v, v, hv, rfl⟩).val : V ⧸ N) =
        LieSubmodule.Quotient.mk' N v := rfl

section VermaFactors
variable [CharZero K]
  {W : Type*} [AddCommGroup W] [Module K W]
  [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W]

/-- An actual Verma factor survives intact at its own full-central character. -/
def vermaEquivCentralBlock (μ : Dual K H)
    (e : VermaModule P μ ≃ₗ⁅K,P.KacMoodyAlgebra⁆ W) (χ : 𝓩 →ₐ[K] K)
    (hχ : centralCharacter P μ = χ) :
    VermaModule P μ ≃ₗ⁅K,P.KacMoodyAlgebra⁆ centralBlock P W χ := by
  have ht : centralBlock P W χ = ⊤ := hχ ▸
    centralBlock_eq_top_of_verma_surjective P μ e.toLieModuleHom e.surjective
  apply LieModuleEquiv.ofBijective (e.toLieModuleHom.codRestrict _
    (fun _ => ht ▸ LieSubmodule.mem_top _))
  exact ⟨fun _ _ h => e.injective (congrArg Subtype.val h), fun w =>
    ⟨e.symm w.val, Subtype.ext (e.apply_symm_apply w.val)⟩⟩

/-- The canonical factor of the restricted filtration is the same shifted Verma module
when its actual full-central character is the target character. -/
def centralBlockStepVermaEquiv (N M : LieSubmodule K P.KacMoodyAlgebra V)
    (hM : IsCategoryO P M) (μ : Dual K H)
    (e : VermaModule P μ ≃ₗ⁅K,P.KacMoodyAlgebra⁆ M.map (LieSubmodule.Quotient.mk' N))
    (χ : 𝓩 →ₐ[K] K) (hχ : centralCharacter P μ = χ) :
    VermaModule P μ ≃ₗ⁅K,P.KacMoodyAlgebra⁆
      (M ⊓ centralBlock P V χ).map (LieSubmodule.Quotient.mk' (N ⊓ centralBlock P V χ)) :=
  (vermaEquivCentralBlock P μ e χ hχ).trans (centralBlockStepEquiv P N M hM χ).symm

/-- A factor with a different actual central character has zero restricted quotient image.
No implication from inequality of highest weights to inequality of characters is used. -/
theorem centralBlockStep_eq_bot (N M : LieSubmodule K P.KacMoodyAlgebra V)
    (hM : IsCategoryO P M) (μ : Dual K H)
    (e : VermaModule P μ ≃ₗ⁅K,P.KacMoodyAlgebra⁆ M.map (LieSubmodule.Quotient.mk' N))
    (χ : 𝓩 →ₐ[K] K) (hχ : centralCharacter P μ ≠ χ) :
    (M ⊓ centralBlock P V χ).map (LieSubmodule.Quotient.mk' (N ⊓ centralBlock P V χ)) = ⊥ := by
  have ht := centralBlock_eq_bot_of_ne P hχ
    (centralBlock_eq_top_of_verma_surjective P μ e.toLieModuleHom e.surjective)
  let g := centralBlockStepEquiv P N M hM χ
  apply le_antisymm _ bot_le
  intro v hv
  have hz : g ⟨v, hv⟩ = 0 := by
    apply Subtype.ext
    simpa only [ht, LieSubmodule.mem_bot, ZeroMemClass.coe_zero] using (g ⟨v, hv⟩).property
  have hv0 := g.injective (hz.trans (map_zero g).symm)
  exact congrArg Subtype.val hv0

/-- Nonzero restricted factors are exactly those whose actual Verma character matches.
The forward implication uses exactness; the reverse uses the nonzero Verma highest vector. -/
theorem centralBlockStep_ne_bot_iff (N M : LieSubmodule K P.KacMoodyAlgebra V)
    (hM : IsCategoryO P M) (μ : Dual K H)
    (e : VermaModule P μ ≃ₗ⁅K,P.KacMoodyAlgebra⁆ M.map (LieSubmodule.Quotient.mk' N))
    (χ : 𝓩 →ₐ[K] K) :
    (M ⊓ centralBlock P V χ).map (LieSubmodule.Quotient.mk' (N ⊓ centralBlock P V χ)) ≠ ⊥ ↔
      centralCharacter P μ = χ := by
  constructor
  · intro hn
    by_contra hχ
    exact hn (centralBlockStep_eq_bot P N M hM μ e χ hχ)
  · intro hχ hz
    let g := centralBlockStepVermaEquiv P N M hM μ e χ hχ
    have hg : g (hwv P μ) = 0 := by
      apply Subtype.ext
      simpa only [hz, LieSubmodule.mem_bot, ZeroMemClass.coe_zero] using (g (hwv P μ)).property
    exact hwv_ne_zero P μ (g.injective (hg.trans (map_zero g).symm))

end VermaFactors

section TensorFiltration
variable [CharZero K] {Z : Type*} [AddCommGroup Z] [Module K Z]
  [LieRingModule P.KacMoodyAlgebra Z] [LieModule K P.KacMoodyAlgebra Z]
  [FiniteDimensional K Z]

omit [IsAlgClosed K] in
/-- Tensor-Verma modules are in category O from finite-dimensionality and Cartan
 diagonalizability of the coefficient module alone. -/
theorem isCategoryO_tensorVerma_of_finite (hZ : IsHDiagonalizable P Z) (Λ : Dual K H) :
    IsCategoryO P (VermaModule P Λ ⊗[K] Z) :=
  (VermaModule.isCategoryO P Λ).tensorProduct (hZ.isCategoryO_of_finite P)

open Classical in
omit [IsAlgClosed K] [FiniteDimensional K Z] in
/-- The multiplicity of a weight among the retained steps is its actual weight dimension
if the shifted Verma character is the target, and zero otherwise. Repeated weights count
separately; this does not classify characters or identify distinct weights. -/
theorem retained_tensorVerma_weight_count {n : ℕ} (wt : Fin n → Dual K H)
    (hc : ∀ μ, Nat.card {j // wt j = μ} = finrank K (weightSpace P Z μ))
    (Λ μ : Dual K H) (χ : 𝓩 →ₐ[K] K) :
    Nat.card {j : Fin n // wt j = μ ∧ centralCharacter P (Λ + wt j) = χ} =
      if centralCharacter P (Λ + μ) = χ then finrank K (weightSpace P Z μ) else 0 := by
  classical
  by_cases h : centralCharacter P (Λ + μ) = χ
  · rw [ite_eq_left h, ← hc μ]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun j => ⟨fun hj => hj.1, fun hj => ⟨hj, hj ▸ h⟩⟩)
  · rw [ite_eq_right h]
    have he : IsEmpty {j : Fin n // wt j = μ ∧ centralCharacter P (Λ + wt j) = χ} :=
      ⟨fun j => h (j.property.1 ▸ j.property.2)⟩
    exact Nat.card_of_isEmpty

open Classical in
/-- The actual finite tensor-Verma standard filtration projects to a filtration of each
full-central block. Its canonical quotient images are the corresponding shifted Verma
modules exactly at the target character, and zero at different characters. The pieces are
literally images under the published full-Lie projection, not merely formal characters.
The original strict filtration and weight counts are retained; the projected filtration
may repeat at killed steps and also covers the zero coefficient module. Reconstructed. -/
theorem exists_centralTensorVermaFiltration (hZ : IsHDiagonalizable P Z) (Λ : Dual K H)
    (χ : 𝓩 →ₐ[K] K) :
    ∃ (N : Fin (finrank K Z + 1) →
        LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ ⊗[K] Z))
      (wt : Fin (finrank K Z) → Dual K H),
      StrictMono N ∧ N 0 = ⊥ ∧ N (Fin.last (finrank K Z)) = ⊤ ∧
      (∀ j, Nonempty (VermaModule P (Λ + wt j) ≃ₗ⁅K,P.KacMoodyAlgebra⁆
        (N j.succ).map (LieSubmodule.Quotient.mk' (N j.castSucc)))) ∧
      (∀ μ, Nat.card {j // wt j = μ} = finrank K (weightSpace P Z μ)) ∧
      let F := fun k => N k ⊓ centralBlock P (VermaModule P Λ ⊗[K] Z) χ
      Monotone F ∧ F 0 = ⊥ ∧
      F (Fin.last (finrank K Z)) = centralBlock P (VermaModule P Λ ⊗[K] Z) χ ∧
      (∀ k, F k = (N k).map (centralBlockProjection P
        ((isCategoryO_tensorVerma_of_finite P hZ Λ).isCentralLocallyFinite P) χ)) ∧
      (∀ j, (centralCharacter P (Λ + wt j) = χ →
        Nonempty (VermaModule P (Λ + wt j) ≃ₗ⁅K,P.KacMoodyAlgebra⁆
          (F j.succ).map (LieSubmodule.Quotient.mk' (F j.castSucc)))) ∧
        (centralCharacter P (Λ + wt j) ≠ χ →
          (F j.succ).map (LieSubmodule.Quotient.mk' (F j.castSucc)) = ⊥)) ∧
      ∀ μ, Nat.card {j // wt j = μ ∧ centralCharacter P (Λ + wt j) = χ} =
        if centralCharacter P (Λ + μ) = χ then finrank K (weightSpace P Z μ) else 0 := by
  classical
  obtain ⟨N, wt, hmono, hzero, hlast, hstep, hcount⟩ :=
    exists_tensorVermaStandardFiltration P hZ Λ
  have hV := isCategoryO_tensorVerma_of_finite P hZ Λ
  refine ⟨N, wt, hmono, hzero, hlast, hstep, hcount, ?_⟩
  refine ⟨fun i j hij => inf_le_inf_right _ (hmono.monotone hij),
    by simp [hzero], by simp [hlast], ?_, ?_, ?_⟩
  · intro k
    exact (map_centralBlockProjection_eq_inf P hV (N k) χ).symm
  · intro j
    obtain ⟨e⟩ := hstep j
    exact ⟨fun hχ => ⟨centralBlockStepVermaEquiv P _ _ (hV.lieSubmodule _) _ e χ hχ⟩,
      fun hχ => centralBlockStep_eq_bot P _ _ (hV.lieSubmodule _) _ e χ hχ⟩
  · exact fun μ => retained_tensorVerma_weight_count P wt hcount Λ μ χ

end TensorFiltration
end Matrix.Realization.KacMoodyAlgebra
