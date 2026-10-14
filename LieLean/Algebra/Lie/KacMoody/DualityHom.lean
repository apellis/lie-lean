/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.DualityFunctor
import Mathlib.Algebra.Lie.DirectSum

/-!
# Duality on morphisms and direct sums

Humphreys, GSM 94, Theorem 3.2 (d): `(⨁ᵢ Mᵢ)^∨ ≅ ⨁ᵢ Mᵢ^∨`, and the dual of an indecomposable
module in `𝒪` is indecomposable. The second statement uses that `f ↦ f^∨` is a bijection
`Hom(M, N) ≅ Hom(N^∨, M^∨)` for `M, N ∈ 𝒪` (duality is an anti-equivalence, Theorem 3.2 (a)).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.restrictedDualHomEquiv`: `Hom(M, N) ≅ Hom(N^∨, M^∨)` for
  `M, N ∈ 𝒪`.
* `Matrix.Realization.KacMoodyAlgebra.restrictedDualDirectSumEquiv`: `(⨁ᵢ Mᵢ)^∨ ≅ ⨁ᵢ Mᵢ^∨` for a
  finite direct sum.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.indecomposable_restrictedDual`: the dual of an
  indecomposable module in `𝒪` is indecomposable.

## Implementation notes

As in `KacMoody/ProjectiveDecomposition.lean`, "indecomposable" is encoded as: nontrivial, and
every idempotent endomorphism is `0` or the identity.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.2.
-/

noncomputable section

open Module LieModule DirectSum

namespace Matrix.Realization.KacMoodyAlgebra

open TwistedDual

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]

local notation "𝔤" => KacMoodyAlgebra P

/-! ### Duality on morphisms -/

section Hom

/-- The duality functor on morphisms, as a linear map `Hom(V, W) → Hom(W^∨, V^∨)`. -/
def restrictedDualMapLin :
    (V →ₗ⁅K,𝔤⁆ W) →ₗ[K] (restrictedDual P W →ₗ⁅K,𝔤⁆ restrictedDual P V) where
  toFun f := restrictedDualMap P f
  map_add' _ _ := LieModuleHom.ext fun _ ↦ restrictedDual_ext P fun _ ↦ by simp
  map_smul' _ _ := LieModuleHom.ext fun _ ↦ restrictedDual_ext P fun _ ↦ by simp

@[simp] lemma restrictedDualMapLin_apply (f : V →ₗ⁅K,𝔤⁆ W) :
    restrictedDualMapLin P f = restrictedDualMap P f := rfl

/-- Duality is contravariant: `(g ∘ f)^∨ = f^∨ ∘ g^∨`. -/
lemma restrictedDualMap_comp {U : Type*} [AddCommGroup U] [Module K U] [LieRingModule 𝔤 U]
    [LieModule K 𝔤 U] (g : V →ₗ⁅K,𝔤⁆ W) (f : U →ₗ⁅K,𝔤⁆ V) :
    restrictedDualMap P (g.comp f) = (restrictedDualMap P f).comp (restrictedDualMap P g) :=
  rfl

lemma restrictedDualMap_id : restrictedDualMap P (LieModuleHom.id : V →ₗ⁅K,𝔤⁆ V) =
    LieModuleHom.id :=
  rfl

/-- Duality is faithful on modules that are sums of their weight spaces. -/
theorem injective_restrictedDualMapLin (hW : ⨆ μ, weightSpaceOfMap W (h P) μ = ⊤) :
    Function.Injective (restrictedDualMapLin (V := V) (W := W) P) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  refine LieModuleHom.ext fun v ↦ injective_restrictedDoubleDual hW ?_
  rw [_root_.zero_apply, map_zero]
  refine restrictedDual_ext P fun α ↦ ?_
  have := congrArg (fun F : restrictedDual P V ↦ TwistedDual.toDual P V F.1 v)
    (LieModuleHom.congr_fun hf α)
  simpa using this

/-- Duality is full on `𝒪`: every morphism `W^∨ → V^∨` is the dual of a morphism `V → W`. -/
theorem surjective_restrictedDualMapLin (hV : IsCategoryO P V) (hW : IsCategoryO P W) :
    Function.Surjective (restrictedDualMapLin (V := V) (W := W) P) := by
  intro b
  let a : V →ₗ⁅K,𝔤⁆ W := (restrictedDoubleDualEquiv hW).symm.toLieModuleHom.comp
    ((restrictedDualMap P b).comp (restrictedDoubleDualEquiv hV).toLieModuleHom)
  refine ⟨a, LieModuleHom.ext fun α ↦ restrictedDual_ext P fun v ↦ ?_⟩
  have ha : restrictedDoubleDual hW.iSup_weightSpaceOfMap_eq_top (a v) =
      restrictedDualMap P b (restrictedDoubleDual hV.iSup_weightSpaceOfMap_eq_top v) := by
    rw [← restrictedDoubleDualEquiv_apply hW]
    exact (restrictedDoubleDualEquiv hW).apply_symm_apply _
  have := congrArg (fun Ψ : restrictedDual P (restrictedDual P W) ↦
    TwistedDual.toDual P (restrictedDual P W) Ψ.1 α) ha
  simpa using this

/-- For `V, W ∈ 𝒪`, duality is a linear isomorphism `Hom(V, W) ≅ Hom(W^∨, V^∨)` (Humphreys,
GSM 94, Theorem 3.2 (a): duality is an anti-equivalence of `𝒪`). -/
def restrictedDualHomEquiv (hV : IsCategoryO P V) (hW : IsCategoryO P W) :
    (V →ₗ⁅K,𝔤⁆ W) ≃ₗ[K] (restrictedDual P W →ₗ⁅K,𝔤⁆ restrictedDual P V) :=
  LinearEquiv.ofBijective (restrictedDualMapLin P)
    ⟨injective_restrictedDualMapLin P hW.iSup_weightSpaceOfMap_eq_top,
      surjective_restrictedDualMapLin P hV hW⟩

@[simp] lemma restrictedDualHomEquiv_apply (hV : IsCategoryO P V) (hW : IsCategoryO P W)
    (f : V →ₗ⁅K,𝔤⁆ W) : restrictedDualHomEquiv P hV hW f = restrictedDualMap P f :=
  rfl

/-- **Humphreys, GSM 94, Theorem 3.2 (d), second part.** The dual of an indecomposable module in
`𝒪` is indecomposable (nontrivial, with only the idempotent endomorphisms `0` and `1`). Humphreys
states this for `𝔤` semisimple over `ℂ`. -/
theorem IsCategoryO.indecomposable_restrictedDual (hV : IsCategoryO P V) [Nontrivial V]
    (hind : ∀ a : V →ₗ⁅K,𝔤⁆ V, a.comp a = a → a = 0 ∨ a = LieModuleHom.id) :
    Nontrivial (restrictedDual P V) ∧
      ∀ e : restrictedDual P V →ₗ⁅K,𝔤⁆ restrictedDual P V, e.comp e = e →
        e = 0 ∨ e = LieModuleHom.id := by
  have hd := hV.iSup_weightSpaceOfMap_eq_top
  refine ⟨?_, fun e he ↦ ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine hv (injective_restrictedDoubleDual hd ?_)
    rw [map_zero]
    exact restrictedDual_ext P fun α ↦ by rw [Subsingleton.elim α 0]; simp
  obtain ⟨a, rfl⟩ := surjective_restrictedDualMapLin P hV hV e
  rw [restrictedDualMapLin_apply] at he ⊢
  have haa : a.comp a = a := injective_restrictedDualMapLin P hd (by
    rw [restrictedDualMapLin_apply, restrictedDualMapLin_apply, restrictedDualMap_comp]
    exact he)
  rcases hind a haa with rfl | rfl
  · exact Or.inl (LieModuleHom.ext fun _ ↦ restrictedDual_ext P fun _ ↦ by simp)
  · exact Or.inr rfl

end Hom

/-! ### Finite direct sums -/

section DirectSum

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (M : κ → Type*) [∀ i, AddCommGroup (M i)]
  [∀ i, Module K (M i)] [∀ i, LieRingModule P.KacMoodyAlgebra (M i)]
  [∀ i, LieModule K P.KacMoodyAlgebra (M i)]

/-- The map `(⨁ᵢ Mᵢ)^∨ → ⨁ᵢ Mᵢ^∨`, `φ ↦ (φ ∘ ιᵢ)ᵢ`. -/
def restrictedDualDirectSumHom :
    restrictedDual P (⨁ i, M i) →ₗ⁅K,𝔤⁆ ⨁ i, restrictedDual P (M i) :=
  ∑ i, (lieModuleOf K κ 𝔤 (fun i ↦ restrictedDual P (M i)) i).comp
    (restrictedDualMap P (lieModuleOf K κ 𝔤 M i))

/-- The map `⨁ᵢ Mᵢ^∨ → (⨁ᵢ Mᵢ)^∨`, `(φᵢ)ᵢ ↦ Σᵢ φᵢ ∘ πᵢ`. -/
def restrictedDualDirectSumInv :
    (⨁ i, restrictedDual P (M i)) →ₗ⁅K,𝔤⁆ restrictedDual P (⨁ i, M i) :=
  ∑ i, (restrictedDualMap P (lieModuleComponent K κ 𝔤 M i)).comp
    (lieModuleComponent K κ 𝔤 (fun i ↦ restrictedDual P (M i)) i)

omit [CharZero K] [DecidableEq κ] in
lemma lieModuleHom_sum_apply {X Y : Type*} [AddCommGroup X] [Module K X] [LieRingModule 𝔤 X]
    [AddCommGroup Y] [Module K Y] [LieRingModule 𝔤 Y] (f : κ → X →ₗ⁅K,𝔤⁆ Y) (x : X) :
    (∑ i, f i) x = ∑ i, f i x := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, _root_.add_apply, ih]

lemma restrictedDualDirectSumHom_apply (φ : restrictedDual P (⨁ i, M i)) (i : κ) :
    restrictedDualDirectSumHom P M φ i = restrictedDualMap P (lieModuleOf K κ 𝔤 M i) φ := by
  rw [restrictedDualDirectSumHom, lieModuleHom_sum_apply, DirectSum.sum_apply,
    Finset.sum_eq_single i]
  · exact DirectSum.of_eq_same _ _
  · intro j _ hj
    exact DirectSum.of_eq_of_ne _ _ _ hj.symm
  · simp

omit [DecidableEq κ] in
lemma toDual_restrictedDualDirectSumInv (ψ : ⨁ i, restrictedDual P (M i)) (m : ⨁ i, M i) :
    TwistedDual.toDual P _ (restrictedDualDirectSumInv P M ψ).1 m =
      ∑ i, TwistedDual.toDual P (M i) (ψ i).1 (m i) := by
  rw [restrictedDualDirectSumInv, lieModuleHom_sum_apply]
  have : ((∑ i, ((restrictedDualMap P (lieModuleComponent K κ 𝔤 M i)).comp
      (lieModuleComponent K κ 𝔤 (fun i ↦ restrictedDual P (M i)) i)) ψ :
        restrictedDual P (⨁ i, M i)) : TwistedDual P (⨁ i, M i)) =
      ∑ i, (((restrictedDualMap P (lieModuleComponent K κ 𝔤 M i)).comp
        (lieModuleComponent K κ 𝔤 (fun i ↦ restrictedDual P (M i)) i)) ψ :
          TwistedDual P (⨁ i, M i)) :=
    map_sum (restrictedDual P (⨁ i, M i)).incl _ _
  rw [this, map_sum, LinearMap.sum_apply]
  rfl

/-- **Humphreys, GSM 94, Theorem 3.2 (d).** `(⨁ᵢ Mᵢ)^∨ ≅ ⨁ᵢ Mᵢ^∨` for a finite direct sum.
Humphreys states this for two summands in `𝒪`, `𝔤` semisimple over `ℂ`. -/
def restrictedDualDirectSumEquiv :
    restrictedDual P (⨁ i, M i) ≃ₗ⁅K,𝔤⁆ ⨁ i, restrictedDual P (M i) :=
  { restrictedDualDirectSumHom P M with
    invFun := restrictedDualDirectSumInv P M
    left_inv := fun φ ↦ restrictedDual_ext P fun m ↦ by
      change TwistedDual.toDual P _ (restrictedDualDirectSumInv P M
        (restrictedDualDirectSumHom P M φ)).1 m = _
      rw [toDual_restrictedDualDirectSumInv]
      simp_rw [restrictedDualDirectSumHom_apply, toDual_restrictedDualMap]
      rw [← map_sum]
      congr 1
      conv_rhs => rw [← DirectSum.sum_univ_of m]
      rfl
    right_inv := fun ψ ↦ by
      ext j : 1
      change restrictedDualDirectSumHom P M (restrictedDualDirectSumInv P M ψ) j = ψ j
      rw [restrictedDualDirectSumHom_apply]
      refine restrictedDual_ext P fun x ↦ ?_
      rw [toDual_restrictedDualMap, toDual_restrictedDualDirectSumInv,
        Finset.sum_eq_single j (fun i _ hi ↦ ?_) (by simp)]
      · change TwistedDual.toDual P (M j) (ψ j).1 ((DirectSum.of M j x) j) = _
        rw [DirectSum.of_eq_same]
      · change TwistedDual.toDual P (M i) (ψ i).1 ((DirectSum.of M j x) i) = 0
        rw [DirectSum.of_eq_of_ne j i x hi, map_zero] }

end DirectSum

end Matrix.Realization.KacMoodyAlgebra
