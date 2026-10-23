/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CentralIdempotent
import LieLean.Algebra.Lie.KacMoody.ProjectiveFunctorBlock

/-!
# Composites of translation functors as summands of tensoring functors

A composite of two translation functors `M ↦ pr_{χ₂}(pr_{χ₁}(M ⊗ L) ⊗ L')` is the image of the
idempotent `translationIdem` of `M ⊗ (L ⊗ L')`, built from the block projections. On finitely
many finitely generated modules of `𝒪` at once, `translationIdem` is the value of a natural
transformation of `− ⊗ (L ⊗ L')` on all modules: block projections act there as central elements
(`exists_rep_eq_centralBlockProjection₂`), and the action of a central element is natural
(`TensorNatTrans.ofCentral`). This puts wall-crossing functors in the form to which Humphreys'
Theorem 10.7 applies (`exists_inverse_of_block`).

## Main definitions

* `UniversalEnvelopingAlgebra.centralActionHom`: the action of a central element of `U(L)`.
* `UniversalEnvelopingAlgebra.TensorNatTrans.ofCentral`: its natural transformation of `− ⊗ V`.
* `UniversalEnvelopingAlgebra.TensorNatTrans.rTensor`: `φ ⊗ X : − ⊗ (V ⊗ X) → − ⊗ (W ⊗ X)`.
* `Matrix.Realization.KacMoodyAlgebra.translationIdem`: the idempotent
  `pr_{χ₂} ∘ (pr_{χ₁} ⊗ 1)` of `M ⊗ (L ⊗ L')`.

## Main results

* `LieSubmodule.exists_finset_lieSpan_tmul_eq_top`: `V ⊗ W` is finitely generated when `V` is
  and `W` is finite-dimensional.
* `Matrix.Realization.KacMoodyAlgebra.translationIdem_idempotent`.
* `Matrix.Realization.KacMoodyAlgebra.exists_tensorNatTrans_app_eq_translationIdem`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §7.15, §10.8 (the presentation of translation functors as summands of
  tensoring functors by central elements is reconstructed).
-/

noncomputable section

open Module TensorProduct

namespace UniversalEnvelopingAlgebra

universe u v w

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  {V W X : Type*} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
  [AddCommGroup X] [Module K X] [LieRingModule L X] [LieModule K L X]

/-- The action of a central element of `U(L)` on an `L`-module, as a morphism of `L`-modules. -/
def centralActionHom (z : UniversalEnvelopingAlgebra K L)
    (hz : z ∈ Subalgebra.center K (UniversalEnvelopingAlgebra K L)) (M : Type*)
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] : M →ₗ⁅K,L⁆ M where
  toLinearMap := actionHom (R := K) (L := L) M z
  map_lie' {x m} := by
    have h := congrArg (fun u ↦ actionHom (R := K) (L := L) M u m)
      (Subalgebra.mem_center_iff.mp hz (ι K x))
    simp only [map_mul, Module.End.mul_apply, actionHom_ι, LieModule.toEnd_apply_apply] at h
    exact h.symm

@[simp] theorem centralActionHom_apply (z : UniversalEnvelopingAlgebra K L)
    (hz : z ∈ Subalgebra.center K (UniversalEnvelopingAlgebra K L)) (M : Type*)
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] (m : M) :
    centralActionHom z hz M m = actionHom (R := K) (L := L) M z m := rfl

namespace TensorNatTrans

variable (V) in
/-- The action of a central element of `U(L)` on `M ⊗ V`, natural in `M`. -/
def ofCentral (z : UniversalEnvelopingAlgebra K L)
    (hz : z ∈ Subalgebra.center K (UniversalEnvelopingAlgebra K L)) :
    TensorNatTrans.{u, v, w} K L V V where
  app M _ _ _ _ := centralActionHom z hz (M ⊗[K] V)
  naturality _ _ _ _ _ _ _ _ _ _ f t :=
    LieModuleHom.map_actionHom (TensorProduct.LieModule.map f (LieModuleHom.id : V →ₗ⁅K,L⁆ V))
      z t

@[simp] theorem ofCentral_app (z : UniversalEnvelopingAlgebra K L)
    (hz : z ∈ Subalgebra.center K (UniversalEnvelopingAlgebra K L)) (M : Type w)
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] :
    (ofCentral V z hz).app M = centralActionHom z hz (M ⊗[K] V) := rfl

omit [LieModule K L V] [LieModule K L W] [LieModule K L X] in
theorem rTensor_assoc_tmul {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] (f : M →ₗ[K] N) (y : M ⊗[K] W) (x : X) :
    f.rTensor (W ⊗[K] X) (TensorProduct.assoc K M W X (y ⊗ₜ x)) =
      TensorProduct.assoc K N W X (f.rTensor W y ⊗ₜ x) := by
  induction y with
  | add a b ha hb => rw [add_tmul, map_add, map_add, ha, hb, map_add, add_tmul, map_add]
  | tmul m w => rfl

variable (X) in
/-- `φ ⊗ X`: the natural transformation `M ⊗ (V ⊗ X) ≅ (M ⊗ V) ⊗ X → (M ⊗ W) ⊗ X ≅ M ⊗ (W ⊗ X)`
induced by `φ : − ⊗ V → − ⊗ W`. -/
def rTensor (φ : TensorNatTrans.{u, v, w} K L V W) :
    TensorNatTrans.{u, v, w} K L (V ⊗[K] X) (W ⊗[K] X) where
  app M _ _ _ _ := (LieModuleEquiv.tensorAssoc K L M W X : (M ⊗[K] W) ⊗[K] X →ₗ⁅K,L⁆ _).comp
    ((TensorProduct.LieModule.map (φ.app M) (LieModuleHom.id : X →ₗ⁅K,L⁆ X)).comp
      ((LieModuleEquiv.tensorAssoc K L M V X).symm : M ⊗[K] (V ⊗[K] X) →ₗ⁅K,L⁆ _))
  naturality M N _ _ _ _ _ _ _ _ f t := by
    induction t with
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
    | tmul m y =>
      induction y with
      | add a b ha hb => rw [tmul_add, map_add, map_add, ha, hb, map_add, map_add]
      | tmul v x =>
        change f.rTensor (W ⊗[K] X) (TensorProduct.assoc K M W X (φ.app M (m ⊗ₜ v) ⊗ₜ x)) =
          TensorProduct.assoc K N W X (φ.app N (f m ⊗ₜ v) ⊗ₜ x)
        rw [rTensor_assoc_tmul]
        congr 2
        exact φ.naturality M N f (m ⊗ₜ v)

theorem rTensor_app_apply (φ : TensorNatTrans.{u, v, w} K L V W) (M : Type w) [AddCommGroup M]
    [Module K M] [LieRingModule L M] [LieModule K L M] (t : M ⊗[K] (V ⊗[K] X)) :
    (rTensor X φ).app M t = LieModuleEquiv.tensorAssoc K L M W X
      (TensorProduct.LieModule.map (φ.app M) (LieModuleHom.id : X →ₗ⁅K,L⁆ X)
        ((LieModuleEquiv.tensorAssoc K L M V X).symm t)) := rfl

end TensorNatTrans

end UniversalEnvelopingAlgebra

namespace LieSubmodule

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]

/-- If `V` is generated by a finite set and `W` is finite-dimensional, `V ⊗ W` is generated by a
finite set. -/
theorem exists_finset_lieSpan_tmul_eq_top [FiniteDimensional K W] {s : Finset V}
    (hs : lieSpan K L (s : Set V) = ⊤) :
    ∃ t : Finset (V ⊗[K] W), lieSpan K L (t : Set (V ⊗[K] W)) = ⊤ := by
  classical
  let b := Module.finBasis K W
  let t : Finset (V ⊗[K] W) := (s ×ˢ Finset.univ).image fun p ↦ p.1 ⊗ₜ b p.2
  refine ⟨t, ?_⟩
  set N := lieSpan K L (t : Set (V ⊗[K] W))
  -- every `m ⊗ w` with `m ∈ s` lies in `N`
  have hs' : ∀ m ∈ s, ∀ w, m ⊗ₜ[K] w ∈ N := by
    intro m hm w
    rw [← b.sum_repr w, tmul_sum]
    refine N.sum_mem fun i _ ↦ ?_
    rw [tmul_smul]
    exact N.smul_mem _ (subset_lieSpan (Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨(m, i), Finset.mem_product.mpr ⟨hm, Finset.mem_univ _⟩, rfl⟩)))
  -- the vectors `m` with `m ⊗ w ∈ N` for all `w` form a Lie submodule
  let S : LieSubmodule K L V :=
    { carrier := {m | ∀ w, m ⊗ₜ[K] w ∈ N}
      add_mem' := fun ha hb w ↦ by rw [add_tmul]; exact N.add_mem (ha w) (hb w)
      zero_mem' := fun w ↦ by rw [zero_tmul]; exact N.zero_mem
      smul_mem' := fun c m hm w ↦ by rw [← smul_tmul']; exact N.smul_mem c (hm w)
      lie_mem := fun {x m} hm w ↦ by
        have h : ⁅x, m ⊗ₜ[K] w⁆ = ⁅x, m⁆ ⊗ₜ[K] w + m ⊗ₜ[K] ⁅x, w⁆ :=
          TensorProduct.LieModule.lie_tmul_right x m w
        have h' : ⁅x, m⁆ ⊗ₜ[K] w = ⁅x, m ⊗ₜ[K] w⁆ - m ⊗ₜ[K] ⁅x, w⁆ := by
          rw [h, add_sub_cancel_right]
        rw [h']
        exact N.sub_mem (N.lie_mem (hm w)) (hm _) }
  have hS : lieSpan K L (s : Set V) ≤ S := by
    rw [lieSpan_le]
    exact fun m hm ↦ hs' m hm
  rw [hs] at hS
  rw [eq_top_iff]
  rintro y -
  induction y with
  | add a b ha hb => exact N.add_mem ha hb
  | tmul m w => exact hS (mem_top m) w

end LieSubmodule

namespace Matrix.Realization.KacMoodyAlgebra

open UniversalEnvelopingAlgebra VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {L L' : Type*} [AddCommGroup L] [Module K L] [LieRingModule P.KacMoodyAlgebra L]
  [LieModule K P.KacMoodyAlgebra L] [AddCommGroup L'] [Module K L']
  [LieRingModule P.KacMoodyAlgebra L'] [LieModule K P.KacMoodyAlgebra L']

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

variable [CharZero K] [IsAlgClosed K]

/-- The idempotent `pr_{χ₂} ∘ (pr_{χ₁} ⊗ 1)` of `M ⊗ (L ⊗ L')` ≅ `(M ⊗ L) ⊗ L'`, whose image is
the composite of translation functors `pr_{χ₂}(pr_{χ₁}(M ⊗ L) ⊗ L')`. -/
def translationIdem (hL : IsCategoryO P L) (hL' : IsCategoryO P L') (χ₁ χ₂ : 𝓩 →ₐ[K] K)
    (M : Type*) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    (hM : IsCategoryO P M) : M ⊗[K] (L ⊗[K] L') →ₗ⁅K,𝔤⁆ M ⊗[K] (L ⊗[K] L') :=
  (LieModuleEquiv.tensorAssoc K 𝔤 M L L' : (M ⊗[K] L) ⊗[K] L' →ₗ⁅K,𝔤⁆ _).comp
    ((((hM.tensorProduct hL).tensorProduct hL').centralBlockProjection P χ₂).comp
      ((TensorProduct.LieModule.map ((hM.tensorProduct hL).centralBlockProjection P χ₁)
        (LieModuleHom.id : L' →ₗ⁅K,𝔤⁆ L')).comp
        ((LieModuleEquiv.tensorAssoc K 𝔤 M L L').symm : M ⊗[K] (L ⊗[K] L') →ₗ⁅K,𝔤⁆ _)))

/-- `translationIdem` is idempotent. -/
theorem translationIdem_idempotent (hL : IsCategoryO P L) (hL' : IsCategoryO P L')
    (χ₁ χ₂ : 𝓩 →ₐ[K] K) (M : Type*) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M] (hM : IsCategoryO P M) (t : M ⊗[K] (L ⊗[K] L')) :
    translationIdem P hL hL' χ₁ χ₂ M hM (translationIdem P hL hL' χ₁ χ₂ M hM t) =
      translationIdem P hL hL' χ₁ χ₂ M hM t := by
  set hML := hM.tensorProduct hL
  set hMLL := hML.tensorProduct hL'
  set p₁ := TensorProduct.LieModule.map (hML.centralBlockProjection P χ₁)
    (LieModuleHom.id : L' →ₗ⁅K,𝔤⁆ L')
  set p₂ := hMLL.centralBlockProjection P χ₂
  have h₁ : ∀ y, p₁ (p₁ y) = p₁ y := by
    intro y
    induction y with
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul m l =>
      change hML.centralBlockProjection P χ₁ (hML.centralBlockProjection P χ₁ m) ⊗ₜ l =
        hML.centralBlockProjection P χ₁ m ⊗ₜ l
      exact congrArg (· ⊗ₜ l)
        (centralBlockProjection_self P _ χ₁ (centralBlockProjection_mem P _ χ₁ m))
  have h₂ : ∀ y, p₂ (p₂ y) = p₂ y := fun y ↦
    centralBlockProjection_self P _ χ₂ (centralBlockProjection_mem P _ χ₂ y)
  have h₁₂ : ∀ y, p₁ (p₂ y) = p₂ (p₁ y) := fun y ↦
    DFunLike.congr_fun (IsCategoryO.centralBlockProjection_natural P hMLL hMLL p₁ χ₂) y
  change LieModuleEquiv.tensorAssoc K 𝔤 M L L' (p₂ (p₁ ((LieModuleEquiv.tensorAssoc K 𝔤 M L L').symm
      (LieModuleEquiv.tensorAssoc K 𝔤 M L L' (p₂ (p₁ _)))))) =
    LieModuleEquiv.tensorAssoc K 𝔤 M L L' (p₂ (p₁ _))
  rw [LieModuleEquiv.symm_apply_apply, h₁₂, h₁, h₂]

universe w₀

/-- The natural transformation `z₂ ∘ (z₁ ⊗ L')` is `translationIdem` at every module of `𝒪` on
which `z₁` and `z₂` act as the block projections. -/
theorem ofCentral_comp_rTensor_app_eq_translationIdem (hL : IsCategoryO P L)
    (hL' : IsCategoryO P L') (χ₁ χ₂ : 𝓩 →ₐ[K] K) (z₁ z₂ : 𝓩) (M : Type w₀) [AddCommGroup M]
    [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsCategoryO P M)
    (h₁ : ∀ v, rep P (M ⊗[K] L) (z₁ : 𝓤) v =
      (hM.tensorProduct hL).centralBlockProjection P χ₁ v)
    (h₂ : ∀ v, rep P ((M ⊗[K] L) ⊗[K] L') (z₂ : 𝓤) v =
      ((hM.tensorProduct hL).tensorProduct hL').centralBlockProjection P χ₂ v) :
    ((TensorNatTrans.ofCentral.{_, _, w₀} (L ⊗[K] L') (z₂ : 𝓤) z₂.property).comp
      (TensorNatTrans.rTensor L' (TensorNatTrans.ofCentral L (z₁ : 𝓤) z₁.property))).app M =
        translationIdem P hL hL' χ₁ χ₂ M hM := by
  ext x
  set e := LieModuleEquiv.tensorAssoc K 𝔤 M L L'
  have hmap : ∀ y : M ⊗[K] L ⊗[K] L', TensorProduct.LieModule.map
      ((TensorNatTrans.ofCentral L (z₁ : 𝓤) z₁.property).app M)
      (LieModuleHom.id : L' →ₗ⁅K,𝔤⁆ L') y =
      TensorProduct.LieModule.map ((hM.tensorProduct hL).centralBlockProjection P χ₁)
      (LieModuleHom.id : L' →ₗ⁅K,𝔤⁆ L') y := by
    intro y
    induction y with
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul m l => exact congrArg (· ⊗ₜ l) (h₁ m)
  have hassoc := LieModuleHom.map_actionHom e.toLieModuleHom (z₂ : 𝓤)
    (TensorProduct.LieModule.map ((TensorNatTrans.ofCentral L (z₁ : 𝓤) z₁.property).app M)
      (LieModuleHom.id : L' →ₗ⁅K,𝔤⁆ L') (e.symm x))
  refine hassoc.symm.trans ?_
  change e (rep P _ (z₂ : 𝓤) _) = e _
  rw [h₂, hmap]
  rfl

/-- **Composites of translation functors are natural summands**: for finitely generated `M`, `N`
in `𝒪` and finite-dimensional `L`, `L'` in `𝒪`, a single natural transformation of
`− ⊗ (L ⊗ L')` on all modules is `translationIdem` at `M` and at `N`. -/
theorem exists_tensorNatTrans_app_eq_translationIdem [FiniteDimensional K L]
    [FiniteDimensional K L'] (hL : IsCategoryO P L) (hL' : IsCategoryO P L') (χ₁ χ₂ : 𝓩 →ₐ[K] K)
    {M N : Type w₀} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    [AddCommGroup N] [Module K N] [LieRingModule 𝔤 N] [LieModule K 𝔤 N]
    (hM : IsCategoryO P M) {s : Finset M} (hs : LieSubmodule.lieSpan K 𝔤 (s : Set M) = ⊤)
    (hN : IsCategoryO P N) {t : Finset N} (ht : LieSubmodule.lieSpan K 𝔤 (t : Set N) = ⊤) :
    ∃ e : TensorNatTrans.{_, _, w₀} K 𝔤 (L ⊗[K] L') (L ⊗[K] L'),
      e.app M = translationIdem P hL hL' χ₁ χ₂ M hM ∧
        e.app N = translationIdem P hL hL' χ₁ χ₂ N hN := by
  obtain ⟨s₁, hs₁⟩ := LieSubmodule.exists_finset_lieSpan_tmul_eq_top (W := L) hs
  obtain ⟨t₁, ht₁⟩ := LieSubmodule.exists_finset_lieSpan_tmul_eq_top (W := L) ht
  obtain ⟨s₂, hs₂⟩ := LieSubmodule.exists_finset_lieSpan_tmul_eq_top (W := L') hs₁
  obtain ⟨t₂, ht₂⟩ := LieSubmodule.exists_finset_lieSpan_tmul_eq_top (W := L') ht₁
  obtain ⟨z₁, hzM₁, hzN₁⟩ := exists_rep_eq_centralBlockProjection₂ P
    ((hM.tensorProduct hL).isCentralLocallyFinite P) hs₁
    ((hN.tensorProduct hL).isCentralLocallyFinite P) ht₁ χ₁
  obtain ⟨z₂, hzM₂, hzN₂⟩ := exists_rep_eq_centralBlockProjection₂ P
    (((hM.tensorProduct hL).tensorProduct hL').isCentralLocallyFinite P) hs₂
    (((hN.tensorProduct hL).tensorProduct hL').isCentralLocallyFinite P) ht₂ χ₂
  exact ⟨_, ofCentral_comp_rTensor_app_eq_translationIdem P hL hL' χ₁ χ₂ z₁ z₂ M hM hzM₁ hzM₂,
    ofCentral_comp_rTensor_app_eq_translationIdem P hL hL' χ₁ χ₂ z₁ z₂ N hN hzN₁ hzN₂⟩

end Matrix.Realization.KacMoodyAlgebra
