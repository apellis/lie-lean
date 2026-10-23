/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BlockProjectiveFunctorClassification
import LieLean.Algebra.Lie.KacMoody.TranslationTensorNatTrans

/-!
# Sums and composites of projective functors on a block

Bernstein–Gelfand's Theorem 3.4 (ii) says that `F ↦ F^K`, the action of a projective functor on
the Grothendieck group, is additive and multiplicative: `(F ⊕ G)^K = F^K + G^K` and
`(FG)^K = F^K G^K`. On a block both are statements about the characters of the values `F(M)`
(`[F(M)] = F^K [M]`), and both come from isomorphisms of values.

* Sums. If `F₁ = e₁(− ⊗ V)` is a summand of `F = e(− ⊗ V)` with complement `F₂ = (e - e₁)(− ⊗ V)`,
  then `F(M)` is an extension of `F₂(M)` by `F₁(M)`, so `ch F(M) = ch F₁(M) + ch F₂(M)`
  (`BlockProjectiveFunctor.character_eq_add`). Every direct sum of two functors `e₁(− ⊗ V₁)`,
  `e₂(− ⊗ V₂)` is of this form inside `− ⊗ (V₁ ⊕ V₂)`.
* Composites. If `G = e(− ⊗ V)` on the block of `λ` takes values in the block of `μ`
  (`BlockProjectiveFunctor.MapsTo`) and `F = e'(− ⊗ W)` is a projective functor on the block of
  `μ`, the composite `FG` is the projective functor `e''(− ⊗ (V ⊗ W))` on the block of `λ` with
  `e''_M = e'_{G(M)} ∘ (e_M ⊗ 1)` (`BlockProjectiveFunctor.comp`), and
  `(FG)(M) ≅ F(G(M))` (`BlockProjectiveFunctor.nonempty_comp_equiv`), so
  `ch (FG)(M) = ch F(G(M))` (`BlockProjectiveFunctor.character_comp`). Its idempotents are the
  components of the natural transformation `(t' ⊗ −) ∘ (t ⊗ W)` of `− ⊗ (V ⊗ W)`
  (`UniversalEnvelopingAlgebra.TensorNatTrans.lTensor`, `TensorNatTrans.rTensor`).

The hypothesis `MapsTo` is what makes the composite of functors given on single blocks defined;
for functors on all of `𝒪` it is supplied by composing with the projection onto the block of `μ`.

## Main definitions

* `UniversalEnvelopingAlgebra.TensorNatTrans.lTensor`: `V ⊗ φ : − ⊗ (V ⊗ W) → − ⊗ (V ⊗ W')`.
* `Matrix.Realization.KacMoodyAlgebra.BlockProjectiveFunctor.MapsTo`.
* `Matrix.Realization.KacMoodyAlgebra.BlockProjectiveFunctor.comp`: the composite `FG`.

## Main results

* `BlockProjectiveFunctor.character_eq_add`: **Bernstein–Gelfand Thm. 3.4 (ii)**, sums.
* `BlockProjectiveFunctor.nonempty_comp_equiv`, `BlockProjectiveFunctor.character_comp`:
  **Bernstein–Gelfand Thm. 3.4 (ii)**, composites.

## References

* J. N. Bernstein, S. I. Gelfand, *Tensor products of finite and infinite dimensional
  representations of semisimple Lie algebras*, Compositio Math. **41** (1980), 245–285,
  Thm. 3.4 (ii).
* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8.
-/

noncomputable section

open Module UniversalEnvelopingAlgebra TensorProduct

namespace UniversalEnvelopingAlgebra.TensorNatTrans

universe u v w

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  {V : Type w} {W W' : Type*} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
  [AddCommGroup W'] [Module K W'] [LieRingModule L W'] [LieModule K L W']

variable (V) in
/-- `V ⊗ φ`: the natural transformation `M ⊗ (V ⊗ W) ≅ (M ⊗ V) ⊗ W → (M ⊗ V) ⊗ W' ≅
M ⊗ (V ⊗ W')` given by the component of `φ : − ⊗ W → − ⊗ W'` at `M ⊗ V`. -/
def lTensor (φ : TensorNatTrans.{u, v, w} K L W W') :
    TensorNatTrans.{u, v, w} K L (V ⊗[K] W) (V ⊗[K] W') where
  app M _ _ _ _ := (LieModuleEquiv.tensorAssoc K L M V W' : (M ⊗[K] V) ⊗[K] W' →ₗ⁅K,L⁆ _).comp
    ((φ.app (M ⊗[K] V)).comp
      ((LieModuleEquiv.tensorAssoc K L M V W).symm : M ⊗[K] (V ⊗[K] W) →ₗ⁅K,L⁆ _))
  naturality M N _ _ _ _ _ _ _ _ f t := by
    have h := φ.naturality (M ⊗[K] V) (N ⊗[K] V)
      (TensorProduct.LieModule.map f (LieModuleHom.id : V →ₗ⁅K,L⁆ V))
      ((TensorProduct.assoc K M V W).symm t)
    change f.rTensor (V ⊗[K] W') (TensorProduct.assoc K M V W'
        (φ.app (M ⊗[K] V) ((TensorProduct.assoc K M V W).symm t))) =
      TensorProduct.assoc K N V W' (φ.app (N ⊗[K] V)
        ((TensorProduct.assoc K N V W).symm (f.rTensor (V ⊗[K] W) t)))
    rw [LinearMap.rTensor_tensor, LinearMap.rTensor_tensor]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact congrArg _ h

theorem lTensor_app_apply (φ : TensorNatTrans.{u, v, w} K L W W') (M : Type w) [AddCommGroup M]
    [Module K M] [LieRingModule L M] [LieModule K L M] (t : M ⊗[K] (V ⊗[K] W)) :
    (lTensor V φ).app M t = LieModuleEquiv.tensorAssoc K L M V W'
      (φ.app (M ⊗[K] V) ((LieModuleEquiv.tensorAssoc K L M V W).symm t)) := rfl

end UniversalEnvelopingAlgebra.TensorNatTrans

namespace LieModuleHom

variable {K L X Y : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup X] [Module K X] [LieRingModule L X] [LieModule K L X]
  [AddCommGroup Y] [Module K Y] [LieRingModule L Y] [LieModule K L Y]

omit [LieAlgebra K L] [LieModule K L X] [LieModule K L Y] in
/-- If `e' = Φ ∘ e ∘ Ψ` with `Ψ ∘ Φ = 1`, then `e'` and `e` have isomorphic images. -/
theorem nonempty_range_comp_equiv (e : X →ₗ⁅K,L⁆ X) (Φ : X →ₗ⁅K,L⁆ Y) (Ψ : Y →ₗ⁅K,L⁆ X)
    (h : ∀ x, Ψ (Φ x) = x) : Nonempty ((Φ.comp (e.comp Ψ)).range ≃ₗ⁅K,L⁆ e.range) := by
  have hmem : ∀ y : e.range, Φ y ∈ (Φ.comp (e.comp Ψ)).range := by
    rintro ⟨_, x, rfl⟩
    exact (LieModuleHom.mem_range _ _).mpr ⟨Φ x, by simp [h]⟩
  let g : e.range →ₗ⁅K,L⁆ (Φ.comp (e.comp Ψ)).range :=
    LieModuleHom.codRestrict _ (Φ.comp e.range.incl) hmem
  refine ⟨(LieModuleEquiv.ofBijective g ⟨fun y₁ y₂ hy ↦ ?_, ?_⟩).symm⟩
  · have hy' : Ψ ((g y₁ : _) : Y) = Ψ ((g y₂ : _) : Y) := by rw [hy]
    change Ψ (Φ (y₁ : X)) = Ψ (Φ (y₂ : X)) at hy'
    rw [h, h] at hy'
    exact Subtype.ext hy'
  · rintro ⟨_, y, rfl⟩
    refine ⟨⟨e (Ψ y), (LieModuleHom.mem_range _ _).mpr ⟨Ψ y, rfl⟩⟩, ?_⟩
    rfl

end LieModuleHom

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ}

namespace BlockProjectiveFunctor

variable {P : Realization A K H} {hA : A.IsFiniteCartan}

local notation "𝔤" => KacMoodyAlgebra P

variable {lam : Dual K H} {V : Type (max u₁ u₂)} [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
  (F : BlockProjectiveFunctor P hA lam V)

/-! ### Sums -/

include P in
/-- **Characters of projective functors are additive** (Bernstein–Gelfand, Thm. 3.4 (ii), sums,
on a block): if `F₁` is a summand of `F` with complement `F₂ = F - F₁`, then
`ch F(M) = ch F₁(M) + ch F₂(M)` for every module `M` of the block. -/
theorem character_eq_add (F₁ : BlockProjectiveFunctor P hA lam V) (h : F₁.IsSummand F)
    {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    (hM : IsInBlock P hA lam M) (hF : IsCategoryO P (F.idem M).range)
    (hF₁ : IsCategoryO P (F₁.idem M).range) (hF₂ : IsCategoryO P ((F.sub F₁ h).idem M).range) :
    hF.character = hF₁.character + hF₂.character := by
  obtain ⟨h₁, h₂⟩ := h M hM
  set e := F.idem M with he_def
  set e₁ := F₁.idem M with he₁_def
  have hee : ∀ x, e (e x) = e x := F.idem_idem M hM
  have he₁e₁ : ∀ x, e₁ (e₁ x) = e₁ x := F₁.idem_idem M hM
  have hee₁ : ∀ x, e (e₁ x) = e₁ x := fun x ↦ LieModuleHom.congr_fun h₁ x
  have he₁e : ∀ x, e₁ (e x) = e₁ x := fun x ↦ LieModuleHom.congr_fun h₂ x
  have hsub : (F.sub F₁ h).idem M = e - e₁ := rfl
  -- the map `F(M) → F₂(M)`, `y ↦ (e - e₁) y`
  have hmem₂ : ∀ y : e.range, (e - e₁) y ∈ ((F.sub F₁ h).idem M).range := fun y ↦
    (LieModuleHom.mem_range _ _).mpr ⟨y, by rw [hsub]⟩
  let g : e.range →ₗ⁅K,𝔤⁆ ((F.sub F₁ h).idem M).range :=
    LieModuleHom.codRestrict _ ((e - e₁).comp e.range.incl) hmem₂
  have hg : Function.Surjective g := by
    rintro ⟨_, z, rfl⟩
    have hz : (e - e₁) z ∈ e.range :=
      (LieModuleHom.mem_range _ _).mpr ⟨(e - e₁) z, by
        simp only [_root_.sub_apply, map_sub, hee, hee₁]⟩
    refine ⟨⟨(e - e₁) z, hz⟩, Subtype.ext ?_⟩
    change (e - e₁) ((e - e₁) z) = ((F.sub F₁ h).idem M) z
    rw [hsub]
    simp only [_root_.sub_apply, map_sub, hee, hee₁, he₁e, he₁e₁, sub_self, sub_zero]
  -- the kernel of `g` is `F₁(M)`
  have hker : ∀ y : e.range, g y = 0 → (y : M ⊗[K] V) = e₁ y := by
    rintro ⟨_, x, rfl⟩ hy
    have hy' : ((g ⟨_, (LieModuleHom.mem_range _ _).mpr ⟨x, rfl⟩⟩ : _) : M ⊗[K] V) = 0 := by
      rw [hy]; rfl
    change e (e x) - e₁ (e x) = 0 at hy'
    rw [hee, he₁e] at hy'
    change e x = e₁ (e x)
    rw [he₁e]
    exact sub_eq_zero.mp hy'
  have hmem₁ : ∀ y : g.ker, ((y : e.range) : M ⊗[K] V) ∈ e₁.range := fun y ↦
    (LieModuleHom.mem_range _ _).mpr ⟨y, (hker y (LieModuleHom.mem_ker.mp y.2)).symm⟩
  let k : g.ker →ₗ⁅K,𝔤⁆ e₁.range :=
    LieModuleHom.codRestrict _ (e.range.incl.comp g.ker.incl) hmem₁
  have hk : Function.Bijective k := by
    refine ⟨fun y₁ y₂ hy ↦ ?_, ?_⟩
    · have hy' : ((k y₁ : _) : M ⊗[K] V) = ((k y₂ : _) : M ⊗[K] V) := by rw [hy]
      exact Subtype.ext (Subtype.ext hy')
    rintro ⟨_, x, rfl⟩
    have hx : e₁ x ∈ e.range := (LieModuleHom.mem_range _ _).mpr ⟨e₁ x, hee₁ x⟩
    have hx' : (⟨e₁ x, hx⟩ : e.range) ∈ g.ker := by
      rw [LieModuleHom.mem_ker]
      refine Subtype.ext ?_
      change (e - e₁) (e₁ x) = 0
      rw [_root_.sub_apply, hee₁, he₁e₁, sub_self]
    exact ⟨⟨_, hx'⟩, rfl⟩
  obtain ⟨q⟩ := LieSubmodule.Quotient.nonempty_lieModuleEquiv_of_surjective g.ker g hg rfl
  rw [hF.character_eq_add g.ker (hF.lieSubmodule g.ker) (hF.quotient g.ker),
    (hF.lieSubmodule g.ker).character_congr hF₁ (LieModuleEquiv.ofBijective k hk),
    (hF.quotient g.ker).character_congr hF₂ q]

/-! ### Composites -/

variable {μ : Dual K H} {W : Type (max u₁ u₂)} [AddCommGroup W] [Module K W]
  [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W]

/-- `F` takes the block of `λ` into the block of `μ`: `F(M)` lies in the block of `μ` for every
module `M` of the block of `λ`. -/
def MapsTo (μ : Dual K H) : Prop :=
  ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M],
    IsInBlock P hA lam M → IsInBlock P hA μ (F.idem M).range

variable (G : BlockProjectiveFunctor P hA μ W)

/-- The inclusion `F(M) ⊗ W → M ⊗ (V ⊗ W)`. -/
def compIncl (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M] : (F.idem M).range ⊗[K] W →ₗ⁅K,𝔤⁆ M ⊗[K] (V ⊗[K] W) :=
  (LieModuleEquiv.tensorAssoc K 𝔤 M V W : (M ⊗[K] V) ⊗[K] W →ₗ⁅K,𝔤⁆ _).comp
    (TensorProduct.LieModule.map (F.idem M).range.incl (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W))

/-- The retraction `M ⊗ (V ⊗ W) → F(M) ⊗ W`. -/
def compRetr (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M] : M ⊗[K] (V ⊗[K] W) →ₗ⁅K,𝔤⁆ (F.idem M).range ⊗[K] W :=
  (TensorProduct.LieModule.map (rangeRetr (F.idem M)) (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W)).comp
    ((LieModuleEquiv.tensorAssoc K 𝔤 M V W).symm : M ⊗[K] (V ⊗[K] W) →ₗ⁅K,𝔤⁆ _)

theorem compRetr_compIncl {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M]
    [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsInBlock P hA lam M)
    (y : (F.idem M).range ⊗[K] W) : F.compRetr M (F.compIncl M y) = y := by
  have he : (F.idem M).comp (F.idem M) = F.idem M := F.idem_mul_idem hM
  change TensorProduct.LieModule.map (rangeRetr (F.idem M)) (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W)
    ((LieModuleEquiv.tensorAssoc K 𝔤 M V W).symm (LieModuleEquiv.tensorAssoc K 𝔤 M V W
      (TensorProduct.LieModule.map (F.idem M).range.incl (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W) y))) = y
  rw [LieModuleEquiv.symm_apply_apply]
  induction y with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul y w =>
    change rangeRetr (F.idem M) ((F.idem M).range.incl y) ⊗ₜ[K] w = y ⊗ₜ[K] w
    rw [rangeRetr_incl he]

/-- The idempotent `e'_{F(M)} ∘ (e_M ⊗ 1)` of `M ⊗ (V ⊗ W)` cutting out `G(F(M))`. -/
def compIdem (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M] : M ⊗[K] (V ⊗[K] W) →ₗ⁅K,𝔤⁆ M ⊗[K] (V ⊗[K] W) :=
  (F.compIncl M).comp ((G.idem (F.idem M).range).comp (F.compRetr M))

/-- The idempotent of `GF` is the component of `(t' ⊗ −) ∘ (e ⊗ W)` for a natural transformation
`t'` of `− ⊗ W` with value `e'_{F(M)}` at `F(M)`. -/
theorem app_eq_compIdem {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M]
    [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (t : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 W W)
    (ht : t.app (F.idem M).range = G.idem (F.idem M).range) (x : M ⊗[K] (V ⊗[K] W)) :
    LieModuleEquiv.tensorAssoc K 𝔤 M V W (t.app (M ⊗[K] V)
      (TensorProduct.LieModule.map (F.idem M) (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W)
        ((LieModuleEquiv.tensorAssoc K 𝔤 M V W).symm x))) = F.compIdem G M x := by
  have h1 : ∀ y : (M ⊗[K] V) ⊗[K] W,
      TensorProduct.LieModule.map (F.idem M) (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W) y =
        TensorProduct.LieModule.map (F.idem M).range.incl (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W)
          (TensorProduct.LieModule.map (rangeRetr (F.idem M)) (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W)
            y) := fun y ↦ by
    induction y with
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
    | tmul a w => rfl
  have h2 := t.naturality _ (M ⊗[K] V) (F.idem M).range.incl
    (TensorProduct.LieModule.map (rangeRetr (F.idem M)) (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W)
      ((LieModuleEquiv.tensorAssoc K 𝔤 M V W).symm x))
  rw [h1]
  change _ = LieModuleEquiv.tensorAssoc K 𝔤 M V W
    (TensorProduct.LieModule.map (F.idem M).range.incl (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W)
      (G.idem (F.idem M).range (TensorProduct.LieModule.map (rangeRetr (F.idem M))
        (LieModuleHom.id : W →ₗ⁅K,𝔤⁆ W) ((LieModuleEquiv.tensorAssoc K 𝔤 M V W).symm x))))
  rw [← ht]
  exact congrArg _ h2.symm

/-- The composite `GF = e''(− ⊗ (V ⊗ W))` of a projective functor `F` on the block of `λ` taking
values in the block of `μ` and a projective functor `G` on the block of `μ`. -/
def comp (hF : F.MapsTo μ) : BlockProjectiveFunctor P hA lam (V ⊗[K] W) where
  idem M _ _ _ _ := F.compIdem G M
  idem_idem M _ _ _ _ hM x := by
    change F.compIncl M (G.idem _ (F.compRetr M (F.compIncl M (G.idem _ (F.compRetr M x))))) =
      F.compIncl M (G.idem _ (F.compRetr M x))
    rw [F.compRetr_compIncl hM, G.idem_idem _ (hF M hM)]
  exists_tensorNatTrans M N _ _ _ _ _ _ _ _ hM hN := by
    obtain ⟨t, htM, htN⟩ := F.exists_tensorNatTrans M N hM hN
    obtain ⟨t', ht'M, ht'N⟩ := G.exists_tensorNatTrans _ _ (hF M hM) (hF N hN)
    refine ⟨(TensorNatTrans.lTensor V t').comp (TensorNatTrans.rTensor W t), ?_, ?_⟩ <;>
    · refine LieModuleHom.ext fun x ↦ ?_
      rw [TensorNatTrans.comp_app, LieModuleHom.comp_apply, TensorNatTrans.lTensor_app_apply,
        TensorNatTrans.rTensor_app_apply, LieModuleEquiv.symm_apply_apply]
      first
        | rw [htM]; exact F.app_eq_compIdem G t' ht'M x
        | rw [htN]; exact F.app_eq_compIdem G t' ht'N x

/-- **The value of a composite** (Bernstein–Gelfand, Thm. 3.4 (ii), composites, on a block):
`(GF)(M) ≅ G(F(M))`. -/
theorem nonempty_comp_equiv (hF : F.MapsTo μ) (M : Type (max u₁ u₂)) [AddCommGroup M]
    [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsInBlock P hA lam M) :
    Nonempty (((F.comp G hF).idem M).range ≃ₗ⁅K,𝔤⁆ (G.idem (F.idem M).range).range) :=
  LieModuleHom.nonempty_range_comp_equiv _ _ _ (F.compRetr_compIncl hM)

include P in
/-- **Characters of composites** (Bernstein–Gelfand, Thm. 3.4 (ii), composites, on a block):
`ch (GF)(M) = ch G(F(M))`, i.e. `(GF)^K = G^K F^K` on the block of `λ`. -/
theorem character_comp (hF : F.MapsTo μ) {M : Type (max u₁ u₂)} [AddCommGroup M]
    [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsInBlock P hA lam M)
    (hGF : IsCategoryO P ((F.comp G hF).idem M).range)
    (hGFM : IsCategoryO P (G.idem (F.idem M).range).range) :
    hGF.character = hGFM.character :=
  hGF.character_congr hGFM (F.nonempty_comp_equiv G hF M hM).some

end BlockProjectiveFunctor

end Matrix.Realization.KacMoodyAlgebra
