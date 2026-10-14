/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.DualityFunctor
import LieLean.Algebra.Lie.KacMoody.TranslationSelfDual
import LieLean.Algebra.Lie.RelativeExt

/-!
# Duality and `Ext¹`

Humphreys, GSM 94, Theorem 3.2 (e): `Ext_𝒪(M, N) ≅ Ext_𝒪(N^∨, M^∨)` for `M, N ∈ 𝒪`. Here `Ext_𝒪`
is the relative `Ext¹` `LieModule.ExtOne (h P)` (see `KacMoody/ExtProjective.lean`).

## Main definitions

* `LieModule.ExtOne.mapComap`: functoriality of `ExtOne` in both variables.
* `Matrix.Realization.KacMoodyAlgebra.dualCocycle`: the dual `x ↦ (α ↦ α ∘ c(σ x))` of a cocycle
  `c` for `(M, N)`, a cocycle for `(N^∨, M^∨)` (it corresponds to the dual extension
  `0 → M^∨ → E^∨ → N^∨ → 0`).
* `Matrix.Realization.KacMoodyAlgebra.extOneRestrictedDual`: the induced map on `ExtOne`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.bijective_extOneRestrictedDual`: **Theorem 3.2 (e)**.
* `Matrix.Realization.KacMoodyAlgebra.nonempty_extOne_irreducibleModule_equiv`:
  `Ext_𝒪(L(λ), L(μ)) ≅ Ext_𝒪(L(μ), L(λ))`.

## Proof notes

Dualizing twice is the transport of cocycles along the isomorphisms `V ≅ V^∨∨` of Theorem 3.2 (a)
(`extOneRestrictedDual_extOneRestrictedDual`); hence the map is injective for all `M, N ∈ 𝒪`,
and, applied to `(N^∨, M^∨)`, also surjective.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.2.
-/

noncomputable section

open Module

/-! ### Functoriality of `ExtOne` -/

namespace LieModule

variable {K H L : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  (φ : H →ₗ[K] L)
  {M N M' N' M'' N'' : Type*}
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [AddCommGroup M'] [Module K M'] [LieRingModule L M'] [LieModule K L M']
  [AddCommGroup N'] [Module K N'] [LieRingModule L N'] [LieModule K L N']
  [AddCommGroup M''] [Module K M''] [LieRingModule L M''] [LieModule K L M'']
  [AddCommGroup N''] [Module K N''] [LieRingModule L N''] [LieModule K L N'']

namespace ExtOne

/-- `c ↦ (x ↦ g ∘ c(x) ∘ f)` on cocycles, for morphisms `f : M' → M`, `g : N → N'`. -/
def cocycleMapComap (g : N →ₗ⁅K,L⁆ N') (f : M' →ₗ⁅K,L⁆ M) :
    extCocycles φ M N →ₗ[K] extCocycles φ M' N' where
  toFun c := ⟨fun x ↦ (g : N →ₗ[K] N') ∘ₗ c.1 x ∘ₗ (f : M' →ₗ[K] M),
    ⟨fun x y ↦ by
      dsimp only
      rw [extCocycles.map_add', LinearMap.add_comp, LinearMap.comp_add],
    fun t x ↦ by
      dsimp only
      rw [extCocycles.map_smul', LinearMap.smul_comp, LinearMap.comp_smul],
    fun a ↦ by
      dsimp only
      rw [extCocycles.map_apply_eq_zero, LinearMap.zero_comp, LinearMap.comp_zero],
    fun x y ↦ by
      ext m
      simp only [LinearMap.comp_apply, LieHom.lie_apply, LinearMap.sub_apply,
        LieModuleHom.coe_toLinearMap, extCocycles.apply_lie_apply, map_sub,
        LieModuleHom.map_lie]⟩⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp] lemma cocycleMapComap_apply (g : N →ₗ⁅K,L⁆ N') (f : M' →ₗ⁅K,L⁆ M)
    (c : extCocycles φ M N) (x : L) (m : M') :
    (cocycleMapComap φ g f c).1 x m = g (c.1 x (f m)) := rfl

/-- `ExtOne` is a functor in both variables: `ExtOne φ M N → ExtOne φ M' N'` for morphisms
`f : M' → M`, `g : N → N'`. -/
def mapComap (g : N →ₗ⁅K,L⁆ N') (f : M' →ₗ⁅K,L⁆ M) : ExtOne φ M N →ₗ[K] ExtOne φ M' N' :=
  Submodule.mapQ _ _ (cocycleMapComap φ g f) <| by
    rintro _ ⟨p, rfl⟩
    refine ⟨⟨(g : N →ₗ[K] N') ∘ₗ (p : M →ₗ[K] N) ∘ₗ (f : M' →ₗ[K] M), fun a m ↦ ?_⟩, ?_⟩
    · simp only [LinearMap.comp_apply, LieModuleHom.coe_toLinearMap, LieModuleHom.map_lie,
        p.2 a (f m)]
    · ext x m
      simp [extCoboundary, LieHom.lie_apply]

@[simp] lemma mapComap_mk (g : N →ₗ⁅K,L⁆ N') (f : M' →ₗ⁅K,L⁆ M) (c : extCocycles φ M N) :
    mapComap φ g f (mk c) = mk (cocycleMapComap φ g f c) := rfl

lemma mapComap_comp (g : N →ₗ⁅K,L⁆ N') (f : M' →ₗ⁅K,L⁆ M) (g' : N' →ₗ⁅K,L⁆ N'')
    (f' : M'' →ₗ⁅K,L⁆ M') (y : ExtOne φ M N) :
    mapComap φ g' f' (mapComap φ g f y) = mapComap φ (g'.comp g) (f.comp f') y := by
  obtain ⟨c, rfl⟩ := mk_surjective y
  rfl

lemma mapComap_id (y : ExtOne φ M N) :
    mapComap φ (LieModuleHom.id : N →ₗ⁅K,L⁆ N) (LieModuleHom.id : M →ₗ⁅K,L⁆ M) y = y := by
  obtain ⟨c, rfl⟩ := mk_surjective y
  rfl

/-- Isomorphisms `M ≅ M'`, `N ≅ N'` give `ExtOne φ M N ≅ ExtOne φ M' N'`. -/
def congr (e : M ≃ₗ⁅K,L⁆ M') (e' : N ≃ₗ⁅K,L⁆ N') : ExtOne φ M N ≃ₗ[K] ExtOne φ M' N' :=
  { mapComap φ e'.toLieModuleHom e.symm.toLieModuleHom with
    invFun := mapComap φ e'.symm.toLieModuleHom e.toLieModuleHom
    left_inv := fun y ↦ by
      have h1 : e'.symm.toLieModuleHom.comp e'.toLieModuleHom = LieModuleHom.id := by
        ext; simp
      have h2 : e.symm.toLieModuleHom.comp e.toLieModuleHom = LieModuleHom.id := by
        ext; simp
      change mapComap φ _ _ (mapComap φ _ _ y) = y
      rw [mapComap_comp, h1, h2, mapComap_id]
    right_inv := fun y ↦ by
      have h1 : e'.toLieModuleHom.comp e'.symm.toLieModuleHom = LieModuleHom.id := by
        ext; simp
      have h2 : e.toLieModuleHom.comp e.symm.toLieModuleHom = LieModuleHom.id := by
        ext; simp
      change mapComap φ _ _ (mapComap φ _ _ y) = y
      rw [mapComap_comp, h1, h2, mapComap_id] }

/-- `mapComap` along isomorphisms is injective. -/
lemma injective_mapComap (e' : N ≃ₗ⁅K,L⁆ N') (e : M' ≃ₗ⁅K,L⁆ M) :
    Function.Injective (mapComap φ e'.toLieModuleHom e.toLieModuleHom) := by
  intro y y' hy
  have h1 : e'.symm.toLieModuleHom.comp e'.toLieModuleHom = LieModuleHom.id := by ext; simp
  have h2 : e.toLieModuleHom.comp e.symm.toLieModuleHom = LieModuleHom.id := by ext; simp
  have := congrArg (mapComap φ e'.symm.toLieModuleHom e.symm.toLieModuleHom) hy
  rwa [mapComap_comp, mapComap_comp, h1, h2, mapComap_id, mapComap_id] at this

lemma mapComap_mapComap_symm (e' : N ≃ₗ⁅K,L⁆ N') (f : M' →ₗ⁅K,L⁆ M) (y : ExtOne φ M N') :
    mapComap φ e'.toLieModuleHom LieModuleHom.id (mapComap φ e'.symm.toLieModuleHom f y) =
      mapComap φ LieModuleHom.id f y := by
  have h1 : e'.toLieModuleHom.comp e'.symm.toLieModuleHom = LieModuleHom.id := by ext; simp
  rw [mapComap_comp, h1]
  rfl

end ExtOne

end LieModule

/-! ### Dual cocycles -/

namespace Matrix.Realization.KacMoodyAlgebra

open LieModule TwistedDual

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {M N : Type*} [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M]
  [AddCommGroup N] [Module K N] [LieRingModule P.KacMoodyAlgebra N]
  [LieModule K P.KacMoodyAlgebra N]

local notation "𝔤" => KacMoodyAlgebra P

variable {P}

/-- For a cocycle `c`, `y ∈ 𝔤_γ` and a functional `α` of weight `ν`, `α ∘ c(y)` has weight
`ν - γ`. -/
lemma comp_cocycle_mem_weightSpace (c : extCocycles (h P) M N) {γ ν : Dual K H} {y : 𝔤}
    (hy : y ∈ rootSpace P γ) {α : TwistedDual P N}
    (hα : α ∈ weightSpaceOfMap (TwistedDual P N) (h P) ν) :
    (TwistedDual.toDual P M).symm (TwistedDual.toDual P N α ∘ₗ c.1 y) ∈
      weightSpaceOfMap (TwistedDual P M) (h P) (ν - γ) := by
  rw [TwistedDual.mem_weightSpaceOfMap_iff]
  intro a m
  have h1 := extCocycles.apply_lie_apply c (h P a) y m
  rw [hy a, extCocycles.map_smul', extCocycles.map_apply_eq_zero, LinearMap.zero_apply,
    lie_zero, LinearMap.zero_apply, sub_zero, sub_zero, LinearMap.smul_apply] at h1
  have h2 : c.1 y ⁅h P a, m⁆ = ⁅h P a, c.1 y m⁆ - γ a • c.1 y m := by
    rw [h1]; abel
  simp only [LinearEquiv.apply_symm_apply, LinearMap.comp_apply]
  rw [h2, map_sub, map_smul, TwistedDual.mem_weightSpaceOfMap_iff.mp hα, smul_eq_mul,
    LinearMap.sub_apply]
  ring

/-- For a cocycle `c` and `α ∈ N^∨`, `α ∘ c(y) ∈ M^∨`. -/
lemma comp_cocycle_mem_restrictedDual (c : extCocycles (h P) M N) (y : 𝔤)
    {α : TwistedDual P N} (hα : α ∈ restrictedDual P N) :
    (TwistedDual.toDual P M).symm (TwistedDual.toDual P N α ∘ₗ c.1 y) ∈ restrictedDual P M := by
  have hy : y ∈ ⨆ γ, rootSpace P γ :=
    (iSup₂_le fun γ _ ↦ le_iSup (rootSpace P) γ :
      ⨆ γ ∈ AuxLieAlgebra.allWeights P, rootSpace P γ ≤ ⨆ γ, rootSpace P γ)
      (iSup_rootSpace_eq_top P ▸ Submodule.mem_top)
  rw [mem_restrictedDual] at hα ⊢
  induction hα using Submodule.iSup_induction' with
  | mem ν α hα =>
    induction hy using Submodule.iSup_induction' with
    | mem γ y hy => exact Submodule.mem_iSup_of_mem _ (comp_cocycle_mem_weightSpace c hy hα)
    | zero => simp [extCocycles.map_zero']
    | add y y' _ _ h1 h2 =>
      rw [extCocycles.map_add', LinearMap.comp_add, map_add]
      exact Submodule.add_mem _ h1 h2
  | zero => simp
  | add α α' _ _ h1 h2 =>
    rw [map_add, LinearMap.add_comp, map_add]
    exact Submodule.add_mem _ h1 h2

/-- The dual `α ↦ α ∘ c(σ x)` of a cocycle `c`, at `x ∈ 𝔤`. -/
def dualCocycleLin (c : extCocycles (h P) M N) (x : 𝔤) :
    restrictedDual P N →ₗ[K] restrictedDual P M where
  toFun α := ⟨(TwistedDual.toDual P M).symm
      (TwistedDual.toDual P N α.1 ∘ₗ c.1 (transpose P x)),
    comp_cocycle_mem_restrictedDual c _ α.2⟩
  map_add' _ _ := restrictedDual_ext P fun _ ↦ rfl
  map_smul' _ _ := restrictedDual_ext P fun _ ↦ rfl

@[simp] lemma toDual_dualCocycleLin (c : extCocycles (h P) M N) (x : 𝔤)
    (α : restrictedDual P N) (m : M) :
    TwistedDual.toDual P M (dualCocycleLin c x α).1 m =
      TwistedDual.toDual P N α.1 (c.1 (transpose P x) m) := rfl

/-- The dual cocycle `x ↦ (α ↦ α ∘ c(σ x))`, a cocycle for `(N^∨, M^∨)`. -/
def dualCocycle (c : extCocycles (h P) M N) :
    extCocycles (h P) (restrictedDual P N) (restrictedDual P M) :=
  ⟨fun x ↦ dualCocycleLin c x,
    ⟨fun x y ↦ LinearMap.ext fun α ↦ restrictedDual_ext P fun m ↦ by
      simp [extCocycles.map_add'],
    fun t x ↦ LinearMap.ext fun α ↦ restrictedDual_ext P fun m ↦ by
      simp [extCocycles.map_smul'],
    fun a ↦ LinearMap.ext fun α ↦ restrictedDual_ext P fun m ↦ by
      simp [extCocycles.map_apply_eq_zero],
    fun x y ↦ LinearMap.ext fun α ↦ restrictedDual_ext P fun m ↦ by
      simp only [toDual_dualCocycleLin, LieHom.lie_apply, LinearMap.sub_apply,
        LieSubmodule.coe_sub, map_sub, LieSubmodule.coe_bracket, TwistedDual.lie_apply,
        transpose_lie, extCocycles.apply_lie_apply]
      abel⟩⟩

@[simp] lemma toDual_dualCocycle (c : extCocycles (h P) M N) (x : 𝔤)
    (α : restrictedDual P N) (m : M) :
    TwistedDual.toDual P M ((dualCocycle c).1 x α).1 m =
      TwistedDual.toDual P N α.1 (c.1 (transpose P x) m) := rfl

/-- For an `𝔥`-equivariant `f : M → N` and `α ∈ N^∨`, `α ∘ f ∈ M^∨`. -/
lemma comp_relHom_mem_restrictedDual (f : relHom (h P) M N) {α : TwistedDual P N}
    (hα : α ∈ restrictedDual P N) :
    (TwistedDual.toDual P M).symm (TwistedDual.toDual P N α ∘ₗ (f : M →ₗ[K] N)) ∈
      restrictedDual P M := by
  rw [mem_restrictedDual] at hα ⊢
  induction hα using Submodule.iSup_induction' with
  | mem ν α hα =>
    refine Submodule.mem_iSup_of_mem ν ?_
    rw [TwistedDual.mem_weightSpaceOfMap_iff]
    intro a m
    simp only [LinearEquiv.apply_symm_apply, LinearMap.comp_apply]
    rw [f.2 a m, TwistedDual.mem_weightSpaceOfMap_iff.mp hα]
  | zero => simp
  | add α α' _ _ h1 h2 =>
    rw [map_add, LinearMap.add_comp, map_add]
    exact Submodule.add_mem _ h1 h2

/-- The dual `α ↦ α ∘ f` of an `𝔥`-equivariant linear map, as a linear map. -/
def dualRelHomLin (f : relHom (h P) M N) : restrictedDual P N →ₗ[K] restrictedDual P M where
  toFun α := ⟨(TwistedDual.toDual P M).symm (TwistedDual.toDual P N α.1 ∘ₗ (f : M →ₗ[K] N)),
    comp_relHom_mem_restrictedDual f α.2⟩
  map_add' _ _ := restrictedDual_ext P fun _ ↦ rfl
  map_smul' _ _ := restrictedDual_ext P fun _ ↦ rfl

@[simp] lemma toDual_dualRelHomLin (f : relHom (h P) M N) (α : restrictedDual P N) (m : M) :
    TwistedDual.toDual P M (dualRelHomLin f α).1 m =
      TwistedDual.toDual P N α.1 ((f : M →ₗ[K] N) m) := rfl

/-- The dual `α ↦ α ∘ f` of an `𝔥`-equivariant linear map. -/
def dualRelHom (f : relHom (h P) M N) : relHom (h P) (restrictedDual P N) (restrictedDual P M) :=
  ⟨dualRelHomLin f, fun a α ↦ restrictedDual_ext P fun m ↦ by
    rw [LieSubmodule.coe_bracket, TwistedDual.lie_apply, toDual_dualRelHomLin,
      toDual_dualRelHomLin, LieSubmodule.coe_bracket, TwistedDual.lie_apply, transpose_h,
      f.2 a m]⟩

@[simp] lemma toDual_dualRelHom (f : relHom (h P) M N) (α : restrictedDual P N) (m : M) :
    TwistedDual.toDual P M ((dualRelHom f : restrictedDual P N →ₗ[K] restrictedDual P M) α).1 m =
      TwistedDual.toDual P N α.1 ((f : M →ₗ[K] N) m) := rfl

/-- The dual of a coboundary is a coboundary. -/
lemma dualCocycle_extCoboundary (f : relHom (h P) M N) :
    dualCocycle (extCoboundary (h P) M N f) = extCoboundary (h P) _ _ (-dualRelHom f) := by
  refine Subtype.ext (funext fun x ↦ LinearMap.ext fun α ↦ restrictedDual_ext P fun m ↦ ?_)
  change TwistedDual.toDual P N α.1 (⁅transpose P x, (f : M →ₗ[K] N)⁆ m) =
    TwistedDual.toDual P M (⁅x, ((-dualRelHom f : relHom (h P) _ _) :
      restrictedDual P N →ₗ[K] restrictedDual P M)⁆ α).1 m
  simp only [LieHom.lie_apply, LieSubmodule.coe_sub, map_sub, LinearMap.sub_apply,
    LieSubmodule.coe_bracket, TwistedDual.lie_apply, Submodule.coe_neg, LinearMap.neg_apply,
    LieSubmodule.coe_neg, map_neg, toDual_dualRelHom]
  abel

/-- Dualizing cocycles, as a linear map. -/
def dualCocycleHom :
    extCocycles (h P) M N →ₗ[K] extCocycles (h P) (restrictedDual P N) (restrictedDual P M) where
  toFun := dualCocycle
  map_add' _ _ := Subtype.ext (funext fun _ ↦ LinearMap.ext fun _ ↦
    restrictedDual_ext P fun _ ↦ by simp)
  map_smul' _ _ := Subtype.ext (funext fun _ ↦ LinearMap.ext fun _ ↦
    restrictedDual_ext P fun _ ↦ by simp)

variable (P M N) in
/-- The map `Ext¹(M, N) → Ext¹(N^∨, M^∨)` induced by duality: the class of an extension
`0 → N → E → M → 0` goes to the class of `0 → M^∨ → E^∨ → N^∨ → 0`. -/
def extOneRestrictedDual :
    ExtOne (h P) M N →ₗ[K] ExtOne (h P) (restrictedDual P N) (restrictedDual P M) :=
  Submodule.mapQ _ _ dualCocycleHom <| by
    rintro _ ⟨f, rfl⟩
    exact ⟨-dualRelHom f, (dualCocycle_extCoboundary f).symm⟩

@[simp] lemma extOneRestrictedDual_mk (c : extCocycles (h P) M N) :
    extOneRestrictedDual P M N (ExtOne.mk c) = ExtOne.mk (dualCocycle c) := rfl

/-- On cocycles, dualizing twice is the transport along `M ≅ M^∨∨`, `N ≅ N^∨∨`. -/
lemma dualCocycle_dualCocycle (hM : IsCategoryO P M) (hN : IsCategoryO P N)
    (c : extCocycles (h P) M N) :
    ExtOne.cocycleMapComap (h P) LieModuleHom.id (restrictedDoubleDualEquiv hM).toLieModuleHom
        (dualCocycle (dualCocycle c)) =
      ExtOne.cocycleMapComap (h P) (restrictedDoubleDualEquiv hN).toLieModuleHom
        LieModuleHom.id c := by
  refine Subtype.ext (funext fun x ↦ LinearMap.ext fun m ↦ restrictedDual_ext P fun α ↦ ?_)
  change TwistedDual.toDual P (restrictedDual P N) ((dualCocycle (dualCocycle c)).1 x
      (restrictedDoubleDualEquiv hM m)).1 α =
    TwistedDual.toDual P (restrictedDual P N) (restrictedDoubleDualEquiv hN (c.1 x m)).1 α
  rw [toDual_dualCocycle, restrictedDoubleDualEquiv_apply, toDual_restrictedDoubleDual,
    toDual_dualCocycle, transpose_transpose, restrictedDoubleDualEquiv_apply,
    toDual_restrictedDoubleDual]

/-- Dualizing twice is the transport along `M ≅ M^∨∨`, `N ≅ N^∨∨`. -/
theorem extOneRestrictedDual_extOneRestrictedDual (hM : IsCategoryO P M) (hN : IsCategoryO P N)
    (y : ExtOne (h P) M N) :
    ExtOne.mapComap (h P) LieModuleHom.id (restrictedDoubleDualEquiv hM).toLieModuleHom
        (extOneRestrictedDual P (restrictedDual P N) (restrictedDual P M)
          (extOneRestrictedDual P M N y)) =
      ExtOne.mapComap (h P) (restrictedDoubleDualEquiv hN).toLieModuleHom LieModuleHom.id y := by
  induction y using Submodule.Quotient.induction_on with
  | H c => exact congrArg ExtOne.mk (dualCocycle_dualCocycle hM hN c)

theorem injective_extOneRestrictedDual (hM : IsCategoryO P M) (hN : IsCategoryO P N) :
    Function.Injective (extOneRestrictedDual P M N) := by
  intro y y' hy
  have := congrArg (fun z ↦ ExtOne.mapComap (h P) LieModuleHom.id
    (restrictedDoubleDualEquiv hM).toLieModuleHom
    (extOneRestrictedDual P (restrictedDual P N) (restrictedDual P M) z)) hy
  simp only [extOneRestrictedDual_extOneRestrictedDual hM hN] at this
  exact ExtOne.injective_mapComap (h P) (restrictedDoubleDualEquiv hN)
    (LieModuleEquiv.refl) this

/-- **Humphreys, GSM 94, Theorem 3.2 (e).** For `M, N ∈ 𝒪`, duality induces an isomorphism
`Ext_𝒪(M, N) ≅ Ext_𝒪(N^∨, M^∨)`. Humphreys states this for `𝔤` semisimple over `ℂ`. -/
theorem bijective_extOneRestrictedDual (hM : IsCategoryO P M) (hN : IsCategoryO P N) :
    Function.Bijective (extOneRestrictedDual P M N) := by
  refine ⟨injective_extOneRestrictedDual hM hN, fun z ↦ ⟨ExtOne.mapComap (h P)
    (restrictedDoubleDualEquiv hN).symm.toLieModuleHom
    (restrictedDoubleDualEquiv hM).toLieModuleHom
    (extOneRestrictedDual P (restrictedDual P N) (restrictedDual P M) z),
    injective_extOneRestrictedDual (isCategoryO_restrictedDual hN)
      (isCategoryO_restrictedDual hM) ?_⟩⟩
  refine ExtOne.injective_mapComap (h P) LieModuleEquiv.refl (restrictedDoubleDualEquiv hM) ?_
  change ExtOne.mapComap (h P) LieModuleHom.id (restrictedDoubleDualEquiv hM).toLieModuleHom
      (extOneRestrictedDual P (restrictedDual P N) (restrictedDual P M) _) =
    ExtOne.mapComap (h P) LieModuleHom.id (restrictedDoubleDualEquiv hM).toLieModuleHom
      (extOneRestrictedDual P (restrictedDual P N) (restrictedDual P M) z)
  exact (extOneRestrictedDual_extOneRestrictedDual hM hN _).trans
    (ExtOne.mapComap_mapComap_symm _ _ _ _)

/-- **Humphreys, GSM 94, Theorem 3.2 (e)**, as a linear isomorphism
`Ext_𝒪(M, N) ≅ Ext_𝒪(N^∨, M^∨)`. -/
def extOneRestrictedDualEquiv (hM : IsCategoryO P M) (hN : IsCategoryO P N) :
    ExtOne (h P) M N ≃ₗ[K] ExtOne (h P) (restrictedDual P N) (restrictedDual P M) :=
  LinearEquiv.ofBijective _ (bijective_extOneRestrictedDual hM hN)

variable (P) in
/-- **Humphreys, GSM 94, Theorem 3.2 (e)**, for simple modules:
`Ext_𝒪(L(λ), L(μ)) ≅ Ext_𝒪(L(μ), L(λ))`, via `L(λ) ≅ L(λ)^∨`. -/
theorem nonempty_extOne_irreducibleModule_equiv (Λ μ : Dual K H) :
    Nonempty (ExtOne (h P) (IrreducibleModule P Λ) (IrreducibleModule P μ) ≃ₗ[K]
      ExtOne (h P) (IrreducibleModule P μ) (IrreducibleModule P Λ)) :=
  ⟨(extOneRestrictedDualEquiv (IrreducibleModule.isCategoryO P Λ)
    (IrreducibleModule.isCategoryO P μ)).trans (ExtOne.congr (h P)
      (IrreducibleModule.equivRestrictedDual P μ).symm
      (IrreducibleModule.equivRestrictedDual P Λ).symm)⟩

end Matrix.Realization.KacMoodyAlgebra
