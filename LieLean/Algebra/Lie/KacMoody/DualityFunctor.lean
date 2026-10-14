/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.DualVerma

/-!
# Exactness of duality and the double dual

Humphreys, GSM 94, Theorem 3.2: the duality functor `M ↦ M^∨` is exact, and (a) its square is
naturally isomorphic to the identity functor on `𝒪`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.restrictedDoubleDual`: the morphism `V → V^∨∨`,
  `v ↦ (φ ↦ φ(v))`.
* `Matrix.Realization.KacMoodyAlgebra.restrictedDoubleDualEquiv`: `V ≅ V^∨∨` for `V ∈ 𝒪`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.exists_restrictedDualMap_eq`: a functional in `V^∨` vanishing
  on the kernel of `g : V → W` factors through `g`.
* `Matrix.Realization.KacMoodyAlgebra.injective_restrictedDualMap`,
  `Matrix.Realization.KacMoodyAlgebra.exact_restrictedDualMap`: **exactness of duality**
  (Humphreys, GSM 94, §3.2).
* `Matrix.Realization.KacMoodyAlgebra.restrictedDualMap_restrictedDualMap_comp`: naturality of
  `V → V^∨∨`.

## Proof notes

Everything is done one weight space at a time: a weight-`κ` functional on `V` is a functional on
`V_κ` (`weightSpaceTwistedDualEquiv`), and `V_κ ≅ (V_κ)^{**}` when `V_κ` is finite-dimensional.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.2.
-/

noncomputable section

open Module LieModule

namespace Matrix.Realization.KacMoodyAlgebra

open TwistedDual

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {U V W : Type*} [AddCommGroup U] [Module K U] [LieRingModule P.KacMoodyAlgebra U]
  [LieModule K P.KacMoodyAlgebra U]
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]

local notation "𝔤" => KacMoodyAlgebra P

/-! ### Exactness -/

section Exact

omit [CharZero K] in
/-- The restriction `V_κ → W_κ` of a morphism has a linear `t` with `g ∘ t ∘ g = g` on `V_κ`. -/
lemma exists_weightSpace_pseudoInverse (g : V →ₗ⁅K,𝔤⁆ W) (κ : Dual K H) :
    ∃ t : weightSpaceOfMap W (h P) κ →ₗ[K] weightSpaceOfMap V (h P) κ,
      ∀ v (hv : v ∈ weightSpaceOfMap V (h P) κ),
        g (t ⟨g v, map_mem_weightSpaceOfMap P g hv⟩ : V) = g v := by
  let gκ : weightSpaceOfMap V (h P) κ →ₗ[K] weightSpaceOfMap W (h P) κ :=
    ((g : V →ₗ[K] W).comp (weightSpaceOfMap V (h P) κ).subtype).codRestrict _
      fun x ↦ map_mem_weightSpaceOfMap P g x.2
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective gκ.rangeRestrict
    (LinearMap.range_rangeRestrict gκ)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range gκ).subtype
    (Submodule.ker_subtype _)
  refine ⟨s ∘ₗ r, fun v hv ↦ ?_⟩
  have h1 : r ⟨g v, map_mem_weightSpaceOfMap P g hv⟩ = gκ.rangeRestrict ⟨v, hv⟩ :=
    LinearMap.congr_fun hr (gκ.rangeRestrict ⟨v, hv⟩)
  have h2 : gκ (s (gκ.rangeRestrict ⟨v, hv⟩)) = gκ ⟨v, hv⟩ :=
    congrArg Subtype.val (LinearMap.congr_fun hs (gκ.rangeRestrict ⟨v, hv⟩))
  rw [LinearMap.comp_apply, h1]
  exact congrArg Subtype.val h2

/-- A functional `φ ∈ V^∨` vanishing on the kernel of `g : V → W` factors as `φ = ψ ∘ g` with
`ψ ∈ W^∨` (`V`, `W` sums of their weight spaces). -/
theorem exists_restrictedDualMap_eq (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤)
    (hW : ⨆ μ, weightSpaceOfMap W (h P) μ = ⊤) (g : V →ₗ⁅K,𝔤⁆ W) (φ : restrictedDual P V)
    (hφ : ∀ v, g v = 0 → TwistedDual.toDual P V φ.1 v = 0) :
    ∃ ψ : restrictedDual P W, restrictedDualMap P g ψ = φ := by
  choose t ht using exists_weightSpace_pseudoInverse P g
  -- every functional agrees on each `V_κ` with `ψ ∘ g` composed with `v ↦ t (g v)`
  have key : ∀ θ ∈ ⨆ μ, weightSpaceOfMap (TwistedDual P V) (h P) μ,
      ∃ ψ : restrictedDual P W, ∀ κ v (hv : v ∈ weightSpaceOfMap V (h P) κ),
        TwistedDual.toDual P W ψ.1 (g v) =
          TwistedDual.toDual P V θ (t κ ⟨g v, map_mem_weightSpaceOfMap P g hv⟩ : V) := by
    intro θ hθ
    induction hθ using Submodule.iSup_induction' with
    | mem μ θ hθ =>
      let γ : Module.Dual K (weightSpaceOfMap W (h P) μ) :=
        TwistedDual.toDual P V θ ∘ₗ (weightSpaceOfMap V (h P) μ).subtype ∘ₗ t μ
      refine ⟨⟨(TwistedDual.toDual P W).symm (γ ∘ₗ weightProj P hW μ),
        Submodule.mem_iSup_of_mem μ (mem_weightSpace_twistedDual_comp hW μ γ)⟩,
        fun κ v hv ↦ ?_⟩
      change γ (weightProj P hW μ (g v)) = _
      by_cases hκ : κ = μ
      · subst hκ
        rw [weightProj_of_mem hW (map_mem_weightSpaceOfMap P g hv)]
        rfl
      · rw [weightProj_of_mem_ne hW (map_mem_weightSpaceOfMap P g hv) hκ, map_zero,
          TwistedDual.apply_eq_zero_of_ne hθ (t κ _).2 (Ne.symm hκ)]
    | zero => exact ⟨0, fun κ v hv ↦ by simp⟩
    | add θ₁ θ₂ _ _ h₁ h₂ =>
      obtain ⟨ψ₁, e₁⟩ := h₁
      obtain ⟨ψ₂, e₂⟩ := h₂
      exact ⟨ψ₁ + ψ₂, fun κ v hv ↦ by
        simp only [LieSubmodule.coe_add, map_add, LinearMap.add_apply, e₁ κ v hv, e₂ κ v hv]⟩
  obtain ⟨ψ, hψ⟩ := key φ.1 φ.2
  refine ⟨ψ, restrictedDual_ext P fun v ↦ ?_⟩
  rw [toDual_restrictedDualMap]
  have hv : v ∈ ⨆ μ, weightSpaceOfMap V (h P) μ := hV ▸ Submodule.mem_top
  induction hv using Submodule.iSup_induction' with
  | mem κ v hv =>
    rw [hψ κ v hv, ← sub_eq_zero, ← map_sub]
    exact hφ _ (by rw [map_sub, ht κ v hv, sub_self])
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- The dual of a surjection is injective (Humphreys, GSM 94, §3.2). -/
theorem injective_restrictedDualMap (g : V →ₗ⁅K,𝔤⁆ W) (hg : Function.Surjective g) :
    Function.Injective (restrictedDualMap P g) := by
  rw [← LieModuleHom.ker_eq_bot, LieSubmodule.eq_bot_iff]
  intro ψ hψ
  refine restrictedDual_ext P fun w ↦ ?_
  obtain ⟨v, rfl⟩ := hg w
  have := congrArg (fun φ : restrictedDual P V ↦ TwistedDual.toDual P V φ.1 v)
    ((LieModuleHom.mem_ker).mp hψ)
  simpa using this

/-- **Exactness of duality** (Humphreys, GSM 94, §3.2): if `U → V → W` is exact, so is
`W^∨ → V^∨ → U^∨`. -/
theorem exact_restrictedDualMap (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤)
    (hW : ⨆ μ, weightSpaceOfMap W (h P) μ = ⊤) {f : U →ₗ⁅K,𝔤⁆ V} {g : V →ₗ⁅K,𝔤⁆ W}
    (hfg : Function.Exact f g) :
    Function.Exact (restrictedDualMap P g) (restrictedDualMap P f) := by
  intro φ
  constructor
  · intro hφ
    refine exists_restrictedDualMap_eq P hV hW g φ fun v hv ↦ ?_
    obtain ⟨u, rfl⟩ := (hfg v).mp hv
    have := congrArg (fun χ : restrictedDual P U ↦ TwistedDual.toDual P U χ.1 u) hφ
    simpa using this
  · rintro ⟨ψ, rfl⟩
    refine restrictedDual_ext P fun u ↦ ?_
    simp only [toDual_restrictedDualMap, (hfg (f u)).mpr ⟨u, rfl⟩, map_zero]
    rfl

end Exact

/-! ### The double dual -/

section DoubleDual

variable {P}

/-- The evaluation `v ↦ (φ ↦ φ(v))` as a linear map `V → (V^∨)^{*σ}`. -/
def restrictedDoubleDualLin : V →ₗ[K] TwistedDual P (restrictedDual P V) :=
  (TwistedDual.toDual P (restrictedDual P V)).symm.toLinearMap ∘ₗ
    ((TwistedDual.toDual P V).toLinearMap ∘ₗ (restrictedDual P V).toSubmodule.subtype).flip

@[simp] lemma toDual_restrictedDoubleDualLin (v : V) (φ : restrictedDual P V) :
    TwistedDual.toDual P (restrictedDual P V) (restrictedDoubleDualLin v) φ =
      TwistedDual.toDual P V φ.1 v := rfl

lemma restrictedDoubleDualLin_mem_weightSpace {μ : Dual K H} {v : V}
    (hv : v ∈ weightSpaceOfMap V (h P) μ) :
    restrictedDoubleDualLin v ∈ weightSpaceOfMap (TwistedDual P (restrictedDual P V)) (h P) μ := by
  rw [TwistedDual.mem_weightSpaceOfMap_iff]
  intro a φ
  rw [toDual_restrictedDoubleDualLin, toDual_restrictedDoubleDualLin, LieSubmodule.coe_bracket,
    lie_apply, transpose_h, hv a, map_smul, smul_eq_mul]

/-- The morphism `V → V^∨∨`, `v ↦ (φ ↦ φ(v))`, for `V` a sum of its weight spaces. -/
def restrictedDoubleDual (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤) :
    V →ₗ⁅K,𝔤⁆ restrictedDual P (restrictedDual P V) where
  toFun v := ⟨restrictedDoubleDualLin v, by
    have hv : v ∈ ⨆ μ, weightSpaceOfMap V (h P) μ := hV ▸ Submodule.mem_top
    change restrictedDoubleDualLin v ∈ ⨆ μ, weightSpaceOfMap _ (h P) μ
    induction hv using Submodule.iSup_induction' with
    | mem μ v hv => exact Submodule.mem_iSup_of_mem μ (restrictedDoubleDualLin_mem_weightSpace hv)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy⟩
  map_add' x y := Subtype.ext (map_add _ x y)
  map_smul' c x := Subtype.ext (map_smul _ c x)
  map_lie' {x v} := Subtype.ext <| TwistedDual.ext fun φ ↦ by
    change TwistedDual.toDual P V φ.1 ⁅x, v⁆ =
      TwistedDual.toDual P (restrictedDual P V) ⁅x, restrictedDoubleDualLin v⁆ φ
    rw [lie_apply, toDual_restrictedDoubleDualLin, LieSubmodule.coe_bracket, lie_apply,
      transpose_transpose]

@[simp] lemma toDual_restrictedDoubleDual (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤) (v : V)
    (φ : restrictedDual P V) :
    TwistedDual.toDual P (restrictedDual P V) (restrictedDoubleDual hV v).1 φ =
      TwistedDual.toDual P V φ.1 v := rfl

/-- **Naturality of `V → V^∨∨`** (Humphreys, GSM 94, §3.2): `f^∨∨ ∘ ι_V = ι_W ∘ f`. -/
theorem restrictedDualMap_restrictedDualMap_comp (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤)
    (hW : ⨆ μ, weightSpaceOfMap W (h P) μ = ⊤) (f : V →ₗ⁅K,𝔤⁆ W) :
    (restrictedDualMap P (restrictedDualMap P f)).comp (restrictedDoubleDual hV) =
      (restrictedDoubleDual hW).comp f :=
  LieModuleHom.ext fun _ ↦ restrictedDual_ext P fun _ ↦ rfl

omit [CharZero K] in
/-- A vector of a sum of weight spaces whose projections to all weight spaces vanish is zero. -/
lemma eq_zero_of_forall_weightProj_eq_zero (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤) {v : V}
    (hv : ∀ κ, weightProj P hV κ v = 0) : v = 0 := by
  have hmem : v ∈ ⨆ μ, weightSpaceOfMap V (h P) μ := hV ▸ Submodule.mem_top
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hmem
  rw [Submodule.mem_iSup_finset_iff_exists_sum] at hs
  obtain ⟨μ, rfl⟩ := hs
  have hμ : ∀ κ ∈ s, (μ κ : V) = 0 := by
    intro κ hκ
    have h1 := congrArg Subtype.val (hv κ)
    rw [map_sum, Finset.sum_eq_single_of_mem κ hκ fun ν _ hν ↦ weightProj_of_mem_ne hV
      (μ ν).2 hν, weightProj_of_mem hV (μ κ).2] at h1
    simpa using h1
  exact Finset.sum_eq_zero hμ

theorem injective_restrictedDoubleDual (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤) :
    Function.Injective (restrictedDoubleDual (P := P) hV) := by
  rw [← LieModuleHom.ker_eq_bot, LieSubmodule.eq_bot_iff]
  intro v hv
  refine eq_zero_of_forall_weightProj_eq_zero hV fun κ ↦ ?_
  refine (Module.forall_dual_apply_eq_zero_iff K _).mp fun γ ↦ ?_
  have := congrArg (fun Ψ : restrictedDual P (restrictedDual P V) ↦
    TwistedDual.toDual P (restrictedDual P V) Ψ.1
      ⟨(TwistedDual.toDual P V).symm (γ ∘ₗ weightProj P hV κ),
      Submodule.mem_iSup_of_mem κ (mem_weightSpace_twistedDual_comp hV κ γ)⟩)
    ((LieModuleHom.mem_ker).mp hv)
  simpa using this

theorem surjective_restrictedDoubleDual (hV : IsCategoryO P V) :
    Function.Surjective (restrictedDoubleDual (P := P) hV.iSup_weightSpaceOfMap_eq_top) := by
  have hd := hV.iSup_weightSpaceOfMap_eq_top
  have hd' := (isCategoryO_restrictedDual hV).iSup_weightSpaceOfMap_eq_top
  rintro ⟨Ψ, hΨ⟩
  suffices H : ∀ Ψ ∈ ⨆ μ, weightSpaceOfMap (TwistedDual P (restrictedDual P V)) (h P) μ,
      ∃ v, (restrictedDoubleDual hd v).1 = Ψ by
    obtain ⟨v, hv⟩ := H Ψ hΨ
    exact ⟨v, Subtype.ext hv⟩
  intro Ψ hΨ
  induction hΨ using Submodule.iSup_induction' with
  | mem μ Ψ hΨ =>
    have := hV.finiteDimensional_weightSpaceOfMap μ
    -- the functional `γ ↦ Ψ(γ ∘ pr_μ)` on `(V_μ)^*` is evaluation at some `v ∈ V_μ`
    let ι : Module.Dual K (weightSpaceOfMap V (h P) μ) →ₗ[K] restrictedDual P V :=
      { toFun γ := ⟨(TwistedDual.toDual P V).symm (γ ∘ₗ weightProj P hd μ),
          Submodule.mem_iSup_of_mem μ (mem_weightSpace_twistedDual_comp hd μ γ)⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    set v := (Module.evalEquiv K (weightSpaceOfMap V (h P) μ)).symm
      (TwistedDual.toDual P (restrictedDual P V) Ψ ∘ₗ ι)
    refine ⟨v, ?_⟩
    rw [← sub_eq_zero]
    refine eq_zero_of_mem_weightSpace_twistedDual hd'
      (Submodule.sub_mem _ (restrictedDoubleDualLin_mem_weightSpace v.2) hΨ) fun φ hφ ↦ ?_
    -- on `(V^∨)_μ` both sides agree
    have hφ' := mem_weightSpaceOfMap_lieSubmodule_iff.mp hφ
    have hι : ι (TwistedDual.toDual P V φ.1 ∘ₗ (weightSpaceOfMap V (h P) μ).subtype) = φ := by
      have e := (weightSpaceTwistedDualEquiv hd μ).symm_apply_apply ⟨φ.1, hφ'⟩
      have e' : ((weightSpaceTwistedDualEquiv hd μ).symm
          ((weightSpaceTwistedDualEquiv hd μ) ⟨φ.1, hφ'⟩)).1 = φ.1 :=
        congrArg Subtype.val e
      exact Subtype.ext e'
    have := Module.apply_evalEquiv_symm_apply
      (f := TwistedDual.toDual P V φ.1 ∘ₗ (weightSpaceOfMap V (h P) μ).subtype)
      (g := TwistedDual.toDual P (restrictedDual P V) Ψ ∘ₗ ι)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hι] at this
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
    exact this
  | zero => exact ⟨0, by simp⟩
  | add Ψ₁ Ψ₂ _ _ h₁ h₂ =>
    obtain ⟨v₁, e₁⟩ := h₁
    obtain ⟨v₂, e₂⟩ := h₂
    exact ⟨v₁ + v₂, by rw [map_add, LieSubmodule.coe_add, e₁, e₂]⟩

/-- **Humphreys, GSM 94, Theorem 3.2 (a).** For `V ∈ 𝒪`, `v ↦ (φ ↦ φ(v))` is an isomorphism
`V ≅ V^∨∨`; it is natural in `V` (`restrictedDualMap_restrictedDualMap_comp`). Humphreys states
this for `𝔤` semisimple over `ℂ`. -/
def restrictedDoubleDualEquiv (hV : IsCategoryO P V) :
    V ≃ₗ⁅K,𝔤⁆ restrictedDual P (restrictedDual P V) :=
  LieModuleEquiv.ofBijective (restrictedDoubleDual hV.iSup_weightSpaceOfMap_eq_top)
    ⟨injective_restrictedDoubleDual _, surjective_restrictedDoubleDual hV⟩

@[simp] lemma restrictedDoubleDualEquiv_apply (hV : IsCategoryO P V) (v : V) :
    restrictedDoubleDualEquiv hV v = restrictedDoubleDual hV.iSup_weightSpaceOfMap_eq_top v := rfl

end DoubleDual

end Matrix.Realization.KacMoodyAlgebra
