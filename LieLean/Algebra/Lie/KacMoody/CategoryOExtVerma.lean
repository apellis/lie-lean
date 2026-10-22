/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOExt
import LieLean.Algebra.Lie.KacMoody.ExtVerma
import LieLean.Algebra.Lie.KacMoody.StandardFiltrationSummand

/-!
# Vanishing of `Extⁿ` between Verma modules

[HumO] Theorem 6.11 (a), first vanishing statement: unless `μ ↑ λ` with `μ ≠ λ`,
`Extⁿ_𝒪(M(μ), M(λ)) = 0` for all `n > 0` (`CategoryO.ext_verma_eq_zero`). Here `Extⁿ_𝒪` is
computed in the derived category of the abelian category `𝒪` (`CategoryO.instHasExt`).

Humphreys states the theorem for `μ = w'·λ`, `λ = w·λ` in the orbit of a dominant integral
weight, where `w'·λ ↑ w·λ` means `w ≤ w'` in the Bruhat order. The argument applies to arbitrary
weights `μ, λ` and is formalized in that generality.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.CategoryO.ofSub`: a Lie submodule of an object of `𝒪`, as
  an object of `𝒪`.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.verma`: the Verma module `M(μ)` as an object of
  `𝒪`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.CategoryO.ext_eq_zero_of_isStdFiltered`: `Extⁿ(N, Y) = 0`
  for `N` with a standard filtration whose factors `M(μ)` all have `Extⁿ(M(μ), Y) = 0`.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.ext_verma_eq_zero`:
  **[HumO] Theorem 6.11 (a)** for Verma modules.

## Proof

As in Humphreys, by induction on `n`: the case `n = 1` is Theorem 6.5 (a) (via
`ext_one_eq_zero_of_extOne_of_equiv`); for the induction step, the kernel `N` of a surjection
`P(μ) → M(μ)` gives `Extⁿ(N, M(λ)) ↠ Extⁿ⁺¹(M(μ), M(λ))`, and `N` has a standard filtration with
factors `M(ν)`, `μ ↑ ν`, `ν ≠ μ` (Theorem 3.10, BGG reciprocity and Theorem 5.1 (b)).
Humphreys takes this filtration of `N` from Theorem 3.10. Here it is obtained (reconstructed) by
intersecting a standard filtration of `P(μ)` with `N` (`ext_inf_ker_eq_zero_aux`): below the
unique factor `M(μ)` the map `P(μ) → M(μ)` vanishes, at that factor it induces an isomorphism, and
above it the intersections with `N` have the same factors as the filtration of `P(μ)`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §6.10–6.11.
-/

open CategoryTheory Limits LieModule Module

noncomputable section

universe w u

namespace CategoryTheory.Abelian.Ext

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]

theorem eq_zero_of_isZero_left {X Y : C} (hX : IsZero X) {n : ℕ} (x : Ext.{w} X Y n) : x = 0 := by
  rw [← mk₀_id_comp x, hX.eq_of_src (𝟙 X) 0, mk₀_zero]
  simp

/-- `Extⁿ(X₂, Y) = 0` if `Extⁿ(X₁, Y) = 0 = Extⁿ(X₃, Y)` for a short exact sequence
`0 → X₁ → X₂ → X₃ → 0`. -/
theorem eq_zero_of_shortExact_left {S : ShortComplex C} (hS : S.ShortExact) {Y : C} {n : ℕ}
    (h₁ : ∀ x : Ext.{w} S.X₁ Y n, x = 0) (h₃ : ∀ x : Ext.{w} S.X₃ Y n, x = 0)
    (x : Ext.{w} S.X₂ Y n) : x = 0 := by
  obtain ⟨x₃, rfl⟩ := contravariant_sequence_exact₂ hS Y x (h₁ _)
  rw [h₃ x₃]
  simp

/-- Dimension shifting: `Extⁿ⁺¹(X₃, Y) = 0` if `Extⁿ(X₁, Y) = 0` for a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` with `X₂` projective. -/
theorem eq_zero_of_shortExact_of_projective {S : ShortComplex C} (hS : S.ShortExact)
    [Projective S.X₂] {Y : C} {n : ℕ} (h : ∀ x : Ext.{w} S.X₁ Y n, x = 0)
    (z : Ext.{w} S.X₃ Y (n + 1)) : z = 0 := by
  obtain ⟨x₁, rfl⟩ := contravariant_sequence_exact₃ hS Y z (eq_zero_of_projective _)
    (n₀ := n) (by omega)
  rw [h x₁]
  simp

end CategoryTheory.Abelian.Ext

namespace Matrix.Realization.KacMoodyAlgebra

section Step

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H} {X : Type*} [AddCommGroup X]
  [Module K X] [LieRingModule P.KacMoodyAlgebra X] [LieModule K P.KacMoodyAlgebra X]
  {N₀ N₁ : LieSubmodule K P.KacMoodyAlgebra X} {μ : Dual K H}

local notation "𝔤" => KacMoodyAlgebra P

omit [CharZero K] in
/-- The map `N₁ → N₁ / N₀ ≅ M(μ)` of a step of a standard filtration. -/
def stdStepMap (_hle : N₀ ≤ N₁)
    (e : VermaModule P μ ≃ₗ⁅K,𝔤⁆ N₁.map (LieSubmodule.Quotient.mk' N₀)) :
    N₁ →ₗ⁅K,𝔤⁆ VermaModule P μ :=
  e.symm.toLieModuleHom.comp (((LieSubmodule.Quotient.mk' N₀).comp N₁.incl).codRestrict
    (N₁.map (LieSubmodule.Quotient.mk' N₀)) fun y ↦ LieSubmodule.mem_map_of_mem y.2)

omit [CharZero K] in
theorem surjective_stdStepMap (hle : N₀ ≤ N₁)
    (e : VermaModule P μ ≃ₗ⁅K,𝔤⁆ N₁.map (LieSubmodule.Quotient.mk' N₀)) :
    Function.Surjective (stdStepMap hle e) := fun m ↦ by
  obtain ⟨y, hy, hyz⟩ := (LieSubmodule.mem_map _).mp (e m).2
  refine ⟨⟨y, hy⟩, ?_⟩
  change e.symm ⟨_, _⟩ = m
  rw [LieModuleEquiv.symm_apply_eq]
  exact Subtype.ext hyz

omit [CharZero K] in
theorem stdStepMap_eq_zero_iff (hle : N₀ ≤ N₁)
    (e : VermaModule P μ ≃ₗ⁅K,𝔤⁆ N₁.map (LieSubmodule.Quotient.mk' N₀)) (y : N₁) :
    stdStepMap hle e y = 0 ↔ (y : X) ∈ N₀ := by
  rw [← LieSubmodule.Quotient.mk_eq_zero]
  change e.symm _ = 0 ↔ _
  rw [LieModuleEquiv.symm_apply_eq, map_zero]
  exact Subtype.ext_iff

end Step

namespace CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P

/-! ### Submodules and Verma modules as objects of `𝒪` -/

/-- A Lie submodule of an object of `𝒪`, as an object of `𝒪`. -/
def ofSub (X : CategoryO.{u} P) (N : LieSubmodule K 𝔤 X.obj) : CategoryO.{u} P :=
  ⟨ofLie P N, isObj_of_injective
    (ofLieModuleHom (N.incl.comp (ofLieEquiv (P := P) N).symm.toLieModuleHom))
    (fun _ _ hab ↦ (ofLieEquiv (P := P) N).symm.injective (Subtype.ext hab)) X.property⟩

theorem isZero_ofSub_bot (X : CategoryO.{u} P) : IsZero (ofSub X ⊥) := by
  have : Subsingleton ((IsObj.{u} P).ι.obj (ofSub X ⊥)) :=
    inferInstanceAs (Subsingleton (⊥ : LieSubmodule K 𝔤 X.obj))
  exact IsZero.of_full_of_faithful_of_isZero (IsObj.{u} P).ι _
    (ModuleCat.isZero_of_subsingleton _)

variable (P) in
/-- The Verma module `M(μ)` as an object of `𝒪`. -/
def verma (μ : Dual K H) : CategoryO.{u} P :=
  mk (VermaModule P μ) (VermaModule.isCategoryO P μ) ⟨{VermaModule.hwv P μ}, by
    rw [Finset.coe_singleton]
    exact VermaModule.lieSpan_map_hwv_eq_top LieModuleHom.id Function.surjective_id⟩

/-- The short complex `N → N' → Z` given by Lie submodules `N ≤ N'` of `X` and a morphism
`g : N' → Z` vanishing on `N`. -/
def subComplex (X : CategoryO.{u} P) {N N' : LieSubmodule K 𝔤 X.obj} (hle : N ≤ N')
    (Z : CategoryO.{u} P) (g : N' →ₗ⁅K,𝔤⁆ Z.obj) (hg : ∀ x (hx : x ∈ N), g ⟨x, hle hx⟩ = 0) :
    ShortComplex (CategoryO.{u} P) :=
  ShortComplex.mk
    ((IsObj.{u} P).homMk (ofLieModuleHom ((ofLieEquiv (P := P) N').toLieModuleHom.comp
      ((LieSubmodule.inclusion hle).comp (ofLieEquiv (P := P) N).symm.toLieModuleHom))) :
        ofSub X N ⟶ ofSub X N')
    ((IsObj.{u} P).homMk (ofLieModuleHom (g.comp (ofLieEquiv (P := P) N').symm.toLieModuleHom)) :
      ofSub X N' ⟶ Z)
    (by
      ext x
      exact hg _ ((ofLieEquiv (P := P) N).symm x).2)

theorem shortExact_subComplex (X : CategoryO.{u} P) {N N' : LieSubmodule K 𝔤 X.obj}
    (hle : N ≤ N') (Z : CategoryO.{u} P) (g : N' →ₗ⁅K,𝔤⁆ Z.obj)
    (hg : ∀ x (hx : x ∈ N), g ⟨x, hle hx⟩ = 0) (hgs : Function.Surjective g)
    (hker : ∀ y : N', g y = 0 → (y : X.obj) ∈ N) : (subComplex X hle Z g hg).ShortExact :=
  shortExact_of_lie
    (fun a b hab ↦ (ofLieEquiv (P := P) N).symm.injective (Subtype.ext
      (congrArg (fun y : N' ↦ (y : X.obj)) ((ofLieEquiv (P := P) N').injective hab))))
    (fun z ↦ by
      obtain ⟨y, rfl⟩ := hgs z
      exact ⟨ofLieEquiv (P := P) N' y, rfl⟩)
    (fun y hy ↦ ⟨ofLieEquiv (P := P) N ⟨_, hker _ hy⟩, rfl⟩)

/-- The kernel sequence `0 → ker φ → X → Z → 0` of a morphism `φ : X → Z`. -/
def kerComplex (X Z : CategoryO.{u} P) (φ : X.obj →ₗ⁅K,𝔤⁆ Z.obj) :
    ShortComplex (CategoryO.{u} P) :=
  ShortComplex.mk
    ((IsObj.{u} P).homMk (ofLieModuleHom (φ.ker.incl.comp
      (ofLieEquiv (P := P) φ.ker).symm.toLieModuleHom)) : ofSub X φ.ker ⟶ X)
    ((IsObj.{u} P).homMk (ofLieModuleHom φ))
    (by
      ext x
      exact LieModuleHom.mem_ker.mp ((ofLieEquiv (P := P) φ.ker).symm x).2)

theorem shortExact_kerComplex (X Z : CategoryO.{u} P) (φ : X.obj →ₗ⁅K,𝔤⁆ Z.obj)
    (hφ : Function.Surjective φ) : (kerComplex X Z φ).ShortExact :=
  shortExact_of_lie
    (fun _ _ hab ↦ (ofLieEquiv (P := P) φ.ker).symm.injective (Subtype.ext hab)) hφ
    (fun y hy ↦ ⟨ofLieEquiv (P := P) φ.ker ⟨y, LieModuleHom.mem_ker.mpr hy⟩, rfl⟩)

/-! ### `Ext` along standard filtrations -/

/-- The map `N₁ → M(μ)` of a step of a standard filtration, into the object `verma P μ`. -/
def stdStepMapO (X : CategoryO.{u} P) {N₀ N₁ : LieSubmodule K 𝔤 X.obj} {μ : Dual K H}
    (hle : N₀ ≤ N₁) (e : VermaModule P μ ≃ₗ⁅K,𝔤⁆ N₁.map (LieSubmodule.Quotient.mk' N₀)) :
    N₁ →ₗ⁅K,𝔤⁆ (verma P μ).obj :=
  (ofLieEquiv (P := P) (VermaModule P μ)).toLieModuleHom.comp (stdStepMap hle e)

theorem stdStepMapO_apply (X : CategoryO.{u} P) {N₀ N₁ : LieSubmodule K 𝔤 X.obj} {μ : Dual K H}
    (hle : N₀ ≤ N₁) (e : VermaModule P μ ≃ₗ⁅K,𝔤⁆ N₁.map (LieSubmodule.Quotient.mk' N₀)) (y : N₁) :
    stdStepMapO X hle e y = ofLieEquiv (P := P) (VermaModule P μ) (stdStepMap hle e y) :=
  rfl

/-- `Extⁿ(N₁, Y) = 0` for a step `N₁ / N₀ ≅ M(μ)` of a standard filtration with
`Extⁿ(N₀, Y) = 0 = Extⁿ(M(μ), Y)`. -/
theorem ext_eq_zero_of_step (X Y : CategoryO.{u} P) {n : ℕ} {N₀ N₁ : LieSubmodule K 𝔤 X.obj}
    {μ : Dual K H} (hle : N₀ ≤ N₁)
    (e : VermaModule P μ ≃ₗ⁅K,𝔤⁆ N₁.map (LieSubmodule.Quotient.mk' N₀))
    (h₀ : ∀ x : Abelian.Ext.{u} (ofSub X N₀) Y n, x = 0)
    (hμ : ∀ x : Abelian.Ext.{u} (verma P μ) Y n, x = 0) :
    ∀ x : Abelian.Ext.{u} (ofSub X N₁) Y n, x = 0 :=
  Abelian.Ext.eq_zero_of_shortExact_left
    (shortExact_subComplex X hle (verma P μ) (stdStepMapO X hle e)
      (fun x hx ↦ by
        rw [stdStepMapO_apply, (stdStepMap_eq_zero_iff hle e _).mpr hx, map_zero])
      ((ofLieEquiv (P := P) _).surjective.comp (surjective_stdStepMap hle e))
      (fun y hy ↦ (stdStepMap_eq_zero_iff hle e y).mp
        ((ofLieEquiv (P := P) _).injective (hy.trans (map_zero _).symm)))) h₀ hμ

/-- `Extⁿ(N, Y) = 0` for a Lie submodule `N` with a standard filtration whose factors `M(μ)` all
have `Extⁿ(M(μ), Y) = 0`. -/
theorem ext_eq_zero_of_isStdFiltered (X Y : CategoryO.{u} P) {n : ℕ}
    {N : LieSubmodule K 𝔤 X.obj} {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s)
    (hY : ∀ μ ∈ s, ∀ x : Abelian.Ext.{u} (verma P μ) Y n, x = 0) :
    ∀ x : Abelian.Ext.{u} (ofSub X N) Y n, x = 0 := by
  induction hN with
  | bot => exact Abelian.Ext.eq_zero_of_isZero_left (isZero_ofSub_bot X)
  | @step N₀ N₁ s₀ μ _ hle he ih =>
    obtain ⟨e⟩ := he
    exact ext_eq_zero_of_step X Y hle e (ih fun ν hν ↦ hY ν (Multiset.mem_cons_of_mem hν))
      (hY μ (Multiset.mem_cons_self _ _))

/-- A nonzero endomorphism of `M(ν)` is surjective. -/
theorem surjective_of_ne_zero_of_eq {κ ν : Dual K H}
    {g : VermaModule P κ →ₗ⁅K,𝔤⁆ VermaModule P ν} (hg : g ≠ 0) (hκ : κ = ν) :
    Function.Surjective g := by
  subst hκ
  obtain ⟨σ, hσ⟩ := exists_section_of_comp_ne_zero P (q := g) (g := LieModuleHom.id)
    (fun h ↦ hg (by ext m; exact LieModuleHom.congr_fun h m))
  exact fun m ↦ ⟨σ m, hσ m⟩

/-- Induction along a standard filtration of `X` for the kernel of `φ : X → M(ν)`: as long as `φ`
vanishes, `Extⁿ(N, Y) = 0` when no factor is `M(ν)`; from the (unique) factor `M(ν)` on, `φ` maps
`N` onto `M(ν)` and `Extⁿ(N ∩ ker φ, Y) = 0`. -/
theorem ext_inf_ker_eq_zero_aux [DecidableEq (Dual K H)] (X Y : CategoryO.{u} P) {n : ℕ}
    {ν : Dual K H}
    (φ : X.obj →ₗ⁅K,𝔤⁆ VermaModule P ν) {N : LieSubmodule K 𝔤 X.obj}
    {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s) (hcount : s.count ν ≤ 1)
    (hhom : ∀ κ ∈ s, ∀ g : VermaModule P κ →ₗ⁅K,𝔤⁆ VermaModule P ν, g ≠ 0 → κ = ν)
    (hY : ∀ κ ∈ s, κ ≠ ν → ∀ x : Abelian.Ext.{u} (verma P κ) Y n, x = 0) :
    ((∀ x ∈ N, φ x = 0) ∧ (ν ∉ s → ∀ x : Abelian.Ext.{u} (ofSub X N) Y n, x = 0)) ∨
      ((∀ v, ∃ x ∈ N, φ x = v) ∧ ν ∈ s ∧
        ∀ x : Abelian.Ext.{u} (ofSub X (N ⊓ φ.ker)) Y n, x = 0) := by
  induction hN with
  | bot =>
    exact Or.inl ⟨fun x hx ↦ by rw [(LieSubmodule.mem_bot x).mp hx, map_zero],
      fun _ ↦ Abelian.Ext.eq_zero_of_isZero_left (isZero_ofSub_bot X)⟩
  | @step N₀ N₁ s₀ κ _ hle he ih =>
    obtain ⟨e⟩ := he
    have hcount₀ : s₀.count ν ≤ 1 :=
      (Multiset.count_le_of_le ν (Multiset.le_cons_self s₀ κ)).trans hcount
    have hκmem : κ ∈ κ ::ₘ s₀ := Multiset.mem_cons_self _ _
    -- the step sequence `N₀ → N₁ → M(κ)` and its exactness data
    have hstep0 : ∀ x (hx : x ∈ N₀), stdStepMap hle e ⟨x, hle hx⟩ = 0 := fun x hx ↦
      (stdStepMap_eq_zero_iff hle e _).mpr hx
    rcases ih hcount₀ (fun κ' h ↦ hhom κ' (Multiset.mem_cons_of_mem h))
        (fun κ' h ↦ hY κ' (Multiset.mem_cons_of_mem h)) with ⟨h0, hext⟩ | ⟨hsurj, hν, hext⟩
    · -- `φ` vanishes on `N₀`: let `g : M(κ) → M(ν)` be the induced map
      have hker₀ : N₀ ≤ φ.ker := fun x hx ↦ LieModuleHom.mem_ker.mpr (h0 x hx)
      let g : VermaModule P κ →ₗ⁅K,𝔤⁆ VermaModule P ν :=
        (LieSubmodule.Quotient.lift N₀ φ hker₀).comp
          ((N₁.map (LieSubmodule.Quotient.mk' N₀)).incl.comp e.toLieModuleHom)
      have hφg : ∀ y : N₁, φ y = g (stdStepMap hle e y) := fun y ↦ by
        simp only [g, stdStepMap, LieModuleHom.comp_apply, LieModuleEquiv.coe_toLieModuleHom,
          LieModuleEquiv.apply_symm_apply, LieSubmodule.incl_apply]
        rfl
      by_cases hg : g = 0
      · refine Or.inl ⟨fun x hx ↦ by rw [hφg ⟨x, hx⟩, hg, _root_.zero_apply], fun hν ↦ ?_⟩
        have hκν : κ ≠ ν := fun h ↦ hν (h ▸ hκmem)
        exact ext_eq_zero_of_step X Y hle e (hext fun h ↦ hν (Multiset.mem_cons_of_mem h))
          (hY κ hκmem hκν)
      · have hκν := hhom κ hκmem g hg
        have hgs := surjective_of_ne_zero_of_eq hg hκν
        have hgi := VermaModule.injective_of_ne_zero P hg
        have hν₀ : ν ∉ s₀ := by
          rw [← hκν, Multiset.count_cons_self] at hcount
          rw [← hκν]
          exact Multiset.count_eq_zero.mp (by omega)
        refine Or.inr ⟨fun v ↦ ?_, hκν ▸ hκmem, ?_⟩
        · obtain ⟨m, rfl⟩ := hgs v
          obtain ⟨y, hy⟩ := surjective_stdStepMap hle e m
          exact ⟨y, y.2, by rw [hφg y, hy]⟩
        · have hN : N₁ ⊓ φ.ker = N₀ := by
            refine le_antisymm (fun x hx ↦ ?_) (le_inf hle hker₀)
            have h1 : g (stdStepMap hle e ⟨x, hx.1⟩) = 0 := by
              rw [← hφg]
              exact LieModuleHom.mem_ker.mp hx.2
            exact (stdStepMap_eq_zero_iff hle e _).mp (hgi (h1.trans (map_zero g).symm))
          rw [hN]
          exact hext hν₀
    · -- `φ` maps `N₀` onto `M(ν)`
      have hκν : κ ≠ ν := by
        rintro rfl
        rw [Multiset.count_cons_self] at hcount
        have := Multiset.count_pos.mpr hν
        omega
      refine Or.inr ⟨fun v ↦ ?_, Multiset.mem_cons_of_mem hν, ?_⟩
      · obtain ⟨x, hx, rfl⟩ := hsurj v
        exact ⟨x, hle hx, rfl⟩
      · have hle' : N₀ ⊓ φ.ker ≤ N₁ ⊓ φ.ker := inf_le_inf_right _ hle
        let g' : (N₁ ⊓ φ.ker : LieSubmodule K 𝔤 X.obj) →ₗ⁅K,𝔤⁆ (verma P κ).obj :=
          (stdStepMapO X hle e).comp (LieSubmodule.inclusion inf_le_left)
        refine Abelian.Ext.eq_zero_of_shortExact_left
          (shortExact_subComplex X hle' (verma P κ) g' (fun x hx ↦ ?_) (fun m ↦ ?_)
            (fun y hy ↦ ?_)) hext (hY κ hκmem hκν)
        · change stdStepMapO X hle e ⟨x, hle hx.1⟩ = 0
          rw [stdStepMapO_apply, hstep0 x hx.1, map_zero]
        · obtain ⟨y, hy⟩ := surjective_stdStepMap hle e
            ((ofLieEquiv (P := P) (VermaModule P κ)).symm m)
          obtain ⟨x, hx, hφx⟩ := hsurj (φ y)
          have hmem : (y : X.obj) - x ∈ N₁ ⊓ φ.ker :=
            ⟨sub_mem y.2 (hle hx), LieModuleHom.mem_ker.mpr (by rw [map_sub, hφx, sub_self])⟩
          refine ⟨⟨_, hmem⟩, ?_⟩
          have hsub : stdStepMap hle e ⟨(y : X.obj) - x, hmem.1⟩ =
              stdStepMap hle e y - stdStepMap hle e ⟨x, hle hx⟩ := by
            rw [← map_sub]
            rfl
          change stdStepMapO X hle e ⟨(y : X.obj) - x, hmem.1⟩ = m
          rw [stdStepMapO_apply, hsub, hstep0 x hx, sub_zero, hy, LieModuleEquiv.apply_symm_apply]
        · have h1 : stdStepMap hle e ⟨y, (y.2 : (y : X.obj) ∈ N₁ ⊓ φ.ker).1⟩ = 0 :=
            (ofLieEquiv (P := P) _).injective (hy.trans (map_zero _).symm)
          exact ⟨(stdStepMap_eq_zero_iff hle e _).mp h1, y.2.2⟩

/-! ### [HumO] Theorem 6.11 (a) for Verma modules -/

theorem ext_verma_eq_zero_aux (lam : Dual K H) (n : ℕ) : ∀ μ : Dual K H,
    ¬ (P.IsStronglyLinked (Fact.out : A.IsFiniteCartan).isGeneralizedCartan μ lam ∧ μ ≠ lam) →
      ∀ x : Abelian.Ext.{u} (verma P μ) (verma P lam) (n + 1), x = 0 := by
  have hA : A.IsFiniteCartan := Fact.out
  induction n with
  | zero =>
    intro μ hμ x
    refine ext_one_eq_zero_of_extOne_of_equiv _ _ (VermaModule P μ) (VermaModule P lam)
      (VermaModule.isCategoryO P μ) (ofLieEquiv (P := P) _) (ofLieEquiv (P := P) _)
      (fun y ↦ ?_) x
    by_contra hy
    exact hμ (VermaModule.isStronglyLinked_of_extOne_ne_zero P hA hy)
  | succ n ih =>
    intro μ hμ x
    classical
    obtain ⟨t, ht, hcount, -⟩ := ProjectiveCover.exists_isStdFiltered P μ hA
    -- every factor `M(κ)` of `P(μ)` has `[M(κ) : L(μ)] ≠ 0`
    have hmult : ∀ κ ∈ t, (VermaModule.isCategoryO P κ).multiplicity μ ≠ 0 := fun κ hκ ↦ by
      rw [← ProjectiveCover.count_eq_multiplicity P μ hA ht κ]
      exact (Multiset.count_pos.mpr hκ).ne'
    -- `P(μ)` as a projective object of `𝒪`
    obtain ⟨p, -, -, hp⟩ := (ProjectiveCover.isProjectiveCover P μ hA).exists_generator
    let Q := mk (ProjectiveCover P hA μ) (ProjectiveCover.isCategoryO P hA μ)
      ⟨{p}, by rw [Finset.coe_singleton]; exact hp⟩
    have hQ : Projective Q := projective_mk _ _ _ (ProjectiveCover.isProjectiveO P hA μ)
    let eQ := ofLieEquiv (P := P) (ProjectiveCover P hA μ)
    -- a surjection `P(μ) → M(μ)`
    obtain ⟨φ₀, hφ₀⟩ := ProjectiveCover.isProjectiveO P hA μ (VermaModule.isCategoryO P μ)
      (IrreducibleModule.isCategoryO P μ) (LieSubmodule.Quotient.mk' (VermaModule.maxSubmodule P μ))
      (LieSubmodule.Quotient.surjective_mk' _) (ProjectiveCover.π P hA μ)
    have hφ₀s : Function.Surjective φ₀ := by
      rw [← LieModuleHom.range_eq_top]
      by_contra hne
      have hle := (VermaModule.le_maxSubmodule_iff P μ φ₀.range).mpr hne
      apply ProjectiveCover.π_ne_zero P hA μ
      rw [← hφ₀]
      ext y
      rw [LieModuleHom.comp_apply, _root_.zero_apply, LieSubmodule.Quotient.mk_eq_zero]
      exact hle ((LieModuleHom.mem_range _ _).mpr ⟨y, rfl⟩)
    let φ : Q.obj →ₗ⁅K,𝔤⁆ VermaModule P μ := φ₀.comp eQ.symm.toLieModuleHom
    have hφ : Function.Surjective φ := hφ₀s.comp eQ.symm.surjective
    -- the standard filtration of `P(μ)`, inside `Q`
    have htop : (⊤ : LieSubmodule K 𝔤 (ProjectiveCover P hA μ)).map eQ.toLieModuleHom = ⊤ := by
      rw [eq_top_iff]
      intro y _
      exact (LieSubmodule.mem_map y).mpr ⟨eQ.symm y, trivial, eQ.apply_symm_apply y⟩
    have ht' : IsStdFiltered P (⊤ : LieSubmodule K 𝔤 Q.obj) t := by
      have h := ht.map_of_injOn P eQ.toLieModuleHom (B := ⊤)
        (fun y _ hy ↦ eQ.injective (hy.trans (map_zero eQ.toLieModuleHom).symm)) le_rfl
      rw [htop] at h
      exact h
    -- the factors `M(κ)` of `P(μ)` satisfy the hypothesis of the theorem
    have hY : ∀ κ ∈ t, κ ≠ μ → ∀ z : Abelian.Ext.{u} (verma P κ) (verma P lam) (n + 1),
        z = 0 := fun κ hκ _ ↦ ih κ fun ⟨hκl, hκne⟩ ↦ by
      have hμκ := VermaModule.isStronglyLinked_of_multiplicity_ne_zero P hA (hmult κ hκ)
      have hμe : μ = lam := by
        by_contra h
        exact hμ ⟨Relation.ReflTransGen.trans hκl hμκ, h⟩
      have h1 : κ ∈ cone P μ := VermaModule.mem_cone_of_multiplicity_ne_zero
        (VermaModule.multiplicity_ne_zero_of_isStronglyLinked P hA (by rw [hμe]; exact hκl))
      exact hκne ((eq_of_mem_cone_of_mem_cone h1
        (VermaModule.mem_cone_of_multiplicity_ne_zero (hmult κ hκ))).trans hμe)
    rcases ext_inf_ker_eq_zero_aux Q (verma P lam) φ ht' hcount.le
        (fun κ hκ g hg ↦ eq_of_mem_cone_of_mem_cone (VermaModule.mem_cone_of_multiplicity_ne_zero
          (VermaModule.multiplicity_ne_zero_of_hom_ne_zero P (φ := g) hg))
          (VermaModule.mem_cone_of_multiplicity_ne_zero (hmult κ hκ))) hY with
      ⟨h0, -⟩ | ⟨-, -, hext⟩
    · obtain ⟨y, hy⟩ := hφ (VermaModule.hwv P μ)
      exact absurd (hy.symm.trans (h0 y (LieSubmodule.mem_top y))) (VermaModule.hwv_ne_zero P μ)
    · rw [top_inf_eq] at hext
      let eV := ofLieEquiv (P := P) (VermaModule P μ)
      let ψ : Q.obj →ₗ⁅K,𝔤⁆ (verma P μ).obj := eV.toLieModuleHom.comp φ
      have hkerψ : ψ.ker = φ.ker := by
        ext y
        simp only [LieModuleHom.mem_ker]
        exact ⟨fun h ↦ eV.injective (h.trans (map_zero eV.toLieModuleHom).symm),
          fun h ↦ (congrArg eV h).trans (map_zero eV.toLieModuleHom)⟩
      have : Projective (kerComplex Q (verma P μ) ψ).X₂ := hQ
      have hker : ∀ z : Abelian.Ext.{u} (ofSub Q ψ.ker) (verma P lam) (n + 1), z = 0 := by
        rw [hkerψ]
        exact hext
      exact Abelian.Ext.eq_zero_of_shortExact_of_projective
        (shortExact_kerComplex Q (verma P μ) ψ (eV.surjective.comp hφ)) hker x

/-- **[HumO] Theorem 6.11 (a)**, first vanishing statement. Unless `μ ↑ λ` with `μ ≠ λ`,
`Extⁿ_𝒪(M(μ), M(λ)) = 0` for all `n > 0`. Finite type, algebraically closed field of
characteristic zero (Humphreys works over `ℂ`, with `μ` and `λ` in the dot-orbit of a dominant
integral weight). -/
theorem ext_verma_eq_zero {μ lam : Dual K H}
    (hμ : ¬ (P.IsStronglyLinked (Fact.out : A.IsFiniteCartan).isGeneralizedCartan μ lam ∧
      μ ≠ lam)) {n : ℕ} (hn : 0 < n) (x : Abelian.Ext.{u} (verma P μ) (verma P lam) n) :
    x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ext_verma_eq_zero_aux lam m μ hμ x

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
