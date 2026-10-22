/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOExtDualVerma
import LieLean.Algebra.Lie.KacMoody.CategoryOExtSimple
import LieLean.Algebra.Lie.KacMoody.CompositionSeries.SimpleQuotient
import LieLean.Algebra.Lie.KacMoody.TranslationSimple

/-!
# Towards the `Ext` criterion for standard filtrations

Steps (2) and (3) of the proof of [HumO] Theorem 6.13 ((c) ⇒ (a)). Let `Y ∈ 𝒪` with
`Ext¹_𝒪(Y, M(μ)^∨) = 0` for all `μ`.

* (2) If `Hom_𝒪(Y, L(ν)) = 0` for all `ν < μ`, then `Ext¹_𝒪(Y, L(μ)) = 0`
  (`CategoryO.ext_one_simple_eq_zero`): apply `Hom(Y, -)` to `0 → L(μ) → M(μ)^∨ → Q → 0`; every
  composition factor `L(ν)` of `Q` has `ν < μ`, so `Hom(Y, Q) = 0`.
* (3) If `Ext¹_𝒪(Y, L(ν)) = 0` for all `ν < λ`, then every morphism `Y → L(λ)` lifts to `M(λ)`
  (`CategoryO.exists_lift_verma`): the composition factors of `N(λ) = ker(M(λ) → L(λ))` are
  `L(ν)` with `ν < λ`, so `Ext¹(Y, N(λ)) = 0` (`CategoryO.ext_eq_zero_of_multiplicity`).

Humphreys argues that `Hom(Y, Q) = 0` via the simple submodules of `Q`; here a nonzero morphism
`Y → Q` gives a nonzero morphism from `Y` onto a simple quotient `L(ν)` of its image, and `L(ν)` is
a composition factor of `Q`.

## Main results

* `CategoryTheory.Abelian.Ext.eq_zero_of_shortExact_right_of_hom`: `Ext¹(X, Y₁) = 0` if
  `Ext¹(X, Y₂) = 0` and `Hom(X, Y₃) = 0`, for `0 → Y₁ → Y₂ → Y₃ → 0` exact.
* `CategoryTheory.Abelian.Ext.exists_comp_of_shortExact`: if `Ext¹(X, Y₁) = 0`, every morphism
  `X → Y₃` lifts to `Y₂`.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.ext_eq_zero_of_multiplicity`: `Extⁿ(X, W) = 0` if
  `Extⁿ(X, L(ν)) = 0` for every composition factor `L(ν)` of `W`.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.ext_one_simple_eq_zero`: step (2).
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.exists_lift_verma`: step (3).

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §6.13.
-/

open CategoryTheory Limits LieModule Module

noncomputable section

universe w u

namespace CategoryTheory.Abelian.Ext

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]

/-- `Ext¹(X, Y₁) = 0` if `Ext¹(X, Y₂) = 0` and `Hom(X, Y₃) = 0`, for a short exact sequence
`0 → Y₁ → Y₂ → Y₃ → 0`. -/
theorem eq_zero_of_shortExact_right_of_hom {S : ShortComplex C} (hS : S.ShortExact) {X : C}
    (h₂ : ∀ x : Ext.{w} X S.X₂ 1, x = 0) (h₃ : ∀ f : X ⟶ S.X₃, f = 0)
    (x : Ext.{w} X S.X₁ 1) : x = 0 := by
  obtain ⟨x₃, rfl⟩ := covariant_sequence_exact₁ X hS x (h₂ _) (zero_add 1)
  rw [← mk₀_homEquiv₀_apply x₃, h₃ (homEquiv₀ x₃), mk₀_zero]
  simp

/-- If `Ext¹(X, Y₁) = 0`, every morphism `X → Y₃` lifts along `Y₂ → Y₃`, for a short exact
sequence `0 → Y₁ → Y₂ → Y₃ → 0`. -/
theorem exists_comp_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) {X : C}
    (h₁ : ∀ x : Ext.{w} X S.X₁ 1, x = 0) (f : X ⟶ S.X₃) : ∃ g : X ⟶ S.X₂, g ≫ S.g = f := by
  obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ X hS (mk₀ f) (zero_add 1) (h₁ _)
  refine ⟨homEquiv₀ x₂, (mk₀_bijective X S.X₃).1 ?_⟩
  rw [← mk₀_comp_mk₀, mk₀_homEquiv₀_apply, hx₂]

end CategoryTheory.Abelian.Ext

namespace Matrix.Realization.KacMoodyAlgebra

section Hom

variable {ι H K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H} {Y Q : Type*} [AddCommGroup Y]
  [Module K Y] [LieRingModule P.KacMoodyAlgebra Y] [LieModule K P.KacMoodyAlgebra Y]
  [AddCommGroup Q] [Module K Q] [LieRingModule P.KacMoodyAlgebra Q]
  [LieModule K P.KacMoodyAlgebra Q]

/-- A morphism `Y → Q` into a noetherian module in `𝒪` vanishes if every morphism from `Y` to a
composition factor `L(ν)` of `Q` does: a nonzero morphism maps onto a simple quotient of its
image. -/
theorem IsCategoryO.lieModuleHom_eq_zero (hQ : IsCategoryO P Q)
    [WellFoundedGT (LieSubmodule K P.KacMoodyAlgebra Q)]
    (h : ∀ ν, hQ.multiplicity ν ≠ 0 →
      ∀ ψ : Y →ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P ν, ψ = 0)
    (φ : Y →ₗ⁅K,P.KacMoodyAlgebra⁆ Q) : φ = 0 := by
  by_contra hφ
  have hr : φ.range ≠ ⊥ := fun h0 ↦ hφ (by
    ext y
    have hy : φ y ∈ φ.range := (LieModuleHom.mem_range φ (φ y)).mpr ⟨y, rfl⟩
    rw [h0, LieSubmodule.mem_bot] at hy
    exact hy)
  obtain ⟨M', -, ν, hν, ⟨ψ⟩⟩ := hQ.exists_subquotient_equiv_of_ne_bot hr
  let q : Y →ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P ν :=
    ψ.toLieModuleHom.comp ((LieSubmodule.Quotient.mk' (M'.comap φ.range.incl)).comp
      (φ.codRestrict φ.range fun y ↦ (LieModuleHom.mem_range φ (φ y)).mpr ⟨y, rfl⟩))
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨w, hw⟩ := LieSubmodule.Quotient.surjective_mk' (M'.comap φ.range.incl) (ψ.symm z)
    obtain ⟨y, hy⟩ := (LieModuleHom.mem_range φ w).mp w.2
    refine ⟨y, ?_⟩
    have hyw : φ.codRestrict φ.range (fun y ↦ (LieModuleHom.mem_range φ (φ y)).mpr ⟨y, rfl⟩) y =
        w := Subtype.ext hy
    change ψ (LieSubmodule.Quotient.mk' _ (φ.codRestrict φ.range _ y)) = z
    rw [hyw, hw, LieModuleEquiv.apply_symm_apply]
  obtain ⟨z, hz⟩ := exists_ne (0 : IrreducibleModule P ν)
  obtain ⟨y, rfl⟩ := hq z
  exact hz (LieModuleHom.congr_fun (h ν hν q) y)

end Hom

namespace CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P

/-! ### Morphisms and `Ext` along isomorphisms -/

/-- A morphism in `𝒪` vanishes if every morphism of the underlying `𝔤`-modules does. -/
theorem hom_eq_zero_of_lie {Y Z : CategoryO.{u} P} (h : ∀ φ : Y.obj →ₗ⁅K,𝔤⁆ Z.obj, φ = 0)
    (f : Y ⟶ Z) : f = 0 := by
  ext y
  exact LieModuleHom.congr_fun (h (toLieModuleHom f.hom)) y

/-- `Extⁿ(Y, -)` vanishes together on objects of `𝒪` with isomorphic underlying `𝔤`-modules. -/
theorem ext_eq_zero_of_equiv_right {Y Z Z' : CategoryO.{u} P} (e : Z.obj ≃ₗ⁅K,𝔤⁆ Z'.obj) {n : ℕ}
    (h : ∀ x : Abelian.Ext.{u} Y Z n, x = 0) (x : Abelian.Ext.{u} Y Z' n) : x = 0 := by
  let f : Z ⟶ Z' := (IsObj.{u} P).homMk (ofLieModuleHom e.toLieModuleHom)
  let g : Z' ⟶ Z := (IsObj.{u} P).homMk (ofLieModuleHom e.symm.toLieModuleHom)
  have hgf : g ≫ f = 𝟙 Z' := by
    ext z
    exact e.apply_symm_apply z
  have hx : x = (x.comp (Abelian.Ext.mk₀ g) (add_zero n)).comp (Abelian.Ext.mk₀ f)
      (add_zero n) := by
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, hgf,
      Abelian.Ext.comp_mk₀_id]
  rw [hx, h (x.comp _ _)]
  simp

/-- `Extⁿ(X, Y) = 0` if `Extⁿ(X, Y') = 0` for the object `Y'` given by the submodule `⊤` of `Y`. -/
theorem ext_eq_zero_of_ofSub_top_right (X Y : CategoryO.{u} P) {n : ℕ}
    (h : ∀ x : Abelian.Ext.{u} X (ofSub Y ⊤) n, x = 0) (x : Abelian.Ext.{u} X Y n) : x = 0 :=
  ext_eq_zero_of_equiv_right ((ofLieEquiv (P := P) (⊤ : LieSubmodule K 𝔤 Y.obj)).symm.trans
    (LieModuleEquiv.ofBijective (⊤ : LieSubmodule K 𝔤 Y.obj).incl
      ⟨Subtype.val_injective, fun y ↦ ⟨⟨y, LieSubmodule.mem_top y⟩, rfl⟩⟩)) h x

/-! ### `Ext` along composition factors -/

/-- `Extⁿ(X, W) = 0` if `Extⁿ(X, Z) = 0` for every `Z ≅ L(ν)` with `L(ν)` a composition factor
of `W`: induction on the submodules of `W`, which form an artinian and noetherian lattice. -/
theorem ext_eq_zero_of_multiplicity (X W : CategoryO.{u} P) (n : ℕ)
    (h : ∀ ν, W.property.1.multiplicity ν ≠ 0 → ∀ Z : CategoryO.{u} P,
      (Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P ν) → ∀ x : Abelian.Ext.{u} X Z n, x = 0)
    (x : Abelian.Ext.{u} X W n) : x = 0 := by
  obtain ⟨S, hS⟩ := W.property.2
  have := W.property.1.wellFoundedLT_lieSubmodule P (Fact.out : A.IsFiniteCartan) hS
  have := W.property.1.wellFoundedGT_lieSubmodule P (Fact.out : A.IsFiniteCartan) hS
  refine ext_eq_zero_of_ofSub_top_right X W (WellFoundedLT.induction
    (motive := fun M ↦ ∀ x : Abelian.Ext.{u} X (ofSub W M) n, x = 0) ⊤ fun M ih ↦ ?_) x
  by_cases hM : M = ⊥
  · subst hM
    exact Abelian.Ext.eq_zero_of_isZero_right (isZero_ofSub_bot W)
  obtain ⟨M', hM'M, ν, hν, ⟨ψ⟩⟩ := W.property.1.exists_subquotient_equiv_of_ne_bot hM
  have hS := shortExact_subComplex W hM'M.le (ofSubquotient W M' M) (toSubquotient W M' M)
    (fun y hy ↦ (toSubquotient_eq_zero_iff W M' M ⟨y, hM'M.le hy⟩).mpr hy)
    (surjective_toSubquotient W M' M) fun y hy ↦ (toSubquotient_eq_zero_iff W M' M y).mp hy
  exact Abelian.Ext.eq_zero_of_shortExact_right hS (ih M' hM'M)
    (h ν hν _ ((ofLieEquiv (P := P) (M'.Subquotient M)).symm.trans ψ))

/-! ### Quotients as objects of `𝒪` -/

/-- The quotient map `X → X / N`, between the `U(𝔤)`-modules defined by `X` and `X / N`. -/
def quotientMap (X : CategoryO.{u} P) (N : LieSubmodule K 𝔤 X.obj) :
    X.obj →ₗ⁅K,𝔤⁆ ofLie P (X.obj ⧸ N) :=
  (ofLieEquiv (P := P) (X.obj ⧸ N)).toLieModuleHom.comp (LieSubmodule.Quotient.mk' N)

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
theorem surjective_quotientMap (X : CategoryO.{u} P) (N : LieSubmodule K 𝔤 X.obj) :
    Function.Surjective (quotientMap X N) :=
  (ofLieEquiv (P := P) (X.obj ⧸ N)).surjective.comp (LieSubmodule.Quotient.surjective_mk' N)

/-- The quotient `X / N` of an object of `𝒪`, as an object of `𝒪`. -/
def ofQuotient (X : CategoryO.{u} P) (N : LieSubmodule K 𝔤 X.obj) : CategoryO.{u} P :=
  ⟨ofLie P (X.obj ⧸ N), isObj_of_surjective (ofLieModuleHom (quotientMap X N))
    (surjective_quotientMap X N) X.property⟩

/-- The quotient map `X → X / N`. -/
def toQuotient (X : CategoryO.{u} P) (N : LieSubmodule K 𝔤 X.obj) :
    X.obj →ₗ⁅K,𝔤⁆ (ofQuotient X N).obj :=
  quotientMap X N

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
theorem toQuotient_eq_zero_iff (X : CategoryO.{u} P) (N : LieSubmodule K 𝔤 X.obj) (x : X.obj) :
    toQuotient X N x = 0 ↔ x ∈ N := by
  change (LieSubmodule.Quotient.mk' N x : X.obj ⧸ N) = 0 ↔ _
  rw [LieSubmodule.Quotient.mk_eq_zero]
  rfl

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
theorem surjective_toQuotient (X : CategoryO.{u} P) (N : LieSubmodule K 𝔤 X.obj) :
    Function.Surjective (toQuotient X N) :=
  surjective_quotientMap X N

/-! ### Step (2): `Ext¹(Y, L(μ))` -/

/-- The embedding `L(μ) ↪ M(μ)^∨`. -/
def simpleToDualVerma (μ : Dual K H) : IrreducibleModule P μ →ₗ⁅K,𝔤⁆ (dualVerma P μ).obj :=
  (ofLieEquiv (P := P) (restrictedDual P (VermaModule P μ))).toLieModuleHom.comp
    (IrreducibleModule.toRestrictedDual P μ)

omit [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
theorem injective_simpleToDualVerma (μ : Dual K H) :
    Function.Injective (simpleToDualVerma (P := P) μ) :=
  (ofLieEquiv (P := P) (restrictedDual P (VermaModule P μ))).injective.comp
    (IrreducibleModule.toRestrictedDual_injective P μ)

/-- **[HumO] Theorem 6.13, proof, step (2).** If `Ext¹(Y, M(μ)^∨) = 0` and every morphism from
`Y` to `L(ν)` with `ν < μ` vanishes, then `Ext¹(Y, Z) = 0` for every `Z ≅ L(μ)`. -/
theorem ext_one_simple_eq_zero (Y : CategoryO.{u} P) (μ : Dual K H)
    (hdual : ∀ x : Abelian.Ext.{u} Y (dualVerma P μ) 1, x = 0)
    (hhom : ∀ ν ∈ cone P μ, ν ≠ μ → ∀ ψ : Y.obj →ₗ⁅K,𝔤⁆ IrreducibleModule P ν, ψ = 0)
    (Z : CategoryO.{u} P) (e : Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P μ)
    (x : Abelian.Ext.{u} Y Z 1) : x = 0 := by
  let D := dualVerma P μ
  let ι := simpleToDualVerma (P := P) μ
  let Q := ofQuotient D ι.range
  let φ := toQuotient D ι.range
  have hφ : Function.Surjective φ := surjective_toQuotient D ι.range
  have hker (y : D.obj) : y ∈ φ.ker ↔ ∃ m, ι m = y := by
    rw [LieModuleHom.mem_ker, toQuotient_eq_zero_iff, LieModuleHom.mem_range]
  -- the kernel of `M(μ)^∨ → Q` is `L(μ)`
  let eK : IrreducibleModule P μ ≃ₗ⁅K,𝔤⁆ φ.ker := LieModuleEquiv.ofBijective
    (ι.codRestrict φ.ker fun m ↦ (hker (ι m)).mpr ⟨m, rfl⟩)
    ⟨fun a b hab ↦ injective_simpleToDualVerma μ (congrArg Subtype.val hab), fun y ↦ by
      obtain ⟨m, hm⟩ := (hker y).mp y.2
      exact ⟨m, Subtype.ext hm⟩⟩
  have hS := shortExact_kerComplex D Q φ hφ
  refine ext_eq_zero_of_equiv_right
    ((ofLieEquiv (P := P) φ.ker).symm.trans (eK.symm.trans e.symm)) ?_ x
  refine Abelian.Ext.eq_zero_of_shortExact_right_of_hom hS hdual fun f ↦ ?_
  -- `Hom(Y, Q) = 0`: the composition factors `L(ν)` of `Q` have `ν < μ`
  have hD := D.property.1
  have hQ := Q.property.1
  have hmult (ν : Dual K H) : (VermaModule.isCategoryO P μ).multiplicity ν =
      (IrreducibleModule.isCategoryO P μ).multiplicity ν + hQ.multiplicity ν := by
    rw [← multiplicity_restrictedDual (VermaModule.isCategoryO P μ),
      IsCategoryO.multiplicity_congr (isCategoryO_restrictedDual (VermaModule.isCategoryO P μ)) hD
        (ofLieEquiv (P := P) (restrictedDual P (VermaModule P μ))),
      IsCategoryO.multiplicity_eq_add_of_exact (hD.lieSubmodule φ.ker) hD hQ φ.ker.incl φ
        Subtype.val_injective φ.ker.range_incl.symm hφ,
      IsCategoryO.multiplicity_congr (hD.lieSubmodule φ.ker) (IrreducibleModule.isCategoryO P μ)
        eK.symm]
  obtain ⟨S, hS'⟩ := Q.property.2
  have := hQ.wellFoundedGT_lieSubmodule P (Fact.out : A.IsFiniteCartan) hS'
  refine hom_eq_zero_of_lie (fun ψ ↦ hQ.lieModuleHom_eq_zero (fun ν hν ↦ ?_) ψ) f
  have h := hmult ν
  rw [IrreducibleModule.multiplicity_eq] at h
  refine hhom ν (VermaModule.mem_cone_of_multiplicity_ne_zero (by omega)) ?_
  rintro rfl
  rw [VermaModule.multiplicity_self] at h
  simp at h
  omega

/-! ### Step (3): lifting to `M(λ)` -/

/-- **[HumO] Theorem 6.13, proof, step (3).** If `Ext¹(Y, Z) = 0` for every `Z ≅ L(ν)` with
`ν < λ`, then every morphism `Y → L(λ)` lifts along `M(λ) → L(λ)`. -/
theorem exists_lift_verma (Y : CategoryO.{u} P) (lam : Dual K H)
    (hext : ∀ ν ∈ cone P lam, ν ≠ lam → ∀ Z : CategoryO.{u} P,
      (Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P ν) → ∀ x : Abelian.Ext.{u} Y Z 1, x = 0)
    (φ : Y.obj →ₗ⁅K,𝔤⁆ IrreducibleModule P lam) :
    ∃ ψ : Y.obj →ₗ⁅K,𝔤⁆ VermaModule P lam,
      (LieSubmodule.Quotient.mk' (VermaModule.maxSubmodule P lam)).comp ψ = φ := by
  let eL := (ofLieEquiv (P := P) (IrreducibleModule P lam)).symm
  let π := toSimple P lam (simple P lam) eL
  have hπ : Function.Surjective π := surjective_toSimple lam (simple P lam) eL
  let N := ofSub (verma P lam) π.ker
  have hV := (verma P lam).property.1
  have hS := shortExact_kerComplex (verma P lam) (simple P lam) π hπ
  -- the composition factors `L(ν)` of `N(λ)` have `ν < λ`
  have hmult (ν : Dual K H) : (VermaModule.isCategoryO P lam).multiplicity ν =
      N.property.1.multiplicity ν + (IrreducibleModule.isCategoryO P lam).multiplicity ν := by
    rw [IsCategoryO.multiplicity_congr (VermaModule.isCategoryO P lam) hV
        (ofLieEquiv (P := P) (VermaModule P lam)),
      IsCategoryO.multiplicity_eq_add_of_exact (hV.lieSubmodule π.ker) hV (simple P lam).property.1
        π.ker.incl π Subtype.val_injective π.ker.range_incl.symm hπ,
      IsCategoryO.multiplicity_congr (hV.lieSubmodule π.ker) N.property.1
        (ofLieEquiv (P := P) π.ker),
      IsCategoryO.multiplicity_congr (simple P lam).property.1
        (IrreducibleModule.isCategoryO P lam) eL]
  have hN1 : ∀ x : Abelian.Ext.{u} Y N 1, x = 0 := by
    refine ext_eq_zero_of_multiplicity Y N 1 fun ν hν ↦ ?_
    have h := hmult ν
    refine hext ν (VermaModule.mem_cone_of_multiplicity_ne_zero (by omega)) ?_
    rintro rfl
    rw [VermaModule.multiplicity_self, IrreducibleModule.multiplicity_eq] at h
    simp at h
    omega
  obtain ⟨g, hg⟩ := Abelian.Ext.exists_comp_of_shortExact hS hN1
    ((IsObj.{u} P).homMk (ofLieModuleHom (eL.symm.toLieModuleHom.comp φ)))
  refine ⟨(ofLieEquiv (P := P) (VermaModule P lam)).symm.toLieModuleHom.comp
    (toLieModuleHom g.hom), LieModuleHom.ext fun y ↦ eL.symm.injective ?_⟩
  exact congrArg (fun k : Y ⟶ simple P lam ↦ k.hom.hom y) hg

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
