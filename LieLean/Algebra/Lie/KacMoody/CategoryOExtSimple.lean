/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOExtVerma

/-!
# Vanishing of `Extⁿ` from Verma modules to simple modules

[HumO] Theorem 6.11 (a), second vanishing statement: unless `μ ↑ λ` with `μ ≠ λ`,
`Extⁿ_𝒪(M(μ), L(λ)) = 0` for all `n > 0` (`CategoryO.ext_simple_eq_zero`). As for Verma modules
(`CategoryO.ext_verma_eq_zero`), Humphreys states the theorem for weights in the dot-orbit of a
dominant integral weight; the argument applies to arbitrary weights and is formalized in that
generality.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.CategoryO.simple`: the simple module `L(λ)` as an object of
  `𝒪`.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.ofSubquotient`: a subquotient of an object of
  `𝒪`, as an object of `𝒪`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.CategoryO.ext_eq_zero_of_isLocalCompositionSeries`:
  `Extⁿ(M(μ), Y) = 0` if `Y` has a local composition series for `μ` whose irreducible factors
  `L(κ)` all have `Extⁿ(M(μ), L(κ)) = 0`.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.ext_simple_eq_zero`:
  **[HumO] Theorem 6.11 (a)** for simple modules.

## Proof

As in Humphreys: the sequence `0 → N(λ) → M(λ) → L(λ) → 0` gives
`Extⁿ(M(μ), M(λ)) → Extⁿ(M(μ), L(λ)) → Extⁿ⁺¹(M(μ), N(λ))`, the first group vanishes by the
Verma case, and the composition factors `L(κ)` of `N(λ)` satisfy `κ ↑ λ`, `κ ≠ λ`, so that the
hypothesis passes from `λ` to `κ`. Humphreys inducts downward along the finitely many weights
linked to `λ`; here the induction is on the height of `λ - μ`. Only the factors `L(κ)` with
`κ ≥ μ` need the induction: a local composition series of `N(λ)` for `μ` isolates them, and its
remaining factors have no weight `≥ μ`, so `Extⁿ(M(μ), -)` vanishes on them for every `n`
(`ext_verma_eq_zero_of_weightSpace`). If `λ` is not `≥ μ`, the same applies to `L(λ)` itself.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §6.11.
-/

open CategoryTheory Limits LieModule Module

noncomputable section

universe w u

namespace CategoryTheory.Abelian.Ext

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]

theorem eq_zero_of_isZero_right {X Y : C} (hY : IsZero Y) {n : ℕ} (x : Ext.{w} X Y n) :
    x = 0 := by
  rw [← comp_mk₀_id x, hY.eq_of_src (𝟙 Y) 0, mk₀_zero]
  simp

/-- `Extⁿ(X, Y₂) = 0` if `Extⁿ(X, Y₁) = 0 = Extⁿ(X, Y₃)` for a short exact sequence
`0 → Y₁ → Y₂ → Y₃ → 0`. -/
theorem eq_zero_of_shortExact_right {S : ShortComplex C} (hS : S.ShortExact) {X : C} {n : ℕ}
    (h₁ : ∀ x : Ext.{w} X S.X₁ n, x = 0) (h₃ : ∀ x : Ext.{w} X S.X₃ n, x = 0)
    (x : Ext.{w} X S.X₂ n) : x = 0 := by
  obtain ⟨x₁, rfl⟩ := covariant_sequence_exact₂ X hS x (h₃ _)
  rw [h₁ x₁]
  simp

/-- `Extⁿ(X, Y₃) = 0` if `Extⁿ(X, Y₂) = 0 = Extⁿ⁺¹(X, Y₁)` for a short exact sequence
`0 → Y₁ → Y₂ → Y₃ → 0`. -/
theorem eq_zero_of_shortExact_right_succ {S : ShortComplex C} (hS : S.ShortExact) {X : C}
    {n : ℕ} (h₂ : ∀ x : Ext.{w} X S.X₂ n, x = 0) (h₁ : ∀ x : Ext.{w} X S.X₁ (n + 1), x = 0)
    (x : Ext.{w} X S.X₃ n) : x = 0 := by
  obtain ⟨x₂, rfl⟩ := covariant_sequence_exact₃ X hS x rfl (h₁ _)
  rw [h₂ x₂]
  simp

end CategoryTheory.Abelian.Ext

namespace Matrix.Realization.KacMoodyAlgebra

section WeightSpace

variable {ι H : Type*} {K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}

/-- Weight spaces vanish together along an isomorphism of `𝔤`-modules. -/
theorem weightSpace_eq_bot_of_equiv {M M' : Type*} [AddCommGroup M] [Module K M]
    [LieRingModule P.KacMoodyAlgebra M] [LieModule K P.KacMoodyAlgebra M] [AddCommGroup M']
    [Module K M'] [LieRingModule P.KacMoodyAlgebra M'] [LieModule K P.KacMoodyAlgebra M']
    (e : M ≃ₗ⁅K,P.KacMoodyAlgebra⁆ M') {ρ : Dual K H} (h : weightSpace P M ρ = ⊥) :
    weightSpace P M' ρ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have hv' : e.symm v ∈ weightSpace P M ρ := map_mem_weightSpaceOfMap P e.symm.toLieModuleHom hv
  rw [h, Submodule.mem_bot] at hv'
  rw [Submodule.mem_bot, ← e.apply_symm_apply v]
  change e (e.symm v) = 0
  rw [hv', map_zero]

end WeightSpace

namespace CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P

/-! ### Simple modules and subquotients as objects of `𝒪` -/

variable (P) in
/-- The simple module `L(λ)` as an object of `𝒪`. -/
def simple (lam : Dual K H) : CategoryO.{u} P :=
  mk (IrreducibleModule P lam) (IrreducibleModule.isCategoryO P lam)
    ⟨{LieSubmodule.Quotient.mk' _ (VermaModule.hwv P lam)}, by
      rw [Finset.coe_singleton]
      exact VermaModule.lieSpan_map_hwv_eq_top _ (LieSubmodule.Quotient.surjective_mk' _)⟩

/-- The quotient map `N' → N' / N`, between the `U(𝔤)`-modules defined by `N'` and `N' / N`. -/
def subquotientMap (X : CategoryO.{u} P) (N N' : LieSubmodule K 𝔤 X.obj) :
    ofLie P N' →ₗ⁅K,𝔤⁆ ofLie P (N.Subquotient N') :=
  (ofLieEquiv (P := P) (N.Subquotient N')).toLieModuleHom.comp
    ((LieSubmodule.Quotient.mk' (N.comap N'.incl)).comp
      (ofLieEquiv (P := P) N').symm.toLieModuleHom)

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
theorem surjective_subquotientMap (X : CategoryO.{u} P) (N N' : LieSubmodule K 𝔤 X.obj) :
    Function.Surjective (subquotientMap X N N') := by
  intro z
  obtain ⟨y, hy⟩ := LieSubmodule.Quotient.surjective_mk' (N.comap N'.incl)
    ((ofLieEquiv (P := P) (N.Subquotient N')).symm z)
  exact ⟨ofLieEquiv (P := P) N' y,
    (congrArg (ofLieEquiv (P := P) (N.Subquotient N')) hy).trans
      ((ofLieEquiv (P := P) (N.Subquotient N')).apply_symm_apply z)⟩

/-- The subquotient `N' / N` of an object of `𝒪`, as an object of `𝒪`. -/
def ofSubquotient (X : CategoryO.{u} P) (N N' : LieSubmodule K 𝔤 X.obj) : CategoryO.{u} P :=
  ⟨ofLie P (N.Subquotient N'), isObj_of_surjective (X := (ofSub X N').obj)
    (ofLieModuleHom (subquotientMap X N N')) (surjective_subquotientMap X N N')
    (ofSub X N').property⟩

/-- The quotient map `N' → N' / N`. -/
def toSubquotient (X : CategoryO.{u} P) (N N' : LieSubmodule K 𝔤 X.obj) :
    N' →ₗ⁅K,𝔤⁆ (ofSubquotient X N N').obj :=
  (ofLieEquiv (P := P) (N.Subquotient N')).toLieModuleHom.comp (LieSubmodule.Quotient.mk' _)

theorem toSubquotient_eq_zero_iff (X : CategoryO.{u} P) (N N' : LieSubmodule K 𝔤 X.obj)
    (y : N') : toSubquotient X N N' y = 0 ↔ (y : X.obj) ∈ N := by
  change (LieSubmodule.Quotient.mk' (N.comap N'.incl) y : N.Subquotient N') = 0 ↔ _
  rw [LieSubmodule.Quotient.mk_eq_zero]
  rfl

theorem surjective_toSubquotient (X : CategoryO.{u} P) (N N' : LieSubmodule K 𝔤 X.obj) :
    Function.Surjective (toSubquotient X N N') :=
  (ofLieEquiv (P := P) (N.Subquotient N')).surjective.comp
    (LieSubmodule.Quotient.surjective_mk' _)

variable (P) in
/-- The quotient map `M(λ) → Z` onto an object `Z ≅ L(λ)`. -/
def toSimple (lam : Dual K H) (Z : CategoryO.{u} P)
    (e : Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P lam) : (verma P lam).obj →ₗ⁅K,𝔤⁆ Z.obj :=
  e.symm.toLieModuleHom.comp ((LieSubmodule.Quotient.mk' _).comp
    (ofLieEquiv (P := P) (VermaModule P lam)).symm.toLieModuleHom)

omit [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
theorem surjective_toSimple (lam : Dual K H) (Z : CategoryO.{u} P)
    (e : Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P lam) : Function.Surjective (toSimple P lam Z e) := by
  intro z
  obtain ⟨m, hm⟩ := LieSubmodule.Quotient.surjective_mk' (VermaModule.maxSubmodule P lam) (e z)
  refine ⟨ofLieEquiv (P := P) (VermaModule P lam) m, ?_⟩
  change e.symm (LieSubmodule.Quotient.mk' (VermaModule.maxSubmodule P lam) m) = z
  rw [hm, LieModuleEquiv.symm_apply_apply]

/-! ### `Ext` along local composition series -/

/-- `Extⁿ(M(μ), Y) = 0` along a local composition series for `μ` from `N` to `M`, given
`Extⁿ(M(μ), N) = 0` and `Extⁿ(M(μ), L(κ)) = 0` for its irreducible factors `L(κ)`: the factors
without a weight `≥ μ` contribute nothing by `ext_verma_eq_zero_of_weightSpace`. -/
theorem ext_eq_zero_of_isLocalCompositionSeries (Y : CategoryO.{u} P) (μ : Dual K H) (n : ℕ)
    {N M : LieSubmodule K 𝔤 Y.obj} {l : List (LieSubmodule K 𝔤 Y.obj × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P μ N l M)
    (hN : ∀ x : Abelian.Ext.{u} (verma P μ) (ofSub Y N) n, x = 0)
    (hfac : ∀ κ ∈ factorWeights l, ∀ Z : CategoryO.{u} P, (Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P κ) →
      ∀ x : Abelian.Ext.{u} (verma P μ) Z n, x = 0) :
    ∀ x : Abelian.Ext.{u} (verma P μ) (ofSub Y M) n, x = 0 := by
  induction l generalizing N with
  | nil =>
    rw [← IsLocalCompositionSeries.nil_iff.mp hl]
    exact hN
  | cons a l ih =>
    obtain ⟨N', o⟩ := a
    obtain ⟨hle, hf, hl'⟩ := IsLocalCompositionSeries.cons_iff.mp hl
    refine ih hl' ?_ fun κ hκ ↦ hfac κ (by cases o <;> simp [hκ])
    have hS := shortExact_subComplex Y hle (ofSubquotient Y N N') (toSubquotient Y N N')
      (fun x hx ↦ (toSubquotient_eq_zero_iff Y N N' ⟨x, hle hx⟩).mpr hx)
      (surjective_toSubquotient Y N N') fun y hy ↦ (toSubquotient_eq_zero_iff Y N N' y).mp hy
    refine Abelian.Ext.eq_zero_of_shortExact_right hS hN ?_
    cases o with
    | none =>
      refine ext_verma_eq_zero_of_weightSpace _ n μ fun ρ hρ ↦ ?_
      exact weightSpace_eq_bot_of_equiv (ofLieEquiv (P := P) (N.Subquotient N'))
        ((hf : ∀ ρ, μ ∈ cone P ρ → weightSpace P (N.Subquotient N') ρ = ⊥) ρ hρ)
    | some κ =>
      obtain ⟨-, ⟨ψ⟩⟩ := hf
      exact hfac κ (by simp) _ ((ofLieEquiv (P := P) (N.Subquotient N')).symm.trans ψ)

/-! ### `Extⁿ(M(μ), L(λ))` -/

theorem ext_simple_eq_zero_aux (μ : Dual K H) (d : ℕ) : ∀ (lam : Dual K H) (k : ι → ℤ),
    0 ≤ k → μ = lam - P.rootOf k → ∑ i, k i ≤ d →
    ¬ (P.IsStronglyLinked (Fact.out : A.IsFiniteCartan).isGeneralizedCartan μ lam ∧ μ ≠ lam) →
    ∀ Z : CategoryO.{u} P, (Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P lam) →
      ∀ (n : ℕ) (x : Abelian.Ext.{u} (verma P μ) Z (n + 1)), x = 0 := by
  have hA : A.IsFiniteCartan := Fact.out
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro lam k hk hμk hkd hμ Z e n
  let φ := toSimple P lam Z e
  have hφ : Function.Surjective φ := surjective_toSimple lam Z e
  let Y := ofSub (verma P lam) φ.ker
  have hV := (verma P lam).property.1
  have hY := Y.property.1
  -- the multiplicities of the kernel `N(λ)` of `M(λ) → L(λ)`
  have hmult (κ : Dual K H) : (VermaModule.isCategoryO P lam).multiplicity κ =
      hY.multiplicity κ + (IrreducibleModule.isCategoryO P lam).multiplicity κ := by
    rw [IsCategoryO.multiplicity_congr (VermaModule.isCategoryO P lam) hV
        (ofLieEquiv (P := P) (VermaModule P lam)),
      IsCategoryO.multiplicity_eq_add_of_exact (hV.lieSubmodule φ.ker) hV Z.property.1
        φ.ker.incl φ Subtype.val_injective φ.ker.range_incl.symm hφ,
      IsCategoryO.multiplicity_congr (hV.lieSubmodule φ.ker) hY (ofLieEquiv (P := P) φ.ker),
      IsCategoryO.multiplicity_congr Z.property.1 (IrreducibleModule.isCategoryO P lam) e]
  have hker (κ : Dual K H) (hκ : hY.multiplicity κ ≠ 0) :
      (VermaModule.isCategoryO P lam).multiplicity κ ≠ 0 ∧ κ ≠ lam := by
    refine ⟨by rw [hmult]; omega, ?_⟩
    rintro rfl
    have h1 : (IrreducibleModule.isCategoryO P κ).multiplicity κ = 1 := by
      rw [IrreducibleModule.multiplicity_eq]
      simp
    have h := hmult κ
    rw [VermaModule.multiplicity_self, h1] at h
    omega
  refine Abelian.Ext.eq_zero_of_shortExact_right_succ (shortExact_kerComplex (verma P lam) Z φ hφ)
    (ext_verma_eq_zero hμ (Nat.succ_pos n)) ?_
  -- `Extⁿ⁺²(M(μ), N(λ)) = 0`, along a local composition series of `N(λ)` for `μ`
  let z : Y.obj →ₗ⁅K,𝔤⁆ (ofSub Y ⊥).obj := 0
  have hz : Function.Surjective z := fun _ ↦ ⟨0, (ofLieEquiv (P := P)
    (⊥ : LieSubmodule K 𝔤 Y.obj)).symm.injective (Subsingleton.elim _ _)⟩
  have hz0 : z.ker = ⊤ := eq_top_iff.mpr fun y _ ↦ LieModuleHom.mem_ker.mpr rfl
  suffices h : ∀ x : Abelian.Ext.{u} (verma P μ) (ofSub Y z.ker) (n + 1 + 1), x = 0 from
    Abelian.Ext.eq_zero_of_shortExact_right (shortExact_kerComplex Y (ofSub Y ⊥) z hz) h
      (Abelian.Ext.eq_zero_of_isZero_right (isZero_ofSub_bot Y))
  rw [hz0]
  obtain ⟨l, hl⟩ := hY.exists_isLocalCompositionSeries μ
  refine ext_eq_zero_of_isLocalCompositionSeries Y μ _ hl
    (Abelian.Ext.eq_zero_of_isZero_right (isZero_ofSub_bot Y)) fun κ hκ Z' e' x ↦ ?_
  obtain ⟨k', hk', hμk'⟩ := hl.mem_cone_of_mem_factorWeights hκ
  obtain ⟨hκV, hκne⟩ := hker κ ((hY.multiplicity_ne_zero_iff ⟨k', hk', hμk'⟩ hl).mpr hκ)
  have hκl := VermaModule.isStronglyLinked_of_multiplicity_ne_zero P hA hκV
  obtain ⟨j, hj, hκj⟩ := VermaModule.mem_cone_of_multiplicity_ne_zero hκV
  -- the height of `κ - μ` is smaller than that of `λ - μ`
  have hkj : k = j + k' := P.rootOf_injective (by
    have e1 : P.rootOf k = lam - μ := by rw [hμk]; abel
    have e2 : P.rootOf j = lam - κ := by rw [hκj]; abel
    have e3 : P.rootOf k' = κ - μ := by rw [hμk']; abel
    rw [map_add, e1, e2, e3]
    abel)
  have hj0 : j ∈ posCone ι := ⟨hj, fun h0 ↦ hκne (by rw [hκj, h0, map_zero, sub_zero])⟩
  have h1 := one_le_sum_of_mem_posCone hj0
  have h2 : ∑ i, k i = ∑ i, j i + ∑ i, k' i := by
    rw [hkj, ← Finset.sum_add_distrib]
    rfl
  have h3 : ((∑ i, k' i).toNat : ℤ) = ∑ i, k' i :=
    Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ ↦ hk' i)
  have hlt : (∑ i, k' i).toNat < d := by omega
  -- the hypothesis passes from `λ` to `κ`
  have hnot : ¬ (P.IsStronglyLinked hA.isGeneralizedCartan μ κ ∧ μ ≠ κ) := by
    rintro ⟨hμκ, hμκne⟩
    have hμl : μ = lam := by
      by_contra h
      exact hμ ⟨Relation.ReflTransGen.trans hκl hμκ, h⟩
    exact hμκne (eq_of_mem_cone_of_mem_cone ⟨k', hk', hμk'⟩ (by rw [hμl]; exact ⟨j, hj, hκj⟩))
  exact ih _ hlt κ k' hk' hμk' h3.ge hnot Z' e' (n + 1) x

/-- **[HumO] Theorem 6.11 (a)**, second vanishing statement, for any object `Z ≅ L(λ)`. -/
theorem ext_simple_eq_zero_of_equiv {μ lam : Dual K H}
    (hμ : ¬ (P.IsStronglyLinked (Fact.out : A.IsFiniteCartan).isGeneralizedCartan μ lam ∧
      μ ≠ lam)) (Z : CategoryO.{u} P) (e : Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P lam) {n : ℕ}
    (hn : 0 < n) (x : Abelian.Ext.{u} (verma P μ) Z n) : x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases hc : μ ∈ cone P lam
  · obtain ⟨k, hk, hμk⟩ := hc
    exact ext_simple_eq_zero_aux μ _ lam k hk hμk (Int.self_le_toNat _) hμ Z e m x
  · refine ext_verma_eq_zero_of_weightSpace Z _ μ (fun ρ hρ ↦ ?_) x
    by_contra hne
    exact hc (mem_cone_trans hρ (IrreducibleModule.mem_cone_of_weightSpace_ne_bot
      fun h ↦ hne (weightSpace_eq_bot_of_equiv e.symm h)))

/-- **[HumO] Theorem 6.11 (a)**, second vanishing statement. Unless `μ ↑ λ` with `μ ≠ λ`,
`Extⁿ_𝒪(M(μ), L(λ)) = 0` for all `n > 0`. Finite type, algebraically closed field of
characteristic zero (Humphreys works over `ℂ`, with `μ` and `λ` in the dot-orbit of a dominant
integral weight). -/
theorem ext_simple_eq_zero {μ lam : Dual K H}
    (hμ : ¬ (P.IsStronglyLinked (Fact.out : A.IsFiniteCartan).isGeneralizedCartan μ lam ∧
      μ ≠ lam)) {n : ℕ} (hn : 0 < n) (x : Abelian.Ext.{u} (verma P μ) (simple P lam) n) :
    x = 0 :=
  ext_simple_eq_zero_of_equiv hμ _ (ofLieEquiv (P := P) (IrreducibleModule P lam)).symm hn x

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
