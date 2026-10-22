/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOProjDimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Category.ModuleCat.Algebra

/-!
# Finiteness of `Extⁿ` in `𝒪`

Two finiteness facts used for the Euler characteristics `∑ₙ (-1)ⁿ dim Extⁿ_𝒪(M(μ), N)` of
[HumO] §6.14:

* `Extⁿ_𝒪(X, Y)` is a finite-dimensional `K`-vector space for all `X, Y ∈ 𝒪`
  (`CategoryO.instFiniteExt`), starting from `Hom` ([HumO] Thm 1.11).
* every Verma module has finite projective dimension: `Extⁿ(M(μ), -) = 0` once `n` exceeds the
  number of weights of the dot orbit `W·μ` strictly above `μ`
  (`CategoryO.hasProjectiveDimensionLT_verma`).

Humphreys quotes the second fact from §6.9, which treats regular integral blocks; here it is
proved directly for every `μ`, by dimension shifting along `P(μ) → M(μ)` as in Prop 6.9 (a).

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Thm 1.11, §6.9, §6.14.
-/

open CategoryTheory Limits LieModule Module

noncomputable section

universe u

namespace Matrix.Realization.KacMoodyAlgebra

namespace CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

local notation "𝔤" => KacMoodyAlgebra P

/-! ### Finite-dimensionality -/

/-- Morphisms in `𝒪` as morphisms of `𝔤`-modules, `K`-linearly. -/
def homToLie (X Y : CategoryO.{u} P) : (X ⟶ Y) →ₗ[K] (X.obj →ₗ⁅K,𝔤⁆ Y.obj) where
  toFun f := toLieModuleHom f.hom
  map_add' _ _ := LieModuleHom.ext fun _ ↦ rfl
  map_smul' _ _ := LieModuleHom.ext fun _ ↦ rfl

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
theorem injective_homToLie (X Y : CategoryO.{u} P) : Function.Injective (homToLie X Y) :=
  fun f g h ↦ by
    ext y
    exact LieModuleHom.congr_fun h y

/-- `Hom` spaces in `𝒪` are finite-dimensional ([HumO] Thm 1.11). -/
instance instFiniteHom (X Y : CategoryO.{u} P) : Module.Finite K (X ⟶ Y) := by
  obtain ⟨S, hS⟩ := X.property.2
  have := X.property.1.finiteDimensional_hom P hS Y.property.1
  exact Module.Finite.of_injective (homToLie X Y) (injective_homToLie X Y)

/-- `Extⁿ` in `𝒪` is finite-dimensional: `Ext⁰ = Hom`, and `Extⁿ⁺¹(X, Y)` is a quotient of
`Extⁿ(K, Y)` for a projective presentation `0 → K → P → X → 0`. -/
instance instFiniteExt (X Y : CategoryO.{u} P) (n : ℕ) :
    Module.Finite K (Abelian.Ext.{u} X Y n) := by
  induction n generalizing X with
  | zero => exact Module.Finite.equiv (Abelian.Ext.linearEquiv₀ (R := K)).symm
  | succ n ih =>
    let S := ShortComplex.mk _ _ (kernel.condition (Projective.π X))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S.g) }
    let f : Abelian.Ext.{u} S.X₁ Y n →ₗ[K] Abelian.Ext.{u} X Y (n + 1) :=
      { toFun := fun x ↦ hS.extClass.comp x (add_comm 1 n)
        map_add' := fun x y ↦ Abelian.Ext.comp_add _ _ _ _
        map_smul' := fun r x ↦ Abelian.Ext.comp_smul _ _ _ r }
    have hf : Function.Surjective f := fun x₃ ↦
      Abelian.Ext.contravariant_sequence_exact₃ hS Y x₃ (Abelian.Ext.eq_zero_of_projective _)
        (by omega)
    have := ih S.X₁
    exact Module.Finite.of_surjective f hf

/-! ### Projective dimension of Verma modules -/

variable (hA : A.IsFiniteCartan)

variable (P) in
/-- The weights of the dot orbit `W·μ` strictly above `μ`. -/
def dotOrbitAbove (μ : Dual K H) : Set (Dual K H) :=
  {κ | (∃ w : P.weylGroup hA.isGeneralizedCartan, κ = P.weylDot hA.isGeneralizedCartan w μ) ∧
    μ ∈ cone P κ ∧ μ ≠ κ}

omit [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
theorem finite_dotOrbitAbove (μ : Dual K H) : (dotOrbitAbove P hA μ).Finite := by
  have := P.finite_weylGroup hA
  refine (Set.finite_range fun w : P.weylGroup hA.isGeneralizedCartan ↦
    P.weylDot hA.isGeneralizedCartan w μ).subset ?_
  rintro κ ⟨⟨w, rfl⟩, -⟩
  exact ⟨w, rfl⟩

omit [IsAlgClosed K] [FiniteDimensional K H] [Fact A.IsFiniteCartan] in
/-- Going up the dot orbit shrinks the set of weights above. -/
theorem ncard_dotOrbitAbove_lt {μ κ : Dual K H} (hκ : κ ∈ dotOrbitAbove P hA μ) :
    (dotOrbitAbove P hA κ).ncard < (dotOrbitAbove P hA μ).ncard := by
  obtain ⟨⟨x, hx⟩, hμκ, hne⟩ := hκ
  have hsub : dotOrbitAbove P hA κ ⊆ dotOrbitAbove P hA μ := by
    rintro ν ⟨⟨y, rfl⟩, hκν, hne'⟩
    refine ⟨⟨y * x, by rw [hx, weylDot_mul]⟩, mem_cone_trans hμκ hκν, fun h ↦ hne' ?_⟩
    subst h
    exact eq_of_mem_cone_of_mem_cone hκν hμκ
  exact Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).mpr
    ⟨κ, ⟨⟨x, hx⟩, hμκ, hne⟩, fun h ↦ h.2.2 rfl⟩) (finite_dotOrbitAbove hA μ)

/-- `Extⁿ(M(μ), -) = 0` once `n` exceeds the number of weights of `W·μ` strictly above `μ`. -/
theorem ext_verma_eq_zero_of_ncard_lt : ∀ (n : ℕ) (μ : Dual K H),
    (dotOrbitAbove P hA μ).ncard < n → ∀ (Y : CategoryO.{u} P)
      (x : Abelian.Ext.{u} (verma P μ) Y n), x = 0 := by
  intro n
  induction n with
  | zero => intro μ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
  intro μ hμ Y x
  refine ext_succ_verma_eq_zero Y μ n (fun κ hκ hne z ↦ ?_) x
  have hlink := VermaModule.isStronglyLinked_of_multiplicity_ne_zero P hA hκ
  rw [← weylDot_one P hA.isGeneralizedCartan μ] at hlink
  obtain ⟨w, hw⟩ := IsStronglyLinked.exists_weylDot_eq P hA.isGeneralizedCartan hlink
  have hmem : κ ∈ dotOrbitAbove P hA μ :=
    ⟨⟨w, hw⟩, VermaModule.mem_cone_of_multiplicity_ne_zero hκ, fun h ↦ hne h.symm⟩
  exact ih κ (by have := ncard_dotOrbitAbove_lt hA hmem; omega) Y z

/-- **Verma modules have finite projective dimension** in `𝒪`: `pd M(μ)` is at most the number
of weights of the dot orbit `W·μ` strictly above `μ`. Finite type, algebraically closed field of
characteristic zero. -/
theorem hasProjectiveDimensionLT_verma (μ : Dual K H) :
    HasProjectiveDimensionLT (verma.{u} P μ) ((dotOrbitAbove P hA μ).ncard + 1) :=
  HasProjectiveDimensionLT.mk fun i hi ⦃Y⦄ x ↦
    ext_verma_eq_zero_of_ncard_lt hA i μ (by omega) Y x

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
