/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.ExactFunctorO
import LieLean.Algebra.Lie.KacMoody.ProjectiveFunctorLift
import LieLean.Algebra.Lie.KacMoody.ProjectiveFunctorVerma
import LieLean.Algebra.Lie.UniversalEnveloping.TensorNatTrans

/-!
# Natural transformations of tensoring functors on a block (Humphreys, Theorem 10.7)

Let `λ` be dominant and `I` the annihilator of `M(λ)` in `U(𝔤)`. For `V`, `W` finite-dimensional:

* (a) every morphism `M(λ) ⊗ V → M(λ) ⊗ W` is the value at `M(λ)` of a natural transformation
  `− ⊗ V → − ⊗ W` defined on all modules (`exists_tensorNatTrans_app_verma`);
* (b) natural transformations `φ : e(− ⊗ V) → e'(− ⊗ W)`, `φ'` back, between summands cut out by
  natural idempotents, which are mutually inverse at `M(λ)`, are isomorphisms
  `e_M(M ⊗ V) ≅ e'_M(M ⊗ W)` at every finitely generated `M ∈ 𝒪` in the block of `λ`
  (`exists_inverse_of_block`).

Projective functors on `𝒪_λ` are such summands `e(− ⊗ V)`, so (a) and (b) are Humphreys'
Theorem 10.7: morphisms of projective functors are determined by, and lift, their values at
`M(λ)`, and a projective functor is determined by its value at `M(λ)`.

As in `bijective_tensorNatLinear_verma`, (a) assumes Kostant's multiplicity formula for
`(U(𝔤) / I)^{ad}`. For (b), every finitely generated module in the block is killed by a power of
`I` (`exists_isKilledByPow_of_block`): its composition factors `L(w·λ)` are subquotients of
`M(λ)`, and modules killed by a power of `I` form a Serre class (`isSerreClassO_isKilledByPow`).

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.1, §10.8, Thm. 10.7.
-/

noncomputable section

open Module UniversalEnvelopingAlgebra
open scoped TensorProduct

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝔤" => KacMoodyAlgebra P

omit [CharZero K] in
/-- Modules killed by a power of a two-sided ideal `I` of `U(𝔤)` form a Serre class. -/
theorem isSerreClassO_isKilledByPow (I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)) :
    IsSerreClassO P fun M _ _ _ _ ↦ ∃ n, IsKilledByPow I n M where
  of_subsingleton _ _ _ _ _ _ := ⟨0, fun _ _ _ ↦ LinearMap.ext fun _ ↦ Subsingleton.elim _ _⟩
  of_equiv {M N} _ _ _ _ _ _ _ _ e := by
    rintro ⟨n, hn⟩
    refine ⟨n, fun l hl hlI ↦ LinearMap.ext fun y ↦ ?_⟩
    rw [← e.apply_symm_apply y, LinearMap.zero_apply]
    change actionHom N l.prod ((e : M →ₗ⁅K,𝔤⁆ N) (e.symm y)) = 0
    rw [← LieModuleHom.map_actionHom, hn l hl hlI, LinearMap.zero_apply, map_zero]
  iff {M} _ _ _ _ _ N := by
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨⟨n, fun l hl hlI ↦ LinearMap.ext fun x ↦ Subtype.ext ?_⟩,
        ⟨n, fun l hl hlI ↦ LinearMap.ext fun q ↦ ?_⟩⟩
      · change N.incl (actionHom N l.prod x) = 0
        rw [LieModuleHom.map_actionHom, hn l hl hlI, LinearMap.zero_apply]
      · induction q using Submodule.Quotient.induction_on with
        | H m =>
          change actionHom _ l.prod (LieSubmodule.Quotient.mk' N m) = 0
          rw [← LieModuleHom.map_actionHom, hn l hl hlI, LinearMap.zero_apply, map_zero]
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨a + b, fun l hl hlI ↦ LinearMap.ext fun m ↦ ?_⟩
      have hm : actionHom M (l.drop a).prod m ∈ N := by
        rw [← LieSubmodule.Quotient.mk_eq_zero, LieModuleHom.map_actionHom,
          hb _ (by simp [hl]) fun x hx ↦ hlI x (List.mem_of_mem_drop hx),
          LinearMap.zero_apply]
      have h := congrArg Subtype.val
        (LinearMap.congr_fun (ha (l.take a) (by simp [hl]) fun x hx ↦ hlI x
          (List.mem_of_mem_take hx)) ⟨_, hm⟩)
      change N.incl (actionHom N (l.take a).prod ⟨_, hm⟩) = 0 at h
      rw [LieModuleHom.map_actionHom] at h
      rw [← List.take_append_drop a l, List.prod_append, map_mul, Module.End.mul_apply]
      exact h

variable [IsAlgClosed K] [FiniteDimensional K H] (hA : A.IsFiniteCartan)

include hA in
/-- Let `λ` be dominant and `I` a two-sided ideal killing `M(λ)`. Every finitely generated
`M ∈ 𝒪` in the block of `λ` (composition factors `L(w·λ)`, `w ∈ W_[λ]`) is killed by a power of
`I`. -/
theorem exists_isKilledByPow_of_block {lam : Dual K H}
    (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hI : IsKilledBy I (VermaModule P lam))
    {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    (hM : IsCategoryO P M) {s : Finset M}
    (hs : LieSubmodule.lieSpan K 𝔤 (s : Set M) = ⊤)
    (hblock : ∀ μ, hM.multiplicity μ ≠ 0 →
      ∃ w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam,
        μ = P.weylDot hA.isGeneralizedCartan w lam) :
    ∃ n, IsKilledByPow I n M :=
  (isSerreClassO_isKilledByPow P I).of_verma_of_isDominant hA hlam
    ⟨1, fun l hl hlI ↦ by
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
      rw [List.prod_singleton]
      exact hI a (hlI a (List.mem_singleton_self a))⟩ hM hs hblock

include hA in
/-- **Humphreys, Theorem 10.7 (a)**: let `λ` be dominant and `I` the annihilator of `M(λ)`, and
assume Kostant's multiplicity formula for `(U(𝔤) / I)^{ad}`. For `V`, `W` finite-dimensional,
every morphism `ψ : M(λ) ⊗ V → M(λ) ⊗ W` is the value at `M(λ)` of a natural transformation
`− ⊗ V → − ⊗ W` defined on all modules. In particular a morphism `e(M(λ) ⊗ V) → e'(M(λ) ⊗ W)`
between the values of projective functors `e(− ⊗ V)`, `e'(− ⊗ W)` is the value of the morphism
of functors `e' φ e`. -/
theorem exists_tensorNatTrans_app_verma {lam : Dual K H}
    (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (hK : KostantMultiplicity P (AdQuotient K 𝔤 I)) {V W : Type (max u₁ u₂)} [AddCommGroup V]
    [Module K V] [LieRingModule 𝔤 V] [LieModule K 𝔤 V] [FiniteDimensional K V] [AddCommGroup W]
    [Module K W] [LieRingModule 𝔤 W] [LieModule K 𝔤 W] [FiniteDimensional K W]
    (ψ : VermaModule P lam ⊗[K] V →ₗ⁅K,𝔤⁆ VermaModule P lam ⊗[K] W) :
    ∃ φ : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 V W, φ.app (VermaModule P lam) = ψ := by
  obtain ⟨g, hg⟩ := (bijective_tensorNatLinear_verma hA hlam hM hI hK V W).2 ψ
  obtain ⟨g', hg'⟩ := exists_tensorNatMap_eq P hA I g
  exact ⟨TensorNatTrans.ofTensorNatMap g', (hg' _ hM).trans hg⟩

include hA in
/-- **Humphreys, Theorem 10.7 (b)**: let `λ` be dominant and `I` the annihilator of `M(λ)`. Let
`e`, `e'` be natural transformations of `− ⊗ V`, `− ⊗ W`, idempotent at a finitely generated
`M ∈ 𝒪` in the block of `λ`, and `φ`, `φ'` natural transformations with `e' φ e = φ` and
`e φ' e' = φ'` at `M`, mutually inverse at `M(λ)` (`φ' φ = e`, `φ φ' = e'`). Then `φ_M` is an
isomorphism `e_M(M ⊗ V) ≅ e'_M(M ⊗ W)`. So a projective functor on the block of `λ` is
determined by its value at `M(λ)`. -/
theorem exists_inverse_of_block {lam : Dual K H} (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule 𝔤 V] [LieModule K 𝔤 V]
    [AddCommGroup W] [Module K W] [LieRingModule 𝔤 W] [LieModule K 𝔤 W]
    (e : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 V V)
    (e' : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 W W)
    (φ : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 V W)
    (φ' : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 W V)
    (h₁ : (φ'.app (VermaModule P lam)).comp (φ.app (VermaModule P lam)) = e.app _)
    (h₂ : (φ.app (VermaModule P lam)).comp (φ'.app (VermaModule P lam)) = e'.app _)
    {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    (hM : IsCategoryO P M) {s : Finset M} (hs : LieSubmodule.lieSpan K 𝔤 (s : Set M) = ⊤)
    (hblock : ∀ μ, hM.multiplicity μ ≠ 0 →
      ∃ w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam,
        μ = P.weylDot hA.isGeneralizedCartan w lam)
    (he : ∀ x, e.app M (e.app M x) = e.app M x) (he' : ∀ y, e'.app M (e'.app M y) = e'.app M y)
    (hφ : ∀ x, e'.app M (φ.app M (e.app M x)) = φ.app M x)
    (hφ' : ∀ y, e.app M (φ'.app M (e'.app M y)) = φ'.app M y) :
    ∃ ψ : M ⊗[K] W →ₗ[K] M ⊗[K] V, ψ ∘ₗ (φ.app M : M ⊗[K] V →ₗ[K] M ⊗[K] W) = e.app M ∧
      (φ.app M : M ⊗[K] V →ₗ[K] M ⊗[K] W) ∘ₗ ψ = e'.app M := by
  obtain ⟨n, hn⟩ := exists_isKilledByPow_of_block P hA hlam hM₀ hM hs hblock
  exact TensorNatTrans.exists_inverse_of_hasKilledFiltration e e' φ φ' hM₀ hI h₁ h₂
    (hasKilledFiltration_of_isKilledByPow hn) he he' hφ hφ'

end Matrix.Realization.KacMoodyAlgebra
