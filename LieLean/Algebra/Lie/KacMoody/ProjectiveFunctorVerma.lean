/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.DominantVermaTensorHom
import LieLean.Algebra.Lie.KacMoody.FiniteDimensional
import LieLean.Algebra.Lie.UniversalEnveloping.TensorNaturalEval

/-!
# Natural transformations of projective functors and dominant Verma modules

Let `λ` be dominant, `I` a two-sided ideal of `U(𝔤)` with annihilator `Ann M(λ) = I`, and
`A = U(𝔤) / I`. Assume Kostant's multiplicity formula for `A^{ad}`: for every dominant integral
`ν`, `Hom_𝔤(L(ν), A^{ad})` is finite-dimensional of dimension `dim L(ν)_0`. Then for
finite-dimensional `V`, `W` the evaluation of natural transformations at `M(λ)`,
`Hom_𝔤(V, A^{ad} ⊗ W) → Hom_𝔤(M(λ) ⊗ V, M(λ) ⊗ W)`, `g ↦ tensorNatMap g`, is bijective
(`bijective_tensorNatLinear_verma`).

This is the core of the proof of Theorem 10.7 in Humphreys (Bernstein–Gelfand). There, `I` is
identified with `U(𝔤) ker χ_λ` by Duflo's theorem, and Kostant's theorem gives the multiplicity
of `L(ν)` in `(U(𝔤) / U(𝔤) ker χ_λ)^{ad}`. Both theorems enter here as hypotheses (maintainer
decision, 2026-10-22).

## Main definitions

* `LieSubmodule.projOfIsCompl`: the projection onto a Lie submodule along a complementary one.
* `LieModule.weightSpaceOfMapCongr`: weight spaces of isomorphic modules.

## Main results

* `LieSubmodule.homEquivProdOfIsCompl`, `LieSubmodule.weightSpaceOfMapEquivProdOfIsCompl`:
  Hom spaces out of, and weight spaces of, `N ⊕ N'`.
* `Matrix.Realization.KacMoodyAlgebra.finrank_hom_of_kostant`: Kostant's formula for simple
  modules extends to `dim Hom_𝔤(Y, X) = dim Y_0` for all finite-dimensional `Y`.
* `Matrix.Realization.KacMoodyAlgebra.bijective_tensorNatLinear_verma`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8, proof of Thm. 10.7.
-/

noncomputable section

open Module LieModule TensorProduct

namespace LieSubmodule

variable {R L M X : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup X] [Module R X] [LieRingModule L X] [LieModule R L X]
  {N N' : LieSubmodule R L M}

/-- The projection onto `N` along a complementary Lie submodule `N'`, a morphism of Lie
modules. -/
def projOfIsCompl (h : IsCompl N N') : M →ₗ⁅R,L⁆ N :=
  { Submodule.projectionOnto N.toSubmodule N'.toSubmodule (isCompl_toSubmodule.mpr h) with
    map_lie' := fun {x m} ↦ by
      have h' := isCompl_toSubmodule.mpr h
      have hm := Submodule.projection_add_projection_eq_self h' m
      apply Subtype.ext
      change (Submodule.projectionOnto _ _ h' ⁅x, m⁆ : M) =
        ⁅x, (Submodule.projectionOnto _ _ h' m : M)⁆
      conv_lhs => rw [← hm]
      rw [lie_add, map_add,
        Submodule.projectionOnto_apply_of_mem_left h' (N.lie_mem (Submodule.projection_apply_mem
          h' m)),
        Submodule.projectionOnto_apply_of_mem_right h' (N'.lie_mem (Submodule.projection_apply_mem
          h'.symm m)), add_zero]
      rfl }

omit [LieAlgebra R L] [LieModule R L M] in
theorem projOfIsCompl_apply_coe (h : IsCompl N N') (m : M) :
    (projOfIsCompl h m : M) =
      N.toSubmodule.projection N'.toSubmodule (isCompl_toSubmodule.mpr h) m := rfl

omit [LieAlgebra R L] [LieModule R L M] in
@[simp] theorem projOfIsCompl_apply_left (h : IsCompl N N') (n : N) :
    projOfIsCompl h n = n :=
  Submodule.projectionOnto_apply_left _ n

omit [LieAlgebra R L] [LieModule R L M] in
@[simp] theorem projOfIsCompl_apply_right (h : IsCompl N N') (n : N') :
    projOfIsCompl h n = 0 :=
  Submodule.projectionOnto_apply_right _ n

omit [LieAlgebra R L] [LieModule R L M] in
theorem projOfIsCompl_add (h : IsCompl N N') (m : M) :
    (projOfIsCompl h m : M) + (projOfIsCompl h.symm m : M) = m :=
  Submodule.projection_add_projection_eq_self _ m

/-- Morphisms out of `M = N ⊕ N'` are pairs of morphisms out of `N` and `N'`. -/
def homEquivProdOfIsCompl (h : IsCompl N N') :
    (M →ₗ⁅R,L⁆ X) ≃ₗ[R] (N →ₗ⁅R,L⁆ X) × (N' →ₗ⁅R,L⁆ X) where
  toFun f := (f.comp N.incl, f.comp N'.incl)
  invFun g := g.1.comp (projOfIsCompl h) + g.2.comp (projOfIsCompl h.symm)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    ext m
    simp only [add_apply, LieModuleHom.coe_comp, Function.comp_apply,
      incl_apply, ← map_add, projOfIsCompl_add]
  right_inv g := by
    ext n
    · simp
    · simp

end LieSubmodule

namespace LieModule

variable {K H L M M' : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L]
  [LieAlgebra K L] [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup M'] [Module K M'] [LieRingModule L M'] [LieModule K L M']
  (φ : H →ₗ[K] L)

/-- Isomorphic modules have isomorphic weight spaces. -/
def weightSpaceOfMapCongr (e : M ≃ₗ⁅K,L⁆ M') (μ : Dual K H) :
    weightSpaceOfMap M φ μ ≃ₗ[K] weightSpaceOfMap M' φ μ where
  toFun v := ⟨e v, fun a ↦ by
    have h1 : ⁅φ a, e (v : M)⁆ = e ⁅φ a, (v : M)⁆ :=
      (LieModuleHom.map_lie (e : M →ₗ⁅K,L⁆ M') _ _).symm
    rw [h1, v.2 a, map_smul]⟩
  invFun w := ⟨e.symm w, fun a ↦ by
    have h1 : ⁅φ a, e.symm (w : M')⁆ = e.symm ⁅φ a, (w : M')⁆ :=
      (LieModuleHom.map_lie (e.symm : M' →ₗ⁅K,L⁆ M) _ _).symm
    rw [h1, w.2 a, map_smul]⟩
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp
  left_inv v := by ext; simp
  right_inv w := by ext; simp

variable {N N' : LieSubmodule K L M}

/-- The weight spaces of `M = N ⊕ N'` are the products of those of `N` and `N'`. -/
def weightSpaceOfMapEquivProdOfIsCompl (h : IsCompl N N') (μ : Dual K H) :
    weightSpaceOfMap M φ μ ≃ₗ[K] weightSpaceOfMap N φ μ × weightSpaceOfMap N' φ μ where
  toFun v := (⟨LieSubmodule.projOfIsCompl h v, fun a ↦ by
      rw [← LieModuleHom.map_lie, v.2 a, map_smul]⟩,
    ⟨LieSubmodule.projOfIsCompl h.symm v, fun a ↦ by
      rw [← LieModuleHom.map_lie, v.2 a, map_smul]⟩)
  invFun w := ⟨(w.1 : N) + (w.2 : N'), fun a ↦ by
    rw [lie_add, smul_add, ← LieSubmodule.coe_bracket, ← LieSubmodule.coe_bracket, w.1.2 a,
      w.2.2 a, LieSubmodule.coe_smul, LieSubmodule.coe_smul]⟩
  map_add' v w := by ext <;> simp
  map_smul' c v := by ext <;> simp
  left_inv v := by
    ext
    exact LieSubmodule.projOfIsCompl_add h v
  right_inv w := by
    ext
    · simp [map_add, LieSubmodule.projOfIsCompl_apply_left,
        LieSubmodule.projOfIsCompl_apply_right h]
    · simp [map_add, LieSubmodule.projOfIsCompl_apply_left,
        LieSubmodule.projOfIsCompl_apply_right h.symm]

end LieModule

namespace Matrix.Realization.KacMoodyAlgebra

open UniversalEnvelopingAlgebra VermaModule

universe u

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

/-- **Kostant's multiplicity formula** for a `𝔤`-module `X`: for every dominant integral `ν`,
`Hom_𝔤(L(ν), X)` is finite-dimensional of dimension `dim L(ν)_0`. Kostant's theorem asserts this
for `X = (U(𝔤) / U(𝔤) ker χ)^{ad}` and every central character `χ` (Humphreys, GSM 94, §10.8). -/
def KostantMultiplicity (X : Type*) [AddCommGroup X] [Module K X] [LieRingModule 𝔤 X]
    [LieModule K 𝔤 X] : Prop :=
  ∀ ν : Dual K H, P.IsDominantIntegral ν →
    FiniteDimensional K (IrreducibleModule P ν →ₗ⁅K,𝔤⁆ X) ∧
      finrank K (IrreducibleModule P ν →ₗ⁅K,𝔤⁆ X) =
        finrank K (weightSpaceOfMap (IrreducibleModule P ν) (h P) 0)

omit [IsAlgClosed K] in
include hA in
/-- Kostant's multiplicity formula for simple modules extends, by Weyl's complete reducibility,
to `dim Hom_𝔤(Y, X) = dim Y_0` for every finite-dimensional `Y`. -/
theorem finrank_hom_of_kostant {X : Type*} [AddCommGroup X] [Module K X] [LieRingModule 𝔤 X]
    [LieModule K 𝔤 X] (hX : KostantMultiplicity P X) (n : ℕ) :
    ∀ (Y : Type u) [AddCommGroup Y] [Module K Y] [LieRingModule 𝔤 Y] [LieModule K 𝔤 Y]
      [FiniteDimensional K Y], finrank K Y = n →
      FiniteDimensional K (Y →ₗ⁅K,𝔤⁆ X) ∧
        finrank K (Y →ₗ⁅K,𝔤⁆ X) = finrank K (weightSpaceOfMap Y (h P) 0) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y _ _ _ _ _ hn
  rcases subsingleton_or_nontrivial Y with hY | hY
  · have : Subsingleton (Y →ₗ⁅K,𝔤⁆ X) :=
      ⟨fun f g ↦ LieModuleHom.ext fun y ↦ by rw [Subsingleton.elim y 0, map_zero, map_zero]⟩
    have : Subsingleton (weightSpaceOfMap Y (h P) 0) := inferInstance
    exact ⟨inferInstance, by rw [finrank_zero_of_subsingleton, finrank_zero_of_subsingleton]⟩
  have : ComplementedLattice (LieSubmodule K 𝔤 Y) :=
    complementedLattice_of_finiteDimensional (V := Y) hA
  obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : LieSubmodule K 𝔤 Y)).resolve_left
    (by simp)
  obtain ⟨N', hNN'⟩ := exists_isCompl N
  obtain ⟨ν, hν, ⟨e⟩⟩ := IsCategoryO.exists_equiv_irreducibleModule_of_isAtom
    hA.isGeneralizedCartan (isCategoryO_of_finiteDimensional hA)
    (isIntegrable_of_finiteDimensional hA) hN
  have hlt : finrank K N' < n := by
    have hadd := Submodule.finrank_add_eq_of_isCompl
      (LieSubmodule.isCompl_toSubmodule.mpr hNN')
    have hpos : 0 < finrank K N := by
      have : Nontrivial N := (LieSubmodule.nontrivial_iff_ne_bot K _ Y).mpr hN.1
      exact finrank_pos
    change finrank K N.toSubmodule + finrank K N'.toSubmodule = finrank K Y at hadd
    change finrank K N'.toSubmodule < n
    change 0 < finrank K N.toSubmodule at hpos
    omega
  obtain ⟨hfin', hrk'⟩ := ih _ hlt N' rfl
  obtain ⟨hfin, hrk⟩ := hX ν hν
  have e₁ := LieSubmodule.homEquivProdOfIsCompl (X := X) hNN'
  have e₂ := lieModuleHomCongr P e (LieModuleEquiv.refl (M := X))
  have e₃ := LieModule.weightSpaceOfMapEquivProdOfIsCompl (h P) hNN' 0
  have e₄ := LieModule.weightSpaceOfMapCongr (h P) e 0
  have : FiniteDimensional K (N →ₗ⁅K,𝔤⁆ X) := LinearEquiv.finiteDimensional e₂.symm
  refine ⟨LinearEquiv.finiteDimensional e₁.symm, ?_⟩
  rw [e₁.finrank_eq, e₃.finrank_eq, finrank_prod, finrank_prod, e₂.finrank_eq, e₄.finrank_eq,
    hrk, hrk']

variable {P}

include hA in
/-- **Humphreys, proof of Theorem 10.7**: let `λ` be dominant and `I` the annihilator of `M(λ)`
in `U(𝔤)`, and assume Kostant's multiplicity formula for `(U(𝔤) / I)^{ad}`. For
finite-dimensional `V`, `W`, a morphism `g : V → (U(𝔤) / I)^{ad} ⊗ W` is determined by the
map `M(λ) ⊗ V → M(λ) ⊗ W` it induces, and every morphism `M(λ) ⊗ V → M(λ) ⊗ W` arises this
way. In Humphreys, `I = U(𝔤) ker χ_λ` (Duflo's theorem) and the Kostant formula is Kostant's
theorem; both are hypotheses here. -/
theorem bijective_tensorNatLinear_verma {Λ : Dual K H} (hΛ : P.IsDominant hA.isGeneralizedCartan Λ)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM : IsKilledBy I (VermaModule P Λ))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P Λ) a = 0 → a ∈ I)
    (hK : KostantMultiplicity P (AdQuotient K 𝔤 I)) (V W : Type u) [AddCommGroup V] [Module K V]
    [LieRingModule 𝔤 V] [LieModule K 𝔤 V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    [LieRingModule 𝔤 W] [LieModule K 𝔤 W] [FiniteDimensional K W] :
    Function.Bijective (tensorNatLinear (V := V) (W := W) hM) := by
  have e : (V →ₗ⁅K,𝔤⁆ AdQuotient K 𝔤 I ⊗[K] W) ≃ₗ[K]
      (V ⊗[K] Module.Dual K W →ₗ⁅K,𝔤⁆ AdQuotient K 𝔤 I) :=
    (lieModuleHomCongr P (LieModuleEquiv.refl (M := V))
      (LieModuleEquiv.tensorCongr (LieModuleEquiv.refl (M := AdQuotient K 𝔤 I))
        (evalEquiv (L := 𝔤) (M := W)))).trans
      (tensorHomAdjunction P (M := V) (N := AdQuotient K 𝔤 I) (L := Module.Dual K W)).symm
  obtain ⟨hfin, hrk⟩ := finrank_hom_of_kostant P hA hK _ (V ⊗[K] Module.Dual K W) rfl
  have : FiniteDimensional K (V →ₗ⁅K,𝔤⁆ AdQuotient K 𝔤 I ⊗[K] W) :=
    LinearEquiv.finiteDimensional e.symm
  have hrkM := finrank_hom_tensor_verma_tensor_self_of_isDominant P hA hΛ (L := V) (L' := W)
  have : FiniteDimensional K (VermaModule P Λ ⊗[K] V →ₗ⁅K,𝔤⁆ VermaModule P Λ ⊗[K] W) := by
    obtain ⟨S, hS⟩ := exists_finset_lieSpan_tmul_eq_top (W := V)
      (VermaModule.lieSpan_map_hwv_eq_top (P := P) (Λ := Λ) LieModuleHom.id
        Function.surjective_id)
    exact ((VermaModule.isCategoryO P Λ).tensorProduct (isCategoryO_of_finiteDimensional hA)
      ).finiteDimensional_hom P hS
        ((VermaModule.isCategoryO P Λ).tensorProduct (isCategoryO_of_finiteDimensional hA))
  exact tensorNatLinear_bijective hM hI (by rw [e.finrank_eq, hrk, hrkM])

end Matrix.Realization.KacMoodyAlgebra
