/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.ProjectiveFunctorIso
import LieLean.Algebra.Lie.KacMoody.VermaHomFiniteType
import LieLean.RingTheory.Idempotents

/-!
# Projective functors on a block

Let `λ` be dominant. A *projective functor on the block of `λ`* is a direct summand `e(− ⊗ V)` of
a tensoring functor (`V` finite-dimensional) on the finitely generated modules `M ∈ 𝒪` whose
composition factors are the `L(w·λ)`, `w ∈ W_[λ]` (`IsInBlock`). It is given by a family of
endomorphisms `e_M` of `M ⊗ V` that are idempotent on the block and, on any two modules of the
block, are the components of one natural transformation `− ⊗ V → − ⊗ V`
(`BlockProjectiveFunctor`). The idempotents cutting out translation functors are components of
natural transformations in this sense (`exists_tensorNatTrans_app_eq_translationIdem`). These are
the functors of Bernstein–Gelfand's classification, restricted to one block.

The value at `M(λ)` controls such a functor: if it vanishes at `M(λ)` it vanishes on the block
(`BlockProjectiveFunctor.idem_eq_zero_of_idem_verma_eq_zero`), and, assuming Kostant's
multiplicity formula for `(U(𝔤) / I)^{ad}` (`I` the annihilator of `M(λ)`), every idempotent of
`e(M(λ) ⊗ V)` is the value at `M(λ)` of a summand of `e(− ⊗ V)`
(`BlockProjectiveFunctor.exists_isSummand_idem_verma`). The summand is obtained by lifting the
idempotent `e φ e` of a natural transformation `φ` with value the given idempotent: `e φ e` is
idempotent up to a nilpotent at every module of the block, and the canonical lift
`idempotentLift` is natural. This is the step of Bernstein–Gelfand's proof of their Theorem 3.3
that reduces the decomposition of projective functors to the decomposition of their values at
`M(λ)`.

## Main definitions

* `UniversalEnvelopingAlgebra.TensorNatTrans.id`, `zero`, `sub`, `idempotentLiftPow`.
* `Matrix.Realization.KacMoodyAlgebra.IsInBlock`: the finitely generated modules of the block.
* `Matrix.Realization.KacMoodyAlgebra.BlockProjectiveFunctor`: projective functors on the
  block; `BlockProjectiveFunctor.IsSummand`, `BlockProjectiveFunctor.tensor` (`− ⊗ V` itself)
  and `BlockProjectiveFunctor.sub` (the complementary summand).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.isInBlock_verma`: `M(λ)` lies in the block of `λ`.
* `BlockProjectiveFunctor.naturality`: the idempotents are natural on the block.
* `BlockProjectiveFunctor.idem_eq_zero_of_idem_verma_eq_zero`.
* `BlockProjectiveFunctor.exists_isSummand_idem_verma`: idempotents at `M(λ)` lift to summands.

## References

* J. N. Bernstein, S. I. Gelfand, *Tensor products of finite and infinite dimensional
  representations of semisimple Lie algebras*, Compositio Math. **41** (1980), 245–285, proof of
  Thm. 3.3.
* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8.
-/

noncomputable section

open Module UniversalEnvelopingAlgebra
open scoped TensorProduct

namespace LieModuleHom

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

/-- Forgetting the Lie structure is a ring homomorphism from the endomorphisms of a Lie module to
its linear endomorphisms. -/
def toEndRingHom : (M →ₗ⁅R,L⁆ M) →+* Module.End R M where
  toFun f := f
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [LieAlgebra R L] [LieModule R L M] in
@[simp] lemma toEndRingHom_apply (f : M →ₗ⁅R,L⁆ M) : toEndRingHom f = (f : M →ₗ[R] M) := rfl

omit [LieAlgebra R L] [LieModule R L M] in
lemma toEndRingHom_injective : Function.Injective (toEndRingHom (R := R) (L := L) (M := M)) :=
  fun _ _ h ↦ LieModuleHom.ext fun m ↦ LinearMap.congr_fun h m

omit [LieAlgebra R L] [LieModule R L M] in
lemma coe_idempotentLiftPow (n : ℕ) (f : M →ₗ⁅R,L⁆ M) :
    ((idempotentLiftPow n f : M →ₗ⁅R,L⁆ M) : M →ₗ[R] M) = idempotentLiftPow n (f : M →ₗ[R] M) :=
  map_idempotentLiftPow toEndRingHom n f

end LieModuleHom

namespace UniversalEnvelopingAlgebra.TensorNatTrans

universe u v w

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]

variable (K L V) in
/-- The identity natural transformation of `− ⊗ V`. -/
def id : TensorNatTrans.{u, v, w} K L V V where
  app _ _ _ _ _ := 1
  naturality _ _ _ _ _ _ _ _ _ _ _ _ := rfl

@[simp] theorem id_app (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] : (id K L V).app M = 1 := rfl

variable (K L V W) in
/-- The zero natural transformation `− ⊗ V → − ⊗ W`. -/
def zero : TensorNatTrans.{u, v, w} K L V W where
  app _ _ _ _ _ := 0
  naturality _ _ _ _ _ _ _ _ _ _ _ _ := by simp

@[simp] theorem zero_app (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M]
    [LieModule K L M] : (zero K L V W).app M = 0 := rfl

/-- The difference of two natural transformations. -/
def sub (φ ψ : TensorNatTrans.{u, v, w} K L V W) : TensorNatTrans.{u, v, w} K L V W where
  app M _ _ _ _ := φ.app M - ψ.app M
  naturality M N _ _ _ _ _ _ _ _ f t := by
    simp only [sub_apply, map_sub, φ.naturality, ψ.naturality]

@[simp] theorem sub_app (φ ψ : TensorNatTrans.{u, v, w} K L V W) (M : Type w) [AddCommGroup M]
    [Module K M] [LieRingModule L M] [LieModule K L M] :
    (φ.sub ψ).app M = φ.app M - ψ.app M := rfl

/-- The natural transformation `1 - (1 - φ ^ n) ^ n`; it is natural since every polynomial in
`φ` is. -/
def idempotentLiftPow (n : ℕ) (φ : TensorNatTrans.{u, v, w} K L V V) :
    TensorNatTrans.{u, v, w} K L V V where
  app M _ _ _ _ := _root_.idempotentLiftPow n (φ.app M)
  naturality M N _ _ _ _ _ _ _ _ f t := by
    have h := LinearMap.congr_fun (LinearMap.comp_idempotentLiftPow
      (f := (f : M →ₗ[K] N).rTensor V) (u := (φ.app M : M ⊗[K] V →ₗ[K] M ⊗[K] V))
      (v := (φ.app N : N ⊗[K] V →ₗ[K] N ⊗[K] V)) (LinearMap.ext (φ.naturality M N f)) n) t
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LieModuleHom.coe_idempotentLiftPow,
      ← LieModuleHom.coe_idempotentLiftPow] at h
    exact h

@[simp] theorem idempotentLiftPow_app (n : ℕ) (φ : TensorNatTrans.{u, v, w} K L V V)
    (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] :
    (φ.idempotentLiftPow n).app M = _root_.idempotentLiftPow n (φ.app M) := rfl

end UniversalEnvelopingAlgebra.TensorNatTrans

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ}

section

variable [IsAlgClosed K] [FiniteDimensional K H] (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

/-- `M` lies in the block of `λ`: it is a finitely generated module in `𝒪` whose composition
factors are the `L(w·λ)` with `w ∈ W_[λ]`. -/
structure IsInBlock (lam : Dual K H) (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M]
    [LieRingModule 𝔤 M] [LieModule K 𝔤 M] : Prop where
  isCategoryO : IsCategoryO P M
  exists_finset : ∃ s : Finset M, LieSubmodule.lieSpan K 𝔤 (s : Set M) = ⊤
  multiplicity_ne_zero : ∀ μ, isCategoryO.multiplicity μ ≠ 0 →
    ∃ w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam,
      μ = P.weylDot hA.isGeneralizedCartan w lam

/-- `M(λ)` lies in the block of `λ`: its composition factors `L(μ)` have `μ = w·λ` with
`λ - μ` in the root lattice. -/
theorem isInBlock_verma (lam : Dual K H) : IsInBlock P hA lam (VermaModule P lam) where
  isCategoryO := VermaModule.isCategoryO P lam
  exists_finset := ⟨{VermaModule.hwv P lam}, by
    rw [Finset.coe_singleton]
    exact VermaModule.lieSpan_map_hwv_eq_top LieModuleHom.id Function.surjective_id⟩
  multiplicity_ne_zero μ hμ := by
    obtain ⟨d, hdpos, hposDef⟩ := hA.exists_posDef
    have hsymm : (diagonal d * A).IsSymm := by
      simpa [IsHermitian, IsSymm] using hposDef.isHermitian
    obtain ⟨w, hw⟩ := VermaModule.exists_weylDot_of_multiplicity_ne_zero P hA
      (Symmetrization.ofDiagonal d hdpos hsymm) hμ
    obtain ⟨k, -, hk⟩ := VermaModule.mem_cone_of_multiplicity_ne_zero hμ
    refine ⟨w, ?_, hw⟩
    rw [mem_integralWeylGroup_iff_dot]
    have h : P.weylDot hA.isGeneralizedCartan w lam - lam = -P.rootOf k := by
      rw [← hw, hk]
      abel
    change P.weylDot hA.isGeneralizedCartan w lam - lam ∈ P.rootLattice
    rw [h]
    exact neg_mem (P.rootOf_mem_rootLattice k)

variable (lam : Dual K H) in
/-- A projective functor `e(− ⊗ V)` on the block of `λ`: endomorphisms `e_M` of `M ⊗ V`,
idempotent at every module of the block, such that for any two modules `M`, `N` of the block
`e_M` and `e_N` are the components of one natural transformation `− ⊗ V → − ⊗ V`. The functor
sends `M` to the image of `e_M`; naturality on the block follows (`naturality`). -/
structure BlockProjectiveFunctor (V : Type (max u₁ u₂)) [AddCommGroup V] [Module K V]
    [LieRingModule 𝔤 V] [LieModule K 𝔤 V] where
  /-- The idempotent of `M ⊗ V`. -/
  idem : ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M], M ⊗[K] V →ₗ⁅K,𝔤⁆ M ⊗[K] V
  idem_idem : ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M], IsInBlock P hA lam M → ∀ x, idem M (idem M x) = idem M x
  exists_tensorNatTrans : ∀ (M N : Type (max u₁ u₂)) [AddCommGroup M] [Module K M]
    [LieRingModule 𝔤 M] [LieModule K 𝔤 M] [AddCommGroup N] [Module K N] [LieRingModule 𝔤 N]
    [LieModule K 𝔤 N], IsInBlock P hA lam M → IsInBlock P hA lam N →
    ∃ t : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 V V, t.app M = idem M ∧ t.app N = idem N

end

namespace BlockProjectiveFunctor

variable {P : Realization A K H} {hA : A.IsFiniteCartan}

local notation "𝔤" => KacMoodyAlgebra P

variable {lam : Dual K H} {V : Type (max u₁ u₂)} [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
  (F : BlockProjectiveFunctor P hA lam V)

theorem idem_mul_idem {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M] (hM : IsInBlock P hA lam M) : F.idem M * F.idem M = F.idem M :=
  LieModuleHom.ext (F.idem_idem M hM)

/-- The idempotents of a projective functor are natural on the block. -/
theorem naturality {M N : Type (max u₁ u₂)} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M] [AddCommGroup N] [Module K N] [LieRingModule 𝔤 N] [LieModule K 𝔤 N]
    (hM : IsInBlock P hA lam M) (hN : IsInBlock P hA lam N) (f : M →ₗ⁅K,𝔤⁆ N)
    (x : M ⊗[K] V) :
    (f : M →ₗ[K] N).rTensor V (F.idem M x) = F.idem N ((f : M →ₗ[K] N).rTensor V x) := by
  obtain ⟨t, htM, htN⟩ := F.exists_tensorNatTrans M N hM hN
  rw [← htM, ← htN]
  exact t.naturality M N f x

/-- `F` is a summand of `G`: `e_G e_F = e_F = e_F e_G` on the block. -/
def IsSummand (G : BlockProjectiveFunctor P hA lam V) : Prop :=
  ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M],
    IsInBlock P hA lam M → G.idem M * F.idem M = F.idem M ∧ F.idem M * G.idem M = F.idem M

variable (P hA lam V) in
/-- The functor `− ⊗ V` itself, with `e = 1`. -/
def tensor : BlockProjectiveFunctor P hA lam V where
  idem _ _ _ _ _ := 1
  idem_idem _ _ _ _ _ _ _ := rfl
  exists_tensorNatTrans _ _ _ _ _ _ _ _ _ _ _ _ := ⟨TensorNatTrans.id K 𝔤 V, rfl, rfl⟩

@[simp] theorem tensor_idem (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M]
    [LieRingModule 𝔤 M] [LieModule K 𝔤 M] : (tensor P hA lam V).idem M = 1 := rfl

theorem isSummand_tensor : F.IsSummand (tensor P hA lam V) :=
  fun _ _ _ _ _ _ ↦ ⟨one_mul _, mul_one _⟩

/-- The complement `e - e₁` of a summand `e₁` of `e`. -/
def sub (F₁ : BlockProjectiveFunctor P hA lam V) (h : F₁.IsSummand F) :
    BlockProjectiveFunctor P hA lam V where
  idem M _ _ _ _ := F.idem M - F₁.idem M
  idem_idem M _ _ _ _ hM x := by
    obtain ⟨h₁, h₂⟩ := h M hM
    have : (F.idem M - F₁.idem M) * (F.idem M - F₁.idem M) = F.idem M - F₁.idem M := by
      rw [sub_mul, mul_sub, mul_sub, F.idem_mul_idem hM, h₁, h₂, F₁.idem_mul_idem hM]
      abel
    exact DFunLike.congr_fun this x
  exists_tensorNatTrans M N _ _ _ _ _ _ _ _ hM hN := by
    obtain ⟨t, htM, htN⟩ := F.exists_tensorNatTrans M N hM hN
    obtain ⟨t₁, ht₁M, ht₁N⟩ := F₁.exists_tensorNatTrans M N hM hN
    exact ⟨t.sub t₁, by rw [TensorNatTrans.sub_app, htM, ht₁M],
      by rw [TensorNatTrans.sub_app, htN, ht₁N]⟩

@[simp] theorem sub_idem (F₁ : BlockProjectiveFunctor P hA lam V) (h : F₁.IsSummand F)
    (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M] : (F.sub F₁ h).idem M = F.idem M - F₁.idem M := rfl

theorem sub_isSummand (F₁ : BlockProjectiveFunctor P hA lam V) (h : F₁.IsSummand F) :
    (F.sub F₁ h).IsSummand F := fun M _ _ _ _ hM ↦ by
  obtain ⟨h₁, h₂⟩ := h M hM
  refine ⟨?_, ?_⟩
  · rw [sub_idem, mul_sub, F.idem_mul_idem hM, h₁]
  · rw [sub_idem, sub_mul, F.idem_mul_idem hM, h₂]

variable [IsAlgClosed K] [FiniteDimensional K H]

include hA in
/-- **A projective functor vanishing at `M(λ)` vanishes on the block** (Bernstein–Gelfand, proof
of Thm. 3.3; Humphreys, §10.8): let `λ` be dominant and `I` the annihilator of `M(λ)`. If
`e_{M(λ)} = 0`, then `e_M = 0` at every module `M` of the block. -/
theorem idem_eq_zero_of_idem_verma_eq_zero (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (h : F.idem (VermaModule P lam) = 0) {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M]
    [LieRingModule 𝔤 M] [LieModule K 𝔤 M] (hM : IsInBlock P hA lam M) : F.idem M = 0 := by
  obtain ⟨t, htM, htV⟩ := F.exists_tensorNatTrans M (VermaModule P lam) hM
    (isInBlock_verma P hA lam)
  obtain ⟨s, hs⟩ := hM.exists_finset
  obtain ⟨ψ, hψ, -⟩ := exists_inverse_of_block P hA hlam hM₀ hI t
    (TensorNatTrans.zero K 𝔤 V V) (TensorNatTrans.zero K 𝔤 V V) (TensorNatTrans.zero K 𝔤 V V)
    (by rw [htV, h]; exact LieModuleHom.ext fun _ ↦ rfl) (LieModuleHom.ext fun _ ↦ rfl)
    hM.isCategoryO hs hM.multiplicity_ne_zero (fun x ↦ by rw [htM]; exact F.idem_idem M hM x)
    (fun _ ↦ by simp) (fun _ ↦ by simp) (fun _ ↦ by simp)
  refine LieModuleHom.ext fun x ↦ ?_
  calc F.idem M x = t.app M x := by rw [htM]
    _ = ψ ((TensorNatTrans.zero K 𝔤 V V).app M x) := (LinearMap.congr_fun hψ x).symm
    _ = 0 := map_zero ψ

include hA in
/-- At every module `M` of the block, `e_M φ_M e_M` is idempotent up to a nilpotent, if `φ` is a
natural transformation with `e φ e` idempotent at `M(λ)` (`I` the annihilator of `M(λ)`). -/
theorem isNilpotent_idem_mul_mul_idem (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (φ : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 V V)
    (hφ : IsIdempotentElem (F.idem (VermaModule P lam) * φ.app _ * F.idem (VermaModule P lam)))
    {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    (hM : IsInBlock P hA lam M) :
    IsNilpotent (F.idem M * φ.app M * F.idem M - (F.idem M * φ.app M * F.idem M) ^ 2) := by
  obtain ⟨t, htM, htV⟩ := F.exists_tensorNatTrans M (VermaModule P lam) hM
    (isInBlock_verma P hA lam)
  obtain ⟨s, hs⟩ := hM.exists_finset
  obtain ⟨n, hn⟩ := exists_isKilledByPow_of_block P hA hlam hM₀ hM.isCategoryO hs
    hM.multiplicity_ne_zero
  set b := (t.comp φ).comp t with hb
  have hbM : b.app M = F.idem M * φ.app M * F.idem M := by
    rw [hb, TensorNatTrans.comp_app, TensorNatTrans.comp_app, htM]
    rfl
  have hbV : (b.app (VermaModule P lam)).comp (b.app _) = b.app (VermaModule P lam) := by
    have hbV' : b.app (VermaModule P lam) =
        F.idem (VermaModule P lam) * φ.app _ * F.idem (VermaModule P lam) := by
      rw [hb, TensorNatTrans.comp_app, TensorNatTrans.comp_app, htV]
      rfl
    rw [hbV']
    exact hφ.eq
  have h := TensorNatTrans.isNilpotent_comp_sub b b b hM₀ hI hbV
    (hasKilledFiltration_of_isKilledByPow hn)
  rw [← IsNilpotent.map_iff LieModuleHom.toEndRingHom_injective]
  have he : LieModuleHom.toEndRingHom (F.idem M * φ.app M * F.idem M -
      (F.idem M * φ.app M * F.idem M) ^ 2) =
      -(((b.comp b).app M : M ⊗[K] V →ₗ[K] M ⊗[K] V) -
        (b.app M : M ⊗[K] V →ₗ[K] M ⊗[K] V)) := by
    rw [map_sub, map_pow, ← hbM, sq, neg_sub]
    rfl
  rw [he]
  exact h.neg

include hA in
/-- **Idempotents at `M(λ)` lift to summands** (Bernstein–Gelfand, proof of Thm. 3.3;
Humphreys, §10.8): let `λ` be dominant, `I` the annihilator of `M(λ)`, and assume Kostant's
multiplicity formula for `(U(𝔤) / I)^{ad}`. For a projective functor `F = e(− ⊗ V)` on the
block of `λ` and an idempotent `q` of `M(λ) ⊗ V` with `e q = q = q e`, there is a summand `F₁`
of `F` with value `q` at `M(λ)`. Its idempotent is the canonical lift `idempotentLift (e φ e)`
of a natural transformation `φ` with `φ_{M(λ)} = q`. -/
theorem exists_isSummand_idem_verma [FiniteDimensional K V]
    (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (hK : KostantMultiplicity P (AdQuotient K 𝔤 I))
    (q : VermaModule P lam ⊗[K] V →ₗ⁅K,𝔤⁆ VermaModule P lam ⊗[K] V) (hq : IsIdempotentElem q)
    (hqF : F.idem (VermaModule P lam) * q = q) (hFq : q * F.idem (VermaModule P lam) = q) :
    ∃ F₁ : BlockProjectiveFunctor P hA lam V,
      F₁.idem (VermaModule P lam) = q ∧ F₁.IsSummand F := by
  obtain ⟨φ, hφ⟩ := exists_tensorNatTrans_app_verma P hA hlam hM₀ hI hK q
  have hqV : F.idem (VermaModule P lam) * φ.app _ * F.idem (VermaModule P lam) = q := by
    rw [hφ, hqF, hFq]
  have hnil : ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
      [LieModule K 𝔤 M], IsInBlock P hA lam M →
      IsNilpotent (F.idem M * φ.app M * F.idem M - (F.idem M * φ.app M * F.idem M) ^ 2) :=
    fun M _ _ _ _ hM ↦ F.isNilpotent_idem_mul_mul_idem hlam hM₀ hI φ (by rw [hqV]; exact hq) hM
  let F₁ : BlockProjectiveFunctor P hA lam V :=
    { idem := fun M _ _ _ _ ↦ idempotentLift (F.idem M * φ.app M * F.idem M)
      idem_idem := fun M _ _ _ _ hM x ↦
        DFunLike.congr_fun (isIdempotentElem_idempotentLift (hnil M hM)).eq x
      exists_tensorNatTrans := fun M N _ _ _ _ _ _ _ _ hM hN ↦ by
        obtain ⟨t, htM, htN⟩ := F.exists_tensorNatTrans M N hM hN
        obtain ⟨k₁, hk₁⟩ := hnil M hM
        obtain ⟨k₂, hk₂⟩ := hnil N hN
        refine ⟨((t.comp φ).comp t).idempotentLiftPow (max k₁ k₂), ?_, ?_⟩
        · rw [idempotentLift_eq (pow_eq_zero_of_le (le_max_left _ _) hk₁),
            TensorNatTrans.idempotentLiftPow_app, TensorNatTrans.comp_app,
            TensorNatTrans.comp_app, htM]
          rfl
        · rw [idempotentLift_eq (pow_eq_zero_of_le (le_max_right _ _) hk₂),
            TensorNatTrans.idempotentLiftPow_app, TensorNatTrans.comp_app,
            TensorNatTrans.comp_app, htN]
          rfl }
  refine ⟨F₁, ?_, fun M _ _ _ _ hM ↦ ?_⟩
  · change idempotentLift (F.idem (VermaModule P lam) * φ.app _ * F.idem (VermaModule P lam)) = q
    rw [hqV]
    exact hq.idempotentLift_eq
  · change F.idem M * idempotentLift (F.idem M * φ.app M * F.idem M) =
        idempotentLift (F.idem M * φ.app M * F.idem M) ∧
      idempotentLift (F.idem M * φ.app M * F.idem M) * F.idem M =
        idempotentLift (F.idem M * φ.app M * F.idem M)
    obtain ⟨k, hk⟩ := hnil M hM
    have he := F.idem_mul_idem hM
    rw [idempotentLift_eq (pow_eq_zero_of_le (Nat.le_succ k) hk)]
    refine ⟨mul_idempotentLiftPow_eq (Nat.succ_ne_zero k) ?_,
      idempotentLiftPow_mul_eq (Nat.succ_ne_zero k) ?_⟩
    · rw [← mul_assoc, ← mul_assoc, he]
    · rw [mul_assoc _ (F.idem M), he]

end BlockProjectiveFunctor

end Matrix.Realization.KacMoodyAlgebra
