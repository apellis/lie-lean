/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BlockProjectiveFunctorDecomposition
import LieLean.Algebra.Lie.KacMoody.ProjectiveDecomposition
import LieLean.Algebra.Lie.KacMoody.TranslationProjectiveCover

/-!
# Indecomposable projective functors on a block

Let `λ` be dominant, `I` the annihilator of `M(λ)`, and assume Kostant's multiplicity formula for
`(U(𝔤) / I)^{ad}`. This file proves, for projective functors `F = e(− ⊗ V)` on the block of `λ`
(`BlockProjectiveFunctor`, `V` finite-dimensional):

* Bernstein–Gelfand's Cor. 3.8 on the block: an isomorphism `F(M(λ)) ≅ G(M(λ))` is the value at
  `M(λ)` of one natural transformation that restricts to bijections `F(M) → G(M)` at every module
  `M` of the block (`BlockProjectiveFunctor.exists_bijOn_of_equiv_verma`);
* Bernstein–Gelfand's Thm. 3.3 (ii) on the block: `F` is indecomposable if and only if
  `F(M(λ)) = e(M(λ) ⊗ V)` is isomorphic to an indecomposable projective `P(μ)`
  (`BlockProjectiveFunctor.isIndecomposable_iff_exists_equiv_projectiveCover`). With Cor. 3.8,
  indecomposable projective functors on the block are determined up to isomorphism on the block
  by the weight `μ`;
* Bernstein–Gelfand's Thm. 3.4 (i) on the block: projective functors with equal characters
  `[F(M)] = [G(M)]` on the block are isomorphic on the block
  (`BlockProjectiveFunctor.exists_bijOn_of_character_eq`).

The direction "`F(M(λ)) ≅ P(μ)` implies `F` indecomposable" needs only the vanishing of a
projective functor that vanishes at `M(λ)`, and holds without the Kostant hypothesis
(`BlockProjectiveFunctor.isIndecomposable_of_equiv_projectiveCover`). The projective covers
`P(μ)` have only the idempotent endomorphisms `0` and `1`
(`ProjectiveCover.eq_zero_or_eq_one_of_isIdempotentElem`).

## Main results

* `ProjectiveCover.eq_zero_or_eq_one_of_isIdempotentElem`.
* `BlockProjectiveFunctor.exists_bijOn_of_equiv_verma`: **Bernstein–Gelfand Cor. 3.8**.
* `BlockProjectiveFunctor.exists_nonempty_equiv_projectiveCover`,
  `BlockProjectiveFunctor.isIndecomposable_iff_exists_equiv_projectiveCover`:
  **Bernstein–Gelfand Thm. 3.3 (ii)** on a block.
* `BlockProjectiveFunctor.exists_bijOn_of_character_eq`: **Bernstein–Gelfand Thm. 3.4 (i)** on
  a block.

## References

* J. N. Bernstein, S. I. Gelfand, *Tensor products of finite and infinite dimensional
  representations of semisimple Lie algebras*, Compositio Math. **41** (1980), 245–285,
  Thm. 3.3, Thm. 3.4, Cor. 3.8.
* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8.
-/

noncomputable section

open Module UniversalEnvelopingAlgebra
open scoped TensorProduct

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ}

namespace ProjectiveCover

variable (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

/-- An idempotent endomorphism of `P(μ)` whose image is not killed by `π_μ` is the identity. -/
theorem eq_one_of_isIdempotentElem_of_not_range_le_ker {μ : Dual K H}
    {b : ProjectiveCover P hA μ →ₗ⁅K,𝔤⁆ ProjectiveCover P hA μ} (hb : IsIdempotentElem b)
    (h : ¬ b.range ≤ (π P hA μ).ker) : b = 1 := by
  have htop := eq_top_of_not_le_ker P hA μ b.range h
  refine LieModuleHom.ext fun y ↦ ?_
  have hy : y ∈ b.range := htop ▸ LieSubmodule.mem_top y
  obtain ⟨x, rfl⟩ := (LieModuleHom.mem_range _ _).mp hy
  exact DFunLike.congr_fun hb.eq x

/-- **`P(μ)` is indecomposable**: its only idempotent endomorphisms are `0` and `1`. -/
theorem eq_zero_or_eq_one_of_isIdempotentElem {μ : Dual K H}
    {a : ProjectiveCover P hA μ →ₗ⁅K,𝔤⁆ ProjectiveCover P hA μ} (ha : IsIdempotentElem a) :
    a = 0 ∨ a = 1 := by
  by_cases h : a.range ≤ (π P hA μ).ker
  · left
    have h1 : 1 - a = 1 := by
      refine eq_one_of_isIdempotentElem_of_not_range_le_ker P hA ha.one_sub fun h' ↦
        π_ne_zero P hA μ (LieModuleHom.ext fun x ↦ ?_)
      have h₁ : π P hA μ ((1 - a) x) = 0 :=
        LieModuleHom.mem_ker.mp (h' ((LieModuleHom.mem_range _ _).mpr ⟨x, rfl⟩))
      have h₂ : π P hA μ (a x) = 0 :=
        LieModuleHom.mem_ker.mp (h ((LieModuleHom.mem_range _ _).mpr ⟨x, rfl⟩))
      rw [_root_.sub_apply, map_sub, h₂, sub_zero] at h₁
      exact h₁
    rwa [sub_eq_self] at h1
  · exact Or.inr (eq_one_of_isIdempotentElem_of_not_range_le_ker P hA ha h)

end ProjectiveCover

namespace BlockProjectiveFunctor

variable {P : Realization A K H} {hA : A.IsFiniteCartan}

local notation "𝔤" => KacMoodyAlgebra P

variable {lam : Dual K H} {V : Type (max u₁ u₂)} [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
  (F : BlockProjectiveFunctor P hA lam V)

include hA in
/-- **An isomorphism at `M(λ)` extends to the block** (Bernstein–Gelfand, Cor. 3.8; Humphreys,
Thm. 10.7): let `λ` be dominant, `I` the annihilator of `M(λ)`, and assume Kostant's multiplicity
formula for `(U(𝔤) / I)^{ad}`. If `F = e(− ⊗ V)` and `G = e'(− ⊗ W)` are projective functors on
the block of `λ` with `F(M(λ)) ≅ G(M(λ))`, there is a natural transformation `φ : − ⊗ V → − ⊗ W`
such that `x ↦ e'_M φ_M x` maps `F(M)` bijectively onto `G(M)` at every module `M` of the
block. -/
theorem exists_bijOn_of_equiv_verma [FiniteDimensional K V] {W : Type (max u₁ u₂)}
    [AddCommGroup W] [Module K W] [LieRingModule 𝔤 W] [LieModule K 𝔤 W] [FiniteDimensional K W]
    (G : BlockProjectiveFunctor P hA lam W) (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (hK : KostantMultiplicity P (AdQuotient K 𝔤 I))
    (E : (F.idem (VermaModule P lam)).range ≃ₗ⁅K,𝔤⁆ (G.idem (VermaModule P lam)).range) :
    ∃ φ : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 V W,
      ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
        [LieModule K 𝔤 M], IsInBlock P hA lam M →
        Set.BijOn (fun x ↦ G.idem M (φ.app M x)) (Set.range (F.idem M))
          (Set.range (G.idem M)) := by
  have hb := isInBlock_verma P hA lam
  obtain ⟨φ, φ', h₁, h₂⟩ := exists_tensorNatTrans_of_equiv_verma P hA hlam hM₀ hI hK
    (F.idem (VermaModule P lam)) (G.idem _) (F.idem_idem _ hb) (G.idem_idem _ hb) E
  refine ⟨φ, fun M _ _ _ _ hM ↦ ?_⟩
  obtain ⟨t, htM, htV⟩ := F.exists_tensorNatTrans M (VermaModule P lam) hM hb
  obtain ⟨t', ht'M, ht'V⟩ := G.exists_tensorNatTrans M (VermaModule P lam) hM hb
  obtain ⟨s, hs⟩ := hM.exists_finset
  have h := bijOn_range_of_block P hA hlam hM₀ hI t t' φ φ' (by rw [htV, ht'V]; exact h₁)
    (by rw [htV, ht'V]; exact h₂) hM.isCategoryO hs hM.multiplicity_ne_zero
    (by rw [htM]; exact F.idem_idem M hM) (by rw [ht'M]; exact G.idem_idem M hM)
  rwa [htM, ht'M] at h

/-- The value `F(M(λ)) = e(M(λ) ⊗ V)` at the Verma module. -/
abbrev vermaValue : LieSubmodule K 𝔤 (VermaModule P lam ⊗[K] V) :=
  (F.idem (VermaModule P lam)).range

theorem idem_comp_idem_verma :
    (F.idem (VermaModule P lam)).comp (F.idem (VermaModule P lam)) = F.idem _ :=
  LieModuleHom.ext (F.idem_idem _ (isInBlock_verma P hA lam))

include hA in
/-- If `F` is nonzero on the block, then `F(M(λ))` is nonzero. -/
theorem nontrivial_vermaValue (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (hF : ¬ F.IsZero) : Nontrivial F.vermaValue := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  refine hF fun M _ _ _ _ hM ↦ F.idem_eq_zero_of_idem_verma_eq_zero hlam hM₀ hI ?_ hM
  refine LieModuleHom.ext fun x ↦ ?_
  have h : rangeRetr (F.idem (VermaModule P lam)) x = 0 := Subsingleton.elim _ _
  exact congrArg Subtype.val h

include hA in
/-- **`F(M(λ))` of an indecomposable projective functor is indecomposable** (Bernstein–Gelfand,
proof of Thm. 3.3): with the Kostant hypothesis, every idempotent endomorphism of `F(M(λ))` is
`0` or `1` when `F` is indecomposable. -/
theorem eq_zero_or_eq_id_of_isIndecomposable [FiniteDimensional K V]
    (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (hK : KostantMultiplicity P (AdQuotient K 𝔤 I)) (hF : F.IsIndecomposable)
    (a : F.vermaValue →ₗ⁅K,𝔤⁆ F.vermaValue) (ha : a.comp a = a) :
    a = 0 ∨ a = LieModuleHom.id := by
  have hb := isInBlock_verma P hA lam
  have he := F.idem_comp_idem_verma
  set e := F.idem (VermaModule P lam) with he_def
  set q := e.range.incl.comp (a.comp (rangeRetr e)) with hq
  have hqq : IsIdempotentElem q := LieModuleHom.ext fun x ↦ by
    change e.range.incl (a (rangeRetr e (e.range.incl (a (rangeRetr e x))))) =
      e.range.incl (a (rangeRetr e x))
    rw [rangeRetr_incl he, ← LieModuleHom.comp_apply a a, ha]
  have heq : e * q = q := LieModuleHom.ext fun x ↦ apply_incl he _
  have hqe : q * e = q := LieModuleHom.ext fun x ↦ by
    change e.range.incl (a (rangeRetr e (e x))) = e.range.incl (a (rangeRetr e x))
    rw [rangeRetr_apply he]
  obtain ⟨F₁, hF₁, hs⟩ := F.exists_isSummand_idem_verma hlam hM₀ hI hK q hqq heq hqe
  rcases hF.2 F₁ hs with h0 | h0
  · refine Or.inl (LieModuleHom.ext fun y ↦ Subtype.ext ?_)
    have h := LieModuleHom.congr_fun (h0 _ hb) (e.range.incl y)
    rw [hF₁] at h
    change e.range.incl (a (rangeRetr e (e.range.incl y))) = 0 at h
    rw [rangeRetr_incl he] at h
    exact h
  · refine Or.inr (LieModuleHom.ext fun y ↦ Subtype.ext ?_)
    have h := LieModuleHom.congr_fun (h0 _ hb) (e.range.incl y)
    rw [sub_idem, _root_.sub_apply, _root_.zero_apply, hF₁, sub_eq_zero,
      apply_incl he] at h
    change _ = e.range.incl (a (rangeRetr e (e.range.incl y))) at h
    rw [rangeRetr_incl he] at h
    exact h.symm

omit [IsAlgClosed K] in
include hA in
/-- `F(M(λ))` lies in `𝒪`. -/
theorem isCategoryO_vermaValue [FiniteDimensional K V] : IsCategoryO P F.vermaValue :=
  ((VermaModule.isCategoryO P lam).tensorProduct
    (isCategoryO_of_finiteDimensional (P := P) (V := V) hA)).lieSubmodule _

include hA in
/-- `F(M(λ))` is projective in `𝒪` for `λ` dominant. -/
theorem isProjectiveO_vermaValue [FiniteDimensional K V]
    (hlam : P.IsDominant hA.isGeneralizedCartan lam) :
    IsProjectiveO.{max u₁ u₂} P F.vermaValue :=
  ((VermaModule.isProjectiveO P hA hlam).tensorProduct P
      (isCategoryO_of_finiteDimensional (P := P) (V := Module.Dual K V) hA)).of_retract
    (F.idem _).range.incl (rangeRetr _) (rangeRetr_comp_incl F.idem_comp_idem_verma)

/-- `F(M(λ))` is finitely generated. -/
theorem exists_finset_lieSpan_vermaValue [FiniteDimensional K V] :
    ∃ S : Finset F.vermaValue, LieSubmodule.lieSpan K 𝔤 (S : Set F.vermaValue) = ⊤ := by
  obtain ⟨T, hT⟩ := exists_finset_lieSpan_tensor_eq_top (W := V)
    (S := {VermaModule.hwv P lam}) (by
      rw [Finset.coe_singleton]
      exact VermaModule.lieSpan_map_hwv_eq_top LieModuleHom.id Function.surjective_id)
  classical
  refine ⟨T.image (rangeRetr (F.idem _)), ?_⟩
  rw [Finset.coe_image]
  exact lieSpan_image_eq_top_of_surjective _ (surjective_rangeRetr F.idem_comp_idem_verma) hT

include hA in
/-- **Indecomposable projective functors give projective covers** (Bernstein–Gelfand,
Thm. 3.3 (ii); Humphreys, §10.8): let `λ` be dominant, `I` the annihilator of `M(λ)`, and assume
Kostant's multiplicity formula for `(U(𝔤) / I)^{ad}`. If a projective functor `F = e(− ⊗ V)` on
the block of `λ` is indecomposable, then `F(M(λ)) ≅ P(μ)` for some weight `μ`. -/
theorem exists_nonempty_equiv_projectiveCover [FiniteDimensional K V]
    (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (hK : KostantMultiplicity P (AdQuotient K 𝔤 I)) (hF : F.IsIndecomposable) :
    ∃ μ : Dual K H, Nonempty (ProjectiveCover P hA μ ≃ₗ⁅K,𝔤⁆ F.vermaValue) := by
  have := F.nontrivial_vermaValue hlam hM₀ hI hF.1
  obtain ⟨S, hS⟩ := F.exists_finset_lieSpan_vermaValue
  exact ProjectiveCover.exists_nonempty_equiv_of_indecomposable P hA
    (F.isProjectiveO_vermaValue hlam) F.isCategoryO_vermaValue hS
    (F.eq_zero_or_eq_id_of_isIndecomposable hlam hM₀ hI hK hF)

include hA in
/-- **A projective functor with value a projective cover is indecomposable** (Bernstein–Gelfand,
Thm. 3.3 (ii)): let `λ` be dominant and `I` the annihilator of `M(λ)`. If `F(M(λ)) ≅ P(μ)` for a
projective functor `F` on the block of `λ`, then `F` is indecomposable. No Kostant hypothesis is
needed. -/
theorem isIndecomposable_of_equiv_projectiveCover
    (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I) {μ : Dual K H}
    (E : ProjectiveCover P hA μ ≃ₗ⁅K,𝔤⁆ F.vermaValue) : F.IsIndecomposable := by
  have hb := isInBlock_verma P hA lam
  have he := F.idem_comp_idem_verma
  set e := F.idem (VermaModule P lam) with he_def
  refine ⟨fun hz ↦ ProjectiveCover.π_ne_zero P hA μ (LieModuleHom.ext fun x ↦ ?_),
    fun F₁ hs ↦ ?_⟩
  · have hz0 : e = 0 := hz _ hb
    have h0 : E x = 0 := by
      apply Subtype.ext
      obtain ⟨y, hy⟩ := (LieModuleHom.mem_range _ _).mp (E x).2
      rw [← hy, ← he_def, hz0]
      rfl
    have hx : x = 0 := E.injective (h0.trans (map_zero E).symm)
    rw [hx, map_zero]
    rfl
  obtain ⟨heq, hqe⟩ := hs _ hb
  set q := F₁.idem (VermaModule P lam) with hq_def
  have hqq : ∀ x, q (q x) = q x := F₁.idem_idem _ hb
  have heq' : ∀ x, e (q x) = q x := fun x ↦ LieModuleHom.congr_fun heq x
  have hqe' : ∀ x, q (e x) = q x := fun x ↦ LieModuleHom.congr_fun hqe x
  set a : F.vermaValue →ₗ⁅K,𝔤⁆ F.vermaValue := (rangeRetr e).comp (q.comp e.range.incl)
  have key : ∀ x, e.range.incl (a (rangeRetr e x)) = q x := fun x ↦ by
    change e (q (e x)) = q x
    rw [hqe', heq']
  have ha : a.comp a = a := LieModuleHom.ext fun y ↦ Subtype.ext <| by
    change e (q (e (q (e.range.incl y)))) = e (q (e.range.incl y))
    rw [heq', hqe', hqq, heq']
  set b : ProjectiveCover P hA μ →ₗ⁅K,𝔤⁆ ProjectiveCover P hA μ :=
    (E.symm : F.vermaValue →ₗ⁅K,𝔤⁆ ProjectiveCover P hA μ).comp
      (a.comp (E : ProjectiveCover P hA μ →ₗ⁅K,𝔤⁆ F.vermaValue))
  have hbb : IsIdempotentElem b := LieModuleHom.ext fun x ↦ by
    change E.symm (a (E (E.symm (a (E x))))) = E.symm (a (E x))
    rw [LieModuleEquiv.apply_symm_apply]
    exact congrArg E.symm (LieModuleHom.congr_fun ha (E x))
  have hab : ∀ y, a y = E (b (E.symm y)) := fun y ↦ by
    change a y = E (E.symm (a (E (E.symm y))))
    rw [LieModuleEquiv.apply_symm_apply, LieModuleEquiv.apply_symm_apply]
  rcases ProjectiveCover.eq_zero_or_eq_one_of_isIdempotentElem P hA hbb with h0 | h1
  · left
    have hq0 : q = 0 := LieModuleHom.ext fun x ↦ by
      rw [← key, hab, h0]
      change e.range.incl (E 0) = 0
      rw [map_zero, map_zero]
    exact fun M _ _ _ _ hM ↦ F₁.idem_eq_zero_of_idem_verma_eq_zero hlam hM₀ hI hq0 hM
  · right
    have hqe0 : (F.sub F₁ hs).idem (VermaModule P lam) = 0 := by
      rw [sub_idem]
      refine LieModuleHom.ext fun x ↦ ?_
      rw [_root_.sub_apply, ← key, hab, h1]
      change e x - e.range.incl (E (E.symm (rangeRetr e x))) = 0
      rw [LieModuleEquiv.apply_symm_apply, incl_rangeRetr, sub_self]
    exact fun M _ _ _ _ hM ↦
      (F.sub F₁ hs).idem_eq_zero_of_idem_verma_eq_zero hlam hM₀ hI hqe0 hM

include hA in
/-- **Bernstein–Gelfand, Thm. 3.3 (ii)** on the block of a dominant weight `λ`, with `I` the
annihilator of `M(λ)` and Kostant's multiplicity formula for `(U(𝔤) / I)^{ad}` assumed: a
projective functor `F = e(− ⊗ V)` on the block is indecomposable if and only if `F(M(λ))` is
isomorphic to an indecomposable projective `P(μ)`. -/
theorem isIndecomposable_iff_exists_equiv_projectiveCover [FiniteDimensional K V]
    (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (hK : KostantMultiplicity P (AdQuotient K 𝔤 I)) :
    F.IsIndecomposable ↔
      ∃ μ : Dual K H, Nonempty (ProjectiveCover P hA μ ≃ₗ⁅K,𝔤⁆ F.vermaValue) :=
  ⟨F.exists_nonempty_equiv_projectiveCover hlam hM₀ hI hK, fun ⟨_, ⟨E⟩⟩ ↦
    F.isIndecomposable_of_equiv_projectiveCover hlam hM₀ hI E⟩

include hA in
/-- **Projective functors with the same action on the Grothendieck group are isomorphic**
(Bernstein–Gelfand, Thm. 3.4 (i), on a block): let `λ` be dominant, `I` the annihilator of
`M(λ)`, and assume Kostant's multiplicity formula for `(U(𝔤) / I)^{ad}`. If projective functors
`F = e(− ⊗ V)` and `G = e'(− ⊗ W)` on the block of `λ` have `[F(M)] = [G(M)]` (equal
characters) for every module `M` of the block, there is a natural transformation
`φ : − ⊗ V → − ⊗ W` such that `x ↦ e'_M φ_M x` maps `F(M)` bijectively onto `G(M)` at every
module `M` of the block. Only the module `M(λ)` is used. -/
theorem exists_bijOn_of_character_eq [FiniteDimensional K V] {W : Type (max u₁ u₂)}
    [AddCommGroup W] [Module K W] [LieRingModule 𝔤 W] [LieModule K 𝔤 W] [FiniteDimensional K W]
    (G : BlockProjectiveFunctor P hA lam W) (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (hK : KostantMultiplicity P (AdQuotient K 𝔤 I))
    (hch : ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
      [LieModule K 𝔤 M], IsInBlock P hA lam M → ∀ (hF : IsCategoryO P (F.idem M).range)
      (hG : IsCategoryO P (G.idem M).range), hF.character = hG.character) :
    ∃ φ : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 V W,
      ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
        [LieModule K 𝔤 M], IsInBlock P hA lam M →
        Set.BijOn (fun x ↦ G.idem M (φ.app M x)) (Set.range (F.idem M))
          (Set.range (G.idem M)) := by
  obtain ⟨S, hS⟩ := F.exists_finset_lieSpan_vermaValue
  obtain ⟨S', hS'⟩ := G.exists_finset_lieSpan_vermaValue
  obtain ⟨E⟩ := IsProjectiveO.nonempty_equiv_of_character_eq P hA
    (F.isProjectiveO_vermaValue hlam) F.isCategoryO_vermaValue hS
    (G.isProjectiveO_vermaValue hlam) G.isCategoryO_vermaValue hS'
    (hch _ (isInBlock_verma P hA lam) _ _)
  exact F.exists_bijOn_of_equiv_verma G hlam hM₀ hI hK E

end BlockProjectiveFunctor

end Matrix.Realization.KacMoodyAlgebra
