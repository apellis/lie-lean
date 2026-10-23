/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BlockProjectiveFunctor
import LieLean.Algebra.Lie.KacMoody.CategoryOTranslation
import LieLean.Algebra.Lie.KacMoody.FiniteLength

/-!
# Decomposition of projective functors on a block

Let `λ` be dominant. A projective functor `F = e(− ⊗ V)` on the block of `λ`
(`BlockProjectiveFunctor`) is *indecomposable* if it is nonzero on the block and each of its
summands `F₁` (`BlockProjectiveFunctor.IsSummand`) is zero on the block or has zero complement
`F - F₁` on the block. This file proves part (i) of Bernstein–Gelfand's Theorem 3.3 for the
block: every projective functor on the block is a finite sum of pairwise orthogonal
indecomposable summands (`BlockProjectiveFunctor.exists_decomposition`).

Since a projective functor vanishing at `M(λ)` vanishes on the block
(`BlockProjectiveFunctor.idem_eq_zero_of_idem_verma_eq_zero`), a summand that is neither zero
nor all of `F` cuts the corner `e End(M(λ) ⊗ V) e` down to a proper subspace. This corner is
finite-dimensional, and the decomposition follows by induction on its dimension. Summands are
taken among projective functors of the form `e₁(− ⊗ V)` with the same `V`. Bernstein–Gelfand
derive Thm. 3.3 (i) from their Cor. 3.8 (decompositions of `F(M(λ))` extend to `F`); here only
the vanishing statement at `M(λ)` is used.

## Main definitions

* `BlockProjectiveFunctor.IsZero`: `F` vanishes on the block.
* `BlockProjectiveFunctor.IsIndecomposable`.
* `BlockProjectiveFunctor.corner`: the corner `e End(M(λ) ⊗ V) e`.

## Main results

* `BlockProjectiveFunctor.IsSummand.trans`, `BlockProjectiveFunctor.IsSummand.mul_eq_zero`
  (summands of `F₁` and of `F - F₁` are orthogonal).
* `BlockProjectiveFunctor.exists_decomposition`: **Bernstein–Gelfand Thm. 3.3 (i)** on a block.

## References

* J. N. Bernstein, S. I. Gelfand, *Tensor products of finite and infinite dimensional
  representations of semisimple Lie algebras*, Compositio Math. **41** (1980), 245–285,
  Thm. 3.3 (i).
* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8.
-/

noncomputable section

open Module UniversalEnvelopingAlgebra
open scoped TensorProduct

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra.BlockProjectiveFunctor

open VermaModule

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ}
  {P : Realization A K H} {hA : A.IsFiniteCartan}

local notation "𝔤" => KacMoodyAlgebra P

variable {lam : Dual K H} {V : Type (max u₁ u₂)} [AddCommGroup V] [Module K V]
  [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
  (F : BlockProjectiveFunctor P hA lam V)

/-- `F` vanishes on the block. -/
def IsZero : Prop :=
  ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M],
    IsInBlock P hA lam M → F.idem M = 0

/-- `F` is indecomposable: it is nonzero on the block, and every summand of `F` is zero on the
block or has zero complement on the block. -/
def IsIndecomposable : Prop :=
  ¬ F.IsZero ∧ ∀ (F₁ : BlockProjectiveFunctor P hA lam V) (h : F₁.IsSummand F),
    F₁.IsZero ∨ (F.sub F₁ h).IsZero

theorem isSummand_refl : F.IsSummand F := fun _ _ _ _ _ hM ↦
  ⟨F.idem_mul_idem hM, F.idem_mul_idem hM⟩

/-- A summand of a summand is a summand. -/
theorem IsSummand.trans {F₁ F₂ : BlockProjectiveFunctor P hA lam V} (h₁ : F₁.IsSummand F₂)
    (h₂ : F₂.IsSummand F) : F₁.IsSummand F := fun M _ _ _ _ hM ↦ by
  obtain ⟨h₁₁, h₁₂⟩ := h₁ M hM
  obtain ⟨h₂₁, h₂₂⟩ := h₂ M hM
  refine ⟨?_, ?_⟩
  · rw [← h₁₁, ← mul_assoc, h₂₁]
  · rw [← h₁₂, mul_assoc, h₂₂]

/-- A summand of `F₁` and a summand of the complement `F - F₁` are orthogonal. -/
theorem IsSummand.mul_eq_zero {F₁ Fa Fb : BlockProjectiveFunctor P hA lam V}
    (h : F₁.IsSummand F) (ha : Fa.IsSummand F₁) (hb : Fb.IsSummand (F.sub F₁ h))
    {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    (hM : IsInBlock P hA lam M) :
    Fa.idem M * Fb.idem M = 0 ∧ Fb.idem M * Fa.idem M = 0 := by
  obtain ⟨h₁, h₂⟩ := h M hM
  obtain ⟨ha₁, ha₂⟩ := ha M hM
  obtain ⟨hb₁, hb₂⟩ := hb M hM
  rw [sub_idem] at hb₁ hb₂
  refine ⟨?_, ?_⟩
  · rw [← ha₂, ← hb₁, mul_assoc, ← mul_assoc (F₁.idem M), mul_sub, h₂, F₁.idem_mul_idem hM,
      sub_self, zero_mul, mul_zero]
  · rw [← ha₁, ← hb₂, mul_assoc, ← mul_assoc _ (F₁.idem M), sub_mul, h₁, F₁.idem_mul_idem hM,
      sub_self, zero_mul, mul_zero]

/-- The linear map `f ↦ e f e` on the endomorphisms of a Lie module. -/
def cornerMap {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    (e : M →ₗ⁅K,𝔤⁆ M) : (M →ₗ⁅K,𝔤⁆ M) →ₗ[K] (M →ₗ⁅K,𝔤⁆ M) where
  toFun f := e * f * e
  map_add' f g := by rw [mul_add, add_mul]
  map_smul' c f := LieModuleHom.ext fun x ↦ by
    change e ((c • f) (e x)) = c • e (f (e x))
    rw [_root_.smul_apply, map_smul]

variable [IsAlgClosed K] [FiniteDimensional K H]

/-- The corner `e End(M(λ) ⊗ V) e` of `F = e(− ⊗ V)`. -/
def corner :
    Submodule K (VermaModule P lam ⊗[K] V →ₗ⁅K,𝔤⁆ VermaModule P lam ⊗[K] V) :=
  LinearMap.range (cornerMap (F.idem (VermaModule P lam)))

theorem idem_mem_corner : F.idem (VermaModule P lam) ∈ F.corner :=
  ⟨1, by
    change F.idem _ * 1 * F.idem _ = F.idem _
    rw [mul_one, F.idem_mul_idem (isInBlock_verma P hA lam)]⟩

theorem corner_le {F₁ : BlockProjectiveFunctor P hA lam V} (h : F₁.IsSummand F) :
    F₁.corner ≤ F.corner := by
  rintro _ ⟨g, rfl⟩
  obtain ⟨h₁, h₂⟩ := h _ (isInBlock_verma P hA lam)
  refine ⟨F₁.idem _ * g * F₁.idem _, ?_⟩
  change F.idem _ * (F₁.idem _ * g * F₁.idem _) * F.idem _ = F₁.idem _ * g * F₁.idem _
  rw [← mul_assoc, ← mul_assoc, h₁, mul_assoc, h₂]

/-- If the idempotent of `F` at `M(λ)` lies in the corner of a summand `F₁`, the two agree at
`M(λ)`. -/
theorem idem_verma_eq_of_mem_corner {F₁ : BlockProjectiveFunctor P hA lam V}
    (h : F₁.IsSummand F) (hmem : F.idem (VermaModule P lam) ∈ F₁.corner) :
    F.idem (VermaModule P lam) = F₁.idem (VermaModule P lam) := by
  obtain ⟨g, hg⟩ := hmem
  change F₁.idem _ * g * F₁.idem _ = F.idem _ at hg
  have hb := isInBlock_verma P hA lam
  calc F.idem (VermaModule P lam) = F₁.idem _ * F.idem _ := by
        rw [← hg, ← mul_assoc, ← mul_assoc, F₁.idem_mul_idem hb]
    _ = F₁.idem _ := (h _ hb).2

omit [IsAlgClosed K] in
include hA in
theorem finiteDimensional_corner [FiniteDimensional K V] :
    FiniteDimensional K
      (VermaModule P lam ⊗[K] V →ₗ⁅K,𝔤⁆ VermaModule P lam ⊗[K] V) := by
  have hO := (VermaModule.isCategoryO P lam).tensorProduct
    (isCategoryO_of_finiteDimensional (P := P) (V := V) hA)
  obtain ⟨T, hT⟩ := exists_finset_lieSpan_tensor_eq_top (W := V)
    (S := {VermaModule.hwv P lam}) (by
      rw [Finset.coe_singleton]
      exact VermaModule.lieSpan_map_hwv_eq_top LieModuleHom.id Function.surjective_id)
  exact hO.finiteDimensional_hom P hT hO

include hA in
/-- A proper summand has a smaller corner. -/
theorem finrank_corner_lt [FiniteDimensional K V] {F₁ : BlockProjectiveFunctor P hA lam V}
    (h : F₁.IsSummand F) (hne : F.idem (VermaModule P lam) ≠ F₁.idem (VermaModule P lam)) :
    finrank K F₁.corner < finrank K F.corner := by
  have := finiteDimensional_corner (P := P) (hA := hA) (lam := lam) (V := V)
  refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (F.corner_le h) fun heq ↦ hne ?_)
  exact F.idem_verma_eq_of_mem_corner h (heq ▸ F.idem_mem_corner)

include hA in
/-- **Projective functors on a block are sums of indecomposables** (Bernstein–Gelfand,
Thm. 3.3 (i); Humphreys, §10.8): let `λ` be dominant and `I` the annihilator of `M(λ)`. Every
projective functor `F = e(− ⊗ V)` on the block of `λ` (`V` finite-dimensional) is the sum on the
block of a finite list of pairwise orthogonal indecomposable summands. -/
theorem exists_decomposition [FiniteDimensional K V]
    (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I) :
    ∃ l : List (BlockProjectiveFunctor P hA lam V),
      (∀ G ∈ l, G.IsIndecomposable ∧ G.IsSummand F) ∧
      l.Pairwise (fun G G' ↦ ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M]
        [LieRingModule 𝔤 M] [LieModule K 𝔤 M], IsInBlock P hA lam M →
          G.idem M * G'.idem M = 0 ∧ G'.idem M * G.idem M = 0) ∧
      ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
        [LieModule K 𝔤 M], IsInBlock P hA lam M → (l.map fun G ↦ G.idem M).sum = F.idem M := by
  -- A summand that is nonzero on the block is nonzero at `M(λ)`.
  have hne : ∀ G : BlockProjectiveFunctor P hA lam V, ¬ G.IsZero →
      G.idem (VermaModule P lam) ≠ 0 := fun G hG h0 ↦
    hG fun M _ _ _ _ hM ↦ G.idem_eq_zero_of_idem_verma_eq_zero hlam hM₀ hI h0 hM
  induction hn : finrank K F.corner using Nat.strong_induction_on generalizing F with
  | _ n ih =>
  by_cases hz : F.IsZero
  · exact ⟨[], by simp, List.Pairwise.nil, fun M _ _ _ _ hM ↦ by simp [hz M hM]⟩
  by_cases hi : F.IsIndecomposable
  · exact ⟨[F], by simpa using ⟨hi, F.isSummand_refl⟩, List.pairwise_singleton _ _,
      fun M _ _ _ _ _ ↦ by simp⟩
  have : ∃ (F₁ : BlockProjectiveFunctor P hA lam V) (h : F₁.IsSummand F),
      ¬ F₁.IsZero ∧ ¬ (F.sub F₁ h).IsZero := by
    by_contra hc
    push Not at hc
    exact hi ⟨hz, fun F₁ h ↦ by
      by_cases h₁ : F₁.IsZero
      · exact Or.inl h₁
      · exact Or.inr (hc F₁ h h₁)⟩
  obtain ⟨F₁, h, h₁, h₂⟩ := this
  have hlt₁ : finrank K F₁.corner < n := hn ▸ F.finrank_corner_lt h fun heq ↦
    hne _ h₂ (by rw [sub_idem, heq, sub_self])
  have hlt₂ : finrank K (F.sub F₁ h).corner < n := hn ▸ F.finrank_corner_lt
    (F.sub_isSummand F₁ h) fun heq ↦ hne _ h₁ (by
      have := congrArg (F.idem (VermaModule P lam) - ·) heq
      simpa using this.symm)
  obtain ⟨l₁, hl₁, hp₁, hs₁⟩ := ih _ hlt₁ F₁ rfl
  obtain ⟨l₂, hl₂, hp₂, hs₂⟩ := ih _ hlt₂ (F.sub F₁ h) rfl
  refine ⟨l₁ ++ l₂, fun G hG ↦ ?_, ?_, fun M _ _ _ _ hM ↦ ?_⟩
  · rcases List.mem_append.mp hG with hG | hG
    · exact ⟨(hl₁ G hG).1, (hl₁ G hG).2.trans F h⟩
    · exact ⟨(hl₂ G hG).1, (hl₂ G hG).2.trans F (F.sub_isSummand F₁ h)⟩
  · refine List.pairwise_append.mpr ⟨hp₁, hp₂, fun Ga hGa Gb hGb M _ _ _ _ hM ↦ ?_⟩
    exact h.mul_eq_zero F (hl₁ Ga hGa).2 (hl₂ Gb hGb).2 hM
  · rw [List.map_append, List.sum_append, hs₁ M hM, hs₂ M hM, sub_idem, add_sub_cancel]

end Matrix.Realization.KacMoodyAlgebra.BlockProjectiveFunctor
