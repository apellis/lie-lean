/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationTensorNatTrans

/-!
# Projective functors are determined by their value at a dominant Verma module

Let `λ` be dominant, `I` the annihilator of `M(λ)`, and assume Kostant's multiplicity formula for
`(U(𝔤) / I)^{ad}`. A projective functor on the block of `λ` is a summand `e(− ⊗ V)` of a
tensoring functor, cut out by a natural idempotent `e`. If two such summands `e(− ⊗ V)`,
`e'(− ⊗ W)` have isomorphic values at `M(λ)`, then a single natural transformation
`φ : − ⊗ V → − ⊗ W` restricts to isomorphisms `e_M(M ⊗ V) ≅ e'_M(M ⊗ W)` at every finitely
generated `M ∈ 𝒪` in the block (Humphreys, Theorem 10.7). For composites of translation functors,
whose idempotents are natural only on `𝒪` and are realized on finitely many modules at a time by
natural transformations (`exists_tensorNatTrans_app_eq_translationIdem`), this is
`exists_bijOn_translationIdem`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.bijOn_range_of_block`: natural transformations that are
  mutually inverse between the summands at `M(λ)` restrict to bijections between the summands at
  every finitely generated `M` in the block.
* `Matrix.Realization.KacMoodyAlgebra.exists_tensorNatTrans_of_equiv_verma`: an isomorphism of
  the summands at `M(λ)` is the value of such a pair of natural transformations.
* `Matrix.Realization.KacMoodyAlgebra.exists_bijOn_translationIdem`: composites of translation
  functors with isomorphic values at `M(λ)` are isomorphic on the block, by one natural
  transformation.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §10.8, Thm. 10.7.
-/

noncomputable section

open Module UniversalEnvelopingAlgebra
open scoped TensorProduct

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

include hA in
/-- **Humphreys, Theorem 10.7 (b), on summands**: let `λ` be dominant and `I` the annihilator of
`M(λ)`. Let `e`, `e'`, `φ`, `φ'` be natural transformations of `− ⊗ V`, `− ⊗ W`, `− ⊗ V → − ⊗ W`
and back, such that `e φ' e'` and `e' φ e` are mutually inverse between the summands
`e(M(λ) ⊗ V)` and `e'(M(λ) ⊗ W)`. Then at every finitely generated `M ∈ 𝒪` in the block of `λ`
at which `e`, `e'` are idempotent, `e' φ` maps the summand `e_M(M ⊗ V)` bijectively onto
`e'_M(M ⊗ W)`. -/
theorem bijOn_range_of_block {lam : Dual K H} (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule 𝔤 V] [LieModule K 𝔤 V]
    [AddCommGroup W] [Module K W] [LieRingModule 𝔤 W] [LieModule K 𝔤 W]
    (e : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 V V)
    (e' : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 W W)
    (φ : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 V W)
    (φ' : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 W V)
    (h₁ : ∀ x, e.app (VermaModule P lam) (φ'.app _ (e'.app _ (e'.app _ (φ.app _
      (e.app (VermaModule P lam) x))))) = e.app _ x)
    (h₂ : ∀ y, e'.app (VermaModule P lam) (φ.app _ (e.app _ (e.app _ (φ'.app _
      (e'.app (VermaModule P lam) y))))) = e'.app _ y)
    {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    (hM : IsCategoryO P M) {s : Finset M} (hs : LieSubmodule.lieSpan K 𝔤 (s : Set M) = ⊤)
    (hblock : ∀ μ, hM.multiplicity μ ≠ 0 →
      ∃ w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam,
        μ = P.weylDot hA.isGeneralizedCartan w lam)
    (he : ∀ x, e.app M (e.app M x) = e.app M x) (he' : ∀ y, e'.app M (e'.app M y) = e'.app M y) :
    Set.BijOn (fun x ↦ e'.app M (φ.app M x)) (Set.range (e.app M)) (Set.range (e'.app M)) := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := exists_inverse_of_block P hA hlam hM₀ hI e e' ((e'.comp φ).comp e)
    ((e.comp φ').comp e') (LieModuleHom.ext h₁) (LieModuleHom.ext h₂) hM hs hblock he he'
    (fun x ↦ by simp only [TensorNatTrans.comp_app, LieModuleHom.comp_apply, he, he'])
    (fun y ↦ by simp only [TensorNatTrans.comp_app, LieModuleHom.comp_apply, he, he'])
  have hψ₁' : ∀ a, ψ (e'.app M (φ.app M (e.app M a))) = e.app M a := LinearMap.congr_fun hψ₁
  have hψ₂' : ∀ b, e'.app M (φ.app M (e.app M (ψ b))) = e'.app M b := LinearMap.congr_fun hψ₂
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    have := congrArg ψ hab
    simp only at this
    rwa [hψ₁', hψ₁'] at this
  · rintro _ ⟨b, rfl⟩
    exact ⟨e.app M (ψ (e'.app M b)), ⟨_, rfl⟩, by simp only [hψ₂', he']⟩

include hA in
/-- **Humphreys, Theorem 10.7 (a), on summands**: let `λ` be dominant, `I` the annihilator of
`M(λ)`, and assume Kostant's multiplicity formula for `(U(𝔤) / I)^{ad}`. For idempotents `p`, `p'`
of `M(λ) ⊗ V`, `M(λ) ⊗ W` (`V`, `W` finite-dimensional), an isomorphism of their images is induced
by natural transformations `φ`, `φ'` of `− ⊗ V → − ⊗ W` and back: `p φ' p'` and `p' φ p` are
mutually inverse between the images. -/
theorem exists_tensorNatTrans_of_equiv_verma {lam : Dual K H}
    (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (hK : KostantMultiplicity P (AdQuotient K 𝔤 I)) {V W : Type (max u₁ u₂)} [AddCommGroup V]
    [Module K V] [LieRingModule 𝔤 V] [LieModule K 𝔤 V] [FiniteDimensional K V] [AddCommGroup W]
    [Module K W] [LieRingModule 𝔤 W] [LieModule K 𝔤 W] [FiniteDimensional K W]
    (p : VermaModule P lam ⊗[K] V →ₗ⁅K,𝔤⁆ VermaModule P lam ⊗[K] V)
    (p' : VermaModule P lam ⊗[K] W →ₗ⁅K,𝔤⁆ VermaModule P lam ⊗[K] W)
    (hp : ∀ x, p (p x) = p x) (hp' : ∀ y, p' (p' y) = p' y) (E : p.range ≃ₗ⁅K,𝔤⁆ p'.range) :
    ∃ (φ : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 V W)
      (φ' : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 W V),
      (∀ x, p (φ'.app _ (p' (p' (φ.app _ (p x))))) = p x) ∧
        ∀ y, p' (φ.app _ (p (p (φ'.app _ (p' y))))) = p' y := by
  let r : VermaModule P lam ⊗[K] V →ₗ⁅K,𝔤⁆ p.range :=
    LieModuleHom.codRestrict p.range p fun x ↦ (LieModuleHom.mem_range p _).mpr ⟨x, rfl⟩
  let r' : VermaModule P lam ⊗[K] W →ₗ⁅K,𝔤⁆ p'.range :=
    LieModuleHom.codRestrict p'.range p' fun y ↦ (LieModuleHom.mem_range p' _).mpr ⟨y, rfl⟩
  obtain ⟨φ, hφ⟩ := exists_tensorNatTrans_app_verma P hA hlam hM₀ hI hK
    (p'.range.incl.comp (E.toLieModuleHom.comp r))
  obtain ⟨φ', hφ'⟩ := exists_tensorNatTrans_app_verma P hA hlam hM₀ hI hK
    (p.range.incl.comp (E.symm.toLieModuleHom.comp r'))
  -- an element of the image of `p` is fixed by `p`
  have hfix : ∀ x : p.range, p x = x := by
    rintro ⟨_, a, rfl⟩
    exact hp a
  have hfix' : ∀ y : p'.range, p' y = y := by
    rintro ⟨_, b, rfl⟩
    exact hp' b
  have hr : ∀ x : p.range, r x = x := fun x ↦ Subtype.ext (hfix x)
  have hr' : ∀ y : p'.range, r' y = y := fun y ↦ Subtype.ext (hfix' y)
  refine ⟨φ, φ', fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [hφ, hφ']
    change p ((E.symm (r' (p' (p' (E (r (p x)) : _))))) : _) = p x
    rw [hfix' (E (r (p x))), hfix' (E (r (p x))), hr', E.symm_apply_apply]
    change p (p (p x)) = p x
    rw [hp, hp]
  · rw [hφ, hφ']
    change p' ((E (r (p (p (E.symm (r' (p' y)) : _))))) : _) = p' y
    rw [hfix (E.symm (r' (p' y))), hfix (E.symm (r' (p' y))), hr, E.apply_symm_apply]
    change p' (p' (p' y)) = p' y
    rw [hp', hp']

include hA in
/-- **Composites of translation functors are determined by their value at a dominant Verma
module** (Humphreys, GSM 94, §10.8, Thm. 10.7; Kostant's multiplicity formula assumed). Let `λ` be
dominant, `I` the annihilator of `M(λ)`, and let `Θ = pr_{χ₂}(pr_{χ₁}(− ⊗ L₁) ⊗ L₁')`,
`Θ' = pr_{χ₂'}(pr_{χ₁'}(− ⊗ L₂) ⊗ L₂')` be composites of translation functors, realized as the
images of `translationIdem`. If `Θ M(λ) ≅ Θ' M(λ)`, a single natural transformation
`φ : − ⊗ (L₁ ⊗ L₁') → − ⊗ (L₂ ⊗ L₂')` gives, after projecting, a bijection `Θ M → Θ' M` at
every finitely generated `M ∈ 𝒪` in the block of `λ`. -/
theorem exists_bijOn_translationIdem {lam : Dual K H}
    (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    {I : TwoSidedIdeal (UniversalEnvelopingAlgebra K 𝔤)} (hM₀ : IsKilledBy I (VermaModule P lam))
    (hI : ∀ a, actionHom (R := K) (L := 𝔤) (VermaModule P lam) a = 0 → a ∈ I)
    (hK : KostantMultiplicity P (AdQuotient K 𝔤 I))
    {L₁ L₁' L₂ L₂' : Type (max u₁ u₂)} [AddCommGroup L₁] [Module K L₁] [LieRingModule 𝔤 L₁]
    [LieModule K 𝔤 L₁] [FiniteDimensional K L₁] [AddCommGroup L₁'] [Module K L₁']
    [LieRingModule 𝔤 L₁'] [LieModule K 𝔤 L₁'] [FiniteDimensional K L₁'] [AddCommGroup L₂]
    [Module K L₂] [LieRingModule 𝔤 L₂] [LieModule K 𝔤 L₂] [FiniteDimensional K L₂]
    [AddCommGroup L₂'] [Module K L₂'] [LieRingModule 𝔤 L₂'] [LieModule K 𝔤 L₂']
    [FiniteDimensional K L₂'] (hL₁ : IsCategoryO P L₁) (hL₁' : IsCategoryO P L₁')
    (hL₂ : IsCategoryO P L₂) (hL₂' : IsCategoryO P L₂') (χ₁ χ₂ χ₁' χ₂' : 𝓩 →ₐ[K] K)
    (hV : IsCategoryO P (VermaModule P lam))
    (E : (translationIdem P hL₁ hL₁' χ₁ χ₂ (VermaModule P lam) hV).range ≃ₗ⁅K,𝔤⁆
      (translationIdem P hL₂ hL₂' χ₁' χ₂' (VermaModule P lam) hV).range) :
    ∃ φ : TensorNatTrans.{0, max u₁ u₂, max u₁ u₂} K 𝔤 (L₁ ⊗[K] L₁') (L₂ ⊗[K] L₂'),
      ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
        [LieModule K 𝔤 M] (hM : IsCategoryO P M) (s : Finset M),
        LieSubmodule.lieSpan K 𝔤 (s : Set M) = ⊤ →
        (∀ μ, hM.multiplicity μ ≠ 0 → ∃ w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam,
          μ = P.weylDot hA.isGeneralizedCartan w lam) →
        Set.BijOn (fun x ↦ translationIdem P hL₂ hL₂' χ₁' χ₂' M hM (φ.app M x))
          (Set.range (translationIdem P hL₁ hL₁' χ₁ χ₂ M hM))
          (Set.range (translationIdem P hL₂ hL₂' χ₁' χ₂' M hM)) := by
  obtain ⟨φ, φ', h₁, h₂⟩ := exists_tensorNatTrans_of_equiv_verma P hA hlam hM₀ hI hK _ _
    (translationIdem_idempotent P hL₁ hL₁' χ₁ χ₂ _ hV)
    (translationIdem_idempotent P hL₂ hL₂' χ₁' χ₂' _ hV) E
  refine ⟨φ, fun M _ _ _ _ hM s hs hblock ↦ ?_⟩
  have hsV : LieSubmodule.lieSpan K 𝔤
      (({VermaModule.hwv P lam} : Finset (VermaModule P lam)) : Set (VermaModule P lam)) = ⊤ := by
    rw [Finset.coe_singleton]
    exact VermaModule.lieSpan_map_hwv_eq_top LieModuleHom.id Function.surjective_id
  obtain ⟨e, heM, heV⟩ := exists_tensorNatTrans_app_eq_translationIdem P hL₁ hL₁' χ₁ χ₂ hM hs hV
    hsV
  obtain ⟨e', he'M, he'V⟩ := exists_tensorNatTrans_app_eq_translationIdem P hL₂ hL₂' χ₁' χ₂' hM
    hs hV hsV
  have key := bijOn_range_of_block P hA hlam hM₀ hI e e' φ φ' (by rw [heV, he'V]; exact h₁)
    (by rw [heV, he'V]; exact h₂) hM hs hblock (by rw [heM]; exact fun x ↦ translationIdem_idempotent ..)
    (by rw [he'M]; exact fun y ↦ translationIdem_idempotent ..)
  rwa [heM, he'M] at key

end Matrix.Realization.KacMoodyAlgebra
