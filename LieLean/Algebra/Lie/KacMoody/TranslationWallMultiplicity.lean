/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationComposite
import LieLean.Algebra.Lie.KacMoody.TranslationWallHead

/-!
# Translation from a wall: multiplicities

In the setting of Humphreys, GSM 94, §7.14 (`λ`, `μ` antidominant, `μ♮` on the single wall `H_α`,
`⟨λ + ρ, α^∨⟩ ≠ 0`, every positive root orthogonal to `λ + ρ` orthogonal to `μ + ρ`,
`w ∈ W_[λ]` with `w α > 0`):

* `Matrix.Realization.KacMoodyAlgebra.stabilizerIndex_eq_two`: `|W_μ°/W_λ°| = 2`;
* `Matrix.Realization.KacMoodyAlgebra.character_translation_translation_irreducible_wall`:
  `ch T_λ^μ T_μ^λ L(w·μ) = 2 ch L(w·μ)` (the character form of 7.14 (1));
* `Matrix.Realization.KacMoodyAlgebra.multiplicity_translation_irreducible_wall`:
  `[T_μ^λ L(w·μ) : L(w·λ)] = 2` (Theorem 7.14 (d));
* `Matrix.Realization.KacMoodyAlgebra.translation_irreducible_eq_zero_of_multiplicity_ne_zero`:
  `T_λ^μ L(η) = 0` for every other composition factor `L(η)` of `T_μ^λ L(w·μ)` (Theorem 7.14 (f),
  second assertion).

## Proof of (d)

By the multiplicity formula, `2 = [T_λ^μ T_μ^λ L(w·μ) : L(w·μ)] = ∑_η [T_μ^λ L(w·μ) : L(η)]
[T_λ^μ L(η) : L(w·μ)]`, and by Theorem 7.9 (`translation_irreducible_wall`) the last factor is
`1` for `η = w·λ` and `0` for every other `η` linked to `λ`. Humphreys argues instead with the
semisimplicity of `T_λ^μ T_μ^λ L(w·μ)` and Exercise 7.7; the argument here is our own.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.14.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Generic

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V X : Type*}
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]

/-- If `ch X = n ch V`, then `[X : L(y)] = n [V : L(y)]`. -/
theorem IsCategoryO.multiplicity_eq_of_character_eq_nsmul (hX : IsCategoryO P X)
    (hV : IsCategoryO P V) (n : ℕ) (h : hX.character = n • hV.character) (y : Dual K H) :
    hX.multiplicity y = n * hV.multiplicity y := by
  rw [IsCategoryO.character_eq_sumIrreducibleCharacter,
    IsCategoryO.character_eq_sumIrreducibleCharacter, ← map_nsmul] at h
  have h1 := congrArg (fun c ↦ c.coeffAt y) (sumIrreducibleCharacter_injective h)
  have h2 : (n • hV.multiplicities).coeffAt y = n • hV.multiplicities.coeffAt y :=
    (congrFun (HahnSeries.coeff_nsmul (x := hV.multiplicities) (n := n)) _).trans
      (Pi.smul_apply _ _ _)
  rw [h2, IsCategoryO.coeffAt_multiplicities, IsCategoryO.coeffAt_multiplicities,
    nsmul_eq_mul] at h1
  exact_mod_cast h1

/-- A module in `𝒪` all of whose composition multiplicities vanish is zero. -/
theorem IsCategoryO.subsingleton_of_multiplicity_eq_zero (hV : IsCategoryO P V)
    (hm0 : ∀ y, hV.multiplicity y = 0) : Subsingleton V := by
  have hw : ∀ ξ, weightSpaceOfMap V (h P) ξ = ⊥ := fun ξ ↦ by
    have := hV.finiteDimensional_weightSpaceOfMap ξ
    have h0 := hV.finrank_weightSpace_eq_finsum ξ
    rw [finsum_eq_zero_of_forall_eq_zero fun μ ↦ by rw [hm0 μ, zero_mul]] at h0
    exact Submodule.finrank_eq_zero.mp h0
  refine ⟨fun a b ↦ ?_⟩
  have htop := hV.iSup_weightSpaceOfMap_eq_top
  simp only [hw, iSup_bot] at htop
  have ha : a ∈ (⊤ : Submodule K V) := trivial
  have hb : b ∈ (⊤ : Submodule K V) := trivial
  rw [← htop, Submodule.mem_bot] at ha hb
  rw [ha, hb]

end Generic

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

omit [IsAlgClosed K] in
include hA in
/-- On a single wall, `|W_μ°/W_λ°| = 2`: the weights `w'·λ`, `w'·μ = μ`, are `λ` and `s·λ`. -/
theorem stabilizerIndex_eq_two {lam μ : Dual K H}
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι}
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0) :
    stabilizerIndex P hA.isGeneralizedCartan lam μ = 2 := by
  classical
  have hA' := hA.isGeneralizedCartan
  set s := P.reflectionOf hA' v i with hs
  have hsμ : P.weylDot hA' s μ = μ := by
    simp only [weylDot, hs, reflectionOf_apply', hμα, zero_smul, sub_zero, add_sub_cancel_right]
  have hsl : P.weylDot hA' s lam ≠ lam := by
    intro h
    have h1 := congrArg (· + P.rho) h
    simp only [weylDot, sub_add_cancel, hs, reflectionOf_apply', sub_eq_self] at h1
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact hlamα h2
    · rw [LinearEquiv.map_eq_zero_iff] at h2
      exact P.linearIndependent_root.ne_zero i h2
  have hset : {y | ∃ w' : P.weylGroup hA', P.weylDot hA' w' μ = μ ∧ y = P.weylDot hA' w' lam} =
      ({lam, P.weylDot hA' s lam} : Finset (Dual K H)) := by
    ext y
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨w', hw', rfl⟩
      rcases eq_one_or_eq_of_weylDot_eq hA
          (fun v' i' h0 ↦ reflectionOf_eq_of_apply_root_eq hA (hwall v' i' h0)) hw' with rfl | rfl
      · left; simp [weylDot]
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨1, by simp [weylDot], by simp [weylDot]⟩
      · exact ⟨s, hsμ, rfl⟩
  rw [stabilizerIndex, hset, Finset.coe_sort_coe, Nat.card_eq_finsetCard,
    Finset.card_insert_of_notMem (by simpa using Ne.symm hsl), Finset.card_singleton]

include hA in
/-- **Translation from a wall and back on `L(w·μ)`, characters** (the character form of
Humphreys, GSM 94, 7.14 (1)): for `X ≅ T_μ^λ L(w·μ)`, `ch T_λ^μ X = 2 ch L(w·μ)`. -/
theorem character_translation_translation_irreducible_wall {lam μ ν ν' : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    (hν' : P.IsDominantIntegral ν') {z' : Dual K H ≃ₗ[K] Dual K H}
    (hz' : z' ∈ P.weylGroup hA.isGeneralizedCartan) (hzν' : z' (μ - lam) = ν')
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι}
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    (w : P.weylGroup hA.isGeneralizedCartan) {X : Type*} [AddCommGroup X] [Module K X]
    [LieRingModule P.KacMoodyAlgebra X] [LieModule K P.KacMoodyAlgebra X]
    (hX : IsCategoryO P X)
    (eX : X ≃ₗ⁅K,𝔤⁆ centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
      (centralCharacter P lam) (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ))) :
    (hX.centralTranslation P (IrreducibleModule.isCategoryO P ν') (centralCharacter P lam)
        (centralCharacter P μ)).character =
      2 • (IrreducibleModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan w μ)).character := by
  rw [← stabilizerIndex_eq_two P hA hμα hwall hlamα]
  exact character_translation_translation P hA hlam hμ hfacet hν hz hzν hν' hz' hzν'
    (IrreducibleModule.isCategoryO P _)
    ((VermaModule.centralCharacter_weyl P hA.isGeneralizedCartan w.property μ) ▸
      centralBlock_irreducible P (P.weylDot hA.isGeneralizedCartan w μ)) hX eX

open Classical in
include hA in
/-- **`[T_μ^λ L(w·μ) : L(w·λ)] = 2`** (Humphreys, GSM 94, Theorem 7.14 (d), arbitrary weights).
Let `λ`, `μ` be antidominant with every positive root orthogonal to `λ + ρ` orthogonal to
`μ + ρ`, `ν = z (λ - μ)` dominant integral, `α = v αᵢ > 0` with `⟨μ + ρ, α^∨⟩ = 0`, `±α` the only
roots orthogonal to `μ + ρ`, `⟨λ + ρ, α^∨⟩ ≠ 0`, and `w ∈ W_[λ]` with `w α > 0`. Then `L(w·λ)`
occurs exactly twice in `T_μ^λ L(w·μ) = pr_{χ_λ}(pr_{χ_μ} L(w·μ) ⊗ L(ν))`. -/
theorem multiplicity_translation_irreducible_wall {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    {w : P.weylGroup hA.isGeneralizedCartan} (hw : P.IsPosRoot hA.isGeneralizedCartan (w * v) i)
    (hwint : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam) :
    ((IrreducibleModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan w μ)).centralTranslation P
        (IrreducibleModule.isCategoryO P ν) (centralCharacter P μ)
        (centralCharacter P lam)).multiplicity (P.weylDot hA.isGeneralizedCartan w lam) = 2 := by
  classical
  have hA' := hA.isGeneralizedCartan
  -- the dual coefficient module `L(ν') ≅ L(ν)^*`, `ν' = z' (-ν)` dominant in `W (μ - λ)`
  obtain ⟨z', hz', hν', -⟩ := IrreducibleModule.exists_equiv_dual P hA hν
  have hzz : z' * z ∈ P.weylGroup hA' := mul_mem hz' hz
  have hzν' : (z' * z) (μ - lam) = z' (-ν) := by
    change z' (z (μ - lam)) = z' (-ν)
    rw [← hzν, ← map_neg, neg_sub]
  set ν' := z' (-ν)
  let a : Dual K H → ℕ := fun η ↦
    ((IrreducibleModule.isCategoryO P (P.weylDot hA' w μ)).centralTranslation P
      (IrreducibleModule.isCategoryO P ν) (centralCharacter P μ)
      (centralCharacter P lam)).multiplicity η
  let b : Dual K H → ℕ := fun η ↦
    ((IrreducibleModule.isCategoryO P η).centralTranslation P
      (IrreducibleModule.isCategoryO P ν') (centralCharacter P lam)
      (centralCharacter P μ)).multiplicity (P.weylDot hA' w μ)
  -- `∑_η a η b η = 2`
  have hsum : ∑ᶠ η, a η * b η = 2 := by
    have h := multiplicity_translation_translation_irreducible P hA hlam hμ hfacet hν hz hzν hν'
      hzz hzν' w (P.weylDot hA' w μ)
    rw [ite_eq_left rfl, stabilizerIndex_eq_two P hA hμα hwall hlamα] at h
    exact h
  -- `b η = δ_{η, w·λ}` for the composition factors `η` of `T_μ^λ L(w·μ)`
  have hb : ∀ η, a η ≠ 0 → b η = if η = P.weylDot hA' w lam then 1 else 0 := by
    intro η hη
    have hχ := centralCharacter_eq_of_multiplicity_centralTranslation_ne_zero P
      (IrreducibleModule.isCategoryO P _) (IrreducibleModule.isCategoryO P ν) _ _ hη
    obtain ⟨x, hx, hxe⟩ := (VermaModule.centralCharacter_eq_iff P hA lam η).mp hχ.symm
    have hηx : η = P.weylDot hA' ⟨x, hx⟩ lam := by rw [weylDot, hxe, add_sub_cancel_right]
    subst hηx
    have key := translation_irreducible_wall P hA hlam hμ hfacet hν' hzz hzν' hv hμα hwall hlamα
      hw hwint ⟨x, hx⟩
    by_cases hxw : P.weylDot hA' ⟨x, hx⟩ lam = P.weylDot hA' w lam
    · obtain ⟨e⟩ := key.1 hxw
      rw [ite_eq_left hxw]
      refine (multiplicity_centralTranslation_eq_of_equiv P (IrreducibleModule.isCategoryO P _)
        (IrreducibleModule.isCategoryO P ν') _ _ (IrreducibleModule.isCategoryO P _) e
          _).trans ?_
      rw [IrreducibleModule.multiplicity_eq, ite_eq_left rfl]
    · rw [ite_eq_right hxw]
      rcases key.2 hxw with hsub | ⟨y, hy, ⟨e⟩⟩
      · refine IsCategoryO.multiplicity_eq_zero_of_weightSpace_eq_bot _ ?_
        exact eq_bot_iff.mpr fun u _ ↦ (Submodule.mem_bot K).mpr (Subsingleton.elim u 0)
      · refine (multiplicity_centralTranslation_eq_of_equiv P (IrreducibleModule.isCategoryO P _)
          (IrreducibleModule.isCategoryO P ν') _ _ (IrreducibleModule.isCategoryO P _) e
            _).trans ?_
        rw [IrreducibleModule.multiplicity_eq, ite_eq_right (Ne.symm hy)]
  -- conclusion
  have hsum' : ∑ᶠ η, a η * b η = a (P.weylDot hA' w lam) := by
    rw [finsum_eq_single _ (P.weylDot hA' w lam) fun η hη ↦ ?_]
    · by_cases ha : a (P.weylDot hA' w lam) = 0
      · rw [ha, zero_mul]
      · rw [hb _ ha, ite_eq_left rfl, mul_one]
    · by_cases ha : a η = 0
      · rw [ha, zero_mul]
      · rw [hb η ha, ite_eq_right hη, mul_zero]
  exact hsum'.symm.trans hsum

include hA in
/-- **Composition factors of `T_μ^λ L(w·μ)` other than `L(w·λ)`** (Humphreys, GSM 94,
Theorem 7.14 (f), vanishing part, arbitrary weights). Under the hypotheses of
`multiplicity_translation_irreducible_wall`, let `T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν'))` with `ν'`
dominant integral in `W (μ - λ)`. If `x·λ ≠ w·λ` and `[T_μ^λ L(w·μ) : L(x·λ)] ≠ 0`, then
`T_λ^μ L(x·λ) = 0`. -/
theorem translation_irreducible_eq_zero_of_multiplicity_ne_zero {lam μ ν ν' : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hfacet : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    (hν' : P.IsDominantIntegral ν') {z' : Dual K H ≃ₗ[K] Dual K H}
    (hz' : z' ∈ P.weylGroup hA.isGeneralizedCartan) (hzν' : z' (μ - lam) = ν')
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hμα : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hwall : ∀ v' i', P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v' i' = 0 →
      (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∨
        (v' : Dual K H ≃ₗ[K] Dual K H) (P.root i') = -(v : Dual K H ≃ₗ[K] Dual K H) (P.root i))
    (hlamα : P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    {w : P.weylGroup hA.isGeneralizedCartan} (hw : P.IsPosRoot hA.isGeneralizedCartan (w * v) i)
    (hwint : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam)
    {η : Dual K H} (hηw : η ≠ P.weylDot hA.isGeneralizedCartan w lam)
    (hη : ((IrreducibleModule.isCategoryO P
        (P.weylDot hA.isGeneralizedCartan w μ)).centralTranslation P
          (IrreducibleModule.isCategoryO P ν) (centralCharacter P μ)
            (centralCharacter P lam)).multiplicity η ≠ 0) :
    Subsingleton (centralTranslation P (IrreducibleModule P ν') (centralCharacter P lam)
      (centralCharacter P μ) (IrreducibleModule P η)) := by
  classical
  have hA' := hA.isGeneralizedCartan
  have hX := (IrreducibleModule.isCategoryO P (P.weylDot hA' w μ)).centralTranslation P
    (IrreducibleModule.isCategoryO P ν) (centralCharacter P μ) (centralCharacter P lam)
  have hZν' : ∀ ν'', weightSpace P (IrreducibleModule P ν') ν'' ≠ ⊥ → ν'' ∈ cone P ν' :=
    fun _ h ↦ IrreducibleModule.mem_cone_of_weightSpace_ne_bot h
  -- `[T_λ^μ X : L(y)] = 2 δ_{w·μ, y}` for `X = T_μ^λ L(w·μ)`
  have hchar := character_translation_translation_irreducible_wall P hA hlam hμ hfacet hν hz hzν
    hν' hz' hzν' hμα hwall hlamα w hX LieModuleEquiv.refl
  have hm := fun y ↦ IsCategoryO.multiplicity_eq_of_character_eq_nsmul P _
    (IrreducibleModule.isCategoryO P (P.weylDot hA' w μ)) 2 hchar y
  -- `[X : L(w·λ)] = 2` (Theorem 7.14 (d)) and `T_λ^μ L(w·λ) ≅ L(w·μ)`
  have hd : hX.multiplicity (P.weylDot hA' w lam) = 2 :=
    multiplicity_translation_irreducible_wall P hA hlam hμ hfacet hν hz hzν hv hμα hwall hlamα
      hw hwint
  have hmη : hX.multiplicity η ≠ 0 := hη
  obtain ⟨e⟩ := (translation_irreducible_wall P hA hlam hμ hfacet hν' hz' hzν' hv hμα hwall hlamα
    hw hwint w).1 rfl
  let b : Dual K H → Dual K H → ℕ := fun η y ↦
    ((IrreducibleModule.isCategoryO P η).centralTranslation P
      (IrreducibleModule.isCategoryO P ν') (centralCharacter P lam)
      (centralCharacter P μ)).multiplicity y
  have hbw : b (P.weylDot hA' w lam) (P.weylDot hA' w μ) = 1 := by
    refine (multiplicity_centralTranslation_eq_of_equiv P (IrreducibleModule.isCategoryO P _)
      (IrreducibleModule.isCategoryO P ν') _ _ (IrreducibleModule.isCategoryO P _) e _).trans ?_
    rw [IrreducibleModule.multiplicity_eq, ite_eq_left rfl]
  -- abbreviations
  let c : Dual K H → ℕ := fun η' ↦ hX.multiplicity η'
  let l : Dual K H → ℕ := fun y ↦
    (IrreducibleModule.isCategoryO P (P.weylDot hA' w μ)).multiplicity y
  have hl : ∀ y, l y = if y = P.weylDot hA' w μ then 1 else 0 := fun y ↦
    IrreducibleModule.multiplicity_eq (P := P) _ y
  have hdc : c (P.weylDot hA' w lam) = 2 := hd
  have hmc : c η ≠ 0 := hmη
  -- every multiplicity of `T_λ^μ L(η)` vanishes
  refine IsCategoryO.subsingleton_of_multiplicity_eq_zero P
    ((IrreducibleModule.isCategoryO P η).centralTranslation P
      (IrreducibleModule.isCategoryO P ν') (centralCharacter P lam) (centralCharacter P μ))
    fun y ↦ ?_
  change b η y = 0
  by_contra hb
  have hfin := hX.finite_setOf_mem_cone (y - ν')
  have hmemH : ∀ η', y - ν' ∈ cone P η' → c η' ≠ 0 → η' ∈ hfin.toFinset :=
    fun η' hc h ↦ (Set.Finite.mem_toFinset _).mpr
      ⟨hc, hX.weightSpace_ne_bot_of_multiplicity_ne_zero h⟩
  have hA1 : (hX.centralTranslation P (IrreducibleModule.isCategoryO P ν')
      (centralCharacter P lam) (centralCharacter P μ)).multiplicity y =
      ∑ η' ∈ hfin.toFinset, c η' * b η' y :=
    multiplicity_centralTranslation_eq_finsetSum P hX (IrreducibleModule.isCategoryO P ν')
      (centralCharacter P lam) (centralCharacter P μ) hZν' hfin.toFinset hmemH
  have hsum : 2 * l y = ∑ η' ∈ hfin.toFinset, c η' * b η' y := (hm y).symm.trans hA1
  have hηH : η ∈ hfin.toFinset := hmemH η
    (mem_cone_of_multiplicity_centralTranslation_ne_zero P (IrreducibleModule.isCategoryO P ν')
      _ _ hZν' hb) hmc
  rw [← Finset.add_sum_erase _ _ hηH] at hsum
  have hpos := Nat.pos_of_ne_zero (mul_ne_zero hmc hb)
  by_cases hy : y = P.weylDot hA' w μ
  · subst hy
    have hbw0 : b (P.weylDot hA' w lam) (P.weylDot hA' w μ) ≠ 0 := by rw [hbw]; exact one_ne_zero
    have hwH : P.weylDot hA' w lam ∈ hfin.toFinset.erase η := Finset.mem_erase.mpr
      ⟨Ne.symm hηw, hmemH _ (mem_cone_of_multiplicity_centralTranslation_ne_zero P
        (IrreducibleModule.isCategoryO P ν') _ _ hZν' hbw0) (by rw [hdc]; exact two_ne_zero)⟩
    rw [← Finset.add_sum_erase _ _ hwH, hdc, hbw, hl, ite_eq_left rfl] at hsum
    omega
  · have hl0 : l y = 0 := (hl y).trans (ite_eq_right hy)
    have h3 := hsum.symm.trans (by rw [hl0])
    exact hpos.ne' (Nat.add_eq_zero_iff.mp h3).1

end Matrix.Realization.KacMoodyAlgebra
