/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationWallMultiplicity

/-!
# Translation from a wall: the factor `L(ws·λ)`

In the setting of Humphreys, GSM 94, §7.14 (`λ`, `μ` antidominant, `μ♮` on the single wall `H_α`,
`⟨λ + ρ, α^∨⟩ ≠ 0`, every positive root orthogonal to `λ + ρ` orthogonal to `μ + ρ`,
`w ∈ W_[λ]` with `w α > 0`), `L(ws·λ)` occurs exactly once in `T_μ^λ L(w·μ)` (Theorem 7.14 (e):
`Matrix.Realization.KacMoodyAlgebra.multiplicity_translation_irreducible_wall_reflection`).

## Proof

Write `a = w·λ < b = ws·λ`, `X = T_μ^λ M(w·μ)`, `Y = T_μ^λ L(w·μ)` and `π : X → Y` for the
translation of `M(w·μ) → L(w·μ)`. By Theorem 7.14 (a), `0 → M(b) → X → M(a) → 0` is exact, so
`X_b` is spanned by the image `v` of the highest weight vector of `M(b)` and every weight of `X`,
hence of `Y`, is `≤ b`; therefore `[Y : L(b)] = dim Y_b ≤ 1`. If `π v = 0`, then `π` kills `M(b)`,
`Y_a` is spanned by the image of a lift of the highest weight vector of `M(a)`, and
`[Y : L(a)] ≤ dim Y_a ≤ 1`, contradicting Theorem 7.14 (d). This is Humphreys' argument, phrased
with weight spaces.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.14.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Generic

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)
  {X Y : Type*}
  [AddCommGroup X] [Module K X] [LieRingModule P.KacMoodyAlgebra X]
  [LieModule K P.KacMoodyAlgebra X]
  [AddCommGroup Y] [Module K Y] [LieRingModule P.KacMoodyAlgebra Y]
  [LieModule K P.KacMoodyAlgebra Y]

local notation "𝔤" => KacMoodyAlgebra P

omit [Fintype ι] [DecidableEq ι] in
/-- The span of one vector has dimension at most one. -/
lemma finrank_span_singleton_le_one {M : Type*} [AddCommGroup M] [Module K M] (u : M) :
    finrank K (K ∙ u) ≤ 1 :=
  (finrank_span_le_card ({u} : Set M)).trans (by simp)

/-- A surjective morphism out of a sum of weight spaces is surjective on each weight space. -/
theorem exists_mem_weightSpace_of_surjective (hX : ⨆ μ, weightSpaceOfMap X (h P) μ = ⊤)
    (g : X →ₗ⁅K,𝔤⁆ Y) (hg : Function.Surjective g) {μ : Dual K H} {y : Y}
    (hy : y ∈ weightSpaceOfMap Y (h P) μ) : ∃ x ∈ weightSpaceOfMap X (h P) μ, g x = y := by
  have hle : ∀ ν, (weightSpaceOfMap X (h P) ν).map (g : X →ₗ[K] Y) ≤
      weightSpaceOfMap Y (h P) ν := fun ν ↦ by
    rintro _ ⟨v, hv, rfl⟩
    exact map_mem_weightSpaceOfMap P g hv
  obtain ⟨x, hx, hxy⟩ := mem_of_mem_iSup_of_le (h P) _ hle hy (by
    rw [← Submodule.map_iSup, hX, Submodule.map_top, LinearMap.range_eq_top.mpr hg]
    trivial)
  exact ⟨x, hx, hxy⟩

/-- An injective morphism reflects weight vectors. -/
theorem mem_weightSpace_of_injective (f : X →ₗ⁅K,𝔤⁆ Y) (hf : Function.Injective f)
    {μ : Dual K H} {x : X} (hx : f x ∈ weightSpaceOfMap Y (h P) μ) :
    x ∈ weightSpaceOfMap X (h P) μ := fun a ↦ hf (by
  rw [LieModuleHom.map_lie, hx a, map_smul])

variable [CharZero K]

/-- At a weight `b` above all weights of `Y`, `[Y : L(b)] = dim Y_b`. -/
theorem IsCategoryO.multiplicity_eq_finrank_of_forall_mem_cone (hY : IsCategoryO P Y)
    {b : Dual K H} (hmax : ∀ μ, weightSpace P Y μ ≠ ⊥ → μ ∈ cone P b) :
    hY.multiplicity b = finrank K (weightSpace P Y b) := by
  rw [hY.finrank_weightSpace_eq_finsum b, finsum_eq_single _ b fun μ hμ ↦ ?_,
    IrreducibleModule.finrank_weightSpace_self, mul_one]
  by_contra hne
  have h1 := hmax μ (hY.weightSpace_ne_bot_of_multiplicity_ne_zero (left_ne_zero_of_mul hne))
  have h2 := IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero (right_ne_zero_of_mul hne)
  exact hμ (eq_of_mem_cone_of_mem_cone h1 h2)

/-- **The top Verma factor of an extension survives in a quotient** (the argument of Humphreys,
GSM 94, 7.14 (e)). Let `0 → M(b) → X → M(a) → 0` be exact (`f`, `g`) with `a < b`, and let
`π : X → Y` be surjective with `[Y : L(a)] ≥ 2`. Then `[Y : L(b)] = 1`. -/
theorem IsCategoryO.multiplicity_eq_one_of_extension (hX : IsCategoryO P X)
    (hY : IsCategoryO P Y) {a b : Dual K H} (hba : b ∉ cone P a) (hab : a ∈ cone P b)
    (f : VermaModule P b →ₗ⁅K,𝔤⁆ X) (hf : Function.Injective f)
    (g : X →ₗ⁅K,𝔤⁆ VermaModule P a) (hg : Function.Surjective g)
    (hker : ∀ x, g x = 0 → ∃ m, f m = x) (π : X →ₗ⁅K,𝔤⁆ Y) (hπ : Function.Surjective π)
    (hd : 1 < hY.multiplicity a) : hY.multiplicity b = 1 := by
  classical
  have hXd := hX.iSup_weightSpaceOfMap_eq_top
  have := hY.finiteDimensional_weightSpaceOfMap a
  have := hY.finiteDimensional_weightSpaceOfMap b
  have hvb : f (VermaModule.hwv P b) ∈ weightSpaceOfMap X (h P) b :=
    map_mem_weightSpaceOfMap P f (VermaModule.hwv_mem_weightSpace P b)
  -- `X_b = K f(v_b)`
  have hXb : ∀ x ∈ weightSpaceOfMap X (h P) b, ∃ c : K, x = c • f (VermaModule.hwv P b) := by
    intro x hx
    have hgx : g x ∈ weightSpaceOfMap (VermaModule P a) (h P) b :=
      map_mem_weightSpaceOfMap P g hx
    rw [show weightSpaceOfMap (VermaModule P a) (h P) b = ⊥ from
      VermaModule.weightSpace_eq_bot P a fun k hk hbk ↦ hba ⟨k, hk, hbk⟩] at hgx
    obtain ⟨m, rfl⟩ := hker x ((Submodule.mem_bot K).mp hgx)
    have hm := mem_weightSpace_of_injective P f hf hx
    rw [show weightSpaceOfMap (VermaModule P b) (h P) b = K ∙ VermaModule.hwv P b from
      VermaModule.weightSpace_self P b] at hm
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
    exact ⟨c, by rw [map_smul]⟩
  -- the weights of `Y` are `≤ b`
  have hmax : ∀ ξ, weightSpace P Y ξ ≠ ⊥ → ξ ∈ cone P b := by
    intro ξ hξ
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hξ
    obtain ⟨x, hx, rfl⟩ := exists_mem_weightSpace_of_surjective P hXd π hπ hy
    have hx0 : x ≠ 0 := fun h0 ↦ hy0 (by rw [h0, map_zero])
    by_cases hgx : g x = 0
    · obtain ⟨m, rfl⟩ := hker x hgx
      have hm := mem_weightSpace_of_injective P f hf hx
      have hm0 : m ≠ 0 := fun h0 ↦ hx0 (by rw [h0, map_zero])
      obtain ⟨k, hk, hke⟩ := VermaModule.exists_eq_sub_of_mem_weightSpace P b LieModuleHom.id
        Function.surjective_id hm hm0
      exact ⟨k, hk, hke⟩
    · obtain ⟨k, hk, hke⟩ := VermaModule.exists_eq_sub_of_mem_weightSpace P a LieModuleHom.id
        Function.surjective_id (map_mem_weightSpaceOfMap P g hx) hgx
      exact mem_cone_trans ⟨k, hk, hke⟩ hab
  rw [hY.multiplicity_eq_finrank_of_forall_mem_cone P hmax]
  -- `Y_b ⊆ K π(f(v_b))`
  have hle : weightSpace P Y b ≤ K ∙ π (f (VermaModule.hwv P b)) := fun y hy ↦ by
    obtain ⟨x, hx, rfl⟩ := exists_mem_weightSpace_of_surjective P hXd π hπ hy
    obtain ⟨c, rfl⟩ := hXb x hx
    rw [map_smul]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  -- `π(f(v_b)) ≠ 0`, otherwise `Y_a` is spanned by one vector and `[Y : L(a)] ≤ 1`
  have hπv : π (f (VermaModule.hwv P b)) ≠ 0 := by
    intro h0
    have hπf : ∀ m, π (f m) = 0 := by
      have hφ : π.comp f = 0 := (VermaModule.eq_zero_iff P (π.comp f)).mpr h0
      exact fun m ↦ LieModuleHom.congr_fun hφ m
    obtain ⟨x₀, -, hgx₀⟩ := exists_mem_weightSpace_of_surjective P hXd g hg
      (VermaModule.hwv_mem_weightSpace P a)
    have hYa : weightSpace P Y a ≤ K ∙ π x₀ := fun y hy ↦ by
      obtain ⟨x, hx, rfl⟩ := exists_mem_weightSpace_of_surjective P hXd π hπ hy
      have hgx : g x ∈ K ∙ VermaModule.hwv P a := by
        rw [← show weightSpaceOfMap (VermaModule P a) (h P) a = K ∙ VermaModule.hwv P a from
          VermaModule.weightSpace_self P a]
        exact map_mem_weightSpaceOfMap P g hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgx
      obtain ⟨m, hm⟩ := hker (x - c • x₀) (by rw [map_sub, map_smul, hgx₀, hc, sub_self])
      have : π x = c • π x₀ := by
        rw [← map_smul, ← sub_eq_zero, ← map_sub, ← hm, hπf]
      rw [this]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
    have h1 := hY.multiplicity_le_finrank a
    have h2 : finrank K (weightSpace P Y a) ≤ 1 :=
      (Submodule.finrank_mono hYa).trans (finrank_span_singleton_le_one _)
    omega
  refine le_antisymm ((Submodule.finrank_mono hle).trans (finrank_span_singleton_le_one _)) ?_
  refine Nat.one_le_iff_ne_zero.mpr fun h0 ↦ hπv ?_
  have hmem : π (f (VermaModule.hwv P b)) ∈ weightSpace P Y b := map_mem_weightSpaceOfMap P π hvb
  rw [Submodule.finrank_eq_zero.mp h0] at hmem
  exact (Submodule.mem_bot K).mp hmem

end Generic

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- **`[T_μ^λ L(w·μ) : L(ws·λ)] = 1`** (Humphreys, GSM 94, Theorem 7.14 (e), arbitrary weights).
Under the hypotheses of `multiplicity_translation_irreducible_wall`, `L(ws·λ)` occurs exactly once
in `T_μ^λ L(w·μ) = pr_{χ_λ}(pr_{χ_μ} L(w·μ) ⊗ L(ν))`, `s = s_α`. -/
theorem multiplicity_translation_irreducible_wall_reflection {lam μ ν : Dual K H}
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
    ((IrreducibleModule.isCategoryO P
        (P.weylDot hA.isGeneralizedCartan w μ)).centralTranslation P
          (IrreducibleModule.isCategoryO P ν) (centralCharacter P μ)
            (centralCharacter P lam)).multiplicity
        (P.weylDot hA.isGeneralizedCartan (w * P.reflectionOf hA.isGeneralizedCartan v i) lam) =
      1 := by
  classical
  have hA' := hA.isGeneralizedCartan
  set a := P.weylDot hA' w lam with ha
  set b := P.weylDot hA' (w * P.reflectionOf hA' v i) lam with hb
  -- `a < b`
  have hint := integral_sub_of_apply_eq hA hν hz hzν
  obtain ⟨n, hn⟩ := (P.isIntegralRoot_congr _ hint v i).mpr ⟨0, by rw [Int.cast_zero]; exact hμα⟩
  change P.corootPairing _ (lam + P.rho) v i = n at hn
  have hn0 : n < 0 := lt_of_le_of_ne (hlam v i hv n hn)
    (by rintro rfl; exact hlamα (by simp [hn]))
  have hba : b ∉ cone P a := weylDot_mul_reflectionOf_notMem_cone hA hn0 hn hw
  have hab : a ∈ cone P b := by
    obtain ⟨l, hl, hwl⟩ := hw
    refine ⟨(-n) • l, smul_nonneg (by omega) hl, ?_⟩
    simp only [ha, hb, weylDot]
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, reflectionOf_apply', hn, map_sub, map_smul,
      ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hwl, map_zsmul, ← Int.cast_smul_eq_zsmul K]
    push_cast
    module
  -- the short exact sequence `0 → M(b) → T → M(a) → 0` (Theorem 7.14 (a))
  have hMχ : centralBlock P (VermaModule P (P.weylDot hA' w μ)) (centralCharacter P μ) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' w.property μ) ▸
      centralBlock_verma P (P.weylDot hA' w μ)
  obtain ⟨S, hS, ⟨eS⟩, ⟨eQ⟩⟩ := translation_verma_shortExact_of_isAntidominant hA hlam hμ hν hz
    hzν hv hμα hwall hlamα hw
  let T := centralBlock P (VermaModule P (P.weylDot hA' w μ) ⊗[K] IrreducibleModule P ν)
    (centralCharacter P lam)
  have hT := ((VermaModule.isCategoryO P (P.weylDot hA' w μ)).tensorProduct
    (IrreducibleModule.isCategoryO P ν)).lieSubmodule T
  let f : VermaModule P b →ₗ⁅K,𝔤⁆ T := (LieSubmodule.inclusion hS).comp eS.toLieModuleHom
  let qT : T →ₗ⁅K,𝔤⁆ T.map (LieSubmodule.Quotient.mk' S) :=
    LieModuleHom.codRestrict _ ((LieSubmodule.Quotient.mk' S).comp T.incl)
      (fun t ↦ (LieSubmodule.mem_map _).mpr ⟨t, t.2, rfl⟩)
  let g : T →ₗ⁅K,𝔤⁆ VermaModule P a := eQ.symm.toLieModuleHom.comp qT
  have hf : Function.Injective f := fun m m' hmm ↦
    eS.injective (LieSubmodule.inclusion_injective hS hmm)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨t, ht, hte⟩ := (LieSubmodule.mem_map _).mp (eQ y).2
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [g, LieModuleHom.comp_apply, LieModuleEquiv.coe_toLieModuleHom]
    rw [LieModuleEquiv.symm_apply_eq]
    exact Subtype.ext hte
  have hker : ∀ x, g x = 0 → ∃ m, f m = x := by
    intro x hx
    have h1 : qT x = 0 := by
      have := congrArg eQ hx
      simp only [g, LieModuleHom.comp_apply, LieModuleEquiv.coe_toLieModuleHom,
        LieModuleEquiv.apply_symm_apply, map_zero] at this
      exact this
    have h2 : x.1 ∈ S := (LieSubmodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val h1)
    exact ⟨eS.symm ⟨x.1, h2⟩, Subtype.ext (by simp [f])⟩
  -- `π : T ≅ T_μ^λ M(w·μ) → T_μ^λ L(w·μ)`
  let e := centralBlockEquiv P (rTensorEquiv P (IrreducibleModule P ν)
    (equivCentralBlockOfEqTop P hMχ)) (centralCharacter P lam)
  let π := (centralTranslationMap P (IrreducibleModule P ν) (centralCharacter P μ)
    (centralCharacter P lam) (LieSubmodule.Quotient.mk' (VermaModule.maxSubmodule P
      (P.weylDot hA' w μ)))).comp e.symm.toLieModuleHom
  have hπ : Function.Surjective π := (centralTranslationMap_surjective P
    (VermaModule.isCategoryO P _) (IrreducibleModule.isCategoryO P ν) _ _ _
    (LieSubmodule.Quotient.surjective_mk' _)).comp e.symm.surjective
  have hd := multiplicity_translation_irreducible_wall P hA hlam hμ hfacet hν hz hzν hv hμα hwall
    hlamα hw hwint
  exact IsCategoryO.multiplicity_eq_one_of_extension P hT _ hba hab f hf g hg hker π hπ
    (by rw [hd]; norm_num)

end Matrix.Realization.KacMoodyAlgebra
