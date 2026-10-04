/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationMultiplicity
import LieLean.Algebra.Lie.KacMoody.UpperClosure

/-!
# Translation of simple modules: the upper-closure criterion

Let `A` be of finite type, `K` algebraically closed of characteristic zero, `λ + ρ`, `μ + ρ`
antidominant integral with every simple wall of `λ + ρ` a wall of `μ + ρ` (`μ` lies in the
closure of the facet of `λ`), `ν = z (μ - λ)` dominant, and
`T = T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν))`. For `w ∈ W` (Humphreys, GSM 94, Theorem 7.9;
integral weights):

* `translation_irreducible_of_memUpperClosure`: if `w·μ` lies in the upper closure of the facet
  of `w·λ`, then `T L(w·λ) ≅ L(w·μ)`;
* `translation_irreducible_of_not_memUpperClosure`: otherwise `T L(w·λ) = 0`;
* `nonempty_equiv_translation_irreducible_iff`: `T L(w·λ) ≅ L(w·μ)` iff `w·μ` lies in the upper
  closure of the facet of `w·λ`.

## Proof

Write `a = λ + ρ`, `b = μ + ρ`, `x = w·λ`, `y = w·μ`. By `translation_irreducible`, `T L(w'·λ)`
is `0` or `L(w'·μ)` for every `w'`, and `T L(η) = 0` if `η ∉ W·λ` (linkage). Since `T` is exact
and `T M(x) ≅ M(y)`, counting the composition factor `L(y)` along a local composition series of
`M(x)` (`multiplicity_centralTranslation_eq_sum`) gives

`1 = [M(y) : L(y)] = ∑_η [M(x) : L(η)] [T L(η) : L(y)]`,

so exactly one composition factor `L(η)` of `M(x)` (counted with multiplicity) has
`T L(η) ≅ L(y)`; it has the form `η = w'·λ ≤ x` with `w' b = w b`.

* If the upper-closure condition holds at `w`, then `w a` is the least element of
  `{w' a | w' b = w b}` (`exists_apply_sub_eq_rootOf_of_upperClosureCondition`), so `η = x`.
* Otherwise a chain of reflections in positive roots orthogonal to `w b` leads from `w a` down
  to some `w'' a ≠ w a` at which the condition holds (`exists_upperClosureCondition`); each
  step is a Kac–Kazhdan step, so `[M(x) : L(w''·λ)] ≠ 0`
  (`VermaModule.multiplicity_ne_zero_iff_reflTransGen`), and `T L(w''·λ) ≅ L(y)` by the first
  case. As `[M(x) : L(x)] = 1`, the count forces `T L(x) = 0`.

The argument is reconstructed; it replaces the embedding `M(s_β·x) ↪ M(x)` of Humphreys' proof
by the Kac–Kazhdan theorem on composition factors and the Grothendieck-group count.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section KacKazhdan

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H)

/-- A reflection step `ξ ↦ ξ - ⟨ξ, β^∨⟩ β` in a positive real root `β` with `⟨ξ, β^∨⟩ ∈ ℤ_{>0}`
is a Kac–Kazhdan step for the weights `ξ - ρ`, `ξ' - ρ`. -/
theorem kacKazhdanStep_of_wallStep (S : A.Symmetrization) (hA : A.IsGeneralizedCartan)
    {η ξ ξ' : Dual K H} (h : P.WallStep hA η ξ ξ') :
    KacKazhdanStep P S (ξ - P.rho) (ξ' - P.rho) := by
  obtain ⟨v, hv, i, n, hpos, hn0, -, hn, rfl⟩ := h
  refine ⟨v (P.root i), hpos, (realRoots_subset_roots P hA ⟨v, hv, i, rfl⟩).2, n, hn0,
    by abel, ?_⟩
  have h1 : P.dualBilinForm S ξ (v (P.root i)) = (n : K) / S.ε i := by
    have := P.dualBilinForm_weylGroup hA S hv (v.symm ξ) (P.root i)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [this, P.dualBilinForm_root_right, hn]
  have h2 : P.dualBilinForm S (v (P.root i)) (v (P.root i)) = 2 / S.ε i := by
    rw [P.dualBilinForm_weylGroup hA S hv, P.dualBilinForm_root_right, P.root_coroot_self hA]
  rw [sub_add_cancel, h1, h2]
  ring

end KacKazhdan

section Lists

/-- Two distinct members of a list of natural-number-valued terms contribute to its sum. -/
theorem _root_.List.add_le_sum_map_of_mem_of_ne {α : Type*} {l : List α} {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) (f : α → ℕ) : f a + f b ≤ (l.map f).sum := by
  classical
  have h1 := (List.perm_cons_erase ha).map f
  have h2 := (List.perm_cons_erase ((List.mem_erase_of_ne hab.symm).mpr hb)).map f
  rw [h1.sum_eq, List.map_cons, List.sum_cons, h2.sum_eq, List.map_cons, List.sum_cons]
  omega

/-- If a list of natural numbers `f a`, `a ∈ l`, has sum `1`, some `f a` is nonzero. -/
theorem _root_.List.exists_mem_of_sum_map_eq_one {α : Type*} {l : List α} {f : α → ℕ}
    (h : (l.map f).sum = 1) : ∃ a ∈ l, f a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  rw [List.sum_eq_zero fun n hn ↦ by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
    exact hcon a ha] at h
  exact zero_ne_one h

end Lists

section Cone

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsFiniteCartan)

include hA in
/-- `y - ν ≤ w'·λ` when `w'·μ = y` and `ν = z (μ - λ)` is dominant: `y - w'·λ = w' (μ - λ)` is
a weight of `L(ν)`. -/
theorem weylDot_sub_mem_cone_weylDot {lam μ ν : Dual K H} (hν : P.IsDominantIntegral ν)
    {z : Dual K H ≃ₗ[K] Dual K H} (hz : z ∈ P.weylGroup hA.isGeneralizedCartan)
    (hzν : z (μ - lam) = ν) (w' : P.weylGroup hA.isGeneralizedCartan) :
    P.weylDot hA.isGeneralizedCartan w' μ - ν ∈
      cone P (P.weylDot hA.isGeneralizedCartan w' lam) := by
  obtain ⟨k, hk, hke⟩ := IrreducibleModule.mem_cone_of_weightSpace_ne_bot
    (IrreducibleModule.weightSpace_weylDot_sub_ne_bot hA hν hz hzν w')
  refine ⟨k, hk, ?_⟩
  rw [sub_eq_sub_iff_add_eq_add] at hke ⊢
  rw [hke, add_comm]

end Cone

section Translation

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- If `[T_λ^μ L(η) : L(y)] ≠ 0`, then `η = w'·λ` with `w'·μ = y`, and `T_λ^μ L(η) ≠ 0`. -/
theorem exists_weylDot_of_multiplicity_translation_ne_zero {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν) {η y : Dual K H}
    (h : ((IrreducibleModule.isCategoryO P η).centralTranslation P
      (IrreducibleModule.isCategoryO P ν) (centralCharacter P lam)
      (centralCharacter P μ)).multiplicity y ≠ 0) :
    ∃ w' : P.weylGroup hA.isGeneralizedCartan, η = P.weylDot hA.isGeneralizedCartan w' lam ∧
      P.weylDot hA.isGeneralizedCartan w' μ = y ∧
      ¬Subsingleton (centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ) (IrreducibleModule P η)) := by
  classical
  have hA' := hA.isGeneralizedCartan
  have hns : ¬Subsingleton (centralTranslation P (IrreducibleModule P ν)
      (centralCharacter P lam) (centralCharacter P μ) (IrreducibleModule P η)) := fun hs ↦
    h (IsCategoryO.multiplicity_eq_zero_of_weightSpace_eq_bot _
      (eq_bot_iff.mpr fun v _ ↦ (Submodule.mem_bot K).mpr (Subsingleton.elim v 0)))
  by_cases hχ : centralCharacter P η = centralCharacter P lam
  · obtain ⟨w', hw', hw'e⟩ := (VermaModule.centralCharacter_eq_iff P hA lam η).mp hχ.symm
    have hη : η = P.weylDot hA' ⟨w', hw'⟩ lam := by
      rw [weylDot, hw'e, add_sub_cancel_right]
    subst hη
    refine ⟨⟨w', hw'⟩, rfl, ?_, hns⟩
    rcases translation_irreducible P hA hlam hμ hfacet hν hz hzν ⟨w', hw'⟩ with hs | he
    · exact absurd hs hns
    · obtain ⟨e⟩ := he
      rw [← IsCategoryO.multiplicity_congr (IrreducibleModule.isCategoryO P _) _ e y,
        IrreducibleModule.multiplicity_eq] at h
      by_contra hne
      exact h (ite_eq_right fun hy ↦ hne hy.symm)
  · exfalso
    have hbot := centralBlock_irreducible_eq_bot P η (centralCharacter P lam) hχ
    refine h (IsCategoryO.multiplicity_eq_zero_of_weightSpace_eq_bot _
      (weightSpace_centralTranslation_eq_bot P (IrreducibleModule.isCategoryO P η)
        (IrreducibleModule.isCategoryO P ν) _ _
        (fun _ hw ↦ IrreducibleModule.mem_cone_of_weightSpace_ne_bot hw) fun μ' _ ↦
          eq_bot_iff.mpr fun v _ ↦ ?_))
    have hv : (v : IrreducibleModule P η) ∈
        (⊥ : LieSubmodule K P.KacMoodyAlgebra (IrreducibleModule P η)) := by
      rw [← hbot]
      exact v.2
    exact (Submodule.mem_bot K).mpr (Subtype.ext ((LieSubmodule.mem_bot _).mp hv))

include hA in
/-- The composition factor count for `T_λ^μ M(w·λ) ≅ M(w·μ)`: along a local composition series
of `M(w·λ)` for the weight `w·μ - ν`, `∑_η [T L(η) : L(w·μ)] = 1`. -/
private theorem sum_multiplicity_translation_eq_one {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan)
    {l : List (LieSubmodule K P.KacMoodyAlgebra
      (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam)) × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P (P.weylDot hA.isGeneralizedCartan w μ - ν) ⊥ l ⊤) :
    ((factorWeights l).map fun η ↦
      ((IrreducibleModule.isCategoryO P η).centralTranslation P
        (IrreducibleModule.isCategoryO P ν) (centralCharacter P lam)
        (centralCharacter P μ)).multiplicity
          (P.weylDot hA.isGeneralizedCartan w μ)).sum = 1 := by
  obtain ⟨e⟩ := translation_verma_equiv P hA hlam hμ hfacet hν hz hzν w
  rw [← multiplicity_centralTranslation_eq_sum P (VermaModule.isCategoryO P _)
    (IrreducibleModule.isCategoryO P ν) _ _
    (fun _ hw ↦ IrreducibleModule.mem_cone_of_weightSpace_ne_bot hw) hl,
    ← IsCategoryO.multiplicity_congr (VermaModule.isCategoryO P _) _ e,
    VermaModule.multiplicity_self]

include hA in
/-- **Translation of simple modules, nonvanishing.** Under the hypotheses of
`translation_verma`, if no positive root `β` with `⟨w(μ + ρ), β^∨⟩ = 0` has
`⟨w(λ + ρ), β^∨⟩ > 0`, then `T_λ^μ L(w·λ) ≅ L(w·μ)`. -/
theorem translation_irreducible_of_upperClosureCondition {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan)
    (hC : P.UpperClosureCondition hA.isGeneralizedCartan (w.val (lam + P.rho))
      (w.val (μ + P.rho))) :
    Nonempty (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ)
        (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) := by
  classical
  have hA' := hA.isGeneralizedCartan
  rcases translation_irreducible P hA hlam hμ hfacet hν hz hzν w with hsub | hne
  swap
  · exact hne
  exfalso
  obtain ⟨l, hl⟩ := (VermaModule.isCategoryO P
    (P.weylDot hA' w lam)).exists_isLocalCompositionSeries (P.weylDot hA' w μ - ν)
  have hsum := sum_multiplicity_translation_eq_one P hA hlam hμ hfacet hν hz hzν w hl
  -- some factor `L(η)` of `M(w·λ)` has `[T L(η) : L(w·μ)] ≠ 0`
  obtain ⟨η, hηl, hη0⟩ := List.exists_mem_of_sum_map_eq_one hsum
  obtain ⟨w', rfl, hw'y, hns⟩ := exists_weylDot_of_multiplicity_translation_ne_zero P hA hlam hμ
    hfacet hν hz hzν hη0
  -- `w'·λ ≤ w·λ`
  obtain ⟨k, hk, hke⟩ := VermaModule.mem_cone_of_multiplicity_ne_zero
    (((VermaModule.isCategoryO P (P.weylDot hA' w lam)).multiplicity_ne_zero_iff
      (hl.mem_cone_of_mem_factorWeights hηl) hl).mpr hηl)
  -- `w·λ ≤ w'·λ` by minimality
  have hb' : w'.val (μ + P.rho) = w.val (μ + P.rho) := by
    rw [← P.weylDot_add_rho hA' w' μ, ← P.weylDot_add_rho hA' w μ, hw'y]
  obtain ⟨c, hc, hce⟩ := P.exists_apply_sub_eq_rootOf_of_upperClosureCondition hA hlam hμ hC hb'
  have h0 : P.rootOf (c + k) = 0 := by
    rw [map_add, ← hce]
    simp only [weylDot] at hke
    linear_combination (norm := abel) hke
  have hck : c + k = 0 := P.rootOf_injective (by rw [h0, map_zero])
  have hk0 : k = 0 := by
    ext j
    have h1 := hc j
    have h2 := hk j
    have h3 := congrFun hck j
    simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 h3 ⊢
    omega
  rw [hk0, map_zero, sub_zero] at hke
  have hxy : P.weylDot hA' w' lam = P.weylDot hA' w lam := by
    exact hke
  rw [hxy] at hns
  exact hns hsub

include hA in
/-- **Translation of simple modules, vanishing.** Under the hypotheses of `translation_verma`,
if some positive root `β` with `⟨w(μ + ρ), β^∨⟩ = 0` has `⟨w(λ + ρ), β^∨⟩ > 0`, then
`T_λ^μ L(w·λ) = 0`. -/
theorem translation_irreducible_of_not_upperClosureCondition {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan)
    (hC : ¬P.UpperClosureCondition hA.isGeneralizedCartan (w.val (lam + P.rho))
      (w.val (μ + P.rho))) :
    Subsingleton (centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
      (centralCharacter P μ)
      (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) := by
  classical
  have hA' := hA.isGeneralizedCartan
  -- descend to `w''` satisfying the condition
  obtain ⟨w'', hw''b, hw''U, hchain⟩ := P.exists_upperClosureCondition hA'
    (a := lam + P.rho) (b := μ + P.rho) hlam w
  have hy : P.weylDot hA' w'' μ = P.weylDot hA' w μ := by
    simp only [weylDot, hw''b]
  have hne : P.weylDot hA' w lam ≠ P.weylDot hA' w'' lam := by
    intro h
    have h' : w''.val (lam + P.rho) = w.val (lam + P.rho) := by
      rw [← P.weylDot_add_rho hA' w'' lam, ← P.weylDot_add_rho hA' w lam, h]
    exact hC (h' ▸ hw''U)
  obtain ⟨e''⟩ := translation_irreducible_of_upperClosureCondition P hA hlam hμ hfacet hν hz hzν
    w'' (by rw [hw''b]; exact hw''U)
  -- `L(w''·λ)` is a composition factor of `M(w·λ)`
  obtain ⟨d, hdpos, hpos⟩ := hA.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hpos.isHermitian
  have hKK : (VermaModule.isCategoryO P (P.weylDot hA' w lam)).multiplicity
      (P.weylDot hA' w'' lam) ≠ 0 :=
    (VermaModule.multiplicity_ne_zero_iff_reflTransGen P
      (Symmetrization.ofDiagonal d hdpos hsymm) hA' _ _).mpr
      (Relation.ReflTransGen.lift (fun ξ ↦ ξ - P.rho)
        (fun _ _ h ↦ kacKazhdanStep_of_wallStep P _ hA' h) _ _ hchain)
  -- the count along a local composition series
  obtain ⟨l, hl⟩ := (VermaModule.isCategoryO P
    (P.weylDot hA' w lam)).exists_isLocalCompositionSeries (P.weylDot hA' w μ - ν)
  have hsum := sum_multiplicity_translation_eq_one P hA hlam hμ hfacet hν hz hzν w hl
  have hx : P.weylDot hA' w lam ∈ factorWeights l :=
    ((VermaModule.isCategoryO P (P.weylDot hA' w lam)).multiplicity_ne_zero_iff
      (weylDot_sub_mem_cone_weylDot P hA hν hz hzν w) hl).mp (by
        rw [VermaModule.multiplicity_self]
        exact one_ne_zero)
  have hx'' : P.weylDot hA' w'' lam ∈ factorWeights l :=
    ((VermaModule.isCategoryO P (P.weylDot hA' w lam)).multiplicity_ne_zero_iff
      (hy ▸ weylDot_sub_mem_cone_weylDot P hA hν hz hzν w'') hl).mp hKK
  have hle := List.add_le_sum_map_of_mem_of_ne hx hx'' hne fun η ↦
    ((IrreducibleModule.isCategoryO P η).centralTranslation P
      (IrreducibleModule.isCategoryO P ν) (centralCharacter P lam)
      (centralCharacter P μ)).multiplicity (P.weylDot hA' w μ)
  rw [hsum, ← IsCategoryO.multiplicity_congr (IrreducibleModule.isCategoryO P _) _ e'',
    IrreducibleModule.multiplicity_eq, ite_eq_left hy.symm] at hle
  rcases translation_irreducible P hA hlam hμ hfacet hν hz hzν w with hsub | he
  · exact hsub
  · obtain ⟨e⟩ := he
    exfalso
    rw [← IsCategoryO.multiplicity_congr (IrreducibleModule.isCategoryO P _) _ e,
      IrreducibleModule.multiplicity_eq, ite_eq_left rfl] at hle
    omega

include hA in
/-- **Translation of simple modules** (Humphreys, GSM 94, Theorem 7.9; integral weights,
finite type, algebraically closed field of characteristic zero). Under the hypotheses of
`translation_verma`, if `w·μ` lies in the upper closure of the facet of `w·λ`, then
`T_λ^μ L(w·λ) ≅ L(w·μ)`. -/
theorem translation_irreducible_of_memUpperClosure {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan)
    (hU : P.MemUpperClosure hA.isGeneralizedCartan (P.weylDot hA.isGeneralizedCartan w lam)
      (P.weylDot hA.isGeneralizedCartan w μ)) :
    Nonempty (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ)
        (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) :=
  translation_irreducible_of_upperClosureCondition P hA hlam hμ hfacet hν hz hzν w
    ((P.memUpperClosure_weylDot_iff hA.isGeneralizedCartan hlam hμ hfacet w).mp hU)

include hA in
/-- **Translation of simple modules** (Humphreys, GSM 94, Theorem 7.9; integral weights,
finite type, algebraically closed field of characteristic zero). Under the hypotheses of
`translation_verma`, if `w·μ` does not lie in the upper closure of the facet of `w·λ`, then
`T_λ^μ L(w·λ) = 0`. -/
theorem translation_irreducible_of_not_memUpperClosure {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan)
    (hU : ¬P.MemUpperClosure hA.isGeneralizedCartan (P.weylDot hA.isGeneralizedCartan w lam)
      (P.weylDot hA.isGeneralizedCartan w μ)) :
    Subsingleton (centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
      (centralCharacter P μ)
      (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) :=
  translation_irreducible_of_not_upperClosureCondition P hA hlam hμ hfacet hν hz hzν w fun hC ↦
    hU ((P.memUpperClosure_weylDot_iff hA.isGeneralizedCartan hlam hμ hfacet w).mpr hC)

include hA in
/-- **The upper-closure criterion** (Humphreys, GSM 94, Theorem 7.9; integral weights,
finite type, algebraically closed field of characteristic zero). Under the hypotheses of
`translation_verma`, `T_λ^μ L(w·λ) ≅ L(w·μ)` iff `w·μ` lies in the upper closure of the facet of
`w·λ`; otherwise `T_λ^μ L(w·λ) = 0` (`translation_irreducible_of_not_memUpperClosure`). -/
theorem nonempty_equiv_translation_irreducible_iff {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    Nonempty (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (IrreducibleModule P ν) (centralCharacter P lam)
        (centralCharacter P μ)
        (IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w lam))) ↔
      P.MemUpperClosure hA.isGeneralizedCartan (P.weylDot hA.isGeneralizedCartan w lam)
        (P.weylDot hA.isGeneralizedCartan w μ) := by
  refine ⟨fun ⟨e⟩ ↦ ?_,
    translation_irreducible_of_memUpperClosure P hA hlam hμ hfacet hν hz hzν w⟩
  by_contra hU
  have hs := translation_irreducible_of_not_memUpperClosure P hA hlam hμ hfacet hν hz hzν w hU
  exact IrreducibleModule.hwv_ne_zero P _ (e.injective (Subsingleton.elim _ _))

end Translation

end Matrix.Realization.KacMoodyAlgebra
