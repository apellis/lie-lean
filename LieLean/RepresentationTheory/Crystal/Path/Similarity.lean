/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Extremal
import LieLean.RepresentationTheory.Crystal.Path.ConcatIsomorphism
import LieLean.RepresentationTheory.Crystal.Path.Decomposition
import LieLean.RepresentationTheory.Crystal.Path.GluingPause
import LieLean.RepresentationTheory.Crystal.Path.LittelmannIsomorphism

/-!
# Similarity data for Littelmann's path crystals

For a dominant integral weight `Λ` of a realization over `ℝ`, Littelmann's path crystal `B(Λ)`
carries the data of Kashiwara's comparison argument (`Crystal.SimilarityData`, [Kas96] §4):

* stretching `π ↦ mπ` is an `m`-similarity of integral paths ([Lit95] Lemma 2.4,
  `LSGeneralClass.fIter_stretch`), sending `π_Λ` to `π_{mΛ}`;
* `π_{mΛ}` is the concatenation of `m` copies of `π_Λ` (with suitable split times), and
  concatenation is a strict embedding of `B(Λ)^{⊗m}` into the crystal of all paths ([Lit95] §2);

so stretching factors through an `m`-similarity `B(Λ) → B(Λ)^{⊗m}` sending `π_Λ` to
`π_Λ ⊗ ⋯ ⊗ π_Λ` (`Matrix.Realization.pathSimilarityData`).

## Main definitions

* `LittelmannPath.concatHomOf`: concatenation of two strict morphisms into the path crystal with
  integral images.
* `Matrix.Realization.concatPow`: the strict embedding `B(Λ)^{⊗(n+1)} → {paths}`,
  `η₁ ⊗ ⋯ ⊗ η_{n+1} ↦ η₁ * (η₂ * ⋯)` (reparametrized), with `π_Λ^{⊗(n+1)} ↦ π_{(n+1)Λ}`.
* `Matrix.Realization.stretchSimilarity`: stretching as an `N`-similarity
  `B(Λ) → {paths}`.
* `Matrix.Realization.pathSimilarityData`: the similarity data of `B(Λ)`.

## References

* [Kas96] M. Kashiwara, *Similarity of crystal bases*, Contemp. Math. 194 (1996), 177–186, §4.
* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. (2)
  142 (1995), 499–525, §2.
-/

open Set Module LittelmannPath

/-! ### Concatenation of strict morphisms -/

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [FloorRing 𝕜]
  {D : CartanDatum ι X} {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}
  {B₁ B₂ : Type*} {C₁ : Crystal D B₁} {C₂ : Crystal D B₂}

/-- The concatenation `b₁ ⊗ b₂ ↦ ψ₁(b₁) * ψ₂(b₂)` of two strict morphisms into the path crystal
with integral images is a strict morphism ([Lit95] §2, `LittelmannPath.e_concat_eq_tensor`). -/
noncomputable def concatHomOf (ψ₁ : Crystal.StrictHom C₁ (crystal S))
    (ψ₂ : Crystal.StrictHom C₂ (crystal S)) (h₁ : ∀ b, (ψ₁ b).IsIntegral)
    (h₂ : ∀ b, (ψ₂ b).IsIntegral) : Crystal.StrictHom (C₁.tensor C₂) (crystal S) where
  toFun p := (ψ₁ p.1).concat (ψ₂ p.2)
  wt_map p := by
    change (ψ₁ p.1).wt + (ψ₂ p.2).wt = _
    rw [← crystal_wt, ← crystal_wt, ψ₁.wt_apply, ψ₂.wt_apply]
    rfl
  ε_map i p := by
    rw [crystal_ε, ε_concat, ← crystal_ε, ← crystal_ε, ψ₁.ε_apply, ψ₂.ε_apply, ← crystal_wt,
      ψ₁.wt_apply]
    rfl
  e_map i p := by
    rw [crystal_e, e_concat_eq_tensor (h₁ p.1) (h₂ p.2)]
    have h := (ψ₁.tensorMap ψ₂).e_apply i p
    rw [show ((ψ₁ p.1, ψ₂ p.2) : LittelmannPath S × LittelmannPath S) =
      ψ₁.tensorMap ψ₂ p from rfl, h, Option.map_map]
    rfl
  f_map i p := by
    rw [crystal_f, f_concat_eq_tensor (h₁ p.1) (h₂ p.2)]
    have h := (ψ₁.tensorMap ψ₂).f_apply i p
    rw [show ((ψ₁ p.1, ψ₂ p.2) : LittelmannPath S × LittelmannPath S) =
      ψ₁.tensorMap ψ₂ p from rfl, h, Option.map_map]
    rfl

@[simp] lemma concatHomOf_apply (ψ₁ : Crystal.StrictHom C₁ (crystal S))
    (ψ₂ : Crystal.StrictHom C₂ (crystal S)) (h₁ : ∀ b, (ψ₁ b).IsIntegral)
    (h₂ : ∀ b, (ψ₂ b).IsIntegral) (p : B₁ × B₂) :
    concatHomOf ψ₁ ψ₂ h₁ h₂ p = (ψ₁ p.1).concat (ψ₂ p.2) := rfl

end LittelmannPath

namespace Matrix.Realization

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H] {A : Matrix ι ι ℤ}
  {P : Realization A ℝ H} (hA : A.IsGeneralizedCartan) {Λ : Dual ℝ H}
  (hΛ : P.IsDominantIntegral Λ)

/-! ### Straight lines as concatenations -/

lemma one_div_lt_one (n : ℕ) : 1 / ((n : ℝ) + 2) < 1 := by
  rw [div_lt_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

lemma straightLine_apply_nsmul (k : ℕ) (x : P.integralWeights) (t : ℝ) :
    straightLine (P.pathSpace hA) (k • x) t = max 0 (min 1 t) • ((k : ℝ) • (x : Dual ℝ H)) := by
  rw [straightLine_apply, pathSpace_embed, AddSubgroup.coe_nsmul, Nat.cast_smul_eq_nsmul]

/-- `π_{(n+2)x}` is `π_x` on `[0, 1/(n+2)]` followed by `π_{(n+1)x}`. -/
theorem pauseReparam_concat_straightLine (n : ℕ) (x : P.integralWeights) :
    pauseReparam (LSGeneralClass.splitClock (1 / ((n : ℝ) + 2)) (by positivity)
        (one_div_lt_one n))
      ((straightLine (P.pathSpace hA) x).concat (straightLine (P.pathSpace hA) ((n + 1) • x))) =
      straightLine (P.pathSpace hA) ((n + 2) • x) := by
  set s : ℝ := 1 / ((n : ℝ) + 2) with hs
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  apply ext_of_eqOn
  intro t ht
  rw [pauseReparam_apply, straightLine_apply_nsmul, min_eq_right ht.2, max_eq_right ht.1]
  rcases le_total t s with h | h
  · have hτ : (LSGeneralClass.splitClock s (by positivity) (one_div_lt_one n)).toFun t =
        t * ((n : ℝ) + 2) / 2 := by
      rw [LSGeneralClass.splitClock_of_le _ _ h, hs]
      field_simp
    have h2 : t * ((n : ℝ) + 2) ≤ 1 := by
      rw [hs, le_div_iff₀ hn] at h
      linarith
    rw [hτ, concat_apply_of_le (by linarith), straightLine_apply, pathSpace_embed,
      show 2 * (t * ((n : ℝ) + 2) / 2) = t * ((n : ℝ) + 2) by ring,
      min_eq_right h2, max_eq_right (by nlinarith [ht.1]), smul_smul]
    congr 1
    push_cast
    ring
  · have hτ : (LSGeneralClass.splitClock s (by positivity) (one_div_lt_one n)).toFun t =
        2⁻¹ + (t * ((n : ℝ) + 2) - 1) / (2 * ((n : ℝ) + 1)) := by
      rw [LSGeneralClass.splitClock_of_ge _ _ h, hs]
      congr 1
      have hd : (0 : ℝ) < 2 * (1 - 1 / ((n : ℝ) + 2)) := by
        have := one_div_lt_one n
        linarith
      rw [div_eq_div_iff hd.ne' (by positivity)]
      field_simp
      ring
    have h2 : 0 ≤ t * ((n : ℝ) + 2) - 1 := by
      rw [hs, div_le_iff₀ hn] at h
      linarith
    have h3 : t * ((n : ℝ) + 2) - 1 ≤ (n : ℝ) + 1 := by nlinarith [ht.2]
    set u : ℝ := (t * ((n : ℝ) + 2) - 1) / ((n : ℝ) + 1) with hu
    have hu0 : 0 ≤ u := by positivity
    have hu1 : u ≤ 1 := (div_le_one hn1).2 h3
    have hu' : u * ((n : ℝ) + 1) = t * ((n : ℝ) + 2) - 1 := by
      rw [hu]
      field_simp
    have h2u : 2 * (2⁻¹ + (t * ((n : ℝ) + 2) - 1) / (2 * ((n : ℝ) + 1))) - 1 = u := by
      rw [hu]
      field_simp
      ring
    rw [hτ, concat_apply_of_ge (by
        have : 0 ≤ (t * ((n : ℝ) + 2) - 1) / (2 * ((n : ℝ) + 1)) := by positivity
        linarith), h2u, straightLine_apply, pathSpace_embed, straightLine_apply_nsmul,
      min_self, max_eq_right zero_le_one, min_eq_right hu1, max_eq_right hu0,
      smul_smul, smul_smul]
    have e1 : u * ((n + 1 : ℕ) : ℝ) = t * ((n : ℝ) + 2) - 1 := by push_cast; exact hu'
    rw [e1]
    have e2 : t * ((n + 2 : ℕ) : ℝ) = t * ((n : ℝ) + 2) := by push_cast; ring
    rw [e2]
    module

/-! ### Concatenation powers -/

/-- The integral paths `π_Λ` of `B(Λ)` and its elements. -/
lemma isIntegral_pathCrystal
    (b : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    (Crystal.restrictHom (isStable_component _) b).IsIntegral :=
  isIntegral_of_mem_pathCrystal hA hΛ b

/-- The strict embeddings `B(Λ)^{⊗(n+1)} → {paths}`, `η₁ ⊗ ⋯ ⊗ η_{n+1} ↦ η₁ * (η₂ * ⋯)`
(reparametrized), with integral images and `π_Λ^{⊗(n+1)} ↦ π_{(n+1)Λ}`. -/
noncomputable def concatPow' : (n : ℕ) →
    {ψ : Crystal.StrictHom ((P.pathCrystal hA hΛ).tensorPow (n + 1)) (crystal (P.pathSpace hA)) //
      (∀ y, (ψ y).IsIntegral) ∧ Function.Injective ψ ∧
      ψ (Crystal.TPow.replicate (pathCrystalTop hA hΛ) (n + 1)) =
        straightLine (P.pathSpace hA) ((n + 1) • ⟨Λ, hΛ.mem_integralWeights⟩)}
  | 0 => ⟨(Crystal.restrictHom (isStable_component _)).comp
      (Crystal.tensorUnit (P.pathCrystal hA hΛ)).toStrictHom,
      fun y ↦ isIntegral_pathCrystal hA hΛ y.1,
      fun y y' h ↦ Prod.ext (Subtype.ext h) rfl,
      by
        change straightLine _ _ = straightLine _ ((0 + 1) • _)
        rw [zero_add, one_nsmul]⟩
  | n + 1 =>
    let ψ := concatPow' n
    ⟨(pauseReparamHom (LSGeneralClass.splitClock (1 / ((n : ℝ) + 2)) (by positivity)
        (one_div_lt_one n))).comp
      (concatHomOf (Crystal.restrictHom (isStable_component _)) ψ.1
        (isIntegral_pathCrystal hA hΛ) ψ.2.1),
      fun y ↦ (isIntegral_pauseReparam_iff _ _).2
        ((isIntegral_pathCrystal hA hΛ y.1).concat (ψ.2.1 y.2)),
      fun y y' h ↦ by
        have h1 := pauseReparam_injective _ h
        obtain ⟨h2, h3⟩ := concat_injective h1
        exact Prod.ext (Subtype.ext h2) (ψ.2.2.1 h3),
      by
        change pauseReparam _ ((pathCrystalTop hA hΛ).1.concat
          (ψ.1 (Crystal.TPow.replicate (pathCrystalTop hA hΛ) (n + 1)))) = _
        rw [ψ.2.2.2, pauseReparam_concat_straightLine hA n]⟩

/-- The strict embedding `B(Λ)^{⊗(n+1)} → {paths}` by concatenation. -/
noncomputable def concatPow (n : ℕ) :
    Crystal.StrictHom ((P.pathCrystal hA hΛ).tensorPow (n + 1)) (crystal (P.pathSpace hA)) :=
  (concatPow' hA hΛ n).1

lemma concatPow_injective (n : ℕ) : Function.Injective (concatPow hA hΛ n) :=
  (concatPow' hA hΛ n).2.2.1

lemma concatPow_replicate (n : ℕ) :
    concatPow hA hΛ n (Crystal.TPow.replicate (pathCrystalTop hA hΛ) (n + 1)) =
      straightLine (P.pathSpace hA) ((n + 1) • ⟨Λ, hΛ.mem_integralWeights⟩) :=
  (concatPow' hA hΛ n).2.2.2

/-! ### Stretching -/

/-- Stretching `π ↦ Nπ` is an `N`-similarity from `B(Λ)` to the crystal of all paths
([Lit95] Lemma 2.4). -/
noncomputable def stretchSimilarity {N : ℕ} (hN : 0 < N) :
    Crystal.Similarity (P.pathCrystal hA hΛ) (crystal (P.pathSpace hA)) N where
  toFun b := LSGeneralClass.stretch N b.1
  wt_map b := LSGeneralClass.wt_stretch N b.1
  ε_map i b := by
    obtain ⟨k, hk⟩ := isIntegral_pathCrystal hA hΛ b i
    change ε i (LSGeneralClass.stretch N b.1) = N • ε i b.1
    rw [ε, ε, LSGeneralClass.minPairing_stretch]
    change _ = N • (((⌊-(b.1.minPairing i)⌋ : ℤ)) : WithBot ℤ)
    rw [show b.1.minPairing i = k from hk, Crystal.nsmul_coe_withBot,
      show -((N : ℝ) * (k : ℝ)) = (((N * -k : ℤ)) : ℝ) by push_cast; ring, Int.floor_intCast,
      Int.floor_neg, Int.ceil_intCast]
  e_map i b := by
    rw [LSGeneralClass.eIter_stretch hN, ← crystal_e, ← Crystal.restrict_e (isStable_component _),
      Option.map_map]
    rfl
  f_map i b := by
    rw [LSGeneralClass.fIter_stretch hN, ← crystal_f, ← Crystal.restrict_f (isStable_component _),
      Option.map_map]
    rfl

lemma stretchSimilarity_injective {N : ℕ} (hN : 0 < N) :
    Function.Injective (stretchSimilarity hA hΛ hN) := fun _ _ h ↦
  Subtype.ext (LSGeneralClass.stretch_injective hN h)

lemma stretchSimilarity_top {N : ℕ} (hN : 0 < N) :
    stretchSimilarity hA hΛ hN (pathCrystalTop hA hΛ) =
      straightLine (P.pathSpace hA) (N • ⟨Λ, hΛ.mem_integralWeights⟩) :=
  LSGeneralClass.stretch_straightLine N _

/-! ### Similarity data -/

/-- The `m`-similarity `B(Λ) → B(Λ)^{⊗m}` with `π_Λ ↦ π_Λ^{⊗m}` and
`concat ∘ T = stretch`. -/
theorem exists_pathSimilarity (n : ℕ) :
    ∃ T : Crystal.Similarity (P.pathCrystal hA hΛ) ((P.pathCrystal hA hΛ).tensorPow (n + 1))
      (n + 1), T (pathCrystalTop hA hΛ) = Crystal.TPow.replicate (pathCrystalTop hA hΛ) (n + 1) ∧
      Function.Injective T := by
  obtain ⟨T, hT₀, hT⟩ := (stretchSimilarity hA hΛ n.succ_pos).exists_lift (concatPow hA hΛ n)
    (concatPow_injective hA hΛ n)
    (by rw [concatPow_replicate, stretchSimilarity_top]) (exists_fWord_pathCrystal hA hΛ)
  refine ⟨T, hT₀, fun b b' h ↦ stretchSimilarity_injective hA hΛ n.succ_pos ?_⟩
  rw [← hT, ← hT, h]

/-- **Littelmann's path crystal `B(Λ)` has similarity data** ([Kas96] §4). -/
noncomputable def pathSimilarityData :
    Crystal.SimilarityData (P.cartanDatum hA) (P.pathCrystal hA hΛ) (pathCrystalTop hA hΛ)
      ⟨Λ, hΛ.mem_integralWeights⟩ where
  isSeminormal := isSeminormal_pathCrystal hA hΛ
  exists_fWord := exists_fWord_pathCrystal hA hΛ
  wt_b₀ := rfl
  T m hm := match m, hm with
    | n + 1, _ => (exists_pathSimilarity hA hΛ n).choose
  T_injective m hm := match m, hm with
    | n + 1, _ => (exists_pathSimilarity hA hΛ n).choose_spec.2
  T_b₀ m hm := match m, hm with
    | n + 1, _ => (exists_pathSimilarity hA hΛ n).choose_spec.1
  existsUnique_wt _ h := Crystal.existsUnique_wt_of_orbit (isSeminormal_pathCrystal hA hΛ)
    (exists_fWord_pathCrystal hA hΛ) (P.linearIndependent_root_cartanDatum hA) h
  ε_eq_zero _ _ h hi := Crystal.ε_eq_zero_of_orbit (isSeminormal_pathCrystal hA hΛ)
    (exists_fWord_pathCrystal hA hΛ) (P.linearIndependent_root_cartanDatum hA)
    (P.rootSign_cartanDatum hA) h hi

end Matrix.Realization
