/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Pitman
import LieLean.RepresentationTheory.Crystal.Path.WeylAction
import LieLean.RepresentationTheory.Crystal.BraidA2

/-!
# The `A₂` braid relation for Kashiwara's reflections on path crystals

For two colours `i, j` with `⟨αⱼ, αᵢ^∨⟩ = ⟨αᵢ, αⱼ^∨⟩ = -1` and a stable set of integral paths
(e.g. `B(λ)`), Kashiwara's reflections satisfy `SᵢSⱼSᵢ = SⱼSᵢSⱼ`
(`LittelmannPath.reflection_braid_three`). The tops of strings are Pitman transforms
(`LittelmannPath.top_apply`), so the hypotheses of
`Crystal.IsSeminormal.reflection_braid_three` are the `A₂` Pitman identities of
`LieLean.RepresentationTheory.Crystal.Path.Pitman`.

## Main results

* `LittelmannPath.reflection_braid_three`: `SᵢSⱼSᵢ = SⱼSᵢSⱼ` on integral paths.
* `Matrix.Realization.pathBraidRelations_of_simplyLaced`: the braid relations on `B(Λ)` for
  every generalized Cartan matrix with `aᵢⱼaⱼᵢ ∈ {0, 1} ∪ [4, ∞)` for all `i ≠ j` (e.g. all
  simply-laced types).

## References

* [BBO05] P. Biane, P. Bougerol, N. O'Connell, *Littelmann paths and Brownian paths*, Duke
  Math. J. **130** (2005), 127–167, §2.
* [Kas94] M. Kashiwara, *Crystal bases of modified quantized enveloping algebra*, Duke Math. J.
  **73** (1994), 383–413, §7.
-/

open Set Module

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [FloorRing 𝕜]
  {D : CartanDatum ι X} {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

lemma εN_of_minPairing_eq {π : LittelmannPath S} {i : ι} {z : ℤ} (hz : π.minPairing i = z) :
    (crystal S).εN i π = (-z).toNat := by
  rw [Crystal.εN, crystal_ε, ε_of_minPairing_eq hz, WithBot.unbotD_coe]

lemma coe_εN_of_minPairing_eq {π : LittelmannPath S} {i : ι} {z : ℤ}
    (hz : π.minPairing i = z) : ((crystal S).εN i π : 𝕜) = -π.minPairing i := by
  have hz0 : z ≤ 0 := by exact_mod_cast hz ▸ π.minPairing_nonpos i
  rw [εN_of_minPairing_eq hz, hz]
  exact_mod_cast Int.toNat_of_nonneg (by omega)

/-- For an integral minimum, the top of the `i`-string is the Pitman transform. -/
theorem top_apply {π : LittelmannPath S} {i : ι} {z : ℤ} (hz : π.minPairing i = z) (t : 𝕜) :
    (crystal S).top i π t = π t - π.runningMin i t • S.root i := by
  obtain ⟨ξ, hξ, hξt⟩ := π.eIter_eq_pitman i hz
  rw [Crystal.top, εN_of_minPairing_eq hz, hξ, Option.getD_some, hξt]

variable {B : Set (LittelmannPath S)}

/-- **The `A₂` braid relation on path crystals**: on a stable set of paths all of whose minima
are integral, `SᵢSⱼSᵢ = SⱼSᵢSⱼ` when `⟨αⱼ, αᵢ^∨⟩ = ⟨αᵢ, αⱼ^∨⟩ = -1`. -/
theorem reflection_braid_three {i j : ι} (hij : D.coroot i (D.root j) = -1)
    (hji : D.coroot j (D.root i) = -1) (hB : (crystal S).IsStable B)
    (hint : ∀ π ∈ B, ∀ k, ∃ z : ℤ, π.minPairing k = z) {π : LittelmannPath S} (hπ : π ∈ B) :
    (crystal S).reflection i ((crystal S).reflection j ((crystal S).reflection i π)) =
      (crystal S).reflection j ((crystal S).reflection i ((crystal S).reflection j π)) := by
  have hij' : S.coroot i (S.root j) = -1 := by
    rw [S.coroot_root, CartanDatum.cartanMatrix_apply, hij, Int.cast_neg, Int.cast_one]
  have hji' : S.coroot j (S.root i) = -1 := by
    rw [S.coroot_root, CartanDatum.cartanMatrix_apply, hji, Int.cast_neg, Int.cast_one]
  -- tops along `(i, j, i)` and `(j, i, j)` are given by Pitman transforms
  have htopf : ∀ ξ ∈ B, ∀ k, ∀ t, (crystal S).top k ξ t = ξ t - ξ.runningMin k t • S.root k :=
    fun ξ hξ k t => by
      obtain ⟨z, hz⟩ := hint ξ hξ k
      exact top_apply hz t
  have hεf : ∀ ξ ∈ B, ∀ k, (((crystal S).εN k ξ : ℤ) : 𝕜) = -ξ.minPairing k := fun ξ hξ k => by
    obtain ⟨z, hz⟩ := hint ξ hξ k
    exact_mod_cast coe_εN_of_minPairing_eq hz
  have hmem : ∀ ξ ∈ B, ∀ k, (crystal S).top k ξ ∈ B := fun ξ hξ k => hB.top_mem hξ
  -- the two `A₂` Pitman identities, for either order of the colours
  have key : ∀ {a c : ι}, S.coroot a (S.root c) = -1 → S.coroot c (S.root a) = -1 →
      ∀ ξ ∈ B, (∀ t, (crystal S).top a ((crystal S).top c ((crystal S).top a ξ)) t =
        ξ t - ((crystal S).top c ξ).runningMin a t • S.root a -
          ((crystal S).top a ξ).runningMin c t • S.root c) ∧
      ((crystal S).εN c ξ : ℤ) = max ((crystal S).εN a ((crystal S).top c
        ((crystal S).top a ξ)) : ℤ) (((crystal S).εN c ((crystal S).top a ξ) : ℤ) -
          (crystal S).εN a ξ) := by
    intro a c hac hca ξ hξ
    have h₁ := htopf ξ hξ a
    have h₂ := htopf _ (hmem ξ hξ a) c
    have h₃ := htopf _ (hmem _ (hmem ξ hξ a) c) a
    have hρ := htopf ξ hξ c
    refine ⟨pitman_three_apply hac hca h₁ h₂ hρ h₃, ?_⟩
    have hf := runningMin_add_runningMin_eq hac hca h₁ h₂ hρ 1
    have hm := minPairing_add_minPairing_eq hac hca h₁ hρ
    change ξ.minPairing a + ((crystal S).top c ((crystal S).top a ξ)).minPairing a =
      ((crystal S).top c ξ).minPairing a at hf
    have e1 := hεf ξ hξ c
    have e2 := hεf _ (hmem _ (hmem ξ hξ a) c) a
    have e3 := hεf _ (hmem ξ hξ a) c
    have e4 := hεf ξ hξ a
    have goal : ((((crystal S).εN c ξ : ℤ) : 𝕜)) = max ((((crystal S).εN a ((crystal S).top c
        ((crystal S).top a ξ)) : ℤ) : 𝕜)) ((((crystal S).εN c ((crystal S).top a ξ) : ℤ) : 𝕜) -
          (((crystal S).εN a ξ : ℤ) : 𝕜)) := by
      rw [e1, e2, e3, e4]
      rcases le_total (((crystal S).top c ξ).minPairing a)
        (((crystal S).top a ξ).minPairing c) with h | h
      · rw [min_eq_left h] at hm
        rw [max_eq_left (by linarith)]
        linarith
      · rw [min_eq_right h] at hm
        rw [max_eq_right (by linarith)]
        linarith
    exact_mod_cast goal
  apply (isSeminormal_crystal S).reflection_braid_three hij hji hB _ (fun ξ hξ => (key hij' hji'
    ξ hξ).2) (fun ξ hξ => (key hji' hij' ξ hξ).2) hπ
  intro ξ hξ
  apply LittelmannPath.ext
  intro t
  rw [(key hij' hji' ξ hξ).1 t, (key hji' hij' ξ hξ).1 t]
  abel

end LittelmannPath

namespace Matrix.Realization

open LittelmannPath

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} (hA : A.IsGeneralizedCartan) {Λ : Dual ℝ H}

omit [DecidableEq ι] in
/-- **The `A₂` braid relation on `B(Λ)`**: `SᵢSⱼSᵢ = SⱼSᵢSⱼ` when `aᵢⱼ = aⱼᵢ = -1`, for any
generalized Cartan matrix. -/
theorem pathCrystal_reflection_braid_three (hΛ : P.IsDominantIntegral Λ) {i j : ι}
    (hij : A i j = -1) (hji : A j i = -1)
    (b : (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    (P.pathCrystal hA hΛ).reflection i ((P.pathCrystal hA hΛ).reflection j
      ((P.pathCrystal hA hΛ).reflection i b)) =
    (P.pathCrystal hA hΛ).reflection j ((P.pathCrystal hA hΛ).reflection i
      ((P.pathCrystal hA hΛ).reflection j b)) := by
  apply Subtype.ext
  simp only [coe_reflection_pathCrystal]
  refine LittelmannPath.reflection_braid_three ?_ ?_ (isStable_component _)
    (fun π hπ => isIntegral_of_mem_pathCrystal hA hΛ ⟨π, hπ⟩) b.2
  · rw [← CartanDatum.cartanMatrix_apply, cartanMatrix_cartanDatum_apply, hij]
  · rw [← CartanDatum.cartanMatrix_apply, cartanMatrix_cartanDatum_apply, hji]

omit [DecidableEq ι] in
/-- The Coxeter relation `(SᵢSⱼ)³ = 1` on `B(Λ)` when `aᵢⱼ = aⱼᵢ = -1`. -/
theorem pathReflectionPerm_mul_pow_three (hΛ : P.IsDominantIntegral Λ) {i j : ι}
    (hij : A i j = -1) (hji : A j i = -1) :
    (pathReflectionPerm P hA hΛ i * pathReflectionPerm P hA hΛ j) ^ 3 = 1 := by
  have hC := isSeminormal_pathCrystal hA hΛ
  ext b
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply,
    Crystal.IsSeminormal.reflectionPerm_apply, Equiv.Perm.one_apply]
  rw [pathCrystal_reflection_braid_three hA hΛ hij hji, hC.reflection_reflection,
    hC.reflection_reflection, hC.reflection_reflection]

/-- **Kashiwara's Weyl group action in the simply-laced case**: if `aᵢⱼaⱼᵢ ∈ {0, 1}` or
`aᵢⱼaⱼᵢ ≥ 4` for all `i ≠ j` (for instance every simply-laced generalized Cartan matrix: types
`A`, `D`, `E` and their affine and hyperbolic relatives), all braid relations hold on `B(Λ)`
(see `Matrix.Realization.pathBraidRelations` for arbitrary generalized Cartan matrices). -/
theorem pathBraidRelations_of_simplyLaced (hΛ : P.IsDominantIntegral Λ)
    (h : ∀ i j, i ≠ j → A i j ≠ 0 → A i j * A j i = 1 ∨ 4 ≤ A i j * A j i) :
    P.PathBraidRelations hA hΛ := by
  intro i j hij hA0 hM
  rcases h i j hij hA0 with h1 | h4
  · have hn := hA.offDiag_nonpos i j hij
    have hn' := hA.offDiag_nonpos j i (Ne.symm hij)
    have e1 : A i j = -1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h | h
      · omega
      · exact h
    have e2 : A j i = -1 := by
      rw [e1] at h1
      omega
    have hm : A.coxeterMatrix i j = 3 := by
      rw [A.coxeterMatrix_apply_of_ne hij, h1]
      rfl
    rw [hm]
    exact pathReflectionPerm_mul_pow_three hA hΛ e1 e2
  · exfalso
    apply hM
    rw [A.coxeterMatrix_apply_of_ne hij]
    exact coxeterEntry_of_four_le (by omega)

end Matrix.Realization
