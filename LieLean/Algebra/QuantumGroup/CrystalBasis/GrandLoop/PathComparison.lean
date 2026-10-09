/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.HighestWeightTensor
import LieLean.RepresentationTheory.Crystal.MapDatum
import LieLean.RepresentationTheory.Crystal.Path.Normal
import LieLean.RepresentationTheory.Crystal.Path.Similarity

/-!
# The crystal of `L_q(λ)` is Littelmann's path crystal

Let `B(λ)` be the crystal of the crystal base `(L(λ), B(λ))` of the irreducible highest weight
module `L_q(λ)` (`GrandLoop.crystalHW`, from Kashiwara's grand loop), and let `P` be a realization
over `ℝ` of a generalized Cartan matrix, with a morphism of Cartan data `ψ` from the root datum
to `P` (an additive map of weight lattices sending simple roots to simple roots and compatible with
the simple coroots). Then `ψ_* B(λ)` is isomorphic to Littelmann's path crystal `B(π_{ψ λ})`, by a
unique isomorphism `u_λ ↦ π_{ψ λ}` ([Kas96] Thm. 4.1, for the path model).

## Main definitions

* `GrandLoop.similarityDataHW`: the data of [Kas96] §4 for `ψ_* B(λ)`: the similarities
  `B(λ) → B(λ)^{⊗m}` (`GrandLoop.exists_similarityPowHW`) and the extremal elements.

## Main results

* `GrandLoop.existsUnique_equiv_pathCrystal`: `ψ_* B(λ) ≅ B(π_{ψ λ})`.
* `GrandLoop.isNormal_crystalHW`: `ψ_* B(λ)` is normal (`Crystal.IsNormal`).

## Proof

Both crystals carry similarity data (`Crystal.SimilarityData`; for paths
`Matrix.Realization.pathSimilarityData`), and `Crystal.SimilarityData.existsUnique_equiv` is the
argument of [Kas96] §4.

## References

* [Kas96] M. Kashiwara, *Similarity of crystal bases*, Contemp. Math. 194 (1996), 177–186, §4.
-/

open LusztigF Pointwise

noncomputable section

namespace Crystal

open Matrix Matrix.Realization

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan} {B B₂ : Type*}
  {C : Crystal (P.cartanDatum hA) B} {C₂ : Crystal (P.cartanDatum hA) B₂}

/-- Normality is invariant under isomorphisms of crystals. -/
theorem IsNormal.of_equiv (hC : C.IsNormal) (Ψ : Equiv C C₂) : C₂.IsNormal where
  isSeminormal i b n := by
    obtain ⟨b, rfl⟩ := Ψ.toEquiv.surjective b
    have h1 := Ψ.toStrictHom.eIter_apply i n b
    have h2 := Ψ.toStrictHom.fIter_apply i n b
    rw [Equiv.coe_toStrictHom] at h1 h2
    rw [Equiv.coe_toEquiv, h1, h2, Option.isSome_map, Option.isSome_map, Ψ.ε_apply, Ψ.φ_apply]
    exact hC.isSeminormal i b n
  exists_leviHom J hJ b := by
    obtain ⟨ν, hν, Φ, hΦ, hL, c, hc⟩ := hC.exists_leviHom J hJ (Ψ.symm b)
    refine ⟨ν, hν, Ψ ∘ Φ, (EquivLike.injective Ψ).comp hΦ, ?_, c, ?_⟩
    · have := hL.strictHom_comp Ψ.toStrictHom
      rwa [Equiv.coe_toStrictHom] at this
    · rw [Function.comp_apply, hc]
      exact Ψ.toEquiv.apply_symm_apply b

end Crystal

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}
  [Fintype I] {H : Type*} [AddCommGroup H] [Module ℝ H] {M : Matrix I I ℤ}
  {P : Matrix.Realization M ℝ H} (hM : M.IsGeneralizedCartan)
  (ψ : R.crystalDatum.Hom (P.cartanDatum hM))

omit [DecidableEq I] in
/-- `ψ λ` is dominant integral. -/
lemma isDominantIntegral_hom (Λ : Dom R) :
    P.IsDominantIntegral ((ψ.toFun Λ.1 : P.integralWeights) : Module.Dual ℝ H) := fun i ↦
  ⟨(Λ.1 (R.coroot i)).toNat, by
    rw [← P.coroot_cartanDatum_cast hM i, ψ.coroot_map,
      LusztigCartanDatum.RootDatum.crystalDatum_coroot, ← Int.cast_natCast,
      Int.toNat_of_nonneg (Λ.2 i)]⟩

variable [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

lemma wt_topHW_mapDatum (Λ : Dom R) :
    ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).mapDatum ψ).wt (topHW hvt hR hinj hϖ Λ) =
      ψ.toFun Λ.1 := by
  rw [Crystal.mapDatum_wt, topHW, wt_mkHW]
  simp

variable [IsFormallyReal (A ⧸ Ideal.span {ϖ})]

variable (hvt hR) in
/-- **Similarity data for `ψ_* B(λ)`** ([Kas96] §4). -/
def similarityDataHW (Λ : Dom R) :
    Crystal.SimilarityData (P.cartanDatum hM)
      ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).mapDatum ψ) (topHW hvt hR hinj hϖ Λ)
      (ψ.toFun Λ.1) where
  isSeminormal := (isSeminormal_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).mapDatum ψ
  exists_fWord b := by
    simpa only [Crystal.mapDatum_fWord] using exists_fWord_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ b
  wt_b₀ := wt_topHW_mapDatum hM ψ hinj hϖ hϖv hk hfund Λ
  T m hm := match m, hm with
    | n + 1, _ =>
      ((exists_similarityPowHW hinj hϖ hϖv hk hfund Λ n).choose.mapDatum ψ).compStrictHom
        (Crystal.tensorPowMapDatum ψ _ (n + 1)).symm.toStrictHom
  T_injective m hm := match m, hm with
    | n + 1, _ => fun b b' h ↦
      (exists_similarityPowHW hinj hϖ hϖv hk hfund Λ n).choose_spec.2 (by simpa using h)
  T_b₀ m hm := match m, hm with
    | n + 1, _ => by
      rw [Crystal.Similarity.compStrictHom_apply, Crystal.Equiv.coe_toStrictHom,
        Crystal.tensorPowMapDatum_symm_apply, Crystal.Similarity.mapDatum_apply]
      exact (exists_similarityPowHW hinj hϖ hϖv hk hfund Λ n).choose_spec.1
  existsUnique_wt _ h := Crystal.existsUnique_wt_of_orbit
    ((isSeminormal_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).mapDatum ψ)
    (by simpa only [Crystal.mapDatum_fWord] using
      exists_fWord_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ)
    (P.linearIndependent_root_cartanDatum hM)
    (by rwa [wt_topHW_mapDatum hM ψ hinj hϖ hϖv hk hfund Λ])
  ε_eq_zero _ _ h hi := Crystal.ε_eq_zero_of_orbit
    ((isSeminormal_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).mapDatum ψ)
    (by simpa only [Crystal.mapDatum_fWord] using
      exists_fWord_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ)
    (P.linearIndependent_root_cartanDatum hM) (P.rootSign_cartanDatum hM)
    (by rwa [wt_topHW_mapDatum hM ψ hinj hϖ hϖv hk hfund Λ]) hi

/-- **The crystal of `L_q(λ)` is Littelmann's path crystal** ([Kas96] Thm. 4.1): there is a
unique isomorphism of crystals `ψ_* B(λ) ≅ B(π_{ψ λ})` with `u_λ ↦ π_{ψ λ}`. Here `B(λ)` is the
crystal of the crystal base `(L(λ), B(λ))` of `L_q(λ)` over the local ring `A ⊆ k = A[ϖ⁻¹]`
(`GrandLoop.isCrystalBase`), and `ψ` is a morphism of Cartan data from the root datum to a
realization `P` over `ℝ`. -/
theorem existsUnique_equiv_pathCrystal (Λ : Dom R) :
    ∃ Φ : Crystal.Equiv ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).mapDatum ψ)
        (P.pathCrystal hM (isDominantIntegral_hom hM ψ Λ)),
      Φ (topHW hvt hR hinj hϖ Λ) =
          Matrix.Realization.pathCrystalTop hM (isDominantIntegral_hom hM ψ Λ) ∧
        ∀ Φ' : Crystal.Equiv ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).mapDatum ψ)
            (P.pathCrystal hM (isDominantIntegral_hom hM ψ Λ)),
          Φ' (topHW hvt hR hinj hϖ Λ) =
            Matrix.Realization.pathCrystalTop hM (isDominantIntegral_hom hM ψ Λ) →
          ∀ b, Φ' b = Φ b :=
  (similarityDataHW hvt hR hM ψ hinj hϖ hϖv hk hfund Λ).existsUnique_equiv
    (Matrix.Realization.pathSimilarityData hM (isDominantIntegral_hom hM ψ Λ))

/-- **The crystal of `L_q(λ)` is normal**: `ψ_* B(λ)` satisfies `Crystal.IsNormal`, from
`GrandLoop.existsUnique_equiv_pathCrystal` and `Matrix.Realization.isNormal_pathCrystal`. -/
theorem isNormal_crystalHW (Λ : Dom R) :
    ((crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).mapDatum ψ).IsNormal := by
  obtain ⟨Φ, -, -⟩ := existsUnique_equiv_pathCrystal hM ψ hinj hϖ hϖv hk hfund Λ
  exact (Matrix.Realization.isNormal_pathCrystal hM (isDominantIntegral_hom hM ψ Λ)).of_equiv
    Φ.symm

end GrandLoop

end LieLean.QuantumGroup
