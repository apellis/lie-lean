/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.CrystalBase
import LieLean.RepresentationTheory.Crystal.MapDatum
import LieLean.RepresentationTheory.Crystal.Realization
import Mathlib.Algebra.Category.Grp.Injective

/-!
# A real realization receiving the weight lattice of a root datum

Let `R` be a root datum of type `(I, ·)` with coweight lattice `Y` and weight lattice
`X = Hom(Y, ℤ)`, and let `P = Matrix.Realization.std (aᵢⱼ) ℝ` be the standard realization over `ℝ`
of its generalized Cartan matrix, on `𝔥 = ℝ^I × (ker A)*`. If `R` is `X`-regular (the simple roots
`i' ∈ X` are linearly independent), there is a morphism of Cartan data
`ψ : R.crystalDatum → P.cartanDatum` (`CartanDatum.Hom`): an additive map from `X` to the integral
weights of `P` with `ψ(i') = αᵢ` and `⟨ψ μ, αᵢ^∨⟩ = ⟨i, μ⟩`.

## Construction

Write `p` for the projection of `ℝ^I` onto `ker A` used by the standard realization. Since `ℝ^I` is
divisible, the map `Σ kⱼ j' ↦ (kⱼ)ⱼ` on the root lattice (well defined by `X`-regularity) extends to
an additive map `c : X → ℝ^I` (Baer's criterion). Then `ψ μ (v, f) = Σᵢ ⟨i, μ⟩ vᵢ + f (p (c μ))`.

Some independence of the simple roots is needed: if `A` is singular and the simple roots of `X` are
linearly dependent, there may be no such `ψ`, since the simple roots of a realization are linearly
independent.

## Main definitions

* `LusztigCartanDatum.RootDatum.stdHom`: the morphism `ψ`.
-/

open Module Matrix Matrix.Realization

noncomputable section

namespace Matrix.Realization

variable {ι : Type*} [Fintype ι] (A : Matrix ι ι ℤ)

/-- The linear form `(v, f) ↦ Σᵢ aᵢ vᵢ + f (p c)` on the space of the standard realization. -/
def stdWeight (a c : ι → ℝ) : Dual ℝ (StdSpace A ℝ) :=
  (∑ i, a i • LinearMap.proj i) ∘ₗ LinearMap.fst ℝ _ _ +
    Dual.eval ℝ _ (stdProj A ℝ c) ∘ₗ LinearMap.snd ℝ _ _

lemma stdWeight_apply (a c : ι → ℝ) (v : ι → ℝ) (f : Dual ℝ (stdKer A ℝ)) :
    stdWeight A a c (v, f) = ∑ i, a i * v i + f (stdProj A ℝ c) := by
  simp [stdWeight]

lemma stdWeight_add (a c a' c' : ι → ℝ) :
    stdWeight A (a + a') (c + c') = stdWeight A a c + stdWeight A a' c' := by
  refine LinearMap.ext fun ⟨v, f⟩ ↦ ?_
  simp only [stdWeight_apply, LinearMap.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib,
    map_add]
  ring

end Matrix.Realization

namespace LusztigCartanDatum.RootDatum

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

section Finite

variable [Finite I]

/-- For an `X`-regular root datum, there is an additive map `c : X → ℝ^I` with `c(j') = eⱼ`. -/
theorem exists_rootCoord (hR : R.IsXRegular) :
    ∃ c : (Y →+ ℤ) →+ (I → ℝ), ∀ j, c (R.root j) = Pi.single j 1 := by
  cases nonempty_fintype I
  obtain ⟨c, hc⟩ := (Module.Baer.of_divisible (I → ℝ)).extension_property_addMonoidHom
    (Fintype.linearCombination ℤ R.root).toAddMonoidHom
    (LinearIndependent.fintypeLinearCombination_injective hR)
    (AddMonoidHom.compLeft (Int.castAddHom ℝ) I)
  refine ⟨c, fun j ↦ ?_⟩
  have := DFunLike.congr_fun hc (Pi.single j 1)
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    Fintype.linearCombination_apply_single, one_smul] at this
  rw [this]
  ext k
  simp [Pi.single_apply]

/-- The additive map `c : X → ℝ^I` with `c(j') = eⱼ` of `exists_rootCoord`. -/
def rootCoord (hR : R.IsXRegular) : (Y →+ ℤ) →+ (I → ℝ) := (exists_rootCoord hR).choose

lemma rootCoord_root (hR : R.IsXRegular) (j : I) : rootCoord hR (R.root j) = Pi.single j 1 :=
  (exists_rootCoord hR).choose_spec j

end Finite

variable [Fintype I]

/-- The linear form `ψ μ` on the standard realization: `(v, f) ↦ Σᵢ ⟨i, μ⟩ vᵢ + f (p (c μ))`. -/
def stdHomFun (hR : R.IsXRegular) : (Y →+ ℤ) →+ Dual ℝ (StdSpace D.cartanMatrix ℝ) where
  toFun μ := stdWeight D.cartanMatrix (fun i ↦ (μ (R.coroot i) : ℝ)) (rootCoord hR μ)
  map_zero' := LinearMap.ext fun ⟨v, f⟩ ↦ by simp [stdWeight_apply]
  map_add' μ ν := by
    rw [← stdWeight_add, map_add]
    congr 1
    ext i
    simp

lemma stdHomFun_apply (hR : R.IsXRegular) (μ : Y →+ ℤ) (v : I → ℝ)
    (f : Dual ℝ (stdKer D.cartanMatrix ℝ)) :
    stdHomFun hR μ (v, f) =
      ∑ i, (μ (R.coroot i) : ℝ) * v i + f (stdProj D.cartanMatrix ℝ (rootCoord hR μ)) :=
  stdWeight_apply _ _ _ _ _

lemma stdHomFun_coroot (hR : R.IsXRegular) (μ : Y →+ ℤ) (i : I) :
    stdHomFun hR μ ((std D.cartanMatrix ℝ).coroot i) = μ (R.coroot i) := by
  change stdHomFun hR μ (Pi.single i 1, 0) = _
  rw [stdHomFun_apply]
  simp [Pi.single_apply]

lemma stdHomFun_root (hR : R.IsXRegular) (j : I) :
    stdHomFun hR (R.root j) = (std D.cartanMatrix ℝ).root j := by
  refine LinearMap.ext fun ⟨v, f⟩ ↦ ?_
  change _ = stdRoot D.cartanMatrix ℝ j (v, f)
  rw [stdHomFun_apply, stdRoot_apply, rootCoord_root]
  congr 1
  simp only [R.root_coroot, vecMul, dotProduct, map_apply]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- **A morphism of Cartan data from an `X`-regular root datum to the standard real realization**
of its Cartan matrix: `ψ(i') = αᵢ` and `⟨ψ μ, αᵢ^∨⟩ = ⟨i, μ⟩`. -/
def stdHom (hR : R.IsXRegular) :
    R.crystalDatum.Hom
      ((std D.cartanMatrix ℝ).cartanDatum D.isGeneralizedCartan_cartanMatrix) where
  toFun := (stdHomFun hR).codRestrict (std D.cartanMatrix ℝ).integralWeights fun μ i ↦
    ⟨μ (R.coroot i), stdHomFun_coroot hR μ i⟩
  map_root j := Subtype.ext (stdHomFun_root hR j)
  coroot_map i μ := Int.cast_injective (α := ℝ) <| by
    rw [coroot_cartanDatum_cast]
    exact stdHomFun_coroot hR μ i

@[simp] lemma coe_stdHom_apply (hR : R.IsXRegular) (μ : Y →+ ℤ) :
    ((stdHom hR).toFun μ : Dual ℝ (StdSpace D.cartanMatrix ℝ)) = stdHomFun hR μ := rfl

end LusztigCartanDatum.RootDatum
