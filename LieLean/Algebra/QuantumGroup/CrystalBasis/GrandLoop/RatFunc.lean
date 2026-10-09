/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.PathComparison
import LieLean.Algebra.QuantumGroup.Sl2.GlobalBasis

/-!
# The grand-loop setting over `ℚ(v)`

The results on crystal bases of `L_q(λ)` (`GrandLoop.isCrystalBase`,
`GrandLoop.existsUnique_equiv_pathCrystal'`, `GrandLoop.isNormal_crystalHW'`) assume: `v`
transcendental over `ℚ`; an `X`-regular root datum with fundamental weights; a discrete valuation
ring `A ⊆ k` with `k = A[ϖ⁻¹]` and `ϖ ↦ v⁻¹`; and `A/ϖA` formally real. We check that all of these
hold in Kashiwara's setting: `k = ℚ(v)`, `A = ℚ[v⁻¹]_{(v⁻¹)}` the local ring at `v = ∞`, `ϖ = v⁻¹`,
`A/ϖA = ℚ`, for every Cartan datum `(I, ·)` with `I` finite and the root datum
`LusztigCartanDatum.extendedRootDatum` on `Y = ℤ^I × ℤ^I`.

We write `ℚ(v) = ℚ(X)` with `v = X⁻¹`, so that `A = ℚ[X]_{(X)}` (`Sl2.RankOne.LocalRing`) and
`ϖ = X` (`Sl2.RankOne.localX`).

## Main definitions

* `LusztigCartanDatum.extendedRootDatum`: the root datum with `Y = ℤ^I × ℤ^I`, `i = (eᵢ, 0)` and
  `j'(y, z) = Σᵢ aᵢⱼ yᵢ + zⱼ`; it is `X`-regular and has fundamental weights `(y, z) ↦ yⱼ`.

## Main results

* `GrandLoop.isNormal_crystalHW_ratFunc`, `GrandLoop.existsUnique_equiv_pathCrystal_ratFunc`: the
  identification of the crystal of `L_q(λ)` with the path crystal over `ℚ(v)`, with no
  hypothesis left.
-/

open LusztigF

noncomputable section

namespace LusztigCartanDatum

variable {I : Type*} [Fintype I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- The root datum with coweight lattice `Y = ℤ^I × ℤ^I`, simple coroots `i = (eᵢ, 0)` and simple
roots `j'(y, z) = Σᵢ aᵢⱼ yᵢ + zⱼ`. -/
def extendedRootDatum : D.RootDatum ((I → ℤ) × (I → ℤ)) where
  coroot i := (Pi.single i 1, 0)
  root j :=
    { toFun := fun y ↦ ∑ i, y.1 i * D.cartanMatrix i j + y.2 j
      map_zero' := by simp
      map_add' := fun y z ↦ by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
        ring }
  root_coroot i j := by simp [Pi.single_apply]

@[simp] lemma extendedRootDatum_coroot (i : I) :
    D.extendedRootDatum.coroot i = (Pi.single i 1, 0) := rfl

lemma extendedRootDatum_root_apply (j : I) (y : (I → ℤ) × (I → ℤ)) :
    D.extendedRootDatum.root j y = ∑ i, y.1 i * D.cartanMatrix i j + y.2 j := rfl

/-- The extended root datum is `X`-regular: `j'(0, eₖ) = δⱼₖ`. -/
theorem isXRegular_extendedRootDatum : D.extendedRootDatum.IsXRegular := by
  rw [RootDatum.IsXRegular, Fintype.linearIndependent_iff]
  intro g hg k
  have := DFunLike.congr_fun hg ((0 : I → ℤ), Pi.single k 1)
  simpa [AddMonoidHom.finsetSum_apply, extendedRootDatum_root_apply, Pi.single_apply] using this

/-- The extended root datum has fundamental weights `(y, z) ↦ yⱼ`. -/
theorem exists_fundamental_extendedRootDatum (j : I) :
    ∃ Λ : LieLean.QuantumGroup.GrandLoop.Dom D.extendedRootDatum,
      ∀ i, Λ.1 (D.extendedRootDatum.coroot i) = if i = j then 1 else 0 := by
  refine ⟨⟨(Pi.evalAddMonoidHom (fun _ ↦ ℤ) j).comp (AddMonoidHom.fst _ _), fun i ↦ ?_⟩,
    fun i ↦ ?_⟩
  · simp only [extendedRootDatum_coroot, AddMonoidHom.coe_comp, Function.comp_apply,
      AddMonoidHom.coe_fst, Pi.evalAddMonoidHom_apply, Pi.single_apply]
    split_ifs <;> simp
  · simp [Pi.single_apply, eq_comm]

end LusztigCartanDatum

/-- A ring with an injective ring homomorphism into a formally real ring is formally real. -/
theorem IsFormallyReal.of_injective {R S : Type*} [CommRing R] [CommRing S] [IsFormallyReal S]
    (f : R →+* S) (hf : Function.Injective f) : IsFormallyReal R := by
  have hmap : ∀ {s : R}, IsSumSq s → IsSumSq (f s) := fun hs ↦ by
    induction hs with
    | zero => simp
    | sq_add b _ ih => rw [map_add, map_mul]; exact .sq_add _ ih
  refine IsFormallyReal.of_eq_zero_of_eq_zero_of_mul_self_add fun {s a} hs h ↦ hf ?_
  have hs' := hmap hs
  have h1 : f a * f a + f s = 0 := by rw [← map_mul, ← map_add, h, map_zero]
  have h2 := IsFormallyReal.eq_zero_of_add_right (IsSumSq.mul_self (f a)) hs' h1
  rw [map_zero]
  exact IsReduced.eq_zero _ ⟨2, by rw [pow_two, h2]⟩

/-- In a discrete valuation ring `A` with fraction field `K` and uniformizer `ϖ`, `K = A[ϖ⁻¹]`. -/
theorem IsDiscreteValuationRing.exists_pow_mul_eq_algebraMap {A K : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] {ϖ : A}
    (hϖ : Irreducible ϖ) (c : K) :
    ∃ (m : ℕ) (a : A), algebraMap A K (ϖ ^ m) * c = algebraMap A K a := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) c
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hs) hϖ
  refine ⟨n, a * ↑u⁻¹, ?_⟩
  have hp : algebraMap A K (ϖ ^ n) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (pow_ne_zero _ hϖ.ne_zero)
  have hu : algebraMap A K (u : A) * algebraMap A K ↑u⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hu0 : algebraMap A K (u : A) ≠ 0 := left_ne_zero_of_mul_eq_one hu
  rw [map_mul, map_mul]
  field_simp
  linear_combination (-algebraMap A K a) * hu

namespace LieLean.QuantumGroup

namespace GrandLoop

open Sl2.RankOne

/-- The ring `A = ℚ[X]_{(X)}` of rational functions regular at `X = 0`, i.e. at `v = X⁻¹ = ∞`, is
a discrete valuation ring. -/
instance : IsDiscreteValuationRing LocalRing :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial ℚ)
    (Polynomial.idealX ℚ).ne_bot (pP := (Polynomial.idealX ℚ).isPrime) LocalRing

lemma residue_surjective : Function.Surjective residue := fun q ↦
  ⟨algebraMap ℚ LocalRing q, residue_rat q⟩

lemma ker_residue : RingHom.ker residue = Ideal.span {localX} := by
  ext x
  rw [RingHom.mem_ker, residue_eq_zero_iff, Ideal.mem_span_singleton]
  rfl

lemma maximalIdeal_localRing : IsLocalRing.maximalIdeal LocalRing = Ideal.span {localX} := by
  rw [← ker_residue]
  exact (IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective _ residue_surjective)).symm

lemma irreducible_localX : Irreducible localX :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr maximalIdeal_localRing

lemma localX_mem_maximalIdeal : localX ∈ IsLocalRing.maximalIdeal LocalRing := by
  rw [maximalIdeal_localRing]
  exact Ideal.mem_span_singleton_self _

/-- `A/ϖA ≅ ℚ` is formally real. -/
instance : IsFormallyReal (LocalRing ⧸ Ideal.span {localX}) :=
  let e := (Ideal.quotEquivOfEq ker_residue.symm).trans
    (RingHom.quotientKerEquivOfSurjective residue_surjective)
  IsFormallyReal.of_injective e.toRingHom e.injective

/-- The quantum parameter `v = X⁻¹ ∈ ℚ(X)`. -/
abbrev vInf : RatFunc ℚ := RatFunc.X⁻¹

instance : NeZero vInf := ⟨inv_ne_zero RatFunc.X_ne_zero⟩

lemma transcendental_vInf : Transcendental ℚ vInf := by
  rw [Transcendental, IsAlgebraic.inv_iff]
  exact LusztigF.transcendental_ratFunc_X

lemma injective_algebraMap_localRing : Function.Injective (algebraMap LocalRing (RatFunc ℚ)) :=
  IsFractionRing.injective _ _

lemma algebraMap_localX : algebraMap LocalRing (RatFunc ℚ) localX = vInf⁻¹ := by
  rw [inv_inv, localX, ← IsScalarTower.algebraMap_apply, RatFunc.algebraMap_X]

lemma exists_pow_localX_mul (c : RatFunc ℚ) :
    ∃ (m : ℕ) (a : LocalRing),
      algebraMap LocalRing (RatFunc ℚ) (localX ^ m) * c = algebraMap LocalRing (RatFunc ℚ) a :=
  IsDiscreteValuationRing.exists_pow_mul_eq_algebraMap irreducible_localX c

variable {I : Type*} [Fintype I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- **The crystal of `L_q(λ)` over `ℚ(v)` is Littelmann's path crystal**
(`GrandLoop.existsUnique_equiv_pathCrystal'` in Kashiwara's setting): for every Cartan datum with
finite index set and every dominant `λ` of the extended root datum, `ψ_* B(λ) ≅ B(π_{ψ λ})` with
`u_λ ↦ π_{ψ λ}`, where `B(λ)` is the crystal of the crystal base of `L_q(λ)` at `v = ∞` and `ψ` is
`LusztigCartanDatum.RootDatum.stdHom`. -/
theorem existsUnique_equiv_pathCrystal_ratFunc (Λ : Dom D.extendedRootDatum) :
    ∃ Φ : Crystal.Equiv
        ((crystalHW transcendental_vInf D.isXRegular_extendedRootDatum
          injective_algebraMap_localRing localX_mem_maximalIdeal algebraMap_localX
          exists_pow_localX_mul D.exists_fundamental_extendedRootDatum Λ).mapDatum
            (D.extendedRootDatum.stdHom D.isXRegular_extendedRootDatum))
        ((Matrix.Realization.std D.cartanMatrix ℝ).pathCrystal
          D.isGeneralizedCartan_cartanMatrix
          (isDominantIntegral_hom _ (D.extendedRootDatum.stdHom D.isXRegular_extendedRootDatum)
            Λ)),
      Φ (topHW transcendental_vInf D.isXRegular_extendedRootDatum injective_algebraMap_localRing
          localX_mem_maximalIdeal Λ) =
        Matrix.Realization.pathCrystalTop _
          (isDominantIntegral_hom _ (D.extendedRootDatum.stdHom D.isXRegular_extendedRootDatum)
            Λ) :=
  (existsUnique_equiv_pathCrystal' injective_algebraMap_localRing localX_mem_maximalIdeal
    algebraMap_localX exists_pow_localX_mul D.exists_fundamental_extendedRootDatum Λ).imp
    fun _ h ↦ h.1

/-- **The crystal of `L_q(λ)` over `ℚ(v)` is normal** (`GrandLoop.isNormal_crystalHW'` in
Kashiwara's setting), for every Cartan datum with finite index set. -/
theorem isNormal_crystalHW_ratFunc (Λ : Dom D.extendedRootDatum) :
    ((crystalHW transcendental_vInf D.isXRegular_extendedRootDatum
      injective_algebraMap_localRing localX_mem_maximalIdeal algebraMap_localX
      exists_pow_localX_mul D.exists_fundamental_extendedRootDatum Λ).mapDatum
        (D.extendedRootDatum.stdHom D.isXRegular_extendedRootDatum)).IsNormal :=
  isNormal_crystalHW' injective_algebraMap_localRing localX_mem_maximalIdeal algebraMap_localX
    exists_pow_localX_mul D.exists_fundamental_extendedRootDatum Λ

end GrandLoop

end LieLean.QuantumGroup
