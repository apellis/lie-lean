/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.RatFunc
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityStar
import LieLean.Algebra.QuantumGroup.LusztigF.IntegralForm

/-!
# The norm criterion on the actual algebra `f`

We compare the original radical quotient with the Serre module quotient used by the
grand loop, preserving the original form. The coefficient ring is the local ring at
`v = ∞`, with `v = RatFunc.X` (not the inverse parameter). The homogeneous norm criterion
therefore applies to the same algebra as the integral PBW preimages.

The lattice is transported from the proved Kashiwara-operator lattice, not defined by
a norm inequality or by a conjectural canonical basis. No independence of the roots in
an ambient root datum is assumed: the grand-loop theorem is applied internally to the
extended root datum. This is a norm/lattice ingredient for 41.1.6, not its signed residue
conclusion. In particular it does not calculate the norm of a general PBW preimage.
-/

open LieLean
noncomputable section
namespace LieLean.QuantumGroup
open LusztigF GrandLoop
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

/-- The local ring at infinity, distinguished from the local ring with parameter `X`. -/
def InfinityLocalRing : Type := Sl2.RankOne.LocalRing

namespace InfinityLocalRing
instance : CommRing InfinityLocalRing := inferInstanceAs (CommRing Sl2.RankOne.LocalRing)
instance : IsDomain InfinityLocalRing := inferInstanceAs (IsDomain Sl2.RankOne.LocalRing)
instance : IsDiscreteValuationRing InfinityLocalRing :=
  inferInstanceAs (IsDiscreteValuationRing Sl2.RankOne.LocalRing)

/-- Its embedding evaluates the local parameter at `v⁻¹`. -/
def toRatFunc : InfinityLocalRing →+* 𝕂 :=
  RatFunc.bar.toRingHom.comp (algebraMap Sl2.RankOne.LocalRing 𝕂)
instance : Algebra InfinityLocalRing 𝕂 := toRatFunc.toAlgebra

def uniformizer : InfinityLocalRing := Sl2.RankOne.localX

lemma injective_algebraMap : Function.Injective (algebraMap InfinityLocalRing 𝕂) := by
  intro x y h
  apply injective_algebraMap_localRing
  change RatFunc.bar (algebraMap Sl2.RankOne.LocalRing 𝕂 x) =
    RatFunc.bar (algebraMap Sl2.RankOne.LocalRing 𝕂 y) at h
  have h' := congrArg RatFunc.bar h
  simpa only [RatFunc.bar_bar] using h'

lemma uniformizer_mem_maximalIdeal :
    uniformizer ∈ IsLocalRing.maximalIdeal InfinityLocalRing := localX_mem_maximalIdeal

lemma algebraMap_uniformizer : algebraMap InfinityLocalRing 𝕂 uniformizer = 𝕧⁻¹ := by
  change RatFunc.bar (algebraMap Sl2.RankOne.LocalRing 𝕂 Sl2.RankOne.localX) = _
  rw [algebraMap_localX, inv_inv]
  exact RatFunc.bar_X

instance : IsFormallyReal (InfinityLocalRing ⧸ Ideal.span {uniformizer}) :=
  inferInstanceAs (IsFormallyReal (Sl2.RankOne.LocalRing ⧸ Ideal.span {Sl2.RankOne.localX}))

lemma exists_pow_mul (c : 𝕂) :
    ∃ (m : ℕ) (a : InfinityLocalRing),
      algebraMap InfinityLocalRing 𝕂 (uniformizer ^ m) * c =
        algebraMap InfinityLocalRing 𝕂 a := by
  obtain ⟨m, a, h⟩ := exists_pow_localX_mul (RatFunc.bar c)
  refine ⟨m, a, ?_⟩
  have h' := congrArg RatFunc.bar h
  change RatFunc.bar (algebraMap Sl2.RankOne.LocalRing 𝕂 (Sl2.RankOne.localX ^ m)) * c =
    RatFunc.bar (algebraMap Sl2.RankOne.LocalRing 𝕂 a)
  simpa only [map_mul, RatFunc.bar_bar] using h'
end InfinityLocalRing

variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- The projection to the original radical quotient descends through the Serre module quotient. -/
def negativeToQuotient : Um D 𝕧 →ₗ[𝕂] Quotient D 𝕧 :=
  (serreSubmodule D 𝕧).liftQ (toQuotient D 𝕧).toLinearMap fun x hx ↦ by
    rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, toQuotient_eq_zero_iff,
      radical_eq_serreIdeal_ratFunc]
    exact mem_serreSubmodule.mp hx

@[simp] theorem negativeToQuotient_mk (x : LusztigF 𝕂 I) :
    negativeToQuotient D (Submodule.Quotient.mk x) = toQuotient D 𝕧 x := rfl

/-- The actual radical quotient and the grand-loop Serre quotient have identical elements. -/
def negativeQuotientEquiv : Um D 𝕧 ≃ₗ[𝕂] Quotient D 𝕧 :=
  LinearEquiv.ofBijective (negativeToQuotient D) ⟨by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.Quotient.mk_eq_zero, mem_serreSubmodule]
    exact (toQuotient_eq_zero_iff_mem_serreIdeal D transcendental_ratFunc_X).mp hx,
    fun x ↦ by
      obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
      exact ⟨Submodule.Quotient.mk x, rfl⟩⟩

@[simp] theorem negativeQuotientEquiv_symm_toQuotient (x : LusztigF 𝕂 I) :
    (negativeQuotientEquiv D).symm (toQuotient D 𝕧 x) = Submodule.Quotient.mk x :=
  (negativeQuotientEquiv D).symm_apply_apply (Submodule.Quotient.mk x)

/-- Lusztig's original form on his radical quotient. -/
def quotientForm : LinearMap.BilinForm 𝕂 (Quotient D 𝕧) :=
  (formU (D := D) (pow_ne_one_of_transcendental' transcendental_ratFunc_X)).compl₁₂
    (negativeQuotientEquiv D).symm.toLinearMap (negativeQuotientEquiv D).symm.toLinearMap

/-- The comparison preserves the original form, not a chosen Gram matrix. -/
@[simp] theorem quotientForm_toQuotient (x y : LusztigF 𝕂 I) :
    quotientForm D (toQuotient D 𝕧 x) (toQuotient D 𝕧 y) = form D 𝕧 x y := by
  simp [quotientForm, formU_mk]

/-- The actual Kashiwara lattice transported to `f`, recorded as a subset to retain
exactly the scalar action used in the grand-loop construction. -/
def quotientCrystalLattice : Set (Quotient D 𝕧) :=
  (negativeQuotientEquiv D).symm ⁻¹'
    (latInf (D := D) transcendental_ratFunc_X InfinityLocalRing : Set (Um D 𝕧))

/-- The homogeneous norm criterion on the original `f`, at the original parameter `v = X`.
It uses no root-independence hypothesis on an ambient realization. -/
theorem mem_quotientCrystalLattice_iff {ν : I →₀ ℕ} {x : Quotient D 𝕧}
    (hx : (negativeQuotientEquiv D).symm x ∈ Uw D 𝕧 ν) :
    x ∈ quotientCrystalLattice D ↔
      ∃ a : InfinityLocalRing, quotientForm D x x = algebraMap InfinityLocalRing 𝕂 a := by
  let := Fintype.ofFinite I
  exact mem_latInf_iff_formU_mem (hvt := transcendental_ratFunc_X)
    (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum hx

/-- Divided multiplication corresponds to the actual boson divided operator. -/
theorem negativeQuotientEquiv_df (i : I) (n : ℕ) (x : Um D 𝕧) :
    negativeQuotientEquiv D
        ((bos (pow_ne_one_of_transcendental' transcendental_ratFunc_X) i).df n x) =
      quotientIntegralGenerator D i n * negativeQuotientEquiv D x := by
  have hf : ∀ x : Um D 𝕧, negativeQuotientEquiv D (NegativePart.f D 𝕧 i x) =
      toQuotient D 𝕧 (θ 𝕂 i) * negativeQuotientEquiv D x := by
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change toQuotient D 𝕧 (θ 𝕂 i * x) = _
    exact map_mul _ _ _
  have hp : ∀ n : ℕ, negativeQuotientEquiv D ((NegativePart.f D 𝕧 i ^ n) x) =
      toQuotient D 𝕧 (θ 𝕂 i) ^ n * negativeQuotientEquiv D x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Module.End.mul_apply, hf, ih, pow_succ', mul_assoc]
  rw [BosonModule.df_apply, map_smul]
  change (qFactorial (𝕧 ^ D.d i)⁻¹ n)⁻¹ •
      negativeQuotientEquiv D ((NegativePart.f D 𝕧 i ^ n) x) = _
  rw [hp, qFactorial_inv]
  exact (smul_mul_assoc _ _ _).symm

/-- The local kernel factorization used in Lusztig 38.2.3(a), on the actual `f`.
The two kernel hypotheses concern the proved skew-derivation operator, not a Gram matrix. -/
theorem quotientForm_divided_mul (i : I) {x y : Quotient D 𝕧}
    (hx : (bos (pow_ne_one_of_transcendental' transcendental_ratFunc_X) i).e
      ((negativeQuotientEquiv D).symm x) = 0)
    (hy : (bos (pow_ne_one_of_transcendental' transcendental_ratFunc_X) i).e
      ((negativeQuotientEquiv D).symm y) = 0) (r s : ℕ) :
    quotientForm D (quotientIntegralGenerator D i r * x) (quotientIntegralGenerator D i s * y) =
      if r = s then coefU D 𝕧 i r * quotientForm D x y else 0 := by
  have he (n : ℕ) (z : Quotient D 𝕧) :
      (negativeQuotientEquiv D).symm (quotientIntegralGenerator D i n * z) =
        (bos (pow_ne_one_of_transcendental' transcendental_ratFunc_X) i).df n
          ((negativeQuotientEquiv D).symm z) := by
    apply (negativeQuotientEquiv D).injective
    rw [(negativeQuotientEquiv D).apply_symm_apply, negativeQuotientEquiv_df,
      (negativeQuotientEquiv D).apply_symm_apply]
  change formU _ ((negativeQuotientEquiv D).symm _) ((negativeQuotientEquiv D).symm _) = _
  rw [he, he]
  exact formU_df_df _ i hx hy r s

omit [Finite I] [DecidableEq I] in
/-- The divided-power norm multiplier has residue one in the actual ring at `v = ∞`.
No norm bound is postulated. -/
theorem quotientForm_divided_norm_factor (i : I) (r : ℕ) :
    ∃ a : InfinityLocalRing, coefU D 𝕧 i r =
      algebraMap InfinityLocalRing 𝕂 (1 + InfinityLocalRing.uniformizer * a) :=
  exists_coefU InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer i r

/-- The actual simple divided powers have their proved norm, rather than an assumed unit norm. -/
theorem quotientForm_integralGenerator (i : I) (n : ℕ) :
    quotientForm D (quotientIntegralGenerator D i n) (quotientIntegralGenerator D i n) =
      coefU D 𝕧 i n := by
  have hone : (negativeQuotientEquiv D).symm 1 = Submodule.Quotient.mk (1 : LusztigF 𝕂 I) := by
    simpa using negativeQuotientEquiv_symm_toQuotient D (1 : LusztigF 𝕂 I)
  have he : (bos (pow_ne_one_of_transcendental' transcendental_ratFunc_X) i).e
      ((negativeQuotientEquiv D).symm 1) = 0 := by
    rw [hone]
    change NegativePart.e D 𝕧 RatFunc.X_ne_zero
      (pow_ne_one_of_transcendental' transcendental_ratFunc_X) i (NegativePart.mk 1) = 0
    simp [NegativePart.e_mk, LusztigF.bosonE]
  have hf : quotientForm D 1 1 = 1 := by
    simpa using quotientForm_toQuotient D (1 : LusztigF 𝕂 I) 1
  simpa [hf] using quotientForm_divided_mul D i he he n n

/-- A norm congruence in the concrete infinity ring for all simple divided powers. -/
theorem quotientForm_integralGenerator_residue (i : I) (n : ℕ) :
    ∃ a : InfinityLocalRing,
      quotientForm D (quotientIntegralGenerator D i n) (quotientIntegralGenerator D i n) =
        algebraMap InfinityLocalRing 𝕂 (1 + InfinityLocalRing.uniformizer * a) := by
  rw [quotientForm_integralGenerator]
  exact quotientForm_divided_norm_factor D i n

/-- Simple divided powers in the original integral `f` belong to the actual lattice.
This is a genuine norm-criterion application, valid at every node of every Cartan datum. -/
theorem quotientIntegralGenerator_mem_lattice (i : I) (n : ℕ) :
    quotientIntegralGenerator D i n ∈ quotientCrystalLattice D := by
  have hp : ∀ n : ℕ, θ 𝕂 i ^ n ∈ LusztigF.weightSpace 𝕂 (n • Finsupp.single i 1) := by
    intro n
    induction n with
    | zero => simpa using (one_mem_weightSpace (k := 𝕂) (I := I))
    | succ n ih =>
      simpa [pow_succ, add_smul] using mul_mem_weightSpace ih (θ_mem_weightSpace i)
  have hg : quotientIntegralGenerator D i n =
      toQuotient D 𝕧 (qDivPow (𝕧 ^ D.d i) n (θ 𝕂 i)) := by
    simp [quotientIntegralGenerator, qDivPow]
  have hw : (negativeQuotientEquiv D).symm (quotientIntegralGenerator D i n) ∈
      Uw D 𝕧 (n • Finsupp.single i 1) := by
    rw [hg, negativeQuotientEquiv_symm_toQuotient]
    exact ⟨_, Submodule.smul_mem _ _ (hp n), rfl⟩
  apply (mem_quotientCrystalLattice_iff D hw).mpr
  obtain ⟨a, ha⟩ := quotientForm_integralGenerator_residue D i n
  exact ⟨_, ha⟩

end LieLean.QuantumGroup
