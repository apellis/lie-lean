/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaCentralCharacter
import LieLean.Algebra.Lie.KacMoody.Shapovalov
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.CharZero.Infinite

/-!
# PBW Harish-Chandra projection and actual Verma central characters

The map is constructed from the actual PBW inverse `U(g) ≃ U(n₋) ⊗ U(b)`:
augment the negative factor and send the Borel factor to `SymmetricAlgebra K H`
by its Cartan projection. It is independent of the highest weight.

## Main results

* `eval_harishChandraProjection`: evaluation is the actual highest-vector coefficient.
* `eval_harishChandraProjection_center`: evaluation recovers `centralCharacter` for every weight.
* `harishChandra`: the restriction is an algebra homomorphism on the actual full centre.
* `eval_comp_harishChandra`: every Verma central character factors through this map.

## Source status

Reconstructed proof of the standard PBW projection/evaluation argument; for finite-dimensional
semisimple `𝔤` over `ℂ` it is J. E. Humphreys, *Representations of semisimple Lie algebras in
the BGG category 𝒪*, GSM 94, §1.7.
No isomorphism, character classification, or finite-type character separation is assumed or claimed.
-/

open Module LieModule TensorProduct

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝓤" => UniversalEnvelopingAlgebra K (KacMoodyAlgebra P)
local notation "𝓢" => SymmetricAlgebra K H
local notation "mapN" => UniversalEnvelopingAlgebra.map (LieSubalgebra.incl (nNeg P))
local notation "mapB" => UniversalEnvelopingAlgebra.map (LieSubalgebra.incl (borel P))

/-- The universal, polynomial-valued Borel character, from its actual Cartan projection. -/
def borelCartanPolynomial : borel P →ₗ⁅K⁆ 𝓢 where
  toLinearMap := SymmetricAlgebra.ι K H ∘ₗ cartanProj P ∘ₗ (borel P).incl.toLinearMap
  map_lie' {x y} := by
    change SymmetricAlgebra.ι K H (cartanProj P ((⁅x, y⁆ : borel P) :
      P.KacMoodyAlgebra)) = _
    rw [LieSubalgebra.coe_bracket,
      cartanProj_of_mem_nPos P (lie_mem_nPos_of_mem_borel P x.2 y.2), map_zero,
      LieRing.of_associative_ring_bracket, mul_comm, sub_self]

/-- The algebra extension of the polynomial-valued Borel character. -/
def envBorelCartanPolynomial : UniversalEnvelopingAlgebra K (borel P) →ₐ[K] 𝓢 :=
  UniversalEnvelopingAlgebra.lift K (borelCartanPolynomial P)

/-- Specialization of the universal Borel character is the existing Borel character. -/
theorem eval_envBorelCartanPolynomial (Λ : Dual K H) :
    (SymmetricAlgebra.lift Λ).comp (envBorelCartanPolynomial P) =
      VermaModule.envBorelChar P Λ := by
  apply UniversalEnvelopingAlgebra.hom_ext
  ext x
  change SymmetricAlgebra.lift Λ
    (UniversalEnvelopingAlgebra.lift K (borelCartanPolynomial P)
      (UniversalEnvelopingAlgebra.ι K x)) =
    UniversalEnvelopingAlgebra.lift K (borelChar P Λ) (UniversalEnvelopingAlgebra.ι K x)
  rw [UniversalEnvelopingAlgebra.lift_ι_apply, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact SymmetricAlgebra.lift_ι_apply Λ (cartanProj P x)

/-- The weight-independent PBW Harish-Chandra projection to the actual Cartan symmetric algebra.
Reconstructed from PBW by augmentation on the negative factor. -/
def harishChandraProjection : 𝓤 →ₗ[K] 𝓢 :=
  (TensorProduct.lid K 𝓢).toLinearMap ∘ₗ
    TensorProduct.map (VermaModule.counitNNeg P).toLinearMap
      (envBorelCartanPolynomial P).toLinearMap ∘ₗ
    (VermaModule.mulEquiv P).symm.toLinearMap

/-- The PBW normal-order formula defining the projection. -/
theorem harishChandraProjection_mul (n : UniversalEnvelopingAlgebra K (nNeg P))
    (b : UniversalEnvelopingAlgebra K (borel P)) :
    harishChandraProjection P (mapN n * mapB b) =
      VermaModule.counitNNeg P n • envBorelCartanPolynomial P b := by
  have ht : (VermaModule.mulEquiv P).symm (mapN n * mapB b) = n ⊗ₜ b := by
    rw [LinearEquiv.symm_apply_eq, UniversalEnvelopingAlgebra.tensorEquivOfIsCompl_apply_tmul]
  simp [harishChandraProjection, ht]

/-- On the Borel enveloping algebra the PBW projection is its universal character. -/
theorem harishChandraProjection_map_borel (b : UniversalEnvelopingAlgebra K (borel P)) :
    harishChandraProjection P (mapB b) = envBorelCartanPolynomial P b := by
  simpa using harishChandraProjection_mul P 1 b

/-- Cartan generators are retained as genuine symmetric-algebra generators. -/
theorem harishChandraProjection_h (a : H) :
    harishChandraProjection P (UniversalEnvelopingAlgebra.ι K (h P a)) =
      SymmetricAlgebra.ι K H a := by
  have ht := harishChandraProjection_map_borel P
    (UniversalEnvelopingAlgebra.ι K ⟨h P a, h_mem_borel P a⟩)
  rw [UniversalEnvelopingAlgebra.map_ι] at ht
  change harishChandraProjection P (UniversalEnvelopingAlgebra.ι K (h P a)) = _ at ht
  rw [ht]
  change UniversalEnvelopingAlgebra.lift K (borelCartanPolynomial P)
    (UniversalEnvelopingAlgebra.ι K ⟨h P a, h_mem_borel P a⟩) = _
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  change SymmetricAlgebra.ι K H (cartanProj P (h P a)) = _
  rw [cartanProj_h]

/-- Evaluation of the PBW projection is the highest-vector coefficient for every weight.
Reconstructed from PBW and the defining Verma relations; centrality is not required. -/
theorem eval_harishChandraProjection (Λ : Dual K H) (u : 𝓤) :
    SymmetricAlgebra.lift Λ (harishChandraProjection P u) =
      VermaModule.hwCoord P Λ (VermaModule.mk P Λ u) := by
  obtain ⟨t, rfl⟩ := (VermaModule.mulEquiv P).surjective u
  induction t using TensorProduct.inductionOn with
  | tmul n b =>
    rw [UniversalEnvelopingAlgebra.tensorEquivOfIsCompl_apply_tmul,
      harishChandraProjection_mul, map_smul]
    have he : SymmetricAlgebra.lift Λ (envBorelCartanPolynomial P b) =
        VermaModule.envBorelChar P Λ b :=
      DFunLike.congr_fun (eval_envBorelCartanPolynomial P Λ) b
    rw [he, VermaModule.mk_eq_smul, mul_smul, ← VermaModule.mk_eq_smul P Λ (mapB b),
      VermaModule.mk_map_borel, smul_comm,
      ← VermaModule.equivEnvNNeg_apply, map_smul]
    change VermaModule.counitNNeg P n * VermaModule.envBorelChar P Λ b =
      VermaModule.envBorelChar P Λ b * VermaModule.counitNNeg P
        ((VermaModule.equivEnvNNeg P Λ).symm (VermaModule.equivEnvNNeg P Λ n))
    rw [LinearEquiv.symm_apply_apply, mul_comm]
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Evaluation of the actual PBW central polynomial recovers the existing Verma character
at arbitrary, not necessarily integral, weights. Reconstructed PBW argument. -/
theorem eval_harishChandraProjection_center (Λ : Dual K H) (z : Subalgebra.center K 𝓤) :
    SymmetricAlgebra.lift Λ (harishChandraProjection P (z : 𝓤)) =
      VermaModule.centralCharacter P Λ z := by
  rw [eval_harishChandraProjection, VermaModule.mk_eq_smul,
    VermaModule.centralCharacter_smul, map_smul, VermaModule.hwCoord_hwv, smul_eq_mul, mul_one]

end Matrix.Realization.KacMoodyAlgebra

namespace SymmetricAlgebra

/-- Over an infinite field, evaluations at all linear weights distinguish symmetric-algebra
polynomials. Reconstructed using Mathlib's multivariate polynomial identity theorem. -/
theorem eq_of_lift_eq {K H : Type*} [Field K] [Infinite K] [AddCommGroup H] [Module K H]
    {p q : SymmetricAlgebra K H}
    (hpq : ∀ Λ : Dual K H, lift Λ p = lift Λ q) : p = q := by
  let b := Module.Free.chooseBasis K H
  let e := equivMvPolynomial b
  apply e.injective
  apply MvPolynomial.funext
  intro x
  have he : (lift (b.constr K x)).comp e.symm.toAlgHom = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [e]
  have hp := DFunLike.congr_fun he (e p)
  have hq := DFunLike.congr_fun he (e q)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at hp hq
  simpa only [MvPolynomial.aeval_eq_eval] using
    hp.symm.trans ((hpq (b.constr K x)).trans hq)

end SymmetricAlgebra

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝓤" => UniversalEnvelopingAlgebra K (KacMoodyAlgebra P)

/-- The actual PBW projection is multiplicative on the full enveloping centre.
Reconstructed by evaluation at every weight, not by assuming character classification. -/
theorem harishChandraProjection_center_mul (z w : Subalgebra.center K 𝓤) :
    harishChandraProjection P ((z * w : Subalgebra.center K 𝓤) : 𝓤) =
      harishChandraProjection P (z : 𝓤) * harishChandraProjection P (w : 𝓤) := by
  apply SymmetricAlgebra.eq_of_lift_eq
  intro Λ
  rw [map_mul, eval_harishChandraProjection_center, eval_harishChandraProjection_center,
    eval_harishChandraProjection_center, map_mul]

/-- The unshifted Harish-Chandra algebra homomorphism on the actual enveloping centre.
No injectivity, surjectivity, or classification premise is used. -/
def harishChandra : Subalgebra.center K 𝓤 →ₐ[K] SymmetricAlgebra K H where
  toFun z := harishChandraProjection P (z : 𝓤)
  map_one' := by
    apply SymmetricAlgebra.eq_of_lift_eq
    intro Λ
    rw [eval_harishChandraProjection_center, map_one, map_one]
  map_mul' := harishChandraProjection_center_mul P
  map_zero' := (harishChandraProjection P).map_zero
  map_add' z w := (harishChandraProjection P).map_add (z : 𝓤) (w : 𝓤)
  commutes' c := by
    apply SymmetricAlgebra.eq_of_lift_eq
    intro Λ
    rw [eval_harishChandraProjection_center, AlgHom.commutes, AlgHom.commutes]

/-- All existing Verma characters factor through this single weight-independent polynomial map.
This is a genuine evaluation identity for arbitrary weights, not only integral ones. -/
theorem eval_comp_harishChandra (Λ : Dual K H) :
    (SymmetricAlgebra.lift Λ).comp (harishChandra P) =
      VermaModule.centralCharacter P Λ := by
  ext z
  exact eval_harishChandraProjection_center P Λ z

end Matrix.Realization.KacMoodyAlgebra
