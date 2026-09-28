/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.HarishChandra
import Mathlib.Algebra.Polynomial.Roots

/-!
# Arbitrary-weight Harish-Chandra invariance

## Main definitions

* `SymmetricAlgebra.affineLine`: polynomial restriction to an affine dual line.
* `SymmetricAlgebra.affinePullback`: genuine polynomial pullback of an affine dual map.
* `shiftedHarishChandra`: the actual HC map followed by translation by negative rho.

## Main results

* `VermaModule.centralCharacter_weyl`: arbitrary-weight dot-Weyl invariance.
* `harishChandra_dot_reflection`: polynomial-level dot-reflection invariance.
* `eval_shiftedHarishChandra_weyl`: ordinary Weyl invariance of the shifted polynomial.
* `shiftedHarishChandra_reflection`: ordinary reflection fixes the actual shifted polynomial.

## Source status

Reconstructed argument: restrict the actual Harish-Chandra polynomial to affine lines,
use actual Verma embeddings on integral coroot hyperplanes, and apply the polynomial
identity theorem. No source was consulted for this extension. No image, isomorphism,
or converse character-separation theorem is assumed or asserted.
-/

open Module

noncomputable section

namespace SymmetricAlgebra

variable {K H : Type*} [Field K] [AddCommGroup H] [Module K H]

/-- Restriction of a symmetric-algebra polynomial to an affine line in the dual space. -/
def affineLine (Λ μ : Dual K H) : SymmetricAlgebra K H →ₐ[K] Polynomial K :=
  lift (((Polynomial.CAlgHom (R := K) (A := K)).toLinearMap.comp Λ) +
    (Polynomial.X : Polynomial K) • ((Polynomial.CAlgHom (R := K) (A := K)).toLinearMap.comp μ))

/-- Evaluation of the affine-line restriction is evaluation at the corresponding weight. -/
theorem eval_affineLine (Λ μ : Dual K H) (t : K) (p : SymmetricAlgebra K H) :
    Polynomial.eval t (affineLine Λ μ p) = lift (Λ + t • μ) p := by
  have he : (Polynomial.aeval t).comp (affineLine Λ μ) = lift (Λ + t • μ) := by
    apply algHom_ext
    ext h
    simpa [affineLine] using mul_comm (μ h) t
  exact DFunLike.congr_fun he p

/-- Equality on the natural parameters of two affine lines extends to every parameter.
Reconstructed univariate density argument; no dimension bound on the Cartan space is needed. -/
theorem lift_affine_eq_of_nat [CharZero K] (p q : SymmetricAlgebra K H)
    (Λ μ Λ' μ' : Dual K H)
    (hn : ∀ n : ℕ, lift (Λ + (n : K) • μ) p = lift (Λ' + (n : K) • μ') q)
    (t : K) : lift (Λ + t • μ) p = lift (Λ' + t • μ') q := by
  have he : affineLine Λ μ p = affineLine Λ' μ' q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R := K))).mono
    rintro x ⟨n, rfl⟩
    simpa only [Set.mem_ofPred_eq, eval_affineLine] using hn n
  simpa only [eval_affineLine] using congrArg (Polynomial.eval t) he

/-- Pullback along a linear map of the Cartan space plus a constant dual shift. -/
def affinePullback (f : H →ₗ[K] H) (δ : Dual K H) :
    SymmetricAlgebra K H →ₐ[K] SymmetricAlgebra K H :=
  lift ((ι K H).comp f + (Algebra.linearMap K (SymmetricAlgebra K H)).comp δ)

/-- Affine pullback evaluates by precomposing the weight and then adding the shift. -/
theorem lift_affinePullback (f : H →ₗ[K] H) (δ Λ : Dual K H)
    (p : SymmetricAlgebra K H) :
    lift Λ (affinePullback f δ p) = lift (Λ.comp f + δ) p := by
  have he : (lift Λ).comp (affinePullback f δ) = lift (Λ.comp f + δ) := by
    apply algHom_ext
    ext h
    simp [affinePullback]
  exact DFunLike.congr_fun he p

end SymmetricAlgebra

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝓤" => UniversalEnvelopingAlgebra K (KacMoodyAlgebra P)

/-- The unshifted HC polynomial is invariant under simple dot reflection at every weight.
Reconstructed from integral-coroot Verma embeddings and affine-line polynomial density.
Only the selected coroot pairing is integral in the density premise, not the whole weight. -/
theorem eval_harishChandra_reflection (hA : A.IsGeneralizedCartan)
    (i : ι) (Λ : Dual K H) (z : Subalgebra.center K 𝓤) :
    SymmetricAlgebra.lift (P.reflection hA i (Λ + P.rho) - P.rho)
      (harishChandra P z) = SymmetricAlgebra.lift Λ (harishChandra P z) := by
  let a : K := (Λ + P.rho) (P.coroot i)
  let ν : Dual K H := Λ - a • P.rho
  have hn : ∀ n : ℕ,
      SymmetricAlgebra.lift
        ((P.reflection hA i (ν + P.rho) - P.rho) +
          (n : K) • P.reflection hA i P.rho) (harishChandra P z) =
      SymmetricAlgebra.lift (ν + (n : K) • P.rho) (harishChandra P z) := by
    intro n
    have hi : ((ν + (n : K) • P.rho) + P.rho) (P.coroot i) = (n : ℤ) := by
      simp only [ν, a, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        P.rho_coroot, smul_eq_mul, mul_one, Int.cast_natCast]
      ring
    have hc := VermaModule.centralCharacter_reflection_of_integral P hA
      (Λ := ν + (n : K) • P.rho) i ⟨(n : ℤ), hi⟩
    have hw : P.reflection hA i (ν + (n : K) • P.rho + P.rho) - P.rho =
        (P.reflection hA i (ν + P.rho) - P.rho) +
          (n : K) • P.reflection hA i P.rho := by
      rw [map_add, map_add, map_smul, map_add]
      abel
    rw [← hw]
    exact (eval_harishChandraProjection_center P _ z).trans
      ((DFunLike.congr_fun hc z).trans (eval_harishChandraProjection_center P _ z).symm)
  have he := SymmetricAlgebra.lift_affine_eq_of_nat (harishChandra P z)
    (harishChandra P z) (P.reflection hA i (ν + P.rho) - P.rho)
    (P.reflection hA i P.rho) ν P.rho hn a
  have hr : ν + a • P.rho = Λ := sub_add_cancel Λ (a • P.rho)
  have hl : (P.reflection hA i (ν + P.rho) - P.rho) +
      a • P.reflection hA i P.rho = P.reflection hA i (Λ + P.rho) - P.rho := by
    rw [← hr]
    simp only [map_add, map_smul]
    abel
  rwa [hr, hl] at he

/-- Arbitrary-weight simple dot-reflection invariance of the actual full-centre character.
Reconstructed through the actual PBW polynomial bridge, not a classification premise. -/
theorem VermaModule.centralCharacter_reflection (hA : A.IsGeneralizedCartan)
    (i : ι) (Λ : Dual K H) :
    VermaModule.centralCharacter P (P.reflection hA i (Λ + P.rho) - P.rho) =
      VermaModule.centralCharacter P Λ := by
  ext z
  exact (eval_harishChandraProjection_center P _ z).symm.trans
    ((eval_harishChandra_reflection P hA i Λ z).trans
      (eval_harishChandraProjection_center P _ z))

/-- Arbitrary-weight dot-Weyl invariance of the actual full-centre Verma character.
Reconstructed by simple-reflection density and Weyl-group induction, for every char-zero GCM. -/
theorem VermaModule.centralCharacter_weyl (hA : A.IsGeneralizedCartan)
    {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA) (Λ : Dual K H) :
    VermaModule.centralCharacter P (w (Λ + P.rho) - P.rho) =
      VermaModule.centralCharacter P Λ := by
  refine P.weylGroup_induction hA (p := fun w ↦
    VermaModule.centralCharacter P (w (Λ + P.rho) - P.rho) =
      VermaModule.centralCharacter P Λ) (by simp) (fun i w ih ↦ ?_) hw
  rw [LinearEquiv.mul_apply]
  have he := VermaModule.centralCharacter_reflection P hA i (w (Λ + P.rho) - P.rho)
  simpa only [sub_add_cancel] using he.trans ih

/-- All dot-Weyl translates evaluate the same actual unshifted HC polynomial. -/
theorem eval_harishChandra_weyl (hA : A.IsGeneralizedCartan)
    {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    (Λ : Dual K H) (z : Subalgebra.center K 𝓤) :
    SymmetricAlgebra.lift (w (Λ + P.rho) - P.rho) (harishChandra P z) =
      SymmetricAlgebra.lift Λ (harishChandra P z) :=
  (eval_harishChandraProjection_center P _ z).trans
    ((DFunLike.congr_fun (VermaModule.centralCharacter_weyl P hA hw Λ) z).trans
      (eval_harishChandraProjection_center P _ z).symm)

/-- Polynomial equality, not just evaluation equality: the unshifted HC image is
fixed by the affine pullback of each dot reflection. Reconstructed from density. -/
theorem harishChandra_dot_reflection (hA : A.IsGeneralizedCartan)
    (i : ι) (z : Subalgebra.center K 𝓤) :
    SymmetricAlgebra.affinePullback (P.coreflection hA i).toLinearMap
      (P.rho.comp (P.coreflection hA i).toLinearMap - P.rho) (harishChandra P z) =
        harishChandra P z := by
  apply SymmetricAlgebra.eq_of_lift_eq
  intro Λ
  rw [SymmetricAlgebra.lift_affinePullback]
  have hw : Λ.comp (P.coreflection hA i).toLinearMap +
      (P.rho.comp (P.coreflection hA i).toLinearMap - P.rho) =
      P.reflection hA i (Λ + P.rho) - P.rho := by
    ext h
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, P.reflection_apply_apply]
    ring
  rw [hw]
  exact eval_harishChandra_reflection P hA i Λ z

/-- The rho-shifted HC map: its polynomial at `μ` is the unshifted polynomial at `μ - ρ`.
This is the sign convention that converts dot invariance into ordinary Weyl invariance. -/
def shiftedHarishChandra : Subalgebra.center K 𝓤 →ₐ[K] SymmetricAlgebra K H :=
  (SymmetricAlgebra.affinePullback (LinearMap.id : H →ₗ[K] H) (-P.rho)).comp
    (harishChandra P)

/-- The shifted HC polynomial evaluates to the actual Verma character of `μ - ρ`. -/
theorem eval_shiftedHarishChandra (μ : Dual K H) (z : Subalgebra.center K 𝓤) :
    SymmetricAlgebra.lift μ (shiftedHarishChandra P z) =
      VermaModule.centralCharacter P (μ - P.rho) z := by
  change SymmetricAlgebra.lift μ
    (SymmetricAlgebra.affinePullback LinearMap.id (-P.rho) (harishChandra P z)) = _
  rw [SymmetricAlgebra.lift_affinePullback, LinearMap.comp_id, ← sub_eq_add_neg]
  exact eval_harishChandraProjection_center P _ z

/-- The shifted HC image is invariant under ordinary Weyl action at arbitrary weights. -/
theorem eval_shiftedHarishChandra_weyl (hA : A.IsGeneralizedCartan)
    {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    (μ : Dual K H) (z : Subalgebra.center K 𝓤) :
    SymmetricAlgebra.lift (w μ) (shiftedHarishChandra P z) =
      SymmetricAlgebra.lift μ (shiftedHarishChandra P z) := by
  rw [eval_shiftedHarishChandra, eval_shiftedHarishChandra]
  have he := DFunLike.congr_fun (VermaModule.centralCharacter_weyl P hA hw (μ - P.rho)) z
  simpa only [sub_add_cancel] using he

/-- Actual polynomial equality: ordinary Cartan reflection fixes the rho-shifted HC image. -/
theorem shiftedHarishChandra_reflection (hA : A.IsGeneralizedCartan)
    (i : ι) (z : Subalgebra.center K 𝓤) :
    SymmetricAlgebra.affinePullback (P.coreflection hA i).toLinearMap 0
      (shiftedHarishChandra P z) = shiftedHarishChandra P z := by
  apply SymmetricAlgebra.eq_of_lift_eq
  intro μ
  rw [SymmetricAlgebra.lift_affinePullback, add_zero]
  have he : μ.comp (P.coreflection hA i).toLinearMap = P.reflection hA i μ := by
    ext h
    exact (P.reflection_apply_apply hA i μ h).symm
  rw [he]
  exact eval_shiftedHarishChandra_weyl P hA (P.reflection_mem_weylGroup hA i) μ z

end Matrix.Realization.KacMoodyAlgebra
