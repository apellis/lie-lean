/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.HarishChandraGraded
import LieLean.Algebra.Lie.KacMoody.FiniteType
import Mathlib.Algebra.Lie.CartanCriterion

/-!
# Infinitesimal invariant restriction toward Chevalley

## Main results

The genuine triangular Cartan restriction sends every infinitesimal adjoint-invariant
symbol to an ordinary Weyl-invariant Cartan symbol, in all degrees and for arbitrary
polynomials. No invariant extension or HC image statement is an assumption.

* `cartanRestriction_reflection_of_invariant`: all-degree invariant-symbol restriction.
* `killingSymbolEquiv_invariant_iff`: adjoint/coadjoint invariants identified in finite type.
* `coordinateCartanRestriction_killingSymbolEquiv`: the actual restriction diagram commutes.
* `coordinateCartanRestriction_weyl_of_invariant`: actual coordinate-polynomial restriction
  lands in the Weyl fixed polynomials, for the supplied finite-type realization.

Full and Cartan Killing nondegeneracy are proved from existing finite-type semisimplicity,
Cartan's criterion, and the actual triangular root decomposition. The Cartan Killing map
intertwines the existing Weyl reflections by the Chevalley-generator bracket relations.

## References

Etingof, MIT 18.757 (Fall 2023), Lecture 10, Theorem 10.1(i) and Remark 10.2(1).
The source works with a complex semisimple Lie algebra and identifies its dual by the
Killing form. Our proof of the symmetric-algebra restriction statement is reconstructed:
normalized symmetrization, the established HC invariance, and genuine graded HC
compatibility replace integration to an adjoint group. This proves this direction for
the supplied characteristic-zero GCM realization, not Chevalley bijectivity. Elements
of `SymmetricAlgebra K L` are symbols (polynomials on the dual); they are not silently
identified with `SymmetricAlgebra K (Module.Dual K L)`.
-/

noncomputable section
open Module

namespace SymmetricAlgebra

variable {K : Type} {M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

/-- Every genuine homogeneous projection takes values in its full degree component. -/
theorem homogeneousComponent_mem (n : ℕ) (p : SymmetricAlgebra K M) :
    homogeneousComponent n p ∈ homogeneousSubmodule n := by
  rw [mem_homogeneousSubmodule_iff (Free.chooseBasis K M),
    equivMvPolynomial_homogeneousComponent]
  exact MvPolynomial.homogeneousComponent_isHomogeneous n _

/-- A degree-preserving linear map commutes with genuine homogeneous projections. -/
theorem homogeneousComponent_naturality
    (F : SymmetricAlgebra K M →ₗ[K] SymmetricAlgebra K N)
    (hF : ∀ n p, p ∈ homogeneousSubmodule n → F p ∈ homogeneousSubmodule n)
    (n : ℕ) (p : SymmetricAlgebra K M) :
    homogeneousComponent n (F p) = F (homogeneousComponent n p) := by
  classical
  let b := Free.chooseBasis K M
  obtain ⟨q, rfl⟩ := (equivMvPolynomial b).symm.surjective p
  induction q using MvPolynomial.induction_on' with
  | monomial s c =>
    have hp : (equivMvPolynomial b).symm (MvPolynomial.monomial s c) ∈
        homogeneousSubmodule s.degree := by
      rw [mem_homogeneousSubmodule_iff b, AlgEquiv.apply_symm_apply]
      exact MvPolynomial.isHomogeneous_monomial c rfl
    rw [homogeneousComponent_of_mem (hF _ _ hp), homogeneousComponent_of_mem hp]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Linear substitutions commute with homogeneous projections. -/
theorem homogeneousComponent_lift_comp_ι (f : M →ₗ[K] N) (n : ℕ)
    (p : SymmetricAlgebra K M) :
    homogeneousComponent n (lift ((ι K N).comp f) p) =
      lift ((ι K N).comp f) (homogeneousComponent n p) :=
  homogeneousComponent_naturality (lift ((ι K N).comp f)).toLinearMap
    (fun _ _ hp => lift_comp_ι_mem_homogeneous f _ hp) n p

/-- The derivation extended from an endomorphism preserves every full degree component. -/
theorem derivation_mem_homogeneous (D : M →ₗ[K] M) (n : ℕ)
    {p : SymmetricAlgebra K M} (hp : p ∈ homogeneousSubmodule n) :
    derivation D p ∈ homogeneousSubmodule n := by
  rw [← SymmetricPower.range_toSymmetricAlgebra (K := K) (M := M) n] at hp ⊢
  obtain ⟨s, rfl⟩ := hp
  rw [← SymmetricPower.toSymmetricAlgebra_diagonal]
  exact LinearMap.mem_range_self _ _

/-- In particular the infinitesimal adjoint action commutes with homogeneous projection. -/
theorem homogeneousComponent_derivation (D : M →ₗ[K] M) (n : ℕ)
    (p : SymmetricAlgebra K M) :
    homogeneousComponent n (derivation D p) = derivation D (homogeneousComponent n p) :=
  homogeneousComponent_naturality (derivation D).toLinearMap
    (fun _ _ hp => derivation_mem_homogeneous D _ hp) n p

/-- Homogeneous components determine a symbol, including its constant component. -/
theorem eq_of_homogeneousComponent_eq (p q : SymmetricAlgebra K M)
    (hpq : ∀ n, homogeneousComponent n p = homogeneousComponent n q) : p = q := by
  apply (equivMvPolynomial (Free.chooseBasis K M)).injective
  ext d
  have hh := congrArg
    (fun r => (equivMvPolynomial (Free.chooseBasis K M) r).coeff d) (hpq d.degree)
  simpa only [equivMvPolynomial_homogeneousComponent,
    MvPolynomial.coeff_homogeneousComponent, ite_true] using hh

/-- The algebra isomorphism induced by a linear equivalence, with explicit inverse. -/
def equivOfLinearEquiv (e : M ≃ₗ[K] N) :
    SymmetricAlgebra K M ≃ₐ[K] SymmetricAlgebra K N :=
  AlgEquiv.ofAlgHom (lift ((ι K N).comp e.toLinearMap))
    (lift ((ι K M).comp e.symm.toLinearMap)) (by
      apply algHom_ext
      ext x
      simp) (by
      apply algHom_ext
      ext x
      simp)

@[simp] theorem equivOfLinearEquiv_apply (e : M ≃ₗ[K] N) (p : SymmetricAlgebra K M) :
    equivOfLinearEquiv e p = lift ((ι K N).comp e.toLinearMap) p := rfl

/-- Extending an intertwiner to symmetric algebras intertwines the extended derivations.
The coadjoint application below retains its contragredient minus sign. -/
theorem derivation_lift_comp_ι (f : M →ₗ[K] N) (D : M →ₗ[K] M) (E : N →ₗ[K] N)
    (hf : ∀ x, f (D x) = E (f x)) (p : SymmetricAlgebra K M) :
    derivation E (lift ((ι K N).comp f) p) =
      lift ((ι K N).comp f) (derivation D p) := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap c => simp
  | ι x => simp [hf]
  | mul p q hp hq => simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

end SymmetricAlgebra

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝔤" => KacMoodyAlgebra P

/-- Homogeneous infinitesimal adjoint invariants restrict to ordinary reflection invariants.
This is the homogeneous symmetric-symbol direction of Etingof, Lecture 10, Thm. 10.1(i),
reconstructed via the independently proved central lift and graded HC identities. -/
theorem cartanRestriction_reflection_of_invariant_homogeneous
    (hA : A.IsGeneralizedCartan) (n : ℕ)
    (p : SymmetricAlgebra.homogeneousSubmodule (K := K) (M := 𝔤) n)
    (hp : ∀ x : 𝔤, SymmetricAlgebra.derivation (LieAlgebra.ad K 𝔤 x) p.val = 0)
    (i : ι) :
    SymmetricAlgebra.affinePullback (P.coreflection hA i).toLinearMap 0
      (cartanRestriction P p.val) = cartanRestriction P p.val := by
  obtain ⟨z, _, _, hz⟩ := exists_centralLift_shiftedHarishChandra_top P n p hp
  rw [← hz]
  have he := congrArg (SymmetricAlgebra.homogeneousComponent (M := H) n)
    (shiftedHarishChandra_reflection P hA i z)
  simpa only [SymmetricAlgebra.affinePullback, LinearMap.comp_zero, add_zero,
    SymmetricAlgebra.homogeneousComponent_lift_comp_ι] using he

/-- Every infinitesimal adjoint-invariant symbol restricts to an ordinary reflection
invariant polynomial, without a homogeneity premise. Reconstructed proof of the
symmetric-symbol direction of Etingof, Lecture 10, Thm. 10.1(i). -/
theorem cartanRestriction_reflection_of_invariant
    (hA : A.IsGeneralizedCartan) (p : SymmetricAlgebra K 𝔤)
    (hp : ∀ x : 𝔤, SymmetricAlgebra.derivation (LieAlgebra.ad K 𝔤 x) p = 0)
    (i : ι) :
    SymmetricAlgebra.affinePullback (P.coreflection hA i).toLinearMap 0
      (cartanRestriction P p) = cartanRestriction P p := by
  apply SymmetricAlgebra.eq_of_homogeneousComponent_eq
  intro n
  have hn (x : 𝔤) : SymmetricAlgebra.derivation (LieAlgebra.ad K 𝔤 x)
      (SymmetricAlgebra.homogeneousComponent n p) = 0 := by
    rw [← SymmetricAlgebra.homogeneousComponent_derivation, hp x, map_zero]
  have hh := cartanRestriction_reflection_of_invariant_homogeneous P hA n
    ⟨_, SymmetricAlgebra.homogeneousComponent_mem n p⟩ hn i
  simpa only [SymmetricAlgebra.affinePullback, LinearMap.comp_zero, add_zero,
    cartanRestriction, SymmetricAlgebra.homogeneousComponent_lift_comp_ι] using hh

/-- The restricted invariant symbol has equal evaluations on every ordinary Weyl orbit.
The group acts on the dual Cartan, as in the production HC invariance theorem. -/
theorem eval_cartanRestriction_weyl_of_invariant
    (hA : A.IsGeneralizedCartan) (p : SymmetricAlgebra K 𝔤)
    (hp : ∀ x : 𝔤, SymmetricAlgebra.derivation (LieAlgebra.ad K 𝔤 x) p = 0)
    {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA) (μ : Dual K H) :
    SymmetricAlgebra.lift (w μ) (cartanRestriction P p) =
      SymmetricAlgebra.lift μ (cartanRestriction P p) := by
  have hi (i : ι) (ν : Dual K H) :
      SymmetricAlgebra.lift (P.reflection hA i ν) (cartanRestriction P p) =
        SymmetricAlgebra.lift ν (cartanRestriction P p) := by
    have hh := congrArg (SymmetricAlgebra.lift ν)
      (cartanRestriction_reflection_of_invariant P hA p hp i)
    rw [SymmetricAlgebra.lift_affinePullback, add_zero] at hh
    have he : ν.comp (P.coreflection hA i).toLinearMap = P.reflection hA i ν := by
      ext h
      exact (P.reflection_apply_apply hA i ν h).symm
    rwa [he] at hh
  refine P.weylGroup_induction hA (p := fun w =>
    SymmetricAlgebra.lift (w μ) (cartanRestriction P p) =
      SymmetricAlgebra.lift μ (cartanRestriction P p)) (by simp) (fun i w ih => ?_) hw
  rw [LinearEquiv.mul_apply]
  exact (hi i (w μ)).trans ih

/-- In finite type the actual Killing form is nondegenerate, by the existing finite-type
semisimplicity theorem and Mathlib's Cartan criterion. No Killing hypothesis is assumed. -/
theorem killingForm_nondegenerate_of_isFiniteCartan [FiniteDimensional K H]
    (hA : A.IsFiniteCartan) : (killingForm K 𝔤).Nondegenerate := by
  let := finiteDimensional P hA
  let := isSemisimple P hA
  exact LieAlgebra.IsKilling.killingForm_nondegenerate K 𝔤

/-- The finite-type Killing identification with the dual, as used in Etingof, Lecture 10,
Remark 10.2(1). Finite dimensionality is supplied by the production finite-type theorem. -/
def killingEquivDual [FiniteDimensional K H] (hA : A.IsFiniteCartan) : 𝔤 ≃ₗ[K] Dual K 𝔤 := by
  letI := finiteDimensional P hA
  exact (killingForm K 𝔤).toDual (killingForm_nondegenerate_of_isFiniteCartan P hA)

@[simp] theorem killingEquivDual_apply [FiniteDimensional K H] (hA : A.IsFiniteCartan)
    (x y : 𝔤) : killingEquivDual P hA x y = killingForm K 𝔤 x y := rfl

/-- The Killing identification intertwines adjoint and coadjoint, not two adjoint actions.
Mathlib's dual module action evaluates to `-φ ⁅x, y⁆`. -/
theorem killingEquivDual_lie [FiniteDimensional K H] (hA : A.IsFiniteCartan) (x y : 𝔤) :
    killingEquivDual P hA ⁅x, y⁆ = ⁅x, killingEquivDual P hA y⁆ := by
  ext z
  simp only [killingEquivDual_apply, Module.Dual.lie_apply]
  exact LieModule.traceForm_lieInvariant K 𝔤 𝔤 x y z

/-- Identification of symmetric symbols with coordinate polynomials on the full Lie
algebra. This is an actual algebra equivalence, not an unproved identification. -/
def killingSymbolEquiv [FiniteDimensional K H] (hA : A.IsFiniteCartan) :
    SymmetricAlgebra K 𝔤 ≃ₐ[K] SymmetricAlgebra K (Dual K 𝔤) :=
  SymmetricAlgebra.equivOfLinearEquiv (killingEquivDual P hA)

/-- The Killing polynomial equivalence transports exactly the infinitesimal invariant
condition. It does not identify it with Weyl invariance or assume integration to a group. -/
theorem killingSymbolEquiv_invariant_iff [FiniteDimensional K H] (hA : A.IsFiniteCartan)
    (p : SymmetricAlgebra K 𝔤) :
    (∀ x : 𝔤, SymmetricAlgebra.derivation
      (LieModule.toEnd K 𝔤 (Dual K 𝔤) x) (killingSymbolEquiv P hA p) = 0) ↔
    (∀ x : 𝔤, SymmetricAlgebra.derivation (LieAlgebra.ad K 𝔤 x) p = 0) := by
  have he (x : 𝔤) : SymmetricAlgebra.derivation
      (LieModule.toEnd K 𝔤 (Dual K 𝔤) x) (killingSymbolEquiv P hA p) =
      killingSymbolEquiv P hA (SymmetricAlgebra.derivation (LieAlgebra.ad K 𝔤 x) p) :=
    SymmetricAlgebra.derivation_lift_comp_ι (killingEquivDual P hA).toLinearMap
      (LieAlgebra.ad K 𝔤 x) (LieModule.toEnd K 𝔤 (Dual K 𝔤) x)
      (fun y => killingEquivDual_lie P hA x y) p
  simp only [he, map_eq_zero_iff _ (killingSymbolEquiv P hA).injective]

omit [CharZero K] in
/-- A nonzero root space is Killing-orthogonal to the actual Cartan image.
This elementary weight argument does not require an identification of two root APIs. -/
theorem killingForm_h_rootSpace_eq_zero (a : H) {μ : Dual K H} (hμ : μ ≠ 0)
    {x : 𝔤} (hx : x ∈ rootSpace P μ) : killingForm K 𝔤 (h P a) x = 0 := by
  by_contra hc
  apply hμ
  ext b
  have he := LieModule.traceForm_apply_lie_apply K 𝔤 𝔤 (h P a) (h P b) x
  rw [lie_h_h, map_zero, LinearMap.zero_apply, hx b, map_smul, smul_eq_mul] at he
  exact (mul_eq_zero.mp he.symm).resolve_right hc

/-- The actual triangular Cartan projection is the Killing-orthogonal projection.
The proof uses the existing positive/negative root decompositions, not an assumed
compatibility between Killing identification and restriction. -/
theorem killingForm_h_cartanProj (a : H) (x : 𝔤) :
    killingForm K 𝔤 (h P a) x = killingForm K 𝔤 (h P a) (h P (cartanProj P x)) := by
  have hn : (nNeg P).toSubmodule ≤ LinearMap.ker (killingForm K 𝔤 (h P a)) := by
    rw [nNeg_toSubmodule_eq]
    refine iSup₂_le fun μ hμ x hx => ?_
    exact killingForm_h_rootSpace_eq_zero P a
      (fun he => P.zero_notMem_negWeights (he ▸ hμ)) hx
  have hp : (nPos P).toSubmodule ≤ LinearMap.ker (killingForm K 𝔤 (h P a)) := by
    rw [nPos_toSubmodule_eq]
    refine iSup₂_le fun μ hμ x hx => ?_
    exact killingForm_h_rootSpace_eq_zero P a
      (fun he => P.zero_notMem_posWeights (he ▸ hμ)) hx
  obtain ⟨y, b, z, rfl⟩ := exists_triangular P x
  have hy : killingForm K 𝔤 (h P a) (fHom P y) = 0 := hn ⟨y, rfl⟩
  have hz : killingForm K 𝔤 (h P a) (eHom P z) = 0 := hp ⟨z, rfl⟩
  simp only [map_add, hy, hz, zero_add, add_zero, cartanProj_h,
    cartanProj_of_mem_nNeg P (show fHom P y ∈ nNeg P from ⟨y, rfl⟩),
    cartanProj_of_mem_nPos P (show eHom P z ∈ nPos P from ⟨z, rfl⟩)]

/-- Restriction of the full Killing form to the actual Cartan embedding. -/
def cartanKillingForm : LinearMap.BilinForm K H :=
  (killingForm K 𝔤).compl₁₂ (h P) (h P)

omit [CharZero K] in
@[simp] theorem cartanKillingForm_apply (a b : H) :
    cartanKillingForm P a b = killingForm K 𝔤 (h P a) (h P b) := rfl

/-- In finite type the restriction of the Killing form to this Cartan is nondegenerate.
This follows from the proved orthogonal-projection identity and full nondegeneracy. -/
theorem cartanKillingForm_nondegenerate [FiniteDimensional K H] (hA : A.IsFiniteCartan) :
    (cartanKillingForm P).Nondegenerate := by
  have hs : (cartanKillingForm P).IsSymm := ⟨fun a b =>
    LieModule.traceForm_comm K 𝔤 𝔤 (h P a) (h P b)⟩
  apply hs.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro a ha
  apply h_injective P
  rw [map_zero]
  apply (killingForm_nondegenerate_of_isFiniteCartan P hA).1
  intro x
  rw [killingForm_h_cartanProj P a x]
  exact ha (cartanProj P x)

/-- The Cartan Killing identification, constructed from its proved nondegeneracy. -/
def cartanKillingEquivDual [FiniteDimensional K H] (hA : A.IsFiniteCartan) :
    H ≃ₗ[K] Dual K H :=
  (cartanKillingForm P).toDual (cartanKillingForm_nondegenerate P hA)

@[simp] theorem cartanKillingEquivDual_apply [FiniteDimensional K H]
    (hA : A.IsFiniteCartan) (a b : H) :
    cartanKillingEquivDual P hA a b = killingForm K 𝔤 (h P a) (h P b) := rfl

/-- Literal restriction of coordinate polynomials on the full Lie algebra to the Cartan:
its generator map precomposes covectors with the Cartan embedding. -/
def coordinateCartanRestriction :
    SymmetricAlgebra K (Dual K 𝔤) →ₐ[K] SymmetricAlgebra K (Dual K H) :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp (h P).dualMap)

/-- The genuine restriction diagram commutes under the full and Cartan Killing
identifications. This proves, rather than assumes, the symmetric-symbol/coordinate
polynomial identification in Etingof, Lecture 10, Remark 10.2(1). -/
theorem coordinateCartanRestriction_killingSymbolEquiv [FiniteDimensional K H]
    (hA : A.IsFiniteCartan) (p : SymmetricAlgebra K 𝔤) :
    coordinateCartanRestriction P (killingSymbolEquiv P hA p) =
      SymmetricAlgebra.equivOfLinearEquiv (cartanKillingEquivDual P hA)
        (cartanRestriction P p) := by
  have he : (coordinateCartanRestriction P).comp (killingSymbolEquiv P hA).toAlgHom =
      (SymmetricAlgebra.equivOfLinearEquiv (cartanKillingEquivDual P hA)).toAlgHom.comp
        (cartanRestriction P) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    change coordinateCartanRestriction P
      (killingSymbolEquiv P hA (SymmetricAlgebra.ι K 𝔤 x)) =
      SymmetricAlgebra.equivOfLinearEquiv (cartanKillingEquivDual P hA)
        (cartanRestriction P (SymmetricAlgebra.ι K 𝔤 x))
    simp only [coordinateCartanRestriction, killingSymbolEquiv,
      SymmetricAlgebra.equivOfLinearEquiv_apply, SymmetricAlgebra.lift_ι_apply,
      LinearMap.comp_apply, cartanRestriction_ι]
    congr 1
    ext a
    change killingForm K 𝔤 x (h P a) = killingForm K 𝔤 (h P (cartanProj P x)) (h P a)
    exact (LieModule.traceForm_comm K 𝔤 𝔤 x (h P a)).trans
      ((killingForm_h_cartanProj P a x).trans
        (LieModule.traceForm_comm K 𝔤 𝔤 (h P a) (h P (cartanProj P x))))
  exact DFunLike.congr_fun he p

omit [CharZero K] in
/-- The coroot pairing for the restricted Killing form follows from the actual sl₂
relations and invariance; no root/dual identification is posited. -/
theorem cartanKillingForm_coroot (a : H) (i : ι) :
    cartanKillingForm P a (P.coroot i) = P.root i a * killingForm K 𝔤 (e P i) (f P i) := by
  change killingForm K 𝔤 (h P a) (h P (P.coroot i)) = _
  rw [← lie_e_f_self, ← LieModule.traceForm_apply_lie_apply, lie_h_e,
    map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- The Cartan Killing identification intertwines the actual coreflection and actual
reflection on weights. This certifies the Weyl actions in the coordinate restriction. -/
theorem cartanKillingEquivDual_coreflection [FiniteDimensional K H]
    (hA : A.IsFiniteCartan) (i : ι) (a : H) :
    cartanKillingEquivDual P hA (P.coreflection hA.isGeneralizedCartan i a) =
      P.reflection hA.isGeneralizedCartan i (cartanKillingEquivDual P hA a) := by
  ext b
  rw [P.reflection_apply_apply]
  change cartanKillingForm P (P.coreflection hA.isGeneralizedCartan i a) b =
    cartanKillingForm P a (P.coreflection hA.isGeneralizedCartan i b)
  have hs : cartanKillingForm P (P.coroot i) b = cartanKillingForm P b (P.coroot i) :=
    LieModule.traceForm_comm K 𝔤 𝔤 _ _
  simp only [P.coreflection_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hs, cartanKillingForm_coroot]
  ring

/-- Killing transport of the Cartan reflection action on symmetric symbols. -/
theorem cartanKillingSymbolEquiv_reflection [FiniteDimensional K H]
    (hA : A.IsFiniteCartan) (i : ι) (q : SymmetricAlgebra K H) :
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp
      (P.reflection hA.isGeneralizedCartan i).toLinearMap)
      (SymmetricAlgebra.equivOfLinearEquiv (cartanKillingEquivDual P hA) q) =
    SymmetricAlgebra.equivOfLinearEquiv (cartanKillingEquivDual P hA)
      (SymmetricAlgebra.affinePullback
        (P.coreflection hA.isGeneralizedCartan i).toLinearMap 0 q) := by
  have he : (SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp
      (P.reflection hA.isGeneralizedCartan i).toLinearMap)).comp
      (SymmetricAlgebra.equivOfLinearEquiv (cartanKillingEquivDual P hA)).toAlgHom =
    (SymmetricAlgebra.equivOfLinearEquiv (cartanKillingEquivDual P hA)).toAlgHom.comp
      (SymmetricAlgebra.affinePullback
        (P.coreflection hA.isGeneralizedCartan i).toLinearMap 0) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro a
    change SymmetricAlgebra.lift _
        (SymmetricAlgebra.equivOfLinearEquiv (cartanKillingEquivDual P hA)
          (SymmetricAlgebra.ι K H a)) =
      SymmetricAlgebra.equivOfLinearEquiv (cartanKillingEquivDual P hA)
        (SymmetricAlgebra.affinePullback _ 0 (SymmetricAlgebra.ι K H a))
    simp [SymmetricAlgebra.affinePullback, cartanKillingEquivDual_coreflection]
  exact DFunLike.congr_fun he q

/-- Coordinate-polynomial Chevalley restriction invariance for the actual finite-type
realization: coadjoint-infinitesimal invariants on `g` restrict to reflection invariants
on `h`. This is Thm. 10.1(i), not the injectivity or extension of Thm. 10.1(ii). -/
theorem coordinateCartanRestriction_reflection_of_invariant [FiniteDimensional K H]
    (hA : A.IsFiniteCartan) (F : SymmetricAlgebra K (Dual K 𝔤))
    (hF : ∀ x : 𝔤, SymmetricAlgebra.derivation (LieModule.toEnd K 𝔤 (Dual K 𝔤) x) F = 0)
    (i : ι) :
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp
      (P.reflection hA.isGeneralizedCartan i).toLinearMap)
      (coordinateCartanRestriction P F) = coordinateCartanRestriction P F := by
  obtain ⟨p, rfl⟩ := (killingSymbolEquiv P hA).surjective F
  have hp := (killingSymbolEquiv_invariant_iff P hA p).mp hF
  rw [coordinateCartanRestriction_killingSymbolEquiv, cartanKillingSymbolEquiv_reflection,
    cartanRestriction_reflection_of_invariant P hA.isGeneralizedCartan p hp]

/-- Every Weyl element fixes the actual restricted coordinate polynomial of an
infinitesimal invariant, not merely its values or its top homogeneous part.
This is the finite-type realization form of Etingof, Lecture 10, Thm. 10.1(i). -/
theorem coordinateCartanRestriction_weyl_of_invariant [FiniteDimensional K H]
    (hA : A.IsFiniteCartan) (F : SymmetricAlgebra K (Dual K 𝔤))
    (hF : ∀ x : 𝔤, SymmetricAlgebra.derivation (LieModule.toEnd K 𝔤 (Dual K 𝔤) x) F = 0)
    {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA.isGeneralizedCartan) :
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp w.toLinearMap)
      (coordinateCartanRestriction P F) = coordinateCartanRestriction P F := by
  refine P.weylGroup_induction hA.isGeneralizedCartan (p := fun w =>
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp w.toLinearMap)
      (coordinateCartanRestriction P F) = coordinateCartanRestriction P F)
    (by simp) (fun i w ih => ?_) hw
  have he : SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp
      (P.reflection hA.isGeneralizedCartan i * w).toLinearMap) =
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp
      (P.reflection hA.isGeneralizedCartan i).toLinearMap)).comp
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp w.toLinearMap)) := by
    apply SymmetricAlgebra.algHom_ext
    ext a
    simp
  rw [he, AlgHom.comp_apply, ih]
  exact coordinateCartanRestriction_reflection_of_invariant P hA F hF i

end Matrix.Realization.KacMoodyAlgebra
