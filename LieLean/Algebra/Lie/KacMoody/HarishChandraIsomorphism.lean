/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.ChevalleyInjectivity

/-!
# The Harish-Chandra isomorphism in finite type

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.coreflectionInvariants`: Cartan polynomials fixed by all
  simple coreflections.
* `Matrix.Realization.KacMoodyAlgebra.shiftedHarishChandraEquiv`: the `ρ`-shifted
  Harish-Chandra homomorphism as an algebra isomorphism from the centre of `U(𝔤)` onto the
  invariants, in finite type.

## Main results

* `UniversalEnvelopingAlgebra.toGr_commutator`: on the associated graded algebra, the
  commutator with `ι x` is the derivation of `Sym(L)` extending `ad x`.
* `UniversalEnvelopingAlgebra.derivation_symbol_eq_zero_of_mem_center`: PBW symbols of central
  elements are `ad`-invariant.
* `Matrix.Realization.KacMoodyAlgebra.eq_zero_of_invariant_of_cartanRestriction_eq_zero` and
  `exists_invariant_cartanRestriction_eq`: Chevalley injectivity and extension for symbols
  in `Sym(𝔤)`.
* `Matrix.Realization.KacMoodyAlgebra.harishChandra_injective`,
  `shiftedHarishChandra_injective`: the Harish-Chandra homomorphism on the centre is injective.
* `Matrix.Realization.KacMoodyAlgebra.exists_shiftedHarishChandra_eq`,
  `shiftedHarishChandra_range`: its `ρ`-shifted image is exactly the coreflection invariants.

All results beyond the graded commutator are for the finite-type realization with
finite-dimensional Cartan space, over an arbitrary field of characteristic zero.

## References

* Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  Theorem 1.10 (check).
* Humphreys, *Introduction to Lie algebras and representation theory*, GTM 9, §23.3 (check).
The arguments are the standard graded ones, reconstructed here from the existing graded HC
compatibility, central lifts, HC invariance and Chevalley's restriction theorem: the top PBW
symbol of a central element is invariant and its Cartan restriction is the top HC term
(injectivity); Chevalley extension of the top component plus a central lift lowers the degree
(image).
-/

noncomputable section

open Module

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type} [Field K] {L : Type*} [LieRing L] [LieAlgebra K L]

/-- Commutators with `ι x` preserve the PBW filtration. -/
theorem commutator_ι_mem_filtration (x : L) {n : ℕ} {u : UniversalEnvelopingAlgebra K L}
    (hu : u ∈ filtration K L n) : ι K x * u - u * ι K x ∈ filtration K L n := by
  have := commutator_mem_filtration (ι_mem_filtration_one (R := K) x) hu
  rwa [Nat.add_sub_cancel_left] at this

/-- Left multiplication by a filtration-one generator `r + ι w` on the graded pieces. -/
theorem toGr_succ_generator_mul {i : ℕ} (r : K) (w : L) (a : filtration K L i)
    (h : (algebraMap K _ r + ι K w) * (a : UniversalEnvelopingAlgebra K L) ∈
      filtration K L (i + 1)) :
    toGr K L (i + 1) ⟨_, h⟩ = toGr K L 1 ⟨ι K w, ι_mem_filtration_one w⟩ * toGr K L i a := by
  have h₁ : algebraMap K _ r * (a : UniversalEnvelopingAlgebra K L) ∈ filtration K L (i + 1) := by
    rw [Algebra.algebraMap_eq_smul_one, smul_one_mul]
    exact Submodule.smul_mem _ _ (filtration_mono (Nat.le_succ i) a.2)
  have h₂ : ι K w * (a : UniversalEnvelopingAlgebra K L) ∈ filtration K L (i + 1) := by
    rw [add_comm]
    exact mul_mem_filtration (ι_mem_filtration_one w) a.2
  have e : (⟨_, h⟩ : filtration K L (i + 1)) = ⟨_, h₁⟩ + ⟨_, h₂⟩ := Subtype.ext (add_mul _ _ _)
  rw [e, map_add, (toGr_succ_eq_zero_iff _).mpr, zero_add, toGr_mul]
  · exact toGr_congr (add_comm i 1) rfl
  · dsimp only
    rw [Algebra.algebraMap_eq_smul_one, smul_one_mul]
    exact Submodule.smul_mem _ _ a.2

/-- **Graded commutator.** On the associated graded algebra, the commutator with `ι x` acts on
the degree-`n` symbol as the derivation of `Sym(L)` extending `ad x`. -/
theorem toGr_commutator (x : L) (n : ℕ) (u : filtration K L n) :
    toGr K L n ⟨ι K x * u - u * ι K x, commutator_ι_mem_filtration x u.2⟩ =
      symmetricAlgebraEquivAssociatedGraded K L
        (SymmetricAlgebra.derivation (LieAlgebra.ad K L x)
          ((symmetricAlgebraEquivAssociatedGraded K L).symm (toGr K L n u))) := by
  set e := symmetricAlgebraEquivAssociatedGraded K L
  set D := SymmetricAlgebra.derivation (LieAlgebra.ad K L x)
  let Δ : AssociatedGraded K L → AssociatedGraded K L := fun t => e (D (e.symm t))
  have hΔmul : ∀ s t, Δ (s * t) = s * Δ t + t * Δ s := by
    intro s t
    simp only [Δ, map_mul, Derivation.leibniz, smul_eq_mul, map_add, e.apply_symm_apply]
  have hΔadd : ∀ s t, Δ (s + t) = Δ s + Δ t := by
    intro s t
    simp only [Δ, map_add]
  have hΔι : ∀ w, Δ (toGr K L 1 ⟨ι K w, ι_mem_filtration_one w⟩) =
      toGr K L 1 ⟨ι K ⁅x, w⁆, ι_mem_filtration_one _⟩ := by
    intro w
    simp only [Δ]
    rw [← symmetricAlgebraEquivAssociatedGraded_ι, e.symm_apply_apply,
      SymmetricAlgebra.derivation_ι, LieAlgebra.ad_apply, symmetricAlgebraEquivAssociatedGraded_ι]
  change _ = Δ (toGr K L n u)
  obtain ⟨u, hu⟩ := u
  induction hu using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    have hr : toGr K L 0 ⟨algebraMap K _ r, algebraMap_mem_filtration r 0⟩ =
        algebraMap K _ r := by
      rw [toGr_apply, ← AlgHom.commutes (AssociatedGraded.mk (R := K) (L := L)) r]
      rfl
    calc _ = toGr K L 0 0 := congrArg _ (Subtype.ext (by simp [Algebra.commutes]))
      _ = Δ (toGr K L 0 ⟨algebraMap K _ r, algebraMap_mem_filtration r 0⟩) := by
        rw [hr, map_zero]
        simp only [Δ, AlgEquiv.commutes, Derivation.map_algebraMap, map_zero]
  | add a b i ha hb iha ihb =>
    calc _ = toGr K L i (⟨_, commutator_ι_mem_filtration x ha⟩ +
          ⟨_, commutator_ι_mem_filtration x hb⟩) :=
          congrArg _ (Subtype.ext (by simp only [Submodule.coe_add]; noncomm_ring))
      _ = Δ (toGr K L i (⟨a, ha⟩ + ⟨b, hb⟩)) := by rw [map_add, map_add, iha, ihb, hΔadd]
  | mem_mul g hg i a ha ih =>
    obtain ⟨y, hy, z, ⟨w, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hg
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hy
    have ha' : a ∈ filtration K L i := ha
    have hra : algebraMap K _ r * a ∈ filtration K L i := by
      rw [Algebra.algebraMap_eq_smul_one, smul_one_mul]
      exact Submodule.smul_mem _ _ ha'
    have hc := commutator_ι_mem_filtration x ha'
    have h₁ : ι K x * (algebraMap K _ r * a) - algebraMap K _ r * a * ι K x ∈
        filtration K L (i + 1) :=
      filtration_mono (Nat.le_succ i) (commutator_ι_mem_filtration x hra)
    have h₂ : ι K ⁅x, w⁆ * a ∈ filtration K L (i + 1) := by
      rw [add_comm]
      exact mul_mem_filtration (ι_mem_filtration_one _) ha'
    have h₃ : ι K w * (ι K x * a - a * ι K x) ∈ filtration K L (i + 1) := by
      rw [add_comm]
      exact mul_mem_filtration (ι_mem_filtration_one _) hc
    have hg : (algebraMap K _ r + ι K w) * a ∈ filtration K L (i + 1) := by
      rw [add_comm]
      exact mul_mem_filtration (add_mem (algebraMap_mem_filtration r 1)
        (ι_mem_filtration_one w)) ha'
    calc _ = toGr K L (i + 1) (⟨_, h₁⟩ + ⟨_, h₂⟩ + ⟨_, h₃⟩) := by
          apply congrArg
          apply Subtype.ext
          simp only [Submodule.coe_add, LieHom.map_lie, Ring.lie_def]
          change ι K x * ((algebraMap K _ r + ι K w) * a) -
            (algebraMap K _ r + ι K w) * a * ι K x = _
          noncomm_ring
      _ = toGr K L 1 ⟨ι K ⁅x, w⁆, ι_mem_filtration_one _⟩ * toGr K L i ⟨a, ha⟩ +
          toGr K L 1 ⟨ι K w, ι_mem_filtration_one w⟩ * Δ (toGr K L i ⟨a, ha⟩) := by
        rw [map_add, map_add, (toGr_succ_eq_zero_iff _).mpr (commutator_ι_mem_filtration x hra),
          zero_add, ← ih, toGr_mul, toGr_mul]
        congr 1
        · exact toGr_congr (add_comm i 1) rfl
        · exact toGr_congr (add_comm i 1) rfl
      _ = Δ (toGr K L (i + 1) ⟨_, hg⟩) := by
        rw [toGr_succ_generator_mul r w ⟨a, ha⟩ hg, hΔmul, hΔι]
        ring

/-- The PBW symbol of a central element is `ad`-invariant, in every filtration degree. -/
theorem derivation_symbol_eq_zero_of_mem_center {n : ℕ} {z : UniversalEnvelopingAlgebra K L}
    (hz : z ∈ Subalgebra.center K (UniversalEnvelopingAlgebra K L)) (hzn : z ∈ filtration K L n)
    (x : L) :
    SymmetricAlgebra.derivation (LieAlgebra.ad K L x)
      ((symmetricAlgebraEquivAssociatedGraded K L).symm (toGr K L n ⟨z, hzn⟩)) = 0 := by
  have h := toGr_commutator x n ⟨z, hzn⟩
  have h0 : (⟨ι K x * z - z * ι K x, commutator_ι_mem_filtration x hzn⟩ :
      filtration K L n) = 0 :=
    Subtype.ext (by
      change ι K x * z - z * ι K x = 0
      rw [Subalgebra.mem_center_iff.mp hz (ι K x), sub_self])
  rw [h0, map_zero, eq_comm, map_eq_zero_iff _ (AlgEquiv.injective _)] at h
  exact h

end UniversalEnvelopingAlgebra

namespace SymmetricAlgebra

variable {K : Type} {M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- A symmetric algebra element of total degree less than `m` has zero component in degree `m`. -/
theorem homogeneousComponent_eq_zero_of_totalDegree_lt {m : ℕ} (f : SymmetricAlgebra K M)
    (hf : (equivMvPolynomial (Free.chooseBasis K M) f).totalDegree < m) :
    homogeneousComponent m f = 0 := by
  apply (equivMvPolynomial (Free.chooseBasis K M)).injective
  rw [equivMvPolynomial_homogeneousComponent, map_zero]
  exact MvPolynomial.homogeneousComponent_eq_zero _ _ hf

end SymmetricAlgebra

namespace Matrix.Realization.KacMoodyAlgebra

open UniversalEnvelopingAlgebra

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K 𝔤

include hA in
/-- **Chevalley injectivity for symbols**: an `ad`-invariant element of `Sym(𝔤)` whose genuine
Cartan restriction vanishes is zero, in finite type. Transported from the coordinate
statement through the Killing identifications. -/
theorem eq_zero_of_invariant_of_cartanRestriction_eq_zero (p : SymmetricAlgebra K 𝔤)
    (hp : ∀ x : 𝔤, SymmetricAlgebra.derivation (LieAlgebra.ad K 𝔤 x) p = 0)
    (h₀ : cartanRestriction P p = 0) : p = 0 := by
  have he := coordinateCartanRestriction_killingSymbolEquiv P hA p
  rw [h₀, map_zero] at he
  have hq := eq_zero_of_invariant_of_coordinateCartanRestriction_eq_zero P hA _
    ((killingSymbolEquiv_invariant_iff P hA p).mpr hp) he
  exact (map_eq_zero_iff _ (killingSymbolEquiv P hA).injective).mp hq

include hA in
/-- A map on the centre whose degree-`n` component is the Cartan restriction of the PBW symbol
of every central element of filtration degree `n` is injective. -/
theorem eq_zero_of_homogeneousComponent_eq_cartanRestriction
    (φ : Subalgebra.center K 𝓤 →ₗ[K] SymmetricAlgebra K H)
    (hφ : ∀ (n : ℕ) (z : Subalgebra.center K 𝓤) (hz : z.val ∈ filtration K 𝔤 n),
      SymmetricAlgebra.homogeneousComponent n (φ z) =
        cartanRestriction P ((symmetricAlgebraEquivAssociatedGraded K 𝔤).symm
          (toGr K 𝔤 n ⟨z.val, hz⟩)))
    (z : Subalgebra.center K 𝓤) (h₀ : φ z = 0) : z = 0 := by
  obtain ⟨n, hn⟩ := exists_mem_filtration (R := K) z.val
  induction n generalizing z with
  | zero =>
    have hs := hφ 0 z hn
    rw [h₀, map_zero, eq_comm] at hs
    have h := eq_zero_of_invariant_of_cartanRestriction_eq_zero P hA _
      (derivation_symbol_eq_zero_of_mem_center z.property hn) hs
    rw [map_eq_zero_iff _ (AlgEquiv.injective _), toGr_zero_eq_zero_iff] at h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  | succ m ih =>
    have hs := hφ (m + 1) z hn
    rw [h₀, map_zero, eq_comm] at hs
    have h := eq_zero_of_invariant_of_cartanRestriction_eq_zero P hA _
      (derivation_symbol_eq_zero_of_mem_center z.property hn) hs
    rw [map_eq_zero_iff _ (AlgEquiv.injective _), toGr_succ_eq_zero_iff] at h
    exact ih z h₀ h

include hA in
/-- **The Harish-Chandra homomorphism is injective** on the centre of `U(𝔤)`, in finite type
over any characteristic-zero field. Humphreys, GSM 94, §1.10 (check); Humphreys, GTM 9,
§23.3 (check). Reconstructed: the top HC term is the Cartan restriction of the invariant PBW
symbol, which vanishes only for zero symbols by Chevalley injectivity. -/
theorem harishChandra_injective : Function.Injective (harishChandra P) := by
  rw [injective_iff_map_eq_zero]
  exact eq_zero_of_homogeneousComponent_eq_cartanRestriction P hA
    (harishChandra P).toLinearMap (fun n z hz => harishChandraProjection_homogeneousComponent
      P n ⟨z.val, hz⟩)

include hA in
/-- The `ρ`-shifted Harish-Chandra homomorphism is injective, in finite type. -/
theorem shiftedHarishChandra_injective : Function.Injective (shiftedHarishChandra P) := by
  rw [injective_iff_map_eq_zero]
  exact eq_zero_of_homogeneousComponent_eq_cartanRestriction P hA
    (shiftedHarishChandra P).toLinearMap (fun n z hz =>
      shiftedHarishChandra_homogeneousComponent P n z hz)

include hA in
/-- **Chevalley extension for symbols**: every coreflection-invariant homogeneous Cartan symbol
of degree `n` is the genuine Cartan restriction of an `ad`-invariant homogeneous symbol of
degree `n` in `Sym(𝔤)`, in finite type. Transported from `exists_homogeneous_chevalley_extension`
through the Killing identifications. -/
theorem exists_invariant_cartanRestriction_eq (n : ℕ) (f : SymmetricAlgebra K H)
    (hf : f ∈ SymmetricAlgebra.homogeneousSubmodule n)
    (hinv : ∀ i, SymmetricAlgebra.affinePullback
      (P.coreflection hA.isGeneralizedCartan i).toLinearMap 0 f = f) :
    ∃ p ∈ SymmetricAlgebra.homogeneousSubmodule (K := K) (M := 𝔤) n,
      (∀ x : 𝔤, SymmetricAlgebra.derivation (LieAlgebra.ad K 𝔤 x) p = 0) ∧
        cartanRestriction P p = f := by
  set κH := SymmetricAlgebra.equivOfLinearEquiv (cartanKillingEquivDual P hA)
  have hq : κH f ∈ SymmetricAlgebra.homogeneousSubmodule n :=
    SymmetricAlgebra.lift_comp_ι_mem_homogeneous _ n hf
  have hw : ∀ w : P.weylGroup hA.isGeneralizedCartan,
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp w.val.toLinearMap)
        (κH f) = κH f := by
    intro w
    refine P.weylGroup_induction hA.isGeneralizedCartan (p := fun w =>
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp w.toLinearMap)
        (κH f) = κH f) (by simp) (fun i w ih => ?_) w.property
    have he : SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp
        (P.reflection hA.isGeneralizedCartan i * w).toLinearMap) =
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp
        (P.reflection hA.isGeneralizedCartan i).toLinearMap)).comp
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp w.toLinearMap)) := by
      apply SymmetricAlgebra.algHom_ext
      ext a
      simp
    rw [he, AlgHom.comp_apply, ih, cartanKillingSymbolEquiv_reflection, hinv i]
  obtain ⟨F, hF, hiF, heF⟩ := exists_homogeneous_chevalley_extension P hA n (κH f) hq hw
  refine ⟨(killingSymbolEquiv P hA).symm F, ?_, ?_, ?_⟩
  · exact SymmetricAlgebra.lift_comp_ι_mem_homogeneous _ n hF
  · apply (killingSymbolEquiv_invariant_iff P hA _).mp
    simpa only [AlgEquiv.apply_symm_apply] using hiF
  · have he := coordinateCartanRestriction_killingSymbolEquiv P hA
      ((killingSymbolEquiv P hA).symm F)
    rw [AlgEquiv.apply_symm_apply, heF] at he
    exact κH.injective he.symm

include hA in
/-- **Image of the Harish-Chandra homomorphism.** Every Cartan polynomial fixed by all simple
coreflections is the `ρ`-shifted Harish-Chandra image of a central element, in finite type.
Humphreys, GSM 94, §1.10 (check). Reconstructed by degree induction: Chevalley extension of the
top component, a central lift with that top HC term, and the proved invariance of HC images. -/
theorem exists_shiftedHarishChandra_eq (f : SymmetricAlgebra K H)
    (hinv : ∀ i, SymmetricAlgebra.affinePullback
      (P.coreflection hA.isGeneralizedCartan i).toLinearMap 0 f = f) :
    ∃ z, shiftedHarishChandra P z = f := by
  have key : ∀ n (f : SymmetricAlgebra K H), (∀ i, SymmetricAlgebra.affinePullback
      (P.coreflection hA.isGeneralizedCartan i).toLinearMap 0 f = f) →
      (∀ m, n ≤ m → SymmetricAlgebra.homogeneousComponent m f = 0) →
      ∃ z, shiftedHarishChandra P z = f := by
    intro n
    induction n with
    | zero =>
      intro f _ hf
      refine ⟨0, ?_⟩
      rw [map_zero]
      exact SymmetricAlgebra.eq_of_homogeneousComponent_eq _ _ fun m => by
        rw [map_zero, hf m (Nat.zero_le m)]
    | succ n ih =>
      intro f hfinv hf
      have hcomp : ∀ i, SymmetricAlgebra.affinePullback
          (P.coreflection hA.isGeneralizedCartan i).toLinearMap 0
          (SymmetricAlgebra.homogeneousComponent n f) =
          SymmetricAlgebra.homogeneousComponent n f := by
        intro i
        have h := SymmetricAlgebra.homogeneousComponent_lift_comp_ι
          (P.coreflection hA.isGeneralizedCartan i).toLinearMap n f
        simp only [SymmetricAlgebra.affinePullback, LinearMap.comp_zero, add_zero] at hfinv ⊢
        rw [← h, hfinv i]
      obtain ⟨p, hp, hpinv, hpres⟩ := exists_invariant_cartanRestriction_eq P hA n _
        (SymmetricAlgebra.homogeneousComponent_mem n f) hcomp
      obtain ⟨z, hz, -, htop⟩ := exists_centralLift_shiftedHarishChandra_top P n ⟨p, hp⟩ hpinv
      obtain ⟨z', hz'⟩ := ih (f - shiftedHarishChandra P z) (fun i => by
          rw [map_sub, hfinv i, shiftedHarishChandra_reflection P hA.isGeneralizedCartan i z])
        (fun m hm => by
          rw [map_sub]
          rcases hm.lt_or_eq with hlt | rfl
          · rw [hf m hlt, SymmetricAlgebra.homogeneousComponent_eq_zero_of_totalDegree_lt _
              (lt_of_le_of_lt (shiftedHarishChandra_degree_le P (Free.chooseBasis K H) n z hz).1
                hlt), sub_zero]
          · rw [htop, hpres, sub_self])
      exact ⟨z + z', by rw [map_add, hz', add_sub_cancel]⟩
  refine key ((SymmetricAlgebra.equivMvPolynomial (Free.chooseBasis K H) f).totalDegree + 1)
    f hinv fun m hm => SymmetricAlgebra.homogeneousComponent_eq_zero_of_totalDegree_lt f ?_
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hm

variable (hA' : A.IsGeneralizedCartan)

/-- The Cartan polynomials fixed by every simple coreflection of `𝔥`, i.e. by the group these
coreflections generate, as a subalgebra of `Sym(𝔥)` (polynomial functions on `𝔥*`). -/
def coreflectionInvariants : Subalgebra K (SymmetricAlgebra K H) :=
  ⨅ i, AlgHom.equalizer
    (SymmetricAlgebra.affinePullback (P.coreflection hA' i).toLinearMap 0) (AlgHom.id K _)

omit [DecidableEq ι] [CharZero K] [FiniteDimensional K H] in
theorem mem_coreflectionInvariants {f : SymmetricAlgebra K H} :
    f ∈ coreflectionInvariants P hA' ↔
      ∀ i, SymmetricAlgebra.affinePullback (P.coreflection hA' i).toLinearMap 0 f = f := by
  simp [coreflectionInvariants, Algebra.mem_iInf, AlgHom.mem_equalizer]

include hA in
/-- The range of the `ρ`-shifted Harish-Chandra homomorphism is exactly the coreflection
invariants, in finite type. -/
theorem shiftedHarishChandra_range :
    (shiftedHarishChandra P).range = coreflectionInvariants P hA.isGeneralizedCartan := by
  ext f
  rw [mem_coreflectionInvariants, AlgHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩ i
    exact shiftedHarishChandra_reflection P hA.isGeneralizedCartan i z
  · exact exists_shiftedHarishChandra_eq P hA f

/-- **Harish-Chandra's theorem** in finite type: the `ρ`-shifted Harish-Chandra homomorphism is
an algebra isomorphism from the centre of `U(𝔤)` onto the polynomials on `𝔥*` fixed by all
simple coreflections. Its value at `μ` is the Verma central character of `μ - ρ`
(`eval_shiftedHarishChandra`). Humphreys, GSM 94, Theorem 1.10 (check); Humphreys, GTM 9,
§23.3 (check). -/
def shiftedHarishChandraEquiv :
    Subalgebra.center K 𝓤 ≃ₐ[K] coreflectionInvariants P hA.isGeneralizedCartan :=
  (AlgEquiv.ofInjective _ (shiftedHarishChandra_injective P hA)).trans
    (Subalgebra.equivOfEq _ _ (shiftedHarishChandra_range P hA))

@[simp] theorem shiftedHarishChandraEquiv_apply (z : Subalgebra.center K 𝓤) :
    (shiftedHarishChandraEquiv P hA z : SymmetricAlgebra K H) = shiftedHarishChandra P z := rfl

end Matrix.Realization.KacMoodyAlgebra
