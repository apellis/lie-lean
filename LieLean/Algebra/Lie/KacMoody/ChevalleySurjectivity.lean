/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.ChevalleyOrbit
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dominant orbit spanning and Chevalley restriction surjectivity

## Main definitions

`chevalleyRestriction` restricts literal coordinate polynomials between the genuine
infinitesimal-invariant source and the genuine Weyl-fixed target.

## Main results

* `span_dominant_powers`: actual dominant-integral powers span each full homogeneous space.
* `mem_span_distinctOrbitPower_iff`: distinct dominant orbit powers span exactly the
  homogeneous Weyl fixed polynomials.
* `exists_homogeneous_chevalley_extension`: genuine invariant homogeneous extensions.
* `chevalleyRestriction_surjective`: literal coordinate restriction is onto the full
  Weyl fixed polynomial space, with no span-defined or image-defined target.

The realization's finite-type dimension theorem supplies the coroot basis. An elementary
natural-number interpolation argument replaces the source's Zariski-density and
GL-irreducibility argument. Averaging uses the proved distinct-orbit stabilizer factor.
The reviewed character-inversion extension supplies invariant lifts of the generators.
All degrees (including zero), empty simple-root index and arbitrary characteristic-zero
fields are included. The scalar universe `K : Type` is inherited from trace-power theory.
This proves surjectivity, not injectivity, a Chevalley isomorphism, or any HC theorem.

## References

Etingof, MIT 18.757 (Fall 2023), Lecture 10, Theorem 10.1(ii), surjectivity proof:
https://ocw.mit.edu/courses/18-757-representations-of-lie-groups-fall-2023/mit18_757_f23_lec10.pdf
The interpolation proof is reconstructed, not transcribed; it preserves the source's dominant
powers → averaging → invariant extension route.
-/

noncomputable section
open Module
open scoped Pointwise

namespace Submodule

variable {K B : Type*} [Field K] [CharZero K] [CommRing B] [Algebra K B]

/-- A subspace containing all powers from an additive monoid contains their first
polarizations. Natural-number interpolation works over every characteristic-zero field. -/
theorem mul_pow_mem_of_additive_powers (T : AddSubmonoid B) (S : Submodule K B)
    (n : ℕ) (hS : ∀ x ∈ T, x ^ (n + 1) ∈ S) {a b : B} (ha : a ∈ T) (hb : b ∈ T) :
    a * b ^ n ∈ S := by
  classical
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp
  intro φ hφ
  let p : Polynomial K := ∑ k ∈ Finset.range (n + 2),
    Polynomial.monomial k ((n + 1).choose k • φ (a ^ k * b ^ (n + 1 - k)))
  have he (m : ℕ) : p.eval (m : K) = 0 := by
    have hm := (Submodule.mem_dualAnnihilator φ).mp hφ _
      (hS _ (T.add_mem (T.nsmul_mem ha m) hb))
    have hh : φ ((m • a + b) ^ (n + 1)) = p.eval (m : K) := by
      rw [add_pow, map_sum]
      simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Nat.cast_smul_eq_nsmul K m a, smul_pow, smul_mul_assoc,
        ← nsmul_eq_mul', map_nsmul, map_smul]
      simp [smul_eq_mul, mul_comm, mul_left_comm]
    exact hh ▸ hm
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R := K))).mono
    rintro _ ⟨m, rfl⟩
    exact he m
  have hc := congrArg (fun q : Polynomial K => q.coeff 1) hp
  have hcoeff : p.coeff 1 = (n + 1 : K) * φ (a * b ^ n) := by
    simp [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Finset.sum_ite_eq']
  rw [hcoeff, Polynomial.coeff_zero] at hc
  exact (mul_eq_zero.mp hc).resolve_left (by exact_mod_cast Nat.succ_ne_zero n)

/-- Pure powers of any additive monoid span the powers of its linear span. -/
theorem span_addSubmonoid_pow (T : AddSubmonoid B) (n : ℕ) :
    Submodule.span K ((fun x : B => x ^ n) '' (T : Set B)) =
      (Submodule.span K (T : Set B)) ^ n := by
  classical
  induction n with
  | zero =>
    rw [pow_zero, Submodule.one_eq_span]
    congr 1
    ext x
    simp only [Set.mem_image, pow_zero, Set.mem_singleton_iff]
    exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨0, T.zero_mem, h.symm⟩⟩
  | succ n ih =>
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, rfl⟩
      exact Submodule.pow_mem_pow _ (Submodule.subset_span hx) _
    · rw [pow_succ', ← ih, Submodule.span_mul_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
      exact mul_pow_mem_of_additive_powers (K := K) T
        (Submodule.span K ((fun x : B => x ^ (n + 1)) '' (T : Set B))) n
        (fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩) ha hb

end Submodule

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

/-- The actual dominant-integral weights, including zero, as an additive monoid. -/
def dominantWeightMonoid : AddSubmonoid (Dual K H) where
  carrier := {Λ | P.IsDominantIntegral Λ}
  zero_mem' := fun _ => ⟨0, by simp⟩
  add_mem' := by
    intro Λ μ hΛ hμ i
    obtain ⟨n, hn⟩ := hΛ i
    obtain ⟨m, hm⟩ := hμ i
    exact ⟨n + m, by simp [hn, hm]⟩

include hA in
/-- Dominant-integral weights span the actual Cartan dual. The dimension equality is
derived from finite type, not assumed as an additional hypothesis. -/
theorem span_dominantWeightMonoid :
    Submodule.span K (dominantWeightMonoid P : Set (Dual K H)) = ⊤ := by
  classical
  let b : Basis ι K H := Basis.mk P.linearIndependent_coroot
    (P.linearIndependent_coroot.span_eq_top_of_card_eq_finrank'
      (P.finrank_eq_card_of_isFiniteCartan hA).symm).ge
  apply top_unique
  rw [← b.dualBasis.span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩ j
  have hj : P.coroot j = b j := by simp [b]
  rw [hj, b.dualBasis_apply_self]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

include hA in
/-- In every degree, powers of actual dominant-integral weights span the full
homogeneous Cartan polynomial space, before averaging.
Reconstructed interpolation proof of Etingof, Lecture 10, Theorem 10.1(ii), spanning step. -/
theorem span_dominant_powers (n : ℕ) :
    Submodule.span K {p : SymmetricAlgebra K (Dual K H) |
      ∃ Λ : Dual K H, P.IsDominantIntegral Λ ∧ SymmetricAlgebra.ι K (Dual K H) Λ ^ n = p} =
        SymmetricAlgebra.homogeneousSubmodule n := by
  let T := (dominantWeightMonoid P).map (SymmetricAlgebra.ι K (Dual K H)).toAddMonoidHom
  have hT : Submodule.span K (T : Set (SymmetricAlgebra K (Dual K H))) =
      LinearMap.range (SymmetricAlgebra.ι K (Dual K H)) := by
    rw [show (T : Set _) = (SymmetricAlgebra.ι K (Dual K H)) ''
      (dominantWeightMonoid P : Set _) from rfl,
      ← Submodule.map_span, span_dominantWeightMonoid P hA, Submodule.map_top]
  rw [SymmetricAlgebra.homogeneousSubmodule, ← hT, ← Submodule.span_addSubmonoid_pow]
  congr 1
  ext p
  constructor
  · rintro ⟨Λ, hΛ, rfl⟩
    exact ⟨SymmetricAlgebra.ι K (Dual K H) Λ, ⟨Λ, hΛ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨Λ, hΛ, rfl⟩, rfl⟩
    exact ⟨Λ, hΛ, rfl⟩

/-- Every actual Weyl-invariant homogeneous Cartan polynomial is a linear
combination of distinct orbit powers of dominant-integral weights.
Etingof, Lecture 10, Theorem 10.1(ii), finite averaging step. -/
theorem mem_span_distinctOrbitPower (n : ℕ) (p : SymmetricAlgebra K (Dual K H))
    (hp : p ∈ SymmetricAlgebra.homogeneousSubmodule n)
    (hw : ∀ w : P.weylGroup hA.isGeneralizedCartan,
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp w.val.toLinearMap) p = p) :
    p ∈ Submodule.span K {q | ∃ Λ : Dual K H, P.IsDominantIntegral Λ ∧
      distinctOrbitPower P hA Λ n = q} := by
  classical
  have := P.finite_weylGroup hA
  let : Fintype (P.weylGroup hA.isGeneralizedCartan) := Fintype.ofFinite _
  let S := Submodule.span K {q | ∃ Λ : Dual K H, P.IsDominantIntegral Λ ∧
    distinctOrbitPower P hA Λ n = q}
  let R : SymmetricAlgebra K (Dual K H) →ₗ[K] SymmetricAlgebra K (Dual K H) :=
    ∑ w : P.weylGroup hA.isGeneralizedCartan,
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp
        w.val.toLinearMap)).toLinearMap
  have hR : R p ∈ S := by
    clear hw
    rw [← span_dominant_powers P hA n] at hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Λ, hΛ, rfl⟩ := hx
      have he : R (SymmetricAlgebra.ι K (Dual K H) Λ ^ n) =
          (orbitStabilizerCard P hA Λ : K) • distinctOrbitPower P hA Λ n := by
        simpa [R] using fullWeylPower_eq_stabilizer_smul P hA Λ n
      rw [he]
      exact S.smul_mem _ (Submodule.subset_span ⟨Λ, hΛ, rfl⟩)
    | zero => simpa only [map_zero] using S.zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using S.add_mem hx hy
    | smul a x _ hx => simpa only [map_smul] using S.smul_mem a hx
  have he : R p = (Fintype.card (P.weylGroup hA.isGeneralizedCartan) : K) • p := by
    simp [R, hw, Nat.cast_smul_eq_nsmul]
  rw [he] at hR
  exact (S.smul_mem_iff (by exact_mod_cast Fintype.card_ne_zero)).mp hR

/-- Actual homogeneous Chevalley extension, without a spanning or extension premise.
Etingof, Lecture 10, Theorem 10.1(ii), degreewise surjectivity. -/
theorem exists_homogeneous_chevalley_extension (n : ℕ) (p : SymmetricAlgebra K (Dual K H))
    (hp : p ∈ SymmetricAlgebra.homogeneousSubmodule n)
    (hw : ∀ w : P.weylGroup hA.isGeneralizedCartan,
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp w.val.toLinearMap) p = p) :
    ∃ F : SymmetricAlgebra K (Dual K P.KacMoodyAlgebra),
      F ∈ SymmetricAlgebra.homogeneousSubmodule n ∧
      (∀ x : P.KacMoodyAlgebra,
        SymmetricAlgebra.derivation (LieModule.toEnd K P.KacMoodyAlgebra
          (Dual K P.KacMoodyAlgebra) x) F = 0) ∧
      coordinateCartanRestriction P F = p := by
  have hs := mem_span_distinctOrbitPower P hA n p hp hw
  clear hp hw
  induction hs using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨Λ, hΛ, rfl⟩ := hq
    exact exists_distinctOrbitPower_extension P hA Λ hΛ n
  | zero => exact ⟨0, Submodule.zero_mem _, by simp, by simp⟩
  | add q r _ _ hq hr =>
    obtain ⟨F, hF, hiF, heF⟩ := hq
    obtain ⟨G, hG, hiG, heG⟩ := hr
    exact ⟨F + G, Submodule.add_mem _ hF hG,
      by simp [hiF, hiG], by simp [heF, heG]⟩
  | smul c q _ hq =>
    obtain ⟨F, hF, hiF, heF⟩ := hq
    exact ⟨c • F, Submodule.smul_mem _ c hF,
      by simp [Derivation.map_smul, hiF], by simp [heF]⟩

/-- Exact spanning criterion: the span of distinct dominant orbit powers is precisely
the full homogeneous Weyl fixed space, not a smaller span-defined target.
Etingof, Lecture 10, Theorem 10.1(ii), orbit-power spanning criterion. -/
theorem mem_span_distinctOrbitPower_iff (n : ℕ) (p : SymmetricAlgebra K (Dual K H)) :
    p ∈ Submodule.span K {q | ∃ Λ : Dual K H, P.IsDominantIntegral Λ ∧
      distinctOrbitPower P hA Λ n = q} ↔
    p ∈ SymmetricAlgebra.homogeneousSubmodule n ∧
      ∀ w : P.weylGroup hA.isGeneralizedCartan,
        SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp w.val.toLinearMap) p = p := by
  constructor
  · intro hp
    induction hp using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨Λ, hΛ, rfl⟩ := hq
      obtain ⟨F, hF, hiF, heF⟩ := exists_distinctOrbitPower_extension P hA Λ hΛ n
      rw [← heF]
      exact ⟨SymmetricAlgebra.lift_comp_ι_mem_homogeneous _ _ hF,
        fun w => coordinateCartanRestriction_weyl_of_invariant P hA F hiF w.property⟩
    | zero => exact ⟨Submodule.zero_mem _, by simp⟩
    | add q r _ _ hq hr => exact ⟨Submodule.add_mem _ hq.1 hr.1, by simp [hq.2, hr.2]⟩
    | smul c q _ hq => exact ⟨Submodule.smul_mem _ c hq.1, by simp [hq.2]⟩
  · rintro ⟨hp, hw⟩
    exact mem_span_distinctOrbitPower P hA n p hp hw

/-- Every actual Weyl-invariant coordinate polynomial has an infinitesimally invariant
extension. Finite homogeneous decomposition upgrades the degreewise result.
Etingof, Lecture 10, Theorem 10.1(ii), surjectivity only. -/
theorem exists_chevalley_extension (p : SymmetricAlgebra K (Dual K H))
    (hw : ∀ w : P.weylGroup hA.isGeneralizedCartan,
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp w.val.toLinearMap) p = p) :
    ∃ F : SymmetricAlgebra K (Dual K P.KacMoodyAlgebra),
      (∀ x : P.KacMoodyAlgebra,
        SymmetricAlgebra.derivation (LieModule.toEnd K P.KacMoodyAlgebra
          (Dual K P.KacMoodyAlgebra) x) F = 0) ∧
      coordinateCartanRestriction P F = p := by
  classical
  have he (n : ℕ) := exists_homogeneous_chevalley_extension P hA n
    (SymmetricAlgebra.homogeneousComponent n p)
    (SymmetricAlgebra.homogeneousComponent_mem n p) (fun w => by
      rw [← SymmetricAlgebra.homogeneousComponent_lift_comp_ι, hw w])
  choose F _ hiF heF using he
  let b := Free.chooseBasis K (Dual K H)
  let N := (SymmetricAlgebra.equivMvPolynomial b p).totalDegree + 1
  refine ⟨∑ n ∈ Finset.range N, F n, ?_, ?_⟩
  · intro x
    simp only [map_sum, hiF, Finset.sum_const_zero]
  · simp only [map_sum, heF]
    apply (SymmetricAlgebra.equivMvPolynomial b).injective
    simpa only [map_sum, SymmetricAlgebra.equivMvPolynomial_homogeneousComponent] using
      (MvPolynomial.sum_homogeneousComponent (φ := SymmetricAlgebra.equivMvPolynomial b p))

/-- Literal coordinate Cartan restriction, with its genuine invariant source and
Weyl-fixed target. Neither space is defined by the span or range of the map. -/
def chevalleyRestriction :
    {F : SymmetricAlgebra K (Dual K P.KacMoodyAlgebra) //
      ∀ x : P.KacMoodyAlgebra,
        SymmetricAlgebra.derivation (LieModule.toEnd K P.KacMoodyAlgebra
          (Dual K P.KacMoodyAlgebra) x) F = 0} →
    {p : SymmetricAlgebra K (Dual K H) //
      ∀ w : P.weylGroup hA.isGeneralizedCartan,
        SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp w.val.toLinearMap) p = p} :=
  fun F => ⟨coordinateCartanRestriction P F.val,
    fun w => coordinateCartanRestriction_weyl_of_invariant P hA F.val F.property w.property⟩

/-- Actual Chevalley restriction is surjective in finite type over characteristic zero.
Etingof, Lecture 10, Theorem 10.1(ii), surjectivity only; no injectivity is asserted. -/
theorem chevalleyRestriction_surjective : Function.Surjective (chevalleyRestriction P hA) := by
  intro p
  obtain ⟨F, hiF, heF⟩ := exists_chevalley_extension P hA p.val p.property
  exact ⟨⟨F, hiF⟩, Subtype.ext heF⟩

end Matrix.Realization.KacMoodyAlgebra
