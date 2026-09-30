/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.ChevalleySurjectivity
import LieLean.Algebra.Lie.KacMoody.WeightBasis
import LieLean.RingTheory.MvPolynomial.LowestWeight

/-!
# Chevalley restriction injectivity

An infinitesimally invariant coordinate polynomial on a Lie algebra that vanishes on a
"Cartan" subspace is zero, provided the Lie algebra has a basis of weight vectors whose
weight-zero members span exactly that subspace. In finite type this makes the literal
Chevalley restriction map bijective.

## Main results

* `SymmetricAlgebra.derivation_ext`: derivations of a symmetric algebra agree once they agree
  on generators.
* `LieAlgebra.eq_zero_of_invariant_of_restrict_eq_zero`: the general injectivity criterion.
* `Matrix.Realization.KacMoodyAlgebra.eq_zero_of_invariant_of_coordinateCartanRestriction_eq_zero`:
  its finite-type Kac–Moody instance.
* `Matrix.Realization.KacMoodyAlgebra.chevalleyRestriction_injective`,
  `chevalleyRestriction_bijective`, `chevalleyRestrictionEquiv`: Chevalley's restriction theorem
  for the finite-type realization, as a bijection between the genuine infinitesimal invariants
  and the genuine Weyl-fixed Cartan polynomials.

## Proof

Choose coordinates dual to a weight basis, with weight `0` on Cartan coordinates and `1` on
root coordinates. The weight-zero component of an invariant `F` is its restriction, hence zero.
If the components of `F` below weight `k ≥ 1` vanish, the component of weight `k - 1` of
`D_{x_α} F = 0` (for a root vector `x_α`) is `ℓ_α · ∂F_k/∂u_α`, where `ℓ_α ≠ 0` is the linear
form `h ↦ α(h)` in the Cartan coordinates. Hence all root derivatives of `F_k` vanish and the
Euler identity gives `F_k = 0`. This lowest-term argument is the infinitesimal version of
`Ad(N)·h = h + 𝔫` for regular `h` and replaces the density of semisimple elements used in
the sources; it is reconstructed, not transcribed.

## References

* Humphreys, *Introduction to Lie algebras and representation theory*, GTM 9, §23.1 (check).
* Etingof, MIT 18.757 (Fall 2023), Lecture 10, Theorem 10.1(ii) (check), injectivity:
  https://ocw.mit.edu/courses/18-757-representations-of-lie-groups-fall-2023/mit18_757_f23_lec10.pdf
* Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  §1.10 (check), where Chevalley's theorem feeds the Harish-Chandra isomorphism.
-/

noncomputable section

open Module

namespace SymmetricAlgebra

variable {K : Type} {M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Derivations of the symmetric algebra are determined by their values on generators. -/
theorem derivation_ext {D₁ D₂ : Derivation K (SymmetricAlgebra K M) (SymmetricAlgebra K M)}
    (h : ∀ x, D₁ (ι K M x) = D₂ (ι K M x)) : D₁ = D₂ := by
  ext p
  induction p using SymmetricAlgebra.induction with
  | algebraMap c => simp only [Derivation.map_algebraMap]
  | ι x => exact h x
  | mul p q hp hq => simp only [Derivation.leibniz, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

/-- In the coordinates of a basis, the canonical derivation extension is the polynomial
derivation with the same values on the variables. -/
theorem equivMvPolynomial_derivation {κ : Type*} (b : Basis κ K M) (D : M →ₗ[K] M)
    (p : SymmetricAlgebra K M) :
    equivMvPolynomial b (derivation D p) =
      MvPolynomial.mkDerivation K (fun i => equivMvPolynomial b (ι K M (D (b i))))
        (equivMvPolynomial b p) := by
  have h : derivation D = derivationOfBasis b D :=
    derivation_ext fun x => by rw [derivation_ι, derivationOfBasis_ι]
  rw [h]
  exact (equivMvPolynomial b).apply_symm_apply _

/-- Coordinates of a linear form in the dual basis. -/
theorem equivMvPolynomial_dualBasis_ι {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Basis κ K M) (φ : Dual K M) :
    equivMvPolynomial b.dualBasis (ι K (Dual K M) φ) = ∑ u, φ (b u) • MvPolynomial.X u := by
  conv_lhs => rw [← b.dualBasis.sum_repr φ]
  simp only [map_sum, map_smul, equivMvPolynomial_ι_apply, Basis.dualBasis_repr]

end SymmetricAlgebra

namespace LieAlgebra

variable {K : Type} [Field K] [CharZero K] {L : Type*} [LieRing L] [LieAlgebra K L]
  {H : Type*} [AddCommGroup H] [Module K H] {ν : Type*} [Finite ν]

open MvPolynomial in
/-- **Injectivity of restriction for invariant polynomials.** Let `b` be a basis of `L` by
weight vectors for the image of `j : H → L` (weights `μ u`), whose weight-zero members span
exactly that image. An infinitesimally coadjoint-invariant coordinate polynomial on `L` whose
restriction along `j` vanishes is zero. Only invariance under the root vectors (the `b u` of
nonzero weight) is used. Reconstructed lowest-term proof of the injectivity half of
Chevalley's restriction theorem (Humphreys, GTM 9, §23.1 (check)). -/
theorem eq_zero_of_invariant_of_restrict_eq_zero (j : H →ₗ[K] L) (b : Basis ν K L)
    (μ : ν → Dual K H) (hμ : ∀ u a, ⁅j a, b u⁆ = μ u a • b u)
    (hspan : Submodule.span K (b '' {u | μ u = 0}) = LinearMap.range j)
    (F : SymmetricAlgebra K (Dual K L))
    (hF : ∀ x : L, SymmetricAlgebra.derivation (LieModule.toEnd K L (Dual K L) x) F = 0)
    (hres : SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp j.dualMap) F = 0) :
    F = 0 := by
  classical
  cases nonempty_fintype ν
  set e := SymmetricAlgebra.equivMvPolynomial b.dualBasis with he_def
  let w : ν → ℕ := fun u => if μ u = 0 then 0 else 1
  have hw : ∀ u, w u ≤ 1 := fun u => by simp only [w]; split_ifs <;> omega
  have hw0 : ∀ u, w u = 0 ↔ μ u = 0 := fun u => by simp only [w]; split_ifs <;> simp_all
  -- Cartan preimages of the weight-zero basis vectors.
  have hC : ∀ u, ∃ a : H, μ u = 0 → j a = b u := fun u => by
    by_cases hu : μ u = 0
    · obtain ⟨a, ha⟩ : b u ∈ LinearMap.range j :=
        hspan ▸ Submodule.subset_span ⟨u, hu, rfl⟩
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hu⟩
  choose a ha using hC
  -- Step 1: the weight-zero component is the restriction.
  have h₀ : weightedHomogeneousComponent w 0 (e F) = 0 := by
    let T : Dual K H →ₗ[K] MvPolynomial ν K :=
      ∑ u ∈ Finset.univ.filter (fun u => μ u = 0),
        (Module.Dual.eval K H (a u)).smulRight (X u)
    let τ := SymmetricAlgebra.lift T
    let R := SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp j.dualMap)
    have hζ : τ.comp (R.comp e.symm.toAlgHom) =
        aeval (fun u => if w u = 0 then X u else 0) := by
      apply MvPolynomial.algHom_ext
      intro u
      have h1 : e.symm (X u) = SymmetricAlgebra.ι K (Dual K L) (b.dualBasis u) :=
        SymmetricAlgebra.equivMvPolynomial_symm_X _ u
      have h2 : ∀ ψ : Dual K H, τ (SymmetricAlgebra.ι K (Dual K H) ψ) =
          ∑ u' ∈ Finset.univ.filter (fun u => μ u = 0), ψ (a u') • X u' := fun ψ => by
        simp [τ, T, LinearMap.sum_apply]
      change τ (R (e.symm (X u))) = aeval (fun u => if w u = 0 then X u else 0) (X u)
      rw [h1, aeval_X]
      simp only [R, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, h2,
        LinearMap.dualMap_apply]
      rw [Finset.sum_congr rfl (g := fun u' => if u' = u then X u' else 0)]
      · rw [Finset.sum_ite_eq']
        simp [hw0]
      · intro u' hu'
        rw [ha u' (Finset.mem_filter.mp hu').2, Basis.dualBasis_apply_self]
        split_ifs <;> simp
    rw [← aeval_weight_zero_eq_weightedHomogeneousComponent, ← hζ]
    change τ (R (e.symm (e F))) = 0
    rw [AlgEquiv.symm_apply_apply]
    change τ (SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp j.dualMap) F) = 0
    rw [hres, map_zero]
  -- Step 2: the derivations of the root vectors, in coordinates.
  have hDx : ∀ x : L, MvPolynomial.mkDerivation K
      (fun i => e (SymmetricAlgebra.ι K (Dual K L) ⁅x, b.dualBasis i⁆)) (e F) = 0 := by
    intro x
    have h := SymmetricAlgebra.equivMvPolynomial_derivation b.dualBasis
      (LieModule.toEnd K L (Dual K L) x) F
    rw [hF x, map_zero] at h
    simpa only [LieModule.toEnd_apply_apply] using h.symm
  have hcomp : ∀ u i, weightedHomogeneousComponent w 0
      (e (SymmetricAlgebra.ι K (Dual K L) ⁅b u, b.dualBasis i⁆)) =
      ∑ u', if w u' = 0 then (μ u (a u') * (if u = i then 1 else 0)) • X u' else 0 := by
    intro u i
    rw [he_def, SymmetricAlgebra.equivMvPolynomial_dualBasis_ι, map_sum]
    refine Finset.sum_congr rfl fun u' _ => ?_
    rw [map_smul]
    have hX := isWeightedHomogeneous_X K w u'
    by_cases hu' : w u' = 0
    · rw [ite_eq_left hu']
      rw [hu'] at hX
      rw [hX.weightedHomogeneousComponent_same, Module.Dual.lie_apply,
        ← ha u' ((hw0 u').mp hu'), ← lie_skew, hμ, map_neg, neg_neg, map_smul,
        Basis.dualBasis_apply_self, smul_eq_mul]
    · rw [ite_eq_right hu', hX.weightedHomogeneousComponent_ne 0 (Ne.symm hu'), smul_zero]
  have hD : ∀ u, w u = 1 → ∃ D : Derivation K (MvPolynomial ν K) (MvPolynomial ν K),
      D (e F) = 0 ∧ weightedHomogeneousComponent w 0 (D (X u)) ≠ 0 ∧
        ∀ i, i ≠ u → w i = 1 → weightedHomogeneousComponent w 0 (D (X i)) = 0 := by
    intro u hu
    refine ⟨_, hDx (b u), ?_, fun i hi _ => ?_⟩
    · rw [mkDerivation_X, hcomp]
      intro h0
      have hc : ∀ u', μ u' = 0 → μ u (a u') = 0 := by
        intro u' hu'
        simp only [ite_true, mul_one] at h0
        have := congrArg (fun q => q.coeff (Finsupp.single u' 1)) h0
        rw [MvPolynomial.coeff_sum, Finset.sum_eq_single u'] at this
        · simpa [(hw0 u').mpr hu', coeff_X] using this
        · intro c _ hc
          split_ifs <;> simp [coeff_X, Finsupp.single_left_inj, hc]
        · simp
      have hμu : μ u = 0 := by
        ext x
        have hx : j x ∈ Submodule.span K (b '' {u | μ u = 0}) := hspan ▸ ⟨x, rfl⟩
        have hle : Submodule.span K (b '' {u | μ u = 0}) ≤ LinearMap.ker (ad K L (b u)) := by
          rw [Submodule.span_le]
          rintro _ ⟨u', hu', rfl⟩
          change ⁅b u, b u'⁆ = 0
          rw [← ha u' hu', ← lie_skew, hμ, hc u' hu', zero_smul, neg_zero]
        have h1 : ⁅b u, j x⁆ = 0 := hle hx
        rw [← lie_skew, hμ, neg_eq_zero, smul_eq_zero] at h1
        exact h1.resolve_right (b.ne_zero u)
      have : w u = 0 := (hw0 u).mpr hμu
      omega
    · rw [mkDerivation_X, hcomp]
      simp [Ne.symm hi]
  -- Step 3: the lowest-weight vanishing criterion.
  have hp := eq_zero_of_derivation_lowestWeight w hw h₀ hD
  exact (map_eq_zero_iff e e.injective).mp hp

end LieAlgebra

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

omit [FiniteDimensional K H] in
/-- The weight-zero vectors of the adjoint weight basis span exactly the Cartan subalgebra. -/
theorem span_diagWeightBasis_zero :
    Submodule.span K (diagWeightBasis (isHDiagonalizable_adjoint P) ''
      {u | u.1 = 0}) = LinearMap.range (h P) := by
  classical
  set hV := isHDiagonalizable_adjoint P
  rw [← rootSpace_zero]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have hm := diagWeightBasis_mem hV u
    rw [Set.mem_ofPred_eq.mp hu] at hm
    exact hm
  · intro x hx
    let B₀ := Basis.ofVectorSpace K (weightSpace P 𝔤 0)
    have hx' : x ∈ Submodule.span K (Subtype.val '' Set.range B₀) := by
      have hm := Submodule.mem_map_of_mem (f := (weightSpace P 𝔤 0).subtype)
        (B₀.mem_span ⟨x, hx⟩)
      rw [Submodule.map_span] at hm
      exact hm
    refine Submodule.span_mono ?_ hx'
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨⟨0, k⟩, rfl, ?_⟩
    simp [diagWeightBasis, IsHDiagonalizable.weightBasis, DirectSum.IsInternal.collectedBasis_coe,
      B₀]

include hA in
/-- **Chevalley restriction injectivity**, finite type: an infinitesimally invariant coordinate
polynomial on `𝔤(A)` whose literal restriction to the Cartan subalgebra vanishes is zero.
Humphreys, GTM 9, §23.1 (check); Etingof, Lecture 10, Theorem 10.1(ii) (check), injectivity.
The proof (reconstructed) is the lowest-term argument of
`LieAlgebra.eq_zero_of_invariant_of_restrict_eq_zero`, applied to an adjoint weight basis. -/
theorem eq_zero_of_invariant_of_coordinateCartanRestriction_eq_zero
    (F : SymmetricAlgebra K (Dual K 𝔤))
    (hF : ∀ x : 𝔤, SymmetricAlgebra.derivation (LieModule.toEnd K 𝔤 (Dual K 𝔤) x) F = 0)
    (h₀ : coordinateCartanRestriction P F = 0) : F = 0 := by
  classical
  have := finiteDimensional P hA
  set hV := isHDiagonalizable_adjoint P
  have : Finite (DiagWeightBasisIndex P 𝔤) := Module.Finite.finite_basis (diagWeightBasis hV)
  exact LieAlgebra.eq_zero_of_invariant_of_restrict_eq_zero (h P) (diagWeightBasis hV)
    (fun u => u.1) (fun u a => diagWeightBasis_mem hV u a) (span_diagWeightBasis_zero P) F hF h₀

/-- **Chevalley restriction is injective** on the genuine infinitesimal invariants, in finite
type over any characteristic-zero field. Etingof, Lecture 10, Theorem 10.1(ii) (check). -/
theorem chevalleyRestriction_injective : Function.Injective (chevalleyRestriction P hA) := by
  intro F G hFG
  have he : coordinateCartanRestriction P F.val = coordinateCartanRestriction P G.val :=
    congrArg Subtype.val hFG
  apply Subtype.ext
  rw [← sub_eq_zero]
  apply eq_zero_of_invariant_of_coordinateCartanRestriction_eq_zero P hA
  · intro x
    rw [map_sub, F.property x, G.property x, sub_zero]
  · rw [map_sub, he, sub_self]

/-- **Chevalley's restriction theorem** for the finite-type realization: literal coordinate
restriction is a bijection from the infinitesimally invariant polynomials on `𝔤(A)` onto the
Weyl-fixed polynomials on the Cartan subalgebra. Neither side is defined through the map.
Humphreys, GTM 9, §23.1 (check); Etingof, Lecture 10, Theorem 10.1 (check). -/
theorem chevalleyRestriction_bijective : Function.Bijective (chevalleyRestriction P hA) :=
  ⟨chevalleyRestriction_injective P hA, chevalleyRestriction_surjective P hA⟩

/-- Chevalley's restriction theorem as an explicit equivalence of the two genuine spaces. -/
def chevalleyRestrictionEquiv :
    {F : SymmetricAlgebra K (Dual K 𝔤) //
      ∀ x : 𝔤, SymmetricAlgebra.derivation (LieModule.toEnd K 𝔤 (Dual K 𝔤) x) F = 0} ≃
    {p : SymmetricAlgebra K (Dual K H) //
      ∀ w : P.weylGroup hA.isGeneralizedCartan,
        SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K H)).comp w.val.toLinearMap) p = p} :=
  Equiv.ofBijective _ (chevalleyRestriction_bijective P hA)

@[simp] theorem chevalleyRestrictionEquiv_apply (F) :
    (chevalleyRestrictionEquiv P hA F).val = coordinateCartanRestriction P F.val := rfl

end Matrix.Realization.KacMoodyAlgebra
