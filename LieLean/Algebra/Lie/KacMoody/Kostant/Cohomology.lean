/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.CochainDualityFinrank
import LieLean.Algebra.Lie.Homology.Transport
import LieLean.Algebra.Lie.KacMoody.CategoryOExtCohomology
import LieLean.Algebra.Lie.KacMoody.CategoryOExtSimple
import LieLean.Algebra.Lie.KacMoody.DualVermaCohomology
import LieLean.Algebra.Lie.KacMoody.Kostant.Theorem
import LieLean.Algebra.Lie.KacMoody.TranslationSelfDual

/-!
# Bott's theorem in the `𝔫`-cohomology form

For `V` in category `𝒪` of a Kac–Moody algebra, the weight spaces of the cohomology of `𝔫 = 𝔫₊`
with coefficients in the restricted dual `V^∨` have the same dimensions as the weight spaces of
the homology of `𝔫₋` with coefficients in `V`. For `V = L(λ)`, which is self-dual, the
Garland–Lepowsky theorem then computes `Hᵏ(𝔫, L(λ))`: Bott's theorem in the cohomological form
of Humphreys. With Humphreys' Prop. 6.15 (b) this computes `Extᵏ_𝒪(M(μ), L(λ))` in finite type.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.finrank_nPosHomology_omegaTwist`:
  `dim H_k(𝔫₊, V^ω)_{ν} = dim H_k(𝔫₋, V)_{-ν}`, transported along the Chevalley involution.
* `Matrix.Realization.KacMoodyAlgebra.finrank_nPosCohomology_restrictedDual`:
  `dim Hᵏ(𝔫, V^∨)_μ = dim H_k(𝔫₋, V)_μ` for `V` in `𝒪`.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.finrank_nPosCohomology_eq_one`,
  `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.finrank_nPosCohomology_eq_zero`:
  **Bott's theorem** for symmetrizable `A` and `λ` dominant integral: `Hᵏ(𝔫, L(λ))_μ` is
  one-dimensional if `μ = w(λ + ρ) - ρ` with `ℓ(w) = k`, and zero otherwise.
* `Matrix.Realization.KacMoodyAlgebra.CategoryO.finrank_ext_verma_simple_eq_one`,
  `Matrix.Realization.KacMoodyAlgebra.CategoryO.finrank_ext_verma_simple_eq_zero`: in finite
  type, `dim Extᵏ_𝒪(M(w·λ), L(λ)) = 1` for `ℓ(w) = k`, and `Extᵏ_𝒪(M(μ), L(λ)) = 0` for the
  other `μ`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Thm. 6.6 (Bott's theorem) and the application of Prop. 6.15 (b) in §6.15.
  Humphreys states these in finite type; the cohomological Bott theorem here holds for every
  symmetrizable generalized Cartan matrix. The deduction from the homological form by duality
  is our own.
-/

open Module LieModule LieModule.ChevalleyEilenberg CategoryTheory

noncomputable section

universe u

namespace Matrix.Realization.KacMoodyAlgebra

section Transport

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-! ### Transport along the Chevalley involution -/

lemma nPosEquivNNeg_D (a : H) (x : nPos P) :
    nPosEquivNNeg P ((nPosDerivAction P (OmegaTwist P V)).D a x) =
      -(nNegDerivAction P V).D a (nPosEquivNNeg P x) :=
  Subtype.ext (by
    change chevalleyInvolution P ⁅h P a, (x : P.KacMoodyAlgebra)⁆ =
      -⁅h P a, chevalleyInvolution P (x : P.KacMoodyAlgebra)⁆
    rw [LieHom.map_lie, chevalleyInvolution_h, neg_lie])

lemma omegaTwist_symm_φ (a : H) (m : OmegaTwist P V) :
    (OmegaTwist.of P V).symm ((nPosDerivAction P (OmegaTwist P V)).φ a m) =
      -(nNegDerivAction P V).φ a ((OmegaTwist.of P V).symm m) := by
  change ⁅chevalleyInvolution P (h P a), (OmegaTwist.of P V).symm m⁆ =
    -⁅h P a, (OmegaTwist.of P V).symm m⁆
  rw [chevalleyInvolution_h, neg_lie]

omit [LieModule K P.KacMoodyAlgebra V] in
lemma omegaTwist_symm_lie (x : nPos P) (m : OmegaTwist P V) :
    (OmegaTwist.of P V).symm ⁅x, m⁆ = ⁅nPosEquivNNeg P x, (OmegaTwist.of P V).symm m⁆ := rfl

variable {P V}

variable (hV : IsCategoryO P V)
include hV

/-- The chains `C_k(𝔫₊, V^ω)_ν` are finite-dimensional for `V` in `𝒪`. -/
theorem IsCategoryO.finiteDimensional_nPosChains_omegaTwist (k : ℕ) (ν : Dual K H) :
    FiniteDimensional K ↥(chainsIn K (nPos P) (OmegaTwist P V) k ⊓
      (nPosDerivAction P (OmegaTwist P V)).chainWeightSpace ν) := by
  have hC := DerivAction.map_chainEquiv_chainsIn_inf (ρ := nPosDerivAction P (OmegaTwist P V))
    (ρ' := nNegDerivAction P V) (nPosEquivNNeg P) (OmegaTwist.of P V).symm
    (nPosEquivNNeg_D P V) (omegaTwist_symm_φ P V) k ν
  have := hV.finiteDimensional_nNegChains k (-ν)
  exact Module.Finite.equiv (((DerivAction.chainEquiv (nPosEquivNNeg P)
    (OmegaTwist.of P V).symm).submoduleMap _).trans (LinearEquiv.ofEq _ _ hC)).symm

/-- `dim H_k(𝔫₊, V^ω)_ν = dim H_k(𝔫₋, V)_{-ν}` for `V` in `𝒪`: the Chevalley involution
identifies the two complexes and reverses the weights. -/
theorem finrank_nPosHomology_omegaTwist (k : ℕ) (ν : Dual K H) :
    finrank K ((nPosDerivAction P (OmegaTwist P V)).homologyWeightSpace k ν) =
      finrank K ((nNegDerivAction P V).homologyWeightSpace k (-ν)) := by
  have := hV.finiteDimensional_nNegChains k (-ν)
  have : FiniteDimensional K
      ↥(cycles K (nNeg P) V k ⊓ (nNegDerivAction P V).chainWeightSpace (-ν)) :=
    Submodule.finiteDimensional_of_le (inf_le_inf_right _ inf_le_left)
  exact DerivAction.finrank_homologyWeightSpace_of_neg (nPosEquivNNeg P) (OmegaTwist.of P V).symm
    (omegaTwist_symm_lie P V) (nPosEquivNNeg_D P V) (omegaTwist_symm_φ P V) k ν

/-- **`dim Hᵏ(𝔫, V^∨)_μ = dim H_k(𝔫₋, V)_μ`** for `V` in `𝒪`. -/
theorem finrank_nPosCohomology_restrictedDual (μ : Dual K H) (k : ℕ) :
    finrank K (nPosCohomology P (restrictedDual P V) μ k) =
      finrank K ((nNegDerivAction P V).homologyWeightSpace k μ) := by
  rw [nPosCohomology, (nPosDerivAction P (OmegaTwist P V)).finrank_weightComplex_homology
    (nPosDerivAction P (restrictedDual P V)) (iSup_weightSpaceOf_adNPos P)
    (iSup_weightSpaceOf_omegaTwist P hV.iSup_weightSpaceOfMap_eq_top) (fun _ ↦ rfl)
    (fun a φ m ↦ dualPairing_lie P (h P a) φ m) (dualPairing_injective P)
    (fun _ _ hψ ↦ mem_range_dualPairing P hψ)
    (fun x φ m ↦ dualPairing_lie P (x : P.KacMoodyAlgebra) φ m)
    (fun j ↦ hV.finiteDimensional_nPosChains_omegaTwist j (-μ)) k,
    finrank_nPosHomology_omegaTwist hV, neg_neg]

end Transport

namespace IrreducibleModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  (hA : A.IsGeneralizedCartan) (hS : A.IsSymmetrizable) {Λ : Dual K H}
  (hΛ : P.IsDominantIntegral Λ)

omit [FiniteDimensional K H] in
/-- `dim Hᵏ(𝔫, L(λ))_μ = dim H_k(𝔫₋, L(λ))_μ`, since `L(λ)` is self-dual. -/
theorem finrank_nPosCohomology_eq (μ : Dual K H) (k : ℕ) :
    finrank K (nPosCohomology P (IrreducibleModule P Λ) μ k) =
      finrank K ((nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace k μ) := by
  rw [(nPosCohomologyCongr P (equivRestrictedDual P Λ) μ k).toLinearEquiv.finrank_eq]
  exact finrank_nPosCohomology_restrictedDual (isCategoryO P Λ) μ k

include hA hS hΛ

/-- **Bott's theorem** (Humphreys GSM 94 Thm. 6.6, cohomological form), dimension part:
`dim H^{ℓ(w)}(𝔫, L(λ))_{w(λ + ρ) - ρ} = 1` for every `w ∈ W`, `A` symmetrizable and `λ`
dominant integral. -/
theorem finrank_nPosCohomology_eq_one (w : P.weylGroup hA) :
    finrank K (nPosCohomology P (IrreducibleModule P Λ)
      ((w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho) ((P.coxeterSystem hA).length w)) = 1 :=
  (finrank_nPosCohomology_eq _ _).trans (finrank_homologyWeightSpace_eq_one hA hS hΛ w)

/-- **Bott's theorem** (Humphreys GSM 94 Thm. 6.6, cohomological form), vanishing part:
`Hᵏ(𝔫, L(λ))_μ = 0` unless `μ = w(λ + ρ) - ρ` for some `w ∈ W` with `ℓ(w) = k`. -/
theorem finrank_nPosCohomology_eq_zero {k : ℕ} {μ : Dual K H}
    (h : ∀ w : P.weylGroup hA, (P.coxeterSystem hA).length w = k →
      (w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho ≠ μ) :
    finrank K (nPosCohomology P (IrreducibleModule P Λ) μ k) = 0 := by
  rw [finrank_nPosCohomology_eq]
  by_contra hne
  obtain ⟨w, hw, hwμ⟩ := (homologyWeightSpace_ne_bot_iff hA hS hΛ k μ).mp fun hbot ↦
    hne (by rw [hbot, finrank_bot])
  exact h w hw hwμ

end IrreducibleModule

namespace CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H} {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)

lemma finrank_ext_verma_simple (μ : Dual K H) (k : ℕ) :
    finrank K (Abelian.Ext.{u} (verma P μ) (simple P Λ) k) =
      finrank K (nPosCohomology P (IrreducibleModule P Λ) μ k) :=
  (nonempty_ext_verma_mk_linearEquiv_nPosCohomology μ _ _ _ k).some.finrank_eq

include hΛ

/-- **`dim Extᵏ_𝒪(M(w·λ), L(λ)) = 1` for `ℓ(w) = k`** (Humphreys GSM 94 §6.15, from Prop. 6.15 (b)
and Bott's theorem), for `λ` dominant integral, in finite type. -/
theorem finrank_ext_verma_simple_eq_one
    (w : P.weylGroup (Fact.out : A.IsFiniteCartan).isGeneralizedCartan) :
    finrank K (Abelian.Ext.{u} (verma P ((w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho))
      (simple P Λ) ((P.coxeterSystem (Fact.out : A.IsFiniteCartan).isGeneralizedCartan).length w))
      = 1 := by
  rw [finrank_ext_verma_simple]
  exact IrreducibleModule.finrank_nPosCohomology_eq_one _
    (Fact.out : A.IsFiniteCartan).isSymmetrizable hΛ w

/-- **`Extᵏ_𝒪(M(μ), L(λ)) = 0`** unless `μ = w·λ` with `ℓ(w) = k` (Humphreys GSM 94 §6.15), for
`λ` dominant integral, in finite type. -/
theorem finrank_ext_verma_simple_eq_zero {k : ℕ} {μ : Dual K H}
    (h : ∀ w : P.weylGroup (Fact.out : A.IsFiniteCartan).isGeneralizedCartan,
      (P.coxeterSystem (Fact.out : A.IsFiniteCartan).isGeneralizedCartan).length w = k →
        (w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho ≠ μ) :
    finrank K (Abelian.Ext.{u} (verma P μ) (simple P Λ) k) = 0 := by
  rw [finrank_ext_verma_simple]
  exact IrreducibleModule.finrank_nPosCohomology_eq_zero _
    (Fact.out : A.IsFiniteCartan).isSymmetrizable hΛ h

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
