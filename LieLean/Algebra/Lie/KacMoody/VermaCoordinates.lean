/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterVerma
import LieLean.Algebra.Lie.KacMoody.VermaEmbedding
import LieLean.Algebra.Lie.UniversalEnveloping.LeadingAction

/-!
# PBW coordinates on Verma modules

Let `(f_j)` be the basis `nNegBasis` of `𝔫₋` consisting of root vectors, `f_j ∈ 𝔤_{-α_j}`.
By PBW, `u ↦ u v_λ` and the PBW isomorphism `U(𝔫₋) ≃ K[x_j]` give polynomial coordinates
`M(λ) ≃ K[x_j]` in which:

* `f_j` acts by multiplication by `x_j` up to terms of lower total degree
  (`Matrix.Realization.KacMoodyAlgebra.VermaModule.vermaCoord_lie_nNegBasis_sub_mem`);
* the Borel subalgebra `𝔟 = 𝔥 ⊕ 𝔫₊` does not raise the total degree
  (`Matrix.Realization.KacMoodyAlgebra.VermaModule.vermaCoord_lie_mem_of_mem_borel`);
* the monomial `x^m` corresponds to a weight vector of weight `λ - Σ mⱼ αⱼ`
  (`Matrix.Realization.KacMoodyAlgebra.VermaModule.vermaCoord_symm_monomial_mem_weightSpace`).

These are the coordinates used for the relative chains in the proof of Humphreys, GSM 94,
Thm. 6.15 (a).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.vermaCoord`: the coordinates `M(λ) ≃ K[x_j]`.
-/

open Module MvPolynomial UniversalEnvelopingAlgebra

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝓤₋" => UniversalEnvelopingAlgebra K (nNeg P)

namespace VermaModule

/-- The PBW coordinates `M(λ) ≃ U(𝔫₋) ≃ K[x_j]`. -/
def vermaCoord (Λ : Dual K H) : VermaModule P Λ ≃ₗ[K] MvPolynomial (NegRootIndex P) K :=
  (equivEnvNNeg P Λ).symm ≪≫ₗ pbwEquiv (nNegBasis P)

lemma vermaCoord_symm_apply (Λ : Dual K H) (q : MvPolynomial (NegRootIndex P) K) :
    (vermaCoord P Λ).symm q = equivEnvNNeg P Λ ((pbwEquiv (nNegBasis P)).symm q) := rfl

lemma vermaCoord_equivEnvNNeg (Λ : Dual K H) (u : 𝓤₋) :
    vermaCoord P Λ (equivEnvNNeg P Λ u) = pbwEquiv (nNegBasis P) u := by
  rw [vermaCoord, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

lemma vermaCoord_mem_iff (Λ : Dual K H) {n : ℕ} (u : 𝓤₋) :
    vermaCoord P Λ (equivEnvNNeg P Λ u) ∈ restrictTotalDegree (NegRootIndex P) K n ↔
      u ∈ filtration K (nNeg P) n := by
  rw [vermaCoord_equivEnvNNeg, mem_filtration_iff_pbwEquiv (nNegBasis P)]

/-- **Leading term of `f_j`**: in PBW coordinates, `f_j` acts by multiplication by `x_j` up to
terms of total degree at most that of the argument. -/
theorem vermaCoord_lie_nNegBasis_sub_mem (Λ : Dual K H) (j : NegRootIndex P) (n : ℕ)
    {q : MvPolynomial (NegRootIndex P) K} (hq : q ∈ restrictTotalDegree (NegRootIndex P) K n) :
    vermaCoord P Λ ⁅(nNegBasis P j : P.KacMoodyAlgebra), (vermaCoord P Λ).symm q⁆ - X j * q ∈
      restrictTotalDegree (NegRootIndex P) K n := by
  obtain ⟨u, rfl⟩ := (pbwEquiv (nNegBasis P)).surjective q
  rw [vermaCoord_symm_apply, LinearEquiv.symm_apply_apply, ← equivEnvNNeg_ι_mul,
    vermaCoord_equivEnvNNeg]
  exact pbwEquiv_ι_basis_mul_sub_mem (nNegBasis P) j n ((mem_filtration_iff_pbwEquiv _).mpr hq)

lemma lie_equivEnvNNeg_mem_of_mem_borel (Λ : Dual K H) (n : ℕ) :
    ∀ u ∈ filtration K (nNeg P) n, ∀ x ∈ borel P,
      (equivEnvNNeg P Λ).symm ⁅x, equivEnvNNeg P Λ u⁆ ∈ filtration K (nNeg P) n := by
  induction n with
  | zero =>
    intro u hu x hx
    obtain ⟨r, rfl⟩ := mem_filtration_zero.mp hu
    obtain ⟨a, y, hy, rfl⟩ := (mem_borel P).mp hx
    have h1 : equivEnvNNeg P Λ (algebraMap K 𝓤₋ r) = r • hwv P Λ := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, equivEnvNNeg_one]
    rw [h1, lie_smul, add_lie, lie_hwv_of_mem_nPos P Λ hy, add_zero, lie_h_hwv, smul_smul,
      ← equivEnvNNeg_one, ← map_smul, LinearEquiv.symm_apply_apply]
    exact Submodule.smul_mem _ _ (one_mem_filtration 0)
  | succ n ih =>
    intro u hu x hx
    rw [filtration_succ] at hu
    induction hu using Submodule.mul_induction_on' with
    | mem_mul_mem g hg w hw =>
      obtain ⟨g₁, hg₁, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hg
      obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hg₁
      rw [add_mul, map_add, lie_add, map_add, Algebra.algebraMap_eq_smul_one, smul_one_mul,
        map_smul, lie_smul, map_smul]
      refine add_mem (Submodule.smul_mem _ _ (filtration_mono (Nat.le_succ n) (ih w hw x hx)))
        ?_
      simp only [LieHom.coe_toLinearMap]
      obtain ⟨y', a, z, hyz⟩ := exists_triangular P ⁅x, (y : P.KacMoodyAlgebra)⁆
      have hb : h P a + eHom P z ∈ borel P := (mem_borel P).mpr ⟨a, _, ⟨z, rfl⟩, rfl⟩
      rw [equivEnvNNeg_ι_mul, leibniz_lie, map_add, hyz, add_assoc, add_lie, map_add]
      refine add_mem (add_mem ?_ ?_) ?_
      · rw [show fHom P y' = ((⟨fHom P y', y', rfl⟩ : nNeg P) : P.KacMoodyAlgebra) from rfl,
          equivEnvNNeg_symm_lie, filtration_succ]
        exact Submodule.mul_mem_mul (Submodule.mem_sup_right ⟨_, rfl⟩) hw
      · exact filtration_mono (Nat.le_succ n) (ih w hw _ hb)
      · have hw' := ih w hw x hx
        rw [← LinearEquiv.apply_symm_apply (equivEnvNNeg P Λ) ⁅x, equivEnvNNeg P Λ w⁆,
          equivEnvNNeg_symm_lie, filtration_succ]
        exact Submodule.mul_mem_mul (Submodule.mem_sup_right ⟨_, rfl⟩) hw'
    | add w w' _ _ h h' => rw [map_add, lie_add, map_add]; exact add_mem h h'

/-- **The Borel subalgebra does not raise the PBW degree.** -/
theorem vermaCoord_lie_mem_of_mem_borel (Λ : Dual K H) {x : P.KacMoodyAlgebra}
    (hx : x ∈ borel P) {n : ℕ} {q : MvPolynomial (NegRootIndex P) K}
    (hq : q ∈ restrictTotalDegree (NegRootIndex P) K n) :
    vermaCoord P Λ ⁅x, (vermaCoord P Λ).symm q⁆ ∈ restrictTotalDegree (NegRootIndex P) K n := by
  obtain ⟨u, rfl⟩ := (pbwEquiv (nNegBasis P)).surjective q
  rw [vermaCoord_symm_apply, LinearEquiv.symm_apply_apply,
    ← LinearEquiv.apply_symm_apply (equivEnvNNeg P Λ) ⁅x, equivEnvNNeg P Λ u⁆, vermaCoord_mem_iff]
  exact lie_equivEnvNNeg_mem_of_mem_borel P Λ n u ((mem_filtration_iff_pbwEquiv _).mpr hq) x hx

/-- **Weights of monomials**: `x^m` corresponds to a weight vector of weight `λ - Σ mⱼ αⱼ`. -/
theorem vermaCoord_symm_monomial_mem_weightSpace (Λ : Dual K H) (m : NegRootIndex P →₀ ℕ) :
    (vermaCoord P Λ).symm (monomial m 1) ∈ weightSpace P Λ (Λ - negRootWt P m) := by
  have h := pbwBasisVerma_mem_weightSpace P Λ m
  rwa [pbwBasisVerma, Basis.map_apply, pbwBasis_apply, ← pbwEquiv_symm_monomial]
    at h

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
