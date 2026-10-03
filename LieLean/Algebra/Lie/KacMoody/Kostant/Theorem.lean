/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Kostant.GarlandLepowsky
import LieLean.Algebra.Lie.KacMoody.Kostant.LaplacianScalar
import LieLean.Algebra.Lie.KacMoody.Kostant.Weights

/-!
# The Garland–Lepowsky theorem

Let `A` be a symmetrizable generalized Cartan matrix, `𝔤 = 𝔤(A)` over a field `K` of
characteristic zero and `Λ` a dominant integral weight. The **Garland–Lepowsky theorem**
([GL] Thm. 8.6; [Kum] Thm. 3.2.7; Kostant's theorem in finite type) states that

  `H_k(𝔫₋, L(Λ)) ≅ ⊕_{w ∈ W, ℓ(w) = k} K_{w(Λ + ρ) - ρ}` as `𝔥`-modules,

i.e. `H_k(𝔫₋, L(Λ))_μ ≠ 0` iff `μ = w(Λ + ρ) - ρ` for some `w ∈ W` with `ℓ(w) = k`, and then
`H_k(𝔫₋, L(Λ))_μ` is one-dimensional.

*Proof.* The Casimir operator acts on `L(Λ)` by `(Λ + 2ρ|Λ)`, so by Kostant's Laplacian
(`IsStandardForm.homologyWeightSpace_eq_bot`) `H_k(𝔫₋, L(Λ))_μ = 0` unless
`(μ + 2ρ|μ) = (Λ + 2ρ|Λ)`, i.e. `(μ + ρ|μ + ρ) = (Λ + ρ|Λ + ρ)`. On this sphere, Kostant's
combinatorial lemma (`IrreducibleModule.exists_weylGroup_of_homologyWeightSpace_ne_bot_of_eq`)
shows that the weights of `H_k(𝔫₋, L(Λ))` are of the form `w(Λ + ρ) - ρ` with `ℓ(w) = k`. The
multiplicities then follow from the Euler characteristic and the Weyl–Kac character formula
(`IrreducibleModule.finrank_homologyWeightSpace_eq_one_of_weights`).

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.homologyWeightSpace_ne_bot_iff`:
  `H_k(𝔫₋, L(Λ))_μ ≠ 0 ↔ ∃ w ∈ W, ℓ(w) = k ∧ w(Λ + ρ) - ρ = μ`.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.finrank_homologyWeightSpace_eq_one`:
  `dim H_{ℓ(w)}(𝔫₋, L(Λ))_{w(Λ + ρ) - ρ} = 1`.

## References

* [GL] H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent.
  Math. **34** (1976), 37–76, Thm. 8.6.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, Thm. 3.2.7.
* B. Kostant, *Lie algebra cohomology and the generalized Borel–Weil theorem*, Ann. of Math.
  **74** (1961), 329–387 (finite type).
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Cor. 2.6
  (stated over `ℂ`).
-/

open Module LieModule LieModule.ChevalleyEilenberg

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

namespace IrreducibleModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  (hA : A.IsGeneralizedCartan) (hS : A.IsSymmetrizable) {Λ : Dual K H}
  (hΛ : P.IsDominantIntegral Λ)

include hA in
/-- The Casimir operator acts on `L(Λ)` by `(Λ + 2ρ|Λ)` ([Kac] Cor. 2.6). -/
lemma casimir_eq_smul {S : A.Symmetrization} {B : LinearMap.BilinForm K P.KacMoodyAlgebra}
    (hB : IsStandardForm P S B) (v : IrreducibleModule P Λ) :
    hB.casimir (IrreducibleModule P Λ) (isCategoryO P Λ).isPosFinite v =
      P.dualBilinForm S (Λ + 2 • P.rho) Λ • v :=
  hB.casimir_eq_smul_of_surjective hA _ (LieSubmodule.Quotient.mk' _)
    (LieSubmodule.Quotient.surjective_mk' _) v

include hA hΛ in
/-- **The Casimir step of the Garland–Lepowsky theorem**: every weight of `H_k(𝔫₋, L(Λ))` is of
the form `w(Λ + ρ) - ρ` with `ℓ(w) = k`, for `A` symmetrizable. -/
theorem exists_weylGroup_of_homologyWeightSpace_ne_bot (S : A.Symmetrization) {k : ℕ}
    {μ : Dual K H} (h : (nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace k μ ≠ ⊥) :
    ∃ w : P.weylGroup hA, (P.coxeterSystem hA).length w = k ∧
      (w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho = μ := by
  have hB := isStandardForm_invForm P S
  refine exists_weylGroup_of_homologyWeightSpace_ne_bot_of_eq hA S hΛ h
    ((dualBilinForm_add_rho_add_rho_eq_iff S Λ μ).mpr ?_).symm
  by_contra hne
  exact h (hB.homologyWeightSpace_eq_bot _ hA (isCategoryO P Λ) (casimir_eq_smul hA hB) k
    (Ne.symm hne))

include hA hS hΛ

/-- **The Garland–Lepowsky theorem, dimension part** ([GL] Thm. 8.6; [Kum] Thm. 3.2.7):
`dim H_{ℓ(w)}(𝔫₋, L(Λ))_{w(Λ + ρ) - ρ} = 1` for every `w ∈ W`. -/
theorem finrank_homologyWeightSpace_eq_one (w : P.weylGroup hA) :
    finrank K ((nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace
      ((P.coxeterSystem hA).length w) ((w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho)) = 1 :=
  have S := (isSymmetrizable_iff_nonempty_symmetrization.mp hS).some
  finrank_homologyWeightSpace_eq_one_of_weights hA hS hΛ
    (fun _ _ h ↦ exists_weylGroup_of_homologyWeightSpace_ne_bot hA hΛ S h) w

/-- **The Garland–Lepowsky theorem** ([GL] Thm. 8.6; [Kum] Thm. 3.2.7; Kostant's
theorem in finite type): for `A` symmetrizable and `Λ` dominant integral,
`H_k(𝔫₋, L(Λ))_μ ≠ 0` iff `μ = w(Λ + ρ) - ρ` for some `w ∈ W` with `ℓ(w) = k`; the nonzero
weight spaces are one-dimensional (`finrank_homologyWeightSpace_eq_one`). -/
theorem homologyWeightSpace_ne_bot_iff (k : ℕ) (μ : Dual K H) :
    (nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace k μ ≠ ⊥ ↔
      ∃ w : P.weylGroup hA, (P.coxeterSystem hA).length w = k ∧
        (w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho = μ := by
  refine ⟨exists_weylGroup_of_homologyWeightSpace_ne_bot hA hΛ
    (isSymmetrizable_iff_nonempty_symmetrization.mp hS).some, ?_⟩
  rintro ⟨w, rfl, rfl⟩ hbot
  have h1 := finrank_homologyWeightSpace_eq_one hA hS hΛ w
  rw [hbot, finrank_bot] at h1
  exact zero_ne_one h1

end IrreducibleModule

end Matrix.Realization.KacMoodyAlgebra
