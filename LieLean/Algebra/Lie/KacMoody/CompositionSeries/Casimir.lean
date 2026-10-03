/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CompositionSeries.Multiplicity

/-!
# Irreducible subquotients of highest-weight modules

Let `A` be a symmetrizable generalized Cartan matrix and let `V` be a highest-weight module over
`𝔤(A)` with highest weight `Λ`, i.e. a quotient of the Verma module `M(Λ)`. Using the Casimir
operator we show that if `L(μ)` occurs as a factor of a local composition series of `V`, then
`μ ≤ Λ` and `(Λ + ρ | Λ + ρ) = (μ + ρ | μ + ρ)` ([Kac] §9.8, proof of Prop. 9.8). More generally
this holds for the weight `μ` of any vector of `V` that is primitive modulo a submodule.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.mem_cone_and_eq_of_lie_e_mem`: if `V` is a
  quotient of `M(Λ)`, `N ⊆ V` is a submodule and `w ∈ V_μ \ N` satisfies `eᵢ w ∈ N` for all `i`,
  then `μ ≤ Λ` and `(Λ + 2ρ | Λ) = (μ + 2ρ | μ)`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.mem_cone_and_eq_of_lie_e_eq_zero`: the case
  `N = 0` (primitive vectors of `V`).
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.mem_cone_and_eq_of_mem_factorWeights`,
  `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.mem_cone_and_eq_of_multiplicity_ne_zero`:
  **[Kac] §9.8, proof of Prop. 9.8**.
* `Matrix.Realization.KacMoodyAlgebra.mem_cone_and_eq_of_mem_factorWeights`,
  `Matrix.Realization.KacMoodyAlgebra.mem_cone_and_eq_of_multiplicity_ne_zero`: the same for any
  symmetrizable generalized Cartan matrix, using the invariant form of [Kac] Thm. 2.2.

## Proof

The Casimir operator `Ω` acts on the quotient `V/N` of `M(Λ)` by the scalar `(Λ + 2ρ | Λ)`
([Kac] Cor. 2.6), and on the image of `w`, a nonzero primitive vector of weight `μ`, by
`(μ + 2ρ | μ)`; also `μ ≤ Λ` as `μ` is a weight of `V/N`. A factor `V_j / V_{j-1} ≅ L(μ)` of a
local composition series provides such a `w` with `N = V_{j-1}`: a preimage in `V_j ∩ V_μ` of the
highest-weight vector of `L(μ)`. Finally `(μ + ρ | μ + ρ) = (μ + 2ρ | μ) + (ρ | ρ)`. [Kac] states
Prop. 9.8 as a character identity for highest-weight `V`; the factor statement and the argument
via `Ω` (Lemma 9.8) are those of its proof in [Kac] §9.8, written out by us.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.2, §2.5–2.6,
  §9.6–9.8 (stated over `ℂ`).
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

omit [DecidableEq ι] in
/-- `(μ + ρ | μ + ρ) = (μ + 2ρ | μ) + (ρ | ρ)`. -/
lemma dualBilinForm_add_rho_add_rho [FiniteDimensional K H] (S : A.Symmetrization)
    (μ : Dual K H) :
    P.dualBilinForm S (μ + P.rho) (μ + P.rho) =
      P.dualBilinForm S (μ + 2 • P.rho) μ + P.dualBilinForm S P.rho P.rho := by
  have hsymm := (P.isSymm_dualBilinForm S).eq P.rho μ
  simp only [two_nsmul, map_add, LinearMap.add_apply] at hsymm ⊢
  rw [hsymm]
  ring

omit [DecidableEq ι] in
/-- `(Λ + ρ | Λ + ρ) = (μ + ρ | μ + ρ)` iff `(Λ + 2ρ | Λ) = (μ + 2ρ | μ)`. -/
lemma dualBilinForm_add_rho_add_rho_eq_iff [FiniteDimensional K H] (S : A.Symmetrization)
    (Λ μ : Dual K H) :
    P.dualBilinForm S (Λ + P.rho) (Λ + P.rho) = P.dualBilinForm S (μ + P.rho) (μ + P.rho) ↔
      P.dualBilinForm S (Λ + 2 • P.rho) Λ = P.dualBilinForm S (μ + 2 • P.rho) μ := by
  rw [dualBilinForm_add_rho_add_rho, dualBilinForm_add_rho_add_rho, add_left_inj]

/-- If a subquotient `M₂ / M₁` of a module `V` in `𝒪` is isomorphic to `L(μ)`, then `M₂` contains a
vector `w ∈ V_μ \ M₁` with `eᵢ w ∈ M₁` for all `i` (a preimage of the highest-weight vector). -/
theorem IsCategoryO.exists_lie_e_mem_of_equiv (hV : IsCategoryO P V) {μ : Dual K H}
    {M₁ M₂ : LieSubmodule K P.KacMoodyAlgebra V}
    (ψ : M₁.Subquotient M₂ ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P μ) :
    ∃ w ∈ weightSpace P V μ, w ∈ M₂ ∧ w ∉ M₁ ∧ ∀ i, ⁅e P i, w⁆ ∈ M₁ := by
  set u := ψ.symm (IrreducibleModule.hwv P μ)
  have hu : u ∈ weightSpace P (M₁.Subquotient M₂) μ :=
    map_mem_weightSpaceOfMap P ψ.symm.toLieModuleHom (IrreducibleModule.hwv_mem_weightSpace P μ)
  have hu0 : u ≠ 0 := by simpa [u] using IrreducibleModule.hwv_ne_zero P μ
  have hue (i : ι) : ⁅e P i, u⁆ = 0 := by
    have : ⁅e P i, IrreducibleModule.hwv P μ⁆ = 0 := by
      rw [IrreducibleModule.hwv, ← LieModuleHom.map_lie, VermaModule.lie_e_hwv, map_zero]
    rw [show u = ψ.symm.toLieModuleHom (IrreducibleModule.hwv P μ) from rfl,
      ← LieModuleHom.map_lie, this, map_zero]
  rw [weightSpace, ← map_weightSpaceOfMap_quotient P (M₁.comap M₂.incl)
    (hV.lieSubmodule M₂).iSup_weightSpaceOfMap_eq_top μ] at hu
  obtain ⟨m, hm, hmu⟩ := hu
  refine ⟨m, mem_weightSpaceOfMap_lieSubmodule_iff.mp hm, m.2, fun hm₁ ↦ hu0 ?_, fun i ↦ ?_⟩
  · rw [← hmu]
    exact (LieSubmodule.Quotient.mk_eq_zero _).mpr hm₁
  · have : LieSubmodule.Quotient.mk' (M₁.comap M₂.incl) ⁅e P i, m⁆ = 0 := by
      rw [LieModuleHom.map_lie]
      exact (congrArg _ hmu).trans (hue i)
    rw [LieSubmodule.Quotient.mk_eq_zero] at this
    exact this

variable [FiniteDimensional K H] {S : A.Symmetrization}
  {B : LinearMap.BilinForm K P.KacMoodyAlgebra}

namespace IsStandardForm

variable (hB : IsStandardForm P S B) (hA : A.IsGeneralizedCartan)
include hB hA

/-- Let `V` be a quotient of `M(Λ)` and let `w ∈ V_μ` be a primitive vector modulo a submodule
`N`: `w ∉ N` and `eᵢ w ∈ N` for all `i`. Then `μ ≤ Λ` and `(Λ + 2ρ | Λ) = (μ + 2ρ | μ)`
(via the Casimir operator, [Kac] §9.8). -/
theorem mem_cone_and_eq_of_lie_e_mem {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ)
    (N : LieSubmodule K P.KacMoodyAlgebra V) {μ : Dual K H} {w : V}
    (hw : w ∈ weightSpace P V μ) (hwN : w ∉ N) (he : ∀ i, ⁅e P i, w⁆ ∈ N) :
    μ ∈ cone P Λ ∧
      P.dualBilinForm S (Λ + 2 • P.rho) Λ = P.dualBilinForm S (μ + 2 • P.rho) μ := by
  set π := LieSubmodule.Quotient.mk' N
  have hπ : Function.Surjective (π.comp φ) :=
    (LieSubmodule.Quotient.surjective_mk' N).comp hφ
  have hO : IsCategoryO P (V ⧸ N) := .of_surjective _ hπ
  have hw' : π w ∈ weightSpace P (V ⧸ N) μ := map_mem_weightSpaceOfMap P π hw
  have hw0 : π w ≠ 0 := by rwa [ne_eq, LieSubmodule.Quotient.mk_eq_zero]
  have he' (i : ι) : ⁅e P i, π w⁆ = 0 := by
    rw [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero]
    exact he i
  refine ⟨VermaModule.exists_eq_sub_of_mem_weightSpace P Λ _ hπ hw' hw0, ?_⟩
  exact smul_left_injective K hw0
    ((hB.casimir_eq_smul_of_surjective hA hO.isPosFinite _ hπ (π w)).symm.trans
      (hB.casimir_apply_of_lie_e_eq_zero hO.isPosFinite hw' he'))

/-- If `V` is a quotient of `M(Λ)` and `w ∈ V_μ` is a nonzero primitive vector (`eᵢ w = 0` for all
`i`), then `μ ≤ Λ` and `(Λ + 2ρ | Λ) = (μ + 2ρ | μ)` ([Kac] §9.8). -/
theorem mem_cone_and_eq_of_lie_e_eq_zero {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ) {μ : Dual K H}
    {w : V} (hw : w ∈ weightSpace P V μ) (hw0 : w ≠ 0) (he : ∀ i, ⁅e P i, w⁆ = 0) :
    μ ∈ cone P Λ ∧
      P.dualBilinForm S (Λ + 2 • P.rho) Λ = P.dualBilinForm S (μ + 2 • P.rho) μ :=
  hB.mem_cone_and_eq_of_lie_e_mem hA φ hφ ⊥ hw (by rwa [LieSubmodule.mem_bot])
    fun i ↦ by rw [he i]; exact LieSubmodule.zero_mem _

/-- **[Kac] §9.8, proof of Prop. 9.8**: if `V` is a quotient of `M(Λ)` and `L(μ)` occurs
as a factor of a local composition series of `V` (for any `ν`), then `μ ≤ Λ` and
`(Λ + ρ | Λ + ρ) = (μ + ρ | μ + ρ)`. -/
theorem mem_cone_and_eq_of_mem_factorWeights {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ) {ν : Dual K H}
    {N₁ N₂ : LieSubmodule K P.KacMoodyAlgebra V}
    {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P ν N₁ l N₂) {μ : Dual K H} (hμ : μ ∈ factorWeights l) :
    μ ∈ cone P Λ ∧
      P.dualBilinForm S (Λ + P.rho) (Λ + P.rho) = P.dualBilinForm S (μ + P.rho) (μ + P.rho) := by
  obtain ⟨M₁, M₂, -, -, -, -, ⟨ψ⟩⟩ := hl.exists_of_mem_factorWeights hμ
  obtain ⟨w, hw, -, hw₁, he⟩ := (IsCategoryO.of_surjective φ hφ).exists_lie_e_mem_of_equiv ψ
  rw [dualBilinForm_add_rho_add_rho_eq_iff]
  exact hB.mem_cone_and_eq_of_lie_e_mem hA φ hφ M₁ hw hw₁ he

/-- **[Kac] §9.8, proof of Prop. 9.8**: if `V` is a quotient of `M(Λ)` and `[V : L(μ)] ≠ 0`, then
`μ ≤ Λ` and `(Λ + ρ | Λ + ρ) = (μ + ρ | μ + ρ)`. -/
theorem mem_cone_and_eq_of_multiplicity_ne_zero {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ)
    (hV : IsCategoryO P V) {μ : Dual K H} (hμ : hV.multiplicity μ ≠ 0) :
    μ ∈ cone P Λ ∧
      P.dualBilinForm S (Λ + P.rho) (Λ + P.rho) = P.dualBilinForm S (μ + P.rho) (μ + P.rho) :=
  have hl := (hV.exists_isLocalCompositionSeries μ).choose_spec
  hB.mem_cone_and_eq_of_mem_factorWeights hA φ hφ hl
    ((hV.multiplicity_ne_zero_iff (mem_cone_self μ) hl).mp hμ)

end IsStandardForm

/-! ### Versions for the invariant form `invForm` -/

variable (hA : A.IsGeneralizedCartan)
include hA

/-- **[Kac] §9.8, proof of Prop. 9.8**: let `A` be a symmetrizable generalized Cartan matrix, `S` a
symmetrization of `A`, and `V` a quotient of `M(Λ)`. If `L(μ)` occurs as a factor of a local
composition series of `V`, then `μ ≤ Λ` and `(Λ + ρ | Λ + ρ) = (μ + ρ | μ + ρ)`. -/
theorem mem_cone_and_eq_of_mem_factorWeights (S : A.Symmetrization) {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ) {ν : Dual K H}
    {N₁ N₂ : LieSubmodule K P.KacMoodyAlgebra V}
    {l : List (LieSubmodule K P.KacMoodyAlgebra V × Option (Dual K H))}
    (hl : IsLocalCompositionSeries P ν N₁ l N₂) {μ : Dual K H} (hμ : μ ∈ factorWeights l) :
    μ ∈ cone P Λ ∧
      P.dualBilinForm S (Λ + P.rho) (Λ + P.rho) = P.dualBilinForm S (μ + P.rho) (μ + P.rho) :=
  (isStandardForm_invForm P S).mem_cone_and_eq_of_mem_factorWeights hA φ hφ hl hμ

/-- **[Kac] §9.8, proof of Prop. 9.8**: let `A` be a symmetrizable generalized Cartan matrix, `S` a
symmetrization of `A`, and `V` a quotient of `M(Λ)`. If `[V : L(μ)] ≠ 0`, then `μ ≤ Λ` and
`(Λ + ρ | Λ + ρ) = (μ + ρ | μ + ρ)`. -/
theorem mem_cone_and_eq_of_multiplicity_ne_zero (S : A.Symmetrization) {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ)
    (hV : IsCategoryO P V) {μ : Dual K H} (hμ : hV.multiplicity μ ≠ 0) :
    μ ∈ cone P Λ ∧
      P.dualBilinForm S (Λ + P.rho) (Λ + P.rho) = P.dualBilinForm S (μ + P.rho) (μ + P.rho) :=
  (isStandardForm_invForm P S).mem_cone_and_eq_of_multiplicity_ne_zero hA φ hφ hV hμ

end Matrix.Realization.KacMoodyAlgebra
