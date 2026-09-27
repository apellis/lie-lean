/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.InvariantForm
import Mathlib.LinearAlgebra.Dual.Basis
import LieLean.Algebra.Lie.KacMoody.IntegrableRoots
import LieLean.LinearAlgebra.Matrix.Cartan.Symmetrizable

/-!
# Standard invariant forms on `𝔤(A)` and dual bases of root spaces

Let `A` be a symmetrizable generalized Cartan matrix with a symmetrization `S`, realization
`(𝔥, Π, Π^∨)` over a field `K` of characteristic zero, and let `(·|·)` be the standard form on
`𝔥` ([Kac] §2.1, `Matrix.Realization.bilinForm`). By [Kac] Thm. 2.2 (check) there is a symmetric
invariant bilinear form `(·|·)` on `𝔤(A)` extending it, for which `𝔤_α ⊥ 𝔤_β` unless
`α + β = 0` and which pairs `𝔤_α` and `𝔤_{-α}` nondegenerately. In this file we record exactly
these properties as a hypothesis `KacMoodyAlgebra.IsStandardForm P S B` on a bilinear form `B`,
so that the construction of the generalized Casimir operator (`KacMoody/Casimir.lean`) only depends
on them.

From these properties we derive that `𝔤_μ` and `𝔤_{-μ}` are nondegenerately paired for *every*
`μ ∈ 𝔥*` (for `μ = 0` this is the nondegeneracy of the form on `𝔥`), so that every basis
`{e_μ^{(k)}}` of `𝔤_μ` has a dual basis `{e_{-μ}^{(k)}}` of `𝔤_{-μ}`:
`(e_μ^{(k)} | e_{-μ}^{(l)}) = δₖₗ`. We fix such dual bases (`rootSpaceBasis`,
`IsStandardForm.dualBasis`) and prove the identity of [Kac] Lemma 2.4 (check), which is the heart of
the proof that the Casimir operator commutes with `𝔤(A)`: for `z ∈ 𝔤_γ`,
`∑ₖ [e_{-μ}^{(k)}, z] ⊗ e_μ^{(k)} = ∑ₖ e_{-(μ-γ)}^{(k)} ⊗ [z, e_{μ-γ}^{(k)}]`
(`IsStandardForm.casimirSum_lie_left`, stated after applying an arbitrary bilinear map).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm`: the properties of the invariant form of
  [Kac] Thm. 2.2 (check) used for the Casimir operator.
* `Matrix.Realization.KacMoodyAlgebra.rootSpaceBasis`: a chosen basis of `𝔤_μ`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.dualBasis`: the dual basis of `𝔤_{-μ}`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.casimirSum`: `∑ₖ Φ(e_{-μ}^{(k)}, e_μ^{(k)})`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.lie_eq_smul`: `[x, y] = (x|y) ν⁻¹(α)` for
  `x ∈ 𝔤_α`, `y ∈ 𝔤_{-α}` ([Kac] Thm. 2.2 e) (check)).
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.eq_zero_of_forall`: `𝔤_μ` and `𝔤_{-μ}` are
  nondegenerately paired for every `μ`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.sum_smul_basis`,
  `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.sum_smul_dualBasis`: expansion in dual bases.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.casimirSum_lie_left`: [Kac] Lemma 2.4 (check).
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.casimirSum_eq_of_basis`: the sums do not depend
  on the chosen dual bases.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.1–2.4.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- A bilinear form `B` on `𝔤(A)` is a *standard form* for the symmetrization `S` if it has the
properties of the invariant form of [Kac] Thm. 2.2 (check) that are used to construct the Casimir
operator: it is symmetric and invariant, it restricts to the standard form
`Matrix.Realization.bilinForm` of [Kac] (2.1.2)–(2.1.3) on `𝔥`, `(𝔤_μ | 𝔤_ν) = 0` unless
`μ + ν = 0`, and for `α ∈ Q₊ \ {0}` it pairs `𝔤_α` and `𝔤_{-α}` nondegenerately. -/
structure IsStandardForm (S : A.Symmetrization) (B : LinearMap.BilinForm K P.KacMoodyAlgebra) :
    Prop where
  isSymm : B.IsSymm
  lieInvariant : B.lieInvariant P.KacMoodyAlgebra
  h_h (a b : H) : B (h P a) (h P b) = P.bilinForm S a b
  eq_zero {μ ν : Dual K H} {x y : P.KacMoodyAlgebra} (hx : x ∈ rootSpace P μ)
    (hy : y ∈ rootSpace P ν) (hμν : μ + ν ≠ 0) : B x y = 0
  eq_zero_of_pos {α : Dual K H} (hα : α ∈ P.posWeights) {x : P.KacMoodyAlgebra}
    (hx : x ∈ rootSpace P α) (hx0 : ∀ y ∈ rootSpace P (-α), B x y = 0) : x = 0
  eq_zero_of_neg {α : Dual K H} (hα : α ∈ P.posWeights) {x : P.KacMoodyAlgebra}
    (hx : x ∈ rootSpace P (-α)) (hx0 : ∀ y ∈ rootSpace P α, B x y = 0) : x = 0

variable [CharZero K] [FiniteDimensional K H]

/-- All root spaces `𝔤_μ` are finite-dimensional ([Kac] §1.3). -/
instance finiteDimensional_rootSpace_all (μ : Dual K H) :
    FiniteDimensional K (rootSpace P μ) := by
  by_cases hμ : rootSpace P μ = ⊥
  · rw [hμ]; infer_instance
  rcases mem_allWeights_of_rootSpace_ne_bot P hμ with (hneg | h0) | hpos
  · obtain ⟨k, hk, rfl⟩ := hneg
    exact finiteDimensional_rootSpace_neg P ⟨k, hk, rfl⟩
  · rw [Set.mem_singleton_iff.mp h0, rootSpace_zero]; infer_instance
  · exact finiteDimensional_rootSpace P hpos

/-- The chosen basis `{e_μ^{(k)}}` of the root space `𝔤_μ`. -/
def rootSpaceBasis (μ : Dual K H) : Basis (Fin (finrank K (rootSpace P μ))) K (rootSpace P μ) :=
  Module.finBasis K _

lemma rootSpaceBasis_mem (μ : Dual K H) (k : Fin (finrank K (rootSpace P μ))) :
    (rootSpaceBasis P μ k : P.KacMoodyAlgebra) ∈ rootSpace P μ :=
  (rootSpaceBasis P μ k).2

namespace IsStandardForm

variable {P} {S : A.Symmetrization} {B : LinearMap.BilinForm K P.KacMoodyAlgebra}
  (hB : IsStandardForm P S B)
include hB

omit [CharZero K] [FiniteDimensional K H] in
lemma symm (x y : P.KacMoodyAlgebra) : B x y = B y x := hB.isSymm.eq x y

omit [CharZero K] [FiniteDimensional K H] in
/-- Invariance in the form `([x, y] | z) = (x | [y, z])`. -/
lemma lie_left (x y z : P.KacMoodyAlgebra) : B ⁅x, y⁆ z = B x ⁅y, z⁆ := by
  rw [← lie_skew, map_neg, LinearMap.neg_apply, hB.lieInvariant y x z, neg_neg]

/-- For every `μ ∈ 𝔥*`, an element of `𝔤_μ` orthogonal to `𝔤_{-μ}` is zero: `𝔤_μ` and `𝔤_{-μ}`
are nondegenerately paired ([Kac] Thm. 2.2 (check)). -/
theorem eq_zero_of_forall {μ : Dual K H} {x : P.KacMoodyAlgebra} (hx : x ∈ rootSpace P μ)
    (hx0 : ∀ y ∈ rootSpace P (-μ), B x y = 0) : x = 0 := by
  by_cases hμ : rootSpace P μ = ⊥
  · rw [hμ] at hx; exact (Submodule.mem_bot K).mp hx
  rcases mem_allWeights_of_rootSpace_ne_bot P hμ with (hneg | h0) | hpos
  · obtain ⟨k, hk, rfl⟩ := hneg
    exact hB.eq_zero_of_neg ⟨k, hk, rfl⟩ hx (by simpa using hx0)
  · rw [Set.mem_singleton_iff] at h0
    subst h0
    rw [rootSpace_zero] at hx
    obtain ⟨a, rfl⟩ := hx
    have ha : a = 0 := (P.nondegenerate_bilinForm S).1 a fun b ↦ by
      rw [← hB.h_h]
      exact hx0 _ (by rw [neg_zero, rootSpace_zero]; exact ⟨b, rfl⟩)
    rw [ha, map_zero]
  · exact hB.eq_zero_of_pos hpos hx hx0

/-- [Kac] Thm. 2.2 e) (check): `[x, y] = (x|y) ν⁻¹(μ)` for `x ∈ 𝔤_μ` and `y ∈ 𝔤_{-μ}`. -/
theorem lie_eq_smul {μ : Dual K H} {x y : P.KacMoodyAlgebra} (hx : x ∈ rootSpace P μ)
    (hy : y ∈ rootSpace P (-μ)) : ⁅x, y⁆ = B x y • h P ((P.toDual S).symm μ) := by
  have hxy : ⁅x, y⁆ ∈ rootSpace P 0 := by
    have := lie_mem_weightSpaceOfMap (h P) hx hy
    rwa [add_neg_cancel] at this
  rw [rootSpace_zero] at hxy
  obtain ⟨c, hc⟩ := hxy
  rw [← hc, ← map_smul]
  congr 1
  apply (P.toDual S).injective
  rw [map_smul, LinearEquiv.apply_symm_apply]
  ext a
  rw [toDual_apply, ← hB.h_h, hc, hB.lie_left, ← lie_skew, hy a]
  simp only [map_neg, map_smul, LinearMap.neg_apply, smul_eq_mul, LinearMap.smul_apply]
  ring

/-! ### Dual bases of `𝔤_μ` and `𝔤_{-μ}` -/

omit hB in
omit [CharZero K] [FiniteDimensional K H] in
variable (B) in
/-- The pairing `𝔤_{-μ} → (𝔤_μ)*`, `y ↦ (x ↦ (x|y))`. -/
def pairing (μ : Dual K H) : rootSpace P (-μ) →ₗ[K] Dual K (rootSpace P μ) :=
  (B.domRestrict₁₂ (rootSpace P μ) (rootSpace P (-μ))).flip

omit hB in
omit [CharZero K] [FiniteDimensional K H] in
@[simp] lemma pairing_apply (μ : Dual K H) (y : rootSpace P (-μ)) (x : rootSpace P μ) :
    pairing B μ y x = B x y := rfl

lemma pairing_injective (μ : Dual K H) : Function.Injective (pairing B μ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  refine Submodule.coe_eq_zero.mp (hB.eq_zero_of_forall (μ := -μ) y.2 fun x hx ↦ ?_)
  rw [hB.symm]
  have := LinearMap.congr_fun hy ⟨x, by rwa [neg_neg] at hx⟩
  simpa using this

lemma finrank_rootSpace_le (μ : Dual K H) :
    finrank K (rootSpace P μ) ≤ finrank K (rootSpace P (-μ)) := by
  have := LinearMap.finrank_le_finrank_of_injective (hB.pairing_injective (-μ))
  rwa [Subspace.dual_finrank_eq, neg_neg] at this

/-- `dim 𝔤_{-μ} = dim 𝔤_μ`. -/
theorem finrank_rootSpace_neg (μ : Dual K H) :
    finrank K (rootSpace P (-μ)) = finrank K (rootSpace P μ) :=
  le_antisymm (by have := hB.finrank_rootSpace_le (-μ); rwa [neg_neg] at this)
    (hB.finrank_rootSpace_le μ)

/-- The isomorphism `𝔤_{-μ} ≃ (𝔤_μ)*` induced by the form. -/
def pairingEquiv (μ : Dual K H) : rootSpace P (-μ) ≃ₗ[K] Dual K (rootSpace P μ) :=
  LinearMap.linearEquivOfInjective _ (hB.pairing_injective μ)
    (by rw [Subspace.dual_finrank_eq, hB.finrank_rootSpace_neg])

/-- The basis `{e_{-μ}^{(k)}}` of `𝔤_{-μ}` dual to `rootSpaceBasis P μ` for the form:
`(e_μ^{(k)} | e_{-μ}^{(l)}) = δₖₗ`. -/
def dualBasis (μ : Dual K H) (k : Fin (finrank K (rootSpace P μ))) : P.KacMoodyAlgebra :=
  ((hB.pairingEquiv μ).symm ((rootSpaceBasis P μ).coord k) : rootSpace P (-μ))

lemma dualBasis_mem (μ : Dual K H) (k : Fin (finrank K (rootSpace P μ))) :
    hB.dualBasis μ k ∈ rootSpace P (-μ) :=
  Subtype.property _

lemma apply_dualBasis (μ : Dual K H) (x : rootSpace P μ) (k : Fin (finrank K (rootSpace P μ))) :
    B x (hB.dualBasis μ k) = (rootSpaceBasis P μ).coord k x :=
  LinearMap.congr_fun ((hB.pairingEquiv μ).apply_symm_apply ((rootSpaceBasis P μ).coord k)) x

lemma basis_dualBasis (μ : Dual K H) (j k : Fin (finrank K (rootSpace P μ))) :
    B (rootSpaceBasis P μ j) (hB.dualBasis μ k) = if j = k then 1 else 0 := by
  rw [apply_dualBasis, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

/-- Expansion in the basis `{e_μ^{(k)}}`: `x = ∑ₖ (x | e_{-μ}^{(k)}) e_μ^{(k)}` for `x ∈ 𝔤_μ`. -/
theorem sum_smul_basis (μ : Dual K H) {x : P.KacMoodyAlgebra} (hx : x ∈ rootSpace P μ) :
    ∑ k, B x (hB.dualBasis μ k) • (rootSpaceBasis P μ k : P.KacMoodyAlgebra) = x := by
  have := congrArg Subtype.val ((rootSpaceBasis P μ).sum_repr ⟨x, hx⟩)
  rw [Submodule.coe_sum] at this
  change _ = x at this
  conv_rhs => rw [← this]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Submodule.coe_smul, ← Basis.coord_apply, ← hB.apply_dualBasis]

/-- Expansion in the dual basis: `y = ∑ₖ (e_μ^{(k)} | y) e_{-μ}^{(k)}` for `y ∈ 𝔤_{-μ}`. -/
theorem sum_smul_dualBasis (μ : Dual K H) {y : P.KacMoodyAlgebra} (hy : y ∈ rootSpace P (-μ)) :
    ∑ k, B (rootSpaceBasis P μ k) y • hB.dualBasis μ k = y := by
  have h1 : ∑ k, B (rootSpaceBasis P μ k) y • (hB.pairingEquiv μ).symm
      ((rootSpaceBasis P μ).coord k) = (⟨y, hy⟩ : rootSpace P (-μ)) := by
    apply (hB.pairingEquiv μ).injective
    rw [map_sum]
    simp_rw [map_smul, LinearEquiv.apply_symm_apply]
    exact (rootSpaceBasis P μ).sum_dual_apply_smul_coord (pairing B μ ⟨y, hy⟩)
  have := congrArg Subtype.val h1
  rwa [Submodule.coe_sum] at this

/-! ### Sums over dual bases -/

/-- The sum `∑ₖ Φ(e_{-μ}^{(k)}, e_μ^{(k)})` over the dual bases of `𝔤_{-μ}` and `𝔤_μ`. For a
bilinear `Φ` it does not depend on the choice of dual bases (`casimirSum_eq_of_basis`). -/
def casimirSum {M : Type*} [AddCommMonoid M] (Φ : P.KacMoodyAlgebra → P.KacMoodyAlgebra → M)
    (μ : Dual K H) : M :=
  ∑ k, Φ (hB.dualBasis μ k) (rootSpaceBasis P μ k)

lemma casimirSum_def {M : Type*} [AddCommMonoid M]
    (Φ : P.KacMoodyAlgebra → P.KacMoodyAlgebra → M) (μ : Dual K H) :
    hB.casimirSum Φ μ = ∑ k, Φ (hB.dualBasis μ k) (rootSpaceBasis P μ k) := rfl

/-- The sum vanishes if `𝔤_μ = 0` and `Φ(y, 0) = 0` for all `y`. -/
lemma casimirSum_eq_zero_of_eq_bot {M : Type*} [AddCommMonoid M]
    {Φ : P.KacMoodyAlgebra → P.KacMoodyAlgebra → M} (hΦ : ∀ y, Φ y 0 = 0) {μ : Dual K H}
    (hμ : rootSpace P μ = ⊥) : hB.casimirSum Φ μ = 0 := by
  have h0 : ∀ x ∈ rootSpace P μ, x = 0 := by rw [hμ]; simp
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [h0 _ (rootSpaceBasis_mem P μ k), hΦ]

/-- If the sum is nonzero, some summand is nonzero. -/
lemma exists_ne_zero_of_casimirSum_ne_zero {M : Type*} [AddCommMonoid M]
    {Φ : P.KacMoodyAlgebra → P.KacMoodyAlgebra → M} {μ : Dual K H}
    (hΦ : hB.casimirSum Φ μ ≠ 0) :
    ∃ y ∈ rootSpace P (-μ), ∃ x ∈ rootSpace P μ, Φ y x ≠ 0 := by
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hΦ
  exact ⟨_, hB.dualBasis_mem μ k, _, rootSpaceBasis_mem P μ k, hk⟩

/-- [Kac] Lemma 2.4 (check): for `z ∈ 𝔤_γ`,
`∑ₖ [e_{-μ}^{(k)}, z] ⊗ e_μ^{(k)} = ∑ₖ e_{-(μ-γ)}^{(k)} ⊗ [z, e_{μ-γ}^{(k)}]`, stated after applying
an arbitrary bilinear map `Ψ`. Both sides are computed by expanding in dual bases; the coefficients
agree by invariance and symmetry of the form. -/
theorem casimirSum_lie_left {M : Type*} [AddCommGroup M] [Module K M]
    (Ψ : P.KacMoodyAlgebra →ₗ[K] P.KacMoodyAlgebra →ₗ[K] M) {γ : Dual K H}
    {z : P.KacMoodyAlgebra} (hz : z ∈ rootSpace P γ) (μ : Dual K H) :
    hB.casimirSum (fun y x ↦ Ψ ⁅y, z⁆ x) μ = hB.casimirSum (fun y x ↦ Ψ y ⁅z, x⁆) (μ - γ) := by
  set b := rootSpaceBasis P μ
  set b' := rootSpaceBasis P (μ - γ)
  have h1 (k) : ⁅hB.dualBasis μ k, z⁆ ∈ rootSpace P (-(μ - γ)) := by
    have := lie_mem_weightSpaceOfMap (h P) (hB.dualBasis_mem μ k) hz
    rwa [show -μ + γ = -(μ - γ) by abel] at this
  have h2 (l) : ⁅z, (b' l : P.KacMoodyAlgebra)⁆ ∈ rootSpace P μ := by
    have := lie_mem_weightSpaceOfMap (h P) hz (rootSpaceBasis_mem P (μ - γ) l)
    rwa [show γ + (μ - γ) = μ by abel] at this
  have hc (k l) : B (b' l) ⁅hB.dualBasis μ k, z⁆ = B ⁅z, b' l⁆ (hB.dualBasis μ k) := by
    rw [hB.lie_left, ← hB.lie_left, hB.symm]
  simp only [casimirSum_def]
  calc ∑ k, Ψ ⁅hB.dualBasis μ k, z⁆ (b k)
      = ∑ k, Ψ (∑ l, B (b' l) ⁅hB.dualBasis μ k, z⁆ • hB.dualBasis (μ - γ) l) (b k) :=
        Finset.sum_congr rfl fun k _ ↦ by rw [hB.sum_smul_dualBasis (μ - γ) (h1 k)]
    _ = ∑ k, ∑ l, B ⁅z, b' l⁆ (hB.dualBasis μ k) • Ψ (hB.dualBasis (μ - γ) l) (b k) := by
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hc]
    _ = ∑ l, ∑ k, B ⁅z, b' l⁆ (hB.dualBasis μ k) • Ψ (hB.dualBasis (μ - γ) l) (b k) :=
        Finset.sum_comm
    _ = ∑ l, Ψ (hB.dualBasis (μ - γ) l)
          (∑ k, B ⁅z, b' l⁆ (hB.dualBasis μ k) • (b k : P.KacMoodyAlgebra)) := by
        simp only [map_sum, map_smul]
    _ = ∑ l, Ψ (hB.dualBasis (μ - γ) l) ⁅z, b' l⁆ :=
        Finset.sum_congr rfl fun l _ ↦ by rw [hB.sum_smul_basis μ (h2 l)]

/-- The sums `∑ₖ Φ(e_{-μ}^{(k)}, e_μ^{(k)})` do not depend on the choice of dual bases: for any
basis `c` of `𝔤_μ` and any family `c'` in `𝔤_{-μ}` with `(cⱼ | c'ₖ) = δⱼₖ`, the sum over `c, c'`
agrees with `casimirSum`. -/
theorem casimirSum_eq_of_basis {M : Type*} [AddCommGroup M] [Module K M]
    (Ψ : P.KacMoodyAlgebra →ₗ[K] P.KacMoodyAlgebra →ₗ[K] M) {μ : Dual K H} {κ : Type*}
    [Fintype κ] [DecidableEq κ] (c : Basis κ K (rootSpace P μ)) (c' : κ → P.KacMoodyAlgebra)
    (hc' : ∀ k, c' k ∈ rootSpace P (-μ)) (hcc' : ∀ j k, B (c j) (c' k) = if j = k then 1 else 0) :
    ∑ k, Ψ (c' k) (c k) = hB.casimirSum (fun y x ↦ Ψ y x) μ := by
  -- expansion of `x ∈ 𝔤_μ` in the basis `c`
  have hx {x : P.KacMoodyAlgebra} (hx : x ∈ rootSpace P μ) :
      ∑ k, B x (c' k) • (c k : P.KacMoodyAlgebra) = x := by
    have hrepr := congrArg Subtype.val (c.sum_repr ⟨x, hx⟩)
    rw [Submodule.coe_sum] at hrepr
    change _ = x at hrepr
    have hcoef (k : κ) : B x (c' k) = c.repr ⟨x, hx⟩ k := by
      conv_lhs => rw [← hrepr]
      simp only [Submodule.coe_smul, map_sum, map_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, hcc', smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact (Finset.sum_congr rfl fun k _ ↦ by rw [hcoef k, Submodule.coe_smul]).trans hrepr
  -- expansion of `y ∈ 𝔤_{-μ}` in the family `c'`
  have hy {y : P.KacMoodyAlgebra} (hy : y ∈ rootSpace P (-μ)) :
      ∑ k, B (c k) y • c' k = y := by
    have hmem : ∑ k, B (c k) y • c' k ∈ rootSpace P (-μ) :=
      Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (hc' k)
    have := hB.pairing_injective μ (a₁ := ⟨_, hmem⟩) (a₂ := ⟨y, hy⟩) (c.ext fun j ↦ ?_)
    · exact congrArg Subtype.val this
    simp only [pairing_apply, map_sum, map_smul, hcc', smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [casimirSum_def]
  calc ∑ k, Ψ (c' k) (c k)
      = ∑ k, Ψ (c' k)
          (∑ l, B (c k) (hB.dualBasis μ l) • (rootSpaceBasis P μ l : P.KacMoodyAlgebra)) :=
        Finset.sum_congr rfl fun k _ ↦ by rw [hB.sum_smul_basis μ (c k).2]
    _ = ∑ l, Ψ (∑ k, B (c k) (hB.dualBasis μ l) • c' k) (rootSpaceBasis P μ l) := by
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
        exact Finset.sum_comm
    _ = ∑ l, Ψ (hB.dualBasis μ l) (rootSpaceBasis P μ l) :=
        Finset.sum_congr rfl fun l _ ↦ by rw [hy (hB.dualBasis_mem μ l)]

end IsStandardForm

end Matrix.Realization.KacMoodyAlgebra
