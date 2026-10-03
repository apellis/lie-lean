/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Basic
import LieLean.Algebra.Lie.KacMoody.InvariantFormAux

/-!
# The invariant bilinear form on a symmetrizable Kac–Moody algebra

Let `A` be a symmetrizable matrix with a symmetrization `A = diag(ε) B`, and `(𝔥, Π, Π^∨)` a
realization of `A` over a field `K` of characteristic zero. The Kac–Moody algebra
`𝔤(A) = 𝔤̃(A)/𝔯` carries a nondegenerate symmetric invariant bilinear form extending the form
`Matrix.Realization.bilinForm` on `𝔥` ([Kac] Thm. 2.2). It is induced by the invariant
form `Matrix.Realization.AuxLieAlgebra.invFormAux` on `𝔤̃(A)`, whose radical is `𝔯`; see
`LieLean/Algebra/Lie/KacMoody/InvariantFormAux.lean` for the construction and the proofs.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.invForm`: the invariant form `(·|·)` on `𝔤(A)`.
* `Matrix.Realization.KacMoodyAlgebra.rootSpacePairingEquiv`: the induced isomorphism
  `𝔤_{-α} ≃ (𝔤_α)*`.

## Main results

[Kac] Thm. 2.2:
* `Matrix.Realization.KacMoodyAlgebra.isSymm_invForm`,
  `Matrix.Realization.KacMoodyAlgebra.nondegenerate_invForm`: the form is symmetric and
  nondegenerate.
* `Matrix.Realization.KacMoodyAlgebra.lieInvariant_invForm`,
  `Matrix.Realization.KacMoodyAlgebra.invForm_lie`: a) the form is invariant.
* `Matrix.Realization.KacMoodyAlgebra.invForm_h_h`: b) it restricts to the form of [Kac] §2.1
  on `𝔥`.
* `Matrix.Realization.KacMoodyAlgebra.invForm_eq_zero`: c) `(𝔤_α | 𝔤_β) = 0` unless
  `α + β = 0`.
* `Matrix.Realization.KacMoodyAlgebra.eq_zero_of_invForm_rootSpace_eq_zero`,
  `Matrix.Realization.KacMoodyAlgebra.rootSpacePairingEquiv`: d) the form pairs `𝔤_α` and
  `𝔤_{-α}` nondegenerately, identifying `𝔤_{-α}` with the dual of `𝔤_α`.
* `Matrix.Realization.KacMoodyAlgebra.lie_eq_invForm_smul`: e) `[x, y] = (x | y) ν⁻¹(α)` for
  `x ∈ 𝔤_α`, `y ∈ 𝔤_{-α}`.
* `Matrix.Realization.KacMoodyAlgebra.invForm_e_f`: `(eᵢ | fⱼ) = δᵢⱼ εᵢ`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.2 (stated over `ℂ`).
-/

open Module LieModule LieAlgebra

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (S : A.Symmetrization)

namespace KacMoodyAlgebra

open AuxLieAlgebra in
lemma maxIdeal_le_ker_flip :
    (maxIdeal P).toSubmodule ≤ LinearMap.ker (invFormAux P S).flip := by
  intro r hr
  rw [LinearMap.mem_ker]
  ext x
  change invFormAux P S x r = 0
  rw [(isSymm_invFormAux P S).eq]
  exact invFormAux_eq_zero_of_mem_maxIdeal P S hr x

open AuxLieAlgebra in
lemma maxIdeal_le_ker_liftQ_flip :
    (maxIdeal P).toSubmodule ≤ LinearMap.ker
      ((maxIdeal P).toSubmodule.liftQ (invFormAux P S).flip (maxIdeal_le_ker_flip P S)).flip := by
  intro r hr
  rw [LinearMap.mem_ker]
  ext y
  exact invFormAux_eq_zero_of_mem_maxIdeal P S hr y

/-- The nondegenerate symmetric invariant bilinear form on `𝔤(A)` ([Kac] Thm. 2.2),
induced by `Matrix.Realization.AuxLieAlgebra.invFormAux`. -/
def invForm : LinearMap.BilinForm K P.KacMoodyAlgebra :=
  (AuxLieAlgebra.maxIdeal P).toSubmodule.liftQ _ (maxIdeal_le_ker_liftQ_flip P S)

@[simp] lemma invForm_π (x y : P.AuxLieAlgebra) :
    invForm P S (π P x) (π P y) = AuxLieAlgebra.invFormAux P S x y := rfl

/-- The form on `𝔤(A)` is symmetric. -/
theorem isSymm_invForm : (invForm P S).IsSymm := by
  refine LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ ?_
  obtain ⟨x, rfl⟩ := π_surjective P x
  obtain ⟨y, rfl⟩ := π_surjective P y
  simp only [invForm_π]
  exact (AuxLieAlgebra.isSymm_invFormAux P S).eq x y

/-- The form on `𝔤(A)` is invariant: `([x, y] | z) = (x | [y, z])`
([Kac] Thm. 2.2 a)). -/
theorem invForm_lie (x y z : P.KacMoodyAlgebra) :
    invForm P S ⁅x, y⁆ z = invForm P S x ⁅y, z⁆ := by
  obtain ⟨x, rfl⟩ := π_surjective P x
  obtain ⟨y, rfl⟩ := π_surjective P y
  obtain ⟨z, rfl⟩ := π_surjective P z
  rw [← LieHom.map_lie, ← LieHom.map_lie, invForm_π, invForm_π, AuxLieAlgebra.invFormAux_lie]

/-- The form on `𝔤(A)` is invariant, in the sense of `LinearMap.BilinForm.lieInvariant`. -/
theorem lieInvariant_invForm : (invForm P S).lieInvariant P.KacMoodyAlgebra := by
  intro x y z
  rw [← lie_skew, map_neg, LinearMap.neg_apply, invForm_lie]

/-- The form on `𝔤(A)` is nondegenerate ([Kac] Thm. 2.2). -/
theorem nondegenerate_invForm : (invForm P S).Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (isSymm_invForm P S).isRefl).mpr fun x hx ↦ ?_
  obtain ⟨x, rfl⟩ := π_surjective P x
  rw [π_eq_zero_iff]
  refine (AuxLieAlgebra.invFormAux_eq_zero_iff_mem_maxIdeal P S).mp fun y ↦ ?_
  rw [← invForm_π]
  exact hx _

/-- The form on `𝔤(A)` restricts to the form `Matrix.Realization.bilinForm` on `𝔥`
([Kac] Thm. 2.2 b)). -/
@[simp] theorem invForm_h_h (a b : H) : invForm P S (h P a) (h P b) = P.bilinForm S a b := by
  rw [← π_h, ← π_h, invForm_π, AuxLieAlgebra.invFormAux_h_h]

/-- `(𝔤_α | 𝔤_β) = 0` unless `α + β = 0` ([Kac] Thm. 2.2 c)). -/
theorem invForm_eq_zero {μ ν : Dual K H} {x y : P.KacMoodyAlgebra} (hx : x ∈ rootSpace P μ)
    (hy : y ∈ rootSpace P ν) (hμν : μ + ν ≠ 0) : invForm P S x y = 0 := by
  rw [rootSpace_eq_map] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  exact AuxLieAlgebra.invFormAux_eq_zero P S hx hy hμν

/-- `[x, y] = (x | y) ν⁻¹(α)` for `x ∈ 𝔤_α` and `y ∈ 𝔤_{-α}` ([Kac] Thm. 2.2 e)). -/
theorem lie_eq_invForm_smul {μ : Dual K H} {x y : P.KacMoodyAlgebra} (hx : x ∈ rootSpace P μ)
    (hy : y ∈ rootSpace P (-μ)) : ⁅x, y⁆ = invForm P S x y • h P ((P.toDual S).symm μ) := by
  rw [rootSpace_eq_map] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  change ⁅π P x, π P y⁆ = invForm P S (π P x) (π P y) • h P _
  rw [← LieHom.map_lie, AuxLieAlgebra.lie_eq_invFormAux_smul P S μ x hx y hy, map_smul, π_h,
    invForm_π]

/-- `(eᵢ | fⱼ) = δᵢⱼ εᵢ` ([Kac] §2.2). -/
theorem invForm_e_f (i j : ι) :
    invForm P S (e P i) (f P j) = if i = j then (S.ε i : K) else 0 := by
  rw [← π_e, ← π_f, invForm_π, AuxLieAlgebra.invFormAux_e_f]

/-- The form pairs `𝔤_α` and `𝔤_{-α}` nondegenerately: if `x ∈ 𝔤_α` is orthogonal to `𝔤_{-α}`
then `x = 0` ([Kac] Thm. 2.2 d)). -/
theorem eq_zero_of_invForm_rootSpace_eq_zero {μ : Dual K H} {x : P.KacMoodyAlgebra}
    (hx : x ∈ rootSpace P μ) (hx0 : ∀ y ∈ rootSpace P (-μ), invForm P S x y = 0) : x = 0 := by
  refine (nondegenerate_invForm P S).1 x fun y ↦ ?_
  have hy : y ∈ ⨆ ν, rootSpace P ν := by
    have : y ∈ ⨆ ν ∈ AuxLieAlgebra.allWeights P, rootSpace P ν := by
      rw [iSup_rootSpace_eq_top]; trivial
    exact (iSup₂_le fun ν _ ↦ le_iSup (fun ν ↦ rootSpace P ν) ν) this
  refine Submodule.iSup_induction _ (motive := fun y ↦ invForm P S x y = 0) hy (fun ν y hy ↦ ?_)
    (by simp) fun y₁ y₂ h₁ h₂ ↦ by rw [map_add, h₁, h₂, add_zero]
  by_cases hμν : μ + ν = 0
  · obtain rfl : ν = -μ := eq_neg_of_add_eq_zero_right hμν
    exact hx0 y hy
  · exact invForm_eq_zero P S hx hy hμν

/-- The pairing `𝔤_{-α} → (𝔤_α)*` induced by the invariant form. -/
def rootSpacePairing (μ : Dual K H) : rootSpace P (-μ) →ₗ[K] Dual K (rootSpace P μ) :=
  ((invForm P S).domRestrict₁₂ (rootSpace P μ) (rootSpace P (-μ))).flip

@[simp] lemma rootSpacePairing_apply (μ : Dual K H) (y : rootSpace P (-μ)) (x : rootSpace P μ) :
    rootSpacePairing P S μ y x = invForm P S x y := rfl

lemma rootSpacePairing_injective (μ : Dual K H) : Function.Injective (rootSpacePairing P S μ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  ext
  refine eq_zero_of_invForm_rootSpace_eq_zero P S y.2 fun x hx ↦ ?_
  rw [neg_neg] at hx
  rw [(isSymm_invForm P S).eq]
  exact LinearMap.congr_fun hy ⟨x, hx⟩

omit [FiniteDimensional K H] in
lemma chevalleyInvolution_mem_rootSpace {μ : Dual K H} {x : P.KacMoodyAlgebra}
    (hx : x ∈ rootSpace P μ) : chevalleyInvolution P x ∈ rootSpace P (-μ) := by
  intro a
  have := congr_arg (chevalleyInvolution P) (hx (-a))
  simp only [LieHom.map_lie, map_neg, chevalleyInvolution_h, neg_neg, map_smul] at this
  rw [this, LinearMap.neg_apply, neg_smul]

omit [FiniteDimensional K H] in
/-- `dim 𝔤_{-α} = dim 𝔤_α`, via the Chevalley involution. -/
theorem finrank_rootSpace_neg_eq {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    finrank K (rootSpace P (-μ)) = finrank K (rootSpace P μ) := by
  have hfin := finiteDimensional_rootSpace P hμ
  have := finiteDimensional_rootSpace_neg P hμ
  have : FiniteDimensional K (rootSpace P (-(-μ))) := by rwa [neg_neg]
  have hinj : ∀ ν : Dual K H, Function.Injective ((chevalleyInvolution P).toLinearMap.restrict
      (p := rootSpace P ν) (q := rootSpace P (-ν))
      fun _ hx ↦ chevalleyInvolution_mem_rootSpace P hx) := fun ν x y hxy ↦ by
    ext
    simpa using congr_arg (fun z : rootSpace P (-ν) ↦ chevalleyInvolution P z) hxy
  have h1 := LinearMap.finrank_le_finrank_of_injective (hinj μ)
  have h2 := LinearMap.finrank_le_finrank_of_injective (hinj (-μ))
  rw [neg_neg] at h2
  omega

/-- The invariant form identifies `𝔤_{-α}` with the dual of `𝔤_α` for `α ∈ Q₊ \ {0}`
([Kac] Thm. 2.2 d)). -/
def rootSpacePairingEquiv {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    rootSpace P (-μ) ≃ₗ[K] Dual K (rootSpace P μ) :=
  have := finiteDimensional_rootSpace P hμ
  have := finiteDimensional_rootSpace_neg P hμ
  LinearMap.linearEquivOfInjective (rootSpacePairing P S μ) (rootSpacePairing_injective P S μ)
    (by rw [Subspace.dual_finrank_eq, finrank_rootSpace_neg_eq P hμ])

@[simp] lemma rootSpacePairingEquiv_apply {μ : Dual K H} (hμ : μ ∈ P.posWeights)
    (y : rootSpace P (-μ)) (x : rootSpace P μ) :
    rootSpacePairingEquiv P S hμ y x = invForm P S x y := rfl

end KacMoodyAlgebra

end Matrix.Realization

end
