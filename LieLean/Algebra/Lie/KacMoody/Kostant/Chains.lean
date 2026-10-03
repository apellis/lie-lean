/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.Weights
import LieLean.Algebra.Lie.KacMoody.CharacterDenominator

/-!
# The weight decomposition of the `𝔫₋`-homology complex

Let `𝔤 = 𝔤(A)` be a Kac–Moody algebra with Cartan subalgebra `𝔥` and `𝔫₋ ⊆ 𝔤` its negative
nilpotent subalgebra, and let `V` be a `𝔤`-module. We study the Chevalley–Eilenberg complex
`C_•(𝔫₋, V) = ⋀^•𝔫₋ ⊗ V` computing the homology `H_•(𝔫₋, V)`. Since `[𝔥, 𝔫₋] ⊆ 𝔫₋`, each `a ∈ 𝔥`
acts on the complex by the derivation `θ(a)` extending `ad a` on `⋀𝔫₋` and the action of `a` on
`V`, and these operators commute with the differential ([GL] Prop. 1.4, [Kum] §3.1).
We package this as a `LieModule.ChevalleyEilenberg.DerivAction` and deduce, from the general
results of `LieLean.Algebra.Lie.Homology.Weights`, that when `V` is the sum of its weight spaces
(e.g. `V` in the category `𝒪`) the complex, its cycles, boundaries and homology decompose into
`𝔥`-weight spaces.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.adNNeg`: `ad a` on `𝔫₋`, for `a ∈ 𝔥`.
* `Matrix.Realization.KacMoodyAlgebra.nNegDerivAction`: the action of `𝔥` on `𝔫₋` and on `V`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.iSup_weightSpaceOf_adNNeg`: `𝔫₋` is the sum of its
  `𝔥`-weight spaces (the root spaces `𝔤_{-α}`).
* `Matrix.Realization.KacMoodyAlgebra.iSup_nNegChainWeightSpace`,
  `Matrix.Realization.KacMoodyAlgebra.iSup_nNegHomologyWeightSpace`: if `V` is the sum of its
  weight spaces, then so are `⋀𝔫₋ ⊗ V` and `H_k(𝔫₋, V)`.

## References

* [GL] H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent.
  Math. **34** (1976), 37–76.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, Ch. 3.
-/

open Module LieModule LieModule.ChevalleyEilenberg

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)
  (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-- `ad a` restricted to `𝔫₋`, for `a ∈ 𝔥`, as a linear map in `a`. -/
def adNNeg : H →ₗ[K] Module.End K (nNeg P) where
  toFun a :=
    { toFun x := ⟨⁅h P a, (x : P.KacMoodyAlgebra)⁆, lie_h_mem_nNeg P a x.2⟩
      map_add' _ _ := Subtype.ext (lie_add _ _ _)
      map_smul' _ _ := Subtype.ext (lie_smul _ _ _) }
  map_add' a b := LinearMap.ext fun x ↦ Subtype.ext (by simp [add_lie])
  map_smul' c a := LinearMap.ext fun x ↦ Subtype.ext (by simp [smul_lie])

@[simp] lemma coe_adNNeg_apply (a : H) (x : nNeg P) :
    (adNNeg P a x : P.KacMoodyAlgebra) = ⁅h P a, (x : P.KacMoodyAlgebra)⁆ := rfl

/-- The action of `𝔥` on `𝔫₋` (by `ad`) and on a `𝔤`-module `V`, compatible with the action of
`𝔫₋` on `V`. -/
def nNegDerivAction : DerivAction K H (nNeg P) V where
  D := adNNeg P
  φ := (toEnd K P.KacMoodyAlgebra V : P.KacMoodyAlgebra →ₗ[K] Module.End K V) ∘ₗ h P
  D_lie a x y := Subtype.ext (leibniz_lie (h P a) (x : P.KacMoodyAlgebra) (y : P.KacMoodyAlgebra))
  φ_lie a x v := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap, toEnd_apply_apply,
      LieSubalgebra.coe_bracket_of_module, coe_adNNeg_apply]
    exact leibniz_lie _ _ _

/-- The weight spaces of `V` for the action of `𝔥` are the usual weight spaces. -/
lemma weightSpaceOf_nNegDerivAction_φ (ν : Dual K H) :
    Module.End.weightSpaceOf (nNegDerivAction P V).φ ν = weightSpaceOfMap V (h P) ν := rfl

variable [CharZero K]

/-- `𝔫₋` is the sum of its `𝔥`-weight spaces (namely the root spaces `𝔤_{-α}`, `α > 0`). -/
theorem iSup_weightSpaceOf_adNNeg : ⨆ γ, Module.End.weightSpaceOf (adNNeg P) γ = ⊤ := by
  refine eq_top_iff.mpr fun y _ ↦ ?_
  have hy : y ∈ Submodule.span K (Set.range (nNegBasis P)) := (nNegBasis P).mem_span y
  refine Submodule.span_le.mpr ?_ hy
  rintro _ ⟨x, rfl⟩
  refine Submodule.mem_iSup_of_mem (-x.root) fun a ↦ Subtype.ext ?_
  simpa using nNegBasis_mem P x a

/-- If `V` is the sum of its weight spaces, then so is `⋀𝔫₋ ⊗ V`. -/
theorem iSup_nNegChainWeightSpace (hV : ⨆ ν, weightSpaceOfMap V (h P) ν = ⊤) :
    ⨆ μ, (nNegDerivAction P V).chainWeightSpace μ = ⊤ :=
  (nNegDerivAction P V).iSup_chainWeightSpace (iSup_weightSpaceOf_adNNeg P) hV

/-- If `V` is the sum of its weight spaces, then `H_k(𝔫₋, V) = ⊕_μ H_k(𝔫₋, V)_μ`
(cf. [GL] Lemma 9.2). -/
theorem iSup_nNegHomologyWeightSpace (hV : ⨆ ν, weightSpaceOfMap V (h P) ν = ⊤) (k : ℕ) :
    ⨆ μ, (nNegDerivAction P V).homologyWeightSpace k μ = homology K (nNeg P) V k :=
  (nNegDerivAction P V).iSup_homologyWeightSpace (iSup_weightSpaceOf_adNNeg P) hV k

end Matrix.Realization.KacMoodyAlgebra
