/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Kostant.ExactSequence

/-!
# Dimension shifting on nilradical homology weight spaces

## Main definitions

* `nNegHomologyWeightConnecting`: the concrete connecting map restricted to the existing
  image-of-weighted-cycles weight spaces.
* `nNegHomologyWeightConnectingEquiv`: dimension shifting on these weight spaces when the
  middle coefficient module has zero homology in the two adjacent degrees.

## References

Reconstructed from the coefficient long exact sequence and Cartan equivariance. No Verma
acyclicity or BGG exactness is asserted: vanishing of the middle homology is explicit.
-/

open Module LieModule LieModule.ChevalleyEilenberg
noncomputable section
namespace Matrix.Realization.KacMoodyAlgebra

universe w
variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V W U : Type w}
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]
  [AddCommGroup U] [Module K U] [LieRingModule P.KacMoodyAlgebra U]
  [LieModule K P.KacMoodyAlgebra U]
  (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (g : W →ₗ⁅K,P.KacMoodyAlgebra⁆ U)
  (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g)
  (hV : ⨆ ν, weightSpaceOfMap V (h P) ν = ⊤)

/-- The actual connecting map, restricted to the existing homology weight spaces.
Reconstructed from the weight-space preservation theorem; no vanishing is required. -/
def nNegHomologyWeightConnecting (k : ℕ) (μ : Dual K H) :
    (nNegDerivAction P U).homologyWeightSpace (k + 1) μ →ₗ[K]
      (nNegDerivAction P V).homologyWeightSpace k μ :=
  (((homology K (nNeg P) V k).subtype.comp
    (homologyConnecting (BGGMinimality.restrictNNeg P f)
      (BGGMinimality.restrictNNeg P g) hfg hf hg k)).comp
    (Submodule.inclusion
      ((nNegDerivAction P U).homologyWeightSpace_le_homology (k + 1) μ))).codRestrict
      _ (fun z ↦ nNegHomologyConnecting_mem_weightSpace P f g hfg hf hg hV k μ
        ⟨z.1, (nNegDerivAction P U).homologyWeightSpace_le_homology (k + 1) μ z.2⟩ z.2)

-- Definitional equality through the restricted nilradical coefficient actions is expensive.
set_option backward.isDefEq.respectTransparency false in
include hV in
/-- If the middle module has zero upper homology, the connecting map detects weight membership
as well as preserving it, provided both endpoint coefficient modules are diagonalizable.
Reconstructed from injectivity and Cartan equivariance. -/
theorem nNegHomologyConnecting_mem_weightSpace_iff
    (hU : ⨆ ν, weightSpaceOfMap U (h P) ν = ⊤) (k : ℕ) (μ : Dual K H)
    [Subsingleton (homology K (nNeg P) W (k + 1))]
    (z : homology K (nNeg P) U (k + 1)) :
    (homologyConnecting (BGGMinimality.restrictNNeg P f)
      (BGGMinimality.restrictNNeg P g) hfg hf hg k z).1 ∈
        (nNegDerivAction P V).homologyWeightSpace k μ ↔
      z.1 ∈ (nNegDerivAction P U).homologyWeightSpace (k + 1) μ := by
  constructor
  · intro hz
    apply (mem_nNegHomologyWeightSpace_iff P hU (k + 1) μ z).mpr
    intro a
    apply homologyConnecting_injective (BGGMinimality.restrictNNeg P f)
      (BGGMinimality.restrictNNeg P g) hfg hf hg k
    have he := LinearMap.congr_fun (nNegHomologyConnecting_equivariant P f g hfg hf hg a k) z
    have hz' := (mem_nNegHomologyWeightSpace_iff P hV k μ _).mp hz a
    exact he.symm.trans (hz'.trans (map_smul _ _ _).symm)
  · exact nNegHomologyConnecting_mem_weightSpace P f g hfg hf hg hV k μ z

omit [Fintype ι] [DecidableEq ι] [CharZero K] in
/-- A bijection between two submodules restricts to a bijection between smaller submodules
when it detects membership in them. -/
lemma bijective_codRestrict_of_mem_iff {E₁ E₂ : Type*} [AddCommGroup E₁] [Module K E₁]
    [AddCommGroup E₂] [Module K E₂] {H₁ S₁ : Submodule K E₁} {H₂ S₂ : Submodule K E₂}
    (h₁ : S₁ ≤ H₁) (h₂ : S₂ ≤ H₂) (δ : H₁ →ₗ[K] H₂) (hδ : Function.Bijective δ)
    (hmem : ∀ z : H₁, (δ z).1 ∈ S₂ ↔ z.1 ∈ S₁)
    (hc : ∀ z, ((H₂.subtype.comp δ).comp (Submodule.inclusion h₁)) z ∈ S₂) :
    Function.Bijective (((H₂.subtype.comp δ).comp (Submodule.inclusion h₁)).codRestrict S₂ hc) := by
  constructor
  · intro x y hxy
    have h : (δ (Submodule.inclusion h₁ x)).1 = (δ (Submodule.inclusion h₁ y)).1 :=
      congrArg (fun t : S₂ ↦ (t : E₂)) hxy
    exact Submodule.inclusion_injective h₁ (hδ.1 (Subtype.ext h))
  · intro y
    obtain ⟨z, hz⟩ := hδ.2 ⟨y.1, h₂ y.2⟩
    have hm : z.1 ∈ S₁ := (hmem z).mp (by rw [hz]; exact y.2)
    exact ⟨⟨z.1, hm⟩, Subtype.ext (congrArg (fun t : H₂ ↦ (t : E₂)) hz)⟩

/-- Weight-space dimension shifting for the actual nilradical CE connecting map.
Reconstructed from its bijectivity and weight detection. The middle module's homology must
vanish in BOTH adjacent degrees; this theorem does not assert that Verma modules are acyclic. -/
def nNegHomologyWeightConnectingEquiv
    (hU : ⨆ ν, weightSpaceOfMap U (h P) ν = ⊤) (k : ℕ) (μ : Dual K H)
    [Subsingleton (homology K (nNeg P) W (k + 1))]
    [Subsingleton (homology K (nNeg P) W k)] :
    (nNegDerivAction P U).homologyWeightSpace (k + 1) μ ≃ₗ[K]
      (nNegDerivAction P V).homologyWeightSpace k μ :=
  LinearEquiv.ofBijective (nNegHomologyWeightConnecting P f g hfg hf hg hV k μ)
    (bijective_codRestrict_of_mem_iff _ ((nNegDerivAction P V).homologyWeightSpace_le_homology k μ)
      _ ⟨homologyConnecting_injective (BGGMinimality.restrictNNeg P f)
          (BGGMinimality.restrictNNeg P g) hfg hf hg k,
        homologyConnecting_surjective (BGGMinimality.restrictNNeg P f)
          (BGGMinimality.restrictNNeg P g) hfg hf hg k⟩
      (nNegHomologyConnecting_mem_weightSpace_iff P f g hfg hf hg hV hU k μ) _)

end Matrix.Realization.KacMoodyAlgebra
