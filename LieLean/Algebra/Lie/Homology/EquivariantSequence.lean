/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.LongExactSequence
import LieLean.Algebra.Lie.Homology.Weights
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Derivation actions on the coefficient homology sequence

## Main definitions

* `DerivAction.chainEnd`: a derivation action as an actual endomorphism of the CE complex.
* `DerivAction.homologyEnd`: the existing quotient action restricted to concrete homology.

## Main results

* `DerivAction.chainComplexHomologyIso_action`: the comparison respects derivation actions.
* `homologyConnecting_equivariant`: compatible coefficient actions commute with the connecting map.
* `homologyConnecting_map_eigenvector`: simultaneous eigenvectors retain their weight.

## References

Reconstructed from the existing derivation-action and homology comparison APIs and Mathlib's
naturality of the snake-lemma connecting map. No BGG exactness is assumed.
-/

open CategoryTheory CategoryTheory.Limits Module TensorProduct ExteriorAlgebra
noncomputable section
namespace LieModule.ChevalleyEilenberg

universe u v w x
variable {K : Type u} [Field K] {H : Type x} [AddCommGroup H] [Module K H]
  {L : Type v} [LieRing L] [LieAlgebra K L]
  {M N P : Type w}
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [AddCommGroup P] [Module K P] [LieRingModule L P] [LieModule K L P]

namespace DerivAction
variable (ρ : DerivAction K H L M) (a : H)

/-- The degree-preserving derivation action on a CE chain module. -/
def onChains (k : ℕ) : Module.End K (⋀[K]^k L ⊗[K] M) :=
  proj K L M k ∘ₗ ρ.θ a ∘ₗ incl K L M k

omit [LieModule K L M] in
lemma incl_onChains (k : ℕ) (x : ⋀[K]^k L ⊗[K] M) :
    incl K L M k (ρ.onChains a k x) = ρ.θ a (incl K L M k x) :=
  incl_proj_of_mem (ρ.θ_mem_chainsIn a (LinearMap.mem_range_self _ x))

set_option backward.isDefEq.respectTransparency false in
/-- A compatible derivation action defines an actual endomorphism of the CE chain complex. -/
def chainEnd : chainComplex K L M ⟶ chainComplex K L M :=
  ChainComplex.ofHom (fun k ↦ ModuleCat.ofHom (ρ.onChains a k)) fun k ↦ by
    rw [chainComplex_d]
    ext x
    apply incl_injective k
    change incl K L M k (d K L M k (ρ.onChains a (k + 1) x)) =
      incl K L M k (ρ.onChains a k (d K L M k x))
    simp only [incl_d, incl_onChains, diff_θ]

/-- Restriction of the existing quotient derivation action to actual concrete homology. -/
def homologyEnd (k : ℕ) : Module.End K (homology K L M k) :=
  (ρ.θQ k a).restrict fun x hx ↦ by
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨ρ.θ a c, ρ.θ_mem_cycles a hc, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The derivation endomorphism acts on the concrete left homology data. -/
def leftHomologyMapData (k : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat K) (ComplexShape.down ℕ) k).map
        (ρ.chainEnd a))
      (chainComplexLeftHomologyData K L M k) (chainComplexLeftHomologyData K L M k) where
  φK := ModuleCat.ofHom (((ρ.onChains a k).domRestrict _).codRestrict _ fun t ↦ by
    apply (incl_mem_cycles_iff k _).mp
    change incl K L M k (ρ.onChains a k t.1) ∈ cycles K L M k
    rw [incl_onChains]
    exact ρ.θ_mem_cycles a ((incl_mem_cycles_iff k t.1).mpr t.2))
  φH := ModuleCat.ofHom (ρ.homologyEnd a k)
  commi := by ext t; rfl
  commf' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    exact (congrArg (fun g ↦ (ModuleCat.Hom.hom g) t)
      ((ρ.chainEnd a).comm ((ComplexShape.down ℕ).prev k) k)).symm
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    change Submodule.Quotient.mk (ρ.θ a (incl K L M k t.1)) =
      Submodule.Quotient.mk (incl K L M k (ρ.onChains a k t.1))
    rw [incl_onChains]

/-- The categorical/concrete homology comparison intertwines the derivation actions. -/
theorem chainComplexHomologyIso_action (k : ℕ) :
    HomologicalComplex.homologyMap (ρ.chainEnd a) k ≫
        (chainComplexHomologyIso K L M k).hom =
      (chainComplexHomologyIso K L M k).hom ≫ ModuleCat.ofHom (ρ.homologyEnd a k) :=
  (ρ.leftHomologyMapData a k).homologyMap_comm

variable {ρ a} (σ : DerivAction K H L N) (f : M →ₗ⁅K,L⁆ N)

omit [LieModule K L M] [LieModule K L N] in
private lemma lTensor_wedge (y : L) (c : ExteriorAlgebra K L ⊗[K] M) :
    f.toLinearMap.lTensor _ (wedge K L M y c) =
      wedge K L N y (f.toLinearMap.lTensor _ c) := by
  induction c using TensorProduct.inductionOn with
  | tmul x m => simp only [wedge_tmul, LinearMap.lTensor_tmul]
  | add c d hc hd => simp only [map_add, hc, hd]

omit [LieModule K L M] [LieModule K L N] in
/-- An equivariant coefficient map intertwines the extended derivation action on chains. -/
lemma θ_lTensor (hD : ρ.D = σ.D)
    (hφ : ∀ a, (σ.φ a).comp f.toLinearMap = f.toLinearMap.comp (ρ.φ a))
    (a : H) (c : ExteriorAlgebra K L ⊗[K] M) :
    σ.θ a (f.toLinearMap.lTensor _ c) = f.toLinearMap.lTensor _ (ρ.θ a c) := by
  refine LieModule.ChevalleyEilenberg.induction
    (p := fun c ↦ σ.θ a (f.toLinearMap.lTensor _ c) =
      f.toLinearMap.lTensor _ (ρ.θ a c))
    (fun m ↦ ?_) (fun y c hc ↦ ?_) (fun c d hc hd ↦ ?_) c
  · simp only [LinearMap.lTensor_tmul, θ_one_tmul]
    exact congrArg (fun m ↦ (1 : ExteriorAlgebra K L) ⊗ₜ[K] m)
      (LinearMap.congr_fun (hφ a) m)
  · rw [lTensor_wedge, θ_wedge, θ_wedge, map_add, lTensor_wedge, lTensor_wedge,
      hD, hc]
  · simp only [map_add, hc, hd]

set_option backward.isDefEq.respectTransparency false in
/-- An equivariant coefficient map commutes with the actual CE chain endomorphisms. -/
theorem chainEnd_map (hD : ρ.D = σ.D)
    (hφ : ∀ a, (σ.φ a).comp f.toLinearMap = f.toLinearMap.comp (ρ.φ a)) (a : H) :
    ρ.chainEnd a ≫ chainComplexMap f = chainComplexMap f ≫ σ.chainEnd a := by
  ext k : 2
  ext t
  apply incl_injective k
  change incl K L N k (mapChains K L k f (ρ.onChains a k t)) =
    incl K L N k (σ.onChains a k (mapChains K L k f t))
  simp only [incl_mapChains, incl_onChains]
  exact (θ_lTensor σ f hD hφ a _).symm

end DerivAction

variable (ρ : DerivAction K H L M) (σ : DerivAction K H L N)
  (τ : DerivAction K H L P) (f : M →ₗ⁅K,L⁆ N) (g : N →ₗ⁅K,L⁆ P)
  (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g)
  (hD₁ : ρ.D = σ.D) (hD₂ : σ.D = τ.D)
  (hφ₁ : ∀ a, (σ.φ a).comp f.toLinearMap = f.toLinearMap.comp (ρ.φ a))
  (hφ₂ : ∀ a, (τ.φ a).comp g.toLinearMap = g.toLinearMap.comp (σ.φ a))

/-- A common derivation action makes a compatible short coefficient sequence equivariant
as a short sequence of the actual CE complexes. -/
def coefficientSequenceEnd (a : H) :
    coefficientChainSequence f g hfg ⟶ coefficientChainSequence f g hfg where
  τ₁ := ρ.chainEnd a
  τ₂ := σ.chainEnd a
  τ₃ := τ.chainEnd a
  comm₁₂ := DerivAction.chainEnd_map σ f hD₁ hφ₁ a
  comm₂₃ := DerivAction.chainEnd_map τ g hD₂ hφ₂ a

set_option backward.isDefEq.respectTransparency false in
include hD₁ hD₂ hφ₁ hφ₂ in
/-- The concrete connecting homomorphism intertwines compatible derivation actions.
This follows from the naturality of the snake map, not from a choice of equivariant splitting. -/
theorem homologyConnecting_equivariant (a : H) (k : ℕ) :
    (ρ.homologyEnd a k).comp (homologyConnecting f g hfg hf hg k) =
      (homologyConnecting f g hfg hf hg k).comp (τ.homologyEnd a (k + 1)) := by
  have hn := HomologicalComplex.HomologySequence.δ_naturality
    (coefficientSequenceEnd ρ σ τ f g hfg hD₁ hD₂ hφ₁ hφ₂ a)
    (coefficientChainSequence_shortExact f g hfg hf hg)
    (coefficientChainSequence_shortExact f g hfg hf hg) (k + 1) k rfl
  change (coefficientChainSequence_shortExact f g hfg hf hg).δ (k + 1) k rfl ≫
      HomologicalComplex.homologyMap (ρ.chainEnd a) k =
    HomologicalComplex.homologyMap (τ.chainEnd a) (k + 1) ≫
      (coefficientChainSequence_shortExact f g hfg hf hg).δ (k + 1) k rfl at hn
  suffices hh : ModuleCat.ofHom (homologyConnecting f g hfg hf hg k) ≫
      ModuleCat.ofHom (ρ.homologyEnd a k) =
    ModuleCat.ofHom (τ.homologyEnd a (k + 1)) ≫
      ModuleCat.ofHom (homologyConnecting f g hfg hf hg k) by
    exact congrArg ModuleCat.Hom.hom hh
  rw [← cancel_epi (chainComplexHomologyIso K L P (k + 1)).hom,
    ← Category.assoc, homologyConnecting_comparison, Category.assoc,
    ← DerivAction.chainComplexHomologyIso_action, ← Category.assoc, hn,
    Category.assoc, ← homologyConnecting_comparison, ← Category.assoc,
    DerivAction.chainComplexHomologyIso_action, Category.assoc]

include hD₁ hD₂ hφ₁ hφ₂ in
/-- The connecting map preserves the weight of a simultaneous eigenvector for compatible
derivation actions. No diagonalizability assumption is needed for this individual vector. -/
theorem homologyConnecting_map_eigenvector (k : ℕ) (μ : Dual K H)
    (z : homology K L P (k + 1))
    (hz : ∀ a, τ.homologyEnd a (k + 1) z = μ a • z) (a : H) :
    ρ.homologyEnd a k (homologyConnecting f g hfg hf hg k z) =
      μ a • homologyConnecting f g hfg hf hg k z := by
  have he := LinearMap.congr_fun
    (homologyConnecting_equivariant ρ σ τ f g hfg hf hg hD₁ hD₂ hφ₁ hφ₂ a k) z
  change ρ.homologyEnd a k (homologyConnecting f g hfg hf hg k z) =
    homologyConnecting f g hfg hf hg k (τ.homologyEnd a (k + 1) z) at he
  rw [he, hz, map_smul]

end LieModule.ChevalleyEilenberg
