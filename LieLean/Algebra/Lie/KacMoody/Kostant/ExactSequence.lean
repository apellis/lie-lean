/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.EquivariantSequence
import LieLean.Algebra.Lie.KacMoody.BGG.Minimality
import LieLean.Algebra.Lie.KacMoody.Kostant.Chains

/-!
# Cartan-equivariant connecting maps for nilradical homology

## Main results

* `nNegHomologyConnecting_equivariant`: the actual coefficient connecting map commutes
  with the Cartan action for a short exact sequence of Kac–Moody modules.
* `nNegHomologyConnecting_mem_weightSpace`: it maps classes represented by cycles of a given
  weight into the same homology weight space when the target coefficients are diagonalizable.

## References

Reconstructed by specializing the naturality of the CE connecting map to `nNegDerivAction`.
These results do not assume or prove BGG exactness or positive-degree Verma acyclicity.
-/

open Module LieModule LieModule.ChevalleyEilenberg
noncomputable section
namespace Matrix.Realization.KacMoodyAlgebra

universe w
variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V W U : Type w}
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]
  [AddCommGroup U] [Module K U] [LieRingModule P.KacMoodyAlgebra U]
  [LieModule K P.KacMoodyAlgebra U]

/-- A Kac–Moody module map intertwines the coefficient part of the Cartan derivation action. -/
lemma nNegDerivAction_intertwines (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (a : H) :
    ((nNegDerivAction P W).φ a).comp f.toLinearMap =
      f.toLinearMap.comp ((nNegDerivAction P V).φ a) := by
  ext v
  exact (f.map_lie (h P a) v).symm

variable (f : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) (g : W →ₗ⁅K,P.KacMoodyAlgebra⁆ U)
  (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g)

/-- The nilradical connecting map for an actual short exact sequence of Kac–Moody modules
commutes with the Cartan action. Reconstructed from naturality, without a splitting. -/
theorem nNegHomologyConnecting_equivariant (a : H) (k : ℕ) :
    ((nNegDerivAction P V).homologyEnd a k).comp
        (homologyConnecting (BGGMinimality.restrictNNeg P f)
          (BGGMinimality.restrictNNeg P g) hfg hf hg k) =
      (homologyConnecting (BGGMinimality.restrictNNeg P f)
        (BGGMinimality.restrictNNeg P g) hfg hf hg k).comp
          ((nNegDerivAction P U).homologyEnd a (k + 1)) :=
  homologyConnecting_equivariant (nNegDerivAction P V) (nNegDerivAction P W)
    (nNegDerivAction P U) _ _ hfg hf hg rfl rfl
    (nNegDerivAction_intertwines P f) (nNegDerivAction_intertwines P g) a k

variable [CharZero K]

set_option maxHeartbeats 800000 in
-- Unfolding the quotient action and restricted nilradical instances exceeds default fuel.
set_option backward.isDefEq.respectTransparency false in
/-- A class belongs to the existing image-of-weighted-cycles homology weight space exactly
when its Cartan eigen-equations hold, provided the coefficient module is diagonalizable.
Reconstructed from `DerivAction.homologyWeightSpace_eq` and the nilradical root decomposition. -/
theorem mem_nNegHomologyWeightSpace_iff
    (hV : ⨆ ν, weightSpaceOfMap V (h P) ν = ⊤) (k : ℕ) (μ : Dual K H)
    (z : homology K (nNeg P) V k) :
    z.1 ∈ (nNegDerivAction P V).homologyWeightSpace k μ ↔
      ∀ a, (nNegDerivAction P V).homologyEnd a k z = μ a • z := by
  rw [(nNegDerivAction P V).homologyWeightSpace_eq (iSup_weightSpaceOf_adNNeg P) hV]
  constructor
  · intro hz a
    apply Subtype.ext
    change (nNegDerivAction P V).θQ k a z.1 = μ a • z.1
    exact hz.2 a
  · intro hz
    exact ⟨z.2, fun a ↦ congrArg Subtype.val (hz a)⟩

set_option maxHeartbeats 800000 in
-- Comparing the connecting map through the restricted module instances exceeds default fuel.
set_option backward.isDefEq.respectTransparency false in
/-- The actual connecting map preserves the existing homology weight spaces. Only the
TARGET coefficient module needs to be diagonalizable: the input is already a weighted class.
Reconstructed from Cartan equivariance and the characterization by eigen-equations. -/
theorem nNegHomologyConnecting_mem_weightSpace
    (hV : ⨆ ν, weightSpaceOfMap V (h P) ν = ⊤) (k : ℕ) (μ : Dual K H)
    (z : homology K (nNeg P) U (k + 1))
    (hz : z.1 ∈ (nNegDerivAction P U).homologyWeightSpace (k + 1) μ) :
    (homologyConnecting (BGGMinimality.restrictNNeg P f)
      (BGGMinimality.restrictNNeg P g) hfg hf hg k z).1 ∈
        (nNegDerivAction P V).homologyWeightSpace k μ := by
  apply (mem_nNegHomologyWeightSpace_iff P hV k μ _).mpr
  intro a
  have he := LinearMap.congr_fun (nNegHomologyConnecting_equivariant P f g hfg hf hg a k) z
  have hz' : (nNegDerivAction P U).homologyEnd a (k + 1) z = μ a • z := by
    apply Subtype.ext
    change (nNegDerivAction P U).θQ (k + 1) a z.1 = μ a • z.1
    exact (nNegDerivAction P U).homologyWeightSpace_le_quotWeightSpace (k + 1) μ hz a
  change (nNegDerivAction P V).homologyEnd a k
      (homologyConnecting (BGGMinimality.restrictNNeg P f)
        (BGGMinimality.restrictNNeg P g) hfg hf hg k z) =
    homologyConnecting (BGGMinimality.restrictNNeg P f)
      (BGGMinimality.restrictNNeg P g) hfg hf hg k
        ((nNegDerivAction P U).homologyEnd a (k + 1) z) at he
  exact he.trans ((congrArg
    (homologyConnecting (BGGMinimality.restrictNNeg P f)
      (BGGMinimality.restrictNNeg P g) hfg hf hg k) hz').trans (map_smul _ _ _))

end Matrix.Realization.KacMoodyAlgebra
