/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.DirectSum
import LieLean.Algebra.Lie.KacMoody.BGG.VermaHomology
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Tensoring with a trivial module preserves acyclicity

Over a field `K`, a vector space `Z` with the trivial action of `L` is a direct sum of copies of
`K`, so `M ⊗ Z ≅ ⊕_b M` as `L`-modules (`LieModule.ChevalleyEilenberg.tensorTrivialEquiv`), and
Chevalley–Eilenberg homology of `M ⊗ Z` vanishes in every degree in which that of `M` does
(`LieModule.ChevalleyEilenberg.subsingleton_homology_tensor_trivial`).

## References

Elementary; reconstructed from `subsingleton_homology_directSum`.
-/

noncomputable section

open scoped TensorProduct DirectSum
open TensorProduct

namespace LieModule.ChevalleyEilenberg

variable {K L M Z : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup Z] [Module K Z]

/-- The linear equivalence `M ⊗ Z ≅ ⊕_b M` for a basis `b` of `Z`. -/
def tensorTrivialLinearEquiv {β : Type*} [DecidableEq β] (b : Module.Basis β K Z) :
    M ⊗[K] TrivialLieModule K L Z ≃ₗ[K] ⨁ _ : β, M :=
  ((TensorProduct.congr (LinearEquiv.refl K M)
    ((TrivialLieModule.equiv K L Z).trans b.repr)).trans
    (finsuppScalarRight K K M β)).trans (finsuppLEquivDirectSum K M β)

lemma tensorTrivialLinearEquiv_lie {β : Type*} [DecidableEq β] (b : Module.Basis β K Z) (x : L)
    (t : M ⊗[K] TrivialLieModule K L Z) :
    tensorTrivialLinearEquiv b ⁅x, t⁆ = ⁅x, tensorTrivialLinearEquiv b t⁆ := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [lie_add, map_add, ht, ht', map_add, lie_add]
  | tmul m z =>
    ext i
    simp only [tensorTrivialLinearEquiv, LinearEquiv.trans_apply,
      TensorProduct.LieModule.lie_tmul_right, trivial_lie_zero, tmul_zero, add_zero, congr_tmul,
      LinearEquiv.refl_apply,
      DirectSum.lie_module_bracket_apply, finsuppLEquivDirectSum_apply,
      finsuppScalarRight_apply_tmul_apply, lie_smul]

/-- `M ⊗ Z ≅ ⊕_b M` for the trivial `L`-module `Z` with a basis `b`. -/
def tensorTrivialEquiv {β : Type*} [DecidableEq β] (b : Module.Basis β K Z) :
    M ⊗[K] TrivialLieModule K L Z ≃ₗ⁅K,L⁆ ⨁ _ : β, M :=
  { tensorTrivialLinearEquiv b with map_lie' := tensorTrivialLinearEquiv_lie b _ _ }

variable (K L M Z) in
/-- Chevalley–Eilenberg homology of `M ⊗ Z`, `Z` trivial, vanishes where that of `M` does. -/
theorem subsingleton_homology_tensor_trivial (q : ℕ) (h : Subsingleton (homology K L M q)) :
    Subsingleton (homology K L (M ⊗[K] TrivialLieModule K L Z) q) := by
  classical
  let b := Module.Free.chooseBasis K Z
  exact (homologyEquiv (tensorTrivialEquiv (L := L) (M := M) b) q).toEquiv.subsingleton_congr.mpr
    (subsingleton_homology_directSum (fun _ : Module.Free.ChooseBasisIndex K Z ↦ M) q
      fun _ ↦ h)

end LieModule.ChevalleyEilenberg
