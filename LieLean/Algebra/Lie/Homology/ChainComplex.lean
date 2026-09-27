/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.Complex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The Chevalley–Eilenberg complex as a chain complex of modules

We package the Chevalley–Eilenberg complex `⋯ → ⋀²L ⊗ M → L ⊗ M → M` of a Lie algebra `L` over
a commutative ring `R` with coefficients in a Lie module `M`
(`LieModule.ChevalleyEilenberg.d`) as a Mathlib chain complex `ChainComplex (ModuleCat R) ℕ`,
functorial in `M`.

## Main definitions

* `LieModule.ChevalleyEilenberg.chainComplex`: the complex `C_•(L, M)`.
* `LieModule.ChevalleyEilenberg.chainComplexMap`: the chain map `C_•(L, M) → C_•(L, N)` induced
  by a morphism of Lie modules.

## Main results

* `LieModule.ChevalleyEilenberg.chainComplexMap_id`, `chainComplexMap_comp`: functoriality.
* `LieModule.ChevalleyEilenberg.exactAt_succ_iff`: `H_{k+1}(L, M) = 0` in the sense of Mathlib's
  homology of chain complexes iff `im d_{k+1} = ker d_k`.

## References

* C. A. Weibel, *An introduction to homological algebra*, CUP 1994, §7.7 (check).
-/

open CategoryTheory TensorProduct ExteriorAlgebra

noncomputable section

namespace LieModule.ChevalleyEilenberg

universe u v w

variable (R : Type u) (L : Type v) (M : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The **Chevalley–Eilenberg complex** `C_•(L, M)`, `C_k(L, M) = ⋀ᵏL ⊗ M`, as a chain complex of
`R`-modules. -/
def chainComplex : ChainComplex (ModuleCat.{max u v w} R) ℕ :=
  ChainComplex.of (fun k ↦ ModuleCat.of R (⋀[R]^k L ⊗[R] M))
    (fun k ↦ ModuleCat.ofHom (d R L M k))
    (fun k ↦ ModuleCat.hom_ext (d_comp_d k))

@[simp] lemma chainComplex_X (k : ℕ) :
    (chainComplex R L M).X k = ModuleCat.of R (⋀[R]^k L ⊗[R] M) := rfl

@[simp] lemma chainComplex_d (k : ℕ) :
    (chainComplex R L M).d (k + 1) k = ModuleCat.ofHom (d R L M k) := by
  simp [chainComplex]

variable {R L M}
variable {N : Type w} [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- The chain map `C_•(L, M) → C_•(L, N)` induced by a morphism `f : M → N` of Lie modules. -/
def chainComplexMap (f : M →ₗ⁅R,L⁆ N) : chainComplex R L M ⟶ chainComplex R L N :=
  ChainComplex.ofHom (fun k ↦ ModuleCat.ofHom (mapChains R L k f)) fun k ↦ by
    rw [chainComplex_d, chainComplex_d]
    ext t
    exact (mapChains_d k f t).symm

@[simp] lemma chainComplexMap_f (f : M →ₗ⁅R,L⁆ N) (k : ℕ) :
    (chainComplexMap f).f k = ModuleCat.ofHom (mapChains R L k f) := rfl

@[simp] lemma chainComplexMap_id :
    chainComplexMap (LieModuleHom.id : M →ₗ⁅R,L⁆ M) = 𝟙 (chainComplex R L M) := by
  ext k : 2
  simp only [chainComplexMap_f, HomologicalComplex.id_f]
  ext t
  change ((LinearMap.id : M →ₗ[R] M).lTensor _) t = t
  rw [LinearMap.lTensor_id]
  rfl

lemma chainComplexMap_comp {P : Type w} [AddCommGroup P] [Module R P] [LieRingModule L P]
    [LieModule R L P] (g : N →ₗ⁅R,L⁆ P) (f : M →ₗ⁅R,L⁆ N) :
    chainComplexMap (g.comp f) = chainComplexMap f ≫ chainComplexMap g := by
  ext k : 2
  simp only [chainComplexMap_f, HomologicalComplex.comp_f]
  ext t
  change ((g.comp f : M →ₗ[R] P).lTensor _) t = (g : N →ₗ[R] P).lTensor _
    ((f : M →ₗ[R] N).lTensor _ t)
  rw [LieModuleHom.toLinearMap_comp, LinearMap.lTensor_comp]
  rfl

/-- The homology `H_{k+1}(L, M)` of the Chevalley–Eilenberg complex vanishes (in the sense of
Mathlib's `HomologicalComplex.ExactAt`) iff `im d_{k+1} = ker d_k`. -/
theorem exactAt_succ_iff (k : ℕ) :
    (chainComplex R L M).ExactAt (k + 1) ↔
      LinearMap.range (d R L M (k + 1)) = LinearMap.ker (d R L M k) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g, chainComplex_d]
  rfl

end LieModule.ChevalleyEilenberg
