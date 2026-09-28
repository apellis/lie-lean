/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.Casimir
import LieLean.Algebra.Lie.KacMoody.BGG.Integrable

/-!
# Positive-degree exactness of the actual BGG complex

## Main results

* `ker_bggDiff_eq_range`: the actual signed BGG complex is exact in every positive degree
  for a dominant integral highest weight, symmetrizable GCM and finite-dimensional Cartan space.

## References

Heckenberger–Kolb, *On the Bernstein–Gelfand–Gelfand resolution for Kac–Moody algebras
and quantized enveloping algebras*, arXiv:math/0605460, §3.1, Proposition 3.4 and the proof
of Theorem 3.2 for symmetrizable Kac–Moody algebras (consulted). The final vanishing step
uses the reconstructed maximal-weight/Casimir argument instead of complete reducibility.
The characteristic-zero field generality follows from the proved Lean arguments.
-/

noncomputable section
namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsGeneralizedCartan) {Λ : Module.Dual K H}
  (hΛ : P.IsDominantIntegral Λ) (hS : A.IsSymmetrizable)

include hS in
/-- The BGG complex is exact at every positive term `C_(k+1)`.
Theorem 3.2 of Heckenberger–Kolb in the symmetrizable case, using the actual signed
cover-map differential; no lower exactness, integrability or coinvariant premise remains. -/
theorem ker_bggDiff_eq_range (k : ℕ) :
    (bggDiff P hA hΛ k).ker = (bggDiff P hA hΛ (k + 1)).range := by
  apply BGGCasimir.exact_of_nilpotent_mod_boundaries_symmetrizable P hA hΛ hS k
  intro x hx i
  exact BGGIntegrable.exists_pow_mem_range_of_cycle P hA hΛ k i x hx

end Matrix.Realization.KacMoodyAlgebra
