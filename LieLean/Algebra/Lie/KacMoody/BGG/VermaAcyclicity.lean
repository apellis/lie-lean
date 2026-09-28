/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.RegularAcyclic

/-!
# Positive-degree nilradical homology of Verma modules

## Main results

* `VermaModule.subsingleton_homology_of_pos`: actual positive-degree negative-nilradical
  CE homology of every Verma module vanishes.

This uses the proved regular CE acyclicity and the actual PBW coefficient equivalence.
No dominance, integrality, finite-dimensionality or symmetrizability hypothesis is added.
This does not assert exactness of the positive-degree BGG differential.

## References

Reconstructed by transport through `homologyEquivLeftRegular` from the proved regular
CE acyclicity. No additional external source consulted.
-/

namespace Matrix.Realization.KacMoodyAlgebra.VermaModule

open LieModule.ChevalleyEilenberg

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (Λ : Module.Dual K H)

/-- Every Verma module is acyclic in positive degrees for actual negative-nilradical CE
homology. Reconstructed from PBW transport and regular CE acyclicity. -/
theorem subsingleton_homology_of_pos (q : ℕ) (hq : 0 < q) :
    Subsingleton (homology K (nNeg P) (VermaModule P Λ) q) := by
  exact (homologyEquivLeftRegular P Λ q).toEquiv.subsingleton_congr.mpr
    (subsingleton_homology_leftRegular q hq)

end Matrix.Realization.KacMoodyAlgebra.VermaModule
