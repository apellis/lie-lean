/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.DirectSum
import LieLean.Algebra.Lie.KacMoody.BGG.VermaAcyclicity
import LieLean.Algebra.Lie.KacMoody.BGG

/-!
# Positive-degree nilradical homology of BGG terms

## Main results

* `subsingleton_homology_bggTerm_of_pos`: every actual BGG term is acyclic in positive
  degrees for negative-nilradical CE homology.

## References

Reconstructed from actual Verma acyclicity and finite-support direct-sum compatibility.
No external source consulted. This does not prove exactness of the BGG differential.
-/

namespace Matrix.Realization.KacMoodyAlgebra
open LieModule.ChevalleyEilenberg
variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsGeneralizedCartan) (Λ : Module.Dual K H)

/-- Every actual BGG term is acyclic for positive-degree negative-nilradical CE homology.
Reconstructed by finite-support direct-sum transport from proved Verma acyclicity.
No dominance, symmetrizability, or finite-dimensionality hypothesis is needed. -/
theorem subsingleton_homology_bggTerm_of_pos (k q : ℕ) (hq : 0 < q) :
    Subsingleton (homology K (nNeg P) (BGGTerm P hA Λ k) q) := by
  exact subsingleton_homology_directSum
    (fun w : {w : P.weylGroup hA // (P.coxeterSystem hA).length w = k} =>
      VermaModule P (P.weylDot hA w Λ)) q
    (fun w => VermaModule.subsingleton_homology_of_pos P (P.weylDot hA w Λ) q hq)

end Matrix.Realization.KacMoodyAlgebra

