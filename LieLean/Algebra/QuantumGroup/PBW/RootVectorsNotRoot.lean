/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Braid

/-!
# Root vectors in `U⁺` at a parameter which is not a root of unity

For `v ≠ 0` not a root of unity and `Tᵢ = braidEquivOfNotRoot`, the braid relations hold for every
Cartan datum (`isBraidLiftable_braidEquivOfNotRoot`), so the results of
`PBW/RootVectorsQuantum.lean` hold for every Cartan datum (no `BraidOuterCondition`):

* `QuantumGroup.braidLift_E_mem_adjoin_of_not_root`: `T_w(Eᵢ) ∈ U⁺` if `ℓ(w sᵢ) > ℓ(w)`
  ([Jan] Prop. 8.20, [Lus] Lemma 40.1.2);
* `QuantumGroup.braidLift_E_eq_of_not_root`: `T_w(Eᵢ) = Eⱼ` if moreover `w sᵢ = sⱼ w`;
* `QuantumGroup.rootVector_mem_adjoin_of_not_root`: the root vectors along a reduced word lie in
  `U⁺` ([Jan] 8.21, [Lus] Prop. 40.1.3).

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, §8.20–8.21.
* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 40.1.2, 40.1.3.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}
  (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-- `braidLift_E_mem_adjoin` for `v` not a root of unity (`Tᵢ = braidEquivOfNotRoot`), with no
condition on the Dynkin diagram ([Lus] Lemma 40.1.2). -/
theorem braidLift_E_mem_adjoin_of_not_root {w : W} {i : I} (hwi : ¬cs.IsRightDescent w i) :
    cs.braidLift (braidEquivOfNotRoot R hv') w (E R v i) ∈
      Algebra.adjoin k (Set.range (E R v)) :=
  CoxeterSystem.braidLift_apply_mem_adjoin (isBraidLiftable_braidEquivOfNotRoot R hv')
    (rankTwoRootProperty_braidEquivOfGeneric
      (fun i ↦ (shortNode_braidGeneric_of_not_root hv' i).sub_ne)
      (braidSerreGeneric_of_not_root hv')) hwi

/-- `braidLift_E_eq` for `v` not a root of unity (`Tᵢ = braidEquivOfNotRoot`). -/
theorem braidLift_E_eq_of_not_root {w : W} {i j : I} (hwi : ¬cs.IsRightDescent w i)
    (h : w * cs.simple i = cs.simple j * w) :
    cs.braidLift (braidEquivOfNotRoot R hv') w (E R v i) = E R v j :=
  CoxeterSystem.braidLift_apply_eq_of_mul_simple_eq (isBraidLiftable_braidEquivOfNotRoot R hv')
    (rankTwoRootProperty_braidEquivOfGeneric
      (fun i ↦ (shortNode_braidGeneric_of_not_root hv' i).sub_ne)
      (braidSerreGeneric_of_not_root hv')) hwi h

/-- `rootVector_mem_adjoin_of_isReduced` for `v` not a root of unity. -/
theorem rootVector_mem_adjoin_of_not_root {ω : List I} (hω : cs.IsReduced ω) (n : ℕ)
    (hn : n < ω.length) :
    CoxeterSystem.rootVector (braidEquivOfNotRoot R hv') (E R v) ω n hn ∈
      Algebra.adjoin k (Set.range (E R v)) :=
  CoxeterSystem.rootVector_mem_adjoin (isBraidLiftable_braidEquivOfNotRoot R hv')
    (rankTwoRootProperty_braidEquivOfGeneric
      (fun i ↦ (shortNode_braidGeneric_of_not_root hv' i).sub_ne)
      (braidSerreGeneric_of_not_root hv')) hω n hn

end LieLean.QuantumGroup
