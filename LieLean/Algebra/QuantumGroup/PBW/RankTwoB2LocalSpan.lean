/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.RankTwoB2

/-!
# Local B₂ ordered spanning in arbitrary ambient quantum groups

## Main results

* `B2PBW.span_mono_eq_adjoin`: the B₂ straightening relations give ordered spanning
  of the two-generator subalgebra of any ambient algebra.
* `span_b2Mono_pair`: the raw B₂ ordered monomials span the actual subalgebra generated
  by a double edge, without restricting the ambient Cartan datum to two nodes.
* `span_b2PBWMono_pair`: the normalized B₂ monomials have the same local span.

The quantum-group results assume a nonzero parameter and the explicit denominator
conditions `vᵢ - vᵢ⁻¹ ≠ 0` and `[2]ᵢ! ≠ 0`. No characteristic-zero, transcendence,
non-root-of-unity, or finite-type hypothesis is imposed. This result does not assert
length-four braid-span invariance, reverse-orientation spanning, or linear independence.

## References

Reconstructed from the established `B2PBW.Rel` straightening formulas and monomial
operators. As in `RankTwoA2LocalSpan`, induction on a two-letter free algebra avoids
requiring an operator representation satisfying relations involving other ambient nodes.
-/

open LieLean

noncomputable section
namespace LieLean.QuantumGroup
namespace B2PBW
open LusztigF
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]
  {p : k} {e x y f : B}

private theorem monoMap_pair_rep (H : Rel p e x y f)
    (hp : p ≠ 0) (h1 : p - 1 ≠ 0) (h2 : p ^ 2 - 1 ≠ 0)
    (a : FreeAlgebra k Bool) (s : Space k) :
    monoMap k e x y f (rep p false a s) =
      FreeAlgebra.lift k (fun b : Bool ↦ if b then f else e) a *
        monoMap k e x y f s := by
  induction a using FreeAlgebra.induction generalizing s with
  | grade0 r =>
    rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, map_smul,
      Algebra.smul_def]
  | grade1 b =>
    cases b with
    | false =>
      change monoMap k e x y f (rep p false (θ k false) s) = _
      rw [rep_θ_left, FreeAlgebra.lift_ι_apply, monoMap_opE]
      rfl
    | true =>
      change monoMap k e x y f (rep p false (θ k true) s) = _
      rw [rep_θ_right (by decide : false ≠ true), FreeAlgebra.lift_ι_apply,
        monoMap_opF H hp h1 h2]
      rfl
  | mul a b ha hb =>
    rw [map_mul, Module.End.mul_apply, ha, hb, map_mul, mul_assoc]
  | add a b ha hb =>
    rw [map_add, LinearMap.add_apply, map_add, ha, hb, map_add, add_mul]

/-- The B₂ straightening relations give ordered spanning of the two-generator
subalgebra in any ambient algebra, under the denominators required by the monomial
operators. Reconstructed using the two-letter free-algebra argument. -/
theorem span_mono_eq_adjoin (H : Rel p e x y f)
    (hp : p ≠ 0) (h1 : p - 1 ≠ 0) (h2 : p ^ 2 - 1 ≠ 0) :
    Submodule.span k (Set.range (mono e x y f)) =
      (Algebra.adjoin k {e, f}).toSubmodule := by
  have hpair : Set.range (fun b : Bool ↦ if b then f else e) = {e, f} := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨b, rfl⟩
      cases b <;> simp
    · rintro (rfl | rfl)
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨m, rfl⟩
    change mono e x y f m ∈ Algebra.adjoin k {e, f}
    have he : e ∈ Algebra.adjoin k {e, f} := Algebra.subset_adjoin (by simp)
    have hf : f ∈ Algebra.adjoin k {e, f} := Algebra.subset_adjoin (by simp)
    have hy : y = e * f - p⁻¹ • (f * e) := by
      rw [H.fe, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hp, one_smul,
        one_smul, sub_sub_cancel]
    have hx : x = e * y - y * e := by rw [H.ye]; abel
    have hy_mem : y ∈ Algebra.adjoin k {e, f} := by
      rw [hy]
      exact sub_mem (mul_mem he hf) (Subalgebra.smul_mem _ (mul_mem hf he) _)
    have hx_mem : x ∈ Algebra.adjoin k {e, f} := by
      rw [hx]
      exact sub_mem (mul_mem he hy_mem) (mul_mem hy_mem he)
    exact mul_mem (pow_mem he _) (mul_mem (pow_mem hx_mem _)
      (mul_mem (pow_mem hy_mem _) (pow_mem hf _)))
  · rw [← hpair, Algebra.adjoin_range_eq_range_freeAlgebra_lift]
    rintro _ ⟨a, rfl⟩
    change FreeAlgebra.lift k (fun b : Bool ↦ if b then f else e) a ∈ _
    have ha := monoMap_pair_rep H hp h1 h2 a (Finsupp.single (0, 0, 0, 0) 1)
    simp only [monoMap_single, mono, pow_zero, one_smul, mul_one] at ha
    rw [← ha, monoMap, ← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ _
end B2PBW

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]
  {i j : I} (hij : i ≠ j) (h : D.cartanMatrix i j = -2)
  (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (h2 : qFactorial (v ^ D.d i) 2 ≠ 0)

include hij h h' hq h2

/-- Raw B₂ ordered monomials span the actual two-generator subalgebra at a double
edge in arbitrary ambient Cartan data. Reconstructed from `b2_rel` and the abstract
local straightening theorem; no assumption on the other nodes is needed. -/
theorem span_b2Mono_pair :
    Submodule.span k (Set.range
      (B2PBW.mono (E R v i) (b2RootX R v i j) (b2RootY R v i j) (E R v j))) =
      (Algebra.adjoin k {E R v i, E R v j}).toSubmodule := by
  obtain ⟨hp, h1, hp2⟩ := B2PBW.param_ne (pow_ne_zero _ (NeZero.ne v)) hq h2
  exact B2PBW.span_mono_eq_adjoin (b2_rel hij h h') hp h1 hp2

/-- Normalized B₂ ordered monomials span the actual two-generator subalgebra at a
double edge in arbitrary ambient Cartan data. Reconstructed by rescaling the raw
monomials with nonzero powers of `[2]ᵢ!⁻¹`. -/
theorem span_b2PBWMono_pair :
    Submodule.span k (Set.range (b2PBWMono R v i j)) =
      (Algebra.adjoin k {E R v i, E R v j}).toSubmodule := by
  rw [← span_b2Mono_pair R v hij h h' hq h2]
  have hc : (qFactorial (v ^ D.d i) 2)⁻¹ ≠ 0 := inv_ne_zero h2
  apply le_antisymm <;> rw [Submodule.span_le] <;> rintro _ ⟨m, rfl⟩
  · rw [b2PBWMono_eq_smul h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  · have hm : B2PBW.mono (E R v i) (b2RootX R v i j) (b2RootY R v i j) (E R v j) m =
        ((qFactorial (v ^ D.d i) 2)⁻¹ ^ m.2.1)⁻¹ • b2PBWMono R v i j m := by
      rw [b2PBWMono_eq_smul h, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hc), one_smul]
    rw [SetLike.mem_coe, hm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
end LieLean.QuantumGroup
