/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.LeadingDifferential

/-!
# Positive-degree acyclicity of the actual left-regular CE complex

## Main results

* `polynomial_positive_acyclic`: positive-degree exactness of the PBW-conjugated differential,
  with primitive coefficient bound `n-1`, by Koszul descent
  (`ExteriorAlgebra.Koszul.exists_primitive_of_isLeadingKoszul`).
* `regular_positive_acyclic`: actual chain-level acyclicity after PBW transport.
* `regular_subsingleton_homology`: positive-degree regular CE homology vanishes.

The base field has characteristic zero; the ordered Lie-algebra basis may have arbitrary index
 type. No finite-dimensionality, projectivity argument, assumed comparison, or assumed vanishing.

## References

Arguments reconstructed from polynomial coefficients, tensor spans, the existing actual PBW
bridge, and the proved concrete Koszul homotopy.
-/
noncomputable section
open scoped TensorProduct BigOperators
open TensorProduct ExteriorAlgebra
open ExteriorAlgebra.Koszul (rectangle rectangle_mono tmul_mem_rectangle)
namespace LieModule.ChevalleyEilenberg.CELeading
variable {R L I : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
local notation "P" => MvPolynomial I R
local notation "EP" => ExteriorAlgebra R L ⊗[R] P

/-- The conjugated actual CE differential squares to zero. -/
theorem polynomialDiff_squared [LinearOrder I] (b : Module.Basis I R L) (z : EP) :
    polynomialDiff b (polynomialDiff b z) = 0 := by
  simp only [polynomialDiff, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, diff_diff, map_zero]

/-- Each actual regular CE chain has a finite polynomial coefficient bound under PBW. -/
theorem exists_rectangle_pbw_incl [LinearOrder I] (b : Module.Basis I R L) (q : ℕ)
    (c : ⋀[R]^q L ⊗[R] UniversalEnvelopingAlgebra.LeftRegular R L) :
    ∃ n, pbwTensor b (incl R L (UniversalEnvelopingAlgebra.LeftRegular R L) q c) ∈
      rectangle q n := by
  induction c with
  | tmul e u =>
    refine ⟨(UniversalEnvelopingAlgebra.pbwEquiv b
      (UniversalEnvelopingAlgebra.LeftRegular.equiv R L u)).totalDegree, ?_⟩
    rw [incl_tmul, pbwTensor_tmul]
    exact tmul_mem_rectangle e.2 ((MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl)
  | add x y hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨max n m, ?_⟩
    rw [map_add, map_add]
    exact add_mem (rectangle_mono q (le_max_left n m) hn)
      (rectangle_mono q (le_max_right n m) hm)

/-- PBW inverse retains exterior chain degree. -/
theorem pbwTensor_symm_mem_chainsIn [LinearOrder I] (b : Module.Basis I R L) (q n : ℕ)
    {z : EP} (hz : z ∈ rectangle q n) :
    (pbwTensor b).symm z ∈ chainsIn R L (UniversalEnvelopingAlgebra.LeftRegular R L) q := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, he, p, _, rfl⟩ := hz
    change e ⊗ₜ[R] _ ∈ _
    exact tmul_mem_chainsIn he _
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx

/-- Unfolding the actual PBW-conjugated CE differential on an actual chain. -/
theorem polynomialDiff_pbwTensor [LinearOrder I] (b : Module.Basis I R L)
    (c : ExteriorAlgebra R L ⊗[R] UniversalEnvelopingAlgebra.LeftRegular R L) :
    polynomialDiff b (pbwTensor b c) =
      pbwTensor b (diff R L (UniversalEnvelopingAlgebra.LeftRegular R L) c) := by
  simp only [polynomialDiff, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

section Field
variable {K : Type*} [Field K] [CharZero K] [LieAlgebra K L] [LinearOrder I]
variable (b : Module.Basis I K L)
local notation "EKP" => ExteriorAlgebra K L ⊗[K] MvPolynomial I K

/-- Positive-degree acyclicity for the actual PBW-conjugated regular CE differential.
The primitive has exterior degree `q+1` and coefficient bound `n-1`; there is no
finite-dimensionality hypothesis and no assumed exactness or comparison theorem.
Proof reconstructed by induction on the coefficient bound using the concrete PBW/Koszul bridge. -/
theorem polynomial_positive_acyclic (q n : ℕ) (hq : 0 < q) {z : EKP}
    (hz : z ∈ rectangle q n) (hcycle : polynomialDiff b z = 0) :
    ∃ y ∈ rectangle (q + 1) (n - 1), polynomialDiff b y = z :=
  Koszul.exists_primitive_of_isLeadingKoszul b (isLeadingKoszul_polynomialDiff b)
    (polynomialDiff_squared b) q n hq hz hcycle
include b in
/-- Every positive-degree cycle for the actual left-regular CE differential is a boundary.
Reconstructed by finite PBW coefficient descent, then transported through the actual PBW
linear equivalence. The ordered basis may have an arbitrary, infinite index type. -/
theorem regular_positive_cycle_boundary (q : ℕ) (hq : 0 < q)
    {c : ExteriorAlgebra K L ⊗[K] UniversalEnvelopingAlgebra.LeftRegular K L}
    (hc : c ∈ chainsIn K L (UniversalEnvelopingAlgebra.LeftRegular K L) q)
    (hcycle : diff K L (UniversalEnvelopingAlgebra.LeftRegular K L) c = 0) :
    c ∈ boundaries K L (UniversalEnvelopingAlgebra.LeftRegular K L) q := by
  obtain ⟨t, rfl⟩ := hc
  obtain ⟨n, hn⟩ := exists_rectangle_pbw_incl b q t
  have hpc : polynomialDiff b (pbwTensor b
      (incl K L (UniversalEnvelopingAlgebra.LeftRegular K L) q t)) = 0 := by
    rw [polynomialDiff_pbwTensor, hcycle, map_zero]
  obtain ⟨y, hy, hdy⟩ := polynomial_positive_acyclic b q n hq hn hpc
  refine ⟨(pbwTensor b).symm y, pbwTensor_symm_mem_chainsIn b (q + 1) (n - 1) hy, ?_⟩
  apply (pbwTensor b).injective
  simpa only [polynomialDiff, LinearMap.comp_apply, LinearEquiv.coe_coe] using hdy

include b in
/-- Positive-degree cycles and boundaries coincide for the actual regular CE complex. -/
theorem regular_cycles_eq_boundaries (q : ℕ) (hq : 0 < q) :
    cycles K L (UniversalEnvelopingAlgebra.LeftRegular K L) q =
      boundaries K L (UniversalEnvelopingAlgebra.LeftRegular K L) q := by
  apply le_antisymm
  · intro c hc
    exact regular_positive_cycle_boundary b q hq hc.1 hc.2
  · exact boundaries_le_cycles q

include b in
/-- Actual chain-level regular CE acyclicity: every cycle in degree `q+1` has a
primitive in degree `q+2`. No comparison or vanishing assumption occurs. -/
theorem regular_positive_acyclic (q : ℕ)
    (c : ⋀[K]^(q + 1) L ⊗[K] UniversalEnvelopingAlgebra.LeftRegular K L)
    (hc : d K L (UniversalEnvelopingAlgebra.LeftRegular K L) q c = 0) :
    ∃ y : ⋀[K]^(q + 1 + 1) L ⊗[K] UniversalEnvelopingAlgebra.LeftRegular K L,
      d K L (UniversalEnvelopingAlgebra.LeftRegular K L) (q + 1) y = c := by
  have hb := regular_positive_cycle_boundary b (q + 1) (Nat.zero_lt_succ q)
    (c := incl K L (UniversalEnvelopingAlgebra.LeftRegular K L) (q + 1) c)
    ⟨c, rfl⟩ (by rw [← incl_d, hc, map_zero])
  obtain ⟨w, ⟨y, rfl⟩, hy⟩ := hb
  refine ⟨y, incl_injective (q + 1) ?_⟩
  rw [incl_d]
  exact hy
include b in
/-- Positive-degree regular CE homology vanishes, for arbitrary ordered basis index types. -/
theorem regular_subsingleton_homology (q : ℕ) (hq : 0 < q) :
    Subsingleton (homology K L (UniversalEnvelopingAlgebra.LeftRegular K L) q) := by
  apply (subsingleton_homology_iff K L (UniversalEnvelopingAlgebra.LeftRegular K L) q).mpr
  exact (regular_cycles_eq_boundaries b q hq).symm

end Field

end LieModule.ChevalleyEilenberg.CELeading

namespace LieModule.ChevalleyEilenberg

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

/-- Positive-degree homology of the left-regular enveloping module vanishes over a
characteristic-zero field, with no chosen basis or dimension restriction in the statement.
Reconstructed by choosing an ordered basis and applying the proved coefficient descent. -/
theorem subsingleton_homology_leftRegular (q : ℕ) (hq : 0 < q) :
    Subsingleton (homology K L (UniversalEnvelopingAlgebra.LeftRegular K L) q) := by
  let : LinearOrder (Module.Free.ChooseBasisIndex K L) :=
    IsWellOrder.linearOrder WellOrderingRel
  exact CELeading.regular_subsingleton_homology (Module.Free.chooseBasis K L) q hq

end LieModule.ChevalleyEilenberg

