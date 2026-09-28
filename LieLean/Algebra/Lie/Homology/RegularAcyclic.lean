/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.LeadingDifferential
import LieLean.LinearAlgebra.ExteriorAlgebra.KoszulExact
import LieLean.LinearAlgebra.ExteriorAlgebra.KoszulSupport

/-!
# Positive-degree acyclicity of the actual left-regular CE complex

## Main results

* `polynomial_cycle_lowering`: a concrete negative Koszul primitive kills the top coefficient
  degree, leaving a genuine cycle of strictly smaller coefficient bound.
* `polynomial_positive_acyclic`: induction terminates, with primitive coefficient bound `n-1`.
* `regular_positive_acyclic`: actual chain-level acyclicity after PBW transport.
* `regular_subsingleton_homology`: positive-degree regular CE homology vanishes.

The base field has characteristic zero; the ordered Lie-algebra basis may have arbitrary index
 type. No finite-dimensionality, projectivity argument, assumed comparison, or assumed vanishing.

## References

Arguments reconstructed from polynomial coefficients, tensor spans, the existing actual PBW
bridge, and the proved concrete Koszul homotopy. No external source was consulted.
-/
noncomputable section
open scoped TensorProduct BigOperators
open TensorProduct ExteriorAlgebra
namespace LieModule.ChevalleyEilenberg.CELeading
variable {R L I : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
local notation "P" => MvPolynomial I R
local notation "EP" => ExteriorAlgebra R L ⊗[R] P

/-- Projection to polynomial degree `n`, leaving exterior degree unchanged. -/
def polynomialTop (n : ℕ) : Module.End R EP :=
  TensorProduct.map LinearMap.id (MvPolynomial.homogeneousComponent n)

@[simp] theorem polynomialTop_tmul (n : ℕ) (e : ExteriorAlgebra R L) (p : P) :
    polynomialTop n (e ⊗ₜ[R] p) = e ⊗ₜ[R] MvPolynomial.homogeneousComponent n p := rfl

/-- Every homogeneous pure-tensor span lies in the corresponding rectangle. -/
theorem homogeneousTensors_le_rectangle (b : Module.Basis I R L) (s : Finset I)
    (n q : ℕ) : Koszul.homogeneousTensors b s n q ≤ rectangle q n := by
  apply Submodule.span_le.mpr
  rintro z ⟨l, p, hl, _, hp, _, rfl⟩
  exact tmul_mem (hl ▸ Koszul.basisWord_mem_exteriorPower b l)
    ((MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hp.totalDegree_le)

/-- The top component of a rectangle belongs to the full homogeneous tensor span. -/
theorem polynomialTop_mem_iSup (b : Module.Basis I R L) (q m n : ℕ) {z : EP}
    (hz : z ∈ rectangle q m) :
    polynomialTop n z ∈ ⨆ s : Finset I, Koszul.homogeneousTensors b s n q := by
  rw [Koszul.iSup_homogeneousTensors]
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, he, p, _, rfl⟩ := hz
    exact Submodule.subset_span ⟨e, MvPolynomial.homogeneousComponent n p, he,
      MvPolynomial.homogeneousComponent_isHomogeneous n p, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx

/-- Projection acts as identity on the supported homogeneous span. -/
theorem polynomialTop_eq_self (b : Module.Basis I R L) (s : Finset I) (n q : ℕ)
    {z : EP} (hz : z ∈ Koszul.homogeneousTensors b s n q) : polynomialTop n z = z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, p, _, _, hp, _, rfl⟩ := hz
    simp only [polynomialTop_tmul, MvPolynomial.homogeneousComponent_eq_self hp]
  | zero => exact map_zero _
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, hx]

/-- Projection above the coefficient bound vanishes. -/
theorem polynomialTop_eq_zero {q m n : ℕ} (hmn : m < n) {z : EP}
    (hz : z ∈ rectangle q m) : polynomialTop n z = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, _, p, hp, rfl⟩ := hz
    rw [polynomialTop_tmul, MvPolynomial.homogeneousComponent_eq_zero n p
      (lt_of_le_of_lt ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hp) hmn), tmul_zero]
  | zero => exact map_zero _
  | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
  | smul r x _ hx => simp only [map_smul, hx, smul_zero]

/-- Removing the degree-`n+1` component lowers the polynomial bound to `n`. -/
theorem sub_homogeneousComponent_mem (n : ℕ) (p : P)
    (hp : p ∈ MvPolynomial.restrictTotalDegree I R (n + 1)) :
    p - MvPolynomial.homogeneousComponent (n + 1) p ∈
      MvPolynomial.restrictTotalDegree I R n := by
  classical
  rw [MvPolynomial.mem_restrictTotalDegree, MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro d hd
  have hne := MvPolynomial.mem_support_iff.mp hd
  change p.coeff d - (MvPolynomial.homogeneousComponent (n + 1) p).coeff d ≠ 0 at hne
  rw [MvPolynomial.coeff_homogeneousComponent] at hne
  have hdeg : d.degree ≠ n + 1 := by
    intro h
    exact hne (by simp [h])
  have hcoeff : p.coeff d ≠ 0 := by simpa [hdeg] using hne
  have hbound := (MvPolynomial.mem_restrictTotalDegree _ _ _).mp hp
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff] at hbound
  have hdle := hbound d (MvPolynomial.mem_support_iff.mpr hcoeff)
  change d.degree ≤ n
  change d.degree ≤ n + 1 at hdle
  omega

/-- Removing the top component of a rectangle strictly lowers its coefficient bound. -/
theorem sub_polynomialTop_mem (q n : ℕ) {z : EP} (hz : z ∈ rectangle q (n + 1)) :
    z - polynomialTop (n + 1) z ∈ rectangle q n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, he, p, hp, rfl⟩ := hz
    rw [polynomialTop_tmul, ← tmul_sub]
    exact tmul_mem he (sub_homogeneousComponent_mem n p hp)
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [map_add, add_sub_add_comm] using add_mem hx hy
  | smul r x _ hx =>
    simpa only [map_smul, smul_sub] using Submodule.smul_mem _ r hx

/-- Multiplication by a variable shifts the polynomial projection by one. -/
theorem homogeneousComponent_X_mul (n : ℕ) (i : I) (p : P) :
    MvPolynomial.homogeneousComponent (n + 1) (MvPolynomial.X i * p) =
      MvPolynomial.X i * MvPolynomial.homogeneousComponent n p := by
  classical
  ext d
  by_cases hi : i ∈ d.support
  · have hle : Finsupp.single i 1 ≤ d := by
      simpa only [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero,
        ← Finsupp.mem_support_iff] using hi
    obtain ⟨a, rfl⟩ := exists_add_of_le hle
    simp only [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_X_mul]
    congr 1
    simp only [map_add, Finsupp.degree_single]
    apply propext
    omega
  · simp [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_X_mul', hi]

/-- The actual finite Koszul differential commutes with degree projection with shift one. -/
theorem polynomialTop_delta (b : Module.Basis I R L) (s : Finset I) (n : ℕ) (z : EP) :
    polynomialTop (n + 1) (Koszul.delta b s z) =
      Koszul.delta b s (polynomialTop n z) := by
  induction z with
  | tmul e p =>
    simp only [Koszul.delta, LinearMap.sum_apply, Koszul.deltaTerm_tmul, map_sum,
      polynomialTop_tmul, homogeneousComponent_X_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The highest homogeneous piece of a genuine CE cycle is a Koszul cycle.
The only support hypothesis is the concrete supported bounded-degree span. -/
theorem delta_polynomialTop_eq_zero [LinearOrder I] (b : Module.Basis I R L)
    (s : Finset I) (q n : ℕ) {z : EP} (hz : z ∈ supportedTensors b s q n)
    (hcycle : polynomialDiff b z = 0) : Koszul.delta b s (polynomialTop n z) = 0 := by
  have he := polynomialDiff_add_delta_mem b s q n z hz
  rw [hcycle, zero_add] at he
  rw [← polynomialTop_delta]
  exact polynomialTop_eq_zero (Nat.lt_succ_self n) he

/-- Positive-degree form of strict coefficient descent. -/
theorem sub_polynomialTop_mem_pred (q n : ℕ) (hn : 0 < n) {z : EP}
    (hz : z ∈ rectangle q n) : z - polynomialTop n z ∈ rectangle q (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using sub_polynomialTop_mem q m hz

/-- Every bounded tensor splits into a lower-degree tensor and a supported homogeneous top. -/
theorem rectangle_decomposition (b : Module.Basis I R L) (q n : ℕ) {z : EP}
    (hz : z ∈ rectangle q (n + 1)) :
    ∃ (y t : EP) (s : Finset I), y ∈ rectangle q n ∧
      t ∈ Koszul.homogeneousTensors b s (n + 1) q ∧ z = y + t := by
  have ht := polynomialTop_mem_iSup b q (n + 1) (n + 1) hz
  rw [Koszul.iSup_homogeneousTensors] at ht
  obtain ⟨s, hs⟩ := Koszul.exists_support_of_mem_homogeneous_span b (n + 1) q ht
  exact ⟨z - polynomialTop (n + 1) z, polynomialTop (n + 1) z, s,
    sub_polynomialTop_mem q n hz, hs, (sub_add_cancel z _).symm⟩

/-- Every homogeneous span lies in its concrete coefficient-degree rectangle. -/
theorem iSup_homogeneousTensors_le_rectangle (b : Module.Basis I R L) (q n : ℕ) :
    (⨆ s : Finset I, Koszul.homogeneousTensors b s n q) ≤ rectangle q n := by
  rw [Koszul.iSup_homogeneousTensors]
  refine Submodule.span_le.mpr ?_
  rintro z ⟨e, p, he, hp, rfl⟩
  exact tmul_mem he (by rw [MvPolynomial.mem_restrictTotalDegree]; exact hp.totalDegree_le)

/-- Projection onto degree zero is the identity on the degree-zero rectangle. -/
theorem polynomialTop_zero_eq_self (q : ℕ) {z : EP}
    (hz : z ∈ rectangle q 0) : polynomialTop 0 z = z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, _, p, hp, rfl⟩ := hz
    rw [MvPolynomial.mem_restrictTotalDegree] at hp
    have hp0 : p.IsHomogeneous 0 := by
      rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous]
      exact Nat.eq_zero_of_le_zero hp
    rw [polynomialTop_tmul, MvPolynomial.homogeneousComponent_eq_self hp0]
  | zero => exact map_zero _
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, hx]

/-- Bounded exterior support is monotone. -/
theorem supportedTensors_mono [LinearOrder I] (b : Module.Basis I R L) (q n : ℕ)
    {s t : Finset I} (hst : s ⊆ t) : supportedTensors b s q n ≤ supportedTensors b t q n := by
  apply Submodule.span_mono
  rintro z ⟨l, p, hl, hs, hp, hz⟩
  exact ⟨l, p, hl, fun i hi => hst (hs i hi), hp, hz⟩

/-- Every homogeneous supported tensor has the corresponding bounded support. -/
theorem homogeneousTensors_le_supportedTensors [LinearOrder I] (b : Module.Basis I R L)
    (s : Finset I) (n q : ℕ) :
    Koszul.homogeneousTensors b s n q ≤ supportedTensors b s q n := by
  apply Submodule.span_le.mpr
  rintro z ⟨l, p, hl, hs, hp, _, rfl⟩
  exact Submodule.subset_span ⟨l, p, hl, hs,
    (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hp.totalDegree_le, rfl⟩

/-- Every bounded rectangle tensor has finite exterior coordinate support. -/
theorem exists_support_rectangle [LinearOrder I] (b : Module.Basis I R L) (q n : ℕ)
    {z : EP} (hz : z ∈ rectangle q n) : ∃ s, z ∈ supportedTensors b s q n := by
  classical
  have hall : rectangle (R := R) (L := L) (I := I) q n ≤ ⨆ s, supportedTensors b s q n := by
    apply Submodule.span_le.mpr
    rintro z ⟨e, he, p, hp, rfl⟩
    rw [← exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top R q L b.span_eq] at he
    induction he using Submodule.span_induction with
    | mem e he =>
      obtain ⟨v, hv, rfl⟩ := he
      have hv' : ∀ j, ∃ i, b i = v j := fun j => hv ⟨j, rfl⟩
      choose f hf using hv'
      let l := List.ofFn f
      have heq : ExteriorAlgebra.ιMulti R q v = Koszul.basisWord b l := by
        simp only [ExteriorAlgebra.ιMulti_apply, Koszul.basisWord, l, List.map_ofFn]
        congr 2
        funext j
        exact congrArg (ι R) (hf j).symm
      rw [heq]
      apply Submodule.mem_iSup_of_mem l.toFinset
      exact Submodule.subset_span ⟨l, p, by simp [l], fun i hi => by simpa using hi, hp, rfl⟩
    | zero => simp
    | add e f _ _ he hf => rw [add_tmul]; exact add_mem he hf
    | smul r e _ he => rw [← smul_tmul']; exact Submodule.smul_mem _ r he
  apply (Submodule.mem_iSup_of_directed _ ?_).mp (hall hz)
  intro s t
  exact ⟨s ∪ t, supportedTensors_mono b q n Finset.subset_union_left,
    supportedTensors_mono b q n Finset.subset_union_right⟩

/-- Common finite support for a tensor and its homogeneous top. -/
theorem exists_common_support [LinearOrder I] (b : Module.Basis I R L) (q n : ℕ)
    {z : EP} (hz : z ∈ rectangle q n) :
    ∃ s, z ∈ supportedTensors b s q n ∧
      polynomialTop n z ∈ Koszul.homogeneousTensors b s n q := by
  classical
  obtain ⟨s, hs⟩ := exists_support_rectangle b q n hz
  have ht := polynomialTop_mem_iSup b q n n hz
  rw [Koszul.iSup_homogeneousTensors] at ht
  obtain ⟨t, ht⟩ := Koszul.exists_support_of_mem_homogeneous_span b n q ht
  exact ⟨s ∪ t, supportedTensors_mono b q n Finset.subset_union_left hs,
    Koszul.homogeneousTensors_mono b n q Finset.subset_union_right ht⟩

/-- The conjugated actual CE differential squares to zero. -/
theorem polynomialDiff_squared [LinearOrder I] (b : Module.Basis I R L) (z : EP) :
    polynomialDiff b (polynomialDiff b z) = 0 := by
  simp only [polynomialDiff, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, diff_diff, map_zero]

/-- Coefficient rectangles are increasing in their degree bound. -/
theorem rectangle_mono (q : ℕ) {n m : ℕ} (hnm : n ≤ m) :
    rectangle (R := R) (L := L) (I := I) q n ≤ rectangle q m := by
  apply Submodule.span_le.mpr
  rintro z ⟨e, he, p, hp, rfl⟩
  apply tmul_mem he
  rw [MvPolynomial.mem_restrictTotalDegree] at hp ⊢
  exact hp.trans hnm

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
    exact tmul_mem e.2 ((MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl)
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

/-- Genuine coefficient-bound descent for actual CE cycles: the negative Koszul primitive
kills the leading term and leaves a cycle with strictly smaller coefficient bound.
The argument is reconstructed from PBW, the proved leading differential and Koszul homotopy. -/
theorem polynomial_cycle_lowering (q n : ℕ) (hq : 0 < q) {z : EKP}
    (hz : z ∈ rectangle q (n + 1)) (hcycle : polynomialDiff b z = 0) :
    ∃ y ∈ rectangle (q + 1) n,
      z - polynomialDiff b y ∈ rectangle q n ∧
      polynomialDiff b (z - polynomialDiff b y) = 0 := by
  obtain ⟨s, hs, ht⟩ := exists_common_support b q (n + 1) hz
  have htop := delta_polynomialTop_eq_zero b s q (n + 1) hs hcycle
  obtain ⟨y, hy, hdy⟩ := Koszul.exists_homogeneous_primitive b s (n + 1) q
    (polynomialTop (n + 1) z) ht htop (by omega)
  have hy' : y ∈ Koszul.homogeneousTensors b s n (q + 1) := by simpa using hy
  have herror := polynomialDiff_add_delta_mem b s (q + 1) n y
    (homogeneousTensors_le_supportedTensors b s n (q + 1) hy')
  rw [hdy, Nat.add_sub_cancel] at herror
  refine ⟨-y, neg_mem (homogeneousTensors_le_rectangle b s n (q + 1) hy'), ?_, ?_⟩
  · have hlower := add_mem (sub_polynomialTop_mem q n hz) herror
    simpa only [map_neg, sub_neg_eq_add, sub_add_add_cancel] using hlower
  · simp only [map_sub, polynomialDiff_squared, hcycle, sub_zero]

/-- Positive-exterior-degree actual CE cycles with constant coefficients vanish. -/
theorem polynomial_cycle_zero_bound (q : ℕ) (hq : 0 < q) {z : EKP}
    (hz : z ∈ rectangle q 0) (hcycle : polynomialDiff b z = 0) : z = 0 := by
  obtain ⟨s, hs, ht⟩ := exists_common_support b q 0 hz
  have htop := delta_polynomialTop_eq_zero b s q 0 hs hcycle
  rw [polynomialTop_zero_eq_self q hz] at ht htop
  exact Koszul.eq_zero_of_cycle_polynomial_degree_zero b s q z ht htop hq

/-- Positive-degree acyclicity for the actual PBW-conjugated regular CE differential.
The primitive has exterior degree `q+1` and coefficient bound `n-1`; there is no
finite-dimensionality hypothesis and no assumed exactness or comparison theorem.
Proof reconstructed by induction on the coefficient bound using the concrete PBW/Koszul bridge. -/
theorem polynomial_positive_acyclic (q n : ℕ) (hq : 0 < q) {z : EKP}
    (hz : z ∈ rectangle q n) (hcycle : polynomialDiff b z = 0) :
    ∃ y ∈ rectangle (q + 1) (n - 1), polynomialDiff b y = z := by
  induction n generalizing z with
  | zero =>
    have heq := polynomial_cycle_zero_bound b q hq hz hcycle
    exact ⟨0, Submodule.zero_mem _, by simpa only [map_zero] using heq.symm⟩
  | succ n ih =>
    obtain ⟨y, hy, hr, hrc⟩ := polynomial_cycle_lowering b q n hq hz hcycle
    obtain ⟨w, hw, hdw⟩ := ih hr hrc
    refine ⟨y + w, ?_, ?_⟩
    · simpa only [Nat.succ_sub_one] using add_mem hy
        (rectangle_mono (q + 1) (Nat.sub_le n 1) hw)
    · rw [map_add, hdw]
      abel
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

