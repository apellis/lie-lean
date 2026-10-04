/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.QBinomial
import LieLean.Algebra.QuantumGroup.PBW.OrderedSpan
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

/-!
# Commutation relations of the G₂ root vectors

Let `e, f` be elements of a `k`-algebra satisfying the two quantum Serre relations of type `G₂`
with `e` short: `S₄(e, f) = 0` with parameter `q` and `S₂(f, e) = 0` with parameter `q³`. Put
`x₁ = ef - q⁻³fe`, `x₂ = ex₁ - q⁻¹x₁e`, `x₃ = ex₂ - qx₂e`, `z = x₂x₁ - qx₁x₂` (the root vectors
along `i j i j i j`, up to scalars) and `y₁ = fe - q⁻³ef`, `y₂ = y₁e - q⁻¹ey₁`, `y₃ = y₁y₂ - qy₂y₁`,
`w = y₂e - qey₂` (the root vectors along `j i j i j i`, up to scalars). We prove the commutation
relations of Levendorskii–Soibelman type between the first letter of each word and the later
root vectors that are not immediate from the definitions:

* `x₃e = q⁻³ex₃`, `ze = ez + b x₂²` (`G2PBW.x3_mul_e`, `G2PBW.z_mul_e`);
* `y₁f = q⁻³fy₁`, `y₃f = q⁻³fy₃ + b y₁³`, `y₂f = fy₂ + b y₁²`, `wf = q³fw + b y₃ + b' y₁y₂`
  (`G2PBW.y1_mul_f`, `G2PBW.y3_mul_f`, `G2PBW.y2_mul_f`, `G2PBW.w_mul_f`).

Together with the defining relations of the `xₘ`, `yₘ` these give the relations
`OrderedSpan.BaseRel` between the first letter and all later letters, for the root vectors
along both words up to nonzero scalars (`G2PBW.baseRel_fwd`, `G2PBW.baseRel_rev`).

Each relation above is an explicit linear combination of two-sided multiples of the Serre
relations (found by computer and checked here by normalization); the only denominators are
powers of `q` and `q² + 1`.

## References

Our own computation.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

namespace G2PBW

variable {k B : Type*} [Field k] [Ring B] [Algebra k B] (q : k) (e f : B)

/-- `x₁ = ef - q⁻³fe`. -/
def x1 : B := e * f - (q ^ 3)⁻¹ • (f * e)

/-- `x₂ = ex₁ - q⁻¹x₁e`. -/
def x2 : B := e * x1 q e f - q⁻¹ • (x1 q e f * e)

/-- `x₃ = ex₂ - qx₂e`. -/
def x3 : B := e * x2 q e f - q • (x2 q e f * e)

/-- `z = x₂x₁ - qx₁x₂`. -/
def z : B := x2 q e f * x1 q e f - q • (x1 q e f * x2 q e f)

/-- `y₁ = fe - q⁻³ef`. -/
def y1 : B := f * e - (q ^ 3)⁻¹ • (e * f)

/-- `y₂ = y₁e - q⁻¹ey₁`. -/
def y2 : B := y1 q e f * e - q⁻¹ • (e * y1 q e f)

/-- `y₃ = y₁y₂ - qy₂y₁`. -/
def y3 : B := y1 q e f * y2 q e f - q • (y2 q e f * y1 q e f)

/-- `w = y₂e - qey₂`. -/
def w : B := y2 q e f * e - q • (e * y2 q e f)

variable {q e f}
variable (hq : q ≠ 0) (hS4 : qSerre q 4 e f = 0) (hS2 : qSerre (q ^ 3) 2 f e = 0)

include hq hS4 in
/-- The quartic Serre relation: `x₃e = q⁻³ex₃`. -/
theorem x3_mul_e :
    x3 q e f * e = (q ^ 3)⁻¹ • (e * x3 q e f) := by
  have key : x3 q e f * e - ((q ^ 3)⁻¹ • (e * x3 q e f)) =
      (-1 / q ^ 3) • ((qSerre q 4 e f)) := by
    simp only [x1, x2, x3, qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial]
    simp only [pow_succ, pow_zero, one_mul, mul_one, mul_add, mul_sub, sub_mul, smul_sub,
      smul_add, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, zero_add, Nat.sub_zero,
      Nat.sub_self, Nat.add_one_sub_one]
    match_scalars <;> (field_simp; try ring)
  rw [← sub_eq_zero, key, hS4]
  simp

include hq hS4 hS2 in
/-- `ze = ez - (q⁶ - 1)/(q(q² + 1)) x₂²`. -/
theorem z_mul_e (hq2 : (q ^ 2 + 1) ≠ 0) :
    z q e f * e = e * z q e f + (-(q ^ 6 - 1) / (q * (q ^ 2 + 1))) • (x2 q e f * x2 q e f) := by
  have key : z q e f * e - (e * z q e f + (-(q ^ 6 - 1) / (q * (q ^ 2 +
      1))) • (x2 q e f * x2 q e f)) =
      (q / (q ^ 2 + 1)) • ((qSerre q 4 e f) * f) +
        (-1 / (q ^ 5 * (q ^ 2 + 1))) • (f * ((qSerre q 4 e f))) +
        (1 / (q ^ 5 * (q ^ 2 + 1))) • ((qSerre (q ^ 3) 2 f e) * (e * (e * e))) +
        (-(q ^ 4 + q ^ 2 + 1) / (q ^ 5 * (q ^ 2 + 1))) •
          (e * ((qSerre (q ^ 3) 2 f e) * (e * e))) +
        ((q ^ 4 + q ^ 2 + 1) / (q ^ 3 * (q ^ 2 + 1))) • (e * e * ((qSerre (q ^ 3) 2 f e) * e)) +
        (-q / (q ^ 2 + 1)) • (e * (e * e) * ((qSerre (q ^ 3) 2 f e))) := by
    simp only [x1, x2, z, qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial]
    simp only [pow_succ, pow_zero, one_mul, mul_one, mul_add, add_mul, mul_sub, sub_mul, smul_sub,
      smul_add, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, zero_add, Nat.sub_zero,
      Nat.sub_self, Nat.add_one_sub_one]
    match_scalars <;> (field_simp; try ring)
  rw [← sub_eq_zero, key, hS2, hS4]
  simp

include hq hS2 in
/-- The quadratic Serre relation: `y₁f = q⁻³fy₁`. -/
theorem y1_mul_f :
    y1 q e f * f = (q ^ 3)⁻¹ • (f * y1 q e f) := by
  have key : y1 q e f * f - ((q ^ 3)⁻¹ • (f * y1 q e f)) =
      (-1 / q ^ 3) • ((qSerre (q ^ 3) 2 f e)) := by
    simp only [y1, qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial]
    simp only [pow_succ, pow_zero, one_mul, mul_one, mul_add, mul_sub, sub_mul, smul_sub,
      smul_add, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, zero_add, Nat.sub_zero,
      Nat.sub_self, Nat.add_one_sub_one]
    match_scalars <;> (field_simp; try ring)
  rw [← sub_eq_zero, key, hS2]
  simp

include hq hS2 in
/-- `y₃f = q⁻³fy₃ - (q² - 1)²(q² + 1)/q³ y₁³`. -/
theorem y3_mul_f :
    y3 q e f * f = (q ^ 3)⁻¹ • (f * y3 q e f) + (-(q ^ 2 - 1) ^ 2 * (q ^ 2 +
        1) / q ^ 3) • (y1 q e f * (y1 q e f * y1 q e f)) := by
  have key : y3 q e f * f - ((q ^ 3)⁻¹ • (f * y3 q e f) + (-(q ^ 2 - 1) ^ 2 * (q ^ 2 +
      1) / q ^ 3) • (y1 q e f * (y1 q e f * y1 q e f))) =
      (-1 / q ^ 3) • ((qSerre (q ^ 3) 2 f e) * (f * (e * e))) +
        (-1) • (f * e * ((qSerre (q ^ 3) 2 f e) * e)) +
        ((q ^ 2 + 1) / q ^ 4) • (f * (e * e) * ((qSerre (q ^ 3) 2 f e))) +
        ((q ^ 4 + q ^ 2 + 1) / q ^ 6) • ((qSerre (q ^ 3) 2 f e) * (e * (f * e))) +
        (-1 / q ^ 6) • (e * ((qSerre (q ^ 3) 2 f e) * (f * e))) +
        (1 / q ^ 3) • (e * f * ((qSerre (q ^ 3) 2 f e) * e)) +
        (-(q ^ 4 + q ^ 2 + 1) / q ^ 7) • (e * (f * e) * ((qSerre (q ^ 3) 2 f e))) +
        (-(q ^ 2 + 1) / q ^ 7) • ((qSerre (q ^ 3) 2 f e) * (e * (e * f))) +
        (1 / q ^ 9) • (e * ((qSerre (q ^ 3) 2 f e) * (e * f))) +
        (1 / q ^ 6) • (e * (e * f) * ((qSerre (q ^ 3) 2 f e))) := by
    simp only [y1, y2, y3, qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial]
    simp only [pow_succ, pow_zero, one_mul, mul_one, mul_add, add_mul, mul_sub, sub_mul, smul_sub,
      smul_add, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, zero_add, Nat.sub_zero,
      Nat.sub_self, Nat.add_one_sub_one]
    match_scalars <;> (field_simp; try ring)
  rw [← sub_eq_zero, key, hS2]
  simp

include hq hS2 in
/-- `y₂f = fy₂ - (q⁴ - 1)/q y₁²`. -/
theorem y2_mul_f :
    y2 q e f * f = f * y2 q e f + (-(q ^ 4 - 1) / q) • (y1 q e f * y1 q e f) := by
  have key : y2 q e f * f - (f * y2 q e f + (-(q ^ 4 - 1) / q) • (y1 q e f * y1 q e f)) =
      (-1) • ((qSerre (q ^ 3) 2 f e) * e) +
        (1 / q ^ 4) • (e * ((qSerre (q ^ 3) 2 f e))) := by
    simp only [y1, y2, qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial]
    simp only [pow_succ, pow_zero, one_mul, mul_one, mul_add, add_mul, mul_sub, sub_mul, smul_sub,
      smul_add, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, zero_add, Nat.sub_zero,
      Nat.sub_self, Nat.add_one_sub_one]
    match_scalars <;> (field_simp; try ring)
  rw [← sub_eq_zero, key, hS2]
  simp

include hq hS2 in
/-- `wf = q³fw + (q⁴ + q² - 1)y₃ - (q⁶ - 1)y₁y₂`. -/
theorem w_mul_f :
    w q e f * f = q ^ 3 • (f * w q e f) + (q ^ 4 + q ^ 2 - 1) • y3 q e f +
        (-(q ^ 6 - 1)) • (y1 q e f * y2 q e f) := by
  have key : w q e f * f - (q ^ 3 • (f * w q e f) + (q ^ 4 + q ^ 2 - 1) • y3 q e f +
      (-(q ^ 6 - 1)) • (y1 q e f * y2 q e f)) =
      (-q ^ 3) • ((qSerre (q ^ 3) 2 f e) * (e * e)) +
        ((q ^ 2 + 1) / q) • (e * ((qSerre (q ^ 3) 2 f e) * e)) +
        (-1 / q ^ 3) • (e * e * ((qSerre (q ^ 3) 2 f e))) := by
    simp only [y1, y2, y3, w, qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial]
    simp only [pow_succ, pow_zero, one_mul, mul_one, mul_add, add_mul, mul_sub, sub_mul, smul_sub,
      smul_add, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, zero_add, Nat.sub_zero,
      Nat.sub_self, Nat.add_one_sub_one]
    match_scalars <;> (field_simp; try ring)
  rw [← sub_eq_zero, key, hS2]
  simp

/-! ### Generation -/

variable (q e f) in
lemma x1_mem : x1 q e f ∈ Algebra.adjoin k {e, f} := by
  have he : e ∈ Algebra.adjoin k {e, f} := Algebra.subset_adjoin (by simp)
  have hf : f ∈ Algebra.adjoin k {e, f} := Algebra.subset_adjoin (by simp)
  exact sub_mem (mul_mem he hf) (Subalgebra.smul_mem _ (mul_mem hf he) _)

variable (q e f) in
lemma x2_mem : x2 q e f ∈ Algebra.adjoin k {e, f} := by
  have he : e ∈ Algebra.adjoin k {e, f} := Algebra.subset_adjoin (by simp)
  exact sub_mem (mul_mem he (x1_mem q e f)) (Subalgebra.smul_mem _ (mul_mem (x1_mem q e f) he) _)

variable (q e f) in
lemma x3_mem : x3 q e f ∈ Algebra.adjoin k {e, f} := by
  have he : e ∈ Algebra.adjoin k {e, f} := Algebra.subset_adjoin (by simp)
  exact sub_mem (mul_mem he (x2_mem q e f)) (Subalgebra.smul_mem _ (mul_mem (x2_mem q e f) he) _)

variable (q e f) in
lemma z_mem : z q e f ∈ Algebra.adjoin k {e, f} :=
  sub_mem (mul_mem (x2_mem q e f) (x1_mem q e f))
    (Subalgebra.smul_mem _ (mul_mem (x1_mem q e f) (x2_mem q e f)) _)

variable (q e f) in
lemma y1_mem : y1 q e f ∈ Algebra.adjoin k {e, f} := by
  have he : e ∈ Algebra.adjoin k {e, f} := Algebra.subset_adjoin (by simp)
  have hf : f ∈ Algebra.adjoin k {e, f} := Algebra.subset_adjoin (by simp)
  exact sub_mem (mul_mem hf he) (Subalgebra.smul_mem _ (mul_mem he hf) _)

variable (q e f) in
lemma y2_mem : y2 q e f ∈ Algebra.adjoin k {e, f} := by
  have he : e ∈ Algebra.adjoin k {e, f} := Algebra.subset_adjoin (by simp)
  exact sub_mem (mul_mem (y1_mem q e f) he) (Subalgebra.smul_mem _ (mul_mem he (y1_mem q e f)) _)

variable (q e f) in
lemma y3_mem : y3 q e f ∈ Algebra.adjoin k {e, f} :=
  sub_mem (mul_mem (y1_mem q e f) (y2_mem q e f))
    (Subalgebra.smul_mem _ (mul_mem (y2_mem q e f) (y1_mem q e f)) _)

variable (q e f) in
lemma w_mem : w q e f ∈ Algebra.adjoin k {e, f} := by
  have he : e ∈ Algebra.adjoin k {e, f} := Algebra.subset_adjoin (by simp)
  exact sub_mem (mul_mem (y2_mem q e f) he) (Subalgebra.smul_mem _ (mul_mem he (y2_mem q e f)) _)

/-! ### The relations with the first letter -/

open OrderedSpan

lemma smul_wordProd_mem {n : ℕ} (y : Fin n → B) {a b : Fin n} (κ : k) (u : List (Fin n))
    (hu : u.Pairwise (· ≤ ·)) (hab : ∀ m ∈ u, a < m ∧ m < b) :
    κ • wordProd y u ∈ innerSpan k y a b :=
  Submodule.smul_mem _ κ (Submodule.subset_span ⟨u, hu, hab, rfl⟩)

include hq hS4 hS2 in
/-- The relations between `e` and the later root vectors along `i j i j i j` (up to nonzero
scalars `s₂, c₃, c₄, c₅`). -/
theorem baseRel_fwd (hq2 : q ^ 2 + 1 ≠ 0) {s2 c3 c4 c5 : k} (hs2 : s2 ≠ 0) (hc3 : c3 ≠ 0)
    (hc5 : c5 ≠ 0) :
    BaseRel k ![e, s2 • x3 q e f, c3 • x2 q e f, c4 • z q e f, c5 • x1 q e f, f] := by
  set V : Fin 6 → B := ![e, s2 • x3 q e f, c3 • x2 q e f, c4 • z q e f, c5 • x1 q e f, f]
  intro l
  fin_cases l
  · refine ⟨(q ^ 3)⁻¹, ?_⟩
    change (s2 • x3 q e f) * e - (q ^ 3)⁻¹ • (e * (s2 • x3 q e f)) ∈ innerSpan k V 0 1
    rw [smul_mul_assoc, mul_smul_comm, x3_mul_e hq hS4, smul_comm, sub_self]
    exact zero_mem _
  · refine ⟨q⁻¹, ?_⟩
    change (c3 • x2 q e f) * e - q⁻¹ • (e * (c3 • x2 q e f)) ∈ innerSpan k V 0 2
    have hw : wordProd V [1] = s2 • x3 q e f := mul_one _
    convert smul_wordProd_mem V (a := 0) (b := 2) (-(c3 * q⁻¹ * s2⁻¹)) [1] (by decide)
      (by decide) using 1
    rw [hw, x3]
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
    match_scalars <;> (field_simp; try ring)
  · refine ⟨1, ?_⟩
    change (c4 • z q e f) * e - (1 : k) • (e * (c4 • z q e f)) ∈ innerSpan k V 0 3
    have hw : wordProd V [2, 2] = (c3 • x2 q e f) * ((c3 • x2 q e f) * 1) := rfl
    convert smul_wordProd_mem V (a := 0) (b := 3)
      (c4 * (-(q ^ 6 - 1) / (q * (q ^ 2 + 1))) / c3 ^ 2) [2, 2] (by decide) (by decide) using 1
    rw [hw, smul_mul_assoc, mul_smul_comm, z_mul_e hq hS4 hS2 hq2]
    simp only [mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    match_scalars <;> (field_simp; try ring)
  · refine ⟨q, ?_⟩
    change (c5 • x1 q e f) * e - q • (e * (c5 • x1 q e f)) ∈ innerSpan k V 0 4
    have hw : wordProd V [2] = c3 • x2 q e f := mul_one _
    convert smul_wordProd_mem V (a := 0) (b := 4) (-(c5 * q / c3)) [2] (by decide)
      (by decide) using 1
    rw [hw, x2]
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul]
    match_scalars <;> (field_simp; try ring)
  · refine ⟨q ^ 3, ?_⟩
    change f * e - q ^ 3 • (e * f) ∈ innerSpan k V 0 5
    have hw : wordProd V [4] = c5 • x1 q e f := mul_one _
    convert smul_wordProd_mem V (a := 0) (b := 5) (-(q ^ 3 / c5)) [4] (by decide)
      (by decide) using 1
    rw [hw, x1]
    simp only [smul_sub, smul_smul]
    match_scalars <;> (field_simp; try ring)

include hq hS2 in
/-- The relations between `f` and the later root vectors along `j i j i j i` (up to nonzero
scalars `s₂, c₃, c₅`). -/
theorem baseRel_rev {s2 c3 c5 : k} (hs2 : s2 ≠ 0) (hc3 : c3 ≠ 0) :
    BaseRel k ![f, y1 q e f, s2 • y3 q e f, c3 • y2 q e f, c5 • w q e f, e] := by
  set V : Fin 6 → B := ![f, y1 q e f, s2 • y3 q e f, c3 • y2 q e f, c5 • w q e f, e]
  intro l
  fin_cases l
  · refine ⟨(q ^ 3)⁻¹, ?_⟩
    change y1 q e f * f - (q ^ 3)⁻¹ • (f * y1 q e f) ∈ innerSpan k V 0 1
    rw [y1_mul_f hq hS2, sub_self]
    exact zero_mem _
  · refine ⟨(q ^ 3)⁻¹, ?_⟩
    change (s2 • y3 q e f) * f - (q ^ 3)⁻¹ • (f * (s2 • y3 q e f)) ∈ innerSpan k V 0 2
    have hw : wordProd V [1, 1, 1] = y1 q e f * (y1 q e f * (y1 q e f * 1)) := rfl
    convert smul_wordProd_mem V (a := 0) (b := 2)
      (s2 * (-(q ^ 2 - 1) ^ 2 * (q ^ 2 + 1) / q ^ 3)) [1, 1, 1] (by decide) (by decide) using 1
    rw [hw, smul_mul_assoc, mul_smul_comm, y3_mul_f hq hS2]
    simp only [mul_one, smul_add, smul_smul]
    match_scalars <;> (field_simp; try ring)
  · refine ⟨1, ?_⟩
    change (c3 • y2 q e f) * f - (1 : k) • (f * (c3 • y2 q e f)) ∈ innerSpan k V 0 3
    have hw : wordProd V [1, 1] = y1 q e f * (y1 q e f * 1) := rfl
    convert smul_wordProd_mem V (a := 0) (b := 3) (c3 * (-(q ^ 4 - 1) / q)) [1, 1] (by decide)
      (by decide) using 1
    rw [hw, smul_mul_assoc, mul_smul_comm, y2_mul_f hq hS2]
    simp only [mul_one, smul_add, smul_smul]
    match_scalars <;> (field_simp; try ring)
  · refine ⟨q ^ 3, ?_⟩
    change (c5 • w q e f) * f - q ^ 3 • (f * (c5 • w q e f)) ∈ innerSpan k V 0 4
    have hw2 : wordProd V [2] = s2 • y3 q e f := mul_one _
    have hw13 : wordProd V [1, 3] = y1 q e f * ((c3 • y2 q e f) * 1) := rfl
    convert add_mem (smul_wordProd_mem V (a := 0) (b := 4) (c5 * (q ^ 4 + q ^ 2 - 1) / s2) [2]
      (by decide) (by decide)) (smul_wordProd_mem V (a := 0) (b := 4) (c5 * (-(q ^ 6 - 1)) / c3)
      [1, 3] (by decide) (by decide)) using 1
    rw [hw2, hw13, smul_mul_assoc, mul_smul_comm, w_mul_f hq hS2]
    simp only [mul_one, smul_add, smul_smul, mul_smul_comm]
    match_scalars <;> (field_simp; try ring)
  · refine ⟨q ^ 3, ?_⟩
    change e * f - q ^ 3 • (f * e) ∈ innerSpan k V 0 5
    have hw : wordProd V [1] = y1 q e f := mul_one _
    convert smul_wordProd_mem V (a := 0) (b := 5) (-(q ^ 3)) [1] (by decide) (by decide) using 1
    rw [hw, y1]
    simp only [smul_sub, smul_smul]
    match_scalars <;> (field_simp; try ring)

end G2PBW

end LieLean.QuantumGroup
