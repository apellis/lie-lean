/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.DoubleEdgeOther

/-!
# Length-four double-edge braid relation

## Main results
* `doubleEdgeBraid_braid`: length-four equality of the published quotient homomorphisms.
* `doubleEdgeBraidEquiv_braid`: length-four equality of the published algebra equivalences.
* Explicit two-step transport and three-step recovery on both Chevalley colors.

The two nodes have Cartan entries `(-2,-1)`. The field and toral lattice are arbitrary.
Assumptions are `v ≠ 0`, `qᵢ - qᵢ⁻¹ ≠ 0`, and `qᵢ + qᵢ⁻¹ ≠ 0`; the other node's
parameter and denominator follow from the published symmetrizer lemmas. No braid
relation, faithful action, or coroot-span assumption is used.

## References
Reconstructed from the original presentation and the published image formulas.
No external primary source consulted. The toral lattice is arbitrary.
-/

noncomputable section
namespace QuantumGroup
variable {k : Type*} [Field k]
section Ring
variable {B : Type*} [Ring B] [Algebra k B]

set_option maxHeartbeats 4000000 in
-- Normal ordering expands mixed products and rational scalar coefficients.
private theorem four_lower_short (a b c u u' : B) (q : k) (hq : q ≠ 0)
    (hd : q - q⁻¹ ≠ 0) (hs : q + q⁻¹ ≠ 0)
    (hca : c * a = a * c - (q - q⁻¹)⁻¹ • (u - u'))
    (hcb : c * b = b * c)
    (hua : u * a = q ^ 2 • (a * u))
    (hub : u * b = q⁻¹ ^ 2 • (b * u))
    (hu'a : u' * a = q⁻¹ ^ 2 • (a * u'))
    (hu'b : u' * b = q ^ 2 • (b * u')) (hu'u : u' * u = 1) :
    let X := (q + q⁻¹)⁻¹ •
      (a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) + q⁻¹ ^ 2 • (b * a ^ 2))
    X * -(c * u) - q⁻¹ ^ 2 • (-(c * u) * X) =
      a * b - q⁻¹ ^ 2 • (b * a) := by
  have hca_assoc (z : B) := congrArg (fun x : B ↦ x * z) hca
  have hcb_assoc (z : B) := congrArg (fun x : B ↦ x * z) hcb
  have hua_assoc (z : B) := congrArg (fun x : B ↦ x * z) hua
  have hub_assoc (z : B) := congrArg (fun x : B ↦ x * z) hub
  have hu'a_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'a
  have hu'b_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'b
  simp only [mul_assoc, sub_mul, smul_mul_assoc] at *
  simp only [pow_two, mul_sub, sub_mul, mul_add, add_mul, mul_neg, neg_mul,
    mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_neg, mul_assoc,
    hua, hub, hca_assoc, hcb_assoc, hua_assoc, hub_assoc, hu'a_assoc, hu'b_assoc,
    hu'u, mul_one]
  have hn : -1 + q ^ 4 ≠ 0 := by
    have he : -1 + q ^ 4 = q ^ 2 * (q - q⁻¹) * (q + q⁻¹) := by
      field_simp
      ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq) hd) hs
  match_scalars <;> field_simp [hq, hd, hs, hn] <;> ring_nf <;>
    field_simp [hn] <;> ring

set_option maxHeartbeats 4000000 in
-- Normal ordering expands mixed products and rational scalar coefficients.
private theorem four_lower_long (a b c u u' : B) (q : k) (hq : q ≠ 0)
    (hd : q ^ 2 - (q ^ 2)⁻¹ ≠ 0)
    (hca : c * a = a * c)
    (hcb : c * b = b * c - (q ^ 2 - (q ^ 2)⁻¹)⁻¹ • (u - u'))
    (hua : u * a = q⁻¹ ^ 2 • (a * u))
    (hub : u * b = q ^ 4 • (b * u))
    (hu'a : u' * a = q ^ 2 • (a * u'))
    (hu'b : u' * b = q⁻¹ ^ 4 • (b * u')) (hu'u : u' * u = 1) :
    let X := b * a - q⁻¹ ^ 2 • (a * b)
    let A := -(c * u)
    X ^ 2 * A - ((q + q⁻¹) * q⁻¹) • (X * A * X) + q⁻¹ ^ 2 • (A * X ^ 2) =
      b * a ^ 2 - ((q + q⁻¹) * q⁻¹) • (a * b * a) + q⁻¹ ^ 2 • (a ^ 2 * b) := by
  have hca_assoc (z : B) := congrArg (fun x : B ↦ x * z) hca
  have hcb_assoc (z : B) := congrArg (fun x : B ↦ x * z) hcb
  have hua_assoc (z : B) := congrArg (fun x : B ↦ x * z) hua
  have hub_assoc (z : B) := congrArg (fun x : B ↦ x * z) hub
  have hu'a_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'a
  have hu'b_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'b
  simp only [mul_assoc, sub_mul, smul_mul_assoc] at *
  simp only [pow_two, mul_sub, sub_mul, add_mul, mul_neg, neg_mul,
    mul_smul_comm, smul_mul_assoc, smul_sub, smul_neg, mul_assoc,
    hua, hub, hca_assoc, hcb_assoc, hua_assoc, hub_assoc, hu'a_assoc, hu'b_assoc,
    hu'u, mul_one]
  have hn : -1 + q ^ 4 ≠ 0 := by
    have he : -1 + q ^ 4 = q ^ 2 * (q ^ 2 - (q ^ 2)⁻¹) := by
      field_simp
      ring
    rw [he]
    exact mul_ne_zero (pow_ne_zero _ hq) hd
  match_scalars <;> field_simp [hq, hd, hn] <;> ring_nf <;>
    field_simp [hn] <;> ring
end Ring

section Lattice
variable {I Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {i j : I}

/-- Length-four reflection relation on the entire lattice; reconstructed by expansion. -/
theorem reflY_braid_of_double_edge
    (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1) (μ : Y) :
    reflY R i (reflY R j (reflY R i (reflY R j μ))) =
      reflY R j (reflY R i (reflY R j (reflY R i μ))) := by
  simp only [reflY_apply, map_sub, map_zsmul, R.root_coroot, h, h',
    D.cartanMatrix_self]
  module
end Lattice

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j : I}

/-- The short-centre lowering identity in the actual quotient. Reconstructed by normal ordering. -/
theorem doubleEdge_four_lower_Ei (hv : v ≠ 0) (h : D.cartanMatrix i j = -2)
    (hd : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0) :
    braidEj R v i j * braidEi R i - (v ^ D.d i)⁻¹ ^ 2 •
      (braidEi R i * braidEj R v i j) =
      E R v i * E R v j - (v ^ D.d i)⁻¹ ^ 2 • (E R v j * E R v i) := by
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have hca : F R v i * E R v i = E R v i * F R v i -
      (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (Kt R v i - K R v (-ktilde R i)) := by
    have hc := E_mul_F_sub R v i i
    simp only [ite_true] at hc
    linear_combination (norm := module) -hc
  have hub : Kt R v i * E R v j =
      (v ^ D.d i)⁻¹ ^ 2 • (E R v j * Kt R v i) := by
    rw [Kt, K_mul_E, root_ktilde, h, mul_neg, zpow_neg, zpow_mul,
      zpow_natCast, zpow_ofNat, inv_pow]
  have hu'b : K R v (-ktilde R i) * E R v j =
      (v ^ D.d i) ^ 2 • (E R v j * K R v (-ktilde R i)) := by
    rw [K_mul_E, map_neg, root_ktilde, h, mul_neg, neg_neg, zpow_mul,
      zpow_natCast, zpow_ofNat]
  rw [braidEj_eq_of_cartanMatrix_eq_neg_two h]
  exact four_lower_short (E R v i) (E R v j) (F R v i)
    (Kt R v i) (K R v (-ktilde R i)) (v ^ D.d i) (pow_ne_zero _ hv) hd hs hca
    (E_mul_F_of_ne hij.symm).symm (Kt_mul_E i) hub
    (by simpa only [inv_pow] using K_neg_ktilde_mul_E (R := R) (v := v) i)
    hu'b (K_neg_mul_Kt i)

/-- The long-centre lowering identity in the actual quotient. Reconstructed by normal ordering. -/
theorem doubleEdge_four_lower_Ej (hv : v ≠ 0)
    (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1)
    (hd : v ^ D.d j - (v ^ D.d j)⁻¹ ≠ 0) :
    let q := v ^ D.d i
    let X := braidEj R v j i
    let A := braidEi (v := v) R j
    X ^ 2 * A - ((q + q⁻¹) * q⁻¹) • (X * A * X) + q⁻¹ ^ 2 • (A * X ^ 2) =
      E R v j * E R v i ^ 2 - ((q + q⁻¹) * q⁻¹) •
        (E R v i * E R v j * E R v i) + q⁻¹ ^ 2 • (E R v i ^ 2 * E R v j) := by
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have hp := parameter_eq_square_of_double_edge (v := v) h h'
  have hcb : F R v j * E R v j = E R v j * F R v j -
      (v ^ D.d j - (v ^ D.d j)⁻¹)⁻¹ • (Kt R v j - K R v (-ktilde R j)) := by
    have hc := E_mul_F_sub R v j j
    simp only [ite_true] at hc
    linear_combination (norm := module) -hc
  have hua : Kt R v j * E R v i =
      (v ^ D.d i)⁻¹ ^ 2 • (E R v i * Kt R v j) := by
    rw [Kt, K_mul_E, root_ktilde, h', mul_neg_one, zpow_neg,
      zpow_natCast, hp, inv_pow]
  have hu'a : K R v (-ktilde R j) * E R v i =
      (v ^ D.d i) ^ 2 • (E R v i * K R v (-ktilde R j)) := by
    rw [K_mul_E, map_neg, root_ktilde, h', mul_neg_one, neg_neg, zpow_natCast, hp]
  have hub := Kt_mul_E (R := R) (v := v) j
  have hu'b := K_neg_ktilde_mul_E (R := R) (v := v) j
  rw [hp, ← pow_mul] at hub
  rw [hp, ← pow_mul, ← inv_pow] at hu'b
  rw [hp] at hd hcb
  dsimp only
  rw [braidEj_eq_of_cartanMatrix_eq_neg_one h', hp, ← inv_pow]
  exact four_lower_long (E R v i) (E R v j) (F R v j)
    (Kt R v j) (K R v (-ktilde R j)) (v ^ D.d i) (pow_ne_zero _ hv) hd
    (E_mul_F_of_ne hij).symm hcb hua hub hu'a hu'b (K_neg_mul_Kt j)


/-- Negative short-centre lowering, obtained from the genuine Chevalley involution. -/
theorem doubleEdge_four_lower_Fi (hv : v ≠ 0) (h : D.cartanMatrix i j = -2)
    (hd : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0) :
    braidFi R i * braidFj R v i j - (v ^ D.d i) ^ 2 •
      (braidFj R v i j * braidFi R i) =
      F R v j * F R v i - (v ^ D.d i) ^ 2 • (F R v i * F R v j) := by
  have hc := congrArg (chevalley R v) (doubleEdge_four_lower_Ei (R := R) hv h hd hs)
  simp only [map_sub, map_mul, map_smul, chevalley_E,
    chevalley_braidEj_of_cartanMatrix_eq_neg_two hv h, chevalley_braidEi hv,
    smul_mul_assoc, mul_smul_comm, smul_smul] at hc
  have hn := pow_ne_zero (D.d i) hv
  calc
    _ = -(v ^ D.d i) ^ 2 • _ := ?_
    _ = _ := congrArg (fun z : QuantumGroup R v ↦ -(v ^ D.d i) ^ 2 • z) hc
    _ = _ := ?_
  all_goals
    simp only [smul_sub, smul_smul]
    match_scalars <;> field_simp

/-- Negative long-centre lowering, obtained from the genuine Chevalley involution. -/
theorem doubleEdge_four_lower_Fj (hv : v ≠ 0)
    (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1)
    (hd : v ^ D.d j - (v ^ D.d j)⁻¹ ≠ 0) :
    let q := v ^ D.d i
    let X := braidFj R v j i
    let A := braidFi (v := v) R j
    q ^ 2 • (X ^ 2 * A) - ((q + q⁻¹) * q) • (X * A * X) + A * X ^ 2 =
      q ^ 2 • (F R v j * F R v i ^ 2) - ((q + q⁻¹) * q) •
        (F R v i * F R v j * F R v i) + F R v i ^ 2 * F R v j := by
  have hc := congrArg (chevalley R v) (doubleEdge_four_lower_Ej (R := R) hv h h' hd)
  dsimp only at hc ⊢
  simp only [map_add, map_sub, map_mul, map_smul, map_pow, chevalley_E,
    chevalley_braidEj_of_cartanMatrix_eq_neg_one hv h', chevalley_braidEi hv,
    smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul,
    parameter_eq_square_of_double_edge (v := v) h h'] at hc
  have hn := pow_ne_zero (D.d i) hv
  calc
    _ = (v ^ D.d i) ^ 2 • _ := ?_
    _ = _ := congrArg (fun z : QuantumGroup R v ↦ (v ^ D.d i) ^ 2 • z) hc
    _ = _ := ?_
  all_goals
    simp only [smul_add, smul_sub, smul_smul]
    match_scalars <;> field_simp


variable [NeZero v]
  (i j : I) (hij : i ≠ j) (hall : ∀ l, l = i ∨ l = j)
  (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)
  (hqj : v ^ D.d j - (v ^ D.d j)⁻¹ ≠ 0)

local notation "Ti" => doubleEdgeBraid (R := R) i j hij hall h h' hq hs
local notation "Tj" => doubleEdgeOtherBraid (R := R) j i hij.symm
  (fun l ↦ Or.symm (hall l)) h' h hqj
local notation "TiInv" => doubleEdgeBraidInv (R := R) i j hij hall h h' hq hs
local notation "TjInv" => doubleEdgeOtherBraidInv (R := R) j i hij.symm
  (fun l ↦ Or.symm (hall l)) h' h hqj

/-- Two forward maps equal the other inverse on the first positive generator. -/
theorem doubleEdge_four_transport_Ei : Ti (Tj (E R v i)) = TjInv (E R v i) := by
  simp only [doubleEdgeOtherBraid_E, hij, ↓reduceIte,
    braidEj_eq_of_cartanMatrix_eq_neg_one h', map_sub, map_mul, map_smul,
    doubleEdgeBraid_E, hij.symm, ↓reduceIte, doubleEdgeOtherBraidInv_Ej,
    parameter_eq_square_of_double_edge (v := v) h h', ← inv_pow]
  simpa only [inv_pow] using doubleEdge_four_lower_Ei (R := R) (NeZero.ne v) h hq hs

/-- Two forward maps equal the other inverse on the first negative generator. -/
theorem doubleEdge_four_transport_Fi : Ti (Tj (F R v i)) = TjInv (F R v i) := by
  simp only [doubleEdgeOtherBraid_F, hij, ↓reduceIte,
    braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h', map_sub, map_mul, map_smul,
    doubleEdgeBraid_F, hij.symm, ↓reduceIte, doubleEdgeOtherBraidInv_Fj,
    parameter_eq_square_of_double_edge (v := v) h h']
  exact doubleEdge_four_lower_Fi (NeZero.ne v) h hq hs

/-- Two forward maps equal the other inverse on the second positive generator. -/
theorem doubleEdge_four_transport_Ej : Tj (Ti (E R v j)) = TiInv (E R v j) := by
  simp only [doubleEdgeBraid_E, hij.symm, ↓reduceIte,
    braidEj_eq_of_cartanMatrix_eq_neg_two h, map_add, map_sub, map_mul, map_smul, map_pow,
    doubleEdgeOtherBraid_E, hij, ↓reduceIte, doubleEdgeBraidInv_Ej]
  exact congrArg (fun z : QuantumGroup R v ↦ (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ • z)
    (doubleEdge_four_lower_Ej (NeZero.ne v) h h' hqj)

/-- Two forward maps equal the other inverse on the second negative generator. -/
theorem doubleEdge_four_transport_Fj : Tj (Ti (F R v j)) = TiInv (F R v j) := by
  simp only [doubleEdgeBraid_F, hij.symm, ↓reduceIte,
    braidFj_eq_of_cartanMatrix_eq_neg_two (NeZero.ne v) h,
    map_add, map_sub, map_mul, map_smul, map_pow,
    doubleEdgeOtherBraid_F, hij, ↓reduceIte, doubleEdgeBraidInv_Fj]
  exact congrArg (fun z : QuantumGroup R v ↦ (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ • z)
    (doubleEdge_four_lower_Fj (NeZero.ne v) h h' hqj)

/-- The alternating three-map word fixes the first positive generator. -/
theorem doubleEdge_four_triple_Ei : Tj (Ti (Tj (E R v i))) = E R v i := by
  rw [doubleEdge_four_transport_Ei i j hij hall h h' hq hs hqj]
  exact DFunLike.congr_fun
    (doubleEdgeOtherBraid_comp_doubleEdgeOtherBraidInv j i hij.symm
      (fun l ↦ Or.symm (hall l)) h' h hqj) (E R v i)

/-- The alternating three-map word fixes the first negative generator. -/
theorem doubleEdge_four_triple_Fi : Tj (Ti (Tj (F R v i))) = F R v i := by
  rw [doubleEdge_four_transport_Fi i j hij hall h h' hq hs hqj]
  exact DFunLike.congr_fun
    (doubleEdgeOtherBraid_comp_doubleEdgeOtherBraidInv j i hij.symm
      (fun l ↦ Or.symm (hall l)) h' h hqj) (F R v i)

/-- The alternating three-map word fixes the second positive generator. -/
theorem doubleEdge_four_triple_Ej : Ti (Tj (Ti (E R v j))) = E R v j := by
  rw [doubleEdge_four_transport_Ej i j hij hall h h' hq hs hqj]
  exact DFunLike.congr_fun
    (doubleEdgeBraid_comp_doubleEdgeBraidInv i j hij hall h h' hq hs) (E R v j)

/-- The alternating three-map word fixes the second negative generator. -/
theorem doubleEdge_four_triple_Fj : Ti (Tj (Ti (F R v j))) = F R v j := by
  rw [doubleEdge_four_transport_Fj i j hij hall h h' hq hs hqj]
  exact DFunLike.congr_fun
    (doubleEdgeBraid_comp_doubleEdgeBraidInv i j hij hall h h' hq hs) (F R v j)


omit [DecidableEq I] in
include h h' in
/-- The triple reflection at the other node fixes the first symmetrized coroot. -/
theorem reflY_triple_ktilde_of_double_edge_left :
    reflY R j (reflY R i (reflY R j (ktilde R i))) = ktilde R i := by
  have hc : reflY R j (reflY R i (reflY R j (R.coroot i))) = R.coroot i := by
    simp only [reflY_apply, map_sub, map_zsmul, R.root_coroot, h, h',
      D.cartanMatrix_self]
    module
  simpa only [ktilde, map_nsmul] using congrArg (fun μ : Y ↦ D.d i • μ) hc

omit [DecidableEq I] in
include h h' in
/-- The triple reflection at the first node fixes the second symmetrized coroot. -/
theorem reflY_triple_ktilde_of_double_edge_right :
    reflY R i (reflY R j (reflY R i (ktilde R j))) = ktilde R j := by
  have hc : reflY R i (reflY R j (reflY R i (R.coroot j))) = R.coroot j := by
    simp only [reflY_apply, map_sub, map_zsmul, R.root_coroot, h, h',
      D.cartanMatrix_self]
    module
  simpa only [ktilde, map_nsmul] using congrArg (fun μ : Y ↦ D.d j • μ) hc

/-- The fourfold words agree on the first positive generator. -/
theorem doubleEdge_four_Ei : Ti (Tj (Ti (Tj (E R v i)))) =
    Tj (Ti (Tj (Ti (E R v i)))) := by
  rw [doubleEdge_four_triple_Ei i j hij hall h h' hq hs hqj]
  simp only [doubleEdgeBraid_E, ↓reduceIte, braidEi, map_neg, map_mul, Kt,
    doubleEdgeBraid_K, doubleEdgeOtherBraid_K,
    doubleEdge_four_triple_Fi i j hij hall h h' hq hs hqj,
    reflY_triple_ktilde_of_double_edge_left i j h h']

/-- The fourfold words agree on the first negative generator. -/
theorem doubleEdge_four_Fi : Ti (Tj (Ti (Tj (F R v i)))) =
    Tj (Ti (Tj (Ti (F R v i)))) := by
  rw [doubleEdge_four_triple_Fi i j hij hall h h' hq hs hqj]
  simp only [doubleEdgeBraid_F, ↓reduceIte, braidFi, map_neg, map_mul,
    doubleEdgeBraid_K, doubleEdgeOtherBraid_K,
    doubleEdge_four_triple_Ei i j hij hall h h' hq hs hqj,
    reflY_triple_ktilde_of_double_edge_left i j h h']

/-- The fourfold words agree on the second positive generator. -/
theorem doubleEdge_four_Ej : Ti (Tj (Ti (Tj (E R v j)))) =
    Tj (Ti (Tj (Ti (E R v j)))) := by
  rw [doubleEdge_four_triple_Ej i j hij hall h h' hq hs hqj]
  simp only [doubleEdgeOtherBraid_E, ↓reduceIte, braidEi, map_neg, map_mul, Kt,
    doubleEdgeBraid_K, doubleEdgeOtherBraid_K,
    doubleEdge_four_triple_Fj i j hij hall h h' hq hs hqj,
    reflY_triple_ktilde_of_double_edge_right i j h h']

/-- The fourfold words agree on the second negative generator. -/
theorem doubleEdge_four_Fj : Ti (Tj (Ti (Tj (F R v j)))) =
    Tj (Ti (Tj (Ti (F R v j)))) := by
  rw [doubleEdge_four_triple_Fj i j hij hall h h' hq hs hqj]
  simp only [doubleEdgeOtherBraid_F, ↓reduceIte, braidFi, map_neg, map_mul,
    doubleEdgeBraid_K, doubleEdgeOtherBraid_K,
    doubleEdge_four_triple_Ej i j hij hall h h' hq hs hqj,
    reflY_triple_ktilde_of_double_edge_right i j h h']


/-- The two published double-edge quotient maps satisfy the actual length-four braid relation.
Reconstructed by checking both positive and negative colors and every toral lattice generator.
Only the short-node sum and difference are assumed; the other denominator is derived. -/
theorem doubleEdgeBraid_braid :
    let Si := doubleEdgeBraid (R := R) i j hij hall h h' hq hs
    let Sj := doubleEdgeOtherBraid (R := R) j i hij.symm (fun l ↦ (hall l).symm) h' h
      (parameter_sub_inv_ne_zero_of_double_edge (NeZero.ne v) h h' hq hs)
    Si.comp (Sj.comp (Si.comp Sj)) = Sj.comp (Si.comp (Sj.comp Si)) := by
  dsimp only
  have hd := parameter_sub_inv_ne_zero_of_double_edge (NeZero.ne v) h h' hq hs
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · rcases hall l with hl | hl
    · subst l
      exact doubleEdge_four_Ei i j hij hall h h' hq hs hd
    · subst l
      exact doubleEdge_four_Ej i j hij hall h h' hq hs hd
  · rcases hall l with hl | hl
    · subst l
      exact doubleEdge_four_Fi i j hij hall h h' hq hs hd
    · subst l
      exact doubleEdge_four_Fj i j hij hall h h' hq hs hd
  · simp only [AlgHom.comp_apply, doubleEdgeBraid_K, doubleEdgeOtherBraid_K,
      reflY_braid_of_double_edge h h']

/-- The actual published algebra equivalences satisfy the length-four braid relation.
Reconstructed from the quotient-map equality, with arbitrary field and toral lattice. -/
theorem doubleEdgeBraidEquiv_braid :
    let Si := doubleEdgeBraidEquiv (R := R) i j hij hall h h' hq hs
    let Sj := doubleEdgeOtherBraidEquiv (R := R) j i hij.symm
      (fun l ↦ (hall l).symm) h' h
      (parameter_sub_inv_ne_zero_of_double_edge (NeZero.ne v) h h' hq hs)
    ((Si.trans Sj).trans Si).trans Sj = ((Sj.trans Si).trans Sj).trans Si := by
  apply DFunLike.ext
  intro x
  exact (DFunLike.congr_fun (doubleEdgeBraid_braid i j hij hall h h' hq hs) x).symm

end QuantumGroup
