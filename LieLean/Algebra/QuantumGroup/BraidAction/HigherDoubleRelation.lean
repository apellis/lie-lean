/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.NonterminalDouble
import LieLean.Algebra.QuantumGroup.BraidAction.DoubleEdgeRelation

/-!
# Higher-rank double-edge braid relations

## Main results
External-generator certificates and actual quotient-map relations.

## References
Reconstructed from the repository's NonterminalDouble, TerminalDouble,
TerminalDoubleOther, DoubleEdgeRelation, SimplyLacedRelations and Artin sources.
No rank-two exhaustion is imposed.
-/

open LieLean
noncomputable section
namespace LieLean.QuantumGroup
section Polynomial
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- The short-side external-generator certificate uses only the original simple Serre relation. -/
theorem higherDouble_short_polynomial (a b c : B) (q : k) (hq : q ≠ 0)
    (hS : qSerre q 2 a c = 0) (hbc : Commute b c) :
    (a * b - q⁻¹ ^ 2 • (b * a)) * (a * c - q⁻¹ • (c * a)) -
        q⁻¹ • ((a * c - q⁻¹ • (c * a)) * (a * b - q⁻¹ ^ 2 • (b * a))) =
      a * ((b * a - q⁻¹ ^ 2 • (a * b)) * c -
        q⁻¹ • (c * (b * a - q⁻¹ ^ 2 • (a * b)))) -
      q⁻¹ • (((b * a - q⁻¹ ^ 2 • (a * b)) * c -
        q⁻¹ • (c * (b * a - q⁻¹ ^ 2 • (a * b)))) * a) := by
  have h0 := congrArg (fun z : B ↦ z * b) hS
  have h1 := congrArg (fun z : B ↦ b * z) hS
  have hcb (z : B) : c * (b * z) = b * (c * z) := by
    rw [← mul_assoc, hbc.symm.eq, mul_assoc]
  simp only [qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial,
    Nat.reduceSub, pow_succ, pow_zero, mul_one, one_mul, mul_zero, zero_mul, add_zero,
    zero_add, one_smul, mul_neg, neg_mul, neg_neg, mul_sub, sub_mul, mul_add,
    add_mul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul,
    mul_assoc, hbc.symm.eq, hcb] at h0 h1 ⊢
  linear_combination (norm := (match_scalars <;> field_simp [hq] <;> ring))
    q⁻¹ ^ 2 • h0 - q⁻¹ ^ 2 • h1

set_option maxHeartbeats 2000000 in
-- The degree-five certificate expands both scalar and noncommutative products.
/-- The long-side external certificate uses the two original quadratic Serre relations.
The explicitly cancelled scalar is the long-node quantum sum. -/
theorem higherDouble_long_polynomial (a b c : B) (q : k) (hq : q ≠ 0)
    (hS : qSerre (q ^ 2) 2 b a = 0) (hU : qSerre (q ^ 2) 2 b c = 0)
    (hac : Commute a c) (hs : q ^ 2 + (q ^ 2)⁻¹ ≠ 0) :
    let X := b * a ^ 2 - ((q + q⁻¹) * q⁻¹) • (a * b * a) +
      q⁻¹ ^ 2 • (a ^ 2 * b)
    let U := a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) +
      q⁻¹ ^ 2 • (b * a ^ 2)
    X * (b * c - q⁻¹ ^ 2 • (c * b)) -
        q⁻¹ ^ 2 • ((b * c - q⁻¹ ^ 2 • (c * b)) * X) =
      b * (U * c - q⁻¹ ^ 2 • (c * U)) -
        q⁻¹ ^ 2 • ((U * c - q⁻¹ ^ 2 • (c * U)) * b) := by
  dsimp only
  have h0 := congrArg (fun z : B ↦ a * z * c) hS
  have h1 := congrArg (fun z : B ↦ a * c * z) hS
  have h2 := congrArg (fun z : B ↦ z * a * c) hS
  have h3 := congrArg (fun z : B ↦ c * z * a) hS
  have h4 := congrArg (fun z : B ↦ a * a * z) hU
  have h5 := congrArg (fun z : B ↦ z * a * a) hU
  have hca (z : B) : c * (a * z) = a * (c * z) := by
    rw [← mul_assoc, hac.symm.eq, mul_assoc]
  apply (smul_right_injective (M := B) hs)
  simp only [qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial,
    Nat.reduceSub, pow_succ, pow_zero, mul_one, one_mul, mul_zero, zero_mul, add_zero,
    zero_add, one_smul, mul_neg, neg_mul, neg_neg, mul_sub, sub_mul, mul_add,
    add_mul, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_smul,
    mul_assoc, hac.symm.eq, hca] at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination (norm := (match_scalars <;> field_simp [hq] <;> ring))
    (1 + q⁻¹ ^ 2) • h0 - (q⁻¹ ^ 6 + q⁻¹ ^ 4) • h1 -
      (1 + q⁻¹ ^ 2) • h2 + (q⁻¹ ^ 6 + q⁻¹ ^ 4) • h3 +
      (q⁻¹ ^ 4 - q⁻¹ ^ 2) • h4 + (q⁻¹ ^ 2 - q⁻¹ ^ 4) • h5

/-- Opposite-algebra transport of the short-side certificate, for negative generators. -/
theorem higherDouble_short_polynomial_right (a b c : B) (q : k) (hq : q ≠ 0)
    (hS : qSerre q 2 a c = 0) (hbc : Commute b c) :
    (c * a - q • (a * c)) * (b * a - q ^ 2 • (a * b)) -
        q • ((b * a - q ^ 2 • (a * b)) * (c * a - q • (a * c))) =
      (c * (a * b - q ^ 2 • (b * a)) -
        q • ((a * b - q ^ 2 • (b * a)) * c)) * a -
      q • (a * (c * (a * b - q ^ 2 • (b * a)) -
        q • ((a * b - q ^ 2 • (b * a)) * c))) := by
  have hSop : qSerre q⁻¹ 2 (MulOpposite.op a) (MulOpposite.op c) = 0 := by
    rw [qSerre_inv, qSerre_op, hS, MulOpposite.op_zero, smul_zero]
  have hh := higherDouble_short_polynomial (MulOpposite.op a) (MulOpposite.op b)
    (MulOpposite.op c) q⁻¹ (inv_ne_zero hq) hSop hbc.op
  simpa only [inv_inv, MulOpposite.unop_mul, MulOpposite.unop_sub,
    MulOpposite.unop_smul, MulOpposite.unop_op] using congrArg MulOpposite.unop hh

/-- Opposite-algebra transport of the long-side certificate, for negative generators. -/
theorem higherDouble_long_polynomial_right (a b c : B) (q : k) (hq : q ≠ 0)
    (hS : qSerre (q ^ 2) 2 b a = 0) (hU : qSerre (q ^ 2) 2 b c = 0)
    (hac : Commute a c) (hs : q ^ 2 + (q ^ 2)⁻¹ ≠ 0) :
    let X := q ^ 2 • (b * a ^ 2) - ((q + q⁻¹) * q) • (a * b * a) + a ^ 2 * b
    let U := q ^ 2 • (a ^ 2 * b) - ((q + q⁻¹) * q) • (a * b * a) + b * a ^ 2
    (c * b - q ^ 2 • (b * c)) * X -
        q ^ 2 • (X * (c * b - q ^ 2 • (b * c))) =
      (c * U - q ^ 2 • (U * c)) * b -
        q ^ 2 • (b * (c * U - q ^ 2 • (U * c))) := by
  have hSop : qSerre (q⁻¹ ^ 2) 2 (MulOpposite.op b) (MulOpposite.op a) = 0 := by
    rw [inv_pow, qSerre_inv, qSerre_op, hS, MulOpposite.op_zero, smul_zero]
  have hUop : qSerre (q⁻¹ ^ 2) 2 (MulOpposite.op b) (MulOpposite.op c) = 0 := by
    rw [inv_pow, qSerre_inv, qSerre_op, hU, MulOpposite.op_zero, smul_zero]
  have hs' : q⁻¹ ^ 2 + (q⁻¹ ^ 2)⁻¹ ≠ 0 := by simpa only [inv_pow, inv_inv, add_comm] using hs
  have hh := higherDouble_long_polynomial (MulOpposite.op a) (MulOpposite.op b)
    (MulOpposite.op c) q⁻¹ (inv_ne_zero hq) hSop hUop hac.op hs'
  have hh' := congrArg MulOpposite.unop hh
  dsimp only at hh' ⊢
  simp only [inv_inv, MulOpposite.unop_mul, MulOpposite.unop_add, MulOpposite.unop_sub,
    MulOpposite.unop_smul, MulOpposite.unop_pow, MulOpposite.unop_op, mul_assoc] at hh'
  convert hh' using 1 <;> noncomm_ring

end Polynomial

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]

/-- Exactly the graph and scalar hypotheses of the published local double-edge map.
This contains no transformed relations or composition identities. -/
structure HigherDoubleData (D : LusztigCartanDatum I) (v : k) (i : I) : Prop where
  edge : ∀ j, j ≠ i → D.cartanMatrix i j = 0 ∨
    (D.cartanMatrix i j = -1 ∧
      (D.cartanMatrix j i = -1 ∨ D.cartanMatrix j i = -2)) ∨
    (D.cartanMatrix i j = -2 ∧ D.cartanMatrix j i = -1)
  leaf : ∀ j l, j ≠ i → l ≠ i →
    D.cartanMatrix i j ≠ 0 → D.cartanMatrix i l ≠ 0 →
    j ≠ l → D.cartanMatrix j l = 0
  unique : ∀ j l, D.cartanMatrix i j = -2 → D.cartanMatrix i l = -2 → j = l
  path : ∀ j l, D.cartanMatrix i j ≠ 0 → D.cartanMatrix i l = 0 →
    D.cartanMatrix j l = 0 ∨ (D.cartanMatrix j l = -1 ∧ D.cartanMatrix l j = -1)
  diff : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0
  sum : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0
  cycl : (1 + (v ^ D.d i)⁻¹ ^ 4) *
    (1 + (v ^ D.d i)⁻¹ ^ 2 + (v ^ D.d i)⁻¹ ^ 4) ≠ 0
  cube : (v ^ D.d i) ^ 4 + (v ^ D.d i) ^ 2 + 1 ≠ 0

variable (i j : I) (Hi : HigherDoubleData D v i) (Hj : HigherDoubleData D v j)
  (hij : i ≠ j) (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1)

local notation "Ti" => nonterminalDoubleBraid (R := R) i
  Hi.edge Hi.leaf Hi.unique Hi.path Hi.diff Hi.sum Hi.cycl Hi.cube
local notation "Tj" => nonterminalDoubleBraid (R := R) j
  Hj.edge Hj.leaf Hj.unique Hj.path Hj.diff Hj.sum Hj.cycl Hj.cube
local notation "TiInv" => nonterminalDoubleBraidInv (R := R) i
  Hi.edge Hi.leaf Hi.unique Hi.path Hi.diff Hi.sum Hi.cycl Hi.cube
local notation "TjInv" => nonterminalDoubleBraidInv (R := R) j
  Hj.edge Hj.leaf Hj.unique Hj.path Hj.diff Hj.sum Hj.cycl Hj.cube

include hij h h'

/-- Two forward maps equal the other inverse on the first positive generator. -/
theorem higherDouble_transport_Ei : Ti (Tj (E R v i)) = TjInv (E R v i) := by
  simp only [nonterminalDoubleBraid_E, hij, ↓reduceIte,
    braidEj_eq_of_cartanMatrix_eq_neg_one h', map_sub, map_mul, map_smul,
    nonterminalDoubleBraid_E, hij.symm, ↓reduceIte, nonterminalDoubleBraidInv_Ej j
      Hj.edge Hj.leaf Hj.unique Hj.path Hj.diff Hj.sum Hj.cycl Hj.cube i hij h',
    parameter_eq_square_of_double_edge (v := v) h h', ← inv_pow]
  simpa only [inv_pow] using doubleEdge_four_lower_Ei (R := R) (NeZero.ne v) h Hi.diff Hi.sum

/-- Two forward maps equal the other inverse on the first negative generator. -/
theorem higherDouble_transport_Fi : Ti (Tj (F R v i)) = TjInv (F R v i) := by
  simp only [nonterminalDoubleBraid_F, hij, ↓reduceIte,
    braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h', map_sub, map_mul, map_smul,
    nonterminalDoubleBraid_F, hij.symm, ↓reduceIte, nonterminalDoubleBraidInv_Fj j
      Hj.edge Hj.leaf Hj.unique Hj.path Hj.diff Hj.sum Hj.cycl Hj.cube i hij h',
    parameter_eq_square_of_double_edge (v := v) h h']
  exact doubleEdge_four_lower_Fi (NeZero.ne v) h Hi.diff Hi.sum

/-- Two forward maps equal the other inverse on the second positive generator. -/
theorem higherDouble_transport_Ej : Tj (Ti (E R v j)) = TiInv (E R v j) := by
  simp only [nonterminalDoubleBraid_E, hij.symm, ↓reduceIte,
    braidEj_eq_of_cartanMatrix_eq_neg_two h, map_add, map_sub, map_mul, map_smul, map_pow,
    nonterminalDoubleBraid_E, hij, ↓reduceIte, nonterminalDoubleBraidInv_Ej_two i
      Hi.edge Hi.leaf Hi.unique Hi.path Hi.diff Hi.sum Hi.cycl Hi.cube j hij.symm h]
  exact congrArg (fun z : QuantumGroup R v ↦ (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ • z)
    (doubleEdge_four_lower_Ej (NeZero.ne v) h h' Hj.diff)

/-- Two forward maps equal the other inverse on the second negative generator. -/
theorem higherDouble_transport_Fj : Tj (Ti (F R v j)) = TiInv (F R v j) := by
  simp only [nonterminalDoubleBraid_F, hij.symm, ↓reduceIte,
    braidFj_eq_of_cartanMatrix_eq_neg_two (NeZero.ne v) h,
    map_add, map_sub, map_mul, map_smul, map_pow,
    nonterminalDoubleBraid_F, hij, ↓reduceIte, nonterminalDoubleBraidInv_Fj_two i
      Hi.edge Hi.leaf Hi.unique Hi.path Hi.diff Hi.sum Hi.cycl Hi.cube j hij.symm h]
  exact congrArg (fun z : QuantumGroup R v ↦ (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ • z)
    (doubleEdge_four_lower_Fj (NeZero.ne v) h h' Hj.diff)

/-- The alternating three-map word fixes the first positive generator. -/
theorem higherDouble_triple_Ei : Tj (Ti (Tj (E R v i))) = E R v i := by
  rw [higherDouble_transport_Ei i j Hi Hj hij h h']
  exact DFunLike.congr_fun
    (nonterminalDoubleBraid_comp_nonterminalDoubleBraidInv j
      Hj.edge Hj.leaf Hj.unique Hj.path Hj.diff Hj.sum Hj.cycl Hj.cube) (E R v i)

/-- The alternating three-map word fixes the first negative generator. -/
theorem higherDouble_triple_Fi : Tj (Ti (Tj (F R v i))) = F R v i := by
  rw [higherDouble_transport_Fi i j Hi Hj hij h h']
  exact DFunLike.congr_fun
    (nonterminalDoubleBraid_comp_nonterminalDoubleBraidInv j
      Hj.edge Hj.leaf Hj.unique Hj.path Hj.diff Hj.sum Hj.cycl Hj.cube) (F R v i)

/-- The alternating three-map word fixes the second positive generator. -/
theorem higherDouble_triple_Ej : Ti (Tj (Ti (E R v j))) = E R v j := by
  rw [higherDouble_transport_Ej i j Hi Hj hij h h']
  exact DFunLike.congr_fun
    (nonterminalDoubleBraid_comp_nonterminalDoubleBraidInv i
      Hi.edge Hi.leaf Hi.unique Hi.path Hi.diff Hi.sum Hi.cycl Hi.cube) (E R v j)

/-- The alternating three-map word fixes the second negative generator. -/
theorem higherDouble_triple_Fj : Ti (Tj (Ti (F R v j))) = F R v j := by
  rw [higherDouble_transport_Fj i j Hi Hj hij h h']
  exact DFunLike.congr_fun
    (nonterminalDoubleBraid_comp_nonterminalDoubleBraidInv i
      Hi.edge Hi.leaf Hi.unique Hi.path Hi.diff Hi.sum Hi.cycl Hi.cube) (F R v j)


/-- Length-four equality on an external positive generator adjacent to the short node.
Only local diagram conditions are assumed; the actual quotient maps are used. -/
theorem higherDouble_four_E_short (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hil : D.cartanMatrix i l = -1) (hjl : D.cartanMatrix j l = 0) :
    Ti (Tj (Ti (Tj (E R v l)))) = Tj (Ti (Tj (Ti (E R v l)))) := by
  have hiEl : Ti (E R v l) =
      E R v i * E R v l - (v ^ D.d i)⁻¹ • (E R v l * E R v i) := by
    simp [hli, braidEj_eq_of_cartanMatrix_eq_neg_one hil]
  have hjEl : Tj (E R v l) = E R v l := by
    simp [hlj, braidEj_eq_of_cartanMatrix_eq_zero hjl]
  have ht : Ti (Tj (Ti (E R v l))) =
      Ti (Tj (E R v i)) * Ti (E R v l) -
        (v ^ D.d i)⁻¹ • (Ti (E R v l) * Ti (Tj (E R v i))) := by
    rw [hiEl]
    simp only [map_sub, map_mul, map_smul, hjEl, hiEl]
  rw [hjEl, ht, map_sub, map_mul, map_smul, map_mul,
    higherDouble_triple_Ei i j Hi Hj hij h h']
  rw [higherDouble_transport_Ei i j Hi Hj hij h h',
    nonterminalDoubleBraidInv_Ej j Hj.edge Hj.leaf Hj.unique Hj.path
      Hj.diff Hj.sum Hj.cycl Hj.cube i hij h', hiEl]
  simp only [map_sub, map_mul, map_smul, hjEl, nonterminalDoubleBraid_E,
    hij, ↓reduceIte, braidEj_eq_of_cartanMatrix_eq_neg_one h',
    parameter_eq_square_of_double_edge (v := v) h h']
  have hS : qSerre (v ^ D.d i) 2 (E R v i) (E R v l) = 0 := by
    simpa only [hil, Int.reduceSub, Int.reduceToNat] using serre_E R v hli.symm
  simpa only [inv_pow] using higherDouble_short_polynomial
    (E R v i) (E R v j) (E R v l) (v ^ D.d i) (pow_ne_zero _ (NeZero.ne v))
    hS (E_commute_E_of_cartanMatrix_eq_zero hjl)

/-- Length-four equality on an external negative generator adjacent to the short node.
Only local diagram conditions are assumed; the actual quotient maps are used. -/
theorem higherDouble_four_F_short (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hil : D.cartanMatrix i l = -1) (hjl : D.cartanMatrix j l = 0) :
    Ti (Tj (Ti (Tj (F R v l)))) = Tj (Ti (Tj (Ti (F R v l)))) := by
  have hiFl : Ti (F R v l) =
      F R v l * F R v i - (v ^ D.d i) • (F R v i * F R v l) := by
    simp [hli, braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hil]
  have hjFl : Tj (F R v l) = F R v l := by
    simp [hlj, braidFj_eq_of_cartanMatrix_eq_zero hjl]
  have ht : Ti (Tj (Ti (F R v l))) =
      Ti (F R v l) * Ti (Tj (F R v i)) -
        (v ^ D.d i) • (Ti (Tj (F R v i)) * Ti (F R v l)) := by
    rw [hiFl]
    simp only [map_sub, map_mul, map_smul, hjFl, hiFl]
  rw [hjFl, ht, map_sub, map_mul, map_smul, map_mul,
    higherDouble_triple_Fi i j Hi Hj hij h h']
  rw [higherDouble_transport_Fi i j Hi Hj hij h h',
    nonterminalDoubleBraidInv_Fj j Hj.edge Hj.leaf Hj.unique Hj.path
      Hj.diff Hj.sum Hj.cycl Hj.cube i hij h', hiFl]
  simp only [map_sub, map_mul, map_smul, hjFl, nonterminalDoubleBraid_F,
    hij, ↓reduceIte, braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h',
    parameter_eq_square_of_double_edge (v := v) h h']
  have hS : qSerre (v ^ D.d i) 2 (F R v i) (F R v l) = 0 := by
    simpa only [hil, Int.reduceSub, Int.reduceToNat] using serre_F R v hli.symm
  exact higherDouble_short_polynomial_right
    (F R v i) (F R v j) (F R v l) (v ^ D.d i) (pow_ne_zero _ (NeZero.ne v))
    hS (F_commute_F_of_cartanMatrix_eq_zero hjl)



/-- Length-four equality on an external positive generator adjacent to the long node.
The certificate cancels only the explicit long-node quantum sum. -/
theorem higherDouble_four_E_long (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hil : D.cartanMatrix i l = 0) (hjl : D.cartanMatrix j l = -1) :
    Ti (Tj (Ti (Tj (E R v l)))) = Tj (Ti (Tj (Ti (E R v l)))) := by
  have hiEl : Ti (E R v l) = E R v l := by
    simp [hli, braidEj_eq_of_cartanMatrix_eq_zero hil]
  have hjEl : Tj (E R v l) =
      E R v j * E R v l - (v ^ D.d j)⁻¹ • (E R v l * E R v j) := by
    simp [hlj, braidEj_eq_of_cartanMatrix_eq_neg_one hjl]
  have ht : Tj (Ti (Tj (E R v l))) =
      Tj (Ti (E R v j)) * Tj (E R v l) -
        (v ^ D.d j)⁻¹ • (Tj (E R v l) * Tj (Ti (E R v j))) := by
    rw [hjEl]
    simp only [map_sub, map_mul, map_smul, hiEl, hjEl]
  rw [hiEl, ht, map_sub, map_mul, map_smul, map_mul,
    higherDouble_triple_Ej i j Hi Hj hij h h']
  symm
  rw [higherDouble_transport_Ej i j Hi Hj hij h h',
    nonterminalDoubleBraidInv_Ej_two i Hi.edge Hi.leaf Hi.unique Hi.path
      Hi.diff Hi.sum Hi.cycl Hi.cube j hij.symm h, hjEl]
  simp only [map_sub, map_mul, map_smul, hiEl, nonterminalDoubleBraid_E,
    hij.symm, ↓reduceIte, braidEj_eq_of_cartanMatrix_eq_neg_two h,
    parameter_eq_square_of_double_edge (v := v) h h']
  have hp := parameter_eq_square_of_double_edge (v := v) h h'
  have hS : qSerre ((v ^ D.d i) ^ 2) 2 (E R v j) (E R v i) = 0 := by
    simpa only [h', hp, Int.reduceSub, Int.reduceToNat] using serre_E R v hij.symm
  have hU : qSerre ((v ^ D.d i) ^ 2) 2 (E R v j) (E R v l) = 0 := by
    simpa only [hjl, hp, Int.reduceSub, Int.reduceToNat] using serre_E R v hlj.symm
  have hs : (v ^ D.d i) ^ 2 + ((v ^ D.d i) ^ 2)⁻¹ ≠ 0 := by
    simpa only [hp] using Hj.sum
  have hP := congrArg (fun z : QuantumGroup R v ↦ (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ • z)
    (higherDouble_long_polynomial (E R v i) (E R v j) (E R v l) (v ^ D.d i)
      (pow_ne_zero _ (NeZero.ne v)) hS hU (E_commute_E_of_cartanMatrix_eq_zero hil) hs)
  simp only [smul_sub, smul_add, smul_smul, smul_mul_assoc, mul_smul_comm, inv_pow,
    mul_sub, sub_mul, mul_add, add_mul] at hP ⊢
  linear_combination (norm := (match_scalars <;> ring)) hP


/-- Length-four equality on an external negative generator adjacent to the long node.
The certificate cancels only the explicit long-node quantum sum. -/
theorem higherDouble_four_F_long (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hil : D.cartanMatrix i l = 0) (hjl : D.cartanMatrix j l = -1) :
    Ti (Tj (Ti (Tj (F R v l)))) = Tj (Ti (Tj (Ti (F R v l)))) := by
  have hiFl : Ti (F R v l) = F R v l := by
    simp [hli, braidFj_eq_of_cartanMatrix_eq_zero hil]
  have hjFl : Tj (F R v l) =
      F R v l * F R v j - (v ^ D.d j) • (F R v j * F R v l) := by
    simp [hlj, braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hjl]
  have ht : Tj (Ti (Tj (F R v l))) =
      Tj (F R v l) * Tj (Ti (F R v j)) -
        (v ^ D.d j) • (Tj (Ti (F R v j)) * Tj (F R v l)) := by
    rw [hjFl]
    simp only [map_sub, map_mul, map_smul, hiFl, hjFl]
  rw [hiFl, ht, map_sub, map_mul, map_smul, map_mul,
    higherDouble_triple_Fj i j Hi Hj hij h h']
  symm
  rw [higherDouble_transport_Fj i j Hi Hj hij h h',
    nonterminalDoubleBraidInv_Fj_two i Hi.edge Hi.leaf Hi.unique Hi.path
      Hi.diff Hi.sum Hi.cycl Hi.cube j hij.symm h, hjFl]
  simp only [map_sub, map_mul, map_smul, hiFl, nonterminalDoubleBraid_F,
    hij.symm, ↓reduceIte, braidFj_eq_of_cartanMatrix_eq_neg_two (NeZero.ne v) h,
    parameter_eq_square_of_double_edge (v := v) h h']
  have hp := parameter_eq_square_of_double_edge (v := v) h h'
  have hS : qSerre ((v ^ D.d i) ^ 2) 2 (F R v j) (F R v i) = 0 := by
    simpa only [h', hp, Int.reduceSub, Int.reduceToNat] using serre_F R v hij.symm
  have hU : qSerre ((v ^ D.d i) ^ 2) 2 (F R v j) (F R v l) = 0 := by
    simpa only [hjl, hp, Int.reduceSub, Int.reduceToNat] using serre_F R v hlj.symm
  have hs : (v ^ D.d i) ^ 2 + ((v ^ D.d i) ^ 2)⁻¹ ≠ 0 := by
    simpa only [hp] using Hj.sum
  have hP := congrArg (fun z : QuantumGroup R v ↦ (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ • z)
    (higherDouble_long_polynomial_right (F R v i) (F R v j) (F R v l) (v ^ D.d i)
      (pow_ne_zero _ (NeZero.ne v)) hS hU (F_commute_F_of_cartanMatrix_eq_zero hil) hs)
  simp only [smul_sub, smul_add, smul_smul, smul_mul_assoc, mul_smul_comm,
    mul_sub, sub_mul, mul_add, add_mul] at hP ⊢
  linear_combination (norm := (match_scalars <;> ring)) hP

/-- The fourfold words agree on the first positive generator. -/
theorem higherDouble_Ei : Ti (Tj (Ti (Tj (E R v i)))) =
    Tj (Ti (Tj (Ti (E R v i)))) := by
  rw [higherDouble_triple_Ei i j Hi Hj hij h h']
  simp only [nonterminalDoubleBraid_E, ↓reduceIte, braidEi, map_neg, map_mul, Kt,
    nonterminalDoubleBraid_K,
    higherDouble_triple_Fi i j Hi Hj hij h h',
    reflY_triple_ktilde_of_double_edge_left i j h h']

/-- The fourfold words agree on the first negative generator. -/
theorem higherDouble_Fi : Ti (Tj (Ti (Tj (F R v i)))) =
    Tj (Ti (Tj (Ti (F R v i)))) := by
  rw [higherDouble_triple_Fi i j Hi Hj hij h h']
  simp only [nonterminalDoubleBraid_F, ↓reduceIte, braidFi, map_neg, map_mul,
    nonterminalDoubleBraid_K,
    higherDouble_triple_Ei i j Hi Hj hij h h',
    reflY_triple_ktilde_of_double_edge_left i j h h']

/-- The fourfold words agree on the second positive generator. -/
theorem higherDouble_Ej : Ti (Tj (Ti (Tj (E R v j)))) =
    Tj (Ti (Tj (Ti (E R v j)))) := by
  rw [higherDouble_triple_Ej i j Hi Hj hij h h']
  simp only [nonterminalDoubleBraid_E, ↓reduceIte, braidEi, map_neg, map_mul, Kt,
    nonterminalDoubleBraid_K,
    higherDouble_triple_Fj i j Hi Hj hij h h',
    reflY_triple_ktilde_of_double_edge_right i j h h']

/-- The fourfold words agree on the second negative generator. -/
theorem higherDouble_Fj : Ti (Tj (Ti (Tj (F R v j)))) =
    Tj (Ti (Tj (Ti (F R v j)))) := by
  rw [higherDouble_triple_Fj i j Hi Hj hij h h']
  simp only [nonterminalDoubleBraid_F, ↓reduceIte, braidFi, map_neg, map_mul,
    nonterminalDoubleBraid_K,
    higherDouble_triple_Ej i j Hi Hj hij h h',
    reflY_triple_ktilde_of_double_edge_right i j h h']


/-- Genuine length-four equality of the published local quantum-group quotient maps.
All external E/F and arbitrary toral generators are included. The only assumptions
are the two published local graph/scalar packages and the double edge. No finiteness,
rank-two exhaustion, characteristic-zero or coroot-span condition is imposed. -/
theorem higherDoubleBraid_braid :
    (Ti).comp ((Tj).comp ((Ti).comp Tj)) = (Tj).comp ((Ti).comp ((Tj).comp Ti)) := by
  have houter (l : I) (hli : l ≠ i) (hlj : l ≠ j) :
      (D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = 0) ∨
      (D.cartanMatrix i l = -1 ∧ D.cartanMatrix j l = 0) ∨
      (D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = -1) := by
    rcases Hi.edge l hli with hi0 | ⟨hi1, _⟩ | ⟨hi2, _⟩
    · rcases Hi.path j l (by simp [h]) hi0 with hj0 | ⟨hj1, _⟩
      · exact Or.inl ⟨hi0, hj0⟩
      · exact Or.inr (Or.inr ⟨hi0, hj1⟩)
    · exact Or.inr (Or.inl ⟨hi1,
        Hi.leaf j l hij.symm hli (by simp [h]) (by simp [hi1]) hlj.symm⟩)
    · exact (hlj (Hi.unique l j hi2 h)).elim
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · by_cases hli : l = i
    · subst l
      exact higherDouble_Ei i j Hi Hj hij h h'
    · by_cases hlj : l = j
      · subst l
        exact higherDouble_Ej i j Hi Hj hij h h'
      · rcases houter l hli hlj with ⟨hi0, hj0⟩ | ⟨hi1, hj0⟩ | ⟨hi0, hj1⟩
        · simp [hli, hlj, braidEj_eq_of_cartanMatrix_eq_zero hi0,
            braidEj_eq_of_cartanMatrix_eq_zero hj0]
        · exact higherDouble_four_E_short i j Hi Hj hij h h' l hli hlj hi1 hj0
        · exact higherDouble_four_E_long i j Hi Hj hij h h' l hli hlj hi0 hj1
  · by_cases hli : l = i
    · subst l
      exact higherDouble_Fi i j Hi Hj hij h h'
    · by_cases hlj : l = j
      · subst l
        exact higherDouble_Fj i j Hi Hj hij h h'
      · rcases houter l hli hlj with ⟨hi0, hj0⟩ | ⟨hi1, hj0⟩ | ⟨hi0, hj1⟩
        · simp [hli, hlj, braidFj_eq_of_cartanMatrix_eq_zero hi0,
            braidFj_eq_of_cartanMatrix_eq_zero hj0]
        · exact higherDouble_four_F_short i j Hi Hj hij h h' l hli hlj hi1 hj0
        · exact higherDouble_four_F_long i j Hi Hj hij h h' l hli hlj hi0 hj1
  · simp only [AlgHom.comp_apply, nonterminalDoubleBraid_K, reflY_braid_of_double_edge h h']

/-- The corresponding actual algebra equivalences satisfy the length-four braid equality. -/
theorem higherDoubleBraidEquiv_braid :
    let Si := nonterminalDoubleBraidEquiv (R := R) i
      Hi.edge Hi.leaf Hi.unique Hi.path Hi.diff Hi.sum Hi.cycl Hi.cube
    let Sj := nonterminalDoubleBraidEquiv (R := R) j
      Hj.edge Hj.leaf Hj.unique Hj.path Hj.diff Hj.sum Hj.cycl Hj.cube
    ((Si.trans Sj).trans Si).trans Sj = ((Sj.trans Si).trans Sj).trans Si := by
  apply DFunLike.ext
  intro x
  exact (DFunLike.congr_fun (higherDoubleBraid_braid i j Hi Hj hij h h') x).symm

end LieLean.QuantumGroup
