/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.TerminalDouble
import LieLean.Algebra.QuantumGroup.BraidAction.TerminalDoubleOther

/-!
# Braid automorphisms at nonterminal double centres

## Main definitions and results
An exact original-Serre certificate for the outgoing (-2,-1) neighbour pair,
all defining relations, the actual quotient lift, its reversal-conjugate inverse,
and both compositions. Arbitrary field, rank and toral lattice. Centre edges are
zero, mutual simple, or either double orientation. Distinct neighbours are
orthogonal, at most one outgoing -2 edge is allowed, and neighbour-to-untouched
edges are zero or mutual simple. Untouched-to-untouched entries are unrestricted.
All scalar cancellations are explicit. Higher-rank braid relations are not proved.

## References
Reconstructed by exact rational-function elimination from the defining Serre
relations. Lean checks the certificate.
-/
noncomputable section
namespace QuantumGroup
variable {k : Type*} [Field k]

set_option maxHeartbeats 2000000 in
-- Expanding the degree-five certificate requires scalar normalization.
/-- Degree-five certificate for a double and a simple outgoing edge.
Only the original cubic, quadratic and orthogonality relations are premises.
The extra quantum-three factor is explicit; necessity is not asserted. -/
theorem commute_double_simple_quantumCommutators
    {B : Type*} [Ring B] [Algebra k B] (a b c : B) (q : k)
    (hq : q ≠ 0) (hn : q ^ 4 + q ^ 2 + 1 ≠ 0)
    (hS : qSerre q 3 a b = 0) (hU : qSerre q 2 a c = 0)
    (hbc : Commute b c) :
    Commute
      (a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) + q⁻¹ ^ 2 • (b * a ^ 2))
      (a * c - q⁻¹ • (c * a)) := by
  have h0 := congrArg (fun z : B ↦ z * c) hS
  have h1 := congrArg (fun z : B ↦ c * z) hS
  have h2 := congrArg (fun z : B ↦ z * (a * b)) hU
  have h3 := congrArg (fun z : B ↦ a * z * b) hU
  have h4 := congrArg (fun z : B ↦ a * b * z) hU
  have h5 := congrArg (fun z : B ↦ z * (b * a)) hU
  have h6 := congrArg (fun z : B ↦ b * z * a) hU
  have h7 := congrArg (fun z : B ↦ b * a * z) hU
  have hcb (z : B) : c * (b * z) = b * (c * z) := by
    rw [← mul_assoc, hbc.symm.eq, mul_assoc]
  apply sub_eq_zero.mp
  apply (smul_eq_zero.mp (show (q ^ 4 + q ^ 2 + 1) •
    ((a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) + q⁻¹ ^ 2 • (b * a ^ 2)) *
        (a * c - q⁻¹ • (c * a)) -
      (a * c - q⁻¹ • (c * a)) *
        (a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) +
          q⁻¹ ^ 2 • (b * a ^ 2))) = 0 from ?_)).resolve_left hn
  simp only [qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial,
    Nat.reduceSub, pow_succ, pow_zero, mul_one, one_mul, mul_zero, zero_mul, add_zero,
    zero_add, one_smul, mul_neg, neg_mul, neg_neg, mul_sub, sub_mul, mul_add,
    add_mul, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_smul,
    mul_assoc, hbc.symm.eq, hcb] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  linear_combination (norm := (match_scalars <;> field_simp [hq] <;> ring))
    -(q ^ 2) • h0 + q⁻¹ • h1 + (q + q ^ 3) • h2 + q ^ 2 • h3 -
      (q ^ 2 + 1 + q⁻¹ ^ 2) • h4 - (q ^ 3 + q + q⁻¹) • h5 +
      q⁻¹ • h6 + (1 + q⁻¹ ^ 2) • h7

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j l : I}

/-- Actual positive images of orthogonal double/simple neighbours commute.
Arbitrary ambient rank, field, lattice, and reverse Cartan entries. The two
original Serre parameters are both the centre parameter, not the leaf parameters. -/
theorem braidEj_commute_braidEj_of_double_simple_neighbours
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -2)
    (hil : D.cartanMatrix i l = -1) (hjl : D.cartanMatrix j l = 0)
    (hn : (v ^ D.d i) ^ 4 + (v ^ D.d i) ^ 2 + 1 ≠ 0) :
    Commute (braidEj R v i j) (braidEj R v i l) := by
  have hij' : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at hij
    norm_num at hij
  have hil' : i ≠ l := by
    rintro rfl
    rw [D.cartanMatrix_self] at hil
    norm_num at hil
  have hS : qSerre (v ^ D.d i) 3 (E R v i) (E R v j) = 0 := by
    simpa only [hij, Int.reduceSub, Int.reduceToNat] using serre_E R v hij'
  have hU : qSerre (v ^ D.d i) 2 (E R v i) (E R v l) = 0 := by
    simpa only [hil, Int.reduceSub, Int.reduceToNat] using serre_E R v hil'
  rw [braidEj_eq_of_cartanMatrix_eq_neg_two hij,
    braidEj_eq_of_cartanMatrix_eq_neg_one hil]
  exact (commute_double_simple_quantumCommutators _ _ _ _ (pow_ne_zero _ hv) hn
    hS hU (E_commute_E_of_cartanMatrix_eq_zero hjl)).smul_left _

/-- Actual negative images commute by the genuine Chevalley involution.
Only its nonzero factor `-q_i^{-3}` is cancelled; no target relation is assumed. -/
theorem braidFj_commute_braidFj_of_double_simple_neighbours
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -2)
    (hil : D.cartanMatrix i l = -1) (hjl : D.cartanMatrix j l = 0)
    (hn : (v ^ D.d i) ^ 4 + (v ^ D.d i) ^ 2 + 1 ≠ 0) :
    Commute (braidFj R v i j) (braidFj R v i l) := by
  have hp := braidEj_commute_braidEj_of_double_simple_neighbours (R := R) hv hij hil hjl hn
  have hc := congrArg (chevalley R v) hp.eq
  rw [map_mul, map_mul,
    chevalley_braidEj_of_cartanMatrix_eq_neg_two hv hij,
    chevalley_braidEj_of_cartanMatrix_eq_neg_one hv hil] at hc
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul] at hc
  have hq : (v ^ D.d i)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hv)
  apply sub_eq_zero.mp
  apply (smul_eq_zero.mp (show ((v ^ D.d i)⁻¹ ^ 2 * -(v ^ D.d i)⁻¹) •
    (braidFj R v i j * braidFj R v i l - braidFj R v i l * braidFj R v i j) = 0
    from ?_)).resolve_left (mul_ne_zero (pow_ne_zero _ hq) (neg_ne_zero.mpr hq))
  simpa only [smul_sub, mul_comm] using sub_eq_zero.mpr hc

end QuantumGroup

namespace QuantumGroup
variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k}

private theorem nonterminal_serre_one (q : k) {a b : QuantumGroup R v}
    (h : Commute a b) : qSerre q 1 a b = 0 := by
  simp [qSerre, Finset.sum_range_succ, h.eq]

private theorem nonterminal_braidEi_commute {i j : I} (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) : Commute (braidEi R i) (E R v j) := by
  have hK : Commute (K R v (ktilde R i)) (E R v j) := by
    change K R v (ktilde R i) * E R v j = E R v j * K R v (ktilde R i)
    simp [K_mul_E, root_ktilde, hij]
  exact ((show Commute (F R v i) (E R v j) from (E_mul_F_of_ne hj).symm).mul_left
    hK).neg_left

private theorem nonterminal_braidFi_commute {i j : I} (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) : Commute (braidFi R i) (F R v j) := by
  have hK : Commute (K R v (-ktilde R i)) (F R v j) := by
    change K R v (-ktilde R i) * F R v j = F R v j * K R v (-ktilde R i)
    simp [K_mul_F, map_neg, root_ktilde, hij]
  exact (hK.mul_left (E_mul_F_of_ne (Ne.symm hj))).neg_left

variable [NeZero v] (i : I)
  (hedge : ∀ j, j ≠ i → D.cartanMatrix i j = 0 ∨
    (D.cartanMatrix i j = -1 ∧
      (D.cartanMatrix j i = -1 ∨ D.cartanMatrix j i = -2)) ∨
    (D.cartanMatrix i j = -2 ∧ D.cartanMatrix j i = -1))
  (hleaf : ∀ j l, j ≠ i → l ≠ i →
    D.cartanMatrix i j ≠ 0 → D.cartanMatrix i l ≠ 0 →
    j ≠ l → D.cartanMatrix j l = 0)
  (hunique : ∀ j l, D.cartanMatrix i j = -2 → D.cartanMatrix i l = -2 → j = l)
  (hpath : ∀ j l, D.cartanMatrix i j ≠ 0 → D.cartanMatrix i l = 0 →
    D.cartanMatrix j l = 0 ∨ (D.cartanMatrix j l = -1 ∧ D.cartanMatrix l j = -1))
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)
  (hn : (1 + (v ^ D.d i)⁻¹ ^ 4) *
    (1 + (v ^ D.d i)⁻¹ ^ 2 + (v ^ D.d i)⁻¹ ^ 4) ≠ 0)
  (hc : (v ^ D.d i) ^ 4 + (v ^ D.d i) ^ 2 + 1 ≠ 0)

include hedge hleaf hunique hpath hq hs hn hc in
/-- All defining relations at a locally simple/double centre with orthogonal
neighbours and at most one outgoing double edge. Reconstructed from original
relations. No finiteness, coroot-span, or transformed-relation premise. -/
theorem nonterminalDoubleBraid_relations :
    Relations R v (fun l ↦ if l = i then braidEi R i else braidEj R v i l)
      (fun l ↦ if l = i then braidFi R i else braidFj R v i l) (braidK R v i) where
  K_mul_E μ l := by
    by_cases hl : l = i
    · subst l
      simpa only [↓reduceIte] using braidK_mul_braidEi (R := R) (v := v) _ μ
    · simpa only [hl, ↓reduceIte] using
        braidK_mul_braidEj (R := R) (NeZero.ne v) (Ne.symm hl) μ
  K_mul_F μ l := by
    by_cases hl : l = i
    · subst l
      simpa only [↓reduceIte] using braidK_mul_braidFi (R := R) (v := v) _ μ
    · simpa only [hl, ↓reduceIte] using
        braidK_mul_braidFj (R := R) (NeZero.ne v) (Ne.symm hl) μ
  E_mul_F l m := by
    by_cases hl : l = i
    · subst l
      by_cases hm : m = i
      · subst m
        simpa only [↓reduceIte] using braidEi_mul_braidFi_sub (R := R) (v := v) i
      · simpa only [hm, (Ne.symm hm), ↓reduceIte] using
          braidEi_mul_braidFj_sub (R := R) (v := v) (Ne.symm hm)
    · by_cases hm : m = i
      · subst m
        simpa only [hl, ↓reduceIte] using
          braidEj_mul_braidFi_sub (R := R) (v := v) (Ne.symm hl)
      · by_cases hlm : l = m
        · subst m
          simp only [hl, ↓reduceIte]
          rcases hedge l hl with h0 | ⟨h1, _⟩ | ⟨h2, _⟩
          · exact braidEj_mul_braidFj_sub_of_cartanMatrix_eq_zero h0
          · exact braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_one (NeZero.ne v) h1 hq
          · exact braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_two (NeZero.ne v) h2 hq hs
        · simp only [hl, hm, hlm, ↓reduceIte]
          rcases hedge l hl with hl0 | ⟨hl1, _⟩ | ⟨hl2, _⟩
          · exact sub_eq_zero.mpr
              (braidEj_commute_braidFj_of_left_orthogonal hl hlm hl0).eq
          · rcases hedge m hm with hm0 | ⟨hm1, _⟩ | ⟨hm2, _⟩
            · exact sub_eq_zero.mpr
                (braidEj_commute_braidFj_of_right_orthogonal (Ne.symm hm) hlm hm0).eq
            · exact braidEj_mul_braidFj_sub_of_two_cartanMatrix_eq_neg_one
                (NeZero.ne v) hl1 hm1 hlm hq
            · exact braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_one_neg_two
                (NeZero.ne v) hl1 hm2 hlm
          · rcases hedge m hm with hm0 | ⟨hm1, _⟩ | ⟨hm2, _⟩
            · exact sub_eq_zero.mpr
                (braidEj_commute_braidFj_of_right_orthogonal (Ne.symm hm) hlm hm0).eq
            · exact braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_two_neg_one
                (NeZero.ne v) hl2 hm1 hlm
            · exact braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_two_neg_two
                (NeZero.ne v) hl2 hm2 hlm
  serre_E l m hlm := by
    by_cases hl : l = i
    · subst l
      rcases hedge m hlm.symm with h0 | ⟨h1, _⟩ | ⟨h2, _⟩
      · simp only [hlm.symm, ↓reduceIte, h0, sub_zero, Int.toNat_one,
          braidEj_eq_of_cartanMatrix_eq_zero h0]
        exact nonterminal_serre_one _ (nonterminal_braidEi_commute hlm.symm h0)
      · simpa only [hlm.symm, ↓reduceIte] using
          qSerre_braidEi_braidEj_of_cartanMatrix_eq_neg_one (R := R) h1 hq
      · simpa only [hlm.symm, ↓reduceIte] using
          qSerre_braidEi_braidEj_of_cartanMatrix_eq_neg_two (R := R) (NeZero.ne v) h2
    · by_cases hm : m = i
      · subst m
        rcases hedge l hl with h0 | ⟨h1, h1' | h2'⟩ | ⟨h2, h1'⟩
        · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i l).mp h0
          simp only [hl, ↓reduceIte, h0', sub_zero, Int.toNat_one,
            braidEj_eq_of_cartanMatrix_eq_zero h0]
          exact nonterminal_serre_one _ (nonterminal_braidEi_commute hl h0).symm
        · simpa only [hl, ↓reduceIte] using
            qSerre_braidEj_braidEi_of_simply_laced_edge (R := R) h1 h1' hq
        · simpa only [hl, ↓reduceIte] using
            qSerre_braidEj_braidEi_of_double_edge_other (R := R) h1 h2' hq
        · simpa only [hl, ↓reduceIte] using
            qSerre_braidEj_braidEi_of_double_edge (R := R) (NeZero.ne v) h2 h1'
      · simp only [hl, hm, ↓reduceIte]
        rcases hedge l hl with hl0 | ⟨hl1, hl'⟩ | ⟨hl2, hl'⟩
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩ | ⟨hm2, _⟩
          · simpa only [braidEj_eq_of_cartanMatrix_eq_zero hl0,
              braidEj_eq_of_cartanMatrix_eq_zero hm0] using serre_E R v hlm
          · rcases hpath m l (by simp [hm1]) hl0 with h0 | ⟨_, h1⟩
            · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm m l).mp h0
              rw [h0']
              exact nonterminal_serre_one _
                (braidEj_commute_braidEj_of_disconnected hl0 h0).symm
            · exact qSerre_braidEj_braidEj_of_path_reverse hm1 h1 hl0
          · rcases hpath m l (by simp [hm2]) hl0 with h0 | ⟨_, h1⟩
            · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm m l).mp h0
              rw [h0']
              exact nonterminal_serre_one _
                (braidEj_commute_braidEj_of_disconnected hl0 h0).symm
            · exact qSerre_braidEj_braidEj_of_double_path_reverse
                (NeZero.ne v) hm2 h1 hl0
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩ | ⟨hm2, _⟩
          · rcases hpath l m (by simp [hl1]) hm0 with h0 | ⟨h1, _⟩
            · rw [h0]
              exact nonterminal_serre_one _ (braidEj_commute_braidEj_of_disconnected hm0 h0)
            · rcases hl' with hl' | hl'
              · exact qSerre_braidEj_braidEj_of_path (NeZero.ne v) hl1 hl' h1 hm0 hs
              · exact qSerre_braidEj_braidEj_of_double_other_path
                  (NeZero.ne v) hl1 hl' h1 hm0 hs
          · have h0 := hleaf l m hl hm (by simp [hl1]) (by simp [hm1]) hlm
            rw [h0]
            exact nonterminal_serre_one _
              (braidEj_commute_braidEj_of_orthogonal_neighbours
                (NeZero.ne v) hl1 hm1 hlm h0 hs)
          · have h0 := hleaf l m hl hm (by simp [hl1]) (by simp [hm2]) hlm
            rw [h0]
            exact nonterminal_serre_one _
              (braidEj_commute_braidEj_of_double_simple_neighbours (NeZero.ne v) hm2 hl1
                ((D.isGeneralizedCartan_cartanMatrix.zero_comm l m).mp h0) hc).symm
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩ | ⟨hm2, _⟩
          · rcases hpath l m (by simp [hl2]) hm0 with h0 | ⟨h1, _⟩
            · rw [h0]
              exact nonterminal_serre_one _ (braidEj_commute_braidEj_of_disconnected hm0 h0)
            · exact qSerre_braidEj_braidEj_of_double_path
                (NeZero.ne v) hl2 hl' h1 hm0 hn
          · have h0 := hleaf l m hl hm (by simp [hl2]) (by simp [hm1]) hlm
            rw [h0]
            exact nonterminal_serre_one _
              (braidEj_commute_braidEj_of_double_simple_neighbours
                (NeZero.ne v) hl2 hm1 h0 hc)
          · exact (hlm (hunique l m hl2 hm2)).elim
  serre_F l m hlm := by
    by_cases hl : l = i
    · subst l
      rcases hedge m hlm.symm with h0 | ⟨h1, _⟩ | ⟨h2, _⟩
      · simp only [hlm.symm, ↓reduceIte, h0, sub_zero, Int.toNat_one,
          braidFj_eq_of_cartanMatrix_eq_zero h0]
        exact nonterminal_serre_one _ (nonterminal_braidFi_commute hlm.symm h0)
      · simpa only [hlm.symm, ↓reduceIte] using
          qSerre_braidFi_braidFj_of_cartanMatrix_eq_neg_one (R := R) h1 hq
      · simpa only [hlm.symm, ↓reduceIte] using
          qSerre_braidFi_braidFj_of_cartanMatrix_eq_neg_two (R := R) (NeZero.ne v) h2
    · by_cases hm : m = i
      · subst m
        rcases hedge l hl with h0 | ⟨h1, h1' | h2'⟩ | ⟨h2, h1'⟩
        · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i l).mp h0
          simp only [hl, ↓reduceIte, h0', sub_zero, Int.toNat_one,
            braidFj_eq_of_cartanMatrix_eq_zero h0]
          exact nonterminal_serre_one _ (nonterminal_braidFi_commute hl h0).symm
        · simpa only [hl, ↓reduceIte] using
            qSerre_braidFj_braidFi_of_simply_laced_edge (R := R) h1 h1' hq
        · simpa only [hl, ↓reduceIte] using
            qSerre_braidFj_braidFi_of_double_edge_other (R := R) h1 h2' hq
        · simpa only [hl, ↓reduceIte] using
            qSerre_braidFj_braidFi_of_double_edge (R := R) (NeZero.ne v) h2 h1'
      · simp only [hl, hm, ↓reduceIte]
        rcases hedge l hl with hl0 | ⟨hl1, hl'⟩ | ⟨hl2, hl'⟩
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩ | ⟨hm2, _⟩
          · simpa only [braidFj_eq_of_cartanMatrix_eq_zero hl0,
              braidFj_eq_of_cartanMatrix_eq_zero hm0] using serre_F R v hlm
          · rcases hpath m l (by simp [hm1]) hl0 with h0 | ⟨_, h1⟩
            · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm m l).mp h0
              rw [h0']
              exact nonterminal_serre_one _
                (braidFj_commute_braidFj_of_disconnected hl0 h0).symm
            · exact qSerre_braidFj_braidFj_of_path_reverse (NeZero.ne v) hm1 h1 hl0
          · rcases hpath m l (by simp [hm2]) hl0 with h0 | ⟨_, h1⟩
            · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm m l).mp h0
              rw [h0']
              exact nonterminal_serre_one _
                (braidFj_commute_braidFj_of_disconnected hl0 h0).symm
            · exact qSerre_braidFj_braidFj_of_double_path_reverse
                (NeZero.ne v) hm2 h1 hl0
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩ | ⟨hm2, _⟩
          · rcases hpath l m (by simp [hl1]) hm0 with h0 | ⟨h1, _⟩
            · rw [h0]
              exact nonterminal_serre_one _ (braidFj_commute_braidFj_of_disconnected hm0 h0)
            · rcases hl' with hl' | hl'
              · exact qSerre_braidFj_braidFj_of_path (NeZero.ne v) hl1 hl' h1 hm0 hs
              · exact qSerre_braidFj_braidFj_of_double_other_path
                  (NeZero.ne v) hl1 hl' h1 hm0 hs
          · have h0 := hleaf l m hl hm (by simp [hl1]) (by simp [hm1]) hlm
            rw [h0]
            exact nonterminal_serre_one _
              (braidFj_commute_braidFj_of_orthogonal_neighbours
                (NeZero.ne v) hl1 hm1 hlm h0 hs)
          · have h0 := hleaf l m hl hm (by simp [hl1]) (by simp [hm2]) hlm
            rw [h0]
            exact nonterminal_serre_one _
              (braidFj_commute_braidFj_of_double_simple_neighbours (NeZero.ne v) hm2 hl1
                ((D.isGeneralizedCartan_cartanMatrix.zero_comm l m).mp h0) hc).symm
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩ | ⟨hm2, _⟩
          · rcases hpath l m (by simp [hl2]) hm0 with h0 | ⟨h1, _⟩
            · rw [h0]
              exact nonterminal_serre_one _ (braidFj_commute_braidFj_of_disconnected hm0 h0)
            · exact qSerre_braidFj_braidFj_of_double_path
                (NeZero.ne v) hl2 hl' h1 hm0 hn
          · have h0 := hleaf l m hl hm (by simp [hl2]) (by simp [hm1]) hlm
            rw [h0]
            exact nonterminal_serre_one _
              (braidFj_commute_braidFj_of_double_simple_neighbours
                (NeZero.ne v) hl2 hm1 h0 hc)
          · exact (hlm (hunique l m hl2 hm2)).elim

/-- Genuine quotient braid homomorphism with pairwise orthogonal neighbours.
Reconstructed from all defining relations, not from an assumed faithful action. -/
def nonterminalDoubleBraid : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  lift (nonterminalDoubleBraid_relations i hedge hleaf hunique hpath hq hs hn hc)

@[simp] theorem nonterminalDoubleBraid_E (l : I) :
    nonterminalDoubleBraid i hedge hleaf hunique hpath hq hs hn hc (E R v l) =
      if l = i then braidEi R i else braidEj R v i l := lift_E _ l

@[simp] theorem nonterminalDoubleBraid_F (l : I) :
    nonterminalDoubleBraid i hedge hleaf hunique hpath hq hs hn hc (F R v l) =
      if l = i then braidFi R i else braidFj R v i l := lift_F _ l

@[simp] theorem nonterminalDoubleBraid_K (μ : Y) :
    nonterminalDoubleBraid i hedge hleaf hunique hpath hq hs hn hc (K R v μ) =
      K R v (reflY R i μ) := lift_K _ μ

/-- Explicit inverse candidate, using the independently proved product reversal. -/
def nonterminalDoubleBraidInv : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  (AlgHom.opComm braidReversalOp).comp
    ((nonterminalDoubleBraid i hedge hleaf hunique hpath hq hs hn hc).op.comp braidReversalOp)

/-- The inverse candidate is reversal-conjugation on the actual quotient. -/
theorem nonterminalDoubleBraidInv_apply (x : QuantumGroup R v) :
    nonterminalDoubleBraidInv i hedge hleaf hunique hpath hq hs hn hc x =
      braidReversal (nonterminalDoubleBraid
        i hedge hleaf hunique hpath hq hs hn hc (braidReversal x)) := rfl

@[simp] theorem nonterminalDoubleBraidInv_Ei :
    nonterminalDoubleBraidInv i hedge hleaf hunique hpath hq hs hn hc (E R v i) =
      braidInvEi R i := by
  simp [nonterminalDoubleBraidInv_apply, braidEi, braidInvEi, braidReversal_mul, Kt]

@[simp] theorem nonterminalDoubleBraidInv_Fi :
    nonterminalDoubleBraidInv i hedge hleaf hunique hpath hq hs hn hc (F R v i) =
      braidInvFi R i := by
  simp [nonterminalDoubleBraidInv_apply, braidFi, braidInvFi, braidReversal_mul, Kt]

@[simp] theorem nonterminalDoubleBraidInv_Ej (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = -1) :
    nonterminalDoubleBraidInv i hedge hleaf hunique hpath hq hs hn hc (E R v j) =
      E R v j * E R v i - (v ^ D.d i)⁻¹ • (E R v i * E R v j) := by
  simp [nonterminalDoubleBraidInv_apply, hj, braidEj_eq_of_cartanMatrix_eq_neg_one hij,
    braidReversal_mul]

@[simp] theorem nonterminalDoubleBraidInv_Fj (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = -1) :
    nonterminalDoubleBraidInv i hedge hleaf hunique hpath hq hs hn hc (F R v j) =
      F R v i * F R v j - (v ^ D.d i) • (F R v j * F R v i) := by
  simp [nonterminalDoubleBraidInv_apply, hj,
    braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hij, braidReversal_mul]

/-- The inverse fixes every positive generator orthogonal to the chosen node. -/
@[simp] theorem nonterminalDoubleBraidInv_E_of_orthogonal (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) :
    nonterminalDoubleBraidInv i hedge hleaf hunique hpath hq hs hn hc (E R v j) = E R v j := by
  simp [nonterminalDoubleBraidInv_apply, hj, braidEj_eq_of_cartanMatrix_eq_zero hij]

/-- The inverse fixes every negative generator orthogonal to the chosen node. -/
@[simp] theorem nonterminalDoubleBraidInv_F_of_orthogonal (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) :
    nonterminalDoubleBraidInv i hedge hleaf hunique hpath hq hs hn hc (F R v j) = F R v j := by
  simp [nonterminalDoubleBraidInv_apply, hj, braidFj_eq_of_cartanMatrix_eq_zero hij]

@[simp] theorem nonterminalDoubleBraidInv_K (μ : Y) :
    nonterminalDoubleBraidInv i hedge hleaf hunique hpath hq hs hn hc (K R v μ) =
      K R v (reflY R i μ) := by
  simp [nonterminalDoubleBraidInv_apply]

/-- Reversed degree-two positive image, with the actual inverse factorial. -/
@[simp] theorem nonterminalDoubleBraidInv_Ej_two (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = -2) :
    nonterminalDoubleBraidInv i hedge hleaf hunique hpath hq hs hn hc (E R v j) =
      (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ •
        (E R v j * E R v i ^ 2 -
          ((v ^ D.d i + (v ^ D.d i)⁻¹) * (v ^ D.d i)⁻¹) •
            (E R v i * E R v j * E R v i) +
          (v ^ D.d i)⁻¹ ^ 2 • (E R v i ^ 2 * E R v j)) := by
  simp [nonterminalDoubleBraidInv_apply, hj, braidEj_eq_of_cartanMatrix_eq_neg_two hij,
    pow_two, braidReversal_mul, mul_assoc]

/-- Reversed degree-two negative image, with the actual inverse factorial. -/
@[simp] theorem nonterminalDoubleBraidInv_Fj_two (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = -2) :
    nonterminalDoubleBraidInv i hedge hleaf hunique hpath hq hs hn hc (F R v j) =
      (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ •
        ((v ^ D.d i) ^ 2 • (F R v j * F R v i ^ 2) -
          ((v ^ D.d i + (v ^ D.d i)⁻¹) * v ^ D.d i) •
            (F R v i * F R v j * F R v i) + F R v i ^ 2 * F R v j) := by
  simp [nonterminalDoubleBraidInv_apply, hj,
    braidFj_eq_of_cartanMatrix_eq_neg_two (NeZero.ne v) hij,
    pow_two, braidReversal_mul, mul_assoc]

/-- The explicit candidate is a right inverse on every quotient generator.
Reconstructed using the rank-independent degree-one and degree-two recovery identities. -/
theorem nonterminalDoubleBraid_comp_nonterminalDoubleBraidInv :
    (nonterminalDoubleBraid (R := R) i hedge hleaf hunique hpath hq hs hn hc).comp
      (nonterminalDoubleBraidInv i hedge hleaf hunique hpath hq hs hn hc) =
      AlgHom.id k (QuantumGroup R v) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · by_cases hl : l = i
    · subst l
      simp only [AlgHom.comp_apply, nonterminalDoubleBraidInv_Ei, braidInvEi, map_neg, map_mul,
        nonterminalDoubleBraid_F, ↓reduceIte, braidFi, nonterminalDoubleBraid_K, reflY_ktilde,
        mul_neg, neg_neg, AlgHom.id_apply, ← mul_assoc, K_mul_K_neg, one_mul]
    · rcases hedge l hl with h0 | ⟨h1, _⟩ | ⟨h2, _⟩
      · simp [nonterminalDoubleBraidInv_apply, hl,
          braidEj_eq_of_cartanMatrix_eq_zero h0]
      · simpa only [AlgHom.comp_apply,
          nonterminalDoubleBraidInv_Ej i hedge hleaf hunique hpath hq hs hn hc l hl h1,
          map_sub, map_mul, map_smul, nonterminalDoubleBraid_E, hl, ↓reduceIte,
          AlgHom.id_apply] using a2Braid_recover_Ej (R := R) i l h1 hq
      · simpa only [AlgHom.comp_apply,
          nonterminalDoubleBraidInv_Ej_two i hedge hleaf hunique hpath hq hs hn hc l hl h2,
          map_add, map_sub, map_mul, map_pow, map_smul, nonterminalDoubleBraid_E, hl,
          ↓reduceIte, AlgHom.id_apply] using doubleEdge_recover_Ej (NeZero.ne v) h2 hq hs
  · by_cases hl : l = i
    · subst l
      simp only [AlgHom.comp_apply, nonterminalDoubleBraidInv_Fi, braidInvFi, map_neg, map_mul,
        nonterminalDoubleBraid_E, ↓reduceIte, braidEi, Kt, nonterminalDoubleBraid_K, reflY_ktilde,
        neg_mul, neg_neg, AlgHom.id_apply, mul_assoc, K_mul_K_neg, mul_one]
    · rcases hedge l hl with h0 | ⟨h1, _⟩ | ⟨h2, _⟩
      · simp [nonterminalDoubleBraidInv_apply, hl,
          braidFj_eq_of_cartanMatrix_eq_zero h0]
      · simpa only [AlgHom.comp_apply,
          nonterminalDoubleBraidInv_Fj i hedge hleaf hunique hpath hq hs hn hc l hl h1,
          map_sub, map_mul, map_smul, nonterminalDoubleBraid_F, hl, ↓reduceIte,
          AlgHom.id_apply] using a2Braid_recover_Fj (R := R) i l h1 hq
      · simpa only [AlgHom.comp_apply,
          nonterminalDoubleBraidInv_Fj_two i hedge hleaf hunique hpath hq hs hn hc l hl h2,
          map_add, map_sub, map_mul, map_pow, map_smul, nonterminalDoubleBraid_F, hl,
          ↓reduceIte, AlgHom.id_apply] using doubleEdge_recover_Fj (NeZero.ne v) h2 hq hs
  · simp

/-- The left-inverse identity follows by conjugating the proved right inverse
by the actual involutive product reversal, without finite-dimensionality. -/
theorem nonterminalDoubleBraidInv_comp_nonterminalDoubleBraid :
    (nonterminalDoubleBraidInv (R := R) i hedge hleaf hunique hpath hq hs hn hc).comp
      (nonterminalDoubleBraid i hedge hleaf hunique hpath hq hs hn hc) =
      AlgHom.id k (QuantumGroup R v) := by
  apply DFunLike.ext
  intro x
  have hc := congrArg braidReversal
    (DFunLike.congr_fun
      (nonterminalDoubleBraid_comp_nonterminalDoubleBraidInv (R := R)
        i hedge hleaf hunique hpath hq hs hn hc)
      (braidReversal x))
  simpa only [AlgHom.comp_apply, nonterminalDoubleBraidInv_apply, braidReversal_involutive x,
    AlgHom.id_apply] using hc

/-- Genuine braid algebra equivalence with pairwise orthogonal neighbours.
The field and root-datum lattice are arbitrary;
All centre sum/difference and certificate factors are explicitly nonzero.
Both double orientations are allowed; leaf parameters are never identified without proof.
Reconstructed from all presentation relations and explicit two-sided recovery. -/
def nonterminalDoubleBraidEquiv : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  AlgEquiv.ofAlgHom (nonterminalDoubleBraid i hedge hleaf hunique hpath hq hs hn hc)
    (nonterminalDoubleBraidInv i hedge hleaf hunique hpath hq hs hn hc)
    (nonterminalDoubleBraid_comp_nonterminalDoubleBraidInv i hedge hleaf hunique hpath hq hs hn hc)
    (nonterminalDoubleBraidInv_comp_nonterminalDoubleBraid i hedge hleaf hunique hpath hq hs hn hc)

end QuantumGroup
