/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.OrthogonalGeneral

/-!
# Simple-centre braid automorphisms across a double next edge

## Main results
Original-Serre certificates for neighbour/untouched pairs and a broader quotient map.

## References
Reconstructed from the defining Serre polynomials and the repository's PathSerre,
SimplyLaced and OrthogonalGeneral.
-/
noncomputable section
namespace QuantumGroup
section Polynomial
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- The reverse path relation in every degree, with independent parameters.
Only an original Serre relation and commutation of the outer vertices are used. -/
theorem nextEdge_qSerre_reverse (q r : k) (n : ℕ) (a b c : B)
    (hcb : qSerre q n c b = 0) (hac : Commute a c) :
    qSerre q n c (a * b - r • (b * a)) = 0 := by
  have hleft : qSerre q n c (a * b) = a * qSerre q n c b := by
    simp only [qSerre, Finset.mul_sum, mul_smul_comm]
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    rw [← mul_assoc, ← mul_assoc, (hac.symm.pow_left (n - t)).eq]
    simp only [mul_assoc]
  have hright : qSerre q n c (b * a) = qSerre q n c b * a := by
    simp only [qSerre, Finset.sum_mul, smul_mul_assoc]
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    simp only [mul_assoc]
    rw [(hac.pow_right t).eq]
  calc
    _ = qSerre q n c (a * b) - r • qSerre q n c (b * a) := by
      simp only [qSerre, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
        smul_sub, smul_smul, Finset.sum_sub_distrib, Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      rw [mul_comm]
    _ = 0 := by rw [hleft, hright, hcb]; simp

set_option maxHeartbeats 4000000 in
-- The degree-seven certificate expands 44 original-relation multiples.
/-- Forward cubic next-edge certificate from the original quadratic and cubic
Serre relations. The displayed scalar factors are sufficient, not claimed necessary. -/
theorem nextEdge_qSerre_three (q : k) (a b c : B) (hq : q ≠ 0)
    (hs : q + q⁻¹ ≠ 0) (hc : q ^ 4 + q ^ 2 + 1 ≠ 0)
    (hab : qSerre q 2 a b = 0) (hbc : qSerre q 3 b c = 0)
    (hac : Commute a c) :
    qSerre q 3 (a * b - q⁻¹ • (b * a)) c = 0 := by
  have h0 := congrArg (fun z : B ↦ z * a * b * b * c) hab
  have h1 := congrArg (fun z : B ↦ a * z * b * b * c) hab
  have h2 := congrArg (fun z : B ↦ a * b * z * b * c) hab
  have h3 := congrArg (fun z : B ↦ a * b * b * z * c) hab
  have h4 := congrArg (fun z : B ↦ a * b * b * c * z) hab
  have h5 := congrArg (fun z : B ↦ z * a * b * c * b) hab
  have h6 := congrArg (fun z : B ↦ a * z * b * c * b) hab
  have h7 := congrArg (fun z : B ↦ a * b * z * c * b) hab
  have h8 := congrArg (fun z : B ↦ a * b * c * z * b) hab
  have h9 := congrArg (fun z : B ↦ a * b * c * b * z) hab
  have h10 := congrArg (fun z : B ↦ z * a * c * b * b) hab
  have h11 := congrArg (fun z : B ↦ a * z * c * b * b) hab
  have h12 := congrArg (fun z : B ↦ a * c * z * b * b) hab
  have h13 := congrArg (fun z : B ↦ a * c * b * z * b) hab
  have h14 := congrArg (fun z : B ↦ a * c * b * b * z) hab
  have h16 := congrArg (fun z : B ↦ b * z * a * b * c) hab
  have h17 := congrArg (fun z : B ↦ b * a * z * b * c) hab
  have h21 := congrArg (fun z : B ↦ b * z * a * c * b) hab
  have h22 := congrArg (fun z : B ↦ b * a * z * c * b) hab
  have h23 := congrArg (fun z : B ↦ b * a * c * z * b) hab
  have h25 := congrArg (fun z : B ↦ z * b * b * a * c) hab
  have h26 := congrArg (fun z : B ↦ b * z * b * a * c) hab
  have h27 := congrArg (fun z : B ↦ b * b * z * a * c) hab
  have h28 := congrArg (fun z : B ↦ b * b * a * z * c) hab
  have h29 := congrArg (fun z : B ↦ b * b * a * c * z) hab
  have h30 := congrArg (fun z : B ↦ b * b * c * z * a) hab
  have h31 := congrArg (fun z : B ↦ b * c * z * a * b) hab
  have h32 := congrArg (fun z : B ↦ z * b * c * b * a) hab
  have h33 := congrArg (fun z : B ↦ b * z * c * b * a) hab
  have h34 := congrArg (fun z : B ↦ b * c * z * b * a) hab
  have h35 := congrArg (fun z : B ↦ b * c * b * z * a) hab
  have h36 := congrArg (fun z : B ↦ b * c * b * a * z) hab
  have h37 := congrArg (fun z : B ↦ c * z * a * b * b) hab
  have h40 := congrArg (fun z : B ↦ c * b * z * a * b) hab
  have h41 := congrArg (fun z : B ↦ c * b * a * z * b) hab
  have h43 := congrArg (fun z : B ↦ z * c * b * b * a) hab
  have h44 := congrArg (fun z : B ↦ c * z * b * b * a) hab
  have h45 := congrArg (fun z : B ↦ c * b * z * b * a) hab
  have h46 := congrArg (fun z : B ↦ c * b * b * z * a) hab
  have h47 := congrArg (fun z : B ↦ c * b * b * a * z) hab
  have h84 := congrArg (fun z : B ↦ z * a * a * a) hbc
  have h85 := congrArg (fun z : B ↦ a * z * a * a) hbc
  have h86 := congrArg (fun z : B ↦ a * a * z * a) hbc
  have h87 := congrArg (fun z : B ↦ a * a * a * z) hbc
  have hca (z : B) : c * (a * z) = a * (c * z) := by
    rw [← mul_assoc, hac.symm.eq, mul_assoc]
  apply (smul_eq_zero.mp (show ((q + q⁻¹) * (q ^ 4 + q ^ 2 + 1)) •
    qSerre q 3 (a * b - q⁻¹ • (b * a)) c = 0 from ?_)).resolve_left
      (mul_ne_zero hs hc)
  simp only [qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial,
    Nat.reduceSub, pow_succ, pow_zero, mul_one, one_mul, mul_zero, zero_mul, add_zero,
    zero_add, one_smul, mul_neg, neg_mul, neg_neg, mul_sub, sub_mul, mul_add,
    add_mul, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_smul,
    mul_assoc, hac.symm.eq, hca]
    at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h16 h17 h21
       h22 h23 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h40 h41 h43 h44 h45 h46 h47 h84
       h85 h86 h87 ⊢
  linear_combination (norm := (match_scalars <;> field_simp [hq] <;> ring))
    (-q - q ^ 3) • h0 +
    (-q ^ 2) • h1 +
    (-1 - q ^ 2 - q ^ 4) • h2 +
    (-q⁻¹ ^ 2 - 1 - q ^ 2) • h3 +
    (q⁻¹ ^ 4 + 2 * q⁻¹ ^ 2 + 3 * 1 + 2 * q ^ 2 + q ^ 4) • h4 +
    (q⁻¹ + 2 * q + 2 * q ^ 3 + q ^ 5) • h5 +
    (1 + q ^ 2 + q ^ 4) • h6 +
    (q⁻¹ ^ 2 + 2 * 1 + 3 * q ^ 2 + 2 * q ^ 4 + q ^ 6) • h7 +
    (-q⁻¹ ^ 2 - 2 * 1 - 3 * q ^ 2 - 2 * q ^ 4 - q ^ 6) • h8 +
    (-q⁻¹ ^ 4 - 2 * q⁻¹ ^ 2 - 3 * 1 - 2 * q ^ 2 - q ^ 4) • h9 +
    (-q⁻¹ - 2 * q - 2 * q ^ 3 - q ^ 5) • h10 +
    (-1 - q ^ 2 - q ^ 4) • h11 +
    (q ^ 2) • h12 +
    (1 + q ^ 2 + q ^ 4) • h13 +
    (q⁻¹ ^ 2 + 1 + q ^ 2) • h14 +
    (-q⁻¹ ^ 2 - 1) • h16 +
    (q + q ^ 3) • h17 +
    (q⁻¹ ^ 4 + 2 * q⁻¹ ^ 2 + 2 * 1 + q ^ 2) • h21 +
    (-q⁻¹ - 2 * q - 2 * q ^ 3 - q ^ 5) • h22 +
    (q⁻¹ + 2 * q + 2 * q ^ 3 + q ^ 5) • h23 +
    (q⁻¹ + q + q ^ 3) • h25 +
    (q⁻¹ ^ 3 + q⁻¹ + q) • h26 +
    (q⁻¹) • h27 +
    (q⁻¹ ^ 2 + 1) • h28 +
    (-q⁻¹ ^ 4 - 2 * q⁻¹ ^ 2 - 2 * 1 - q ^ 2) • h29 +
    (-q⁻¹ ^ 3 - q⁻¹ - q) • h30 +
    (-q⁻¹ ^ 4 - 2 * q⁻¹ ^ 2 - 2 * 1 - q ^ 2) • h31 +
    (-q⁻¹ ^ 3 - 2 * q⁻¹ - 3 * q - 2 * q ^ 3 - q ^ 5) • h32 +
    (-q⁻¹ ^ 5 - 2 * q⁻¹ ^ 3 - 3 * q⁻¹ - 2 * q - q ^ 3) • h33 +
    (q⁻¹ ^ 5 + 2 * q⁻¹ ^ 3 + 3 * q⁻¹ + 2 * q + q ^ 3) • h34 +
    (q⁻¹ ^ 3 + q⁻¹ + q) • h35 +
    (q⁻¹ ^ 4 + 2 * q⁻¹ ^ 2 + 2 * 1 + q ^ 2) • h36 +
    (q + q ^ 3) • h37 +
    (q⁻¹ ^ 2 + 1) • h40 +
    (-q - q ^ 3) • h41 +
    (q⁻¹ ^ 3 + 2 * q⁻¹ + 3 * q + 2 * q ^ 3 + q ^ 5) • h43 +
    (-q⁻¹ - q - q ^ 3) • h44 +
    (-q⁻¹ ^ 3 - q⁻¹ - q) • h45 +
    (-q⁻¹) • h46 +
    (-q⁻¹ ^ 2 - 1) • h47 +
    (-q⁻¹) • h84 +
    (q⁻¹ ^ 2 + 1 + q ^ 2) • h85 +
    (-q⁻¹ - q - q ^ 3) • h86 +
    (q ^ 2) • h87

end Polynomial
variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j l : I}

/-- Forward cubic positive relation across an outgoing double next edge.
Only the centre and its neighbour have equal parameters, by symmetrizability. -/
theorem nextEdge_braidE_forward_three
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -1)
    (hji : D.cartanMatrix j i = -1) (hjl : D.cartanMatrix j l = -2)
    (hil : D.cartanMatrix i l = 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)
    (hc : (v ^ D.d i) ^ 4 + (v ^ D.d i) ^ 2 + 1 ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j l).toNat
      (braidEj R v i j) (braidEj R v i l) = 0 := by
  have hd : D.d i = D.d j := by
    have h := D.d_mul_cartanMatrix_comm i j
    rw [hij, hji, mul_neg_one, mul_neg_one] at h
    exact_mod_cast neg_injective h
  have hij' : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at hij
    norm_num at hij
  have hjl' : j ≠ l := by
    rintro rfl
    rw [D.cartanMatrix_self] at hjl
    norm_num at hjl
  have hab : qSerre (v ^ D.d i) 2 (E R v i) (E R v j) = 0 := by
    simpa [hij] using serre_E R v hij'
  have hbc : qSerre (v ^ D.d i) 3 (E R v j) (E R v l) = 0 := by
    simpa [hjl, hd] using serre_E R v hjl'
  rw [braidEj_eq_of_cartanMatrix_eq_neg_one hij,
    braidEj_eq_of_cartanMatrix_eq_zero hil, hjl, ← hd]
  exact nextEdge_qSerre_three _ _ _ _ (pow_ne_zero _ hv) hs hc hab hbc
    (E_commute_E_of_cartanMatrix_eq_zero hil)

/-- Reverse actual positive relation in every untouched-node Cartan degree.
The parameter at the untouched node is never identified with the centre parameter. -/
theorem nextEdge_braidE_reverse
    (hij : D.cartanMatrix i j = -1) (hil : D.cartanMatrix i l = 0) :
    qSerre (v ^ D.d l) (1 - D.cartanMatrix l j).toNat
      (braidEj R v i l) (braidEj R v i j) = 0 := by
  have hlj : l ≠ j := by
    rintro rfl
    rw [hil] at hij
    norm_num at hij
  rw [braidEj_eq_of_cartanMatrix_eq_neg_one hij,
    braidEj_eq_of_cartanMatrix_eq_zero hil]
  exact nextEdge_qSerre_reverse _ _ _ _ _ _ (serre_E R v hlj)
    (E_commute_E_of_cartanMatrix_eq_zero hil)

/-- Forward cubic negative relation by the actual Chevalley involution. -/
theorem nextEdge_braidF_forward_three
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -1)
    (hji : D.cartanMatrix j i = -1) (hjl : D.cartanMatrix j l = -2)
    (hil : D.cartanMatrix i l = 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)
    (hc : (v ^ D.d i) ^ 4 + (v ^ D.d i) ^ 2 + 1 ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j l).toNat
      (braidFj R v i j) (braidFj R v i l) = 0 := by
  have h := congrArg (chevalley R v)
    (nextEdge_braidE_forward_three (R := R) hv hij hji hjl hil hs hc)
  rw [map_qSerre, map_zero,
    chevalley_braidEj_of_cartanMatrix_eq_neg_one hv hij,
    braidEj_eq_of_cartanMatrix_eq_zero hil, chevalley_E] at h
  rw [braidFj_eq_of_cartanMatrix_eq_zero hil]
  have h' := qSerre_smul_smul (v := v ^ D.d j) (1 - D.cartanMatrix j l).toNat
    (braidFj R v i j) (F R v l) (-(v ^ D.d i)⁻¹) 1
  simp only [one_smul, mul_one] at h'
  rw [h'] at h
  exact (smul_eq_zero.mp h).resolve_left
    (pow_ne_zero _ (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hv))))

/-- Reverse negative relation in every Cartan degree by Chevalley transport. -/
theorem nextEdge_braidF_reverse
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -1)
    (hil : D.cartanMatrix i l = 0) :
    qSerre (v ^ D.d l) (1 - D.cartanMatrix l j).toNat
      (braidFj R v i l) (braidFj R v i j) = 0 := by
  have h := congrArg (chevalley R v)
    (nextEdge_braidE_reverse (R := R) hij hil)
  rw [map_qSerre, map_zero,
    chevalley_braidEj_of_cartanMatrix_eq_neg_one hv hij,
    braidEj_eq_of_cartanMatrix_eq_zero hil, chevalley_E] at h
  rw [braidFj_eq_of_cartanMatrix_eq_zero hil]
  have h' := qSerre_smul_smul (v := v ^ D.d l) (1 - D.cartanMatrix l j).toNat
    (F R v l) (braidFj R v i j) 1 (-(v ^ D.d i)⁻¹)
  simp only [one_smul, one_pow, one_mul] at h'
  rw [h'] at h
  exact (smul_eq_zero.mp h).resolve_left
    (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hv)))

private theorem nextEdge_assembly_serre_one (q : k) {a b : QuantumGroup R v}
    (h : Commute a b) : qSerre q 1 a b = 0 := by
  simp [qSerre, Finset.sum_range_succ, h.eq]


private theorem nextEdge_assembly_braidEi_commute (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) : Commute (braidEi R i) (E R v j) := by
  have hK : Commute (K R v (ktilde R i)) (E R v j) := by
    change K R v (ktilde R i) * E R v j = E R v j * K R v (ktilde R i)
    simp [K_mul_E, root_ktilde, hij]
  exact ((show Commute (F R v i) (E R v j) from (E_mul_F_of_ne hj).symm).mul_left
    hK).neg_left

private theorem nextEdge_assembly_braidFi_commute (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) : Commute (braidFi R i) (F R v j) := by
  have hK : Commute (K R v (-ktilde R i)) (F R v j) := by
    change K R v (-ktilde R i) * F R v j = F R v j * K R v (-ktilde R i)
    simp [K_mul_F, map_neg, root_ktilde, hij]
  exact (hK.mul_left (E_mul_F_of_ne (Ne.symm hj))).neg_left

variable [NeZero v] (i : I)
  (hedge : ∀ j, j ≠ i → D.cartanMatrix i j = 0 ∨
    (D.cartanMatrix i j = -1 ∧ D.cartanMatrix j i = -1))
  (hleaf : ∀ j l, D.cartanMatrix i j = -1 → D.cartanMatrix i l = -1 →
    j ≠ l → D.cartanMatrix j l = 0)
  (hpath : ∀ j l, D.cartanMatrix i j = -1 → D.cartanMatrix i l = 0 →
    D.cartanMatrix j l = 0 ∨ D.cartanMatrix j l = -1 ∨ D.cartanMatrix j l = -2)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)
  (hc : (v ^ D.d i) ^ 4 + (v ^ D.d i) ^ 2 + 1 ≠ 0)

include hedge hleaf hpath hq hs hc in
/-- All defining relations for the actual braid images. The hypotheses constrain
Cartan entries, not a target relation package. Reconstructed case assembly. -/
theorem nextEdgeBraid_relations :
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
          rcases hedge l hl with h0 | ⟨h1, _⟩
          · simpa only [hl, ↓reduceIte] using
              braidEj_mul_braidFj_sub_of_cartanMatrix_eq_zero (R := R) (v := v) h0
          · simpa only [hl, ↓reduceIte] using
              braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_one
                (R := R) (NeZero.ne v) h1 hq
        · simp only [hl, hm, hlm, ↓reduceIte]
          rcases hedge l hl with hl0 | ⟨hl1, _⟩
          · exact sub_eq_zero.mpr
              (braidEj_commute_braidFj_of_left_orthogonal hl hlm hl0).eq
          · rcases hedge m hm with hm0 | ⟨hm1, _⟩
            · exact sub_eq_zero.mpr
                (braidEj_commute_braidFj_of_right_orthogonal (Ne.symm hm) hlm hm0).eq
            · exact braidEj_mul_braidFj_sub_of_two_cartanMatrix_eq_neg_one
                (NeZero.ne v) hl1 hm1 hlm hq
  serre_E l m hlm := by
    by_cases hl : l = i
    · subst l
      rcases hedge m hlm.symm with h0 | ⟨h1, _⟩
      · simp only [hlm.symm, ↓reduceIte, h0, sub_zero, Int.toNat_one,
          braidEj_eq_of_cartanMatrix_eq_zero h0]
        exact nextEdge_assembly_serre_one _ (nextEdge_assembly_braidEi_commute hlm.symm h0)
      · simpa only [hlm.symm, ↓reduceIte] using
          qSerre_braidEi_braidEj_of_cartanMatrix_eq_neg_one (R := R) h1 hq
    · by_cases hm : m = i
      · subst m
        rcases hedge l hl with h0 | ⟨h1, h1'⟩
        · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i l).mp h0
          simp only [hl, ↓reduceIte, h0', sub_zero, Int.toNat_one,
            braidEj_eq_of_cartanMatrix_eq_zero h0]
          exact nextEdge_assembly_serre_one _ (nextEdge_assembly_braidEi_commute hl h0).symm
        · simpa only [hl, ↓reduceIte] using
            qSerre_braidEj_braidEi_of_simply_laced_edge (R := R) h1 h1' hq
      · simp only [hl, hm, ↓reduceIte]
        rcases hedge l hl with hl0 | ⟨hl1, hl1'⟩
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩
          · simpa only [braidEj_eq_of_cartanMatrix_eq_zero hl0,
              braidEj_eq_of_cartanMatrix_eq_zero hm0] using serre_E R v hlm
          · exact nextEdge_braidE_reverse hm1 hl0
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩
          · rcases hpath l m hl1 hm0 with h0 | h1 | h2
            · rw [h0]
              exact nextEdge_assembly_serre_one _ (braidEj_commute_braidEj_of_disconnected hm0 h0)
            · exact qSerre_braidEj_braidEj_of_path (NeZero.ne v) hl1 hl1' h1 hm0 hs
            · exact nextEdge_braidE_forward_three (NeZero.ne v) hl1 hl1' h2 hm0 hs hc
          · have h0 := hleaf l m hl1 hm1 hlm
            rw [h0]
            exact nextEdge_assembly_serre_one _
              (braidEj_commute_braidEj_of_orthogonal_neighbours
                (NeZero.ne v) hl1 hm1 hlm h0 hs)
  serre_F l m hlm := by
    by_cases hl : l = i
    · subst l
      rcases hedge m hlm.symm with h0 | ⟨h1, _⟩
      · simp only [hlm.symm, ↓reduceIte, h0, sub_zero, Int.toNat_one,
          braidFj_eq_of_cartanMatrix_eq_zero h0]
        exact nextEdge_assembly_serre_one _ (nextEdge_assembly_braidFi_commute hlm.symm h0)
      · simpa only [hlm.symm, ↓reduceIte] using
          qSerre_braidFi_braidFj_of_cartanMatrix_eq_neg_one (R := R) h1 hq
    · by_cases hm : m = i
      · subst m
        rcases hedge l hl with h0 | ⟨h1, h1'⟩
        · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i l).mp h0
          simp only [hl, ↓reduceIte, h0', sub_zero, Int.toNat_one,
            braidFj_eq_of_cartanMatrix_eq_zero h0]
          exact nextEdge_assembly_serre_one _ (nextEdge_assembly_braidFi_commute hl h0).symm
        · simpa only [hl, ↓reduceIte] using
            qSerre_braidFj_braidFi_of_simply_laced_edge (R := R) h1 h1' hq
      · simp only [hl, hm, ↓reduceIte]
        rcases hedge l hl with hl0 | ⟨hl1, hl1'⟩
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩
          · simpa only [braidFj_eq_of_cartanMatrix_eq_zero hl0,
              braidFj_eq_of_cartanMatrix_eq_zero hm0] using serre_F R v hlm
          · exact nextEdge_braidF_reverse (NeZero.ne v) hm1 hl0
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩
          · rcases hpath l m hl1 hm0 with h0 | h1 | h2
            · rw [h0]
              exact nextEdge_assembly_serre_one _ (braidFj_commute_braidFj_of_disconnected hm0 h0)
            · exact qSerre_braidFj_braidFj_of_path (NeZero.ne v) hl1 hl1' h1 hm0 hs
            · exact nextEdge_braidF_forward_three (NeZero.ne v) hl1 hl1' h2 hm0 hs hc
          · have h0 := hleaf l m hl1 hm1 hlm
            rw [h0]
            exact nextEdge_assembly_serre_one _
              (braidFj_commute_braidFj_of_orthogonal_neighbours
                (NeZero.ne v) hl1 hm1 hlm h0 hs)

/-- Genuine quotient braid homomorphism with pairwise orthogonal neighbours.
Reconstructed from all defining relations, not from an assumed faithful action. -/
def nextEdgeBraid : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  lift (nextEdgeBraid_relations i hedge hleaf hpath hq hs hc)

@[simp] theorem nextEdgeBraid_E (l : I) :
    nextEdgeBraid i hedge hleaf hpath hq hs hc (E R v l) =
      if l = i then braidEi R i else braidEj R v i l := lift_E _ l

@[simp] theorem nextEdgeBraid_F (l : I) :
    nextEdgeBraid i hedge hleaf hpath hq hs hc (F R v l) =
      if l = i then braidFi R i else braidFj R v i l := lift_F _ l

@[simp] theorem nextEdgeBraid_K (μ : Y) :
    nextEdgeBraid i hedge hleaf hpath hq hs hc (K R v μ) = K R v (reflY R i μ) := lift_K _ μ

/-- Explicit inverse candidate, using the independently proved product reversal. -/
def nextEdgeBraidInv : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  (AlgHom.opComm braidReversalOp).comp
    ((nextEdgeBraid i hedge hleaf hpath hq hs hc).op.comp braidReversalOp)

/-- The inverse candidate is reversal-conjugation on the actual quotient. -/
theorem nextEdgeBraidInv_apply (x : QuantumGroup R v) :
    nextEdgeBraidInv i hedge hleaf hpath hq hs hc x =
      braidReversal (nextEdgeBraid i hedge hleaf hpath hq hs hc (braidReversal x)) := rfl

@[simp] theorem nextEdgeBraidInv_Ei :
    nextEdgeBraidInv i hedge hleaf hpath hq hs hc (E R v i) = braidInvEi R i := by
  simp [nextEdgeBraidInv_apply, braidEi, braidInvEi, braidReversal_mul, Kt]

@[simp] theorem nextEdgeBraidInv_Fi :
    nextEdgeBraidInv i hedge hleaf hpath hq hs hc (F R v i) = braidInvFi R i := by
  simp [nextEdgeBraidInv_apply, braidFi, braidInvFi, braidReversal_mul, Kt]

@[simp] theorem nextEdgeBraidInv_Ej (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = -1) :
    nextEdgeBraidInv i hedge hleaf hpath hq hs hc (E R v j) =
      E R v j * E R v i - (v ^ D.d i)⁻¹ • (E R v i * E R v j) := by
  simp [nextEdgeBraidInv_apply, hj, braidEj_eq_of_cartanMatrix_eq_neg_one hij,
    braidReversal_mul]

@[simp] theorem nextEdgeBraidInv_Fj (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = -1) :
    nextEdgeBraidInv i hedge hleaf hpath hq hs hc (F R v j) =
      F R v i * F R v j - (v ^ D.d i) • (F R v j * F R v i) := by
  simp [nextEdgeBraidInv_apply, hj,
    braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hij, braidReversal_mul]

/-- The inverse fixes every positive generator orthogonal to the chosen node. -/
@[simp] theorem nextEdgeBraidInv_E_of_orthogonal (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) :
    nextEdgeBraidInv i hedge hleaf hpath hq hs hc (E R v j) = E R v j := by
  simp [nextEdgeBraidInv_apply, hj, braidEj_eq_of_cartanMatrix_eq_zero hij]

/-- The inverse fixes every negative generator orthogonal to the chosen node. -/
@[simp] theorem nextEdgeBraidInv_F_of_orthogonal (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) :
    nextEdgeBraidInv i hedge hleaf hpath hq hs hc (F R v j) = F R v j := by
  simp [nextEdgeBraidInv_apply, hj, braidFj_eq_of_cartanMatrix_eq_zero hij]

@[simp] theorem nextEdgeBraidInv_K (μ : Y) :
    nextEdgeBraidInv i hedge hleaf hpath hq hs hc (K R v μ) = K R v (reflY R i μ) := by
  simp [nextEdgeBraidInv_apply]

/-- The explicit candidate is a right inverse on every quotient generator.
Reconstructed using the rank-independent degree-one recovery identities. -/
theorem nextEdgeBraid_comp_nextEdgeBraidInv :
    (nextEdgeBraid (R := R) i hedge hleaf hpath hq hs hc).comp
      (nextEdgeBraidInv i hedge hleaf hpath hq hs hc) = AlgHom.id k (QuantumGroup R v) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · by_cases hl : l = i
    · subst l
      simp only [AlgHom.comp_apply, nextEdgeBraidInv_Ei, braidInvEi, map_neg, map_mul,
        nextEdgeBraid_F, ↓reduceIte, braidFi, nextEdgeBraid_K, reflY_ktilde,
        mul_neg, neg_neg, AlgHom.id_apply, ← mul_assoc, K_mul_K_neg, one_mul]
    · rcases hedge l hl with h0 | ⟨h1, _⟩
      · simp [nextEdgeBraidInv_apply, hl,
          braidEj_eq_of_cartanMatrix_eq_zero h0]
      · simpa only [AlgHom.comp_apply,
          nextEdgeBraidInv_Ej i hedge hleaf hpath hq hs hc l hl h1,
          map_sub, map_mul, map_smul, nextEdgeBraid_E, hl, ↓reduceIte,
          AlgHom.id_apply] using a2Braid_recover_Ej (R := R) i l h1 hq
  · by_cases hl : l = i
    · subst l
      simp only [AlgHom.comp_apply, nextEdgeBraidInv_Fi, braidInvFi, map_neg, map_mul,
        nextEdgeBraid_E, ↓reduceIte, braidEi, Kt, nextEdgeBraid_K, reflY_ktilde,
        neg_mul, neg_neg, AlgHom.id_apply, mul_assoc, K_mul_K_neg, mul_one]
    · rcases hedge l hl with h0 | ⟨h1, _⟩
      · simp [nextEdgeBraidInv_apply, hl,
          braidFj_eq_of_cartanMatrix_eq_zero h0]
      · simpa only [AlgHom.comp_apply,
          nextEdgeBraidInv_Fj i hedge hleaf hpath hq hs hc l hl h1,
          map_sub, map_mul, map_smul, nextEdgeBraid_F, hl, ↓reduceIte,
          AlgHom.id_apply] using a2Braid_recover_Fj (R := R) i l h1 hq
  · simp

/-- The left-inverse identity follows by conjugating the proved right inverse
by the actual involutive product reversal, without finite-dimensionality. -/
theorem nextEdgeBraidInv_comp_nextEdgeBraid :
    (nextEdgeBraidInv (R := R) i hedge hleaf hpath hq hs hc).comp
      (nextEdgeBraid i hedge hleaf hpath hq hs hc) = AlgHom.id k (QuantumGroup R v) := by
  apply DFunLike.ext
  intro x
  have hconj := congrArg braidReversal
    (DFunLike.congr_fun
      (nextEdgeBraid_comp_nextEdgeBraidInv (R := R) i hedge hleaf hpath hq hs hc)
      (braidReversal x))
  simpa only [AlgHom.comp_apply, nextEdgeBraidInv_apply, braidReversal_involutive x,
    AlgHom.id_apply] using hconj

/-- Genuine braid algebra equivalence with pairwise orthogonal neighbours.
The field and root-datum lattice are arbitrary;
`v`, `q - q⁻¹`, `q + q⁻¹`, and `q ^ 4 + q ^ 2 + 1` are explicitly nonzero,
where `q = v ^ D.d i`. Outgoing next-edge entries are zero, -1 or -2;
reverse next-edge entries and untouched–untouched entries are unrestricted.
Reconstructed from all presentation relations and explicit two-sided recovery. -/
def nextEdgeBraidEquiv : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  AlgEquiv.ofAlgHom (nextEdgeBraid i hedge hleaf hpath hq hs hc)
    (nextEdgeBraidInv i hedge hleaf hpath hq hs hc)
    (nextEdgeBraid_comp_nextEdgeBraidInv i hedge hleaf hpath hq hs hc)
    (nextEdgeBraidInv_comp_nextEdgeBraid i hedge hleaf hpath hq hs hc)

/-- The broader constructed quotient map supplies the constructor-independent interface. -/
theorem nextEdgeBraid_hasBraidGeneratorImages :
    HasBraidGeneratorImages i (nextEdgeBraid (R := R) i hedge hleaf hpath hq hs hc) where
  map_E := nextEdgeBraid_E i hedge hleaf hpath hq hs hc
  map_F := nextEdgeBraid_F i hedge hleaf hpath hq hs hc
  map_K := nextEdgeBraid_K i hedge hleaf hpath hq hs hc

/-- Consumer theorem: the new actual map commutes with any constructed braid map at
an orthogonal centre. Existence at the new simple centre is proved, not assumed. -/
theorem nextEdgeBraid_comm_of_images
    {T : QuantumGroup R v →ₐ[k] QuantumGroup R v}
    (HT : HasBraidGeneratorImages j T) (hij : i ≠ j)
    (h0 : D.cartanMatrix i j = 0) :
    (nextEdgeBraid i hedge hleaf hpath hq hs hc).comp T =
      T.comp (nextEdgeBraid i hedge hleaf hpath hq hs hc) :=
  (nextEdgeBraid_hasBraidGeneratorImages i hedge hleaf hpath hq hs hc).comm HT hij h0

end QuantumGroup
