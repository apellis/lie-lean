/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.DoubleEdgeOther
import LieLean.Algebra.QuantumGroup.BraidAction.SimplyLaced

/-!
# Opposite-orientation terminal double-edge braid automorphism

## Main definitions and results
* `qSerre_braidEj_braidEj_of_double_other_path` and its negative companion:
  the missing connected degree-two target relations, from original Serre relations.
* `terminalDoubleOtherBraid_relations`: every defining relation for actual images.
* `terminalDoubleOtherBraid` and `terminalDoubleOtherBraidInv`: actual quotient maps.
* `terminalDoubleOtherBraidEquiv`: algebra automorphism with both compositions proved.

## References and scope
Reconstructed from the quotient presentation and repository recovery identities.
Arbitrary field, rank and root-datum lattice.
The centre has entries `a_ij = -1`, `a_ji = -2`; thus `q_i = q_j²`, derived
from symmetrization. All other centre edges are zero. Neighbour-to-untouched
edges are zero or mutual simple. Untouched-to-untouched entries are unrestricted.
Assume nonzero `v`, `q_i - q_i⁻¹`, and `q_i + q_i⁻¹`; necessity is not claimed.
The last condition is exactly the cancellation used by the degree-five certificate.
No two-node exhaustion, finite-rank, characteristic-zero, lattice-separation,
transformed-relation or recovery premise. Higher-rank braid relations and a
full all-node action are not established here.
-/
noncomputable section
namespace QuantumGroup
variable {k : Type*} [Field k]
section Ring
variable {B : Type*} [Ring B] [Algebra k B]

set_option maxHeartbeats 2000000 in
-- Exact degree-five certificate, with the two distinct Serre parameters.
private theorem other_path_positive (a b c : B) (q : k) (hq : q ≠ 0)
    (hS : qSerre (q ^ 2) 2 a b = 0) (hU : qSerre q 2 b c = 0)
    (hac : Commute a c) (hn : q ^ 2 + (q ^ 2)⁻¹ ≠ 0) :
    qSerre q 2 (a * b - q⁻¹ ^ 2 • (b * a)) c = 0 := by
  have h0 := congrArg (fun z : B ↦ z * (b * c)) hS
  have h1 := congrArg (fun z : B ↦ b * (z * c)) hS
  have h2 := congrArg (fun z : B ↦ b * (c * z)) hS
  have h3 := congrArg (fun z : B ↦ z * (c * b)) hS
  have h4 := congrArg (fun z : B ↦ c * (z * b)) hS
  have h5 := congrArg (fun z : B ↦ c * (b * z)) hS
  have h6 := congrArg (fun z : B ↦ z * (a * a)) hU
  have h7 := congrArg (fun z : B ↦ a * (z * a)) hU
  have h8 := congrArg (fun z : B ↦ a * (a * z)) hU
  have hca (z : B) : c * (a * z) = a * (c * z) := by
    rw [← mul_assoc, hac.symm.eq, mul_assoc]
  apply (smul_eq_zero.mp (show (q ^ 2 + (q ^ 2)⁻¹) •
    qSerre q 2 (a * b - q⁻¹ ^ 2 • (b * a)) c = 0 from ?_)).resolve_left hn
  simp only [qSerre, Finset.sum_range_succ, Finset.sum_range_zero, qBinomial,
    Nat.reduceSub, pow_succ, pow_zero, mul_one, one_mul, mul_zero, zero_mul, add_zero,
    zero_add, one_smul, mul_neg, neg_mul, neg_neg, mul_sub, sub_mul, mul_add,
    add_mul, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_smul,
    mul_assoc, hac.symm.eq, hca] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  linear_combination (norm := (match_scalars <;> field_simp [hq] <;> ring))
    -h0 - q⁻¹ ^ 4 • h1 + (q⁻¹ ^ 5 + q⁻¹ ^ 3) • h2 +
      (q + q⁻¹) • h3 - h4 - q⁻¹ ^ 4 • h5 + q⁻¹ ^ 4 • h6 -
      (1 + q⁻¹ ^ 4) • h7 + h8
end Ring

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j l : I}

/-- Connected forward quadratic relation at the opposite double terminal.
Reconstructed certificate; `q_i = q_j²` is derived, not assumed. -/
theorem qSerre_braidEj_braidEj_of_double_other_path
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -1)
    (hji : D.cartanMatrix j i = -2) (hjl : D.cartanMatrix j l = -1)
    (hil : D.cartanMatrix i l = 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j l).toNat
      (braidEj R v i j) (braidEj R v i l) = 0 := by
  have hij' : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at hij
    norm_num at hij
  have hjl' : j ≠ l := by
    rintro rfl
    rw [D.cartanMatrix_self] at hjl
    norm_num at hjl
  have hp := parameter_eq_square_of_double_edge (v := v) hji hij
  have hS : qSerre ((v ^ D.d j) ^ 2) 2 (E R v i) (E R v j) = 0 := by
    simpa only [hij, hp, Int.reduceSub, Int.reduceToNat] using serre_E R v hij'
  have hU : qSerre (v ^ D.d j) 2 (E R v j) (E R v l) = 0 := by
    simpa only [hjl, Int.reduceSub, Int.reduceToNat] using serre_E R v hjl'
  rw [braidEj_eq_of_cartanMatrix_eq_neg_one hij,
    braidEj_eq_of_cartanMatrix_eq_zero hil, hp, ← inv_pow, hjl]
  exact other_path_positive _ _ _ _ (pow_ne_zero _ hv) hS hU
    (E_commute_E_of_cartanMatrix_eq_zero hil) (by simpa only [hp] using hs)

/-- Negative connected forward quadratic relation via the actual Chevalley map.
Reconstructed; cancellation only uses its proved nonzero scalar factor. -/
theorem qSerre_braidFj_braidFj_of_double_other_path
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -1)
    (hji : D.cartanMatrix j i = -2) (hjl : D.cartanMatrix j l = -1)
    (hil : D.cartanMatrix i l = 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0) :
    qSerre (v ^ D.d j) (1 - D.cartanMatrix j l).toNat
      (braidFj R v i j) (braidFj R v i l) = 0 := by
  have h := congrArg (chevalley R v)
    (qSerre_braidEj_braidEj_of_double_other_path (R := R) hv hij hji hjl hil hs)
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

private theorem terminal_other_serre_one (q : k) {a b : QuantumGroup R v}
    (h : Commute a b) : qSerre q 1 a b = 0 := by
  simp [qSerre, Finset.sum_range_succ, h.eq]

private theorem terminal_other_braidEi_commute (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) : Commute (braidEi R i) (E R v j) := by
  have hK : Commute (K R v (ktilde R i)) (E R v j) := by
    change K R v (ktilde R i) * E R v j = E R v j * K R v (ktilde R i)
    simp [K_mul_E, root_ktilde, hij]
  exact ((show Commute (F R v i) (E R v j) from (E_mul_F_of_ne hj).symm).mul_left
    hK).neg_left

private theorem terminal_other_braidFi_commute (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) : Commute (braidFi R i) (F R v j) := by
  have hK : Commute (K R v (-ktilde R i)) (F R v j) := by
    change K R v (-ktilde R i) * F R v j = F R v j * K R v (-ktilde R i)
    simp [K_mul_F, map_neg, root_ktilde, hij]
  exact (hK.mul_left (E_mul_F_of_ne (Ne.symm hj))).neg_left

variable [NeZero v] (i j : I) (hij : i ≠ j)
  (hterminal : ∀ l, l ≠ i → l ≠ j → D.cartanMatrix i l = 0)
  (hpath : ∀ l, l ≠ i → l ≠ j → D.cartanMatrix j l = 0 ∨
    (D.cartanMatrix j l = -1 ∧ D.cartanMatrix l j = -1))
  (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -2)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)

include hij hterminal hpath h h' hq hs in
/-- All defining relations of the actual terminal-double braid images.
Reconstructed by exhaustive centre/neighbour/untouched cases. -/
theorem terminalDoubleOtherBraid_relations :
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
          by_cases hlj : l = j
          · subst l
            simpa only [hl, ↓reduceIte] using
              braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_one
                (R := R) (NeZero.ne v) h hq
          · simpa only [hl, ↓reduceIte] using
              braidEj_mul_braidFj_sub_of_cartanMatrix_eq_zero
                (R := R) (v := v) (hterminal l hl hlj)
        · simp only [hl, hm, hlm, ↓reduceIte]
          by_cases hlj : l = j
          · subst l
            exact sub_eq_zero.mpr
              (braidEj_commute_braidFj_of_right_orthogonal (Ne.symm hm) hlm
                (hterminal m hm (Ne.symm hlm))).eq
          · exact sub_eq_zero.mpr
              (braidEj_commute_braidFj_of_left_orthogonal hl hlm (hterminal l hl hlj)).eq
  serre_E l m hlm := by
    by_cases hl : l = i
    · subst l
      by_cases hmj : m = j
      · subst m
        simpa only [hij.symm, ↓reduceIte] using
          qSerre_braidEi_braidEj_of_cartanMatrix_eq_neg_one
            (R := R) h hq
      · have h0 := hterminal m hlm.symm hmj
        simp only [hlm.symm, ↓reduceIte, h0, sub_zero, Int.toNat_one,
          braidEj_eq_of_cartanMatrix_eq_zero h0]
        exact terminal_other_serre_one _ (terminal_other_braidEi_commute hlm.symm h0)
    · by_cases hm : m = i
      · subst m
        by_cases hlj : l = j
        · subst l
          simpa only [hij.symm, ↓reduceIte] using
            qSerre_braidEj_braidEi_of_double_edge_other (R := R) h h' hq
        · have h0 := hterminal l hl hlj
          have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i l).mp h0
          simp only [hl, ↓reduceIte, h0', sub_zero, Int.toNat_one,
            braidEj_eq_of_cartanMatrix_eq_zero h0]
          exact terminal_other_serre_one _ (terminal_other_braidEi_commute hl h0).symm
      · simp only [hl, hm, ↓reduceIte]
        by_cases hlj : l = j
        · subst l
          have hm0 := hterminal m hm hlm.symm
          rcases hpath m hm hlm.symm with h0 | ⟨h1, _⟩
          · rw [h0]
            exact terminal_other_serre_one _
              (braidEj_commute_braidEj_of_disconnected hm0 h0)
          · exact qSerre_braidEj_braidEj_of_double_other_path
              (NeZero.ne v) h h' h1 hm0 hs
        · have hl0 := hterminal l hl hlj
          by_cases hmj : m = j
          · subst m
            rcases hpath l hl hlj with h0 | ⟨_, h1⟩
            · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm j l).mp h0
              rw [h0']
              exact terminal_other_serre_one _
                (braidEj_commute_braidEj_of_disconnected hl0 h0).symm
            · exact qSerre_braidEj_braidEj_of_path_reverse
                h h1 hl0
          · simpa only [braidEj_eq_of_cartanMatrix_eq_zero hl0,
              braidEj_eq_of_cartanMatrix_eq_zero (hterminal m hm hmj)] using
              serre_E R v hlm
  serre_F l m hlm := by
    by_cases hl : l = i
    · subst l
      by_cases hmj : m = j
      · subst m
        simpa only [hij.symm, ↓reduceIte] using
          qSerre_braidFi_braidFj_of_cartanMatrix_eq_neg_one
            (R := R) h hq
      · have h0 := hterminal m hlm.symm hmj
        simp only [hlm.symm, ↓reduceIte, h0, sub_zero, Int.toNat_one,
          braidFj_eq_of_cartanMatrix_eq_zero h0]
        exact terminal_other_serre_one _ (terminal_other_braidFi_commute hlm.symm h0)
    · by_cases hm : m = i
      · subst m
        by_cases hlj : l = j
        · subst l
          simpa only [hij.symm, ↓reduceIte] using
            qSerre_braidFj_braidFi_of_double_edge_other (R := R) h h' hq
        · have h0 := hterminal l hl hlj
          have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i l).mp h0
          simp only [hl, ↓reduceIte, h0', sub_zero, Int.toNat_one,
            braidFj_eq_of_cartanMatrix_eq_zero h0]
          exact terminal_other_serre_one _ (terminal_other_braidFi_commute hl h0).symm
      · simp only [hl, hm, ↓reduceIte]
        by_cases hlj : l = j
        · subst l
          have hm0 := hterminal m hm hlm.symm
          rcases hpath m hm hlm.symm with h0 | ⟨h1, _⟩
          · rw [h0]
            exact terminal_other_serre_one _
              (braidFj_commute_braidFj_of_disconnected hm0 h0)
          · exact qSerre_braidFj_braidFj_of_double_other_path
              (NeZero.ne v) h h' h1 hm0 hs
        · have hl0 := hterminal l hl hlj
          by_cases hmj : m = j
          · subst m
            rcases hpath l hl hlj with h0 | ⟨_, h1⟩
            · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm j l).mp h0
              rw [h0']
              exact terminal_other_serre_one _
                (braidFj_commute_braidFj_of_disconnected hl0 h0).symm
            · exact qSerre_braidFj_braidFj_of_path_reverse
                (NeZero.ne v) h h1 hl0
          · simpa only [braidFj_eq_of_cartanMatrix_eq_zero hl0,
              braidFj_eq_of_cartanMatrix_eq_zero (hterminal m hm hmj)] using
              serre_F R v hlm

/-- The genuine double-edge braid algebra homomorphism on the quotient presentation.
No relation package or faithful action is assumed. Reconstructed proof. -/
def terminalDoubleOtherBraid : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  lift (terminalDoubleOtherBraid_relations i j hij hterminal hpath h h' hq hs)

@[simp] theorem terminalDoubleOtherBraid_E (l : I) :
    terminalDoubleOtherBraid i j hij hterminal hpath h h' hq hs (E R v l) =
      if l = i then braidEi R i else braidEj R v i l := lift_E _ l

@[simp] theorem terminalDoubleOtherBraid_F (l : I) :
    terminalDoubleOtherBraid i j hij hterminal hpath h h' hq hs (F R v l) =
      if l = i then braidFi R i else braidFj R v i l := lift_F _ l

@[simp] theorem terminalDoubleOtherBraid_K (μ : Y) :
    terminalDoubleOtherBraid i j hij hterminal hpath h h' hq hs (K R v μ) =
      K R v (reflY R i μ) := lift_K _ μ


/-- Explicit inverse candidate obtained by conjugating the proved braid homomorphism
by the proved product-reversal anti-homomorphism. No extra relations are assumed. -/
def terminalDoubleOtherBraidInv : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  (AlgHom.opComm braidReversalOp).comp
    ((terminalDoubleOtherBraid i j hij hterminal hpath h h' hq hs).op.comp braidReversalOp)

/-- The inverse candidate is reversal-conjugation on every element. -/
theorem terminalDoubleOtherBraidInv_apply (x : QuantumGroup R v) :
    terminalDoubleOtherBraidInv i j hij hterminal hpath h h' hq hs x =
      braidReversal
        (terminalDoubleOtherBraid i j hij hterminal hpath h h' hq hs (braidReversal x)) := rfl

@[simp] theorem terminalDoubleOtherBraidInv_Ei :
    terminalDoubleOtherBraidInv i j hij hterminal hpath h h' hq hs (E R v i) = braidInvEi R i := by
  simp [terminalDoubleOtherBraidInv_apply, braidEi, braidInvEi, braidReversal_mul, Kt]

@[simp] theorem terminalDoubleOtherBraidInv_Fi :
    terminalDoubleOtherBraidInv i j hij hterminal hpath h h' hq hs (F R v i) = braidInvFi R i := by
  simp [terminalDoubleOtherBraidInv_apply, braidFi, braidInvFi, braidReversal_mul, Kt]

@[simp] theorem terminalDoubleOtherBraidInv_Ej :
    terminalDoubleOtherBraidInv i j hij hterminal hpath h h' hq hs (E R v j) =
      E R v j * E R v i - (v ^ D.d i)⁻¹ • (E R v i * E R v j) := by
  simp [terminalDoubleOtherBraidInv_apply, hij.symm,
    braidEj_eq_of_cartanMatrix_eq_neg_one h, braidReversal_mul]

@[simp] theorem terminalDoubleOtherBraidInv_Fj :
    terminalDoubleOtherBraidInv i j hij hterminal hpath h h' hq hs (F R v j) =
      F R v i * F R v j - (v ^ D.d i) • (F R v j * F R v i) := by
  simp [terminalDoubleOtherBraidInv_apply, hij.symm,
    braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h, braidReversal_mul]

/-- The inverse fixes every positive generator orthogonal to the chosen node. -/
@[simp] theorem terminalDoubleOtherBraidInv_E_of_orthogonal (l : I) (hl : l ≠ i)
    (hil : D.cartanMatrix i l = 0) :
    terminalDoubleOtherBraidInv i j hij hterminal hpath h h' hq hs (E R v l) = E R v l := by
  simp [terminalDoubleOtherBraidInv_apply, hl, braidEj_eq_of_cartanMatrix_eq_zero hil]

/-- The inverse fixes every negative generator orthogonal to the chosen node. -/
@[simp] theorem terminalDoubleOtherBraidInv_F_of_orthogonal (l : I) (hl : l ≠ i)
    (hil : D.cartanMatrix i l = 0) :
    terminalDoubleOtherBraidInv i j hij hterminal hpath h h' hq hs (F R v l) = F R v l := by
  simp [terminalDoubleOtherBraidInv_apply, hl, braidFj_eq_of_cartanMatrix_eq_zero hil]

@[simp] theorem terminalDoubleOtherBraidInv_K (μ : Y) :
    terminalDoubleOtherBraidInv i j hij hterminal hpath h h' hq hs (K R v μ) =
      K R v (reflY R i μ) := by
  simp [terminalDoubleOtherBraidInv_apply]


/-- The candidate is a right inverse, checked on both Chevalley colors and all toral
lattice generators, not inferred from a surjectivity assertion. -/
theorem terminalDoubleOtherBraid_comp_terminalDoubleOtherBraidInv :
    (terminalDoubleOtherBraid (R := R) i j hij hterminal hpath h h' hq hs).comp
      (terminalDoubleOtherBraidInv i j hij hterminal hpath h h' hq hs) =
        AlgHom.id k (QuantumGroup R v) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · by_cases hl : l = i
    · subst l
      simp only [AlgHom.comp_apply, terminalDoubleOtherBraidInv_Ei, braidInvEi, map_neg, map_mul,
        terminalDoubleOtherBraid_F, ↓reduceIte, braidFi, terminalDoubleOtherBraid_K, reflY_ktilde,
        mul_neg, neg_neg, AlgHom.id_apply, ← mul_assoc, K_mul_K_neg, one_mul]
    · by_cases hlj : l = j
      · subst l
        simpa only [AlgHom.comp_apply, terminalDoubleOtherBraidInv_Ej, map_add, map_sub, map_mul,
          map_pow, map_smul, terminalDoubleOtherBraid_E, hij.symm, ↓reduceIte,
          AlgHom.id_apply] using
          a2Braid_recover_Ej (R := R) i j h hq
      · simp [terminalDoubleOtherBraidInv_apply, hl,
          braidEj_eq_of_cartanMatrix_eq_zero (hterminal l hl hlj)]
  · by_cases hl : l = i
    · subst l
      simp only [AlgHom.comp_apply, terminalDoubleOtherBraidInv_Fi, braidInvFi, map_neg, map_mul,
        terminalDoubleOtherBraid_E, ↓reduceIte, braidEi, Kt, terminalDoubleOtherBraid_K,
        reflY_ktilde,
        neg_mul, neg_neg, AlgHom.id_apply, mul_assoc, K_mul_K_neg, mul_one]
    · by_cases hlj : l = j
      · subst l
        simpa only [AlgHom.comp_apply, terminalDoubleOtherBraidInv_Fj, map_add, map_sub, map_mul,
          map_pow, map_smul, terminalDoubleOtherBraid_F, hij.symm, ↓reduceIte,
          AlgHom.id_apply] using
          a2Braid_recover_Fj (R := R) i j h hq
      · simp [terminalDoubleOtherBraidInv_apply, hl,
          braidFj_eq_of_cartanMatrix_eq_zero (hterminal l hl hlj)]
  · simp

/-- The candidate is also a left inverse. Conjugating the proved generator-level
right-inverse identity by the involutive product reversal gives this identity. -/
theorem terminalDoubleOtherBraidInv_comp_terminalDoubleOtherBraid :
    (terminalDoubleOtherBraidInv (R := R) i j hij hterminal hpath h h' hq hs).comp
      (terminalDoubleOtherBraid i j hij hterminal hpath h h' hq hs) =
        AlgHom.id k (QuantumGroup R v) := by
  apply DFunLike.ext
  intro x
  have hc := congrArg braidReversal
    (DFunLike.congr_fun
      (terminalDoubleOtherBraid_comp_terminalDoubleOtherBraidInv
        (R := R) i j hij hterminal hpath h h' hq hs)
      (braidReversal x))
  simpa only [AlgHom.comp_apply, terminalDoubleOtherBraidInv_apply, braidReversal_involutive x,
    AlgHom.id_apply] using hc

/-- Lusztig's actual double-edge braid algebra equivalence, with explicit two-sided inverse.
Assumptions: a terminal `(-1,-2)` centre, zero or mutual-simple next edges,
arbitrary ambient rank, field and root-datum lattice, nonzero `v`, centre quantum
sum and difference nonzero. No parameter-optimality claim. Reconstructed from the
presentation; no transformed-relation, inverse or faithful-action premise. -/
def terminalDoubleOtherBraidEquiv : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  AlgEquiv.ofAlgHom (terminalDoubleOtherBraid i j hij hterminal hpath h h' hq hs)
    (terminalDoubleOtherBraidInv i j hij hterminal hpath h h' hq hs)
    (terminalDoubleOtherBraid_comp_terminalDoubleOtherBraidInv i j hij hterminal hpath h h' hq hs)
    (terminalDoubleOtherBraidInv_comp_terminalDoubleOtherBraid i j hij hterminal hpath h h' hq hs)

end QuantumGroup
