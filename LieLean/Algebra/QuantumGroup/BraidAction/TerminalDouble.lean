/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.DoublePathSerre
import LieLean.Algebra.QuantumGroup.BraidAction.DoubleEdge
import LieLean.Algebra.QuantumGroup.BraidAction.SimplyLaced

/-!
# Quantum braid automorphism at a terminal double node

## Main definitions and results
* `terminalDoubleBraid_relations`: all defining quotient relations.
* `terminalDoubleBraid`: genuine quotient lift.
* `terminalDoubleBraidInv`: explicit product-reversal conjugate inverse.
* `terminalDoubleBraidEquiv`: algebra automorphism, with both compositions proved.

## Scope and references
Reconstructed from the defining presentation and published repository recovery
identities; no primary source consulted. The centre `i` has exactly one
nonorthogonal neighbour `j`, with directed Cartan entries `(-2,-1)`.
Edges from `j` to other nodes are zero or mutual simple; entries between two
untouched nodes are unrestricted. Neither finite rank nor characteristic zero
nor any coroot-span or lattice-separation assumption is imposed.
For `q = v ^ D.d i`, assume `v`, `q-q⁻¹`, `q+q⁻¹`, and
`(1+q⁻⁴)(1+q⁻²+q⁻⁴)` are nonzero. Necessity is not claimed.
This covers connected higher-rank terminal-double chains in the stated Cartan
orientation, not just a two-node diagram. It does not construct the opposite
orientation, an action by all nodes, higher braid relations, or faithfulness.
-/

noncomputable section
namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j : I}

private theorem terminal_serre_one (q : k) {a b : QuantumGroup R v}
    (h : Commute a b) : qSerre q 1 a b = 0 := by
  simp [qSerre, Finset.sum_range_succ, h.eq]

private theorem terminal_braidEi_commute (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) : Commute (braidEi R i) (E R v j) := by
  have hK : Commute (K R v (ktilde R i)) (E R v j) := by
    change K R v (ktilde R i) * E R v j = E R v j * K R v (ktilde R i)
    simp [K_mul_E, root_ktilde, hij]
  exact ((show Commute (F R v i) (E R v j) from (E_mul_F_of_ne hj).symm).mul_left
    hK).neg_left

private theorem terminal_braidFi_commute (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) : Commute (braidFi R i) (F R v j) := by
  have hK : Commute (K R v (-ktilde R i)) (F R v j) := by
    change K R v (-ktilde R i) * F R v j = F R v j * K R v (-ktilde R i)
    simp [K_mul_F, map_neg, root_ktilde, hij]
  exact (hK.mul_left (E_mul_F_of_ne (Ne.symm hj))).neg_left

variable [NeZero v] (i j : I) (hij : i ≠ j)
  (hterminal : ∀ l, l ≠ i → l ≠ j → D.cartanMatrix i l = 0)
  (hpath : ∀ l, l ≠ i → l ≠ j → D.cartanMatrix j l = 0 ∨
    (D.cartanMatrix j l = -1 ∧ D.cartanMatrix l j = -1))
  (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)
  (hn : (1 + (v ^ D.d i)⁻¹ ^ 4) *
    (1 + (v ^ D.d i)⁻¹ ^ 2 + (v ^ D.d i)⁻¹ ^ 4) ≠ 0)

include hij hterminal hpath h h' hq hs hn in
/-- All defining relations of the actual terminal-double braid images.
Reconstructed by exhaustive centre/neighbour/untouched cases. -/
theorem terminalDoubleBraid_relations :
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
              braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_two
                (R := R) (NeZero.ne v) h hq hs
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
          qSerre_braidEi_braidEj_of_cartanMatrix_eq_neg_two
            (R := R) (NeZero.ne v) h
      · have h0 := hterminal m hlm.symm hmj
        simp only [hlm.symm, ↓reduceIte, h0, sub_zero, Int.toNat_one,
          braidEj_eq_of_cartanMatrix_eq_zero h0]
        exact terminal_serre_one _ (terminal_braidEi_commute hlm.symm h0)
    · by_cases hm : m = i
      · subst m
        by_cases hlj : l = j
        · subst l
          simpa only [hij.symm, ↓reduceIte] using
            qSerre_braidEj_braidEi_of_double_edge (R := R) (NeZero.ne v) h h'
        · have h0 := hterminal l hl hlj
          have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i l).mp h0
          simp only [hl, ↓reduceIte, h0', sub_zero, Int.toNat_one,
            braidEj_eq_of_cartanMatrix_eq_zero h0]
          exact terminal_serre_one _ (terminal_braidEi_commute hl h0).symm
      · simp only [hl, hm, ↓reduceIte]
        by_cases hlj : l = j
        · subst l
          have hm0 := hterminal m hm hlm.symm
          rcases hpath m hm hlm.symm with h0 | ⟨h1, _⟩
          · rw [h0]
            exact terminal_serre_one _
              (braidEj_commute_braidEj_of_disconnected hm0 h0)
          · exact qSerre_braidEj_braidEj_of_double_path
              (NeZero.ne v) h h' h1 hm0 hn
        · have hl0 := hterminal l hl hlj
          by_cases hmj : m = j
          · subst m
            rcases hpath l hl hlj with h0 | ⟨_, h1⟩
            · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm j l).mp h0
              rw [h0']
              exact terminal_serre_one _
                (braidEj_commute_braidEj_of_disconnected hl0 h0).symm
            · exact qSerre_braidEj_braidEj_of_double_path_reverse
                (NeZero.ne v) h h1 hl0
          · simpa only [braidEj_eq_of_cartanMatrix_eq_zero hl0,
              braidEj_eq_of_cartanMatrix_eq_zero (hterminal m hm hmj)] using
              serre_E R v hlm
  serre_F l m hlm := by
    by_cases hl : l = i
    · subst l
      by_cases hmj : m = j
      · subst m
        simpa only [hij.symm, ↓reduceIte] using
          qSerre_braidFi_braidFj_of_cartanMatrix_eq_neg_two
            (R := R) (NeZero.ne v) h
      · have h0 := hterminal m hlm.symm hmj
        simp only [hlm.symm, ↓reduceIte, h0, sub_zero, Int.toNat_one,
          braidFj_eq_of_cartanMatrix_eq_zero h0]
        exact terminal_serre_one _ (terminal_braidFi_commute hlm.symm h0)
    · by_cases hm : m = i
      · subst m
        by_cases hlj : l = j
        · subst l
          simpa only [hij.symm, ↓reduceIte] using
            qSerre_braidFj_braidFi_of_double_edge (R := R) (NeZero.ne v) h h'
        · have h0 := hterminal l hl hlj
          have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i l).mp h0
          simp only [hl, ↓reduceIte, h0', sub_zero, Int.toNat_one,
            braidFj_eq_of_cartanMatrix_eq_zero h0]
          exact terminal_serre_one _ (terminal_braidFi_commute hl h0).symm
      · simp only [hl, hm, ↓reduceIte]
        by_cases hlj : l = j
        · subst l
          have hm0 := hterminal m hm hlm.symm
          rcases hpath m hm hlm.symm with h0 | ⟨h1, _⟩
          · rw [h0]
            exact terminal_serre_one _
              (braidFj_commute_braidFj_of_disconnected hm0 h0)
          · exact qSerre_braidFj_braidFj_of_double_path
              (NeZero.ne v) h h' h1 hm0 hn
        · have hl0 := hterminal l hl hlj
          by_cases hmj : m = j
          · subst m
            rcases hpath l hl hlj with h0 | ⟨_, h1⟩
            · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm j l).mp h0
              rw [h0']
              exact terminal_serre_one _
                (braidFj_commute_braidFj_of_disconnected hl0 h0).symm
            · exact qSerre_braidFj_braidFj_of_double_path_reverse
                (NeZero.ne v) h h1 hl0
          · simpa only [braidFj_eq_of_cartanMatrix_eq_zero hl0,
              braidFj_eq_of_cartanMatrix_eq_zero (hterminal m hm hmj)] using
              serre_F R v hlm

/-- The genuine double-edge braid algebra homomorphism on the quotient presentation.
No relation package or faithful action is assumed. Reconstructed proof. -/
def terminalDoubleBraid : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  lift (terminalDoubleBraid_relations i j hij hterminal hpath h h' hq hs hn)

@[simp] theorem terminalDoubleBraid_E (l : I) :
    terminalDoubleBraid i j hij hterminal hpath h h' hq hs hn (E R v l) =
      if l = i then braidEi R i else braidEj R v i l := lift_E _ l

@[simp] theorem terminalDoubleBraid_F (l : I) :
    terminalDoubleBraid i j hij hterminal hpath h h' hq hs hn (F R v l) =
      if l = i then braidFi R i else braidFj R v i l := lift_F _ l

@[simp] theorem terminalDoubleBraid_K (μ : Y) :
    terminalDoubleBraid i j hij hterminal hpath h h' hq hs hn (K R v μ) =
      K R v (reflY R i μ) := lift_K _ μ


/-- Explicit inverse candidate obtained by conjugating the proved braid homomorphism
by the proved product-reversal anti-homomorphism. No extra relations are assumed. -/
def terminalDoubleBraidInv : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  (AlgHom.opComm braidReversalOp).comp
    ((terminalDoubleBraid i j hij hterminal hpath h h' hq hs hn).op.comp braidReversalOp)

/-- The inverse candidate is reversal-conjugation on every element. -/
theorem terminalDoubleBraidInv_apply (x : QuantumGroup R v) :
    terminalDoubleBraidInv i j hij hterminal hpath h h' hq hs hn x =
      braidReversal
        (terminalDoubleBraid i j hij hterminal hpath h h' hq hs hn (braidReversal x)) := rfl

@[simp] theorem terminalDoubleBraidInv_Ei :
    terminalDoubleBraidInv i j hij hterminal hpath h h' hq hs hn (E R v i) = braidInvEi R i := by
  simp [terminalDoubleBraidInv_apply, braidEi, braidInvEi, braidReversal_mul, Kt]

@[simp] theorem terminalDoubleBraidInv_Fi :
    terminalDoubleBraidInv i j hij hterminal hpath h h' hq hs hn (F R v i) = braidInvFi R i := by
  simp [terminalDoubleBraidInv_apply, braidFi, braidInvFi, braidReversal_mul, Kt]

@[simp] theorem terminalDoubleBraidInv_Ej :
    terminalDoubleBraidInv i j hij hterminal hpath h h' hq hs hn (E R v j) =
      (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ •
        (E R v j * E R v i ^ 2 -
          ((v ^ D.d i + (v ^ D.d i)⁻¹) * (v ^ D.d i)⁻¹) •
            (E R v i * E R v j * E R v i) +
          (v ^ D.d i)⁻¹ ^ 2 • (E R v i ^ 2 * E R v j)) := by
  simp [terminalDoubleBraidInv_apply, hij.symm, braidEj_eq_of_cartanMatrix_eq_neg_two h,
    pow_two, braidReversal_mul, mul_assoc]

@[simp] theorem terminalDoubleBraidInv_Fj :
    terminalDoubleBraidInv i j hij hterminal hpath h h' hq hs hn (F R v j) =
      (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ •
        ((v ^ D.d i) ^ 2 • (F R v j * F R v i ^ 2) -
          ((v ^ D.d i + (v ^ D.d i)⁻¹) * v ^ D.d i) •
            (F R v i * F R v j * F R v i) + F R v i ^ 2 * F R v j) := by
  simp [terminalDoubleBraidInv_apply, hij.symm,
    braidFj_eq_of_cartanMatrix_eq_neg_two (NeZero.ne v) h,
    pow_two, braidReversal_mul, mul_assoc]

/-- The inverse fixes every positive generator orthogonal to the chosen node. -/
@[simp] theorem terminalDoubleBraidInv_E_of_orthogonal (l : I) (hl : l ≠ i)
    (hil : D.cartanMatrix i l = 0) :
    terminalDoubleBraidInv i j hij hterminal hpath h h' hq hs hn (E R v l) = E R v l := by
  simp [terminalDoubleBraidInv_apply, hl, braidEj_eq_of_cartanMatrix_eq_zero hil]

/-- The inverse fixes every negative generator orthogonal to the chosen node. -/
@[simp] theorem terminalDoubleBraidInv_F_of_orthogonal (l : I) (hl : l ≠ i)
    (hil : D.cartanMatrix i l = 0) :
    terminalDoubleBraidInv i j hij hterminal hpath h h' hq hs hn (F R v l) = F R v l := by
  simp [terminalDoubleBraidInv_apply, hl, braidFj_eq_of_cartanMatrix_eq_zero hil]

@[simp] theorem terminalDoubleBraidInv_K (μ : Y) :
    terminalDoubleBraidInv i j hij hterminal hpath h h' hq hs hn (K R v μ) =
      K R v (reflY R i μ) := by
  simp [terminalDoubleBraidInv_apply]


/-- The candidate is a right inverse, checked on both Chevalley colors and all toral
lattice generators, not inferred from a surjectivity assertion. -/
theorem terminalDoubleBraid_comp_terminalDoubleBraidInv :
    (terminalDoubleBraid (R := R) i j hij hterminal hpath h h' hq hs hn).comp
      (terminalDoubleBraidInv i j hij hterminal hpath h h' hq hs hn) =
        AlgHom.id k (QuantumGroup R v) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · by_cases hl : l = i
    · subst l
      simp only [AlgHom.comp_apply, terminalDoubleBraidInv_Ei, braidInvEi, map_neg, map_mul,
        terminalDoubleBraid_F, ↓reduceIte, braidFi, terminalDoubleBraid_K, reflY_ktilde,
        mul_neg, neg_neg, AlgHom.id_apply, ← mul_assoc, K_mul_K_neg, one_mul]
    · by_cases hlj : l = j
      · subst l
        simpa only [AlgHom.comp_apply, terminalDoubleBraidInv_Ej, map_add, map_sub, map_mul,
          map_pow, map_smul, terminalDoubleBraid_E, hij.symm, ↓reduceIte, AlgHom.id_apply] using
          doubleEdge_recover_Ej (NeZero.ne v) h hq hs
      · simp [terminalDoubleBraidInv_apply, hl,
          braidEj_eq_of_cartanMatrix_eq_zero (hterminal l hl hlj)]
  · by_cases hl : l = i
    · subst l
      simp only [AlgHom.comp_apply, terminalDoubleBraidInv_Fi, braidInvFi, map_neg, map_mul,
        terminalDoubleBraid_E, ↓reduceIte, braidEi, Kt, terminalDoubleBraid_K, reflY_ktilde,
        neg_mul, neg_neg, AlgHom.id_apply, mul_assoc, K_mul_K_neg, mul_one]
    · by_cases hlj : l = j
      · subst l
        simpa only [AlgHom.comp_apply, terminalDoubleBraidInv_Fj, map_add, map_sub, map_mul,
          map_pow, map_smul, terminalDoubleBraid_F, hij.symm, ↓reduceIte, AlgHom.id_apply] using
          doubleEdge_recover_Fj (NeZero.ne v) h hq hs
      · simp [terminalDoubleBraidInv_apply, hl,
          braidFj_eq_of_cartanMatrix_eq_zero (hterminal l hl hlj)]
  · simp

/-- The candidate is also a left inverse. Conjugating the proved generator-level
right-inverse identity by the involutive product reversal gives this identity. -/
theorem terminalDoubleBraidInv_comp_terminalDoubleBraid :
    (terminalDoubleBraidInv (R := R) i j hij hterminal hpath h h' hq hs hn).comp
      (terminalDoubleBraid i j hij hterminal hpath h h' hq hs hn) =
        AlgHom.id k (QuantumGroup R v) := by
  apply DFunLike.ext
  intro x
  have hc := congrArg braidReversal
    (DFunLike.congr_fun
      (terminalDoubleBraid_comp_terminalDoubleBraidInv
        (R := R) i j hij hterminal hpath h h' hq hs hn)
      (braidReversal x))
  simpa only [AlgHom.comp_apply, terminalDoubleBraidInv_apply, braidReversal_involutive x,
    AlgHom.id_apply] using hc

/-- Lusztig's actual double-edge braid algebra equivalence, with explicit two-sided inverse.
Assumptions: a terminal `(-2,-1)` centre, zero or mutual-simple next edges,
arbitrary ambient rank, field and root-datum lattice, nonzero `v`, centre quantum
sum/difference and forward double-path cyclotomic factor. Reconstructed from the
presentation; no transformed-relation, inverse or faithful-action premise. -/
def terminalDoubleBraidEquiv : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  AlgEquiv.ofAlgHom (terminalDoubleBraid i j hij hterminal hpath h h' hq hs hn)
    (terminalDoubleBraidInv i j hij hterminal hpath h h' hq hs hn)
    (terminalDoubleBraid_comp_terminalDoubleBraidInv i j hij hterminal hpath h h' hq hs hn)
    (terminalDoubleBraidInv_comp_terminalDoubleBraid i j hij hterminal hpath h h' hq hs hn)

end QuantumGroup
