/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.PathSerre

/-!
# Quantum braid equivalences with orthogonal neighbours

## Main definitions

* `QuantumGroup.simplyLacedBraid`: the quotient lift at the chosen node.
* `QuantumGroup.simplyLacedBraidInv`: its explicit reversal-conjugate inverse.
* `QuantumGroup.simplyLacedBraidEquiv`: the resulting algebra automorphism.

## Scope and references

Reconstructed from the defining presentation and existing recovery identities.
Centre edges are zero or mutual simple edges, distinct neighbours are orthogonal,
and neighbour/non-neighbour edges are zero or mutual simple edges. Edges between two
non-neighbours are unrestricted.
This includes the classical finite-type simply-laced diagrams, but does not
cover triangles through the chosen node or establish braid-group relations.
Neither finite rank nor characteristic zero is assumed. Both parameter sum
and difference nonvanishing are explicit; their necessity is not asserted.
-/

open LieLean

noncomputable section
namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j l : I}

private theorem assembly_serre_one (q : k) {a b : QuantumGroup R v}
    (h : Commute a b) : qSerre q 1 a b = 0 := by
  simp [qSerre, Finset.sum_range_succ, h.eq]

/-- An untouched positive generator commutes with a disconnected braid image.
Direct finite-sum argument through `commute_serreAux`. -/
theorem braidEj_commute_braidEj_of_disconnected
    (hil : D.cartanMatrix i l = 0) (hjl : D.cartanMatrix j l = 0) :
    Commute (braidEj R v i j) (braidEj R v i l) := by
  rw [braidEj_eq_of_cartanMatrix_eq_zero hil]
  unfold braidEj
  apply Commute.smul_left
  exact (commute_serreAux (E_commute_E_of_cartanMatrix_eq_zero hil).symm
    (E_commute_E_of_cartanMatrix_eq_zero hjl).symm _ _ _).symm

/-- The negative disconnected relation follows directly from the Serre sum. -/
theorem braidFj_commute_braidFj_of_disconnected
    (hil : D.cartanMatrix i l = 0) (hjl : D.cartanMatrix j l = 0) :
    Commute (braidFj R v i j) (braidFj R v i l) := by
  rw [braidFj_eq_of_cartanMatrix_eq_zero hil]
  unfold braidFj
  apply Commute.smul_left
  exact (commute_serreAux (F_commute_F_of_cartanMatrix_eq_zero hil).symm
    (F_commute_F_of_cartanMatrix_eq_zero hjl).symm _ _ _).symm

private theorem assembly_braidEi_commute (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) : Commute (braidEi R i) (E R v j) := by
  have hK : Commute (K R v (ktilde R i)) (E R v j) := by
    change K R v (ktilde R i) * E R v j = E R v j * K R v (ktilde R i)
    simp [K_mul_E, root_ktilde, hij]
  exact ((show Commute (F R v i) (E R v j) from (E_mul_F_of_ne hj).symm).mul_left
    hK).neg_left

private theorem assembly_braidFi_commute (hj : j ≠ i)
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
    D.cartanMatrix j l = 0 ∨ (D.cartanMatrix j l = -1 ∧ D.cartanMatrix l j = -1))
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)

include hedge hleaf hpath hq hs in
/-- All defining relations for the actual braid images. The hypotheses constrain
Cartan entries, not a target relation package. Reconstructed case assembly. -/
theorem simplyLacedBraid_relations :
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
        exact assembly_serre_one _ (assembly_braidEi_commute hlm.symm h0)
      · simpa only [hlm.symm, ↓reduceIte] using
          qSerre_braidEi_braidEj_of_cartanMatrix_eq_neg_one (R := R) h1 hq
    · by_cases hm : m = i
      · subst m
        rcases hedge l hl with h0 | ⟨h1, h1'⟩
        · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i l).mp h0
          simp only [hl, ↓reduceIte, h0', sub_zero, Int.toNat_one,
            braidEj_eq_of_cartanMatrix_eq_zero h0]
          exact assembly_serre_one _ (assembly_braidEi_commute hl h0).symm
        · simpa only [hl, ↓reduceIte] using
            qSerre_braidEj_braidEi_of_simply_laced_edge (R := R) h1 h1' hq
      · simp only [hl, hm, ↓reduceIte]
        rcases hedge l hl with hl0 | ⟨hl1, hl1'⟩
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩
          · simpa only [braidEj_eq_of_cartanMatrix_eq_zero hl0,
              braidEj_eq_of_cartanMatrix_eq_zero hm0] using serre_E R v hlm
          · rcases hpath m l hm1 hl0 with h0 | ⟨_, h1⟩
            · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm m l).mp h0
              rw [h0']
              exact assembly_serre_one _
                (braidEj_commute_braidEj_of_disconnected hl0 h0).symm
            · exact qSerre_braidEj_braidEj_of_path_reverse hm1 h1 hl0
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩
          · rcases hpath l m hl1 hm0 with h0 | ⟨h1, _⟩
            · rw [h0]
              exact assembly_serre_one _ (braidEj_commute_braidEj_of_disconnected hm0 h0)
            · exact qSerre_braidEj_braidEj_of_path (NeZero.ne v) hl1 hl1' h1 hm0 hs
          · have h0 := hleaf l m hl1 hm1 hlm
            rw [h0]
            exact assembly_serre_one _
              (braidEj_commute_braidEj_of_orthogonal_neighbours
                (NeZero.ne v) hl1 hm1 hlm h0 hs)
  serre_F l m hlm := by
    by_cases hl : l = i
    · subst l
      rcases hedge m hlm.symm with h0 | ⟨h1, _⟩
      · simp only [hlm.symm, ↓reduceIte, h0, sub_zero, Int.toNat_one,
          braidFj_eq_of_cartanMatrix_eq_zero h0]
        exact assembly_serre_one _ (assembly_braidFi_commute hlm.symm h0)
      · simpa only [hlm.symm, ↓reduceIte] using
          qSerre_braidFi_braidFj_of_cartanMatrix_eq_neg_one (R := R) h1 hq
    · by_cases hm : m = i
      · subst m
        rcases hedge l hl with h0 | ⟨h1, h1'⟩
        · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i l).mp h0
          simp only [hl, ↓reduceIte, h0', sub_zero, Int.toNat_one,
            braidFj_eq_of_cartanMatrix_eq_zero h0]
          exact assembly_serre_one _ (assembly_braidFi_commute hl h0).symm
        · simpa only [hl, ↓reduceIte] using
            qSerre_braidFj_braidFi_of_simply_laced_edge (R := R) h1 h1' hq
      · simp only [hl, hm, ↓reduceIte]
        rcases hedge l hl with hl0 | ⟨hl1, hl1'⟩
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩
          · simpa only [braidFj_eq_of_cartanMatrix_eq_zero hl0,
              braidFj_eq_of_cartanMatrix_eq_zero hm0] using serre_F R v hlm
          · rcases hpath m l hm1 hl0 with h0 | ⟨_, h1⟩
            · have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm m l).mp h0
              rw [h0']
              exact assembly_serre_one _
                (braidFj_commute_braidFj_of_disconnected hl0 h0).symm
            · exact qSerre_braidFj_braidFj_of_path_reverse (NeZero.ne v) hm1 h1 hl0
        · rcases hedge m hm with hm0 | ⟨hm1, _⟩
          · rcases hpath l m hl1 hm0 with h0 | ⟨h1, _⟩
            · rw [h0]
              exact assembly_serre_one _ (braidFj_commute_braidFj_of_disconnected hm0 h0)
            · exact qSerre_braidFj_braidFj_of_path (NeZero.ne v) hl1 hl1' h1 hm0 hs
          · have h0 := hleaf l m hl1 hm1 hlm
            rw [h0]
            exact assembly_serre_one _
              (braidFj_commute_braidFj_of_orthogonal_neighbours
                (NeZero.ne v) hl1 hm1 hlm h0 hs)

/-- Genuine quotient braid homomorphism with pairwise orthogonal neighbours.
Reconstructed from all defining relations, not from an assumed faithful action. -/
def simplyLacedBraid : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  lift (simplyLacedBraid_relations i hedge hleaf hpath hq hs)

@[simp] theorem simplyLacedBraid_E (l : I) :
    simplyLacedBraid i hedge hleaf hpath hq hs (E R v l) =
      if l = i then braidEi R i else braidEj R v i l := lift_E _ l

@[simp] theorem simplyLacedBraid_F (l : I) :
    simplyLacedBraid i hedge hleaf hpath hq hs (F R v l) =
      if l = i then braidFi R i else braidFj R v i l := lift_F _ l

@[simp] theorem simplyLacedBraid_K (μ : Y) :
    simplyLacedBraid i hedge hleaf hpath hq hs (K R v μ) = K R v (reflY R i μ) := lift_K _ μ

/-- Explicit inverse candidate, using the independently proved product reversal. -/
def simplyLacedBraidInv : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  (AlgHom.opComm braidReversalOp).comp
    ((simplyLacedBraid i hedge hleaf hpath hq hs).op.comp braidReversalOp)

/-- The inverse candidate is reversal-conjugation on the actual quotient. -/
theorem simplyLacedBraidInv_apply (x : QuantumGroup R v) :
    simplyLacedBraidInv i hedge hleaf hpath hq hs x =
      braidReversal (simplyLacedBraid i hedge hleaf hpath hq hs (braidReversal x)) := rfl

@[simp] theorem simplyLacedBraidInv_Ei :
    simplyLacedBraidInv i hedge hleaf hpath hq hs (E R v i) = braidInvEi R i := by
  simp [simplyLacedBraidInv_apply, braidEi, braidInvEi, braidReversal_mul, Kt]

@[simp] theorem simplyLacedBraidInv_Fi :
    simplyLacedBraidInv i hedge hleaf hpath hq hs (F R v i) = braidInvFi R i := by
  simp [simplyLacedBraidInv_apply, braidFi, braidInvFi, braidReversal_mul, Kt]

@[simp] theorem simplyLacedBraidInv_Ej (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = -1) :
    simplyLacedBraidInv i hedge hleaf hpath hq hs (E R v j) =
      E R v j * E R v i - (v ^ D.d i)⁻¹ • (E R v i * E R v j) := by
  simp [simplyLacedBraidInv_apply, hj, braidEj_eq_of_cartanMatrix_eq_neg_one hij,
    braidReversal_mul]

@[simp] theorem simplyLacedBraidInv_Fj (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = -1) :
    simplyLacedBraidInv i hedge hleaf hpath hq hs (F R v j) =
      F R v i * F R v j - (v ^ D.d i) • (F R v j * F R v i) := by
  simp [simplyLacedBraidInv_apply, hj,
    braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hij, braidReversal_mul]

/-- The inverse fixes every positive generator orthogonal to the chosen node. -/
@[simp] theorem simplyLacedBraidInv_E_of_orthogonal (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) :
    simplyLacedBraidInv i hedge hleaf hpath hq hs (E R v j) = E R v j := by
  simp [simplyLacedBraidInv_apply, hj, braidEj_eq_of_cartanMatrix_eq_zero hij]

/-- The inverse fixes every negative generator orthogonal to the chosen node. -/
@[simp] theorem simplyLacedBraidInv_F_of_orthogonal (j : I) (hj : j ≠ i)
    (hij : D.cartanMatrix i j = 0) :
    simplyLacedBraidInv i hedge hleaf hpath hq hs (F R v j) = F R v j := by
  simp [simplyLacedBraidInv_apply, hj, braidFj_eq_of_cartanMatrix_eq_zero hij]

@[simp] theorem simplyLacedBraidInv_K (μ : Y) :
    simplyLacedBraidInv i hedge hleaf hpath hq hs (K R v μ) = K R v (reflY R i μ) := by
  simp [simplyLacedBraidInv_apply]

/-- The explicit candidate is a right inverse on every quotient generator.
Reconstructed using the rank-independent degree-one recovery identities. -/
theorem simplyLacedBraid_comp_simplyLacedBraidInv :
    (simplyLacedBraid (R := R) i hedge hleaf hpath hq hs).comp
      (simplyLacedBraidInv i hedge hleaf hpath hq hs) = AlgHom.id k (QuantumGroup R v) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · by_cases hl : l = i
    · subst l
      simp only [AlgHom.comp_apply, simplyLacedBraidInv_Ei, braidInvEi, map_neg, map_mul,
        simplyLacedBraid_F, ↓reduceIte, braidFi, simplyLacedBraid_K, reflY_ktilde,
        mul_neg, neg_neg, AlgHom.id_apply, ← mul_assoc, K_mul_K_neg, one_mul]
    · rcases hedge l hl with h0 | ⟨h1, _⟩
      · simp [simplyLacedBraidInv_apply, hl,
          braidEj_eq_of_cartanMatrix_eq_zero h0]
      · simpa only [AlgHom.comp_apply,
          simplyLacedBraidInv_Ej i hedge hleaf hpath hq hs l hl h1,
          map_sub, map_mul, map_smul, simplyLacedBraid_E, hl, ↓reduceIte,
          AlgHom.id_apply] using a2Braid_recover_Ej (R := R) i l h1 hq
  · by_cases hl : l = i
    · subst l
      simp only [AlgHom.comp_apply, simplyLacedBraidInv_Fi, braidInvFi, map_neg, map_mul,
        simplyLacedBraid_E, ↓reduceIte, braidEi, Kt, simplyLacedBraid_K, reflY_ktilde,
        neg_mul, neg_neg, AlgHom.id_apply, mul_assoc, K_mul_K_neg, mul_one]
    · rcases hedge l hl with h0 | ⟨h1, _⟩
      · simp [simplyLacedBraidInv_apply, hl,
          braidFj_eq_of_cartanMatrix_eq_zero h0]
      · simpa only [AlgHom.comp_apply,
          simplyLacedBraidInv_Fj i hedge hleaf hpath hq hs l hl h1,
          map_sub, map_mul, map_smul, simplyLacedBraid_F, hl, ↓reduceIte,
          AlgHom.id_apply] using a2Braid_recover_Fj (R := R) i l h1 hq
  · simp

/-- The left-inverse identity follows by conjugating the proved right inverse
by the actual involutive product reversal, without finite-dimensionality. -/
theorem simplyLacedBraidInv_comp_simplyLacedBraid :
    (simplyLacedBraidInv (R := R) i hedge hleaf hpath hq hs).comp
      (simplyLacedBraid i hedge hleaf hpath hq hs) = AlgHom.id k (QuantumGroup R v) := by
  apply DFunLike.ext
  intro x
  have hc := congrArg braidReversal
    (DFunLike.congr_fun
      (simplyLacedBraid_comp_simplyLacedBraidInv (R := R) i hedge hleaf hpath hq hs)
      (braidReversal x))
  simpa only [AlgHom.comp_apply, simplyLacedBraidInv_apply, braidReversal_involutive x,
    AlgHom.id_apply] using hc

/-- Genuine braid algebra equivalence with pairwise orthogonal neighbours.
The field and root-datum lattice are arbitrary;
`v`, `q - q⁻¹`, and `q + q⁻¹` are explicitly nonzero, where `q = v ^ D.d i`.
Reconstructed from all presentation relations and explicit two-sided recovery. -/
def simplyLacedBraidEquiv : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  AlgEquiv.ofAlgHom (simplyLacedBraid i hedge hleaf hpath hq hs)
    (simplyLacedBraidInv i hedge hleaf hpath hq hs)
    (simplyLacedBraid_comp_simplyLacedBraidInv i hedge hleaf hpath hq hs)
    (simplyLacedBraidInv_comp_simplyLacedBraid i hedge hleaf hpath hq hs)

end LieLean.QuantumGroup
