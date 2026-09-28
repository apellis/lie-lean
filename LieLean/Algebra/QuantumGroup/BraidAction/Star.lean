/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.A2Relation
import LieLean.Algebra.QuantumGroup.BraidAction.CoupledMixed

/-!
# Quantum braid equivalences at simply-laced star centres

## Main definitions

* `QuantumGroup.starBraid`: actual quotient homomorphism at a simply-laced star centre.
* `QuantumGroup.starBraidInv`: explicit inverse by product-reversal conjugation.
* `QuantumGroup.starBraidEquiv`: the resulting two-sided algebra equivalence.
* `QuantumGroup.a3MiddleBraidEquiv`: the explicit three-node A3 specialization.

## Main results

The positive and negative braid images of two orthogonal neighbours commute, in
arbitrary ambient rank and over an arbitrary field with the stated nonvanishing.
This completes all relations at the centre of a simply-laced star and proves an
actual automorphism. The star restriction is explicit: every other node is a
mutual `-1` neighbour, and distinct neighbours are orthogonal. This is not a theorem
for every simply-laced graph. No finiteness or characteristic restriction is used.

## References

Reconstructed directly from the defining quantum Serre relations; no external
source was consulted. No rank restriction or assumed braid automorphism is used.
-/

noncomputable section
namespace QuantumGroup

variable {k : Type*} [Field k]

private lemma neighbours_qSerre_two {B : Type*} [Ring B] [Algebra k B]
    (q : k) (a b : B) :
    qSerre q 2 a b = a * (a * b) - (q + q⁻¹) • (a * (b * a)) + b * (a * a) := by
  simp [qSerre, Finset.sum_range_succ, qBinomial, pow_two, mul_assoc]
  module

/-- Two quantum commutators commute when their common left entry satisfies the
quadratic Serre relations and the right entries commute. Reconstructed polynomial
identity, with division only by `q + q⁻¹`. -/
theorem commute_quantumCommutators_of_serre_two
    {B : Type*} [Ring B] [Algebra k B] {q : k} {a b c : B}
    (hq : q ≠ 0) (hs : q + q⁻¹ ≠ 0)
    (hab : qSerre q 2 a b = 0) (hac : qSerre q 2 a c = 0)
    (hbc : Commute b c) :
    Commute (a * b - q⁻¹ • (b * a)) (a * c - q⁻¹ • (c * a)) := by
  have hb := congrArg (fun x : B ↦ x * c) hab
  have hc := congrArg (fun x : B ↦ x * b) hac
  have hb' := congrArg (fun x : B ↦ c * x) hab
  have hc' := congrArg (fun x : B ↦ b * x) hac
  simp only [neighbours_qSerre_two, mul_add, add_mul, mul_sub, sub_mul,
    mul_smul_comm, smul_mul_assoc, mul_zero, zero_mul, mul_assoc] at hb hc hb' hc'
  have hmid : a * (b * (c * a)) = a * (c * (b * a)) := by
    rw [← mul_assoc b c a, hbc.eq, mul_assoc]
  have hlast : b * (c * (a * a)) = c * (b * (a * a)) := by
    rw [← mul_assoc b c (a * a), hbc.eq, mul_assoc]
  have hfirst : a * (a * (b * c)) = a * (a * (c * b)) := by rw [hbc.eq]
  apply sub_eq_zero.mp
  apply (smul_eq_zero.mp (show (q + q⁻¹) •
    ((a * b - q⁻¹ • (b * a)) * (a * c - q⁻¹ • (c * a)) -
      (a * c - q⁻¹ • (c * a)) * (a * b - q⁻¹ • (b * a))) = 0 from ?_)).resolve_left hs
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub,
    smul_smul, mul_assoc]
  rw [hmid]
  rw [hfirst] at hb
  rw [hlast] at hc'
  linear_combination (norm := (match_scalars <;> field_simp <;> ring))
    -hb + hc + q⁻¹ ^ 2 • hb' - q⁻¹ ^ 2 • hc'

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j l : I}

/-- Actual positive braid images of two orthogonal neighbours commute in the
quantum-group quotient. The ambient rank and reverse Cartan entries are unrestricted.
Reconstructed from the two quadratic and one linear defining Serre relations. -/
theorem braidEj_commute_braidEj_of_orthogonal_neighbours
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -1)
    (hil : D.cartanMatrix i l = -1) (hjl : j ≠ l)
    (hzero : D.cartanMatrix j l = 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0) :
    Commute (braidEj R v i j) (braidEj R v i l) := by
  have hij' : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at hij
    norm_num at hij
  have hil' : i ≠ l := by
    rintro rfl
    rw [D.cartanMatrix_self] at hil
    norm_num at hil
  have hab : qSerre (v ^ D.d i) 2 (E R v i) (E R v j) = 0 := by
    simpa [hij] using serre_E R v hij'
  have hac : qSerre (v ^ D.d i) 2 (E R v i) (E R v l) = 0 := by
    simpa [hil] using serre_E R v hil'
  have hbc : Commute (E R v j) (E R v l) := by
    apply sub_eq_zero.mp
    simpa [hzero, qSerre, Finset.sum_range_succ, sub_eq_add_neg] using serre_E R v hjl
  rw [braidEj_eq_of_cartanMatrix_eq_neg_one hij,
    braidEj_eq_of_cartanMatrix_eq_neg_one hil]
  exact commute_quantumCommutators_of_serre_two (pow_ne_zero _ hv) hs hab hac hbc

/-- Actual negative braid images of two orthogonal neighbours commute, by applying
Chevalley to the proved positive relation and cancelling its nonzero scalar.
Reconstructed proof; no rank or characteristic restriction. -/
theorem braidFj_commute_braidFj_of_orthogonal_neighbours
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -1)
    (hil : D.cartanMatrix i l = -1) (hjl : j ≠ l)
    (hzero : D.cartanMatrix j l = 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0) :
    Commute (braidFj R v i j) (braidFj R v i l) := by
  have hp := braidEj_commute_braidEj_of_orthogonal_neighbours
    (R := R) hv hij hil hjl hzero hs
  have hc := congrArg (chevalley R v) hp.eq
  rw [map_mul, map_mul,
    chevalley_braidEj_of_cartanMatrix_eq_neg_one hv hij,
    chevalley_braidEj_of_cartanMatrix_eq_neg_one hv hil] at hc
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul] at hc
  have hq : -(v ^ D.d i)⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hv))
  apply sub_eq_zero.mp
  apply (smul_eq_zero.mp (show (-(v ^ D.d i)⁻¹ * -(v ^ D.d i)⁻¹) •
    (braidFj R v i j * braidFj R v i l - braidFj R v i l * braidFj R v i j) = 0
    from ?_)).resolve_left (mul_ne_zero hq hq)
  simpa only [smul_sub] using sub_eq_zero.mpr hc

end QuantumGroup


namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  (i : I)
  (hedge : ∀ j, j ≠ i → D.cartanMatrix i j = -1 ∧ D.cartanMatrix j i = -1)
  (hleaf : ∀ j l, j ≠ i → l ≠ i → j ≠ l → D.cartanMatrix j l = 0)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)

include hedge hleaf hq hs in
/-- All defining relations at the centre of a simply-laced star, reconstructed
from the presentation. All nodes other than `i` are mutually orthogonal neighbours;
there is no bound on their number and no assumed relation package. -/
theorem starBraid_relations :
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
          simpa only [hl, ↓reduceIte] using
            braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_one
              (R := R) (NeZero.ne v) (hedge l hl).1 hq
        · simpa only [hl, hm, hlm, ↓reduceIte] using
            braidEj_mul_braidFj_sub_of_two_cartanMatrix_eq_neg_one
              (R := R) (NeZero.ne v) (hedge l hl).1 (hedge m hm).1 hlm hq
  serre_E l m hlm := by
    by_cases hl : l = i
    · subst l
      simpa only [hlm.symm, ↓reduceIte] using
        qSerre_braidEi_braidEj_of_cartanMatrix_eq_neg_one
          (R := R) (hedge m hlm.symm).1 hq
    · by_cases hm : m = i
      · subst m
        simpa only [hl, ↓reduceIte] using
          qSerre_braidEj_braidEi_of_simply_laced_edge
            (R := R) (hedge l hl).1 (hedge l hl).2 hq
      · have hc := braidEj_commute_braidEj_of_orthogonal_neighbours
          (R := R) (NeZero.ne v) (hedge l hl).1 (hedge m hm).1
          hlm (hleaf l m hl hm hlm) hs
        simp [hl, hm, hleaf l m hl hm hlm, qSerre, Finset.sum_range_succ, hc.eq]
  serre_F l m hlm := by
    by_cases hl : l = i
    · subst l
      simpa only [hlm.symm, ↓reduceIte] using
        qSerre_braidFi_braidFj_of_cartanMatrix_eq_neg_one
          (R := R) (hedge m hlm.symm).1 hq
    · by_cases hm : m = i
      · subst m
        simpa only [hl, ↓reduceIte] using
          qSerre_braidFj_braidFi_of_simply_laced_edge
            (R := R) (hedge l hl).1 (hedge l hl).2 hq
      · have hc := braidFj_commute_braidFj_of_orthogonal_neighbours
          (R := R) (NeZero.ne v) (hedge l hl).1 (hedge m hm).1
          hlm (hleaf l m hl hm hlm) hs
        simp [hl, hm, hleaf l m hl hm hlm, qSerre, Finset.sum_range_succ, hc.eq]

/-- Genuine quotient braid homomorphism at the centre of a simply-laced star.
Reconstructed from all defining relations, not from an assumed faithful action. -/
def starBraid : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  lift (starBraid_relations i hedge hleaf hq hs)

@[simp] theorem starBraid_E (l : I) :
    starBraid i hedge hleaf hq hs (E R v l) =
      if l = i then braidEi R i else braidEj R v i l := lift_E _ l

@[simp] theorem starBraid_F (l : I) :
    starBraid i hedge hleaf hq hs (F R v l) =
      if l = i then braidFi R i else braidFj R v i l := lift_F _ l

@[simp] theorem starBraid_K (μ : Y) :
    starBraid i hedge hleaf hq hs (K R v μ) = K R v (reflY R i μ) := lift_K _ μ

/-- Explicit inverse candidate, using the independently proved product reversal. -/
def starBraidInv : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  (AlgHom.opComm braidReversalOp).comp
    ((starBraid i hedge hleaf hq hs).op.comp braidReversalOp)

/-- The inverse candidate is reversal-conjugation on the actual quotient. -/
theorem starBraidInv_apply (x : QuantumGroup R v) :
    starBraidInv i hedge hleaf hq hs x =
      braidReversal (starBraid i hedge hleaf hq hs (braidReversal x)) := rfl

@[simp] theorem starBraidInv_Ei :
    starBraidInv i hedge hleaf hq hs (E R v i) = braidInvEi R i := by
  simp [starBraidInv_apply, braidEi, braidInvEi, braidReversal_mul, Kt]

@[simp] theorem starBraidInv_Fi :
    starBraidInv i hedge hleaf hq hs (F R v i) = braidInvFi R i := by
  simp [starBraidInv_apply, braidFi, braidInvFi, braidReversal_mul, Kt]

@[simp] theorem starBraidInv_Ej (j : I) (hj : j ≠ i) :
    starBraidInv i hedge hleaf hq hs (E R v j) =
      E R v j * E R v i - (v ^ D.d i)⁻¹ • (E R v i * E R v j) := by
  simp [starBraidInv_apply, hj, braidEj_eq_of_cartanMatrix_eq_neg_one (hedge j hj).1,
    braidReversal_mul]

@[simp] theorem starBraidInv_Fj (j : I) (hj : j ≠ i) :
    starBraidInv i hedge hleaf hq hs (F R v j) =
      F R v i * F R v j - (v ^ D.d i) • (F R v j * F R v i) := by
  simp [starBraidInv_apply, hj,
    braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) (hedge j hj).1, braidReversal_mul]

@[simp] theorem starBraidInv_K (μ : Y) :
    starBraidInv i hedge hleaf hq hs (K R v μ) = K R v (reflY R i μ) := by
  simp [starBraidInv_apply]

/-- The explicit candidate is a right inverse on every quotient generator.
Reconstructed using the rank-independent degree-one recovery identities. -/
theorem starBraid_comp_starBraidInv :
    (starBraid (R := R) i hedge hleaf hq hs).comp
      (starBraidInv i hedge hleaf hq hs) = AlgHom.id k (QuantumGroup R v) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · by_cases hl : l = i
    · subst l
      simp only [AlgHom.comp_apply, starBraidInv_Ei, braidInvEi, map_neg, map_mul,
        starBraid_F, ↓reduceIte, braidFi, starBraid_K, reflY_ktilde,
        mul_neg, neg_neg, AlgHom.id_apply, ← mul_assoc, K_mul_K_neg, one_mul]
    · simpa only [AlgHom.comp_apply, starBraidInv_Ej i hedge hleaf hq hs l hl,
        map_sub, map_mul, map_smul, starBraid_E, hl, ↓reduceIte, AlgHom.id_apply] using
        a2Braid_recover_Ej (R := R) i l (hedge l hl).1 hq
  · by_cases hl : l = i
    · subst l
      simp only [AlgHom.comp_apply, starBraidInv_Fi, braidInvFi, map_neg, map_mul,
        starBraid_E, ↓reduceIte, braidEi, Kt, starBraid_K, reflY_ktilde,
        neg_mul, neg_neg, AlgHom.id_apply, mul_assoc, K_mul_K_neg, mul_one]
    · simpa only [AlgHom.comp_apply, starBraidInv_Fj i hedge hleaf hq hs l hl,
        map_sub, map_mul, map_smul, starBraid_F, hl, ↓reduceIte, AlgHom.id_apply] using
        a2Braid_recover_Fj (R := R) i l (hedge l hl).1 hq
  · simp

/-- The left-inverse identity follows by conjugating the proved right inverse
by the actual involutive product reversal, without finite-dimensionality. -/
theorem starBraidInv_comp_starBraid :
    (starBraidInv (R := R) i hedge hleaf hq hs).comp
      (starBraid i hedge hleaf hq hs) = AlgHom.id k (QuantumGroup R v) := by
  apply DFunLike.ext
  intro x
  have hc := congrArg braidReversal
    (DFunLike.congr_fun (starBraid_comp_starBraidInv (R := R) i hedge hleaf hq hs)
      (braidReversal x))
  simpa only [AlgHom.comp_apply, starBraidInv_apply, braidReversal_involutive x,
    AlgHom.id_apply] using hc

/-- Genuine braid algebra equivalence at the centre of a simply-laced star,
including the middle node of A3. The field and root-datum lattice are arbitrary;
`v`, `q - q⁻¹`, and `q + q⁻¹` are explicitly nonzero, where `q = v ^ D.d i`.
Reconstructed from all presentation relations and explicit two-sided recovery. -/
def starBraidEquiv : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  AlgEquiv.ofAlgHom (starBraid i hedge hleaf hq hs) (starBraidInv i hedge hleaf hq hs)
    (starBraid_comp_starBraidInv i hedge hleaf hq hs)
    (starBraidInv_comp_starBraid i hedge hleaf hq hs)

omit hedge hleaf in
/-- The middle-node braid equivalence for exactly three distinct nodes `i,j,l`,
with mutual simple edges `i-j`, `i-l` and orthogonal endpoints `j,l`.
The reverse zero entry is derived from the Cartan axiom. Reconstructed specialization;
no relation package, faithful action or restriction of the toral lattice is assumed. -/
def a3MiddleBraidEquiv (j l : I)
    (hall : ∀ m, m = i ∨ m = j ∨ m = l)
    (hij' : D.cartanMatrix i j = -1) (hji : D.cartanMatrix j i = -1)
    (hil' : D.cartanMatrix i l = -1) (hli : D.cartanMatrix l i = -1)
    (hjl' : D.cartanMatrix j l = 0) : QuantumGroup R v ≃ₐ[k] QuantumGroup R v := by
  clear hedge hleaf
  have he : ∀ m, m ≠ i → D.cartanMatrix i m = -1 ∧ D.cartanMatrix m i = -1 := by
    intro m hm
    rcases hall m with rfl | rfl | rfl
    · exact (hm rfl).elim
    · exact ⟨hij', hji⟩
    · exact ⟨hil', hli⟩
  have hl : ∀ m n, m ≠ i → n ≠ i → m ≠ n → D.cartanMatrix m n = 0 := by
    intro m n hm hn hmn
    rcases hall m with rfl | rfl | rfl <;> rcases hall n with rfl | rfl | rfl
    all_goals try first | exact (hm rfl).elim | exact (hn rfl).elim | exact (hmn rfl).elim
    · exact hjl'
    · exact (D.isGeneralizedCartan_cartanMatrix.zero_comm _ _).mp hjl'
  exact starBraidEquiv i he hl hq hs

end QuantumGroup
