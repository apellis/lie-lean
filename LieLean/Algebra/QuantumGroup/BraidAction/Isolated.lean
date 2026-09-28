/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.Mixed

/-!
# Orthogonal quantum braid relations and isolated-node automorphisms

## Main results

* `braidEj_eq_of_cartanMatrix_eq_zero`, `braidFj_eq_of_cartanMatrix_eq_zero`:
  a braid generator fixes generators at an orthogonal node.
* `braidEj_commute_braidFj_of_right_orthogonal`: the off-diagonal mixed relation when
  the right node is orthogonal to the braid index.
* `isolatedBraidEquiv`: the braid automorphism at an isolated Dynkin node, with an explicit
  two-sided inverse, in arbitrary ambient rank.
* `isolatedBraid_comp_comm`: the braid relation for isolated nodes.

## References

The arguments are reconstructed directly from the candidate images and the defining relations.
An isolated node has zero Cartan entries with every other node. The automorphism only assumes
that the parameter is nonzero; no genericity hypothesis is needed. This file does not construct
the automorphisms at coupled nodes or prove their braid relations.
-/

noncomputable section

namespace QuantumGroup

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- Anything commuting with both inputs commutes with their rescaled Serre element.
Direct finite-sum argument, reconstructed here. -/
theorem commute_serreAux {a b c : B} (ha : Commute c a) (hb : Commute c b)
    (q t : k) (r : ℕ) : Commute c (serreAux q t r a b) := by
  unfold serreAux
  apply Commute.sum_right
  intro j _
  exact (((ha.pow_right (r - j)).mul_right hb).mul_right (ha.pow_right j)).smul_right _

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} {i j l : I}

/-- A zero Cartan entry makes the proposed positive braid image the original generator.
Direct simplification of the degree-zero Serre sum. -/
theorem braidEj_eq_of_cartanMatrix_eq_zero (h : D.cartanMatrix i j = 0) :
    braidEj R v i j = E R v j := by
  simp [braidEj, negA, h, serreAux]

/-- A zero Cartan entry makes the proposed negative braid image the original generator.
Direct simplification of the degree-zero Serre sum. -/
theorem braidFj_eq_of_cartanMatrix_eq_zero (h : D.cartanMatrix i j = 0) :
    braidFj R v i j = F R v j := by
  simp [braidFj, negA, h, serreAux]

/-- The positive braid image commutes with any negative generator of a distinct color
from both its inputs. This uses only the off-diagonal `E,F` commutators. -/
theorem braidEj_commute_F (hil : i ≠ l) (hjl : j ≠ l) :
    Commute (braidEj R v i j) (F R v l) := by
  unfold braidEj
  apply Commute.smul_left
  exact (commute_serreAux (E_mul_F_of_ne hil).symm (E_mul_F_of_ne hjl).symm _ _ _).symm

/-- The negative braid image commutes with any positive generator of a distinct color
from both its inputs. This uses only the off-diagonal `E,F` commutators. -/
theorem E_commute_braidFj (hli : l ≠ i) (hlj : l ≠ j) :
    Commute (E R v l) (braidFj R v i j) := by
  unfold braidFj
  apply Commute.smul_right
  exact commute_serreAux (E_mul_F_of_ne hli) (E_mul_F_of_ne hlj) _ _ _

/-- The off-diagonal mixed braid relation when the negative node is orthogonal to the
braid index. Reconstructed from the two input commutators and the degree-zero image. -/
theorem braidEj_commute_braidFj_of_right_orthogonal
    (hil : i ≠ l) (hjl : j ≠ l) (hil0 : D.cartanMatrix i l = 0) :
    Commute (braidEj R v i j) (braidFj R v i l) := by
  rw [braidFj_eq_of_cartanMatrix_eq_zero hil0]
  exact braidEj_commute_F hil hjl

/-- The off-diagonal mixed braid relation when the positive node is orthogonal to the
braid index. Reconstructed from the two input commutators and the degree-zero image. -/
theorem braidEj_commute_braidFj_of_left_orthogonal
    (hji : j ≠ i) (hjl : j ≠ l) (hij0 : D.cartanMatrix i j = 0) :
    Commute (braidEj R v i j) (braidFj R v i l) := by
  rw [braidEj_eq_of_cartanMatrix_eq_zero hij0]
  exact E_commute_braidFj hji hjl

/-- Orthogonal positive generators commute, by their degree-one Serre relation. -/
theorem E_commute_E_of_cartanMatrix_eq_zero (h : D.cartanMatrix i j = 0) :
    Commute (E R v i) (E R v j) := by
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have hserre := serre_E R v hij
  exact sub_eq_zero.mp (by simpa [h, qSerre, Finset.sum_range_succ, sub_eq_add_neg] using hserre)

/-- Orthogonal negative generators commute, by their degree-one Serre relation. -/
theorem F_commute_F_of_cartanMatrix_eq_zero (h : D.cartanMatrix i j = 0) :
    Commute (F R v i) (F R v j) := by
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have hserre := serre_F R v hij
  exact sub_eq_zero.mp (by simpa [h, qSerre, Finset.sum_range_succ, sub_eq_add_neg] using hserre)

omit [DecidableEq I] in
/-- A reflection fixes the toral element of an orthogonal node. -/
theorem reflY_ktilde_of_cartanMatrix_eq_zero (h : D.cartanMatrix i j = 0) :
    reflY R i (ktilde R j) = ktilde R j := by
  have hji := (D.isGeneralizedCartan_cartanMatrix.zero_comm i j).mp h
  simp [reflY_apply, root_ktilde, hji]

/-- The diagonal mixed relation at a node orthogonal to the braid index, with the reflected
Cartan term required by the presentation. This is a direct specialization, not an assumption. -/
theorem braidEj_mul_braidFj_sub_of_cartanMatrix_eq_zero
    (h : D.cartanMatrix i j = 0) :
    braidEj R v i j * braidFj R v i j - braidFj R v i j * braidEj R v i j =
      (v ^ D.d j - (v ^ D.d j)⁻¹)⁻¹ •
        (braidK R v i (.ofAdd (ktilde R j)) - braidK R v i (.ofAdd (-ktilde R j))) := by
  rw [braidEj_eq_of_cartanMatrix_eq_zero h, braidFj_eq_of_cartanMatrix_eq_zero h,
    braidK_apply, braidK_apply, map_neg, reflY_ktilde_of_cartanMatrix_eq_zero h]
  simpa only [↓reduceIte] using E_mul_F_sub R v j j

private theorem qSerre_one_eq_zero_of_commute (q : k) {a b : B} (h : Commute a b) :
    qSerre q 1 a b = 0 := by
  simp [qSerre, Finset.sum_range_succ, h.eq]

private theorem isolated_relations (i : I)
    (hi : ∀ j, j ≠ i → D.cartanMatrix i j = 0)
    (e f : QuantumGroup R v)
    (hE : ∀ μ, braidK R v i (.ofAdd μ) * e = v ^ R.root i μ • (e * braidK R v i (.ofAdd μ)))
    (hF : ∀ μ, braidK R v i (.ofAdd μ) * f = v ^ (-R.root i μ) • (f * braidK R v i (.ofAdd μ)))
    (hEF : e * f - f * e = (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ •
      (braidK R v i (.ofAdd (ktilde R i)) - braidK R v i (.ofAdd (-ktilde R i))))
    (heE : ∀ j, j ≠ i → Commute e (E R v j))
    (heF : ∀ j, j ≠ i → Commute e (F R v j))
    (hfE : ∀ j, j ≠ i → Commute f (E R v j))
    (hfF : ∀ j, j ≠ i → Commute f (F R v j)) :
    Relations R v (fun j ↦ if j = i then e else E R v j)
      (fun j ↦ if j = i then f else F R v j) (braidK R v i) where
  K_mul_E μ j := by
    by_cases hj : j = i
    · subst j; simpa only [↓reduceIte] using hE μ
    · simp only [hj, ↓reduceIte, braidK_apply, K_mul_E, root_reflY, hi j hj,
        mul_zero, sub_zero]
  K_mul_F μ j := by
    by_cases hj : j = i
    · subst j; simpa only [↓reduceIte] using hF μ
    · simp only [hj, ↓reduceIte, braidK_apply, K_mul_F, root_reflY, hi j hj,
        mul_zero, sub_zero]
  E_mul_F j l := by
    by_cases hj : j = i
    · subst j
      by_cases hl : l = i
      · subst l; simpa only [↓reduceIte] using hEF
      · simp only [hl, Ne.symm hl, ↓reduceIte]
        exact sub_eq_zero.mpr (heF l hl).eq
    · by_cases hl : l = i
      · subst l
        simp only [hj, ↓reduceIte]
        exact sub_eq_zero.mpr (hfE j hj).symm.eq
      · simp only [hj, hl, ↓reduceIte, braidK_apply, map_neg,
          reflY_ktilde_of_cartanMatrix_eq_zero (hi j hj)]
        exact E_mul_F_sub R v j l
  serre_E j l hjl := by
    by_cases hj : j = i
    · subst j
      have hl := Ne.symm hjl
      simp only [hl, ↓reduceIte, hi l hl, sub_zero, Int.toNat_one]
      exact qSerre_one_eq_zero_of_commute _ (heE l hl)
    · by_cases hl : l = i
      · subst l
        have hji := (D.isGeneralizedCartan_cartanMatrix.zero_comm i j).mp (hi j hj)
        simp only [hj, ↓reduceIte, hji, sub_zero, Int.toNat_one]
        exact qSerre_one_eq_zero_of_commute _ (heE j hj).symm
      · simpa only [hj, hl, ↓reduceIte] using serre_E R v hjl
  serre_F j l hjl := by
    by_cases hj : j = i
    · subst j
      have hl := Ne.symm hjl
      simp only [hl, ↓reduceIte, hi l hl, sub_zero, Int.toNat_one]
      exact qSerre_one_eq_zero_of_commute _ (hfF l hl)
    · by_cases hl : l = i
      · subst l
        have hji := (D.isGeneralizedCartan_cartanMatrix.zero_comm i j).mp (hi j hj)
        simp only [hj, ↓reduceIte, hji, sub_zero, Int.toNat_one]
        exact qSerre_one_eq_zero_of_commute _ (hfF j hj).symm
      · simpa only [hj, hl, ↓reduceIte] using serre_F R v hjl

private theorem K_commute_E_of_root_eq_zero (μ : Y) (j : I) (h : R.root j μ = 0) :
    Commute (K R v μ) (E R v j) := by
  change K R v μ * E R v j = E R v j * K R v μ
  simp [K_mul_E, h]

private theorem K_commute_F_of_root_eq_zero (μ : Y) (j : I) (h : R.root j μ = 0) :
    Commute (K R v μ) (F R v j) := by
  change K R v μ * F R v j = F R v j * K R v μ
  simp [K_mul_F, h]

variable [NeZero v]

/-- The braid formulas at an isolated Dynkin node satisfy all defining relations.
Every other generator is fixed; the ambient rank need not be one. -/
theorem isolatedBraid_relations (i : I) (hi : ∀ j, j ≠ i → D.cartanMatrix i j = 0) :
    Relations R v (fun j ↦ if j = i then braidEi R i else E R v j)
      (fun j ↦ if j = i then braidFi R i else F R v j) (braidK R v i) := by
  refine isolated_relations i hi _ _ (braidK_mul_braidEi i) (braidK_mul_braidFi i)
    (braidEi_mul_braidFi_sub i) ?_ ?_ ?_ ?_
  · intro j hj
    exact ((show Commute (F R v i) (E R v j) from (E_mul_F_of_ne hj).symm).mul_left
      (K_commute_E_of_root_eq_zero _ j (by simp [root_ktilde, hi j hj]))).neg_left
  · intro j hj
    exact ((F_commute_F_of_cartanMatrix_eq_zero (hi j hj)).mul_left
      (K_commute_F_of_root_eq_zero _ j (by simp [root_ktilde, hi j hj]))).neg_left
  · intro j hj
    exact ((K_commute_E_of_root_eq_zero _ j (by simp [map_neg, root_ktilde, hi j hj])).mul_left
      (E_commute_E_of_cartanMatrix_eq_zero (hi j hj))).neg_left
  · intro j hj
    exact ((K_commute_F_of_root_eq_zero _ j (by simp [map_neg, root_ktilde, hi j hj])).mul_left
      (E_mul_F_of_ne (Ne.symm hj))).neg_left

/-- The inverse braid formulas at an isolated Dynkin node satisfy all defining relations. -/
theorem isolatedBraidInv_relations (i : I) (hi : ∀ j, j ≠ i → D.cartanMatrix i j = 0) :
    Relations R v (fun j ↦ if j = i then braidInvEi R i else E R v j)
      (fun j ↦ if j = i then braidInvFi R i else F R v j) (braidK R v i) := by
  refine isolated_relations i hi _ _ (braidK_mul_braidInvEi i) (braidK_mul_braidInvFi i)
    (braidInvEi_mul_braidInvFi_sub i) ?_ ?_ ?_ ?_
  · intro j hj
    exact ((K_commute_E_of_root_eq_zero _ j (by simp [map_neg, root_ktilde, hi j hj])).mul_left
      (E_mul_F_of_ne hj).symm).neg_left
  · intro j hj
    exact ((K_commute_F_of_root_eq_zero _ j (by simp [map_neg, root_ktilde, hi j hj])).mul_left
      (F_commute_F_of_cartanMatrix_eq_zero (hi j hj))).neg_left
  · intro j hj
    exact ((E_commute_E_of_cartanMatrix_eq_zero (hi j hj)).mul_left
      (K_commute_E_of_root_eq_zero _ j (by simp [root_ktilde, hi j hj]))).neg_left
  · intro j hj
    exact ((show Commute (E R v i) (F R v j) from E_mul_F_of_ne (Ne.symm hj)).mul_left
      (K_commute_F_of_root_eq_zero _ j (by simp [root_ktilde, hi j hj]))).neg_left

variable (i : I) (hi : ∀ j, j ≠ i → D.cartanMatrix i j = 0)

/-- Lusztig's braid map at an isolated node, fixing every other Chevalley generator. -/
def isolatedBraid : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  lift (isolatedBraid_relations i hi)

/-- The explicit inverse candidate at an isolated node. -/
def isolatedBraidInv : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  lift (isolatedBraidInv_relations i hi)

@[simp] theorem isolatedBraid_E (j : I) :
    isolatedBraid i hi (E R v j) = if j = i then braidEi R i else E R v j := lift_E _ j

@[simp] theorem isolatedBraid_F (j : I) :
    isolatedBraid i hi (F R v j) = if j = i then braidFi R i else F R v j := lift_F _ j

@[simp] theorem isolatedBraid_K (μ : Y) :
    isolatedBraid i hi (K R v μ) = K R v (reflY R i μ) := lift_K _ μ

@[simp] theorem isolatedBraidInv_E (j : I) :
    isolatedBraidInv i hi (E R v j) = if j = i then braidInvEi R i else E R v j := lift_E _ j

@[simp] theorem isolatedBraidInv_F (j : I) :
    isolatedBraidInv i hi (F R v j) = if j = i then braidInvFi R i else F R v j := lift_F _ j

@[simp] theorem isolatedBraidInv_K (μ : Y) :
    isolatedBraidInv i hi (K R v μ) = K R v (reflY R i μ) := lift_K _ μ

/-- The inverse candidate is a left inverse on every generator, hence on the algebra. -/
theorem isolatedBraidInv_comp_isolatedBraid :
    (isolatedBraidInv (R := R) i hi).comp (isolatedBraid i hi) =
      AlgHom.id k (QuantumGroup R v) := by
  refine hom_ext (fun j ↦ ?_) (fun j ↦ ?_) (fun μ ↦ ?_)
  · by_cases hj : j = i
    · subst j
      simp only [AlgHom.comp_apply, isolatedBraid_E, ↓reduceIte, braidEi, map_neg, map_mul,
        isolatedBraidInv_F, braidInvFi, Kt, isolatedBraidInv_K, reflY_ktilde, neg_mul,
        neg_neg, AlgHom.id_apply, mul_assoc, K_mul_K_neg, mul_one]
    · simp [hj]
  · by_cases hj : j = i
    · subst j
      simp only [AlgHom.comp_apply, isolatedBraid_F, ↓reduceIte, braidFi, map_neg, map_mul,
        isolatedBraidInv_E, braidInvEi, isolatedBraidInv_K, reflY_ktilde, mul_neg,
        neg_neg, AlgHom.id_apply, ← mul_assoc, K_mul_K_neg, one_mul]
    · simp [hj]
  · simp

/-- The inverse candidate is a right inverse on every generator, hence on the algebra. -/
theorem isolatedBraid_comp_isolatedBraidInv :
    (isolatedBraid (R := R) i hi).comp (isolatedBraidInv i hi) =
      AlgHom.id k (QuantumGroup R v) := by
  refine hom_ext (fun j ↦ ?_) (fun j ↦ ?_) (fun μ ↦ ?_)
  · by_cases hj : j = i
    · subst j
      simp only [AlgHom.comp_apply, isolatedBraidInv_E, ↓reduceIte, braidInvEi, map_neg,
        map_mul, isolatedBraid_F, braidFi, isolatedBraid_K, reflY_ktilde, mul_neg,
        neg_neg, AlgHom.id_apply, ← mul_assoc, K_mul_K_neg, one_mul]
    · simp [hj]
  · by_cases hj : j = i
    · subst j
      simp only [AlgHom.comp_apply, isolatedBraidInv_F, ↓reduceIte, braidInvFi, map_neg,
        map_mul, isolatedBraid_E, braidEi, Kt, isolatedBraid_K, reflY_ktilde, neg_mul,
        neg_neg, AlgHom.id_apply, mul_assoc, K_mul_K_neg, mul_one]
    · simp [hj]
  · simp

/-- Lusztig's braid automorphism at an isolated Dynkin node, in arbitrary ambient rank.
The inverse formulas are proved, not assumed. Coupled nodes are outside this theorem's scope. -/
def isolatedBraidEquiv : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  AlgEquiv.ofAlgHom (isolatedBraid i hi) (isolatedBraidInv i hi)
    (isolatedBraid_comp_isolatedBraidInv i hi) (isolatedBraidInv_comp_isolatedBraid i hi)

omit [NeZero v] [DecidableEq I] in
/-- Simple coroot reflections commute when their nodes are orthogonal. -/
theorem reflY_comm_of_cartanMatrix_eq_zero (j : I) (hij : D.cartanMatrix i j = 0) (μ : Y) :
    reflY R i (reflY R j μ) = reflY R j (reflY R i μ) := by
  have hji := (D.isGeneralizedCartan_cartanMatrix.zero_comm i j).mp hij
  simp [reflY_apply, R.root_coroot, hij, hji]
  abel

/-- Braid maps at isolated nodes commute, the braid relation for disconnected nodes.
This does not assert braid relations for coupled nodes. -/
theorem isolatedBraid_comp_comm (j : I)
    (hj : ∀ l, l ≠ j → D.cartanMatrix j l = 0) :
    (isolatedBraid (R := R) (v := v) i hi).comp (isolatedBraid j hj) =
      (isolatedBraid j hj).comp (isolatedBraid i hi) := by
  by_cases hij : i = j
  · subst j; rfl
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · by_cases hli : l = i
    · subst l
      simp [hij, braidEi, Kt,
        reflY_ktilde_of_cartanMatrix_eq_zero (hj i hij)]
    · by_cases hlj : l = j
      · subst l
        simp [Ne.symm hij, braidEi, Kt,
          reflY_ktilde_of_cartanMatrix_eq_zero (hi j (Ne.symm hij))]
      · simp [hli, hlj]
  · by_cases hli : l = i
    · subst l
      simp [hij, braidFi,
        reflY_ktilde_of_cartanMatrix_eq_zero (hj i hij)]
    · by_cases hlj : l = j
      · subst l
        simp [Ne.symm hij, braidFi,
          reflY_ktilde_of_cartanMatrix_eq_zero (hi j (Ne.symm hij))]
      · simp [hli, hlj]
  · simp only [AlgHom.comp_apply, isolatedBraid_K]
    rw [reflY_comm_of_cartanMatrix_eq_zero i j (hi j (Ne.symm hij))]

end QuantumGroup
