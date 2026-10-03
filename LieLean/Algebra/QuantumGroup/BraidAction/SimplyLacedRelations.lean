/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.SimplyLaced
import LieLean.Algebra.QuantumGroup.BraidAction.A2Relation

/-!
# Higher ambient-rank relations for the actual local-Cartan braid maps

## Main results

Orthogonal-node commutation and adjacent-node length-three relations on the entire
quantum-group quotient, not merely on the two distinguished generators.

## References and scope

Reconstructed from the quotient presentation and recovery identities. All local Cartan and
parameter hypotheses of `simplyLacedBraidEquiv` are retained. No finiteness, characteristic-zero
or coroot spanning assumption is imposed. Triangles through either centre are excluded.
-/

noncomputable section
namespace QuantumGroup

section Polynomial
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- Commuting outer nodes give commuting quantum adjoint operators.
Reconstructed by expansion; their two scalar parameters need not agree. -/
theorem simplyLaced_qadj_comm {a b : B} (c : B) (r s : k) (hab : Commute a b) :
    b * (a * c - r • (c * a)) - s • ((a * c - r • (c * a)) * b) =
      a * (b * c - s • (c * b)) - r • ((b * c - s • (c * b)) * a) := by
  have hswap (x : B) : b * (a * x) = a * (b * x) := by
    rw [← mul_assoc, hab.symm.eq, mul_assoc]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub,
    smul_smul, mul_assoc, hswap, hab.symm.eq]
  module

/-- Right quantum adjoint operators also commute at orthogonal nodes. -/
theorem simplyLaced_qadj_right_comm {a b : B} (c : B) (r s : k) (hab : Commute a b) :
    (c * a - r • (a * c)) * b - s • (b * (c * a - r • (a * c))) =
      (c * b - s • (b * c)) * a - r • (a * (c * b - s • (b * c))) := by
  have hswap (x : B) : b * (a * x) = a * (b * x) := by
    rw [← mul_assoc, hab.symm.eq, mul_assoc]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub,
    smul_smul, mul_assoc, hswap, hab.symm.eq]
  module

/-- Quantum Jacobi identity when the two outer entries commute. -/
theorem simplyLaced_qjacobi {a b c : B} (r s : k) (hbc : Commute b c) :
    b * (a * c - r • (c * a)) - s • ((a * c - r • (c * a)) * b) =
      (b * a - s • (a * b)) * c - r • (c * (b * a - s • (a * b))) := by
  have hswap (x : B) : c * (b * x) = b * (c * x) := by
    rw [← mul_assoc, hbc.symm.eq, mul_assoc]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub,
    smul_smul, mul_assoc, hswap, hbc.symm.eq]
  module

/-- Right-oriented quantum Jacobi identity, used for negative generators. -/
theorem simplyLaced_qjacobi_right {a b c : B} (r s : k) (hbc : Commute b c) :
    (c * a - r • (a * c)) * b - s • (b * (c * a - r • (a * c))) =
      c * (a * b - s • (b * a)) - r • ((a * b - s • (b * a)) * c) := by
  have hswap (x : B) : c * (b * x) = b * (c * x) := by
    rw [← mul_assoc, hbc.symm.eq, mul_assoc]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub,
    smul_smul, mul_assoc, hswap, hbc.symm.eq]
  module
end Polynomial

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  (i j : I)
  (hei : ∀ l, l ≠ i → D.cartanMatrix i l = 0 ∨
    (D.cartanMatrix i l = -1 ∧ D.cartanMatrix l i = -1))
  (hli : ∀ l m, D.cartanMatrix i l = -1 → D.cartanMatrix i m = -1 →
    l ≠ m → D.cartanMatrix l m = 0)
  (hpi : ∀ l m, D.cartanMatrix i l = -1 → D.cartanMatrix i m = 0 →
    D.cartanMatrix l m = 0 ∨ (D.cartanMatrix l m = -1 ∧ D.cartanMatrix m l = -1))
  (hqi : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hsi : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)
  (hej : ∀ l, l ≠ j → D.cartanMatrix j l = 0 ∨
    (D.cartanMatrix j l = -1 ∧ D.cartanMatrix l j = -1))
  (hlj : ∀ l m, D.cartanMatrix j l = -1 → D.cartanMatrix j m = -1 →
    l ≠ m → D.cartanMatrix l m = 0)
  (hpj : ∀ l m, D.cartanMatrix j l = -1 → D.cartanMatrix j m = 0 →
    D.cartanMatrix l m = 0 ∨ (D.cartanMatrix l m = -1 ∧ D.cartanMatrix m l = -1))
  (hqj : v ^ D.d j - (v ^ D.d j)⁻¹ ≠ 0)
  (hsj : v ^ D.d j + (v ^ D.d j)⁻¹ ≠ 0)

local notation "Ti" => simplyLacedBraid (R := R) i hei hli hpi hqi hsi
local notation "Tj" => simplyLacedBraid (R := R) j hej hlj hpj hqj hsj

/-- Actual orthogonal-node maps commute on every positive generator, including
common neighbours. Reconstructed from the degree-one formula. -/
theorem simplyLaced_comm_E (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) (l : I) :
    Ti (Tj (E R v l)) = Tj (Ti (E R v l)) := by
  have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i j).mp h0
  by_cases hli' : l = i
  · subst l
    simp [hij, braidEi, Kt, braidEj_eq_of_cartanMatrix_eq_zero h0',
      braidFj_eq_of_cartanMatrix_eq_zero h0', reflY_ktilde_of_cartanMatrix_eq_zero h0']
  · by_cases hlj' : l = j
    · subst l
      simp [hij.symm, braidEi, Kt, braidEj_eq_of_cartanMatrix_eq_zero h0,
        braidFj_eq_of_cartanMatrix_eq_zero h0, reflY_ktilde_of_cartanMatrix_eq_zero h0]
    · rcases hei l hli' with hi0 | ⟨hi1, _⟩ <;>
        rcases hej l hlj' with hj0 | ⟨hj1, _⟩
      · simp [hli', hlj', braidEj_eq_of_cartanMatrix_eq_zero hi0,
          braidEj_eq_of_cartanMatrix_eq_zero hj0]
      · simp [hli', hlj', hij.symm, braidEj_eq_of_cartanMatrix_eq_zero hi0,
          braidEj_eq_of_cartanMatrix_eq_zero h0, braidEj_eq_of_cartanMatrix_eq_neg_one hj1]
      · simp [hli', hlj', hij, braidEj_eq_of_cartanMatrix_eq_zero hj0,
          braidEj_eq_of_cartanMatrix_eq_zero h0', braidEj_eq_of_cartanMatrix_eq_neg_one hi1]
      · simp only [simplyLacedBraid_E, hli', hlj', hij, hij.symm, ↓reduceIte,
          braidEj_eq_of_cartanMatrix_eq_neg_one hi1,
          braidEj_eq_of_cartanMatrix_eq_neg_one hj1, map_sub, map_mul, map_smul,
          braidEj_eq_of_cartanMatrix_eq_zero h0, braidEj_eq_of_cartanMatrix_eq_zero h0']
        exact simplyLaced_qadj_comm _ _ _ (E_commute_E_of_cartanMatrix_eq_zero h0)

/-- Actual orthogonal-node maps commute on every negative generator. -/
theorem simplyLaced_comm_F (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) (l : I) :
    Ti (Tj (F R v l)) = Tj (Ti (F R v l)) := by
  have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i j).mp h0
  by_cases hli' : l = i
  · subst l
    simp [hij, braidFi, braidEj_eq_of_cartanMatrix_eq_zero h0',
      braidFj_eq_of_cartanMatrix_eq_zero h0', reflY_ktilde_of_cartanMatrix_eq_zero h0']
  · by_cases hlj' : l = j
    · subst l
      simp [hij.symm, braidFi, braidEj_eq_of_cartanMatrix_eq_zero h0,
        braidFj_eq_of_cartanMatrix_eq_zero h0, reflY_ktilde_of_cartanMatrix_eq_zero h0]
    · rcases hei l hli' with hi0 | ⟨hi1, _⟩ <;>
        rcases hej l hlj' with hj0 | ⟨hj1, _⟩
      · simp [hli', hlj', braidFj_eq_of_cartanMatrix_eq_zero hi0,
          braidFj_eq_of_cartanMatrix_eq_zero hj0]
      · simp [hli', hlj', hij.symm, braidFj_eq_of_cartanMatrix_eq_zero hi0,
          braidFj_eq_of_cartanMatrix_eq_zero h0,
          braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hj1]
      · simp [hli', hlj', hij, braidFj_eq_of_cartanMatrix_eq_zero hj0,
          braidFj_eq_of_cartanMatrix_eq_zero h0',
          braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hi1]
      · simp only [simplyLacedBraid_F, hli', hlj', hij, hij.symm, ↓reduceIte,
          braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hi1,
          braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hj1,
          map_sub, map_mul, map_smul, braidFj_eq_of_cartanMatrix_eq_zero h0,
          braidFj_eq_of_cartanMatrix_eq_zero h0']
        exact simplyLaced_qadj_right_comm _ _ _ (F_commute_F_of_cartanMatrix_eq_zero h0)

/-- Length-two braid relation on the entire actual quotient in arbitrary ambient
rank and arbitrary root-datum lattice. No isolation assumption is imposed. -/
theorem simplyLacedBraid_comm (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) :
    (Ti).comp Tj = (Tj).comp Ti := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · exact simplyLaced_comm_E i j hei hli hpi hqi hsi hej hlj hpj hqj hsj hij h0 l
  · exact simplyLaced_comm_F i j hei hli hpi hqi hsi hej hlj hpj hqj hsj hij h0 l
  · simp only [AlgHom.comp_apply, simplyLacedBraid_K,
      reflY_comm_of_cartanMatrix_eq_zero i j h0]

/-- Length-two relation for the published actual algebra equivalences. -/
theorem simplyLacedBraidEquiv_comm (hij : i ≠ j)
    (h0 : D.cartanMatrix i j = 0) :
    (simplyLacedBraidEquiv (R := R) i hei hli hpi hqi hsi).trans
      (simplyLacedBraidEquiv j hej hlj hpj hqj hsj) =
    (simplyLacedBraidEquiv j hej hlj hpj hqj hsj).trans
      (simplyLacedBraidEquiv i hei hli hpi hqi hsi) := by
  apply DFunLike.ext
  intro x
  exact (DFunLike.congr_fun
    (simplyLacedBraid_comm i j hei hli hpi hqi hsi hej hlj hpj hqj hsj hij h0) x).symm

variable (hij : i ≠ j) (h : D.cartanMatrix i j = -1)
  (h' : D.cartanMatrix j i = -1)

include hij h h'

/-- Double transport at an adjacent pair, with arbitrary extra generators present. -/
theorem simplyLaced_double_E : Ti (Tj (E R v i)) = E R v j := by
  rw [simplyLacedBraid_E, ite_eq_right hij,
    braidEj_eq_of_cartanMatrix_eq_neg_one h']
  simpa only [map_sub, map_mul, map_smul, simplyLacedBraid_E, hij.symm, ↓reduceIte,
    ← D.d_eq_of_simply_laced_edge h h'] using a2Braid_recover_Ej (R := R) i j h hqi

/-- Negative double transport in arbitrary ambient rank. -/
theorem simplyLaced_double_F : Ti (Tj (F R v i)) = F R v j := by
  rw [simplyLacedBraid_F, ite_eq_right hij,
    braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h']
  simpa only [map_sub, map_mul, map_smul, simplyLacedBraid_F, hij.symm, ↓reduceIte,
    ← D.d_eq_of_simply_laced_edge h h'] using a2Braid_recover_Fj (R := R) i j h hqi

/-- The length-three words agree on the first positive generator. -/
theorem simplyLaced_braid_Ei : Ti (Tj (Ti (E R v i))) = Tj (Ti (Tj (E R v i))) := by
  rw [simplyLaced_double_E i j hei hli hpi hqi hsi hej hlj hpj hqj hsj hij h h']
  simp only [simplyLacedBraid_E, ↓reduceIte, braidEi, map_neg, map_mul, Kt,
    simplyLacedBraid_K,
    simplyLaced_double_F i j hei hli hpi hqi hsi hej hlj hpj hqj hsj hij h h',
    reflY_reflY_ktilde_of_simply_laced_edge h h']

/-- The length-three words agree on the first negative generator. -/
theorem simplyLaced_braid_Fi : Ti (Tj (Ti (F R v i))) = Tj (Ti (Tj (F R v i))) := by
  rw [simplyLaced_double_F i j hei hli hpi hqi hsi hej hlj hpj hqj hsj hij h h']
  simp only [simplyLacedBraid_F, ↓reduceIte, braidFi, map_neg, map_mul,
    simplyLacedBraid_K,
    simplyLaced_double_E i j hei hli hpi hqi hsi hej hlj hpj hqj hsj hij h h',
    reflY_reflY_ktilde_of_simply_laced_edge h h']

/-- The new ambient-rank positive case: a third node joined to `i` and orthogonal
to `j`. Reconstructed using double transport and quantum Jacobi. -/
theorem simplyLaced_braid_E_extra (l : I) (hli' : l ≠ i) (hlj' : l ≠ j)
    (hi1 : D.cartanMatrix i l = -1) (hj0 : D.cartanMatrix j l = 0) :
    Ti (Tj (Ti (E R v l))) = Tj (Ti (Tj (E R v l))) := by
  have hiEl : Ti (E R v l) =
      E R v i * E R v l - (v ^ D.d i)⁻¹ • (E R v l * E R v i) := by
    simp [hli', braidEj_eq_of_cartanMatrix_eq_neg_one hi1]
  have hjEl : Tj (E R v l) = E R v l := by
    simp [hlj', braidEj_eq_of_cartanMatrix_eq_zero hj0]
  have hjEi : Tj (E R v i) =
      E R v j * E R v i - (v ^ D.d i)⁻¹ • (E R v i * E R v j) := by
    simp [hij, braidEj_eq_of_cartanMatrix_eq_neg_one h',
      D.d_eq_of_simply_laced_edge h h']
  calc
    Ti (Tj (Ti (E R v l))) =
        E R v j * Ti (E R v l) - (v ^ D.d i)⁻¹ • (Ti (E R v l) * E R v j) := by
      rw [hiEl, map_sub, map_mul, map_smul, map_mul, hjEl,
        map_sub, map_mul, map_smul, map_mul,
        simplyLaced_double_E i j hei hli hpi hqi hsi hej hlj hpj hqj hsj hij h h', hiEl]
    _ = Tj (E R v i) * E R v l - (v ^ D.d i)⁻¹ • (E R v l * Tj (E R v i)) := by
      rw [hiEl, hjEi]
      exact simplyLaced_qjacobi _ _ (E_commute_E_of_cartanMatrix_eq_zero hj0)
    _ = Tj (Ti (Tj (E R v l))) := by
      rw [hjEl, hiEl, map_sub, map_mul, map_smul, map_mul, hjEl]

/-- The new ambient-rank negative case at the same three-node path. -/
theorem simplyLaced_braid_F_extra (l : I) (hli' : l ≠ i) (hlj' : l ≠ j)
    (hi1 : D.cartanMatrix i l = -1) (hj0 : D.cartanMatrix j l = 0) :
    Ti (Tj (Ti (F R v l))) = Tj (Ti (Tj (F R v l))) := by
  have hiFl : Ti (F R v l) =
      F R v l * F R v i - (v ^ D.d i) • (F R v i * F R v l) := by
    simp [hli', braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hi1]
  have hjFl : Tj (F R v l) = F R v l := by
    simp [hlj', braidFj_eq_of_cartanMatrix_eq_zero hj0]
  have hjFi : Tj (F R v i) =
      F R v i * F R v j - (v ^ D.d i) • (F R v j * F R v i) := by
    simp [hij, braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h',
      D.d_eq_of_simply_laced_edge h h']
  calc
    Ti (Tj (Ti (F R v l))) =
        Ti (F R v l) * F R v j - (v ^ D.d i) • (F R v j * Ti (F R v l)) := by
      rw [hiFl, map_sub, map_mul, map_smul, map_mul, hjFl,
        map_sub, map_mul, map_smul, map_mul,
        simplyLaced_double_F i j hei hli hpi hqi hsi hej hlj hpj hqj hsj hij h h', hiFl]
    _ = F R v l * Tj (F R v i) - (v ^ D.d i) • (Tj (F R v i) * F R v l) := by
      rw [hiFl, hjFi]
      exact simplyLaced_qjacobi_right _ _ (F_commute_F_of_cartanMatrix_eq_zero hj0)
    _ = Tj (Ti (Tj (F R v l))) := by
      rw [hjFl, hiFl, map_sub, map_mul, map_smul, map_mul, hjFl]

/-- Length-three relation for the actual quotient homomorphisms in arbitrary
ambient rank. The local orthogonal-neighbour hypothesis rules out triangles;
every extra positive/negative and every arbitrary toral generator is checked. -/
theorem simplyLacedBraid_braid :
    (Ti).comp ((Tj).comp Ti) = (Tj).comp ((Ti).comp Tj) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · by_cases hli' : l = i
    · subst l
      exact simplyLaced_braid_Ei i j hei hli hpi hqi hsi hej hlj hpj hqj hsj hij h h'
    · by_cases hlj' : l = j
      · subst l
        exact (simplyLaced_braid_Ei j i hej hlj hpj hqj hsj hei hli hpi hqi hsi hij.symm h' h).symm
      · rcases hei l hli' with hi0 | ⟨hi1, _⟩
        · rcases hej l hlj' with hj0 | ⟨hj1, _⟩
          · simp [hli', hlj', braidEj_eq_of_cartanMatrix_eq_zero hi0,
              braidEj_eq_of_cartanMatrix_eq_zero hj0]
          · exact (simplyLaced_braid_E_extra j i hej hlj hpj hqj hsj hei hli hpi hqi hsi
              hij.symm h' h l hlj' hli' hj1 hi0).symm
        · exact simplyLaced_braid_E_extra i j hei hli hpi hqi hsi hej hlj hpj hqj hsj
            hij h h' l hli' hlj' hi1 (hli j l h hi1 (Ne.symm hlj'))
  · by_cases hli' : l = i
    · subst l
      exact simplyLaced_braid_Fi i j hei hli hpi hqi hsi hej hlj hpj hqj hsj hij h h'
    · by_cases hlj' : l = j
      · subst l
        exact (simplyLaced_braid_Fi j i hej hlj hpj hqj hsj hei hli hpi hqi hsi hij.symm h' h).symm
      · rcases hei l hli' with hi0 | ⟨hi1, _⟩
        · rcases hej l hlj' with hj0 | ⟨hj1, _⟩
          · simp [hli', hlj', braidFj_eq_of_cartanMatrix_eq_zero hi0,
              braidFj_eq_of_cartanMatrix_eq_zero hj0]
          · exact (simplyLaced_braid_F_extra j i hej hlj hpj hqj hsj hei hli hpi hqi hsi
              hij.symm h' h l hlj' hli' hj1 hi0).symm
        · exact simplyLaced_braid_F_extra i j hei hli hpi hqi hsi hej hlj hpj hqj hsj
            hij h h' l hli' hlj' hi1 (hli j l h hi1 (Ne.symm hlj'))
  · simp only [AlgHom.comp_apply, simplyLacedBraid_K,
      reflY_braid_of_simply_laced_edge h h']

/-- The published actual local-Cartan algebra equivalences satisfy the adjacent
braid relation on the whole quotient, without a two-node or lattice-spanning hypothesis. -/
theorem simplyLacedBraidEquiv_braid :
    let ei := simplyLacedBraidEquiv (R := R) i hei hli hpi hqi hsi
    let ej := simplyLacedBraidEquiv (R := R) j hej hlj hpj hqj hsj
    (ei.trans ej).trans ei = (ej.trans ei).trans ej := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun
    (simplyLacedBraid_braid i j hei hli hpi hqi hsi hej hlj hpj hqj hsj hij h h') x

end QuantumGroup
