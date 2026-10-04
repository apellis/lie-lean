/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.Mixed

/-!
# A genuinely coupled diagonal mixed quantum braid relation

## Main results

* `QuantumGroup.braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_one` proves the
  diagonal `E,F` presentation relation for the existing candidate braid images when
  `aᵢⱼ = -1`. The ambient rank and reverse Cartan entry are unrestricted.
* `QuantumGroup.braidEj_mul_Fi_sub_of_cartanMatrix_eq_neg_one` and
  `QuantumGroup.braidEj_mul_Fj_sub_of_cartanMatrix_eq_neg_one` supply the two lowering
  commutators used in the proof.

## References

The proof is reconstructed from the defining presentation and the candidate images in
`BraidAction/Mixed.lean`; no external theorem numbering is asserted. It needs explicitly
`v ≠ 0` and `vᵢ - vᵢ⁻¹ ≠ 0`, not merely a nonzero parameter. No characteristic-zero,
finite-rank, type-1, or field-specialization hypothesis is introduced. This file neither
constructs a general-node automorphism nor a faithful integrable action. Higher-degree
diagonal relations, fully coupled off-diagonal relations, and transformed Serre relations
remain outside this boundary.
-/

open LieLean


noncomputable section
namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j : I}

/-- Degree-one braid image, directly expanded from the existing Serre-sum definition. -/
theorem braidEj_eq_of_cartanMatrix_eq_neg_one (h : D.cartanMatrix i j = -1) :
    braidEj R v i j = E R v i * E R v j - (v ^ D.d i)⁻¹ • (E R v j * E R v i) := by
  simp [braidEj, negA, h, serreAux, Finset.sum_range_succ, sub_eq_add_neg,
    qFactorial, qInt]

/-- Degree-one negative braid image, directly expanded from the existing definition. -/
theorem braidFj_eq_of_cartanMatrix_eq_neg_one (hv : v ≠ 0)
    (h : D.cartanMatrix i j = -1) :
    braidFj R v i j = F R v j * F R v i - (v ^ D.d i) • (F R v i * F R v j) := by
  simp [braidFj, negA, h, serreAux, Finset.sum_range_succ, smul_add,
    smul_smul, pow_ne_zero _ hv, sub_eq_add_neg, qFactorial, qInt, add_comm]

section Ring
variable {B : Type*} [Ring B] [Algebra k B]

private lemma commutator_qcomm_left (a b c : B) (t : k) (h : Commute b c) :
    (a * b - t • (b * a)) * c - c * (a * b - t • (b * a)) =
      (a * c - c * a) * b - t • (b * (a * c - c * a)) := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, mul_assoc]
  rw [h.eq, ← mul_assoc c b a, ← h.eq, mul_assoc]
  module

private lemma commutator_qcomm_right (a b d : B) (t : k) (h : Commute a d) :
    (a * b - t • (b * a)) * d - d * (a * b - t • (b * a)) =
      a * (b * d - d * b) - t • ((b * d - d * b) * a) := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub, mul_assoc]
  rw [h.eq, ← mul_assoc d a b, ← h.eq, mul_assoc]
  module

end Ring

/-- Toral commutation at a coupled edge, reconstructed from the presentation. -/
lemma Kt_mul_E_of_cartanMatrix_eq_neg_one (h : D.cartanMatrix i j = -1) :
    Kt R v i * E R v j = (v ^ D.d i)⁻¹ • (E R v j * Kt R v i) := by
  rw [Kt, K_mul_E, root_ktilde, h, mul_neg_one, zpow_neg, zpow_natCast]

/-- Inverse toral commutation at a coupled edge. -/
lemma K_neg_mul_E_of_cartanMatrix_eq_neg_one (h : D.cartanMatrix i j = -1) :
    K R v (-ktilde R i) * E R v j = (v ^ D.d i) • (E R v j * K R v (-ktilde R i)) := by
  rw [K_mul_E, map_neg, root_ktilde, h, mul_neg_one, neg_neg, zpow_natCast]

/-- The first lowering commutator of a coupled braid image. Reconstructed directly from
`E_mul_F_sub`, the off-diagonal commutator, and toral commutation. -/
theorem braidEj_mul_Fi_sub_of_cartanMatrix_eq_neg_one
    (h : D.cartanMatrix i j = -1) (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    braidEj R v i j * F R v i - F R v i * braidEj R v i j =
      -(E R v j * K R v (-ktilde R i)) := by
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  rw [braidEj_eq_of_cartanMatrix_eq_neg_one h,
    commutator_qcomm_left _ _ _ _ (E_mul_F_of_ne hij.symm), E_mul_F_sub]
  simp only [↓reduceIte, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub]
  rw [Kt_mul_E_of_cartanMatrix_eq_neg_one h, K_neg_mul_E_of_cartanMatrix_eq_neg_one h]
  have hc : (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ * (v ^ D.d i - (v ^ D.d i)⁻¹) = 1 :=
    inv_mul_cancel₀ hq
  simp only [smul_smul]
  linear_combination (norm := module) - congrArg
    (fun t : k ↦ t • (E R v j * K R v (-ktilde R i))) hc

omit [DecidableEq I] in
/-- The reflected coroot at a directed simple edge adds `ktilde i`; the reverse Cartan
entry is unrestricted. This uses the Cartan symmetrizer identity. -/
lemma reflY_ktilde_of_cartanMatrix_eq_neg_one (h : D.cartanMatrix i j = -1) :
    reflY R i (ktilde R j) = ktilde R j + ktilde R i := by
  have hr : R.root i (ktilde R j) = -(D.d i : ℤ) := by
    rw [root_ktilde, ← D.d_mul_cartanMatrix_comm i j, h, mul_neg_one]
  rw [reflY_apply, hr, neg_smul, sub_neg_eq_add, natCast_zsmul]
  rfl

/-- The second lowering commutator for the degree-one coupled braid image.
Reconstructed directly from the presentation; no restriction on the reverse Cartan entry. -/
theorem braidEj_mul_Fj_sub_of_cartanMatrix_eq_neg_one
    (hv : v ≠ 0) (h : D.cartanMatrix i j = -1) :
    braidEj R v i j * F R v j - F R v j * braidEj R v i j =
      ((v ^ D.d j - (v ^ D.d j)⁻¹)⁻¹ * (1 - (v ^ D.d i)⁻¹ * (v ^ D.d i)⁻¹)) •
        (E R v i * Kt R v j) := by
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have hr : R.root i (ktilde R j) = -(D.d i : ℤ) := by
    rw [root_ktilde, ← D.d_mul_cartanMatrix_comm i j, h, mul_neg_one]
  have hL : Kt R v j * E R v i = (v ^ D.d i)⁻¹ • (E R v i * Kt R v j) := by
    rw [Kt, K_mul_E, hr, zpow_neg, zpow_natCast]
  have hL' : K R v (-ktilde R j) * E R v i =
      (v ^ D.d i) • (E R v i * K R v (-ktilde R j)) := by
    rw [K_mul_E, map_neg, hr, neg_neg, zpow_natCast]
  rw [braidEj_eq_of_cartanMatrix_eq_neg_one h,
    commutator_qcomm_right _ _ _ _ (E_mul_F_of_ne hij), E_mul_F_sub]
  simp only [↓reduceIte, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub]
  rw [hL, hL']
  simp only [smul_smul]
  have hc := inv_mul_cancel₀ (pow_ne_zero (D.d i) hv)
  linear_combination (norm := module)
    congrArg (fun t : k ↦ ((v ^ D.d j - (v ^ D.d j)⁻¹)⁻¹ * t) •
      (E R v i * K R v (-ktilde R j))) hc

/-- The diagonal mixed braid relation at a genuinely coupled edge `aᵢⱼ = -1`, in arbitrary
ambient rank. No restriction is imposed on `aⱼᵢ`. The parameter assumptions are explicit:
`v ≠ 0` and `vᵢ - vᵢ⁻¹ ≠ 0`. Reconstructed directly from the presentation, rather than assuming
faithfulness or a braid automorphism. This proves one missing relation, not the automorphism. -/
theorem braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_one
    (hv : v ≠ 0) (h : D.cartanMatrix i j = -1)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    braidEj R v i j * braidFj R v i j - braidFj R v i j * braidEj R v i j =
      (v ^ D.d j - (v ^ D.d j)⁻¹)⁻¹ •
        (braidK R v i (.ofAdd (ktilde R j)) - braidK R v i (.ofAdd (-ktilde R j))) := by
  let a := E R v i
  let b := E R v j
  let c := F R v i
  let d := F R v j
  let L := Kt R v j
  let K' := K R v (-ktilde R i)
  let q := v ^ D.d i
  let p := (v ^ D.d j - (v ^ D.d j)⁻¹)⁻¹
  let t := p * (1 - q⁻¹ * q⁻¹)
  have hq0 : q ≠ 0 := pow_ne_zero _ hv
  have hr : R.root i (ktilde R j) = -(D.d i : ℤ) := by
    rw [root_ktilde, ← D.d_mul_cartanMatrix_comm i j, h, mul_neg_one]
  have hLc : L * c = q • (c * L) := by
    dsimp [L, c, q]
    rw [Kt, K_mul_F, hr, neg_neg, zpow_natCast]
  have hKd : K' * d = q⁻¹ • (d * K') := by
    dsimp [K', d, q]
    rw [K_mul_F, map_neg, neg_neg, root_ktilde, h, mul_neg_one, zpow_neg, zpow_natCast]
  have hXi := braidEj_mul_Fi_sub_of_cartanMatrix_eq_neg_one (R := R) h hq
  have hXj := braidEj_mul_Fj_sub_of_cartanMatrix_eq_neg_one (R := R) hv h
  let X := braidEj R v i j
  change X * c - c * X = -(b * K') at hXi
  change X * d - d * X = t • (a * L) at hXj
  have he : X * (d * c - q • (c * d)) - (d * c - q • (c * d)) * X =
      (X * d - d * X) * c + d * (X * c - c * X) -
        q • ((X * c - c * X) * d + c * (X * d - d * X)) := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub,
      mul_assoc]
    module
  rw [braidFj_eq_of_cartanMatrix_eq_neg_one hv h]
  change X * (d * c - q • (c * d)) - (d * c - q • (c * d)) * X = _
  rw [he, hXi, hXj]
  have he' : t • (a * L) * c + d * -(b * K') -
      q • (-(b * K') * d + c * (t • (a * L))) =
      (t * q) • ((a * c - c * a) * L) + (b * d - d * b) * K' := by
    simp only [smul_mul_assoc, mul_smul_comm, mul_neg, neg_mul, sub_mul, smul_sub,
      smul_add, smul_neg, mul_assoc]
    rw [hLc, hKd]
    simp only [mul_smul_comm, smul_smul]
    have hc := mul_inv_cancel₀ hq0
    linear_combination (norm := module)
      congrArg (fun s : k ↦ s • (b * (d * K'))) hc
  rw [he']
  have hac : a * c - c * a = (q - q⁻¹)⁻¹ • (Kt R v i - K') := by
    simpa only [↓reduceIte] using E_mul_F_sub R v i i
  have hbd : b * d - d * b = p • (L - K R v (-ktilde R j)) := by
    simpa only [↓reduceIte] using E_mul_F_sub R v j j
  have ht : t * q * (q - q⁻¹)⁻¹ = p := by
    dsimp [t]
    field_simp
    grind
  rw [hac, hbd, smul_mul_assoc, smul_smul, ht, smul_mul_assoc, ← smul_add]
  rw [braidK_apply, braidK_apply, map_neg,
    reflY_ktilde_of_cartanMatrix_eq_neg_one h, ← K_add, neg_add, ← K_add]
  congr 1
  dsimp [L, K', Kt]
  rw [sub_mul, sub_mul, K_comm (R := R) (v := v) (ktilde R j) (-ktilde R i),
    K_comm (R := R) (v := v) (-ktilde R j) (-ktilde R i),
    K_comm (R := R) (v := v) (ktilde R i) (ktilde R j)]
  abel

end LieLean.QuantumGroup
