/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.Coupled
import LieLean.Algebra.QuantumGroup.BraidAction.Isolated

/-!
# Fully coupled off-diagonal braid commutators at two directed simple edges

## Main results

* `QuantumGroup.braidEj_mul_braidFj_sub_of_two_cartanMatrix_eq_neg_one`: the two
  candidate images commute for distinct target nodes `j,l` with `aᵢⱼ = aᵢₗ = -1`.
  The reverse entries and all entries between `j` and `l` are unrestricted.

## References

Reconstructed directly from the quantum group presentation and the degree-one
lowering identity in `BraidAction/Coupled.lean`.
This is an additional defining relation, not a construction of a braid automorphism.
-/

noncomputable section

namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j l : I}

/-- The fully coupled off-diagonal mixed braid relation when both outgoing Cartan
entries are `-1`. Reconstructed from the presentation: the lowering commutator
leaves two terms, which cancel by toral commutation. No condition on `aⱼₗ`, `aₗⱼ`,
`aⱼᵢ`, or `aₗᵢ` is required. The ambient rank and characteristic are unrestricted. -/
theorem braidEj_mul_braidFj_sub_of_two_cartanMatrix_eq_neg_one
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -1)
    (hil : D.cartanMatrix i l = -1) (hjl : j ≠ l)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    braidEj R v i j * braidFj R v i l - braidFj R v i l * braidEj R v i j = 0 := by
  have hil' : i ≠ l := by
    rintro rfl
    rw [D.cartanMatrix_self] at hil
    norm_num at hil
  let X := braidEj R v i j
  let c := F R v i
  let d := F R v l
  let b := E R v j
  let K' := K R v (-ktilde R i)
  let q := v ^ D.d i
  have hXd : Commute X d := braidEj_commute_F hil' hjl
  have hXc := braidEj_mul_Fi_sub_of_cartanMatrix_eq_neg_one (R := R) hij hq
  change X * c - c * X = -(b * K') at hXc
  have hKd : K' * d = q⁻¹ • (d * K') := by
    dsimp [K', d, q]
    rw [K_mul_F, map_neg, neg_neg, root_ktilde, hil, mul_neg_one,
      zpow_neg, zpow_natCast]
  have hbd : Commute b d := E_mul_F_of_ne hjl
  have he : X * (d * c - q • (c * d)) - (d * c - q • (c * d)) * X =
      d * (X * c - c * X) - q • ((X * c - c * X) * d) := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub,
      mul_assoc]
    rw [← mul_assoc X d c, hXd.eq, mul_assoc]
    module
  rw [braidFj_eq_of_cartanMatrix_eq_neg_one hv hil]
  change X * (d * c - q • (c * d)) - (d * c - q • (c * d)) * X = 0
  rw [he, hXc]
  simp only [mul_neg, neg_mul, smul_neg, sub_neg_eq_add, mul_assoc]
  rw [hKd, mul_smul_comm, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hv), one_smul]
  rw [← mul_assoc d b K', ← hbd.eq, mul_assoc]
  exact neg_add_cancel _

/-- The fully coupled degree-one result in `Commute` form. -/
theorem braidEj_commute_braidFj_of_two_cartanMatrix_eq_neg_one
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -1)
    (hil : D.cartanMatrix i l = -1) (hjl : j ≠ l)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    Commute (braidEj R v i j) (braidFj R v i l) :=
  sub_eq_zero.mp (braidEj_mul_braidFj_sub_of_two_cartanMatrix_eq_neg_one hv hij hil hjl hq)

end QuantumGroup
