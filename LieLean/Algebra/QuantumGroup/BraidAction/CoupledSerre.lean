/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.Coupled

/-!
# A transformed positive quantum Serre relation at a simple edge

## Main results

The actual candidate images `braidEi`, `braidEj` satisfy the degree-two positive
Serre relation at a directed simple edge. In particular this applies to a simply-laced
adjacent pair, with no restriction on the other nodes of the datum.

## References

Reconstructed directly from the defining presentation and the lowering commutator in
`BraidAction/Coupled.lean`; no external source was consulted. No braid automorphism,
faithful module action, finite type, or rank-one specialization is assumed.
-/

noncomputable section
namespace QuantumGroup

variable {k : Type*} [Field k]

section Ring
variable {B : Type*} [Ring B] [Algebra k B]

private lemma qSerre_two_expansion (q : k) (a b : B) :
    qSerre q 2 a b = a * (a * b) - (q + q⁻¹) • (a * (b * a)) + b * (a * a) := by
  simp [qSerre, Finset.sum_range_succ, qBinomial, pow_two, mul_assoc]
  module

end Ring

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j : I}

/-- The positive Serre relation for the actual images of the reflected node and an
adjacent node. Reconstructed from the presentation. The reverse Cartan entry is
unrestricted; in particular a simply-laced pair is included. -/
theorem qSerre_braidEi_braidEj_of_cartanMatrix_eq_neg_one [NeZero v]
    (h : D.cartanMatrix i j = -1)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat
      (braidEi R i) (braidEj R v i j) = 0 := by
  have hv := NeZero.ne v
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  let q := v ^ D.d i
  let A := braidEi (v := v) R i
  let X := braidEj R v i j
  let b := E R v j
  have hq0 : q ≠ 0 := pow_ne_zero _ hv
  have hKX : Kt R v i * X = q • (X * Kt R v i) := by
    have ht := braidK_mul_braidEj (R := R) hv hij (-ktilde R i)
    rw [braidK_apply, reflY_neg_ktilde, map_neg, root_ktilde, h,
      mul_neg_one, neg_neg, zpow_natCast] at ht
    exact ht
  have hAX : A * X - q • (X * A) = -q • b := by
    have hc := congrArg (fun z : QuantumGroup R v ↦ z * Kt R v i)
      (braidEj_mul_Fi_sub_of_cartanMatrix_eq_neg_one (R := R) h hq)
    change (X * F R v i - F R v i * X) * Kt R v i =
      -(b * K R v (-ktilde R i)) * Kt R v i at hc
    simp only [sub_mul, neg_mul, mul_assoc, K_neg_mul_Kt, mul_one] at hc
    dsimp [A, braidEi]
    simp only [neg_mul, mul_neg, mul_assoc]
    rw [hKX, mul_smul_comm]
    linear_combination (norm := module) congrArg (fun z : QuantumGroup R v ↦ q • z) hc
  have hAb : A * b = q⁻¹ • (b * A) := by
    change -(F R v i * Kt R v i) * E R v j =
      q⁻¹ • (E R v j * -(F R v i * Kt R v i))
    simp only [neg_mul, mul_neg, smul_neg, mul_assoc]
    rw [Kt_mul_E_of_cartanMatrix_eq_neg_one h, mul_smul_comm,
      ← mul_assoc, ← E_mul_F_of_ne hij.symm, mul_assoc]
  have he : qSerre q 2 A X = A * (A * X - q • (X * A)) -
      q⁻¹ • ((A * X - q • (X * A)) * A) := by
    rw [qSerre_two_expansion]
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub,
      smul_smul, mul_assoc, inv_mul_cancel₀ hq0, one_smul, add_smul]
    module
  rw [h]
  change qSerre q 2 A X = 0
  rw [he, hAX]
  simp [hAb, smul_smul, hq0]

end QuantumGroup

