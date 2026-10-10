/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.IntegralG2Commuting
import LieLean.Algebra.QuantumGroup.PBW.RankTwoG2BraidSpan

/-!
# The complete normalized G₂ relations

All fifteen pair relations for the order `e < A < B < C < D < f` are assembled in
`G2Integral.Rel`. For the normalized root vectors `A = X3`, `B = X2`, `C = Z`, `D = x1`,
they follow from the two Serre relations (`G2Integral.rel_of_serre`). At a non-root-of-unity
parameter the auxiliary scalar assumptions disappear (`G2Integral.rel_of_not_root`).

These are degree-one commutation identities, not the full divided-power straightening theorem.
-/

noncomputable section

namespace LieLean.QuantumGroup

namespace G2Integral

variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- The fifteen pair relations among the normalized ordered G₂ root vectors.
The parameters of `e, B, D` are `q`, those of `A, C, f` are `q³`. -/
structure Rel (q : k) (e A b C D f : B) : Prop where
  Ae : A * e = (q ^ 3)⁻¹ • (e * A)
  Be : b * e = q⁻¹ • (e * b) - (q⁻¹ * qInt q 3) • A
  BA : b * A = (q ^ 3)⁻¹ • (A * b)
  Ce : C * e = e * C - (q ^ 2 - 1) • b ^ 2
  CA : C * A = (q ^ 3)⁻¹ • (A * C) -
    ((q ^ 2 - 1) ^ 2 / (q ^ 2 * qInt q 3)) • b ^ 3
  CB : C * b = (q ^ 3)⁻¹ • (b * C)
  De : D * e = q • (e * D) - (q * qInt q 2) • b
  DA : D * A = A * D - (q ^ 2 - 1) • b ^ 2
  DB : D * b = q⁻¹ • (b * D) - (q⁻¹ * qInt q 3) • C
  DC : D * C = (q ^ 3)⁻¹ • (C * D)
  fe : f * e = q ^ 3 • (e * f) - q ^ 3 • D
  fA : f * A = q ^ 3 • (A * f) + (q ^ 4 + q ^ 2 - 1) • C -
    (q ^ 2 * (q ^ 2 - 1)) • (b * D)
  fB : f * b = b * f - (q ^ 2 - 1) • D ^ 2
  fC : f * C = (q ^ 3)⁻¹ • (C * f) -
    ((q ^ 2 - 1) ^ 2 / (q ^ 2 * qInt q 3)) • D ^ 3
  fD : f * D = (q ^ 3)⁻¹ • (D * f)

variable {q : k} {e f : B}

/-- The complete normalized relations, derived from the two Serre relations. -/
theorem rel_of_serre (hq : q ≠ 0) (h2 : qInt q 2 ≠ 0) (h3 : qInt q 3 ≠ 0)
    (h4 : q ^ 4 + 1 ≠ 0) (h6 : q ^ 4 - q ^ 2 + 1 ≠ 0)
    (hS4 : qSerre q 4 e f = 0) (hS2 : qSerre (q ^ 3) 2 f e = 0) :
    Rel q e (X3 q e f) (X2 q e f) (Z q e f) (G2PBW.x1 q e f) f where
  Ae := X3_mul_e hq hS4
  Be := X2_mul_e hq h2 h3
  BA := X2_mul_X3 hq h4 hS4 hS2
  Ce := Z_mul_e hq h2 h3 hS4 hS2
  CA := Z_mul_X3 hq h2 h3 h4 hS4 hS2
  CB := Z_mul_X2 hq h4 h6 hS4 hS2
  De := x1_mul_e hq h2
  DA := x1_mul_X3 hq h2 h3 hS4 hS2
  DB := x1_mul_X2 hq h2 h3
  DC := x1_mul_Z hq h2 h6 hS4 hS2
  fe := f_mul_e hq
  fA := f_mul_X3 hq h2 h3 hS2
  fB := f_mul_X2 hq h2 hS2
  fC := f_mul_Z hq h2 h3 hS2
  fD := f_mul_x1 hq hS2

lemma fourth_add_one_ne_zero (hn : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) : q ^ 4 + 1 ≠ 0 := by
  intro hz
  have h4 : q ^ 4 = -1 := eq_neg_of_add_eq_zero_left hz
  apply hn 8 (by decide)
  rw [show 8 = 4 * 2 by decide, pow_mul, h4]
  ring

lemma sixth_cyclotomic_ne_zero (hn : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) :
    q ^ 4 - q ^ 2 + 1 ≠ 0 := by
  intro hz
  have h6 : q ^ 6 = -1 := by linear_combination (q ^ 2 + 1) * hz
  apply hn 12 (by decide)
  rw [show 12 = 6 * 2 by decide, pow_mul, h6]
  ring

/-- No auxiliary scalar restrictions are needed at a nonzero parameter which is not a root
of unity. -/
theorem rel_of_not_root (hq : q ≠ 0) (hn : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
    (hS4 : qSerre q 4 e f = 0) (hS2 : qSerre (q ^ 3) 2 f e = 0) :
    Rel q e (X3 q e f) (X2 q e f) (Z q e f) (G2PBW.x1 q e f) f :=
  rel_of_serre hq (qInt_ne_zero_of_pow_ne_one hq hn (by decide))
    (qInt_ne_zero_of_pow_ne_one hq hn (by decide)) (fourth_add_one_ne_zero hn)
    (sixth_cyclotomic_ne_zero hn) hS4 hS2

lemma g2c3_eq {q : k} (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0)
    (hf : qFactorial q 3 ≠ 0) : g2c3 q = (qInt q 2)⁻¹ := by
  have h2 : qInt q 2 ≠ 0 := (mul_ne_zero_iff.mp (qFactorial_three (q := q) ▸ hf)).1
  have h3 : qInt q 3 ≠ 0 := (mul_ne_zero_iff.mp (qFactorial_three (q := q) ▸ hf)).2
  rw [g2c3, tripleSix_cc_three hq hd, ← qInt_three hq, qFactorial_three]
  field_simp

lemma g2c2_eq {q : k} (hq : q ≠ 0) (hd : q - q⁻¹ ≠ 0)
    (hf : qFactorial q 3 ≠ 0) : g2c2 q = qInt q 2 := by
  have h2 : qInt q 2 ≠ 0 := (mul_ne_zero_iff.mp (qFactorial_three (q := q) ▸ hf)).1
  have h3 : qInt q 3 ≠ 0 := (mul_ne_zero_iff.mp (qFactorial_three (q := q) ▸ hf)).2
  rw [g2c2, tripleSix_cc_three hq hd, tripleSix_cc_two hq hd,
    ← qInt_three hq, ← qInt_two, qFactorial_three]
  field_simp

end G2Integral

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k) [NeZero v]
  (T : I → QuantumGroup R v ≃ₐ[k] QuantumGroup R v)
  {i j : I} (Hi : HasBraidGeneratorImages i (T i).toAlgHom)
  (Hj : HasBraidGeneratorImages j (T j).toAlgHom)
  (hij : i ≠ j) (h : D.cartanMatrix i j = -3) (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) (hf : qFactorial (v ^ D.d i) 3 ≠ 0)

include Hi Hj hij h h' hq hf in
/-- The actual G₂ braid root vectors in the normalization of `G2Integral.Rel`. -/
theorem altVec_g2_normalized : OrderedSpan.altVec T (E R v) i j 6 =
    ![E R v i, G2Integral.X3 (v ^ D.d i) (E R v i) (E R v j),
      G2Integral.X2 (v ^ D.d i) (E R v i) (E R v j),
      G2Integral.Z (v ^ D.d i) (E R v i) (E R v j),
      G2PBW.x1 (v ^ D.d i) (E R v i) (E R v j), E R v j] := by
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have h2 : qInt (v ^ D.d i) 2 ≠ 0 :=
    (mul_ne_zero_iff.mp (G2Integral.qFactorial_three (q := v ^ D.d i) ▸ hf)).1
  rw [altVec_g2 R v T Hi Hj hij h h' hq hf,
    G2Integral.g2c3_eq hq0 hq hf, G2Integral.g2c2_eq hq0 hq hf]
  simp only [G2Integral.X3, G2Integral.X2, G2Integral.Z, mul_assoc, inv_mul_cancel₀ h2,
    mul_one, one_smul]

end LieLean.QuantumGroup
