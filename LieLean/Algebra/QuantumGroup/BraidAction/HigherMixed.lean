/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.DegreeTwo
import LieLean.Algebra.QuantumGroup.BraidAction.CoupledMixed

/-!
# Degree-two coupled off-diagonal mixed braid relations

## Main results
The actual quotient candidate images commute for distinct target nodes when their
outgoing Cartan entries are (-2,-1), (-1,-2), or (-2,-2).
Ambient rank, reverse entries, and entries between the targets are unrestricted.
Only `v ≠ 0` is assumed. The actual candidates retain their explicit totalized
inverse factors `(q_i + q_i⁻¹)⁻¹`, and the presentation uses `(q_i - q_i⁻¹)⁻¹`.
Here neither factor needs to be cancelled: all coefficients vanish before division.
Identifying these candidates with nonsingular divided-power formulas still requires
the corresponding quantum factorial to be nonzero. No such identification is needed
for the quotient identities proved here.

## References
Reconstructed directly from the quotient presentation.
These are defining-relation prerequisites, not an automorphism construction.
-/

noncomputable section
namespace QuantumGroup
variable {k : Type*} [Field k]
section Ring
variable {B : Type*} [Ring B] [Algebra k B]

set_option maxHeartbeats 4000000 in
-- Normal ordering expands the commutator into many scalar coefficients.
private lemma higher_mixed_2_1 (a b c d u u' : B) (q : k)
    (hq : q ≠ 0)
    (hac : a * c = c * a + (q - q⁻¹)⁻¹ • (u - u'))
    (hbd : b * d = d * b)
    (had : a * d = d * a)
    (hbc : b * c = c * b)
    (hua : u * a = q ^ 2 • (a * u))
    (huc : u * c = q⁻¹ ^ 2 • (c * u))
    (hu'a : u' * a = q⁻¹ ^ 2 • (a * u'))
    (hu'c : u' * c = q ^ 2 • (c * u'))
    (hub : u * b = q⁻¹ ^ 2 • (b * u))
    (hud : u * d = q • (d * u))
    (hu'b : u' * b = q ^ 2 • (b * u'))
    (hu'd : u' * d = q⁻¹ • (d * u')) :
    let X := ((q + q⁻¹)⁻¹ • (a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) + q⁻¹ ^ 2 • (b * a ^ 2)))
    let Z := (d * c - q • (c * d))
    X * Z - Z * X = 0 := by
  have hac_assoc (z : B) := congrArg (fun t : B ↦ t * z) hac
  have hbd_assoc (z : B) := congrArg (fun t : B ↦ t * z) hbd
  have had_assoc (z : B) := congrArg (fun t : B ↦ t * z) had
  have hbc_assoc (z : B) := congrArg (fun t : B ↦ t * z) hbc
  have hua_assoc (z : B) := congrArg (fun t : B ↦ t * z) hua
  have huc_assoc (z : B) := congrArg (fun t : B ↦ t * z) huc
  have hu'a_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'a
  have hu'c_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'c
  have hub_assoc (z : B) := congrArg (fun t : B ↦ t * z) hub
  have hud_assoc (z : B) := congrArg (fun t : B ↦ t * z) hud
  have hu'b_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'b
  have hu'd_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'd
  simp only [mul_assoc, add_mul, sub_mul, smul_mul_assoc] at *
  simp only [pow_two, mul_sub, mul_add, mul_smul_comm, smul_add, smul_sub, mul_assoc,
    hac, hbd, had, hbc, hua, hu'a, hub, hud, hu'b, hu'd, hac_assoc, hbd_assoc, had_assoc,
    hbc_assoc, hua_assoc, hu'a_assoc, hub_assoc, hud_assoc, hu'b_assoc, hu'd_assoc]
  match_scalars <;> field_simp [hq] <;> ring

set_option maxHeartbeats 4000000 in
-- Normal ordering expands the commutator into many scalar coefficients.
private lemma higher_mixed_1_2 (a b c d u u' : B) (q : k)
    (hq : q ≠ 0)
    (hac : a * c = c * a + (q - q⁻¹)⁻¹ • (u - u'))
    (hbd : b * d = d * b)
    (had : a * d = d * a)
    (hbc : b * c = c * b)
    (hua : u * a = q ^ 2 • (a * u))
    (huc : u * c = q⁻¹ ^ 2 • (c * u))
    (hu'a : u' * a = q⁻¹ ^ 2 • (a * u'))
    (hu'c : u' * c = q ^ 2 • (c * u'))
    (hub : u * b = q⁻¹ • (b * u))
    (hud : u * d = q ^ 2 • (d * u))
    (hu'b : u' * b = q • (b * u'))
    (hu'd : u' * d = q⁻¹ ^ 2 • (d * u')) :
    let X := (a * b - q⁻¹ • (b * a))
    let Z := ((q + q⁻¹)⁻¹ • (q ^ 2 • (c ^ 2 * d) - ((q + q⁻¹) * q) • (c * d * c) + d * c ^ 2))
    X * Z - Z * X = 0 := by
  have hac_assoc (z : B) := congrArg (fun t : B ↦ t * z) hac
  have hbd_assoc (z : B) := congrArg (fun t : B ↦ t * z) hbd
  have had_assoc (z : B) := congrArg (fun t : B ↦ t * z) had
  have hbc_assoc (z : B) := congrArg (fun t : B ↦ t * z) hbc
  have hua_assoc (z : B) := congrArg (fun t : B ↦ t * z) hua
  have huc_assoc (z : B) := congrArg (fun t : B ↦ t * z) huc
  have hu'a_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'a
  have hu'c_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'c
  have hub_assoc (z : B) := congrArg (fun t : B ↦ t * z) hub
  have hud_assoc (z : B) := congrArg (fun t : B ↦ t * z) hud
  have hu'b_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'b
  have hu'd_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'd
  simp only [mul_assoc, add_mul, sub_mul, smul_mul_assoc] at *
  simp only [pow_two, mul_sub, mul_add, mul_smul_comm, smul_add, smul_sub, mul_assoc,
    hac, hbd, had, hbc, huc, hu'c, hub, hud, hu'b, hu'd, hac_assoc, hbd_assoc, had_assoc,
    hbc_assoc, huc_assoc, hu'c_assoc, hud_assoc, hu'd_assoc]
  match_scalars <;> field_simp [hq] <;> ring

set_option maxHeartbeats 4000000 in
-- Normal ordering expands the commutator into many scalar coefficients.
private lemma higher_mixed_2_2 (a b c d u u' : B) (q : k)
    (hq : q ≠ 0)
    (hac : a * c = c * a + (q - q⁻¹)⁻¹ • (u - u'))
    (hbd : b * d = d * b)
    (had : a * d = d * a)
    (hbc : b * c = c * b)
    (hua : u * a = q ^ 2 • (a * u))
    (huc : u * c = q⁻¹ ^ 2 • (c * u))
    (hu'a : u' * a = q⁻¹ ^ 2 • (a * u'))
    (hu'c : u' * c = q ^ 2 • (c * u'))
    (hub : u * b = q⁻¹ ^ 2 • (b * u))
    (hud : u * d = q ^ 2 • (d * u))
    (hu'b : u' * b = q ^ 2 • (b * u'))
    (hu'd : u' * d = q⁻¹ ^ 2 • (d * u')) :
    let X := ((q + q⁻¹)⁻¹ • (a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) + q⁻¹ ^ 2 • (b * a ^ 2)))
    let Z := ((q + q⁻¹)⁻¹ • (q ^ 2 • (c ^ 2 * d) - ((q + q⁻¹) * q) • (c * d * c) + d * c ^ 2))
    X * Z - Z * X = 0 := by
  have hac_assoc (z : B) := congrArg (fun t : B ↦ t * z) hac
  have hbd_assoc (z : B) := congrArg (fun t : B ↦ t * z) hbd
  have had_assoc (z : B) := congrArg (fun t : B ↦ t * z) had
  have hbc_assoc (z : B) := congrArg (fun t : B ↦ t * z) hbc
  have hua_assoc (z : B) := congrArg (fun t : B ↦ t * z) hua
  have huc_assoc (z : B) := congrArg (fun t : B ↦ t * z) huc
  have hu'a_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'a
  have hu'c_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'c
  have hub_assoc (z : B) := congrArg (fun t : B ↦ t * z) hub
  have hud_assoc (z : B) := congrArg (fun t : B ↦ t * z) hud
  have hu'b_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'b
  have hu'd_assoc (z : B) := congrArg (fun t : B ↦ t * z) hu'd
  simp only [mul_assoc, add_mul, sub_mul, smul_mul_assoc] at *
  simp only [pow_two, mul_sub, mul_add, mul_smul_comm, smul_add, smul_sub, mul_assoc,
    hac, hbd, had, hbc, hua, huc, hu'a, hu'c, hub, hud, hu'b, hu'd, hac_assoc, hbd_assoc,
    had_assoc, hbc_assoc, hua_assoc, huc_assoc, hu'a_assoc, hu'c_assoc, hub_assoc, hud_assoc,
    hu'b_assoc, hu'd_assoc]
  match_scalars <;> field_simp [hq] <;> ring

end Ring

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j l : I}

/-- Actual coupled off-diagonal mixed relation at outgoing degrees (2,1).
Reconstructed from the defining quotient relations. Only `v ≠ 0` is required;
no reverse-edge, target-edge, finite-rank, or characteristic hypothesis is imposed. -/
theorem braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_two_neg_one
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -2)
    (hil : D.cartanMatrix i l = -1) (hjl : j ≠ l) :
    braidEj R v i j * braidFj R v i l - braidFj R v i l * braidEj R v i j = 0 := by
  have hij' : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at hij
    norm_num at hij
  have hil' : i ≠ l := by
    rintro rfl
    rw [D.cartanMatrix_self] at hil
    norm_num at hil
  have he : v ^ ((D.d i : ℤ) * 2) = (v ^ D.d i) ^ 2 := by
    rw [zpow_mul, zpow_natCast, zpow_ofNat]
  rw [braidEj_eq_of_cartanMatrix_eq_neg_two hij,
    braidFj_eq_of_cartanMatrix_eq_neg_one hv hil]
  exact higher_mixed_2_1
    (E R v i) (E R v j) (F R v i) (F R v l)
    (Kt R v i) (K R v (-ktilde R i)) (v ^ D.d i) (pow_ne_zero _ hv)
    (by simpa only [↓reduceIte] using
      (sub_eq_iff_eq_add'.mp (E_mul_F_sub R v i i)))
    (E_mul_F_of_ne hjl) (E_mul_F_of_ne hil') (E_mul_F_of_ne hij'.symm)
    (by rw [Kt, K_mul_E, root_ktilde, D.cartanMatrix_self, he])
    (by rw [Kt, K_mul_F, root_ktilde, D.cartanMatrix_self, zpow_neg, he, inv_pow])
    (by rw [K_mul_E, map_neg, root_ktilde, D.cartanMatrix_self, zpow_neg, he, inv_pow])
    (by rw [K_mul_F, map_neg, neg_neg, root_ktilde, D.cartanMatrix_self, he])
    (by rw [Kt, K_mul_E, root_ktilde, hij, mul_neg, zpow_neg, he, inv_pow])
    (by rw [Kt, K_mul_F, root_ktilde, hil, mul_neg_one, neg_neg, zpow_natCast])
    (by rw [K_mul_E, map_neg, root_ktilde, hij, mul_neg, neg_neg, he])
    (by rw [K_mul_F, map_neg, neg_neg, root_ktilde, hil, mul_neg_one, zpow_neg, zpow_natCast])

/-- Actual coupled off-diagonal mixed relation at outgoing degrees (1,2).
Reconstructed from the defining quotient relations. Only `v ≠ 0` is required;
no reverse-edge, target-edge, finite-rank, or characteristic hypothesis is imposed. -/
theorem braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_one_neg_two
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -1)
    (hil : D.cartanMatrix i l = -2) (hjl : j ≠ l) :
    braidEj R v i j * braidFj R v i l - braidFj R v i l * braidEj R v i j = 0 := by
  have hij' : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at hij
    norm_num at hij
  have hil' : i ≠ l := by
    rintro rfl
    rw [D.cartanMatrix_self] at hil
    norm_num at hil
  have he : v ^ ((D.d i : ℤ) * 2) = (v ^ D.d i) ^ 2 := by
    rw [zpow_mul, zpow_natCast, zpow_ofNat]
  rw [braidEj_eq_of_cartanMatrix_eq_neg_one hij,
    braidFj_eq_of_cartanMatrix_eq_neg_two hv hil]
  exact higher_mixed_1_2
    (E R v i) (E R v j) (F R v i) (F R v l)
    (Kt R v i) (K R v (-ktilde R i)) (v ^ D.d i) (pow_ne_zero _ hv)
    (by simpa only [↓reduceIte] using
      (sub_eq_iff_eq_add'.mp (E_mul_F_sub R v i i)))
    (E_mul_F_of_ne hjl) (E_mul_F_of_ne hil') (E_mul_F_of_ne hij'.symm)
    (by rw [Kt, K_mul_E, root_ktilde, D.cartanMatrix_self, he])
    (by rw [Kt, K_mul_F, root_ktilde, D.cartanMatrix_self, zpow_neg, he, inv_pow])
    (by rw [K_mul_E, map_neg, root_ktilde, D.cartanMatrix_self, zpow_neg, he, inv_pow])
    (by rw [K_mul_F, map_neg, neg_neg, root_ktilde, D.cartanMatrix_self, he])
    (by rw [Kt, K_mul_E, root_ktilde, hij, mul_neg_one, zpow_neg, zpow_natCast])
    (by rw [Kt, K_mul_F, root_ktilde, hil, mul_neg, neg_neg, he])
    (by rw [K_mul_E, map_neg, root_ktilde, hij, mul_neg_one, neg_neg, zpow_natCast])
    (by rw [K_mul_F, map_neg, neg_neg, root_ktilde, hil, mul_neg, zpow_neg, he, inv_pow])

/-- Actual coupled off-diagonal mixed relation at outgoing degrees (2,2).
Reconstructed from the defining quotient relations. Only `v ≠ 0` is required;
no reverse-edge, target-edge, finite-rank, or characteristic hypothesis is imposed. -/
theorem braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_two_neg_two
    (hv : v ≠ 0) (hij : D.cartanMatrix i j = -2)
    (hil : D.cartanMatrix i l = -2) (hjl : j ≠ l) :
    braidEj R v i j * braidFj R v i l - braidFj R v i l * braidEj R v i j = 0 := by
  have hij' : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at hij
    norm_num at hij
  have hil' : i ≠ l := by
    rintro rfl
    rw [D.cartanMatrix_self] at hil
    norm_num at hil
  have he : v ^ ((D.d i : ℤ) * 2) = (v ^ D.d i) ^ 2 := by
    rw [zpow_mul, zpow_natCast, zpow_ofNat]
  rw [braidEj_eq_of_cartanMatrix_eq_neg_two hij,
    braidFj_eq_of_cartanMatrix_eq_neg_two hv hil]
  exact higher_mixed_2_2
    (E R v i) (E R v j) (F R v i) (F R v l)
    (Kt R v i) (K R v (-ktilde R i)) (v ^ D.d i) (pow_ne_zero _ hv)
    (by simpa only [↓reduceIte] using
      (sub_eq_iff_eq_add'.mp (E_mul_F_sub R v i i)))
    (E_mul_F_of_ne hjl) (E_mul_F_of_ne hil') (E_mul_F_of_ne hij'.symm)
    (by rw [Kt, K_mul_E, root_ktilde, D.cartanMatrix_self, he])
    (by rw [Kt, K_mul_F, root_ktilde, D.cartanMatrix_self, zpow_neg, he, inv_pow])
    (by rw [K_mul_E, map_neg, root_ktilde, D.cartanMatrix_self, zpow_neg, he, inv_pow])
    (by rw [K_mul_F, map_neg, neg_neg, root_ktilde, D.cartanMatrix_self, he])
    (by rw [Kt, K_mul_E, root_ktilde, hij, mul_neg, zpow_neg, he, inv_pow])
    (by rw [Kt, K_mul_F, root_ktilde, hil, mul_neg, neg_neg, he])
    (by rw [K_mul_E, map_neg, root_ktilde, hij, mul_neg, neg_neg, he])
    (by rw [K_mul_F, map_neg, neg_neg, root_ktilde, hil, mul_neg, zpow_neg, he, inv_pow])

end QuantumGroup
