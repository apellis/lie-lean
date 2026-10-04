/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.HigherSerreReverse
import LieLean.Algebra.QuantumGroup.BraidAction.A2

/-!
# Explicit degree-two braid recovery

## Main results
* `doubleEdge_recover_Ej` and `doubleEdge_recover_Fj`: neighboring-generator recovery
  from the actual `T''` images at a directed entry `-2`, in arbitrary ambient rank.
* `doubleEdgeBraidEquiv`: the quotient automorphism at the `-2` centre of an exact
  two-node diagram with directed entries `(-2,-1)`, with explicit two-sided inverse.

The toral lattice and field remain arbitrary. Both quantum sum and difference at
the chosen centre must be nonzero. The other node parameter is not identified with
the centre parameter; the existing reverse Serre theorem derives its square relation.
This is the first higher-edge quotient lift, not a length-four braid relation or an
action with both node automorphisms. The simple-side automorphism (outgoing `-1`,
reverse `-2`) still needs its neighbor-first cubic transformed Serre relation.

## References
Reconstructed directly from the quotient presentation.
-/

open LieLean

noncomputable section
namespace LieLean.QuantumGroup
variable {k : Type*} [Field k]

section Ring
variable {B : Type*} [Ring B] [Algebra k B]

set_option maxHeartbeats 4000000 in
-- Normal ordering the twice-lowered candidate produces many scalar coefficients.
private lemma double_recover (a b c u u' : B) (q : k) (hq : q ≠ 0)
    (hd : q - q⁻¹ ≠ 0) (hs : q + q⁻¹ ≠ 0)
    (hca : c * a = a * c - (q - q⁻¹)⁻¹ • (u - u'))
    (hcb : c * b = b * c)
    (hua : u * a = q ^ 2 • (a * u))
    (hub : u * b = q⁻¹ ^ 2 • (b * u))
    (huc : u * c = q⁻¹ ^ 2 • (c * u))
    (hu'a : u' * a = q⁻¹ ^ 2 • (a * u'))
    (hu'b : u' * b = q ^ 2 • (b * u'))
    (hu'c : u' * c = q ^ 2 • (c * u'))
    (hu'u : u' * u = 1) (huu' : u * u' = 1) :
    let X := (q + q⁻¹)⁻¹ •
      (a ^ 2 * b - ((q + q⁻¹) * q⁻¹) • (a * b * a) + q⁻¹ ^ 2 • (b * a ^ 2))
    let A := -(c * u)
    (q + q⁻¹)⁻¹ •
      (X * A ^ 2 - ((q + q⁻¹) * q⁻¹) • (A * X * A) + q⁻¹ ^ 2 • (A ^ 2 * X)) = b := by
  have hca_assoc (z : B) := congrArg (fun x : B ↦ x * z) hca
  have hcb_assoc (z : B) := congrArg (fun x : B ↦ x * z) hcb
  have hua_assoc (z : B) := congrArg (fun x : B ↦ x * z) hua
  have hub_assoc (z : B) := congrArg (fun x : B ↦ x * z) hub
  have huc_assoc (z : B) := congrArg (fun x : B ↦ x * z) huc
  have hu'a_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'a
  have hu'b_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'b
  have hu'c_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'c
  have hu'u_assoc (z : B) := congrArg (fun x : B ↦ x * z) hu'u
  have huu'_assoc (z : B) := congrArg (fun x : B ↦ x * z) huu'
  simp only [mul_assoc, sub_mul, smul_mul_assoc, one_mul] at *
  simp only [pow_two, mul_sub, sub_mul, mul_add, add_mul, mul_neg, neg_mul,
    neg_neg, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_neg, mul_assoc,
    hua, hub, hu'u, hca_assoc, hcb_assoc, hua_assoc, hub_assoc, huc_assoc, hu'a_assoc,
    hu'b_assoc, hu'c_assoc, hu'u_assoc, mul_one]
  have hn : 1 - q ^ 4 * 2 + q ^ 8 ≠ 0 := by
    have he : 1 - q ^ 4 * 2 + q ^ 8 = (q * (q - q⁻¹) * (q * (q + q⁻¹))) ^ 2 := by
      field_simp
      ring
    rw [he]
    exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero hq hd) (mul_ne_zero hq hs))
  match_scalars <;> field_simp [hq, hd, hs, hn] <;> ring_nf
  field_simp [hn]
  ring

end Ring

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} {i j : I}

/-- Explicit inverse polynomial in the actual positive `T''` images recovers `E_j`.
Reconstructed from the quotient commutator and toral relations. The reverse Cartan
entry, ambient rank, characteristic and toral lattice are unrestricted. -/
theorem doubleEdge_recover_Ej (hv : v ≠ 0) (h : D.cartanMatrix i j = -2)
    (hd : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0) :
    (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ •
      (braidEj R v i j * braidEi R i ^ 2 -
        ((v ^ D.d i + (v ^ D.d i)⁻¹) * (v ^ D.d i)⁻¹) •
          (braidEi R i * braidEj R v i j * braidEi R i) +
        (v ^ D.d i)⁻¹ ^ 2 • (braidEi R i ^ 2 * braidEj R v i j)) = E R v j := by
  have hij : i ≠ j := by
    rintro rfl
    rw [D.cartanMatrix_self] at h
    norm_num at h
  have hca : F R v i * E R v i = E R v i * F R v i -
      (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (Kt R v i - K R v (-ktilde R i)) := by
    have hc := E_mul_F_sub R v i i
    simp only [ite_true] at hc
    linear_combination (norm := module) -hc
  have hub : Kt R v i * E R v j =
      (v ^ D.d i)⁻¹ ^ 2 • (E R v j * Kt R v i) := by
    rw [Kt, K_mul_E, root_ktilde, h, mul_neg, zpow_neg, zpow_mul,
      zpow_natCast, zpow_ofNat, inv_pow]
  have hu'b : K R v (-ktilde R i) * E R v j =
      (v ^ D.d i) ^ 2 • (E R v j * K R v (-ktilde R i)) := by
    rw [K_mul_E, map_neg, root_ktilde, h, mul_neg, neg_neg, zpow_mul,
      zpow_natCast, zpow_ofNat]
  rw [braidEj_eq_of_cartanMatrix_eq_neg_two h]
  exact double_recover (E R v i) (E R v j) (F R v i)
    (Kt R v i) (K R v (-ktilde R i)) (v ^ D.d i) (pow_ne_zero _ hv) hd hs hca
    (E_mul_F_of_ne hij.symm).symm (Kt_mul_E i) hub (Kt_mul_F i)
    (by simpa only [inv_pow] using K_neg_ktilde_mul_E (R := R) (v := v) i)
    hu'b (K_neg_ktilde_mul_F i) (K_neg_mul_Kt i) (Kt_mul_K_neg i)

/-- Explicit inverse polynomial in the actual negative `T''` images recovers `F_j`.
Reconstructed via the genuine Chevalley involution, without any assumed inverse. -/
theorem doubleEdge_recover_Fj (hv : v ≠ 0) (h : D.cartanMatrix i j = -2)
    (hd : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
    (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0) :
    (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ •
      ((v ^ D.d i) ^ 2 • (braidFj R v i j * braidFi R i ^ 2) -
        ((v ^ D.d i + (v ^ D.d i)⁻¹) * v ^ D.d i) •
          (braidFi R i * braidFj R v i j * braidFi R i) +
        braidFi R i ^ 2 * braidFj R v i j) = F R v j := by
  have hc := congrArg (chevalley R v) (doubleEdge_recover_Ej (R := R) hv h hd hs)
  simp only [map_smul, map_add, map_sub, map_mul, map_pow,
    chevalley_braidEj_of_cartanMatrix_eq_neg_two hv h,
    chevalley_braidEi hv, chevalley_E, smul_pow, smul_mul_assoc,
    mul_smul_comm, smul_add, smul_sub, smul_smul] at hc
  calc
    _ = _ := ?_
    _ = F R v j := hc
  match_scalars <;> field_simp [pow_ne_zero (D.d i) hv]

variable [NeZero v]
  (i j : I) (hij : i ≠ j) (hall : ∀ l, l = i ∨ l = j)
  (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)

include hij hall h h' hq hs in
/-- All defining relations for the actual double-edge braid images, not an assumption.
Reconstructed by exhaustive two-node cases from the published relation theorems. -/
theorem doubleEdgeBraid_relations :
    Relations R v (fun l ↦ if l = i then braidEi R i else braidEj R v i l)
      (fun l ↦ if l = i then braidFi R i else braidFj R v i l) (braidK R v i) where
  K_mul_E μ l := by
    rcases hall l with rfl | rfl
    · simpa only [↓reduceIte] using braidK_mul_braidEi (R := R) (v := v) _ μ
    · simpa only [hij.symm, ↓reduceIte] using braidK_mul_braidEj (R := R) (NeZero.ne v) hij μ
  K_mul_F μ l := by
    rcases hall l with rfl | rfl
    · simpa only [↓reduceIte] using braidK_mul_braidFi (R := R) (v := v) _ μ
    · simpa only [hij.symm, ↓reduceIte] using braidK_mul_braidFj (R := R) (NeZero.ne v) hij μ
  E_mul_F l m := by
    rcases hall l with rfl | rfl <;> rcases hall m with rfl | rfl
    · simpa only [↓reduceIte] using braidEi_mul_braidFi_sub (R := R) (v := v) _
    · simpa only [hij, hij.symm, ↓reduceIte] using braidEi_mul_braidFj_sub (R := R) (v := v) hij
    · simpa only [hij.symm, ↓reduceIte] using braidEj_mul_braidFi_sub (R := R) (v := v) hij
    · simpa only [hij.symm, ↓reduceIte] using
        braidEj_mul_braidFj_sub_of_cartanMatrix_eq_neg_two (R := R) (NeZero.ne v) h hq hs
  serre_E l m hlm := by
    rcases hall l with rfl | rfl <;> rcases hall m with rfl | rfl
    · exact (hlm rfl).elim
    · simpa only [hij.symm, ↓reduceIte] using
        qSerre_braidEi_braidEj_of_cartanMatrix_eq_neg_two (R := R) (NeZero.ne v) h
    · simpa only [hij.symm, ↓reduceIte] using
        qSerre_braidEj_braidEi_of_double_edge (R := R) (NeZero.ne v) h h'
    · exact (hlm rfl).elim
  serre_F l m hlm := by
    rcases hall l with rfl | rfl <;> rcases hall m with rfl | rfl
    · exact (hlm rfl).elim
    · simpa only [hij.symm, ↓reduceIte] using
        qSerre_braidFi_braidFj_of_cartanMatrix_eq_neg_two (R := R) (NeZero.ne v) h
    · simpa only [hij.symm, ↓reduceIte] using
        qSerre_braidFj_braidFi_of_double_edge (R := R) (NeZero.ne v) h h'
    · exact (hlm rfl).elim

/-- The genuine double-edge braid algebra homomorphism on the quotient presentation.
No relation package or faithful action is assumed. Reconstructed proof. -/
def doubleEdgeBraid : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  lift (doubleEdgeBraid_relations i j hij hall h h' hq hs)

@[simp] theorem doubleEdgeBraid_E (l : I) :
    doubleEdgeBraid i j hij hall h h' hq hs (E R v l) =
      if l = i then braidEi R i else braidEj R v i l := lift_E _ l

@[simp] theorem doubleEdgeBraid_F (l : I) :
    doubleEdgeBraid i j hij hall h h' hq hs (F R v l) =
      if l = i then braidFi R i else braidFj R v i l := lift_F _ l

@[simp] theorem doubleEdgeBraid_K (μ : Y) :
    doubleEdgeBraid i j hij hall h h' hq hs (K R v μ) = K R v (reflY R i μ) := lift_K _ μ


/-- Explicit inverse candidate obtained by conjugating the proved braid homomorphism
by the proved product-reversal anti-homomorphism. No extra relations are assumed. -/
def doubleEdgeBraidInv : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  (AlgHom.opComm braidReversalOp).comp
    ((doubleEdgeBraid i j hij hall h h' hq hs).op.comp braidReversalOp)

/-- The inverse candidate is reversal-conjugation on every element. -/
theorem doubleEdgeBraidInv_apply (x : QuantumGroup R v) :
    doubleEdgeBraidInv i j hij hall h h' hq hs x =
      braidReversal (doubleEdgeBraid i j hij hall h h' hq hs (braidReversal x)) := rfl

@[simp] theorem doubleEdgeBraidInv_Ei :
    doubleEdgeBraidInv i j hij hall h h' hq hs (E R v i) = braidInvEi R i := by
  simp [doubleEdgeBraidInv_apply, braidEi, braidInvEi, braidReversal_mul, Kt]

@[simp] theorem doubleEdgeBraidInv_Fi :
    doubleEdgeBraidInv i j hij hall h h' hq hs (F R v i) = braidInvFi R i := by
  simp [doubleEdgeBraidInv_apply, braidFi, braidInvFi, braidReversal_mul, Kt]

@[simp] theorem doubleEdgeBraidInv_Ej :
    doubleEdgeBraidInv i j hij hall h h' hq hs (E R v j) =
      (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ •
        (E R v j * E R v i ^ 2 -
          ((v ^ D.d i + (v ^ D.d i)⁻¹) * (v ^ D.d i)⁻¹) •
            (E R v i * E R v j * E R v i) +
          (v ^ D.d i)⁻¹ ^ 2 • (E R v i ^ 2 * E R v j)) := by
  simp [doubleEdgeBraidInv_apply, hij.symm, braidEj_eq_of_cartanMatrix_eq_neg_two h,
    pow_two, braidReversal_mul, mul_assoc]

@[simp] theorem doubleEdgeBraidInv_Fj :
    doubleEdgeBraidInv i j hij hall h h' hq hs (F R v j) =
      (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ •
        ((v ^ D.d i) ^ 2 • (F R v j * F R v i ^ 2) -
          ((v ^ D.d i + (v ^ D.d i)⁻¹) * v ^ D.d i) •
            (F R v i * F R v j * F R v i) + F R v i ^ 2 * F R v j) := by
  simp [doubleEdgeBraidInv_apply, hij.symm,
    braidFj_eq_of_cartanMatrix_eq_neg_two (NeZero.ne v) h,
    pow_two, braidReversal_mul, mul_assoc]

@[simp] theorem doubleEdgeBraidInv_K (μ : Y) :
    doubleEdgeBraidInv i j hij hall h h' hq hs (K R v μ) = K R v (reflY R i μ) := by
  simp [doubleEdgeBraidInv_apply]


/-- The candidate is a right inverse, checked on both Chevalley colors and all toral
lattice generators, not inferred from a surjectivity assertion. -/
theorem doubleEdgeBraid_comp_doubleEdgeBraidInv :
    (doubleEdgeBraid (R := R) i j hij hall h h' hq hs).comp
      (doubleEdgeBraidInv i j hij hall h h' hq hs) = AlgHom.id k (QuantumGroup R v) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · rcases hall l with hl | hl
    · subst l
      simp only [AlgHom.comp_apply, doubleEdgeBraidInv_Ei, braidInvEi, map_neg, map_mul,
        doubleEdgeBraid_F, ↓reduceIte, braidFi, doubleEdgeBraid_K, reflY_ktilde,
        mul_neg, neg_neg, AlgHom.id_apply, ← mul_assoc, K_mul_K_neg, one_mul]
    · subst l
      simpa only [AlgHom.comp_apply, doubleEdgeBraidInv_Ej, map_add, map_sub, map_mul,
        map_pow, map_smul, doubleEdgeBraid_E, hij.symm, ↓reduceIte, AlgHom.id_apply] using
        doubleEdge_recover_Ej (NeZero.ne v) h hq hs
  · rcases hall l with hl | hl
    · subst l
      simp only [AlgHom.comp_apply, doubleEdgeBraidInv_Fi, braidInvFi, map_neg, map_mul,
        doubleEdgeBraid_E, ↓reduceIte, braidEi, Kt, doubleEdgeBraid_K, reflY_ktilde,
        neg_mul, neg_neg, AlgHom.id_apply, mul_assoc, K_mul_K_neg, mul_one]
    · subst l
      simpa only [AlgHom.comp_apply, doubleEdgeBraidInv_Fj, map_add, map_sub, map_mul,
        map_pow, map_smul, doubleEdgeBraid_F, hij.symm, ↓reduceIte, AlgHom.id_apply] using
        doubleEdge_recover_Fj (NeZero.ne v) h hq hs
  · simp

/-- The candidate is also a left inverse. Conjugating the proved generator-level
right-inverse identity by the involutive product reversal gives this identity. -/
theorem doubleEdgeBraidInv_comp_doubleEdgeBraid :
    (doubleEdgeBraidInv (R := R) i j hij hall h h' hq hs).comp
      (doubleEdgeBraid i j hij hall h h' hq hs) = AlgHom.id k (QuantumGroup R v) := by
  apply DFunLike.ext
  intro x
  have hc := congrArg braidReversal
    (DFunLike.congr_fun (doubleEdgeBraid_comp_doubleEdgeBraidInv (R := R) i j hij hall h h' hq hs)
      (braidReversal x))
  simpa only [AlgHom.comp_apply, doubleEdgeBraidInv_apply, braidReversal_involutive x,
    AlgHom.id_apply] using hc

/-- Lusztig's actual double-edge braid algebra equivalence, with explicit two-sided inverse.
Assumptions: exactly two distinct nodes, Cartan entries `(-2,-1)`, arbitrary root datum
lattice and field, `v ≠ 0`, `vᵢ - vᵢ⁻¹ ≠ 0` and `vᵢ + vᵢ⁻¹ ≠ 0`.
Reconstructed from the presentation; this constructs only the `-2` centre automorphism. -/
def doubleEdgeBraidEquiv : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  AlgEquiv.ofAlgHom (doubleEdgeBraid i j hij hall h h' hq hs)
    (doubleEdgeBraidInv i j hij hall h h' hq hs)
    (doubleEdgeBraid_comp_doubleEdgeBraidInv i j hij hall h h' hq hs)
    (doubleEdgeBraidInv_comp_doubleEdgeBraid i j hij hall h h' hq hs)

end LieLean.QuantumGroup
