/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.GeneralRelations
import LieLean.Algebra.QuantumGroup.BraidAction.HigherDoubleRelation

/-!
# The length-four braid relation at a double edge, in arbitrary rank

Let `i, j` be two nodes of an arbitrary Cartan datum with `aᵢⱼ = -2`, `aⱼᵢ = -1` (so `vⱼ = vᵢ²`),
and let `Tᵢ = braidEquiv hgᵢ hSᵢ`, `Tⱼ = braidEquiv hgⱼ hSⱼ` be the general braid automorphisms of
`BraidAction/General.lean` (for instance `braidEquivOfGeneric`). We prove
`Tᵢ Tⱼ Tᵢ Tⱼ = Tⱼ Tᵢ Tⱼ Tᵢ` on the whole algebra when every other node `l` satisfies
`(aᵢₗ, aⱼₗ) ∈ {(0, 0), (-1, 0), (0, -1)}`, with no other restriction on the rank or graph.

## Main results

* `QuantumGroup.braidHom_double_transport_Ei` (and `Fi`, `Ej`, `Fj`): `Tᵢ Tⱼ (Eᵢ) = Tⱼ⁻¹ (Eᵢ)`
  and its analogues, where `Tⱼ⁻¹ = braidInvHom` is the reversal conjugate of `Tⱼ`.
* `QuantumGroup.braidHom_double_triple_Ei` (and `Fi`, `Ej`, `Fj`): `Tⱼ Tᵢ Tⱼ (Eᵢ) = Eᵢ`, etc.
* `QuantumGroup.braidHom_double_four_E_short`, `..._E_long` (and `F`): the relation on an outer
  generator attached to one end by a simple bond.
* `QuantumGroup.braidEquiv_braid_four`: the length-four relation for `braidEquiv`.

## Method

This is the argument of `BraidAction/DoubleEdgeRelation.lean` and
`BraidAction/HigherDoubleRelation.lean`, which was written for the local constructions; only
the generator formulas of `Tᵢ`, `Tⱼ` and of their reversal-conjugate inverses enter, so it
transfers verbatim to the general automorphisms. The rank-two normal-ordering identities
(`doubleEdge_four_lower_Ei`, ..., `higherDouble_short_polynomial`, ...) are reused.

## References

Reconstructed; see the files cited above. G. Lusztig, *Introduction to quantum groups*,
39.4 (check), for the braid relations.
-/

noncomputable section

namespace QuantumGroup

section Inverse

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v] {i : I}
  (hg : BraidGeneric D v i) (hS : TransformedSerre R v i)

/-- `Tᵢ⁻¹(Eⱼ)` for a simple bond `aᵢⱼ = -1`. -/
theorem braidInvHom_E_of_neg_one (j : I) (hj : j ≠ i) (hij : D.cartanMatrix i j = -1) :
    braidInvHom hg hS (E R v j) = E R v j * E R v i - (v ^ D.d i)⁻¹ • (E R v i * E R v j) := by
  simp [braidInvHom_apply, braidImageE, hj, braidEj_eq_of_cartanMatrix_eq_neg_one hij,
    braidReversal_mul]

/-- `Tᵢ⁻¹(Fⱼ)` for a simple bond `aᵢⱼ = -1`. -/
theorem braidInvHom_F_of_neg_one (j : I) (hj : j ≠ i) (hij : D.cartanMatrix i j = -1) :
    braidInvHom hg hS (F R v j) = F R v i * F R v j - (v ^ D.d i) • (F R v j * F R v i) := by
  simp [braidInvHom_apply, braidImageF, hj,
    braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hij, braidReversal_mul]

/-- `Tᵢ⁻¹(Eⱼ)` for a double bond `aᵢⱼ = -2`. -/
theorem braidInvHom_E_of_neg_two (j : I) (hj : j ≠ i) (hij : D.cartanMatrix i j = -2) :
    braidInvHom hg hS (E R v j) =
      (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ •
        (E R v j * E R v i ^ 2 -
          ((v ^ D.d i + (v ^ D.d i)⁻¹) * (v ^ D.d i)⁻¹) • (E R v i * E R v j * E R v i) +
          (v ^ D.d i)⁻¹ ^ 2 • (E R v i ^ 2 * E R v j)) := by
  simp [braidInvHom_apply, braidImageE, hj, braidEj_eq_of_cartanMatrix_eq_neg_two hij,
    pow_two, braidReversal_mul, mul_assoc]

/-- `Tᵢ⁻¹(Fⱼ)` for a double bond `aᵢⱼ = -2`. -/
theorem braidInvHom_F_of_neg_two (j : I) (hj : j ≠ i) (hij : D.cartanMatrix i j = -2) :
    braidInvHom hg hS (F R v j) =
      (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ •
        ((v ^ D.d i) ^ 2 • (F R v j * F R v i ^ 2) -
          ((v ^ D.d i + (v ^ D.d i)⁻¹) * v ^ D.d i) • (F R v i * F R v j * F R v i) +
          F R v i ^ 2 * F R v j) := by
  simp [braidInvHom_apply, braidImageF, hj,
    braidFj_eq_of_cartanMatrix_eq_neg_two (NeZero.ne v) hij, pow_two, braidReversal_mul,
    mul_assoc]

end Inverse

variable {k : Type*} [Field k] {I Y : Type*} [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v] {i j : I}
  (hgi : BraidGeneric D v i) (hSi : TransformedSerre R v i)
  (hgj : BraidGeneric D v j) (hSj : TransformedSerre R v j)
  (hij : i ≠ j) (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1)
  (hsi : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)

local notation "Ti" => braidHom hgi hSi
local notation "Tj" => braidHom hgj hSj
local notation "TiInv" => braidInvHom hgi hSi
local notation "TjInv" => braidInvHom hgj hSj

include hij h h'

include hsi in
/-- Two forward maps equal the other inverse on `Eᵢ`. -/
theorem braidHom_double_transport_Ei : Ti (Tj (E R v i)) = TjInv (E R v i) := by
  rw [braidInvHom_apply]
  simp only [braidReversal_E, braidHom_E, braidImageE, hij, hij.symm, ↓reduceIte,
    braidEj_eq_of_cartanMatrix_eq_neg_one h', map_sub, map_mul, map_smul, braidReversal_mul,
    parameter_eq_square_of_double_edge (v := v) h h', ← inv_pow]
  simpa only [inv_pow] using doubleEdge_four_lower_Ei (R := R) (NeZero.ne v) h hgi.sub_ne hsi

include hsi in
/-- Two forward maps equal the other inverse on `Fᵢ`. -/
theorem braidHom_double_transport_Fi : Ti (Tj (F R v i)) = TjInv (F R v i) := by
  rw [braidInvHom_apply]
  simp only [braidReversal_F, braidHom_F, braidImageF, hij, hij.symm, ↓reduceIte,
    braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h', map_sub, map_mul, map_smul,
    braidReversal_mul, parameter_eq_square_of_double_edge (v := v) h h']
  exact doubleEdge_four_lower_Fi (NeZero.ne v) h hgi.sub_ne hsi

/-- Two forward maps equal the other inverse on `Eⱼ`. -/
theorem braidHom_double_transport_Ej : Tj (Ti (E R v j)) = TiInv (E R v j) := by
  rw [braidInvHom_apply]
  simp only [braidReversal_E, braidHom_E, braidImageE, hij, hij.symm, ↓reduceIte,
    braidEj_eq_of_cartanMatrix_eq_neg_two h, map_add, map_sub, map_mul, map_smul, map_pow,
    braidReversal_mul, braidReversal_pow]
  simpa only [mul_assoc] using
    congrArg (fun z : QuantumGroup R v ↦ (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ • z)
      (doubleEdge_four_lower_Ej (R := R) (NeZero.ne v) h h' hgj.sub_ne)

/-- Two forward maps equal the other inverse on `Fⱼ`. -/
theorem braidHom_double_transport_Fj : Tj (Ti (F R v j)) = TiInv (F R v j) := by
  rw [braidInvHom_apply]
  simp only [braidReversal_F, braidHom_F, braidImageF, hij, hij.symm, ↓reduceIte,
    braidFj_eq_of_cartanMatrix_eq_neg_two (NeZero.ne v) h, map_add, map_sub, map_mul,
    map_smul, map_pow, braidReversal_mul, braidReversal_pow]
  simpa only [mul_assoc] using
    congrArg (fun z : QuantumGroup R v ↦ (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ • z)
      (doubleEdge_four_lower_Fj (R := R) (NeZero.ne v) h h' hgj.sub_ne)

include hsi in
/-- The alternating three-map word fixes `Eᵢ`. -/
theorem braidHom_double_triple_Ei : Tj (Ti (Tj (E R v i))) = E R v i := by
  rw [braidHom_double_transport_Ei hgi hSi hgj hSj hij h h' hsi]
  exact DFunLike.congr_fun (braidHom_comp_braidInvHom hgj hSj) (E R v i)

include hsi in
/-- The alternating three-map word fixes `Fᵢ`. -/
theorem braidHom_double_triple_Fi : Tj (Ti (Tj (F R v i))) = F R v i := by
  rw [braidHom_double_transport_Fi hgi hSi hgj hSj hij h h' hsi]
  exact DFunLike.congr_fun (braidHom_comp_braidInvHom hgj hSj) (F R v i)

/-- The alternating three-map word fixes `Eⱼ`. -/
theorem braidHom_double_triple_Ej : Ti (Tj (Ti (E R v j))) = E R v j := by
  rw [braidHom_double_transport_Ej hgi hSi hgj hSj hij h h']
  exact DFunLike.congr_fun (braidHom_comp_braidInvHom hgi hSi) (E R v j)

/-- The alternating three-map word fixes `Fⱼ`. -/
theorem braidHom_double_triple_Fj : Ti (Tj (Ti (F R v j))) = F R v j := by
  rw [braidHom_double_transport_Fj hgi hSi hgj hSj hij h h']
  exact DFunLike.congr_fun (braidHom_comp_braidInvHom hgi hSi) (F R v j)

include hsi in
/-- The fourfold words agree on `Eᵢ`. -/
theorem braidHom_double_four_Ei : Ti (Tj (Ti (Tj (E R v i)))) = Tj (Ti (Tj (Ti (E R v i)))) := by
  rw [braidHom_double_triple_Ei hgi hSi hgj hSj hij h h' hsi]
  simp only [braidHom_E, braidImageE, ↓reduceIte, braidEi, map_neg, map_mul, Kt, braidHom_K,
    braidHom_double_triple_Fi hgi hSi hgj hSj hij h h' hsi,
    reflY_triple_ktilde_of_double_edge_left i j h h']

include hsi in
/-- The fourfold words agree on `Fᵢ`. -/
theorem braidHom_double_four_Fi : Ti (Tj (Ti (Tj (F R v i)))) = Tj (Ti (Tj (Ti (F R v i)))) := by
  rw [braidHom_double_triple_Fi hgi hSi hgj hSj hij h h' hsi]
  simp only [braidHom_F, braidImageF, ↓reduceIte, braidFi, map_neg, map_mul, braidHom_K,
    braidHom_double_triple_Ei hgi hSi hgj hSj hij h h' hsi,
    reflY_triple_ktilde_of_double_edge_left i j h h']

/-- The fourfold words agree on `Eⱼ`. -/
theorem braidHom_double_four_Ej : Ti (Tj (Ti (Tj (E R v j)))) = Tj (Ti (Tj (Ti (E R v j)))) := by
  rw [braidHom_double_triple_Ej hgi hSi hgj hSj hij h h']
  simp only [braidHom_E, braidImageE, ↓reduceIte, braidEi, map_neg, map_mul, Kt, braidHom_K,
    braidHom_double_triple_Fj hgi hSi hgj hSj hij h h',
    reflY_triple_ktilde_of_double_edge_right i j h h']

/-- The fourfold words agree on `Fⱼ`. -/
theorem braidHom_double_four_Fj : Ti (Tj (Ti (Tj (F R v j)))) = Tj (Ti (Tj (Ti (F R v j)))) := by
  rw [braidHom_double_triple_Fj hgi hSi hgj hSj hij h h']
  simp only [braidHom_F, braidImageF, ↓reduceIte, braidFi, map_neg, map_mul, braidHom_K,
    braidHom_double_triple_Ej hgi hSi hgj hSj hij h h',
    reflY_triple_ktilde_of_double_edge_right i j h h']

include hsi in
/-- Length four on an outer `Eₗ` joined to the short node `i` by a simple bond (`aᵢₗ = -1`)
and orthogonal to `j`. -/
theorem braidHom_double_four_E_short (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hil : D.cartanMatrix i l = -1) (hjl : D.cartanMatrix j l = 0) :
    Ti (Tj (Ti (Tj (E R v l)))) = Tj (Ti (Tj (Ti (E R v l)))) := by
  have hiEl : Ti (E R v l) =
      E R v i * E R v l - (v ^ D.d i)⁻¹ • (E R v l * E R v i) := by
    simp [braidImageE, hli, braidEj_eq_of_cartanMatrix_eq_neg_one hil]
  have hjEl : Tj (E R v l) = E R v l := by
    simp [braidImageE, hlj, braidEj_eq_of_cartanMatrix_eq_zero hjl]
  have ht : Ti (Tj (Ti (E R v l))) =
      Ti (Tj (E R v i)) * Ti (E R v l) -
        (v ^ D.d i)⁻¹ • (Ti (E R v l) * Ti (Tj (E R v i))) := by
    rw [hiEl]
    simp only [map_sub, map_mul, map_smul, hjEl, hiEl]
  rw [hjEl, ht, map_sub, map_mul, map_smul, map_mul,
    braidHom_double_triple_Ei hgi hSi hgj hSj hij h h' hsi]
  rw [braidHom_double_transport_Ei hgi hSi hgj hSj hij h h' hsi,
    braidInvHom_E_of_neg_one hgj hSj i hij h', hiEl]
  simp only [map_sub, map_mul, map_smul, hjEl, braidHom_E, braidImageE,
    hij, ↓reduceIte, braidEj_eq_of_cartanMatrix_eq_neg_one h',
    parameter_eq_square_of_double_edge (v := v) h h']
  have hS : qSerre (v ^ D.d i) 2 (E R v i) (E R v l) = 0 := by
    simpa only [hil, Int.reduceSub, Int.reduceToNat] using serre_E R v hli.symm
  simpa only [inv_pow] using higherDouble_short_polynomial
    (E R v i) (E R v j) (E R v l) (v ^ D.d i) (pow_ne_zero _ (NeZero.ne v))
    hS (E_commute_E_of_cartanMatrix_eq_zero hjl)

include hsi in
/-- Length four on an outer `Fₗ` joined to the short node `i` by a simple bond. -/
theorem braidHom_double_four_F_short (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hil : D.cartanMatrix i l = -1) (hjl : D.cartanMatrix j l = 0) :
    Ti (Tj (Ti (Tj (F R v l)))) = Tj (Ti (Tj (Ti (F R v l)))) := by
  have hiFl : Ti (F R v l) =
      F R v l * F R v i - (v ^ D.d i) • (F R v i * F R v l) := by
    simp [braidImageF, hli, braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hil]
  have hjFl : Tj (F R v l) = F R v l := by
    simp [braidImageF, hlj, braidFj_eq_of_cartanMatrix_eq_zero hjl]
  have ht : Ti (Tj (Ti (F R v l))) =
      Ti (F R v l) * Ti (Tj (F R v i)) -
        (v ^ D.d i) • (Ti (Tj (F R v i)) * Ti (F R v l)) := by
    rw [hiFl]
    simp only [map_sub, map_mul, map_smul, hjFl, hiFl]
  rw [hjFl, ht, map_sub, map_mul, map_smul, map_mul,
    braidHom_double_triple_Fi hgi hSi hgj hSj hij h h' hsi]
  rw [braidHom_double_transport_Fi hgi hSi hgj hSj hij h h' hsi,
    braidInvHom_F_of_neg_one hgj hSj i hij h', hiFl]
  simp only [map_sub, map_mul, map_smul, hjFl, braidHom_F, braidImageF,
    hij, ↓reduceIte, braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h',
    parameter_eq_square_of_double_edge (v := v) h h']
  have hS : qSerre (v ^ D.d i) 2 (F R v i) (F R v l) = 0 := by
    simpa only [hil, Int.reduceSub, Int.reduceToNat] using serre_F R v hli.symm
  exact higherDouble_short_polynomial_right
    (F R v i) (F R v j) (F R v l) (v ^ D.d i) (pow_ne_zero _ (NeZero.ne v))
    hS (F_commute_F_of_cartanMatrix_eq_zero hjl)

/-- Length four on an outer `Eₗ` joined to the long node `j` by a simple bond (`aⱼₗ = -1`)
and orthogonal to `i`; here `vⱼ + vⱼ⁻¹ ≠ 0` is assumed. -/
theorem braidHom_double_four_E_long (hsj : v ^ D.d j + (v ^ D.d j)⁻¹ ≠ 0)
    (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hil : D.cartanMatrix i l = 0) (hjl : D.cartanMatrix j l = -1) :
    Ti (Tj (Ti (Tj (E R v l)))) = Tj (Ti (Tj (Ti (E R v l)))) := by
  have hiEl : Ti (E R v l) = E R v l := by
    simp [braidImageE, hli, braidEj_eq_of_cartanMatrix_eq_zero hil]
  have hjEl : Tj (E R v l) =
      E R v j * E R v l - (v ^ D.d j)⁻¹ • (E R v l * E R v j) := by
    simp [braidImageE, hlj, braidEj_eq_of_cartanMatrix_eq_neg_one hjl]
  have ht : Tj (Ti (Tj (E R v l))) =
      Tj (Ti (E R v j)) * Tj (E R v l) -
        (v ^ D.d j)⁻¹ • (Tj (E R v l) * Tj (Ti (E R v j))) := by
    rw [hjEl]
    simp only [map_sub, map_mul, map_smul, hiEl, hjEl]
  rw [hiEl, ht, map_sub, map_mul, map_smul, map_mul,
    braidHom_double_triple_Ej hgi hSi hgj hSj hij h h']
  symm
  rw [braidHom_double_transport_Ej hgi hSi hgj hSj hij h h',
    braidInvHom_E_of_neg_two hgi hSi j hij.symm h, hjEl]
  simp only [map_sub, map_mul, map_smul, hiEl, braidHom_E, braidImageE,
    hij.symm, ↓reduceIte, braidEj_eq_of_cartanMatrix_eq_neg_two h,
    parameter_eq_square_of_double_edge (v := v) h h']
  have hp := parameter_eq_square_of_double_edge (v := v) h h'
  have hS : qSerre ((v ^ D.d i) ^ 2) 2 (E R v j) (E R v i) = 0 := by
    simpa only [h', hp, Int.reduceSub, Int.reduceToNat] using serre_E R v hij.symm
  have hU : qSerre ((v ^ D.d i) ^ 2) 2 (E R v j) (E R v l) = 0 := by
    simpa only [hjl, hp, Int.reduceSub, Int.reduceToNat] using serre_E R v hlj.symm
  have hs : (v ^ D.d i) ^ 2 + ((v ^ D.d i) ^ 2)⁻¹ ≠ 0 := by
    simpa only [hp] using hsj
  have hP := congrArg (fun z : QuantumGroup R v ↦ (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ • z)
    (higherDouble_long_polynomial (E R v i) (E R v j) (E R v l) (v ^ D.d i)
      (pow_ne_zero _ (NeZero.ne v)) hS hU (E_commute_E_of_cartanMatrix_eq_zero hil) hs)
  simp only [smul_sub, smul_add, smul_smul, smul_mul_assoc, mul_smul_comm, inv_pow,
    mul_sub, sub_mul, mul_add, add_mul] at hP ⊢
  linear_combination (norm := (match_scalars <;> ring)) hP

/-- Length four on an outer `Fₗ` joined to the long node `j` by a simple bond. -/
theorem braidHom_double_four_F_long (hsj : v ^ D.d j + (v ^ D.d j)⁻¹ ≠ 0)
    (l : I) (hli : l ≠ i) (hlj : l ≠ j)
    (hil : D.cartanMatrix i l = 0) (hjl : D.cartanMatrix j l = -1) :
    Ti (Tj (Ti (Tj (F R v l)))) = Tj (Ti (Tj (Ti (F R v l)))) := by
  have hiFl : Ti (F R v l) = F R v l := by
    simp [braidImageF, hli, braidFj_eq_of_cartanMatrix_eq_zero hil]
  have hjFl : Tj (F R v l) =
      F R v l * F R v j - (v ^ D.d j) • (F R v j * F R v l) := by
    simp [braidImageF, hlj, braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) hjl]
  have ht : Tj (Ti (Tj (F R v l))) =
      Tj (F R v l) * Tj (Ti (F R v j)) -
        (v ^ D.d j) • (Tj (Ti (F R v j)) * Tj (F R v l)) := by
    rw [hjFl]
    simp only [map_sub, map_mul, map_smul, hiFl, hjFl]
  rw [hiFl, ht, map_sub, map_mul, map_smul, map_mul,
    braidHom_double_triple_Fj hgi hSi hgj hSj hij h h']
  symm
  rw [braidHom_double_transport_Fj hgi hSi hgj hSj hij h h',
    braidInvHom_F_of_neg_two hgi hSi j hij.symm h, hjFl]
  simp only [map_sub, map_mul, map_smul, hiFl, braidHom_F, braidImageF,
    hij.symm, ↓reduceIte, braidFj_eq_of_cartanMatrix_eq_neg_two (NeZero.ne v) h,
    parameter_eq_square_of_double_edge (v := v) h h']
  have hp := parameter_eq_square_of_double_edge (v := v) h h'
  have hS : qSerre ((v ^ D.d i) ^ 2) 2 (F R v j) (F R v i) = 0 := by
    simpa only [h', hp, Int.reduceSub, Int.reduceToNat] using serre_F R v hij.symm
  have hU : qSerre ((v ^ D.d i) ^ 2) 2 (F R v j) (F R v l) = 0 := by
    simpa only [hjl, hp, Int.reduceSub, Int.reduceToNat] using serre_F R v hlj.symm
  have hs : (v ^ D.d i) ^ 2 + ((v ^ D.d i) ^ 2)⁻¹ ≠ 0 := by
    simpa only [hp] using hsj
  have hP := congrArg (fun z : QuantumGroup R v ↦ (v ^ D.d i + (v ^ D.d i)⁻¹)⁻¹ • z)
    (higherDouble_long_polynomial_right (F R v i) (F R v j) (F R v l) (v ^ D.d i)
      (pow_ne_zero _ (NeZero.ne v)) hS hU (F_commute_F_of_cartanMatrix_eq_zero hil) hs)
  simp only [smul_sub, smul_add, smul_smul, smul_mul_assoc, mul_smul_comm,
    mul_sub, sub_mul, mul_add, add_mul] at hP ⊢
  linear_combination (norm := (match_scalars <;> ring)) hP

include hsi in
/-- **Length four at a double edge, in arbitrary rank.** For `aᵢⱼ = -2`, `aⱼᵢ = -1`, the general
braid homomorphisms satisfy `Tᵢ Tⱼ Tᵢ Tⱼ = Tⱼ Tᵢ Tⱼ Tᵢ` provided every other node `l` has
`(aᵢₗ, aⱼₗ) ∈ {(0, 0), (-1, 0), (0, -1)}` and `vᵢ + vᵢ⁻¹`, `vⱼ + vⱼ⁻¹` are nonzero. -/
theorem braidHom_braid_four (hsj : v ^ D.d j + (v ^ D.d j)⁻¹ ≠ 0)
    (hout : ∀ l, l ≠ i → l ≠ j →
      (D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = 0) ∨
      (D.cartanMatrix i l = -1 ∧ D.cartanMatrix j l = 0) ∨
      (D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = -1)) :
    (Ti).comp ((Tj).comp ((Ti).comp Tj)) = (Tj).comp ((Ti).comp ((Tj).comp Ti)) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · by_cases hli : l = i
    · subst l
      exact braidHom_double_four_Ei hgi hSi hgj hSj hij h h' hsi
    · by_cases hlj : l = j
      · subst l
        exact braidHom_double_four_Ej hgi hSi hgj hSj hij h h'
      · rcases hout l hli hlj with ⟨hi0, hj0⟩ | ⟨hi1, hj0⟩ | ⟨hi0, hj1⟩
        · simp [braidImageE, hli, hlj, braidEj_eq_of_cartanMatrix_eq_zero hi0,
            braidEj_eq_of_cartanMatrix_eq_zero hj0]
        · exact braidHom_double_four_E_short hgi hSi hgj hSj hij h h' hsi l hli hlj hi1 hj0
        · exact braidHom_double_four_E_long hgi hSi hgj hSj hij h h' hsj l hli hlj hi0 hj1
  · by_cases hli : l = i
    · subst l
      exact braidHom_double_four_Fi hgi hSi hgj hSj hij h h' hsi
    · by_cases hlj : l = j
      · subst l
        exact braidHom_double_four_Fj hgi hSi hgj hSj hij h h'
      · rcases hout l hli hlj with ⟨hi0, hj0⟩ | ⟨hi1, hj0⟩ | ⟨hi0, hj1⟩
        · simp [braidImageF, hli, hlj, braidFj_eq_of_cartanMatrix_eq_zero hi0,
            braidFj_eq_of_cartanMatrix_eq_zero hj0]
        · exact braidHom_double_four_F_short hgi hSi hgj hSj hij h h' hsi l hli hlj hi1 hj0
        · exact braidHom_double_four_F_long hgi hSi hgj hSj hij h h' hsj l hli hlj hi0 hj1
  · simp only [AlgHom.comp_apply, braidHom_K, reflY_braid_of_double_edge h h']

include hsi in
/-- The length-four relation for the general braid automorphisms `braidEquiv` at a double
edge of any Cartan datum, under the outer-node condition of `braidHom_braid_four`. -/
theorem braidEquiv_braid_four (hsj : v ^ D.d j + (v ^ D.d j)⁻¹ ≠ 0)
    (hout : ∀ l, l ≠ i → l ≠ j →
      (D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = 0) ∨
      (D.cartanMatrix i l = -1 ∧ D.cartanMatrix j l = 0) ∨
      (D.cartanMatrix i l = 0 ∧ D.cartanMatrix j l = -1)) :
    braidEquiv hgi hSi * braidEquiv hgj hSj * braidEquiv hgi hSi * braidEquiv hgj hSj =
      braidEquiv hgj hSj * braidEquiv hgi hSi * braidEquiv hgj hSj * braidEquiv hgi hSi := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (braidHom_braid_four hgi hSi hgj hSj hij h h' hsi hsj hout) x

end QuantumGroup
