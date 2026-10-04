/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.A2

/-!
# The coupled A2 quantum braid relation

## Main results

* `QuantumGroup.a2Braid_braid`: the length-three relation for the actual quotient maps.
* `QuantumGroup.a2BraidEquiv_braid`: the same relation for the published equivalences.

## References

Reconstructed from the quotient presentation and the proved coupled recovery identities.
The field and root datum lattice are arbitrary; the index type has exactly two distinct nodes
with mutual Cartan entries `-1`.
-/

open LieLean

namespace LusztigCartanDatum

variable {I : Type*} {D : LusztigCartanDatum I} {i j : I}

/-- Symmetrizer entries agree across a simply laced edge. Reconstructed from symmetrization. -/
theorem d_eq_of_simply_laced_edge
    (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1) : D.d i = D.d j := by
  have hs := D.d_mul_cartanMatrix_comm i j
  rw [h, h', mul_neg_one, mul_neg_one] at hs
  exact_mod_cast neg_injective hs

/-- The quantum commutator denominator condition transports across a simply laced edge. -/
theorem sub_inv_ne_zero_of_simply_laced_edge {k : Type*} [Field k] {v : k}
    (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) : v ^ D.d j - (v ^ D.d j)⁻¹ ≠ 0 := by
  rwa [← d_eq_of_simply_laced_edge h h']

end LusztigCartanDatum

namespace LieLean.QuantumGroup

section Lattice

variable {I Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {i j : I}

/-- The simple reflections satisfy the length-three braid relation on the entire root datum
lattice. Reconstructed from the reflection formula, with no spanning assumption. -/
theorem reflY_braid_of_simply_laced_edge
    (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1) (μ : Y) :
    reflY R i (reflY R j (reflY R i μ)) =
      reflY R j (reflY R i (reflY R j μ)) := by
  simp only [reflY_apply, map_sub, map_zsmul, R.root_coroot, h, h',
    D.cartanMatrix_self]
  module

/-- The double reflection exchanges the symmetrized simple coroots at a simply laced edge.
Reconstructed using the symmetrizer-aware single-reflection formula. -/
theorem reflY_reflY_ktilde_of_simply_laced_edge
    (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1) :
    reflY R i (reflY R j (ktilde R i)) = ktilde R j := by
  rw [reflY_ktilde_of_cartanMatrix_eq_neg_one h', map_add, reflY_ktilde,
    reflY_ktilde_of_cartanMatrix_eq_neg_one h]
  abel

end Lattice

noncomputable section

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
  (i j : I) (hij : i ≠ j) (hall : ∀ l, l = i ∨ l = j)
  (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hq' : v ^ D.d j - (v ^ D.d j)⁻¹ ≠ 0)

/-- Two successive coupled braid maps transport the first positive generator to the second.
Reconstructed by applying the previously proved positive recovery identity. -/
theorem a2Braid_a2Braid_Ei :
    a2Braid i j hij hall h h' hq
      (a2Braid j i hij.symm (fun l ↦ (hall l).symm) h' h hq' (E R v i)) = E R v j := by
  rw [a2Braid_E, ite_eq_right hij, braidEj_eq_of_cartanMatrix_eq_neg_one h']
  simpa only [map_sub, map_mul, map_smul, a2Braid_E, hij.symm, ↓reduceIte,
    ← D.d_eq_of_simply_laced_edge h h'] using a2Braid_recover_Ej (R := R) i j h hq

/-- Two successive coupled braid maps transport the first negative generator to the second.
Reconstructed from the negative recovery identity, with equal parameters proved. -/
theorem a2Braid_a2Braid_Fi :
    a2Braid i j hij hall h h' hq
      (a2Braid j i hij.symm (fun l ↦ (hall l).symm) h' h hq' (F R v i)) = F R v j := by
  rw [a2Braid_F, ite_eq_right hij, braidFj_eq_of_cartanMatrix_eq_neg_one (NeZero.ne v) h']
  simpa only [map_sub, map_mul, map_smul, a2Braid_F, hij.symm, ↓reduceIte,
    ← D.d_eq_of_simply_laced_edge h h'] using a2Braid_recover_Fj (R := R) i j h hq

/-- The length-three braid words agree on the first positive generator. Reconstructed from
the double-generator transport and the reflection formula on symmetrized coroots. -/
theorem a2Braid_braid_Ei :
    a2Braid i j hij hall h h' hq
        (a2Braid j i hij.symm (fun l ↦ (hall l).symm) h' h hq'
          (a2Braid i j hij hall h h' hq (E R v i))) =
      a2Braid j i hij.symm (fun l ↦ (hall l).symm) h' h hq'
        (a2Braid i j hij hall h h' hq
          (a2Braid j i hij.symm (fun l ↦ (hall l).symm) h' h hq' (E R v i))) := by
  rw [a2Braid_a2Braid_Ei i j hij hall h h' hq hq']
  simp only [a2Braid_E, ↓reduceIte, braidEi, map_neg, map_mul, Kt, a2Braid_K,
    a2Braid_a2Braid_Fi i j hij hall h h' hq hq',
    reflY_reflY_ktilde_of_simply_laced_edge h h']

/-- The length-three braid words agree on the first negative generator. Reconstructed by
the same double-generator transport, including the negative toral exponent. -/
theorem a2Braid_braid_Fi :
    a2Braid i j hij hall h h' hq
        (a2Braid j i hij.symm (fun l ↦ (hall l).symm) h' h hq'
          (a2Braid i j hij hall h h' hq (F R v i))) =
      a2Braid j i hij.symm (fun l ↦ (hall l).symm) h' h hq'
        (a2Braid i j hij hall h h' hq
          (a2Braid j i hij.symm (fun l ↦ (hall l).symm) h' h hq' (F R v i))) := by
  rw [a2Braid_a2Braid_Fi i j hij hall h h' hq hq']
  simp only [a2Braid_F, ↓reduceIte, braidFi, map_neg, map_mul, a2Braid_K,
    a2Braid_a2Braid_Ei i j hij hall h h' hq hq',
    reflY_reflY_ktilde_of_simply_laced_edge h h']

/-- The actual coupled A2 quotient automorphisms satisfy the length-three braid relation.
Reconstructed by checking both Chevalley colors and every toral lattice generator. Only the
first denominator condition is assumed; the second is transported by symmetrization. -/
theorem a2Braid_braid :
    let Ti := a2Braid (R := R) i j hij hall h h' hq
    let Tj := a2Braid (R := R) j i hij.symm (fun l ↦ (hall l).symm) h' h
      (D.sub_inv_ne_zero_of_simply_laced_edge h h' hq)
    Ti.comp (Tj.comp Ti) = Tj.comp (Ti.comp Tj) := by
  dsimp only
  have hqj := D.sub_inv_ne_zero_of_simply_laced_edge h h' hq
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · rcases hall l with hl | hl
    · subst l
      exact a2Braid_braid_Ei i j hij hall h h' hq hqj
    · subst l
      exact (a2Braid_braid_Ei j i hij.symm (fun l ↦ (hall l).symm) h' h hqj hq).symm
  · rcases hall l with hl | hl
    · subst l
      exact a2Braid_braid_Fi i j hij hall h h' hq hqj
    · subst l
      exact (a2Braid_braid_Fi j i hij.symm (fun l ↦ (hall l).symm) h' h hqj hq).symm
  · simp only [AlgHom.comp_apply, a2Braid_K,
      reflY_braid_of_simply_laced_edge h h']

/-- The published coupled A2 algebra equivalences satisfy `Tᵢ Tⱼ Tᵢ = Tⱼ Tᵢ Tⱼ`.
Reconstructed from the actual quotient-homomorphism equality. The arbitrary field and
root datum lattice hypotheses of `a2BraidEquiv` are retained without extra assumptions. -/
theorem a2BraidEquiv_braid :
    let Ti := a2BraidEquiv (R := R) i j hij hall h h' hq
    let Tj := a2BraidEquiv (R := R) j i hij.symm (fun l ↦ (hall l).symm) h' h
      (D.sub_inv_ne_zero_of_simply_laced_edge h h' hq)
    (Ti.trans Tj).trans Ti = (Tj.trans Ti).trans Tj := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (a2Braid_braid i j hij hall h h' hq) x

end

end LieLean.QuantumGroup
