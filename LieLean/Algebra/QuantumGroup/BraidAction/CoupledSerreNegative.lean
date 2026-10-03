/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.CoupledSerre

/-!
# Chevalley involution and negative transformed Serre relations

## Main results

The coefficient-linear Chevalley involution is constructed from the actual quotient
presentation, not from an assumed braid automorphism. Its scalar factors on the actual
braid candidates transport the established positive Serre relation to negative images.

## References

Reconstructed directly from the presentation.
-/

noncomputable section
namespace QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k)

/-- Toral inversion as a monoid homomorphism. -/
def chevalleyK : Multiplicative Y →* QuantumGroup R v where
  toFun μ := K R v (-μ.toAdd)
  map_one' := by simp
  map_mul' μ ν := by simp [K_add, add_comm]

/-- Swapping `E,F` and inverting `K` preserves the actual defining relations. -/
theorem chevalley_relations : Relations R v (F R v) (E R v) (chevalleyK R v) where
  K_mul_E μ i := by
    change K R v (-μ) * F R v i = _
    simpa [chevalleyK] using K_mul_F R v (-μ) i
  K_mul_F μ i := by
    change K R v (-μ) * E R v i = _
    simpa [chevalleyK] using K_mul_E R v (-μ) i
  E_mul_F i j := by
    change F R v i * E R v j - E R v j * F R v i = _
    by_cases h : i = j
    · subst j
      simpa [chevalleyK, neg_sub, smul_sub] using
        congrArg Neg.neg (E_mul_F_sub R v i i)
    · simpa [chevalleyK, h, Ne.symm h, neg_sub] using
        congrArg Neg.neg (E_mul_F_sub R v j i)
  serre_E _ _ h := serre_F R v h
  serre_F _ _ h := serre_E R v h

/-- Genuine coefficient-linear Chevalley homomorphism on the quantum quotient. -/
def chevalley : QuantumGroup R v →ₐ[k] QuantumGroup R v :=
  lift (chevalley_relations R v)

@[simp] theorem chevalley_E (i : I) : chevalley R v (E R v i) = F R v i := lift_E _ i

@[simp] theorem chevalley_F (i : I) : chevalley R v (F R v i) = E R v i := lift_F _ i

@[simp] theorem chevalley_K (μ : Y) : chevalley R v (K R v μ) = K R v (-μ) :=
  lift_K _ μ

/-- Squaring the Chevalley map is the identity on the actual quotient. -/
theorem chevalley_comp_chevalley :
    (chevalley R v).comp (chevalley R v) = AlgHom.id k (QuantumGroup R v) := by
  apply hom_ext <;> intro x <;> simp

/-- The coefficient-linear Chevalley involution, with its inverse proved. -/
def chevalleyEquiv : QuantumGroup R v ≃ₐ[k] QuantumGroup R v :=
  AlgEquiv.ofAlgHom (chevalley R v) (chevalley R v)
    (chevalley_comp_chevalley R v) (chevalley_comp_chevalley R v)

variable {R v} {i j : I}

/-- The reflected-node scalar factor is `qᵢ²`, not one. -/
theorem chevalley_braidEi (hv : v ≠ 0) (i : I) :
    chevalley R v (braidEi R i) = (v ^ D.d i) ^ 2 • braidFi R i := by
  simp only [braidEi, braidFi, map_neg, map_mul, chevalley_F, Kt, chevalley_K,
    K_neg_ktilde_mul_E, smul_neg, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero 2 (pow_ne_zero _ hv)), one_smul]

/-- The neighboring scalar factor at a directed simple edge is `-qᵢ⁻¹`. -/
theorem chevalley_braidEj_of_cartanMatrix_eq_neg_one (hv : v ≠ 0)
    (h : D.cartanMatrix i j = -1) :
    chevalley R v (braidEj R v i j) = -(v ^ D.d i)⁻¹ • braidFj R v i j := by
  rw [braidEj_eq_of_cartanMatrix_eq_neg_one h,
    braidFj_eq_of_cartanMatrix_eq_neg_one hv h]
  simp only [map_sub, map_mul, map_smul, chevalley_E, smul_sub, smul_smul]
  have hc := inv_mul_cancel₀ (pow_ne_zero (D.d i) hv)
  linear_combination (norm := module) -
    congrArg (fun t : k ↦ t • (F R v i * F R v j)) hc

/-- The negative transformed Serre relation for the actual reflected-node and neighbor
images at a directed simple edge. The reverse Cartan entry is unrestricted. -/
theorem qSerre_braidFi_braidFj_of_cartanMatrix_eq_neg_one [NeZero v]
    (h : D.cartanMatrix i j = -1)
    (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0) :
    qSerre (v ^ D.d i) (1 - D.cartanMatrix i j).toNat
      (braidFi R i) (braidFj R v i j) = 0 := by
  have hs := congrArg (chevalley R v)
    (qSerre_braidEi_braidEj_of_cartanMatrix_eq_neg_one (R := R) h hq)
  rw [map_qSerre, map_zero, chevalley_braidEi (NeZero.ne v),
    chevalley_braidEj_of_cartanMatrix_eq_neg_one (NeZero.ne v) h,
    qSerre_smul_smul] at hs
  exact (smul_eq_zero.mp hs).resolve_left
    (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ (NeZero.ne v))))
      (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ (NeZero.ne v)))))

end QuantumGroup
