/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ContravariantForm
import LieLean.Algebra.QuantumGroup.LusztigF.MapCoeffs
import LieLean.Algebra.QuantumGroup.PBW.RootVectorWeights

/-!
# Base change of `U_q(𝔤)` along a field extension

For a field extension `L / k` and `v ∈ k`, the defining relations of `U = U_q(𝔤)` at `v` and at
the image `v' ∈ L` of `v` have the same coefficients, so `Eᵢ ↦ Eᵢ`, `Fᵢ ↦ Fᵢ`, `K_μ ↦ K_μ`
defines an isomorphism of `L`-algebras `L ⊗_K U_K ≅ U_L` ([Lus] 3.1.1 and 1.3.1 for the
quantum binomial coefficients).

## Main definitions

* `QuantumGroup.toBaseChange`: the ring homomorphism `U_K → U_L` on generators.
* `QuantumGroup.baseChangeEquiv`: the `L`-algebra isomorphism `L ⊗[k] U_K ≃ U_L`.

## Main results

* `QuantumGroup.relations_algebraMap_iff`: the defining relations at `v` and at `v'` agree.
* `QuantumGroup.toBaseChange_minusHom`, `toBaseChange_plusHom`: compatibility with `x ↦ x⁻`,
  `x ↦ x⁺` and the coefficient map of `'f`.
* `QuantumGroup.toBaseChange_rho`: compatibility with Lusztig's anti-automorphism `ρ`.
* `QuantumGroup.toBaseChange_mem_adWeightSpace`: compatibility with the conjugation weights.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.3.1, 3.1.1, 19.1.1.
-/

noncomputable section

open TensorProduct

namespace LieLean.QuantumGroup

section Coefficients

variable {k L : Type*} [Field k] [Field L]

theorem qBinomial_map (φ : k →+* L) (w : k) (n j : ℕ) :
    qBinomial (φ w) n j = φ (qBinomial w n j) := by
  induction n generalizing j with
  | zero => cases j <;> simp [qBinomial]
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j => simp [qBinomial, ih, map_inv₀]

variable [Algebra k L] {B : Type*} [Ring B] [Algebra k B] [Algebra L B] [IsScalarTower k L B]

theorem qSerre_algebraMap (w : k) (m : ℕ) (a b : B) :
    qSerre (algebraMap k L w) m a b = qSerre w m a b := by
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [qBinomial_map, show (-1 : L) ^ r * algebraMap k L (qBinomial w m r) =
    algebraMap k L ((-1) ^ r * qBinomial w m r) by simp, algebraMap_smul]

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k) {e f : I → B} {κ : Multiplicative Y →* B}

/-- The defining relations of `U` at `v ∈ k` and at its image in `L` are the same. -/
theorem relations_algebraMap_iff :
    Relations R (algebraMap k L v) e f κ ↔ Relations R v e f κ := by
  have hz (n : ℤ) (x : B) : algebraMap k L v ^ n • x = v ^ n • x := by
    rw [← map_zpow₀, algebraMap_smul]
  have hc (d : ℕ) (x : B) :
      (algebraMap k L v ^ d - (algebraMap k L v ^ d)⁻¹)⁻¹ • x = (v ^ d - (v ^ d)⁻¹)⁻¹ • x := by
    rw [← map_pow, ← map_inv₀, ← map_sub, ← map_inv₀, algebraMap_smul]
  have hs (d m : ℕ) (a b : B) : qSerre (algebraMap k L v ^ d) m a b = qSerre (v ^ d) m a b := by
    rw [← map_pow, qSerre_algebraMap]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨⟨fun μ i ↦ by rw [h1, hz], fun μ i ↦ by rw [h2, hz], fun i j ↦ by rw [h3, hc]⟩,
      fun i j h ↦ by rw [← hs, h4 i j h], fun i j h ↦ by rw [← hs, h5 i j h]⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨⟨fun μ i ↦ by rw [h1, hz], fun μ i ↦ by rw [h2, hz], fun i j ↦ by rw [h3, hc]⟩,
      fun i j h ↦ by rw [hs, h4 i j h], fun i j h ↦ by rw [hs, h5 i j h]⟩

end Coefficients

variable {k L I Y : Type*} [Field k] [Field L] [Algebra k L] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (v : k)

/-- The `k`-algebra structure on `U_L` through `k → L` (used locally to construct the base change
maps). -/
abbrev baseChangeAlgebra : Algebra k (QuantumGroup R (algebraMap k L v)) :=
  Algebra.compHom _ (algebraMap k L)

attribute [local instance] baseChangeAlgebra

instance : IsScalarTower k L (QuantumGroup R (algebraMap k L v)) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- `U_K → U_L` as a `k`-algebra homomorphism. -/
def toBaseChangeAlgHom : QuantumGroup R v →ₐ[k] QuantumGroup R (algebraMap k L v) :=
  lift ((relations_algebraMap_iff R v).mp (relations R (algebraMap k L v)))

/-- The ring homomorphism `U_K → U_L`, `Eᵢ ↦ Eᵢ`, `Fᵢ ↦ Fᵢ`, `K_μ ↦ K_μ`. -/
def toBaseChange : QuantumGroup R v →+* QuantumGroup R (algebraMap k L v) :=
  (toBaseChangeAlgHom R v).toRingHom

variable {R v}

@[simp] theorem toBaseChange_E (i : I) :
    toBaseChange (L := L) R v (E R v i) = E R (algebraMap k L v) i := by
  simp [toBaseChange, toBaseChangeAlgHom]

@[simp] theorem toBaseChange_F (i : I) :
    toBaseChange (L := L) R v (F R v i) = F R (algebraMap k L v) i := by
  simp [toBaseChange, toBaseChangeAlgHom]

@[simp] theorem toBaseChange_K (μ : Y) :
    toBaseChange (L := L) R v (K R v μ) = K R (algebraMap k L v) μ := by
  simp only [toBaseChange, toBaseChangeAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, lift_K]
  rfl

theorem toBaseChange_smul (c : k) (x : QuantumGroup R v) :
    toBaseChange (L := L) R v (c • x) = algebraMap k L c • toBaseChange R v x :=
  map_smul (toBaseChangeAlgHom R v) c x

@[simp] theorem toBaseChange_algebraMap (c : k) :
    toBaseChange (L := L) R v (algebraMap k _ c) = algebraMap L _ (algebraMap k L c) :=
  (toBaseChangeAlgHom R v).commutes c

variable (R v)

/-- The `L`-algebra homomorphism `L ⊗[k] U_K → U_L`. -/
def baseChangeHom : L ⊗[k] QuantumGroup R v →ₐ[L] QuantumGroup R (algebraMap k L v) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (toBaseChangeAlgHom R v)
    fun c _ ↦ Algebra.commute_algebraMap_left c _

/-- The `L`-algebra homomorphism `U_L → L ⊗[k] U_K`, `Eᵢ ↦ 1 ⊗ Eᵢ`. -/
def baseChangeInv : QuantumGroup R (algebraMap k L v) →ₐ[L] L ⊗[k] QuantumGroup R v :=
  lift ((relations_algebraMap_iff R v).mpr
    ((relations R v).map Algebra.TensorProduct.includeRight))

/-- Base change of `U_q(𝔤)` along a field extension `L / k`: `L ⊗_K U_K(v) ≅ U_L(v)` as
`L`-algebras, `1 ⊗ Eᵢ ↦ Eᵢ`, `1 ⊗ Fᵢ ↦ Fᵢ`, `1 ⊗ K_μ ↦ K_μ`. -/
def baseChangeEquiv : L ⊗[k] QuantumGroup R v ≃ₐ[L] QuantumGroup R (algebraMap k L v) :=
  AlgEquiv.ofAlgHom (baseChangeHom R v) (baseChangeInv R v)
    (hom_ext (fun i ↦ by simp [baseChangeHom, baseChangeInv, toBaseChangeAlgHom])
      (fun i ↦ by simp [baseChangeHom, baseChangeInv, toBaseChangeAlgHom])
      (fun μ ↦ by simp [baseChangeHom, baseChangeInv, toBaseChangeAlgHom]))
    (Algebra.TensorProduct.ext (Subsingleton.elim _ _)
      (hom_ext (fun i ↦ by simp [baseChangeHom, baseChangeInv, toBaseChangeAlgHom])
        (fun i ↦ by simp [baseChangeHom, baseChangeInv, toBaseChangeAlgHom])
        (fun μ ↦ by simp [baseChangeHom, baseChangeInv, toBaseChangeAlgHom])))

variable {R v}

@[simp] theorem baseChangeEquiv_tmul (c : L) (x : QuantumGroup R v) :
    baseChangeEquiv (L := L) R v (c ⊗ₜ x) = c • toBaseChange R v x := by
  rw [Algebra.smul_def]
  change baseChangeHom (L := L) R v (c ⊗ₜ x) = _
  exact Algebra.TensorProduct.lift_tmul _ _ _ c x

theorem baseChangeEquiv_one_tmul (x : QuantumGroup R v) :
    baseChangeEquiv (L := L) R v ((1 : L) ⊗ₜ x) = toBaseChange R v x := by
  simp

/-! ### Compatibilities -/

theorem toBaseChange_minusHom (x : LusztigF k I) :
    toBaseChange (L := L) R v (minusHom R v x) =
      minusHom R (algebraMap k L v) (FreeAlgebra.mapCoeffs (algebraMap k L) x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 i => simp [minusHom]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem toBaseChange_plusHom (x : LusztigF k I) :
    toBaseChange (L := L) R v (plusHom R v x) =
      plusHom R (algebraMap k L v) (FreeAlgebra.mapCoeffs (algebraMap k L) x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 i => simp [plusHom]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

instance [NeZero v] : NeZero (algebraMap k L v) :=
  ⟨(map_ne_zero _).mpr (NeZero.ne v)⟩

theorem toBaseChange_rho [NeZero v] (x : QuantumGroup R v) :
    toBaseChange (L := L) R v (rho R v x) = rho R (algebraMap k L v) (toBaseChange R v x) := by
  induction x using induction_on with
  | algebraMap c => simp
  | E i => simp [rhoE, Kt, toBaseChange_smul]
  | F i => simp [rhoF, toBaseChange_smul]
  | K μ => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [rho_mul, map_mul, hx, hy]

theorem toBaseChange_mem_adWeightSpace {χ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v χ) :
    toBaseChange (L := L) R v x ∈ adWeightSpace R (algebraMap k L v) χ := fun μ ↦ by
  have := congr_arg (toBaseChange (L := L) R v) (hx μ)
  rwa [map_mul, toBaseChange_smul, map_mul, toBaseChange_K, map_zpow₀] at this

end LieLean.QuantumGroup
