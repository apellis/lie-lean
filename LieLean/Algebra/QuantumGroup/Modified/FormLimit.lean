/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Faithful
import LieLean.Algebra.QuantumGroup.Modified.FormOmega
import LieLean.Algebra.QuantumGroup.ShapovalovLimit

/-!
# The inner product on `U̇` as a limit

For `Λ, Λ' : Y →+ ℤ` consider the `U`-module `ʷL_q(Λ) ⊗ L_q(Λ')`, where `ʷL_q(Λ)` is `L_q(Λ)`
with `u` acting as `ω(u)` (`QuantumGroup.ChevalleyTwist`), and the bilinear form
`(x ⊗ x', y ⊗ y') = (x, y)_Λ (x', y')_{Λ'}` on it ([Lus] 26.2.1,
`QuantumGroup.IrreducibleModule.tensorForm`).

## Main results

* `QuantumGroup.ChevalleyTwist.isContravariant_form`: a contravariant form on `M` is
  contravariant on `ʷM`, since `ω ρ = ρ ω`.
* `QuantumGroup.IrreducibleModule.isContravariant_tensorForm`: [Lus] Lemma 26.2.2,
  `(u X, X') = (X, ρ(u) X')` on `ʷL_q(Λ) ⊗ L_q(Λ')`.

Lusztig assumes a `Y`-regular root datum and works with the modules `Λ_λ` (`λ` dominant). Here
`L_q(Λ) = M_q(Λ) ⧸ M'_q(Λ)` carries its contravariant form `IrreducibleModule.form`, which is
defined for `X`-regular root data; for `v` transcendental and `Λ` dominant `L_q(Λ)` is `Λ_Λ`
(`FPowQuotient.equivIrreducibleModule`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 26.2.1, 26.2.2.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]

namespace ChevalleyTwist

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

variable (R v) in
/-- A bilinear form on `M`, as a bilinear form on the twist `ʷM`. -/
def form (B : LinearMap.BilinForm k M) : LinearMap.BilinForm k (ChevalleyTwist R v M) :=
  B.compl₁₂ (toTwist R v M).symm.toLinearMap (toTwist R v M).symm.toLinearMap

omit [DecidableEq I] [NeZero v] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] in
@[simp] lemma form_toTwist (B : LinearMap.BilinForm k M) (x y : M) :
    form R v B (toTwist R v M x) (toTwist R v M y) = B x y := rfl

omit [IsScalarTower k (QuantumGroup R v) M] in
/-- A contravariant form on `M` is contravariant on `ʷM`: `ω ρ = ρ ω` ([Lus] 26.2.2, proof). -/
theorem isContravariant_form {B : LinearMap.BilinForm k M} (hB : IsContravariant R v B) :
    IsContravariant R v (form R v B) := by
  intro u x y
  obtain ⟨x, rfl⟩ := (toTwist R v M).surjective x
  obtain ⟨y, rfl⟩ := (toTwist R v M).surjective y
  rw [smul_toTwist, smul_toTwist, form_toTwist, form_toTwist, hB, chevalley_rho]

end ChevalleyTwist

namespace IrreducibleModule

variable (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-- The form `(x ⊗ x', y ⊗ y') = (x, y)_Λ (x', y')_{Λ'}` on `ʷL_q(Λ) ⊗ L_q(Λ')`
([Lus] 26.2.1). -/
def tensorForm (Λ Λ' : Y →+ ℤ) : LinearMap.BilinForm k
    (TensorModule k (ChevalleyTwist R v (IrreducibleModule R v Λ)) (IrreducibleModule R v Λ')) :=
  TensorModule.form (ChevalleyTwist.form R v (form Λ hR hv')) (form Λ' hR hv')

/-- **[Lus] Lemma 26.2.2**: the form on `ʷL_q(Λ) ⊗ L_q(Λ')` is contravariant,
`(u X, X') = (X, ρ(u) X')`. -/
theorem isContravariant_tensorForm (Λ Λ' : Y →+ ℤ) :
    IsContravariant R v (tensorForm hR hv' Λ Λ') :=
  TensorModule.isContravariant_form
    (ChevalleyTwist.isContravariant_form (isContravariant_form hR hv'))
    (isContravariant_form hR hv')

end IrreducibleModule

end LieLean.QuantumGroup
