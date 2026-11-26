/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.QuasiR.Braiding
import LieLean.Algebra.QuantumGroup.Modified.TensorQuotientQuasiR

/-!
# The braiding of simple highest weight modules

The hypotheses of `QuantumGroup.braidingEquiv` hold for Verma modules and their quotients,
in particular for the simple modules `L_q(Λ)`: their weights lie in `Λ - ℕ[I]`, and they have
the finiteness property of [Lus] 3.4.7. This gives the braiding
`σ : L_q(Λ₁) ⊗ L_q(Λ₂) ≅ L_q(Λ₂) ⊗ L_q(Λ₁)` of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, (1.1), for any `Λ₁`, `Λ₂` (no dominance is needed).

## Main results

* `QuantumGroup.VermaModule.iSup_depthSpace_eq_top`,
  `QuantumGroup.iSup_depthSpace_eq_top_of_surjective`: the weights of `M_q(Λ)` and of its
  quotients lie in `Λ - ℕ[I]`.
* `QuantumGroup.IrreducibleModule.braidingEquiv`: the braiding of `L_q(Λ₁)` and `L_q(Λ₂)`.
* `QuantumGroup.IrreducibleModule.braidingEquiv_tmul_hwv`: `σ(m ⊗ v_{Λ₂}) = v^{-(ν, Λ₂)} v_{Λ₂} ⊗ m`
  for `m` of weight `Λ₁ - ν`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 3.4.7.
* B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, (1.1).
-/

open LieLean LusztigF TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

variable (R) in
/-- The weights of `M_q(Λ)` lie in `Λ - ℕ[I]`. -/
theorem VermaModule.iSup_depthSpace_eq_top (Λ : Y →+ ℤ) :
    ⨆ ν, depthSpace R (VermaModule R 𝕧 Λ) Λ ν = ⊤ := by
  rw [eq_top_iff, ← VermaModule.range_toVerma (Λ := Λ), ← VermaModule.iSup_map_toVerma]
  exact iSup_mono fun ν ↦ Submodule.map_le_iff_le_comap.2 fun y hy ↦
    VermaModule.toVerma_mem_weightSpace hy

/-- The weights of a quotient of a module with weights in `Λ - ℕ[I]` lie in `Λ - ℕ[I]`. -/
theorem iSup_depthSpace_eq_top_of_surjective {M N : Type*} [AddCommGroup M] [Module 𝕂 M]
    [Module (QuantumGroup R 𝕧) M] [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M] [AddCommGroup N]
    [Module 𝕂 N] [Module (QuantumGroup R 𝕧) N] [IsScalarTower 𝕂 (QuantumGroup R 𝕧) N]
    {Λ : Y →+ ℤ} (hM : ⨆ ν, depthSpace R M Λ ν = ⊤) (g : M →ₗ[QuantumGroup R 𝕧] N)
    (hg : Function.Surjective g) : ⨆ ν, depthSpace R N Λ ν = ⊤ := by
  rw [eq_top_iff]
  rintro n -
  obtain ⟨m, rfl⟩ := hg n
  have hm : m ∈ ⨆ ν, depthSpace R M Λ ν := by rw [hM]; trivial
  induction hm using Submodule.iSup_induction' with
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mem ν x hx =>
    refine Submodule.mem_iSup_of_mem ν fun μ ↦ ?_
    rw [← g.map_smul, hx μ, LinearMap.map_smul_of_tower]

namespace IrreducibleModule

variable (Λ : Y →+ ℤ)

/-- The quotient map `M_q(Λ) → L_q(Λ)`. -/
abbrev mkQ : VermaModule R 𝕧 Λ →ₗ[QuantumGroup R 𝕧] IrreducibleModule R 𝕧 Λ :=
  (VermaModule.maxSubmodule R 𝕧 Λ).mkQ

theorem iSup_depthSpace_eq_top :
    ⨆ ν, depthSpace R (IrreducibleModule R 𝕧 Λ) Λ ν = ⊤ :=
  iSup_depthSpace_eq_top_of_surjective (VermaModule.iSup_depthSpace_eq_top R Λ) (mkQ Λ)
    (Submodule.mkQ_surjective _)

/-- The highest weight vector has depth `0`. -/
theorem hwv_mem_depthSpace_zero :
    hwv R 𝕧 Λ ∈ depthSpace R (IrreducibleModule R 𝕧 Λ) Λ 0 := fun μ ↦ by
  rw [R.rootSum_zero, sub_zero, IrreducibleModule.hwv, ← Submodule.Quotient.mk_smul,
    VermaModule.K_smul_hwv, Submodule.Quotient.mk_smul]

variable [Finite I]

theorem isPlusLocallyNilpotent : IsPlusLocallyNilpotent R (IrreducibleModule R 𝕧 Λ) :=
  (VermaModule.isPlusLocallyNilpotent R Λ).of_surjective (mkQ Λ) (Submodule.mkQ_surjective _)

variable (hR : R.IsXRegular) (Λ₁ Λ₂ : Y →+ ℤ)

/-- The braiding `σ : L_q(Λ₁) ⊗ L_q(Λ₂) ≅ L_q(Λ₂) ⊗ L_q(Λ₁)` (Webster, arXiv:1309.3796v3,
(1.1), up to the scalar `v^{(Λ₁, Λ₂)}`). -/
def braidingEquiv :
    TensorModule 𝕂 (IrreducibleModule R 𝕧 Λ₁) (IrreducibleModule R 𝕧 Λ₂) ≃ₗ[QuantumGroup R 𝕧]
      TensorModule 𝕂 (IrreducibleModule R 𝕧 Λ₂) (IrreducibleModule R 𝕧 Λ₁) :=
  QuantumGroup.braidingEquiv hR (iSup_depthSpace_eq_top Λ₁) (iSup_depthSpace_eq_top Λ₂)
    (isPlusLocallyNilpotent Λ₂)

/-- `σ(m ⊗ v_{Λ₂}) = v^{-(ν, Λ₂)} v_{Λ₂} ⊗ m` for `m` of weight `Λ₁ - ν`. -/
theorem braidingEquiv_tmul_hwv {ν : I →₀ ℕ} {m : IrreducibleModule R 𝕧 Λ₁}
    (hm : m ∈ depthSpace R (IrreducibleModule R 𝕧 Λ₁) Λ₁ ν) :
    braidingEquiv hR Λ₁ Λ₂ (TensorModule.mk _ _ (m ⊗ₜ hwv R 𝕧 Λ₂)) =
      TensorModule.mk _ _ (𝕧 ^ (-pairDepth R Λ₂ ν) • (hwv R 𝕧 Λ₂ ⊗ₜ m)) := by
  refine braiding_tmul_of_highest hR (iSup_depthSpace_eq_top Λ₁) (iSup_depthSpace_eq_top Λ₂)
    (isPlusLocallyNilpotent Λ₂) hm ?_ ?_
  · exact fun μ ↦ congrArg (Submodule.Quotient.mk (p := VermaModule.maxSubmodule R 𝕧 Λ₂))
      (VermaModule.K_smul_hwv μ)
  · intro ν hν x hx
    rw [IrreducibleModule.hwv, ← Submodule.Quotient.mk_smul, VermaModule.plusHom_smul_hwv,
      LusztigF.counit_eq_zero_of_mem hν hx, zero_smul, Submodule.Quotient.mk_zero]

end IrreducibleModule

end LieLean.QuantumGroup
