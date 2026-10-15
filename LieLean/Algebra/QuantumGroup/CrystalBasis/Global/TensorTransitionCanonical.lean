/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorTransition

/-!
# The transition maps on the canonical bases `(b ◇ b'')_{λ,λ''}`

For dominant `λ, λ', λ''`, [Lus] 25.1.7–25.1.10 show that the map
`t : ʷΛ_{λ'+λ} ⊗ Λ_{λ'+λ''} → ʷΛ_λ ⊗ Λ_{λ''}` of 25.1.5 maps the canonical basis element
`(b ◇ b'')_{λ'+λ,λ'+λ''}` of 24.3.3 to `(b ◇ b'')_{λ,λ''}` when `b ∈ B(λ)`, `b'' ∈ B(λ'')`, and
to `0` otherwise. Here `B(λ) ⊆ B(λ'+λ)` (`canonicalBasisHW_subset_add`).

The proof is Lusztig's: modulo `v⁻¹ℒ` this is Lemma 25.1.6, and `t` commutes with the involutions
`Ψ` of 24.3.2 (Lemma 25.1.9), so the difference is a `Ψ`-invariant element of `v⁻¹ℒ`, hence zero
by 24.3.3.

## Main results

* `tensorPsi_hwv`: `Ψ(ξ_{-λ} ⊗ η_{λ'}) = ξ_{-λ} ⊗ η_{λ'}`;
* `tensorTransition_tensorPsi`: **[Lus] Lemma 25.1.9**, `tΨ = Ψt`;
* `tensorTransition_mem_tensorLatNeg_of_mem`: `t(v⁻¹ℒ) ⊆ v⁻¹ℒ`;
* `tensorTransition_tensorCanonical_sub_mem`, `tensorTransition_tensorCanonical_mem`:
  **[Lus] Lemma 25.1.7 (a), (b)**;
* `tensorTransition_tensorCanonical`, `tensorTransition_tensorCanonical_eq_zero`:
  **[Lus] Prop. 25.1.10 (a), (b)**.

As in 25.1.2–25.1.6, the root datum is assumed `X`-regular, where Lusztig assumes it
`Y`-regular.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 25.1.7–25.1.10.
-/

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop LusztigF TensorProduct

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular)

variable (D) in
/-- `B(λ) ⊆ B(λ' + λ)` for dominant `λ'`. -/
lemma canonicalBasisHW_subset_add (Λ Λ' : Dom R) :
    canonicalBasisHW D Λ ⊆ canonicalBasisHW D (Λ' + Λ) := by
  intro x hx
  rw [mem_canonicalBasisHW_iff] at hx ⊢
  refine ⟨hx.1, fun i hi ↦ hx.2 i (rightRange_anti D i ?_ hi)⟩
  have := Λ'.2 i
  simp only [Dom.add_val, AddMonoidHom.add_apply]
  omega

/-! ### `Ψ` and `t` -/

section Psi

variable (Λ Λ' : Dom R)

omit [Finite I] in
lemma hwv_mem_hwWt : IrreducibleModule.hwv R 𝕧 Λ.1 ∈ hwWt Λ 0 := by
  rw [hwWt, LusztigCartanDatum.RootDatum.rootSum_zero, sub_zero]
  exact fun μ ↦ hw_K_smul_hwv Λ μ

/-- `Ψ(ξ_{-λ} ⊗ η_{λ'}) = ξ_{-λ} ⊗ η_{λ'}`. -/
theorem tensorPsi_hwv :
    tensorPsi hR Λ Λ' (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
      IrreducibleModule.hwv R 𝕧 Λ'.1) =
      ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
        IrreducibleModule.hwv R 𝕧 Λ'.1 := by
  rw [tensorPsi_apply, barPair_tmul, twBar_toTwist]
  change quasiRAct (isPlusLocallyNilpotent_hw Λ')
    (ChevalleyTwist.toTwist R 𝕧 _ (hwBar hR Λ (IrreducibleModule.hwv R 𝕧 Λ.1)) ⊗ₜ[𝕂]
      hwBar hR Λ' (IrreducibleModule.hwv R 𝕧 Λ'.1)) = _
  rw [hwBar_hwv, hwBar_hwv, quasiRAct_apply, finsum_eq_single _ 0 fun ν hν ↦
    actPair_quasiR_eq_zero hR Λ Λ' (fun h ↦ hν (nonpos_iff_eq_zero.1 h.1))
      (tmul_mem_tensorWt Λ Λ' (hwv_mem_hwWt Λ) (hwv_mem_hwWt Λ')),
    quasiR_zero, map_one, Module.End.one_apply]

/-- `Ψ(u(ξ_{-λ} ⊗ η_{λ'})) = ū(ξ_{-λ} ⊗ η_{λ'})`. -/
lemma tensorPsi_act_hwv (u : QuantumGroup R 𝕧) :
    tensorPsi hR Λ Λ' (TensorModule.act R 𝕧 _ _ u
      (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
        IrreducibleModule.hwv R 𝕧 Λ'.1)) =
      TensorModule.act R 𝕧 _ _ (barHom R u)
        (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
          IrreducibleModule.hwv R 𝕧 Λ'.1) := by
  conv_lhs => rw [← barHom_barHom R u]
  rw [← act_tensorPsi, tensorPsi_hwv]

end Psi

section Transition

variable (Λ Λ' Λ'' : Dom R)

/-- **[Lus] Lemma 25.1.9**: `tΨ = Ψt`. -/
theorem tensorTransition_tensorPsi (z : TwL (Λ' + Λ) ⊗[𝕂] IrreducibleModule R 𝕧 (Λ' + Λ'').1) :
    tensorTransition hR Λ Λ' Λ'' (tensorPsi hR (Λ' + Λ) (Λ' + Λ'') z) =
      tensorPsi hR Λ Λ'' (tensorTransition hR Λ Λ' Λ'' z) := by
  obtain ⟨u, rfl⟩ := exists_act_tmul_hwv_eq (Λ' + Λ) (Λ' + Λ'') z
  rw [tensorPsi_act_hwv, tensorTransition_act, tensorTransition_act, tensorTransition_hwv,
    tensorPsi_act_hwv]

end Transition

/-! ### The lattices -/

section Lattice

variable (Λ Λ' : Dom R)

lemma tensorCanonical_sub_tensorBasisIdx_mem (h : TensorIdx Λ Λ') :
    tensorCanonical hR Λ Λ' h - tensorBasisIdx hR Λ Λ' h ∈ tensorLatNeg hR Λ Λ' := by
  classical
  intro h'
  rw [map_sub, Finsupp.sub_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hh : h = h'
  · subst hh
    rw [ite_eq_left rfl, repr_tensorCanonical_self, sub_self]
    exact isNegLaurent_zero
  · rw [ite_eq_right hh, sub_zero]
    exact isNegLaurent_repr_tensorCanonical hR Λ Λ' (Ne.symm hh)

/-- [Lus] 24.3.3 (b): `(b₁ ◇ b₁')_{λ,λ'} - b₁⁺ξ_{-λ} ⊗ b₁'⁻η_{λ'} ∈ v⁻¹ℒ`. -/
lemma tensorCanonical_sub_mem_tensorLatNeg (h : canonicalBasisHW D Λ × canonicalBasisHW D Λ') :
    tensorCanonical hR Λ Λ' h - tensorBasis hR Λ Λ' h ∈ tensorLatNeg hR Λ Λ' :=
  tensorCanonical_sub_tensorBasisIdx_mem hR Λ Λ' h

variable (Λ'' : Dom R)

/-- The coordinates of `t(b⁺ξ_{-λ'-λ} ⊗ b''⁻η_{λ'+λ''})` lie in `ℤ[v⁻¹]` (by [Lus] 25.1.6). -/
lemma isIntInv_repr_tensorTransition
    (h : canonicalBasisHW D (Λ' + Λ) × canonicalBasisHW D (Λ' + Λ''))
    (p : canonicalBasisHW D Λ × canonicalBasisHW D Λ'') :
    IsIntInv ((tensorBasis hR Λ Λ'').repr
      (tensorTransition hR Λ Λ' Λ'' (tensorBasis hR (Λ' + Λ) (Λ' + Λ'') h)) p) := by
  classical
  have := repr_tensorTransition_sub hR Λ Λ' Λ'' (canonicalBasisHW_subset D _ h.1.2)
    (canonicalBasisHW_subset D _ h.2.2) p
  rw [tensorBasis_apply]
  have hite : IsIntInv (if (p.1 : Um D 𝕧) = h.1 ∧ (p.2 : Um D 𝕧) = h.2 then (1 : 𝕂) else 0) := by
    split_ifs
    exacts [isIntInv_one, isIntInv_zero]
  convert this.isIntInv.add hite using 1
  exact (sub_add_cancel _ _).symm

/-- `t(v⁻¹ℒ_{λ'+λ,λ'+λ''}) ⊆ v⁻¹ℒ_{λ,λ''}`. -/
theorem tensorTransition_mem_tensorLatNeg_of_mem
    {z : TwL (Λ' + Λ) ⊗[𝕂] IrreducibleModule R 𝕧 (Λ' + Λ'').1}
    (hz : z ∈ tensorLatNeg hR (Λ' + Λ) (Λ' + Λ'')) :
    tensorTransition hR Λ Λ' Λ'' z ∈ tensorLatNeg hR Λ Λ'' := by
  intro p
  rw [← (tensorBasisIdx hR (Λ' + Λ) (Λ' + Λ'')).linearCombination_repr z,
    Finsupp.linearCombination_apply, map_finsuppSum, map_finsuppSum, Finsupp.sum_apply]
  refine isNegLaurent_finsuppSum _ fun h _ ↦ ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact (hz h).mul_isIntInv (isIntInv_repr_tensorTransition hR Λ Λ' Λ'' h p)

end Lattice

/-! ### [Lus] Lemma 25.1.7 and Prop. 25.1.10 -/

section Canonical

variable (Λ Λ' Λ'' : Dom R)

/-- `(b, b'') ∈ B(λ) × B(λ'')` as an element of `B(λ'+λ) × B(λ'+λ'')`. -/
def tensorIdxAdd (b : canonicalBasisHW D Λ) (b'' : canonicalBasisHW D Λ'') :
    canonicalBasisHW D (Λ' + Λ) × canonicalBasisHW D (Λ' + Λ'') :=
  (⟨b, canonicalBasisHW_subset_add D Λ Λ' b.2⟩, ⟨b'', canonicalBasisHW_subset_add D Λ'' Λ' b''.2⟩)

@[simp] lemma coe_tensorIdxAdd_fst (b : canonicalBasisHW D Λ) (b'' : canonicalBasisHW D Λ'') :
    ((tensorIdxAdd Λ Λ' Λ'' b b'').1 : Um D 𝕧) = b := rfl

@[simp] lemma coe_tensorIdxAdd_snd (b : canonicalBasisHW D Λ) (b'' : canonicalBasisHW D Λ'') :
    ((tensorIdxAdd Λ Λ' Λ'' b b'').2 : Um D 𝕧) = b'' := rfl

/-- **[Lus] Lemma 25.1.7 (a)**: for `b ∈ B(λ)`, `b'' ∈ B(λ'')`,
`t((b ◇ b'')_{λ'+λ,λ'+λ''}) ≡ (b ◇ b'')_{λ,λ''}` modulo `v⁻¹ℒ_{λ,λ''}`. -/
theorem tensorTransition_tensorCanonical_sub_mem (b : canonicalBasisHW D Λ)
    (b'' : canonicalBasisHW D Λ'') :
    tensorTransition hR Λ Λ' Λ'' (tensorCanonical hR (Λ' + Λ) (Λ' + Λ'')
      (tensorIdxAdd Λ Λ' Λ'' b b'')) - tensorCanonical hR Λ Λ'' (b, b'') ∈
        tensorLatNeg hR Λ Λ'' := by
  have h₁ := tensorTransition_mem_tensorLatNeg_of_mem hR Λ Λ' Λ''
    (tensorCanonical_sub_mem_tensorLatNeg hR (Λ' + Λ) (Λ' + Λ'') (tensorIdxAdd Λ Λ' Λ'' b b''))
  have h₂ := tensorTransition_sub_mem_tensorLatNeg hR Λ Λ' Λ'' b b''
  have h₃ := tensorCanonical_sub_mem_tensorLatNeg hR Λ Λ'' (b, b'')
  rw [map_sub, tensorBasis_apply, coe_tensorIdxAdd_fst, coe_tensorIdxAdd_snd] at h₁
  convert add_mem (add_mem h₁ h₂) (neg_mem h₃) using 1
  abel

/-- **[Lus] Lemma 25.1.7 (b)**: for `b ∈ B(λ'+λ)`, `b'' ∈ B(λ'+λ'')` with `b ∉ B(λ)` or
`b'' ∉ B(λ'')`, `t((b ◇ b'')_{λ'+λ,λ'+λ''}) ≡ 0` modulo `v⁻¹ℒ_{λ,λ''}`. -/
theorem tensorTransition_tensorCanonical_mem (b : canonicalBasisHW D (Λ' + Λ))
    (b'' : canonicalBasisHW D (Λ' + Λ''))
    (h : (b : Um D 𝕧) ∉ canonicalBasisHW D Λ ∨ (b'' : Um D 𝕧) ∉ canonicalBasisHW D Λ'') :
    tensorTransition hR Λ Λ' Λ'' (tensorCanonical hR (Λ' + Λ) (Λ' + Λ'') (b, b'')) ∈
      tensorLatNeg hR Λ Λ'' := by
  have h₁ := tensorTransition_mem_tensorLatNeg_of_mem hR Λ Λ' Λ''
    (tensorCanonical_sub_mem_tensorLatNeg hR (Λ' + Λ) (Λ' + Λ'') (b, b''))
  have h₂ := tensorTransition_mem_tensorLatNeg hR Λ Λ' Λ'' b b'' h
  rw [map_sub, tensorBasis_apply] at h₁
  convert add_mem h₁ h₂ using 1
  abel

/-- **[Lus] Prop. 25.1.10 (a)**: for `b ∈ B(λ)`, `b'' ∈ B(λ'')`,
`t((b ◇ b'')_{λ'+λ,λ'+λ''}) = (b ◇ b'')_{λ,λ''}`. -/
theorem tensorTransition_tensorCanonical (b : canonicalBasisHW D Λ)
    (b'' : canonicalBasisHW D Λ'') :
    tensorTransition hR Λ Λ' Λ'' (tensorCanonical hR (Λ' + Λ) (Λ' + Λ'')
      (tensorIdxAdd Λ Λ' Λ'' b b'')) = tensorCanonical hR Λ Λ'' (b, b'') := by
  rw [← sub_eq_zero]
  refine eq_zero_of_tensorPsi_eq hR Λ Λ'' ?_ ((mem_tensorLatNeg_iff hR Λ Λ'').1
    (tensorTransition_tensorCanonical_sub_mem hR Λ Λ' Λ'' b b''))
  have e₁ := tensorPsi_tensorCanonical hR (Λ' + Λ) (Λ' + Λ'') (tensorIdxAdd Λ Λ' Λ'' b b'')
  have e₂ := tensorPsi_tensorCanonical hR Λ Λ'' (b, b'')
  rw [map_sub, ← tensorTransition_tensorPsi, e₁, e₂]

/-- **[Lus] Prop. 25.1.10 (b)**: for `b ∈ B(λ'+λ)`, `b'' ∈ B(λ'+λ'')` with `b ∉ B(λ)` or
`b'' ∉ B(λ'')`, `t((b ◇ b'')_{λ'+λ,λ'+λ''}) = 0`. -/
theorem tensorTransition_tensorCanonical_eq_zero (b : canonicalBasisHW D (Λ' + Λ))
    (b'' : canonicalBasisHW D (Λ' + Λ''))
    (h : (b : Um D 𝕧) ∉ canonicalBasisHW D Λ ∨ (b'' : Um D 𝕧) ∉ canonicalBasisHW D Λ'') :
    tensorTransition hR Λ Λ' Λ'' (tensorCanonical hR (Λ' + Λ) (Λ' + Λ'') (b, b'')) = 0 := by
  refine eq_zero_of_tensorPsi_eq hR Λ Λ'' ?_ ((mem_tensorLatNeg_iff hR Λ Λ'').1
    (tensorTransition_tensorCanonical_mem hR Λ Λ' Λ'' b b'' h))
  have e := tensorPsi_tensorCanonical hR (Λ' + Λ) (Λ' + Λ'') (b, b'')
  rw [← tensorTransition_tensorPsi, e]

end Canonical

end LieLean.QuantumGroup
