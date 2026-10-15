/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.IrreducibleCharacter.Verma
import LieLean.Algebra.QuantumGroup.Modified.FormPlus
import LieLean.Algebra.QuantumGroup.Modified.TensorVermaIntegral
import LieLean.Algebra.QuantumGroup.QuasiR.TensorAction

/-!
# The quasi-R-matrix on tensor products of Verma modules

Over `ℚ(v)`, let `M = ʷM_Λ` (the Verma module `M_Λ` twisted by the Chevalley involution) and
`M' = M_{Λ'}`. The Verma module `M_{Λ'}` has the finiteness property of [Lus] 3.4.7, so the
quasi-R-matrix `Θ` acts on `M ⊗ M'` ([Lus] 24.1.1). **[Lus] Proposition 24.1.4**: `Θ` leaves
stable the `𝒜`-submodule `ʷ𝒜M_Λ ⊗_𝒜 𝒜M_{Λ'}` (`Modified.vermaTensorLattice`).

## Main definitions and results

* `QuantumGroup.barHom_chevalley`: the bar involution of `U` commutes with the Chevalley
  involution.
* `QuantumGroup.VermaModule.isPlusLocallyNilpotent`: `M_Λ` has the property of [Lus] 3.4.7.
* `QuantumGroup.VermaModule.bar`: the bar involution of `M_Λ`, induced by that of `U`
  (`bar_smul`: `\overline{u m} = ū m̄`).
* `QuantumGroup.Modified.quasiRAct_mem_vermaTensorLattice`: **[Lus] Proposition 24.1.4**.

## Proof

As in [Lus] 24.1.4: with `Ξ = Θ ∘ (¯ ⊗ ¯)`, [Lus] 24.1.3 gives `u (ξ ⊗ η) = Ξ(ū (ξ ⊗ η))`,
since `Θ (ξ ⊗ η) = ξ ⊗ η`. An element `x` of the lattice is `\overline{x'}` with `x'` in the
lattice, and `x' = u' (ξ ⊗ η)` with `u'` in the `𝒜`-span of the `F_w E_{w'}` (the reverse
inclusion of [Lus] 23.3.2 (a), `Modified.vermaTensorLattice_le_fePowImage`). That span is
bar-stable, so `Θ(x) = Ξ(u' (ξ ⊗ η)) = ū' (ξ ⊗ η)` lies in the lattice. Lusztig phrases the
middle step through the bar involution of `𝒜U̇ 1_ζ`; we use the `𝒜`-span of the `F_w E_{w'}` in
`U` instead.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 3.4.7, 23.3.2, 24.1.
-/

open LieLean TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)

attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

/-! ### The bar involution and the Chevalley involution -/

theorem barHom_chevalley (u : QuantumGroup R 𝕧) :
    barHom R (chevalley R 𝕧 u) = chevalley R 𝕧 (barHom R u) := by
  induction u using QuantumGroup.induction_on with
  | algebraMap c => rw [AlgHom.commutes, barHom_algebraMap, AlgHom.commutes]
  | E i => rw [chevalley_E, barHom_F, barHom_E, chevalley_E]
  | F i => rw [chevalley_F, barHom_E, barHom_F, chevalley_F]
  | K μ => rw [chevalley_K, barHom_K, barHom_K, chevalley_K]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy, map_mul, map_mul]

theorem barHom_qDivPow (d n : ℕ) (x : QuantumGroup R 𝕧) :
    barHom R (qDivPow (𝕧 ^ d) n x) = qDivPow (𝕧 ^ d) n (barHom R x) := by
  rw [qDivPow, qDivPow, barHom_smul, bar_inv_qFactorial, map_pow]

namespace Modified

theorem barHom_fPow (w : List (I × ℕ)) : barHom R (fPow R w) = fPow R w := by
  induction w with
  | nil => simp
  | cons p w ih => rw [fPow_cons, _root_.map_mul, barHom_qDivPow, barHom_F, ih]

theorem barHom_ePow (w : List (I × ℕ)) : barHom R (ePow R w) = ePow R w := by
  induction w with
  | nil => simp
  | cons p w ih => rw [ePow_cons, _root_.map_mul, barHom_qDivPow, barHom_E, ih]

/-- The `𝒜`-span of the `F_w E_{w'}` is stable under the bar involution. -/
theorem barHom_mem_fePowSpan {u : QuantumGroup R 𝕧} (hu : u ∈ fePowSpan R) :
    barHom R u ∈ fePowSpan R := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, _, ⟨w, w', rfl⟩, rfl⟩ := hx
    rw [barHom_smul, bar_zpow_X, _root_.map_mul, barHom_fPow, barHom_ePow]
    exact zpow_smul_mem_laurentSpan _ (mem_laurentSpan_of_mem ⟨w, w', rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_zsmul]; exact zsmul_mem hx c

end Modified

/-! ### Verma modules -/

namespace VermaModule

variable (R) (Λ : Y →+ ℤ)

/-- The bar involution of `U` as a `bar`-semilinear map. -/
def barSemilinear : QuantumGroup R 𝕧 →ₛₗ[barHom R] QuantumGroup R 𝕧 where
  toFun := barHom R
  map_add' := map_add _
  map_smul' := map_mul _

lemma vermaIdeal_le_comap_bar :
    vermaIdeal R 𝕧 Λ ≤ (vermaIdeal R 𝕧 Λ).comap (barSemilinear R) := by
  refine Submodule.span_le.2 ?_
  rintro _ (⟨i, rfl⟩ | ⟨μ, rfl⟩)
  · change barHom R (E R 𝕧 i) ∈ vermaIdeal R 𝕧 Λ
    rw [barHom_E]
    exact Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  · change barHom R (K R 𝕧 μ - algebraMap 𝕂 _ (𝕧 ^ Λ μ)) ∈ vermaIdeal R 𝕧 Λ
    rw [map_sub, barHom_K, barHom_algebraMap, bar_zpow_X, ← map_neg]
    exact Submodule.subset_span (Or.inr ⟨-μ, rfl⟩)

/-- The bar involution `m ↦ m̄` of the Verma module `M_Λ = U ⧸ (Σᵢ U Eᵢ + Σ_μ U (K_μ -
v^{⟨μ,Λ⟩}))`, induced by the bar involution of `U` ([Lus] 24.1.4). -/
def bar : VermaModule R 𝕧 Λ →+ VermaModule R 𝕧 Λ :=
  ((vermaIdeal R 𝕧 Λ).mapQ (vermaIdeal R 𝕧 Λ) (barSemilinear R)
    (vermaIdeal_le_comap_bar R Λ)).toAddMonoidHom

variable {R Λ}

@[simp] lemma bar_mk (u : QuantumGroup R 𝕧) :
    bar R Λ (Submodule.Quotient.mk u) = Submodule.Quotient.mk (barHom R u) := rfl

lemma bar_smul (u : QuantumGroup R 𝕧) (m : VermaModule R 𝕧 Λ) :
    bar R Λ (u • m) = barHom R u • bar R Λ m := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, bar_mk, bar_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
    smul_eq_mul, map_mul]

@[simp] lemma bar_bar (m : VermaModule R 𝕧 Λ) : bar R Λ (bar R Λ m) = m := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [bar_mk, bar_mk, barHom_barHom]

@[simp] lemma bar_hwv : bar R Λ (hwv R 𝕧 Λ) = hwv R 𝕧 Λ := by
  rw [hwv, bar_mk, map_one]

/-- For `x ∈ 'f_μ`, `x' ∈ 'f_ν` with `ν ≰ μ`, `x'⁺ (x⁻ η) = 0`. -/
lemma plusHom_smul_toVerma_eq_zero {μ ν : I →₀ ℕ} (hμν : ¬ ν ≤ μ) {x : LusztigF 𝕂 I}
    (hx : x ∈ LusztigF.weightSpace 𝕂 μ) {x' : LusztigF 𝕂 I}
    (hx' : x' ∈ LusztigF.weightSpace 𝕂 ν) :
    plusHom R 𝕧 x' • toVerma R 𝕧 Λ x = 0 := by
  induction hx' using FreeAlgebra.wordSpan_induction with
  | word w hw =>
    rw [plusHom_smul_toVerma ratFunc_X_not_root,
      (LusztigF.vermaWordOp_mem _ w.reverse hx).2 (by rwa [wordWeight_reverse, hw]), map_zero]
  | zero => rw [map_zero, zero_smul]
  | add y z _ _ hy hz => rw [map_add, add_smul, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, smul_assoc, hy, smul_zero]

variable [Finite I]

variable (R Λ) in
/-- The Verma module `M_Λ` has the finiteness property of [Lus] 3.4.7: `x⁺ m = 0` for
`x ∈ f_ν` with `tr ν` large. -/
theorem isPlusLocallyNilpotent : IsPlusLocallyNilpotent R (VermaModule R 𝕧 Λ) := by
  intro m
  obtain ⟨y, rfl⟩ := toVerma_surjective (Λ := Λ) ratFunc_X_not_root m
  have hy : y ∈ ⨆ μ, LusztigF.weightSpace 𝕂 (I := I) μ := by
    rw [LusztigF.iSup_weightSpace]; trivial
  induction hy using Submodule.iSup_induction' with
  | mem μ y hy =>
    refine ⟨μ.degree + 1, fun ν hν x hx ↦ ?_⟩
    obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hx
    rw [AlgHom.toLinearMap_apply, quotientPlus_toQuotient]
    refine plusHom_smul_toVerma_eq_zero (fun hle ↦ ?_) hy hx₀
    have := Finsupp.degree_mono hle
    omega
  | zero => exact ⟨0, fun _ _ x _ ↦ by rw [map_zero, smul_zero]⟩
  | add y z _ _ hy hz =>
    obtain ⟨N, hN⟩ := hy
    obtain ⟨N', hN'⟩ := hz
    exact ⟨max N N', fun ν hν x hx ↦ by
      rw [map_add, smul_add, hN ν (le_of_max_le_left hν) x hx,
        hN' ν (le_of_max_le_right hν) x hx, add_zero]⟩

end VermaModule

/-! ### [Lus] 24.1.4 -/

namespace Modified

variable {Λ Λ' : Y →+ ℤ}

local notation "Mt" => ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ)

local notation "VT" =>
  TensorModule 𝕂 (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ)) (VermaModule R 𝕧 Λ')

local notation "tw" => ChevalleyTwist.toTwist R 𝕧 (VermaModule R 𝕧 Λ)

local notation "mkT" =>
  TensorModule.mk (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ)) (VermaModule R 𝕧 Λ')

variable (R Λ) in
/-- The bar involution of `ʷM_Λ`. -/
def twistBar : Mt →+ Mt :=
  (tw).toAddMonoidHom.comp ((VermaModule.bar R Λ).comp (tw).symm.toAddMonoidHom)

lemma twistBar_toTwist (m : VermaModule R 𝕧 Λ) :
    twistBar R Λ (tw m) = tw (VermaModule.bar R Λ m) :=
  rfl

lemma twistBar_smul (u : QuantumGroup R 𝕧) (m : Mt) :
    twistBar R Λ (u • m) = barHom R u • twistBar R Λ m := by
  obtain ⟨m, rfl⟩ := (tw).surjective m
  rw [ChevalleyTwist.smul_toTwist, twistBar_toTwist, VermaModule.bar_smul, barHom_chevalley,
    twistBar_toTwist, ChevalleyTwist.smul_toTwist]

variable (R Λ Λ') in
/-- The map `¯ ⊗ ¯` on `ʷM_Λ ⊗ M_{Λ'}` ([Lus] 24.1.4). -/
def vermaBarPair : Mt ⊗[𝕂] VermaModule R 𝕧 Λ' →+ Mt ⊗[𝕂] VermaModule R 𝕧 Λ' :=
  barPair (twistBar R Λ) (VermaModule.bar R Λ') twistBar_smul VermaModule.bar_smul

lemma vermaBarPair_tmul (a : Mt) (b : VermaModule R 𝕧 Λ') :
    vermaBarPair R Λ Λ' (a ⊗ₜ[𝕂] b) = twistBar R Λ a ⊗ₜ[𝕂] VermaModule.bar R Λ' b := rfl

lemma vermaBarPair_smul (c : 𝕂) (z : Mt ⊗[𝕂] VermaModule R 𝕧 Λ') :
    vermaBarPair R Λ Λ' (c • z) = RatFunc.bar c • vermaBarPair R Λ Λ' z := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
  | tmul a b =>
    rw [smul_tmul', vermaBarPair_tmul, vermaBarPair_tmul,
      map_smul_of_barHom (twistBar R Λ) twistBar_smul, smul_tmul']

@[simp] lemma vermaBarPair_vermaBarPair (z : Mt ⊗[𝕂] VermaModule R 𝕧 Λ') :
    vermaBarPair R Λ Λ' (vermaBarPair R Λ Λ' z) = z := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul a b =>
    obtain ⟨a, rfl⟩ := (tw).surjective a
    rw [vermaBarPair_tmul, vermaBarPair_tmul, twistBar_toTwist, twistBar_toTwist,
      VermaModule.bar_bar, VermaModule.bar_bar]

/-- `¯ ⊗ ¯` fixes the generators `F_w ξ ⊗ F_{w'} η` of the lattice. -/
lemma vermaBarPair_fPow (w w' : List (I × ℕ)) :
    vermaBarPair R Λ Λ' (tw (fPow R w • VermaModule.hwv R 𝕧 Λ) ⊗ₜ[𝕂]
      (fPow R w' • VermaModule.hwv R 𝕧 Λ')) =
      tw (fPow R w • VermaModule.hwv R 𝕧 Λ) ⊗ₜ[𝕂] (fPow R w' • VermaModule.hwv R 𝕧 Λ') := by
  rw [vermaBarPair_tmul, twistBar_toTwist, VermaModule.bar_smul, VermaModule.bar_smul,
    barHom_fPow, barHom_fPow, VermaModule.bar_hwv, VermaModule.bar_hwv]

/-- `¯ ⊗ ¯` preserves `ʷ𝒜M_Λ ⊗_𝒜 𝒜M_{Λ'}`. -/
lemma vermaBarPair_mem {z : VT} (hz : z ∈ vermaTensorLattice R Λ Λ') :
    mkT (vermaBarPair R Λ Λ' ((mkT).symm z)) ∈ vermaTensorLattice R Λ Λ' := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, _, ⟨w, w', rfl⟩, rfl⟩ := hx
    rw [map_smul, vermaBarPair_smul, bar_zpow_X, map_smul]
    refine zpow_smul_mem_laurentSpan _ (mem_laurentSpan_of_mem ⟨w, w', ?_⟩)
    exact congrArg mkT (vermaBarPair_fPow w w')
  | zero => rw [map_zero, map_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, map_add, map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_zsmul, map_zsmul, map_zsmul]; exact zsmul_mem hx c

variable [Finite I]

/-- `Θ (ξ ⊗ η) = ξ ⊗ η`. -/
lemma quasiRAct_hwv :
    quasiRAct (VermaModule.isPlusLocallyNilpotent R Λ')
      (tw (VermaModule.hwv R 𝕧 Λ) ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ') =
      tw (VermaModule.hwv R 𝕧 Λ) ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ' := by
  rw [quasiRAct_apply,
    finsum_eq_single _ 0 fun ν hν ↦ actPair_quasiR_tmul_eq_zero (fun x hx ↦ ?_) _,
    quasiR_zero, _root_.map_one, Module.End.one_apply]
  obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hx
  rw [AlgHom.toLinearMap_apply, quotientPlus_toQuotient, VermaModule.plusHom_smul_hwv,
    LusztigF.counit_eq_zero_of_mem hν hx₀, zero_smul]

omit [Finite I] in
/-- The `𝒜`-span of the `F_w E_{w'}` maps `ξ ⊗ η` into the lattice. -/
lemma fePowImage_le_vermaTensorLattice : fePowImage R Λ Λ' ≤ vermaTensorLattice R Λ Λ' := by
  rintro _ hz
  obtain ⟨u, hu, rfl⟩ := mem_fePowImage.1 hz
  clear hz
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, _, ⟨w, w', rfl⟩, rfl⟩ := hx
    rw [smul_assoc]
    exact zpow_smul_mem_laurentSpan k (fPow_mul_ePow_smul_mem w w')
  | zero => rw [zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_assoc]; exact zsmul_mem hx c

/-- **[Lus] Proposition 24.1.4**: the quasi-R-matrix `Θ` on `ʷM_Λ ⊗ M_{Λ'}` ([Lus] 24.1.1;
`M_{Λ'}` has the property of [Lus] 3.4.7 by `VermaModule.isPlusLocallyNilpotent`) leaves stable
the `𝒜`-submodule `ʷ𝒜M_Λ ⊗_𝒜 𝒜M_{Λ'}`. Lusztig works over `ℚ(v)` with `𝒜 = ℤ[v, v⁻¹]`, as
here. -/
theorem quasiRAct_mem_vermaTensorLattice {z : VT} (hz : z ∈ vermaTensorLattice R Λ Λ') :
    mkT (quasiRAct (VermaModule.isPlusLocallyNilpotent R Λ') ((mkT).symm z)) ∈
      vermaTensorLattice R Λ Λ' := by
  obtain ⟨u', hu', e⟩ :=
    mem_fePowImage.1 (vermaTensorLattice_le_fePowImage (vermaBarPair_mem hz))
  have hz' :
      (mkT).symm z = vermaBarPair R Λ Λ' ((mkT).symm (u' • vermaTensorHwv R 𝕧 Λ Λ')) := by
    rw [e, LinearEquiv.symm_apply_apply, vermaBarPair_vermaBarPair]
  have key : TensorModule.act R 𝕧 _ _ (barHom R u') (quasiRAct
      (VermaModule.isPlusLocallyNilpotent R Λ') (vermaBarPair R Λ Λ'
        (tw (VermaModule.hwv R 𝕧 Λ) ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ'))) =
      quasiRAct (VermaModule.isPlusLocallyNilpotent R Λ') (vermaBarPair R Λ Λ'
        (TensorModule.act R 𝕧 _ _ u' (tw (VermaModule.hwv R 𝕧 Λ) ⊗ₜ[𝕂]
          VermaModule.hwv R 𝕧 Λ'))) := by
    have h := act_quasiRAct_barPair (twistBar R Λ) (VermaModule.bar R Λ') twistBar_smul
      VermaModule.bar_smul (VermaModule.isPlusLocallyNilpotent R Λ') (barHom R u')
      (tw (VermaModule.hwv R 𝕧 Λ) ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ')
    rw [barHom_barHom] at h
    exact h
  rw [vermaBarPair_tmul, twistBar_toTwist, VermaModule.bar_hwv, VermaModule.bar_hwv,
    quasiRAct_hwv] at key
  rw [hz']
  change mkT (quasiRAct _ (vermaBarPair R Λ Λ' (TensorModule.act R 𝕧 _ _ u'
    (tw (VermaModule.hwv R 𝕧 Λ) ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ')))) ∈ _
  rw [← key]
  exact fePowImage_le_vermaTensorLattice
    (mem_fePowImage.2 ⟨_, barHom_mem_fePowSpan hu', rfl⟩)

end Modified

end LieLean.QuantumGroup
