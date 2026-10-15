/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.TensorVermaQuasiR

/-!
# The quasi-R-matrix on tensor products of quotients of Verma modules

The quasi-R-matrix `Θ` ([Lus] 24.1.1) is natural for `U`-module maps (`quasiRAct_map`), and
the property of [Lus] 3.4.7 passes to quotients (`IsPlusLocallyNilpotent.of_surjective`). Hence
[Lus] Proposition 24.1.4 descends to quotients `M_Λ ⧸ N`, `M_{Λ'} ⧸ N'` of Verma modules: `Θ`
leaves stable the image of `ʷ𝒜M_Λ ⊗_𝒜 𝒜M_{Λ'}` (`Modified.quasiRAct_mem_quotTensorLattice`).
For `Λ_λ = M_λ ⧸ Σᵢ U Fᵢ^{⟨i,λ⟩+1} η` (`FPowQuotient`) this is **[Lus] Corollary 24.1.5**
(`Modified.quasiRAct_mem_fPowQuotientTensorLattice`).

## Main definitions and results

* `QuantumGroup.quasiRAct_map`: naturality of `Θ`.
* `QuantumGroup.ChevalleyTwist.map`: the twist of a `U`-module map.
* `QuantumGroup.Modified.quotTensorLattice`: the `𝒜`-span of the `F_w ξ ⊗ F_{w'} η` in
  `ʷ(M_Λ ⧸ N) ⊗ (M_{Λ'} ⧸ N')`, the image of `ʷ𝒜M_Λ ⊗_𝒜 𝒜M_{Λ'}`.
* `QuantumGroup.Modified.quasiRAct_mem_fPowQuotientTensorLattice`: **[Lus] Corollary 24.1.5**.

Lusztig assumes the root datum `Y`-regular and `λ, λ'` dominant; the statement here holds for
every root datum and all `λ, λ'`, and for every pair of quotients, e.g. the simple quotients
`IrreducibleModule`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 3.4.7, 24.1.
-/

open LieLean TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)

attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

/-! ### Naturality of `Θ` -/

section Naturality

variable {M₁ M₂ N₁ N₂ : Type*}
  [AddCommGroup M₁] [Module 𝕂 M₁] [Module (QuantumGroup R 𝕧) M₁]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₁]
  [AddCommGroup M₂] [Module 𝕂 M₂] [Module (QuantumGroup R 𝕧) M₂]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂]
  [AddCommGroup N₁] [Module 𝕂 N₁] [Module (QuantumGroup R 𝕧) N₁]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) N₁]
  [AddCommGroup N₂] [Module 𝕂 N₂] [Module (QuantumGroup R 𝕧) N₂]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) N₂]

/-- The tensor product of two `U`-module maps, as a `𝕂`-linear map. -/
abbrev tensorMap (f : M₁ →ₗ[QuantumGroup R 𝕧] N₁) (g : M₂ →ₗ[QuantumGroup R 𝕧] N₂) :
    M₁ ⊗[𝕂] M₂ →ₗ[𝕂] N₁ ⊗[𝕂] N₂ :=
  TensorProduct.map (f.restrictScalars 𝕂) (g.restrictScalars 𝕂)

lemma actPair_tensorMap (f : M₁ →ₗ[QuantumGroup R 𝕧] N₁) (g : M₂ →ₗ[QuantumGroup R 𝕧] N₂)
    (t : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧) (z : M₁ ⊗[𝕂] M₂) :
    TensorModule.actPair R 𝕧 N₁ N₂ t (tensorMap f g z) =
      tensorMap f g (TensorModule.actPair R 𝕧 M₁ M₂ t z) := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, LinearMap.add_apply, ha, hb, map_add, LinearMap.add_apply,
      map_add]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]
    | tmul x y =>
      rw [map_tmul, TensorModule.act_tmul, TensorModule.act_tmul, map_tmul]
      simp

variable [Finite I]

omit [Module 𝕂 M₂] [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂] [Module 𝕂 N₂]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) N₂] in
/-- If `M₂` has the property of [Lus] 3.4.7, so has every quotient of `M₂`. -/
theorem IsPlusLocallyNilpotent.of_surjective (h : IsPlusLocallyNilpotent R M₂)
    (g : M₂ →ₗ[QuantumGroup R 𝕧] N₂) (hg : Function.Surjective g) :
    IsPlusLocallyNilpotent R N₂ := by
  intro n
  obtain ⟨m, rfl⟩ := hg n
  obtain ⟨N, hN⟩ := h m
  exact ⟨N, fun ν hν x hx ↦ by rw [← g.map_smul, hN ν hν x hx, map_zero]⟩

/-- `Θ` commutes with tensor products of `U`-module maps. -/
theorem quasiRAct_map (h : IsPlusLocallyNilpotent R M₂) (h' : IsPlusLocallyNilpotent R N₂)
    (f : M₁ →ₗ[QuantumGroup R 𝕧] N₁) (g : M₂ →ₗ[QuantumGroup R 𝕧] N₂) (z : M₁ ⊗[𝕂] M₂) :
    quasiRAct h' (tensorMap f g z) = tensorMap f g (quasiRAct h z) := by
  rw [quasiRAct_apply, quasiRAct_apply, map_finsum _ (support_quasiR_finite h z)]
  exact finsum_congr fun ν ↦ actPair_tensorMap f g _ z

end Naturality

/-! ### Twisting `U`-module maps -/

namespace ChevalleyTwist

variable {M N : Type*} [AddCommGroup M] [Module 𝕂 M] [Module (QuantumGroup R 𝕧) M]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M]
  [AddCommGroup N] [Module 𝕂 N] [Module (QuantumGroup R 𝕧) N]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) N]

/-- The map `ʷM → ʷN` induced by a `U`-module map `M → N`. -/
def map (f : M →ₗ[QuantumGroup R 𝕧] N) :
    ChevalleyTwist R 𝕧 M →ₗ[QuantumGroup R 𝕧] ChevalleyTwist R 𝕧 N where
  toFun m := toTwist R 𝕧 N (f ((toTwist R 𝕧 M).symm m))
  map_add' a b := by simp
  map_smul' u m := by
    obtain ⟨m, rfl⟩ := (toTwist R 𝕧 M).surjective m
    simp only [smul_toTwist, LinearEquiv.symm_apply_apply, f.map_smul, RingHom.id_apply]

omit [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M] [IsScalarTower 𝕂 (QuantumGroup R 𝕧) N] in
@[simp] lemma map_toTwist (f : M →ₗ[QuantumGroup R 𝕧] N) (m : M) :
    map f (toTwist R 𝕧 M m) = toTwist R 𝕧 N (f m) := by
  simp [map]

end ChevalleyTwist

/-! ### Quotients of Verma modules -/

namespace Modified

variable {Λ Λ' : Y →+ ℤ} (N : Submodule (QuantumGroup R 𝕧) (VermaModule R 𝕧 Λ))
  (N' : Submodule (QuantumGroup R 𝕧) (VermaModule R 𝕧 Λ'))

local notation "VT" =>
  TensorModule 𝕂 (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ)) (VermaModule R 𝕧 Λ')

local notation "QT" =>
  TensorModule 𝕂 (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ ⧸ N)) (VermaModule R 𝕧 Λ' ⧸ N')

local notation "mkT" =>
  TensorModule.mk (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ)) (VermaModule R 𝕧 Λ')

local notation "mkQ" =>
  TensorModule.mk (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ ⧸ N)) (VermaModule R 𝕧 Λ' ⧸ N')

variable (R) in
/-- The `𝒜`-span of the `F_w ξ ⊗ F_{w'} η` in `ʷ(M_Λ ⧸ N) ⊗ (M_{Λ'} ⧸ N')`: the image of
`ʷ𝒜M_Λ ⊗_𝒜 𝒜M_{Λ'}` (for `N`, `N'` the kernels of `M_Λ → Λ_Λ`, `M_{Λ'} → Λ_{Λ'}`, the
`𝒜`-submodule `ʷ(𝒜Λ_Λ) ⊗_𝒜 𝒜Λ_{Λ'}` of [Lus] 24.1.5). -/
def quotTensorLattice : Submodule ℤ QT :=
  laurentSpan {z | ∃ w w' : List (I × ℕ), z = mkQ
    (ChevalleyTwist.toTwist R 𝕧 _ (fPow R w • Submodule.Quotient.mk (VermaModule.hwv R 𝕧 Λ)) ⊗ₜ[𝕂]
      (fPow R w' • Submodule.Quotient.mk (VermaModule.hwv R 𝕧 Λ')))}

/-- The projection `ʷM_Λ ⊗ M_{Λ'} → ʷ(M_Λ ⧸ N) ⊗ (M_{Λ'} ⧸ N')`. -/
abbrev quotTensorProj : VT →ₗ[𝕂] QT :=
  (mkQ).toLinearMap ∘ₗ tensorMap (ChevalleyTwist.map N.mkQ) N'.mkQ ∘ₗ (mkT).symm.toLinearMap

lemma quotTensorProj_mem {z : VT} (hz : z ∈ vermaTensorLattice R Λ Λ') :
    quotTensorProj N N' z ∈ quotTensorLattice R N N' := by
  refine map_mem_laurentSpan _ ?_ hz
  rintro _ ⟨w, w', rfl⟩
  refine mem_laurentSpan_of_mem ⟨w, w', ?_⟩
  simp [quotTensorProj]

lemma quotTensorLattice_le_map :
    quotTensorLattice R N N' ≤
      (vermaTensorLattice R Λ Λ').map (quotTensorProj N N').toAddMonoidHom.toIntLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, _, ⟨w, w', rfl⟩, rfl⟩
  refine ⟨_, zpow_smul_mem_laurentSpan k (mem_laurentSpan_of_mem ⟨w, w', rfl⟩), ?_⟩
  simp [quotTensorProj]

variable [Finite I]

lemma isPlusLocallyNilpotent_quot :
    IsPlusLocallyNilpotent R (VermaModule R 𝕧 Λ' ⧸ N') :=
  (VermaModule.isPlusLocallyNilpotent R Λ').of_surjective N'.mkQ (Submodule.mkQ_surjective N')

/-- **[Lus] Proposition 24.1.4** for quotients of Verma modules: `Θ` on
`ʷ(M_Λ ⧸ N) ⊗ (M_{Λ'} ⧸ N')` leaves stable the image of `ʷ𝒜M_Λ ⊗_𝒜 𝒜M_{Λ'}`. -/
theorem quasiRAct_mem_quotTensorLattice {z : QT} (hz : z ∈ quotTensorLattice R N N') :
    mkQ (quasiRAct (isPlusLocallyNilpotent_quot (R := R) N') ((mkQ).symm z)) ∈
      quotTensorLattice R N N' := by
  obtain ⟨z₀, hz₀, rfl⟩ := quotTensorLattice_le_map N N' hz
  change mkQ (quasiRAct _ (tensorMap (ChevalleyTwist.map N.mkQ) N'.mkQ ((mkT).symm z₀))) ∈ _
  rw [quasiRAct_map (VermaModule.isPlusLocallyNilpotent R Λ')]
  exact quotTensorProj_mem N N' (quasiRAct_mem_vermaTensorLattice hz₀)

variable (Λ Λ') in
/-- **[Lus] Corollary 24.1.5**: for `Λ_λ = M_λ ⧸ Σᵢ U Fᵢ^{⟨i,λ⟩+1} η` (`FPowQuotient`), `Θ` on
`ʷΛ_Λ ⊗ Λ_{Λ'}` leaves stable the `𝒜`-submodule `ʷ(𝒜Λ_Λ) ⊗_𝒜 𝒜Λ_{Λ'}`, the image of
`ʷ𝒜M_Λ ⊗_𝒜 𝒜M_{Λ'}`. Lusztig assumes the root datum `Y`-regular and `Λ, Λ'` dominant; neither is
needed here. -/
theorem quasiRAct_mem_fPowQuotientTensorLattice
    {z : TensorModule 𝕂 (ChevalleyTwist R 𝕧 (FPowQuotient R 𝕧 Λ)) (FPowQuotient R 𝕧 Λ')}
    (hz : z ∈ quotTensorLattice R (VermaModule.fPowSubmodule R 𝕧 Λ)
      (VermaModule.fPowSubmodule R 𝕧 Λ')) :
    TensorModule.mk _ _ (quasiRAct (isPlusLocallyNilpotent_quot (R := R) _)
        ((TensorModule.mk _ _).symm z)) ∈ quotTensorLattice R (VermaModule.fPowSubmodule R 𝕧 Λ)
        (VermaModule.fPowSubmodule R 𝕧 Λ') :=
  quasiRAct_mem_quotTensorLattice _ _ hz

end Modified

end LieLean.QuantumGroup
