/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.ModifiedCanonical
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorCanonicalBasis
import LieLean.Algebra.QuantumGroup.YRegular

/-!
# [Lus] Thm. 25.2.1 (a), (b) without large dominant weights

`ModifiedCanonical.lean` proves [Lus] Thm. 25.2.1 for root data with arbitrarily large dominant
weights (`hY`), and constructs `Modified.columnCanonical` for every `X`-regular root datum by
transport from the free-coroot datum `freeCoroot R`. Here we prove that the transported elements
satisfy the defining properties (a), (b) of 25.2.1 for every `X`-regular root datum, with no `hY`:
`(b ◇_ζ b'')(ξ_{-λ} ⊗ η_{λ''}) = (b ◇ b'')_{λ,λ''}` for all dominant `λ, λ''` with `λ'' - λ = ζ`,
`b ∈ B(λ)`, `b'' ∈ B(λ'')`, and `= 0` if `b ∉ B(λ)` or `b'' ∉ B(λ'')`.

Without `hY`, these properties do not determine `b ◇_ζ b''` (see the module docstring of
`ModifiedCanonical.lean` for a counterexample in type affine `A₁`), so the uniqueness part of
25.2.1 (a) keeps `hY`. For `Y` free of finite rank, `hY` follows from `Y`-regularity
(`LusztigCartanDatum.RootDatum.exists_le_coroot_of_isYRegular`), so Lusztig's statement holds
as printed (`existsUnique_modifiedCanonical_of_isYRegular`).

## Main results

* `hwMap_smul`: for a morphism of root data `φ : R → R'` and dominant weights with
  `λ = λ' ∘ φ`, the isomorphism `Λ_λ ≃ Λ_{λ'}`, `y⁻ξ ↦ y⁻ξ'`, intertwines `u` and `φ(u)`;
* `pairMap_tensorPsi`, `pairMap_tensorCanonical`: the induced isomorphism
  `ʷΛ_λ ⊗ Λ_{λ''} ≃ ʷΛ_{λ'} ⊗ Λ_{λ'''}` intertwines the involutions `Ψ` of [Lus] 24.3.2 and maps
  `(b ◇ b'')_{λ,λ''}` to `(b ◇ b'')_{λ',λ'''}` ([Lus] 24.3.3);
* `modTensorAct_columnCanonical`, `modTensorAct_columnCanonical_eq_zero`: **[Lus] Thm. 25.2.1
  (a), (b)** for `columnCanonical`, for every `X`-regular root datum;
* `existsUnique_modifiedCanonical_of_isYRegular`: **[Lus] Thm. 25.2.1 (a)** with uniqueness,
  for `X`- and `Y`-regular root data with `Y` free of finite rank.

The transfer along `φ` is our own route; Lusztig reduces to the simply connected root datum in
25.2.2.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 24.3.2, 24.3.3, 25.2.1,
  25.2.2.
-/

open TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop LusztigF Modified

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y Y' : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] [AddCommGroup Y']
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {R' : D.RootDatum Y'}
  (hR : R.IsXRegular) (hR' : R'.IsXRegular)

/-! ### Compatibility of `mapHom` with the structure maps of `U` -/

section MapHom

variable (φ : R.Hom R')

omit [Finite I] in
lemma chevalley_mapHom (u : QuantumGroup R 𝕧) :
    chevalley R' 𝕧 (mapHom 𝕧 φ u) = mapHom 𝕧 φ (chevalley R 𝕧 u) := by
  have : (chevalley R' 𝕧).comp (mapHom 𝕧 φ) = (mapHom 𝕧 φ).comp (chevalley R 𝕧) :=
    hom_ext (fun i ↦ by simp) (fun i ↦ by simp) (fun μ ↦ by simp)
  exact DFunLike.congr_fun this u

omit [Finite I] in
lemma comul_mapHom (u : QuantumGroup R 𝕧) :
    comul R' 𝕧 (mapHom 𝕧 φ u) =
      Algebra.TensorProduct.map (mapHom 𝕧 φ) (mapHom 𝕧 φ) (comul R 𝕧 u) := by
  have : (comul R' 𝕧).comp (mapHom 𝕧 φ) =
      (Algebra.TensorProduct.map (mapHom 𝕧 φ) (mapHom 𝕧 φ)).comp (comul R 𝕧) :=
    hom_ext (fun i ↦ by simp [Kt, Hom.map_ktilde]) (fun i ↦ by simp [Hom.map_ktilde])
      (fun μ ↦ by simp)
  exact DFunLike.congr_fun this u

lemma mapHom_quotientMinus (x : Quotient D 𝕧) :
    mapHom 𝕧 φ (quotientMinus R x) = quotientMinus R' x := by
  obtain ⟨y, rfl⟩ := toQuotient_surjective D 𝕧 x
  rw [quotientMinus_toQuotient, quotientMinus_toQuotient]
  induction y using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]
  | grade1 i => simp [minusHom]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | mul a b ha hb => rw [_root_.map_mul, _root_.map_mul, ha, hb, _root_.map_mul]

lemma mapHom_quotientPlus (x : Quotient D 𝕧) :
    mapHom 𝕧 φ (quotientPlus R x) = quotientPlus R' x := by
  obtain ⟨y, rfl⟩ := toQuotient_surjective D 𝕧 x
  rw [quotientPlus_toQuotient, quotientPlus_toQuotient]
  induction y using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]
  | grade1 i => simp [plusHom]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | mul a b ha hb => rw [_root_.map_mul, _root_.map_mul, ha, hb, _root_.map_mul]

/-- `(φ ⊗ φ)(Θ_ν) = Θ_ν`. -/
lemma map_quasiR (ν : I →₀ ℕ) :
    Algebra.TensorProduct.map (mapHom 𝕧 φ) (mapHom 𝕧 φ) (quasiR R ν) = quasiR R' ν := by
  rw [quasiR, quasiR, map_smul]
  congr 1
  induction quasiRTensor D ν using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | tmul a b =>
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    simp only [AlgHom.toLinearMap_apply, mapHom_quotientMinus, mapHom_quotientPlus]

end MapHom

/-! ### Transfer of `Λ_λ` along a morphism of root data -/

section HighestWeight

omit [Finite I] in
/-- `Eᵢ Fⱼ x = Fⱼ Eᵢ x + δᵢⱼ (K̃ᵢ x - K̃₋ᵢ x)/(vᵢ - vᵢ⁻¹)` on `Λ_λ`. -/
lemma E_smul_F_smul_hw {Z : Type*} [AddCommGroup Z] {R₀ : D.RootDatum Z} (Λ₀ : Z →+ ℤ)
    (i j : I) (x : IrreducibleModule R₀ 𝕧 Λ₀) :
    E R₀ 𝕧 i • F R₀ 𝕧 j • x = F R₀ 𝕧 j • E R₀ 𝕧 i • x + (if i = j then
      (𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹)⁻¹ • (Kt R₀ 𝕧 i • x - K R₀ 𝕧 (-ktilde R₀ i) • x) else 0) := by
  rw [← mul_smul, ← mul_smul, ← sub_eq_iff_eq_add', ← sub_smul, E_mul_F_sub]
  split_ifs
  · rw [smul_assoc, sub_smul]
  · rw [zero_smul]

variable {φ : R.Hom R'} {Λ : Dom R} {Λ' : Dom R'} (hΛ : Λ.1 = Λ'.1.comp φ.toHom)

include hΛ in
omit [Finite I] [DecidableEq I] in
lemma coroot_eq_of_comp (i : I) : Λ'.1 (R'.coroot i) = Λ.1 (R.coroot i) := by
  rw [hΛ, AddMonoidHom.comp_apply, φ.map_coroot]

/-- For `λ = λ' ∘ φ`, the isomorphism `Λ_λ ≃ Λ_{λ'}`, `y⁻ξ ↦ y⁻ξ'` (`hwTransfer`). -/
def hwMap : IrreducibleModule R 𝕧 Λ.1 ≃ₗ[𝕂] IrreducibleModule R' 𝕧 Λ'.1 :=
  hwTransfer hR hR' (coroot_eq_of_comp hΛ)

lemma hwMap_ev (y : LusztigF 𝕂 I) : hwMap hR hR' hΛ (ev R 𝕧 Λ.1 y) = ev R' 𝕧 Λ'.1 y :=
  hwTransfer_ev hR hR' _ y

lemma hwMap_evq (x : Um D 𝕧) : hwMap hR hR' hΛ (evq hvt Λ x) = evq hvt Λ' x :=
  hwTransfer_evq hR hR' _ x

lemma hwMap_hwv :
    hwMap hR hR' hΛ (IrreducibleModule.hwv R 𝕧 Λ.1) = IrreducibleModule.hwv R' 𝕧 Λ'.1 :=
  hwTransfer_hwv hR hR' _

lemma hwMap_F (i : I) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwMap hR hR' hΛ (F R 𝕧 i • m) = F R' 𝕧 i • hwMap hR hR' hΛ m :=
  hwTransfer_F hR hR' _ i m

lemma hwMap_K (μ : Y) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwMap hR hR' hΛ (K R 𝕧 μ • m) = K R' 𝕧 (φ.toHom μ) • hwMap hR hR' hΛ m := by
  induction m using hw_induction with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
  | smul c a ha => rw [smul_comm, LinearEquiv.map_smul, ha, LinearEquiv.map_smul, smul_comm]
  | hwv =>
    rw [hw_K_smul_hwv, LinearEquiv.map_smul, hwMap_hwv, hw_K_smul_hwv, hΛ,
      AddMonoidHom.comp_apply]
  | F i a ha =>
    rw [← mul_smul, K_mul_F, smul_assoc, mul_smul, LinearEquiv.map_smul, hwMap_F, ha, hwMap_F,
      ← mul_smul (K R' 𝕧 _), K_mul_F, smul_assoc, mul_smul, φ.root_map]

lemma hwMap_E (i : I) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwMap hR hR' hΛ (E R 𝕧 i • m) = E R' 𝕧 i • hwMap hR hR' hΛ m := by
  induction m using hw_induction with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
  | smul c a ha => rw [smul_comm, LinearEquiv.map_smul, ha, LinearEquiv.map_smul, smul_comm]
  | hwv =>
    rw [IrreducibleModule.E_smul_hwv, map_zero, hwMap_hwv, IrreducibleModule.E_smul_hwv]
  | F j a ha =>
    rw [E_smul_F_smul_hw, map_add, hwMap_F, ha, hwMap_F, E_smul_F_smul_hw]
    congr 1
    split_ifs
    · rw [LinearEquiv.map_smul, map_sub, Kt, hwMap_K, hwMap_K, map_neg, Hom.map_ktilde]
    · rw [map_zero]

/-- `hwMap` intertwines `u ∈ U(R)` with `φ(u) ∈ U(R')`. -/
theorem hwMap_smul (u : QuantumGroup R 𝕧) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwMap hR hR' hΛ (u • m) = mapHom 𝕧 φ u • hwMap hR hR' hΛ m := by
  induction u using QuantumGroup.induction_on generalizing m with
  | algebraMap c =>
    rw [algebraMap_smul, LinearEquiv.map_smul, AlgHom.commutes, algebraMap_smul]
  | E i => rw [hwMap_E, mapHom_E]
  | F i => rw [hwMap_F, mapHom_F]
  | K μ => rw [hwMap_K, mapHom_K]
  | add x y hx hy => rw [add_smul, map_add, hx, hy, map_add, add_smul]
  | mul x y hx hy => rw [mul_smul, hx, hy, _root_.map_mul, mul_smul]

lemma hwMap_hwBar (m : IrreducibleModule R 𝕧 Λ.1) :
    hwMap hR hR' hΛ (hwBar hR Λ m) = hwBar hR' Λ' (hwMap hR hR' hΛ m) := by
  obtain ⟨y, rfl⟩ := ev_surjective Λ m
  rw [hwBar_ev, hwMap_ev, hwMap_ev, hwBar_ev]

/-- `hwMap` on the twisted modules `ʷΛ_λ ≃ ʷΛ_{λ'}`. -/
def twMap : TwL Λ ≃ₗ[𝕂] TwL Λ' :=
  (ChevalleyTwist.toTwist R 𝕧 _).symm ≪≫ₗ hwMap hR hR' hΛ ≪≫ₗ ChevalleyTwist.toTwist R' 𝕧 _

lemma twMap_toTwist (m : IrreducibleModule R 𝕧 Λ.1) :
    twMap hR hR' hΛ (ChevalleyTwist.toTwist R 𝕧 _ m) =
      ChevalleyTwist.toTwist R' 𝕧 _ (hwMap hR hR' hΛ m) :=
  rfl

lemma twMap_smul (u : QuantumGroup R 𝕧) (m : TwL Λ) :
    twMap hR hR' hΛ (u • m) = mapHom 𝕧 φ u • twMap hR hR' hΛ m := by
  obtain ⟨m, rfl⟩ := (ChevalleyTwist.toTwist R 𝕧 _).surjective m
  rw [ChevalleyTwist.smul_toTwist, twMap_toTwist, hwMap_smul, twMap_toTwist,
    ChevalleyTwist.smul_toTwist, chevalley_mapHom]

lemma twMap_twBar (m : TwL Λ) :
    twMap hR hR' hΛ (twBar hR Λ m) = twBar hR' Λ' (twMap hR hR' hΛ m) := by
  obtain ⟨m, rfl⟩ := (ChevalleyTwist.toTwist R 𝕧 _).surjective m
  rw [twBar_toTwist, twMap_toTwist, hwMap_hwBar, twMap_toTwist, twBar_toTwist]

end HighestWeight

/-! ### Transfer of `ʷΛ_λ ⊗ Λ_{λ''}` -/

section Tensor

variable {φ : R.Hom R'} {Λ Λ₂ : Dom R} {Λ' Λ₂' : Dom R'} (hΛ : Λ.1 = Λ'.1.comp φ.toHom)
  (hΛ₂ : Λ₂.1 = Λ₂'.1.comp φ.toHom)

/-- The isomorphism `ʷΛ_λ ⊗ Λ_{λ₂} ≃ ʷΛ_{λ'} ⊗ Λ_{λ₂'}` induced by `hwMap`. -/
def pairMap : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ₂.1 ≃ₗ[𝕂]
    TwL Λ' ⊗[𝕂] IrreducibleModule R' 𝕧 Λ₂'.1 :=
  TensorProduct.congr (twMap hR hR' hΛ) (hwMap hR hR' hΛ₂)

lemma pairMap_tmul (x : TwL Λ) (y : IrreducibleModule R 𝕧 Λ₂.1) :
    pairMap hR hR' hΛ hΛ₂ (x ⊗ₜ[𝕂] y) = twMap hR hR' hΛ x ⊗ₜ[𝕂] hwMap hR hR' hΛ₂ y :=
  rfl

lemma pairMap_actPair (t : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧)
    (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ₂.1) :
    pairMap hR hR' hΛ hΛ₂ (TensorModule.actPair R 𝕧 _ _ t z) =
      TensorModule.actPair R' 𝕧 _ _ (Algebra.TensorProduct.map (mapHom 𝕧 φ) (mapHom 𝕧 φ) t)
        (pairMap hR hR' hΛ hΛ₂ z) := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      rw [TensorModule.act_tmul, pairMap_tmul, pairMap_tmul, Algebra.TensorProduct.map_tmul,
        TensorModule.act_tmul, twMap_smul, hwMap_smul]

lemma pairMap_act (u : QuantumGroup R 𝕧) (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ₂.1) :
    pairMap hR hR' hΛ hΛ₂ (TensorModule.act R 𝕧 _ _ u z) =
      TensorModule.act R' 𝕧 _ _ (mapHom 𝕧 φ u) (pairMap hR hR' hΛ hΛ₂ z) := by
  simp only [TensorModule.act, AlgHom.comp_apply]
  rw [pairMap_actPair, comul_mapHom]

lemma pairMap_quasiRAct (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ₂.1) :
    pairMap hR hR' hΛ hΛ₂ (quasiRAct (isPlusLocallyNilpotent_hw Λ₂) z) =
      quasiRAct (isPlusLocallyNilpotent_hw Λ₂') (pairMap hR hR' hΛ hΛ₂ z) := by
  rw [quasiRAct_apply, quasiRAct_apply,
    map_finsum (pairMap hR hR' hΛ hΛ₂) (support_quasiR_finite (isPlusLocallyNilpotent_hw Λ₂) z)]
  exact finsum_congr fun ν ↦ by rw [pairMap_actPair, map_quasiR]

lemma pairMap_barPair (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ₂.1) :
    pairMap hR hR' hΛ hΛ₂ (barPair (twBar hR Λ) (hwBar hR Λ₂).toAddMonoidHom
      (twBar_smul_U hR Λ) (hwBar_smul_U' hR Λ₂) z) =
      barPair (twBar hR' Λ') (hwBar hR' Λ₂').toAddMonoidHom (twBar_smul_U hR' Λ')
        (hwBar_smul_U' hR' Λ₂') (pairMap hR hR' hΛ hΛ₂ z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul x y =>
    rw [barPair_tmul, pairMap_tmul, pairMap_tmul, barPair_tmul, twMap_twBar]
    exact congrArg _ (hwMap_hwBar hR hR' hΛ₂ y)

/-- `pairMap` intertwines the involutions `Ψ` of [Lus] 24.3.2. -/
theorem pairMap_tensorPsi (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ₂.1) :
    pairMap hR hR' hΛ hΛ₂ (tensorPsi hR Λ Λ₂ z) =
      tensorPsi hR' Λ' Λ₂' (pairMap hR hR' hΛ hΛ₂ z) := by
  rw [tensorPsi_apply, tensorPsi_apply, pairMap_quasiRAct, pairMap_barPair]

/-- The identification of the index sets `B(λ) × B(λ₂)` and `B(λ') × B(λ₂')`. -/
def idxMap : TensorIdx Λ Λ₂ ≃ TensorIdx Λ' Λ₂' :=
  tensorIdxEquiv (coroot_eq_of_comp hΛ) (coroot_eq_of_comp hΛ₂)

lemma pairMap_tensorBasisIdx (p : TensorIdx Λ Λ₂) :
    pairMap hR hR' hΛ hΛ₂ (tensorBasisIdx hR Λ Λ₂ p) =
      tensorBasisIdx hR' Λ' Λ₂' (idxMap hΛ hΛ₂ p) := by
  have key : ∀ q : canonicalBasisHW D Λ × canonicalBasisHW D Λ₂,
      pairMap hR hR' hΛ hΛ₂ (tensorBasis hR Λ Λ₂ q) =
        tensorBasis hR' Λ' Λ₂'
          (tensorIdxEquiv (coroot_eq_of_comp hΛ) (coroot_eq_of_comp hΛ₂) q) := fun q ↦ by
    rw [tensorBasis_apply, tensorBasis_apply, pairMap_tmul, twMap_toTwist, hwMap_evq, hwMap_evq]
    rfl
  exact key p

lemma repr_pairMap (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ₂.1) (p : TensorIdx Λ Λ₂) :
    (tensorBasisIdx hR' Λ' Λ₂').repr (pairMap hR hR' hΛ hΛ₂ z) (idxMap hΛ hΛ₂ p) =
      (tensorBasisIdx hR Λ Λ₂).repr z p := by
  have hb : ((tensorBasisIdx hR Λ Λ₂).map (pairMap hR hR' hΛ hΛ₂)).reindex (idxMap hΛ hΛ₂) =
      tensorBasisIdx hR' Λ' Λ₂' :=
    Module.Basis.eq_of_apply_eq fun q ↦ by
      rw [Module.Basis.reindex_apply, Module.Basis.map_apply, pairMap_tensorBasisIdx,
        Equiv.apply_symm_apply]
  rw [← hb, Module.Basis.repr_reindex_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, Equiv.symm_apply_apply]

lemma pairMap_mem_tensorLat {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ₂.1}
    (hz : z ∈ tensorLat hR Λ Λ₂) : pairMap hR hR' hΛ hΛ₂ z ∈ tensorLat hR' Λ' Λ₂' := fun h' ↦ by
  obtain ⟨p, rfl⟩ := (idxMap hΛ hΛ₂).surjective h'
  rw [repr_pairMap]
  exact hz p

/-- The three properties characterizing `(b ◇ b'')_{λ,λ₂}` in [Lus] 24.3.3. -/
lemma tensorCanonical_spec (h : TensorIdx Λ Λ₂) :
    tensorCanonical hR Λ Λ₂ h ∈ tensorLat hR Λ Λ₂ ∧
      tensorPsi hR Λ Λ₂ (tensorCanonical hR Λ Λ₂ h) = tensorCanonical hR Λ Λ₂ h ∧
      𝕧 • (tensorCanonical hR Λ Λ₂ h - tensorBasisIdx hR Λ Λ₂ h) ∈ tensorLat hR Λ Λ₂ := by
  classical
  refine ⟨by simpa using smul_tensorCanonical_mem_tensorLat hR Λ Λ₂ isIntInv_one h,
    tensorPsi_tensorCanonical hR Λ Λ₂ h, ?_⟩
  rw [smul_mem_tensorLat_iff]
  intro h'
  rw [map_sub, Finsupp.sub_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hh : h = h'
  · subst hh
    simp only [↓reduceIte, repr_tensorCanonical_self, sub_self]
    exact isNegLaurent_zero
  · simp only [hh, ↓reduceIte, sub_zero]
    exact isNegLaurent_repr_tensorCanonical hR Λ Λ₂ (Ne.symm hh)

/-- `pairMap` maps `(b ◇ b'')_{λ,λ₂}` to `(b ◇ b'')_{λ',λ₂'}` ([Lus] 24.3.3). -/
theorem pairMap_tensorCanonical (p : TensorIdx Λ Λ₂) :
    pairMap hR hR' hΛ hΛ₂ (tensorCanonical hR Λ Λ₂ p) =
      tensorCanonical hR' Λ' Λ₂' (idxMap hΛ hΛ₂ p) := by
  obtain ⟨h₁, h₂, h₃⟩ := tensorCanonical_spec hR p
  refine (existsUnique_tensorCanonical hR' Λ' Λ₂' (idxMap hΛ hΛ₂ p)).unique
    ⟨pairMap_mem_tensorLat hR hR' hΛ hΛ₂ h₁, ?_, ?_⟩
    (tensorCanonical_spec (R := R') (Λ := Λ') (Λ₂ := Λ₂') hR' _)
  · rw [← pairMap_tensorPsi hR hR' hΛ hΛ₂, h₂]
  · rw [← pairMap_tensorBasisIdx hR hR' hΛ hΛ₂, ← map_sub, ← LinearEquiv.map_smul]
    exact pairMap_mem_tensorLat hR hR' hΛ hΛ₂ h₃

end Tensor

/-! ### [Lus] Thm. 25.2.1 (a), (b) for `columnCanonical` -/

section Column

omit [Finite I] in
lemma Modified.columnEquiv_eq_leftActOne (φ : R.Hom R') (ζ : Y' →+ ℤ)
    {x : LinearMap.range (leftActOne R ratFunc_X_not_root (ζ.comp φ.toHom))}
    {u : QuantumGroup R 𝕧} (hu : (x : Modified R 𝕧) =
      leftActOne R ratFunc_X_not_root (ζ.comp φ.toHom) u) :
    (columnEquiv R R' ratFunc_X_not_root φ ζ x : Modified R' 𝕧) =
      leftActOne R' ratFunc_X_not_root ζ (QuantumGroup.mapHom 𝕧 φ u) := by
  obtain ⟨x, hx⟩ := x
  have : (⟨x, hx⟩ : LinearMap.range (leftActOne R ratFunc_X_not_root (ζ.comp φ.toHom))) =
      ⟨leftActOne R ratFunc_X_not_root (ζ.comp φ.toHom) u, u, rfl⟩ := Subtype.ext hu
  rw [this, columnEquiv_leftActOne]

variable (Λ Λ'' : Dom R)

omit [Finite I] [DecidableEq I] in
lemma domFreeCoroot_eq_comp : (domFreeCoroot Λ).1 = Λ.1.comp R.freeCorootHom.toHom :=
  rfl

/-- `u(ξ_{-λ} ⊗ η_{λ''})` for `columnCanonical`, through the free-coroot datum. -/
lemma modTensorAct_columnCanonical_eq_pairMap (ζ : Y →+ ℤ) {b b'' : Um D 𝕧}
    (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D) (hζ : Λ''.1 - Λ.1 = ζ) :
    modTensorAct Λ Λ'' (columnCanonical hR ζ hb hb'') =
      pairMap (isXRegular_freeCoroot hR) hR (domFreeCoroot_eq_comp Λ)
        (domFreeCoroot_eq_comp Λ'') (modTensorAct (domFreeCoroot Λ) (domFreeCoroot Λ'')
          (modifiedCanonical (isXRegular_freeCoroot hR) exists_dom_freeCoroot
            (ζ.comp R.freeCorootHom.toHom) hb hb'')) := by
  have hR₁ := isXRegular_freeCoroot hR
  obtain ⟨u, hu⟩ := modifiedCanonical_mem_range hR₁ exists_dom_freeCoroot
    (ζ.comp R.freeCorootHom.toHom) hb hb''
  have hc : columnCanonical hR ζ hb hb'' =
      leftActOne R hvn_ratFunc ζ (QuantumGroup.mapHom 𝕧 R.freeCorootHom u) :=
    columnEquiv_eq_leftActOne R.freeCorootHom ζ (u := u) hu.symm
  have hζ₁ : (domFreeCoroot Λ'').1 - (domFreeCoroot Λ).1 = ζ.comp R.freeCorootHom.toHom := by
    rw [← hζ]
    rfl
  rw [hc, ← hu, modTensorAct_leftActOne Λ Λ'' hζ, modTensorAct_leftActOne _ _ hζ₁, pairMap_act,
    pairMap_tmul, twMap_toTwist, hwMap_hwv, hwMap_hwv]

/-- **[Lus] Thm. 25.2.1 (a)** for every `X`-regular root datum, with no `hY`:
`(b ◇_ζ b'')(ξ_{-λ} ⊗ η_{λ''}) = (b ◇ b'')_{λ,λ''}` for `λ'' - λ = ζ`, `b ∈ B(λ)`, `b'' ∈ B(λ'')`,
where `b ◇_ζ b''` is `columnCanonical`. -/
theorem modTensorAct_columnCanonical (ζ : Y →+ ℤ) {b b'' : Um D 𝕧}
    (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D) (hζ : Λ''.1 - Λ.1 = ζ)
    (h₁ : b ∈ canonicalBasisHW D Λ) (h₂ : b'' ∈ canonicalBasisHW D Λ'') :
    modTensorAct Λ Λ'' (columnCanonical hR ζ hb hb'') =
      tensorCanonical hR Λ Λ'' (⟨b, h₁⟩, ⟨b'', h₂⟩) := by
  have hR₁ := isXRegular_freeCoroot hR
  have hζ₁ : (domFreeCoroot Λ'').1 - (domFreeCoroot Λ).1 = ζ.comp R.freeCorootHom.toHom := by
    rw [← hζ]
    rfl
  have e₁ : b ∈ canonicalBasisHW D (domFreeCoroot Λ) := by
    rwa [canonicalBasisHW_eq (coroot_eq_of_comp (domFreeCoroot_eq_comp Λ))] at h₁
  have e₂ : b'' ∈ canonicalBasisHW D (domFreeCoroot Λ'') := by
    rwa [canonicalBasisHW_eq (coroot_eq_of_comp (domFreeCoroot_eq_comp Λ''))] at h₂
  rw [modTensorAct_columnCanonical_eq_pairMap hR Λ Λ'' ζ hb hb'' hζ,
    modTensorAct_modifiedCanonical hR₁ exists_dom_freeCoroot _ hb hb'' _ _ hζ₁ e₁ e₂]
  exact pairMap_tensorCanonical hR₁ hR (domFreeCoroot_eq_comp Λ) (domFreeCoroot_eq_comp Λ'')
    ((⟨b, e₁⟩, ⟨b'', e₂⟩) : TensorIdx _ _)

/-- **[Lus] Thm. 25.2.1 (b)** for every `X`-regular root datum, with no `hY`:
`(b ◇_ζ b'')(ξ_{-λ} ⊗ η_{λ''}) = 0` for `λ'' - λ = ζ` if `b ∉ B(λ)` or `b'' ∉ B(λ'')`. -/
theorem modTensorAct_columnCanonical_eq_zero (ζ : Y →+ ℤ) {b b'' : Um D 𝕧}
    (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D) (hζ : Λ''.1 - Λ.1 = ζ)
    (h : b ∉ canonicalBasisHW D Λ ∨ b'' ∉ canonicalBasisHW D Λ'') :
    modTensorAct Λ Λ'' (columnCanonical hR ζ hb hb'') = 0 := by
  have hR₁ := isXRegular_freeCoroot hR
  have hζ₁ : (domFreeCoroot Λ'').1 - (domFreeCoroot Λ).1 = ζ.comp R.freeCorootHom.toHom := by
    rw [← hζ]
    rfl
  rw [canonicalBasisHW_eq (coroot_eq_of_comp (domFreeCoroot_eq_comp Λ)),
    canonicalBasisHW_eq (coroot_eq_of_comp (domFreeCoroot_eq_comp Λ''))] at h
  rw [modTensorAct_columnCanonical_eq_pairMap hR Λ Λ'' ζ hb hb'' hζ,
    modTensorAct_modifiedCanonical_eq_zero hR₁ exists_dom_freeCoroot _ hb hb'' _ _ hζ₁ h,
    map_zero]

omit [DecidableEq I] in
/-- For `Y` free of finite rank, `Y`-regularity gives the hypothesis `hY` of
`existsUnique_modifiedCanonical`. -/
theorem exists_dom_of_isYRegular [Module.Free ℤ Y] [Module.Finite ℤ Y] (hY : R.IsYRegular)
    (N : ℕ) : ∃ Λ : Dom R, ∀ i, (N : ℤ) ≤ Λ.1 (R.coroot i) := by
  obtain ⟨Λ, hΛ⟩ := LusztigCartanDatum.RootDatum.exists_le_coroot_of_isYRegular hY N
  exact ⟨⟨Λ, fun i ↦ le_trans (Int.natCast_nonneg N) (hΛ i)⟩, hΛ⟩

/-- **[Lus] Thm. 25.2.1 (a)** for `X`- and `Y`-regular root data with `Y` free of finite rank:
for `ζ ∈ X` and `b, b'' ∈ B` there is a unique `u ∈ U̇1_ζ` with
`u(ξ_{-λ} ⊗ η_{λ''}) = (b ◇ b'')_{λ,λ''}` for all dominant `λ, λ''` with `λ'' - λ = ζ`,
`b ∈ B(λ)` and `b'' ∈ B(λ'')`. -/
theorem existsUnique_modifiedCanonical_of_isYRegular [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (hY : R.IsYRegular) (ζ : Y →+ ℤ) {b b'' : Um D 𝕧}
    (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D) :
    ∃! u, u ∈ LinearMap.range (leftActOne R hvn_ratFunc ζ) ∧
      ∀ (Λ Λ'' : Dom R) (_ : Λ''.1 - Λ.1 = ζ) (h₁ : b ∈ canonicalBasisHW D Λ)
        (h₂ : b'' ∈ canonicalBasisHW D Λ''),
        modTensorAct Λ Λ'' u = tensorCanonical hR Λ Λ'' (⟨b, h₁⟩, ⟨b'', h₂⟩) :=
  existsUnique_modifiedCanonical hR (exists_dom_of_isYRegular hY) ζ hb hb''

end Column

end LieLean.QuantumGroup
