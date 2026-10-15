/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorEmbCoordinates

/-!
# [Lus] Prop. 25.1.2 (b) for every `X`-regular root datum

`isIntInv_repr_tensorEmb_evq_of_fund` proves [Lus] Prop. 25.1.2 (b) for root data with
fundamental weights. Here we remove that hypothesis: the module `Λ_λ`, the map
`χ : Λ_{λ+λ'} → Λ_λ ⊗ Λ_{λ'}` and the set `B(λ)` depend only on the pairings `⟨i, λ⟩`, and every
`X`-regular root datum `R` has the same pairings as the root datum `freeCoroot R`, which has
fundamental weights.

## Main results

* `hwTransfer`: for `X`-regular root data `R`, `R'` and dominant weights `λ`, `λ'` with
  `⟨i, λ⟩ = ⟨i, λ'⟩` for all `i`, the linear isomorphism `L_q(λ) ≃ L_q(λ')`, `y⁻ v_λ ↦ y⁻ v_{λ'}`;
  it commutes with the `Fᵢ` and with the `K_{-ĩ}` (`hwTransfer_F`, `hwTransfer_K`);
* `tensorTransfer_tensorEmb_ev`: the induced isomorphism of tensor products intertwines the
  maps `χ`;
* `repr_tensorTransfer`: it preserves the coordinates in the bases `b₁⁻η ⊗ b₂⁻η'`;
* `isIntInv_repr_tensorEmb_evq`: **[Lus] Prop. 25.1.2 (b)**.

The comparison through `freeCoroot R` is our own route; Lusztig proves 25.1.2 (b) directly from
his lattice `ℒ(Λ_λ)` ([Lus] 18.1.4).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 25.1.2.
-/

open TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y Y' : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] [AddCommGroup Y']
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {R' : D.RootDatum Y'}
  (hR : R.IsXRegular) (hR' : R'.IsXRegular)

/-! ### `L_q(λ)` depends only on the pairings `⟨i, λ⟩` -/

section HighestWeight

variable {Λ : Dom R} {Λ' : Dom R'} (h : ∀ i, Λ'.1 (R'.coroot i) = Λ.1 (R.coroot i))

include h in
omit [Finite I] [DecidableEq I] in
lemma sub_rootSum_neg_ktilde (ν : I →₀ ℕ) (i : I) :
    (Λ'.1 - R'.rootSum ν) (-ktilde R' i) = (Λ.1 - R.rootSum ν) (-ktilde R i) := by
  simp only [map_neg, AddMonoidHom.sub_apply, ktilde, map_nsmul, h, rootSum_coroot]

include hR hR' h in
lemma ker_ev_eq_ker_ev : LinearMap.ker (ev R 𝕧 Λ.1) = LinearMap.ker (ev R' 𝕧 Λ'.1) := by
  rw [ker_ev_eq hR Λ, ker_ev_eq hR' Λ']
  simp only [h]

/-- For `⟨i, λ⟩ = ⟨i, λ'⟩` (all `i`), the isomorphism `L_q(λ) ≃ L_q(λ')`, `y⁻ v_λ ↦ y⁻ v_{λ'}`,
of the irreducible modules of two `X`-regular root data. -/
def hwTransfer : IrreducibleModule R 𝕧 Λ.1 ≃ₗ[𝕂] IrreducibleModule R' 𝕧 Λ'.1 :=
  ((ev R 𝕧 Λ.1).quotKerEquivOfSurjective (ev_surjective Λ)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (ker_ev_eq_ker_ev hR hR' h) ≪≫ₗ
    (ev R' 𝕧 Λ'.1).quotKerEquivOfSurjective (ev_surjective Λ')

lemma hwTransfer_ev (y : LusztigF 𝕂 I) :
    hwTransfer hR hR' h (ev R 𝕧 Λ.1 y) = ev R' 𝕧 Λ'.1 y := by
  have h₁ : ((ev R 𝕧 Λ.1).quotKerEquivOfSurjective (ev_surjective Λ)).symm (ev R 𝕧 Λ.1 y) =
      Submodule.Quotient.mk y :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  simp only [hwTransfer, LinearEquiv.trans_apply, h₁, Submodule.quotEquivOfEq_mk]
  rfl

lemma hwTransfer_evq (x : Um D 𝕧) :
    hwTransfer hR hR' h (evq hvt Λ x) = evq hvt Λ' x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [evq_mk, evq_mk, hwTransfer_ev]

lemma hwTransfer_hwv :
    hwTransfer hR hR' h (IrreducibleModule.hwv R 𝕧 Λ.1) = IrreducibleModule.hwv R' 𝕧 Λ'.1 := by
  rw [← ev_one, hwTransfer_ev, ev_one]

lemma hwTransfer_F (i : I) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwTransfer hR hR' h (F R 𝕧 i • m) = F R' 𝕧 i • hwTransfer hR hR' h m := by
  obtain ⟨y, rfl⟩ := ev_surjective Λ m
  rw [← ev_ι_mul, hwTransfer_ev, hwTransfer_ev, ev_ι_mul]

lemma hwTransfer_K (i : I) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwTransfer hR hR' h (K R 𝕧 (-ktilde R i) • m) =
      K R' 𝕧 (-ktilde R' i) • hwTransfer hR hR' h m := by
  obtain ⟨y, rfl⟩ := ev_surjective Λ m
  rw [← sum_weightProj y]
  simp only [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ ↦ ?_
  have hy := FreeAlgebra.weightProj_mem ν y
  rw [ev_mem_weightSpace hvn_ratFunc hR Λ.1 hy (-ktilde R i), map_smul, hwTransfer_ev,
    ev_mem_weightSpace hvn_ratFunc hR' Λ'.1 hy (-ktilde R' i), sub_rootSum_neg_ktilde h]

end HighestWeight

/-! ### Tensor products -/

section Tensor

variable {Λ₁ Λ₂ : Dom R} {Λ₁' Λ₂' : Dom R'} (h₁ : ∀ i, Λ₁'.1 (R'.coroot i) = Λ₁.1 (R.coroot i))
  (h₂ : ∀ i, Λ₂'.1 (R'.coroot i) = Λ₂.1 (R.coroot i))

/-- The isomorphism `L_q(λ₁) ⊗ L_q(λ₂) ≃ L_q(λ₁') ⊗ L_q(λ₂')` induced by `hwTransfer`. -/
def tensorTransfer :
    TensorModule 𝕂 (IrreducibleModule R 𝕧 Λ₁.1) (IrreducibleModule R 𝕧 Λ₂.1) ≃ₗ[𝕂]
      TensorModule 𝕂 (IrreducibleModule R' 𝕧 Λ₁'.1) (IrreducibleModule R' 𝕧 Λ₂'.1) :=
  (TensorModule.mk _ _).symm ≪≫ₗ
    TensorProduct.congr (hwTransfer hR hR' h₁) (hwTransfer hR hR' h₂) ≪≫ₗ TensorModule.mk _ _

lemma tensorTransfer_mk (x : IrreducibleModule R 𝕧 Λ₁.1) (y : IrreducibleModule R 𝕧 Λ₂.1) :
    tensorTransfer hR hR' h₁ h₂ (TensorModule.mk _ _ (x ⊗ₜ[𝕂] y)) =
      TensorModule.mk _ _ (hwTransfer hR hR' h₁ x ⊗ₜ[𝕂] hwTransfer hR hR' h₂ y) :=
  rfl

lemma tensorTransfer_F (i : I)
    (z : TensorModule 𝕂 (IrreducibleModule R 𝕧 Λ₁.1) (IrreducibleModule R 𝕧 Λ₂.1)) :
    tensorTransfer hR hR' h₁ h₂ (F R 𝕧 i • z) = F R' 𝕧 i • tensorTransfer hR hR' h₁ h₂ z := by
  obtain ⟨z, rfl⟩ := (TensorModule.mk _ _).surjective z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorModule.F_smul_tmul, tensorTransfer_mk, TensorModule.F_smul_tmul]
    simp only [map_add, tensorTransfer_mk, hwTransfer_F, hwTransfer_K]
  | add a b ha hb => simp only [map_add, smul_add, ha, hb]

/-- The isomorphism `tensorTransfer` intertwines `χ : Λ_{λ₁+λ₂} → Λ_{λ₁} ⊗ Λ_{λ₂}` with the
corresponding map for `R'`. -/
theorem tensorTransfer_tensorEmb_ev (y : LusztigF 𝕂 I) :
    tensorTransfer hR hR' h₁ h₂ (tensorEmb hvt hR Λ₁.2 Λ₂.2 (ev R 𝕧 (Λ₁ + Λ₂).1 y)) =
      tensorEmb hvt hR' Λ₁'.2 Λ₂'.2 (ev R' 𝕧 (Λ₁' + Λ₂').1 y) := by
  let P : LusztigF 𝕂 I → Prop := fun y ↦
    tensorTransfer hR hR' h₁ h₂ (tensorEmb hvt hR Λ₁.2 Λ₂.2 (ev R 𝕧 (Λ₁ + Λ₂).1 y)) =
      tensorEmb hvt hR' Λ₁'.2 Λ₂'.2 (ev R' 𝕧 (Λ₁' + Λ₂').1 y)
  have hP1 : P 1 := by
    simp only [P, ev_one]
    erw [tensorEmb_hwv, tensorEmb_hwv]
    rw [tensorTransfer_mk, hwTransfer_hwv, hwTransfer_hwv]
  have hPadd : ∀ a b, P a → P b → P (a + b) := fun a b ha hb ↦ by
    simp only [P, map_add] at ha hb ⊢
    rw [ha, hb]
  have hPsmul : ∀ (c : 𝕂) a, P a → P (c • a) := fun c a ha ↦ by
    simp only [P, map_smul, LinearMap.map_smul_of_tower] at ha ⊢
    rw [ha]
  have hPι : ∀ j a, P a → P (FreeAlgebra.ι 𝕂 j * a) := fun j a ha ↦ by
    simp only [P, ev_ι_mul, map_smul] at ha ⊢
    rw [tensorTransfer_F, ha]
  have key : ∀ a z, P z → P (a * z) := by
    intro a
    induction a using FreeAlgebra.induction with
    | grade0 c =>
      intro z hz
      rw [← Algebra.smul_def]
      exact hPsmul c z hz
    | grade1 j => exact hPι j
    | mul a b ha hb => intro z hz; rw [mul_assoc]; exact ha _ (hb z hz)
    | add a b ha hb => intro z hz; rw [add_mul]; exact hPadd _ _ (ha z hz) (hb z hz)
  have := key y 1 hP1
  rw [mul_one] at this
  exact this

lemma canonicalBasisHW_eq {Λ : Dom R} {Λ' : Dom R'}
    (h : ∀ i, Λ'.1 (R'.coroot i) = Λ.1 (R.coroot i)) :
    canonicalBasisHW D Λ' = canonicalBasisHW D Λ := by
  simp only [canonicalBasisHW, h]

/-- The identification of the index sets `B(λ₁) × B(λ₂)` for `R` and `R'`. -/
def tensorIdxEquiv :
    canonicalBasisHW D Λ₁ × canonicalBasisHW D Λ₂ ≃
      canonicalBasisHW D Λ₁' × canonicalBasisHW D Λ₂' :=
  Equiv.prodCongr (Set.equivOfEq (canonicalBasisHW_eq h₁).symm)
    (Set.equivOfEq (canonicalBasisHW_eq h₂).symm)

/-- `tensorTransfer` preserves the coordinates in the bases `b₁⁻η ⊗ b₂⁻η'`. -/
theorem repr_tensorTransfer
    (z : TensorModule 𝕂 (IrreducibleModule R 𝕧 Λ₁.1) (IrreducibleModule R 𝕧 Λ₂.1))
    (p : canonicalBasisHW D Λ₁ × canonicalBasisHW D Λ₂) :
    (tensorHWBasis hR' Λ₁' Λ₂').repr (tensorTransfer hR hR' h₁ h₂ z) (tensorIdxEquiv h₁ h₂ p) =
      (tensorHWBasis hR Λ₁ Λ₂).repr z p := by
  have hb : ((tensorHWBasis hR Λ₁ Λ₂).map (tensorTransfer hR hR' h₁ h₂)).reindex
      (tensorIdxEquiv h₁ h₂) = tensorHWBasis hR' Λ₁' Λ₂' :=
    Module.Basis.eq_of_apply_eq fun q ↦ by
      rw [Module.Basis.reindex_apply, Module.Basis.map_apply, tensorHWBasis_apply,
        tensorHWBasis_apply, tensorTransfer_mk, hwTransfer_evq, hwTransfer_evq]
      rfl
  rw [← hb, Module.Basis.repr_reindex_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, Equiv.symm_apply_apply]

end Tensor

/-! ### The root datum `freeCoroot R` -/

section FreeCoroot

variable (I) in
/-- `f ↦ f ∘ pr₁`, `X → X × ℤ^I`. -/
def compFst : (Y →+ ℤ) →ₗ[ℤ] (Y × (I →₀ ℤ) →+ ℤ) where
  toFun f := f.comp (AddMonoidHom.fst _ _)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

include hR in
omit [Finite I] [DecidableEq I] in
lemma isXRegular_freeCoroot : R.freeCoroot.IsXRegular := by
  have hker : LinearMap.ker (compFst I (Y := Y)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    ext y
    exact DFunLike.congr_fun hf (y, 0)
  exact hR.map' (compFst I) hker

omit [Finite I] in
lemma exists_fund_freeCoroot (j : I) :
    ∃ Λ : Dom R.freeCoroot, ∀ i, Λ.1 (R.freeCoroot.coroot i) = if i = j then 1 else 0 := by
  classical
  refine ⟨⟨(Finsupp.applyAddHom j).comp (AddMonoidHom.snd _ _), fun i ↦ ?_⟩, fun i ↦ ?_⟩ <;>
  · simp only [LusztigCartanDatum.RootDatum.freeCoroot, AddMonoidHom.coe_comp,
      Function.comp_apply, AddMonoidHom.coe_snd, Finsupp.applyAddHom_apply,
      Finsupp.single_apply] <;> split_ifs <;> simp

/-- A dominant weight `λ` of `R`, as a dominant weight `λ ∘ pr₁` of `freeCoroot R`. -/
def domFreeCoroot (Λ : Dom R) : Dom R.freeCoroot :=
  ⟨compFst I Λ.1, Λ.2⟩

omit [Finite I] [DecidableEq I] in
lemma domFreeCoroot_coroot (Λ : Dom R) (i : I) :
    (domFreeCoroot Λ).1 (R.freeCoroot.coroot i) = Λ.1 (R.coroot i) :=
  rfl

end FreeCoroot

/-! ### [Lus] Prop. 25.1.2 (b) -/

variable (Λ₁ Λ₂ : Dom R)

/-- **[Lus] Prop. 25.1.2 (b)**: for `b ∈ B`, the coordinates `f(b; b₁, b₂)` of `χ(b⁻η'')` in the
basis `b₁⁻η ⊗ b₂⁻η'` of `Λ_λ ⊗ Λ_{λ'}` lie in `ℤ[v⁻¹]`.

Lusztig assumes `Y`-regular root data; here the root datum is `X`-regular. The proof (our own
route) transfers `isIntInv_repr_tensorEmb_evq_of_fund` from the root datum `freeCoroot R`, which
has fundamental weights. -/
theorem isIntInv_repr_tensorEmb_evq {x : Um D 𝕧} (hx : x ∈ canonicalBasis D)
    (p : canonicalBasisHW D Λ₁ × canonicalBasisHW D Λ₂) :
    IsIntInv ((tensorHWBasis hR Λ₁ Λ₂).repr
      (tensorEmb hvt hR Λ₁.2 Λ₂.2 (evq hvt (Λ₁ + Λ₂) x)) p) := by
  have h₁ := domFreeCoroot_coroot Λ₁
  have h₂ := domFreeCoroot_coroot Λ₂
  have hR₁ := isXRegular_freeCoroot hR
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have := isIntInv_repr_tensorEmb_evq_of_fund hR₁ exists_fund_freeCoroot
    (domFreeCoroot Λ₁) (domFreeCoroot Λ₂) hx (tensorIdxEquiv h₁ h₂ p)
  rw [evq_mk] at this ⊢
  rwa [← tensorTransfer_tensorEmb_ev hR hR₁ h₁ h₂, repr_tensorTransfer] at this

end LieLean.QuantumGroup
