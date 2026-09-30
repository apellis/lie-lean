/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Shapovalov
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The duality functor `M ↦ M^∨` on weight modules

For a `𝔤(A)`-module `V`, the *restricted twisted dual* `V^∨` is the sum of the weight spaces of
the twisted dual `V^{*σ}` (the full dual with `⁅x, φ⁆ = φ ∘ σ(x)`, `σ` the transpose
antiinvolution). For `V` in category `𝒪` this is the duality functor of Humphreys, GSM 94, §3.2
(check): `V^∨ = ⨁_μ (V_μ)^*`. It is a contravariant functor of `V`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.TwistedDual.map`: contravariant functoriality of `V^{*σ}`.
* `Matrix.Realization.KacMoodyAlgebra.restrictedDual`: the Lie submodule `V^∨ ⊆ V^{*σ}`.
* `Matrix.Realization.KacMoodyAlgebra.restrictedDualMap`, `restrictedDualEquiv`: functoriality.
* `Matrix.Realization.KacMoodyAlgebra.restrictedDualTensorEquiv`: for a finite-dimensional
  weight module `L` with a nondegenerate symmetric contravariant form,
  `V^∨ ⊗ L ≅ (V ⊗ L)^∨` (Humphreys, GSM 94, §3.2 (check), with `L^∨ ≅ L`).

## Main results

* `TwistedDual.toDual_rep`: `U(𝔤)` acts on `V^{*σ}` by `φ ↦ φ ∘ σ(u)`.
* `TwistedDual.apply_eq_zero_of_ne`: a weight-`μ` functional kills `V_ν` for `ν ≠ μ`.
-/

noncomputable section

open Module LieModule TensorProduct

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra

namespace TwistedDual

variable {P}

omit [DecidableEq ι] [CharZero K] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] in
@[ext] lemma ext {φ ψ : TwistedDual P V} (hφψ : ∀ v, toDual P V φ v = toDual P V ψ v) :
    φ = ψ :=
  (toDual P V).injective (LinearMap.ext hφψ)

omit [DecidableEq ι] [CharZero K] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W] in
/-- Functionals on a tensor product agree if they agree on pure tensors. -/
lemma ext_tmul {φ ψ : TwistedDual P (V ⊗[K] W)}
    (hφψ : ∀ v w, toDual P _ φ (v ⊗ₜ w) = toDual P _ ψ (v ⊗ₜ w)) : φ = ψ :=
  (toDual P _).injective (TensorProduct.ext' hφψ)

variable (P) in
/-- The twisted dual is a contravariant functor: `f^* φ = φ ∘ f`. -/
def map (f : V →ₗ⁅K,𝔤⁆ W) : TwistedDual P W →ₗ⁅K,𝔤⁆ TwistedDual P V where
  toLinearMap := (toDual P V).symm.toLinearMap ∘ₗ f.toLinearMap.dualMap ∘ₗ
    (toDual P W).toLinearMap
  map_lie' {x φ} := by
    ext v
    change toDual P W ⁅x, φ⁆ (f v) = toDual P V ⁅x, (toDual P V).symm
      (f.toLinearMap.dualMap (toDual P W φ))⁆ v
    rw [lie_apply, lie_apply, LinearEquiv.apply_symm_apply, LinearMap.dualMap_apply,
      LieModuleHom.coe_toLinearMap, LieModuleHom.map_lie]

@[simp] lemma toDual_map (f : V →ₗ⁅K,𝔤⁆ W) (φ : TwistedDual P W) (v : V) :
    toDual P V (map P f φ) v = toDual P W φ (f v) := rfl

/-- `U(𝔤)` acts on the twisted dual through the antiautomorphism `σ`: `u φ = φ ∘ σ(u)`. -/
theorem toDual_rep (u : 𝓤) (φ : TwistedDual P V) :
    toDual P V (rep P (TwistedDual P V) u φ) =
      toDual P V φ ∘ₗ rep P V (envTranspose P u).unop := by
  induction u using UniversalEnvelopingAlgebra.induction generalizing φ with
  | algebraMap c =>
    ext v
    simp [Algebra.algebraMap_eq_smul_one]
  | ι x =>
    ext v
    rw [rep_ι, lie_apply, envTranspose_ι, MulOpposite.unop_op, LinearMap.comp_apply, rep_ι]
  | mul a b ha hb =>
    ext v
    rw [map_mul, Module.End.mul_apply, ha, LinearMap.comp_apply, hb, LinearMap.comp_apply,
      unop_envTranspose_mul, map_mul, LinearMap.comp_apply, Module.End.mul_apply]
  | add a b ha hb =>
    ext v
    simp only [map_add, LinearMap.add_apply, ha, hb, LinearMap.comp_apply, MulOpposite.unop_add]

/-- Weight vectors of the twisted dual: `φ(h v) = μ(h) φ(v)`. -/
lemma mem_weightSpaceOfMap_iff {μ : Dual K H} {φ : TwistedDual P V} :
    φ ∈ weightSpaceOfMap (TwistedDual P V) (h P) μ ↔
      ∀ a v, toDual P V φ ⁅h P a, v⁆ = μ a * toDual P V φ v := by
  rw [mem_weightSpaceOfMap]
  constructor
  · intro hφ a v
    have := congrArg (fun ψ ↦ toDual P V ψ v) (hφ a)
    simpa only [lie_apply, transpose_h, map_smul, LinearMap.smul_apply, smul_eq_mul] using this
  · intro hφ a
    ext v
    rw [lie_apply, transpose_h, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- A functional of weight `μ` vanishes on the weight space `V_ν` for `ν ≠ μ`. -/
lemma apply_eq_zero_of_ne {μ ν : Dual K H} {φ : TwistedDual P V}
    (hφ : φ ∈ weightSpaceOfMap (TwistedDual P V) (h P) μ) {v : V}
    (hv : v ∈ weightSpaceOfMap V (h P) ν) (hne : μ ≠ ν) : toDual P V φ v = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := by
    by_contra hc
    push Not at hc
    exact hne (LinearMap.ext hc)
  have h1 := mem_weightSpaceOfMap_iff.mp hφ a v
  rw [hv a, map_smul, smul_eq_mul] at h1
  have h2 : (μ a - ν a) * toDual P V φ v = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)

end TwistedDual

open TwistedDual

omit [CharZero K] in
/-- Lie-module maps preserve sums of weight spaces. -/
lemma map_mem_iSup_weightSpaceOfMap (f : V →ₗ⁅K,𝔤⁆ W) {v : V}
    (hv : v ∈ ⨆ μ, weightSpaceOfMap V (h P) μ) : f v ∈ ⨆ μ, weightSpaceOfMap W (h P) μ := by
  induction hv using Submodule.iSup_induction' with
  | mem μ v hv => exact Submodule.mem_iSup_of_mem μ (map_mem_weightSpaceOfMap P f hv)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

omit [CharZero K] in
/-- A tensor product of weight vectors is a weight vector. -/
lemma tmul_mem_weightSpaceOfMap {μ ν : Dual K H} {v : V} {w : W}
    (hv : v ∈ weightSpaceOfMap V (h P) μ) (hw : w ∈ weightSpaceOfMap W (h P) ν) :
    v ⊗ₜ[K] w ∈ weightSpaceOfMap (V ⊗[K] W) (h P) (μ + ν) := fun a ↦ by
  rw [TensorProduct.LieModule.lie_tmul_right, hv a, hw a]
  simp only [LinearMap.add_apply, add_smul, tmul_smul, smul_tmul']

omit [CharZero K] in
/-- Pure tensors of sums of weight vectors are sums of weight vectors. -/
lemma tmul_mem_iSup_weightSpaceOfMap {v : V} {w : W}
    (hv : v ∈ ⨆ μ, weightSpaceOfMap V (h P) μ) (hw : w ∈ ⨆ μ, weightSpaceOfMap W (h P) μ) :
    v ⊗ₜ[K] w ∈ ⨆ μ, weightSpaceOfMap (V ⊗[K] W) (h P) μ := by
  induction hv using Submodule.iSup_induction' with
  | mem μ v hv =>
    induction hw using Submodule.iSup_induction' with
    | mem ν w hw => exact Submodule.mem_iSup_of_mem _ (tmul_mem_weightSpaceOfMap P hv hw)
    | zero => simp
    | add x y _ _ hx hy => rw [tmul_add]; exact Submodule.add_mem _ hx hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_tmul]; exact Submodule.add_mem _ hx hy

variable (V) in
/-- The restricted twisted dual `V^∨`: the sum of the weight spaces of the twisted dual
`V^{*σ}`. For `V` in category `𝒪`, `V^∨ = ⨁_μ (V_μ)^*` with `x φ = φ ∘ σ(x)`
(Humphreys, GSM 94, §3.2 (check)). -/
def restrictedDual : LieSubmodule K 𝔤 (TwistedDual P V) where
  toSubmodule := ⨆ μ, weightSpaceOfMap (TwistedDual P V) (h P) μ
  lie_mem {x φ} hφ := by
    change φ ∈ ⨆ μ, weightSpaceOfMap (TwistedDual P V) (h P) μ at hφ
    change ⁅x, φ⁆ ∈ ⨆ μ, weightSpaceOfMap (TwistedDual P V) (h P) μ
    induction hφ using Submodule.iSup_induction' with
    | mem μ φ hφ =>
      have hx : x ∈ ⨆ α, rootSpace P α :=
        (iSup₂_le fun α _ ↦ le_iSup (rootSpace P) α :
          ⨆ α ∈ AuxLieAlgebra.allWeights P, rootSpace P α ≤ ⨆ α, rootSpace P α)
          (iSup_rootSpace_eq_top P ▸ Submodule.mem_top)
      induction hx using Submodule.iSup_induction' with
      | mem α x hx => exact Submodule.mem_iSup_of_mem _ (lie_mem_weightSpaceOfMap (h P) hx hφ)
      | zero => simp
      | add x y _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
    | zero => simp
    | add φ ψ _ _ hφ hψ => rw [lie_add]; exact Submodule.add_mem _ hφ hψ

lemma mem_restrictedDual {φ : TwistedDual P V} :
    φ ∈ restrictedDual P V ↔ φ ∈ ⨆ μ, weightSpaceOfMap (TwistedDual P V) (h P) μ := Iff.rfl

/-- Elements of `V^∨` are determined by their values. -/
lemma restrictedDual_ext {φ ψ : restrictedDual P V}
    (hφψ : ∀ v, toDual P V φ.val v = toDual P V ψ.val v) : φ = ψ :=
  Subtype.ext (TwistedDual.ext hφψ)

/-- The duality functor on morphisms: `f^∨ φ = φ ∘ f`. -/
def restrictedDualMap (f : V →ₗ⁅K,𝔤⁆ W) : restrictedDual P W →ₗ⁅K,𝔤⁆ restrictedDual P V :=
  ((TwistedDual.map P f).comp (restrictedDual P W).incl).codRestrict _
    fun φ ↦ map_mem_iSup_weightSpaceOfMap P (TwistedDual.map P f) φ.property

@[simp] lemma toDual_restrictedDualMap (f : V →ₗ⁅K,𝔤⁆ W) (φ : restrictedDual P W) (v : V) :
    toDual P V (restrictedDualMap P f φ).val v = toDual P W φ.val (f v) := rfl

/-- The duality functor on isomorphisms. -/
def restrictedDualEquiv (e : V ≃ₗ⁅K,𝔤⁆ W) : restrictedDual P W ≃ₗ⁅K,𝔤⁆ restrictedDual P V :=
  { restrictedDualMap P e.toLieModuleHom with
    invFun := restrictedDualMap P e.symm.toLieModuleHom
    left_inv := fun φ ↦ restrictedDual_ext P fun w ↦ by
      change toDual P W φ.val (e (e.symm w)) = _
      rw [LieModuleEquiv.apply_symm_apply]
    right_inv := fun φ ↦ restrictedDual_ext P fun v ↦ by
      change toDual P V φ.val (e.symm (e v)) = _
      rw [LieModuleEquiv.symm_apply_apply] }

/-! ### Duality and tensor products with finite-dimensional modules -/

section Tensor

variable {L : Type*} [AddCommGroup L] [Module K L] [LieRingModule P.KacMoodyAlgebra L]
  [LieModule K P.KacMoodyAlgebra L] (B : LinearMap.BilinForm K L)
  (hB : ∀ (x : P.KacMoodyAlgebra) (u w : L), B ⁅x, u⁆ w = B u ⁅transpose P x, w⁆)

/-- The pairing `V^{*σ} ⊗ L → (V ⊗ L)^{*σ}`, `φ ⊗ l ↦ (v ⊗ l' ↦ φ(v) B(l, l'))`. -/
def tensorDualLin : TwistedDual P V ⊗[K] L →ₗ[K] TwistedDual P (V ⊗[K] L) :=
  (toDual P _).symm.toLinearMap ∘ₗ TensorProduct.dualDistrib K V L ∘ₗ
    TensorProduct.map (toDual P V).toLinearMap B

omit [DecidableEq ι] [CharZero K] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [LieRingModule P.KacMoodyAlgebra L]
  [LieModule K P.KacMoodyAlgebra L] in
lemma toDual_tensorDualLin_tmul (φ : TwistedDual P V) (l : L) (v : V) (l' : L) :
    toDual P _ (tensorDualLin P B (φ ⊗ₜ l)) (v ⊗ₜ l') = toDual P V φ v * B l l' := rfl

include hB in
/-- For a contravariant form `B` on `L`, the pairing `V^{*σ} ⊗ L → (V ⊗ L)^{*σ}` is a morphism
of `𝔤(A)`-modules. -/
def tensorDualHom : TwistedDual P V ⊗[K] L →ₗ⁅K,𝔤⁆ TwistedDual P (V ⊗[K] L) where
  toLinearMap := tensorDualLin P B
  map_lie' {x t} := by
    change tensorDualLin P B ⁅x, t⁆ = ⁅x, tensorDualLin P B t⁆
    induction t with
    | add s t hs ht => rw [lie_add, map_add, hs, ht, map_add, lie_add]
    | tmul φ l =>
      apply ext_tmul
      intro v l'
      rw [TensorProduct.LieModule.lie_tmul_right, map_add, map_add, LinearMap.add_apply,
        lie_apply, TensorProduct.LieModule.lie_tmul_right, map_add, toDual_tensorDualLin_tmul,
        toDual_tensorDualLin_tmul, toDual_tensorDualLin_tmul, toDual_tensorDualLin_tmul,
        lie_apply, hB]

lemma toDual_tensorDualHom_tmul (φ : TwistedDual P V) (l : L) (v : V) (l' : L) :
    toDual P _ (tensorDualHom P B hB (φ ⊗ₜ l)) (v ⊗ₜ l') = toDual P V φ v * B l l' := rfl

variable (V) in
/-- `V^∨ ⊗ L → (V ⊗ L)^∨`, when `L` is spanned by weight vectors. -/
def restrictedDualTensorHom (hL : ⨆ μ, weightSpaceOfMap L (h P) μ = ⊤) :
    restrictedDual P V ⊗[K] L →ₗ⁅K,𝔤⁆ restrictedDual P (V ⊗[K] L) :=
  ((tensorDualHom P B hB).comp (TensorProduct.LieModule.map (restrictedDual P V).incl
    LieModuleHom.id)).codRestrict _ fun t ↦ by
    induction t with
    | add s t hs ht => rw [map_add]; exact Submodule.add_mem _ hs ht
    | tmul φ l =>
      change tensorDualHom P B hB (φ.val ⊗ₜ l) ∈ _
      exact map_mem_iSup_weightSpaceOfMap P _
        (tmul_mem_iSup_weightSpaceOfMap P φ.property (hL ▸ Submodule.mem_top))

/-- The slice `v ↦ Ψ(v ⊗ l)` of a functional on `V ⊗ L`. -/
def sliceDual (l : L) : TwistedDual P (V ⊗[K] L) →ₗ[K] TwistedDual P V :=
  (toDual P V).symm.toLinearMap ∘ₗ ((TensorProduct.mk K V L).flip l).dualMap ∘ₗ
    (toDual P _).toLinearMap

omit [DecidableEq ι] [CharZero K] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [LieRingModule P.KacMoodyAlgebra L]
  [LieModule K P.KacMoodyAlgebra L] in
@[simp] lemma toDual_sliceDual (l : L) (Ψ : TwistedDual P (V ⊗[K] L)) (v : V) :
    toDual P V (sliceDual P l Ψ) v = toDual P _ Ψ (v ⊗ₜ l) := rfl

omit [DecidableEq ι] [CharZero K] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [LieRingModule P.KacMoodyAlgebra L] [LieModule K P.KacMoodyAlgebra L] in
lemma sliceDual_add (l l' : L) (Ψ : TwistedDual P (V ⊗[K] L)) :
    sliceDual P (l + l') Ψ = sliceDual P l Ψ + sliceDual P l' Ψ := by
  ext v
  rw [toDual_sliceDual, map_add, LinearMap.add_apply, toDual_sliceDual, toDual_sliceDual,
    tmul_add, map_add]

omit [DecidableEq ι] [CharZero K] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [LieRingModule P.KacMoodyAlgebra L] [LieModule K P.KacMoodyAlgebra L] in
lemma sliceDual_zero (Ψ : TwistedDual P (V ⊗[K] L)) : sliceDual P (0 : L) Ψ = 0 := by
  ext v
  rw [toDual_sliceDual, tmul_zero, map_zero, map_zero, LinearMap.zero_apply]

lemma sliceDual_mem_weightSpaceOfMap {κ ν : Dual K H} {Ψ : TwistedDual P (V ⊗[K] L)}
    (hΨ : Ψ ∈ weightSpaceOfMap _ (h P) κ) {l : L} (hl : l ∈ weightSpaceOfMap L (h P) ν) :
    sliceDual P l Ψ ∈ weightSpaceOfMap (TwistedDual P V) (h P) (κ - ν) := by
  rw [mem_weightSpaceOfMap_iff] at hΨ ⊢
  intro a v
  have h1 := hΨ a (v ⊗ₜ l)
  rw [TensorProduct.LieModule.lie_tmul_right, map_add, hl a, tmul_smul, map_smul,
    smul_eq_mul] at h1
  rw [toDual_sliceDual, toDual_sliceDual, LinearMap.sub_apply, sub_mul]
  linear_combination h1

lemma sliceDual_mem_restrictedDual (hL : ⨆ μ, weightSpaceOfMap L (h P) μ = ⊤) (l : L)
    (Ψ : restrictedDual P (V ⊗[K] L)) : sliceDual P l Ψ.val ∈ restrictedDual P V := by
  have hl : l ∈ ⨆ μ, weightSpaceOfMap L (h P) μ := hL ▸ Submodule.mem_top
  obtain ⟨Ψ, hΨ⟩ := Ψ
  change Ψ ∈ ⨆ μ, weightSpaceOfMap _ (h P) μ at hΨ
  induction hΨ using Submodule.iSup_induction' with
  | mem κ Ψ hΨ =>
    induction hl using Submodule.iSup_induction' with
    | mem ν l hl => exact Submodule.mem_iSup_of_mem _ (sliceDual_mem_weightSpaceOfMap P hΨ hl)
    | zero => rw [sliceDual_zero]; exact zero_mem _
    | add l l' _ _ hl hl' => rw [sliceDual_add]; exact add_mem hl hl'
  | zero => rw [map_zero]; exact zero_mem _
  | add Ψ Ψ' _ _ hΨ hΨ' => rw [map_add]; exact add_mem hΨ hΨ'

/-- The slice as a map `(V ⊗ L)^∨ → V^∨`. -/
def restrictedSliceDual (hL : ⨆ μ, weightSpaceOfMap L (h P) μ = ⊤) (l : L) :
    restrictedDual P (V ⊗[K] L) →ₗ[K] restrictedDual P V :=
  ((sliceDual P l).comp (restrictedDual P (V ⊗[K] L)).toSubmodule.subtype).codRestrict _
    (sliceDual_mem_restrictedDual P hL l)

omit [CharZero K] [LieRingModule P.KacMoodyAlgebra L] [LieModule K P.KacMoodyAlgebra L] in
lemma sum_apply_dualBasis_smul {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (hBn : B.Nondegenerate)
    (b : Basis ι' K L) (l : L) : ∑ i, B l (b i) • B.dualBasis hBn b i = l := by
  conv_rhs => rw [← (B.dualBasis hBn b).sum_repr l]
  simp only [LinearMap.BilinForm.dualBasis_repr_apply]

omit [CharZero K] [LieRingModule P.KacMoodyAlgebra L] [LieModule K P.KacMoodyAlgebra L] in
lemma sum_dualBasis_apply_smul {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (hBn : B.Nondegenerate)
    (hBs : B.IsSymm) (b : Basis ι' K L) (l : L) : ∑ i, B (B.dualBasis hBn b i) l • b i = l := by
  conv_rhs => rw [← (B.dualBasis hBn (B.dualBasis hBn b)).sum_repr l]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, hBs.eq,
    LinearMap.BilinForm.dualBasis_dualBasis hBn hBs b]

variable [FiniteDimensional K L] (hBn : B.Nondegenerate) (hBs : B.IsSymm)

include hB in
variable (V) in
/-- **Duality commutes with tensoring by a self-dual finite-dimensional module**: if `L` is a
finite-dimensional weight module with a nondegenerate symmetric contravariant form, then
`V^∨ ⊗ L ≅ (V ⊗ L)^∨` (Humphreys, GSM 94, §3.2 (check); `L^∨ ≅ L` via the form). -/
def restrictedDualTensorEquiv (hL : ⨆ μ, weightSpaceOfMap L (h P) μ = ⊤) :
    restrictedDual P V ⊗[K] L ≃ₗ⁅K,𝔤⁆ restrictedDual P (V ⊗[K] L) := by
  classical
  let b := Module.finBasis K L
  let d := B.dualBasis hBn b
  have hd : ∀ l : L, ∑ i, B l (b i) • d i = l := sum_apply_dualBasis_smul B hBn b
  have hb : ∀ l : L, ∑ i, B (d i) l • b i = l := sum_dualBasis_apply_smul B hBn hBs b
  let F := restrictedDualTensorHom P V B hB hL
  let G : restrictedDual P (V ⊗[K] L) →ₗ[K] restrictedDual P V ⊗[K] L :=
    ∑ i, ((TensorProduct.mk K _ L).flip (d i)) ∘ₗ restrictedSliceDual P hL (b i)
  have hG : ∀ Ψ, G Ψ = ∑ i, restrictedSliceDual P hL (b i) Ψ ⊗ₜ d i := fun Ψ ↦ by
    simp only [G, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.flip_apply,
      TensorProduct.mk_apply]
  have hFG : ∀ Ψ, F (G Ψ) = Ψ := fun Ψ ↦ by
    apply Subtype.ext
    apply ext_tmul
    intro v l'
    let E : restrictedDual P (V ⊗[K] L) →ₗ[K] K := (LinearMap.applyₗ (v ⊗ₜ[K] l')) ∘ₗ
      (toDual P _).toLinearMap ∘ₗ (restrictedDual P (V ⊗[K] L)).toSubmodule.subtype
    change E (F (G Ψ)) = E Ψ
    rw [hG, map_sum, map_sum]
    change ∑ i, toDual P _ Ψ.val (v ⊗ₜ b i) * B (d i) l' = toDual P _ Ψ.val (v ⊗ₜ l')
    conv_rhs => rw [← hb l', tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [tmul_smul, map_smul, smul_eq_mul, mul_comm]
  have hGF : ∀ t, G (F t) = t := fun t ↦ by
    induction t with
    | add s t hs ht => rw [map_add, map_add, hs, ht]
    | tmul φ l =>
      rw [hG]
      have hs : ∀ i, restrictedSliceDual P hL (b i) (F (φ ⊗ₜ l)) = B l (b i) • φ := fun i ↦
        restrictedDual_ext P fun v ↦ by
          change toDual P V φ.val v * B l (b i) = toDual P V (B l (b i) • φ.val) v
          rw [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]
      simp_rw [hs, smul_tmul, ← tmul_sum, hd]
  exact LieModuleEquiv.ofBijective F
    ⟨Function.LeftInverse.injective hGF, Function.RightInverse.surjective hFG⟩

end Tensor

end Matrix.Realization.KacMoodyAlgebra
