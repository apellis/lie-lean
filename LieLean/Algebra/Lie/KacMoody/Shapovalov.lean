/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaIrreducible
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The contravariant (Shapovalov) form on Verma modules

Let `𝔤 = 𝔤(A)` be the Kac–Moody algebra of a realization of a square integer matrix `A` over a
field `K` of characteristic zero, and let `ω` be its Chevalley involution. The map `σ = -ω` is an
antiinvolution of `𝔤`: `σ(eᵢ) = fᵢ`, `σ(fᵢ) = eᵢ`, `σ(h) = h` and `σ⁅x, y⁆ = ⁅σ y, σ x⁆`. It
extends to an antiautomorphism of `U(𝔤)`.

The Verma module `M(Λ)` carries a unique bilinear form `B` with `B(v_Λ, v_Λ) = 1` which is
*contravariant*: `B(x u, w) = B(u, σ(x) w)` for `x ∈ 𝔤`. It is symmetric, different weight spaces
are orthogonal, and its radical is the maximal proper submodule `M'(Λ)` of `M(Λ)`
([Kac] §9.4; [Kum] Prop. 2.3.2). Hence it descends to a nondegenerate contravariant form on
`L(Λ) = M(Λ)/M'(Λ)`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.transpose`: the antiinvolution `σ = -ω` of `𝔤(A)`.
* `Matrix.Realization.KacMoodyAlgebra.envTranspose`: its extension to an algebra morphism
  `U(𝔤) → U(𝔤)ᵐᵒᵖ`.
* `Matrix.Realization.KacMoodyAlgebra.TwistedDual`: the dual `V^*` of a `𝔤(A)`-module, with the
  action `⁅x, φ⁆ = φ ∘ σ(x)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.hwCoord`: the linear form on `M(Λ)` giving the
  coefficient of `v_Λ`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.contravariantForm`: the contravariant form `B`
  on `M(Λ)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.weightSpaceForm`: the restriction of `B` to a
  weight space `M(Λ)_μ`.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.contravariantForm`: the induced form on
  `L(Λ)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.contravariantForm_lie_left`: contravariance.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.contravariantForm_smul_left`: contravariance
  for the action of `U(𝔤)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.contravariantForm_smul_hwv`:
  `B(a v_Λ, b v_Λ)` is the coefficient of `v_Λ` in `σ(a) b v_Λ`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.existsUnique_contravariantForm`: uniqueness.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.isSymm_contravariantForm`: symmetry.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.contravariantForm_eq_zero_of_ne`: different
  weight spaces are orthogonal.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.mem_maxSubmodule_iff`: the radical of `B` is
  the maximal proper submodule `M'(Λ)` ([Kum] Prop. 2.3.2); `maxSubmodule_eq_bot_iff`: `M(Λ)`
  is irreducible iff `B` is nondegenerate.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.mem_maxSubmodule_iff_of_mem_weightSpace`,
  `nondegenerate_weightSpaceForm_iff`, `det_toMatrix_weightSpaceForm_ne_zero_iff`: the same
  weight space by weight space; `B` is nondegenerate on `M(Λ)_μ` (its determinant is nonzero)
  iff `M'(Λ)_μ = 0`.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.nondegenerate_contravariantForm`: the
  induced form on `L(Λ)` is nondegenerate.

No hypothesis on `A` (such as being a generalized Cartan matrix or symmetrizable) is needed.

## Construction

Rather than via the Harish-Chandra projection `U(𝔤) → U(𝔥)`, we construct `B` from the universal
property of `M(Λ)`. Via PBW, `M(Λ) ≅ U(𝔫₋)`, and the augmentation of `U(𝔫₋)` gives a linear form
`hwCoord` on `M(Λ)` with `hwCoord(v_Λ) = 1` vanishing on `𝔫₋ M(Λ)`. In the twisted dual
`M(Λ)^{*σ}` it has weight `Λ` and is killed by `𝔫₊ = σ(𝔫₋)`, so it is the image of `v_Λ` under a
unique morphism `M(Λ) → M(Λ)^{*σ}`, i.e. a contravariant bilinear form. Uniqueness, symmetry and
the description of the radical then follow formally: a linear form on `M(Λ)` vanishing on
`𝔫₋ M(Λ)` is a multiple of `hwCoord`, since `M(Λ) = K v_Λ + 𝔫₋ M(Λ)`; and the radical is a
submodule not containing `v_Λ`, while the vectors orthogonal to `M'(Λ)` form a submodule
containing `v_Λ` (as `M'(Λ)` has no component of weight `Λ`). This organisation of the standard
argument is ours.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.4.
* [KK] V. G. Kac, D. A. Kazhdan, *Structure of representations with highest weight of
  infinite-dimensional Lie algebras*, Adv. Math. 34 (1979).
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §2.3.
* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §3.14–3.15.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝓤" => UniversalEnvelopingAlgebra K (KacMoodyAlgebra P)
local notation "ιᵤ" => UniversalEnvelopingAlgebra.ι K

/-! ### The antiinvolution `σ` -/

/-- The antiinvolution `σ = -ω` of `𝔤(A)`, where `ω` is the Chevalley involution:
`σ(eᵢ) = fᵢ`, `σ(fᵢ) = eᵢ`, `σ(h) = h` and `σ⁅x, y⁆ = ⁅σ y, σ x⁆` ([Kac] §9.4). -/
def transpose : P.KacMoodyAlgebra →ₗ[K] P.KacMoodyAlgebra :=
  -(chevalleyInvolution P).toLinearMap

lemma transpose_apply (x : P.KacMoodyAlgebra) : transpose P x = -chevalleyInvolution P x := rfl

@[simp] lemma transpose_e (i : ι) : transpose P (e P i) = f P i := by simp [transpose_apply]

@[simp] lemma transpose_f (i : ι) : transpose P (f P i) = e P i := by simp [transpose_apply]

@[simp] lemma transpose_h (a : H) : transpose P (h P a) = h P a := by simp [transpose_apply]

@[simp] lemma transpose_transpose (x : P.KacMoodyAlgebra) : transpose P (transpose P x) = x := by
  simp [transpose_apply]

/-- `σ` is an antiautomorphism: `σ⁅x, y⁆ = ⁅σ y, σ x⁆`. -/
lemma transpose_lie (x y : P.KacMoodyAlgebra) :
    transpose P ⁅x, y⁆ = ⁅transpose P y, transpose P x⁆ := by
  rw [transpose_apply, transpose_apply, transpose_apply, LieHom.map_lie, neg_lie, lie_neg,
    neg_neg, ← lie_skew, neg_neg]

/-- `σ(𝔫₊) ⊆ 𝔫₋`. -/
lemma transpose_mem_nNeg {x : P.KacMoodyAlgebra} (hx : x ∈ nPos P) : transpose P x ∈ nNeg P := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨-AuxLieAlgebra.negGen z, ?_⟩
  change π P (AuxLieAlgebra.fHom P _) = -chevalleyInvolution P (π P (AuxLieAlgebra.eHom P z))
  rw [chevalleyInvolution_π, AuxLieAlgebra.chevalleyInvolution_eHom, map_neg, map_neg]

/-- `σ` as a morphism of Lie algebras `𝔤(A) → U(𝔤(A))ᵐᵒᵖ`, `x ↦ σ(x)`. -/
def transposeHom : P.KacMoodyAlgebra →ₗ⁅K⁆ 𝓤ᵐᵒᵖ where
  toLinearMap := (MulOpposite.opLinearEquiv K).toLinearMap ∘ₗ (ιᵤ).toLinearMap ∘ₗ transpose P
  map_lie' {x y} := by
    change MulOpposite.op (ιᵤ (transpose P ⁅x, y⁆)) =
      MulOpposite.op (ιᵤ (transpose P x)) * MulOpposite.op (ιᵤ (transpose P y)) -
        MulOpposite.op (ιᵤ (transpose P y)) * MulOpposite.op (ιᵤ (transpose P x))
    rw [transpose_lie, LieHom.map_lie, LieRing.of_associative_ring_bracket, ← MulOpposite.op_mul,
      ← MulOpposite.op_mul, ← MulOpposite.op_sub]

/-- The antiautomorphism `σ` of `U(𝔤(A))` extending the antiinvolution `σ` of `𝔤(A)`, as an
algebra morphism `U(𝔤) → U(𝔤)ᵐᵒᵖ` ([Kac] §9.4). -/
def envTranspose : 𝓤 →ₐ[K] 𝓤ᵐᵒᵖ := UniversalEnvelopingAlgebra.lift K (transposeHom P)

@[simp] lemma envTranspose_ι (x : P.KacMoodyAlgebra) :
    envTranspose P (ιᵤ x) = MulOpposite.op (ιᵤ (transpose P x)) :=
  UniversalEnvelopingAlgebra.lift_ι_apply K _ x

lemma unop_envTranspose_mul (a b : 𝓤) :
    (envTranspose P (a * b)).unop = (envTranspose P b).unop * (envTranspose P a).unop := by
  rw [map_mul, MulOpposite.unop_mul]

/-- `σ` is an involution of `U(𝔤(A))`. -/
@[simp] lemma unop_envTranspose_unop_envTranspose (a : 𝓤) :
    (envTranspose P (envTranspose P a).unop).unop = a := by
  induction a using UniversalEnvelopingAlgebra.induction with
  | algebraMap r => simp
  | ι x => rw [envTranspose_ι, MulOpposite.unop_op, envTranspose_ι, MulOpposite.unop_op,
      transpose_transpose]
  | mul a b ha hb => rw [unop_envTranspose_mul, unop_envTranspose_mul, ha, hb]
  | add a b ha hb => simp only [map_add, MulOpposite.unop_add, ha, hb]

/-! ### The twisted dual -/

/-- The dual `V^*` of a `𝔤(A)`-module `V`, with the action twisted by the antiinvolution `σ`:
`⁅x, φ⁆ = φ ∘ σ(x)`. Equivalently, the dual module pulled back along the Chevalley involution.
Bilinear forms `B` on `V` with `B(x u, w) = B(u, σ(x) w)` are the same as morphisms
`V → V^{*σ}` ([Kac] §9.4). -/
@[nolint unusedArguments]
def TwistedDual (_P : Realization A K H) (V : Type*) [AddCommGroup V] [Module K V] : Type _ :=
  Module.Dual K V

variable (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

namespace TwistedDual

instance : AddCommGroup (TwistedDual P V) := inferInstanceAs (AddCommGroup (Module.Dual K V))

instance : Module K (TwistedDual P V) := inferInstanceAs (Module K (Module.Dual K V))

instance : LieRingModule P.KacMoodyAlgebra (TwistedDual P V) :=
  LieRingModule.compLieHom (Module.Dual K V) (chevalleyInvolution P)

instance : LieModule K P.KacMoodyAlgebra (TwistedDual P V) :=
  LieModule.compLieHom (Module.Dual K V) (chevalleyInvolution P)

/-- The identification of the twisted dual with the dual. -/
def toDual : TwistedDual P V ≃ₗ[K] Module.Dual K V := LinearEquiv.refl K _

variable {P V}

lemma lie_apply (x : P.KacMoodyAlgebra) (φ : TwistedDual P V) (v : V) :
    toDual P V ⁅x, φ⁆ v = toDual P V φ ⁅transpose P x, v⁆ := by
  change -(toDual P V φ) ⁅chevalleyInvolution P x, v⁆ = _
  rw [transpose_apply, neg_lie, map_neg]

variable (P V) in
/-- A contravariant bilinear form on `V`, as a morphism of `𝔤(A)`-modules `V → V^{*σ}`. -/
def homOfForm (B : LinearMap.BilinForm K V)
    (hB : ∀ x u w, B ⁅x, u⁆ w = B u ⁅transpose P x, w⁆) :
    V →ₗ⁅K,P.KacMoodyAlgebra⁆ TwistedDual P V where
  toLinearMap := (toDual P V).symm.toLinearMap ∘ₗ B
  map_lie' {x u} := by
    apply (toDual P V).injective
    ext w
    rw [lie_apply]
    exact hB x u w

@[simp] lemma toDual_homOfForm (B : LinearMap.BilinForm K V)
    (hB : ∀ x u w, B ⁅x, u⁆ w = B u ⁅transpose P x, w⁆) (u : V) :
    toDual P V (homOfForm P V B hB u) = B u := rfl

end TwistedDual

/-! ### The contravariant form on `M(Λ)` -/

namespace VermaModule

open TwistedDual

variable (Λ : Dual K H)

local notation "mapN" => UniversalEnvelopingAlgebra.map (LieSubalgebra.incl (nNeg P))

/-- The augmentation `U(𝔫₋) → K`. -/
abbrev counitNNeg : UniversalEnvelopingAlgebra K (nNeg P) →ₐ[K] K :=
  UniversalEnvelopingAlgebra.lift K 0

/-- The coefficient of `v_Λ`: the linear form on `M(Λ) ≅ U(𝔫₋)` induced by the augmentation of
`U(𝔫₋)`. It is the projection onto `M(Λ)_Λ = K v_Λ` along the other weight spaces
(`hwCoord_eq_zero_of_ne`). -/
def hwCoord : Module.Dual K (VermaModule P Λ) :=
  (counitNNeg P).toLinearMap ∘ₗ (equivEnvNNeg P Λ).symm.toLinearMap

@[simp] lemma hwCoord_hwv : hwCoord P Λ (hwv P Λ) = 1 := by
  have : (equivEnvNNeg P Λ).symm (hwv P Λ) = 1 := by
    rw [LinearEquiv.symm_apply_eq, equivEnvNNeg_apply, map_one, one_smul]
  simp [hwCoord, this]

/-- `hwCoord` vanishes on `𝔫₋ M(Λ)`. -/
lemma hwCoord_lie_of_mem_nNeg {y : P.KacMoodyAlgebra} (hy : y ∈ nNeg P) (m : VermaModule P Λ) :
    hwCoord P Λ ⁅y, m⁆ = 0 := by
  obtain ⟨u, rfl⟩ := (equivEnvNNeg P Λ).surjective m
  have : ⁅y, equivEnvNNeg P Λ u⁆ =
      equivEnvNNeg P Λ (UniversalEnvelopingAlgebra.ι K ⟨y, hy⟩ * u) := by
    rw [equivEnvNNeg_mul, UniversalEnvelopingAlgebra.map_ι, lie_eq_smul]
    rfl
  rw [this]
  simp [hwCoord, -equivEnvNNeg_apply]

/-- A linear form on `M(Λ)` vanishing on the `fᵢ M(Λ)` is a multiple of `hwCoord`. -/
theorem eq_smul_hwCoord (φ : Module.Dual K (VermaModule P Λ))
    (hφ : ∀ i m, φ ⁅f P i, m⁆ = 0) : φ = φ (hwv P Λ) • hwCoord P Λ := by
  refine LinearMap.ext_on_range (span_fWord_smul_eq_top P Λ) fun w ↦ ?_
  cases w with
  | nil => simp
  | cons j w =>
    rw [fWord_smul_cons, hφ, LinearMap.smul_apply,
      hwCoord_lie_of_mem_nNeg P Λ (f_mem_nNeg P j), smul_zero]

/-- `hwCoord` has weight `Λ`. -/
lemma hwCoord_lie_h (a : H) (m : VermaModule P Λ) :
    hwCoord P Λ ⁅h P a, m⁆ = Λ a * hwCoord P Λ m := by
  set ψ : Module.Dual K (VermaModule P Λ) :=
    hwCoord P Λ ∘ₗ (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (h P a)) - Λ a • hwCoord P Λ
  have hψ : ∀ m, ψ m = hwCoord P Λ ⁅h P a, m⁆ - Λ a * hwCoord P Λ m := fun _ ↦ rfl
  have := eq_smul_hwCoord P Λ ψ fun i m ↦ by
    rw [hψ, leibniz_lie, map_add,
      hwCoord_lie_of_mem_nNeg P Λ (lie_h_mem_nNeg P a (f_mem_nNeg P i)),
      hwCoord_lie_of_mem_nNeg P Λ (f_mem_nNeg P i), hwCoord_lie_of_mem_nNeg P Λ (f_mem_nNeg P i),
      zero_add, mul_zero, sub_zero]
  have h0 := LinearMap.congr_fun this m
  rw [hψ, hψ, lie_h_hwv, map_smul, hwCoord_hwv, smul_eq_mul, mul_one, sub_self, zero_smul,
    LinearMap.zero_apply, sub_eq_zero] at h0
  exact h0

/-- `hwCoord` as an element of the twisted dual `M(Λ)^{*σ}`. -/
abbrev hwCoordTw : TwistedDual P (VermaModule P Λ) := (toDual P _).symm (hwCoord P Λ)

lemma lie_hwCoordTw_of_mem_nPos {x : P.KacMoodyAlgebra} (hx : x ∈ nPos P) :
    ⁅x, hwCoordTw P Λ⁆ = 0 := by
  apply (toDual P _).injective
  ext m
  rw [lie_apply, map_zero, LinearMap.zero_apply]
  exact hwCoord_lie_of_mem_nNeg P Λ (transpose_mem_nNeg P hx) m

lemma lie_h_hwCoordTw (a : H) : ⁅h P a, hwCoordTw P Λ⁆ = Λ a • hwCoordTw P Λ := by
  apply (toDual P _).injective
  ext m
  rw [lie_apply, transpose_h, map_smul, LinearMap.smul_apply, smul_eq_mul]
  exact hwCoord_lie_h P Λ a m

/-- The morphism `M(Λ) → M(Λ)^{*σ}` sending `v_Λ` to `hwCoord`. -/
def toTwistedDual : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ TwistedDual P (VermaModule P Λ) :=
  lift P (hwCoordTw P Λ) (fun _ hx ↦ lie_hwCoordTw_of_mem_nPos P Λ hx) (lie_h_hwCoordTw P Λ)

/-- The contravariant (Shapovalov) form `B` on the Verma module `M(Λ)`: the unique bilinear form
with `B(v_Λ, v_Λ) = 1` and `B(x u, w) = B(u, σ(x) w)` for `x ∈ 𝔤(A)` ([Kac] §9.4;
uniqueness: cf. [HumO] Prop. 3.14 (b)). -/
def contravariantForm : LinearMap.BilinForm K (VermaModule P Λ) :=
  (toDual P _).toLinearMap ∘ₗ (toTwistedDual P Λ).toLinearMap

lemma contravariantForm_apply (u w : VermaModule P Λ) :
    contravariantForm P Λ u w = toDual P _ (toTwistedDual P Λ u) w := rfl

@[simp] lemma contravariantForm_hwv_left (w : VermaModule P Λ) :
    contravariantForm P Λ (hwv P Λ) w = hwCoord P Λ w := by
  rw [contravariantForm_apply, toTwistedDual, lift_hwv, LinearEquiv.apply_symm_apply]

@[simp] lemma contravariantForm_hwv_hwv : contravariantForm P Λ (hwv P Λ) (hwv P Λ) = 1 := by
  simp

/-- **Contravariance** of the Shapovalov form: `B(x u, w) = B(u, σ(x) w)`
([Kac] §9.4). -/
theorem contravariantForm_lie_left (x : P.KacMoodyAlgebra) (u w : VermaModule P Λ) :
    contravariantForm P Λ ⁅x, u⁆ w = contravariantForm P Λ u ⁅transpose P x, w⁆ := by
  rw [contravariantForm_apply, LieModuleHom.map_lie, lie_apply]
  rfl

/-- **Uniqueness** of the contravariant form: a contravariant bilinear form `B'` on `M(Λ)` is
`B'(v_Λ, v_Λ) B` ([HumO] Prop. 3.14 (b), for semisimple `𝔤`; cf. [Kac] Prop. 9.4 for `L(Λ)`). -/
theorem eq_smul_contravariantForm (B : LinearMap.BilinForm K (VermaModule P Λ))
    (hB : ∀ x u w, B ⁅x, u⁆ w = B u ⁅transpose P x, w⁆) :
    B = B (hwv P Λ) (hwv P Λ) • contravariantForm P Λ := by
  have hv : B (hwv P Λ) = B (hwv P Λ) (hwv P Λ) • hwCoord P Λ :=
    eq_smul_hwCoord P Λ _ fun i m ↦ by rw [← transpose_e, ← hB, lie_e_hwv, map_zero,
      LinearMap.zero_apply]
  have := hom_ext P Λ (φ := homOfForm P _ B hB)
    (ψ := B (hwv P Λ) (hwv P Λ) • toTwistedDual P Λ) (by
      apply (toDual P _).injective
      rw [toDual_homOfForm, _root_.smul_apply, map_smul, toTwistedDual, lift_hwv,
        LinearEquiv.apply_symm_apply]
      exact hv)
  ext u w
  have := LinearMap.congr_fun (congr_arg (toDual P _) (LieModuleHom.congr_fun this u)) w
  rw [toDual_homOfForm] at this
  rw [this, _root_.smul_apply, map_smul]
  rfl

/-- **Symmetry** of the contravariant form ([Kac] §9.4). -/
theorem isSymm_contravariantForm : (contravariantForm P Λ).IsSymm := by
  have := eq_smul_contravariantForm P Λ (LinearMap.flip (contravariantForm P Λ)) fun x u w ↦ by
    simp only [LinearMap.flip_apply]
    conv_lhs => rw [← transpose_transpose P x]
    rw [← contravariantForm_lie_left]
  rw [LinearMap.flip_apply, contravariantForm_hwv_hwv, one_smul] at this
  exact ⟨fun u w ↦ LinearMap.congr_fun₂ this w u⟩

/-- The contravariant form on `M(Λ)` is the unique bilinear form `B` with `B(v_Λ, v_Λ) = 1` and
`B(x u, w) = B(u, σ(x) w)` for `x ∈ 𝔤(A)` ([Kac] §9.4; uniqueness: cf. [HumO] Prop. 3.14 (b)). -/
theorem existsUnique_contravariantForm :
    ∃! B : LinearMap.BilinForm K (VermaModule P Λ),
      (∀ x u w, B ⁅x, u⁆ w = B u ⁅transpose P x, w⁆) ∧ B (hwv P Λ) (hwv P Λ) = 1 :=
  ⟨contravariantForm P Λ, ⟨contravariantForm_lie_left P Λ, contravariantForm_hwv_hwv P Λ⟩,
    fun B ⟨hB, h1⟩ ↦ by rw [eq_smul_contravariantForm P Λ B hB, h1, one_smul]⟩

lemma contravariantForm_lie_right (x : P.KacMoodyAlgebra) (u w : VermaModule P Λ) :
    contravariantForm P Λ u ⁅x, w⁆ = contravariantForm P Λ ⁅transpose P x, u⁆ w := by
  rw [contravariantForm_lie_left, transpose_transpose]

/-- Contravariance for the action of `U(𝔤)`: `B(a u, w) = B(u, σ(a) w)`. -/
theorem contravariantForm_smul_left (a : 𝓤) (u w : VermaModule P Λ) :
    contravariantForm P Λ (a • u) w = contravariantForm P Λ u ((envTranspose P a).unop • w) := by
  induction a using UniversalEnvelopingAlgebra.induction generalizing u w with
  | algebraMap r => simp [algebraMap_smul]
  | ι x => rw [← lie_eq_smul, envTranspose_ι, MulOpposite.unop_op, ← lie_eq_smul,
      contravariantForm_lie_left]
  | mul a b ha hb => rw [mul_smul, ha, hb, unop_envTranspose_mul, mul_smul]
  | add a b ha hb => simp only [add_smul, map_add, MulOpposite.unop_add, LinearMap.add_apply,
      ha, hb]

/-- The Shapovalov form in terms of `U(𝔤)`: `B(a v_Λ, b v_Λ)` is the coefficient of `v_Λ` in
`σ(a) b v_Λ` ([Kac] §9.4). -/
theorem contravariantForm_smul_hwv (a b : 𝓤) :
    contravariantForm P Λ (a • hwv P Λ) (b • hwv P Λ) =
      hwCoord P Λ (((envTranspose P a).unop * b) • hwv P Λ) := by
  rw [contravariantForm_smul_left, contravariantForm_hwv_left, mul_smul]

/-- **Orthogonality of weight spaces**: `B(M(Λ)_μ, M(Λ)_ν) = 0` for `μ ≠ ν`
([Kac] §9.4). -/
theorem contravariantForm_eq_zero_of_ne {μ ν : Dual K H} {u w : VermaModule P Λ}
    (hu : u ∈ weightSpace P Λ μ) (hw : w ∈ weightSpace P Λ ν) (hμν : μ ≠ ν) :
    contravariantForm P Λ u w = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := by
    by_contra! h
    exact hμν (LinearMap.ext h)
  have := contravariantForm_lie_left P Λ (h P a) u w
  rw [transpose_h, hu a, hw a, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
    smul_eq_mul] at this
  have h0 : (μ a - ν a) * contravariantForm P Λ u w = 0 := by rw [sub_mul, this, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr ha)

/-- `hwCoord` vanishes on the weight spaces `M(Λ)_μ`, `μ ≠ Λ`. -/
lemma hwCoord_eq_zero_of_ne {μ : Dual K H} {w : VermaModule P Λ} (hw : w ∈ weightSpace P Λ μ)
    (hμ : μ ≠ Λ) : hwCoord P Λ w = 0 := by
  rw [← contravariantForm_hwv_left]
  exact contravariantForm_eq_zero_of_ne P Λ (hwv_mem_weightSpace P Λ) hw (Ne.symm hμ)

lemma lowerPart_le_ker_hwCoord : lowerPart P Λ ≤ LinearMap.ker (hwCoord P Λ) :=
  iSup₂_le fun _ hμ _ hw ↦ hwCoord_eq_zero_of_ne P Λ hw hμ

/-- The vectors orthogonal to `M'(Λ)`, a submodule of `M(Λ)`. -/
def orthMaxSubmodule : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ) where
  carrier := {w | ∀ u ∈ maxSubmodule P Λ, contravariantForm P Λ u w = 0}
  add_mem' hw hw' u hu := by rw [map_add, hw u hu, hw' u hu, add_zero]
  zero_mem' _ _ := map_zero _
  smul_mem' c w hw u hu := by rw [map_smul, hw u hu, smul_zero]
  lie_mem {x w} hw u hu := by
    rw [contravariantForm_lie_right]
    exact hw _ ((maxSubmodule P Λ).lie_mem hu)

/-- **The radical of the contravariant form is the maximal proper submodule** `M'(Λ)` of `M(Λ)`
([Kum] Prop. 2.3.2). -/
theorem mem_maxSubmodule_iff (u : VermaModule P Λ) :
    u ∈ maxSubmodule P Λ ↔ ∀ w, contravariantForm P Λ u w = 0 := by
  constructor
  · intro hu w
    have htop : orthMaxSubmodule P Λ = ⊤ := eq_top_of_hwv_mem P Λ fun u hu ↦ by
      rw [(isSymm_contravariantForm P Λ).eq, contravariantForm_hwv_left]
      exact lowerPart_le_ker_hwCoord P Λ (maxSubmodule_le_lowerPart P Λ hu)
    exact (htop ▸ LieSubmodule.mem_top w : w ∈ orthMaxSubmodule P Λ) u hu
  · intro hu
    have hker : hwv P Λ ∉ (toTwistedDual P Λ).ker := fun h ↦ by
      have := LinearMap.congr_fun (congr_arg (toDual P _) (LieModuleHom.mem_ker.mp h))
        (hwv P Λ)
      rw [← contravariantForm_apply, contravariantForm_hwv_hwv, map_zero,
        LinearMap.zero_apply] at this
      exact one_ne_zero this
    refine (le_maxSubmodule_iff P Λ (toTwistedDual P Λ).ker).mpr
      (fun h ↦ hker (by rw [h]; exact LieSubmodule.mem_top _)) ?_
    rw [LieModuleHom.mem_ker]
    apply (toDual P _).injective
    ext w
    exact hu w

/-- The maximal proper submodule `M'(Λ)` is the kernel of the contravariant form
([Kum] Prop. 2.3.2). -/
theorem maxSubmodule_toSubmodule_eq_ker :
    (maxSubmodule P Λ).toSubmodule = LinearMap.ker (contravariantForm P Λ) := by
  ext u
  rw [LieSubmodule.mem_toSubmodule, mem_maxSubmodule_iff, LinearMap.mem_ker]
  exact ⟨fun h ↦ LinearMap.ext h, fun h w ↦ by rw [h, LinearMap.zero_apply]⟩

lemma contravariantForm_eq_zero_of_mem {u : VermaModule P Λ} (hu : u ∈ maxSubmodule P Λ) :
    contravariantForm P Λ u = 0 :=
  LinearMap.ext ((mem_maxSubmodule_iff P Λ u).mp hu)

/-- A weight vector of `M(Λ)` of weight `μ` lies in `M'(Λ)` iff it is orthogonal to `M(Λ)_μ`
(cf. [Kum] Prop. 2.3.2). -/
theorem mem_maxSubmodule_iff_of_mem_weightSpace {μ : Dual K H} {u : VermaModule P Λ}
    (hu : u ∈ weightSpace P Λ μ) :
    u ∈ maxSubmodule P Λ ↔ ∀ w ∈ weightSpace P Λ μ, contravariantForm P Λ u w = 0 := by
  rw [mem_maxSubmodule_iff]
  refine ⟨fun h w _ ↦ h w, fun h w ↦ ?_⟩
  have hle : ⨆ (k : ι → ℤ) (_ : 0 ≤ k), weightSpace P Λ (Λ - P.rootOf k) ≤
      LinearMap.ker (contravariantForm P Λ u) := by
    refine iSup₂_le fun k _ w hw ↦ ?_
    by_cases hν : Λ - P.rootOf k = μ
    · rw [hν] at hw
      exact h w hw
    · exact contravariantForm_eq_zero_of_ne P Λ hu hw (Ne.symm hν)
  exact hle (by rw [iSup_weightSpace_eq_top]; trivial)

/-- `M(Λ)` is irreducible, i.e. `M'(Λ) = 0`, iff its contravariant form is nondegenerate
([Kum] Prop. 2.3.2). -/
theorem maxSubmodule_eq_bot_iff : maxSubmodule P Λ = ⊥ ↔ (contravariantForm P Λ).Nondegenerate := by
  have hsep : (contravariantForm P Λ).Nondegenerate ↔
      ∀ u, (∀ w, contravariantForm P Λ u w = 0) → u = 0 := by
    refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun w hw ↦ h w fun u ↦ ?_⟩⟩
    rw [(isSymm_contravariantForm P Λ).eq]
    exact hw u
  rw [hsep, LieSubmodule.eq_bot_iff]
  simp_rw [mem_maxSubmodule_iff]

/-! ### Restriction to weight spaces -/

/-- The restriction of the contravariant form to the (finite-dimensional) weight space
`M(Λ)_μ`. -/
abbrev weightSpaceForm (μ : Dual K H) : LinearMap.BilinForm K (weightSpace P Λ μ) :=
  (contravariantForm P Λ).restrict (weightSpace P Λ μ)

/-- The restriction of the contravariant form to `M(Λ)_μ` is nondegenerate iff `M'(Λ)` has no
nonzero vector of weight `μ`, i.e. iff `dim L(Λ)_μ = dim M(Λ)_μ` (cf. [Kum] Prop. 2.3.2). -/
theorem nondegenerate_weightSpaceForm_iff (μ : Dual K H) :
    (weightSpaceForm P Λ μ).Nondegenerate ↔
      (maxSubmodule P Λ).toSubmodule ⊓ weightSpace P Λ μ = ⊥ := by
  have hsep : (weightSpaceForm P Λ μ).Nondegenerate ↔
      ∀ u, (∀ w, weightSpaceForm P Λ μ u w = 0) → u = 0 := by
    refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun w hw ↦ h w fun u ↦ ?_⟩⟩
    change contravariantForm P Λ w u = 0
    rw [(isSymm_contravariantForm P Λ).eq]
    exact hw u
  rw [hsep, Submodule.eq_bot_iff]
  constructor
  · rintro h u ⟨hu, huμ⟩
    have := h ⟨u, huμ⟩ fun w ↦
      (mem_maxSubmodule_iff_of_mem_weightSpace P Λ huμ).mp hu w w.2
    exact congr_arg Subtype.val this
  · intro h u hu
    exact Subtype.ext (h u ⟨(mem_maxSubmodule_iff_of_mem_weightSpace P Λ u.2).mpr
      fun w hw ↦ hu ⟨w, hw⟩, u.2⟩)

/-- The determinant of the contravariant form on `M(Λ)_μ` (with respect to any basis) is nonzero
iff `M'(Λ)` has no nonzero vector of weight `μ` (cf. [Kum] Prop. 2.3.2). -/
theorem det_toMatrix_weightSpaceForm_ne_zero_iff {n : Type*} [Fintype n] [DecidableEq n]
    (μ : Dual K H) (b : Basis n K (weightSpace P Λ μ)) :
    (LinearMap.BilinForm.toMatrix b (weightSpaceForm P Λ μ)).det ≠ 0 ↔
      (maxSubmodule P Λ).toSubmodule ⊓ weightSpace P Λ μ = ⊥ := by
  rw [← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero, nondegenerate_weightSpaceForm_iff]

end VermaModule

/-! ### The contravariant form on `L(Λ)` -/

namespace IrreducibleModule

open VermaModule

variable (Λ : Dual K H)

/-- The contravariant form on `L(Λ) = M(Λ)/M'(Λ)`, induced by the contravariant form of `M(Λ)`
([Kac] §9.4). -/
def contravariantForm : LinearMap.BilinForm K (IrreducibleModule P Λ) :=
  ((maxSubmodule P Λ).toSubmodule.liftQ
    ((maxSubmodule P Λ).toSubmodule.liftQ (VermaModule.contravariantForm P Λ)
      fun _ hu ↦ LinearMap.mem_ker.mpr (contravariantForm_eq_zero_of_mem P Λ hu)).flip
    fun w hw ↦ LinearMap.mem_ker.mpr <| by
      ext u
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.flip_apply,
        Submodule.liftQ_apply, LinearMap.zero_apply]
      rw [(isSymm_contravariantForm P Λ).eq, contravariantForm_eq_zero_of_mem P Λ hw,
        LinearMap.zero_apply]).flip

@[simp] lemma contravariantForm_mk (u w : VermaModule P Λ) :
    contravariantForm P Λ (LieSubmodule.Quotient.mk' _ u) (LieSubmodule.Quotient.mk' _ w) =
      VermaModule.contravariantForm P Λ u w := rfl

@[simp] lemma contravariantForm_hwv_hwv : contravariantForm P Λ (hwv P Λ) (hwv P Λ) = 1 :=
  VermaModule.contravariantForm_hwv_hwv P Λ

/-- Contravariance of the form on `L(Λ)`: `B(x u, w) = B(u, σ(x) w)`. -/
theorem contravariantForm_lie_left (x : P.KacMoodyAlgebra) (u w : IrreducibleModule P Λ) :
    contravariantForm P Λ ⁅x, u⁆ w = contravariantForm P Λ u ⁅transpose P x, w⁆ := by
  obtain ⟨u, rfl⟩ := LieSubmodule.Quotient.surjective_mk' _ u
  obtain ⟨w, rfl⟩ := LieSubmodule.Quotient.surjective_mk' _ w
  rw [← LieModuleHom.map_lie, ← LieModuleHom.map_lie, contravariantForm_mk, contravariantForm_mk,
    VermaModule.contravariantForm_lie_left]

/-- The form on `L(Λ)` is symmetric. -/
theorem isSymm_contravariantForm : (contravariantForm P Λ).IsSymm := by
  refine ⟨fun u w ↦ ?_⟩
  obtain ⟨u, rfl⟩ := LieSubmodule.Quotient.surjective_mk' _ u
  obtain ⟨w, rfl⟩ := LieSubmodule.Quotient.surjective_mk' _ w
  rw [contravariantForm_mk, contravariantForm_mk, (VermaModule.isSymm_contravariantForm P Λ).eq]

/-- The contravariant form on `L(Λ)` is nondegenerate ([Kac] §9.4). -/
theorem nondegenerate_contravariantForm : (contravariantForm P Λ).Nondegenerate := by
  have hl : ∀ u : IrreducibleModule P Λ, (∀ w, contravariantForm P Λ u w = 0) → u = 0 := by
    intro u hu
    obtain ⟨u, rfl⟩ := LieSubmodule.Quotient.surjective_mk' _ u
    rw [LieSubmodule.Quotient.mk_eq_zero, mem_maxSubmodule_iff]
    exact fun w ↦ hu (LieSubmodule.Quotient.mk' _ w)
  refine ⟨hl, fun w hw ↦ hl w fun u ↦ ?_⟩
  rw [(isSymm_contravariantForm P Λ).eq]
  exact hw u

end IrreducibleModule

end Matrix.Realization.KacMoodyAlgebra

end
