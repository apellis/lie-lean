/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationDuality
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Contravariant forms

Let `σ` be the transpose antiinvolution of `𝔤 = 𝔤(A)` (`σ(eᵢ) = fᵢ`, `σ(h) = h`; Humphreys
writes `τ`). A bilinear form `B` on a `𝔤`-module `V` is *contravariant* if it is symmetric and
`B(x u, w) = B(u, σ(x) w)` for `x ∈ 𝔤`. Then the same identity holds for all `x ∈ U(𝔤)`, with
`σ` extended to an antiautomorphism of `U(𝔤)`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsContravariantForm`: contravariant forms.
* `Matrix.Realization.KacMoodyAlgebra.IsContravariantForm.orthogonal`: the orthogonal
  `N^⊥ = {v | B(v, N) = 0}` of a submodule, as a submodule.

## Main results

Humphreys, GSM 94, Proposition 3.14:
* (a) `IsContravariantForm.apply_eq_zero_of_ne`: distinct weight spaces are orthogonal;
* (b) `IsContravariantForm.eq_of_apply_eq`: on a quotient of `M(λ)`, a contravariant form is
  determined by its value at the image of the highest weight vector `v⁺`, and
  `IsContravariantForm.apply_hwv_ne_zero`: this value is nonzero for a nonzero form;
* (c) `IsContravariantForm.tmul`: `(v ⊗ w, v' ⊗ w') = (v, v')(w, w')` is contravariant on
  `V₁ ⊗ V₂`, and `LinearMap.BilinForm.Nondegenerate.tmul`: it is nondegenerate when both factors
  are (over a field, without finiteness assumptions);
* (d) `IsContravariantForm.orthogonal`: `N^⊥` is a submodule;
* (e) `IsContravariantForm.apply_eq_zero_of_centralBlock`: generalized central blocks for
  distinct central characters are orthogonal (finite type).

Humphreys, GSM 94, Theorem 3.15:
* `exists_isContravariantForm_of_surjective`: a nonzero quotient `V` of `M(λ)` has a
  contravariant form with value `1` at `v⁺`, whose radical is the image of the maximal
  submodule `N(λ)` of `M(λ)`;
* `IsContravariantForm.nondegenerate_iff_nonempty_equiv`: a contravariant form on `V` which is
  nonzero at `v⁺` is nondegenerate iff `V ≅ L(λ)`.

Humphreys works with semisimple `𝔤` over `ℂ`; here `A` is any square integer matrix and `K` any
field of characteristic zero, except in (e), which uses finite type (through `σ(z) = z` for `z`
in the centre of `U(𝔤)`, `unop_envTranspose_center`). In (e) the module is arbitrary, not only in
`𝒪`. The form of Theorem 3.15 is obtained from the Shapovalov form of `M(λ)`
(`VermaModule.contravariantForm`), descended along `M(λ) ↠ V`, instead of from the universal
form on `U(𝔤)`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.14–3.15.
-/

noncomputable section

open Module LieModule TensorProduct

/-! ### Tensor products of nondegenerate forms -/

namespace LinearMap.BilinForm

variable {K V₁ V₂ : Type*} [Field K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
  [Module K V₂] {B₁ : LinearMap.BilinForm K V₁} {B₂ : LinearMap.BilinForm K V₂}

/-- The tensor product of left-separating bilinear forms over a field is left-separating. -/
theorem separatingLeft_tmul (h₁ : B₁.SeparatingLeft) (h₂ : B₂.SeparatingLeft) :
    (B₁.tmul B₂).SeparatingLeft := by
  classical
  intro t ht
  let b := Basis.ofVectorSpace K V₁
  set f := equivFinsuppOfBasisLeft b t with hf
  have ht' : t = f.sum fun i w ↦ b i ⊗ₜ w := by
    have := LinearMap.congr_fun (equivFinsuppOfBasisLeft_symm b) f
    simp only [LinearEquiv.coe_coe, hf, LinearEquiv.symm_apply_apply, Finsupp.lsum_apply] at this
    exact this
  suffices hf0 : f = 0 by rw [ht', hf0, Finsupp.sum_zero_index]
  by_contra hf0
  obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hf0
  rw [Finsupp.coe_zero, Pi.zero_apply] at hi₀
  have hmem : i₀ ∈ f.support := Finsupp.mem_support_iff.mpr hi₀
  -- the functionals `B₁ (b i) (-)`, `i ∈ supp f`, are linearly independent
  let Ψ : V₁ →ₗ[K] (f.support → K) := LinearMap.pi fun i ↦ B₁ (b i)
  have hΨ : Function.Surjective Ψ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨ψ, hψ0, hψ⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    have hψv : ∀ v, ψ (Ψ v) = 0 := fun v ↦ by
      have : ψ (Ψ v) ∈ (LinearMap.range Ψ).map ψ := ⟨Ψ v, ⟨v, rfl⟩, rfl⟩
      rwa [hψ, Submodule.mem_bot] at this
    have hψe : ∀ x : f.support → K, ψ x = ∑ i, x i * ψ (Pi.single i 1) := fun x ↦ by
      conv_lhs => rw [← Finset.univ_sum_single x]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← smul_eq_mul, ← map_smul]
      congr 1
      ext j
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    have hsum : (∑ i : f.support, ψ (Pi.single i 1) • b i) = 0 := by
      apply h₁
      intro v
      rw [map_sum, LinearMap.sum_apply]
      have := hψv v
      rw [hψe] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]
      rfl
    have hc := Fintype.linearIndependent_iff.mp
      (b.linearIndependent.comp (fun i : f.support ↦ (i : _)) Subtype.val_injective) _ hsum
    apply hψ0
    refine LinearMap.ext fun x ↦ ?_
    rw [hψe, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [hc i, mul_zero]
  obtain ⟨v', hv'⟩ := hΨ (Pi.single ⟨i₀, hmem⟩ 1)
  have hv'i : ∀ i (hi : i ∈ f.support), B₁ (b i) v' = if i = i₀ then 1 else 0 := by
    intro i hi
    have := congrArg (fun g ↦ g (⟨i, hi⟩ : f.support)) hv'
    change B₁ (b i) v' = _ at this
    rw [this]
    by_cases h : i = i₀
    · subst h
      simp
    · simp [Subtype.ext_iff, h]
  obtain ⟨w', hw'⟩ : ∃ w', B₂ (f i₀) w' ≠ 0 := by
    by_contra! h
    exact hi₀ (h₂ _ h)
  apply hw'
  have := ht (v' ⊗ₜ w')
  rw [ht', Finsupp.sum, map_sum, LinearMap.sum_apply] at this
  rw [← this, Finset.sum_eq_single i₀]
  · rw [tensorDistrib_tmul, hv'i i₀ hmem]
    simp
  · intro i hi hne
    rw [tensorDistrib_tmul, hv'i i hi]
    simp [hne]
  · intro h
    exact absurd hmem h

attribute [local ext] TensorProduct.ext in
lemma flip_tmul (B₁ : LinearMap.BilinForm K V₁) (B₂ : LinearMap.BilinForm K V₂) :
    (B₁.tmul B₂).flip = B₁.flip.tmul B₂.flip := by
  ext x₁ x₂ y₁ y₂
  rfl

/-- The tensor product of nondegenerate bilinear forms over a field is nondegenerate (Humphreys,
GSM 94, Proposition 3.14 (c)). No finiteness is assumed. -/
theorem Nondegenerate.tmul (h₁ : B₁.Nondegenerate) (h₂ : B₂.Nondegenerate) :
    (B₁.tmul B₂).Nondegenerate := by
  refine ⟨separatingLeft_tmul h₁.1 h₂.1, ?_⟩
  rw [← LinearMap.flip_separatingLeft, flip_tmul]
  exact separatingLeft_tmul (LinearMap.flip_separatingLeft.mpr h₁.2)
    (LinearMap.flip_separatingLeft.mpr h₂.2)

end LinearMap.BilinForm

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule TwistedDual

section Contravariant

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra

/-- A bilinear form `B` on a `𝔤`-module is *contravariant* if it is symmetric and
`B(x u, w) = B(u, σ(x) w)` for `x ∈ 𝔤`, `σ = transpose P` (Humphreys, GSM 94, §3.14, where `σ`
is written `τ` and the identity is required for `x ∈ U(𝔤)`; see
`IsContravariantForm.apply_rep_left`). -/
structure IsContravariantForm (B : LinearMap.BilinForm K V) : Prop where
  isSymm : B.IsSymm
  lie_left : ∀ (x : P.KacMoodyAlgebra) (u w : V), B ⁅x, u⁆ w = B u ⁅transpose P x, w⁆

variable {P}

namespace IsContravariantForm

variable {B : LinearMap.BilinForm K V}

omit [LieModule K P.KacMoodyAlgebra V] in
lemma lie_right (hB : IsContravariantForm P B) (x : P.KacMoodyAlgebra) (u w : V) :
    B u ⁅x, w⁆ = B ⁅transpose P x, u⁆ w := by
  rw [hB.lie_left, transpose_transpose]

/-- Contravariance for the action of `U(𝔤)`: `B(a u, w) = B(u, σ(a) w)` (the definition of
Humphreys, GSM 94, §3.14). -/
theorem apply_rep_left (hB : IsContravariantForm P B) (a : 𝓤) (u w : V) :
    B (rep P V a u) w = B u (rep P V (envTranspose P a).unop w) := by
  induction a using UniversalEnvelopingAlgebra.induction generalizing u w with
  | algebraMap r => simp [Module.algebraMap_end_apply]
  | ι x => rw [rep_ι, envTranspose_ι, MulOpposite.unop_op, rep_ι, hB.lie_left]
  | mul a b ha hb => rw [map_mul, Module.End.mul_apply, ha, hb, unop_envTranspose_mul, map_mul,
      Module.End.mul_apply]
  | add a b ha hb => simp only [map_add, MulOpposite.unop_add, LinearMap.add_apply, ha, hb]

/-- **Proposition 3.14 (a)** (Humphreys, GSM 94): weight vectors of distinct weights are
orthogonal for a contravariant form. -/
theorem apply_eq_zero_of_ne (hB : IsContravariantForm P B) {μ ν : Dual K H} {u w : V}
    (hu : u ∈ weightSpaceOfMap V (h P) μ) (hw : w ∈ weightSpaceOfMap V (h P) ν) (hne : μ ≠ ν) :
    B u w = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := by
    by_contra hc
    push Not at hc
    exact hne (LinearMap.ext hc)
  have h1 := hB.lie_left (h P a) u w
  rw [transpose_h, hu a, hw a, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul,
    smul_eq_mul] at h1
  have h2 : (μ a - ν a) * B u w = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)

omit [LieModule K P.KacMoodyAlgebra V] in
/-- The pullback of a contravariant form along a morphism out of `M(λ)` is the Shapovalov form
times its value at `v⁺`. -/
theorem compl₁₂_eq_smul_contravariantForm (hB : IsContravariantForm P B) {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) :
    B.compl₁₂ (φ : VermaModule P Λ →ₗ[K] V) (φ : VermaModule P Λ →ₗ[K] V) =
      B (φ (hwv P Λ)) (φ (hwv P Λ)) • VermaModule.contravariantForm P Λ := by
  have := eq_smul_contravariantForm P Λ
    (B.compl₁₂ (φ : VermaModule P Λ →ₗ[K] V) (φ : VermaModule P Λ →ₗ[K] V)) fun x u w ↦ by
      simp only [LinearMap.compl₁₂_apply, LieModuleHom.coe_toLinearMap, LieModuleHom.map_lie,
        hB.lie_left]
  rw [this]
  rfl

omit [LieModule K P.KacMoodyAlgebra V] in
/-- **Proposition 3.14 (b)** (Humphreys, GSM 94): on a quotient `V` of `M(λ)`, two contravariant
forms with the same value at the image of `v⁺` are equal. -/
theorem eq_of_apply_eq {B' : LinearMap.BilinForm K V} (hB : IsContravariantForm P B)
    (hB' : IsContravariantForm P B') {Λ : Dual K H} (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V)
    (hφ : Function.Surjective φ)
    (h : B (φ (hwv P Λ)) (φ (hwv P Λ)) = B' (φ (hwv P Λ)) (φ (hwv P Λ))) :
    B = B' := by
  have h1 := hB.compl₁₂_eq_smul_contravariantForm φ
  have h2 := hB'.compl₁₂_eq_smul_contravariantForm φ
  rw [h, ← h2] at h1
  ext u w
  obtain ⟨u, rfl⟩ := hφ u
  obtain ⟨w, rfl⟩ := hφ w
  exact LinearMap.congr_fun₂ h1 u w

omit [LieModule K P.KacMoodyAlgebra V] in
/-- A nonzero contravariant form on a quotient of `M(λ)` is nonzero at the image of `v⁺`
(Humphreys, GSM 94, Proposition 3.14 (b)). -/
theorem apply_hwv_ne_zero (hB : IsContravariantForm P B) (hB0 : B ≠ 0) {Λ : Dual K H}
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ) :
    B (φ (hwv P Λ)) (φ (hwv P Λ)) ≠ 0 := fun h ↦
  hB0 (hB.eq_of_apply_eq ⟨⟨fun _ _ ↦ by simp⟩, fun _ _ _ ↦ by simp⟩ φ hφ (by simpa using h))

/-- **Proposition 3.14 (d)** (Humphreys, GSM 94): the orthogonal `N^⊥ = {v | B(v, N) = 0}` of a
submodule `N` for a contravariant form is a submodule. -/
def orthogonal (hB : IsContravariantForm P B) (N : LieSubmodule K P.KacMoodyAlgebra V) :
    LieSubmodule K P.KacMoodyAlgebra V where
  carrier := {v | ∀ w ∈ N, B v w = 0}
  add_mem' hv hv' w hw := by rw [map_add, LinearMap.add_apply, hv w hw, hv' w hw, add_zero]
  zero_mem' _ _ := by rw [map_zero, LinearMap.zero_apply]
  smul_mem' c v hv w hw := by rw [map_smul, LinearMap.smul_apply, hv w hw, smul_zero]
  lie_mem {x v} hv w hw := by
    rw [hB.lie_left]
    exact hv _ (N.lie_mem hw)

omit [LieModule K P.KacMoodyAlgebra V] in
@[simp] lemma mem_orthogonal (hB : IsContravariantForm P B)
    (N : LieSubmodule K P.KacMoodyAlgebra V) (v : V) :
    v ∈ hB.orthogonal N ↔ ∀ w ∈ N, B v w = 0 := Iff.rfl

end IsContravariantForm

section Tensor

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [LieRingModule P.KacMoodyAlgebra V₁]
  [LieModule K P.KacMoodyAlgebra V₁] [AddCommGroup V₂] [Module K V₂]
  [LieRingModule P.KacMoodyAlgebra V₂] [LieModule K P.KacMoodyAlgebra V₂]
  {B₁ : LinearMap.BilinForm K V₁} {B₂ : LinearMap.BilinForm K V₂}

/-- **Proposition 3.14 (c)** (Humphreys, GSM 94): the tensor product
`(v ⊗ w, v' ⊗ w') = (v, v')(w, w')` of contravariant forms is contravariant. It is
nondegenerate when both factors are (`LinearMap.BilinForm.Nondegenerate.tmul`). -/
theorem IsContravariantForm.tmul (h₁ : IsContravariantForm P B₁)
    (h₂ : IsContravariantForm P B₂) : IsContravariantForm P (B₁.tmul B₂) := by
  refine ⟨LinearMap.BilinForm.isSymm_iff.mpr (LinearMap.IsSymm.tmul
    (LinearMap.BilinForm.isSymm_iff.mp h₁.isSymm) (LinearMap.BilinForm.isSymm_iff.mp h₂.isSymm)),
    fun x t t' ↦ ?_⟩
  induction t with
  | add t₁ t₂ ht₁ ht₂ => rw [lie_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      ht₁, ht₂]
  | tmul v w =>
    induction t' with
    | add t₁ t₂ ht₁ ht₂ => rw [map_add, lie_add, map_add, ht₁, ht₂]
    | tmul v' w' =>
      simp only [LieModule.lie_tmul_right, map_add, LinearMap.add_apply,
        LinearMap.BilinForm.tensorDistrib_tmul, h₁.lie_left, h₂.lie_left, smul_eq_mul]

end Tensor

/-- **Proposition 3.14 (e)** (Humphreys, GSM 94), in finite type: for a contravariant form, the
generalized central blocks `V^{χ₁}`, `V^{χ₂}` for distinct central characters are orthogonal.
Humphreys states it for modules in `𝒪`; here `V` is arbitrary. The proof uses `σ(z) = z` for `z`
central (`unop_envTranspose_center`). -/
theorem IsContravariantForm.apply_eq_zero_of_centralBlock {ι H : Type*} {K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    {A : Matrix ι ι ℤ} {P : Realization A K H} (hA : A.IsFiniteCartan) {V : Type*} [AddCommGroup V]
    [Module K V] [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
    {B : LinearMap.BilinForm K V} (hB : IsContravariantForm P B)
    {χ₁ χ₂ : Subalgebra.center K (UniversalEnvelopingAlgebra K P.KacMoodyAlgebra) →ₐ[K] K}
    (hχ : χ₁ ≠ χ₂) {u w : V} (hu : u ∈ centralBlock P V χ₁) (hw : w ∈ centralBlock P V χ₂) :
    B u w = 0 := by
  obtain ⟨z, hz⟩ : ∃ z, χ₁ z ≠ χ₂ z := by
    by_contra hc
    push Not at hc
    exact hχ (AlgHom.ext hc)
  set c₁ := χ₁ z
  set c₂ := χ₂ z
  set T₁ := rep P V (z : UniversalEnvelopingAlgebra K P.KacMoodyAlgebra) - c₁ • 1
  set T₂ := rep P V (z : UniversalEnvelopingAlgebra K P.KacMoodyAlgebra) - c₂ • 1
  have hid : ∀ u w : V, B (T₁ u) w - B u (T₂ w) = (c₂ - c₁) * B u w := by
    intro u w
    have h := hB.apply_rep_left (z : UniversalEnvelopingAlgebra K P.KacMoodyAlgebra) u w
    rw [unop_envTranspose_center P hA z] at h
    simp only [T₁, T₂, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h]
    ring
  have key : ∀ n m (u w : V), (T₁ ^ n) u = 0 → (T₂ ^ m) w = 0 → B u w = 0 := by
    intro n
    induction n with
    | zero =>
      intro m u w hu _
      rw [pow_zero, Module.End.one_apply] at hu
      rw [hu, map_zero, LinearMap.zero_apply]
    | succ n ihn =>
      intro m
      induction m with
      | zero =>
        intro u w _ hw
        rw [pow_zero, Module.End.one_apply] at hw
        rw [hw, map_zero]
      | succ m ihm =>
        intro u w hu hw
        rw [pow_succ, Module.End.mul_apply] at hu hw
        have h1 : B (T₁ u) w = 0 :=
          ihn (m + 1) _ _ hu (by rw [pow_succ, Module.End.mul_apply]; exact hw)
        have h2 : B u (T₂ w) = 0 := ihm u _ (by rw [pow_succ, Module.End.mul_apply]; exact hu) hw
        have h3 := hid u w
        rw [h1, h2, sub_zero] at h3
        exact (mul_eq_zero.mp h3.symm).resolve_left (sub_ne_zero.mpr (Ne.symm hz))
  obtain ⟨n, hn⟩ := (mem_centralBlock P χ₁ u).mp hu z
  obtain ⟨m, hm⟩ := (mem_centralBlock P χ₂ w).mp hw z
  exact key n m u w hn hm

/-! ### Existence: Theorem 3.15 -/

section Existence

variable {B : LinearMap.BilinForm K V} {Λ : Dual K H}

/-- The radical `{v | B(v, V) = 0}` of a contravariant form, as a submodule. -/
abbrev IsContravariantForm.radical (hB : IsContravariantForm P B) :
    LieSubmodule K P.KacMoodyAlgebra V :=
  hB.orthogonal ⊤

omit [LieModule K P.KacMoodyAlgebra V] in
lemma IsContravariantForm.mem_radical (hB : IsContravariantForm P B) (v : V) :
    v ∈ hB.radical ↔ ∀ w, B v w = 0 :=
  ⟨fun h w ↦ h w (LieSubmodule.mem_top w), fun h w _ ↦ h w⟩

variable (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ)

omit [LieModule K P.KacMoodyAlgebra V] in
lemma ker_le_maxSubmodule (h0 : φ (hwv P Λ) ≠ 0) : φ.ker ≤ maxSubmodule P Λ :=
  (le_maxSubmodule_iff P Λ φ.ker).mpr fun h ↦ h0 <| by
    have : hwv P Λ ∈ φ.ker := by rw [h]; exact LieSubmodule.mem_top _
    exact LieModuleHom.mem_ker.mp this

omit [LieModule K P.KacMoodyAlgebra V] in
include hφ in
/-- **Theorem 3.15** (Humphreys, GSM 94), existence: a nonzero quotient `V` of `M(λ)` carries a
contravariant form `B` with `B(v⁺, v⁺) = 1`, whose radical is the image `φ(N(λ))` of the maximal
submodule `N(λ)` of `M(λ)`. Uniqueness up to scalars is `IsContravariantForm.eq_of_apply_eq`.
The form is the Shapovalov form of `M(λ)` descended along `φ`. -/
theorem exists_isContravariantForm_of_surjective (h0 : φ (hwv P Λ) ≠ 0) :
    ∃ B : LinearMap.BilinForm K V, ∃ hB : IsContravariantForm P B,
      B (φ (hwv P Λ)) (φ (hwv P Λ)) = 1 ∧ hB.radical = (maxSubmodule P Λ).map φ := by
  set S := VermaModule.contravariantForm P Λ
  obtain ⟨g, hg⟩ := (φ : VermaModule P Λ →ₗ[K] V).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hφ)
  have hgφ : ∀ u, g (φ u) - u ∈ maxSubmodule P Λ := fun u ↦
    ker_le_maxSubmodule φ h0 (by
      rw [LieModuleHom.mem_ker, map_sub]
      have := LinearMap.congr_fun hg (φ u)
      simp only [LinearMap.comp_apply, LinearMap.id_apply, LieModuleHom.coe_toLinearMap] at this
      rw [this, sub_self])
  have hS : ∀ u u' w, u - u' ∈ maxSubmodule P Λ → S u w = S u' w := fun u u' w h ↦ by
    have := LinearMap.congr_fun (contravariantForm_eq_zero_of_mem P Λ h) w
    rwa [map_sub, LinearMap.sub_apply, LinearMap.zero_apply, sub_eq_zero] at this
  let B := S.compl₁₂ g g
  have hBφ : ∀ u w, B (φ u) (φ w) = S u w := fun u w ↦ by
    change S (g (φ u)) (g (φ w)) = S u w
    rw [hS _ _ _ (hgφ u), (isSymm_contravariantForm P Λ).eq, hS _ _ _ (hgφ w),
      (isSymm_contravariantForm P Λ).eq]
  have hB : IsContravariantForm P B := by
    refine ⟨⟨fun v w ↦ ?_⟩, fun x v w ↦ ?_⟩
    · obtain ⟨u, rfl⟩ := hφ v
      obtain ⟨u', rfl⟩ := hφ w
      rw [hBφ, hBφ, (isSymm_contravariantForm P Λ).eq]
    · obtain ⟨u, rfl⟩ := hφ v
      obtain ⟨u', rfl⟩ := hφ w
      rw [← LieModuleHom.map_lie, ← LieModuleHom.map_lie, hBφ, hBφ, contravariantForm_lie_left]
  refine ⟨B, hB, by rw [hBφ, contravariantForm_hwv_hwv], ?_⟩
  ext v
  obtain ⟨u, rfl⟩ := hφ v
  rw [hB.mem_radical, LieSubmodule.mem_map]
  constructor
  · intro h
    refine ⟨u, (mem_maxSubmodule_iff P Λ u).mpr fun w ↦ ?_, rfl⟩
    rw [← hBφ]
    exact h (φ w)
  · rintro ⟨m, hm, hmu⟩ w
    obtain ⟨w, rfl⟩ := hφ w
    rw [hBφ]
    have hmu' : u - m ∈ maxSubmodule P Λ :=
      ker_le_maxSubmodule φ h0 (by rw [LieModuleHom.mem_ker, map_sub, hmu, sub_self])
    have := (maxSubmodule P Λ).add_mem hmu' hm
    rw [sub_add_cancel] at this
    exact (mem_maxSubmodule_iff P Λ u).mp this w

include hφ in
/-- **Theorem 3.15** (Humphreys, GSM 94), last assertion: a contravariant form on a quotient `V`
of `M(λ)` which is nonzero at `v⁺` is nondegenerate iff `V ≅ L(λ)`. -/
theorem IsContravariantForm.nondegenerate_iff_nonempty_equiv (hB : IsContravariantForm P B)
    (hB0 : B (φ (hwv P Λ)) (φ (hwv P Λ)) ≠ 0) :
    B.Nondegenerate ↔ Nonempty (V ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P Λ) := by
  have h0 : φ (hwv P Λ) ≠ 0 := fun h ↦ hB0 (by simp [h])
  have hleft : B.Nondegenerate ↔ hB.radical = ⊥ := by
    rw [LieSubmodule.eq_bot_iff]
    refine ⟨fun h v hv ↦ h.1 v ((hB.mem_radical v).mp hv), fun h ↦ ?_⟩
    have hsep : B.SeparatingLeft := fun v hv ↦ h v ((hB.mem_radical v).mpr hv)
    refine ⟨hsep, fun w hw ↦ hsep w fun v ↦ ?_⟩
    rw [hB.isSymm.eq]
    exact hw v
  rw [hleft]
  constructor
  · intro hrad
    have hpull := hB.compl₁₂_eq_smul_contravariantForm φ
    have hker : φ.ker = maxSubmodule P Λ := by
      refine le_antisymm (ker_le_maxSubmodule φ h0) fun m hm ↦ ?_
      rw [LieModuleHom.mem_ker]
      have : φ m ∈ hB.radical := (hB.mem_radical _).mpr fun w ↦ by
        obtain ⟨w, rfl⟩ := hφ w
        have := LinearMap.congr_fun₂ hpull m w
        simp only [LinearMap.compl₁₂_apply, LieModuleHom.coe_toLinearMap,
          LinearMap.smul_apply] at this
        rw [this, (mem_maxSubmodule_iff P Λ m).mp hm w, smul_zero]
      rw [hrad] at this
      exact (LieSubmodule.mem_bot _).mp this
    obtain ⟨e⟩ := LieSubmodule.Quotient.nonempty_lieModuleEquiv_of_surjective _ φ hφ hker
    exact ⟨e.symm⟩
  · rintro ⟨e⟩
    have := IrreducibleModule.isIrreducible P Λ
    rcases IsSimpleOrder.eq_bot_or_eq_top (hB.radical.map e.toLieModuleHom) with h | h
    · rw [LieSubmodule.eq_bot_iff]
      intro v hv
      have : e v ∈ hB.radical.map e.toLieModuleHom := LieSubmodule.mem_map_of_mem hv
      rw [h, LieSubmodule.mem_bot] at this
      exact e.injective (by rw [this, map_zero])
    · exfalso
      have : e (φ (hwv P Λ)) ∈ hB.radical.map e.toLieModuleHom := h ▸ LieSubmodule.mem_top _
      obtain ⟨v, hv, hev⟩ := (LieSubmodule.mem_map _).mp this
      have hv' : v = φ (hwv P Λ) := e.injective hev
      exact hB0 ((hB.mem_radical _).mp (hv' ▸ hv) _)

end Existence

end Contravariant

end Matrix.Realization.KacMoodyAlgebra

end
