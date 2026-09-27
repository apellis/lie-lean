/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.Derivation.BaseChange
import Mathlib.Algebra.Lie.SemiDirect
import LieLean.Algebra.Lie.KacMoody.ToLieAlgebra

/-!
# `Matrix.ToLieAlgebra` is the derived algebra `𝔤'(A)`

Let `A` be a symmetrizable generalized Cartan matrix and `K` a field of characteristic zero. We
show that the morphism `Matrix.ToLieAlgebra K A → 𝔤(A)`, `Hᵢ ↦ αᵢ^∨`, `Eᵢ ↦ eᵢ`, `Fᵢ ↦ fᵢ`, is
injective, so that `Matrix.ToLieAlgebra K A` is isomorphic to the derived algebra
`𝔤'(A) = [𝔤(A), 𝔤(A)]`: `𝔤'(A)` is presented by the Chevalley generators `eᵢ, fᵢ, αᵢ^∨` and the
Chevalley–Serre relations ([Kac] §9.11 (check)). For singular `A` this is a genuine refinement
of `Matrix.Realization.KacMoodyAlgebra.toLieAlgebraEquiv`, since then `𝔤'(A) ≠ 𝔤(A)`.

## Proof

The argument is our own (a standard "grading and derivations" construction). Let
`T = Matrix.ToLieAlgebra K A`, `B = K[𝔥*]` the group algebra of the additive group `𝔥*` (with
basis `t^μ`) and `N = B ⊗ T` the base change of `T`.
1. There is a morphism `Γ : T → N`, `Hᵢ ↦ 1 ⊗ Hᵢ`, `Eᵢ ↦ t^{αᵢ} ⊗ Eᵢ`, `Fᵢ ↦ t^{-αᵢ} ⊗ Fᵢ`
   (`Matrix.ToLieAlgebra.gradingHom`), which is injective since composing it with the
   evaluation `t^μ ↦ 1` gives the identity.
2. For `a ∈ 𝔥`, `t^μ ↦ ⟨μ, a⟩ t^μ` is a derivation `∂ₐ` of `B`, hence induces a derivation of
   `N`; these derivations commute. Let `M = N ⋊ Der(B)` be the semidirect product.
3. Choose a linear projection `p` of `𝔥` onto the span `𝔥'` of the coroots and let
   `Φ : 𝔥' → T`, `αᵢ^∨ ↦ Hᵢ`. Then `eᵢ ↦ Γ(Eᵢ)`, `fᵢ ↦ Γ(Fᵢ)`,
   `a ↦ (1 ⊗ Φ(p a), ∂_{a - p a})` satisfies the relations (1.2.1) of `𝔤̃(A)` and the Serre
   relations, so defines a morphism `𝔤̃(A) → M` killing the Serre ideal. By the Gabber–Kac
   theorem ([Kac] Thm. 9.11) it factors through `Ψ : 𝔤(A) → M`.
4. `Ψ` composed with `T → 𝔤(A)` is `Γ` (followed by `N ⊆ M`), which is injective.

## Main definitions

* `AddMonoidAlgebra.degreeDerivation`: the derivation `t^g ↦ χ(g) t^g` of `K[G]` given by an
  additive character `χ : G →+ K`.
* `LieAlgebra.ExtendScalars.evalHom`: the morphism `A ⊗ L → L` induced by `φ : A →ₐ[R] R`.
* `Matrix.ToLieAlgebra.gradingHom`: the morphism `Γ` above, for any family `μ : ι → G`.
* `Matrix.Realization.KacMoodyAlgebra.toLieAlgebraEquivDerived`: the isomorphism
  `Matrix.ToLieAlgebra K A ≃ 𝔤'(A)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.ofToLieAlgebra_injective`: the morphism
  `Matrix.ToLieAlgebra K A → 𝔤(A)` is injective for a symmetrizable generalized Cartan matrix.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §1.3, §9.11 (check).
-/

open Module TensorProduct LieAlgebra LieAlgebra.ExtendScalars

noncomputable section

/-! ### Degree derivations of group algebras -/

namespace AddMonoidAlgebra

variable {K G : Type*} [CommRing K] [AddCommMonoid G]

/-- The linear map `t^g ↦ χ(g) t^g` of `K[G]`. -/
def degreeLinearMap (χ : G →+ K) : K[G] →ₗ[K] K[G] :=
  (coeffLinearEquiv K).symm.toLinearMap ∘ₗ
    Finsupp.lsum K (fun g ↦ χ g • Finsupp.lsingle g) ∘ₗ (coeffLinearEquiv K).toLinearMap

@[simp] lemma degreeLinearMap_single (χ : G →+ K) (g : G) (c : K) :
    degreeLinearMap χ (single g c) = single g (χ g * c) := by
  simp [degreeLinearMap, ← ofCoeff_single]

/-- The derivation `t^g ↦ χ(g) t^g` of `K[G]` given by an additive character `χ : G →+ K`. -/
def degreeDerivation (χ : G →+ K) : Derivation K K[G] K[G] :=
  Derivation.mk' (degreeLinearMap χ) fun a b ↦ by
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [add_mul, map_add, hx, hy, smul_eq_mul, mul_add]; abel
    | single g c =>
      induction b using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simp only [mul_add, map_add, hx, hy, smul_eq_mul, add_mul]; abel
      | single g' c' =>
        simp only [single_mul_single, degreeLinearMap_single, smul_eq_mul, map_add]
        rw [add_comm g' g, ← single_add]
        congr 1
        ring

@[simp] lemma degreeDerivation_single (χ : G →+ K) (g : G) (c : K) :
    degreeDerivation χ (single g c) = single g (χ g * c) :=
  degreeLinearMap_single χ g c

/-- Derivations of `K[G]` are determined by their values on the `single g c`. -/
lemma derivation_ext {D₁ D₂ : Derivation K K[G] K[G]}
    (h : ∀ g c, D₁ (single g c) = D₂ (single g c)) : D₁ = D₂ :=
  Derivation.ext fun x ↦ by
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | single g c => exact h g c

/-- Degree derivations commute. -/
lemma lie_degreeDerivation (χ χ' : G →+ K) :
    ⁅degreeDerivation χ, degreeDerivation χ'⁆ = 0 :=
  derivation_ext fun g c ↦ by
    rw [Derivation.commutator_apply, Derivation.zero_apply, degreeDerivation_single,
      degreeDerivation_single,
      degreeDerivation_single, degreeDerivation_single, sub_eq_zero, mul_left_comm]

end AddMonoidAlgebra

/-! ### Evaluation of a base change -/

namespace LieAlgebra.ExtendScalars

variable {R A L : Type*} [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]

/-- The morphism `A ⊗ L → L`, `a ⊗ x ↦ φ(a) x`, induced by an algebra morphism `φ : A → R`. -/
def evalHom (φ : A →ₐ[R] R) : A ⊗[R] L →ₗ⁅R⁆ L :=
  { TensorProduct.lift ((LinearMap.lsmul R L).comp φ.toLinearMap) with
    map_lie' := by
      intro x y
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      induction x using TensorProduct.inductionOn with
      | add x x' hx hx' => rw [add_lie, map_add, map_add, hx, hx', add_lie]
      | tmul a x =>
        induction y using TensorProduct.inductionOn with
        | add y y' hy hy' => rw [lie_add, map_add, map_add, hy, hy', lie_add]
        | tmul b y => simp [bracket_tmul, mul_smul, smul_comm (φ a)] }

@[simp] lemma evalHom_tmul (φ : A →ₐ[R] R) (a : A) (x : L) :
    evalHom φ (a ⊗ₜ x) = φ a • x :=
  TensorProduct.lift.tmul _ _

lemma ad_tmul_pow_tmul (s t : A) (x y : L) (n : ℕ) :
    (ad R (A ⊗[R] L) (s ⊗ₜ x) ^ n) (t ⊗ₜ y) = (s ^ n * t) ⊗ₜ ((ad R L x ^ n) y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, ad_apply, bracket_tmul, pow_succ' (ad R L x),
      Module.End.mul_apply, ad_apply, pow_succ', mul_assoc]

end LieAlgebra.ExtendScalars

/-! ### The grading morphism `Γ` -/

namespace Matrix.ToLieAlgebra

open AddMonoidAlgebra

variable {ι : Type*} [DecidableEq ι] (K : Type*) [CommRing K] (A : Matrix ι ι ℤ)
  {G : Type*} [AddCommGroup G]

/-- The morphism `Matrix.ToLieAlgebra K A → K[G] ⊗ Matrix.ToLieAlgebra K A`,
`Hᵢ ↦ 1 ⊗ Hᵢ`, `Eᵢ ↦ t^{μᵢ} ⊗ Eᵢ`, `Fᵢ ↦ t^{-μᵢ} ⊗ Fᵢ`, for a family `μ : ι → G`. -/
def gradingHom (μ : ι → G) :
    Matrix.ToLieAlgebra K A →ₗ⁅K⁆ K[G] ⊗[K] Matrix.ToLieAlgebra K A :=
  lift
    { h i := 1 ⊗ₜ h K A i
      e i := AddMonoidAlgebra.single (μ i) 1 ⊗ₜ e K A i
      f i := AddMonoidAlgebra.single (-μ i) 1 ⊗ₜ f K A i
      lie_h_h i j := by rw [bracket_tmul, lie_h_h, tmul_zero]
      lie_e_f i j := by
        rw [bracket_tmul, lie_e_f, single_mul_single]
        split_ifs with hij
        · rw [hij, add_neg_cancel, mul_one, ← one_def]
        · rw [tmul_zero]
      lie_h_e i j := by rw [bracket_tmul, lie_h_e, one_mul, tmul_smul]
      lie_h_f i j := by rw [bracket_tmul, lie_h_f, one_mul, tmul_neg, tmul_smul]
      serre_e i j _ := by rw [bracket_tmul, ad_tmul_pow_tmul, serre_e, tmul_zero]
      serre_f i j _ := by rw [bracket_tmul, ad_tmul_pow_tmul, serre_f, tmul_zero] }

variable {K A}

@[simp] lemma gradingHom_h (μ : ι → G) (i : ι) :
    gradingHom K A μ (h K A i) = 1 ⊗ₜ h K A i :=
  lift_h _ i

@[simp] lemma gradingHom_e (μ : ι → G) (i : ι) :
    gradingHom K A μ (e K A i) = AddMonoidAlgebra.single (μ i) 1 ⊗ₜ e K A i :=
  lift_e _ i

@[simp] lemma gradingHom_f (μ : ι → G) (i : ι) :
    gradingHom K A μ (f K A i) = AddMonoidAlgebra.single (-μ i) 1 ⊗ₜ f K A i :=
  lift_f _ i

variable (K G) in
/-- The augmentation `K[G] → K`, `t^g ↦ 1`. -/
abbrev augmentation : K[G] →ₐ[K] K := AddMonoidAlgebra.lift K K G 1

lemma augmentation_single (g : G) (c : K) :
    augmentation K G (AddMonoidAlgebra.single g c) = c := by
  simp [AddMonoidAlgebra.lift_single]

lemma evalHom_comp_gradingHom (μ : ι → G) :
    (evalHom (augmentation K G)).comp (gradingHom K A μ) = LieHom.id := by
  ext i <;> simp

lemma gradingHom_injective (μ : ι → G) : Function.Injective (gradingHom K A μ) :=
  fun x y hxy ↦ by
    have h := congr(evalHom (augmentation K G) $hxy)
    rwa [← LieHom.comp_apply, ← LieHom.comp_apply, evalHom_comp_gradingHom, LieHom.id_apply,
      LieHom.id_apply] at h

end Matrix.ToLieAlgebra

/-! ### Injectivity of `Matrix.ToLieAlgebra K A → 𝔤(A)` -/

namespace Matrix.Realization.KacMoodyAlgebra

open Matrix.ToLieAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- The group algebra `K[𝔥*]`. -/
local notation "𝔅" => AddMonoidAlgebra K (Dual K H)

/-- The base change `K[𝔥*] ⊗ Matrix.ToLieAlgebra K A`. -/
local notation "𝔑" => 𝔅 ⊗[K] Matrix.ToLieAlgebra K A

/-- The semidirect product `(K[𝔥*] ⊗ Matrix.ToLieAlgebra K A) ⋊ Der(K[𝔥*])`. -/
local notation "𝔐" =>
  𝔑 ⋊⁅Lie.Derivation.ofDerivation (A := 𝔅) (Matrix.ToLieAlgebra K A)⁆ Derivation K 𝔅 𝔅

variable (K H) in
/-- The degree derivations `t^μ ↦ ⟨μ, a⟩ t^μ` of `K[𝔥*]`, as a linear map in `a ∈ 𝔥`. -/
def degreeDer : H →ₗ[K] Derivation K 𝔅 𝔅 where
  toFun a := AddMonoidAlgebra.degreeDerivation
    (AddMonoidHom.mk' (fun μ : Dual K H ↦ μ a) fun _ _ ↦ rfl)
  map_add' a b := AddMonoidAlgebra.derivation_ext fun g c ↦ by simp [add_mul]
  map_smul' r a := AddMonoidAlgebra.derivation_ext fun g c ↦ by simp [mul_assoc]

@[simp] lemma degreeDer_single (a : H) (μ : Dual K H) (c : K) :
    degreeDer K H a (AddMonoidAlgebra.single μ c) = AddMonoidAlgebra.single μ (μ a * c) := by
  simp [degreeDer]

lemma lie_degreeDer (a b : H) : ⁅degreeDer K H a, degreeDer K H b⁆ = 0 :=
  AddMonoidAlgebra.lie_degreeDerivation _ _

/-- The span `𝔥'` of the simple coroots. -/
local notation "𝔥'" => Submodule.span K (Set.range P.coroot)

/-- The linear map `𝔥' → Matrix.ToLieAlgebra K A`, `αᵢ^∨ ↦ Hᵢ`. -/
def corootSpanToLieAlgebra : 𝔥' →ₗ[K] Matrix.ToLieAlgebra K A :=
  (Basis.span P.linearIndependent_coroot).constr K (Matrix.ToLieAlgebra.h K A)

lemma corootSpanToLieAlgebra_coroot (i : ι) :
    corootSpanToLieAlgebra P ⟨P.coroot i, Submodule.subset_span ⟨i, rfl⟩⟩ =
      Matrix.ToLieAlgebra.h K A i := by
  rw [corootSpanToLieAlgebra, ← Basis.span_apply P.linearIndependent_coroot, Basis.constr_basis]

omit [DecidableEq ι] in
/-- Induction on `𝔥'` along the simple coroots. -/
lemma corootSpan_induction {p : 𝔥' → Prop} (x : 𝔥')
    (hc : ∀ i, p ⟨P.coroot i, Submodule.subset_span ⟨i, rfl⟩⟩) (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y)) (hsmul : ∀ (c : K) x, p x → p (c • x)) : p x := by
  have hx : x ∈ Submodule.span K (Set.range (Basis.span P.linearIndependent_coroot)) := by
    rw [Basis.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; rw [Basis.span_apply]; exact hc i
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

lemma lie_corootSpanToLieAlgebra (x y : 𝔥') :
    ⁅corootSpanToLieAlgebra P x, corootSpanToLieAlgebra P y⁆ = 0 := by
  induction x using corootSpan_induction P with
  | hc i =>
    induction y using corootSpan_induction P with
    | hc j =>
      rw [corootSpanToLieAlgebra_coroot, corootSpanToLieAlgebra_coroot,
        Matrix.ToLieAlgebra.lie_h_h]
    | h0 => simp
    | hadd y y' hy hy' => rw [map_add, lie_add, hy, hy', add_zero]
    | hsmul c y hy => rw [map_smul, lie_smul, hy, smul_zero]
  | h0 => simp
  | hadd x x' hx hx' => rw [map_add, add_lie, hx, hx', add_zero]
  | hsmul c x hx => rw [map_smul, smul_lie, hx, smul_zero]

lemma lie_corootSpanToLieAlgebra_e (x : 𝔥') (j : ι) :
    ⁅corootSpanToLieAlgebra P x, Matrix.ToLieAlgebra.e K A j⁆ =
      P.root j x • Matrix.ToLieAlgebra.e K A j := by
  induction x using corootSpan_induction P with
  | hc i =>
    rw [corootSpanToLieAlgebra_coroot, Matrix.ToLieAlgebra.lie_h_e, root_coroot,
      Int.cast_smul_eq_zsmul]
  | h0 => simp
  | hadd x y hx hy => rw [map_add, add_lie, hx, hy, Submodule.coe_add, map_add, add_smul]
  | hsmul c x hx =>
    rw [map_smul, smul_lie, hx, Submodule.coe_smul, map_smul, smul_eq_mul, mul_smul]

lemma lie_corootSpanToLieAlgebra_f (x : 𝔥') (j : ι) :
    ⁅corootSpanToLieAlgebra P x, Matrix.ToLieAlgebra.f K A j⁆ =
      -(P.root j x • Matrix.ToLieAlgebra.f K A j) := by
  induction x using corootSpan_induction P with
  | hc i =>
    rw [corootSpanToLieAlgebra_coroot, Matrix.ToLieAlgebra.lie_h_f, root_coroot,
      Int.cast_smul_eq_zsmul]
  | h0 => simp
  | hadd x y hx hy =>
    rw [map_add, add_lie, hx, hy, Submodule.coe_add, map_add, add_smul, neg_add]
  | hsmul c x hx =>
    rw [map_smul, smul_lie, hx, Submodule.coe_smul, map_smul, smul_eq_mul, mul_smul, smul_neg]

/-- A linear projection of `𝔥` onto the span `𝔥'` of the simple coroots. -/
def corootSpanProj : H →ₗ[K] 𝔥' :=
  (𝔥').projectionOnto _ (Submodule.exists_isCompl (𝔥')).choose_spec

omit [DecidableEq ι] in
lemma corootSpanProj_of_mem {a : H} (ha : a ∈ 𝔥') : corootSpanProj P a = ⟨a, ha⟩ :=
  Submodule.projectionOnto_apply_of_mem_left _ ha

/-- The morphism `ψ : Der(K[𝔥*]) → Der(K[𝔥*] ⊗ Matrix.ToLieAlgebra K A)`. -/
local notation "ψ" => Lie.Derivation.ofDerivation (A := 𝔅) (Matrix.ToLieAlgebra K A)

/-- The linear map `𝔥 → 𝔐`, `a ↦ (1 ⊗ Φ(p a), ∂_{a - p a})`. -/
def semidirectH : H →ₗ[K] 𝔐 :=
  (SemiDirectSum.inl ψ).toLinearMap ∘ₗ TensorProduct.mk K 𝔅 _ 1 ∘ₗ
      corootSpanToLieAlgebra P ∘ₗ corootSpanProj P +
    (SemiDirectSum.inr ψ).toLinearMap ∘ₗ degreeDer K H ∘ₗ
      (LinearMap.id - (𝔥').subtype ∘ₗ corootSpanProj P)

lemma semidirectH_apply (a : H) :
    semidirectH P a = ⟨1 ⊗ₜ corootSpanToLieAlgebra P (corootSpanProj P a),
      degreeDer K H (a - corootSpanProj P a)⟩ := by
  simp [semidirectH]

lemma semidirectH_coroot (i : ι) :
    semidirectH P (P.coroot i) = ⟨1 ⊗ₜ Matrix.ToLieAlgebra.h K A i, 0⟩ := by
  rw [semidirectH_apply, corootSpanProj_of_mem P (Submodule.subset_span ⟨i, rfl⟩),
    corootSpanToLieAlgebra_coroot, sub_self, map_zero]

/-- The data defining `𝔤̃(A) → 𝔐`. -/
def semidirectLiftData : AuxLieAlgebra.LiftData P 𝔐 where
  h := semidirectH P
  e i := SemiDirectSum.inl ψ (gradingHom K A P.root (Matrix.ToLieAlgebra.e K A i))
  f i := SemiDirectSum.inl ψ (gradingHom K A P.root (Matrix.ToLieAlgebra.f K A i))
  lie_h_h a b := by
    rw [semidirectH_apply, semidirectH_apply, SemiDirectSum.lie_eq_mk]
    simp [bracket_tmul, lie_corootSpanToLieAlgebra, lie_degreeDer]
  lie_e_f i j := by
    rw [← LieHom.map_lie, ← LieHom.map_lie, Matrix.ToLieAlgebra.lie_e_f]
    split_ifs
    · rw [semidirectH_coroot]; simp
    · simp
  lie_h_e a i := by
    rw [semidirectH_apply]
    ext
    · simp only [Matrix.ToLieAlgebra.gradingHom_e, SemiDirectSum.inl_eq_mk,
        SemiDirectSum.lie_eq_mk, bracket_tmul,
        one_mul, lie_corootSpanToLieAlgebra_e, Lie.Derivation.ofDerivation_apply, map_zero,
        LieDerivation.zero_apply, sub_zero, SemiDirectSum.smul_eq_mk]
      rw [LinearMap.rTensor_tmul, Derivation.coeFn_coe, degreeDer_single,
        ← AddMonoidAlgebra.smul_single', ← smul_tmul', tmul_smul, map_sub]
      module
    · simp
  lie_h_f a i := by
    rw [semidirectH_apply]
    ext
    · simp only [Matrix.ToLieAlgebra.gradingHom_f, SemiDirectSum.inl_eq_mk,
        SemiDirectSum.lie_eq_mk, bracket_tmul,
        one_mul, lie_corootSpanToLieAlgebra_f, Lie.Derivation.ofDerivation_apply, map_zero,
        LieDerivation.zero_apply, sub_zero, SemiDirectSum.smul_eq_mk, SemiDirectSum.neg_eq_mk]
      rw [LinearMap.rTensor_tmul, Derivation.coeFn_coe, degreeDer_single,
        ← AddMonoidAlgebra.smul_single', ← smul_tmul', tmul_neg, tmul_smul, map_sub,
        LinearMap.neg_apply, LinearMap.neg_apply]
      module
    · simp

@[simp] lemma semidirectLiftData_h (a : H) : (semidirectLiftData P).h a = semidirectH P a := rfl

@[simp] lemma semidirectLiftData_e (i : ι) :
    (semidirectLiftData P).e i =
      SemiDirectSum.inl ψ (gradingHom K A P.root (Matrix.ToLieAlgebra.e K A i)) := rfl

@[simp] lemma semidirectLiftData_f (i : ι) :
    (semidirectLiftData P).f i =
      SemiDirectSum.inl ψ (gradingHom K A P.root (Matrix.ToLieAlgebra.f K A i)) := rfl

variable [CharZero K] (hA : A.IsGeneralizedCartan) (hS : A.IsSymmetrizable)

include hA hS in
/-- The morphism `𝔤̃(A) → 𝔐` kills `𝔯`, by the Gabber–Kac theorem. -/
lemma maxIdeal_le_ker_semidirectLift :
    AuxLieAlgebra.maxIdeal P ≤ (AuxLieAlgebra.lift (semidirectLiftData P)).ker := by
  rw [AuxLieAlgebra.maxIdeal_eq_serreIdeal P hA hS, AuxLieAlgebra.serreIdeal,
    LieSubmodule.lieSpan_le]
  rintro x ⟨i, j, -, rfl | rfl⟩
  · have h := congr(SemiDirectSum.inl ψ (gradingHom K A P.root
      $(Matrix.ToLieAlgebra.serre_e K A i j)))
    simp only [LieHom.map_ad_pow, LieHom.map_lie, map_zero] at h
    simp only [SetLike.mem_coe, LieHom.mem_ker, AuxLieAlgebra.serreE, LieHom.map_ad_pow,
      LieHom.map_lie, AuxLieAlgebra.lift_e, semidirectLiftData_e]
    exact h
  · have h := congr(SemiDirectSum.inl ψ (gradingHom K A P.root
      $(Matrix.ToLieAlgebra.serre_f K A i j)))
    simp only [LieHom.map_ad_pow, LieHom.map_lie, map_zero] at h
    simp only [SetLike.mem_coe, LieHom.mem_ker, AuxLieAlgebra.serreF, LieHom.map_ad_pow,
      LieHom.map_lie, AuxLieAlgebra.lift_f, semidirectLiftData_f]
    exact h

/-- The morphism `Ψ : 𝔤(A) → 𝔐`, `eᵢ ↦ (t^{αᵢ} ⊗ Eᵢ, 0)`, `fᵢ ↦ (t^{-αᵢ} ⊗ Fᵢ, 0)`,
`a ↦ (1 ⊗ Φ(p a), ∂_{a - p a})`, for a symmetrizable generalized Cartan matrix. -/
def toSemidirect : P.KacMoodyAlgebra →ₗ⁅K⁆ 𝔐 :=
  LieIdeal.lift _ (AuxLieAlgebra.lift (semidirectLiftData P))
    (maxIdeal_le_ker_semidirectLift P hA hS)

@[simp] lemma toSemidirect_π (x : P.AuxLieAlgebra) :
    toSemidirect P hA hS (π P x) = AuxLieAlgebra.lift (semidirectLiftData P) x :=
  rfl

lemma toSemidirect_comp_ofToLieAlgebra :
    (toSemidirect P hA hS).comp (ofToLieAlgebra P hA) =
      (SemiDirectSum.inl ψ).comp (gradingHom K A P.root) := by
  apply Matrix.ToLieAlgebra.hom_ext <;> intro i
  · rw [LieHom.comp_apply, ofToLieAlgebra_h, ← π_h, toSemidirect_π, AuxLieAlgebra.lift_h,
      semidirectLiftData_h, semidirectH_coroot, LieHom.comp_apply, gradingHom_h]
    rfl
  · rw [LieHom.comp_apply, ofToLieAlgebra_e, ← π_e, toSemidirect_π, AuxLieAlgebra.lift_e,
      semidirectLiftData_e, LieHom.comp_apply]
  · rw [LieHom.comp_apply, ofToLieAlgebra_f, ← π_f, toSemidirect_π, AuxLieAlgebra.lift_f,
      semidirectLiftData_f, LieHom.comp_apply]

include hS in
/-- For a symmetrizable generalized Cartan matrix `A` over a field of characteristic zero, the
morphism `Matrix.ToLieAlgebra K A → 𝔤(A)`, `Hᵢ ↦ αᵢ^∨`, `Eᵢ ↦ eᵢ`, `Fᵢ ↦ fᵢ`, is injective
([Kac] §9.11 (check); the argument is our own, see the module docstring). -/
theorem ofToLieAlgebra_injective : Function.Injective (ofToLieAlgebra P hA) := by
  intro x y hxy
  have h := congr(toSemidirect P hA hS $hxy)
  rw [← LieHom.comp_apply, ← LieHom.comp_apply, toSemidirect_comp_ofToLieAlgebra,
    LieHom.comp_apply, LieHom.comp_apply] at h
  exact gradingHom_injective P.root (SemiDirectSum.inl_injective ψ h)

/-- **Presentation of the derived algebra `𝔤'(A)`** ([Kac] §9.11 (check)). For a symmetrizable
generalized Cartan matrix `A` over a field of characteristic zero, Mathlib's
`Matrix.ToLieAlgebra K A` (generated by `Hᵢ, Eᵢ, Fᵢ` subject to the Chevalley–Serre relations) is
isomorphic to the derived algebra `𝔤'(A) = [𝔤(A), 𝔤(A)]`, via `Hᵢ ↦ αᵢ^∨`, `Eᵢ ↦ eᵢ`,
`Fᵢ ↦ fᵢ`. -/
def toLieAlgebraEquivDerived :
    Matrix.ToLieAlgebra K A ≃ₗ⁅K⁆
      (derivedSeries K P.KacMoodyAlgebra 1 : LieSubalgebra K P.KacMoodyAlgebra) :=
  (LieEquiv.ofInjective _ (ofToLieAlgebra_injective P hA hS)).trans
    (LieEquiv.ofEq _ _ (by rw [range_ofToLieAlgebra_eq_derivedSeries]))

@[simp] lemma coe_toLieAlgebraEquivDerived_apply (x : Matrix.ToLieAlgebra K A) :
    (toLieAlgebraEquivDerived P hA hS x : P.KacMoodyAlgebra) = ofToLieAlgebra P hA x :=
  rfl

end Matrix.Realization.KacMoodyAlgebra

end
