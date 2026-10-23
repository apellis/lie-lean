/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.Cochain
import LieLean.Algebra.Lie.Homology.Weights
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Weight decomposition of the Chevalley–Eilenberg cochain complex

Let `L` be a Lie algebra and `N` an `L`-module over a field `K`, and suppose that a vector space
`H` acts on `L` by derivations `D a` and on `N` compatibly
(`LieModule.ChevalleyEilenberg.DerivAction`; the main example is `L = 𝔫` in a Kac–Moody algebra and
`H = 𝔥`). Then `H` acts on the cochains
`Hom(⋀L, N)` by `(θ(a) f)(c) = φ(a)(f c) - f(D̃(a) c)`, where `D̃(a)` is the derivation of `⋀L`
extending `D a`, and these operators commute with the codifferential. The weight-`μ` cochains
form a subcomplex, whose cohomology is the weight-`μ` part `H^n(L, N)_μ` of the cohomology.

## Main definitions

* `LieModule.ChevalleyEilenberg.extDeriv`: the derivation `D̃` of `⋀L` extending `D : L → L`.
* `LieModule.ChevalleyEilenberg.DerivAction.coAct`: the action `θ` of `H` on `Hom(⋀L, N)`.
* `LieModule.ChevalleyEilenberg.DerivAction.coActDeg`: its restriction to `C^k(L, N)`.
* `LieModule.ChevalleyEilenberg.DerivAction.cochainWeightSpace`: the weight-`μ` cochains
  `C^k(L, N)_μ`.
* `LieModule.ChevalleyEilenberg.DerivAction.weightComplex`: the cochain complex `C^•(L, N)_μ`.

## Main results

* `LieModule.ChevalleyEilenberg.lieDeriv_apply`: the Lie derivative of a cochain is
  `(θ_y f)(c) = f(ad_y c) - y f(c)`.
* `LieModule.ChevalleyEilenberg.DerivAction.cochainDiff_coAct`: `δ ∘ θ(a) = θ(a) ∘ δ`.
* `LieModule.ChevalleyEilenberg.DerivAction.δ_coActDeg`: the same on graded pieces.
-/

open TensorProduct ExteriorAlgebra CategoryTheory

noncomputable section

namespace LieModule.ChevalleyEilenberg

section ExtDeriv

variable {R L : Type*} [CommRing R] [AddCommGroup L] [Module R L]

/-- **Induction principle** for `⋀L`, from the left. -/
theorem exterior_induction {p : ExteriorAlgebra R L → Prop}
    (algebraMap : ∀ r : R, p (algebraMap R _ r)) (add : ∀ c c', p c → p c' → p (c + c'))
    (ι_mul : ∀ (y : L) (c : ExteriorAlgebra R L), p c → p (ι R y * c)) (c : ExteriorAlgebra R L) :
    p c := by
  induction c using CliffordAlgebra.left_induction with
  | algebraMap r => exact algebraMap r
  | add c c' hc hc' => exact add c c' hc hc'
  | ι_mul c y hc => exact ι_mul y c hc

lemma rid_wedge (y : L) (c : ExteriorAlgebra R L ⊗[R] R) :
    TensorProduct.rid R _ (wedge R L R y c) = ι R y * TensorProduct.rid R _ c := by
  induction c with
  | tmul ω r => simp
  | add c c' hc hc' => simp only [map_add, hc, hc', mul_add]

/-- The derivation of `⋀L` extending a linear map `D : L → L`:
`D̃(y₁ ∧ ⋯ ∧ y_k) = ∑ᵢ y₁ ∧ ⋯ ∧ D yᵢ ∧ ⋯ ∧ y_k`. -/
def extDeriv (D : L →ₗ[R] L) : Module.End R (ExteriorAlgebra R L) :=
  (TensorProduct.rid R _).toLinearMap ∘ₗ derivExt (M := R) D 0 ∘ₗ
    (TensorProduct.rid R _).symm.toLinearMap

@[simp] lemma extDeriv_one (D : L →ₗ[R] L) : extDeriv D (1 : ExteriorAlgebra R L) = 0 := by
  simp [extDeriv]

@[simp] lemma extDeriv_algebraMap (D : L →ₗ[R] L) (r : R) :
    extDeriv D (algebraMap R (ExteriorAlgebra R L) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, extDeriv_one, smul_zero]

lemma extDeriv_ι_mul (D : L →ₗ[R] L) (y : L) (c : ExteriorAlgebra R L) :
    extDeriv D (ι R y * c) = ι R (D y) * c + ι R y * extDeriv D c := by
  have h : (TensorProduct.rid R _).symm (ι R y * c) = wedge R L R y (c ⊗ₜ 1) := rfl
  simp only [extDeriv, LinearMap.comp_apply, LinearEquiv.coe_coe, h, derivExt_wedge, map_add,
    rid_wedge]
  simp

@[simp] lemma extDeriv_ι (D : L →ₗ[R] L) (y : L) : extDeriv D (ι R y) = ι R (D y) := by
  simpa using extDeriv_ι_mul D y 1

lemma extDeriv_add (D D' : L →ₗ[R] L) : extDeriv (D + D') = extDeriv D + extDeriv D' := by
  refine LinearMap.ext fun c ↦ ?_
  induction c using exterior_induction with
  | algebraMap r => simp
  | add c c' hc hc' => simp only [map_add, hc, hc', LinearMap.add_apply] at *
  | ι_mul y c hc =>
    simp only [extDeriv_ι_mul, LinearMap.add_apply, hc, map_add, add_mul, mul_add] at *
    abel

lemma extDeriv_smul (t : R) (D : L →ₗ[R] L) : extDeriv (t • D) = t • extDeriv D := by
  refine LinearMap.ext fun c ↦ ?_
  induction c using exterior_induction with
  | algebraMap r => simp
  | add c c' hc hc' => simp only [map_add, hc, hc', LinearMap.smul_apply] at *
  | ι_mul y c hc =>
    simp only [extDeriv_ι_mul, LinearMap.smul_apply, hc, map_smul, smul_mul_assoc,
      mul_smul_comm, smul_add] at *

lemma extDeriv_mem_exteriorPower (D : L →ₗ[R] L) {k : ℕ} {c : ExteriorAlgebra R L}
    (hc : c ∈ ⋀[R]^k L) : extDeriv D c ∈ ⋀[R]^k L := by
  have h := derivExt_mem_chainsIn (M := R) D 0 (tmul_mem_chainsIn hc (1 : R))
  obtain ⟨s, hs⟩ := h
  change TensorProduct.rid R _ (derivExt D 0 (c ⊗ₜ 1)) ∈ _
  rw [← hs]
  clear hs
  induction s with
  | tmul ω r => simpa [incl_tmul] using Submodule.smul_mem _ r ω.2
  | add s s' hs hs' => rw [map_add, map_add]; exact add_mem hs hs'

/-- The restriction of `D̃` to `⋀ᵏL`. -/
def extDerivDeg (D : L →ₗ[R] L) (k : ℕ) : Module.End R (⋀[R]^k L) :=
  (extDeriv D).restrict fun _ hc ↦ extDeriv_mem_exteriorPower D hc

@[simp] lemma coe_extDerivDeg (D : L →ₗ[R] L) (k : ℕ) (ω : ⋀[R]^k L) :
    (extDerivDeg D k ω : ExteriorAlgebra R L) = extDeriv D ω := rfl

lemma extDerivDeg_add (D D' : L →ₗ[R] L) (k : ℕ) :
    extDerivDeg (D + D') k = extDerivDeg D k + extDerivDeg D' k := by
  ext ω
  simp [extDeriv_add]

lemma extDerivDeg_smul (t : R) (D : L →ₗ[R] L) (k : ℕ) :
    extDerivDeg (t • D) k = t • extDerivDeg D k := by
  ext ω
  simp [extDeriv_smul]

end ExtDeriv

section Lie

variable {R L N : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- `[D̃, ad_y~] = (ad_{D y})~` for a derivation `D` of `L`. -/
lemma extDeriv_comm {D : L →ₗ[R] L} (hD : ∀ x y : L, D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆) (y : L)
    (c : ExteriorAlgebra R L) :
    extDeriv D (extDeriv (LieAlgebra.ad R L y) c) - extDeriv (LieAlgebra.ad R L y) (extDeriv D c) =
      extDeriv (LieAlgebra.ad R L (D y)) c := by
  induction c using exterior_induction with
  | algebraMap r => simp
  | add c c' hc hc' => simp only [map_add, ← hc, ← hc']; abel
  | ι_mul z c hc =>
    simp only [extDeriv_ι_mul, map_add, LieAlgebra.ad_apply]
    rw [← hc, hD]
    simp only [map_add, add_mul, mul_sub]
    abel

/-- The Lie derivative of a cochain: `(θ_y f)(c) = f(ad_y c) - y f(c)`. -/
lemma lieDeriv_apply (y : L) (f : ExteriorAlgebra R L →ₗ[R] N) (c : ExteriorAlgebra R L) :
    lieDeriv y f c = f (extDeriv (LieAlgebra.ad R L y) c) - ⁅y, f c⁆ := by
  induction c using exterior_induction generalizing f with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    simp only [map_smul, lie_smul, lieDeriv_one, extDeriv_one, map_zero, smul_zero, zero_sub,
      smul_neg]
  | add c c' hc hc' => simp only [map_add, lie_add, hc, hc']; abel
  | ι_mul z c hc =>
    have h := LinearMap.congr_fun (contract_lieDeriv y z f) c
    rw [contract_apply, LinearMap.add_apply, hc, contract_apply, contract_apply,
      contract_apply] at h
    rw [h, extDeriv_ι_mul, map_add, LieAlgebra.ad_apply]
    abel

end Lie

/-! ### The action of `H` on the cochains -/

namespace DerivAction

variable {K H L N : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  (ρ : DerivAction K H L N)

/-- The action `(θ(a) f)(c) = φ(a)(f c) - f(D̃(a) c)` of `a ∈ H` on the cochains `Hom(⋀L, N)`. -/
def coAct : H →ₗ[K] Module.End K (ExteriorAlgebra K L →ₗ[K] N) where
  toFun a := LinearMap.llcomp K (ExteriorAlgebra K L) N N (ρ.φ a) -
    LinearMap.lcomp K N (extDeriv (ρ.D a))
  map_add' a b := by
    ext f : 1; refine LinearMap.ext fun c ↦ ?_
    simp only [map_add, extDeriv_add, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.llcomp_apply, LinearMap.lcomp_apply, LinearMap.add_apply]
    abel
  map_smul' t a := by
    ext f : 1; refine LinearMap.ext fun c ↦ ?_
    simp only [map_smul, extDeriv_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.llcomp_apply, LinearMap.lcomp_apply, RingHom.id_apply,
      smul_sub]

omit [LieModule K L N] in
lemma coAct_apply (a : H) (f : ExteriorAlgebra K L →ₗ[K] N) (c : ExteriorAlgebra K L) :
    ρ.coAct a f c = ρ.φ a (f c) - f (extDeriv (ρ.D a) c) := rfl

omit [LieModule K L N] in
lemma contract_coAct (a : H) (y : L) (f : ExteriorAlgebra K L →ₗ[K] N) :
    contract y (ρ.coAct a f) = ρ.coAct a (contract y f) - contract (ρ.D a y) f := by
  refine LinearMap.ext fun c ↦ ?_
  simp only [contract_apply, coAct_apply, LinearMap.sub_apply, extDeriv_ι_mul, map_add]
  abel

lemma coAct_lieDeriv (a : H) (y : L) (f : ExteriorAlgebra K L →ₗ[K] N) :
    ρ.coAct a (lieDeriv y f) = lieDeriv y (ρ.coAct a f) + lieDeriv (ρ.D a y) f := by
  refine LinearMap.ext fun c ↦ ?_
  have hc := extDeriv_comm (ρ.D_lie a) y c
  rw [sub_eq_iff_eq_add] at hc
  simp only [coAct_apply, lieDeriv_apply, LinearMap.add_apply, map_sub, ρ.φ_lie, lie_sub, hc,
    map_add]
  abel

/-- **`δ` commutes with the action of `H`**: `δ ∘ θ(a) = θ(a) ∘ δ`. -/
theorem cochainDiff_coAct (a : H) (f : ExteriorAlgebra K L →ₗ[K] N) :
    cochainDiff K L N (ρ.coAct a f) = ρ.coAct a (cochainDiff K L N f) := by
  refine LinearMap.ext fun c ↦ ?_
  induction c using exterior_induction generalizing f with
  | algebraMap r =>
    simp [Algebra.algebraMap_eq_smul_one, coAct_apply, cochainDiff_one]
  | add c c' hc hc' => rw [map_add, map_add, hc, hc']
  | ι_mul y c hc =>
    have e₁ : ∀ g : ExteriorAlgebra K L →ₗ[K] N, cochainDiff K L N g (ι K y * c) =
        contract y (cochainDiff K L N g) c := fun _ ↦ rfl
    have e₂ : ∀ g : ExteriorAlgebra K L →ₗ[K] N, ρ.coAct a g (ι K y * c) =
        contract y (ρ.coAct a g) c := fun _ ↦ rfl
    rw [e₁, e₂, contract_cochainDiff, contract_coAct, contract_coAct, contract_cochainDiff,
      contract_cochainDiff]
    simp only [map_sub, map_neg, coAct_lieDeriv, LinearMap.sub_apply, LinearMap.neg_apply,
      LinearMap.add_apply, ← hc]
    abel

/-! ### Graded pieces -/

/-- The action of `H` on `C^k(L, N)`: `(θ(a) f)(ω) = φ(a)(f ω) - f(D̃(a) ω)`. -/
def coActDeg (k : ℕ) : H →ₗ[K] Module.End K (Cochains K L N k) where
  toFun a := LinearMap.llcomp K (⋀[K]^k L) N N (ρ.φ a) -
    LinearMap.lcomp K N (extDerivDeg (ρ.D a) k)
  map_add' a b := by
    ext f : 1; refine LinearMap.ext fun ω ↦ ?_
    simp only [map_add, extDerivDeg_add, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.llcomp_apply, LinearMap.lcomp_apply, LinearMap.add_apply]
    abel
  map_smul' t a := by
    ext f : 1; refine LinearMap.ext fun ω ↦ ?_
    simp only [map_smul, extDerivDeg_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.llcomp_apply, LinearMap.lcomp_apply, RingHom.id_apply,
      smul_sub]

omit [LieModule K L N] in
lemma coActDeg_apply (k : ℕ) (a : H) (f : Cochains K L N k) (ω : ⋀[K]^k L) :
    ρ.coActDeg k a f ω = ρ.φ a (f ω) - f (extDerivDeg (ρ.D a) k ω) := rfl

omit [LieModule K L N] in
lemma coActDeg_comp_degProj (k : ℕ) (a : H) (f : Cochains K L N k) :
    (ρ.coActDeg k a f ∘ₗ degProj K L k) ∘ₗ (⋀[K]^k L).subtype =
      ρ.coAct a (f ∘ₗ degProj K L k) ∘ₗ (⋀[K]^k L).subtype := by
  refine LinearMap.ext fun ω ↦ ?_
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, coActDeg_apply, coAct_apply,
    degProj_subtype]
  congr 2
  exact (degProj_subtype k (extDerivDeg (ρ.D a) k ω)).symm

/-- **`δ` commutes with the action of `H`** on the graded pieces. -/
theorem δ_coActDeg (k : ℕ) (a : H) (f : Cochains K L N k) :
    δ K L N k (ρ.coActDeg k a f) = ρ.coActDeg (k + 1) a (δ K L N k f) := by
  refine LinearMap.ext fun ω ↦ ?_
  have h := LinearMap.congr_fun (cochainDiff_eq_of_eq (ρ.coActDeg_comp_degProj k a f)) ω
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
  rw [δ_apply, h, cochainDiff_coAct, coActDeg_apply, coAct_apply, δ_apply, δ_apply,
    coe_extDerivDeg]

/-- The weight-`μ` cochains `C^k(L, N)_μ`. -/
def cochainWeightSpace (k : ℕ) (μ : Module.Dual K H) : Submodule K (Cochains K L N k) :=
  Module.End.weightSpaceOf (ρ.coActDeg k) μ

omit [LieModule K L N] in
lemma mem_cochainWeightSpace {k : ℕ} {μ : Module.Dual K H} {f : Cochains K L N k} :
    f ∈ ρ.cochainWeightSpace k μ ↔ ∀ a, ρ.coActDeg k a f = μ a • f := Iff.rfl

lemma δ_mem_cochainWeightSpace {k : ℕ} {μ : Module.Dual K H} {f : Cochains K L N k}
    (hf : f ∈ ρ.cochainWeightSpace k μ) : δ K L N k f ∈ ρ.cochainWeightSpace (k + 1) μ :=
  fun a ↦ by rw [← δ_coActDeg, hf a, map_smul]

/-- The codifferential `δ : C^k(L, N)_μ → C^{k+1}(L, N)_μ`. -/
def δWeight (k : ℕ) (μ : Module.Dual K H) :
    ρ.cochainWeightSpace k μ →ₗ[K] ρ.cochainWeightSpace (k + 1) μ :=
  (δ K L N k).restrict fun _ hf ↦ ρ.δ_mem_cochainWeightSpace hf

@[simp] lemma coe_δWeight (k : ℕ) (μ : Module.Dual K H) (f : ρ.cochainWeightSpace k μ) :
    (ρ.δWeight k μ f : Cochains K L N (k + 1)) = δ K L N k f := rfl

theorem δWeight_comp_δWeight (k : ℕ) (μ : Module.Dual K H) :
    ρ.δWeight (k + 1) μ ∘ₗ ρ.δWeight k μ = 0 :=
  LinearMap.ext fun f ↦ Subtype.ext (LinearMap.congr_fun (δ_comp_δ k) (f : Cochains K L N k))

/-- The **weight-`μ` cochain complex** `C^•(L, N)_μ`; its cohomology is `H^•(L, N)_μ`. -/
def weightComplex (μ : Module.Dual K H) : CochainComplex (ModuleCat K) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of K (ρ.cochainWeightSpace k μ))
    (fun k ↦ ModuleCat.ofHom (ρ.δWeight k μ))
    (fun k ↦ ModuleCat.hom_ext (ρ.δWeight_comp_δWeight k μ))

@[simp] lemma weightComplex_X (μ : Module.Dual K H) (k : ℕ) :
    (ρ.weightComplex μ).X k = ModuleCat.of K (ρ.cochainWeightSpace k μ) := rfl

@[simp] lemma weightComplex_d (μ : Module.Dual K H) (k : ℕ) :
    (ρ.weightComplex μ).d k (k + 1) = ModuleCat.ofHom (ρ.δWeight k μ) := by
  simp [weightComplex]


/-! ### Weight bases -/

section Basis

variable {I : Type*} [LinearOrder I] (bL : Module.Basis I K L) {γ : I → Module.Dual K H}

omit [LieModule K L N] in
lemma extDeriv_ιMulti {n : ℕ} (f : Fin n → L) (g : Fin n → Module.Dual K H)
    (hf : ∀ i, f i ∈ Module.End.weightSpaceOf ρ.D (g i)) (a : H) :
    extDeriv (ρ.D a) (ιMulti K n f) = (∑ i, g i a) • ιMulti K n f := by
  induction n with
  | zero => simp [ιMulti_zero_apply]
  | succ n ih =>
    rw [ιMulti_succ_apply, extDeriv_ι_mul, hf 0 a,
      ih (Matrix.vecTail f) (Matrix.vecTail g) fun i ↦ hf i.succ, Fin.sum_univ_succ, add_smul,
      LinearMap.map_smul_of_tower, smul_mul_assoc, mul_smul_comm]
    rfl

omit [LieModule K L N] in
/-- The basis vector `x_S` of `⋀ᵏL` has weight `γ S = ∑_{i ∈ S} γ i` for `D̃`. -/
lemma extDeriv_exteriorPower_basis (hbL : ∀ i, bL i ∈ Module.End.weightSpaceOf ρ.D (γ i))
    {k : ℕ} (s : Set.powersetCard I k) (a : H) :
    extDerivDeg (ρ.D a) k (bL.exteriorPower k s) =
      (∑ i ∈ s.val, γ i a) • bL.exteriorPower k s := by
  apply Subtype.ext
  rw [coe_extDerivDeg, _root_.exteriorPower.basis_apply, _root_.exteriorPower.ιMulti_family,
    _root_.exteriorPower.ιMulti_apply_coe,
    extDeriv_ιMulti (ρ := ρ) (⇑bL ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm s))
      (γ ∘ Set.powersetCard.ofFinEmbEquiv.symm s) fun i ↦ hbL _]
  simp only [SetLike.val_smul, _root_.exteriorPower.ιMulti_apply_coe]
  congr 1
  rw [← Finset.sum_coe_sort s.val, ← (Set.powersetCard.orderIsoOfFin s).toEquiv.sum_comp]
  rfl

variable (γ) in
/-- The weight `γ S = ∑_{i ∈ S} γ i` of the basis vector `x_S`. -/
def basisWt {k : ℕ} (s : Set.powersetCard I k) : Module.Dual K H := ∑ i ∈ s.val, γ i

omit [LinearOrder I] [LieRingModule L N] in
@[simp] lemma basisWt_apply {k : ℕ} (s : Set.powersetCard I k) (a : H) :
    basisWt γ s a = ∑ i ∈ s.val, γ i a := by
  simp [basisWt]

variable {bL}
variable (hbL : ∀ i, bL i ∈ Module.End.weightSpaceOf ρ.D (γ i))
include hbL

omit [LieModule K L N] in
/-- A cochain has weight `μ` if and only if it maps each basis vector `x_S` to a vector of weight
`μ + γ S`. -/
theorem mem_cochainWeightSpace_iff_basis {k : ℕ} {μ : Module.Dual K H} {f : Cochains K L N k} :
    f ∈ ρ.cochainWeightSpace k μ ↔
      ∀ s, f (bL.exteriorPower k s) ∈ Module.End.weightSpaceOf ρ.φ (μ + basisWt γ s) := by
  constructor
  · intro hf s a
    have h := LinearMap.congr_fun (hf a) (bL.exteriorPower k s)
    rw [coActDeg_apply, extDeriv_exteriorPower_basis ρ bL hbL, map_smul,
      LinearMap.smul_apply, sub_eq_iff_eq_add] at h
    rw [h, LinearMap.add_apply, basisWt_apply, add_smul]
  · intro hf a
    refine (bL.exteriorPower k).ext fun s ↦ ?_
    rw [coActDeg_apply, extDeriv_exteriorPower_basis ρ bL hbL, map_smul, hf s a,
      LinearMap.smul_apply, LinearMap.add_apply, basisWt_apply, add_smul, add_sub_cancel_right]

omit [LieModule K L N] in
lemma apply_basis_mem {k : ℕ} {μ : Module.Dual K H} (f : ρ.cochainWeightSpace k μ)
    (s : Set.powersetCard I k) :
    (f : Cochains K L N k) (bL.exteriorPower k s) ∈
      Module.End.weightSpaceOf ρ.φ (μ + basisWt γ s) :=
  (ρ.mem_cochainWeightSpace_iff_basis hbL).mp f.2 s

/-- The weight-`μ` cochains of degree `k` are the families `(f(x_S))_S` with `f(x_S)` of weight
`μ + γ S`. -/
def cochainWeightEquiv (k : ℕ) (μ : Module.Dual K H) :
    ρ.cochainWeightSpace k μ ≃ₗ[K]
      ((s : Set.powersetCard I k) → Module.End.weightSpaceOf ρ.φ (μ + basisWt γ s)) where
  toFun f s := ⟨(f : Cochains K L N k) (bL.exteriorPower k s), ρ.apply_basis_mem hbL f s⟩
  map_add' f g := by ext; simp
  map_smul' t f := by ext; simp
  invFun g := ⟨(bL.exteriorPower k).constr K fun s ↦ (g s : N),
    (ρ.mem_cochainWeightSpace_iff_basis hbL).mpr fun s ↦ by
      rw [Module.Basis.constr_basis]; exact (g s).2⟩
  left_inv f := by
    refine Subtype.ext ((bL.exteriorPower k).ext fun s ↦ ?_)
    exact (bL.exteriorPower k).constr_basis K _ s
  right_inv g := by
    ext s
    exact (bL.exteriorPower k).constr_basis K _ s

omit [LieModule K L N] in
@[simp] lemma cochainWeightEquiv_apply (k : ℕ) (μ : Module.Dual K H) (f) (s) :
    (ρ.cochainWeightEquiv hbL k μ f s : N) = (f : Cochains K L N k) (bL.exteriorPower k s) :=
  rfl

end Basis


end DerivAction

/-! ### Maps and short exact sequences -/

namespace DerivAction

universe w

variable {K H L : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  {N₁ N₂ N₃ : Type w} [AddCommGroup N₁] [Module K N₁] [LieRingModule L N₁] [LieModule K L N₁]
  [AddCommGroup N₂] [Module K N₂] [LieRingModule L N₂] [LieModule K L N₂]
  [AddCommGroup N₃] [Module K N₃] [LieRingModule L N₃] [LieModule K L N₃]
  {ρ₁ : DerivAction K H L N₁} {ρ₂ : DerivAction K H L N₂} {ρ₃ : DerivAction K H L N₃}

/-- A morphism of Lie modules compatible with the actions of `H` (for the same action on `L`). -/
structure IsEquivariant (ρ₁ : DerivAction K H L N₁) (ρ₂ : DerivAction K H L N₂)
    (g : N₁ →ₗ⁅K,L⁆ N₂) : Prop where
  D_eq : ρ₂.D = ρ₁.D
  map_φ : ∀ a n, g (ρ₁.φ a n) = ρ₂.φ a (g n)

variable {g : N₁ →ₗ⁅K,L⁆ N₂}

omit [LieModule K L N₁] [LieModule K L N₂] in
lemma IsEquivariant.map_mem_weightSpaceOf (hg : IsEquivariant ρ₁ ρ₂ g) {ν : Module.Dual K H}
    {x : N₁} (hx : x ∈ Module.End.weightSpaceOf ρ₁.φ ν) :
    g x ∈ Module.End.weightSpaceOf ρ₂.φ ν := fun a ↦ by
  rw [← hg.map_φ, hx a, map_smul]

omit [LieModule K L N₁] [LieModule K L N₂] in
lemma IsEquivariant.mem_weightSpaceOf_of_map (hg : IsEquivariant ρ₁ ρ₂ g)
    (hinj : Function.Injective g) {ν : Module.Dual K H} {x : N₁}
    (hx : g x ∈ Module.End.weightSpaceOf ρ₂.φ ν) :
    x ∈ Module.End.weightSpaceOf ρ₁.φ ν := fun a ↦ hinj (by rw [hg.map_φ, hx a, map_smul])

omit [LieModule K L N₁] [LieModule K L N₂] in
lemma IsEquivariant.comp_mem_cochainWeightSpace (hg : IsEquivariant ρ₁ ρ₂ g) {k : ℕ}
    {μ : Module.Dual K H} {f : Cochains K L N₁ k} (hf : f ∈ ρ₁.cochainWeightSpace k μ) :
    (g : N₁ →ₗ[K] N₂) ∘ₗ f ∈ ρ₂.cochainWeightSpace k μ := fun a ↦ by
  refine LinearMap.ext fun ω ↦ ?_
  have h := LinearMap.congr_fun (hf a) ω
  rw [coActDeg_apply] at h ⊢
  simp only [hg.D_eq, LinearMap.comp_apply, LieModuleHom.coe_toLinearMap, LinearMap.smul_apply]
  rw [← hg.map_φ, ← map_sub, h, LinearMap.smul_apply, map_smul]

/-- The map `C^k(L, N₁)_μ → C^k(L, N₂)_μ`, `f ↦ g ∘ f`. -/
def weightMap (hg : IsEquivariant ρ₁ ρ₂ g) (k : ℕ) (μ : Module.Dual K H) :
    ρ₁.cochainWeightSpace k μ →ₗ[K] ρ₂.cochainWeightSpace k μ :=
  (LinearMap.llcomp K (⋀[K]^k L) N₁ N₂ (g : N₁ →ₗ[K] N₂)).restrict fun _ hf ↦
    hg.comp_mem_cochainWeightSpace hf

omit [LieModule K L N₁] [LieModule K L N₂] in
@[simp] lemma coe_weightMap (hg : IsEquivariant ρ₁ ρ₂ g) (k : ℕ) (μ : Module.Dual K H)
    (f : ρ₁.cochainWeightSpace k μ) :
    (weightMap hg k μ f : Cochains K L N₂ k) = (g : N₁ →ₗ[K] N₂) ∘ₗ (f : Cochains K L N₁ k) :=
  rfl

lemma weightMap_δWeight (hg : IsEquivariant ρ₁ ρ₂ g) (k : ℕ) (μ : Module.Dual K H) :
    weightMap hg (k + 1) μ ∘ₗ ρ₁.δWeight k μ = ρ₂.δWeight k μ ∘ₗ weightMap hg k μ :=
  LinearMap.ext fun f ↦ Subtype.ext (δ_comp k g (f : Cochains K L N₁ k)).symm

/-- The cochain map `C^•(L, N₁)_μ → C^•(L, N₂)_μ` induced by `g`. -/
def weightComplexMap (hg : IsEquivariant ρ₁ ρ₂ g) (μ : Module.Dual K H) :
    ρ₁.weightComplex μ ⟶ ρ₂.weightComplex μ :=
  CochainComplex.ofHom (fun k ↦ ModuleCat.ofHom (weightMap hg k μ)) fun k ↦ by
    simp only [weightComplex_d]
    exact ModuleCat.hom_ext (weightMap_δWeight hg k μ).symm

@[simp] lemma weightComplexMap_f (hg : IsEquivariant ρ₁ ρ₂ g) (μ : Module.Dual K H) (k : ℕ) :
    (weightComplexMap hg μ).f k = ModuleCat.ofHom (weightMap hg k μ) :=
  rfl

variable {I : Type*} [LinearOrder I] {bL : Module.Basis I K L} {γ : I → Module.Dual K H}

/-- A short exact sequence `0 → N₁ → N₂ → N₃ → 0` which is surjective on weight spaces gives a
short exact sequence of weight cochain complexes. -/
theorem weightComplex_shortExact {g₁ : N₁ →ₗ⁅K,L⁆ N₂} {g₂ : N₂ →ₗ⁅K,L⁆ N₃}
    (hg₁ : IsEquivariant ρ₁ ρ₂ g₁) (hg₂ : IsEquivariant ρ₂ ρ₃ g₂)
    (hbL : ∀ i, bL i ∈ Module.End.weightSpaceOf ρ₁.D (γ i))
    (hinj : Function.Injective g₁) (hex : Function.Exact g₁ g₂)
    (hsurj : ∀ ν, ∀ x ∈ Module.End.weightSpaceOf ρ₃.φ ν,
      ∃ y ∈ Module.End.weightSpaceOf ρ₂.φ ν, g₂ y = x) (μ : Module.Dual K H) :
    (ShortComplex.mk (weightComplexMap hg₁ μ) (weightComplexMap hg₂ μ) (by
      ext k f : 3
      refine Subtype.ext (LinearMap.ext fun ω ↦ ?_)
      exact hex.apply_apply_eq_zero _)).ShortExact := by
  have hbL₂ : ∀ i, bL i ∈ Module.End.weightSpaceOf ρ₂.D (γ i) := hg₁.D_eq ▸ hbL
  have hbL₃ : ∀ i, bL i ∈ Module.End.weightSpaceOf ρ₃.D (γ i) := hg₂.D_eq ▸ hbL₂
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun k ↦ ?_
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro (f₂ : ρ₂.cochainWeightSpace k μ)
    constructor
    · intro h
      have hs : ∀ s, ∃ y ∈ Module.End.weightSpaceOf ρ₁.φ (μ + basisWt γ s),
          g₁ y = (f₂ : Cochains K L N₂ k) (bL.exteriorPower k s) := by
        intro s
        obtain ⟨y, hy⟩ := (hex _).mp
          (LinearMap.congr_fun (congrArg Subtype.val h) (bL.exteriorPower k s))
        refine ⟨y, hg₁.mem_weightSpaceOf_of_map hinj ?_, hy⟩
        rw [hy]
        exact ρ₂.apply_basis_mem hbL₂ f₂ s
      choose y hy hgy using hs
      refine ⟨(ρ₁.cochainWeightEquiv hbL k μ).symm fun s ↦ ⟨y s, hy s⟩, ?_⟩
      apply (ρ₂.cochainWeightEquiv hbL₂ k μ).injective
      funext s
      apply Subtype.ext
      change g₁ ((ρ₁.cochainWeightEquiv hbL k μ (
        (ρ₁.cochainWeightEquiv hbL k μ).symm fun s ↦ ⟨y s, hy s⟩) s : N₁)) = _
      rw [LinearEquiv.apply_symm_apply, hgy, cochainWeightEquiv_apply]
    · rintro ⟨f₁, rfl⟩
      refine Subtype.ext (LinearMap.ext fun ω ↦ ?_)
      exact hex.apply_apply_eq_zero _
  · intro (f : ρ₁.cochainWeightSpace k μ) (f' : ρ₁.cochainWeightSpace k μ) h
    refine Subtype.ext (LinearMap.ext fun ω ↦ hinj ?_)
    exact LinearMap.congr_fun (congrArg Subtype.val h) ω
  · intro (f₃ : ρ₃.cochainWeightSpace k μ)
    have hs : ∀ s, ∃ y ∈ Module.End.weightSpaceOf ρ₂.φ (μ + basisWt γ s),
        g₂ y = (f₃ : Cochains K L N₃ k) (bL.exteriorPower k s) :=
      fun s ↦ hsurj _ _ (ρ₃.apply_basis_mem hbL₃ f₃ s)
    choose y hy hgy using hs
    refine ⟨(ρ₂.cochainWeightEquiv hbL₂ k μ).symm fun s ↦ ⟨y s, hy s⟩, ?_⟩
    apply (ρ₃.cochainWeightEquiv hbL₃ k μ).injective
    funext s
    apply Subtype.ext
    change g₂ ((ρ₂.cochainWeightEquiv hbL₂ k μ (
      (ρ₂.cochainWeightEquiv hbL₂ k μ).symm fun s ↦ ⟨y s, hy s⟩) s : N₂)) = _
    rw [LinearEquiv.apply_symm_apply, hgy, cochainWeightEquiv_apply]

end DerivAction

end LieModule.ChevalleyEilenberg
