/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.CochainWeights
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Algebra.Lie.Abelian

/-!
# Relative Chevalley–Eilenberg cochains

Let `L` be a Lie algebra over a commutative ring `R`, `N` an `L`-module and `S ⊆ L` a subset
(in practice a subalgebra `𝔥`). The **relative cochains** `C^k(L, S; N)` are the cochains
`f : ⋀ᵏL → N` with `ι_y f = 0` and `θ_y f = 0` for all `y ∈ S`, where `ι_y f = f(y ∧ ·)` is the
contraction and `θ_y` the Lie derivative. By Cartan's formula `θ_y = -(ι_y δ + δ ι_y)` they form
a subcomplex of `C^•(L, N)`; for a subalgebra `𝔥` its cohomology is the relative Lie algebra
cohomology `H^•(L, 𝔥; N)` of Hochschild.

## Main definitions

* `LieModule.ChevalleyEilenberg.IsRelative`: the relative condition on `Hom(⋀L, N)`.
* `LieModule.ChevalleyEilenberg.relCochains`: the relative cochains of degree `k`.
* `LieModule.ChevalleyEilenberg.relCochainComplex`: the cochain complex `C^•(L, S; N)`,
  functorial in `N` (`relCochainComplexMap`).

## Main results

* `LieModule.ChevalleyEilenberg.lieDeriv_cochainDiff`: `θ_y ∘ δ = δ ∘ θ_y`.
* `LieModule.ChevalleyEilenberg.IsRelative.cochainDiff`: `δ` preserves relative cochains.
* `LieModule.ChevalleyEilenberg.cochainDiff_comp_degProj`: `δ` on graded pieces is the
  restriction of `δ` on `Hom(⋀L, N)`.
* `LieModule.ChevalleyEilenberg.relCochainComplex_shortExact`: a short exact sequence of
  coefficients which splits `S`-equivariantly gives a short exact sequence of relative cochains.
* `LieModule.ChevalleyEilenberg.relCocycleZeroEquiv`, `relCohomologyZeroEquiv`: the degree-`0`
  relative cocycles, and `H⁰(L, S; N)`, are the `L`-invariants of `N`.

## References

* G. Hochschild, *Relative homological algebra*, Trans. Amer. Math. Soc. **82** (1956), 246–269,
  §7 (relative Lie algebra cohomology).
-/

open TensorProduct ExteriorAlgebra CategoryTheory

noncomputable section

universe w

namespace LieModule.ChevalleyEilenberg

/-! ### Linear maps on the exterior algebra -/

section Grading

variable {R L N : Type*} [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup N] [Module R N]

/-- Linear maps on `⋀L` that agree on every `⋀ʲL` are equal. -/
lemma linearMap_ext_exteriorPower {F G : ExteriorAlgebra R L →ₗ[R] N}
    (h : ∀ j, F ∘ₗ (⋀[R]^j L).subtype = G ∘ₗ (⋀[R]^j L).subtype) : F = G := by
  refine LinearMap.ext fun c ↦ ?_
  have hc : c ∈ ⨆ j, ⋀[R]^j L := by
    rw [(DirectSum.Decomposition.isInternal (fun j : ℕ ↦ ⋀[R]^j L)).submodule_iSup_eq_top]
    trivial
  induction hc using Submodule.iSup_induction' with
  | mem j ω hω => exact LinearMap.congr_fun (h j) ⟨ω, hω⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]

/-- `degProj k` vanishes on `⋀ʲL` for `j ≠ k`. -/
lemma degProj_of_mem {j k : ℕ} {ω : ExteriorAlgebra R L} (hω : ω ∈ ⋀[R]^j L) (h : j ≠ k) :
    degProj R L k ω = 0 :=
  Subtype.ext (by
    change gradeFun R L ω k = 0
    simp [gradeFun_of_mem hω k, Ne.symm h])

lemma ι_mul_mem_exteriorPower (y : L) {j : ℕ} {c : ExteriorAlgebra R L} (hc : c ∈ ⋀[R]^j L) :
    ι R y * c ∈ ⋀[R]^(j + 1) L := by
  rw [exteriorPower, pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ y) hc

lemma mem_exteriorPower_zero {c : ExteriorAlgebra R L} (hc : c ∈ ⋀[R]^0 L) :
    ∃ r : R, algebraMap R _ r = c := by
  rw [exteriorPower, pow_zero, Submodule.mem_one] at hc
  exact hc

end Grading

/-! ### Cartan's formula -/

section Lie

variable {R L : Type*} {N : Type w} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

lemma lieDeriv_add (y : L) (f g : ExteriorAlgebra R L →ₗ[R] N) :
    lieDeriv y (f + g) = lieDeriv y f + lieDeriv y g := by
  simp only [lieDeriv, map_add, LinearMap.add_comp]

lemma lieDeriv_smul (y : L) (t : R) (f : ExteriorAlgebra R L →ₗ[R] N) :
    lieDeriv y (t • f) = t • lieDeriv y f := by
  simp only [lieDeriv, map_smul, LinearMap.smul_comp]

@[simp] lemma lieDeriv_zero (y : L) : lieDeriv y (0 : ExteriorAlgebra R L →ₗ[R] N) = 0 := by
  simp [lieDeriv]

/-- **Cartan's formula** `θ_y = -(ι_y δ + δ ι_y)`. -/
lemma lieDeriv_eq (y : L) (f : ExteriorAlgebra R L →ₗ[R] N) :
    lieDeriv y f = -contract y (cochainDiff R L N f) - cochainDiff R L N (contract y f) := by
  rw [contract_cochainDiff]
  abel

/-- `θ_y ∘ δ = δ ∘ θ_y`. -/
theorem lieDeriv_cochainDiff (y : L) (f : ExteriorAlgebra R L →ₗ[R] N) :
    lieDeriv y (cochainDiff R L N f) = cochainDiff R L N (lieDeriv y f) := by
  rw [lieDeriv_eq y (cochainDiff R L N f), lieDeriv_eq y f]
  simp [map_sub, map_neg]

variable {N' : Type w} [AddCommGroup N'] [Module R N'] [LieRingModule L N'] [LieModule R L N']

lemma lieDeriv_comp (φ : N →ₗ⁅R,L⁆ N') (y : L) (f : ExteriorAlgebra R L →ₗ[R] N) :
    lieDeriv y ((φ : N →ₗ[R] N') ∘ₗ f) = (φ : N →ₗ[R] N') ∘ₗ lieDeriv y f := by
  refine LinearMap.ext fun c ↦ ?_
  simp [lieDeriv_apply]

/-- `δ` on `C^k(L, N)` is the restriction of `δ` on `Hom(⋀L, N)`. -/
theorem cochainDiff_comp_degProj (k : ℕ) (f : Cochains R L N k) :
    cochainDiff R L N (f ∘ₗ degProj R L k) = δ R L N k f ∘ₗ degProj R L (k + 1) := by
  refine linearMap_ext_exteriorPower fun j ↦ LinearMap.ext fun ω ↦ ?_
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  by_cases hj : j = k + 1
  · subst hj
    rw [degProj_subtype, δ_apply]
  · rw [degProj_of_mem ω.2 hj, map_zero]
    rcases j with _ | i
    · obtain ⟨r, hr⟩ := mem_exteriorPower_zero ω.2
      rw [← hr, Algebra.algebraMap_eq_smul_one, map_smul, cochainDiff_one, smul_zero]
    · have h0 : (f ∘ₗ degProj R L k) ∘ₗ (⋀[R]^i L).subtype = 0 ∘ₗ (⋀[R]^i L).subtype := by
        refine LinearMap.ext fun ω' ↦ ?_
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply]
        rw [degProj_of_mem ω'.2 (fun h ↦ hj (by rw [h])), map_zero]
      have := LinearMap.congr_fun (cochainDiff_eq_of_eq h0) ω
      simpa using this

/-! ### Relative cochains -/

variable (S : Set L)

/-- A cochain `F : ⋀L → N` is **relative** to `S` if `ι_y F = 0` and `θ_y F = 0` for `y ∈ S`. -/
def IsRelative (F : ExteriorAlgebra R L →ₗ[R] N) : Prop :=
  ∀ y ∈ S, contract y F = 0 ∧ lieDeriv y F = 0

variable {S}

/-- `δ` preserves relative cochains. -/
theorem IsRelative.cochainDiff {F : ExteriorAlgebra R L →ₗ[R] N} (hF : IsRelative S F) :
    IsRelative S (cochainDiff R L N F) := fun y hy ↦
  ⟨by rw [contract_cochainDiff, (hF y hy).1, (hF y hy).2]; simp,
    by rw [lieDeriv_cochainDiff, (hF y hy).2, map_zero]⟩

lemma IsRelative.comp (φ : N →ₗ⁅R,L⁆ N') {F : ExteriorAlgebra R L →ₗ[R] N}
    (hF : IsRelative S F) : IsRelative S ((φ : N →ₗ[R] N') ∘ₗ F) := fun y hy ↦
  ⟨by rw [show contract y ((φ : N →ₗ[R] N') ∘ₗ F) = (φ : N →ₗ[R] N') ∘ₗ contract y F from rfl,
      (hF y hy).1, LinearMap.comp_zero],
    by rw [lieDeriv_comp, (hF y hy).2, LinearMap.comp_zero]⟩

variable (R L N S) in
/-- The **relative cochains** `C^k(L, S; N)`: the `f : ⋀ᵏL → N` such that `f ∘ degProj k` is
relative to `S`. -/
def relCochains (k : ℕ) : Submodule R (Cochains R L N k) where
  carrier := {f | IsRelative S (f ∘ₗ degProj R L k)}
  zero_mem' y _ := by simp
  add_mem' {f g} hf hg y hy := by
    simp only [LinearMap.add_comp, map_add, lieDeriv_add, (hf y hy).1,
      (hg y hy).1, (hf y hy).2, (hg y hy).2, add_zero, and_self]
  smul_mem' t f hf y hy := by
    simp only [LinearMap.smul_comp, map_smul, lieDeriv_smul, (hf y hy).1,
      (hf y hy).2, smul_zero, and_self]

lemma mem_relCochains {k : ℕ} {f : Cochains R L N k} :
    f ∈ relCochains R L N S k ↔ IsRelative S (f ∘ₗ degProj R L k) := Iff.rfl

lemma δ_mem_relCochains {k : ℕ} {f : Cochains R L N k} (hf : f ∈ relCochains R L N S k) :
    δ R L N k f ∈ relCochains R L N S (k + 1) := by
  rw [mem_relCochains, ← cochainDiff_comp_degProj]
  exact IsRelative.cochainDiff hf

variable (R L N S) in
/-- The relative codifferential `δ : C^k(L, S; N) → C^{k+1}(L, S; N)`. -/
def relδ (k : ℕ) : relCochains R L N S k →ₗ[R] relCochains R L N S (k + 1) :=
  (δ R L N k).restrict fun _ hf ↦ δ_mem_relCochains hf

@[simp] lemma coe_relδ (k : ℕ) (f : relCochains R L N S k) :
    (relδ R L N S k f : Cochains R L N (k + 1)) = δ R L N k f := rfl

theorem relδ_comp_relδ (k : ℕ) : relδ R L N S (k + 1) ∘ₗ relδ R L N S k = 0 :=
  LinearMap.ext fun f ↦ Subtype.ext (LinearMap.congr_fun (δ_comp_δ k) (f : Cochains R L N k))

variable (R L N S) in
/-- The **relative cochain complex** `C^•(L, S; N)`; for a subalgebra `𝔥 = S` its cohomology is
the relative Lie algebra cohomology `H^•(L, 𝔥; N)`. -/
def relCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of R (relCochains R L N S k))
    (fun k ↦ ModuleCat.ofHom (relδ R L N S k))
    (fun k ↦ ModuleCat.hom_ext (relδ_comp_relδ k))

@[simp] lemma relCochainComplex_X (k : ℕ) :
    (relCochainComplex R L N S).X k = ModuleCat.of R (relCochains R L N S k) := rfl

@[simp] lemma relCochainComplex_d (k : ℕ) :
    (relCochainComplex R L N S).d k (k + 1) = ModuleCat.ofHom (relδ R L N S k) := by
  simp [relCochainComplex]

/-! ### Functoriality -/

lemma comp_mem_relCochains (φ : N →ₗ⁅R,L⁆ N') {k : ℕ} {f : Cochains R L N k}
    (hf : f ∈ relCochains R L N S k) :
    (φ : N →ₗ[R] N') ∘ₗ f ∈ relCochains R L N' S k := by
  rw [mem_relCochains, LinearMap.comp_assoc]
  exact hf.comp φ

variable (S) in
/-- The map `C^k(L, S; N) → C^k(L, S; N')`, `f ↦ φ ∘ f`. -/
def relMap (φ : N →ₗ⁅R,L⁆ N') (k : ℕ) : relCochains R L N S k →ₗ[R] relCochains R L N' S k :=
  (LinearMap.llcomp R (⋀[R]^k L) N N' (φ : N →ₗ[R] N')).restrict fun _ hf ↦
    comp_mem_relCochains φ hf

@[simp] lemma coe_relMap (φ : N →ₗ⁅R,L⁆ N') (k : ℕ) (f : relCochains R L N S k) :
    (relMap S φ k f : Cochains R L N' k) = (φ : N →ₗ[R] N') ∘ₗ (f : Cochains R L N k) := rfl

lemma relMap_relδ (φ : N →ₗ⁅R,L⁆ N') (k : ℕ) :
    relMap S φ (k + 1) ∘ₗ relδ R L N S k = relδ R L N' S k ∘ₗ relMap S φ k :=
  LinearMap.ext fun f ↦ Subtype.ext (δ_comp k φ (f : Cochains R L N k)).symm

variable (S) in
/-- The cochain map `C^•(L, S; N) → C^•(L, S; N')` induced by a morphism of Lie modules. -/
def relCochainComplexMap (φ : N →ₗ⁅R,L⁆ N') :
    relCochainComplex R L N S ⟶ relCochainComplex R L N' S :=
  CochainComplex.ofHom (fun k ↦ ModuleCat.ofHom (relMap S φ k)) fun k ↦ by
    simp only [relCochainComplex_d]
    exact ModuleCat.hom_ext (relMap_relδ φ k).symm

@[simp] lemma relCochainComplexMap_f (φ : N →ₗ⁅R,L⁆ N') (k : ℕ) :
    (relCochainComplexMap S φ).f k = ModuleCat.ofHom (relMap S φ k) := rfl

end Lie

/-! ### Degree zero -/

section Zero

variable {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V] {S : Set L}

/-- A degree-`0` cochain whose value at `1` is `L`-invariant is relative. -/
lemma cochainZero_mem_relCochains {v : V} (hv : ∀ x : L, ⁅x, v⁆ = 0) :
    cochainZero K L v ∈ relCochains K L V S 0 := by
  intro y _
  constructor
  · refine linearMap_ext_exteriorPower fun j ↦ LinearMap.ext fun ω ↦ ?_
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, contract_apply,
      LinearMap.zero_apply]
    rw [degProj_of_mem (ι_mul_mem_exteriorPower y ω.2) (Nat.succ_ne_zero j), map_zero]
  · have h0 : cochainZero K L v ∘ₗ degProj K L 0 ∘ₗ extDeriv (LieAlgebra.ad K L y) = 0 := by
      refine linearMap_ext_exteriorPower fun j ↦ LinearMap.ext fun ω ↦ ?_
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply]
      rcases j with _ | j
      · obtain ⟨r, hr⟩ := mem_exteriorPower_zero ω.2
        rw [← hr, extDeriv_algebraMap, map_zero, map_zero]
      · rw [degProj_of_mem (extDeriv_mem_exteriorPower _ ω.2) (Nat.succ_ne_zero j), map_zero]
    refine LinearMap.ext fun c ↦ ?_
    rw [lieDeriv_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.zero_apply]
    simp only [cochainZero, LinearMap.smulRight_apply, lie_smul, hv, smul_zero, sub_zero]
    exact LinearMap.congr_fun h0 c

/-- **The degree-`0` relative cocycles are the `L`-invariants**: `f ↦ f(1)`. -/
def relCocycleZeroEquiv :
    LinearMap.ker (relδ K L V S 0) ≃ₗ[K] maxTrivSubmodule K L V where
  toFun f := ⟨(f.1 : Cochains K L V 0) ⟨1, by simp⟩, (mem_maxTrivSubmodule K L V _).mpr
    (δ_zero_eq_zero_iff.mp (congrArg Subtype.val (LinearMap.mem_ker.mp f.2)))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨⟨cochainZero K L (v : V),
      cochainZero_mem_relCochains ((mem_maxTrivSubmodule K L V _).mp v.2)⟩,
    LinearMap.mem_ker.mpr (Subtype.ext (δ_zero_eq_zero_iff.mpr fun x ↦ by
      change ⁅x, cochainZero K L (v : V) ⟨1, by simp⟩⁆ = 0
      rw [cochainZero_one]; exact (mem_maxTrivSubmodule K L V _).mp v.2 x))⟩
  left_inv f := Subtype.ext (Subtype.ext (cochainZero_apply_one _))
  right_inv v := Subtype.ext (cochainZero_one _)

variable (K L V S) in
/-- **`H⁰(L, S; V)` is the space of `L`-invariants of `V`**. -/
def relCohomologyZeroEquiv :
    (relCochainComplex K L V S).homology 0 ≃ₗ[K] maxTrivSubmodule K L V :=
  (((CochainComplex.isoHomologyπ₀ _).symm ≪≫
    (relCochainComplex K L V S).cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫
    ((relCochainComplex K L V S).sc' 0 0 1).moduleCatCyclesIso).toLinearEquiv.trans
    (LinearEquiv.ofEq _ _ (by
      change LinearMap.ker ((relCochainComplex K L V S).d 0 (0 + 1)).hom = _
      rw [relCochainComplex_d]
      rfl))).trans relCocycleZeroEquiv

end Zero

/-! ### Short exact sequences -/

section ShortExact

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] {S : Set L}
  {N₁ N₂ N₃ : Type w} [AddCommGroup N₁] [Module K N₁] [LieRingModule L N₁] [LieModule K L N₁]
  [AddCommGroup N₂] [Module K N₂] [LieRingModule L N₂] [LieModule K L N₂]
  [AddCommGroup N₃] [Module K N₃] [LieRingModule L N₃] [LieModule K L N₃]

/-- A short exact sequence `0 → N₁ → N₂ → N₃ → 0` of `L`-modules which splits by a linear map
commuting with the action of `S` gives a short exact sequence of relative cochain complexes. -/
theorem relCochainComplex_shortExact {g₁ : N₁ →ₗ⁅K,L⁆ N₂} {g₂ : N₂ →ₗ⁅K,L⁆ N₃}
    (hinj : Function.Injective g₁) (hex : Function.Exact g₁ g₂) (σ : N₃ →ₗ[K] N₂)
    (hσ : ∀ n, g₂ (σ n) = n) (hσS : ∀ y ∈ S, ∀ n, σ ⁅y, n⁆ = ⁅y, σ n⁆) :
    (ShortComplex.mk (relCochainComplexMap S g₁) (relCochainComplexMap S g₂) (by
      ext k f : 3
      refine Subtype.ext (LinearMap.ext fun ω ↦ ?_)
      exact hex.apply_apply_eq_zero _)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun k ↦ ?_
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro (f₂ : relCochains K L N₂ S k)
    constructor
    · intro h
      have hr : ∀ ω, (f₂ : Cochains K L N₂ k) ω ∈ LinearMap.range (g₁ : N₁ →ₗ[K] N₂) :=
        fun ω ↦ (hex _).mp (LinearMap.congr_fun (congrArg Subtype.val h) ω)
      let e := LinearEquiv.ofInjective (g₁ : N₁ →ₗ[K] N₂) hinj
      let f₁ : Cochains K L N₁ k :=
        e.symm.toLinearMap ∘ₗ (f₂ : Cochains K L N₂ k).codRestrict _ hr
      have hf₁ : (g₁ : N₁ →ₗ[K] N₂) ∘ₗ f₁ = f₂ := LinearMap.ext fun ω ↦ by
        change ((e (e.symm _)) : N₂) = _
        rw [LinearEquiv.apply_symm_apply]
        rfl
      have hcomp : ∀ F : ExteriorAlgebra K L →ₗ[K] N₁,
          (g₁ : N₁ →ₗ[K] N₂) ∘ₗ F = 0 → F = 0 := fun F hF ↦
        LinearMap.ext fun c ↦ hinj (by
          rw [LinearMap.zero_apply, map_zero]; exact LinearMap.congr_fun hF c)
      refine ⟨⟨f₁, fun y hy ↦ ⟨hcomp _ ?_, hcomp _ ?_⟩⟩, Subtype.ext hf₁⟩
      · rw [show (g₁ : N₁ →ₗ[K] N₂) ∘ₗ contract y (f₁ ∘ₗ degProj K L k) =
          contract y (((g₁ : N₁ →ₗ[K] N₂) ∘ₗ f₁) ∘ₗ degProj K L k) from rfl, hf₁]
        exact (f₂.2 y hy).1
      · rw [← lieDeriv_comp, ← LinearMap.comp_assoc, hf₁]
        exact (f₂.2 y hy).2
    · rintro ⟨f₁, rfl⟩
      refine Subtype.ext (LinearMap.ext fun ω ↦ ?_)
      exact hex.apply_apply_eq_zero _
  · intro (f : relCochains K L N₁ S k) (f' : relCochains K L N₁ S k) h
    refine Subtype.ext (LinearMap.ext fun ω ↦ hinj ?_)
    exact LinearMap.congr_fun (congrArg Subtype.val h) ω
  · intro (f₃ : relCochains K L N₃ S k)
    refine ⟨⟨σ ∘ₗ (f₃ : Cochains K L N₃ k), fun y hy ↦ ⟨?_, ?_⟩⟩, ?_⟩
    · rw [show contract y ((σ ∘ₗ (f₃ : Cochains K L N₃ k)) ∘ₗ degProj K L k) =
        σ ∘ₗ contract y ((f₃ : Cochains K L N₃ k) ∘ₗ degProj K L k) from rfl, (f₃.2 y hy).1,
        LinearMap.comp_zero]
    · have h := (f₃.2 y hy).2
      refine LinearMap.ext fun c ↦ ?_
      have hc := LinearMap.congr_fun h c
      rw [lieDeriv_apply] at hc ⊢
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hc ⊢
      rw [← hσS y hy, ← map_sub, hc, map_zero]
    · refine Subtype.ext (LinearMap.ext fun ω ↦ ?_)
      exact hσ _

end ShortExact

end LieModule.ChevalleyEilenberg
