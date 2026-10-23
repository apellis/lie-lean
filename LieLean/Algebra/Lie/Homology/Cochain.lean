/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.ChainComplex
import LieLean.Algebra.Lie.UniversalEnveloping.LeftRegular

/-!
# The Chevalley–Eilenberg cochain complex

Let `L` be a Lie algebra over a commutative ring `R` and `N` a Lie module. The Lie algebra
cohomology `H^•(L, N)` is computed by the cochains `C^k(L, N) = Hom_R(⋀ᵏL, N)` with differential
`(δf)(x₀ ∧ ⋯ ∧ x_k) = ∑ᵢ (-1)ⁱ xᵢ f(x₀ ∧ ⋯ x̂ᵢ ⋯ ∧ x_k)`
`  + ∑_{i < j} (-1)^{i+j} f([xᵢ, xⱼ] ∧ x₀ ∧ ⋯ x̂ᵢ ⋯ x̂ⱼ ⋯ ∧ x_k)`
([Weibel, §7.7], up to the sign convention of the chain complex).

## Design

We obtain `δ` as the transpose of the chain differential `d` on the Koszul complex
`⋀L ⊗ U(L)` (coefficients in the left-regular module), whose terms are free right
`U(L)`-modules. A cochain `f : ⋀L → N` extends to the right `U(L)`-linear map
`f̃ : ⋀L ⊗ U(L) → N`, `f̃(c ⊗ u) = u^⊤ f(c)`, where `u ↦ u^⊤` is the anti-homomorphism
`U(L) → End(N)` with `x^⊤ = -x_N`; then `δf = f̃ ∘ d ∘ (· ⊗ 1)`. Since `d` commutes with
right multiplication by `U(L)`, `(δf)~ = f̃ ∘ d`, so `δ ∘ δ = 0` follows from `d ∘ d = 0`.
The recursion `(δf)(y ∧ c) = y f(c) - f(θ(y) c) - δ(ι_y f)(c)` (with `ι_y f = f(y ∧ ·)` and
`θ(y)` the adjoint action on `⋀L`) unwinds to the displayed formula.

## Main definitions

* `LieModule.ChevalleyEilenberg.envAction`: `u ↦ u^⊤`, the anti-homomorphism `U(L) → End(N)`.
* `LieModule.ChevalleyEilenberg.cochainDiff`: the differential `δ` on `Hom_R(⋀L, N)`.
* `LieModule.ChevalleyEilenberg.δ`: its graded pieces `C^k(L, N) → C^{k+1}(L, N)`.
* `LieModule.ChevalleyEilenberg.cochainComplex`: `C^•(L, N)` as a cochain complex of
  `R`-modules, functorial in `N` (`cochainComplexMap`).

## Main results

* `LieModule.ChevalleyEilenberg.cochainDiff_cochainDiff`, `δ_comp_δ`: `δ ∘ δ = 0`.
* `LieModule.ChevalleyEilenberg.contract_cochainDiff`: the recursion formula for `δ`.
* `LieModule.ChevalleyEilenberg.cochainPair_cochainDiff`: `δ` is the transpose of the chain
  differential for an invariant pairing.
* `LieModule.ChevalleyEilenberg.δ_zero_apply`: `(δf)(x) = x f(1)` in degree `0`.

## References

* C. A. Weibel, *An introduction to homological algebra*, CUP 1994, §7.7.
-/

open TensorProduct ExteriorAlgebra CategoryTheory
open UniversalEnvelopingAlgebra (LeftRegular mkAlgHom)

noncomputable section

namespace LieModule.ChevalleyEilenberg

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

section Cochains

universe w

variable {R L : Type*} {N : Type w} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable (R L N) in
/-- `x ↦ -x_N`, a morphism of Lie algebras from `L` to the opposite algebra of `End(N)`. -/
def oppositeAction : L →ₗ⁅R⁆ (Module.End R N)ᵐᵒᵖ where
  toFun x := MulOpposite.op (-toEnd R L N x)
  map_add' x y := by rw [map_add, neg_add, MulOpposite.op_add]
  map_smul' t x := by rw [map_smul, ← smul_neg, MulOpposite.op_smul, RingHom.id_apply]
  map_lie' {x y} := by
    rw [LieRing.of_associative_ring_bracket, ← MulOpposite.op_mul, ← MulOpposite.op_mul,
      ← MulOpposite.op_sub, LieHom.map_lie, LieRing.of_associative_ring_bracket]
    rw [neg_mul_neg, neg_mul_neg, neg_sub]

variable (R L N) in
/-- The anti-homomorphism `u ↦ u^⊤` from `U(L)` to `End(N)` with `x^⊤ = -x_N` for `x ∈ L`. -/
def envAction : UniversalEnvelopingAlgebra R L →ₗ[R] Module.End R N :=
  (MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ
    (UniversalEnvelopingAlgebra.lift R (oppositeAction R L N)).toLinearMap

lemma envAction_mul (u v : UniversalEnvelopingAlgebra R L) :
    envAction R L N (u * v) = envAction R L N v * envAction R L N u := by
  simp [envAction]

@[simp] lemma envAction_one : envAction R L N (1 : UniversalEnvelopingAlgebra R L) = 1 := by
  simp [envAction]

@[simp] lemma envAction_ι (x : L) (n : N) :
    envAction R L N (UniversalEnvelopingAlgebra.ι R x) n = -⁅x, n⁆ := by
  simp [envAction, oppositeAction]

/-- The action `u^⊤` commutes with morphisms of Lie modules. -/
lemma envAction_comp {N' : Type*} [AddCommGroup N'] [Module R N'] [LieRingModule L N']
    [LieModule R L N'] (φ : N →ₗ⁅R,L⁆ N') (u : UniversalEnvelopingAlgebra R L) :
    envAction R L N' u ∘ₗ (φ : N →ₗ[R] N') = (φ : N →ₗ[R] N') ∘ₗ envAction R L N u := by
  obtain ⟨a, rfl⟩ : ∃ a, mkAlgHom R L a = u := by
    induction u using Quotient.inductionOn' with
    | h a => exact ⟨a, rfl⟩
  induction a using TensorAlgebra.induction with
  | algebraMap r =>
    ext n
    simp [Algebra.algebraMap_eq_smul_one]
  | ι y =>
    ext n
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      show mkAlgHom R L (TensorAlgebra.ι R y) = UniversalEnvelopingAlgebra.ι R y from rfl,
      envAction_ι, envAction_ι, LieModuleHom.coe_toLinearMap, map_neg, LieModuleHom.map_lie]
  | add a₁ a₂ h₁ h₂ => rw [map_add, map_add, map_add, LinearMap.add_comp, h₁, h₂,
      LinearMap.comp_add]
  | mul a₁ a₂ h₁ h₂ => rw [map_mul, envAction_mul, envAction_mul, Module.End.mul_eq_comp,
      Module.End.mul_eq_comp, LinearMap.comp_assoc, h₁, ← LinearMap.comp_assoc, h₂,
      LinearMap.comp_assoc]

local notation "E" => ExteriorAlgebra R L ⊗[R] LeftRegular R L

variable (R L N) in
/-- `envAction` on the left-regular coefficient type. -/
def regAction : LeftRegular R L →ₗ[R] Module.End R N :=
  envAction R L N ∘ₗ (LeftRegular.equiv R L).toLinearMap

variable (R L N) in
/-- The right `U(L)`-linear extension `f̃(c ⊗ u) = u^⊤ f(c)` of a cochain `f : ⋀L → N` to the
Koszul complex `⋀L ⊗ U(L)`. -/
def cochainExt : (ExteriorAlgebra R L →ₗ[R] N) →ₗ[R] (E →ₗ[R] N) :=
  (TensorProduct.lift.equiv (RingHom.id R) _ _ _).toLinearMap ∘ₗ
    LinearMap.llcomp R _ _ _ (regAction R L N).flip

@[simp] lemma cochainExt_tmul (f : ExteriorAlgebra R L →ₗ[R] N) (c : ExteriorAlgebra R L)
    (u : LeftRegular R L) :
    cochainExt R L N f (c ⊗ₜ u) = envAction R L N (LeftRegular.equiv R L u) (f c) := rfl

lemma cochainExt_one (f : ExteriorAlgebra R L →ₗ[R] N) (c : ExteriorAlgebra R L) :
    cochainExt R L N f (c ⊗ₜ (LeftRegular.equiv R L).symm 1) = f c := by
  simp

/-- `f̃` is right `U(L)`-linear. -/
lemma cochainExt_mulRight (f : ExteriorAlgebra R L →ₗ[R] N) (u : UniversalEnvelopingAlgebra R L)
    (t : E) :
    cochainExt R L N f ((LeftRegular.mulRight u : LeftRegular R L →ₗ[R] LeftRegular R L).lTensor
      _ t) = envAction R L N u (cochainExt R L N f t) := by
  induction t with
  | tmul c v =>
    simp only [LinearMap.lTensor_tmul, LieModuleHom.coe_toLinearMap, cochainExt_tmul,
      LeftRegular.equiv_mulRight, envAction_mul, Module.End.mul_apply]
  | add t t' ht ht' => simp only [map_add, ht, ht']

variable (R L N) in
/-- The **Chevalley–Eilenberg codifferential** `δf = f̃ ∘ d ∘ (· ⊗ 1)` on `Hom_R(⋀L, N)`. -/
def cochainDiff : Module.End R (ExteriorAlgebra R L →ₗ[R] N) where
  toFun f := cochainExt R L N f ∘ₗ diff R L (LeftRegular R L) ∘ₗ
    (TensorProduct.mk R _ _).flip ((LeftRegular.equiv R L).symm 1)
  map_add' f g := by rw [map_add, LinearMap.add_comp]
  map_smul' t f := by rw [map_smul, LinearMap.smul_comp, RingHom.id_apply]

lemma cochainDiff_apply (f : ExteriorAlgebra R L →ₗ[R] N) (c : ExteriorAlgebra R L) :
    cochainDiff R L N f c =
      cochainExt R L N f (diff R L (LeftRegular R L) (c ⊗ₜ (LeftRegular.equiv R L).symm 1)) :=
  rfl

/-- `(δf)~ = f̃ ∘ d`. -/
theorem cochainExt_cochainDiff (f : ExteriorAlgebra R L →ₗ[R] N) :
    cochainExt R L N (cochainDiff R L N f) = cochainExt R L N f ∘ₗ diff R L (LeftRegular R L) := by
  ext c u
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_self, LinearMap.comp_apply]
  have hu : c ⊗ₜ[R] u = (LeftRegular.mulRight (LeftRegular.equiv R L u) :
      LeftRegular R L →ₗ[R] LeftRegular R L).lTensor _ (c ⊗ₜ (LeftRegular.equiv R L).symm 1) := by
    simp only [LinearMap.lTensor_tmul]
    congr 1
    apply (LeftRegular.equiv R L).injective
    simp
  rw [cochainExt_tmul, cochainDiff_apply]
  conv_rhs => rw [hu, ← lTensor_diff, cochainExt_mulRight]

/-- `δ ∘ δ = 0`. -/
@[simp] theorem cochainDiff_cochainDiff (f : ExteriorAlgebra R L →ₗ[R] N) :
    cochainDiff R L N (cochainDiff R L N f) = 0 := by
  ext c
  rw [cochainDiff_apply, cochainExt_cochainDiff, LinearMap.comp_apply, diff_diff, map_zero,
    LinearMap.zero_apply]

theorem cochainDiff_comp_cochainDiff : cochainDiff R L N ∘ₗ cochainDiff R L N = 0 :=
  LinearMap.ext fun f ↦ by rw [LinearMap.comp_apply, cochainDiff_cochainDiff, LinearMap.zero_apply]

lemma cochainDiff_one (f : ExteriorAlgebra R L →ₗ[R] N) :
    cochainDiff R L N f (1 : ExteriorAlgebra R L) = 0 := by
  rw [cochainDiff_apply]
  exact (congrArg (cochainExt R L N f) (diff_one_tmul _)).trans (map_zero _)

/-- `(δf)(x) = x f(1)`. -/
lemma cochainDiff_ι (f : ExteriorAlgebra R L →ₗ[R] N) (x : L) :
    cochainDiff R L N f (ι R x) = ⁅x, f 1⁆ := by
  rw [cochainDiff_apply, diff_ι_tmul, map_neg, cochainExt_tmul]
  have : LeftRegular.equiv R L ⁅x, (LeftRegular.equiv R L).symm 1⁆ =
      UniversalEnvelopingAlgebra.ι R x := by simp
  rw [this, envAction_ι, neg_neg]

/-- `δ` commutes with postcomposition by morphisms of Lie modules. -/
lemma cochainDiff_comp {N' : Type*} [AddCommGroup N'] [Module R N'] [LieRingModule L N']
    [LieModule R L N'] (φ : N →ₗ⁅R,L⁆ N') (f : ExteriorAlgebra R L →ₗ[R] N) :
    cochainDiff R L N' ((φ : N →ₗ[R] N') ∘ₗ f) = (φ : N →ₗ[R] N') ∘ₗ cochainDiff R L N f := by
  have : cochainExt R L N' ((φ : N →ₗ[R] N') ∘ₗ f) =
      (φ : N →ₗ[R] N') ∘ₗ cochainExt R L N f := by
    ext c u
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.restrictScalars_self, LinearMap.comp_apply, cochainExt_tmul]
    exact LinearMap.congr_fun (envAction_comp φ _) (f c)
  ext c
  rw [cochainDiff_apply, this, LinearMap.comp_apply, LinearMap.comp_apply, cochainDiff_apply]

/-! ### Grading -/

/-- `f̃` on `⋀ʲL ⊗ U(L)` only depends on the restriction of `f` to `⋀ʲL`. -/
lemma cochainExt_eq_of_mem_chainsIn {j : ℕ} {f g : ExteriorAlgebra R L →ₗ[R] N}
    (h : f ∘ₗ (⋀[R]^j L).subtype = g ∘ₗ (⋀[R]^j L).subtype) {t : E}
    (ht : t ∈ chainsIn R L (LeftRegular R L) j) :
    cochainExt R L N f t = cochainExt R L N g t := by
  obtain ⟨s, rfl⟩ := ht
  induction s with
  | tmul ω u =>
    have hω := LinearMap.congr_fun h ω
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hω
    simp only [incl_tmul, cochainExt_tmul, hω]
  | add s s' hs hs' => simp only [map_add, hs, hs']

/-- `δf` on `⋀ʲ⁺¹L` only depends on the restriction of `f` to `⋀ʲL`. -/
lemma cochainDiff_eq_of_eq {j : ℕ} {f g : ExteriorAlgebra R L →ₗ[R] N}
    (h : f ∘ₗ (⋀[R]^j L).subtype = g ∘ₗ (⋀[R]^j L).subtype) :
    cochainDiff R L N f ∘ₗ (⋀[R]^(j + 1) L).subtype =
      cochainDiff R L N g ∘ₗ (⋀[R]^(j + 1) L).subtype := by
  ext ω
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, cochainDiff_apply]
  exact cochainExt_eq_of_mem_chainsIn h (diff_mem_chainsIn (tmul_mem_chainsIn ω.2 _))

variable (R L N) in
/-- The **Chevalley–Eilenberg cochains** `C^k(L, N) = Hom_R(⋀ᵏL, N)`. -/
abbrev Cochains (k : ℕ) := ⋀[R]^k L →ₗ[R] N

variable (R L N) in
/-- The codifferential `δ : C^k(L, N) → C^{k+1}(L, N)`. -/
def δ (k : ℕ) : Cochains R L N k →ₗ[R] Cochains R L N (k + 1) :=
  LinearMap.lcomp R N (⋀[R]^(k + 1) L).subtype ∘ₗ cochainDiff R L N ∘ₗ
    LinearMap.lcomp R N (degProj R L k)

lemma δ_apply (k : ℕ) (f : Cochains R L N k) (ω : ⋀[R]^(k + 1) L) :
    δ R L N k f ω = cochainDiff R L N (f ∘ₗ degProj R L k) ω := rfl

/-- `δ ∘ δ = 0`. -/
theorem δ_comp_δ (k : ℕ) : δ R L N (k + 1) ∘ₗ δ R L N k = 0 := by
  ext f ω
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  change (cochainDiff R L N ((δ R L N k f) ∘ₗ degProj R L (k + 1)) ∘ₗ
    (⋀[R]^(k + 2) L).subtype) ω = 0
  rw [cochainDiff_eq_of_eq (g := cochainDiff R L N (f ∘ₗ degProj R L k)) (j := k + 1)]
  · simp
  · ext ω'
    simp [δ_apply, degProj_subtype]

/-- In degree `0`, `(δf)(x) = x f(1)`. -/
lemma δ_zero_apply (f : Cochains R L N 0) (x : L) :
    δ R L N 0 f ⟨ι R x, by simp⟩ =
      ⁅x, f ⟨1, by simp⟩⁆ := by
  rw [δ_apply]
  change cochainDiff R L N (f ∘ₗ degProj R L 0) (ι R x) = _
  rw [cochainDiff_ι, LinearMap.comp_apply]
  congr 2
  exact degProj_subtype 0 ⟨1, _⟩

variable {N' : Type*} [AddCommGroup N'] [Module R N'] [LieRingModule L N'] [LieModule R L N']

lemma δ_comp (k : ℕ) (φ : N →ₗ⁅R,L⁆ N') (f : Cochains R L N k) :
    δ R L N' k ((φ : N →ₗ[R] N') ∘ₗ f) = (φ : N →ₗ[R] N') ∘ₗ δ R L N k f := by
  ext ω
  simp only [δ_apply, LinearMap.comp_apply]
  rw [LinearMap.comp_assoc, cochainDiff_comp, LinearMap.comp_apply]

variable (R L N) in
/-- The **Chevalley–Eilenberg cochain complex** `C^•(L, N)`, `C^k(L, N) = Hom_R(⋀ᵏL, N)`. -/
def cochainComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of R (Cochains R L N k))
    (fun k ↦ ModuleCat.ofHom (δ R L N k))
    (fun k ↦ ModuleCat.hom_ext (δ_comp_δ k))

@[simp] lemma cochainComplex_X (k : ℕ) :
    (cochainComplex R L N).X k = ModuleCat.of R (Cochains R L N k) := rfl

@[simp] lemma cochainComplex_d (k : ℕ) :
    (cochainComplex R L N).d k (k + 1) = ModuleCat.ofHom (δ R L N k) := by
  simp [cochainComplex]

section Map

variable {M M' : Type w} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

/-- The cochain map `C^•(L, N) → C^•(L, M)` induced by a morphism of Lie modules. -/
def cochainComplexMap (φ : N →ₗ⁅R,L⁆ M) : cochainComplex R L N ⟶ cochainComplex R L M :=
  CochainComplex.ofHom (fun k ↦ ModuleCat.ofHom
    (LinearMap.llcomp R (⋀[R]^k L) N M (φ : N →ₗ[R] M))) fun k ↦ by
    simp only [cochainComplex_d]
    ext f : 2
    exact δ_comp k φ f

@[simp] lemma cochainComplexMap_f (φ : N →ₗ⁅R,L⁆ M) (k : ℕ) :
    (cochainComplexMap φ).f k =
      ModuleCat.ofHom (LinearMap.llcomp R (⋀[R]^k L) N M (φ : N →ₗ[R] M)) :=
  rfl

@[simp] lemma cochainComplexMap_id :
    cochainComplexMap (LieModuleHom.id : N →ₗ⁅R,L⁆ N) = 𝟙 (cochainComplex R L N) := by
  ext k f : 3
  rfl

lemma cochainComplexMap_comp
    (ψ : M →ₗ⁅R,L⁆ M') (φ : N →ₗ⁅R,L⁆ M) :
    cochainComplexMap (ψ.comp φ) = cochainComplexMap φ ≫ cochainComplexMap ψ := by
  ext k f : 3
  rfl

end Map

/-! ### Contraction and transpose -/

/-- The contraction `(ι_y f)(c) = f(y ∧ c)` of a cochain. -/
def contract (y : L) : Module.End R (ExteriorAlgebra R L →ₗ[R] N) :=
  LinearMap.lcomp R N (LinearMap.mulLeft R (ι R y))

omit [LieRingModule L N] [LieModule R L N] in
@[simp] lemma contract_apply (y : L) (f : ExteriorAlgebra R L →ₗ[R] N) (c : ExteriorAlgebra R L) :
    contract y f c = f (ι R y * c) := rfl

lemma cochainExt_wedge (f : ExteriorAlgebra R L →ₗ[R] N) (y : L) (t : E) :
    cochainExt R L N f (wedge R L (LeftRegular R L) y t) = cochainExt R L N (contract y f) t := by
  induction t with
  | tmul c u => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- The Lie derivative `(θ_y f)(c) = f̃(θ(y)(c ⊗ 1))` of a cochain; see `lieDeriv_one`
and `contract_lieDeriv` for its recursion. -/
def lieDeriv (y : L) (f : ExteriorAlgebra R L →ₗ[R] N) : ExteriorAlgebra R L →ₗ[R] N :=
  cochainExt R L N f ∘ₗ lieAction R L (LeftRegular R L) y ∘ₗ
    (TensorProduct.mk R _ _).flip ((LeftRegular.equiv R L).symm 1)

lemma lieDeriv_one (y : L) (f : ExteriorAlgebra R L →ₗ[R] N) :
    lieDeriv y f 1 = -⁅y, f 1⁆ := by
  change cochainExt R L N f (lieAction R L (LeftRegular R L) y (1 ⊗ₜ _)) = _
  rw [lieAction_one_tmul, cochainExt_tmul]
  have : LeftRegular.equiv R L ⁅y, (LeftRegular.equiv R L).symm 1⁆ =
      UniversalEnvelopingAlgebra.ι R y := by simp
  rw [this, envAction_ι]

lemma contract_lieDeriv (y z : L) (f : ExteriorAlgebra R L →ₗ[R] N) :
    contract z (lieDeriv y f) = contract ⁅y, z⁆ f + lieDeriv y (contract z f) := by
  ext c
  change cochainExt R L N f (lieAction R L (LeftRegular R L) y
      (wedge R L (LeftRegular R L) z (c ⊗ₜ (LeftRegular.equiv R L).symm 1))) = _
  rw [lieAction_wedge, map_add, cochainExt_wedge, cochainExt_wedge, LinearMap.add_apply,
    cochainExt_one]
  rfl

/-- The recursion `ι_y (δf) = -θ_y f - δ(ι_y f)`. -/
lemma contract_cochainDiff (y : L) (f : ExteriorAlgebra R L →ₗ[R] N) :
    contract y (cochainDiff R L N f) = -lieDeriv y f - cochainDiff R L N (contract y f) := by
  ext c
  change cochainExt R L N f (diff R L (LeftRegular R L)
      (wedge R L (LeftRegular R L) y (c ⊗ₜ (LeftRegular.equiv R L).symm 1))) = _
  rw [diff_wedge, map_sub, map_neg, cochainExt_wedge, LinearMap.sub_apply, LinearMap.neg_apply]
  rfl

section Transpose

variable {X : Type*} [AddCommGroup X] [Module R X] [LieRingModule L X] [LieModule R L X]

variable (B : N →ₗ[R] X →ₗ[R] R)

/-- The pairing `f̂(c ⊗ m) = B(f c, m)` of a cochain with the chains `⋀L ⊗ X`. -/
def cochainPair : (ExteriorAlgebra R L →ₗ[R] N) →ₗ[R] (ExteriorAlgebra R L ⊗[R] X →ₗ[R] R) :=
  (TensorProduct.lift.equiv (RingHom.id R) _ _ _).toLinearMap ∘ₗ
    LinearMap.llcomp R (ExteriorAlgebra R L) N (X →ₗ[R] R) B

omit [LieRingModule L N] [LieModule R L N] [LieRingModule L X] [LieModule R L X] in
@[simp] lemma cochainPair_tmul (f : ExteriorAlgebra R L →ₗ[R] N) (c : ExteriorAlgebra R L)
    (m : X) : cochainPair B f (c ⊗ₜ m) = B (f c) m := rfl

omit [LieRingModule L N] [LieModule R L N] [LieRingModule L X] [LieModule R L X] in
lemma cochainPair_wedge (f : ExteriorAlgebra R L →ₗ[R] N) (y : L) (t : ExteriorAlgebra R L ⊗[R] X) :
    cochainPair B f (wedge R L X y t) = cochainPair B (contract y f) t := by
  induction t with
  | tmul c m => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']

variable {B}

lemma cochainPair_lieDeriv (hB : ∀ (x : L) (n : N) (m : X), B ⁅x, n⁆ m = -B n ⁅x, m⁆) (y : L)
    (f : ExteriorAlgebra R L →ₗ[R] N) (t : ExteriorAlgebra R L ⊗[R] X) :
    cochainPair B (lieDeriv y f) t = cochainPair B f (lieAction R L X y t) := by
  induction t using induction generalizing f with
  | one m => simp [lieDeriv_one, hB]
  | wedge z t ht =>
    rw [cochainPair_wedge, contract_lieDeriv, map_add, LinearMap.add_apply, ht, lieAction_wedge,
      map_add, cochainPair_wedge, cochainPair_wedge]
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- **Transpose formula**: for an `L`-invariant pairing `B : N × X → R`
(`B(x n, m) = -B(n, x m)`), the codifferential `δ` is the transpose of the chain
differential `d` on `⋀L ⊗ X`: `(δf)^ = f̂ ∘ d`. -/
theorem cochainPair_cochainDiff (hB : ∀ (x : L) (n : N) (m : X), B ⁅x, n⁆ m = -B n ⁅x, m⁆)
    (f : ExteriorAlgebra R L →ₗ[R] N) (t : ExteriorAlgebra R L ⊗[R] X) :
    cochainPair B (cochainDiff R L N f) t = cochainPair B f (diff R L X t) := by
  induction t using induction generalizing f with
  | one m => simp [cochainDiff_one]
  | wedge y t ht =>
    rw [cochainPair_wedge, contract_cochainDiff, map_sub, map_neg, LinearMap.sub_apply,
      LinearMap.neg_apply, ht, cochainPair_lieDeriv hB, diff_wedge, map_sub, map_neg,
      cochainPair_wedge]
  | add t t' ht ht' => simp only [map_add, ht, ht']

end Transpose

end Cochains

end LieModule.ChevalleyEilenberg
