/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# The Chevalley–Eilenberg differential

Let `L` be a Lie algebra over a commutative ring `R` and `M` a Lie module over `L`. The
Chevalley–Eilenberg complex computing the Lie algebra homology `H_•(L, M)` has chains
`C_k(L, M) = ⋀ᵏ L ⊗ M` and differential
`d(x₁ ∧ ⋯ ∧ x_k ⊗ m) = ∑ᵢ (-1)ⁱ x₁ ∧ ⋯ x̂ᵢ ⋯ ∧ x_k ⊗ xᵢ m`
`  + ∑_{i < j} (-1)^{i+j} [xᵢ, xⱼ] ∧ x₁ ∧ ⋯ x̂ᵢ ⋯ x̂ⱼ ⋯ ∧ x_k ⊗ m`
(indices from `1`). This is the complex of [Weibel, §7.7] for the right module structure
`m · x = -x m`; for trivial coefficients it agrees with `LieAlgebra.ChevalleyEilenberg.d₂`.

In this file we construct `d` on the whole space `⋀L ⊗ M` (with `⋀L` the exterior algebra),
together with the action `θ(x)` of `x ∈ L` on `⋀L ⊗ M` (by the derivation extending `ad x` on
`⋀L`, and by `x` on `M`), and prove `d ∘ d = 0`. The grading is dealt with in
`LieLean.Algebra.Lie.Homology.Complex`.

## Design

Rather than working with the explicit formula (which needs heavy bookkeeping of signs and
indices), we characterize all operators by recursion over the exterior algebra, using Mathlib's
`CliffordAlgebra.foldr'` (the exterior algebra is the Clifford algebra of the zero form). Writing
`ε(y)` for left multiplication `c ↦ y ∧ c` on `⋀L ⊗ M`, the operators are determined by
* `θ(x)(1 ⊗ m) = 1 ⊗ x m` and `θ(x) ∘ ε(y) = ε([x, y]) + ε(y) ∘ θ(x)`;
* `d(1 ⊗ m) = 0` and `d ∘ ε(y) = -θ(y) - ε(y) ∘ d` (a form of the Cartan formula).
Unwinding the recursion gives the displayed formula. The identities
`[θ(x), θ(y)] = θ([x, y])`, `d ∘ θ(x) = θ(x) ∘ d` and `d ∘ d = 0` then follow by a simple
induction over the generators `y ∧ c` (`LieModule.ChevalleyEilenberg.induction`). More generally
we define `θ(D, φ)` for a derivation `D` of `L` and a compatible endomorphism `φ` of `M`
(`φ (x m) = (D x) m + x (φ m)`); it commutes with `d`. This gives, for instance, the action of a
Cartan subalgebra `𝔥` on the complex of `𝔫₋`.

## Main definitions

* `LieModule.ChevalleyEilenberg.wedge`: `ε(y)`, left multiplication by `y ∈ L` on `⋀L ⊗ M`.
* `LieModule.ChevalleyEilenberg.derivExt`: the operator `θ(D, φ)` on `⋀L ⊗ M`.
* `LieModule.ChevalleyEilenberg.lieAction`: `θ(x) = θ(ad x, x_M)`.
* `LieModule.ChevalleyEilenberg.diff`: the Chevalley–Eilenberg differential `d` on `⋀L ⊗ M`.

## Main results

* `LieModule.ChevalleyEilenberg.lieAction_lie`: `θ([x, y]) = [θ(x), θ(y)]`.
* `LieModule.ChevalleyEilenberg.diff_comp_derivExt`: `d` commutes with `θ(D, φ)`.
* `LieModule.ChevalleyEilenberg.diff_comp_diff`: `d ∘ d = 0`.
* `LieModule.ChevalleyEilenberg.diff_ι_tmul`, `diff_ι_mul_ι_tmul`: the explicit formula in degrees
  `1` and `2`: `d(x ⊗ m) = -(1 ⊗ x m)`, `d(x ∧ y ⊗ m) = -y ⊗ x m + x ⊗ y m - [x, y] ⊗ m`.
* `LieModule.ChevalleyEilenberg.lTensor_comp_diff`: naturality of `d` in `M`.

## References

* C. A. Weibel, *An introduction to homological algebra*, CUP 1994, §7.7.
* H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent. Math.
  **34** (1976), 37–76, §1, pp. 41–42.
* The recursive characterization and the inductive proof of `d ∘ d = 0` are standard (they are
  the homological Cartan formulas `θ(x) = -(d ε(x) + ε(x) d)`); the argument here was
  reconstructed by us.
-/

open TensorProduct ExteriorAlgebra

noncomputable section

namespace LieModule.ChevalleyEilenberg

section Module

variable (R L M : Type*) [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R L ⊗[R] M

/-- Left multiplication `ε(y) : c ↦ y ∧ c` by `y ∈ L` on `⋀L ⊗ M`. -/
def wedge : L →ₗ[R] Module.End R E :=
  LinearMap.rTensorHom M ∘ₗ LinearMap.mul R (ExteriorAlgebra R L) ∘ₗ ι R

variable {R L M}

@[simp] lemma wedge_tmul (y : L) (ω : ExteriorAlgebra R L) (m : M) :
    wedge R L M y (ω ⊗ₜ m) = (ι R y * ω) ⊗ₜ m := rfl

@[simp] lemma wedge_wedge (y : L) (c : E) : wedge R L M y (wedge R L M y c) = 0 := by
  induction c with
  | tmul ω m => simp [← mul_assoc]
  | add c c' hc hc' => simp [hc, hc']

/-- **Induction principle** for `⋀L ⊗ M`: a property which holds for all `1 ⊗ m`, is stable under
all `ε(y)` and under addition holds everywhere. -/
theorem induction {p : E → Prop} (one : ∀ m : M, p (1 ⊗ₜ m))
    (wedge : ∀ (y : L) (c : E), p c → p (wedge R L M y c))
    (add : ∀ c c' : E, p c → p c' → p (c + c')) (c : E) : p c := by
  induction c with
  | add c c' hc hc' => exact add c c' hc hc'
  | tmul ω m =>
    induction ω using CliffordAlgebra.left_induction generalizing m with
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
      exact one _
    | add ω ω' hω hω' => rw [add_tmul]; exact add _ _ (hω m) (hω' m)
    | ι_mul ω y hω => exact wedge y _ (hω m)

/-- Two linear maps out of `⋀L ⊗ M` agree if they agree on all `1 ⊗ m` and agreement on `c`
implies agreement on each `y ∧ c`. -/
theorem ext_of {N : Type*} [AddCommGroup N] [Module R N] {f g : E →ₗ[R] N}
    (one : ∀ m : M, f (1 ⊗ₜ m) = g (1 ⊗ₜ m))
    (wedge : ∀ (y : L) (c : E), f c = g c → f (wedge R L M y c) = g (wedge R L M y c)) :
    f = g :=
  LinearMap.ext fun c ↦ induction one wedge (fun c c' hc hc' ↦ by simp [hc, hc']) c

/-! ### The operators `θ(D, φ)` -/

section DerivExt

variable (D : L →ₗ[R] L) (φ : M →ₗ[R] M)

/-- The recursion step for `derivExt`: `(y, ω, g) ↦ (m ↦ D y ∧ ω ⊗ m + y ∧ g m)`. -/
def derivExtStep : L →ₗ[R] ExteriorAlgebra R L × (M →ₗ[R] E) →ₗ[R] (M →ₗ[R] E) :=
  LinearMap.mk₂ R (fun y p ↦ TensorProduct.mk R _ M (ι R (D y) * p.1) + wedge R L M y ∘ₗ p.2)
    (fun y y' p ↦ by ext m; simp [add_mul]; abel)
    (fun r y p ↦ by ext m; simp [smul_tmul', smul_add])
    (fun y p p' ↦ by ext m; simp [mul_add]; abel)
    (fun r y p ↦ by ext m; simp [smul_tmul', smul_add])

lemma derivExtStep_apply (y : L) (p : ExteriorAlgebra R L × (M →ₗ[R] E)) (m : M) :
    derivExtStep D y p m = (ι R (D y) * p.1) ⊗ₜ m + wedge R L M y (p.2 m) := rfl

lemma derivExtStep_step (y : L) (ω : ExteriorAlgebra R L) (g : M →ₗ[R] E) :
    derivExtStep D y (ι R y * ω, derivExtStep D y (ω, g)) =
      (0 : QuadraticForm R L) y • g := by
  ext m
  rw [derivExtStep_apply, derivExtStep_apply, map_add, wedge_wedge, add_zero, wedge_tmul,
    ← mul_assoc, ← mul_assoc, ← add_tmul, ← add_mul, ι_add_mul_swap]
  simp

/-- Auxiliary for `derivExt`: the fold over `⋀L`. -/
def derivExtFold : ExteriorAlgebra R L →ₗ[R] M →ₗ[R] E :=
  CliffordAlgebra.foldr' (0 : QuadraticForm R L) (derivExtStep D)
    (fun y ω g ↦ by exact derivExtStep_step D y ω g)
    ((TensorProduct.mk R (ExteriorAlgebra R L) M 1).comp φ)

/-- The operator `θ(D, φ)` on `⋀L ⊗ M` determined by `θ(D, φ)(1 ⊗ m) = 1 ⊗ φ m` and
`θ(D, φ)(y ∧ c) = D y ∧ c + y ∧ θ(D, φ) c`. When `D` is a derivation of `L` and
`φ (x m) = (D x) m + x (φ m)`, it commutes with the Chevalley–Eilenberg differential. -/
def derivExt : Module.End R E :=
  TensorProduct.lift (derivExtFold D φ)

lemma derivExtFold_algebraMap (r : R) :
    derivExtFold D φ (algebraMap R _ r) =
      r • (TensorProduct.mk R (ExteriorAlgebra R L) M 1).comp φ :=
  CliffordAlgebra.foldr'_algebraMap _ _ _ _ _

lemma derivExtFold_ι_mul (y : L) (ω : ExteriorAlgebra R L) :
    derivExtFold D φ (ι R y * ω) = derivExtStep D y (ω, derivExtFold D φ ω) :=
  CliffordAlgebra.foldr'_ι_mul _ _ _ _ _ _

@[simp] lemma derivExt_one_tmul (m : M) : derivExt D φ (1 ⊗ₜ m) = 1 ⊗ₜ φ m := by
  have h := derivExtFold_algebraMap D φ 1
  rw [map_one, one_smul] at h
  exact LinearMap.congr_fun h m

lemma derivExt_wedge (y : L) (c : E) :
    derivExt D φ (wedge R L M y c) = wedge R L M (D y) c + wedge R L M y (derivExt D φ c) := by
  induction c with
  | add c c' hc hc' => simp only [map_add, hc, hc']; abel
  | tmul ω m => exact LinearMap.congr_fun (derivExtFold_ι_mul D φ y ω) m

lemma derivExt_comp_wedge (y : L) :
    derivExt D φ ∘ₗ wedge R L M y = wedge R L M (D y) + wedge R L M y ∘ₗ derivExt D φ :=
  LinearMap.ext (derivExt_wedge D φ y)

lemma derivExt_add (D' : L →ₗ[R] L) (φ' : M →ₗ[R] M) :
    derivExt (D + D') (φ + φ') = derivExt D φ + derivExt (M := M) D' φ' := by
  refine ext_of (fun m ↦ by simp [tmul_add]) fun y c hc ↦ ?_
  simp only [LinearMap.add_apply, derivExt_wedge, hc, map_add, LinearMap.add_apply]
  abel

lemma derivExt_smul (r : R) : derivExt (r • D) (r • φ) = r • derivExt D φ := by
  refine ext_of (fun m ↦ by simp [tmul_smul]) fun y c hc ↦ ?_
  simp only [LinearMap.smul_apply, derivExt_wedge, hc, map_smul, LinearMap.smul_apply,
    smul_add]

variable {N : Type*} [AddCommGroup N] [Module R N]

lemma lTensor_comp_wedge (f : M →ₗ[R] N) (y : L) :
    f.lTensor _ ∘ₗ wedge R L M y = wedge R L N y ∘ₗ f.lTensor _ := by
  ext ω m
  simp

lemma lTensor_derivExt (f : M →ₗ[R] N) (φ' : N →ₗ[R] N) (hf : f ∘ₗ φ = φ' ∘ₗ f) (c : E) :
    f.lTensor _ (derivExt D φ c) = derivExt D φ' (f.lTensor _ c) := by
  induction c using induction with
  | one m =>
    simp only [derivExt_one_tmul, LinearMap.lTensor_tmul]
    rw [← LinearMap.comp_apply f φ, hf, LinearMap.comp_apply]
  | wedge y c hc =>
    rw [derivExt_wedge, map_add, ← LinearMap.comp_apply (f.lTensor _),
      ← LinearMap.comp_apply (f.lTensor _), lTensor_comp_wedge, lTensor_comp_wedge,
      LinearMap.comp_apply, LinearMap.comp_apply, hc, ← LinearMap.comp_apply (f.lTensor _),
      lTensor_comp_wedge, LinearMap.comp_apply, derivExt_wedge]
  | add c c' hc hc' => simp only [map_add, hc, hc']

end DerivExt

end Module

/-! ### The action `θ(x)` of `L` -/

section LieAction

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "E" => ExteriorAlgebra R L ⊗[R] M

variable (R L M) in
/-- The action `θ(x) = θ(ad x, x_M)` of `x ∈ L` on `⋀L ⊗ M`:
`θ(x)(y₁ ∧ ⋯ ∧ y_k ⊗ m) = ∑ᵢ y₁ ∧ ⋯ [x, yᵢ] ⋯ ∧ y_k ⊗ m + y₁ ∧ ⋯ ∧ y_k ⊗ x m`. -/
def lieAction : L →ₗ[R] Module.End R E where
  toFun x := derivExt (LieAlgebra.ad R L x) (toEnd R L M x)
  map_add' x x' := by simp only [map_add, derivExt_add]
  map_smul' r x := by simp only [map_smul, derivExt_smul, RingHom.id_apply]

@[simp] lemma lieAction_one_tmul (x : L) (m : M) :
    lieAction R L M x (1 ⊗ₜ m) = 1 ⊗ₜ ⁅x, m⁆ :=
  derivExt_one_tmul _ _ m

lemma lieAction_wedge (x y : L) (c : E) :
    lieAction R L M x (wedge R L M y c) =
      wedge R L M ⁅x, y⁆ c + wedge R L M y (lieAction R L M x c) :=
  derivExt_wedge _ _ y c

/-- `θ([x, y]) = θ(x) θ(y) - θ(y) θ(x)`: the operators `θ` define a representation of `L` on
`⋀L ⊗ M`. -/
theorem lieAction_lie (x y : L) :
    lieAction R L M ⁅x, y⁆ =
      lieAction R L M x ∘ₗ lieAction R L M y - lieAction R L M y ∘ₗ lieAction R L M x := by
  refine ext_of (fun m ↦ by simp [lie_lie, tmul_sub]) fun z c hc ↦ ?_
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, lieAction_wedge, map_add, map_sub, hc,
    lie_lie]
  abel

/-- `θ(D, φ)` commutes with `θ(y)` up to `θ(D y)`, when `D` is a derivation of `L` and `φ` is
compatible with `D`. -/
lemma derivExt_comp_lieAction {D : L →ₗ[R] L} {φ : M →ₗ[R] M}
    (hD : ∀ x y, D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆)
    (hφ : ∀ (x : L) (m : M), φ ⁅x, m⁆ = ⁅D x, m⁆ + ⁅x, φ m⁆)
    (y : L) :
    derivExt D φ ∘ₗ lieAction R L M y - lieAction R L M y ∘ₗ derivExt D φ =
      lieAction R L M (D y) := by
  refine ext_of (fun m ↦ ?_) fun z c hc ↦ ?_
  · simp [hφ, tmul_add]
  · simp only [LinearMap.sub_apply, LinearMap.comp_apply] at hc ⊢
    simp only [lieAction_wedge, derivExt_wedge, map_add, map_sub, hD, ← hc, LinearMap.add_apply]
    abel

end LieAction

/-! ### The differential -/

section Diff

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "E" => ExteriorAlgebra R L ⊗[R] M

variable (R L M) in
/-- The recursion step for `diff`: `(y, ω, g) ↦ (m ↦ -θ(y)(ω ⊗ m) - y ∧ g m)`. -/
def diffStep : L →ₗ[R] ExteriorAlgebra R L × (M →ₗ[R] E) →ₗ[R] (M →ₗ[R] E) :=
  LinearMap.mk₂ R
    (fun y p ↦ -(lieAction R L M y ∘ₗ TensorProduct.mk R _ M p.1) - wedge R L M y ∘ₗ p.2)
    (fun y y' p ↦ by ext m; simp; abel)
    (fun r y p ↦ by ext m; simp [smul_sub])
    (fun y p p' ↦ by ext m; simp; abel)
    (fun r y p ↦ by ext m; simp [smul_sub])

lemma diffStep_apply (y : L) (p : ExteriorAlgebra R L × (M →ₗ[R] E)) (m : M) :
    diffStep R L M y p m = -lieAction R L M y (p.1 ⊗ₜ m) - wedge R L M y (p.2 m) := rfl

lemma diffStep_step (y : L) (ω : ExteriorAlgebra R L) (g : M →ₗ[R] E) :
    diffStep R L M y (ι R y * ω, diffStep R L M y (ω, g)) =
      (0 : QuadraticForm R L) y • g := by
  ext m
  rw [diffStep_apply, diffStep_apply, ← wedge_tmul, lieAction_wedge, lie_self, map_zero]
  simp

variable (R L M) in
/-- Auxiliary for `diff`: the fold over `⋀L`. -/
def diffFold : ExteriorAlgebra R L →ₗ[R] M →ₗ[R] E :=
  CliffordAlgebra.foldr' (0 : QuadraticForm R L) (diffStep R L M)
    (fun y ω g ↦ by exact diffStep_step y ω g) (0 : M →ₗ[R] E)

variable (R L M) in
/-- The **Chevalley–Eilenberg differential** `d` on `⋀L ⊗ M`, determined by `d(1 ⊗ m) = 0` and
`d(y ∧ c) = -θ(y) c - y ∧ d c`. Explicitly, `d(x₁ ∧ ⋯ ∧ x_k ⊗ m)` is
`∑ᵢ (-1)ⁱ x₁ ∧ ⋯ x̂ᵢ ⋯ ∧ x_k ⊗ xᵢ m + ∑_{i < j} (-1)^{i+j} [xᵢ, xⱼ] ∧ x₁ ∧ ⋯ x̂ᵢ ⋯ x̂ⱼ ⋯ ∧ x_k ⊗ m`
([Weibel, §7.7], for the right module structure `m · x = -x m`). -/
def diff : Module.End R E := TensorProduct.lift (diffFold R L M)

lemma diffFold_algebraMap (r : R) : diffFold R L M (algebraMap R _ r) = 0 := by
  rw [diffFold, CliffordAlgebra.foldr'_algebraMap, smul_zero]

lemma diffFold_ι_mul (y : L) (ω : ExteriorAlgebra R L) :
    diffFold R L M (ι R y * ω) = diffStep R L M y (ω, diffFold R L M ω) :=
  CliffordAlgebra.foldr'_ι_mul _ _ _ _ _ _

@[simp] lemma diff_one_tmul (m : M) : diff R L M (1 ⊗ₜ m) = 0 := by
  have h := diffFold_algebraMap (M := M) (L := L) (1 : R)
  rw [map_one] at h
  exact LinearMap.congr_fun h m

/-- The recursion formula `d(y ∧ c) = -θ(y) c - y ∧ d c`. -/
lemma diff_wedge (y : L) (c : E) :
    diff R L M (wedge R L M y c) = -lieAction R L M y c - wedge R L M y (diff R L M c) := by
  induction c with
  | add c c' hc hc' => simp only [map_add, hc, hc']; abel
  | tmul ω m => exact LinearMap.congr_fun (diffFold_ι_mul y ω) m

/-- `d(x ⊗ m) = -(1 ⊗ x m)`. -/
lemma diff_ι_tmul (x : L) (m : M) : diff R L M (ι R x ⊗ₜ m) = -(1 ⊗ₜ ⁅x, m⁆) := by
  have := diff_wedge (R := R) (M := M) x (1 ⊗ₜ m)
  rw [wedge_tmul, mul_one] at this
  simp [this]

/-- `d(x ∧ y ⊗ m) = -y ⊗ x m + x ⊗ y m - [x, y] ⊗ m`. -/
lemma diff_ι_mul_ι_tmul (x y : L) (m : M) :
    diff R L M ((ι R x * ι R y) ⊗ₜ m) =
      -(ι R y ⊗ₜ ⁅x, m⁆) + ι R x ⊗ₜ ⁅y, m⁆ - ι R ⁅x, y⁆ ⊗ₜ m := by
  have h1 := diff_wedge (R := R) (M := M) x (ι R y ⊗ₜ m)
  have h2 := lieAction_wedge (R := R) (M := M) x y (1 ⊗ₜ m)
  rw [wedge_tmul] at h1
  rw [wedge_tmul, wedge_tmul, mul_one, mul_one] at h2
  rw [h1, h2, diff_ι_tmul, lieAction_one_tmul]
  simp only [wedge_tmul, map_neg, mul_one]
  abel

/-- The differential `d` commutes with the operators `θ(D, φ)`, for a derivation `D` of `L` and a
compatible endomorphism `φ` of `M`. -/
theorem diff_comp_derivExt {D : L →ₗ[R] L} {φ : M →ₗ[R] M}
    (hD : ∀ x y, D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆)
    (hφ : ∀ (x : L) (m : M), φ ⁅x, m⁆ = ⁅D x, m⁆ + ⁅x, φ m⁆) :
    diff R L M ∘ₗ derivExt D φ = derivExt D φ ∘ₗ diff R L M := by
  refine ext_of (fun m ↦ by simp) fun z c hc ↦ ?_
  have h := LinearMap.congr_fun (derivExt_comp_lieAction hD hφ z) c
  simp only [LinearMap.sub_apply, LinearMap.comp_apply] at hc h ⊢
  simp only [derivExt_wedge, map_add, diff_wedge, hc, map_sub, map_neg, ← h]
  abel

/-- The differential `d` commutes with the action `θ(x)` of `L`. -/
theorem diff_comp_lieAction (x : L) :
    diff R L M ∘ₗ lieAction R L M x = lieAction R L M x ∘ₗ diff R L M :=
  diff_comp_derivExt (fun y z ↦ by simp only [LieAlgebra.ad_apply]; exact leibniz_lie x y z)
    (fun y m ↦ by simp only [LieAlgebra.ad_apply, toEnd_apply_apply]; exact leibniz_lie x y m)

/-- `d ∘ d = 0`. -/
theorem diff_comp_diff : diff R L M ∘ₗ diff R L M = 0 := by
  refine ext_of (fun m ↦ by simp) fun y c hc ↦ ?_
  have h := LinearMap.congr_fun (diff_comp_lieAction (M := M) y) c
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hc h ⊢
  simp only [diff_wedge, map_sub, map_neg, hc, h, map_zero]
  abel

@[simp] lemma diff_diff (c : E) : diff R L M (diff R L M c) = 0 :=
  LinearMap.congr_fun diff_comp_diff c

variable {N : Type*} [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

lemma lTensor_lieAction (f : M →ₗ⁅R,L⁆ N) (x : L) (c : E) :
    (f : M →ₗ[R] N).lTensor _ (lieAction R L M x c) =
      lieAction R L N x ((f : M →ₗ[R] N).lTensor _ c) :=
  lTensor_derivExt _ _ _ _ (LinearMap.ext fun m ↦ by simp) c

/-- **Naturality** of the differential in the coefficient module. -/
theorem lTensor_diff (f : M →ₗ⁅R,L⁆ N) (c : E) :
    (f : M →ₗ[R] N).lTensor _ (diff R L M c) = diff R L N ((f : M →ₗ[R] N).lTensor _ c) := by
  induction c using induction with
  | one m => simp
  | wedge y c hc =>
    rw [diff_wedge, map_sub, map_neg, lTensor_lieAction,
      ← LinearMap.comp_apply (LinearMap.lTensor _ _), lTensor_comp_wedge, LinearMap.comp_apply, hc,
      ← LinearMap.comp_apply (LinearMap.lTensor _ _), lTensor_comp_wedge, LinearMap.comp_apply,
      diff_wedge]
  | add c c' hc hc' => simp only [map_add, hc, hc']

end Diff

end LieModule.ChevalleyEilenberg
