/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.Euler

/-!
# Codifferentials and Laplacians on the Chevalley–Eilenberg complex

Let `L` be a Lie algebra and `M` an `L`-module over a commutative ring `R`. On the chains
`⋀L ⊗ M` we have the Chevalley–Eilenberg differential `d` (`LieModule.ChevalleyEilenberg.diff`),
characterized by `d(1 ⊗ m) = 0` and `d ∘ ε(y) = -θ(y) - ε(y) ∘ d`, where `ε(y)` is left
multiplication by `y ∈ L` and `θ(y)` the action of `y`. In the same way, given
* a linear map `δ₀ : M → ⋀L ⊗ M`, and
* a linear family `G(y)` of operators on `⋀L ⊗ M` with `G(y) ε(y) = ε(y) G(y)`,

there is a unique operator `δ` on `⋀L ⊗ M` with `δ(1 ⊗ m) = δ₀ m` and
`δ ∘ ε(y) = -G(y) - ε(y) ∘ δ` (`LieModule.ChevalleyEilenberg.coDiff`). This is the shape of
Kostant's "adjoint" `∂` of the differential ([Kostant 1961, §2 (check)]): for `𝔫₋`-homology,
`δ₀ m = -∑ f_a ⊗ e_a m` and `G(y) = ½ ∑ ε(f_a) ε(π[e_a, y])` (see
`LieLean.Algebra.Lie.KacMoody.Kostant.Identity`).

We compute the commutation of the *Laplacian* `□ = dδ + δd` with the operators `ε(y)`:
`□ ε(y) = ε(y) □ + R(y)` with `R(y) = [θ(y), δ] - d G(y) + G(y) d` (`laplacian_wedge`), and, if
the `G(y)` commute with all `ε(z)`,
`R(y) ε(z) = -ε(z) R(y) + G([y, z]) - [θ(y), G(z)] + [θ(z), G(y)]` (`laplacianComm_wedge`).
These reduce Kostant's identity to computations in degrees `0` and `1`. Finally, if `□` acts on
a cycle `c` of degree `k` by an invertible scalar, then `c` is a boundary, since
`c = d(s⁻¹ δ c)` (`mem_boundaries_of_laplacian_eq_smul`).

## Main definitions

* `LieModule.ChevalleyEilenberg.coDiff`: the operator `δ` determined by `δ₀` and `G`.
* `LieModule.ChevalleyEilenberg.laplacian`: `□ = dδ + δd`.
* `LieModule.ChevalleyEilenberg.laplacianComm`: the operator `R(y) = [θ(y), δ] - d G(y) + G(y) d`.

## Main results

* `LieModule.ChevalleyEilenberg.laplacian_wedge`, `laplacianComm_wedge`: the commutation rules.
* `LieModule.ChevalleyEilenberg.coDiff_mem_chainsIn`: `δ` raises the degree by one.
* `LieModule.ChevalleyEilenberg.mem_boundaries_of_laplacian_eq_smul`: cycles on which `□` acts by
  an invertible scalar are boundaries.
* `LieModule.ChevalleyEilenberg.DerivAction.laplacian_eq_smul_of_mem_chainWeightSpace`: a
  criterion for `□` to act on each weight space of the chains by a scalar.

## References

* B. Kostant, *Lie algebra cohomology and the generalized Borel–Weil theorem*, Ann. of Math.
  **74** (1961), 329–387 (check).
* The recursive definition and the commutation rules are reconstructed by us, in the style of
  `LieLean.Algebra.Lie.Homology.ChevalleyEilenberg`.
-/

open Module TensorProduct ExteriorAlgebra

noncomputable section

namespace LieModule.ChevalleyEilenberg

/-! ### The codifferential -/

section CoDiff

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M]

local notation "E" => ExteriorAlgebra R L ⊗[R] M

variable (δ₀ : M →ₗ[R] ExteriorAlgebra R L ⊗[R] M)
  (G : L →ₗ[R] Module.End R (ExteriorAlgebra R L ⊗[R] M))

/-- The recursion step for `coDiff`: `(y, ω, g) ↦ (m ↦ -G(y)(ω ⊗ m) - y ∧ g m)`. -/
def coDiffStep : L →ₗ[R] ExteriorAlgebra R L × (M →ₗ[R] E) →ₗ[R] (M →ₗ[R] E) :=
  LinearMap.mk₂ R
    (fun y p ↦ -(G y ∘ₗ TensorProduct.mk R _ M p.1) - wedge R L M y ∘ₗ p.2)
    (fun y y' p ↦ by ext m; simp; abel)
    (fun r y p ↦ by ext m; simp [smul_sub])
    (fun y p p' ↦ by ext m; simp; abel)
    (fun r y p ↦ by ext m; simp [smul_sub])

lemma coDiffStep_apply (y : L) (p : ExteriorAlgebra R L × (M →ₗ[R] E)) (m : M) :
    coDiffStep G y p m = -G y (p.1 ⊗ₜ m) - wedge R L M y (p.2 m) := rfl

omit G in
/-- Left multiplications by elements of `L` anticommute on `⋀L ⊗ M`. -/
lemma wedge_wedge_comm (a b : L) (c : E) :
    wedge R L M a (wedge R L M b c) = -wedge R L M b (wedge R L M a c) := by
  have h := wedge_wedge (R := R) (M := M) (a + b) c
  simp only [map_add, LinearMap.add_apply, wedge_wedge, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)

omit G in
lemma wedge_wedge_wedge_comm (a b z : L) (c : E) :
    wedge R L M a (wedge R L M b (wedge R L M z c)) =
      wedge R L M z (wedge R L M a (wedge R L M b c)) := by
  rw [wedge_wedge_comm b z, map_neg, wedge_wedge_comm a z, neg_neg]

omit G in
lemma ι_tmul_mem_chainsIn_one (y : L) (m : M) :
    (ι R y : ExteriorAlgebra R L) ⊗ₜ m ∈ chainsIn R L M 1 := by
  have := wedge_mem_chainsIn (M := M) y (one_tmul_mem_chainsIn (R := R) (L := L) m)
  rwa [wedge_tmul, mul_one] at this

variable (hG : ∀ y, G y ∘ₗ wedge R L M y = wedge R L M y ∘ₗ G y)
include hG

lemma coDiffStep_step (y : L) (ω : ExteriorAlgebra R L) (g : M →ₗ[R] E) :
    coDiffStep G y (ι R y * ω, coDiffStep G y (ω, g)) =
      (0 : QuadraticForm R L) y • g := by
  ext m
  rw [coDiffStep_apply, coDiffStep_apply, ← wedge_tmul, ← LinearMap.comp_apply (G y), hG y]
  simp

/-- Auxiliary for `coDiff`: the fold over `⋀L`. -/
def coDiffFold : ExteriorAlgebra R L →ₗ[R] M →ₗ[R] E :=
  CliffordAlgebra.foldr' (0 : QuadraticForm R L) (coDiffStep G)
    (fun y ω g ↦ by exact coDiffStep_step G hG y ω g) δ₀

/-- The operator `δ` on `⋀L ⊗ M` determined by `δ(1 ⊗ m) = δ₀ m` and
`δ(y ∧ c) = -G(y) c - y ∧ δ c`. -/
def coDiff : Module.End R E := TensorProduct.lift (coDiffFold δ₀ G hG)

lemma coDiffFold_ι_mul (y : L) (ω : ExteriorAlgebra R L) :
    coDiffFold δ₀ G hG (ι R y * ω) = coDiffStep G y (ω, coDiffFold δ₀ G hG ω) :=
  CliffordAlgebra.foldr'_ι_mul _ _ _ _ _ _

@[simp] lemma coDiff_one_tmul (m : M) : coDiff δ₀ G hG (1 ⊗ₜ m) = δ₀ m := by
  have h := CliffordAlgebra.foldr'_algebraMap (0 : QuadraticForm R L) (coDiffStep G)
    (fun y ω g ↦ by exact coDiffStep_step G hG y ω g) δ₀ (1 : R)
  rw [map_one, one_smul] at h
  exact LinearMap.congr_fun h m

/-- The recursion formula `δ(y ∧ c) = -G(y) c - y ∧ δ c`. -/
lemma coDiff_wedge (y : L) (c : E) :
    coDiff δ₀ G hG (wedge R L M y c) = -G y c - wedge R L M y (coDiff δ₀ G hG c) := by
  induction c with
  | add c c' hc hc' => simp only [map_add, hc, hc']; abel
  | tmul ω m => exact LinearMap.congr_fun (coDiffFold_ι_mul δ₀ G hG y ω) m

/-- `δ` raises the degree by one if `δ₀` has values in degree `1` and the `G(y)` raise the degree
by two. -/
theorem coDiff_mem_chainsIn (hδ₀ : ∀ m, δ₀ m ∈ chainsIn R L M 1)
    (hGk : ∀ y k c, c ∈ chainsIn R L M k → G y c ∈ chainsIn R L M (k + 2))
    {k : ℕ} {c : E} (hc : c ∈ chainsIn R L M k) : coDiff δ₀ G hG c ∈ chainsIn R L M (k + 1) := by
  induction k generalizing c with
  | zero =>
    refine chainsIn_zero_le (S := (chainsIn R L M 1).comap (coDiff δ₀ G hG))
      (fun m ↦ ?_) hc
    rw [Submodule.mem_comap, coDiff_one_tmul]
    exact hδ₀ m
  | succ k ih =>
    refine chainsIn_succ_le (S := (chainsIn R L M (k + 2)).comap (coDiff δ₀ G hG))
      (fun y c hc ↦ ?_) hc
    rw [Submodule.mem_comap, coDiff_wedge]
    exact sub_mem (neg_mem (hGk y k c hc)) (wedge_mem_chainsIn y (ih hc))

/-! ### The Laplacian -/

variable [LieRingModule L M] [LieModule R L M]

/-- The Laplacian `□ = dδ + δd`. -/
def laplacian : Module.End R E :=
  diff R L M ∘ₗ coDiff δ₀ G hG + coDiff δ₀ G hG ∘ₗ diff R L M

/-- The operator `R(y) = [θ(y), δ] - d G(y) + G(y) d` measuring the failure of `□` to commute
with `ε(y)`. -/
def laplacianComm (y : L) : Module.End R E :=
  lieAction R L M y ∘ₗ coDiff δ₀ G hG - coDiff δ₀ G hG ∘ₗ lieAction R L M y -
    diff R L M ∘ₗ G y + G y ∘ₗ diff R L M

lemma laplacian_apply (c : E) :
    laplacian δ₀ G hG c = diff R L M (coDiff δ₀ G hG c) + coDiff δ₀ G hG (diff R L M c) := rfl

lemma laplacianComm_apply (y : L) (c : E) :
    laplacianComm δ₀ G hG y c = lieAction R L M y (coDiff δ₀ G hG c) -
      coDiff δ₀ G hG (lieAction R L M y c) - diff R L M (G y c) + G y (diff R L M c) := rfl

@[simp] lemma laplacian_one_tmul (m : M) :
    laplacian δ₀ G hG (1 ⊗ₜ m) = diff R L M (δ₀ m) := by
  simp [laplacian_apply]

lemma laplacianComm_one_tmul (y : L) (m : M) :
    laplacianComm δ₀ G hG y (1 ⊗ₜ m) =
      lieAction R L M y (δ₀ m) - δ₀ ⁅y, m⁆ - diff R L M (G y (1 ⊗ₜ m)) := by
  simp [laplacianComm_apply]

/-- `□ ε(y) = ε(y) □ + R(y)`. -/
theorem laplacian_wedge (y : L) (c : E) :
    laplacian δ₀ G hG (wedge R L M y c) =
      wedge R L M y (laplacian δ₀ G hG c) + laplacianComm δ₀ G hG y c := by
  simp only [laplacian_apply, laplacianComm_apply, coDiff_wedge, diff_wedge, map_sub, map_neg,
    map_add]
  abel

/-- `R(y) ε(z) = -ε(z) R(y) + G([y, z]) - [θ(y), G(z)] + [θ(z), G(y)]`, if the `G(y)` commute
with the `ε(z)`. -/
theorem laplacianComm_wedge (hGε : ∀ y z, G y ∘ₗ wedge R L M z = wedge R L M z ∘ₗ G y)
    (y z : L) (c : E) :
    laplacianComm δ₀ G hG y (wedge R L M z c) =
      -wedge R L M z (laplacianComm δ₀ G hG y c) + (G ⁅y, z⁆ c -
        (lieAction R L M y (G z c) - G z (lieAction R L M y c)) +
        (lieAction R L M z (G y c) - G y (lieAction R L M z c))) := by
  have h (c : E) : G y (wedge R L M z c) = wedge R L M z (G y c) :=
    LinearMap.congr_fun (hGε y z) c
  simp only [laplacianComm_apply, coDiff_wedge, diff_wedge, lieAction_wedge, map_sub, map_neg,
    map_add, h]
  abel

end CoDiff

section Formulas

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "E" => ExteriorAlgebra R L ⊗[R] M

lemma lieAction_wedge_one_tmul (y a : L) (m : M) :
    lieAction R L M y (wedge R L M a (1 ⊗ₜ m)) =
      wedge R L M ⁅y, a⁆ (1 ⊗ₜ m) + wedge R L M a (1 ⊗ₜ ⁅y, m⁆) := by
  rw [lieAction_wedge, lieAction_one_tmul]

lemma lieAction_wedge_wedge (y a b : L) (c : E) :
    lieAction R L M y (wedge R L M a (wedge R L M b c)) =
      wedge R L M ⁅y, a⁆ (wedge R L M b c) + wedge R L M a (wedge R L M ⁅y, b⁆ c) +
        wedge R L M a (wedge R L M b (lieAction R L M y c)) := by
  rw [lieAction_wedge, lieAction_wedge, map_add, add_assoc]

lemma diff_wedge_one_tmul (a : L) (m : M) :
    diff R L M (wedge R L M a (1 ⊗ₜ m)) = -(1 ⊗ₜ ⁅a, m⁆) := by
  rw [wedge_tmul, mul_one, diff_ι_tmul]

lemma diff_wedge_wedge_one_tmul (a b : L) (m : M) :
    diff R L M (wedge R L M a (wedge R L M b (1 ⊗ₜ m))) =
      -wedge R L M b (1 ⊗ₜ ⁅a, m⁆) + wedge R L M a (1 ⊗ₜ ⁅b, m⁆) -
        wedge R L M ⁅a, b⁆ (1 ⊗ₜ m) := by
  simp only [wedge_tmul, mul_one]
  exact diff_ι_mul_ι_tmul a b m

end Formulas

/-! ### Cycles on which the Laplacian is invertible -/

section Boundaries

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  (δ₀ : M →ₗ[K] ExteriorAlgebra K L ⊗[K] M) (G : L →ₗ[K] Module.End K (ExteriorAlgebra K L ⊗[K] M))
  (hG : ∀ y, G y ∘ₗ wedge K L M y = wedge K L M y ∘ₗ G y)

/-- A cycle `c` of degree `k` with `□ c = s c`, `s ≠ 0`, is a boundary: `c = d(s⁻¹ δ c)`. This is
the algebraic core of Kostant's argument: over a general field there is no harmonic theory, but
`δ` is a contracting homotopy on the eigenspaces of `□` for nonzero eigenvalues. -/
theorem mem_boundaries_of_laplacian_eq_smul
    (hδ : ∀ k c, c ∈ chainsIn K L M k → coDiff δ₀ G hG c ∈ chainsIn K L M (k + 1))
    {k : ℕ} {c : ExteriorAlgebra K L ⊗[K] M} (hc : c ∈ cycles K L M k) {s : K} (hs : s ≠ 0)
    (hL : laplacian δ₀ G hG c = s • c) : c ∈ boundaries K L M k := by
  have hdc : diff K L M c = 0 := hc.2
  rw [laplacian_apply, hdc, map_zero, add_zero] at hL
  refine ⟨s⁻¹ • coDiff δ₀ G hG c, Submodule.smul_mem _ _ (hδ k c hc.1), ?_⟩
  rw [map_smul, hL, smul_smul, inv_mul_cancel₀ hs, one_smul]

end Boundaries

/-! ### Operators acting by scalars on the weight spaces of the chains -/

namespace DerivAction

variable {K H L M : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] {ρ : DerivAction K H L M}
  {I J : Type*} [LinearOrder I] (bL : Basis I K L) (bM : Basis J K M)
  {γ : I → Dual K H} {ν : J → Dual K H}
  (hbL : ∀ i, bL i ∈ Module.End.weightSpaceOf ρ.D (γ i))
  (hbM : ∀ j, bM j ∈ Module.End.weightSpaceOf ρ.φ (ν j))
  (T : Module.End K (ExteriorAlgebra K L ⊗[K] M)) (s : Dual K H → K)
  (hbase : ∀ j, T (1 ⊗ₜ bM j) = s (ν j) • (1 ⊗ₜ bM j))
  (hstep : ∀ i μ c, c ∈ ρ.chainWeightSpace μ → T c = s μ • c →
    T (wedge K L M (bL i) c) = s (γ i + μ) • wedge K L M (bL i) c)
include hbL hbM hbase hstep

omit [LinearOrder I] in
lemma apply_ιMulti_tmul_eq_smul (n : ℕ) (f : Fin n → I) (j : J) :
    T (ιMulti K n (bL ∘ f) ⊗ₜ bM j) = s (∑ k, γ (f k) + ν j) • (ιMulti K n (bL ∘ f) ⊗ₜ bM j) := by
  induction n with
  | zero => simpa using hbase j
  | succ n ih =>
    have hc := ιMulti_tmul_mem_chainWeightSpace (ρ := ρ) (bL ∘ Matrix.vecTail f)
      (γ ∘ Matrix.vecTail f) (fun k ↦ hbL _) (hbM j)
    rw [ιMulti_succ_apply, ← wedge_tmul, Fin.sum_univ_succ, add_assoc]
    exact hstep (f 0) _ _ hc (ih (Matrix.vecTail f))

/-- **A criterion for an operator to act by scalars on the weight spaces of the chains**: if `T`
acts on `1 ⊗ m_j` by `s(ν_j)`, and `T (y_i ∧ c) = s(γ_i + μ) (y_i ∧ c)` whenever `c` has weight
`μ` and `T c = s(μ) c`, then `T` acts on the weight-`μ` chains by `s(μ)`, for all `μ`. -/
theorem apply_eq_smul_of_mem_chainWeightSpace {μ : Dual K H} {c : ExteriorAlgebra K L ⊗[K] M}
    (hc : c ∈ ρ.chainWeightSpace μ) : T c = s μ • c := by
  rw [chainWeightSpace_eq_span bL bM hbL hbM μ] at hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    rw [← Set.mem_ofPred_eq (p := fun t ↦ chainWt γ ν t = μ).mp ht, chainBasis_apply,
      basis_exteriorAlgebra_eq]
    convert apply_ιMulti_tmul_eq_smul bL bM hbL hbM T s hbase hstep _
      (t.1.orderEmbOfFin rfl) t.2 using 3
    rw [chainWt]
    conv_lhs => rw [← Finset.image_orderEmbOfFin_univ t.1 rfl]
    rw [Finset.sum_image fun _ _ _ _ h ↦ (t.1.orderEmbOfFin rfl).injective h]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul r x _ hx => rw [map_smul, hx, smul_comm]

end DerivAction

end LieModule.ChevalleyEilenberg
