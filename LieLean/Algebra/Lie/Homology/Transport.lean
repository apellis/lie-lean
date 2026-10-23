/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.Weights

/-!
# Transport of Lie algebra homology along a change of Lie algebra

Let `e : L → L'` be a morphism of Lie algebras and `g : M → M'` a linear map from an `L`-module
to an `L'`-module with `g [x, m] = [e x, g m]`. Then `⋀e ⊗ g : ⋀L ⊗ M → ⋀L' ⊗ M'`
(`LieModule.ChevalleyEilenberg.chainMap`) preserves the degrees and commutes with the
Chevalley–Eilenberg differentials.

If `e` and `g` are bijective and reverse the actions of a Cartan part `H`
(`e (D a x) = -D' a (e x)`, `g (φ a m) = -φ' a (g m)`), then `⋀e ⊗ g` identifies the weight-`ν`
cycles and boundaries of `M` with the weight-`(-ν)` cycles and boundaries of `M'`, so
`dim H_k(L, M)_ν = dim H_k(L', M')_{-ν}`
(`LieModule.ChevalleyEilenberg.DerivAction.finrank_homologyWeightSpace_of_neg`). This is used to
pass between `𝔫₊`-homology of a module twisted by the Chevalley involution and `𝔫₋`-homology.

## Main definitions

* `LieModule.ChevalleyEilenberg.chainMap`: the map `⋀e ⊗ g` on chains.

## Main results

* `LieModule.ChevalleyEilenberg.chainMap_diff`: `⋀e ⊗ g` commutes with the differentials.
* `LieModule.ChevalleyEilenberg.DerivAction.finrank_homologyWeightSpace_of_neg`: the dimension
  identity above.
-/

open Module TensorProduct ExteriorAlgebra

noncomputable section

namespace LieModule.ChevalleyEilenberg

section Chains

variable {R L L' M M' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L'] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

/-- The map `⋀e ⊗ g : ⋀L ⊗ M → ⋀L' ⊗ M'`. -/
def chainMap (e : L →ₗ[R] L') (g : M →ₗ[R] M') :
    ExteriorAlgebra R L ⊗[R] M →ₗ[R] ExteriorAlgebra R L' ⊗[R] M' :=
  TensorProduct.map (ExteriorAlgebra.map e).toLinearMap g

variable (e : L →ₗ[R] L') (g : M →ₗ[R] M')

@[simp] lemma chainMap_tmul (ω : ExteriorAlgebra R L) (m : M) :
    chainMap e g (ω ⊗ₜ m) = ExteriorAlgebra.map e ω ⊗ₜ g m := rfl

lemma chainMap_wedge (y : L) (c : ExteriorAlgebra R L ⊗[R] M) :
    chainMap e g (wedge R L M y c) = wedge R L' M' (e y) (chainMap e g c) := by
  induction c with
  | tmul ω m => simp [map_mul, ExteriorAlgebra.map_apply_ι]
  | add c c' hc hc' => simp only [map_add, hc, hc']

lemma chainMap_derivExt {D : L →ₗ[R] L} {φ : M →ₗ[R] M} {D' : L' →ₗ[R] L'} {φ' : M' →ₗ[R] M'}
    (hD : ∀ x, e (D x) = D' (e x)) (hφ : ∀ m, g (φ m) = φ' (g m))
    (c : ExteriorAlgebra R L ⊗[R] M) :
    chainMap e g (derivExt D φ c) = derivExt D' φ' (chainMap e g c) := by
  induction c using induction with
  | one m => simp [hφ]
  | wedge y c hc =>
    rw [derivExt_wedge, map_add, chainMap_wedge, chainMap_wedge, hc, chainMap_wedge,
      derivExt_wedge, hD]
  | add c c' hc hc' => simp only [map_add, hc, hc']

lemma chainMap_mem_chainsIn {k : ℕ} {c : ExteriorAlgebra R L ⊗[R] M}
    (hc : c ∈ chainsIn R L M k) : chainMap e g c ∈ chainsIn R L' M' k := by
  induction k generalizing c with
  | zero =>
    refine chainsIn_zero_le (S := (chainsIn R L' M' 0).comap (chainMap e g)) (fun m ↦ ?_) hc
    rw [Submodule.mem_comap, chainMap_tmul, map_one]
    exact one_tmul_mem_chainsIn _
  | succ k ih =>
    refine chainsIn_succ_le (S := (chainsIn R L' M' (k + 1)).comap (chainMap e g))
      (fun y c hc ↦ ?_) hc
    rw [Submodule.mem_comap, chainMap_wedge]
    exact wedge_mem_chainsIn _ (ih hc)

variable [LieRingModule L M] [LieModule R L M] [LieRingModule L' M'] [LieModule R L' M']

variable (e : L →ₗ⁅R⁆ L') {g} (hg : ∀ (x : L) (m : M), g ⁅x, m⁆ = ⁅e x, g m⁆)
include hg

lemma chainMap_lieAction (x : L) (c : ExteriorAlgebra R L ⊗[R] M) :
    chainMap (e : L →ₗ[R] L') g (lieAction R L M x c) =
      lieAction R L' M' (e x) (chainMap (e : L →ₗ[R] L') g c) :=
  chainMap_derivExt (e : L →ₗ[R] L') g (fun y ↦ by simp) (fun m ↦ by simp [hg]) c

/-- `⋀e ⊗ g` commutes with the Chevalley–Eilenberg differentials. -/
theorem chainMap_diff (c : ExteriorAlgebra R L ⊗[R] M) :
    chainMap (e : L →ₗ[R] L') g (diff R L M c) = diff R L' M' (chainMap (e : L →ₗ[R] L') g c) := by
  induction c using induction with
  | one m => simp
  | wedge y c hc =>
    rw [diff_wedge, map_sub, map_neg, chainMap_lieAction e hg, chainMap_wedge, hc,
      chainMap_wedge, diff_wedge]
    rfl
  | add c c' hc hc' => simp only [map_add, hc, hc']

lemma chainMap_mem_cycles {k : ℕ} {c : ExteriorAlgebra R L ⊗[R] M}
    (hc : c ∈ cycles R L M k) : chainMap (e : L →ₗ[R] L') g c ∈ cycles R L' M' k :=
  ⟨chainMap_mem_chainsIn _ g hc.1, LinearMap.mem_ker.mpr (by
    rw [← chainMap_diff e hg, LinearMap.mem_ker.mp hc.2, map_zero])⟩

lemma chainMap_mem_boundaries {k : ℕ} {c : ExteriorAlgebra R L ⊗[R] M}
    (hc : c ∈ boundaries R L M k) : chainMap (e : L →ₗ[R] L') g c ∈ boundaries R L' M' k := by
  obtain ⟨c, hc, rfl⟩ := hc
  exact ⟨_, chainMap_mem_chainsIn _ g hc, (chainMap_diff e hg c).symm⟩

end Chains

namespace DerivAction

variable {K H L L' M M' : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L]
  [LieAlgebra K L] [LieRing L'] [LieAlgebra K L'] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] [AddCommGroup M'] [Module K M'] [LieRingModule L' M']
  [LieModule K L' M'] {ρ : DerivAction K H L M} {ρ' : DerivAction K H L' M'}

omit [LieModule K L M] [LieModule K L' M'] in
lemma chainMap_mem_chainWeightSpace {e : L →ₗ[K] L'} {g : M →ₗ[K] M'}
    (hD : ∀ a x, e (ρ.D a x) = -ρ'.D a (e x)) (hφ : ∀ a m, g (ρ.φ a m) = -ρ'.φ a (g m))
    {ν : Dual K H} {c : ExteriorAlgebra K L ⊗[K] M} (hc : c ∈ ρ.chainWeightSpace ν) :
    chainMap e g c ∈ ρ'.chainWeightSpace (-ν) := by
  refine mem_chainWeightSpace.mpr fun a ↦ ?_
  have h := chainMap_derivExt e g (D' := -ρ'.D a) (φ' := -ρ'.φ a) (hD a) (hφ a) c
  have hneg : derivExt (-ρ'.D a) (-ρ'.φ a) = -derivExt (ρ'.D a) (ρ'.φ a) := by
    have h1 := derivExt_smul (ρ'.D a) (ρ'.φ a) (-1 : K)
    simp only [neg_smul, one_smul] at h1
    exact h1.trans (LinearMap.ext fun x ↦ by simp)
  rw [← θ_apply, mem_chainWeightSpace.mp hc a, map_smul, hneg, LinearMap.neg_apply,
    ← θ_apply] at h
  rw [LinearMap.neg_apply, ← neg_neg (ρ'.θ a _), ← h]
  exact (neg_smul (ν a) _).symm

variable (e : L ≃ₗ⁅K⁆ L') (g : M ≃ₗ[K] M') (hg : ∀ (x : L) (m : M), g ⁅x, m⁆ = ⁅e x, g m⁆)
  (hD : ∀ a x, e (ρ.D a x) = -ρ'.D a (e x)) (hφ : ∀ a m, g (ρ.φ a m) = -ρ'.φ a (g m))

/-- `⋀e ⊗ g` as a linear equivalence. -/
def chainEquiv : (ExteriorAlgebra K L ⊗[K] M) ≃ₗ[K] (ExteriorAlgebra K L' ⊗[K] M') :=
  LinearEquiv.ofLinearMap (chainMap (e : L →ₗ[K] L') (g : M →ₗ[K] M'))
    (chainMap (e.symm : L' →ₗ[K] L) (g.symm : M' →ₗ[K] M))
    (TensorProduct.ext' fun ω m ↦ by
      have h : (e : L →ₗ[K] L') ∘ₗ (e.symm : L' →ₗ[K] L) = LinearMap.id :=
        LinearMap.ext fun x ↦ e.apply_symm_apply x
      change ExteriorAlgebra.map (e : L →ₗ[K] L') (ExteriorAlgebra.map (e.symm : L' →ₗ[K] L) ω)
        ⊗ₜ g (g.symm m) = ω ⊗ₜ m
      rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h, ExteriorAlgebra.map_id,
        AlgHom.id_apply, LinearEquiv.apply_symm_apply])
    (TensorProduct.ext' fun ω m ↦ by
      have h : (e.symm : L' →ₗ[K] L) ∘ₗ (e : L →ₗ[K] L') = LinearMap.id :=
        LinearMap.ext fun x ↦ e.symm_apply_apply x
      change ExteriorAlgebra.map (e.symm : L' →ₗ[K] L) (ExteriorAlgebra.map (e : L →ₗ[K] L') ω)
        ⊗ₜ g.symm (g m) = ω ⊗ₜ m
      rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h, ExteriorAlgebra.map_id,
        AlgHom.id_apply, LinearEquiv.symm_apply_apply])

omit [LieRingModule L M] [LieModule K L M] [LieRingModule L' M'] [LieModule K L' M'] in
@[simp] lemma chainEquiv_apply (c : ExteriorAlgebra K L ⊗[K] M) :
    chainEquiv e g c = chainMap (e : L →ₗ[K] L') (g : M →ₗ[K] M') c := rfl

omit [LieRingModule L M] [LieModule K L M] [LieRingModule L' M'] [LieModule K L' M'] in
@[simp] lemma chainEquiv_symm_apply (c : ExteriorAlgebra K L' ⊗[K] M') :
    (chainEquiv e g).symm c = chainMap (e.symm : L' →ₗ[K] L) (g.symm : M' →ₗ[K] M) c := rfl

omit [LieModule K L M] [LieModule K L' M'] in
include hD in
lemma symm_hD : ∀ a x, e.symm (ρ'.D a x) = -ρ.D a (e.symm x) := fun a x ↦ by
  have h := hD a (e.symm x)
  rw [LieEquiv.apply_symm_apply] at h
  rw [← neg_neg (ρ'.D a x), ← h, map_neg, LieEquiv.symm_apply_apply]

omit [LieModule K L M] [LieModule K L' M'] in
include hφ in
lemma symm_hφ : ∀ a m, g.symm (ρ'.φ a m) = -ρ.φ a (g.symm m) := fun a m ↦ by
  have h := hφ a (g.symm m)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [← neg_neg (ρ'.φ a m), ← h, map_neg, LinearEquiv.symm_apply_apply]

include hD hφ in
omit [LieModule K L M] [LieModule K L' M'] in
/-- `⋀e ⊗ g` identifies the chains of degree `k` and weight `ν` with those of weight `-ν`. -/
lemma map_chainEquiv_chainsIn_inf (k : ℕ) (ν : Dual K H) :
    (chainsIn K L M k ⊓ ρ.chainWeightSpace ν).map (chainEquiv e g).toLinearMap =
      chainsIn K L' M' k ⊓ ρ'.chainWeightSpace (-ν) := by
  refine le_antisymm ?_ fun c hc ↦
    ⟨(chainEquiv e g).symm c, ?_, (chainEquiv e g).apply_symm_apply c⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact ⟨chainMap_mem_chainsIn _ _ hc.1, chainMap_mem_chainWeightSpace hD hφ hc.2⟩
  · have h := chainMap_mem_chainWeightSpace (symm_hD e hD) (symm_hφ g hφ) hc.2
    rw [neg_neg] at h
    exact ⟨chainMap_mem_chainsIn _ _ hc.1, h⟩

include hg hD hφ in
/-- `⋀e ⊗ g` identifies the cycles of degree `k` and weight `ν` with those of weight `-ν`. -/
lemma map_chainEquiv_cycles_inf (k : ℕ) (ν : Dual K H) :
    (cycles K L M k ⊓ ρ.chainWeightSpace ν).map (chainEquiv e g).toLinearMap =
      cycles K L' M' k ⊓ ρ'.chainWeightSpace (-ν) := by
  have hg' : ∀ (x : L') (m : M'), g.symm ⁅x, m⁆ = ⁅e.symm x, g.symm m⁆ := fun x m ↦ by
    apply g.injective
    rw [hg, LinearEquiv.apply_symm_apply, LieEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  refine le_antisymm ?_ fun c hc ↦
    ⟨(chainEquiv e g).symm c, ?_, (chainEquiv e g).apply_symm_apply c⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact ⟨chainMap_mem_cycles e.toLieHom hg hc.1, chainMap_mem_chainWeightSpace hD hφ hc.2⟩
  · have h := chainMap_mem_chainWeightSpace (symm_hD e hD) (symm_hφ g hφ) hc.2
    rw [neg_neg] at h
    exact ⟨chainMap_mem_cycles e.symm.toLieHom hg' hc.1, h⟩

include hg hD hφ in
/-- `⋀e ⊗ g` identifies the boundaries of degree `k` and weight `ν` with those of weight `-ν`. -/
lemma map_chainEquiv_boundaries_inf (k : ℕ) (ν : Dual K H) :
    (boundaries K L M k ⊓ ρ.chainWeightSpace ν).map (chainEquiv e g).toLinearMap =
      boundaries K L' M' k ⊓ ρ'.chainWeightSpace (-ν) := by
  have hg' : ∀ (x : L') (m : M'), g.symm ⁅x, m⁆ = ⁅e.symm x, g.symm m⁆ := fun x m ↦ by
    apply g.injective
    rw [hg, LinearEquiv.apply_symm_apply, LieEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  refine le_antisymm ?_ fun c hc ↦
    ⟨(chainEquiv e g).symm c, ?_, (chainEquiv e g).apply_symm_apply c⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact ⟨chainMap_mem_boundaries e.toLieHom hg hc.1, chainMap_mem_chainWeightSpace hD hφ hc.2⟩
  · have h := chainMap_mem_chainWeightSpace (symm_hD e hD) (symm_hφ g hφ) hc.2
    rw [neg_neg] at h
    exact ⟨chainMap_mem_boundaries e.symm.toLieHom hg' hc.1, h⟩

include hg hD hφ in
/-- **`dim H_k(L, M)_ν = dim H_k(L', M')_{-ν}`** when `e : L ≃ L'` and `g : M ≃ M'` are
compatible and reverse the actions of `H`. -/
theorem finrank_homologyWeightSpace_of_neg (k : ℕ) (ν : Dual K H)
    [FiniteDimensional K ↥(cycles K L' M' k ⊓ ρ'.chainWeightSpace (-ν))] :
    finrank K (ρ.homologyWeightSpace k ν) = finrank K (ρ'.homologyWeightSpace k (-ν)) := by
  have hZ := map_chainEquiv_cycles_inf e g hg hD hφ k ν
  have hB := map_chainEquiv_boundaries_inf e g hg hD hφ k ν
  let eZ := ((chainEquiv e g).submoduleMap (cycles K L M k ⊓ ρ.chainWeightSpace ν)).trans
    (LinearEquiv.ofEq _ _ hZ)
  have : FiniteDimensional K ↥(cycles K L M k ⊓ ρ.chainWeightSpace ν) :=
    Module.Finite.equiv eZ.symm
  have h₁ := ρ.finrank_homologyWeightSpace_add k ν
  have h₂ := ρ'.finrank_homologyWeightSpace_add k (-ν)
  have h₃ := LinearEquiv.finrank_map_eq (chainEquiv e g) (cycles K L M k ⊓ ρ.chainWeightSpace ν)
  have h₄ := LinearEquiv.finrank_map_eq (chainEquiv e g)
    (boundaries K L M k ⊓ ρ.chainWeightSpace ν)
  rw [hZ] at h₃
  rw [hB] at h₄
  omega

end DerivAction

end LieModule.ChevalleyEilenberg
