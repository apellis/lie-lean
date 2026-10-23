/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.CochainWeights
import LieLean.Algebra.Lie.Homology.Vanishing
import Mathlib.Tactic.LinearCombination

/-!
# Vanishing of weight cohomology by duality with homology

Let `L` be a Lie algebra over a field `K`, let `X` and `N` be `L`-modules with compatible actions
of a vector space `H` (`LieModule.ChevalleyEilenberg.DerivAction`, the same action on `L`), and
let `B : N × X → K` be an invariant pairing, `B(x n, m) = -B(n, x m)` and
`B(a n, m) = -B(n, a m)` for `a ∈ H`, which identifies `N` with the functionals on `X` that are
sums of weight vectors (`B` injective, and every weight functional on `X` is some `B(n, ·)`). The
main example is `N = M^∨` the restricted dual of a module `X = M` in the category `𝒪`.

If `L` and `X` are sums of weight spaces and the homology `H_{k+1}(L, X)` vanishes, then every
`(k+1)`-cocycle of weight `μ` with values in `N` is the coboundary of a `k`-cochain of weight
`μ`, so `H^{k+1}(L, N)_μ = 0`
(`LieModule.ChevalleyEilenberg.DerivAction.exists_δ_eq_of_subsingleton_homology`).

The proof is the transpose argument: a cocycle `f` gives the functional `f̂(c ⊗ m) = B(f c, m)`
on the chains, which vanishes on the cycles because they are boundaries; it therefore factors
through the differential, and the factorization can be chosen of weight `-μ`. A weight functional
on `⋀ᵏL ⊗ X` comes from a `k`-cochain with values in `N`, which is the required primitive. This
is the duality step behind Humphreys, *Representations of semisimple Lie algebras in the BGG
category 𝒪*, GSM 94, Prop. 6.15 (b); the argument here is our own.

## Main definitions

* `Module.End.weightProj`: the projection onto a weight space along the other weight spaces.

## Main results

* `LieModule.ChevalleyEilenberg.DerivAction.θ_tmul`:
  `θ(a)(c ⊗ m) = D̃(a) c ⊗ m + c ⊗ φ(a) m`.
* `LieModule.ChevalleyEilenberg.DerivAction.exists_δ_eq_of_subsingleton_homology`: the duality
  theorem above.
-/

open Module TensorProduct ExteriorAlgebra

noncomputable section

namespace Module.End

variable {K H Y : Type*} [Field K] [AddCommGroup H] [Module K H] [AddCommGroup Y] [Module K Y]
  {T : H →ₗ[K] Module.End K Y}

/-- If `Y` is the sum of its weight spaces, each weight space has the sum of the others as a
complement. -/
lemma isCompl_weightSpaceOf (hT : ⨆ ν, weightSpaceOf T ν = ⊤) (μ : Dual K H) :
    IsCompl (weightSpaceOf T μ) (⨆ ν, ⨆ (_ : ν ≠ μ), weightSpaceOf T ν) :=
  ⟨iSupIndep_weightSpaceOf T μ,
    codisjoint_iff.mpr ((iSup_split_single (fun ν ↦ weightSpaceOf T ν) μ).symm.trans hT)⟩

/-- The projection of `Y = ⊕_ν Y_ν` onto the weight space `Y_μ`. -/
def weightProj (hT : ⨆ ν, weightSpaceOf T ν = ⊤) (μ : Dual K H) : Module.End K Y :=
  (weightSpaceOf T μ).projection _ (isCompl_weightSpaceOf hT μ)

variable (hT : ⨆ ν, weightSpaceOf T ν = ⊤)
include hT

lemma weightProj_mem (μ : Dual K H) (y : Y) : weightProj hT μ y ∈ weightSpaceOf T μ :=
  Submodule.projection_apply_mem _ y

lemma weightProj_of_mem {μ : Dual K H} {y : Y} (hy : y ∈ weightSpaceOf T μ) :
    weightProj hT μ y = y :=
  Submodule.projection_apply_of_mem_left _ hy

lemma weightProj_of_mem_ne {μ ν : Dual K H} (h : ν ≠ μ) {y : Y} (hy : y ∈ weightSpaceOf T ν) :
    weightProj hT μ y = 0 :=
  (Submodule.projection_apply_eq_zero_iff _).mpr
    (Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem h hy))

/-- The projection onto a weight space commutes with the action. -/
lemma weightProj_comm (μ : Dual K H) (a : H) (y : Y) :
    weightProj hT μ (T a y) = T a (weightProj hT μ y) := by
  have hy : y ∈ ⨆ ν, weightSpaceOf T ν := hT ▸ Submodule.mem_top
  induction hy using Submodule.iSup_induction' with
  | mem ν y hy =>
    rw [hy a, map_smul]
    by_cases h : ν = μ
    · subst h
      rw [weightProj_of_mem hT hy, hy a]
    · rw [weightProj_of_mem_ne hT h hy, map_zero, smul_zero]
  | zero => simp
  | add y y' _ _ h h' => simp only [map_add, h, h']

end Module.End

/-- Over a field, a linear functional vanishing on the kernel of `D` factors through `D`. -/
lemma LinearMap.exists_comp_eq_of_ker_le {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (D : V →ₗ[K] W) (F : V →ₗ[K] K)
    (h : LinearMap.ker D ≤ LinearMap.ker F) : ∃ ψ : W →ₗ[K] K, ψ ∘ₗ D = F := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend
    ((LinearMap.ker D).liftQ F h ∘ₗ D.quotKerEquivRange.symm.toLinearMap)
  refine ⟨ψ, LinearMap.ext fun x ↦ ?_⟩
  simpa using LinearMap.congr_fun hψ ⟨D x, LinearMap.mem_range_self D x⟩

namespace LieModule.ChevalleyEilenberg.DerivAction

variable {K H L X N : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  [AddCommGroup X] [Module K X] [LieRingModule L X] (ρ : DerivAction K H L X)
  [AddCommGroup N] [Module K N] [LieRingModule L N] (ρN : DerivAction K H L N)

/-- `θ(a)(c ⊗ m) = D̃(a) c ⊗ m + c ⊗ φ(a) m`. -/
lemma θ_tmul (a : H) (c : ExteriorAlgebra K L) (m : X) :
    ρ.θ a (c ⊗ₜ m) = extDeriv (ρ.D a) c ⊗ₜ m + c ⊗ₜ ρ.φ a m := by
  induction c using exterior_induction with
  | algebraMap r =>
    have e : ∀ m' : X, algebraMap K (ExteriorAlgebra K L) r ⊗ₜ[K] m' =
        r • ((1 : ExteriorAlgebra K L) ⊗ₜ m') := fun m' ↦ by
      rw [Algebra.algebraMap_eq_smul_one, smul_tmul']
    rw [e, e, map_smul, θ_one_tmul, extDeriv_algebraMap, zero_tmul, zero_add]
  | add c c' hc hc' => simp only [add_tmul, map_add, hc, hc']; abel
  | ι_mul y c hc =>
    rw [← wedge_tmul, θ_wedge, hc, map_add, wedge_tmul, wedge_tmul, wedge_tmul, extDeriv_ι_mul,
      add_tmul, add_assoc]

/-- For a cochain `f` of weight `μ`, the functional `f̂(c ⊗ m) = B(f c, m)` on `⋀ᵏL ⊗ X` has
weight `-μ`. -/
lemma cochainPair_θ {B : N →ₗ[K] X →ₗ[K] K} (hD : ∀ a, ρN.D a = ρ.D a)
    (hBφ : ∀ (a : H) (n : N) (m : X), B (ρN.φ a n) m = -B n (ρ.φ a m)) {k : ℕ}
    {μ : Dual K H} {f : Cochains K L N k} (hf : f ∈ ρN.cochainWeightSpace k μ) (a : H)
    {t : ExteriorAlgebra K L ⊗[K] X} (ht : t ∈ chainsIn K L X k) :
    cochainPair B (f ∘ₗ degProj K L k) (ρ.θ a t) =
      -μ a * cochainPair B (f ∘ₗ degProj K L k) t := by
  obtain ⟨s, rfl⟩ := ht
  induction s with
  | tmul ω m =>
    have h := LinearMap.congr_fun (hf a) ω
    rw [coActDeg_apply, hD, LinearMap.smul_apply] at h
    have h' : f (extDerivDeg (ρ.D a) k ω) = ρN.φ a (f ω) - μ a • f ω := by
      rw [← h, sub_sub_cancel]
    have e : degProj K L k (extDeriv (ρ.D a) (ω : ExteriorAlgebra K L)) =
        extDerivDeg (ρ.D a) k ω := by
      rw [← coe_extDerivDeg, degProj_subtype]
    rw [incl_tmul, θ_tmul, map_add, cochainPair_tmul, cochainPair_tmul, cochainPair_tmul]
    simp only [LinearMap.comp_apply, e, degProj_subtype, h', map_sub, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply, hBφ, smul_eq_mul]
    ring
  | add s s' hs hs' => simp only [map_add, hs, hs', mul_add]

omit [LieRingModule L N] in
/-- A functional of weight `γ` on `⋀L ⊗ X`, restricted to `c ⊗ X`, is of the form `B(n, ·)`. -/
lemma comp_mk_mem_range {B : N →ₗ[K] X →ₗ[K] K}
    (hrep : ∀ (γ : Dual K H) (ψ : X →ₗ[K] K), (∀ a m, ψ (ρ.φ a m) = γ a * ψ m) →
      ψ ∈ LinearMap.range B)
    (hL : ⨆ γ, Module.End.weightSpaceOf ρ.D γ = ⊤) (c : ExteriorAlgebra K L) :
    ∀ (χ : ExteriorAlgebra K L ⊗[K] X →ₗ[K] K) (γ : Dual K H),
      (∀ a t, χ (ρ.θ a t) = γ a * χ t) →
        χ ∘ₗ TensorProduct.mk K _ X c ∈ LinearMap.range B := by
  induction c using exterior_induction with
  | algebraMap r =>
    intro χ γ hχ
    have e : χ ∘ₗ TensorProduct.mk K _ X (algebraMap K _ r) =
        r • (χ ∘ₗ TensorProduct.mk K _ X 1) := by
      ext m
      rw [LinearMap.comp_apply, TensorProduct.mk_apply, Algebra.algebraMap_eq_smul_one,
        ← smul_tmul', map_smul, LinearMap.smul_apply, LinearMap.comp_apply,
        TensorProduct.mk_apply]
    rw [e]
    refine Submodule.smul_mem _ r (hrep γ _ fun a m ↦ ?_)
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply]
    rw [← θ_one_tmul, hχ]
  | add c c' hc hc' =>
    intro χ γ hχ
    rw [map_add, LinearMap.comp_add]
    exact add_mem (hc χ γ hχ) (hc' χ γ hχ)
  | ι_mul y c hc =>
    intro χ γ hχ
    have hy : y ∈ ⨆ β, Module.End.weightSpaceOf ρ.D β := hL ▸ Submodule.mem_top
    induction hy using Submodule.iSup_induction' with
    | mem β y hy =>
      have e : χ ∘ₗ TensorProduct.mk K _ X (ι K y * c) =
          (χ ∘ₗ wedge K L X y) ∘ₗ TensorProduct.mk K _ X c := by
        ext m
        rfl
      rw [e]
      refine hc _ (γ - β) fun a t ↦ ?_
      have h := ρ.θ_wedge a y t
      rw [Module.End.mem_weightSpaceOf.mp hy a, map_smul, LinearMap.smul_apply] at h
      simp only [LinearMap.comp_apply]
      rw [eq_sub_of_add_eq' h.symm, map_sub, hχ, map_smul, smul_eq_mul, LinearMap.sub_apply]
      ring
    | zero =>
      rw [map_zero, zero_mul, map_zero, LinearMap.comp_zero]
      exact zero_mem _
    | add y y' _ _ h h' =>
      rw [map_add, add_mul, map_add, LinearMap.comp_add]
      exact add_mem h h'

variable [LieModule K L X] [LieModule K L N]

omit [LieModule K L X] [LieModule K L N] in
/-- A functional `ψ` of weight `-μ` on `⋀L ⊗ X` is, on the chains of degree `k`, the pairing
with a `k`-cochain of weight `μ` with values in `N`. -/
lemma exists_cochain_of_weight {B : N →ₗ[K] X →ₗ[K] K} (hD : ∀ a, ρN.D a = ρ.D a)
    (hBφ : ∀ (a : H) (n : N) (m : X), B (ρN.φ a n) m = -B n (ρ.φ a m))
    (hinj : Function.Injective B)
    (hrep : ∀ (γ : Dual K H) (ψ : X →ₗ[K] K), (∀ a m, ψ (ρ.φ a m) = γ a * ψ m) →
      ψ ∈ LinearMap.range B)
    (hL : ⨆ γ, Module.End.weightSpaceOf ρ.D γ = ⊤) {k : ℕ} {μ : Dual K H}
    (ψ : ExteriorAlgebra K L ⊗[K] X →ₗ[K] K) (hψθ : ∀ a t, ψ (ρ.θ a t) = -μ a * ψ t) :
    ∃ g ∈ ρN.cochainWeightSpace k μ,
      ∀ t ∈ chainsIn K L X k, cochainPair B (g ∘ₗ degProj K L k) t = ψ t := by
  have hΦ : ∀ ω : ⋀[K]^k L, ψ ∘ₗ TensorProduct.mk K _ X (ω : ExteriorAlgebra K L) ∈
      LinearMap.range B := fun ω ↦ comp_mk_mem_range ρ hrep hL _ ψ (-μ) hψθ
  obtain ⟨g, hg⟩ : ∃ g : Cochains K L N k,
      ∀ ω m, B (g ω) m = ψ ((ω : ExteriorAlgebra K L) ⊗ₜ m) :=
    ⟨(LinearEquiv.ofInjective B hinj).symm.toLinearMap ∘ₗ
        (((LinearMap.llcomp K X _ K ψ) ∘ₗ TensorProduct.mk K _ X ∘ₗ
          (⋀[K]^k L).subtype).codRestrict (LinearMap.range B) hΦ),
      fun ω m ↦ LinearMap.congr_fun (LinearEquiv.ofInjective_symm_apply (f := B) (h := hinj)
        (⟨_, hΦ ω⟩ : LinearMap.range B)) m⟩
  refine ⟨g, fun a ↦ ?_, ?_⟩
  · refine LinearMap.ext fun ω ↦ hinj (LinearMap.ext fun m ↦ ?_)
    have h := hψθ a ((ω : ExteriorAlgebra K L) ⊗ₜ m)
    rw [θ_tmul, map_add] at h
    rw [coActDeg_apply, LinearMap.smul_apply, map_sub, LinearMap.sub_apply, hBφ, hD, map_smul,
      LinearMap.smul_apply, hg, hg, hg, smul_eq_mul, coe_extDerivDeg]
    linear_combination -h
  · rintro t ⟨s, rfl⟩
    induction s with
    | tmul ω m => rw [incl_tmul, cochainPair_tmul, LinearMap.comp_apply, degProj_subtype, hg]
    | add s s' h h' => rw [map_add, map_add, map_add, h, h']

/-- **Vanishing of weight cohomology by duality.** Let `B : N × X → K` be an invariant pairing
(for `L` and for `H`) identifying `N` with the weight functionals on `X`, with `L` and `X` sums
of weight spaces. If `H_{k+1}(L, X) = 0`, then every `(k+1)`-cocycle of weight `μ` with values in
`N` is the coboundary of a `k`-cochain of weight `μ`; that is, `H^{k+1}(L, N)_μ = 0`. -/
theorem exists_δ_eq_of_subsingleton_homology {B : N →ₗ[K] X →ₗ[K] K}
    (hD : ∀ a, ρN.D a = ρ.D a) (hB : ∀ (x : L) (n : N) (m : X), B ⁅x, n⁆ m = -B n ⁅x, m⁆)
    (hBφ : ∀ (a : H) (n : N) (m : X), B (ρN.φ a n) m = -B n (ρ.φ a m))
    (hinj : Function.Injective B)
    (hrep : ∀ (γ : Dual K H) (ψ : X →ₗ[K] K), (∀ a m, ψ (ρ.φ a m) = γ a * ψ m) →
      ψ ∈ LinearMap.range B)
    (hL : ⨆ γ, Module.End.weightSpaceOf ρ.D γ = ⊤)
    (hX : ⨆ ν, Module.End.weightSpaceOf ρ.φ ν = ⊤)
    {k : ℕ} (hk : Subsingleton (homology K L X (k + 1)))
    {μ : Dual K H} {f : Cochains K L N (k + 1)} (hf : f ∈ ρN.cochainWeightSpace (k + 1) μ)
    (hδ : δ K L N (k + 1) f = 0) :
    ∃ g ∈ ρN.cochainWeightSpace k μ, δ K L N k g = f := by
  obtain ⟨F, hF⟩ : ∃ F, F = cochainPair B (f ∘ₗ degProj K L (k + 1)) := ⟨_, rfl⟩
  have hFθ : ∀ (a : H) {t}, t ∈ chainsIn K L X (k + 1) → F (ρ.θ a t) = -μ a * F t := by
    intro a t ht
    rw [hF]
    exact cochainPair_θ ρ ρN hD hBφ hf a ht
  -- `F` vanishes on the cycles, which are boundaries
  have hcyc : ∀ t ∈ chainsIn K L X (k + 1), diff K L X t = 0 → F t = 0 := by
    intro t ht ht0
    have hb : t ∈ boundaries K L X (k + 1) := by
      rw [(subsingleton_homology_iff K L X (k + 1)).mp hk]
      exact ⟨ht, LinearMap.mem_ker.mpr ht0⟩
    obtain ⟨s, ⟨s, rfl⟩, rfl⟩ := hb
    clear ht ht0
    rw [hF, ← cochainPair_cochainDiff hB]
    induction s with
    | tmul ω m =>
      have h := LinearMap.congr_fun hδ ω
      rw [δ_apply, LinearMap.zero_apply] at h
      rw [incl_tmul, cochainPair_tmul, h, map_zero, LinearMap.zero_apply]
    | add s s' hs hs' => simp only [map_add, hs, hs', add_zero]
  -- so `F` factors through the differential on the chains of degree `k + 1`
  obtain ⟨ψ₁, hψ₁d⟩ : ∃ ψ₁ : ExteriorAlgebra K L ⊗[K] X →ₗ[K] K,
      ∀ t ∈ chainsIn K L X (k + 1), ψ₁ (diff K L X t) = F t := by
    obtain ⟨ψ₁, hψ₁⟩ := LinearMap.exists_comp_eq_of_ker_le
      ((diff K L X).domRestrict (chainsIn K L X (k + 1))) (F.domRestrict (chainsIn K L X (k + 1)))
      fun t ht ↦ LinearMap.mem_ker.mpr (hcyc t t.2 (LinearMap.mem_ker.mp ht))
    exact ⟨ψ₁, fun t ht ↦ LinearMap.congr_fun hψ₁ ⟨t, ht⟩⟩
  -- the projection onto the weight space of weight `-μ`
  obtain ⟨Pr, hPmem, hPself, hPne, hPcomm⟩ : ∃ Pr : Module.End K (ExteriorAlgebra K L ⊗[K] X),
      (∀ t, Pr t ∈ ρ.chainWeightSpace (-μ)) ∧ (∀ t ∈ ρ.chainWeightSpace (-μ), Pr t = t) ∧
      (∀ ν ≠ -μ, ∀ t ∈ ρ.chainWeightSpace ν, Pr t = 0) ∧
      (∀ a t, Pr (ρ.θ a t) = ρ.θ a (Pr t)) :=
    have hT := ρ.iSup_chainWeightSpace hL hX
    ⟨Module.End.weightProj hT (-μ), Module.End.weightProj_mem hT _,
      fun _ ↦ Module.End.weightProj_of_mem hT, fun _ h _ ↦ Module.End.weightProj_of_mem_ne hT h,
      Module.End.weightProj_comm hT _⟩
  -- a factorization of weight `-μ`
  obtain ⟨ψ, hψθ, hψd⟩ : ∃ ψ : ExteriorAlgebra K L ⊗[K] X →ₗ[K] K,
      (∀ a t, ψ (ρ.θ a t) = -μ a * ψ t) ∧
      ∀ t ∈ chainsIn K L X (k + 1), ψ (diff K L X t) = F t := by
    refine ⟨ψ₁ ∘ₗ Pr, fun a t ↦ ?_, fun t ht ↦ ?_⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hPcomm,
        mem_chainWeightSpace.mp (hPmem t) a, map_smul, smul_eq_mul, LinearMap.neg_apply]
    · rw [← ρ.iSup_inf_chainWeightSpace hL hX (chainsIn K L X (k + 1))
        (fun a _ hc ↦ ρ.θ_mem_chainsIn a hc)] at ht
      induction ht using Submodule.iSup_induction' with
      | mem ν t ht =>
        obtain ⟨htc, htw⟩ := ht
        have hdw := ρ.diff_mem_chainWeightSpace htw
        by_cases hν : ν = -μ
        · subst hν
          rw [LinearMap.comp_apply, hPself _ hdw, hψ₁d t htc]
        · rw [LinearMap.comp_apply, hPne ν hν _ hdw, map_zero]
          obtain ⟨a, ha⟩ : ∃ a, ν a ≠ -μ a := by
            by_contra h
            push Not at h
            exact hν (LinearMap.ext fun a ↦ (h a).trans (LinearMap.neg_apply μ a).symm)
          have h1 := hFθ a htc
          rw [mem_chainWeightSpace.mp htw a, map_smul, smul_eq_mul] at h1
          have h2 : (ν a - -μ a) * F t = 0 := by rw [sub_mul, h1, sub_self]
          exact ((mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)).symm
      | zero => simp only [map_zero]
      | add t t' _ _ h h' => rw [map_add, map_add, map_add, h, h']
  -- the primitive
  obtain ⟨g, hgw, hpair⟩ := exists_cochain_of_weight ρ ρN hD hBφ hinj hrep hL (k := k) ψ hψθ
  refine ⟨g, hgw, LinearMap.ext fun ω ↦ hinj (LinearMap.ext fun m ↦ ?_)⟩
  have hω : (ω : ExteriorAlgebra K L) ⊗ₜ m ∈ chainsIn K L X (k + 1) := tmul_mem_chainsIn ω.2 m
  rw [δ_apply]
  change cochainPair B (cochainDiff K L N (g ∘ₗ degProj K L k)) ((ω : ExteriorAlgebra K L) ⊗ₜ m)
    = _
  rw [cochainPair_cochainDiff hB, hpair _ (diff_mem_chainsIn hω), hψd _ hω, hF,
    cochainPair_tmul, LinearMap.comp_apply, degProj_subtype]

end LieModule.ChevalleyEilenberg.DerivAction
