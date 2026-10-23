/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.CochainDualityFinrank
import LieLean.Algebra.Lie.Homology.RelativeCochain

/-!
# Vanishing of relative cohomology by duality with relative homology

Let `L` be a Lie algebra over a field `K` and `η : H → L` a linear map onto an abelian
subalgebra which acts diagonalizably (a `DerivAction` given by `ad η` and the action of `η`). The
relative cochains `C^k(L, η(H); N)` are then the cochains of weight `0` that vanish under
contraction with `η(H)` (`LieModule.ChevalleyEilenberg.DerivAction.mem_relCochains_range_iff`).

Dually, the relative chains are `C_k(L, X)_0` modulo the chains `η(a) ∧ c`. Let `B : N × X → K` be
an invariant pairing identifying `N` with the weight functionals on `X`, as in
`LieModule.ChevalleyEilenberg.DerivAction.exists_δ_eq_of_subsingleton_homology`. If the relative
chain complex is exact in degree `k + 1` (every chain of weight `0` whose differential lies in
`⨆ₐ η(a) ∧ C` is a boundary modulo `⨆ₐ η(a) ∧ C`), then every relative `(k+1)`-cocycle with
values in `N` is the coboundary of a relative `k`-cochain
(`LieModule.ChevalleyEilenberg.DerivAction.exists_δ_eq_of_relExact`).

The proof is the transpose argument of the absolute case. The pairing `f̂` of a relative cocycle
vanishes on the chains `η(a) ∧ c` and on the relative cycles, so it factors through the
differential on the relative chains; a factorization of weight `0` vanishing on the chains
`η(a) ∧ c` comes from a relative cochain.

## Main definitions

* `LieModule.ChevalleyEilenberg.wedgeRange`: the chains `⨆ₐ η(a) ∧ C`.

## Main results

* `LieModule.ChevalleyEilenberg.DerivAction.mem_relCochains_range_iff`: relative cochains are
  the cochains of weight `0` killed by contraction with `η(H)`.
* `LieModule.ChevalleyEilenberg.DerivAction.exists_δ_eq_of_relExact`: the duality theorem.

## References

This is the duality step behind Humphreys, *Representations of semisimple Lie algebras in the
BGG category 𝒪*, GSM 94, Thm. 6.15 (a); the argument here is our own.
-/

open Module TensorProduct ExteriorAlgebra

noncomputable section

namespace Module.End

variable {K H Y : Type*} [Field K] [AddCommGroup H] [Module K H] [AddCommGroup Y] [Module K Y]
  {T : H →ₗ[K] Module.End K Y} (hT : ⨆ ν, weightSpaceOf T ν = ⊤)
include hT

/-- The projection onto a weight space commutes with an endomorphism preserving every weight
space. -/
lemma weightProj_comm_of_mapsTo (μ : Dual K H) (φ : Module.End K Y)
    (hφ : ∀ ν, ∀ y ∈ weightSpaceOf T ν, φ y ∈ weightSpaceOf T ν) (y : Y) :
    weightProj hT μ (φ y) = φ (weightProj hT μ y) := by
  have hy : y ∈ ⨆ ν, weightSpaceOf T ν := hT ▸ Submodule.mem_top
  induction hy using Submodule.iSup_induction' with
  | mem ν y hy =>
    by_cases h : ν = μ
    · subst h
      rw [weightProj_of_mem hT hy, weightProj_of_mem hT (hφ ν y hy)]
    · rw [weightProj_of_mem_ne hT h hy, weightProj_of_mem_ne hT h (hφ ν y hy), map_zero]
  | zero => simp
  | add y y' _ _ h h' => simp only [map_add, h, h']

end Module.End

namespace LieModule.ChevalleyEilenberg

variable {K H L X : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  [AddCommGroup X] [Module K X]

variable (K L X) in
/-- The chains `⨆ₐ η(a) ∧ C` of `⋀L ⊗ X`, which are divided out in the relative chains. -/
def wedgeRange (η : H →ₗ[K] L) : Submodule K (ExteriorAlgebra K L ⊗[K] X) :=
  ⨆ a, LinearMap.range (wedge K L X (η a))

lemma wedge_mem_wedgeRange (η : H →ₗ[K] L) (a : H) (c : ExteriorAlgebra K L ⊗[K] X) :
    wedge K L X (η a) c ∈ wedgeRange K L X η :=
  Submodule.mem_iSup_of_mem a (LinearMap.mem_range_self _ c)

namespace DerivAction

variable [LieRingModule L X] [LieModule K L X] (ρ : DerivAction K H L X)
  {N : Type*} [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  (ρN : DerivAction K H L N) {η : H →ₗ[K] L}

/-! ### Relative cochains as weight-`0` cochains -/

section Cochains

variable {ρN}
variable (hDN : ∀ a, ρN.D a = LieAlgebra.ad K L (η a)) (hφN : ∀ a n, ρN.φ a n = ⁅η a, n⁆)
include hDN hφN

omit [LieModule K L X] in
lemma coAct_eq_neg_lieDeriv (a : H) (F : ExteriorAlgebra K L →ₗ[K] N) :
    ρN.coAct a F = -lieDeriv (η a) F := by
  refine LinearMap.ext fun c ↦ ?_
  rw [coAct_apply, LinearMap.neg_apply, lieDeriv_apply, hDN, hφN, neg_sub]

omit [LieModule K L X] in
/-- The relative cochains `C^k(L, η(H); N)` are the cochains of weight `0` that vanish under
contraction with `η(H)`. -/
theorem mem_relCochains_range_iff {k : ℕ} {f : Cochains K L N k} :
    f ∈ relCochains K L N (Set.range η) k ↔
      f ∈ ρN.cochainWeightSpace k 0 ∧ ∀ a, contract (η a) (f ∘ₗ degProj K L k) = 0 := by
  have hco : ∀ a, (ρN.coActDeg k a f = 0 ↔ ρN.coAct a (f ∘ₗ degProj K L k) = 0) := by
    intro a
    have h := ρN.coActDeg_comp_degProj k a f
    constructor
    · intro h0
      refine linearMap_ext_exteriorPower fun j ↦ ?_
      by_cases hj : j = k
      · subst hj
        rw [← h, h0]; rfl
      · refine LinearMap.ext fun ω ↦ ?_
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply,
          coAct_apply, degProj_of_mem ω.2 hj,
          degProj_of_mem (extDeriv_mem_exteriorPower (ρN.D a) ω.2) hj, map_zero, sub_zero]
    · intro h0
      refine LinearMap.ext fun ω ↦ ?_
      have h' := LinearMap.congr_fun h ω
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, degProj_subtype, h0,
        LinearMap.zero_apply] at h'
      exact h'
  constructor
  · intro hf
    refine ⟨fun a ↦ ?_, fun a ↦ (hf (η a) ⟨a, rfl⟩).1⟩
    rw [LinearMap.zero_apply, zero_smul, hco, coAct_eq_neg_lieDeriv hDN hφN,
      (hf (η a) ⟨a, rfl⟩).2, neg_zero]
  · rintro ⟨hw, hc⟩ y ⟨a, rfl⟩
    refine ⟨hc a, ?_⟩
    have h0 : ρN.coActDeg k a f = 0 := by
      rw [hw a, LinearMap.zero_apply, zero_smul]
    rw [hco, coAct_eq_neg_lieDeriv hDN hφN, neg_eq_zero] at h0
    exact h0

end Cochains

/-! ### The duality theorem -/

variable {ρ ρN}

/-- **Vanishing of relative cohomology by duality.** Let `η : H → L` have abelian image acting
on `L`, `X` and `N` through the given `DerivAction`s, and let `B : N × X → K` be an invariant
pairing identifying `N` with the weight functionals on `X`, with `L` and `X` sums of weight
spaces. If the relative chain complex `C_•(L, X)_0 / (⨆ₐ η(a) ∧ C)` is exact in degree `k + 1`,
then every relative `(k+1)`-cocycle with values in `N` is the coboundary of a relative
`k`-cochain. -/
theorem exists_δ_eq_of_relExact {B : N →ₗ[K] X →ₗ[K] K}
    (hD : ∀ a, ρN.D a = ρ.D a) (hDN : ∀ a, ρN.D a = LieAlgebra.ad K L (η a))
    (hφN : ∀ a n, ρN.φ a n = ⁅η a, n⁆) (hab : ∀ a b, ⁅η a, η b⁆ = 0)
    (hB : ∀ (x : L) (n : N) (m : X), B ⁅x, n⁆ m = -B n ⁅x, m⁆)
    (hBφ : ∀ (a : H) (n : N) (m : X), B (ρN.φ a n) m = -B n (ρ.φ a m))
    (hinj : Function.Injective B)
    (hrep : ∀ (γ : Dual K H) (ψ : X →ₗ[K] K), (∀ a m, ψ (ρ.φ a m) = γ a * ψ m) →
      ψ ∈ LinearMap.range B)
    (hL : ⨆ γ, Module.End.weightSpaceOf ρ.D γ = ⊤)
    (hX : ⨆ ν, Module.End.weightSpaceOf ρ.φ ν = ⊤) {k : ℕ}
    (hexact : ∀ t ∈ ρ.chainPiece (k + 1) 0, diff K L X t ∈ wedgeRange K L X η →
      ∃ s ∈ ρ.chainPiece (k + 2) 0, t - diff K L X s ∈ wedgeRange K L X η)
    {f : Cochains K L N (k + 1)} (hf : f ∈ relCochains K L N (Set.range η) (k + 1))
    (hδ : δ K L N (k + 1) f = 0) :
    ∃ g ∈ relCochains K L N (Set.range η) k, δ K L N k g = f := by
  obtain ⟨hfw, hfc⟩ := (mem_relCochains_range_iff hDN hφN).mp hf
  obtain ⟨F, hF⟩ : ∃ F, F = cochainPair B (f ∘ₗ degProj K L (k + 1)) := ⟨_, rfl⟩
  have hFθ : ∀ (a : H) {t}, t ∈ chainsIn K L X (k + 1) → F (ρ.θ a t) = 0 := by
    intro a t ht
    rw [hF, cochainPair_θ ρ ρN hD hBφ hfw a ht, LinearMap.zero_apply, neg_zero, zero_mul]
  -- `F` vanishes on the chains `η(a) ∧ c`
  have hFw : ∀ w ∈ wedgeRange K L X η, F w = 0 := by
    intro w hw
    induction hw using Submodule.iSup_induction' with
    | mem a w hw =>
      obtain ⟨c, rfl⟩ := hw
      rw [hF, cochainPair_wedge, hfc a, map_zero, LinearMap.zero_apply]
    | zero => exact map_zero F
    | add w w' _ _ h h' => rw [map_add, h, h', add_zero]
  -- `F ∘ d = 0` on all chains, since `f` is a cocycle
  have hFd : ∀ s ∈ chainsIn K L X (k + 2), F (diff K L X s) = 0 := by
    rintro s ⟨s, rfl⟩
    rw [hF, ← cochainPair_cochainDiff hB]
    induction s with
    | tmul ω m =>
      have h := LinearMap.congr_fun hδ ω
      rw [δ_apply, LinearMap.zero_apply] at h
      rw [incl_tmul, cochainPair_tmul, h, map_zero, LinearMap.zero_apply]
    | add s s' hs hs' => simp only [map_add, hs, hs', add_zero]
  -- so `F` factors through `(t, w) ↦ d t + w` on the relative chains
  obtain ⟨ψ₁, hψ₁⟩ : ∃ ψ₁ : ExteriorAlgebra K L ⊗[K] X →ₗ[K] K,
      ∀ (t : ρ.chainPiece (k + 1) 0) (w : wedgeRange K L X η),
        ψ₁ (diff K L X t + w) = F t := by
    let D : ρ.chainPiece (k + 1) 0 × wedgeRange K L X η →ₗ[K] ExteriorAlgebra K L ⊗[K] X :=
      (diff K L X ∘ₗ (ρ.chainPiece (k + 1) 0).subtype).coprod (wedgeRange K L X η).subtype
    obtain ⟨ψ₁, hψ₁⟩ := LinearMap.exists_comp_eq_of_ker_le
      (V := ρ.chainPiece (k + 1) 0 × wedgeRange K L X η) D
      ((F ∘ₗ (ρ.chainPiece (k + 1) 0).subtype).coprod 0) fun ⟨t, w⟩ htw ↦ by
        have h0 : diff K L X t + w = 0 := htw
        obtain ⟨s, hs, hts⟩ := hexact t t.2
          (by rw [eq_neg_of_add_eq_zero_left h0]; exact neg_mem w.2)
        have e : F t = F (↑t - diff K L X s) + F (diff K L X s) := by
          rw [← map_add, sub_add_cancel]
        exact LinearMap.mem_ker.mpr (by
          simp only [LinearMap.coprod_apply, LinearMap.comp_apply, Submodule.subtype_apply,
            LinearMap.zero_apply, add_zero]
          rw [e, hFw _ hts, hFd s hs.1, add_zero])
    refine ⟨ψ₁, fun t w ↦ ?_⟩
    simpa [D] using LinearMap.congr_fun hψ₁ (t, w)
  -- the projection onto the weight space of weight `0`
  have hT := ρ.iSup_chainWeightSpace hL hX
  set Pr := Module.End.weightProj hT 0
  have hwedge : ∀ (a : H) (c : ExteriorAlgebra K L ⊗[K] X),
      Pr (wedge K L X (η a) c) = wedge K L X (η a) (Pr c) := by
    intro a c
    refine Module.End.weightProj_comm_of_mapsTo hT 0 _ (fun ν c hc b ↦ ?_) c
    rw [ρ.θ_wedge, ← hD, hDN, LieAlgebra.ad_apply, hab, map_zero, LinearMap.zero_apply,
      zero_add, hc b, map_smul]
  obtain ⟨ψ, hψθ, hψw, hψd⟩ : ∃ ψ : ExteriorAlgebra K L ⊗[K] X →ₗ[K] K,
      (∀ a t, ψ (ρ.θ a t) = -(0 : Dual K H) a * ψ t) ∧
      (∀ w ∈ wedgeRange K L X η, ψ w = 0) ∧
      ∀ t ∈ chainsIn K L X (k + 1), ψ (diff K L X t) = F t := by
    have hψ₁w : ∀ w ∈ wedgeRange K L X η, ψ₁ w = 0 := by
      intro w hw
      have h := hψ₁ 0 ⟨w, hw⟩
      rwa [ZeroMemClass.coe_zero, map_zero, zero_add, map_zero] at h
    refine ⟨ψ₁ ∘ₗ Pr, fun a t ↦ ?_, fun w hw ↦ ?_, fun t ht ↦ ?_⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, Module.End.weightProj_comm hT,
        mem_chainWeightSpace.mp (Module.End.weightProj_mem hT 0 t) a, map_smul,
        LinearMap.zero_apply, zero_smul]
      simp
    · rw [LinearMap.comp_apply]
      refine hψ₁w _ ?_
      induction hw using Submodule.iSup_induction' with
      | mem a w hw =>
        obtain ⟨c, rfl⟩ := hw
        rw [hwedge]
        exact wedge_mem_wedgeRange η a _
      | zero => rw [map_zero]; exact zero_mem _
      | add w w' _ _ h h' => rw [map_add]; exact add_mem h h'
    · rw [← ρ.iSup_inf_chainWeightSpace hL hX (chainsIn K L X (k + 1))
        (fun a _ hc ↦ ρ.θ_mem_chainsIn a hc)] at ht
      induction ht using Submodule.iSup_induction' with
      | mem ν t ht =>
        obtain ⟨htc, htw⟩ := ht
        have hdw := ρ.diff_mem_chainWeightSpace htw
        by_cases hν : ν = 0
        · subst hν
          have h := hψ₁ ⟨t, htc, htw⟩ 0
          rw [ZeroMemClass.coe_zero, add_zero] at h
          rw [LinearMap.comp_apply, Module.End.weightProj_of_mem hT hdw, h]
        · rw [LinearMap.comp_apply, Module.End.weightProj_of_mem_ne hT hν hdw, map_zero]
          obtain ⟨a, ha⟩ : ∃ a, ν a ≠ 0 := by
            by_contra h
            push Not at h
            exact hν (LinearMap.ext fun a ↦ h a)
          have h1 := hFθ a htc
          rw [mem_chainWeightSpace.mp htw a, map_smul, smul_eq_mul] at h1
          exact ((mul_eq_zero.mp h1).resolve_left ha).symm
      | zero => simp only [map_zero]
      | add t t' _ _ h h' => rw [map_add, map_add, map_add, h, h']
  -- the primitive
  obtain ⟨g, hgw, hpair⟩ := exists_cochain_of_weight (ρ := ρ) (ρN := ρN) hD hBφ hinj hrep hL
    (k := k) ψ hψθ
  have hgc : ∀ a, contract (η a) (g ∘ₗ degProj K L k) = 0 := by
    intro a
    refine linearMap_ext_exteriorPower fun j ↦ LinearMap.ext fun ω ↦ hinj
      (LinearMap.ext fun m ↦ ?_)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, contract_apply,
      LinearMap.zero_apply, map_zero]
    by_cases hj : j + 1 = k
    · have hω : (ι K (η a) * (ω : ExteriorAlgebra K L)) ⊗ₜ m ∈ chainsIn K L X k :=
        hj ▸ tmul_mem_chainsIn (ι_mul_mem_exteriorPower (η a) ω.2) m
      have h := hpair _ hω
      rw [cochainPair_tmul, LinearMap.comp_apply, ← wedge_tmul,
        hψw _ (wedge_mem_wedgeRange η a _)] at h
      exact h
    · rw [degProj_of_mem (ι_mul_mem_exteriorPower (η a) ω.2) hj, map_zero, map_zero,
        LinearMap.zero_apply]
  refine ⟨g, (mem_relCochains_range_iff hDN hφN).mpr ⟨hgw, hgc⟩,
    LinearMap.ext fun ω ↦ hinj (LinearMap.ext fun m ↦ ?_)⟩
  have hω : (ω : ExteriorAlgebra K L) ⊗ₜ m ∈ chainsIn K L X (k + 1) := tmul_mem_chainsIn ω.2 m
  rw [δ_apply]
  change cochainPair B (cochainDiff K L N (g ∘ₗ degProj K L k)) ((ω : ExteriorAlgebra K L) ⊗ₜ m)
    = _
  rw [cochainPair_cochainDiff hB, hpair _ (diff_mem_chainsIn hω), hψd _ hω, hF,
    cochainPair_tmul, LinearMap.comp_apply, degProj_subtype]

end DerivAction

end LieModule.ChevalleyEilenberg
