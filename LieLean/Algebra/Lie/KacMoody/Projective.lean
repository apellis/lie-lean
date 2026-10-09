/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.HarishChandraLinkage
import LieLean.Algebra.Lie.KacMoody.HighestWeightVector
import LieLean.Algebra.Lie.KacMoody.TranslationWallExt
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroupDominant

/-!
# Projective objects in category `𝒪`

A module `V` is *projective in `𝒪`* (`IsProjectiveO`) if every morphism from `V` to a module `N`
in `𝒪` lifts along every surjection `M → N` of modules in `𝒪`. The definition quantifies over
modules in a fixed universe `w`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsProjectiveO`: projectivity in `𝒪`.
* `Matrix.Realization.IsDominant`: `⟨λ + ρ, β^∨⟩ ∉ ℤ_{<0}` for all positive roots `β`
  (Humphreys, GSM 94, §3.5).
* `Matrix.Realization.KacMoodyAlgebra.projectiveCoverAmbient`: `M(λ + nρ) ⊗ L(nρ)^*`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsProjectiveO.of_retract`: direct summands (retracts) of
  projectives are projective.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.isProjectiveO_of_forall`: in finite type, if
  no weight `w·λ ≠ λ` of the dot orbit of `λ` lies in `λ + Q₊`, then `M(λ)` is projective in `𝒪`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.isProjectiveO`: `M(λ)` is projective for
  `λ` dominant (Humphreys, GSM 94, Proposition 3.8 (a)).
* `Matrix.Realization.KacMoodyAlgebra.IsProjectiveO.tensorProduct`: `P ⊗ L` is projective for
  `P` projective and `L` finite-dimensional in `𝒪` (Humphreys, GSM 94, Proposition 3.8 (b)).
* `Matrix.Realization.IsDominant.eq_zero_of_apply_eq`: a dominant weight is maximal in its dot
  orbit.
* `Matrix.Realization.exists_forall_add_nsmul_rho`: `λ + nρ` is maximal in its dot orbit for
  some `n ∈ ℕ`.
* `Matrix.Realization.KacMoodyAlgebra.exists_isProjectiveO_surjective_verma`: every Verma module
  `M(λ)` (hence every `L(λ)`) is a quotient of the projective module `M(λ + nρ) ⊗ L(nρ)^*`
  (Humphreys, GSM 94, proof of Theorem 3.8).

## Proof notes

Proposition 3.8 (a) follows Humphreys: a lift `y` of weight `λ` of the image of the highest
weight vector can be taken in the generalized central block of `χ_λ`; if some `eᵢ y ≠ 0`, the
block contains a primitive vector of weight `λ + αᵢ + (Q₊)`, whose central character is then
`χ_λ`, so by Harish-Chandra's theorem its weight is `w·λ ∈ λ + Q₊`, `w·λ ≠ λ`. The surjection
`M(λ + nρ) ⊗ L(nρ)^* → M(λ)` is the adjoint of the primitive vector `v_λ ⊗ ξ` of
`M(λ) ⊗ L(nρ)^{**}`, `ξ` the evaluation at the highest weight vector of `L(nρ)`. The
dominance of `λ + nρ` for large `n` is reconstructed by bounding root coordinates: for `w ≠ 1`,
`ρ - wρ ∈ Q₊ \ {0}`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §3.5, §3.8.
-/

noncomputable section

open Module LieModule TensorProduct

universe w

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)

/-- For a weight `μ` with `⟨μ, αᵢ^∨⟩ ∈ ℤ_{>0}` for all `i` (e.g. `ρ`) and `w ∈ W`, either `w = 1`
or `μ - w μ` is a nonzero element of `Q₊`. -/
theorem eq_one_or_exists_sub_apply_eq_rootOf {μ : Dual K H}
    (hμ : ∀ i, ∃ n : ℕ, μ (P.coroot i) = n + 1) (w : P.weylGroup hA) :
    w = 1 ∨ ∃ k : ι → ℤ, 0 ≤ k ∧ k ≠ 0 ∧
      μ - (w : Dual K H ≃ₗ[K] Dual K H) μ = P.rootOf k := by
  classical
  refine P.weylGroup_induction_length hA (p := fun w : P.weylGroup hA ↦ w = 1 ∨
    ∃ k : ι → ℤ, 0 ≤ k ∧ k ≠ 0 ∧ μ - (w : Dual K H ≃ₗ[K] Dual K H) μ = P.rootOf k)
    (Or.inl rfl) (fun w i hwi ih ↦ Or.inr ?_) w
  obtain ⟨l, hl, hwl⟩ := (P.not_isRightDescent_coxeterSystem_iff hA).mp hwi
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero, LinearEquiv.map_eq_zero_iff] at hwl
    exact P.linearIndependent_root.ne_zero i hwl
  obtain ⟨m, hm⟩ := hμ i
  obtain ⟨k, hk, hwk⟩ : ∃ k : ι → ℤ, 0 ≤ k ∧
      μ - (w : Dual K H ≃ₗ[K] Dual K H) μ = P.rootOf k := by
    rcases ih with rfl | ⟨k, hk, -, hwk⟩
    · exact ⟨0, le_rfl, by simp⟩
    · exact ⟨k, hk, hwk⟩
  refine ⟨k + ((m : ℤ) + 1) • l, add_nonneg hk (smul_nonneg (by positivity) hl), ?_, ?_⟩
  · intro h0
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hl0
    have h1 := congrFun h0 j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    have h2 : 0 < l j := lt_of_le_of_ne (hl j) (Ne.symm hj)
    have h3 : (0 : ℤ) ≤ k j := hk j
    nlinarith
  · rw [Subgroup.coe_mul, coxeterSystem_simple, LinearEquiv.mul_apply, reflection_apply, map_sub,
      map_smul, hm, hwl, map_add, map_zsmul, ← hwk, ← Int.cast_smul_eq_zsmul K]
    push_cast
    module

section Dominant

variable [DecidableEq ι] (hF : A.IsFiniteCartan)

/-- A weight `λ` is **dominant** if `⟨λ + ρ, β^∨⟩ ∉ ℤ_{<0}` for every positive root `β`
(Humphreys, GSM 94, §3.5; for integral `λ` these are the weights in `Λ⁺ - ρ`). -/
def IsDominant (μ : Dual K H) : Prop :=
  ∀ v i, P.IsPosRoot hA v i → ∀ n : ℤ, P.corootPairing hA (μ + P.rho) v i = n → 0 ≤ n

include hF in
/-- A dominant weight is maximal in its dot orbit (Humphreys, GSM 94, §3.5, the statement dual
to Prop. 3.5 (c)): if `w·λ - λ ∈ Q₊` then `w·λ = λ`. -/
theorem IsDominant.eq_zero_of_apply_eq {μ : Dual K H} (hμ : P.IsDominant hF.isGeneralizedCartan μ)
    {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hF.isGeneralizedCartan) {k : ι → ℤ}
    (hk : 0 ≤ k) (hwk : w (μ + P.rho) = μ + P.rho + P.rootOf k) : k = 0 := by
  have hb : ∀ v i, P.IsPosRoot hF.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hF.isGeneralizedCartan (-(μ + P.rho)) v i = n → n ≤ 0 := by
    intro v i hv n hn
    rw [corootPairing_neg, neg_eq_iff_eq_neg] at hn
    have := hμ v i hv (-n) (by rw [hn]; push_cast; ring)
    omega
  have hwb : (⟨w, hw⟩ : P.weylGroup hF.isGeneralizedCartan) ∈
      P.integralWeylGroup hF.isGeneralizedCartan (-(μ + P.rho)) := by
    rw [mem_integralWeylGroup]
    change w (-(μ + P.rho)) - -(μ + P.rho) ∈ P.rootLattice
    rw [map_neg, hwk, show -(μ + P.rho + P.rootOf k) - -(μ + P.rho) = P.rootOf (-k) by
      rw [map_neg]; abel]
    exact P.rootOf_mem_rootLattice _
  obtain ⟨k', hk', hwk'⟩ := exists_nonneg_apply_sub_eq_rootOf (P := P) hF hb hwb
  change w (-(μ + P.rho)) - -(μ + P.rho) = P.rootOf k' at hwk'
  rw [map_neg, hwk, show -(μ + P.rho + P.rootOf k) - -(μ + P.rho) = P.rootOf (-k) by
    rw [map_neg]; abel] at hwk'
  have h := P.rootOf_injective hwk'
  ext j
  have h1 := congrFun h j
  have h2 : (0 : ℤ) ≤ k j := hk j
  have h3 : (0 : ℤ) ≤ k' j := hk' j
  simp only [Pi.neg_apply] at h1
  simp only [Pi.zero_apply]
  omega

include hF in
/-- For every weight `λ` there is `n ∈ ℕ` such that `λ + nρ` is maximal in its dot orbit: no
`w·(λ + nρ)` lies in `λ + nρ + Q₊ \ {0}`. (Humphreys, proof of Theorem 3.8, uses that `λ + nρ` is
dominant for large `n`; reconstructed: for `w ≠ 1`, `ρ - wρ ∈ Q₊ \ {0}`, which bounds the root
coordinates of `w(λ + ρ) - (λ + ρ)` below by `n`.) -/
theorem exists_forall_add_nsmul_rho (μ : Dual K H) :
    ∃ n : ℕ, ∀ w ∈ P.weylGroup hF.isGeneralizedCartan, ∀ k : ι → ℤ, 0 ≤ k →
      w (μ + (n : K) • P.rho + P.rho) = μ + (n : K) • P.rho + P.rho + P.rootOf k → k = 0 := by
  classical
  have hA := hF.isGeneralizedCartan
  have := P.finite_weylGroup hF
  let _ : Fintype (P.weylGroup hA) := Fintype.ofFinite _
  let c : P.weylGroup hA → ℕ := fun w ↦
    if h : ∃ k : ι → ℤ, P.rootOf k = (w : Dual K H ≃ₗ[K] Dual K H) (μ + P.rho) - (μ + P.rho)
    then ∑ j, (h.choose j).natAbs else 0
  refine ⟨∑ w, c w + 1, fun w hw k hk hwk ↦ ?_⟩
  set n := ∑ w, c w + 1 with hn
  rcases P.eq_one_or_exists_sub_apply_eq_rootOf hA (μ := P.rho) (fun i ↦ ⟨0, by simp⟩)
    ⟨w, hw⟩ with h1 | ⟨m, hm, hm0, hwm⟩
  · have hw1 : w = 1 := congrArg Subtype.val h1
    subst hw1
    have : P.rootOf k = P.rootOf 0 := by
      rw [map_zero]; simpa using hwk.symm
    exact P.rootOf_injective this
  · change P.rho - w P.rho = P.rootOf m at hwm
    have hex : P.rootOf (k + (n : ℤ) • m) = w (μ + P.rho) - (μ + P.rho) := by
      have e1 : w (μ + (n : K) • P.rho + P.rho) =
          w (μ + P.rho) + (n : K) • (P.rho - P.rootOf m) := by
        rw [← hwm, sub_sub_cancel, show μ + (n : K) • P.rho + P.rho = (μ + P.rho) + (n : K) • P.rho
          by abel, map_add, map_smul]
      rw [e1, smul_sub] at hwk
      rw [map_add, map_zsmul, ← Int.cast_smul_eq_zsmul K, Int.cast_natCast,
        eq_sub_of_add_eq hwk]
      abel
    have hc : c ⟨w, hw⟩ = ∑ j, (k j + (n : ℤ) * m j).natAbs := by
      have h : ∃ k' : ι → ℤ, P.rootOf k' = w (μ + P.rho) - (μ + P.rho) := ⟨_, hex⟩
      simp only [c, h, ↓reduceDIte]
      have := P.rootOf_injective (h.choose_spec.trans hex.symm)
      rw [this]
      rfl
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hm0
    have hmj : 1 ≤ m j := lt_of_le_of_ne (hm j) (Ne.symm hj)
    have hle : n ≤ c ⟨w, hw⟩ := by
      rw [hc]
      refine le_trans ?_ (Finset.single_le_sum (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ j))
      have h2 : (0 : ℤ) ≤ k j := hk j
      have : (n : ℤ) ≤ k j + (n : ℤ) * m j := by nlinarith
      omega
    have hlt : c ⟨w, hw⟩ < n := by
      rw [hn]
      exact Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _))
    omega

end Dominant

end Matrix.Realization

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Projective

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V W : Type*}
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]

local notation "𝔤" => KacMoodyAlgebra P

variable (V) in
/-- `V` is **projective in `𝒪`** (Humphreys, GSM 94, §3.8): for every surjection `π : M → N` of
modules in `𝒪` (in the universe `w`) and every morphism `φ : V → N` there is `ψ : V → M` with
`π ∘ ψ = φ`. -/
def IsProjectiveO : Prop :=
  ∀ ⦃M N : Type w⦄ [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M] [LieModule K 𝔤 M]
    [AddCommGroup N] [Module K N] [LieRingModule 𝔤 N] [LieModule K 𝔤 N],
    IsCategoryO P M → IsCategoryO P N → ∀ π : M →ₗ⁅K,𝔤⁆ N, Function.Surjective π →
      ∀ φ : V →ₗ⁅K,𝔤⁆ N, ∃ ψ : V →ₗ⁅K,𝔤⁆ M, π.comp ψ = φ

namespace IsProjectiveO

variable {P}

omit [LieModule K 𝔤 V] [LieModule K 𝔤 W] in
/-- A retract of a projective module is projective: if `r ∘ s = id_W` with `V` projective, then
`W` is projective. -/
theorem of_retract (hV : IsProjectiveO.{w} P V) (s : W →ₗ⁅K,𝔤⁆ V) (r : V →ₗ⁅K,𝔤⁆ W)
    (hrs : r.comp s = LieModuleHom.id) : IsProjectiveO.{w} P W := by
  intro M N _ _ _ _ _ _ _ _ hM hN π hπ φ
  obtain ⟨ψ, hψ⟩ := hV hM hN π hπ (φ.comp r)
  refine ⟨ψ.comp s, ?_⟩
  ext x
  have h1 := LieModuleHom.congr_fun hψ (s x)
  have h2 := LieModuleHom.congr_fun hrs x
  simp only [LieModuleHom.comp_apply, LieModuleHom.id_apply] at h1 h2 ⊢
  rw [h1, h2]

omit [LieModule K 𝔤 V] [LieModule K 𝔤 W] in
/-- Projectivity is invariant under isomorphism. -/
theorem of_equiv (hV : IsProjectiveO.{w} P V) (e : V ≃ₗ⁅K,𝔤⁆ W) : IsProjectiveO.{w} P W :=
  hV.of_retract e.symm.toLieModuleHom e.toLieModuleHom (by ext; simp)

end IsProjectiveO

/-- A surjective morphism of `𝔥`-diagonalizable modules maps weight spaces onto weight spaces. -/
theorem map_weightSpace_of_surjective (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤)
    (f : V →ₗ⁅K,𝔤⁆ W) (hf : Function.Surjective f) (μ : Dual K H) :
    (weightSpaceOfMap V (h P) μ).map (f : V →ₗ[K] W) = weightSpaceOfMap W (h P) μ := by
  have hle : ∀ ν, (weightSpaceOfMap V (h P) ν).map (f : V →ₗ[K] W) ≤
      weightSpaceOfMap W (h P) ν := fun ν ↦ by
    rintro _ ⟨v, hv, rfl⟩
    exact map_mem_weightSpaceOfMap P f hv
  refine le_antisymm (hle μ) fun x hx ↦ mem_of_mem_iSup_of_le (h P) _ hle hx ?_
  rw [← Submodule.map_iSup, hV, Submodule.map_top, LinearMap.range_eq_top.mpr hf]
  trivial

end Projective

section CentralCharacter

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

/-- A nonzero primitive vector of weight `ν` in the generalized central block of `χ` forces
`χ = χ_ν`. -/
theorem centralCharacter_eq_of_mem_centralBlock {χ : 𝓩 →ₐ[K] K} {ν : Dual K H} {v : V}
    (hv : v ∈ primitiveVectors P V ν) (hv0 : v ≠ 0) (hχ : v ∈ centralBlock P V χ) :
    centralCharacter P ν = χ := by
  set φ := (homEquiv P V ν).symm ⟨v, hv⟩
  have hφ : φ (hwv P ν) = v := congrArg Subtype.val ((homEquiv P V ν).apply_symm_apply ⟨v, hv⟩)
  ext z
  obtain ⟨n, hn⟩ := (mem_centralBlock P χ v).mp hχ z
  have hz : rep P V (z : 𝓤) v = centralCharacter P ν z • v := by
    rw [← hφ]; exact rep_center_map P ν φ z _
  have key : ∀ m : ℕ, ((rep P V (z : 𝓤) - χ z • 1) ^ m) v =
      (centralCharacter P ν z - χ z) ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hz,
        LinearMap.smul_apply, Module.End.one_apply, ← sub_smul, smul_smul, pow_succ', mul_comm]
  rw [key, smul_eq_zero] at hn
  rcases hn with hn | hn
  · exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hn)
  · exact absurd hn hv0

end CentralCharacter

section VermaProjective

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- **Verma modules of maximal weights are projective** (cf. Humphreys, GSM 94,
Proposition 3.8 (a)): in finite type, over an algebraically closed field of characteristic
zero, if no weight `w·λ` of the dot orbit of `λ` lies in `λ + Q₊ \ {0}`, then `M(λ)` is
projective in `𝒪`. -/
theorem VermaModule.isProjectiveO_of_forall {Λ : Dual K H}
    (hΛ : ∀ w ∈ P.weylGroup hA.isGeneralizedCartan, ∀ k : ι → ℤ, 0 ≤ k →
      w (Λ + P.rho) = Λ + P.rho + P.rootOf k → k = 0) :
    IsProjectiveO.{w} P (VermaModule P Λ) := by
  intro M N _ _ _ _ _ _ _ _ hM hN π hπ φ
  set χ := centralCharacter P Λ
  have hB : IsCategoryO P (centralBlock P M χ) := hM.centralBlock P χ
  have hx : φ (hwv P Λ) ∈ centralBlock P N χ :=
    map_mem_centralBlock P φ χ (by rw [centralBlock_verma]; trivial)
  have hxw : φ (hwv P Λ) ∈ weightSpaceOfMap N (h P) Λ :=
    map_mem_weightSpaceOfMap P φ (hwv_mem_weightSpace P Λ)
  have hmem : (⟨_, hx⟩ : centralBlock P N χ) ∈ weightSpaceOfMap (centralBlock P N χ) (h P) Λ :=
    mem_weightSpaceOfMap_lieSubmodule_iff.mpr hxw
  rw [← map_weightSpace_of_surjective P hB.iSup_weightSpaceOfMap_eq_top _
    (hM.surjective_centralBlockMap P π hπ χ)] at hmem
  obtain ⟨y, hy, hyx⟩ := hmem
  have hyM : (y : M) ∈ weightSpaceOfMap M (h P) Λ := mem_weightSpaceOfMap_lieSubmodule_iff.mp hy
  have hprim : ∀ i, ⁅e P i, (y : M)⁆ = 0 := by
    intro i
    by_contra hne
    have hne' : toEnd K 𝔤 (centralBlock P M χ) (e P i) y ≠ 0 := fun h0 ↦
      hne (by simpa using congrArg Subtype.val h0)
    have hw : weightSpaceOfMap (centralBlock P M χ) (h P) (Λ + P.root i) ≠ ⊥ := fun hbot ↦
      hne' (by simpa [hbot] using toEnd_e_mem_weightSpace i hy)
    obtain ⟨l, hl, z, hz, hz0, hze⟩ := hB.exists_lie_e_eq_zero_of_weightSpace_ne_bot hw
    have hzp : (z : M) ∈ primitiveVectors P M (Λ + P.root i + P.rootOf l) :=
      mem_primitiveVectors.mpr ⟨mem_weightSpaceOfMap_lieSubmodule_iff.mp hz,
        fun j ↦ by simpa using congrArg Subtype.val (hze j)⟩
    have hχ := centralCharacter_eq_of_mem_centralBlock P hzp
      (fun h0 ↦ hz0 (Subtype.ext h0)) z.2
    obtain ⟨w, hw, hwe⟩ := (VermaModule.centralCharacter_eq_iff P hA Λ _).mp hχ.symm
    have hk := hΛ w hw (Pi.single i 1 + l)
      (add_nonneg (Pi.single_nonneg.mpr zero_le_one) hl)
      (by rw [hwe, map_add, rootOf_single]; abel)
    have := congrFun hk i
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at this
    have h0 : (0 : ℤ) ≤ l i := hl i
    omega
  refine ⟨(homEquiv P M Λ).symm ⟨y, mem_primitiveVectors.mpr ⟨hyM, hprim⟩⟩, hom_ext P Λ ?_⟩
  rw [LieModuleHom.comp_apply]
  have h1 : ((homEquiv P M Λ).symm ⟨y, mem_primitiveVectors.mpr ⟨hyM, hprim⟩⟩) (hwv P Λ) = y :=
    congrArg Subtype.val ((homEquiv P M Λ).apply_symm_apply _)
  rw [h1]
  exact congrArg Subtype.val hyx

include hA in
/-- **`M(λ)` is projective for `λ` dominant** (Humphreys, GSM 94, Proposition 3.8 (a)), in
finite type over an algebraically closed field of characteristic zero. -/
theorem VermaModule.isProjectiveO {Λ : Dual K H} (hΛ : P.IsDominant hA.isGeneralizedCartan Λ) :
    IsProjectiveO.{w} P (VermaModule P Λ) :=
  isProjectiveO_of_forall P hA fun _ hw _ hk hwk ↦ hΛ.eq_zero_of_apply_eq P hA hw hk hwk

end VermaProjective

section Tensor

universe u l

variable {ι H : Type*} {K : Type u} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V M N N' : Type*}
  [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup M] [Module K M] [LieRingModule P.KacMoodyAlgebra M]
  [LieModule K P.KacMoodyAlgebra M]
  [AddCommGroup N] [Module K N] [LieRingModule P.KacMoodyAlgebra N]
  [LieModule K P.KacMoodyAlgebra N]
  [AddCommGroup N'] [Module K N'] [LieRingModule P.KacMoodyAlgebra N']
  [LieModule K P.KacMoodyAlgebra N']
  {L : Type l} [AddCommGroup L] [Module K L] [LieRingModule P.KacMoodyAlgebra L]
  [LieModule K P.KacMoodyAlgebra L] [FiniteDimensional K L]

local notation "𝔤" => KacMoodyAlgebra P

omit [CharZero K] in
/-- `Hom_K(L, −)` applied to `tensorHomAdjunction f` evaluates `f`:
`(tensorHomAdjunction f m)(l) = f (m ⊗ l)` under `N ⊗ L^* ≅ Hom_K(L, N)`. -/
theorem tensorDualEquivHom_tensorHomAdjunction (f : M ⊗[K] L →ₗ⁅K,𝔤⁆ N) (m : M) (l : L) :
    tensorDualEquivHom P N L (tensorHomAdjunction P f m) l = f (m ⊗ₜ l) := by
  change tensorDualEquivHom P N L ((tensorDualEquivHom P N L).symm _) l = _
  rw [LieModuleEquiv.apply_symm_apply]
  rfl

omit [CharZero K] in
/-- Naturality of the tensor–Hom adjunction in the target. -/
theorem tensorHomAdjunction_comp (q : N →ₗ⁅K,𝔤⁆ N') (f : M ⊗[K] L →ₗ⁅K,𝔤⁆ N) :
    tensorHomAdjunction P (q.comp f) =
      (TensorProduct.LieModule.map q LieModuleHom.id).comp (tensorHomAdjunction P f) := by
  ext m
  apply (tensorDualEquivHom P N' L).injective
  rw [LieModuleHom.comp_apply, tensorDualEquivHom_map]
  ext l
  rw [tensorDualEquivHom_tensorHomAdjunction, LinearMap.comp_apply,
    tensorDualEquivHom_tensorHomAdjunction]
  rfl

/-- **Tensoring a projective with a finite-dimensional module** (Humphreys, GSM 94,
Proposition 3.8 (b)): if `V` is projective in `𝒪` and `L` is finite-dimensional with `L^*` in
`𝒪`, then `V ⊗ L` is projective, via `Hom(V ⊗ L, −) ≅ Hom(V, − ⊗ L^*)` and exactness of
`− ⊗ L^*`. -/
theorem IsProjectiveO.tensorProduct (hV : IsProjectiveO.{max w u l} P V)
    (hL' : IsCategoryO P (Module.Dual K L)) : IsProjectiveO.{w} P (V ⊗[K] L) := by
  intro M N _ _ _ _ _ _ _ _ hM hN π hπ φ
  set π' := TensorProduct.LieModule.map π (LieModuleHom.id : Module.Dual K L →ₗ⁅K,𝔤⁆ _)
  have hπ' : Function.Surjective π' :=
    TensorProduct.map_surjective hπ Function.surjective_id
  obtain ⟨ψ', hψ'⟩ := hV (hM.tensorProduct hL') (hN.tensorProduct hL') π' hπ'
    (tensorHomAdjunction P φ)
  refine ⟨(tensorHomAdjunction P).symm ψ', (tensorHomAdjunction P).injective ?_⟩
  rw [tensorHomAdjunction_comp, LinearEquiv.apply_symm_apply, hψ']

omit [CharZero K] in
/-- `tensorDualEquivHom` on pure tensors: `n ⊗ f ↦ (l ↦ f(l) n)`. -/
theorem tensorDualEquivHom_tmul (n : N) (f : Module.Dual K L) (l : L) :
    tensorDualEquivHom P N L (n ⊗ₜ f) l = f l • n := by
  simp [tensorDualEquivHom]

end Tensor

section Existence

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

/-- The projective module `M(λ + nρ) ⊗ L(nρ)^*` of Humphreys' proof of Theorem 3.8 (GSM 94). -/
abbrev projectiveCoverAmbient (Λ : Dual K H) (n : ℕ) : Type _ :=
  VermaModule P (Λ + (n : K) • P.rho) ⊗[K] Module.Dual K (IrreducibleModule P ((n : K) • P.rho))

omit [DecidableEq ι] [CharZero K] [IsAlgClosed K] [FiniteDimensional K H] in
lemma isDominantIntegral_nsmul_rho (n : ℕ) : P.IsDominantIntegral ((n : K) • P.rho) :=
  fun i ↦ ⟨n, by simp⟩

include hA in
omit [IsAlgClosed K] in
/-- `L(nρ)^*` lies in `𝒪` (it is `≅ L(nρ')` for a dominant integral `nρ'`). -/
theorem isCategoryO_dual_irreducible_nsmul_rho (n : ℕ) :
    IsCategoryO P (Module.Dual K (IrreducibleModule P ((n : K) • P.rho))) := by
  obtain ⟨z, hz, hzν, ⟨eν⟩⟩ := IrreducibleModule.exists_equiv_dual P hA
    (isDominantIntegral_nsmul_rho P n)
  exact IsCategoryO.of_equiv (IrreducibleModule.isCategoryO P _) eν.symm

include hA in
omit [IsAlgClosed K] in
theorem isCategoryO_projectiveCoverAmbient (Λ : Dual K H) (n : ℕ) :
    IsCategoryO P (projectiveCoverAmbient P Λ n) :=
  (VermaModule.isCategoryO P _).tensorProduct (isCategoryO_dual_irreducible_nsmul_rho P hA n)

include hA in
omit [IsAlgClosed K] in
/-- A surjection `M(λ + nρ) ⊗ L(nρ)^* → M(λ)`: the adjoint of the primitive vector
`v_λ ⊗ ξ` of `M(λ) ⊗ L(nρ)^{**}`, `ξ` the evaluation at the highest weight vector of `L(nρ)`
(Humphreys, GSM 94, Remark 3.6 and proof of Theorem 3.8). -/
theorem exists_surjective_projectiveCoverAmbient (Λ : Dual K H) (n : ℕ) :
    ∃ π : projectiveCoverAmbient P Λ n →ₗ⁅K,𝔤⁆ VermaModule P Λ, Function.Surjective π := by
  set ν : Dual K H := (n : K) • P.rho
  have := IrreducibleModule.finiteDimensional (P := P) hA (isDominantIntegral_nsmul_rho P n)
  set L := IrreducibleModule P ν
  set ξ : Module.Dual K (Module.Dual K L) :=
    LieModule.evalEquiv (L := 𝔤) (IrreducibleModule.hwv P ν)
  have hξw : ξ ∈ weightSpaceOfMap (Module.Dual K (Module.Dual K L)) (h P) ν :=
    map_mem_weightSpaceOfMap P (LieModule.evalEquiv (L := 𝔤) (M := L)).toLieModuleHom
      (IrreducibleModule.hwv_mem_weightSpace P ν)
  have hξe : ∀ i, ⁅e P i, ξ⁆ = 0 := by
    intro i
    have h1 : ⁅e P i, IrreducibleModule.hwv P ν⁆ = 0 := by
      rw [IrreducibleModule.hwv, ← LieModuleHom.map_lie, VermaModule.lie_e_hwv, map_zero]
    have h2 := (LieModule.evalEquiv (K := K) (L := 𝔤) (M := L)).toLieModuleHom.map_lie (e P i)
      (IrreducibleModule.hwv P ν)
    rw [h1, map_zero] at h2
    exact h2.symm
  set x := VermaModule.hwv P Λ ⊗ₜ[K] ξ
  have hx : x ∈ primitiveVectors P (VermaModule P Λ ⊗[K] Module.Dual K (Module.Dual K L))
      (Λ + ν) := by
    refine mem_primitiveVectors.mpr ⟨tmul_mem_weightSpaceOfMap P
      (VermaModule.hwv_mem_weightSpace P Λ) hξw, fun i ↦ ?_⟩
    rw [TensorProduct.LieModule.lie_tmul_right, VermaModule.lie_e_hwv, hξe, zero_tmul,
      tmul_zero, add_zero]
  set ψ := (homEquiv P _ (Λ + ν)).symm ⟨x, hx⟩
  have hψ : ψ (VermaModule.hwv P (Λ + ν)) = x :=
    congrArg Subtype.val ((homEquiv P _ (Λ + ν)).apply_symm_apply ⟨x, hx⟩)
  set φ := (tensorHomAdjunction P (M := VermaModule P (Λ + ν)) (L := Module.Dual K L)).symm ψ
  refine ⟨φ, ?_⟩
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K (IrreducibleModule.hwv_ne_zero P ν)
  have hφ : φ (VermaModule.hwv P (Λ + ν) ⊗ₜ f) = VermaModule.hwv P Λ := by
    rw [← tensorDualEquivHom_tensorHomAdjunction, LinearEquiv.apply_symm_apply, hψ,
      tensorDualEquivHom_tmul]
    simp [ξ, hf]
  rw [← LieModuleHom.range_eq_top]
  exact VermaModule.eq_top_of_hwv_mem P Λ ⟨_, hφ⟩

include hA in
/-- **Enough projectives for Verma modules** (Humphreys, GSM 94, proof of Theorem 3.8): in finite
type over an algebraically closed field of characteristic zero, every Verma module `M(λ)` is a
quotient of the projective module `M(λ + nρ) ⊗ L(nρ)^*` in `𝒪`, for suitable `n ∈ ℕ`. -/
theorem exists_isProjectiveO_surjective_verma (Λ : Dual K H) :
    ∃ n : ℕ, IsCategoryO P (projectiveCoverAmbient P Λ n) ∧
      IsProjectiveO.{w} P (projectiveCoverAmbient P Λ n) ∧
      ∃ π : projectiveCoverAmbient P Λ n →ₗ⁅K,𝔤⁆ VermaModule P Λ, Function.Surjective π := by
  obtain ⟨n, hn⟩ := exists_forall_add_nsmul_rho P hA Λ
  refine ⟨n, isCategoryO_projectiveCoverAmbient P hA Λ n, ?_,
    exists_surjective_projectiveCoverAmbient P hA Λ n⟩
  have := IrreducibleModule.finiteDimensional (P := P) hA (isDominantIntegral_nsmul_rho P n)
  exact IsProjectiveO.tensorProduct P (VermaModule.isProjectiveO_of_forall P hA hn)
    (IsCategoryO.of_equiv (IrreducibleModule.isCategoryO P _) LieModule.evalEquiv)

end Existence

end Matrix.Realization.KacMoodyAlgebra
