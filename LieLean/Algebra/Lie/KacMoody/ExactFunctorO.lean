/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.DominantVermaTensor
import LieLean.Algebra.Lie.KacMoody.TranslationMultiplicity
import LieLean.LinearAlgebra.Matrix.Cartan.IntegralWeylGroupAntidominant

/-!
# Exact functors on category `𝒪` and blocks

Let `F` be an exact functor on `𝒪`. All that Humphreys' Proposition 10.1 uses about `F` is the
class of modules it kills: this class contains the zero module, is closed under isomorphisms,
and for a submodule `N` of `M ∈ 𝒪`, `F M = 0` iff `F N = 0` and `F (M / N) = 0` (exactness of
`F` on `0 → N → M → M / N → 0`). We call a class of modules with these three properties an
`IsSerreClassO` and prove Proposition 10.1 for it. The modules killed by a translation functor
`pr_{χ₂}(pr_{χ₁}(−) ⊗ Z)` form such a class (`isSerreClassO_centralTranslation`).

A module `M` lies in the block of the dominant weight `λ` when all its composition factors are
`L(w·λ)` with `w ∈ W_[λ]` (Humphreys, GSM 94, Theorem 4.9).

## Main results

* `IsDominant.exists_sub_weylDot_eq_rootOf`: for `λ` dominant, `w·λ ≤ λ` for all `w ∈ W_[λ]`
  (Humphreys, GSM 94, Prop. 3.5, dominant form).
* `VermaModule.exists_injective_weylDot_of_isDominant`: **Humphreys, GSM 94, §5.1, Example**:
  for `λ` dominant and `w ∈ W_[λ]` there is an embedding `M(w·λ) ↪ M(λ)`; hence
  `[M(λ) : L(w·λ)] ≠ 0` (`VermaModule.multiplicity_weylDot_ne_zero_of_isDominant`).
* `IsCategoryO.exists_equiv_of_isAtom`: a simple submodule of a module in `𝒪` is some `L(ξ)`.
* **Humphreys, GSM 94, Proposition 10.1**, for a class `S` of modules killed by an exact
  functor (`S M` standing for `F M = 0`):
  - (a) `IsSerreClassO.of_forall_multiplicity`: if `F L(μ) = 0` for every composition factor
    `L(μ)` of a finitely generated `M ∈ 𝒪`, then `F M = 0`;
  - (b) `IsSerreClassO.irreducibleModule_of_multiplicity_ne_zero`: if `F M = 0`, then
    `F L(μ) = 0` for every composition factor `L(μ)` of `M`;
  - (c) `IsSerreClassO.of_verma_of_isDominant`: if `λ` is dominant and `F M(λ) = 0`, then
    `F M = 0` for every finitely generated `M` in the block of `λ`.

Parts (a) and (c) assume finite type, a finite-dimensional Cartan subalgebra and an algebraically
closed field of characteristic zero (they use finite length, Theorem 1.11); part (b) only
characteristic zero. Humphreys works over `ℂ`.

## Proof notes

Part (b) follows Humphreys. Humphreys proves (a) by induction on the length of `M`; we induct on
the quotients `M / N`, ordered by reverse inclusion of `N` (the submodules of `M` satisfy the
ascending chain condition), and split off a simple submodule of `M / N` (they satisfy the
descending chain condition). For (c), Humphreys refers to the Example of §5.1 (Prop. 4.3 for
nonintegral weights); we prove it by raising a non-dominant `μ ∈ W_[λ]·λ` along a positive root
`β` with `⟨μ + ρ, β^∨⟩ ∈ ℤ_{<0}`, using Theorem 4.6 (`VermaModule.exists_injective_reflectionOf`)
and the dominant form of Prop. 3.5 to see that the process ends at `λ`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category `𝒪`*,
  GSM 94, §3.5, §4.9, §5.1, §10.1.
-/

noncomputable section

open Module LieModule
open scoped TensorProduct

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

/-! ### Dominant Verma modules -/

section Dominant

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

/-- **Humphreys, GSM 94, Prop. 3.5, dominant form.** If `λ` is dominant, then `w·λ ≤ λ` for every
`w ∈ W_[λ]`. -/
theorem IsDominant.exists_sub_weylDot_eq_rootOf {lam : Dual K H}
    (hlam : P.IsDominant hA.isGeneralizedCartan lam) {w : P.weylGroup hA.isGeneralizedCartan}
    (hw : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam) :
    ∃ k : ι → ℤ, 0 ≤ k ∧ lam - P.weylDot hA.isGeneralizedCartan w lam = P.rootOf k := by
  have hb : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hA.isGeneralizedCartan (-(lam + P.rho)) v i = n → n ≤ 0 := by
    intro v i hv n hn
    rw [corootPairing_neg, neg_eq_iff_eq_neg] at hn
    have := hlam v i hv (-n) (by rw [hn]; push_cast; ring)
    omega
  have hw' : w ∈ P.integralWeylGroup hA.isGeneralizedCartan (-(lam + P.rho)) := by
    rw [P.integralWeylGroup_eq_of_integral hA.isGeneralizedCartan (μ' := lam + P.rho)
      fun j ↦ ⟨-1, by simp⟩] at hw
    rw [mem_integralWeylGroup, map_neg, show -(w : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) -
      -(lam + P.rho) = -((w : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) - (lam + P.rho)) by abel]
    exact neg_mem hw
  obtain ⟨k, hk, hwk⟩ := exists_nonneg_apply_sub_eq_rootOf hA hb hw'
  refine ⟨k, hk, ?_⟩
  rw [← hwk, weylDot, map_neg]
  abel

variable [FiniteDimensional K H]

omit [CharZero K] [FiniteDimensional K H] in
/-- A weight `μ` that is not dominant can be raised: there are a positive root `β = v αᵢ` and
`c > 0` with `⟨μ + ρ, β^∨⟩ = -c`; then `s_β (μ + ρ) = μ + ρ + c β` and
`⟨μ + cβ + ρ, β^∨⟩ = c`. -/
theorem exists_raise_of_not_isDominant {μ : Dual K H}
    (hμ : ¬P.IsDominant hA.isGeneralizedCartan μ) :
    ∃ (v : P.weylGroup hA.isGeneralizedCartan) (i : ι) (l : ι → ℤ) (c : ℕ),
      0 ≤ l ∧ (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) = P.rootOf l ∧ 0 < c ∧
      P.IsPosRoot hA.isGeneralizedCartan v i ∧
      P.corootPairing hA.isGeneralizedCartan
        (μ + c • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) + P.rho) v i = c ∧
      (P.reflectionOf hA.isGeneralizedCartan v i : Dual K H ≃ₗ[K] Dual K H) (μ + P.rho) =
        μ + c • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) + P.rho := by
  simp only [IsDominant, not_forall, not_le] at hμ
  obtain ⟨v, i, hv, m, hm, hm0⟩ := hμ
  obtain ⟨l, hl, hvl⟩ := hv
  refine ⟨v, i, l, (-m).toNat, hl, hvl, by omega, ⟨l, hl, hvl⟩, ?_, ?_⟩
  · have hcm : (((-m).toNat : ℕ) : K) = -(m : K) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]
    have hββ : P.corootPairing hA.isGeneralizedCartan
        ((v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) v i = 2 := by
      rw [corootPairing, inv_apply_apply, P.root_coroot_self hA.isGeneralizedCartan]
    rw [add_right_comm, corootPairing_add, hm, ← Nat.cast_smul_eq_nsmul K, corootPairing_smul,
      hββ, hcm]
    ring
  · rw [reflectionOf_apply', hm, ← Nat.cast_smul_eq_nsmul K]
    have hcm : (((-m).toNat : ℕ) : K) = -(m : K) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]
    rw [hcm, neg_smul]
    abel

/-- **Humphreys, GSM 94, §5.1, Example** (Prop. 4.3 for dominant, possibly nonintegral, weights):
if `λ` is dominant and `w ∈ W_[λ]`, then `M(w·λ)` embeds in `M(λ)`. -/
theorem VermaModule.exists_injective_weylDot_of_isDominant {lam : Dual K H}
    (hlam : P.IsDominant hA.isGeneralizedCartan lam) {w : P.weylGroup hA.isGeneralizedCartan}
    (hw : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam) :
    ∃ φ : VermaModule P (P.weylDot hA.isGeneralizedCartan w lam) →ₗ⁅K,𝔤⁆ VermaModule P lam,
      Function.Injective φ := by
  suffices H : ∀ n : ℕ, ∀ w : P.weylGroup hA.isGeneralizedCartan,
      w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam → ∀ k : ι → ℤ, 0 ≤ k →
      lam - P.weylDot hA.isGeneralizedCartan w lam = P.rootOf k → ∑ i, k i = n →
      ∃ φ : VermaModule P (P.weylDot hA.isGeneralizedCartan w lam) →ₗ⁅K,𝔤⁆ VermaModule P lam,
        Function.Injective φ by
    obtain ⟨k, hk, hwk⟩ := IsDominant.exists_sub_weylDot_eq_rootOf P hA hlam hw
    exact H (∑ i, k i).toNat w hw k hk hwk
      (Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ ↦ hk i)).symm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw k hk hwk hn
  by_cases hdom : P.IsDominant hA.isGeneralizedCartan (P.weylDot hA.isGeneralizedCartan w lam)
  · -- `w·λ` is dominant: then also `λ ≤ w·λ`, so `w·λ = λ`
    have hint : ∀ j, ∃ z : ℤ,
        (P.weylDot hA.isGeneralizedCartan w lam - lam) (P.coroot j) = z := by
      have h := P.exists_int_of_mem_rootLattice (P.rootOf_mem_rootLattice (-k))
      rwa [map_neg, ← hwk, neg_sub] at h
    have hw' : w⁻¹ ∈ P.integralWeylGroup hA.isGeneralizedCartan
        (P.weylDot hA.isGeneralizedCartan w lam) := by
      rw [P.integralWeylGroup_eq_of_integral hA.isGeneralizedCartan hint]
      exact inv_mem hw
    obtain ⟨l, hl, hwl⟩ := IsDominant.exists_sub_weylDot_eq_rootOf P hA hdom hw'
    rw [← weylDot_mul, inv_mul_cancel, weylDot_one] at hwl
    have hkl : k + l = 0 := P.rootOf_injective (by rw [map_add, ← hwk, ← hwl, map_zero]; abel)
    have hk0 : k = 0 := by
      ext i
      have h1 := congr_fun hkl i
      have h2 := hk i
      have h3 := hl i
      simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 h3 ⊢
      omega
    have heq : P.weylDot hA.isGeneralizedCartan w lam = lam := by
      rw [hk0, map_zero, sub_eq_zero] at hwk
      exact hwk.symm
    rw [heq]
    exact ⟨LieModuleHom.id, Function.injective_id⟩
  · -- otherwise raise `w·λ` along a positive root `β` with `⟨w·λ + ρ, β^∨⟩ ∈ ℤ_{<0}`
    obtain ⟨v, i, l, c, hl, hvl, hc, hv, hpair, hrefl⟩ :=
      exists_raise_of_not_isDominant P hA hdom
    -- the raised weight is `(s_β w)·λ = w·λ + c β`
    have hw'μ : P.weylDot hA.isGeneralizedCartan (P.reflectionOf hA.isGeneralizedCartan v i * w)
        lam = P.weylDot hA.isGeneralizedCartan w lam + P.rootOf (c • l) := by
      rw [weylDot_mul]
      change (P.reflectionOf hA.isGeneralizedCartan v i : Dual K H ≃ₗ[K] Dual K H)
        (P.weylDot hA.isGeneralizedCartan w lam + P.rho) - P.rho = _
      rw [hrefl, add_sub_cancel_right, hvl, map_nsmul]
    have hw'mem : P.reflectionOf hA.isGeneralizedCartan v i * w ∈
        P.integralWeylGroup hA.isGeneralizedCartan lam := by
      rw [mem_integralWeylGroup_iff_dot, ← weylDot, hw'μ, add_sub_right_comm, ← neg_sub, hwk,
        ← map_neg, ← map_add]
      exact P.rootOf_mem_rootLattice _
    obtain ⟨k', hk', hwk'⟩ := IsDominant.exists_sub_weylDot_eq_rootOf P hA hlam hw'mem
    -- the height drops
    have hkk' : k = k' + c • l := by
      refine P.rootOf_injective ?_
      rw [map_add, ← hwk', hw'μ, ← hwk]
      abel
    have hl0 : l ≠ 0 := by
      rintro rfl
      have h0 : (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) = 0 := by rw [hvl, map_zero]
      have h2 := P.root_coroot_self hA.isGeneralizedCartan i
      rw [LinearEquiv.map_eq_zero_iff] at h0
      rw [h0, LinearMap.zero_apply] at h2
      exact two_ne_zero h2.symm
    have hlpos : 0 < ∑ j, l j := by
      obtain ⟨j, hj⟩ : ∃ j, l j ≠ 0 := by
        by_contra h
        push Not at h
        exact hl0 (funext h)
      exact lt_of_lt_of_le (lt_of_le_of_ne (hl j) (Ne.symm hj))
        (Finset.single_le_sum (fun j _ ↦ hl j) (Finset.mem_univ j))
    have hsum : ∑ j, k j = ∑ j, k' j + c * ∑ j, l j := by
      rw [hkk', Finset.mul_sum, ← Finset.sum_add_distrib]
      simp [nsmul_eq_mul]
    have hk'n : ∑ j, k' j = ((∑ j, k' j).toNat : ℤ) :=
      (Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ ↦ hk' j)).symm
    obtain ⟨φ₂, hφ₂⟩ := ih (∑ j, k' j).toNat (by
      have : (c : ℤ) * ∑ j, l j > 0 := mul_pos (by exact_mod_cast hc) hlpos
      omega) _ hw'mem k' hk' hwk' hk'n
    -- Theorem 4.6: `M(μ) ↪ M(μ + cβ)`
    have h46 := VermaModule.exists_injective_reflectionOf P hA hv hpair
    rw [add_sub_cancel_right, hvl, ← map_nsmul, ← hw'μ] at h46
    obtain ⟨φ₁, hφ₁⟩ := h46
    exact ⟨φ₂.comp φ₁, hφ₂.comp hφ₁⟩

/-- `[M(λ) : L(w·λ)] ≠ 0` for `λ` dominant and `w ∈ W_[λ]` (Humphreys, GSM 94, §5.1,
Example). -/
theorem VermaModule.multiplicity_weylDot_ne_zero_of_isDominant {lam : Dual K H}
    (hlam : P.IsDominant hA.isGeneralizedCartan lam) {w : P.weylGroup hA.isGeneralizedCartan}
    (hw : w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam) :
    (isCategoryO P lam).multiplicity (P.weylDot hA.isGeneralizedCartan w lam) ≠ 0 := by
  obtain ⟨φ, hφ⟩ := VermaModule.exists_injective_weylDot_of_isDominant P hA hlam hw
  refine multiplicity_ne_zero_of_hom_ne_zero P (φ := φ) fun h ↦ hwv_ne_zero P _ (hφ ?_)
  rw [h, map_zero, _root_.zero_apply]

end Dominant

/-! ### Classes of modules killed by an exact functor -/

section Serre

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝔤" => KacMoodyAlgebra P

/-- The class `S` of modules killed by an exact functor `F` on `𝒪` (`S M` stands for `F M = 0`):
it contains the zero modules, it is closed under isomorphisms, and for a submodule `N` of
`M ∈ 𝒪`, `S M` holds iff `S N` and `S (M / N)` hold (exactness of `F` on
`0 → N → M → M / N → 0`). The modules live in the universe of the Verma modules. -/
structure IsSerreClassO
    (S : ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
      [LieModule K 𝔤 M], Prop) : Prop where
  of_subsingleton (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M] [Subsingleton M] : S M
  of_equiv {M N : Type (max u₁ u₂)} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M] [AddCommGroup N] [Module K N] [LieRingModule 𝔤 N] [LieModule K 𝔤 N]
    (e : M ≃ₗ⁅K,𝔤⁆ N) : S M → S N
  iff {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M] [LieRingModule 𝔤 M]
    [LieModule K 𝔤 M] (hM : IsCategoryO P M) (N : LieSubmodule K 𝔤 M) :
    S M ↔ S N ∧ S (M ⧸ N)

namespace IsSerreClassO

variable {P} {S : ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M]
  [LieRingModule P.KacMoodyAlgebra M] [LieModule K P.KacMoodyAlgebra M], Prop}
  (hS : IsSerreClassO P S) {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M]
  [LieRingModule P.KacMoodyAlgebra M] [LieModule K P.KacMoodyAlgebra M]

include hS

/-- **Humphreys, GSM 94, Proposition 10.1 (b)**: if an exact functor `F` kills `M ∈ 𝒪`, it kills
every composition factor `L(μ)` of `M`. -/
theorem irreducibleModule_of_multiplicity_ne_zero (hM : IsCategoryO P M) (hSM : S M)
    {μ : Dual K H} (hμ : hM.multiplicity μ ≠ 0) : S (IrreducibleModule P μ) := by
  obtain ⟨l, hl⟩ := hM.exists_isLocalCompositionSeries μ
  rw [hM.multiplicity_ne_zero_iff (mem_cone_self μ) hl] at hμ
  obtain ⟨N₁, N₂, -, h₁₂, -, -, ⟨e⟩⟩ := hl.exists_of_mem_factorWeights hμ
  have h₂ : S N₂ := ((hS.iff hM N₂).mp hSM).1
  have hq : S (N₁.Subquotient N₂) :=
    ((hS.iff (hM.lieSubmodule N₂) (N₁.comap N₂.incl)).mp h₂).2
  exact hS.of_equiv e hq

end IsSerreClassO

section FiniteType

variable [IsAlgClosed K] [FiniteDimensional K H] (hA : A.IsFiniteCartan)

include hA in
/-- In finite type, a simple submodule `B` of a module `Q` in `𝒪` is isomorphic to some
`L(ξ)`. -/
theorem IsCategoryO.exists_equiv_of_isAtom {Q : Type*} [AddCommGroup Q] [Module K Q]
    [LieRingModule P.KacMoodyAlgebra Q] [LieModule K P.KacMoodyAlgebra Q] (hQ : IsCategoryO P Q)
    {B : LieSubmodule K P.KacMoodyAlgebra Q} (hB : IsAtom B) :
    ∃ ξ : Dual K H, Nonempty (B ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P ξ) := by
  classical
  obtain ⟨b, hb, hb0⟩ : ∃ b ∈ B, b ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hB.1 (eq_bot_iff.mpr fun b hb ↦ (LieSubmodule.mem_bot b).mpr (hc b hb))
  -- a proper submodule of `B` is zero
  have hsub : ∀ T : LieSubmodule K P.KacMoodyAlgebra B, T < ⊤ → T = ⊥ := by
    intro T hT
    have h := hB.2 _ (LieSubmodule.map_incl_lt_iff_lt_top.mpr hT)
    rw [← LieSubmodule.map_bot (f := B.incl)] at h
    exact LieSubmodule.map_injective_of_injective (LieSubmodule.injective_incl B) h
  have hspan : LieSubmodule.lieSpan K P.KacMoodyAlgebra
      (({⟨b, hb⟩} : Finset B) : Set B) = ⊤ := by
    by_contra hne
    have h := hsub _ (lt_top_iff_ne_top.mpr hne)
    have hmem : (⟨b, hb⟩ : B) ∈ LieSubmodule.lieSpan K P.KacMoodyAlgebra
        (({⟨b, hb⟩} : Finset B) : Set B) :=
      LieSubmodule.subset_lieSpan (by simp)
    rw [h, LieSubmodule.mem_bot] at hmem
    exact hb0 (congrArg Subtype.val hmem)
  have : Nontrivial B := ⟨⟨⟨b, hb⟩, 0, fun h ↦ hb0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨ξ, φ, hφ⟩ := (hQ.lieSubmodule B).exists_surjective_irreducibleModule P hA hspan
  have hker : φ.ker = ⊥ := by
    refine hsub _ (lt_top_iff_ne_top.mpr fun htop ↦ ?_)
    obtain ⟨x, hx⟩ := hφ (IrreducibleModule.hwv P ξ)
    have : x ∈ φ.ker := htop ▸ LieSubmodule.mem_top x
    rw [LieModuleHom.mem_ker, hx] at this
    exact IrreducibleModule.hwv_ne_zero P ξ this
  exact ⟨ξ, ⟨LieModuleEquiv.ofBijective φ ⟨(LieModuleHom.ker_eq_bot φ).mp hker, hφ⟩⟩⟩

namespace IsSerreClassO

variable {P} {S : ∀ (M : Type (max u₁ u₂)) [AddCommGroup M] [Module K M]
  [LieRingModule P.KacMoodyAlgebra M] [LieModule K P.KacMoodyAlgebra M], Prop}
  (hS : IsSerreClassO P S) {M : Type (max u₁ u₂)} [AddCommGroup M] [Module K M]
  [LieRingModule P.KacMoodyAlgebra M] [LieModule K P.KacMoodyAlgebra M]

include hS hA

/-- **Humphreys, GSM 94, Proposition 10.1 (a)**: if an exact functor `F` kills every composition
factor `L(μ)` of a finitely generated `M ∈ 𝒪`, then `F M = 0`. Humphreys inducts on the length
of `M`; we induct on the quotients `M / N` (reverse inclusion of `N`) and split off a simple
submodule of `M / N`. Humphreys works over `ℂ`. -/
theorem of_forall_multiplicity (hM : IsCategoryO P M) {s : Finset M}
    (hs : LieSubmodule.lieSpan K P.KacMoodyAlgebra (s : Set M) = ⊤)
    (h : ∀ μ, hM.multiplicity μ ≠ 0 → S (IrreducibleModule P μ)) : S M := by
  classical
  have hwf := hM.wellFoundedGT_lieSubmodule P hA hs
  suffices H : ∀ N : LieSubmodule K P.KacMoodyAlgebra M, S (M ⧸ N) by
    obtain ⟨e⟩ := LieSubmodule.Quotient.nonempty_lieModuleEquiv_of_surjective ⊥
      (LieModuleHom.id : M →ₗ⁅K,P.KacMoodyAlgebra⁆ M) Function.surjective_id
      ((LieModuleHom.ker_eq_bot _).mpr Function.injective_id)
    exact hS.of_equiv e (H ⊥)
  intro N
  induction N using WellFoundedGT.induction with
  | _ N ih =>
  set q := LieSubmodule.Quotient.mk' N
  have hq : Function.Surjective q := LieSubmodule.Quotient.surjective_mk' N
  have hQ : IsCategoryO P (M ⧸ N) := hM.quotient N
  by_cases hN : N = ⊤
  · have : Subsingleton (M ⧸ N) := ⟨fun x y ↦ by
      obtain ⟨x, rfl⟩ := hq x
      obtain ⟨y, rfl⟩ := hq y
      rw [← sub_eq_zero, ← map_sub, LieSubmodule.Quotient.mk_eq_zero, hN]
      exact LieSubmodule.mem_top _⟩
    exact hS.of_subsingleton _
  -- `M / N` is artinian, so it has a simple submodule `B`
  have hsQ : LieSubmodule.lieSpan K P.KacMoodyAlgebra
      ((s.image q : Finset (M ⧸ N)) : Set (M ⧸ N)) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := hq y
    have hle : LieSubmodule.lieSpan K P.KacMoodyAlgebra (s : Set M) ≤
        LieSubmodule.comap q (LieSubmodule.lieSpan K P.KacMoodyAlgebra
          ((s.image q : Finset (M ⧸ N)) : Set (M ⧸ N))) := by
      rw [LieSubmodule.lieSpan_le]
      intro x hx
      exact LieSubmodule.subset_lieSpan (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
    exact hle (hs ▸ LieSubmodule.mem_top x)
  have hwfQ := hQ.wellFoundedLT_lieSubmodule P hA hsQ
  have htop : (⊤ : LieSubmodule K P.KacMoodyAlgebra (M ⧸ N)) ≠ ⊥ := by
    intro h0
    obtain ⟨x, hx⟩ : ∃ x : M, x ∉ N := by
      by_contra hc
      push Not at hc
      exact hN (eq_top_iff.mpr fun x _ ↦ hc x)
    have : q x ∈ (⊥ : LieSubmodule K P.KacMoodyAlgebra (M ⧸ N)) :=
      h0 ▸ LieSubmodule.mem_top _
    rw [LieSubmodule.mem_bot] at this
    exact hx ((LieSubmodule.Quotient.mk_eq_zero _).mp this)
  obtain ⟨B, hB, -⟩ := (IsAtomic.eq_bot_or_exists_atom_le
    (⊤ : LieSubmodule K P.KacMoodyAlgebra (M ⧸ N))).resolve_left htop
  obtain ⟨ξ, ⟨e⟩⟩ := hQ.exists_equiv_of_isAtom P hA hB
  -- `(M / N) / B ≅ M / N'` with `N < N'`
  set N' := B.comap q
  have hlt : N < N' := by
    refine lt_of_le_of_ne (fun x hx ↦ ?_) fun hNN ↦ hB.1 (eq_bot_iff.mpr fun y hy ↦ ?_)
    · rw [LieSubmodule.mem_comap, (LieSubmodule.Quotient.mk_eq_zero _).mpr hx]
      exact zero_mem B
    · obtain ⟨x, rfl⟩ := hq y
      have hx : x ∈ N' := hy
      rw [← hNN] at hx
      rw [LieSubmodule.mem_bot]
      exact (LieSubmodule.Quotient.mk_eq_zero _).mpr hx
  obtain ⟨e'⟩ := LieSubmodule.Quotient.nonempty_lieModuleEquiv_of_surjective N'
    ((LieSubmodule.Quotient.mk' B).comp q)
    ((LieSubmodule.Quotient.surjective_mk' B).comp hq) (by
      ext x
      rw [LieModuleHom.mem_ker, LieModuleHom.comp_apply]
      exact LieSubmodule.Quotient.mk_eq_zero _)
  -- `L(ξ)` is a composition factor of `M`
  have hmult : hM.multiplicity ξ ≠ 0 := by
    have h₁ := hM.multiplicity_eq_add N ξ
    have h₂ := hQ.multiplicity_eq_add B ξ
    have h₃ := IsCategoryO.multiplicity_congr (hQ.lieSubmodule B)
      (IrreducibleModule.isCategoryO P ξ) e ξ
    simp only [IrreducibleModule.multiplicity_eq, ↓reduceIte] at h₃
    omega
  exact (hS.iff hQ B).mpr ⟨hS.of_equiv e.symm (h ξ hmult), hS.of_equiv e' (ih N' hlt)⟩

/-- **Humphreys, GSM 94, Proposition 10.1 (c)**: if `λ` is dominant and an exact functor `F`
kills `M(λ)`, then `F` kills every finitely generated `M` in the block of `λ`, i.e. every `M ∈ 𝒪`
whose composition factors are `L(w·λ)` with `w ∈ W_[λ]` (Theorem 4.9). The input is
`[M(λ) : L(w·λ)] ≠ 0` (§5.1, Example). Humphreys works over `ℂ`. -/
theorem of_verma_of_isDominant {lam : Dual K H} (hlam : P.IsDominant hA.isGeneralizedCartan lam)
    (hSV : S (VermaModule P lam)) (hM : IsCategoryO P M) {s : Finset M}
    (hs : LieSubmodule.lieSpan K P.KacMoodyAlgebra (s : Set M) = ⊤)
    (hblock : ∀ μ, hM.multiplicity μ ≠ 0 →
      ∃ w ∈ P.integralWeylGroup hA.isGeneralizedCartan lam,
        μ = P.weylDot hA.isGeneralizedCartan w lam) : S M :=
  hS.of_forall_multiplicity hA hM hs fun μ hμ ↦ by
    obtain ⟨w, hw, rfl⟩ := hblock μ hμ
    exact hS.irreducibleModule_of_multiplicity_ne_zero (VermaModule.isCategoryO P lam) hSV
      (VermaModule.multiplicity_weylDot_ne_zero_of_isDominant P hA hlam hw)

end IsSerreClassO

end FiniteType

section Translation

variable [IsAlgClosed K] {Z : Type*} [AddCommGroup Z] [Module K Z]
  [LieRingModule P.KacMoodyAlgebra Z] [LieModule K P.KacMoodyAlgebra Z]

/-- The modules killed by a translation functor `T = pr_{χ₂}(pr_{χ₁}(−) ⊗ Z)` with `Z ∈ 𝒪` form an
`IsSerreClassO`: `T` is exact (`centralTranslationMap_shortExact`). So Proposition 10.1 applies
to `T`. -/
theorem isSerreClassO_centralTranslation (hZ : IsCategoryO P Z)
    (χ₁ χ₂ : Subalgebra.center K (UniversalEnvelopingAlgebra K P.KacMoodyAlgebra) →ₐ[K] K) :
    IsSerreClassO P fun M _ _ _ _ ↦ Subsingleton (centralTranslation P Z χ₁ χ₂ M) where
  of_subsingleton M _ _ _ _ _ := ⟨fun x y ↦ by
    have h0 : ∀ t : centralBlock P M χ₁ ⊗[K] Z, t = 0 := fun t ↦ by
      induction t using TensorProduct.inductionOn with
      | tmul a z =>
        rw [show a = 0 from Subtype.ext (Subsingleton.elim _ _), TensorProduct.zero_tmul]
      | add a b ha hb => rw [ha, hb, add_zero]
    exact Subtype.ext ((h0 x.val).trans (h0 y.val).symm)⟩
  of_equiv {M N} _ _ _ _ _ _ _ _ e hM := ⟨fun x y ↦ by
    have hc : ∀ t, centralTranslationMap P Z χ₁ χ₂ e.toLieModuleHom
        (centralTranslationMap P Z χ₁ χ₂ e.symm.toLieModuleHom t) = t := fun t ↦ by
      rw [← LieModuleHom.comp_apply, ← centralTranslationMap_comp]
      have : e.toLieModuleHom.comp e.symm.toLieModuleHom = LieModuleHom.id := by
        ext; simp
      rw [this, centralTranslationMap_id, LieModuleHom.id_apply]
    rw [← hc x, ← hc y]
    congr 1
    exact Subsingleton.elim _ _⟩
  iff {M} _ _ _ _ hM N := by
    obtain ⟨hf, hex, hg⟩ := centralTranslationMap_shortExact P Z hM hZ N.incl
      (LieSubmodule.Quotient.mk' N) (LieSubmodule.injective_incl N)
      (by rw [LieSubmodule.Quotient.mk'_ker, LieSubmodule.range_incl])
      (LieSubmodule.Quotient.surjective_mk' N) χ₁ χ₂
    constructor
    · intro h
      exact ⟨hf.subsingleton, hg.subsingleton⟩
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun x y ↦ ?_⟩
      have hx : x ∈ (centralTranslationMap P Z χ₁ χ₂ (LieSubmodule.Quotient.mk' N)).ker := by
        rw [LieModuleHom.mem_ker]
        exact Subsingleton.elim _ _
      have hy : y ∈ (centralTranslationMap P Z χ₁ χ₂ (LieSubmodule.Quotient.mk' N)).ker := by
        rw [LieModuleHom.mem_ker]
        exact Subsingleton.elim _ _
      rw [hex, LieModuleHom.mem_range] at hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      rw [Subsingleton.elim a b]

end Translation

end Serre

end Matrix.Realization.KacMoodyAlgebra
