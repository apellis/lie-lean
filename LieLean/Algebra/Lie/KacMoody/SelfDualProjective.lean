/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationProjective
import LieLean.Algebra.Lie.KacMoody.TranslationComposite
import LieLean.Algebra.Lie.KacMoody.TranslationWallMultiplicity
import LieLean.Algebra.Lie.KacMoody.TranslationSelfDual

/-!
# Self-dual projectives

Humphreys, GSM 94, Theorem 7.16 and Theorem 4.10: for `λ` antidominant, `P(λ) ≅ P(λ)^∨`, and every
standard filtration of `P(λ)` contains each `M(w·λ)`, `w ∈ W_[λ]`, exactly once; equivalently
`[M(w·λ) : L(λ)] = 1`.

Here this is proved whenever there is a weight `μ` with `λ - μ` integral such that `μ + ρ` is
orthogonal to every root `β` with `⟨λ + ρ, β^∨⟩ ∈ ℤ`. Then `P(λ) ≅ T_μ^λ M(μ)`, with `M(μ)` simple
and projective. Such a `μ` exists for integral `λ` (`μ = -ρ`, Theorem 4.10), and more generally
when the coroots of the integral roots of `λ` span a saturated sublattice of the coroot lattice.
For arbitrary antidominant `λ`, Humphreys follows Irving's argument with wall-crossing functors;
that general case is not formalized here.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.maxSubmodule_eq_bot_of_isAntidominant`:
  `M(μ)` is simple for antidominant `μ` (one direction of Humphreys, Theorem 4.8).
* `Matrix.Realization.KacMoodyAlgebra.nonempty_equiv_projectiveCover_of_singular`:
  `P(λ) ≅ T_μ^λ M(μ)`.
* `Matrix.Realization.KacMoodyAlgebra.nonempty_equiv_restrictedDual_projectiveCover_of_singular`:
  `P(λ) ≅ P(λ)^∨` (Theorem 7.16 (a)).
* `Matrix.Realization.KacMoodyAlgebra.multiplicity_verma_weylDot_of_singular`,
  `Matrix.Realization.KacMoodyAlgebra.count_projectiveCover_of_singular`: Theorem 7.16 (b).
* `Matrix.Realization.KacMoodyAlgebra.exists_nonempty_equiv_projectiveCover_of_integral`,
  `Matrix.Realization.KacMoodyAlgebra.nonempty_equiv_restrictedDual_projectiveCover_of_integral`,
  `Matrix.Realization.KacMoodyAlgebra.multiplicity_verma_weylDot_of_integral`: Theorem 4.10.

## Proof

`P(λ) ≅ T_μ^λ M(μ)` follows from Proposition 7.13 (`w = 1`), where the weight `x·λ` produced there
is `λ`: `dim Hom(T_μ^λ M(μ), M(y·λ)) = dim Hom(M(μ), T_λ^μ M(y·λ)) = dim End M(μ) = 1` for
`y ∈ W_[λ]` (adjunction, Theorem 7.6 and `y·μ = μ`), so `[M(λ) : L(x·λ)] = 1`, forcing
`x·λ = λ` by antidominance; the same computation with Theorem 3.9 (c) gives (b). Self-duality
follows from `(T M)^∨ ≅ T(M^∨)` (Proposition 7.1) and `M(μ) ≅ L(μ) ≅ L(μ)^∨`. Reconstructed.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §4.10, §7.16.
-/

noncomputable section

open Module LieModule TensorProduct

universe u₁ u₂

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Integral

variable {ι K H : Type*} [Fintype ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)

/-- An integral weight pairs integrally with every real coroot. -/
theorem exists_int_corootPairing_of_integral {x : Dual K H}
    (h : ∀ j, ∃ z : ℤ, x (P.coroot j) = z) (v : P.weylGroup hA) (i : ι) :
    ∃ z : ℤ, P.corootPairing hA x v i = z := by
  obtain ⟨a, ha⟩ := h i
  obtain ⟨b, hb⟩ := P.exists_int_of_mem_rootLattice
    (P.apply_sub_mem_rootLattice_of_integral hA (v⁻¹).2 h) i
  refine ⟨b + a, ?_⟩
  have e : P.corootPairing hA x v i =
      (((v⁻¹ : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H) x - x) (P.coroot i) +
        x (P.coroot i) := by
    simp [Matrix.Realization.corootPairing]
  rw [e, hb, ha]
  push_cast
  ring

end Integral

section Generic

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V X : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V] [AddCommGroup X] [Module K X]
  [LieRingModule P.KacMoodyAlgebra X] [LieModule K P.KacMoodyAlgebra X]

/-- Self-duality is invariant under isomorphism. -/
theorem nonempty_equiv_restrictedDual_of_equiv (he : Nonempty (V ≃ₗ⁅K,P.KacMoodyAlgebra⁆ X))
    (f : X ≃ₗ⁅K,P.KacMoodyAlgebra⁆ restrictedDual P X) :
    Nonempty (V ≃ₗ⁅K,P.KacMoodyAlgebra⁆ restrictedDual P V) :=
  he.map fun e ↦ e.trans (f.trans (restrictedDualEquiv P e))

end Generic

section Main

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [CharZero K] [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

omit [IsAlgClosed K] in
include hA in
/-- **Antidominant Verma modules are simple** (Humphreys, GSM 94, Theorem 4.8, one direction):
if `⟨μ + ρ, β^∨⟩ ∉ ℤ_{>0}` for all positive roots `β`, then `M(μ)` has no nonzero proper
submodule. Proof: a composition factor `L(y)` of `M(μ)` has `y = w·μ ∈ μ - Q₊` (linkage), and
antidominance gives `w·μ ∈ μ + Q₊`. -/
theorem VermaModule.maxSubmodule_eq_bot_of_isAntidominant {μ : Dual K H}
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ) : maxSubmodule P μ = ⊥ := by
  classical
  have hA' := hA.isGeneralizedCartan
  have hM := VermaModule.isCategoryO P μ
  have key : ∀ y, hM.multiplicity y ≠ 0 → y = μ := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := VermaModule.mem_cone_of_multiplicity_ne_zero hy
    have hχ := hM.centralCharacter_eq_of_multiplicity_ne_zero P (centralBlock_verma P μ) hy
    obtain ⟨w, hw, hwy⟩ := (VermaModule.centralCharacter_eq_iff P hA μ _).mp hχ.symm
    have hwint : (⟨w, hw⟩ : P.weylGroup hA') ∈ P.integralWeylGroup hA' μ := by
      rw [P.integralWeylGroup_eq_of_integral hA' (μ' := μ + P.rho) fun j ↦ ⟨-1, by simp⟩,
        mem_integralWeylGroup]
      change w (μ + P.rho) - (μ + P.rho) ∈ P.rootLattice
      rw [hwy, mem_rootLattice]
      exact ⟨-c, by rw [map_neg]; abel⟩
    obtain ⟨k, hk, hwk⟩ := hμ.exists_weylDot_sub_eq_rootOf hA hwint
    change w (μ + P.rho) - (μ + P.rho) = P.rootOf k at hwk
    rw [hwy] at hwk
    have h0 : P.rootOf (k + c) = P.rootOf 0 := by
      rw [map_add, map_zero, ← hwk]
      abel
    have hkc := P.rootOf_injective h0
    have hc0 : c = 0 := by
      ext j
      have h1 := congrFun hkc j
      have h2 : (0 : ℤ) ≤ k j := hk j
      have h3 : (0 : ℤ) ≤ c j := hc j
      simp only [Pi.add_apply, Pi.zero_apply] at h1 ⊢
      omega
    rw [hc0, map_zero, sub_zero]
  have hsub : Subsingleton (maxSubmodule P μ) :=
    (hM.lieSubmodule _).subsingleton_of_multiplicity_eq_zero P fun y ↦ by
      have hadd := hM.multiplicity_eq_add (maxSubmodule P μ) y
      by_cases hy : hM.multiplicity y = 0
      · omega
      · obtain rfl := key y hy
        have h1 := VermaModule.multiplicity_self (P := P) y
        have h2 : (hM.quotient (maxSubmodule P y)).multiplicity y = 1 := by
          simpa using IrreducibleModule.multiplicity_eq (P := P) y y
        omega
  rw [LieSubmodule.eq_bot_iff]
  intro m hm
  exact congrArg Subtype.val (Subsingleton.elim (⟨m, hm⟩ : maxSubmodule P μ) 0)

omit [IsAlgClosed K] in
include hA in
/-- An antidominant Verma module is isomorphic to its simple quotient. -/
theorem VermaModule.nonempty_equiv_irreducible_of_isAntidominant {μ : Dual K H}
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ) :
    Nonempty (VermaModule P μ ≃ₗ⁅K,𝔤⁆ IrreducibleModule P μ) := by
  refine ⟨LieModuleEquiv.ofBijective (LieSubmodule.Quotient.mk' (maxSubmodule P μ))
    ⟨?_, LieSubmodule.Quotient.surjective_mk' _⟩⟩
  rw [← LieModuleHom.ker_eq_bot, LieSubmodule.Quotient.mk'_ker,
    maxSubmodule_eq_bot_of_isAntidominant P hA hμ]

section Singular

variable {lam μ ν : Dual K H} {z : Dual K H ≃ₗ[K] Dual K H}

omit [IsAlgClosed K] [FiniteDimensional K H] in
include hA in
/-- Under the hypotheses of `nonempty_equiv_projectiveCover_of_singular`, `μ` is dominant and
antidominant, `W_[λ] = W_[μ]`, and `W_[λ]` fixes `μ` under the dot action. -/
theorem isDominant_and_isAntidominant_of_singular
    (hsing : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = n →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) (hz : z ∈ P.weylGroup hA.isGeneralizedCartan)
    (hzν : z (lam - μ) = ν) :
    P.IsDominant hA.isGeneralizedCartan μ ∧ P.IsAntidominant hA.isGeneralizedCartan μ ∧
      ∀ y ∈ P.integralWeylGroup hA.isGeneralizedCartan lam,
        P.weylDot hA.isGeneralizedCartan y μ = μ := by
  have hA' := hA.isGeneralizedCartan
  have hint := sub_rho_integral P hA hν hz hzν
  have hzero : ∀ v i, P.IsPosRoot hA' v i → ∀ n : ℤ,
      P.corootPairing hA' (μ + P.rho) v i = n → n = 0 := by
    intro v i hv n hn
    obtain ⟨m, hm⟩ := exists_int_corootPairing_of_integral P hA' hint v i
    rw [corootPairing_sub, hn] at hm
    have h0 := hsing v i hv (n - m) (by push_cast; linear_combination -hm)
    rw [hn] at h0
    exact_mod_cast h0
  have hdom : P.IsDominant hA' μ := fun v i hv n hn ↦ (hzero v i hv n hn).ge
  have hanti : P.IsAntidominant hA' μ := fun v i hv n hn ↦ (hzero v i hv n hn).le
  refine ⟨hdom, hanti, fun y hy ↦ ?_⟩
  have hWl : P.integralWeylGroup hA' lam = P.integralWeylGroup hA' μ := by
    rw [P.integralWeylGroup_eq_of_integral hA' (μ' := lam + P.rho) fun j ↦ ⟨-1, by simp⟩,
      P.integralWeylGroup_eq_of_integral hA' (μ' := μ + P.rho) fun j ↦ by
        obtain ⟨n, hn⟩ := hint j
        exact ⟨-n, by rw [← neg_sub, LinearMap.neg_apply, hn, Int.cast_neg]⟩,
      ← P.integralWeylGroup_eq_of_integral hA' (μ := μ) (μ' := μ + P.rho) fun j ↦ ⟨-1, by simp⟩]
  obtain ⟨k, hk, hyk⟩ := hanti.exists_weylDot_sub_eq_rootOf hA (hWl ▸ hy)
  have hk0 := hdom.eq_zero_of_apply_eq P hA y.2 hk (by rw [← hyk]; abel)
  rw [hk0, map_zero, sub_eq_zero] at hyk
  simp only [weylDot, hyk, add_sub_cancel_right]

include hA in
/-- `dim Hom(T_μ^λ M(μ), M(y·λ)) = 1` for `y ∈ W_[λ]`, under the hypotheses of
`nonempty_equiv_projectiveCover_of_singular`: by adjunction this is `dim End M(μ)`. -/
theorem finrank_hom_translation_verma_of_singular
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hsing : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = n →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) (hz : z ∈ P.weylGroup hA.isGeneralizedCartan)
    (hzν : z (lam - μ) = ν) {y : P.weylGroup hA.isGeneralizedCartan}
    (hy : y ∈ P.integralWeylGroup hA.isGeneralizedCartan lam) :
    FiniteDimensional K (centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
        (centralCharacter P lam) (VermaModule P μ) →ₗ⁅K,𝔤⁆
          VermaModule P (P.weylDot hA.isGeneralizedCartan y lam)) ∧
      finrank K (centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
        (centralCharacter P lam) (VermaModule P μ) →ₗ⁅K,𝔤⁆
          VermaModule P (P.weylDot hA.isGeneralizedCartan y lam)) = 1 := by
  classical
  have hA' := hA.isGeneralizedCartan
  obtain ⟨hdom, hanti, hfix⟩ := isDominant_and_isAntidominant_of_singular P hA hsing hν hz hzν
  have hfacet : ∀ v i, P.IsPosRoot hA' v i → P.corootPairing hA' (lam + P.rho) v i = 0 →
      P.corootPairing hA' (μ + P.rho) v i = 0 := fun v i hv h0 ↦
    hsing v i hv 0 (by rw [h0, Int.cast_zero])
  obtain ⟨z', hz', hν', ⟨eν⟩⟩ := IrreducibleModule.exists_equiv_dual P hA hν
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have hzz : z' * z ∈ P.weylGroup hA' := mul_mem hz' hz
  have hzν' : (z' * z) (μ - lam) = z' (-ν) := by
    change z' (z (μ - lam)) = z' (-ν)
    rw [← hzν, ← map_neg, neg_sub]
  have hMχ : centralBlock P (VermaModule P μ) (centralCharacter P μ) = ⊤ := centralBlock_verma P μ
  have hNχ : centralBlock P (VermaModule P (P.weylDot hA' y lam)) (centralCharacter P lam) = ⊤ :=
    (VermaModule.centralCharacter_weyl P hA' y.property lam) ▸ centralBlock_verma P _
  have hLO := IrreducibleModule.isCategoryO P ν
  have hL'O : IsCategoryO P (Module.Dual K (IrreducibleModule P ν)) :=
    IsCategoryO.of_equiv (IrreducibleModule.isCategoryO P _) eν.symm
  have hMO := VermaModule.isCategoryO P μ
  have hMp : IsProjectiveO.{max u₁ u₂} P (VermaModule P μ) := VermaModule.isProjectiveO P hA hdom
  let adj := translationAdjunction P hMO hLO hMχ hNχ
  let E := centralTranslationCoeffEquiv P (VermaModule P (P.weylDot hA' y lam))
    (centralCharacter P lam) (centralCharacter P μ) eν
  have hT'O := (VermaModule.isCategoryO P (P.weylDot hA' y lam)).centralTranslation P hL'O
    (centralCharacter P lam) (centralCharacter P μ)
  have hT''O := (VermaModule.isCategoryO P (P.weylDot hA' y lam)).centralTranslation P
    (IrreducibleModule.isCategoryO P (z' (-ν))) (centralCharacter P lam) (centralCharacter P μ)
  obtain ⟨eV⟩ := translation_verma_equiv_of_isAntidominant P hA hlam hanti hfacet hν' hzz hzν' y
  have hcov := VermaModule.isProjectiveCover P μ
  have := hcov.finiteDimensional_hom hT'O
  refine ⟨LinearEquiv.finiteDimensional adj.symm, ?_⟩
  rw [adj.finrank_eq, hcov.finrank_hom_eq_multiplicity hMp hT'O,
    IsCategoryO.multiplicity_congr hT'O hT''O E μ,
    ← IsCategoryO.multiplicity_congr (VermaModule.isCategoryO P _) hT''O eV μ, hfix y hy]
  exact VermaModule.multiplicity_self (P := P) μ

include hA in
/-- **`P(λ)` as a translated Verma module.** Let `λ` be antidominant and let `μ` be a weight with
`ν = z (λ - μ)` dominant integral (`z ∈ W`) and `μ + ρ` orthogonal to every positive root `β` with
`⟨λ + ρ, β^∨⟩ ∈ ℤ` (so `μ` is antidominant and `M(μ)` is simple and projective). Then
`P(λ) ≅ T_μ^λ M(μ)`, `T_μ^λ = pr_{χ_λ}(pr_{χ_μ}(−) ⊗ L(ν))` (Humphreys, GSM 94, proof of
Theorem 4.10 for integral `λ`, `μ = -ρ`). -/
theorem nonempty_equiv_projectiveCover_of_singular
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hsing : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = n →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) (hz : z ∈ P.weylGroup hA.isGeneralizedCartan)
    (hzν : z (lam - μ) = ν) :
    Nonempty (ProjectiveCover P hA lam ≃ₗ⁅K,𝔤⁆ centralTranslation P (IrreducibleModule P ν)
      (centralCharacter P μ) (centralCharacter P lam) (VermaModule P μ)) := by
  classical
  have hA' := hA.isGeneralizedCartan
  obtain ⟨hdom, hanti, -⟩ := isDominant_and_isAntidominant_of_singular P hA hsing hν hz hzν
  have hfacet : ∀ v i, P.IsPosRoot hA' v i → P.corootPairing hA' (lam + P.rho) v i = 0 →
      P.corootPairing hA' (μ + P.rho) v i = 0 := fun v i hv h0 ↦
    hsing v i hv 0 (by rw [h0, Int.cast_zero])
  obtain ⟨x, -, -, ⟨e⟩⟩ := nonempty_equiv_projectiveCover_translation_verma P hA hlam hanti hfacet
    hν hz hzν (w := 1) (one_mem _) fun w' hw' k hk h ↦
      hdom.eq_zero_of_apply_eq P hA hw' hk (by simpa using h)
  rw [weylDot_one] at e
  -- `[M(λ) : L(x·λ)] = dim Hom(P(x·λ), M(λ)) = dim Hom(T M(μ), M(λ)) = 1`
  obtain ⟨-, hdim⟩ := finrank_hom_translation_verma_of_singular P hA hlam hsing hν hz hzν
    (y := 1) (one_mem _)
  rw [weylDot_one] at hdim
  have hmult : (VermaModule.isCategoryO P lam).multiplicity (P.weylDot hA' x lam) ≠ 0 := by
    have h1 := ProjectiveCover.finrank_hom_eq_multiplicity (P := P) (hA := hA)
      (Λ := P.weylDot hA' x lam) (VermaModule.isCategoryO P lam)
    rw [(lieModuleHomCongr P e (LieModuleEquiv.refl)).finrank_eq, hdim] at h1
    rw [← h1]
    exact one_ne_zero
  obtain ⟨c, hc, hxc⟩ := VermaModule.mem_cone_of_multiplicity_ne_zero hmult
  -- `x ∈ W_[λ]` and antidominance force `x·λ = λ`
  have hxint : x ∈ P.integralWeylGroup hA' lam := by
    rw [P.integralWeylGroup_eq_of_integral hA' (μ' := lam + P.rho) fun j ↦ ⟨-1, by simp⟩,
      mem_integralWeylGroup, mem_rootLattice]
    refine ⟨-c, ?_⟩
    have : (x : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) = P.weylDot hA' x lam + P.rho := by
      simp [weylDot]
    rw [this, hxc, map_neg]
    abel
  obtain ⟨k, hk, hxk⟩ := hlam.exists_weylDot_sub_eq_rootOf hA hxint
  have hxk' : (x : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) - (lam + P.rho) = -P.rootOf c := by
    have : (x : Dual K H ≃ₗ[K] Dual K H) (lam + P.rho) = P.weylDot hA' x lam + P.rho := by
      simp [weylDot]
    rw [this, hxc]
    abel
  have h0 : P.rootOf (k + c) = P.rootOf 0 := by
    rw [map_add, map_zero, ← hxk, hxk']
    abel
  have hkc := P.rootOf_injective h0
  have hc0 : c = 0 := by
    ext j
    have h1 := congrFun hkc j
    have h2 : (0 : ℤ) ≤ k j := hk j
    have h3 : (0 : ℤ) ≤ c j := hc j
    simp only [Pi.add_apply, Pi.zero_apply] at h1 ⊢
    omega
  rw [hc0, map_zero, sub_zero] at hxc
  rw [hxc] at e
  exact ⟨e⟩

include hA in
/-- **Humphreys, GSM 94, Theorem 7.16 (b)**, multiplicity form, under the hypotheses of
`nonempty_equiv_projectiveCover_of_singular`: `[M(y·λ) : L(λ)] = 1` for every `y ∈ W_[λ]`. -/
theorem multiplicity_verma_weylDot_of_singular
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hsing : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = n →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) (hz : z ∈ P.weylGroup hA.isGeneralizedCartan)
    (hzν : z (lam - μ) = ν) {y : P.weylGroup hA.isGeneralizedCartan}
    (hy : y ∈ P.integralWeylGroup hA.isGeneralizedCartan lam) :
    (VermaModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan y lam)).multiplicity lam = 1 := by
  obtain ⟨e⟩ := nonempty_equiv_projectiveCover_of_singular P hA hlam hsing hν hz hzν
  obtain ⟨-, hdim⟩ := finrank_hom_translation_verma_of_singular P hA hlam hsing hν hz hzν hy
  have h1 := ProjectiveCover.finrank_hom_eq_multiplicity (P := P) (hA := hA) (Λ := lam)
    (VermaModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan y lam))
  rw [(lieModuleHomCongr P e (LieModuleEquiv.refl)).finrank_eq, hdim] at h1
  exact h1.symm

include hA in
/-- **Humphreys, GSM 94, Theorem 7.16 (b)**, under the hypotheses of
`nonempty_equiv_projectiveCover_of_singular`: every standard filtration of `P(λ)` contains each
`M(y·λ)`, `y ∈ W_[λ]`, exactly once. -/
theorem count_projectiveCover_of_singular [DecidableEq (Dual K H)]
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hsing : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = n →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) (hz : z ∈ P.weylGroup hA.isGeneralizedCartan)
    (hzν : z (lam - μ) = ν) {t : Multiset (Dual K H)}
    (ht : IsStdFiltered P (⊤ : LieSubmodule K 𝔤 (ProjectiveCover P hA lam)) t)
    {y : P.weylGroup hA.isGeneralizedCartan}
    (hy : y ∈ P.integralWeylGroup hA.isGeneralizedCartan lam) :
    t.count (P.weylDot hA.isGeneralizedCartan y lam) = 1 := by
  rw [ProjectiveCover.count_eq_multiplicity P lam hA ht]
  exact multiplicity_verma_weylDot_of_singular P hA hlam hsing hν hz hzν hy

include hA in
/-- **Humphreys, GSM 94, Theorem 7.16 (a)**, under the hypotheses of
`nonempty_equiv_projectiveCover_of_singular`: `P(λ)` is self-dual, `P(λ) ≅ P(λ)^∨`. -/
theorem nonempty_equiv_restrictedDual_projectiveCover_of_singular
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hsing : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i = n →
        P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = 0)
    (hν : P.IsDominantIntegral ν) (hz : z ∈ P.weylGroup hA.isGeneralizedCartan)
    (hzν : z (lam - μ) = ν) :
    Nonempty (ProjectiveCover P hA lam ≃ₗ⁅K,𝔤⁆ restrictedDual P (ProjectiveCover P hA lam)) := by
  have hanti := (isDominant_and_isAntidominant_of_singular P hA hsing hν hz hzν).2.1
  let eM := (VermaModule.nonempty_equiv_irreducible_of_isAntidominant P hA hanti).some
  let eD : restrictedDual P (VermaModule P μ) ≃ₗ⁅K,𝔤⁆ VermaModule P μ :=
    (restrictedDualEquiv P eM).symm.trans
      ((IrreducibleModule.equivRestrictedDual P μ).symm.trans eM.symm)
  let f : centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
      (centralCharacter P lam) (VermaModule P μ) ≃ₗ⁅K,𝔤⁆
      restrictedDual P (centralTranslation P (IrreducibleModule P ν) (centralCharacter P μ)
        (centralCharacter P lam) (VermaModule P μ)) :=
    (centralTranslationEquiv P (IrreducibleModule P ν) (centralCharacter P μ)
      (centralCharacter P lam) eD).symm.trans (restrictedDualCentralTranslationEquiv P hA hν
        (VermaModule.isCategoryO P μ) (centralCharacter P μ) (centralCharacter P lam)).symm
  exact nonempty_equiv_restrictedDual_of_equiv P
    (nonempty_equiv_projectiveCover_of_singular P hA hlam hsing hν hz hzν) f

end Singular

section Integral

variable {lam : Dual K H}

omit [IsAlgClosed K] in
include hA in
/-- For `λ` antidominant with `λ + ρ` integral there is `z ∈ W` with `z (λ + ρ)` dominant
integral (so `μ = -ρ` satisfies the hypotheses of `nonempty_equiv_projectiveCover_of_singular`). -/
theorem exists_isDominantIntegral_of_integral
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hint : ∀ j, ∃ n : ℤ, (lam + P.rho) (P.coroot j) = n) :
    ∃ z ∈ P.weylGroup hA.isGeneralizedCartan, P.IsDominantIntegral (z (lam + P.rho)) := by
  have hν : P.IsDominantIntegral (-(lam + P.rho)) := fun i ↦ by
    obtain ⟨m, hm⟩ := hint i
    have h1 : P.IsPosRoot hA.isGeneralizedCartan 1 i :=
      ⟨Pi.single i 1, fun l ↦ by by_cases h : l = i <;> simp [h], by simp⟩
    have hle := hlam 1 i h1 m (by rw [corootPairing_one, hm])
    refine ⟨(-m).toNat, ?_⟩
    rw [LinearMap.neg_apply, hm]
    have : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this.symm
  obtain ⟨z, hz, hzν, -⟩ := IrreducibleModule.exists_equiv_dual P hA hν
  exact ⟨z, hz, by rwa [neg_neg] at hzν⟩

include hA in
/-- **Humphreys, GSM 94, Theorem 4.10**, first part: for `λ` antidominant with `λ + ρ` integral,
`P(λ) ≅ T_{-ρ}^λ M(-ρ)`, where `T_{-ρ}^λ = pr_{χ_λ}(pr_{χ_{-ρ}}(−) ⊗ L(ν))`, `ν = z (λ + ρ)`
dominant integral. -/
theorem exists_nonempty_equiv_projectiveCover_of_integral
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hint : ∀ j, ∃ n : ℤ, (lam + P.rho) (P.coroot j) = n) :
    ∃ z ∈ P.weylGroup hA.isGeneralizedCartan, ∃ _ : P.IsDominantIntegral (z (lam + P.rho)),
      Nonempty (ProjectiveCover P hA lam ≃ₗ⁅K,𝔤⁆
        centralTranslation P (IrreducibleModule P (z (lam + P.rho))) (centralCharacter P (-P.rho))
          (centralCharacter P lam) (VermaModule P (-P.rho))) := by
  obtain ⟨z, hz, hν⟩ := exists_isDominantIntegral_of_integral P hA hlam hint
  exact ⟨z, hz, hν, nonempty_equiv_projectiveCover_of_singular P hA hlam
    (fun v i _ _ _ ↦ by simp [Matrix.Realization.corootPairing]) hν hz (by rw [sub_neg_eq_add])⟩

include hA in
/-- **Humphreys, GSM 94, Theorem 4.10**, self-duality: for `λ` antidominant with `λ + ρ` integral,
`P(λ) ≅ P(λ)^∨`. -/
theorem nonempty_equiv_restrictedDual_projectiveCover_of_integral
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hint : ∀ j, ∃ n : ℤ, (lam + P.rho) (P.coroot j) = n) :
    Nonempty (ProjectiveCover P hA lam ≃ₗ⁅K,𝔤⁆ restrictedDual P (ProjectiveCover P hA lam)) := by
  obtain ⟨z, hz, hν⟩ := exists_isDominantIntegral_of_integral P hA hlam hint
  exact nonempty_equiv_restrictedDual_projectiveCover_of_singular P hA (μ := -P.rho) hlam
    (fun v i _ _ _ ↦ by simp [Matrix.Realization.corootPairing]) hν hz (by rw [sub_neg_eq_add])

include hA in
/-- **Humphreys, GSM 94, Theorem 4.10**, multiplicities: for `λ` antidominant with `λ + ρ`
integral, `[M(w·λ) : L(λ)] = 1` for every `w ∈ W`, so every standard filtration of `P(λ)` contains
each `M(w·λ)` exactly once. -/
theorem multiplicity_verma_weylDot_of_integral
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hint : ∀ j, ∃ n : ℤ, (lam + P.rho) (P.coroot j) = n) (w : P.weylGroup hA.isGeneralizedCartan) :
    (VermaModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan w lam)).multiplicity lam = 1 := by
  obtain ⟨z, hz, hν⟩ := exists_isDominantIntegral_of_integral P hA hlam hint
  refine multiplicity_verma_weylDot_of_singular P hA (μ := -P.rho) hlam
    (fun v i _ _ _ ↦ by simp [Matrix.Realization.corootPairing]) hν hz (by rw [sub_neg_eq_add]) ?_
  rw [P.integralWeylGroup_eq_of_integral hA.isGeneralizedCartan (μ' := lam + P.rho)
    fun j ↦ ⟨-1, by simp⟩, mem_integralWeylGroup, mem_rootLattice]
  obtain ⟨k, hk⟩ := P.exists_apply_eq_add_rootOf hA.isGeneralizedCartan w.2 hint
  exact ⟨k, by rw [hk, add_sub_cancel_left]⟩

end Integral

end Main

end Matrix.Realization.KacMoodyAlgebra
