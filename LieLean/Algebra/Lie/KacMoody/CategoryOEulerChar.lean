/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOExtFinite

/-!
# Euler characteristics of `Ext•_𝒪(M(μ), -)`

[HumO] §6.14 uses the Euler characteristic
`χ(Ext•_𝒪(M(μ), N)) = ∑ₙ (-1)ⁿ dim Extⁿ_𝒪(M(μ), N)`. The sum is finite because `M(μ)` has finite
projective dimension (`CategoryO.hasProjectiveDimensionLT_verma`) and each term is finite
(`CategoryO.instFiniteExt`). Here it is `CategoryO.eulerChar`, and it is additive on short exact
sequences (`CategoryO.eulerChar_eq_add`), by the long exact `Ext` sequence.

## Main results

* `CategoryO.sum_finrank_ext_eq_add`: alternating sums of `dim Extⁿ(X, -)` are additive along a
  short exact sequence `0 → A → B → C → 0`, provided `Ext^{N+1}(X, A) = 0`.
* `CategoryO.eulerChar_eq_add`: additivity of `χ(Ext•(M(μ), -))`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §6.14.
-/

open CategoryTheory Limits LieModule Module

noncomputable section

universe u

namespace Matrix.Realization.KacMoodyAlgebra

namespace CategoryO

variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}

/-! ### The long exact sequence and alternating sums -/

section LongExact

variable (X : CategoryO.{u} P) {S : ShortComplex (CategoryO.{u} P)} (hS : S.ShortExact)

/-- Postcomposition `Extⁿ(X, Y) → Extⁿ(X, Y')` with a morphism `Y → Y'`, as a linear map. -/
def postcompLinear {Y Y' : CategoryO.{u} P} (f : Y ⟶ Y') (n : ℕ) :
    Abelian.Ext.{u} X Y n →ₗ[K] Abelian.Ext.{u} X Y' n where
  toFun x := x.comp (Abelian.Ext.mk₀ f) (add_zero n)
  map_add' x y := Abelian.Ext.add_comp _ _ _ _
  map_smul' r x := Abelian.Ext.smul_comp _ _ _ r

/-- The connecting map `Extⁿ(X, S.X₃) → Extⁿ⁺¹(X, S.X₁)`, as a linear map. -/
def connectingLinear (n : ℕ) :
    Abelian.Ext.{u} X S.X₃ n →ₗ[K] Abelian.Ext.{u} X S.X₁ (n + 1) where
  toFun x := x.comp hS.extClass rfl
  map_add' x y := Abelian.Ext.add_comp _ _ _ _
  map_smul' r x := Abelian.Ext.smul_comp _ _ _ r

include hS in
theorem exact_postcompLinear (n : ℕ) :
    Function.Exact (postcompLinear X S.f n) (postcompLinear X S.g n) := by
  have := Abelian.Ext.covariant_sequence_exact₂' X hS n
  rw [ShortComplex.ab_exact_iff_function_exact] at this
  exact this

theorem exact_connectingLinear (n : ℕ) :
    Function.Exact (postcompLinear X S.g n) (connectingLinear X hS n) := by
  have := Abelian.Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at this
  exact this

theorem exact_connectingLinear_postcompLinear (n : ℕ) :
    Function.Exact (connectingLinear X hS n) (postcompLinear X S.f (n + 1)) := by
  have := Abelian.Ext.covariant_sequence_exact₁' X hS n (n + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at this
  exact this

include hS in
theorem injective_postcompLinear_zero : Function.Injective (postcompLinear X S.f 0) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have := hS.mono_f
  rw [← Abelian.Ext.mk₀_homEquiv₀_apply x] at hx ⊢
  change (Abelian.Ext.mk₀ _).comp (Abelian.Ext.mk₀ S.f) (add_zero 0) = 0 at hx
  rw [Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_eq_zero_iff] at hx
  rw [(cancel_mono S.f).mp (hx.trans zero_comp.symm), Abelian.Ext.mk₀_zero]

/-- **Alternating sums along the long exact sequence.** For `0 → A → B → C → 0` short exact and
`Ext^{N+1}(X, A) = 0`, `∑_{n ≤ N} (-1)ⁿ dim Extⁿ(X, B)` is the sum of the corresponding sums for
`A` and `C`. -/
include hS in
theorem sum_finrank_ext_eq_add (N : ℕ)
    (hN : ∀ x : Abelian.Ext.{u} X S.X₁ (N + 1), x = 0) :
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * finrank K (Abelian.Ext.{u} X S.X₂ n) =
      ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * finrank K (Abelian.Ext.{u} X S.X₁ n) +
        ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * finrank K (Abelian.Ext.{u} X S.X₃ n) := by
  let rf : ℕ → ℤ := fun n ↦ finrank K (LinearMap.range (postcompLinear X S.f n))
  let rg : ℕ → ℤ := fun n ↦ finrank K (LinearMap.range (postcompLinear X S.g n))
  let rd : ℕ → ℤ := fun n ↦ finrank K (LinearMap.range (connectingLinear X hS n))
  have hb (n : ℕ) : (finrank K (Abelian.Ext.{u} X S.X₂ n) : ℤ) = rf n + rg n := by
    have h := LinearMap.finrank_range_add_finrank_ker (postcompLinear X S.g n)
    rw [(LinearMap.exact_iff.mp (exact_postcompLinear X hS n))] at h
    simp only [rf, rg]
    omega
  have hc (n : ℕ) : (finrank K (Abelian.Ext.{u} X S.X₃ n) : ℤ) = rg n + rd n := by
    have h := LinearMap.finrank_range_add_finrank_ker (connectingLinear X hS n)
    rw [(LinearMap.exact_iff.mp (exact_connectingLinear X hS n))] at h
    simp only [rg, rd]
    omega
  have ha (n : ℕ) : (finrank K (Abelian.Ext.{u} X S.X₁ (n + 1)) : ℤ) = rd n + rf (n + 1) := by
    have h := LinearMap.finrank_range_add_finrank_ker (postcompLinear X S.f (n + 1))
    rw [(LinearMap.exact_iff.mp (exact_connectingLinear_postcompLinear X hS n))] at h
    simp only [rf, rd]
    omega
  have ha₀ : (finrank K (Abelian.Ext.{u} X S.X₁ 0) : ℤ) = rf 0 := by
    have h := LinearMap.finrank_range_add_finrank_ker (postcompLinear X S.f 0)
    rw [LinearMap.ker_eq_bot.mpr (injective_postcompLinear_zero X hS), finrank_bot] at h
    simp only [rf]
    omega
  have hrd : rd N = 0 := by
    have : LinearMap.range (connectingLinear X hS N) = ⊥ :=
      eq_bot_iff.mpr fun x _ ↦ (Submodule.mem_bot K).mpr (hN x)
    simp only [rd, this, finrank_bot, Nat.cast_zero]
  -- the alternating sum of `dim B - dim A - dim C` telescopes to `± rd M`
  have key (M : ℕ) : ∑ n ∈ Finset.range (M + 1), (-1 : ℤ) ^ n *
      ((finrank K (Abelian.Ext.{u} X S.X₂ n) : ℤ) - finrank K (Abelian.Ext.{u} X S.X₁ n) -
        finrank K (Abelian.Ext.{u} X S.X₃ n)) = (-1) ^ (M + 1) * rd M := by
    induction M with
    | zero =>
      rw [Finset.sum_range_one, hb, hc, ha₀]
      ring
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, hb, hc, ha]
      ring
  have h := key N
  rw [hrd, mul_zero] at h
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  linarith

end LongExact

/-! ### The Euler characteristic -/

variable (hA : A.IsFiniteCartan)

/-- The Euler characteristic `χ(Ext•_𝒪(M(μ), N)) = ∑ₙ (-1)ⁿ dim Extⁿ_𝒪(M(μ), N)` ([HumO] §6.14);
the terms vanish beyond `pd M(μ)`, which is at most `#(dotOrbitAbove P hA μ)`. -/
def eulerChar (μ : Dual K H) (N : CategoryO.{u} P) : ℤ :=
  ∑ n ∈ Finset.range ((dotOrbitAbove P hA μ).ncard + 1),
    (-1 : ℤ) ^ n * finrank K (Abelian.Ext.{u} (verma P μ) N n)

/-- **Additivity of the Euler characteristic** on short exact sequences `0 → A → B → C → 0`
in `𝒪`. -/
theorem eulerChar_eq_add (μ : Dual K H) {S : ShortComplex (CategoryO.{u} P)}
    (hS : S.ShortExact) :
    eulerChar hA μ S.X₂ = eulerChar hA μ S.X₁ + eulerChar hA μ S.X₃ :=
  sum_finrank_ext_eq_add (verma P μ) hS _
    (ext_verma_eq_zero_of_ncard_lt hA _ μ (Nat.lt_succ_self _) S.X₁)

/-- The Euler characteristic can be computed with any upper bound beyond `pd M(μ)`. -/
theorem eulerChar_eq_sum (μ : Dual K H) (N : CategoryO.{u} P) {B : ℕ}
    (hB : (dotOrbitAbove P hA μ).ncard < B) :
    eulerChar hA μ N = ∑ n ∈ Finset.range B,
      (-1 : ℤ) ^ n * finrank K (Abelian.Ext.{u} (verma P μ) N n) := by
  refine Finset.sum_subset (Finset.range_subset_range.mpr hB) fun n hn hn' ↦ ?_
  rw [Finset.mem_range] at hn hn'
  have : Subsingleton (Abelian.Ext.{u} (verma P μ) N n) :=
    ⟨fun x y ↦ (ext_verma_eq_zero_of_ncard_lt hA n μ (by omega) N x).trans
      (ext_verma_eq_zero_of_ncard_lt hA n μ (by omega) N y).symm⟩
  rw [finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]

end CategoryO

end Matrix.Realization.KacMoodyAlgebra
