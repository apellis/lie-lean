/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.QBinomial
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.Range

/-!
# Modules over the `q`-boson algebra and their Kashiwara operators

Let `k` be a field and `q ∈ k` nonzero and not a root of unity. A *`q`-boson module*
(`QuantumGroup.BosonModule`) is a `k`-vector space `M` with two operators `e`, `f` such that
`e f = q⁻² f e + 1` and `e` is locally nilpotent. Up to the normalization of `e` this is the action
of Kashiwara's operators `e'ᵢ`, `fᵢ` (one node `i`) of the `q`-boson algebra on `U⁻`
([HK] (6.13), [Jan] 10.1, where `e'ᵢ` is Lusztig's skew derivation `rᵢ`).

Writing `f^{(n)} = fⁿ/[n]!`, we show that every `m ∈ M` is uniquely a finite sum
`m = Σₙ f^{(n)} mₙ` with `e mₙ = 0` (`QuantumGroup.BosonModule.stringEquiv`), and define the
Kashiwara operators `ẽ m = Σₙ f^{(n-1)} mₙ`, `f̃ m = Σₙ f^{(n+1)} mₙ` ([Jan] 10.2).
Unlike the integrable `U_q(𝔰𝔩₂)`-case, the strings are infinite: `ẽ f̃ = 1` and `f̃` is injective.

The key identities are `e f^{(n+1)} = q^{-2(n+1)} f^{(n+1)} e + q^{-n} f^{(n)}`, hence
`e f^{(n+1)} x = q^{-n} f^{(n)} x` for `x ∈ ker e`; existence of the decomposition follows by
induction on the nilpotency order of `e` (subtracting `q^{n(n-1)/2} f^{(n)} eⁿ m`), uniqueness by
applying `e`. The arguments are our own.

## Main definitions

* `QuantumGroup.BosonModule q M`, its divided powers `BosonModule.df`.
* `BosonModule.stringEquiv`: `(ℕ →₀ ker e) ≃ M`, `(xₙ) ↦ Σ f^{(n)} xₙ`.
* `BosonModule.component n`: the component `mₙ` of `m`.
* `BosonModule.eTilde`, `BosonModule.fTilde`: the Kashiwara operators `ẽ`, `f̃`.

## Main results

* `BosonModule.e_df_succ`: `e f^{(n+1)} x = q^{-n} f^{(n)} x` for `x ∈ ker e`.
* `BosonModule.eq_zero_of_sum_range_eq_zero`: uniqueness of the string decomposition.
* `BosonModule.component_sum`: the components of an explicit decomposition.
* `BosonModule.fTilde_df`, `BosonModule.eTilde_df_succ`, `BosonModule.eTilde_of_ker`.
* `BosonModule.eTilde_fTilde`: `ẽ f̃ = 1`; `BosonModule.fTilde_eTilde`: `f̃ ẽ m = m - m₀`;
  `BosonModule.eTilde_eq_zero_iff`: `ẽ m = 0 ↔ e m = 0`.
* `BosonModule.map_eTilde`, `BosonModule.map_fTilde`: naturality.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §6.3.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 10.
-/

open Finset

namespace LieLean.QuantumGroup

variable {k : Type*} [Field k]

/-- A module over the `q`-boson algebra at one node: operators `e`, `f` with `e f = q⁻² f e + 1`
and `e` locally nilpotent. -/
structure BosonModule (q : k) (M : Type*) [AddCommGroup M] [Module k M] where
  /-- The operator `e` (Kashiwara's `e'ᵢ`). -/
  e : Module.End k M
  /-- The operator `f`. -/
  f : Module.End k M
  e_mul_f : e * f = (q⁻¹ ^ 2) • (f * e) + 1
  exists_e_pow_eq_zero (m : M) : ∃ N : ℕ, (e ^ N) m = 0

namespace BosonModule

variable {q : k} {M : Type*} [AddCommGroup M] [Module k M] (V : BosonModule q M)

/-- The divided power `f^{(n)} = fⁿ/[n]!`. -/
noncomputable abbrev df (n : ℕ) : Module.End k M := qDivPow q n V.f

variable {V}

lemma df_apply (n : ℕ) (m : M) : V.df n m = (qFactorial q n)⁻¹ • (V.f ^ n) m := rfl

@[simp] lemma df_zero (m : M) : V.df 0 m = m := by simp [df_apply, qFactorial]

lemma e_f_apply (m : M) : V.e (V.f m) = (q⁻¹ ^ 2) • V.f (V.e m) + m := by
  have := LinearMap.congr_fun V.e_mul_f m
  simpa using this

/-- `e f^{n+1} m = q^{-2(n+1)} f^{n+1} e m + (Σ_{j ≤ n} q^{-2j}) fⁿ m`. -/
lemma e_f_pow_succ (n : ℕ) (m : M) :
    V.e ((V.f ^ (n + 1)) m) = ((q⁻¹ ^ 2) ^ (n + 1)) • (V.f ^ (n + 1)) (V.e m) +
      (∑ j ∈ range (n + 1), (q⁻¹ ^ 2) ^ j) • (V.f ^ n) m := by
  induction n with
  | zero => simp [e_f_apply]
  | succ n ih =>
    have hS : ∑ j ∈ range (n + 1 + 1), (q⁻¹ ^ 2) ^ j =
        q⁻¹ ^ 2 * ∑ j ∈ range (n + 1), (q⁻¹ ^ 2) ^ j + 1 := by
      rw [sum_range_succ', mul_sum]
      simp [pow_succ']
    rw [pow_succ' V.f (n + 1), Module.End.mul_apply, e_f_apply, ih, map_add, map_smul, map_smul,
      hS]
    simp only [Module.End.mul_apply]
    rw [show V.f ((V.f ^ n) m) = (V.f ^ (n + 1)) m by rw [pow_succ', Module.End.mul_apply]]
    module

/-- `Σ_{j ≤ n} q^{-2j} = q^{-n} [n+1]`. -/
lemma sum_inv_sq_pow (hq0 : q ≠ 0) (n : ℕ) :
    ∑ j ∈ range (n + 1), (q⁻¹ ^ 2) ^ j = q⁻¹ ^ n * qInt q (n + 1) := by
  rw [qInt, mul_sum]
  refine sum_congr rfl fun s hs ↦ ?_
  have hs' : s ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hs)
  rw [show n + 1 - 1 - s = n - s by omega]
  have e1 : q⁻¹ ^ n = q⁻¹ ^ (n - s) * q⁻¹ ^ s := by rw [← pow_add, Nat.sub_add_cancel hs']
  have e2 : q⁻¹ ^ (n - s) * q ^ (n - s) = 1 := by rw [← mul_pow, inv_mul_cancel₀ hq0, one_pow]
  rw [e1]
  linear_combination (-(q⁻¹ ^ s * q⁻¹ ^ s)) * e2

variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq0 hq

lemma qInt_ne_zero' {n : ℕ} (hn : 0 < n) : qInt q n ≠ 0 :=
  qInt_ne_zero hq0 (hq _ (by omega))

lemma qFactorial_ne_zero' (n : ℕ) : qFactorial q n ≠ 0 :=
  qFactorial_ne_zero hq0 fun m hm _ ↦ hq _ (by omega)

/-- `e f^{(n+1)} x = q^{-n} f^{(n)} x` for `x ∈ ker e`. -/
theorem e_df_succ {x : M} (hx : V.e x = 0) (n : ℕ) :
    V.e (V.df (n + 1) x) = q⁻¹ ^ n • V.df n x := by
  rw [df_apply, map_smul, e_f_pow_succ, hx, map_zero, smul_zero, zero_add,
    sum_inv_sq_pow hq0, df_apply, smul_smul, smul_smul, qFactorial_succ, mul_inv]
  congr 1
  have := qInt_ne_zero' hq0 hq (Nat.succ_pos n)
  field_simp

/-- `eⁿ f^{(n)} x = q^{-n(n-1)/2} x` for `x ∈ ker e`, recorded as `x = c • eⁿ f^{(n)} x` with
`c ≠ 0`. -/
theorem e_pow_df {x : M} (hx : V.e x = 0) (n : ℕ) :
    ∃ c : k, c ≠ 0 ∧ (V.e ^ n) (V.df n x) = c • x := by
  induction n with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc, h⟩ := ih
    refine ⟨q⁻¹ ^ n * c, mul_ne_zero (pow_ne_zero _ (inv_ne_zero hq0)) hc, ?_⟩
    rw [pow_succ, Module.End.mul_apply, e_df_succ hq0 hq hx, map_smul, h, smul_smul]

/-- `f^{(n)}` is injective on `ker e`. -/
theorem eq_zero_of_df_eq_zero {x : M} (hx : V.e x = 0) {n : ℕ} (h : V.df n x = 0) : x = 0 := by
  obtain ⟨c, hc, he⟩ := e_pow_df hq0 hq hx n
  rw [h, map_zero] at he
  rw [← inv_smul_smul₀ hc x, ← he, smul_zero]

/-- Uniqueness of the string decomposition: if `Σ_{n<N} f^{(n)} xₙ = 0` with `e xₙ = 0`, then
every `xₙ` vanishes. -/
theorem eq_zero_of_sum_range_eq_zero (N : ℕ) :
    ∀ x : ℕ → M, (∀ n, V.e (x n) = 0) → ∑ n ∈ range N, V.df n (x n) = 0 → ∀ n < N, x n = 0 := by
  induction N with
  | zero => intro _ _ _ n hn; omega
  | succ N ih =>
    intro x hx hsum
    rw [sum_range_succ'] at hsum
    have hE : ∑ n ∈ range N, V.df n (q⁻¹ ^ n • x (n + 1)) = 0 := by
      have := congrArg V.e hsum
      rw [map_add, map_sum, map_zero, df_zero, hx 0, add_zero] at this
      rw [← this]
      refine sum_congr rfl fun n _ ↦ ?_
      rw [e_df_succ hq0 hq (hx (n + 1)), map_smul]
    have h1 := ih (fun n ↦ q⁻¹ ^ n • x (n + 1)) (fun n ↦ by rw [map_smul, hx, smul_zero]) hE
    have hsucc : ∀ n < N, x (n + 1) = 0 := fun n hn ↦ by
      have h0 : q⁻¹ ^ n ≠ 0 := pow_ne_zero _ (inv_ne_zero hq0)
      rw [← inv_smul_smul₀ h0 (x (n + 1)), h1 n hn, smul_zero]
    intro n hn
    rcases n with _ | n
    · rw [sum_eq_zero fun n hn ↦ by rw [hsucc n (mem_range.1 hn), map_zero], zero_add,
        df_zero] at hsum
      exact hsum
    · exact hsucc n (by omega)

/-! ### The string decomposition -/

omit hq0 hq in
variable (V) in
/-- The map `(xₙ) ↦ Σₙ f^{(n)} xₙ` from finitely supported families in `ker e`. -/
noncomputable def stringMap : (ℕ →₀ LinearMap.ker V.e) →ₗ[k] M :=
  Finsupp.lsum k fun n ↦ V.df n ∘ₗ (LinearMap.ker V.e).subtype

omit hq0 hq in
lemma stringMap_single (n : ℕ) (x : LinearMap.ker V.e) :
    V.stringMap (Finsupp.single n x) = V.df n x := by
  simp [stringMap]

omit hq0 hq in
lemma stringMap_apply (s : ℕ →₀ LinearMap.ker V.e) :
    V.stringMap s = s.sum fun n x ↦ V.df n x := by
  simp only [stringMap, Finsupp.lsum_apply]
  rfl

theorem stringMap_injective : Function.Injective V.stringMap := by
  classical
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro s hs
  rw [LinearMap.mem_ker, stringMap_apply] at hs
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ∈ s.support, n < N :=
    ⟨s.support.sup id + 1, fun n hn ↦ Nat.lt_succ_of_le (le_sup (f := id) hn)⟩
  have hsum : ∑ n ∈ range N, V.df n ((s n : LinearMap.ker V.e) : M) = 0 := by
    rw [← hs, Finsupp.sum]
    refine (sum_subset (fun n hn ↦ mem_range.2 (hN n hn)) fun n _ hn ↦ ?_).symm
    rw [Finsupp.notMem_support_iff.1 hn]
    simp
  have := eq_zero_of_sum_range_eq_zero hq0 hq N (fun n ↦ ((s n : LinearMap.ker V.e) : M))
    (fun n ↦ (s n).2) hsum
  ext n
  by_cases hn : n ∈ s.support
  · simpa using this n (hN n hn)
  · simpa using Finsupp.notMem_support_iff.1 hn

theorem stringMap_surjective : Function.Surjective V.stringMap := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro m -
  obtain ⟨N, hN⟩ := V.exists_e_pow_eq_zero m
  induction N using Nat.strong_induction_on generalizing m with
  | _ N ih =>
  rcases N with _ | N
  · rw [pow_zero, Module.End.one_apply] at hN
    rw [hN]; exact zero_mem _
  -- `x = eᴺ m ∈ ker e`
  set x := (V.e ^ N) m
  have hx : V.e x = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ']; exact hN
  obtain ⟨c, hc, hcx⟩ := e_pow_df hq0 hq hx N
  set m' := m - c⁻¹ • V.df N x
  have hm' : (V.e ^ N) m' = 0 := by
    simp only [m', map_sub, map_smul, hcx, smul_smul, inv_mul_cancel₀ hc, one_smul]
    exact sub_self _
  have h1 := ih N (Nat.lt_succ_self N) hm'
  have h2 : V.df N x ∈ LinearMap.range V.stringMap :=
    ⟨Finsupp.single N ⟨x, hx⟩, stringMap_single N _⟩
  have : m = m' + c⁻¹ • V.df N x := by simp [m']
  rw [this]
  exact add_mem h1 (Submodule.smul_mem _ _ h2)

variable (V) in
/-- The string decomposition `(ℕ →₀ ker e) ≃ M`, `(xₙ) ↦ Σ f^{(n)} xₙ` ([Jan] 10.1–10.2). -/
noncomputable def stringEquiv : (ℕ →₀ LinearMap.ker V.e) ≃ₗ[k] M :=
  LinearEquiv.ofBijective V.stringMap ⟨stringMap_injective hq0 hq, stringMap_surjective hq0 hq⟩

lemma stringEquiv_apply (s : ℕ →₀ LinearMap.ker V.e) : V.stringEquiv hq0 hq s = V.stringMap s := rfl

lemma stringEquiv_symm_df {x : M} (hx : V.e x = 0) (n : ℕ) :
    (V.stringEquiv hq0 hq).symm (V.df n x) = Finsupp.single n ⟨x, hx⟩ := by
  rw [LinearEquiv.symm_apply_eq, stringEquiv_apply, stringMap_single]

variable (V) in
/-- The component `mₙ ∈ ker e` of `m = Σ f^{(n)} mₙ`. -/
noncomputable def component (n : ℕ) : M →ₗ[k] M :=
  (LinearMap.ker V.e).subtype ∘ₗ Finsupp.lapply n ∘ₗ (V.stringEquiv hq0 hq).symm.toLinearMap

lemma e_component (n : ℕ) (m : M) : V.e (V.component hq0 hq n m) = 0 :=
  ((V.stringEquiv hq0 hq).symm m n).2

lemma component_df {x : M} (hx : V.e x = 0) (n n' : ℕ) :
    V.component hq0 hq n' (V.df n x) = if n = n' then x else 0 := by
  simp only [component, LinearMap.comp_apply, LinearEquiv.coe_coe, stringEquiv_symm_df hq0 hq hx,
    Finsupp.lapply_apply, Finsupp.single_apply]
  split_ifs <;> rfl

/-- The components of an explicit decomposition `Σ_{n<N} f^{(n)} xₙ` with `e xₙ = 0`. -/
theorem component_sum {N : ℕ} {x : ℕ → M} (hx : ∀ n, V.e (x n) = 0) (n : ℕ) :
    V.component hq0 hq n (∑ j ∈ range N, V.df j (x j)) = if n < N then x n else 0 := by
  rw [map_sum]
  simp_rw [component_df hq0 hq (hx _)]
  rw [sum_ite_eq' (range N) n x]
  simp

/-- `m = Σ_{n<N} f^{(n)} mₙ` for `N` large. -/
theorem exists_sum_component (m : M) :
    ∃ N, (∀ n, N ≤ n → V.component hq0 hq n m = 0) ∧
      m = ∑ n ∈ range N, V.df n (V.component hq0 hq n m) := by
  classical
  set s := (V.stringEquiv hq0 hq).symm m
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ∈ s.support, n < N :=
    ⟨s.support.sup id + 1, fun n hn ↦ Nat.lt_succ_of_le (le_sup (f := id) hn)⟩
  refine ⟨N, fun n hn ↦ ?_, ?_⟩
  · have : n ∉ s.support := fun h ↦ absurd (hN n h) (by omega)
    change ((s n : LinearMap.ker V.e) : M) = 0
    rw [Finsupp.notMem_support_iff.1 this]
    rfl
  · conv_lhs => rw [← (V.stringEquiv hq0 hq).apply_symm_apply m]
    rw [stringEquiv_apply, stringMap_apply, Finsupp.sum]
    refine sum_subset (fun n hn ↦ mem_range.2 (hN n hn)) fun n _ hn ↦ ?_
    rw [Finsupp.notMem_support_iff.1 hn]
    simp

/-! ### The Kashiwara operators -/

variable (V) in
/-- The Kashiwara operator `ẽ`: `ẽ (Σₙ f^{(n)} mₙ) = Σₙ f^{(n-1)} mₙ` (the term `n = 0` is
dropped). -/
noncomputable def eTilde : Module.End k M :=
  (Finsupp.lsum k fun n ↦
      (if n = 0 then 0 else V.df (n - 1)) ∘ₗ (LinearMap.ker V.e).subtype) ∘ₗ
    (V.stringEquiv hq0 hq).symm.toLinearMap

variable (V) in
/-- The Kashiwara operator `f̃`: `f̃ (Σₙ f^{(n)} mₙ) = Σₙ f^{(n+1)} mₙ`. -/
noncomputable def fTilde : Module.End k M :=
  (Finsupp.lsum k fun n ↦ V.df (n + 1) ∘ₗ (LinearMap.ker V.e).subtype) ∘ₗ
    (V.stringEquiv hq0 hq).symm.toLinearMap

/-- `f̃ f^{(n)} x = f^{(n+1)} x` for `x ∈ ker e`. -/
theorem fTilde_df {x : M} (hx : V.e x = 0) (n : ℕ) :
    V.fTilde hq0 hq (V.df n x) = V.df (n + 1) x := by
  simp [fTilde, stringEquiv_symm_df hq0 hq hx]

/-- `ẽ f^{(n+1)} x = f^{(n)} x` for `x ∈ ker e`. -/
theorem eTilde_df_succ {x : M} (hx : V.e x = 0) (n : ℕ) :
    V.eTilde hq0 hq (V.df (n + 1) x) = V.df n x := by
  simp [eTilde, stringEquiv_symm_df hq0 hq hx]

/-- `ẽ x = 0` for `x ∈ ker e`. -/
theorem eTilde_of_ker {x : M} (hx : V.e x = 0) : V.eTilde hq0 hq x = 0 := by
  have := stringEquiv_symm_df hq0 hq hx 0
  rw [df_zero] at this
  simp [eTilde, this]

/-- `f̃ x = f x` for `x ∈ ker e`. -/
theorem fTilde_of_ker {x : M} (hx : V.e x = 0) : V.fTilde hq0 hq x = V.f x := by
  have := fTilde_df hq0 hq hx 0
  rw [df_zero] at this
  rw [this, df_apply, zero_add, pow_one, qFactorial_succ, qFactorial, mul_one]
  have : qInt q 1 = 1 := by simp [qInt]
  rw [this, inv_one, one_smul]

/-- Two linear maps out of `M` agreeing on all `f^{(n)} x`, `x ∈ ker e`, are equal. -/
theorem ext_df {N : Type*} [AddCommGroup N] [Module k N] {φ ψ : M →ₗ[k] N}
    (h : ∀ n (x : M), V.e x = 0 → φ (V.df n x) = ψ (V.df n x)) : φ = ψ := by
  have : φ ∘ₗ (V.stringEquiv hq0 hq).toLinearMap = ψ ∘ₗ (V.stringEquiv hq0 hq).toLinearMap := by
    refine Finsupp.lhom_ext fun n x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, stringEquiv_apply, stringMap_single]
    exact h n x x.2
  ext m
  have := LinearMap.congr_fun this ((V.stringEquiv hq0 hq).symm m)
  simpa using this

/-- `ẽ f̃ = 1`. -/
theorem eTilde_fTilde (m : M) : V.eTilde hq0 hq (V.fTilde hq0 hq m) = m := by
  have : V.eTilde hq0 hq ∘ₗ V.fTilde hq0 hq = LinearMap.id :=
    ext_df (V := V) hq0 hq fun n x hx ↦ by
      simp [fTilde_df hq0 hq hx, eTilde_df_succ hq0 hq hx]
  exact LinearMap.congr_fun this m

/-- `f̃` is injective. -/
theorem fTilde_injective : Function.Injective (V.fTilde hq0 hq) :=
  Function.LeftInverse.injective (eTilde_fTilde hq0 hq)

/-- `f̃ ẽ m + m₀ = m`. -/
theorem fTilde_eTilde_add_component (m : M) :
    V.fTilde hq0 hq (V.eTilde hq0 hq m) + V.component hq0 hq 0 m = m := by
  have : V.fTilde hq0 hq ∘ₗ V.eTilde hq0 hq + V.component hq0 hq 0 = LinearMap.id :=
    ext_df (V := V) hq0 hq fun n x hx ↦ by
      rcases n with _ | n
      · have h0 : V.component hq0 hq 0 x = x := by simpa using component_df hq0 hq hx 0 0
        simp [eTilde_of_ker hq0 hq hx, h0]
      · simp [eTilde_df_succ hq0 hq hx, fTilde_df hq0 hq hx, component_df hq0 hq hx]
  exact LinearMap.congr_fun this m

/-- `ẽ m = 0` if and only if `e m = 0`. -/
theorem eTilde_eq_zero_iff (m : M) : V.eTilde hq0 hq m = 0 ↔ V.e m = 0 := by
  refine ⟨fun h ↦ ?_, eTilde_of_ker hq0 hq⟩
  have := fTilde_eTilde_add_component (V := V) hq0 hq m
  rw [h, map_zero, zero_add] at this
  rw [← this]
  exact e_component hq0 hq 0 m

/-- `f̃ⁿ x = f^{(n)} x` for `x ∈ ker e`. -/
theorem fTilde_pow_apply {x : M} (hx : V.e x = 0) (n : ℕ) :
    (V.fTilde hq0 hq ^ n) x = V.df n x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, fTilde_df hq0 hq hx]

/-! ### Naturality -/

omit hq0 hq in
lemma map_df {M' : Type*} [AddCommGroup M'] [Module k M'] {V' : BosonModule q M'}
    {φ : M →ₗ[k] M'} (hf : ∀ m, φ (V.f m) = V'.f (φ m)) (n : ℕ) (m : M) :
    φ (V.df n m) = V'.df n (φ m) := by
  have hpow : ∀ (n : ℕ) m, φ ((V.f ^ n) m) = (V'.f ^ n) (φ m) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro m; rw [pow_succ', pow_succ', Module.End.mul_apply,
        Module.End.mul_apply, hf, ih]
  rw [df_apply, df_apply, map_smul, hpow]

/-- The Kashiwara operator `ẽ` commutes with linear maps commuting with `e` and `f`. -/
theorem map_eTilde {M' : Type*} [AddCommGroup M'] [Module k M'] (V' : BosonModule q M')
    (φ : M →ₗ[k] M') (he : ∀ m, φ (V.e m) = V'.e (φ m)) (hf : ∀ m, φ (V.f m) = V'.f (φ m))
    (m : M) : φ (V.eTilde hq0 hq m) = V'.eTilde hq0 hq (φ m) := by
  have : φ ∘ₗ V.eTilde hq0 hq = V'.eTilde hq0 hq ∘ₗ φ := ext_df (V := V) hq0 hq fun n x hx ↦ by
    have hx' : V'.e (φ x) = 0 := by rw [← he, hx, map_zero]
    simp only [LinearMap.comp_apply]
    rw [map_df hf]
    rcases n with _ | n
    · rw [df_zero, df_zero, eTilde_of_ker hq0 hq hx, eTilde_of_ker hq0 hq hx', map_zero]
    · rw [eTilde_df_succ hq0 hq hx, eTilde_df_succ hq0 hq hx', map_df hf]
  exact LinearMap.congr_fun this m

/-- The Kashiwara operator `f̃` commutes with linear maps commuting with `e` and `f`. -/
theorem map_fTilde {M' : Type*} [AddCommGroup M'] [Module k M'] (V' : BosonModule q M')
    (φ : M →ₗ[k] M') (he : ∀ m, φ (V.e m) = V'.e (φ m)) (hf : ∀ m, φ (V.f m) = V'.f (φ m))
    (m : M) : φ (V.fTilde hq0 hq m) = V'.fTilde hq0 hq (φ m) := by
  have : φ ∘ₗ V.fTilde hq0 hq = V'.fTilde hq0 hq ∘ₗ φ := ext_df (V := V) hq0 hq fun n x hx ↦ by
    have hx' : V'.e (φ x) = 0 := by rw [← he, hx, map_zero]
    simp only [LinearMap.comp_apply]
    rw [map_df hf, fTilde_df hq0 hq hx, fTilde_df hq0 hq hx', map_df hf]
  exact LinearMap.congr_fun this m

/-- The components commute with linear maps commuting with `e` and `f`. -/
theorem map_component {M' : Type*} [AddCommGroup M'] [Module k M'] (V' : BosonModule q M')
    (φ : M →ₗ[k] M') (he : ∀ m, φ (V.e m) = V'.e (φ m)) (hf : ∀ m, φ (V.f m) = V'.f (φ m))
    (n : ℕ) (m : M) : φ (V.component hq0 hq n m) = V'.component hq0 hq n (φ m) := by
  have : φ ∘ₗ V.component hq0 hq n = V'.component hq0 hq n ∘ₗ φ :=
      ext_df (V := V) hq0 hq fun n' x hx ↦ by
    have hx' : V'.e (φ x) = 0 := by rw [← he, hx, map_zero]
    simp only [LinearMap.comp_apply]
    rw [map_df hf, component_df hq0 hq hx, component_df hq0 hq hx']
    split_ifs <;> simp
  exact LinearMap.congr_fun this m

/-! ### Graded naturality

If a family of linear maps `φ_γ : M → M'` (`γ` in an additive group) shifts `e` and `f` by a
fixed degree `δ` (`φ_γ e = e' φ_{γ+δ}`, `φ_γ f = f' φ_{γ-δ}`), then it shifts the components and
the Kashiwara operators accordingly. Applied to the projections onto graded pieces this shows that
`ẽ`, `f̃` are homogeneous of degrees `-δ`, `δ`. -/

section Shift

variable {Γ : Type*} [AddCommGroup Γ] {M' : Type*} [AddCommGroup M'] [Module k M']
  (V' : BosonModule q M') (φ : Γ → M →ₗ[k] M') (δ : Γ)

omit hq0 hq in
lemma map_df_shift (hf : ∀ γ m, φ γ (V.f m) = V'.f (φ (γ - δ) m)) (n : ℕ) (γ : Γ) (m : M) :
    φ γ (V.df n m) = V'.df n (φ (γ - n • δ) m) := by
  have hpow : ∀ (n : ℕ) (γ : Γ) m, φ γ ((V.f ^ n) m) = (V'.f ^ n) (φ (γ - n • δ) m) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro γ m
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hf, ih,
        sub_sub, succ_nsmul, add_comm δ]
  rw [df_apply, df_apply, map_smul, hpow]

/-- `φ_γ mₙ = (φ_{γ+nδ} m)ₙ` for a family shifting `e`, `f` by `δ`. -/
theorem map_component_shift (he : ∀ γ m, φ γ (V.e m) = V'.e (φ (γ + δ) m))
    (hf : ∀ γ m, φ γ (V.f m) = V'.f (φ (γ - δ) m)) (n : ℕ) (γ : Γ) (m : M) :
    V'.component hq0 hq n (φ γ m) = φ (γ - n • δ) (V.component hq0 hq n m) := by
  obtain ⟨N, -, hm⟩ := V.exists_sum_component hq0 hq m
  have hker : ∀ j, V'.e (φ (γ - j • δ) (V.component hq0 hq j m)) = 0 := fun j ↦ by
    have := he (γ - j • δ - δ) (V.component hq0 hq j m)
    rw [e_component, map_zero, sub_add_cancel] at this
    exact this.symm
  have hsum : φ γ m = ∑ j ∈ range N, V'.df j (φ (γ - j • δ) (V.component hq0 hq j m)) := by
    conv_lhs => rw [hm]
    rw [map_sum]
    exact sum_congr rfl fun j _ ↦ map_df_shift V' φ δ hf j γ _
  rw [hsum, component_sum hq0 hq hker]
  split_ifs with hn
  · rfl
  · have : V.component hq0 hq n m = 0 := by
      have h := congrArg (V.component hq0 hq n) hm
      rw [component_sum hq0 hq (fun j ↦ e_component hq0 hq j m),
        ite_eq_right_iff.2 (fun h' ↦ absurd h' hn)] at h
      exact h
    rw [this, map_zero]

/-- `φ_γ (ẽ m) = ẽ (φ_{γ+δ} m)` for a family shifting `e`, `f` by `δ`. -/
theorem map_eTilde_shift (he : ∀ γ m, φ γ (V.e m) = V'.e (φ (γ + δ) m))
    (hf : ∀ γ m, φ γ (V.f m) = V'.f (φ (γ - δ) m)) (γ : Γ) (m : M) :
    φ γ (V.eTilde hq0 hq m) = V'.eTilde hq0 hq (φ (γ + δ) m) := by
  obtain ⟨N, -, hm⟩ := V.exists_sum_component hq0 hq m
  have hker : ∀ j, V'.e (φ (γ + δ - j • δ) (V.component hq0 hq j m)) = 0 := fun j ↦ by
    have := he (γ + δ - j • δ - δ) (V.component hq0 hq j m)
    rw [e_component, map_zero, sub_add_cancel] at this
    exact this.symm
  conv_lhs => rw [hm]
  conv_rhs => rw [hm]
  rw [map_sum, map_sum, map_sum, map_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [map_df_shift V' φ δ hf j (γ + δ)]
  rcases j with _ | j
  · rw [df_zero, df_zero, eTilde_of_ker hq0 hq (e_component hq0 hq 0 m),
      eTilde_of_ker hq0 hq (by simpa using hker 0), map_zero]
  · rw [eTilde_df_succ hq0 hq (e_component hq0 hq _ m), eTilde_df_succ hq0 hq (hker _),
      map_df_shift V' φ δ hf j γ]
    congr 2
    rw [succ_nsmul]
    abel_nf

/-- `φ_γ (f̃ m) = f̃ (φ_{γ+δ} m)` for a family shifting `e`, `f` by `δ`. -/
theorem map_fTilde_shift (he : ∀ γ m, φ γ (V.e m) = V'.e (φ (γ + δ) m))
    (hf : ∀ γ m, φ γ (V.f m) = V'.f (φ (γ - δ) m)) (γ : Γ) (m : M) :
    φ γ (V.fTilde hq0 hq m) = V'.fTilde hq0 hq (φ (γ - δ) m) := by
  obtain ⟨N, -, hm⟩ := V.exists_sum_component hq0 hq m
  have hker : ∀ j, V'.e (φ (γ - δ - j • δ) (V.component hq0 hq j m)) = 0 := fun j ↦ by
    have := he (γ - δ - j • δ - δ) (V.component hq0 hq j m)
    rw [e_component, map_zero, sub_add_cancel] at this
    exact this.symm
  conv_lhs => rw [hm]
  conv_rhs => rw [hm]
  rw [map_sum, map_sum, map_sum, map_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [map_df_shift V' φ δ hf j (γ - δ), fTilde_df hq0 hq (e_component hq0 hq _ m),
    fTilde_df hq0 hq (hker _), map_df_shift V' φ δ hf (j + 1) γ]
  congr 2
  rw [succ_nsmul]
  abel_nf

end Shift

end BosonModule

end LieLean.QuantumGroup
