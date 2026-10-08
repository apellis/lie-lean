/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.KashiwaraOperators
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Tensor products of integrable `U_q(𝔰𝔩₂)`-modules

For integrable `U_q(𝔰𝔩₂)`-modules `M₁`, `M₂` (`QuantumGroup.IntegrableSl2`) we put an integrable
structure on `M₁ ⊗ M₂` (`QuantumGroup.IntegrableSl2.tensor`) by Kashiwara's coproduct
([Kas] §1.2):
`E = E ⊗ K⁻¹ + 1 ⊗ E`, `F = F ⊗ 1 + K ⊗ F`, `K = K ⊗ K`,
where `K` acts on `Mⁿ` by `qⁿ` (`QuantumGroup.IntegrableSl2.K`). The graded pieces of `M₁ ⊗ M₂`
are the eigenspaces of `K ⊗ K`.

The coproduct of `U = U_q(𝔤)` used in this library ([Lus] 3.1.4) is
`Δ E = E ⊗ 1 + K̃ ⊗ E`, `Δ F = F ⊗ K̃⁻¹ + 1 ⊗ F`; on `M₁ ⊗ M₂` it is Kashiwara's coproduct for the
parameter `q⁻¹` on `M₂ ⊗ M₁`, transported by the flip.

## Main definitions

* `IntegrableSl2.K`, `IntegrableSl2.Kinv`: `qⁿ` and `q⁻ⁿ` on `Mⁿ`.
* `IntegrableSl2.tensor`: the tensor product.

## Main results

* `IntegrableSl2.tensorE_tmul`, `IntegrableSl2.tensorF_tmul`: the action on `x ⊗ y`,
  `x ∈ M₁ᵃ`, `y ∈ M₂ᵇ`: `E (x ⊗ y) = q⁻ᵇ E x ⊗ y + x ⊗ E y`, `F (x ⊗ y) = F x ⊗ y + qᵃ x ⊗ F y`.
* `IntegrableSl2.tensor_dF_tmul`, `IntegrableSl2.tensor_dE_tmul`: the divided powers,
  `F^{(r)} (x ⊗ y) = Σ_{m+n=r} q^{na - mn} F^{(m)} x ⊗ F^{(n)} y` and
  `E^{(t)} (x ⊗ y) = Σ_{n+m=t} q^{-nb - nm} E^{(n)} x ⊗ E^{(m)} y` (cf. [Kas] (1.2)).
* `IntegrableSl2.tmul_mem_tensor_wt`: `x ⊗ y ∈ (M₁ ⊗ M₂)^{a+b}`.

## References

* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §1.
* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §3.1.
-/

open TensorProduct

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  (V : IntegrableSl2 q M)

/-! ### The operators `K`, `K⁻¹` -/

/-- `K` acts on `Mⁿ` by `qⁿ`. -/
noncomputable def K : Module.End k M :=
  DirectSum.toModule k ℤ M (fun n ↦ q ^ n • (V.wt n).subtype) ∘ₗ V.decompose.toLinearMap

/-- `K⁻¹` acts on `Mⁿ` by `q⁻ⁿ`. -/
noncomputable def Kinv : Module.End k M :=
  DirectSum.toModule k ℤ M (fun n ↦ q ^ (-n) • (V.wt n).subtype) ∘ₗ V.decompose.toLinearMap

variable {V}

lemma K_of_mem {n : ℤ} {m : M} (hm : m ∈ V.wt n) : V.K m = q ^ n • m := by
  rw [K, LinearMap.comp_apply, LinearEquiv.coe_coe, decompose_of_mem V hm,
    ← DirectSum.lof_eq_of k, DirectSum.toModule_lof]
  rfl

lemma Kinv_of_mem {n : ℤ} {m : M} (hm : m ∈ V.wt n) : V.Kinv m = q ^ (-n) • m := by
  rw [Kinv, LinearMap.comp_apply, LinearEquiv.coe_coe, decompose_of_mem V hm,
    ← DirectSum.lof_eq_of k, DirectSum.toModule_lof]
  rfl

/-! ### Linear maps out of a tensor product -/

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
  {V₁ : IntegrableSl2 q M₁} {V₂ : IntegrableSl2 q M₂}

lemma mem_iSup_wt (V : IntegrableSl2 q M) (m : M) : m ∈ ⨆ n, V.wt n :=
  V.iSup_wt ▸ Submodule.mem_top

/-- Linear maps on `M₁ ⊗ M₂` agreeing on `x ⊗ y` for weight vectors `x`, `y` are equal. -/
lemma ext_tensor {N : Type*} [AddCommGroup N] [Module k N] {f g : M₁ ⊗[k] M₂ →ₗ[k] N}
    (h : ∀ (a b : ℤ) (x : M₁) (y : M₂), x ∈ V₁.wt a → y ∈ V₂.wt b →
      f (x ⊗ₜ y) = g (x ⊗ₜ y)) : f = g := by
  refine TensorProduct.ext' fun x y ↦ ?_
  induction mem_iSup_wt V₁ x using Submodule.iSup_induction' with
  | mem a x hx =>
    induction mem_iSup_wt V₂ y using Submodule.iSup_induction' with
    | mem b y hy => exact h a b x y hx hy
    | zero => simp
    | add y₁ y₂ _ _ h₁ h₂ => rw [tmul_add, map_add, map_add, h₁, h₂]
  | zero => simp
  | add x₁ x₂ _ _ h₁ h₂ => rw [add_tmul, map_add, map_add, h₁, h₂]

/-- A property of vectors of `M₁ ⊗ M₂` closed under sums and holding for `x ⊗ y` with `x`, `y`
weight vectors holds everywhere. -/
lemma tensor_induction {P : M₁ ⊗[k] M₂ → Prop} (h0 : P 0)
    (hadd : ∀ z w, P z → P w → P (z + w))
    (h : ∀ (a b : ℤ) (x : M₁) (y : M₂), x ∈ V₁.wt a → y ∈ V₂.wt b → P (x ⊗ₜ y))
    (z : M₁ ⊗[k] M₂) : P z := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => exact hadd z w hz hw
  | tmul x y =>
    induction mem_iSup_wt V₁ x using Submodule.iSup_induction' with
    | mem a x hx =>
      induction mem_iSup_wt V₂ y using Submodule.iSup_induction' with
      | mem b y hy => exact h a b x y hx hy
      | zero => simpa using h0
      | add y₁ y₂ _ _ h₁ h₂ => rw [tmul_add]; exact hadd _ _ h₁ h₂
    | zero => simpa using h0
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_tmul]; exact hadd _ _ h₁ h₂

/-! ### The operators on `M₁ ⊗ M₂` -/

variable (V₁ V₂)

/-- `E ⊗ K⁻¹ + 1 ⊗ E`. -/
noncomputable def tensorE : Module.End k (M₁ ⊗[k] M₂) := map V₁.E V₂.Kinv + map 1 V₂.E

/-- `F ⊗ 1 + K ⊗ F`. -/
noncomputable def tensorF : Module.End k (M₁ ⊗[k] M₂) := map V₁.F 1 + map V₁.K V₂.F

/-- `K ⊗ K`. -/
noncomputable def tensorK : Module.End k (M₁ ⊗[k] M₂) := map V₁.K V₂.K

/-- `K⁻¹ ⊗ K⁻¹`. -/
noncomputable def tensorKinv : Module.End k (M₁ ⊗[k] M₂) := map V₁.Kinv V₂.Kinv

variable {V₁ V₂}

lemma tensorF_tmul {a : ℤ} {x : M₁} (hx : x ∈ V₁.wt a) (y : M₂) :
    tensorF V₁ V₂ (x ⊗ₜ y) = V₁.F x ⊗ₜ y + q ^ a • (x ⊗ₜ V₂.F y) := by
  simp [tensorF, K_of_mem hx, smul_tmul']

lemma tensorE_tmul (x : M₁) {b : ℤ} {y : M₂} (hy : y ∈ V₂.wt b) :
    tensorE V₁ V₂ (x ⊗ₜ y) = q ^ (-b) • (V₁.E x ⊗ₜ y) + x ⊗ₜ V₂.E y := by
  simp [tensorE, Kinv_of_mem hy, tmul_smul]

section Tmul

variable {a b : ℤ} {x : M₁} {y : M₂} (hx : x ∈ V₁.wt a) (hy : y ∈ V₂.wt b)
include hx hy

lemma tensorK_tmul (hq0 : q ≠ 0) : tensorK V₁ V₂ (x ⊗ₜ y) = q ^ (a + b) • (x ⊗ₜ y) := by
  simp [tensorK, K_of_mem hx, K_of_mem hy, smul_tmul', tmul_smul, smul_smul, mul_comm,
    zpow_add₀ hq0]

lemma tensorKinv_tmul (hq0 : q ≠ 0) :
    tensorKinv V₁ V₂ (x ⊗ₜ y) = q ^ (-(a + b)) • (x ⊗ₜ y) := by
  simp [tensorKinv, Kinv_of_mem hx, Kinv_of_mem hy, smul_tmul', tmul_smul, smul_smul, mul_comm,
    zpow_add₀ hq0]

end Tmul

/-! ### Commutation relations -/

section Relations

variable (V₁ V₂) (hq0 : q ≠ 0)
include hq0

lemma tensorK_mul_tensorE :
    tensorK V₁ V₂ * tensorE V₁ V₂ = q ^ (2 : ℤ) • (tensorE V₁ V₂ * tensorK V₁ V₂) := by
  refine ext_tensor (V₁ := V₁) (V₂ := V₂) fun a b x y hx hy ↦ ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply]
  rw [tensorE_tmul _ hy, map_add, map_smul, tensorK_tmul (V₁.E_mem hx) hy hq0,
    tensorK_tmul hx (V₂.E_mem hy) hq0, tensorK_tmul hx hy hq0, map_smul, tensorE_tmul _ hy]
  simp only [zpow_add₀ hq0, zpow_neg]
  module

lemma tensorK_mul_tensorF :
    tensorK V₁ V₂ * tensorF V₁ V₂ = q ^ (-2 : ℤ) • (tensorF V₁ V₂ * tensorK V₁ V₂) := by
  refine ext_tensor (V₁ := V₁) (V₂ := V₂) fun a b x y hx hy ↦ ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply]
  rw [tensorF_tmul hx _, map_add, map_smul, tensorK_tmul (V₁.F_mem hx) hy hq0,
    tensorK_tmul hx (V₂.F_mem hy) hq0, tensorK_tmul hx hy hq0, map_smul, tensorF_tmul hx _]
  simp only [zpow_add₀ hq0, zpow_neg, zpow_sub₀ hq0]
  module

lemma tensorKinv_mul_tensorK : tensorKinv V₁ V₂ * tensorK V₁ V₂ = 1 := by
  refine ext_tensor (V₁ := V₁) (V₂ := V₂) fun a b x y hx hy ↦ ?_
  simp only [Module.End.mul_apply, Module.End.one_apply]
  rw [tensorK_tmul hx hy hq0, map_smul, tensorKinv_tmul hx hy hq0, smul_smul,
    ← zpow_add₀ hq0, add_neg_cancel, zpow_zero, one_smul]

lemma tensorE_mul_tensorF_sub :
    tensorE V₁ V₂ * tensorF V₁ V₂ - tensorF V₁ V₂ * tensorE V₁ V₂ =
      (q - q⁻¹)⁻¹ • (tensorK V₁ V₂ - tensorKinv V₁ V₂) := by
  refine ext_tensor (V₁ := V₁) (V₂ := V₂) fun a b x y hx hy ↦ ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply]
  rw [tensorF_tmul hx _, map_add, map_smul, tensorE_tmul _ hy,
    tensorE_tmul _ (V₂.F_mem hy), tensorE_tmul _ hy, map_add, map_smul,
    tensorF_tmul (V₁.E_mem hx) _, tensorF_tmul hx _, tensorK_tmul hx hy hq0,
    tensorKinv_tmul hx hy hq0]
  have h1 := V₁.E_F_sub hx
  have h2 := V₂.E_F_sub hy
  rw [sub_eq_iff_eq_add] at h1 h2
  rw [h1, h2]
  simp only [add_tmul, tmul_add, ← smul_tmul', tmul_smul, qIntZ, neg_sub, zpow_add₀ hq0,
    zpow_neg, zpow_sub₀ hq0, div_eq_mul_inv]
  module

end Relations

/-! ### The tensor product -/

section Structure

variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)

include hq0 hq in
lemma zpow_injective : Function.Injective fun n : ℤ ↦ q ^ n := by
  intro m n h
  by_contra hne
  refine zpow_ne_one_of_pow_ne_one hq (sub_ne_zero.2 hne) ?_
  simp only at h
  rw [zpow_sub₀ hq0, h, div_self (zpow_ne_zero _ hq0)]

include hq0 in
lemma tmul_mem_eigenspace {a b : ℤ} {x : M₁} {y : M₂} (hx : x ∈ V₁.wt a) (hy : y ∈ V₂.wt b) :
    x ⊗ₜ y ∈ (tensorK V₁ V₂).eigenspace (q ^ (a + b)) :=
  Module.End.mem_eigenspace_iff.2 (tensorK_tmul hx hy hq0)

omit [Module k M] in
lemma pow_apply_eq_zero_of_le' {N : Type*} [AddCommGroup N] [Module k N] {f : Module.End k N}
    {x : N} {n m : ℕ} (h : (f ^ n) x = 0) (hnm : n ≤ m) : (f ^ m) x = 0 := by
  rw [← Nat.sub_add_cancel hnm, pow_add, Module.End.mul_apply, h, map_zero]

lemma exists_tensorE_pow_eq_zero (z : M₁ ⊗[k] M₂) :
    ∃ N : ℕ, (tensorE V₁ V₂ ^ N) z = 0 := by
  refine tensor_induction (V₁ := V₁) (V₂ := V₂) (P := fun z ↦ ∃ N : ℕ, (tensorE V₁ V₂ ^ N) z = 0)
    ⟨0, by simp⟩ ?_ ?_ z
  · rintro z w ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    exact ⟨max N₁ N₂, by rw [map_add, pow_apply_eq_zero_of_le' h₁ (le_max_left _ _),
      pow_apply_eq_zero_of_le' h₂ (le_max_right _ _), add_zero]⟩
  intro a b x y hx hy
  obtain ⟨N₁, h₁⟩ := V₁.exists_E_pow_eq_zero x
  obtain ⟨N₂, h₂⟩ := V₂.exists_E_pow_eq_zero y
  -- `Eᵐ (x ⊗ y)` lies in the span of the `Eⁱ x ⊗ Eʲ y`, `i + j = m`
  let P : ℕ → Submodule k (M₁ ⊗[k] M₂) := fun m ↦ Submodule.span k
    {z | ∃ i j : ℕ, i + j = m ∧ z = (V₁.E ^ i) x ⊗ₜ (V₂.E ^ j) y}
  have hP : ∀ m, (tensorE V₁ V₂ ^ m) (x ⊗ₜ y) ∈ P m := by
    intro m
    induction m with
    | zero => exact Submodule.subset_span ⟨0, 0, rfl, by simp⟩
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      have : ∀ z ∈ P m, tensorE V₁ V₂ z ∈ P (m + 1) := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨i, j, hij, rfl⟩ := hz
          rw [tensorE_tmul _ (E_pow_mem hy j)]
          refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i + 1, j, by omega,
            by rw [pow_succ', Module.End.mul_apply]⟩)) (Submodule.subset_span ⟨i, j + 1,
            by omega, by rw [pow_succ' V₂.E, Module.End.mul_apply]⟩)
        | zero => simp
        | add z w _ _ hz hw => rw [map_add]; exact add_mem hz hw
        | smul c z _ hz => rw [map_smul]; exact Submodule.smul_mem _ c hz
      exact this _ ih
  refine ⟨N₁ + N₂, ?_⟩
  have h0 : P (N₁ + N₂) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨i, j, hij, rfl⟩
    rcases le_or_gt N₁ i with hi | hi
    · rw [pow_apply_eq_zero_of_le' h₁ hi, zero_tmul]
    · rw [pow_apply_eq_zero_of_le' h₂ (by omega : N₂ ≤ j), tmul_zero]
  have := hP (N₁ + N₂)
  rwa [h0, Submodule.mem_bot] at this

lemma exists_tensorF_pow_eq_zero (z : M₁ ⊗[k] M₂) :
    ∃ N : ℕ, (tensorF V₁ V₂ ^ N) z = 0 := by
  refine tensor_induction (V₁ := V₁) (V₂ := V₂) (P := fun z ↦ ∃ N : ℕ, (tensorF V₁ V₂ ^ N) z = 0)
    ⟨0, by simp⟩ ?_ ?_ z
  · rintro z w ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    exact ⟨max N₁ N₂, by rw [map_add, pow_apply_eq_zero_of_le' h₁ (le_max_left _ _),
      pow_apply_eq_zero_of_le' h₂ (le_max_right _ _), add_zero]⟩
  intro a b x y hx hy
  obtain ⟨N₁, h₁⟩ := V₁.exists_F_pow_eq_zero x
  obtain ⟨N₂, h₂⟩ := V₂.exists_F_pow_eq_zero y
  let P : ℕ → Submodule k (M₁ ⊗[k] M₂) := fun m ↦ Submodule.span k
    {z | ∃ i j : ℕ, i + j = m ∧ z = (V₁.F ^ i) x ⊗ₜ (V₂.F ^ j) y}
  have hP : ∀ m, (tensorF V₁ V₂ ^ m) (x ⊗ₜ y) ∈ P m := by
    intro m
    induction m with
    | zero => exact Submodule.subset_span ⟨0, 0, rfl, by simp⟩
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      have : ∀ z ∈ P m, tensorF V₁ V₂ z ∈ P (m + 1) := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨i, j, hij, rfl⟩ := hz
          rw [tensorF_tmul (F_pow_mem hx i) _]
          refine add_mem (Submodule.subset_span ⟨i + 1, j, by omega,
            by rw [pow_succ', Module.End.mul_apply]⟩) (Submodule.smul_mem _ _
            (Submodule.subset_span ⟨i, j + 1, by omega,
              by rw [pow_succ' V₂.F, Module.End.mul_apply]⟩))
        | zero => simp
        | add z w _ _ hz hw => rw [map_add]; exact add_mem hz hw
        | smul c z _ hz => rw [map_smul]; exact Submodule.smul_mem _ c hz
      exact this _ ih
  refine ⟨N₁ + N₂, ?_⟩
  have h0 : P (N₁ + N₂) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨i, j, hij, rfl⟩
    rcases le_or_gt N₁ i with hi | hi
    · rw [pow_apply_eq_zero_of_le' h₁ hi, zero_tmul]
    · rw [pow_apply_eq_zero_of_le' h₂ (by omega : N₂ ≤ j), tmul_zero]
  have := hP (N₁ + N₂)
  rwa [h0, Submodule.mem_bot] at this

variable (V₁ V₂) in
/-- The tensor product of integrable `U_q(𝔰𝔩₂)`-modules, with Kashiwara's coproduct
`E = E ⊗ K⁻¹ + 1 ⊗ E`, `F = F ⊗ 1 + K ⊗ F` ([Kas] §1.2); the graded pieces are the eigenspaces
of `K ⊗ K`. -/
noncomputable def tensor : IntegrableSl2 q (M₁ ⊗[k] M₂) where
  E := tensorE V₁ V₂
  F := tensorF V₁ V₂
  wt n := (tensorK V₁ V₂).eigenspace (q ^ n)
  iSupIndep_wt := (Module.End.eigenspaces_iSupIndep _).comp (zpow_injective hq0 hq)
  iSup_wt := by
    rw [eq_top_iff]
    rintro z -
    refine tensor_induction (V₁ := V₁) (V₂ := V₂)
      (P := fun z ↦ z ∈ ⨆ n, (tensorK V₁ V₂).eigenspace (q ^ n)) (zero_mem _)
      (fun _ _ ↦ add_mem) (fun a b x y hx hy ↦ ?_) z
    exact Submodule.mem_iSup_of_mem (a + b) (tmul_mem_eigenspace hq0 hx hy)
  E_mem {n m} h := by
    rw [Module.End.mem_eigenspace_iff] at h ⊢
    rw [← Module.End.mul_apply, tensorK_mul_tensorE V₁ V₂ hq0, LinearMap.smul_apply,
      Module.End.mul_apply, h, map_smul, smul_smul, ← zpow_add₀ hq0, add_comm]
  F_mem {n m} h := by
    rw [Module.End.mem_eigenspace_iff] at h ⊢
    rw [← Module.End.mul_apply, tensorK_mul_tensorF V₁ V₂ hq0, LinearMap.smul_apply,
      Module.End.mul_apply, h, map_smul, smul_smul, ← zpow_add₀ hq0, sub_eq_add_neg, add_comm]
  E_F_sub {n m} h := by
    have hK := Module.End.mem_eigenspace_iff.1 h
    have hKinv : tensorKinv V₁ V₂ m = q ^ (-n) • m := by
      have := congrArg (tensorKinv V₁ V₂) hK
      rw [← Module.End.mul_apply, tensorKinv_mul_tensorK V₁ V₂ hq0, Module.End.one_apply,
        map_smul] at this
      calc tensorKinv V₁ V₂ m = q ^ (-n) • (q ^ n • tensorKinv V₁ V₂ m) := by
            rw [smul_smul, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, one_smul]
        _ = q ^ (-n) • m := by rw [← this]
    have := congrArg (· m) (tensorE_mul_tensorF_sub V₁ V₂ hq0)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, hK, hKinv, ← sub_smul, smul_smul, qIntZ, div_eq_inv_mul]
  exists_E_pow_eq_zero := exists_tensorE_pow_eq_zero
  exists_F_pow_eq_zero := exists_tensorF_pow_eq_zero

lemma tensor_E : (tensor V₁ V₂ hq0 hq).E = tensorE V₁ V₂ := rfl

lemma tensor_F : (tensor V₁ V₂ hq0 hq).F = tensorF V₁ V₂ := rfl

lemma mem_tensor_wt {n : ℤ} {z : M₁ ⊗[k] M₂} :
    z ∈ (tensor V₁ V₂ hq0 hq).wt n ↔ tensorK V₁ V₂ z = q ^ n • z :=
  Module.End.mem_eigenspace_iff

lemma tmul_mem_tensor_wt {a b : ℤ} {x : M₁} {y : M₂} (hx : x ∈ V₁.wt a) (hy : y ∈ V₂.wt b) :
    x ⊗ₜ y ∈ (tensor V₁ V₂ hq0 hq).wt (a + b) :=
  tmul_mem_eigenspace hq0 hx hy

end Structure

/-! ### Divided powers on pure tensors -/

section DividedPowers

variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)

include hq0 hq in
/-- `F^{(r)} (x ⊗ y) = Σ_{m + n = r} q^{na - mn} F^{(m)} x ⊗ F^{(n)} y` for `x ∈ M₁ᵃ`
(cf. [Kas] (1.2)). -/
theorem tensor_dF_tmul {a : ℤ} {x : M₁} (hx : x ∈ V₁.wt a) (y : M₂) (r : ℕ) :
    (tensor V₁ V₂ hq0 hq).dF r (x ⊗ₜ y) = ∑ p ∈ Finset.antidiagonal r,
      q ^ ((p.2 : ℤ) * a - p.1 * p.2) • (V₁.dF p.1 x ⊗ₜ V₂.dF p.2 y) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hne : qInt q (r + 1) ≠ 0 := qInt_ne_zero_of_pow_ne_one hq0 hq (Nat.succ_pos r)
    refine smul_right_injective _ hne ?_
    simp only
    rw [← F_dF (V := tensor V₁ V₂ hq0 hq) hq0 hq, ih, map_sum]
    -- the left side
    have hL : ∀ p : ℕ × ℕ, p ∈ Finset.antidiagonal r → (tensor V₁ V₂ hq0 hq).F
        (q ^ ((p.2 : ℤ) * a - p.1 * p.2) • (V₁.dF p.1 x ⊗ₜ[k] V₂.dF p.2 y)) =
        (q ^ ((p.2 : ℤ) * a - p.1 * p.2) * qInt q (p.1 + 1)) •
          (V₁.dF (p.1 + 1) x ⊗ₜ[k] V₂.dF p.2 y) +
        (q ^ ((p.2 : ℤ) * a - p.1 * p.2) * q ^ (a - 2 * p.1) * qInt q (p.2 + 1)) •
          (V₁.dF p.1 x ⊗ₜ[k] V₂.dF (p.2 + 1) y) := by
      intro p _
      rw [map_smul, tensor_F, tensorF_tmul (dF_mem hx p.1) _, F_dF hq0 hq, F_dF hq0 hq]
      simp only [← smul_tmul' (R' := k), tmul_smul (R' := k)]
      module
    rw [Finset.sum_congr rfl hL, Finset.sum_add_distrib, Finset.smul_sum]
    -- split `[r+1] = q^{n}[m] + q^{-m}[n]`
    have hR : ∀ p : ℕ × ℕ, p ∈ Finset.antidiagonal (r + 1) → qInt q (r + 1) •
        (q ^ ((p.2 : ℤ) * a - p.1 * p.2) • (V₁.dF p.1 x ⊗ₜ[k] V₂.dF p.2 y)) =
        (q ^ ((p.2 : ℤ) * a - p.1 * p.2) * q ^ (p.2 : ℤ) * qInt q p.1) •
          (V₁.dF p.1 x ⊗ₜ[k] V₂.dF p.2 y) +
        (q ^ ((p.2 : ℤ) * a - p.1 * p.2) * q ^ (-(p.1 : ℤ)) * qInt q p.2) •
          (V₁.dF p.1 x ⊗ₜ[k] V₂.dF p.2 y) := by
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      rw [smul_smul, ← add_smul, ← hp, add_comm p.1 p.2, qInt_add, zpow_neg, zpow_natCast,
        zpow_natCast, inv_pow]
      congr 1
      ring
    rw [Finset.sum_congr rfl hR, Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.sum_antidiagonal_succ']
    simp only [qInt_zero, mul_zero, zero_smul, zero_add]
    have h1 : ∀ (e₁ e₂ e₃ : ℤ) (c : k), e₁ = e₂ + e₃ → q ^ e₁ * c = q ^ e₂ * q ^ e₃ * c := by
      intro e₁ e₂ e₃ c h; rw [h, zpow_add₀ hq0]
    have h2 : ∀ (e₁ e₂ e₃ e₄ : ℤ) (c : k), e₁ + e₂ = e₃ + e₄ →
        q ^ e₁ * q ^ e₂ * c = q ^ e₃ * q ^ e₄ * c := by
      intro e₁ e₂ e₃ e₄ c h; rw [← zpow_add₀ hq0, ← zpow_add₀ hq0, h]
    congr 1
    · refine Finset.sum_congr rfl fun p _ ↦ ?_
      congr 1
      refine h1 _ _ _ _ ?_
      push_cast
      ring
    · refine Finset.sum_congr rfl fun p _ ↦ ?_
      congr 1
      refine h2 _ _ _ _ _ ?_
      push_cast
      ring


include hq0 hq in
/-- `E^{(t)} (x ⊗ y) = Σ_{n + m = t} q^{-nb - nm} E^{(n)} x ⊗ E^{(m)} y` for `y ∈ M₂ᵇ`. -/
theorem tensor_dE_tmul (x : M₁) {b : ℤ} {y : M₂} (hy : y ∈ V₂.wt b) (t : ℕ) :
    (tensor V₁ V₂ hq0 hq).dE t (x ⊗ₜ y) = ∑ p ∈ Finset.antidiagonal t,
      q ^ (-((p.1 : ℤ) * b) - p.1 * p.2) • (V₁.dE p.1 x ⊗ₜ V₂.dE p.2 y) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hne : qInt q (t + 1) ≠ 0 := qInt_ne_zero_of_pow_ne_one hq0 hq (Nat.succ_pos t)
    refine smul_right_injective _ hne ?_
    simp only
    rw [← E_dE (V := tensor V₁ V₂ hq0 hq) hq0 hq, ih, map_sum]
    have hL : ∀ p : ℕ × ℕ, p ∈ Finset.antidiagonal t → (tensor V₁ V₂ hq0 hq).E
        (q ^ (-((p.1 : ℤ) * b) - p.1 * p.2) • (V₁.dE p.1 x ⊗ₜ[k] V₂.dE p.2 y)) =
        (q ^ (-((p.1 : ℤ) * b) - p.1 * p.2) * q ^ (-(b + 2 * p.2)) * qInt q (p.1 + 1)) •
          (V₁.dE (p.1 + 1) x ⊗ₜ[k] V₂.dE p.2 y) +
        (q ^ (-((p.1 : ℤ) * b) - p.1 * p.2) * qInt q (p.2 + 1)) •
          (V₁.dE p.1 x ⊗ₜ[k] V₂.dE (p.2 + 1) y) := by
      intro p _
      rw [map_smul, tensor_E, tensorE_tmul _ (dE_mem hy p.2), E_dE hq0 hq, E_dE hq0 hq]
      simp only [← smul_tmul' (R' := k), tmul_smul (R' := k)]
      module
    rw [Finset.sum_congr rfl hL, Finset.sum_add_distrib, Finset.smul_sum]
    have hR : ∀ p : ℕ × ℕ, p ∈ Finset.antidiagonal (t + 1) → qInt q (t + 1) •
        (q ^ (-((p.1 : ℤ) * b) - p.1 * p.2) • (V₁.dE p.1 x ⊗ₜ[k] V₂.dE p.2 y)) =
        (q ^ (-((p.1 : ℤ) * b) - p.1 * p.2) * q ^ (-(p.2 : ℤ)) * qInt q p.1) •
          (V₁.dE p.1 x ⊗ₜ[k] V₂.dE p.2 y) +
        (q ^ (-((p.1 : ℤ) * b) - p.1 * p.2) * q ^ (p.1 : ℤ) * qInt q p.2) •
          (V₁.dE p.1 x ⊗ₜ[k] V₂.dE p.2 y) := by
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      rw [smul_smul, ← add_smul, ← hp, qInt_add, zpow_neg, zpow_natCast, zpow_natCast, inv_pow]
      congr 1
      ring
    rw [Finset.sum_congr rfl hR, Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.sum_antidiagonal_succ']
    simp only [qInt_zero, mul_zero, zero_smul, zero_add]
    have h1 : ∀ (e₁ e₂ e₃ : ℤ) (c : k), e₁ = e₂ + e₃ → q ^ e₁ * c = q ^ e₂ * q ^ e₃ * c := by
      intro e₁ e₂ e₃ c h; rw [h, zpow_add₀ hq0]
    have h2 : ∀ (e₁ e₂ e₃ e₄ : ℤ) (c : k), e₁ + e₂ = e₃ + e₄ →
        q ^ e₁ * q ^ e₂ * c = q ^ e₃ * q ^ e₄ * c := by
      intro e₁ e₂ e₃ e₄ c h; rw [← zpow_add₀ hq0, ← zpow_add₀ hq0, h]
    congr 1
    · refine Finset.sum_congr rfl fun p _ ↦ ?_
      congr 1
      refine h2 _ _ _ _ _ ?_
      push_cast
      ring
    · refine Finset.sum_congr rfl fun p _ ↦ ?_
      congr 1
      refine h1 _ _ _ _ ?_
      push_cast
      ring

end DividedPowers

end IntegrableSl2

end LieLean.QuantumGroup
