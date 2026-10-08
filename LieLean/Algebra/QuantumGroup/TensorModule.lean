/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Hopf
import LieLean.Algebra.QuantumGroup.Integrable
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor products of `U_q(𝔤)`-modules

For `U`-modules `M₁`, `M₂`, the coproduct `Δ` (`QuantumGroup.comul`) makes `M₁ ⊗[k] M₂` a
`U`-module ([Lus] 3.1.4). To avoid a clash with the module structure through the left
factor, it is carried by the type synonym `QuantumGroup.TensorModule k M₁ M₂`:
`Eᵢ (x ⊗ y) = Eᵢ x ⊗ y + K̃ᵢ x ⊗ Eᵢ y`, `Fᵢ (x ⊗ y) = Fᵢ x ⊗ K̃ᵢ⁻¹ y + x ⊗ Fᵢ y`,
`K_μ (x ⊗ y) = K_μ x ⊗ K_μ y`.

## Main results

* `QuantumGroup.TensorModule.tmul_mem_weightSpace`: `M₁^Λ ⊗ M₂^{Λ'} ⊆ (M₁ ⊗ M₂)^{Λ + Λ'}`.
* `QuantumGroup.TensorModule.isIntegrable`: tensor products of integrable modules are
  integrable ([Lus] 3.5.2 (a); our own argument by induction on nilpotency orders).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993.
-/

open TensorProduct

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k) [NeZero v]
  (M₁ M₂ : Type*) [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁]
  [AddCommGroup M₂] [Module k M₂] [Module (QuantumGroup R v) M₂]
  [IsScalarTower k (QuantumGroup R v) M₂]

variable (k) in
/-- The tensor product `M₁ ⊗[k] M₂`, to be equipped with the `U`-module structure through the
coproduct. -/
def TensorModule (M₁ M₂ : Type*) [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂]
    [Module k M₂] : Type _ :=
  M₁ ⊗[k] M₂

namespace TensorModule

instance : AddCommGroup (TensorModule k M₁ M₂) := inferInstanceAs (AddCommGroup (M₁ ⊗[k] M₂))

instance : Module k (TensorModule k M₁ M₂) := inferInstanceAs (Module k (M₁ ⊗[k] M₂))

/-- The identification of `TensorModule k M₁ M₂` with `M₁ ⊗[k] M₂`. -/
def mk : M₁ ⊗[k] M₂ ≃ₗ[k] TensorModule k M₁ M₂ := LinearEquiv.refl k _

/-- The action of `U ⊗ U` on `M₁ ⊗ M₂`. -/
noncomputable def actPair :
    QuantumGroup R v ⊗[k] QuantumGroup R v →ₐ[k] Module.End k (M₁ ⊗[k] M₂) :=
  (Module.endTensorEndAlgHom (R := k) (S := k) (A := k) (M := M₁) (N := M₂)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul k k M₁ : QuantumGroup R v →ₐ[k] _)
      (Algebra.lsmul k k M₂ : QuantumGroup R v →ₐ[k] _))

/-- The action of `U` on `M₁ ⊗ M₂` through the coproduct. -/
noncomputable def act : QuantumGroup R v →ₐ[k] Module.End k (M₁ ⊗[k] M₂) :=
  (actPair R v M₁ M₂).comp (comul R v)

noncomputable instance : Module (QuantumGroup R v) (TensorModule k M₁ M₂) :=
  Module.compHom (M₁ ⊗[k] M₂) (act R v M₁ M₂).toRingHom

variable {R v M₁ M₂}

lemma smul_mk (u : QuantumGroup R v) (z : M₁ ⊗[k] M₂) :
    u • mk M₁ M₂ z = mk M₁ M₂ (act R v M₁ M₂ u z) := rfl

instance : IsScalarTower k (QuantumGroup R v) (TensorModule k M₁ M₂) where
  smul_assoc c u z := by
    obtain ⟨z, rfl⟩ := (mk M₁ M₂).surjective z
    rw [smul_mk, smul_mk, map_smul, LinearMap.smul_apply, map_smul]

omit [NeZero v] in
lemma act_tmul (a b : QuantumGroup R v) (x : M₁) (y : M₂) :
    actPair R v M₁ M₂ (a ⊗ₜ[k] b) (x ⊗ₜ[k] y) = (a • x) ⊗ₜ[k] (b • y) := by
  simp [actPair, Module.endTensorEndAlgHom_apply]

lemma E_smul_tmul (i : I) (x : M₁) (y : M₂) :
    E R v i • mk M₁ M₂ (x ⊗ₜ[k] y) =
      mk M₁ M₂ ((E R v i • x) ⊗ₜ[k] y + (Kt R v i • x) ⊗ₜ[k] (E R v i • y)) := by
  rw [smul_mk, act, AlgHom.comp_apply, comul_E, map_add, map_add,
    LinearMap.add_apply, act_tmul, act_tmul, one_smul, map_add]

lemma F_smul_tmul (i : I) (x : M₁) (y : M₂) :
    F R v i • mk M₁ M₂ (x ⊗ₜ[k] y) =
      mk M₁ M₂ ((F R v i • x) ⊗ₜ[k] (K R v (-ktilde R i) • y) + x ⊗ₜ[k] (F R v i • y)) := by
  rw [smul_mk, act, AlgHom.comp_apply, comul_F, map_add, map_add,
    LinearMap.add_apply, act_tmul, act_tmul, one_smul, map_add]

lemma K_smul_tmul (μ : Y) (x : M₁) (y : M₂) :
    K R v μ • mk M₁ M₂ (x ⊗ₜ[k] y) = mk M₁ M₂ ((K R v μ • x) ⊗ₜ[k] (K R v μ • y)) := by
  rw [smul_mk, act, AlgHom.comp_apply, comul_K, act_tmul]

/-- `M₁^Λ ⊗ M₂^{Λ'} ⊆ (M₁ ⊗ M₂)^{Λ + Λ'}`. -/
theorem tmul_mem_weightSpace {Λ Λ' : Y →+ ℤ} {x : M₁} {y : M₂}
    (hx : x ∈ weightSpace R v M₁ Λ) (hy : y ∈ weightSpace R v M₂ Λ') :
    mk M₁ M₂ (x ⊗ₜ[k] y) ∈ weightSpace R v (TensorModule k M₁ M₂) (Λ + Λ') := fun μ ↦ by
  rw [K_smul_tmul, hx μ, hy μ, smul_tmul_smul, ← map_smul, AddMonoidHom.add_apply,
    zpow_add₀ (NeZero.ne v)]

omit [NeZero v] in
/-- The pure tensors of weight vectors span `M₁ ⊗ M₂`. -/
theorem span_tmul_weight (h₁ : ⨆ Λ, weightSpace R v M₁ Λ = ⊤)
    (h₂ : ⨆ Λ, weightSpace R v M₂ Λ = ⊤) :
    Submodule.span k {z : TensorModule k M₁ M₂ | ∃ Λ Λ' x y, x ∈ weightSpace R v M₁ Λ ∧
      y ∈ weightSpace R v M₂ Λ' ∧ z = mk M₁ M₂ (x ⊗ₜ[k] y)} = ⊤ := by
  set S := Submodule.span k {z : TensorModule k M₁ M₂ | ∃ Λ Λ' x y,
    x ∈ weightSpace R v M₁ Λ ∧ y ∈ weightSpace R v M₂ Λ' ∧ z = mk M₁ M₂ (x ⊗ₜ[k] y)}
  rw [eq_top_iff]
  rintro z -
  obtain ⟨z, rfl⟩ := (mk M₁ M₂).surjective z
  induction z using TensorProduct.inductionOn with
  | add z z' h h' => rw [map_add]; exact S.add_mem h h'
  | tmul x y =>
    have hx : x ∈ ⨆ Λ, weightSpace R v M₁ Λ := h₁ ▸ Submodule.mem_top
    induction hx using Submodule.iSup_induction' with
    | mem Λ x hx =>
      have hy : y ∈ ⨆ Λ, weightSpace R v M₂ Λ := h₂ ▸ Submodule.mem_top
      induction hy using Submodule.iSup_induction' with
      | mem Λ' y hy => exact Submodule.subset_span ⟨Λ, Λ', x, y, hx, hy, rfl⟩
      | zero => simp
      | add y y' _ _ h h' => rw [tmul_add, map_add]; exact S.add_mem h h'
    | zero => simp
    | add x x' _ _ h h' => rw [add_tmul, map_add]; exact S.add_mem h h'

lemma E_pow_smul_tmul_eq_zero (i : I) (N : ℕ) :
    ∀ (Λ Λ' : Y →+ ℤ) (x : M₁) (y : M₂) (a b : ℕ), x ∈ weightSpace R v M₁ Λ →
      y ∈ weightSpace R v M₂ Λ' → E R v i ^ a • x = 0 → E R v i ^ b • y = 0 → a + b ≤ N →
      E R v i ^ N • mk M₁ M₂ (x ⊗ₜ[k] y) = 0 := by
  induction N with
  | zero =>
    intro Λ Λ' x y a b _ _ ha _ hab
    obtain rfl : a = 0 := by omega
    rw [pow_zero, one_smul] at ha
    simp [ha]
  | succ N ih =>
    intro Λ Λ' x y a b hx hy ha hb hab
    rw [pow_succ, mul_smul, E_smul_tmul, map_add, smul_add]
    rcases a with _ | a
    · rw [pow_zero, one_smul] at ha
      simp [ha]
    rcases b with _ | b
    · rw [pow_zero, one_smul] at hb
      simp [hb]
    rw [pow_succ, mul_smul] at ha hb
    rw [Kt_smul_of_mem_weightSpace hx,
      ← smul_tmul' ((v ^ D.d i) ^ Λ (R.coroot i)) x (E R v i • y), (mk M₁ M₂).map_smul,
      smul_comm (E R v i ^ N) ((v ^ D.d i) ^ Λ (R.coroot i)),
      ih _ _ _ _ a (b + 1) (E_smul_mem_weightSpace hx i) hy ha (by rwa [pow_succ, mul_smul])
        (by omega),
      ih _ _ _ _ (a + 1) b hx (E_smul_mem_weightSpace hy i) (by rwa [pow_succ, mul_smul]) hb
        (by omega), smul_zero, add_zero]

lemma F_pow_smul_tmul_eq_zero (i : I) (N : ℕ) :
    ∀ (Λ Λ' : Y →+ ℤ) (x : M₁) (y : M₂) (a b : ℕ), x ∈ weightSpace R v M₁ Λ →
      y ∈ weightSpace R v M₂ Λ' → F R v i ^ a • x = 0 → F R v i ^ b • y = 0 → a + b ≤ N →
      F R v i ^ N • mk M₁ M₂ (x ⊗ₜ[k] y) = 0 := by
  induction N with
  | zero =>
    intro Λ Λ' x y a b _ _ ha _ hab
    obtain rfl : a = 0 := by omega
    rw [pow_zero, one_smul] at ha
    simp [ha]
  | succ N ih =>
    intro Λ Λ' x y a b hx hy ha hb hab
    rw [pow_succ, mul_smul, F_smul_tmul, map_add, smul_add]
    rcases a with _ | a
    · rw [pow_zero, one_smul] at ha
      simp [ha]
    rcases b with _ | b
    · rw [pow_zero, one_smul] at hb
      simp [hb]
    rw [pow_succ, mul_smul] at ha hb
    rw [K_neg_ktilde_smul_of_mem_weightSpace hy,
      tmul_smul ((v ^ D.d i) ^ (-Λ' (R.coroot i))) (F R v i • x) y, (mk M₁ M₂).map_smul,
      smul_comm (F R v i ^ N) ((v ^ D.d i) ^ (-Λ' (R.coroot i))),
      ih _ _ _ _ a (b + 1) (F_smul_mem_weightSpace hx i) hy ha (by rwa [pow_succ, mul_smul])
        (by omega),
      ih _ _ _ _ (a + 1) b hx (F_smul_mem_weightSpace hy i) (by rwa [pow_succ, mul_smul]) hb
        (by omega), smul_zero, add_zero]

/-- Tensor products of integrable modules are integrable ([Lus] 3.5.2 (a)). -/
theorem isIntegrable (h₁ : IsIntegrable R v M₁) (h₂ : IsIntegrable R v M₂) :
    IsIntegrable R v (TensorModule k M₁ M₂) := by
  have hspan := span_tmul_weight h₁.iSup_weightSpace_eq_top h₂.iSup_weightSpace_eq_top
  refine ⟨?_, fun i z ↦ ?_, fun i z ↦ ?_⟩
  · rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨Λ, Λ', x, y, hx, hy, rfl⟩
    exact Submodule.mem_iSup_of_mem _ (tmul_mem_weightSpace hx hy)
  · have hz : z ∈ Submodule.span k _ := hspan ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨Λ, Λ', x, y, hx, hy, rfl⟩ := hz
      obtain ⟨a, ha⟩ := h₁.exists_E_pow_smul_eq_zero i x
      obtain ⟨b, hb⟩ := h₂.exists_E_pow_smul_eq_zero i y
      exact ⟨a + b, E_pow_smul_tmul_eq_zero i _ Λ Λ' x y a b hx hy ha hb le_rfl⟩
    | zero => exact ⟨0, smul_zero _⟩
    | add z z' _ _ h h' =>
      obtain ⟨n, hn⟩ := h
      obtain ⟨n', hn'⟩ := h'
      refine ⟨n + n', ?_⟩
      have e1 : E R v i ^ (n + n') • z = 0 := by rw [add_comm, pow_add, mul_smul, hn, smul_zero]
      have e2 : E R v i ^ (n + n') • z' = 0 := by rw [pow_add, mul_smul, hn', smul_zero]
      rw [smul_add, e1, e2, add_zero]
    | smul c z _ h =>
      obtain ⟨n, hn⟩ := h
      exact ⟨n, by rw [smul_comm, hn, smul_zero]⟩
  · have hz : z ∈ Submodule.span k _ := hspan ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨Λ, Λ', x, y, hx, hy, rfl⟩ := hz
      obtain ⟨a, ha⟩ := h₁.exists_F_pow_smul_eq_zero i x
      obtain ⟨b, hb⟩ := h₂.exists_F_pow_smul_eq_zero i y
      exact ⟨a + b, F_pow_smul_tmul_eq_zero i _ Λ Λ' x y a b hx hy ha hb le_rfl⟩
    | zero => exact ⟨0, smul_zero _⟩
    | add z z' _ _ h h' =>
      obtain ⟨n, hn⟩ := h
      obtain ⟨n', hn'⟩ := h'
      refine ⟨n + n', ?_⟩
      have e1 : F R v i ^ (n + n') • z = 0 := by rw [add_comm, pow_add, mul_smul, hn, smul_zero]
      have e2 : F R v i ^ (n + n') • z' = 0 := by rw [pow_add, mul_smul, hn', smul_zero]
      rw [smul_add, e1, e2, add_zero]
    | smul c z _ h =>
      obtain ⟨n, hn⟩ := h
      exact ⟨n, by rw [smul_comm, hn, smul_zero]⟩

end TensorModule

end LieLean.QuantumGroup
