/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Basic

/-!
# Kashiwara's grand loop: string data and the tensor product rule in bounded depth

A vector `x ∈ L(λ)` has *string data* `(k, a, u)` at `i` (`QuantumGroup.GrandLoop.IsStr`) if
`x ≡ Fᵢ^{(k)} u` modulo `ϖ L(λ)` with `u ∈ L(λ) \ ϖ L(λ)` killed by `Eᵢ`, of `⟨i, ·⟩`-weight
`a ≥ k`; then `εᵢ(x) = k` and `φᵢ(x) = a - k`. By the string lemma
(`QuantumGroup.GrandLoop.exists_string`) every class of `B(λ)` of depth `≤ d` has string data once
`A`, `B`, `C` hold up to depth `d`.
For string data on both factors we prove the tensor product rule on `L(λ₁) ⊗ L(λ₂)` modulo
`ϖ (L(λ₁) ⊗ L(λ₂))` in the library's order of the factors ([HK] Lemma 5.3.2 (1), (2)):
`f̃ᵢ (x ⊗ y) ≡ x ⊗ f̃ᵢ y` if `εᵢ(x) < φᵢ(y)` and `≡ f̃ᵢ x ⊗ y` otherwise; `ẽᵢ (x ⊗ y) ≡ x ⊗ ẽᵢ y` if
`εᵢ(x) ≤ φᵢ(y)` and `≡ ẽᵢ x ⊗ y` otherwise.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
-/

open Finset Pointwise TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

/-- `Fᵢ^{(j)}` on `V(λ)`. -/
abbrev dFV (Λ : Dom R) (i : I) (j : ℕ) : Module.End k (IrreducibleModule R v Λ.1) :=
  (nodeSl2 R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF j

variable (hvt hR ϖ) in
/-- String data at `i`: `x ≡ Fᵢ^{(k)} u` modulo `ϖ L(λ)` with `u ∈ L(λ) \ ϖ L(λ)` of weight
`λ - ν + k αᵢ` killed by `Eᵢ`, `⟨i, wt u⟩ = a ≥ k`. -/
structure IsStr (Λ : Dom R) (i : I) (ν : I →₀ ℕ) (x : IrreducibleModule R v Λ.1) (kk a : ℕ)
    (u : IrreducibleModule R v Λ.1) : Prop where
  x_wt : x ∈ wsp Λ ν
  mem : u ∈ lat hvt hR A Λ
  wt : u ∈ weightSpace R v _ (Λ.1 - R.rootSum ν + kk • R.root i)
  E_smul : E R v i • u = 0
  node : (a : ℤ) = (Λ.1 - R.rootSum ν) (R.coroot i) + 2 * kk
  notMem : u ∉ ϖ • lat hvt hR A Λ
  le : kk ≤ a
  sub : x - dFV (hvt := hvt) (hR := hR) Λ i kk u ∈ ϖ • lat hvt hR A Λ

namespace IsStr

variable {Λ : Dom R} {i : I} {ν : I →₀ ℕ} {x : IrreducibleModule R v Λ.1} {kk a : ℕ}
  {u : IrreducibleModule R v Λ.1}

lemma prim (h : IsStr hvt hR ϖ Λ i ν x kk a u) :
    u ∈ (nodeSl2 R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).prim a :=
  ⟨by rw [h.node]; exact mem_nodeWt_of_mem_add_nsmul i h.wt, h.E_smul⟩

lemma ne_zero (h : IsStr hvt hR ϖ Λ i ν x kk a u) : u ≠ 0 := fun h0 ↦
  h.notMem (by rw [h0]; exact zero_mem _)

lemma dFV_mem (h : IsStr hvt hR ϖ Λ i ν x kk a u) (j : ℕ) :
    dFV (hvt := hvt) (hR := hR) Λ i j u ∈ lat hvt hR A Λ := by
  rw [← kashiwaraF_pow_of_primitive _ _ i h.E_smul h.prim.1]
  exact kashiwaraF_pow_mem _ _ i (fun _ hy ↦ kashiwaraF_mem_lat Λ i hy) _ h.mem

lemma dFV_mem_weightSpace (h : IsStr hvt hR ϖ Λ i ν x kk a u) :
    dFV (hvt := hvt) (hR := hR) Λ i kk u ∈ wsp Λ ν :=
  dF_mem_weightSpace _ _ i h.wt

/-- `x ∈ L(λ)`. -/
lemma mem_lat (h : IsStr hvt hR ϖ Λ i ν x kk a u) : x ∈ lat hvt hR A Λ := by
  have := add_mem (Submodule.smul_le_self_of_tower ϖ _ h.sub) (h.dFV_mem kk)
  rwa [sub_add_cancel] at this

/-- `Fᵢ^{(j)} u ∉ ϖ L(λ)` for `j ≤ k`, given `A` up to the depth of `x`. -/
lemma dFV_notMem {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s) (hν : ν.degree = d)
    (hϖv : algebraMap A k ϖ ≠ 0) (h : IsStr hvt hR ϖ Λ i ν x kk a u) :
    ∀ j ≤ kk, dFV (hvt := hvt) (hR := hR) Λ i j u ∉ ϖ • lat hvt hR A Λ := by
  intro j
  induction j with
  | zero => intro _; simpa using h.notMem
  | succ j ih =>
    intro hj hmem
    refine ih (by omega) ?_
    have he := localE_smul hA Λ hν i (kk - (j + 1)) hϖv hmem (by
      have := dF_mem_weightSpace (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i
        (μ := Λ.1 - R.rootSum ν + (kk - (j + 1)) • R.root i) (j := j + 1) (m := u)
        (by rw [add_assoc, ← add_nsmul, Nat.sub_add_cancel hj]; exact h.wt)
      exact this)
    have hle := h.le
    have hja : (j : ℤ) < a := by omega
    have key : eK hvt hR Λ i (dFV (hvt := hvt) (hR := hR) Λ i (j + 1) u) =
        dFV (hvt := hvt) (hR := hR) Λ i j u :=
      IntegrableSl2.eTilde_dF_succ (pow_d_ne_zero i)
        (pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) h.E_smul h.prim.1 hja
    rwa [key] at he

/-- `x ∉ ϖ L(λ)`. -/
lemma notMem_x {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s) (hν : ν.degree = d)
    (hϖv : algebraMap A k ϖ ≠ 0) (h : IsStr hvt hR ϖ Λ i ν x kk a u) :
    x ∉ ϖ • lat hvt hR A Λ := fun hx ↦
  h.dFV_notMem hA hν hϖv kk le_rfl (by simpa using sub_mem hx h.sub)

/-- `f̃ᵢ` on string data. -/
lemma kashiwaraF (h : IsStr hvt hR ϖ Λ i ν x kk a u) (hk : kk + 1 ≤ a) :
    IsStr hvt hR ϖ Λ i (ν + Finsupp.single i 1) (fK hvt hR Λ i x) (kk + 1) a u where
  x_wt := by
    have := kashiwaraF_mem_weightSpace (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i
      h.x_wt
    convert this using 2
    rw [R.rootSum_add, R.rootSum_single, one_nsmul]
    abel
  mem := h.mem
  wt := by
    convert h.wt using 2
    rw [R.rootSum_add, R.rootSum_single, add_nsmul, one_nsmul]
    abel
  E_smul := h.E_smul
  node := by
    rw [h.node, R.rootSum_add, R.rootSum_single, one_nsmul, ← sub_sub, AddMonoidHom.sub_apply,
      AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, R.root_coroot, D.cartanMatrix_self]
    push_cast; ring
  notMem := h.notMem
  le := hk
  sub := by
    have := kashiwaraF_mem_smul_lat Λ i h.sub
    rwa [map_sub, kashiwaraF_dF h.prim.1 h.E_smul] at this

/-- `f̃ᵢ x ∈ ϖ L(λ)` at the end of the string. -/
lemma kashiwaraF_mem (h : IsStr hvt hR ϖ Λ i ν x kk a u) (hk : kk = a) :
    fK hvt hR Λ i x ∈ ϖ • lat hvt hR A Λ := by
  have := kashiwaraF_mem_smul_lat Λ i h.sub
  rwa [map_sub, kashiwaraF_dF h.prim.1 h.E_smul, IntegrableSl2.dF_eq_zero_of_primitive
    (pow_d_ne_zero i) (pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) h.prim.1 h.E_smul
    (by push_cast; omega),
    sub_zero] at this

/-- `ẽᵢ` on string data. -/
lemma kashiwaraE {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s) (hν : ν.degree = d)
    (hϖv : algebraMap A k ϖ ≠ 0) (h : IsStr hvt hR ϖ Λ i ν x kk a u) {ν' : I →₀ ℕ}
    (hν' : ν = ν' + Finsupp.single i 1) (hk : 1 ≤ kk) :
    IsStr hvt hR ϖ Λ i ν' (eK hvt hR Λ i x) (kk - 1) a u where
  x_wt := by
    have := kashiwaraE_mem_weightSpace (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i
      h.x_wt
    convert this using 2
    rw [hν', R.rootSum_add, R.rootSum_single, one_nsmul]
    abel
  mem := h.mem
  wt := by
    convert h.wt using 2
    rw [hν', R.rootSum_add, R.rootSum_single, one_nsmul]
    conv_rhs => rw [show kk = (kk - 1) + 1 by omega, add_nsmul, one_nsmul]
    abel
  E_smul := h.E_smul
  node := by
    rw [h.node, hν', R.rootSum_add, R.rootSum_single, one_nsmul, ← sub_sub]
    simp only [AddMonoidHom.sub_apply]
    rw [R.root_coroot, D.cartanMatrix_self]
    push_cast [Nat.cast_sub hk]; ring
  notMem := h.notMem
  le := by have := h.le; omega
  sub := by
    have hw : x - dFV (hvt := hvt) (hR := hR) Λ i kk u ∈ wsp Λ ν :=
      sub_mem h.x_wt h.dFV_mem_weightSpace
    have := localE_smul hA Λ hν i 0 hϖv h.sub (by simpa using hw)
    have hle := h.le
    have hja : ((kk - 1 : ℕ) : ℤ) < a := by omega
    have key : eK hvt hR Λ i (dFV (hvt := hvt) (hR := hR) Λ i (kk - 1 + 1) u) =
        dFV (hvt := hvt) (hR := hR) Λ i (kk - 1) u :=
      IntegrableSl2.eTilde_dF_succ (pow_d_ne_zero i)
        (pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) h.E_smul h.prim.1 hja
    rwa [map_sub, show kk = (kk - 1) + 1 by omega, key] at this

end IsStr

/-- Every `x ∈ L(λ) \ ϖ L(λ)` of depth `d` congruent to some `f̃_w v_λ` has string data at every
`i`, given `A`, `B`, `C` up to depth `d` (from [HK] Lemma 5.3.1 (2)). -/
theorem exists_isStr (hϖv : algebraMap A k ϖ ≠ 0) {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s)
    (hB : ∀ s ≤ d, PropB hvt hR A ϖ s) (hC : ∀ s ≤ d, PropC hvt hR A ϖ s) (Λ : Dom R) (i : I)
    {ν : I →₀ ℕ} (hν : ν.degree = d) {x : IrreducibleModule R v Λ.1} (hx : x ∈ lat hvt hR A Λ)
    (hxw : x ∈ wsp Λ ν) {w : List I} (hxw' : x - fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ)
    (hx0 : x ∉ ϖ • lat hvt hR A Λ) : ∃ kk a u, IsStr hvt hR ϖ Λ i ν x kk a u := by
  set hv' := pow_ne_one_of_transcendental' hvt
  obtain ⟨j, u, huL, huw, huE, hsub⟩ := exists_string ϖ hϖv Λ i d hA hB hC hν hx hxw hxw' hx0
  have hun : u ∈ nodeWt R v _ i ((Λ.1 - R.rootSum ν) (R.coroot i) + 2 * j) :=
    mem_nodeWt_of_mem_add_nsmul i huw
  have hdF : dFV (hvt := hvt) (hR := hR) Λ i j u ∉ ϖ • lat hvt hR A Λ := fun h ↦
    hx0 (by simpa using add_mem hsub h)
  have hu0 : u ∉ ϖ • lat hvt hR A Λ := fun h ↦ hdF (by
    rw [← kashiwaraF_pow_of_primitive hv' _ i huE hun]
    exact kashiwaraF_pow_mem hv' _ i (fun _ hy ↦ kashiwaraF_mem_smul_lat Λ i hy) _ h)
  have hpos := TensorModule.nonneg_of_primitive hv' i (isInt hvt hR Λ) hun huE
    (fun h0 ↦ hu0 (by rw [h0]; exact zero_mem _))
  refine ⟨j, ((Λ.1 - R.rootSum ν) (R.coroot i) + 2 * j).toNat, u, hxw, huL, huw, huE,
    by omega, hu0, ?_, hsub⟩
  by_contra hj
  refine hdF ?_
  rw [IntegrableSl2.dF_eq_zero_of_primitive (pow_d_ne_zero i) (pow_d_ne_one hv' i) hun huE
    (by omega)]
  exact zero_mem _

/-- A string position `k ≥ 1` comes from a weight one step up. -/
lemma IsStr.exists_pred {Λ : Dom R} {i : I} {ν : I →₀ ℕ} {x : IrreducibleModule R v Λ.1}
    {kk a : ℕ} {u : IrreducibleModule R v Λ.1} (h : IsStr hvt hR ϖ Λ i ν x kk a u)
    (hk : 1 ≤ kk) : ∃ ν', ν = ν' + Finsupp.single i 1 := by
  obtain ⟨ν'', rfl⟩ := exists_eq_add_single hR (pow_ne_one_of_transcendental' hvt) Λ h.wt
    h.ne_zero
  refine ⟨ν'' + Finsupp.single i (kk - 1), ?_⟩
  rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel hk]

/-- `ẽᵢ x ≡ Fᵢ^{(k-1)} u` (`0` if `k = 0`). -/
lemma IsStr.eK_sub {Λ : Dom R} {i : I} {ν : I →₀ ℕ} {x : IrreducibleModule R v Λ.1}
    {kk a : ℕ} {u : IrreducibleModule R v Λ.1} {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s)
    (hν : ν.degree = d) (hϖv : algebraMap A k ϖ ≠ 0) (h : IsStr hvt hR ϖ Λ i ν x kk a u) :
    eK hvt hR Λ i x - (if kk = 0 then 0 else dFV (hvt := hvt) (hR := hR) Λ i (kk - 1) u) ∈
      ϖ • lat hvt hR A Λ := by
  have hw : x - dFV (hvt := hvt) (hR := hR) Λ i kk u ∈ wsp Λ ν :=
    sub_mem h.x_wt h.dFV_mem_weightSpace
  have := localE_smul hA Λ hν i 0 hϖv h.sub (by simpa using hw)
  rw [map_sub] at this
  split_ifs with hk
  · subst hk
    have key : eK hvt hR Λ i (dFV (hvt := hvt) (hR := hR) Λ i 0 u) = 0 := by
      rw [IntegrableSl2.dF_zero]
      exact IntegrableSl2.eTilde_of_primitive (pow_d_ne_zero i)
        (pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) h.E_smul h.prim.1
    rw [key, sub_zero] at this
    simpa using this
  · have hle := h.le
    have hja : ((kk - 1 : ℕ) : ℤ) < a := by omega
    have key : eK hvt hR Λ i (dFV (hvt := hvt) (hR := hR) Λ i (kk - 1 + 1) u) =
        dFV (hvt := hvt) (hR := hR) Λ i (kk - 1) u :=
      IntegrableSl2.eTilde_dF_succ (pow_d_ne_zero i)
        (pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) h.E_smul h.prim.1 hja
    rwa [show kk = (kk - 1) + 1 by omega, key] at this

/-! ### The tensor product rule -/

variable (v) in
/-- `V(λ₁) ⊗ V(λ₂)`. -/
abbrev TM (Λ₁ Λ₂ : Dom R) : Type _ :=
  TensorModule k (IrreducibleModule R v Λ₁.1) (IrreducibleModule R v Λ₂.1)

variable (hvt hR) in
include hvt hR in
lemma isIntT (Λ₁ Λ₂ : Dom R) : IsIntegrable R v (TM v Λ₁ Λ₂) :=
  TensorModule.isIntegrable (isInt hvt hR Λ₁) (isInt hvt hR Λ₂)

variable (hvt hR) in
/-- `ẽᵢ` on `V(λ₁) ⊗ V(λ₂)`. -/
abbrev eT (Λ₁ Λ₂ : Dom R) (i : I) : Module.End k (TM v Λ₁ Λ₂) :=
  kashiwaraE R v _ (pow_ne_one_of_transcendental' hvt) (isIntT hvt hR Λ₁ Λ₂) i

variable (hvt hR) in
/-- `f̃ᵢ` on `V(λ₁) ⊗ V(λ₂)`. -/
abbrev fT (Λ₁ Λ₂ : Dom R) (i : I) : Module.End k (TM v Λ₁ Λ₂) :=
  kashiwaraF R v _ (pow_ne_one_of_transcendental' hvt) (isIntT hvt hR Λ₁ Λ₂) i

variable (hvt hR A) in
/-- `L(λ₁) ⊗ L(λ₂)`. -/
abbrev LL (Λ₁ Λ₂ : Dom R) : Submodule A (TM v Λ₁ Λ₂) :=
  TensorModule.lattice k A (lat hvt hR A Λ₁) (lat hvt hR A Λ₂)

/-- `[x ⊗ y]` with `x ∈ ϖ L(λ₁)`, `y ∈ L(λ₂)` lies in `ϖ (L(λ₁) ⊗ L(λ₂))`. -/
lemma tmul_mem_smul_left {Λ₁ Λ₂ : Dom R} {x : IrreducibleModule R v Λ₁.1}
    {y : IrreducibleModule R v Λ₂.1} (hx : x ∈ ϖ • lat hvt hR A Λ₁) (hy : y ∈ lat hvt hR A Λ₂) :
    TensorModule.mk _ _ (x ⊗ₜ[k] y) ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  obtain ⟨x₀, hx₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [← smul_tmul']
  exact Submodule.smul_mem_pointwise_smul _ _ _ (TensorModule.tmul_mem_lattice hx₀ hy)

/-- `[x ⊗ y]` with `x ∈ L(λ₁)`, `y ∈ ϖ L(λ₂)` lies in `ϖ (L(λ₁) ⊗ L(λ₂))`. -/
lemma tmul_mem_smul_right {Λ₁ Λ₂ : Dom R} {x : IrreducibleModule R v Λ₁.1}
    {y : IrreducibleModule R v Λ₂.1} (hx : x ∈ lat hvt hR A Λ₁) (hy : y ∈ ϖ • lat hvt hR A Λ₂) :
    TensorModule.mk _ _ (x ⊗ₜ[k] y) ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  obtain ⟨y₀, hy₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
  rw [tmul_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (TensorModule.tmul_mem_lattice hx hy₀)

section Rule

variable [IsLocalRing A] (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖv : algebraMap A k ϖ = v⁻¹)
  {d₁ d₂ : ℕ} (hA₁ : ∀ s ≤ d₁, PropA hvt hR A s) (hA₂ : ∀ s ≤ d₂, PropA hvt hR A s)
  {Λ₁ Λ₂ : Dom R} {i : I} {ν₁ ν₂ : I →₀ ℕ} (hν₁ : ν₁.degree = d₁) (hν₂ : ν₂.degree = d₂)
  {x : IrreducibleModule R v Λ₁.1} {y : IrreducibleModule R v Λ₂.1} {k₁ k₂ a b : ℕ}
  {u : IrreducibleModule R v Λ₁.1} {u' : IrreducibleModule R v Λ₂.1}
  (hx : IsStr hvt hR ϖ Λ₁ i ν₁ x k₁ a u) (hy : IsStr hvt hR ϖ Λ₂ i ν₂ y k₂ b u')
include hϖ hϖv hA₁ hA₂ hν₁ hν₂ hx hy

/-- **Tensor product rule for `f̃ᵢ`** in bounded depth ([HK] Lemma 5.3.2 (2), library order):
`f̃ᵢ (x ⊗ y) ≡ x ⊗ f̃ᵢ y` if `εᵢ(x) < φᵢ(y)` and `≡ f̃ᵢ x ⊗ y` otherwise. -/
theorem fT_tmul :
    fT hvt hR Λ₁ Λ₂ i (TensorModule.mk _ _ (x ⊗ₜ[k] y)) -
      (if k₁ < b - k₂ then TensorModule.mk _ _ (x ⊗ₜ[k] fK hvt hR Λ₂ i y)
        else TensorModule.mk _ _ (fK hvt hR Λ₁ i x ⊗ₜ[k] y)) ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have h := TensorModule.kashiwaraF_tmul_sub_mem (pow_ne_one_of_transcendental' hvt)
    (isInt hvt hR Λ₁) (isInt hvt hR Λ₂) i (fun _ hy ↦ kashiwaraF_mem_lat Λ₁ i hy)
    (fun _ hy ↦ kashiwaraF_mem_lat Λ₂ i hy) (localE hA₁ Λ₁ hν₁ i) (localE hA₂ Λ₂ hν₂ i) hϖ hϖv
    hx.x_wt hy.mem_lat hy.x_wt hx.mem hx.wt hx.E_smul hx.node hx.ne_zero hx.le hy.mem hy.wt
    hy.E_smul hy.node hy.ne_zero hy.le hx.sub hy.sub
  have hfy := kashiwaraF_mem_smul_lat Λ₂ i hy.sub
  have hfx := kashiwaraF_mem_smul_lat Λ₁ i hx.sub
  rw [map_sub, kashiwaraF_dF hy.prim.1 hy.E_smul] at hfy
  rw [map_sub, kashiwaraF_dF hx.prim.1 hx.E_smul] at hfx
  split_ifs at h ⊢ with hc
  · have e : TensorModule.mk _ _ (x ⊗ₜ[k] fK hvt hR Λ₂ i y) -
        TensorModule.mk _ _ (dFV (hvt := hvt) (hR := hR) Λ₁ i k₁ u ⊗ₜ[k]
          dFV (hvt := hvt) (hR := hR) Λ₂ i (k₂ + 1) u') ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
      have := add_mem (tmul_mem_smul_left (y := fK hvt hR Λ₂ i y) hx.sub
        (kashiwaraF_mem_lat Λ₂ i hy.mem_lat)) (tmul_mem_smul_right (hx.dFV_mem k₁) hfy)
      convert this using 1
      rw [← map_add, ← map_sub, sub_tmul, tmul_sub]
      congr 1
      abel
    simpa using sub_mem h e
  · have e : TensorModule.mk _ _ (fK hvt hR Λ₁ i x ⊗ₜ[k] y) -
        TensorModule.mk _ _ (dFV (hvt := hvt) (hR := hR) Λ₁ i (k₁ + 1) u ⊗ₜ[k]
          dFV (hvt := hvt) (hR := hR) Λ₂ i k₂ u') ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
      have := add_mem (tmul_mem_smul_left (y := y) hfx hy.mem_lat)
        (tmul_mem_smul_right (hx.dFV_mem (k₁ + 1)) hy.sub)
      convert this using 1
      rw [← map_add, ← map_sub, sub_tmul, tmul_sub]
      congr 1
      abel
    simpa using sub_mem h e

/-- **Tensor product rule for `ẽᵢ`** in bounded depth ([HK] Lemma 5.3.2 (2), library order):
`ẽᵢ (x ⊗ y) ≡ x ⊗ ẽᵢ y` if `εᵢ(x) ≤ φᵢ(y)` and `≡ ẽᵢ x ⊗ y` otherwise. -/
theorem eT_tmul :
    eT hvt hR Λ₁ Λ₂ i (TensorModule.mk _ _ (x ⊗ₜ[k] y)) -
      (if k₁ ≤ b - k₂ then TensorModule.mk _ _ (x ⊗ₜ[k] eK hvt hR Λ₂ i y)
        else TensorModule.mk _ _ (eK hvt hR Λ₁ i x ⊗ₜ[k] y)) ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  have h := TensorModule.kashiwaraE_tmul_sub_mem (pow_ne_one_of_transcendental' hvt)
    (isInt hvt hR Λ₁) (isInt hvt hR Λ₂) i (fun _ hy ↦ kashiwaraF_mem_lat Λ₁ i hy)
    (fun _ hy ↦ kashiwaraF_mem_lat Λ₂ i hy) (localE hA₁ Λ₁ hν₁ i) (localE hA₂ Λ₂ hν₂ i) hϖ hϖv
    hx.x_wt hy.mem_lat hy.x_wt hx.mem hx.wt hx.E_smul hx.node hx.ne_zero hx.le hy.mem hy.wt
    hy.E_smul hy.node hy.ne_zero hy.le hx.sub hy.sub
  have hey := hy.eK_sub hA₂ hν₂ hϖ0
  have hex := hx.eK_sub hA₁ hν₁ hϖ0
  have heyL : eK hvt hR Λ₂ i y ∈ lat hvt hR A Λ₂ := localE hA₂ Λ₂ hν₂ i 0 hy.mem_lat
    (by simpa using hy.x_wt)
  have hexL : eK hvt hR Λ₁ i x ∈ lat hvt hR A Λ₁ := localE hA₁ Λ₁ hν₁ i 0 hx.mem_lat
    (by simpa using hx.x_wt)
  split_ifs at h ⊢ with hc hk
  · -- `k₂ = 0`
    subst hk
    simp only [↓reduceIte, sub_zero] at hey h
    exact sub_mem h (tmul_mem_smul_right hx.mem_lat hey)
  · simp only [hk, ↓reduceIte] at hey
    have e : TensorModule.mk _ _ (x ⊗ₜ[k] eK hvt hR Λ₂ i y) -
        TensorModule.mk _ _ (dFV (hvt := hvt) (hR := hR) Λ₁ i k₁ u ⊗ₜ[k]
          dFV (hvt := hvt) (hR := hR) Λ₂ i (k₂ - 1) u') ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
      have := add_mem (tmul_mem_smul_left (y := eK hvt hR Λ₂ i y) hx.sub heyL)
        (tmul_mem_smul_right (hx.dFV_mem k₁) hey)
      convert this using 1
      rw [← map_add, ← map_sub, sub_tmul, tmul_sub]
      congr 1
      abel
    simpa using sub_mem h e
  · have hk1 : k₁ ≠ 0 := by omega
    simp only [hk1, ↓reduceIte] at hex
    have e : TensorModule.mk _ _ (eK hvt hR Λ₁ i x ⊗ₜ[k] y) -
        TensorModule.mk _ _ (dFV (hvt := hvt) (hR := hR) Λ₁ i (k₁ - 1) u ⊗ₜ[k]
          dFV (hvt := hvt) (hR := hR) Λ₂ i k₂ u') ∈ ϖ • LL hvt hR A Λ₁ Λ₂ := by
      have := add_mem (tmul_mem_smul_left (y := y) hex hy.mem_lat)
        (tmul_mem_smul_right (hx.dFV_mem (k₁ - 1)) hy.sub)
      convert this using 1
      rw [← map_add, ← map_sub, sub_tmul, tmul_sub]
      congr 1
      abel
    simpa using sub_mem h e

end Rule

end GrandLoop

end LieLean.QuantumGroup

end
