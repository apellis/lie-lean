/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorRule
import Mathlib.RingTheory.Nakayama

/-!
# The tensor product rule for two strings

Let `η ∈ M₁ᵃ`, `ζ ∈ M₂ᵇ` be nonzero primitive vectors, `uᵢ = F^{(i)} η`, `vⱼ = F^{(j)} ζ`, and let
`A` be a local ring with `ϖ ∈ A` a non-unit mapping to `q`, acting compatibly on `M₁`. Let
`L ⊆ M₁ ⊗ M₂` be the `A`-span of the `uᵢ ⊗ vⱼ` (`i ≤ a`, `j ≤ b`). Then:

* `L` is the `A`-span of the strings `F^{(r)} w_s` of the primitive vectors `w_s`
  (`QuantumGroup.IntegrableSl2.tensorPieceLattice_eq`, by Nakayama's lemma);
* `L` is stable under the Kashiwara operators of `M₁ ⊗ M₂`
  (`QuantumGroup.IntegrableSl2.fTilde_mem_tensorPieceLattice`, `eTilde_mem_tensorPieceLattice`);
* modulo `ϖ L`, `f̃ (uᵢ ⊗ vⱼ) ≡ u_{i+1} ⊗ vⱼ` if `j < a - i` and `≡ uᵢ ⊗ v_{j+1}` otherwise
  (`QuantumGroup.IntegrableSl2.fTilde_tensorPiece_sub`), and similarly for `ẽ`
  (`QuantumGroup.IntegrableSl2.eTilde_tensorPiece_sub`).
This is the tensor product rule for `B(a) ⊗ B(b)` ([HK] Thm. 4.4.3, (4.12); [Kas] §4): with
`φ(uᵢ) = a - i`, `ε(vⱼ) = j`, `f̃` acts on the first factor if `φ > ε` and on the second otherwise.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.4.
* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995).
-/

open TensorProduct Finset Pointwise

namespace LieLean.QuantumGroup

namespace IntegrableSl2

/-! ### Indices -/

/-- The inverse of `tensorIndex`: the string `(s, r)` through `uᵢ ⊗ vⱼ`. -/
def tensorString (a i j : ℕ) : ℕ × ℕ := if i + j ≤ a then (j, i) else (a - i, 2 * i + j - a)

lemma tensorString_spec {a b i j : ℕ} (hi : i ≤ a) (hj : j ≤ b) :
    (tensorString a i j).1 ≤ a ∧ (tensorString a i j).1 ≤ b ∧
      (tensorString a i j).2 ≤ a + b - 2 * (tensorString a i j).1 ∧
      tensorIndex a (tensorString a i j).1 (tensorString a i j).2 = (i, j) := by
  by_cases h : i + j ≤ a
  · simp only [tensorString, h, ↓reduceIte]
    refine ⟨by omega, by omega, by omega, ?_⟩
    simp only [tensorIndex, show i ≤ a - j by omega, ↓reduceIte]
  · simp only [tensorString, h, ↓reduceIte]
    refine ⟨by omega, by omega, by omega, ?_⟩
    simp only [tensorIndex, show ¬ 2 * i + j - a ≤ a - (a - i) by omega, ↓reduceIte,
      Prod.mk.injEq]
    omega

/-- The next position on the string of `w_s`. -/
lemma tensorIndex_succ {a s : ℕ} (hs : s ≤ a) (r : ℕ) :
    tensorIndex a s (r + 1) = if (tensorIndex a s r).2 < a - (tensorIndex a s r).1 then
      ((tensorIndex a s r).1 + 1, (tensorIndex a s r).2)
      else ((tensorIndex a s r).1, (tensorIndex a s r).2 + 1) := by
  unfold tensorIndex
  split_ifs <;> simp only [Prod.mk.injEq, true_and] at * <;> omega

/-- The previous position on the string of `w_s`. -/
lemma tensorIndex_pred {a s : ℕ} (hs : s ≤ a) (r : ℕ) :
    tensorIndex a s r = if (tensorIndex a s (r + 1)).2 ≤ a - (tensorIndex a s (r + 1)).1 then
      ((tensorIndex a s (r + 1)).1 - 1, (tensorIndex a s (r + 1)).2)
      else ((tensorIndex a s (r + 1)).1, (tensorIndex a s (r + 1)).2 - 1) := by
  unfold tensorIndex
  split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true] at * <;> omega

lemma tensorIndex_zero (a s : ℕ) : tensorIndex a s 0 = (0, s) := by simp [tensorIndex]

/-! ### The lattice of a tensor product of two strings -/

section Piece

variable {k : Type*} [Field k] {q : k} {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁]
  [AddCommGroup M₂] [Module k M₂] (V₁ : IntegrableSl2 q M₁) (V₂ : IntegrableSl2 q M₂)
  (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
  {A : Type*} [CommRing A] [Algebra A k] [IsLocalRing A] [Module A M₁] [IsScalarTower A k M₁]
  {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖq : algebraMap A k ϖ = q)
  {a b : ℕ} {η : M₁} {ζ : M₂}

variable (A a b η ζ) in
/-- The `A`-span of the `uᵢ ⊗ vⱼ`, `i ≤ a`, `j ≤ b`. -/
def tensorPieceLattice : Submodule A (M₁ ⊗[k] M₂) :=
  Submodule.span A (Set.range fun x : Fin (a + 1) × Fin (b + 1) ↦
    V₁.dF x.1 η ⊗ₜ[k] V₂.dF x.2 ζ)

omit [IsLocalRing A] in
include hq0 hq in
lemma tmul_mem_tensorPieceLattice (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) (i j : ℕ) :
    V₁.dF i η ⊗ₜ[k] V₂.dF j ζ ∈ tensorPieceLattice V₁ V₂ A a b η ζ := by
  by_cases hi : i ≤ a
  · by_cases hj : j ≤ b
    · exact Submodule.subset_span ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), rfl⟩
    · rw [dF_eq_zero_of_primitive hq0 hq hζ.1 hζ.2 (by omega), tmul_zero]
      exact zero_mem _
  · rw [dF_eq_zero_of_primitive hq0 hq hη.1 hη.2 (by omega), zero_tmul]
    exact zero_mem _

omit [IsLocalRing A] in
include hq0 hq in
lemma smallSpan_le_smul (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) {y : M₁ ⊗[k] M₂}
    (hy : y ∈ smallSpan k ϖ (fun p ↦ V₁.dF p.1 η ⊗ₜ[k] V₂.dF p.2 ζ)) :
    y ∈ ϖ • tensorPieceLattice V₁ V₂ A a b η ζ := by
  induction hy using AddSubmonoid.closure_induction with
  | mem y hy =>
    obtain ⟨κ, p, ⟨α, rfl⟩, rfl⟩ := hy
    rw [zpow_one, ← map_mul, algebraMap_smul, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _
      (Submodule.smul_mem _ _ (tmul_mem_tensorPieceLattice V₁ V₂ hq0 hq hη hζ p.1 p.2))
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz

include hϖ hϖq in
/-- The vectors `F^{(r)} w_s` lie in the lattice. -/
lemma tensor_dF_tensorHigh_mem (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) (hη0 : η ≠ 0)
    (hζ0 : ζ ≠ 0) {s : ℕ} (hsa : s ≤ a) (hsb : s ≤ b) {r : ℕ} (hr : r ≤ a + b - 2 * s) :
    (tensor V₁ V₂ hq0 hq).dF r (tensorHigh V₁ V₂ a b η ζ s) ∈
      tensorPieceLattice V₁ V₂ A a b η ζ := by
  have h := tensor_dF_tensorHigh_sub_tensorIndex V₁ V₂ hq0 hq hϖ hϖq hη hζ hη0 hζ0 hsa hsb hr
  have h' := smallSpan_le_smul V₁ V₂ hq0 hq hη hζ h
  have := add_mem (Submodule.smul_le_self_of_tower ϖ _ h')
    (tmul_mem_tensorPieceLattice V₁ V₂ hq0 hq hη hζ (tensorIndex a s r).1 (tensorIndex a s r).2)
  rwa [sub_add_cancel] at this

variable (A a b η ζ) in
/-- The `A`-span of the strings `F^{(r)} w_s`. -/
def tensorPieceStrings : Submodule A (M₁ ⊗[k] M₂) :=
  Submodule.span A {x | ∃ s r : ℕ, s ≤ a ∧ s ≤ b ∧ r ≤ a + b - 2 * s ∧
    x = (tensor V₁ V₂ hq0 hq).dF r (tensorHigh V₁ V₂ a b η ζ s)}

include hϖ hϖq in
/-- The lattice of a tensor product of two strings is spanned by the strings of the `w_s`
(Nakayama's lemma). -/
theorem tensorPieceLattice_eq (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) (hη0 : η ≠ 0)
    (hζ0 : ζ ≠ 0) :
    tensorPieceLattice V₁ V₂ A a b η ζ = tensorPieceStrings V₁ V₂ hq0 hq A a b η ζ := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {ϖ})
      (Submodule.fg_span (Set.finite_range _))
      ((Ideal.span_le.2 (by simpa using hϖ)).trans (IsLocalRing.maximalIdeal_le_jacobson _)) ?_
    rw [Submodule.ideal_span_singleton_smul]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨i, j⟩, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := tensorString_spec (b := b) (Nat.lt_succ_iff.1 i.2)
      (Nat.lt_succ_iff.1 j.2)
    set s := (tensorString a i j).1
    set r := (tensorString a i j).2
    have h := tensor_dF_tensorHigh_sub_tensorIndex V₁ V₂ hq0 hq hϖ hϖq hη hζ hη0 hζ0 h1 h2 h3
    rw [h4] at h
    have h' := smallSpan_le_smul V₁ V₂ hq0 hq hη hζ h
    have hmem : (tensor V₁ V₂ hq0 hq).dF r (tensorHigh V₁ V₂ a b η ζ s) ∈
        tensorPieceStrings V₁ V₂ hq0 hq A a b η ζ :=
      Submodule.subset_span ⟨s, r, h1, h2, h3, rfl⟩
    have := Submodule.sub_mem_sup hmem h'
    simpa using this
  · rintro _ ⟨s, r, h1, h2, h3, rfl⟩
    exact tensor_dF_tensorHigh_mem V₁ V₂ hq0 hq hϖ hϖq hη hζ hη0 hζ0 h1 h2 h3

lemma tensorHigh_mem_wt' (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) {s : ℕ} (h : 2 * s ≤ a + b) :
    tensorHigh V₁ V₂ a b η ζ s ∈ (tensor V₁ V₂ hq0 hq).wt ((a + b - 2 * s : ℕ) : ℤ) := by
  convert tensorHigh_mem_wt V₁ V₂ hq0 hq hη hζ s using 2
  push_cast [h]
  ring

include hϖ hϖq in
/-- The lattice of a tensor product of two strings is stable under `f̃`. -/
theorem fTilde_mem_tensorPieceLattice (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) (hη0 : η ≠ 0)
    (hζ0 : ζ ≠ 0) {x : M₁ ⊗[k] M₂} (hx : x ∈ tensorPieceLattice V₁ V₂ A a b η ζ) :
    (tensor V₁ V₂ hq0 hq).fTilde hq0 hq x ∈ tensorPieceLattice V₁ V₂ A a b η ζ := by
  rw [tensorPieceLattice_eq V₁ V₂ hq0 hq hϖ hϖq hη hζ hη0 hζ0] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, r, h1, h2, h3, rfl⟩ := hx
    have hw := tensorHigh_mem_wt' V₁ V₂ hq0 hq hη hζ (s := s) (by omega)
    have hwE := tensor_E_tensorHigh V₁ V₂ hq0 hq hη hζ h1
    rw [fTilde_dF hq0 hq hwE hw]
    by_cases hr : r + 1 ≤ a + b - 2 * s
    · exact Submodule.subset_span ⟨s, r + 1, h1, h2, hr, rfl⟩
    · rw [dF_eq_zero_of_primitive hq0 hq hw hwE (by push_cast; omega)]
      exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c hx

include hϖ hϖq in
/-- The lattice of a tensor product of two strings is stable under `ẽ`. -/
theorem eTilde_mem_tensorPieceLattice (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) (hη0 : η ≠ 0)
    (hζ0 : ζ ≠ 0) {x : M₁ ⊗[k] M₂} (hx : x ∈ tensorPieceLattice V₁ V₂ A a b η ζ) :
    (tensor V₁ V₂ hq0 hq).eTilde hq0 hq x ∈ tensorPieceLattice V₁ V₂ A a b η ζ := by
  rw [tensorPieceLattice_eq V₁ V₂ hq0 hq hϖ hϖq hη hζ hη0 hζ0] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, r, h1, h2, h3, rfl⟩ := hx
    have hw := tensorHigh_mem_wt' V₁ V₂ hq0 hq hη hζ (s := s) (by omega)
    have hwE := tensor_E_tensorHigh V₁ V₂ hq0 hq hη hζ h1
    rcases r with _ | r
    · rw [dF_zero, eTilde_of_primitive hq0 hq hwE hw]
      exact zero_mem _
    · rw [eTilde_dF_succ hq0 hq hwE hw (by omega)]
      exact Submodule.subset_span ⟨s, r, h1, h2, by omega, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c hx

omit [IsLocalRing A] in
include hq0 hq in
/-- The lattice of a tensor product of two strings is graded. -/
theorem wtProj_mem_tensorPieceLattice (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) (n : ℤ)
    {x : M₁ ⊗[k] M₂} (hx : x ∈ tensorPieceLattice V₁ V₂ A a b η ζ) :
    (tensor V₁ V₂ hq0 hq).wtProj n x ∈ tensorPieceLattice V₁ V₂ A a b η ζ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨i, j⟩, rfl⟩ := hx
    rw [wtProj_of_mem (tmul_mem_tensor_wt hq0 hq (dF_mem hη.1 i) (dF_mem hζ.1 j))]
    split_ifs
    · exact tmul_mem_tensorPieceLattice V₁ V₂ hq0 hq hη hζ i j
    · exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c hx

include hϖ hϖq in
/-- **Tensor product rule for `f̃`** ([HK] (4.12)): modulo `ϖ L`,
`f̃ (uᵢ ⊗ vⱼ) ≡ u_{i+1} ⊗ vⱼ` if `j < a - i` and `≡ uᵢ ⊗ v_{j+1}` otherwise. -/
theorem fTilde_tensorPiece_sub (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) (hη0 : η ≠ 0)
    (hζ0 : ζ ≠ 0) {i j : ℕ} (hi : i ≤ a) (hj : j ≤ b) :
    (tensor V₁ V₂ hq0 hq).fTilde hq0 hq (V₁.dF i η ⊗ₜ[k] V₂.dF j ζ) -
      (if j < a - i then V₁.dF (i + 1) η ⊗ₜ[k] V₂.dF j ζ else V₁.dF i η ⊗ₜ[k] V₂.dF (j + 1) ζ) ∈
      ϖ • tensorPieceLattice V₁ V₂ A a b η ζ := by
  set T := tensor V₁ V₂ hq0 hq
  set L := tensorPieceLattice V₁ V₂ A a b η ζ
  obtain ⟨h1, h2, h3, h4⟩ := tensorString_spec (b := b) hi hj
  set s := (tensorString a i j).1
  set r := (tensorString a i j).2
  have hw := tensorHigh_mem_wt' V₁ V₂ hq0 hq hη hζ (s := s) (by omega)
  have hwE := tensor_E_tensorHigh V₁ V₂ hq0 hq hη hζ h1
  have hd := smallSpan_le_smul V₁ V₂ hq0 hq hη hζ
    (tensor_dF_tensorHigh_sub_tensorIndex V₁ V₂ hq0 hq hϖ hϖq hη hζ hη0 hζ0 h1 h2 h3)
  rw [h4] at hd
  have hfd := LinearMap.map_mem_smul_of_mem (f := T.fTilde hq0 hq) ϖ
    (fun x hx ↦ fTilde_mem_tensorPieceLattice V₁ V₂ hq0 hq hϖ hϖq hη hζ hη0 hζ0 hx) hd
  rw [map_sub, fTilde_dF hq0 hq hwE hw] at hfd
  -- the next vector
  have hnext : T.dF (r + 1) (tensorHigh V₁ V₂ a b η ζ s) -
      (if j < a - i then V₁.dF (i + 1) η ⊗ₜ[k] V₂.dF j ζ
        else V₁.dF i η ⊗ₜ[k] V₂.dF (j + 1) ζ) ∈ ϖ • L := by
    have hs := tensorIndex_succ (show s ≤ a from h1) r
    rw [h4] at hs
    have hv : (if j < a - i then V₁.dF (i + 1) η ⊗ₜ[k] V₂.dF j ζ
        else V₁.dF i η ⊗ₜ[k] V₂.dF (j + 1) ζ) =
        V₁.dF (tensorIndex a s (r + 1)).1 η ⊗ₜ[k] V₂.dF (tensorIndex a s (r + 1)).2 ζ := by
      rw [hs]; split_ifs <;> rfl
    rw [hv]
    by_cases hr : r + 1 ≤ a + b - 2 * s
    · exact smallSpan_le_smul V₁ V₂ hq0 hq hη hζ
        (tensor_dF_tensorHigh_sub_tensorIndex V₁ V₂ hq0 hq hϖ hϖq hη hζ hη0 hζ0 h1 h2 hr)
    · have hb : b < (tensorIndex a s (r + 1)).2 := by
        unfold tensorIndex; split_ifs <;> simp only at * <;> omega
      rw [dF_eq_zero_of_primitive hq0 hq hw hwE (by push_cast; omega),
        dF_eq_zero_of_primitive hq0 hq hζ.1 hζ.2 (by omega), tmul_zero, sub_zero]
      exact zero_mem _
  have := sub_mem hnext hfd
  rwa [sub_sub_sub_cancel_left] at this

include hϖ hϖq in
/-- **Tensor product rule for `ẽ`** ([HK] (4.11)): modulo `ϖ L`,
`ẽ (uᵢ ⊗ vⱼ) ≡ u_{i-1} ⊗ vⱼ` (`0` if `i = 0`) if `j ≤ a - i` and `≡ uᵢ ⊗ v_{j-1}` otherwise. -/
theorem eTilde_tensorPiece_sub (hη : η ∈ V₁.prim a) (hζ : ζ ∈ V₂.prim b) (hη0 : η ≠ 0)
    (hζ0 : ζ ≠ 0) {i j : ℕ} (hi : i ≤ a) (hj : j ≤ b) :
    (tensor V₁ V₂ hq0 hq).eTilde hq0 hq (V₁.dF i η ⊗ₜ[k] V₂.dF j ζ) -
      (if j ≤ a - i then (if i = 0 then 0 else V₁.dF (i - 1) η ⊗ₜ[k] V₂.dF j ζ)
        else V₁.dF i η ⊗ₜ[k] V₂.dF (j - 1) ζ) ∈
      ϖ • tensorPieceLattice V₁ V₂ A a b η ζ := by
  set T := tensor V₁ V₂ hq0 hq
  set L := tensorPieceLattice V₁ V₂ A a b η ζ
  obtain ⟨h1, h2, h3, h4⟩ := tensorString_spec (b := b) hi hj
  set s := (tensorString a i j).1
  set r := (tensorString a i j).2
  clear_value s r
  have hw := tensorHigh_mem_wt' V₁ V₂ hq0 hq hη hζ (s := s) (by omega)
  have hwE := tensor_E_tensorHigh V₁ V₂ hq0 hq hη hζ h1
  have hd := smallSpan_le_smul V₁ V₂ hq0 hq hη hζ
    (tensor_dF_tensorHigh_sub_tensorIndex V₁ V₂ hq0 hq hϖ hϖq hη hζ hη0 hζ0 h1 h2 h3)
  rw [h4] at hd
  have hed := LinearMap.map_mem_smul_of_mem (f := T.eTilde hq0 hq) ϖ
    (fun x hx ↦ eTilde_mem_tensorPieceLattice V₁ V₂ hq0 hq hϖ hϖq hη hζ hη0 hζ0 hx) hd
  rw [map_sub] at hed
  rcases hr : r with _ | r'
  · -- `r = 0`: `(i, j) = (0, s)`
    have h0 : tensorIndex a s 0 = (i, j) := hr ▸ h4
    rw [tensorIndex_zero] at h0
    simp only [Prod.mk.injEq] at h0
    have hi0 : i = 0 := h0.1.symm
    have hcond : j ≤ a - 0 := by omega
    rw [hr, dF_zero, eTilde_of_primitive hq0 hq hwE hw, zero_sub, neg_mem_iff] at hed
    simp only [hi0, hcond, ↓reduceIte, sub_zero]
    simpa only [hi0] using hed
  · rw [hr, eTilde_dF_succ hq0 hq hwE hw (by omega)] at hed
    have hp := tensorIndex_pred (show s ≤ a from h1) r'
    rw [← hr, h4] at hp
    have hprev : T.dF r' (tensorHigh V₁ V₂ a b η ζ s) -
        (if j ≤ a - i then (if i = 0 then 0 else V₁.dF (i - 1) η ⊗ₜ[k] V₂.dF j ζ)
          else V₁.dF i η ⊗ₜ[k] V₂.dF (j - 1) ζ) ∈ ϖ • L := by
      have hc := smallSpan_le_smul V₁ V₂ hq0 hq hη hζ
        (tensor_dF_tensorHigh_sub_tensorIndex V₁ V₂ hq0 hq hϖ hϖq hη hζ hη0 hζ0 h1 h2
          (r := r') (by omega))
      rw [hp] at hc
      by_cases hc1 : j ≤ a - i
      · have hi0 : i ≠ 0 := by
          intro hi0
          subst hi0
          have := h4
          unfold tensorIndex at this
          rw [hr] at this
          split_ifs at this <;> simp only [Prod.mk.injEq] at this <;> omega
        simpa only [hc1, hi0, ↓reduceIte] using hc
      · simpa only [hc1, ↓reduceIte] using hc
    have := sub_mem hprev hed
    rwa [sub_sub_sub_cancel_left] at this

end Piece

end IntegrableSl2

end LieLean.QuantumGroup
