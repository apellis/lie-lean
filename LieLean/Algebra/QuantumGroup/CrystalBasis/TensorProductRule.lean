/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Sl2Structure
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorCrystalBase

/-!
# The tensor product rule for crystal bases of `U_q(𝔰𝔩₂)`-modules

Let `(L₁, B₁)`, `(L₂, B₂)` be crystal bases of finite-dimensional integrable
`U_q(𝔰𝔩₂)`-modules `M₁`, `M₂` over a local ring `A` with fraction field `k`, at a non-unit `c`,
and let `ϖ ∈ cA` be an element of the maximal ideal with image `q` in `k`. By
`QuantumGroup.IntegrableSl2.IsCrystalBase.eq_stringLattice` both are string lattices, so
`QuantumGroup.IntegrableSl2.isCrystalBase_tensorLattice` applies:

* `QuantumGroup.IntegrableSl2.IsCrystalBase.tensorLattice_eq`: the lattice of that theorem is
  `L₁ ⊗ L₂`, the `A`-span of the `x ⊗ y` (`x ∈ L₁`, `y ∈ L₂`);
* `QuantumGroup.IntegrableSl2.IsCrystalBase.isCrystalBase_tensor`: `L₁ ⊗ L₂` with the classes of
  the products of the string vectors representing `B₁` and `B₂` is a crystal base of `M₁ ⊗ M₂`
  (with Kashiwara's coproduct), on which `ẽ`, `f̃` act by the tensor product rule.

This is [HK] Thm. 4.4.1 for `𝔰𝔩₂` (stated there for `A` the localization of `ℚ(q)` at `q = 0`
and Kashiwara's coproduct).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.4.
-/

open TensorProduct

namespace LieLean.QuantumGroup

namespace IntegrableSl2

namespace IsCrystalBase

variable {k : Type*} [Field k] {q : k} {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁]
  [AddCommGroup M₂] [Module k M₂] {V₁ : IntegrableSl2 q M₁} {V₂ : IntegrableSl2 q M₂}
  {hq0 : q ≠ 0} {hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M₁] [IsScalarTower A k M₁]
  [Module A M₂] [IsScalarTower A k M₂]
  {L₁ : Submodule A M₁} {L₂ : Submodule A M₂} {c : A}
  {B₁ : Set (L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁))}
  {B₂ : Set (L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂))}
  (hB₁ : V₁.IsCrystalBase hq0 hq L₁ c B₁) (hB₂ : V₂.IsCrystalBase hq0 hq L₂ c B₂)
  (hc : ¬IsUnit c)

variable [IsLocalRing A] [IsFractionRing A k] [FiniteDimensional k M₁] [FiniteDimensional k M₂]

/-- The lattice of the tensor product rule is `L₁ ⊗ L₂`. -/
theorem tensorLattice_eq :
    tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A =
      Submodule.span A (Set.image2 (fun x y ↦ x ⊗ₜ[k] y) (L₁ : Set M₁) (L₂ : Set M₂)) := by
  apply le_antisymm
  · rw [tensorLattice, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact Submodule.subset_span ⟨_, hB₁.strVec_mem hc x.1, _, hB₂.strVec_mem hc x.2, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    set T := tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A
    rw [← hB₂.span_strVec hc] at hy
    rw [← hB₁.span_strVec hc] at hx
    change x ⊗ₜ[k] y ∈ T
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact Submodule.subset_span ⟨(i, j), rfl⟩
      | zero => simp
      | add y y' _ _ h h' => rw [tmul_add]; exact T.add_mem h h'
      | smul a y _ h =>
        rw [← algebraMap_smul k a y, tmul_smul, algebraMap_smul]
        exact T.smul_mem a h
    | zero => simp
    | add x x' _ _ h h' => rw [add_tmul]; exact T.add_mem h h'
    | smul a x _ h =>
      rw [← algebraMap_smul k a x, ← smul_tmul', algebraMap_smul]
      exact T.smul_mem a h

include hB₁ hB₂ hc in
/-- **Tensor product rule** ([HK] Thm. 4.4.1 for `𝔰𝔩₂`): if `(L₁, B₁)`, `(L₂, B₂)` are crystal
bases of finite-dimensional integrable `U_q(𝔰𝔩₂)`-modules over a local ring `A` with fraction
field `k`, then `L₁ ⊗ L₂` (`tensorLattice_eq`) with the classes of `u ⊗ v`, `u`, `v` the string
vectors lifting the elements of `B₁`, `B₂`, is a crystal base of `M₁ ⊗ M₂`; `ẽ`, `f̃` act on it by
the tensor product rule (`fTilde_tensorVec_sub`, `eTilde_tensorVec_sub`). Here `ϖ ∈ cA` lies in
the maximal ideal and maps to `q`. -/
theorem isCrystalBase_tensor {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
    (hϖq : algebraMap A k ϖ = q) (hϖc : ϖ ∈ Ideal.span {c}) :
    (tensor V₁ V₂ hq0 hq).IsCrystalBase hq0 hq
      (tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A) c
      (Set.range fun x ↦ Submodule.Quotient.mk
        (⟨tensorVec V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) x,
          tensorVec_mem V₁ V₂ _ _ _ _ x⟩ :
          tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A)) := by
  obtain ⟨hη₁, hind₁, hspan₁, -⟩ := hB₁.eq_stringLattice hc
  obtain ⟨hη₂, hind₂, hspan₂, -⟩ := hB₂.eq_stringLattice hc
  exact isCrystalBase_tensorLattice hq0 hq hϖ hϖq hη₁ hη₂ hind₁ hind₂ hspan₁ hspan₂ hc hϖc

end IsCrystalBase

end IntegrableSl2

end LieLean.QuantumGroup
