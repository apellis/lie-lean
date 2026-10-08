/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorCrystal

/-!
# Tensor products of crystal bases of integrable `U_q(𝔰𝔩₂)`-modules

Let `M₁`, `M₂` be integrable `U_q(𝔰𝔩₂)`-modules with string bases: primitive vectors
`η₁ₜ ∈ M₁^{p₁ₜ}` whose members of each weight form a basis of the primitive vectors of that
weight, and similarly `η₂ₜ`. Their crystal bases are the `A`-spans `L₁`, `L₂` of the
`F^{(i)} η₁ₜ`, `F^{(j)} η₂ₜ` (`QuantumGroup.IntegrableSl2.isCrystalBase_stringLattice`). Let `A`
be a local ring with `ϖ ∈ A` a non-unit mapping to `q`, `A ⊆ k`, and `c ∈ A` a non-unit with
`ϖ ∈ c A`.

**Tensor product rule** ([HK] Thm. 4.4.1 for `𝔰𝔩₂`, Kashiwara's coproduct): the `A`-span
`L₁ ⊗ L₂` of the `F^{(i)} η₁ₜ ⊗ F^{(j)} η₂ₜ'`, with the classes of these vectors in
`(L₁ ⊗ L₂) / c (L₁ ⊗ L₂)`, is a crystal base of `M₁ ⊗ M₂`
(`QuantumGroup.IntegrableSl2.isCrystalBase_tensorLattice`), and on these classes `f̃` acts on
the first factor if `φ > ε` and on the second otherwise (`QuantumGroup.IntegrableSl2.fTilde_tensorVec_sub`, positions `nextPos`),
where `φ(F^{(i)} η) = p - i` and `ε(F^{(j)} η') = j`; similarly for `ẽ`
(`QuantumGroup.IntegrableSl2.eTilde_tensorVec_sub`, `prevPos`).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.4.
-/

open TensorProduct Finset Pointwise

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁]
  [AddCommGroup M₂] [Module k M₂] (V₁ : IntegrableSl2 q M₁) (V₂ : IntegrableSl2 q M₂)
  (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
  {ι₁ ι₂ : Type*} (p₁ : ι₁ → ℕ) (p₂ : ι₂ → ℕ) (η₁ : ι₁ → M₁) (η₂ : ι₂ → M₂)

/-! ### Positions in a tensor product of strings -/

/-- The positions `(F^{(i)} η₁ₜ, F^{(j)} η₂ₜ')` of the tensor product of two string bases. -/
abbrev TensorPos := (Σ t, Fin (p₁ t + 1)) × (Σ t, Fin (p₂ t + 1))

variable {p₁ p₂} in
/-- The position reached by `f̃` (the tensor product rule), if any. -/
def nextPos (x : TensorPos p₁ p₂) : Option (TensorPos p₁ p₂) :=
  if h : (x.2.2 : ℕ) < p₁ x.1.1 - x.1.2 then
    some (⟨x.1.1, ⟨x.1.2 + 1, by omega⟩⟩, x.2)
  else if h' : (x.2.2 : ℕ) + 1 ≤ p₂ x.2.1 then
    some (x.1, ⟨x.2.1, ⟨x.2.2 + 1, by omega⟩⟩)
  else none

variable {p₁ p₂} in
/-- The position reached by `ẽ` (the tensor product rule), if any. -/
def prevPos (x : TensorPos p₁ p₂) : Option (TensorPos p₁ p₂) :=
  if (x.2.2 : ℕ) ≤ p₁ x.1.1 - x.1.2 then
    if h : (x.1.2 : ℕ) = 0 then none else some (⟨x.1.1, ⟨x.1.2 - 1, by omega⟩⟩, x.2)
  else some (x.1, ⟨x.2.1, ⟨x.2.2 - 1, by omega⟩⟩)

lemma tensorPos_ext {x y : TensorPos p₁ p₂} (h1 : x.1.1 = y.1.1) (h2 : (x.1.2 : ℕ) = y.1.2)
    (h3 : x.2.1 = y.2.1) (h4 : (x.2.2 : ℕ) = y.2.2) : x = y := by
  obtain ⟨⟨t₁, i⟩, ⟨t₂, j⟩⟩ := x
  obtain ⟨⟨t₁', i'⟩, ⟨t₂', j'⟩⟩ := y
  simp only at h1 h2 h3 h4
  subst h1 h3
  rw [Fin.ext h2, Fin.ext h4]

lemma tensorPos_eq_iff {x y : TensorPos p₁ p₂} :
    x = y ↔ x.1.1 = y.1.1 ∧ (x.1.2 : ℕ) = y.1.2 ∧ x.2.1 = y.2.1 ∧ (x.2.2 : ℕ) = y.2.2 :=
  ⟨fun h ↦ by subst h; simp, fun ⟨h1, h2, h3, h4⟩ ↦ tensorPos_ext p₁ p₂ h1 h2 h3 h4⟩

/-- `f̃ b = b' ↔ ẽ b' = b` on positions. -/
lemma nextPos_eq_some_iff (x y : TensorPos p₁ p₂) : nextPos x = some y ↔ prevPos y = some x := by
  constructor
  · intro h
    obtain ⟨⟨t₁, i, hi⟩, ⟨t₂, j, hj⟩⟩ := x
    simp only [nextPos] at h
    split_ifs at h with h1 h2
    · obtain rfl := Option.some.inj h.symm
      simp only [prevPos, show j ≤ p₁ t₁ - (i + 1) by omega, show ¬ i + 1 = 0 by omega,
        ↓reduceIte, ↓reduceDIte, Option.some.injEq]
      exact tensorPos_ext p₁ p₂ rfl (by simp) rfl rfl
    · obtain rfl := Option.some.inj h.symm
      simp only [prevPos, show ¬ j + 1 ≤ p₁ t₁ - i by omega, ↓reduceIte, Option.some.injEq]
      exact tensorPos_ext p₁ p₂ rfl rfl rfl (by simp)
  · intro h
    obtain ⟨⟨t₁, i, hi⟩, ⟨t₂, j, hj⟩⟩ := y
    simp only [prevPos] at h
    split_ifs at h with h1 h2
    · obtain rfl := Option.some.inj h.symm
      simp only [nextPos, show j < p₁ t₁ - (i - 1) by omega, ↓reduceDIte, Option.some.injEq]
      exact tensorPos_ext p₁ p₂ rfl (by simp; omega) rfl rfl
    · obtain rfl := Option.some.inj h.symm
      simp only [nextPos, show ¬ j - 1 < p₁ t₁ - i by omega, show j - 1 + 1 ≤ p₂ t₂ by omega,
        ↓reduceDIte, Option.some.injEq]
      exact tensorPos_ext p₁ p₂ rfl rfl rfl (by simp; omega)

/-! ### The tensor product lattice -/

lemma _root_.Submodule.mem_smul_of_le {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    {P Q : Submodule R N} (hPQ : P ≤ Q) (c : R) {y : N} (hy : y ∈ c • P) : y ∈ c • Q := by
  obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
  exact Submodule.smul_mem_pointwise_smul _ _ _ (hPQ hz)

/-- The vector `F^{(i)} η₁ₜ ⊗ F^{(j)} η₂ₜ'` at a position. -/
noncomputable def tensorVec (x : TensorPos p₁ p₂) : M₁ ⊗[k] M₂ :=
  V₁.dF x.1.2 (η₁ x.1.1) ⊗ₜ[k] V₂.dF x.2.2 (η₂ x.2.1)

/-- The vector at an optional position (`0` for `none`). -/
noncomputable def tensorVecOpt (o : Option (TensorPos p₁ p₂)) : M₁ ⊗[k] M₂ :=
  o.elim 0 (tensorVec V₁ V₂ p₁ p₂ η₁ η₂)

section Lattice

variable {A : Type*} [CommRing A] [Algebra A k] [Module A M₁] [IsScalarTower A k M₁]

variable (A) in
/-- The `A`-span `L₁ ⊗ L₂` of the vectors `F^{(i)} η₁ₜ ⊗ F^{(j)} η₂ₜ'`. -/
def tensorLattice : Submodule A (M₁ ⊗[k] M₂) :=
  Submodule.span A (Set.range (tensorVec V₁ V₂ p₁ p₂ η₁ η₂))

lemma tensorVec_mem (x : TensorPos p₁ p₂) :
    tensorVec V₁ V₂ p₁ p₂ η₁ η₂ x ∈ tensorLattice V₁ V₂ p₁ p₂ η₁ η₂ A :=
  Submodule.subset_span ⟨x, rfl⟩

variable {V₁ V₂ p₁ p₂ η₁ η₂} (hη₁ : ∀ t, η₁ t ∈ V₁.prim (p₁ t)) (hη₂ : ∀ t, η₂ t ∈ V₂.prim (p₂ t))
include hq0 hq hη₁ hη₂

omit hq0 hq hη₁ hη₂ in
lemma tensorPieceLattice_le_tensorLattice (t₁ : ι₁) (t₂ : ι₂) :
    tensorPieceLattice V₁ V₂ A (p₁ t₁) (p₂ t₂) (η₁ t₁) (η₂ t₂) ≤
      tensorLattice V₁ V₂ p₁ p₂ η₁ η₂ A := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact tensorVec_mem V₁ V₂ p₁ p₂ η₁ η₂ (⟨t₁, i⟩, ⟨t₂, j⟩)

omit hq0 hq hη₁ hη₂ in
lemma tensorVec_mem_piece (x : TensorPos p₁ p₂) :
    tensorVec V₁ V₂ p₁ p₂ η₁ η₂ x ∈
      tensorPieceLattice V₁ V₂ A (p₁ x.1.1) (p₂ x.2.1) (η₁ x.1.1) (η₂ x.2.1) :=
  Submodule.subset_span ⟨(x.1.2, x.2.2), rfl⟩

omit hq0 hq hη₁ hη₂ in
lemma mem_tensorLattice_of_piece {T : Module.End k (M₁ ⊗[k] M₂)}
    (hT : ∀ x : TensorPos p₁ p₂, T (tensorVec V₁ V₂ p₁ p₂ η₁ η₂ x) ∈
      tensorLattice V₁ V₂ p₁ p₂ η₁ η₂ A) {m : M₁ ⊗[k] M₂}
    (hm : m ∈ tensorLattice V₁ V₂ p₁ p₂ η₁ η₂ A) : T m ∈ tensorLattice V₁ V₂ p₁ p₂ η₁ η₂ A := by
  induction hm using Submodule.span_induction with
  | mem x hx => obtain ⟨x, rfl⟩ := hx; exact hT x
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c hx

variable [IsLocalRing A] {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖq : algebraMap A k ϖ = q)
include hϖ hϖq

/-- `L₁ ⊗ L₂` is Kashiwara-stable for the tensor product. -/
theorem isKashiwaraStable_tensorLattice (h0₁ : ∀ t, η₁ t ≠ 0) (h0₂ : ∀ t, η₂ t ≠ 0) :
    (tensor V₁ V₂ hq0 hq).IsKashiwaraStable hq0 hq (tensorLattice V₁ V₂ p₁ p₂ η₁ η₂ A) where
  wtProj_mem _ hm n := mem_tensorLattice_of_piece (fun x ↦
    tensorPieceLattice_le_tensorLattice _ _
      (wtProj_mem_tensorPieceLattice V₁ V₂ hq0 hq (hη₁ _) (hη₂ _) n
        (tensorVec_mem_piece x))) hm
  eTilde_mem _ hm := mem_tensorLattice_of_piece (fun x ↦
    tensorPieceLattice_le_tensorLattice _ _
      (eTilde_mem_tensorPieceLattice V₁ V₂ hq0 hq hϖ hϖq (hη₁ _) (hη₂ _) (h0₁ _) (h0₂ _)
        (tensorVec_mem_piece x))) hm
  fTilde_mem _ hm := mem_tensorLattice_of_piece (fun x ↦
    tensorPieceLattice_le_tensorLattice _ _
      (fTilde_mem_tensorPieceLattice V₁ V₂ hq0 hq hϖ hϖq (hη₁ _) (hη₂ _) (h0₁ _) (h0₂ _)
        (tensorVec_mem_piece x))) hm

/-- The tensor product rule for `f̃` on `L₁ ⊗ L₂`, modulo `ϖ`. -/
theorem fTilde_tensorVec_sub (h0₁ : ∀ t, η₁ t ≠ 0) (h0₂ : ∀ t, η₂ t ≠ 0)
    (x : TensorPos p₁ p₂) :
    (tensor V₁ V₂ hq0 hq).fTilde hq0 hq (tensorVec V₁ V₂ p₁ p₂ η₁ η₂ x) -
      tensorVecOpt V₁ V₂ p₁ p₂ η₁ η₂ (nextPos x) ∈ ϖ • tensorLattice V₁ V₂ p₁ p₂ η₁ η₂ A := by
  obtain ⟨⟨t₁, i, hi⟩, ⟨t₂, j, hj⟩⟩ := x
  have h := fTilde_tensorPiece_sub V₁ V₂ hq0 hq hϖ hϖq (hη₁ t₁) (hη₂ t₂) (h0₁ t₁) (h0₂ t₂)
    (i := i) (j := j) (by omega) (by omega)
  refine Submodule.mem_smul_of_le
    (tensorPieceLattice_le_tensorLattice (A := A) t₁ t₂) ϖ ?_
  convert h using 2
  · rfl
  simp only [tensorVecOpt, nextPos]
  split_ifs with h1 h2
  · rfl
  · rfl
  · simp only [Option.elim_none]
    rw [dF_eq_zero_of_primitive hq0 hq (hη₂ t₂).1 (hη₂ t₂).2 (by push_cast; omega), tmul_zero]

/-- The tensor product rule for `ẽ` on `L₁ ⊗ L₂`, modulo `ϖ`. -/
theorem eTilde_tensorVec_sub (h0₁ : ∀ t, η₁ t ≠ 0) (h0₂ : ∀ t, η₂ t ≠ 0)
    (x : TensorPos p₁ p₂) :
    (tensor V₁ V₂ hq0 hq).eTilde hq0 hq (tensorVec V₁ V₂ p₁ p₂ η₁ η₂ x) -
      tensorVecOpt V₁ V₂ p₁ p₂ η₁ η₂ (prevPos x) ∈ ϖ • tensorLattice V₁ V₂ p₁ p₂ η₁ η₂ A := by
  obtain ⟨⟨t₁, i, hi⟩, ⟨t₂, j, hj⟩⟩ := x
  have h := eTilde_tensorPiece_sub V₁ V₂ hq0 hq hϖ hϖq (hη₁ t₁) (hη₂ t₂) (h0₁ t₁) (h0₂ t₂)
    (i := i) (j := j) (by omega) (by omega)
  refine Submodule.mem_smul_of_le
    (tensorPieceLattice_le_tensorLattice (A := A) t₁ t₂) ϖ ?_
  convert h using 2
  · rfl
  simp only [tensorVecOpt, prevPos]
  split_ifs <;> rfl

end Lattice

/-! ### The crystal base `L₁ ⊗ L₂` -/

section CrystalBase

variable {A : Type*} [CommRing A] [Algebra A k] [Module A M₁] [IsScalarTower A k M₁]
  [IsLocalRing A] [FaithfulSMul A k] {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖq : algebraMap A k ϖ = q)
  {V₁ V₂ p₁ p₂ η₁ η₂}

omit [IsLocalRing A] [FaithfulSMul A k] in
lemma span_tmul_range {ια ιβ : Type*} {f : ια → M₁} {g : ιβ → M₂}
    (hf : Submodule.span k (Set.range f) = ⊤) (hg : Submodule.span k (Set.range g) = ⊤) :
    Submodule.span k (Set.range fun x : ια × ιβ ↦ f x.1 ⊗ₜ[k] g x.2) = ⊤ := by
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨m, n, rfl⟩
  have hm : m ∈ Submodule.span k (Set.range f) := hf ▸ Submodule.mem_top
  have hn : n ∈ Submodule.span k (Set.range g) := hg ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨a, rfl⟩ := hm
    induction hn using Submodule.span_induction with
    | mem n hn => obtain ⟨b, rfl⟩ := hn; exact Submodule.subset_span ⟨(a, b), rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [tmul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [tmul_smul]; exact Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy => rw [add_tmul]; exact add_mem hx hy
  | smul c x _ hx => rw [← smul_tmul']; exact Submodule.smul_mem _ c hx

include hq0 hq hϖ hϖq in
/-- **Tensor product rule** ([HK] Thm. 4.4.1 for `𝔰𝔩₂`): for string bases `η₁`, `η₂` of
integrable `U_q(𝔰𝔩₂)`-modules `M₁`, `M₂`, the `A`-span `L₁ ⊗ L₂` of the
`F^{(i)} η₁ₜ ⊗ F^{(j)} η₂ₜ'` and the classes of these vectors form a crystal base of `M₁ ⊗ M₂`
(Kashiwara's coproduct), for every non-unit `c` with `ϖ ∈ c A`. -/
theorem isCrystalBase_tensorLattice (hη₁ : ∀ t, η₁ t ∈ V₁.prim (p₁ t))
    (hη₂ : ∀ t, η₂ t ∈ V₂.prim (p₂ t))
    (hind₁ : ∀ p₀ : ℕ, LinearIndependent k (fun t : {t // p₁ t = p₀} ↦ η₁ t))
    (hind₂ : ∀ p₀ : ℕ, LinearIndependent k (fun t : {t // p₂ t = p₀} ↦ η₂ t))
    (hspan₁ : ∀ p₀ : ℕ,
      V₁.prim p₀ ≤ Submodule.span k (Set.range fun t : {t // p₁ t = p₀} ↦ η₁ t))
    (hspan₂ : ∀ p₀ : ℕ,
      V₂.prim p₀ ≤ Submodule.span k (Set.range fun t : {t // p₂ t = p₀} ↦ η₂ t))
    {c : A} (hc : ¬IsUnit c) (hϖc : ϖ ∈ Ideal.span {c}) :
    (tensor V₁ V₂ hq0 hq).IsCrystalBase hq0 hq (tensorLattice V₁ V₂ p₁ p₂ η₁ η₂ A) c
      (Set.range fun x ↦ Submodule.Quotient.mk
        (⟨tensorVec V₁ V₂ p₁ p₂ η₁ η₂ x, tensorVec_mem V₁ V₂ p₁ p₂ η₁ η₂ x⟩ :
          tensorLattice V₁ V₂ p₁ p₂ η₁ η₂ A)) := by
  set L := tensorLattice V₁ V₂ p₁ p₂ η₁ η₂ A
  set T := tensor V₁ V₂ hq0 hq
  have h0₁ : ∀ t, η₁ t ≠ 0 := fun t ↦ (hind₁ (p₁ t)).ne_zero ⟨t, rfl⟩
  have h0₂ : ∀ t, η₂ t ≠ 0 := fun t ↦ (hind₂ (p₂ t)).ne_zero ⟨t, rfl⟩
  have hL := isKashiwaraStable_tensorLattice (A := A) hq0 hq hη₁ hη₂ hϖ hϖq h0₁ h0₂
  -- the basis of `L`
  have hlik : LinearIndependent k (tensorVec V₁ V₂ p₁ p₂ η₁ η₂) := by
    have h1 := linearIndependent_dF hq0 hq hη₁ hind₁
    have h2 := linearIndependent_dF hq0 hq hη₂ hind₂
    have h := LinearIndependent.tmul_of_isDomain h1 h2
    exact h
  let bL : Module.Basis (TensorPos p₁ p₂) A L := Module.Basis.span (hlik.restrict_scalars' A)
  have hbL : ∀ x, bL x = ⟨tensorVec V₁ V₂ p₁ p₂ η₁ η₂ x, tensorVec_mem V₁ V₂ p₁ p₂ η₁ η₂ x⟩ :=
    fun x ↦ Module.Basis.span_apply _ x
  set Q := L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)
  set cls : TensorPos p₁ p₂ → Q := fun x ↦ Submodule.Quotient.mk
    (⟨tensorVec V₁ V₂ p₁ p₂ η₁ η₂ x, tensorVec_mem V₁ V₂ p₁ p₂ η₁ η₂ x⟩ : L)
  have hB : Set.range cls = Set.range fun x ↦ (Submodule.Quotient.mk (bL x) : Q) := by
    simp only [cls, hbL]
  have hli := linearIndependent_mk_basis c bL
  have : Nontrivial (A ⧸ Ideal.span {c}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hinj : Function.Injective cls := by
    have := hli.injective
    simpa only [hbL] using this
  have hne : ∀ x, cls x ≠ 0 := fun x ↦ by
    have := hli.ne_zero x
    simpa only [hbL] using this
  -- `ϖ L ⊆ c L`
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hϖc
  have hϖL : ∀ y, y ∈ ϖ • L → y ∈ c • L := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    rw [← hd, mul_comm, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (L.smul_mem d hz)
  -- the classes of the optional positions
  set clsOpt : Option (TensorPos p₁ p₂) → Q := fun o ↦ o.elim 0 cls
  have hOpt : ∀ o, tensorVecOpt V₁ V₂ p₁ p₂ η₁ η₂ o ∈ L := by
    rintro (_ | y)
    · exact zero_mem _
    · exact tensorVec_mem V₁ V₂ p₁ p₂ η₁ η₂ y
  have hclsOpt : ∀ o, (Submodule.Quotient.mk ⟨_, hOpt o⟩ : Q) = clsOpt o := by
    rintro (_ | y)
    · exact Submodule.Quotient.mk_zero _
    · rfl
  have heQ : ∀ x, T.eTildeQ hq0 hq hL.eTilde_mem c (cls x) = clsOpt (prevPos x) := by
    intro x
    rw [← hclsOpt, eTildeQ_mk, mk_eq_mk_iff]
    exact hϖL _ (eTilde_tensorVec_sub hq0 hq hη₁ hη₂ hϖ hϖq h0₁ h0₂ x)
  have hfQ : ∀ x, T.fTildeQ hq0 hq hL.fTilde_mem c (cls x) = clsOpt (nextPos x) := by
    intro x
    rw [← hclsOpt, fTildeQ_mk, mk_eq_mk_iff]
    exact hϖL _ (fTilde_tensorVec_sub hq0 hq hη₁ hη₂ hϖ hϖq h0₁ h0₂ x)
  have hclsOpt_eq : ∀ o y, clsOpt o = cls y ↔ o = some y := by
    rintro (_ | z) y
    · simp only [clsOpt, Option.elim_none, reduceCtorEq, iff_false]
      exact fun h ↦ hne y h.symm
    · simp only [clsOpt, Option.elim_some, Option.some.injEq]
      exact hinj.eq_iff
  refine
    { isKashiwaraStable := hL
      span_eq_top := ?_
      free := Module.Free.of_basis bL
      linearIndependent := by rw [hB]; exact hli.linearIndepOn_id
      span_quot_eq_top := by rw [hB]; exact span_mk_basis c bL
      exists_wt := ?_
      eQ_mem := ?_
      fQ_mem := ?_
      fQ_eq_iff := ?_ }
  · rw [eq_top_iff, ← span_tmul_range (span_dF hq0 hq hspan₁) (span_dF hq0 hq hspan₂)]
    exact Submodule.span_mono (by rintro _ ⟨x, rfl⟩; exact tensorVec_mem V₁ V₂ p₁ p₂ η₁ η₂ x)
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, _, tmul_mem_tensor_wt hq0 hq (dF_mem (hη₁ x.1.1).1 x.1.2)
      (dF_mem (hη₂ x.2.1).1 x.2.2), rfl⟩
  · rintro _ ⟨x, rfl⟩
    rw [heQ]
    rcases prevPos x with _ | y
    · exact Or.inr rfl
    · exact Or.inl ⟨y, rfl⟩
  · rintro _ ⟨x, rfl⟩
    rw [hfQ]
    rcases nextPos x with _ | y
    · exact Or.inr rfl
    · exact Or.inl ⟨y, rfl⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hfQ, heQ, hclsOpt_eq, hclsOpt_eq]
    exact nextPos_eq_some_iff p₁ p₂ x y

end CrystalBase

end IntegrableSl2

end LieLean.QuantumGroup
