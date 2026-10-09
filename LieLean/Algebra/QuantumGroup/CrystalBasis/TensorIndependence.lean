/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorModuleCrystal

/-!
# Pure tensors of basis classes

Let `A ⊆ k` with `k = A[ϖ⁻¹]` and let `L₁ ⊆ M₁`, `L₂ ⊆ M₂` be free `A`-lattices spanning the
`k`-vector spaces `M₁`, `M₂`, with `A/ϖA`-bases `B₁` of `L₁/ϖL₁` and `B₂` of `L₂/ϖL₂`. Then the
classes of the pure tensors `x ⊗ y` (`[x] ∈ B₁`, `[y] ∈ B₂`) in `(L₁ ⊗ L₂)/ϖ(L₁ ⊗ L₂)` are
nonzero and pairwise distinct. No finite-dimensionality is needed (compare
`IntegrableSl2.IsCrystalBase.tmulQ_injective`).

## Main results

* `TensorModule.mul_eq_of_tmul_sub_mem`: if `x ⊗ y ≡ x' ⊗ y'` modulo `ϖ (L₁ ⊗ L₂)`, then
  `p₁(x) p₂(y) = p₁(x') p₂(y')` for all `A`-linear `p₁ : L₁ → A/ϖA`, `p₂ : L₂ → A/ϖA`.
* `TensorModule.mk_eq_of_tmul_sub_mem`: pure tensors of basis classes that agree modulo
  `ϖ (L₁ ⊗ L₂)` have the same factors.
* `TensorModule.mk_tmul_notMem`: pure tensors of basis classes are not in `ϖ (L₁ ⊗ L₂)`.

## Proof

Our argument: an `A`-linear functional on `L₁` extends `k`-linearly to `M₁`, since an `A`-basis
of `L₁` is a `k`-basis of `M₁` (`TensorModule.exists_extend`); a lift `f` of the coordinate
functional of `[x₀] ∈ B₁` and a lift `g` of that of `[y₀] ∈ B₂` give `f ⊗ g : M₁ ⊗ M₂ → k`, which
maps `L₁ ⊗ L₂` into `A` and `ϖ (L₁ ⊗ L₂)` into `ϖA`.
-/
open TensorProduct Pointwise

noncomputable section

namespace LieLean.QuantumGroup

namespace TensorModule

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra A k]
  {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower A k M]
  {ϖ : A}

/-- An `A`-basis of a lattice `L ⊆ M` spanning `M` over `k = A[ϖ⁻¹]` is a `k`-basis of `M`. -/
lemma linearIndependent_coe_of_basis
    (hϖ0 : algebraMap A k ϖ ≠ 0)
    (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
    {L : Submodule A M} {κ : Type*} (e : Module.Basis κ A L) :
    LinearIndependent k (fun a ↦ (e a : M)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  choose m a ha using hk
  set N := s.sup fun j ↦ m (g j)
  have hN : ∀ j ∈ s, ∃ c : A, algebraMap A k (ϖ ^ N) * g j = algebraMap A k c := fun j hj ↦ by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := fun j ↦ m (g j)) hj)
    refine ⟨ϖ ^ d * a (g j), ?_⟩
    have hd' : N = m (g j) + d := hd
    rw [hd', pow_add, map_mul, map_mul, ← ha]
    ring
  choose c hc using hN
  let c' : κ → A := fun j ↦ if h : j ∈ s then c j h else 0
  have hc' : ∀ j ∈ s, algebraMap A k (c' j) = algebraMap A k (ϖ ^ N) * g j := fun j hj ↦ by
    simp only [c', hj, ↓reduceDIte, hc]
  have hsum : ∑ j ∈ s, c' j • e j = 0 := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_zero]
    have : ∑ j ∈ s, (c' j • e j : L).1 = algebraMap A k (ϖ ^ N) • ∑ j ∈ s, g j • (e j : M) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [Submodule.coe_smul, ← algebraMap_smul k (c' j), hc' j hj, mul_smul]
    rw [this, hg, smul_zero]
  have h0 := (linearIndependent_iff'.1 e.linearIndependent) s c' hsum i hi
  have h1 := hc' i hi
  rw [h0, map_zero, eq_comm, mul_eq_zero] at h1
  exact h1.resolve_left (by rw [map_pow]; exact pow_ne_zero _ hϖ0)

/-- An `A`-linear functional on a free lattice `L ⊆ M` spanning `M` extends `k`-linearly to `M`. -/
lemma exists_extend (hϖ0 : algebraMap A k ϖ ≠ 0)
    (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
    {L : Submodule A M} [Module.Free A L] (hL : Submodule.span k (L : Set M) = ⊤)
    (f : L →ₗ[A] A) : ∃ F : M →ₗ[k] k, ∀ x : L, F x = algebraMap A k (f x) := by
  classical
  let e := Module.Free.chooseBasis A L
  have hli := linearIndependent_coe_of_basis hϖ0 hk e
  have hsp : ⊤ ≤ Submodule.span k (Set.range fun a ↦ (e a : M)) := by
    rw [← hL, Submodule.span_le]
    intro x hx
    have h1 : x ∈ Submodule.span A (Set.range fun a ↦ (e a : M)) := by
      have := Submodule.mem_map_of_mem (f := L.subtype) (e.mem_span ⟨x, hx⟩)
      rwa [Submodule.map_span, ← Set.range_comp] at this
    exact Submodule.span_le_restrictScalars A k _ h1
  let bk := Module.Basis.mk hli hsp
  let F := bk.constr k fun a ↦ algebraMap A k (f (e a))
  refine ⟨F, fun x ↦ ?_⟩
  have h : (F.restrictScalars A).comp L.subtype = (Algebra.linearMap A k).comp f :=
    e.ext fun a ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        LinearMap.coe_restrictScalars, Algebra.linearMap_apply]
      have := bk.constr_basis k (fun a ↦ algebraMap A k (f (e a))) a
      rwa [Module.Basis.mk_apply] at this
  exact LinearMap.congr_fun h x

section Pair

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module A M₁] [IsScalarTower A k M₁]
  [AddCommGroup M₂] [Module k M₂] [Module A M₂] [IsScalarTower A k M₂]
  {L₁ : Submodule A M₁} {L₂ : Submodule A M₂}

omit [IsScalarTower A k M₂] in
/-- A product functional `F₁ ⊗ F₂` that is `A`-valued on `L₁`, `L₂` is `A`-valued on `L₁ ⊗ L₂`
and `ϖA`-valued on `ϖ (L₁ ⊗ L₂)`. -/
lemma exists_eq_algebraMap_of_mem_smul (F₁ : M₁ →ₗ[k] k) (F₂ : M₂ →ₗ[k] k)
    (hF₁ : ∀ x ∈ L₁, ∃ a : A, F₁ x = algebraMap A k a)
    (hF₂ : ∀ y ∈ L₂, ∃ a : A, F₂ y = algebraMap A k a) {z : TensorModule k M₁ M₂}
    (hz : z ∈ ϖ • lattice k A L₁ L₂) :
    ∃ a ∈ Ideal.span {ϖ}, TensorProduct.lift ((LinearMap.mul k k).compl₁₂ F₁ F₂)
      ((mk M₁ M₂).symm z) = algebraMap A k a := by
  set Φ := TensorProduct.lift ((LinearMap.mul k k).compl₁₂ F₁ F₂)
  have hL : ∀ z ∈ lattice k A L₁ L₂, ∃ a : A, Φ ((mk M₁ M₂).symm z) = algebraMap A k a := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      obtain ⟨a, ha⟩ := hF₁ x hx
      obtain ⟨b, hb⟩ := hF₂ y hy
      refine ⟨a * b, ?_⟩
      change Φ (x ⊗ₜ[k] y) = _
      rw [map_mul, ← ha, ← hb]
      simp [Φ]
    | zero => exact ⟨0, by simp⟩
    | add z z' _ _ h h' =>
      obtain ⟨a, ha⟩ := h
      obtain ⟨b, hb⟩ := h'
      exact ⟨a + b, by rw [map_add, map_add, ha, hb, map_add]⟩
    | smul c z _ h =>
      obtain ⟨a, ha⟩ := h
      refine ⟨c * a, ?_⟩
      rw [← algebraMap_smul k c z, map_smul, map_smul, ha, smul_eq_mul, map_mul]
  obtain ⟨z₀, hz₀, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
  obtain ⟨a, ha⟩ := hL z₀ hz₀
  refine ⟨ϖ * a, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ), ?_⟩
  rw [← algebraMap_smul k ϖ z₀, map_smul, map_smul, ha, smul_eq_mul, map_mul]

/-- If `x ⊗ y ≡ x' ⊗ y'` modulo `ϖ (L₁ ⊗ L₂)`, then `p₁(x) p₂(y) = p₁(x') p₂(y')` for all `A`-linear
`p₁ : L₁ → A/ϖA`, `p₂ : L₂ → A/ϖA`. -/
theorem mul_eq_of_tmul_sub_mem (hinj : Function.Injective (algebraMap A k))
    (hϖ0 : algebraMap A k ϖ ≠ 0)
    (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
    [Module.Free A L₁] [Module.Free A L₂] (hL₁ : Submodule.span k (L₁ : Set M₁) = ⊤)
    (hL₂ : Submodule.span k (L₂ : Set M₂) = ⊤) (p₁ : L₁ →ₗ[A] A ⧸ Ideal.span {ϖ})
    (p₂ : L₂ →ₗ[A] A ⧸ Ideal.span {ϖ}) {x x' : L₁} {y y' : L₂}
    (h : mk M₁ M₂ ((x : M₁) ⊗ₜ[k] (y : M₂)) - mk M₁ M₂ ((x' : M₁) ⊗ₜ[k] (y' : M₂)) ∈
      ϖ • lattice k A L₁ L₂) :
    p₁ x * p₂ y = p₁ x' * p₂ y' := by
  obtain ⟨f₁, hf₁⟩ := Module.projective_lifting_property (Ideal.span {ϖ}).mkQ p₁
    (Submodule.mkQ_surjective _)
  obtain ⟨f₂, hf₂⟩ := Module.projective_lifting_property (Ideal.span {ϖ}).mkQ p₂
    (Submodule.mkQ_surjective _)
  obtain ⟨F₁, hF₁⟩ := exists_extend hϖ0 hk hL₁ f₁
  obtain ⟨F₂, hF₂⟩ := exists_extend hϖ0 hk hL₂ f₂
  obtain ⟨a, ha, he⟩ := exists_eq_algebraMap_of_mem_smul F₁ F₂
    (fun x hx ↦ ⟨f₁ ⟨x, hx⟩, hF₁ ⟨x, hx⟩⟩) (fun y hy ↦ ⟨f₂ ⟨y, hy⟩, hF₂ ⟨y, hy⟩⟩) h
  have e : ∀ (x : M₁) (y : M₂), TensorProduct.lift ((LinearMap.mul k k).compl₁₂ F₁ F₂)
      ((mk M₁ M₂).symm (mk M₁ M₂ (x ⊗ₜ[k] y))) = F₁ x * F₂ y := fun x y ↦ by simp
  rw [map_sub, map_sub, e, e, hF₁, hF₁, hF₂, hF₂, ← map_mul, ← map_mul, ← map_sub] at he
  have hd := hinj he
  rw [← hf₁, ← hf₂]
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    Ideal.Quotient.mk_eq_mk, ← map_mul]
  rw [Ideal.Quotient.eq, hd]
  exact ha

section Bases

variable (hinj : Function.Injective (algebraMap A k)) (hϖ0 : algebraMap A k ϖ ≠ 0)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  [Module.Free A L₁] [Module.Free A L₂] (hL₁ : Submodule.span k (L₁ : Set M₁) = ⊤)
  (hL₂ : Submodule.span k (L₂ : Set M₂) = ⊤)
  {B₁ : Set (L₁ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L₁))}
  {B₂ : Set (L₂ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L₂))}
  (hB₁ : LinearIndependent (A ⧸ Ideal.span {ϖ}) (Subtype.val : B₁ → _))
  (hB₁' : Submodule.span (A ⧸ Ideal.span {ϖ}) B₁ = ⊤)
  (hB₂ : LinearIndependent (A ⧸ Ideal.span {ϖ}) (Subtype.val : B₂ → _))
  (hB₂' : Submodule.span (A ⧸ Ideal.span {ϖ}) B₂ = ⊤)
include hinj hϖ0 hk hL₁ hL₂ hB₁ hB₁' hB₂ hB₂'

omit [Module.Free A L₁] [Module.Free A L₂] hinj hϖ0 hk hL₁ hL₂ hB₂ hB₂' in
/-- The coordinate functional `L₁ → A/ϖA` of `b ∈ B₁`. -/
private lemma exists_coord (b : B₁) :
    ∃ p : L₁ →ₗ[A] A ⧸ Ideal.span {ϖ}, ∀ x : L₁, ∀ hx : Submodule.Quotient.mk x ∈ B₁,
      ((⟨_, hx⟩ : B₁) = b → p x = 1) ∧ ((⟨_, hx⟩ : B₁) ≠ b → p x = 0) := by
  let bas := Module.Basis.mk hB₁ (by rw [Subtype.range_coe, hB₁'])
  refine ⟨((bas.coord b).restrictScalars A).comp (Ideal.span {ϖ} • ⊤ : Submodule A L₁).mkQ,
    fun x hx ↦ ?_⟩
  have e : (Submodule.Quotient.mk x : L₁ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L₁)) =
      bas ⟨_, hx⟩ := by rw [Module.Basis.mk_apply]
  have hc : bas.coord b (Submodule.Quotient.mk x) = Finsupp.single (⟨_, hx⟩ : B₁) 1 b := by
    conv_lhs => rw [e]
    rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply, hc]
  exact ⟨fun h ↦ by rw [h, Finsupp.single_eq_same],
    fun h ↦ Finsupp.single_eq_of_ne (Ne.symm h)⟩

/-- **Distinct pure tensors** of basis classes are distinct modulo `ϖ (L₁ ⊗ L₂)`. -/
theorem mk_eq_of_tmul_sub_mem {x x' : L₁} {y y' : L₂}
    (hx : Submodule.Quotient.mk x ∈ B₁) (hx' : Submodule.Quotient.mk x' ∈ B₁)
    (hy : Submodule.Quotient.mk y ∈ B₂) (hy' : Submodule.Quotient.mk y' ∈ B₂)
    (h : mk M₁ M₂ ((x : M₁) ⊗ₜ[k] (y : M₂)) - mk M₁ M₂ ((x' : M₁) ⊗ₜ[k] (y' : M₂)) ∈
      ϖ • lattice k A L₁ L₂) :
    (Submodule.Quotient.mk x : L₁ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L₁)) =
        Submodule.Quotient.mk x' ∧
      (Submodule.Quotient.mk y : L₂ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L₂)) =
        Submodule.Quotient.mk y' := by
  obtain ⟨p₁, hp₁⟩ := exists_coord hB₁ hB₁' ⟨_, hx⟩
  obtain ⟨p₂, hp₂⟩ := exists_coord hB₂ hB₂' ⟨_, hy⟩
  have e := mul_eq_of_tmul_sub_mem hinj hϖ0 hk hL₁ hL₂ p₁ p₂ h
  rw [(hp₁ x hx).1 rfl, (hp₂ y hy).1 rfl, one_mul] at e
  by_contra hne
  have h10 : (1 : A ⧸ Ideal.span {ϖ}) = 0 := by
    rw [not_and_or] at hne
    rcases hne with hne | hne
    · rwa [(hp₁ x' hx').2 fun h ↦ hne (congrArg Subtype.val h).symm, zero_mul] at e
    · rwa [(hp₂ y' hy').2 fun h ↦ hne (congrArg Subtype.val h).symm, mul_zero] at e
  have : Subsingleton (A ⧸ Ideal.span {ϖ}) := subsingleton_of_zero_eq_one h10.symm
  have := Module.subsingleton (A ⧸ Ideal.span {ϖ}) (L₁ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L₁))
  have := Module.subsingleton (A ⧸ Ideal.span {ϖ}) (L₂ ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L₂))
  exact hne ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Pure tensors of basis classes do not lie in `ϖ (L₁ ⊗ L₂)`. -/
theorem mk_tmul_notMem (hϖ : ¬IsUnit ϖ) {x : L₁} {y : L₂}
    (hx : Submodule.Quotient.mk x ∈ B₁) (hy : Submodule.Quotient.mk y ∈ B₂) :
    mk M₁ M₂ ((x : M₁) ⊗ₜ[k] (y : M₂)) ∉ ϖ • lattice k A L₁ L₂ := by
  intro h
  obtain ⟨p₁, hp₁⟩ := exists_coord hB₁ hB₁' ⟨_, hx⟩
  obtain ⟨p₂, hp₂⟩ := exists_coord hB₂ hB₂' ⟨_, hy⟩
  have e := mul_eq_of_tmul_sub_mem hinj hϖ0 hk hL₁ hL₂ p₁ p₂ (x' := 0) (y' := y)
    (by simpa using h)
  rw [(hp₁ x hx).1 rfl, (hp₂ y hy).1 rfl, map_zero, zero_mul, one_mul] at e
  have : Nontrivial (A ⧸ Ideal.span {ϖ}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  exact one_ne_zero e

end Bases

end Pair

end TensorModule

end LieLean.QuantumGroup
