/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Super.InvariantFormLie
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Dual bases of the root spaces of `G̃(A, τ)` modulo `R`

The root space `G̃_μ = G̃ ∩ U_μ` of `G̃ = G̃(A, τ)` is finite-dimensional and homogeneous: for
`μ = ±∑ kⱼ αⱼ` all its elements have parity `∑ kⱼ τⱼ`. Since the radical of the supersymmetric
form `(·|·)` on `G̃` is the maximal ideal `R` ([Kac78] Prop. 1.5), the form induces a perfect
pairing between `G̃_μ / R_μ` and `G̃_{-μ} / R_{-μ}`. We choose dual bases: elements
`e_μ^{(k)} ∈ G̃_μ` and `e_{-μ}^{(k)} ∈ G̃_{-μ}` with `(e_μ^{(k)} | e_{-μ}^{(l)}) = δₖₗ`, such that
every `x ∈ G̃_μ` and `y ∈ G̃_{-μ}` satisfy
`x ≡ ∑ₖ (x | e_{-μ}^{(k)}) e_μ^{(k)}` and `y ≡ ∑ₖ (e_μ^{(k)} | y) e_{-μ}^{(k)}` modulo `R`.
With the element of `G̃_μ` on the left the super Casimir operator telescopes for odd elements.
These are the dual bases used to define the Casimir operator ([Kac78] §2.3; cf. [Kac] §2.5),
on modules killed by `R`.

## Main definitions

* `Matrix.Realization.SuperEnveloping.gRoot`: the root space `G̃_μ`.
* `Matrix.Realization.SuperEnveloping.weightParity`: its parity.
* `Matrix.Realization.SuperEnveloping.rootPairing`: the pairing `G̃_μ/R × G̃_{-μ}/R → K`.
* `Matrix.Realization.SuperEnveloping.rootBasis`, `rootCobasis`: dual bases modulo `R`.

## Main results

* `Matrix.Realization.SuperEnveloping.isHomog_of_mem_gRoot`: `G̃_μ` is homogeneous, of parity
  `weightParity μ`.
* `Matrix.Realization.SuperEnveloping.finiteDimensional_gRoot`: `G̃_μ` is finite-dimensional.
* `Matrix.Realization.SuperEnveloping.mem_maxIdeal_of_forall_invForm_left`,
  `mem_maxIdeal_of_forall_invForm_right`: the radical of `(·|·) : G̃_μ × G̃_{-μ} → K` is `R`.
* `Matrix.Realization.SuperEnveloping.invForm_rootBasis_rootCobasis`: `(e_μ^{(k)} | e_{-μ}^{(l)})
  = δₖₗ`.
* `Matrix.Realization.SuperEnveloping.sub_sum_rootBasis_mem_maxIdeal`,
  `sub_sum_rootCobasis_mem_maxIdeal`: the expansions modulo `R`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.5, §2.3.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.5.
-/

open Module

noncomputable section

/-- For dual bases `b`, `a` of a pairing `B`, `n = ∑ₖ B (b k) n • a k`. -/
lemma LinearMap.sum_apply_basis_smul_right {ι K M N : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (B : M →ₗ[K] N →ₗ[K] K) (b : Basis ι K M) (a : Basis ι K N)
    (hB : ∀ k l, B (b k) (a l) = if k = l then 1 else 0) (n : N) :
    ∑ k, B (b k) n • a k = n := by
  conv_rhs => rw [← a.sum_repr n]
  refine Finset.sum_congr rfl fun k _ ↦ congrArg (· • a k) ?_
  rw [show B (b k) n = B (b k) (∑ l, a.repr n l • a l) by rw [a.sum_repr], map_sum]
  simp [hB]

/-- For dual bases `b`, `a` of a pairing `B`, `m = ∑ₖ B m (a k) • b k`. -/
lemma LinearMap.sum_apply_basis_smul_left {ι K M N : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (B : M →ₗ[K] N →ₗ[K] K) (b : Basis ι K M) (a : Basis ι K N)
    (hB : ∀ k l, B (b k) (a l) = if k = l then 1 else 0) (m : M) :
    ∑ k, B m (a k) • b k = m :=
  B.flip.sum_apply_basis_smul_right a b (fun k l ↦ by
    rw [LinearMap.flip_apply, hB]; exact if_congr eq_comm rfl rfl) m

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (p : ι → ZMod 2)

namespace SuperEnveloping

/-- The root space `G̃_μ = G̃ ∩ U_μ`. -/
def gRoot (μ : Dual K H) : Submodule K (P.SuperEnveloping p) := gTilde P p ⊓ weightSpace P p μ

/-! ### Parities of root spaces -/

/-- The parity `∑ kⱼ τⱼ` of `∑ kⱼ αⱼ`. -/
def rootParity (k : ι → ℤ) : ZMod 2 := ∑ j, (k j : ZMod 2) * p j

omit [DecidableEq ι] in
lemma rootParity_add (k l : ι → ℤ) :
    rootParity p (k + l) = rootParity p k + rootParity p l := by
  simp [rootParity, add_mul, Finset.sum_add_distrib]

lemma rootParity_single (j : ι) : rootParity p (Pi.single j 1) = p j := by
  simp [rootParity, Pi.single_apply]

lemma rootParity_wordVec (w : List ι) : rootParity p (wordVec w) = (w.map p).sum := by
  induction w with
  | nil => simp [rootParity]
  | cons j w ih =>
    rw [wordVec_cons, rootParity_add, rootParity_single, ih, List.map_cons, List.sum_cons]

lemma sum_wordVec (w : List ι) : ∑ j, wordVec w j = w.length := by
  induction w with
  | nil => simp
  | cons j w ih =>
    simp only [wordVec_cons, Pi.add_apply, Finset.sum_add_distrib, ih, Pi.single_apply,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, List.length_cons]
    push_cast; ring

variable [CharZero K]

lemma isHomog_of_mem_nPlusRoot {k : ι → ℤ} {x : P.SuperEnveloping p}
    (hx : x ∈ nPlusRoot P p k) : IsHomog P p (rootParity p k) x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, w, hk, rfl⟩ := hx
    have := isHomog_eLie P p i w
    rwa [add_comm, ← List.sum_cons, ← List.map_cons, ← rootParity_wordVec, hk] at this
  | zero => exact isHomog_zero _
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

open Classical in
/-- The parity of the root space `G̃_μ`: `∑ kⱼ τⱼ` if `μ = ∑ kⱼ αⱼ`, and `0` otherwise. -/
def weightParity (μ : Dual K H) : ZMod 2 :=
  if hμ : ∃ k, P.rootOf k = μ then rootParity p hμ.choose else 0

omit [DecidableEq ι] in
lemma weightParity_rootOf (k : ι → ℤ) : weightParity P p (P.rootOf k) = rootParity p k := by
  have hμ : ∃ l, P.rootOf l = P.rootOf k := ⟨k, rfl⟩
  simp only [weightParity, hμ, ↓reduceDIte]
  rw [P.rootOf_injective hμ.choose_spec]

omit [DecidableEq ι] in
lemma rootParity_neg (k : ι → ℤ) : rootParity p (-k) = rootParity p k := by
  simp only [rootParity, Pi.neg_apply, Int.cast_neg, ZMod.neg_eq_self_mod_two]

omit [DecidableEq ι] in
/-- `G̃_μ` and `G̃_{-μ}` have the same parity. -/
@[simp] lemma weightParity_neg (μ : Dual K H) : weightParity P p (-μ) = weightParity P p μ := by
  by_cases hμ : ∃ k, P.rootOf k = μ
  · obtain ⟨k, rfl⟩ := hμ
    rw [← map_neg, weightParity_rootOf, weightParity_rootOf, rootParity_neg]
  · have hμ' : ¬∃ k, P.rootOf k = -μ := fun ⟨k, hk⟩ ↦ hμ ⟨-k, by rw [map_neg, hk, neg_neg]⟩
    simp only [weightParity, hμ, hμ', ↓reduceDIte]

/-- All elements of `G̃_μ` are homogeneous of parity `weightParity μ`. -/
theorem isHomog_of_mem_gRoot {μ : Dual K H} {x : P.SuperEnveloping p} (hx : x ∈ gRoot P p μ) :
    IsHomog P p (weightParity P p μ) x := by
  by_cases hx0 : x = 0
  · rw [hx0]; exact isHomog_zero _
  rcases mem_allWeights P p hx.1 hx.2 hx0 with (⟨k, hk, rfl⟩ | hμ) | ⟨k, hk, rfl⟩
  · simp only at hx ⊢
    rw [weightParity_neg, weightParity_rootOf]
    obtain ⟨y, hy, hyk, rfl⟩ := exists_omega_eq P p hx.1 hx.2
    refine (isHomog_of_mem_nPlusRoot P p ?_).omega
    rw [← gTilde_inf_weightSpace_rootOf P p hk]; exact ⟨hy, hyk⟩
  · rw [Set.mem_singleton_iff] at hμ
    subst hμ
    rw [← map_zero P.rootOf, weightParity_rootOf, rootParity, Finset.sum_eq_zero fun j _ ↦ by simp]
    obtain ⟨a, rfl⟩ : x ∈ LinearMap.range (h P p) := by
      rw [← gTilde_inf_weightSpace_zero P p]; exact hx
    exact isHomog_h P p a
  · rw [weightParity_rootOf]
    refine isHomog_of_mem_nPlusRoot P p ?_
    rw [← gTilde_inf_weightSpace_rootOf P p hk]; exact hx

/-! ### Finite-dimensionality -/

omit [CharZero K] in
lemma finite_nPlusRoot_generators (k : ι → ℤ) :
    {x | ∃ i w, wordVec (i :: w) = k ∧ eLie P p i w = x}.Finite := by
  let eL : List ι → P.SuperEnveloping p := fun l ↦ match l with
    | [] => 0
    | i :: w => eLie P p i w
  refine ((List.finite_length_eq ι (∑ j, k j).toNat).image eL).subset ?_
  rintro _ ⟨i, w, hk, rfl⟩
  refine ⟨i :: w, ?_, rfl⟩
  have := sum_wordVec (i :: w)
  rw [hk] at this
  simp only [Set.mem_ofPred_eq, this]
  omega

/-- The root spaces `G̃_μ` are finite-dimensional ([Kac78] §1.2). -/
instance finiteDimensional_gRoot [FiniteDimensional K H] (μ : Dual K H) :
    FiniteDimensional K (gRoot P p μ) := by
  by_cases hμ : μ ∈ AuxLieAlgebra.allWeights P
  swap
  · have : gRoot P p μ = ⊥ := eq_bot_iff.2 fun x hx ↦ by
      by_contra hx0
      exact hμ (mem_allWeights P p hx.1 hx.2 hx0)
    rw [this]; infer_instance
  have hpos : ∀ k ∈ posCone ι, FiniteDimensional K (gRoot P p (P.rootOf k)) := fun k hk ↦ by
    rw [gRoot, gTilde_inf_weightSpace_rootOf P p hk]
    exact FiniteDimensional.span_of_finite K (finite_nPlusRoot_generators P p k)
  rcases hμ with (⟨k, hk, rfl⟩ | hμ) | ⟨k, hk, rfl⟩
  · have := hpos k hk
    refine Submodule.finiteDimensional_of_le
      (S₂ := (gRoot P p (P.rootOf k)).map (omega P p).toLinearMap) fun x hx ↦ ?_
    obtain ⟨y, hy, hyk, rfl⟩ := exists_omega_eq P p hx.1 hx.2
    exact ⟨y, ⟨hy, hyk⟩, rfl⟩
  · rw [Set.mem_singleton_iff] at hμ
    subst hμ
    rw [gRoot, gTilde_inf_weightSpace_zero P p]
    infer_instance
  · exact hpos k hk

/-! ### The radical of the pairing `G̃_μ × G̃_{-μ} → K` -/

variable [FiniteDimensional K H] (S : A.Symmetrization)

/-- An element of `G̃_μ` orthogonal on the right to `G̃_{-μ}` lies in `R`. -/
theorem mem_maxIdeal_of_forall_invForm_right {μ : Dual K H} {y : P.SuperEnveloping p}
    (hy : y ∈ gRoot P p μ) (h0 : ∀ x ∈ gRoot P p (-μ), invForm P p S x y = 0) :
    y ∈ maxIdeal P p := by
  refine (mem_maxIdeal_iff P p S hy.1).2 fun x hx ↦ ?_
  refine induction_on_gTilde P p (q := fun x ↦ invForm P p S x y = 0) hx
    (fun ν x hx hxν ↦ ?_) fun x₁ x₂ h₁ h₂ ↦ by rw [map_add, LinearMap.add_apply, h₁, h₂, add_zero]
  by_cases hν : ν = -μ
  · subst hν; exact h0 x ⟨hx, hxν⟩
  · exact invForm_eq_zero P p S hxν hy.2 fun h ↦ hν (eq_neg_of_add_eq_zero_left h)

/-- An element of `G̃_μ` orthogonal on the left to `G̃_{-μ}` lies in `R`. -/
theorem mem_maxIdeal_of_forall_invForm_left {μ : Dual K H} {x : P.SuperEnveloping p}
    (hx : x ∈ gRoot P p μ) (h0 : ∀ y ∈ gRoot P p (-μ), invForm P p S x y = 0) :
    x ∈ maxIdeal P p := by
  refine mem_maxIdeal_of_forall_invForm_right P p S hx fun y hy ↦ ?_
  rw [invForm_swap P p S hx.1 hx.2 (isHomog_of_mem_gRoot P p hx) hy.1 hy.2
    (isHomog_of_mem_gRoot P p hy), h0 y hy, mul_zero]

/-! ### The induced perfect pairing -/

/-- `R ∩ G̃_μ`, as a submodule of `G̃_μ`. -/
def rootRad (μ : Dual K H) : Submodule K (gRoot P p μ) :=
  (maxIdeal P p).comap (gRoot P p μ).subtype

/-- `G̃_μ / (R ∩ G̃_μ)`. -/
abbrev RootQuot (μ : Dual K H) : Type _ := gRoot P p μ ⧸ rootRad P p μ

/-- The form `(·|·) : G̃_μ × G̃_{-μ} → K`. -/
def rootForm (μ : Dual K H) : gRoot P p μ →ₗ[K] gRoot P p (-μ) →ₗ[K] K :=
  (invForm P p S).compl₁₂ (gRoot P p μ).subtype (gRoot P p (-μ)).subtype

/-- The pairing `G̃_μ/R × G̃_{-μ}/R → K` induced by `(·|·)`. -/
def rootPairing (μ : Dual K H) : RootQuot P p μ →ₗ[K] RootQuot P p (-μ) →ₗ[K] K :=
  (rootRad P p μ).liftQ
    (((rootRad P p (-μ)).liftQ (rootForm P p S μ).flip fun _ hy ↦ LinearMap.ext fun x ↦
      (invForm_eq_zero_of_mem_maxIdeal P p S hy x.2.1).2).flip)
    fun _ hx ↦ LinearMap.ext fun y ↦ Submodule.Quotient.induction_on _ y fun y ↦
      (invForm_eq_zero_of_mem_maxIdeal P p S hx y.2.1).1

@[simp]
lemma rootPairing_mk (μ : Dual K H) (x : gRoot P p μ) (y : gRoot P p (-μ)) :
    rootPairing P p S μ (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      invForm P p S x y :=
  rfl

lemma rootPairing_injective (μ : Dual K H) : Function.Injective (rootPairing P p S μ) := by
  refine (injective_iff_map_eq_zero _).2 fun q hq ↦ ?_
  induction q using Submodule.Quotient.induction_on with
  | H x =>
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  refine mem_maxIdeal_of_forall_invForm_left P p S x.2 fun y hy ↦ ?_
  simpa using congrArg (fun φ ↦ φ (Submodule.Quotient.mk ⟨y, hy⟩)) hq

lemma rootPairing_flip_injective (μ : Dual K H) :
    Function.Injective (rootPairing P p S μ).flip := by
  refine (injective_iff_map_eq_zero _).2 fun q hq ↦ ?_
  induction q using Submodule.Quotient.induction_on with
  | H y =>
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  refine mem_maxIdeal_of_forall_invForm_right P p S y.2 fun x hx ↦ ?_
  rw [neg_neg] at hx
  simpa using congrArg (fun φ ↦ φ (Submodule.Quotient.mk ⟨x, hx⟩)) hq

instance isPerfPair_rootPairing (μ : Dual K H) : (rootPairing P p S μ).IsPerfPair :=
  .of_injective (rootPairing_injective P p S μ) (rootPairing_flip_injective P p S μ)

/-! ### Dual bases -/

/-- The index set of the dual bases of `G̃_{±μ}` modulo `R`. -/
abbrev RootIdx (μ : Dual K H) : Type := Fin (finrank K (RootQuot P p μ))

/-- A basis of `G̃_μ/R`. -/
def rootBasisQ (μ : Dual K H) : Basis (RootIdx P p μ) K (RootQuot P p μ) :=
  Module.finBasis K _

/-- The basis of `G̃_{-μ}/R` dual to `rootBasisQ` for `rootPairing`. -/
def rootCobasisQ (μ : Dual K H) : Basis (RootIdx P p μ) K (RootQuot P p (-μ)) :=
  (rootBasisQ P p μ).dualBasis.map (rootPairing P p S μ).flip.toPerfPair.symm

lemma rootPairing_rootBasisQ_rootCobasisQ (μ : Dual K H) (k l : RootIdx P p μ) :
    rootPairing P p S μ (rootBasisQ P p μ k) (rootCobasisQ P p S μ l) =
      if k = l then 1 else 0 := by
  have := congrArg (fun φ ↦ φ (rootBasisQ P p μ k))
    ((rootPairing P p S μ).flip.apply_symm_toPerfPair_self ((rootBasisQ P p μ).dualBasis l))
  simp only [LinearMap.flip_apply] at this
  rw [rootCobasisQ, Basis.map_apply, this, Basis.dualBasis_apply_self]

/-- Elements `e_μ^{(k)} ∈ G̃_μ` lifting `rootBasisQ`. -/
def rootBasis (μ : Dual K H) (k : RootIdx P p μ) : gRoot P p μ :=
  (Submodule.Quotient.mk_surjective _ (rootBasisQ P p μ k)).choose

/-- Elements `e_{-μ}^{(k)} ∈ G̃_{-μ}` lifting `rootCobasisQ`. -/
def rootCobasis (μ : Dual K H) (k : RootIdx P p μ) : gRoot P p (-μ) :=
  (Submodule.Quotient.mk_surjective _ (rootCobasisQ P p S μ k)).choose

lemma mk_rootBasis (μ : Dual K H) (k : RootIdx P p μ) :
    Submodule.Quotient.mk (rootBasis P p μ k) = rootBasisQ P p μ k :=
  (Submodule.Quotient.mk_surjective _ _).choose_spec

lemma mk_rootCobasis (μ : Dual K H) (k : RootIdx P p μ) :
    Submodule.Quotient.mk (rootCobasis P p S μ k) = rootCobasisQ P p S μ k :=
  (Submodule.Quotient.mk_surjective _ _).choose_spec

/-- `(e_μ^{(k)} | e_{-μ}^{(l)}) = δₖₗ`. -/
theorem invForm_rootBasis_rootCobasis (μ : Dual K H) (k l : RootIdx P p μ) :
    invForm P p S (rootBasis P p μ k) (rootCobasis P p S μ l) = if k = l then 1 else 0 := by
  rw [← rootPairing_mk, mk_rootBasis, mk_rootCobasis, rootPairing_rootBasisQ_rootCobasisQ]

/-- Every `x ∈ G̃_μ` satisfies `x ≡ ∑ₖ (x | e_{-μ}^{(k)}) e_μ^{(k)}` modulo `R`. -/
theorem sub_sum_rootBasis_mem_maxIdeal {μ : Dual K H} {x : P.SuperEnveloping p}
    (hx : x ∈ gRoot P p μ) :
    x - ∑ k, invForm P p S x (rootCobasis P p S μ k) • (rootBasis P p μ k : P.SuperEnveloping p)
      ∈ maxIdeal P p := by
  have := (rootPairing P p S μ).sum_apply_basis_smul_left (rootBasisQ P p μ)
    (rootCobasisQ P p S μ) (rootPairing_rootBasisQ_rootCobasisQ P p S μ)
    (Submodule.Quotient.mk ⟨x, hx⟩)
  simp only [← mk_rootCobasis, ← mk_rootBasis, rootPairing_mk] at this
  simp only [← Submodule.mkQ_apply, ← map_smul, ← map_sum] at this
  have h := (Submodule.Quotient.eq _).1 this.symm
  simpa [rootRad] using h

/-- Every `y ∈ G̃_{-μ}` satisfies `y ≡ ∑ₖ (e_μ^{(k)} | y) e_{-μ}^{(k)}` modulo `R`. -/
theorem sub_sum_rootCobasis_mem_maxIdeal {μ : Dual K H} {y : P.SuperEnveloping p}
    (hy : y ∈ gRoot P p (-μ)) :
    y - ∑ k, invForm P p S (rootBasis P p μ k) y • (rootCobasis P p S μ k : P.SuperEnveloping p)
      ∈ maxIdeal P p := by
  have := (rootPairing P p S μ).sum_apply_basis_smul_right (rootBasisQ P p μ)
    (rootCobasisQ P p S μ) (rootPairing_rootBasisQ_rootCobasisQ P p S μ)
    (Submodule.Quotient.mk ⟨y, hy⟩)
  simp only [← mk_rootCobasis, ← mk_rootBasis, rootPairing_mk] at this
  simp only [← Submodule.mkQ_apply, ← map_smul, ← map_sum] at this
  have h := (Submodule.Quotient.eq _).1 this.symm
  simpa [rootRad] using h

end SuperEnveloping

end Matrix.Realization
