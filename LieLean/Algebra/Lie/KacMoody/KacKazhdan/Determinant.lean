/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterDenominator
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Gram
import Mathlib.Algebra.CharZero.Infinite

/-!
# The leading term of the Shapovalov determinant

Let `A` be a symmetrizable matrix and `𝔤 = 𝔤(A)` over a field `K` of characteristic zero. For
`β ∈ 𝔥*`, the weight space `M(λ)_{λ-β}` of the Verma module has the PBW basis `(e_s v_λ)`, where
`s` runs over the finite set `T_β` of multisets of indices of the root vector basis `nNegBasis` of
`𝔫₋` of total weight `β` (Kostant partitions); this basis is independent of `λ` via
`U(𝔫₋) ≃ M(λ)`. Let `D_β(λ)` be the determinant of the Shapovalov form on `M(λ)_{λ-β}` in this
basis. We prove ([KK] §3 (check); cf. [Kac] §9 (check)):

`D_β` is a polynomial function of `λ` of degree `N = ∑_{s ∈ T_β} |s|`, whose homogeneous component
of degree `N` is `c ∏_{s ∈ T_β} ∏_x (λ | α_x)^{s(x)}` for a nonzero constant `c`.

This is the "leading term" part of the Kac–Kazhdan determinant formula
`D_β(λ) = c ∏_{α > 0} ∏_{n ≥ 1} ((λ + ρ | α) - n (α | α)/2)^{mult α · P(β - n α)}`.

## Proof

Let `(e'_x)` be the basis of `𝔫₋` dual to `(e_x)` for the pairings `(σ y | y')` on the root spaces
(`nNegDualBasis`), and `(e'_t v_λ)` the corresponding PBW basis. By
`VermaModule.contravariantForm_pbw_mem_polyLE` and `VermaModule.contravariantForm_pbw_hasTop`,
the matrix `M(λ) = (B_λ(e_s v_λ, e'_t v_λ))_{s,t ∈ T_β}` has polynomial entries of degree
`≤ min(|s|, |t|)`, the component of degree `|s|` being `δ_{st} ∏ s(x)! ∏ (λ | α_x)^{s(x)}` when
`|s| = |t|`. By `MvPolynomial.homogeneousComponent_det`, `det M(λ)` has degree `≤ N` with top
component `∏_s ∏_x s(x)! (λ | α_x)^{s(x)}`. Finally `M(λ) = G(λ) C`, where `G(λ)` is the Gram
matrix of the Shapovalov form in the basis `(e_s v_λ)` and `C` is the (invertible, constant)
matrix expressing the basis `(e'_t)` in the basis `(e_s)` of `U(𝔫₋)`.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.partitions`: the finite set `T_β`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.pbwWeightBasis`: the PBW basis of
  `M(λ)_{λ-β}`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.hasTop_det_pbwWeightBasis`: the leading term of
  the Shapovalov determinant.

## References

* [KK] V. G. Kac, D. A. Kazhdan, *Structure of representations with highest weight of
  infinite-dimensional Lie algebras*, Adv. Math. 34 (1979), 97–108.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.
-/

open Module LieModule Module.Dual MvPolynomial UniversalEnvelopingAlgebra

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "ιᵤ" => UniversalEnvelopingAlgebra.ι K

/-! ### PBW bases of Verma modules from root vector bases -/

namespace VermaModule

variable (Λ : Dual K H) {c : Basis (NegRootIndex P) K (nNeg P)}
  (hc : ∀ x, ((c x : nNeg P) : P.KacMoodyAlgebra) ∈ rootSpace P (-x.root))

variable (c) in
/-- The PBW basis of `M(Λ)` built from a basis `c` of `𝔫₋`. -/
def pbwOf : Basis (NegRootIndex P →₀ ℕ) K (VermaModule P Λ) :=
  (pbwBasis c).map (equivEnvNNeg P Λ)

lemma pbwBasisVerma_eq_pbwOf : pbwBasisVerma P Λ = pbwOf P Λ (nNegBasis P) := rfl

omit [CharZero K] in
include hc in
lemma listProd_smul_mem_weightSpace_of_basis (l : List (NegRootIndex P)) {μ : Dual K H}
    {m : VermaModule P Λ} (hm : m ∈ weightSpace P Λ μ) :
    (l.map fun x ↦ ιᵤ ((c x : nNeg P) : P.KacMoodyAlgebra)).prod • m ∈
      weightSpace P Λ (μ - (l.map NegRootIndex.root).sum) := by
  induction l with
  | nil => simpa using hm
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, mul_smul, ← lie_eq_smul]
    convert lie_mem_weightSpaceOfMap (h P) (hc a) ih using 2
    abel

include hc in
lemma pbwOf_mem_weightSpace (s : NegRootIndex P →₀ ℕ) :
    pbwOf P Λ c s ∈ weightSpace P Λ (Λ - negRootWt P s) := by
  rw [pbwOf, Basis.map_apply, pbwBasis_apply, equivEnvNNeg_apply, map_pbwMonomial,
    pbwMonomial, ← sum_sort_toMultiset]
  exact listProd_smul_mem_weightSpace_of_basis P Λ hc _ (hwv_mem_weightSpace P Λ)

include hc in
/-- The weight space `M(Λ)_μ` is spanned by the PBW basis vectors of weight `μ`. -/
theorem weightSpace_eq_span_pbwOf (μ : Dual K H) :
    weightSpace P Λ μ = Submodule.span K (pbwOf P Λ c '' {s | Λ - negRootWt P s = μ}) := by
  have hle : ∀ ν, Submodule.span K (pbwOf P Λ c '' {s | Λ - negRootWt P s = ν}) ≤
      weightSpace P Λ ν := fun ν ↦ by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl, rfl⟩
    exact pbwOf_mem_weightSpace P Λ hc s
  refine le_antisymm (fun m hm ↦ mem_of_mem_iSup_of_le (h P) _ hle hm ?_) (hle μ)
  have htop : Submodule.span K (Set.range (pbwOf P Λ c)) ≤
      ⨆ ν, Submodule.span K (pbwOf P Λ c '' {s | Λ - negRootWt P s = ν}) := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    exact Submodule.mem_iSup_of_mem (Λ - negRootWt P s)
      (Submodule.subset_span ⟨s, rfl, rfl⟩)
  exact htop (by rw [(pbwOf P Λ c).span_eq]; trivial)

end VermaModule

/-! ### Kostant partitions -/

/-- The finite set `T_β` of Kostant partitions of `β`: multisets of indices of the root vector
basis of `𝔫₋` of total weight `β`. -/
def partitions (β : Dual K H) : Finset (NegRootIndex P →₀ ℕ) :=
  (finite_setOf_negRootWt_eq P β).toFinset

@[simp] lemma mem_partitions {β : Dual K H} {s : NegRootIndex P →₀ ℕ} :
    s ∈ partitions P β ↔ negRootWt P s = β := by
  simp [partitions]

/-! ### PBW bases of weight spaces -/

namespace VermaModule

variable (Λ β : Dual K H) (c : Basis (NegRootIndex P) K (nNeg P))
  (hc : ∀ x, ((c x : nNeg P) : P.KacMoodyAlgebra) ∈ rootSpace P (-x.root))

/-- The PBW vectors (for the basis `c` of `𝔫₋`) of weight `Λ - β`, as a basis of the weight
space `M(Λ)_{Λ - β}`. -/
def weightBasisOf : Basis (partitions P β) K (weightSpace P Λ (Λ - β)) :=
  have hli : LinearIndependent K fun s : partitions P β ↦ pbwOf P Λ c s :=
    (pbwOf P Λ c).linearIndependent.comp _ Subtype.val_injective
  (Basis.span hli).map (LinearEquiv.ofEq _ _ (by
    rw [weightSpace_eq_span_pbwOf P Λ hc]
    congr 1
    ext m
    simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq, sub_right_inj]
    exact ⟨fun ⟨s, hs⟩ ↦ ⟨s, (mem_partitions P).mp s.2, hs⟩,
      fun ⟨s, hs, hm⟩ ↦ ⟨⟨s, (mem_partitions P).mpr hs⟩, hm⟩⟩))

@[simp] lemma weightBasisOf_apply (s : partitions P β) :
    (weightBasisOf P Λ β c hc s : VermaModule P Λ) = pbwOf P Λ c s := by
  simp [weightBasisOf, Basis.span_apply]

/-- The coordinates in the PBW basis of the weight space are the coordinates in the PBW basis of
`M(Λ)`. -/
lemma repr_weightBasisOf (w : weightSpace P Λ (Λ - β)) (s : partitions P β) :
    (weightBasisOf P Λ β c hc).repr w s = (pbwOf P Λ c).repr w s := by
  classical
  conv_rhs => rw [← (weightBasisOf P Λ β c hc).sum_repr w]
  simp only [Submodule.coe_sum, Submodule.coe_smul, weightBasisOf_apply, map_sum, map_smul,
    Basis.repr_self, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single s (fun t _ hts ↦ by
      have : (t : NegRootIndex P →₀ ℕ) ≠ s := fun h ↦ hts (Subtype.ext h)
      simp [this]) (fun h ↦ absurd (Finset.mem_univ s) h)]
  simp

end VermaModule

namespace VermaModule

variable [FiniteDimensional K H] (S : A.Symmetrization) (Λ β : Dual K H)

/-- The PBW basis `(e_s v_Λ)_{s ∈ T_β}` of `M(Λ)_{Λ - β}` (for the basis `nNegBasis` of `𝔫₋`).
It is independent of `Λ` in the sense that it is the image of the PBW basis of `U(𝔫₋)` under
`U(𝔫₋) ≃ M(Λ)`. -/
abbrev pbwWeightBasis : Basis (partitions P β) K (weightSpace P Λ (Λ - β)) :=
  weightBasisOf P Λ β (nNegBasis P) (nNegBasis_mem P)

/-- The PBW basis `(e'_t v_Λ)_{t ∈ T_β}` of `M(Λ)_{Λ - β}` for the dual basis `nNegDualBasis`. -/
abbrev pbwDualWeightBasis : Basis (partitions P β) K (weightSpace P Λ (Λ - β)) :=
  weightBasisOf P Λ β (nNegDualBasis P S) (nNegDualVec_mem P S)

/-- The (constant) matrix expressing the basis `(e'_t)` of `U(𝔫₋)` in the basis `(e_s)`. -/
def changeMatrix : Matrix (partitions P β) (partitions P β) K :=
  fun s t ↦ (pbwBasis (nNegBasis P)).repr (pbwBasis (nNegDualBasis P S) t) s

lemma toMatrix_pbwWeightBasis :
    (pbwWeightBasis P Λ β).toMatrix (pbwDualWeightBasis P S Λ β) = changeMatrix P S β := by
  ext s t
  rw [Basis.toMatrix_apply, repr_weightBasisOf, weightBasisOf_apply, pbwOf, pbwOf,
    Basis.map_apply, Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

lemma det_changeMatrix_ne_zero : (changeMatrix P S β).det ≠ 0 := by
  classical
  have h := Basis.toMatrix_mul_toMatrix_flip (pbwWeightBasis P 0 β) (pbwDualWeightBasis P S 0 β)
  rw [toMatrix_pbwWeightBasis] at h
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/-- The Shapovalov matrix `(B_Λ(e_s v_Λ, e'_t v_Λ))_{s, t ∈ T_β}` is the Gram matrix of the
Shapovalov form in the basis `(e_s v_Λ)` times the change of basis matrix. -/
lemma of_contravariantForm_eq_mul :
    (Matrix.of fun s t : partitions P β ↦
      contravariantForm P Λ (pbwBasisVerma P Λ s) (pbwDualVerma P S Λ t)) =
      LinearMap.BilinForm.toMatrix (pbwWeightBasis P Λ β) (weightSpaceForm P Λ (Λ - β)) *
        changeMatrix P S β := by
  classical
  rw [← toMatrix_pbwWeightBasis P S Λ β]
  ext s t
  simp only [Matrix.of_apply, Matrix.mul_apply, LinearMap.BilinForm.toMatrix_apply,
    Basis.toMatrix_apply]
  have key : weightSpaceForm P Λ (Λ - β) (pbwWeightBasis P Λ β s) (pbwDualWeightBasis P S Λ β t) =
      ∑ j, weightSpaceForm P Λ (Λ - β) (pbwWeightBasis P Λ β s) (pbwWeightBasis P Λ β j) *
        (pbwWeightBasis P Λ β).repr (pbwDualWeightBasis P S Λ β t) j := by
    conv_lhs => rw [← (pbwWeightBasis P Λ β).sum_repr (pbwDualWeightBasis P S Λ β t)]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  rw [← key]
  simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
    weightBasisOf_apply]
  rfl

/-- **The leading term of `det (B_λ(e_s v_λ, e'_t v_λ))`**: it is a polynomial function of `λ` of
degree at most `N = ∑_{s ∈ T_β} |s|`, with component of degree `N` equal to
`∏_{s ∈ T_β} ∏_x s(x)! (λ | α_x)^{s(x)}`. -/
theorem hasTop_det_of_contravariantForm :
    HasTop (∑ s ∈ partitions P β, s.degree) (∏ s ∈ partitions P β, pbwTopPoly P S s)
      (fun Λ ↦ (Matrix.of fun s t : partitions P β ↦
        contravariantForm P Λ (pbwBasisVerma P Λ s) (pbwDualVerma P S Λ t)).det) := by
  classical
  choose p hp using fun s t : partitions P β ↦
    mem_polyLE.mp (contravariantForm_pbw_mem_polyLE P S s t)
  have htop : ∀ s t : partitions P β,
      (s : NegRootIndex P →₀ ℕ).degree = (t : NegRootIndex P →₀ ℕ).degree →
      homogeneousComponent (s : NegRootIndex P →₀ ℕ).degree (p s t) =
        if s = t then pbwTopPoly P S s else 0 := fun s t hst ↦ by
    have h1 : HasTop (s : NegRootIndex P →₀ ℕ).degree
        (homogeneousComponent (s : NegRootIndex P →₀ ℕ).degree (p s t))
        (fun Λ ↦ contravariantForm P Λ (pbwBasisVerma P Λ s) (pbwDualVerma P S Λ t)) :=
      ⟨p s t, (hp s t).1.trans (by rw [hst, min_self]), rfl, (hp s t).2⟩
    rw [h1.unique (contravariantForm_pbw_hasTop P S s t hst)]
    by_cases h : s = t
    · subst h
      simp
    · have : (s : NegRootIndex P →₀ ℕ) ≠ t := fun h' ↦ h (Subtype.ext h')
      simp [h, this]
  obtain ⟨hdeg, hcomp⟩ := homogeneousComponent_det (Matrix.of p)
    (fun s ↦ (s : NegRootIndex P →₀ ℕ).degree) (fun s t ↦ (hp s t).1)
    (fun s t hst hd ↦ by rw [Matrix.of_apply, htop s t hd]; simp [hst])
  refine ⟨(Matrix.of p).det, ?_, ?_, ?_⟩
  · rw [← Finset.sum_coe_sort]; exact hdeg
  · rw [← Finset.sum_coe_sort, hcomp, ← Finset.prod_coe_sort (partitions P β) (pbwTopPoly P S)]
    refine Finset.prod_congr rfl fun s _ ↦ ?_
    rw [Matrix.of_apply, htop s s rfl]
    simp
  · funext Λ
    have := RingHom.map_det ((Pi.evalRingHom (fun _ : Dual K H ↦ K) Λ).comp
      (evalPoly K H).toRingHom) (Matrix.of p)
    simp only [RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this]
    congr 1
    ext s t
    simp [(hp s t).2]

/-- **The leading term of the Shapovalov determinant** ([KK] §3 (check)). Let `A` be
symmetrizable, and let `D_β(λ)` be the determinant of the Shapovalov form on `M(λ)_{λ-β}` with
respect to the PBW basis `(e_s v_λ)_{s ∈ T_β}` (independent of `λ` via `U(𝔫₋) ≃ M(λ)`). Then
`D_β` is a polynomial function of `λ` of degree at most `N = ∑_{s ∈ T_β} |s|`, whose homogeneous
component of degree `N` is `c ∏_{s ∈ T_β} ∏_x (λ | α_x)^{s(x)}` for some nonzero constant `c`.
Here `x` runs over the root vector basis of `𝔫₋`, `α_x` is the positive root of `x`, and
`(λ | α) = λ(ν⁻¹ α)`. -/
theorem hasTop_det_pbwWeightBasis :
    ∃ c : K, c ≠ 0 ∧ HasTop (∑ s ∈ partitions P β, s.degree)
      (C c * ∏ s ∈ partitions P β, ∏ x ∈ s.support,
        linPoly K H ((P.toDual S).symm x.root) ^ s x)
      (fun Λ ↦ (LinearMap.BilinForm.toMatrix (pbwWeightBasis P Λ β)
        (weightSpaceForm P Λ (Λ - β))).det) := by
  have hC := det_changeMatrix_ne_zero P S β
  refine ⟨(∏ s ∈ partitions P β, ∏ x ∈ s.support, ((s x).factorial : K)) *
      ((changeMatrix P S β).det)⁻¹, mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun s _ ↦
        Finset.prod_ne_zero_iff.mpr fun x _ ↦ by exact_mod_cast (s x).factorial_ne_zero)
      (inv_ne_zero hC), ?_⟩
  have h := (hasTop_det_of_contravariantForm P S β).smul ((changeMatrix P S β).det)⁻¹
  have hfun : (((changeMatrix P S β).det)⁻¹ • fun Λ ↦ (Matrix.of fun s t : partitions P β ↦
      contravariantForm P Λ (pbwBasisVerma P Λ s) (pbwDualVerma P S Λ t)).det) =
      fun Λ ↦ (LinearMap.BilinForm.toMatrix (pbwWeightBasis P Λ β)
        (weightSpaceForm P Λ (Λ - β))).det := by
    funext Λ
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [of_contravariantForm_eq_mul, Matrix.det_mul, mul_comm, mul_inv_cancel_right₀ hC]
  rw [hfun] at h
  convert h using 1
  simp only [pbwTopPoly, Finset.prod_mul_distrib, ← map_prod, smul_eq_C_mul, map_mul]
  ring

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
