/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.HarishChandraHomogeneous
import LieLean.Algebra.Lie.KacMoody.HarishChandraInvariance

/-!
# Graded Harish-Chandra projection compatibility

## Main definitions

* `cartanRestriction`: algebra extension of the actual triangular `cartanProj`.
* `SymmetricAlgebra.homogeneousComponent`: genuine polynomial homogeneous projection,
  proved independent of the selected basis.

## Main results

* `harishChandraProjection_totalDegree_le`: the actual PBW projection preserves degree.
* `harishChandraProjection_homogeneousComponent`: graded compatibility for all filtered
  enveloping elements, with the canonical graded PBW equivalence.
* `shiftedHarishChandra_degree_le`: negative-rho translation changes only lower terms.
* `exists_centralLift_shiftedHarishChandra_top`: a consumer of the production invariant
  homogeneous central lift with its actual shifted HC leading term identified.

## References

Reconstructed from the production triangular PBW decomposition and pinned Mathlib's
homogeneous polynomial components; no new printed source was consulted. The PBW
source provenance is inherited from `UniversalEnveloping/{PBW,Filtration,Graded,
TensorDecomposition}`. The invariant-lift consumer uses the production symmetrization
construction documented against Etingof, MIT 18.757 (Fall 2023), Lecture 13, §13.3,
proof of Theorem 13.5. No Chevalley restriction or HC image result is assumed or claimed.

The field is characteristic zero, its universe is `K : Type`, and no Cartan-dimension
assumption is added beyond the supplied `Realization`, including its `finrank_add_rank`.
No finite-type, algebraic-closure, integrality, or GCM hypothesis is added.
All degrees, including zero, are covered. The exact total identity is only for adapted
ordered PBW coordinates, not total symmetrization or the shifted map.
-/

noncomputable section
open Module

namespace UniversalEnvelopingAlgebra

variable {K L C σ : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [CommRing C] [Algebra K C] [LinearOrder σ]

/-- A commutative algebra image of an ordered PBW monomial is its ordinary monomial. -/
theorem algHom_pbwMonomial (f : UniversalEnvelopingAlgebra K L →ₐ[K] C)
    (v : σ → L) (s : σ →₀ ℕ) :
    f (pbwMonomial K v s) = MvPolynomial.aeval (R := K) (fun i => f (ι K (v i)))
      (MvPolynomial.monomial s 1) := by
  have h : ∀ m (s : σ →₀ ℕ), s.degree = m →
      f (pbwMonomial K v s) = MvPolynomial.aeval (R := K) (fun i => f (ι K (v i)))
        (MvPolynomial.monomial s 1) := by
    intro m
    induction m with
    | zero =>
      intro s hs
      rw [Finsupp.degree_eq_zero_iff] at hs
      subst s
      simp
    | succ m ih =>
      intro s hs
      have hne : s.support.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty, Ne, Finsupp.support_eq_empty]
        rintro rfl
        simp at hs
      have hts := PBW.sub_add_single_minIdx s hne
      have htdeg := PBW.degree_sub_single_minIdx s hne
      have e : MvPolynomial.monomial s (1 : K) =
          MvPolynomial.X (PBW.minIdx s hne) *
            MvPolynomial.monomial (s - Finsupp.single (PBW.minIdx s hne) 1) 1 := by
        rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul,
          add_comm, hts]
      rw [e, map_mul, MvPolynomial.aeval_X, ← ih _ (by omega),
        ← map_mul, ← PBW.pbwMonomial_add_single (PBW.leAll_minIdx s hne), hts]
  exact h s.degree s rfl

end UniversalEnvelopingAlgebra

namespace SymmetricAlgebra

variable {K : Type} {M N σ : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

/-- A linear substitution on symmetric algebras preserves the independently defined
full homogeneous components. -/
theorem lift_comp_ι_mem_homogeneous (f : M →ₗ[K] N) (n : ℕ)
    {p : SymmetricAlgebra K M} (hp : p ∈ homogeneousSubmodule n) :
    lift ((ι K N).comp f) p ∈ homogeneousSubmodule n := by
  have h : (homogeneousSubmodule (K := K) (M := M) n).map
      (lift ((ι K N).comp f)).toLinearMap ≤ homogeneousSubmodule n := by
    unfold homogeneousSubmodule
    rw [Submodule.map_pow]
    apply pow_le_pow_left'
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨f x, by simp⟩
  exact h ⟨p, hp, rfl⟩

/-- The algebra map on a basis polynomial model is ordinary substitution. -/
theorem lift_comp_equivMvPolynomial_symm (b : Basis σ K M)
    {C : Type*} [CommRing C] [Algebra K C] (f : M →ₗ[K] C) :
    (lift f).comp (equivMvPolynomial b).symm.toAlgHom =
      MvPolynomial.aeval (R := K) (fun i => f (b i)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

/-- The genuine homogeneous component, using the existing polynomial grading.
Its characterization below proves that the construction does not depend on this basis. -/
def homogeneousComponent (n : ℕ) : SymmetricAlgebra K M →ₗ[K] SymmetricAlgebra K M :=
  let e := equivMvPolynomial (Module.Free.chooseBasis K M)
  e.symm.toLinearMap.comp ((MvPolynomial.homogeneousComponent n).comp e.toLinearMap)

/-- On every full homogeneous component the projection is its expected Kronecker action. -/
theorem homogeneousComponent_of_mem {m n : ℕ} {p : SymmetricAlgebra K M}
    (hp : p ∈ homogeneousSubmodule n) :
    homogeneousComponent m p = if m = n then p else 0 := by
  classical
  have hh := (mem_homogeneousSubmodule_iff (Module.Free.chooseBasis K M) n p).mp hp
  simp only [homogeneousComponent, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    MvPolynomial.homogeneousComponent_of_mem hh]
  split_ifs <;> simp

/-- Every basis presentation gives exactly the same genuine homogeneous component. -/
theorem equivMvPolynomial_homogeneousComponent (b : Basis σ K M) (n : ℕ)
    (p : SymmetricAlgebra K M) :
    equivMvPolynomial b (homogeneousComponent n p) =
      MvPolynomial.homogeneousComponent n (equivMvPolynomial b p) := by
  classical
  obtain ⟨q, rfl⟩ := (equivMvPolynomial b).symm.surjective p
  induction q using MvPolynomial.induction_on' with
  | monomial s c =>
    have hp : (equivMvPolynomial b).symm (MvPolynomial.monomial s c) ∈
        homogeneousSubmodule s.degree := by
      rw [mem_homogeneousSubmodule_iff b]
      simp only [AlgEquiv.apply_symm_apply]
      exact MvPolynomial.isHomogeneous_monomial c rfl
    rw [homogeneousComponent_of_mem hp, AlgEquiv.apply_symm_apply,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl)]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Translation preserves degree and its difference from the identity lowers degree
on every genuine homogeneous component, with constants fixed exactly. -/
theorem affinePullback_id_degree_of_homogeneous (b : Basis σ K M) (δ : Module.Dual K M)
    {n : ℕ} {p : SymmetricAlgebra K M} (hp : p ∈ homogeneousSubmodule n) :
    (equivMvPolynomial b (affinePullback LinearMap.id δ p)).totalDegree ≤ n ∧
    (equivMvPolynomial b (affinePullback LinearMap.id δ p - p)).totalDegree ≤ n - 1 ∧
    (n = 0 → affinePullback LinearMap.id δ p - p = 0) := by
  let e := equivMvPolynomial b
  let f := affinePullback (LinearMap.id : M →ₗ[K] M) δ
  have hf (x : M) : f (ι K M x) = ι K M x + algebraMap K (SymmetricAlgebra K M) (δ x) := by
    simp [f, affinePullback]
  change (e (f p)).totalDegree ≤ n ∧ (e (f p - p)).totalDegree ≤ n - 1 ∧
    (n = 0 → f p - p = 0)
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap c => simp [e, f]
  | add p q i _ _ hp hq =>
    simp only [map_add, add_sub_add_comm]
    exact ⟨(MvPolynomial.totalDegree_add _ _).trans (max_le hp.1 hq.1),
      (MvPolynomial.totalDegree_add _ _).trans (max_le hp.2.1 hq.2.1),
      fun hi => by rw [hp.2.2 hi, hq.2.2 hi, zero_add]⟩
  | mem_mul g hg i p _ ih =>
    obtain ⟨x, rfl⟩ := hg
    have hx : (e (ι K M x)).totalDegree ≤ 1 := by
      apply MvPolynomial.IsHomogeneous.totalDegree_le
      apply (mem_homogeneousSubmodule_iff b 1 _).mp
      exact (show ι K M x ∈ LinearMap.range (ι K M) ^ 1 by
        rw [pow_one]; exact ⟨x, rfl⟩)
    have he : e (f (ι K M x)) = e (ι K M x) + MvPolynomial.C (δ x) := by
      simp [hf, e]
    have hfd : (e (f (ι K M x))).totalDegree ≤ 1 := by
      rw [he]
      exact (MvPolynomial.totalDegree_add _ _).trans
        (max_le hx (by simp))
    have hd : e (f (ι K M x * p) - ι K M x * p) =
        e (ι K M x) * e (f p - p) + MvPolynomial.C (δ x) * e (f p) := by
      rw [map_sub, map_mul, map_mul, map_mul, he, map_sub]
      ring
    refine ⟨?_, ?_, by omega⟩
    · rw [map_mul, map_mul]
      exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
    · rw [hd]
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le
      · by_cases hi : i = 0
        · rw [ih.2.2 hi, map_zero, mul_zero, MvPolynomial.totalDegree_zero]
          omega
        · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
      · apply (MvPolynomial.totalDegree_mul _ _).trans
        rw [MvPolynomial.totalDegree_C]
        omega

/-- Translation cannot change a homogeneous component at or above the input degree.
This includes degree zero, where translation fixes constants. -/
theorem homogeneousComponent_affinePullback_id_of_homogeneous
    (δ : Module.Dual K M) {m n : ℕ} {p : SymmetricAlgebra K M}
    (hp : p ∈ homogeneousSubmodule m) (hmn : m ≤ n) :
    homogeneousComponent n (affinePullback LinearMap.id δ p) = homogeneousComponent n p := by
  have hd := affinePullback_id_degree_of_homogeneous (Free.chooseBasis K M) δ hp
  rw [← sub_eq_zero, ← map_sub]
  apply (equivMvPolynomial (Free.chooseBasis K M)).injective
  rw [equivMvPolynomial_homogeneousComponent, map_zero]
  by_cases hm : m = 0
  · rw [hd.2.2 hm, map_zero, map_zero]
  · exact MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega)

/-- Translation preserves a genuine total-degree bound, and its correction lowers
that bound by one; at degree zero the correction is exactly zero. -/
theorem affinePullback_id_degree_le (b : Basis σ K M) (δ : Module.Dual K M)
    (n : ℕ) {p : SymmetricAlgebra K M} (hp : (equivMvPolynomial b p).totalDegree ≤ n) :
    (equivMvPolynomial b (affinePullback LinearMap.id δ p)).totalDegree ≤ n ∧
    (equivMvPolynomial b (affinePullback LinearMap.id δ p - p)).totalDegree ≤ n - 1 ∧
    (n = 0 → affinePullback LinearMap.id δ p - p = 0) := by
  obtain ⟨q, rfl⟩ := (equivMvPolynomial b).symm.surjective p
  rw [AlgEquiv.apply_symm_apply, ← MvPolynomial.mem_restrictTotalDegree] at hp
  rw [MvPolynomial.restrictTotalDegree, MvPolynomial.restrictSupport_eq_span] at hp
  induction hp using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨s, hs, rfl⟩ := hq
    change s.degree ≤ n at hs
    have hh : (equivMvPolynomial b).symm (MvPolynomial.monomial s 1) ∈
        homogeneousSubmodule s.degree := by
      rw [mem_homogeneousSubmodule_iff b, AlgEquiv.apply_symm_apply]
      exact MvPolynomial.isHomogeneous_monomial 1 rfl
    have hd := affinePullback_id_degree_of_homogeneous b δ hh
    exact ⟨hd.1.trans hs, hd.2.1.trans (Nat.sub_le_sub_right hs 1),
      fun hn => hd.2.2 (by omega)⟩
  | zero => simp
  | add q r _ _ hq hr =>
    simp only [map_add, add_sub_add_comm]
    exact ⟨(MvPolynomial.totalDegree_add _ _).trans (max_le hq.1 hr.1),
      (MvPolynomial.totalDegree_add _ _).trans (max_le hq.2.1 hr.2.1),
      fun hn => by rw [hq.2.2 hn, hr.2.2 hn, zero_add]⟩
  | smul c q _ hq =>
    simp only [map_smul, ← smul_sub]
    exact ⟨(MvPolynomial.totalDegree_smul_le _ _).trans hq.1,
      (MvPolynomial.totalDegree_smul_le _ _).trans hq.2.1,
      fun hn => by rw [hq.2.2 hn, smul_zero]⟩

/-- Translation acts as the identity on the top homogeneous component of every
polynomial of degree at most `n`; this is not equality of the total polynomials. -/
theorem homogeneousComponent_affinePullback_id (b : Basis σ K M) (δ : Module.Dual K M)
    (n : ℕ) {p : SymmetricAlgebra K M} (hp : (equivMvPolynomial b p).totalDegree ≤ n) :
    homogeneousComponent n (affinePullback LinearMap.id δ p) = homogeneousComponent n p := by
  have hd := affinePullback_id_degree_le b δ n hp
  rw [← sub_eq_zero, ← map_sub]
  apply (equivMvPolynomial b).injective
  rw [equivMvPolynomial_homogeneousComponent, map_zero]
  by_cases hn : n = 0
  · rw [hd.2.2 hn, map_zero, map_zero]
  · exact MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega)

end SymmetricAlgebra

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K 𝔤
local notation "𝓢" => SymmetricAlgebra K H

/-- Genuine Cartan restriction: extend the existing triangular Cartan projection,
which is the identity on Cartan and zero on both nilpotent summands. -/
def cartanRestriction : SymmetricAlgebra K 𝔤 →ₐ[K] 𝓢 :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι K H).comp (cartanProj P))

@[simp] theorem cartanRestriction_ι (x : 𝔤) :
    cartanRestriction P (SymmetricAlgebra.ι K 𝔤 x) =
      SymmetricAlgebra.ι K H (cartanProj P x) := by
  simp [cartanRestriction]

/-- Restriction is the identity on the actual Cartan generators. -/
@[simp] theorem cartanRestriction_h (a : H) :
    cartanRestriction P (SymmetricAlgebra.ι K 𝔤 (h P a)) = SymmetricAlgebra.ι K H a := by
  simp [cartanRestriction_ι]

/-- Restriction kills the negative-root summand, by the actual triangular projection. -/
theorem cartanRestriction_of_mem_nNeg {x : 𝔤} (hx : x ∈ nNeg P) :
    cartanRestriction P (SymmetricAlgebra.ι K 𝔤 x) = 0 := by
  simp [cartanRestriction_ι, cartanProj_of_mem_nNeg P hx]

/-- Restriction kills the positive-root summand, by the actual triangular projection. -/
theorem cartanRestriction_of_mem_nPos {x : 𝔤} (hx : x ∈ nPos P) :
    cartanRestriction P (SymmetricAlgebra.ι K 𝔤 x) = 0 := by
  simp [cartanRestriction_ι, cartanProj_of_mem_nPos P hx]

/-- Evaluating a restricted symbol is evaluating the full symbol at the weight
extended by zero on both root summands. This certifies the ordinary Cartan restriction. -/
theorem eval_cartanRestriction (Λ : Module.Dual K H) (p : SymmetricAlgebra K 𝔤) :
    SymmetricAlgebra.lift Λ (cartanRestriction P p) =
      SymmetricAlgebra.lift (Λ.comp (cartanProj P)) p := by
  have hh : (SymmetricAlgebra.lift Λ).comp (cartanRestriction P) =
      SymmetricAlgebra.lift (Λ.comp (cartanProj P)) := by
    ext x
    simp
  exact DFunLike.congr_fun hh p

open UniversalEnvelopingAlgebra

/-- The actual PBW projection on a basis ordered with the negative summand first.
This is an exact unshifted identity, not an equality with total symmetrization. -/
theorem harishChandraProjection_pbwMonomial
    {σ τ : Type*} [LinearOrder σ] [LinearOrder τ]
    (bN : Basis σ K (nNeg P)) (bB : Basis τ K (borel P))
    (s : σ ⊕ₗ τ →₀ ℕ) :
    harishChandraProjection P
      (pbwMonomial K (PBW.basisOfIsCompl (isCompl_nNeg_borel P) bN bB) s) =
      MvPolynomial.aeval (R := K)
        (fun i => SymmetricAlgebra.ι K H
          (cartanProj P (PBW.basisOfIsCompl (isCompl_nNeg_borel P) bN bB i)))
        (MvPolynomial.monomial s 1) := by
  obtain ⟨⟨sN, sB⟩, rfl⟩ := PBW.lexFinsuppEquiv.surjective s
  rw [← mulMap_pbwMonomial_tmul, mulMap_tmul, harishChandraProjection_mul,
    algHom_pbwMonomial, algHom_pbwMonomial, PBW.lexFinsuppEquiv_apply]
  rw [show MvPolynomial.monomial
      (sN.mapDomain (toLex ∘ Sum.inl) + sB.mapDomain (toLex ∘ Sum.inr)) (1 : K) =
      MvPolynomial.rename (toLex ∘ Sum.inl) (MvPolynomial.monomial sN 1) *
        MvPolynomial.rename (toLex ∘ Sum.inr) (MvPolynomial.monomial sB 1) by
      simp [MvPolynomial.rename_monomial, MvPolynomial.monomial_mul_monomial]]
  rw [map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename]
  have hn : (fun i => SymmetricAlgebra.ι K H
      (cartanProj P (PBW.basisOfIsCompl (isCompl_nNeg_borel P) bN bB
        ((toLex ∘ Sum.inl) i)))) = fun _ : σ => (0 : 𝓢) := by
    funext i
    simp [PBW.basisOfIsCompl_inl, cartanProj_of_mem_nNeg P (bN i).property]
  have hb : (fun i => SymmetricAlgebra.ι K H
      (cartanProj P (PBW.basisOfIsCompl (isCompl_nNeg_borel P) bN bB
        ((toLex ∘ Sum.inr) i)))) =
      fun i => envBorelCartanPolynomial P (UniversalEnvelopingAlgebra.ι K (bB i)) := by
    funext i
    simp only [Function.comp_apply, PBW.basisOfIsCompl_inr,
      envBorelCartanPolynomial, UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl
  simp only [Function.comp_def] at hn hb ⊢
  rw [hn, hb]
  simp [VermaModule.counitNNeg, Algebra.smul_def, MvPolynomial.aeval_def,
    map_finsuppProd]

/-- Restriction preserves the full homogeneous component in every degree. -/
theorem cartanRestriction_mem_homogeneous (n : ℕ)
    {p : SymmetricAlgebra K 𝔤} (hp : p ∈ SymmetricAlgebra.homogeneousSubmodule n) :
    cartanRestriction P p ∈ SymmetricAlgebra.homogeneousSubmodule n :=
  SymmetricAlgebra.lift_comp_ι_mem_homogeneous (cartanProj P) n hp

/-- Exact ordered-PBW formula, using a genuinely adapted triangular basis.
It does not identify HC with restriction of the total symmetrization inverse. -/
theorem harishChandraProjection_eq_cartanRestriction_pbw
    {σ τ : Type*} [LinearOrder σ] [LinearOrder τ]
    (bN : Basis σ K (nNeg P)) (bB : Basis τ K (borel P)) (u : 𝓤) :
    harishChandraProjection P u = cartanRestriction P
      ((SymmetricAlgebra.equivMvPolynomial
        (PBW.basisOfIsCompl (isCompl_nNeg_borel P) bN bB)).symm
          (pbwEquiv (PBW.basisOfIsCompl (isCompl_nNeg_borel P) bN bB) u)) := by
  let b := PBW.basisOfIsCompl (isCompl_nNeg_borel P) bN bB
  have hm : harishChandraProjection P = (cartanRestriction P).toLinearMap.comp
      ((SymmetricAlgebra.equivMvPolynomial b).symm.toLinearMap.comp
        (pbwEquiv b).toLinearMap) := by
    apply (pbwBasis b).ext
    intro s
    simp only [pbwBasis_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      AlgEquiv.toLinearMap_apply, AlgHom.toLinearMap_apply, pbwEquiv_pbwMonomial]
    rw [harishChandraProjection_pbwMonomial]
    exact (DFunLike.congr_fun (SymmetricAlgebra.lift_comp_equivMvPolynomial_symm b
      ((SymmetricAlgebra.ι K H).comp (cartanProj P))) (MvPolynomial.monomial s 1)).symm
  exact LinearMap.congr_fun hm u

/-- Each adapted ordered monomial projects to a homogeneous Cartan polynomial
of its full word length, possibly zero. -/
theorem harishChandraProjection_pbwMonomial_mem_homogeneous
    {σ τ : Type*} [LinearOrder σ] [LinearOrder τ]
    (bN : Basis σ K (nNeg P)) (bB : Basis τ K (borel P))
    (s : σ ⊕ₗ τ →₀ ℕ) :
    harishChandraProjection P
      (pbwMonomial K (PBW.basisOfIsCompl (isCompl_nNeg_borel P) bN bB) s) ∈
        SymmetricAlgebra.homogeneousSubmodule s.degree := by
  rw [harishChandraProjection_eq_cartanRestriction_pbw P bN bB, pbwEquiv_pbwMonomial]
  apply cartanRestriction_mem_homogeneous
  rw [SymmetricAlgebra.mem_homogeneousSubmodule_iff
    (PBW.basisOfIsCompl (isCompl_nNeg_borel P) bN bB)]
  simp only [AlgEquiv.apply_symm_apply]
  exact MvPolynomial.isHomogeneous_monomial 1 rfl

/-- The actual HC projection preserves PBW degree. The conclusion is genuine polynomial
 total degree in every Cartan basis, not a replacement filtration defined by the image. -/
theorem harishChandraProjection_totalDegree_le {κ : Type*} (bH : Basis κ K H)
    (n : ℕ) {u : 𝓤} (hu : u ∈ filtration K 𝔤 n) :
    (SymmetricAlgebra.equivMvPolynomial bH (harishChandraProjection P u)).totalDegree ≤ n := by
  let : LinearOrder (Free.ChooseBasisIndex K (nNeg P)) :=
    IsWellOrder.linearOrder WellOrderingRel
  let : LinearOrder (Free.ChooseBasisIndex K (borel P)) :=
    IsWellOrder.linearOrder WellOrderingRel
  let bN := Free.chooseBasis K (nNeg P)
  let bB := Free.chooseBasis K (borel P)
  let b := PBW.basisOfIsCompl (isCompl_nNeg_borel P) bN bB
  rw [filtration_eq_span b n] at hu
  rw [← MvPolynomial.mem_restrictTotalDegree]
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨s, hs, rfl⟩ := hu
    apply (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
    exact ((SymmetricAlgebra.mem_homogeneousSubmodule_iff bH _ _).mp
      (harishChandraProjection_pbwMonomial_mem_homogeneous P bN bB s)).totalDegree_le.trans hs
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

/-- Graded HC compatibility for every filtered enveloping element, not just the centre:
the top homogeneous Cartan term is genuine restriction of the canonical full PBW symbol.
Reconstructed ordered-PBW proof; no graded compatibility or HC image premise. -/
theorem harishChandraProjection_homogeneousComponent (n : ℕ)
    (u : filtration K 𝔤 n) :
    SymmetricAlgebra.homogeneousComponent n (harishChandraProjection P u) =
      cartanRestriction P ((symmetricAlgebraEquivAssociatedGraded K 𝔤).symm
        (toGr K 𝔤 n u)) := by
  classical
  let : LinearOrder (Free.ChooseBasisIndex K (nNeg P)) :=
    IsWellOrder.linearOrder WellOrderingRel
  let : LinearOrder (Free.ChooseBasisIndex K (borel P)) :=
    IsWellOrder.linearOrder WellOrderingRel
  let bN := Free.chooseBasis K (nNeg P)
  let bB := Free.chooseBasis K (borel P)
  let b := PBW.basisOfIsCompl (isCompl_nNeg_borel P) bN bB
  have hm : (SymmetricAlgebra.homogeneousComponent n).comp
      ((harishChandraProjection P).comp (filtration K 𝔤 n).subtype) =
      (cartanRestriction P).toLinearMap.comp
        ((symmetricAlgebraEquivAssociatedGraded K 𝔤).symm.toLinearMap.comp (toGr K 𝔤 n)) := by
    apply (filtrationBasis b n).ext
    intro s
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, filtrationBasis_apply,
      AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply]
    rw [SymmetricAlgebra.homogeneousComponent_of_mem
      (harishChandraProjection_pbwMonomial_mem_homogeneous P bN bB s.val)]
    by_cases hs : n = s.val.degree
    · rw [ite_eq_left hs, harishChandraProjection_eq_cartanRestriction_pbw P bN bB,
        pbwEquiv_pbwMonomial]
      congr 1
      apply (symmetricAlgebraEquivAssociatedGraded K 𝔤).injective
      rw [AlgEquiv.apply_symm_apply]
      change symmetricAlgebraToAssociatedGraded K 𝔤 _ = _
      rw [symmetricAlgebraToAssociatedGraded_symm_monomial b _ s.val rfl]
      exact toGr_congr hs.symm (by simp)
    · rw [ite_eq_right hs]
      have hlt : s.val.degree < n := lt_of_le_of_ne s.property (Ne.symm hs)
      have hz : toGr K 𝔤 n (filtrationBasis b n s) = 0 := by
        apply toGr_eq_zero_of_mem
        · simpa only [filtrationBasis_apply] using
            (filtration_mono (show s.val.degree ≤ n - 1 by omega)
              (pbwMonomial_mem_filtration (R := K) b s.val))
        · intro hn
          omega
      rw [hz, map_zero, map_zero]
  exact LinearMap.congr_fun hm u

/-- The actual unshifted HC algebra map has the prescribed top term whenever an
actual filtered central element has the given full PBW symbol. -/
theorem harishChandra_homogeneousComponent_of_symbol (n : ℕ)
    (z : Subalgebra.center K 𝓤) (hz : z.val ∈ filtration K 𝔤 n)
    (p : SymmetricAlgebra K 𝔤)
    (hp : toGr K 𝔤 n ⟨z.val, hz⟩ = symmetricAlgebraToAssociatedGraded K 𝔤 p) :
    SymmetricAlgebra.homogeneousComponent n (harishChandra P z) =
      cartanRestriction P p := by
  change SymmetricAlgebra.homogeneousComponent n (harishChandraProjection P z.val) = _
  rw [harishChandraProjection_homogeneousComponent P n ⟨z.val, hz⟩, hp]
  exact congrArg (cartanRestriction P)
    ((symmetricAlgebraEquivAssociatedGraded K 𝔤).symm_apply_apply p)

/-- Consumer of the production invariant homogeneous central lift: every actual
adjoint-invariant homogeneous full symbol has a filtered central lift whose actual HC
polynomial has precisely its genuine Cartan restriction as top homogeneous component.
This does not claim extension of arbitrary Weyl-invariant Cartan symbols. -/
theorem exists_centralLift_harishChandra_top (n : ℕ)
    (p : SymmetricAlgebra.homogeneousSubmodule (K := K) (M := 𝔤) n)
    (hp : ∀ x : 𝔤, SymmetricAlgebra.derivation (LieAlgebra.ad K 𝔤 x) p.val = 0) :
    ∃ z : Subalgebra.center K 𝓤, ∃ hz : z.val ∈ filtration K 𝔤 n,
      toGr K 𝔤 n ⟨z.val, hz⟩ = symmetricAlgebraToAssociatedGraded K 𝔤 p.val ∧
      SymmetricAlgebra.homogeneousComponent n (harishChandra P z) =
        cartanRestriction P p.val := by
  obtain ⟨z, hz, hsymbol⟩ := exists_centralLift_of_invariant_homogeneous n p hp
  exact ⟨z, hz, hsymbol, harishChandra_homogeneousComponent_of_symbol P n z hz p.val hsymbol⟩

/-- Negative-rho translation preserves the actual HC degree and changes it only
in lower degree. The degree-zero correction vanishes exactly. -/
theorem shiftedHarishChandra_degree_le {κ : Type*} (bH : Basis κ K H)
    (n : ℕ) (z : Subalgebra.center K 𝓤) (hz : z.val ∈ filtration K 𝔤 n) :
    (SymmetricAlgebra.equivMvPolynomial bH (shiftedHarishChandra P z)).totalDegree ≤ n ∧
    (SymmetricAlgebra.equivMvPolynomial bH
      (shiftedHarishChandra P z - harishChandra P z)).totalDegree ≤ n - 1 ∧
    (n = 0 → shiftedHarishChandra P z - harishChandra P z = 0) :=
  SymmetricAlgebra.affinePullback_id_degree_le bH (-P.rho) n
    (harishChandraProjection_totalDegree_le P bH n hz)

/-- The shifted HC map has the same genuine restricted top PBW symbol. The sign
is the production negative-rho convention; no total-polynomial equality is asserted. -/
theorem shiftedHarishChandra_homogeneousComponent (n : ℕ)
    (z : Subalgebra.center K 𝓤) (hz : z.val ∈ filtration K 𝔤 n) :
    SymmetricAlgebra.homogeneousComponent n (shiftedHarishChandra P z) =
      cartanRestriction P ((symmetricAlgebraEquivAssociatedGraded K 𝔤).symm
        (toGr K 𝔤 n ⟨z.val, hz⟩)) := by
  change SymmetricAlgebra.homogeneousComponent n
    (SymmetricAlgebra.affinePullback LinearMap.id (-P.rho)
      (harishChandraProjection P z.val)) = _
  rw [SymmetricAlgebra.homogeneousComponent_affinePullback_id (Free.chooseBasis K H)
    (-P.rho) n (harishChandraProjection_totalDegree_le P (Free.chooseBasis K H) n hz)]
  exact harishChandraProjection_homogeneousComponent P n ⟨z.val, hz⟩

/-- Full consumer for HC degree induction: an actual adjoint-invariant homogeneous
full symbol has an actual central filtered lift with the right PBW symbol and the right
shifted HC top term. Chevalley extension and HC image/injectivity are not assumed. -/
theorem exists_centralLift_shiftedHarishChandra_top (n : ℕ)
    (p : SymmetricAlgebra.homogeneousSubmodule (K := K) (M := 𝔤) n)
    (hp : ∀ x : 𝔤, SymmetricAlgebra.derivation (LieAlgebra.ad K 𝔤 x) p.val = 0) :
    ∃ z : Subalgebra.center K 𝓤, ∃ hz : z.val ∈ filtration K 𝔤 n,
      toGr K 𝔤 n ⟨z.val, hz⟩ = symmetricAlgebraToAssociatedGraded K 𝔤 p.val ∧
      SymmetricAlgebra.homogeneousComponent n (shiftedHarishChandra P z) =
        cartanRestriction P p.val := by
  obtain ⟨z, hz, hsymbol⟩ := exists_centralLift_of_invariant_homogeneous n p hp
  refine ⟨z, hz, hsymbol, ?_⟩
  rw [shiftedHarishChandra_homogeneousComponent P n z hz, hsymbol]
  exact congrArg (cartanRestriction P)
    ((symmetricAlgebraEquivAssociatedGraded K 𝔤).symm_apply_apply p.val)

end Matrix.Realization.KacMoodyAlgebra
