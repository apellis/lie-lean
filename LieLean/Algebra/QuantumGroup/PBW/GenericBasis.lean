/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.KostantCounting
import LieLean.Algebra.QuantumGroup.PBW.KostantDimension
import LieLean.Algebra.QuantumGroup.PBW.Independence
import LieLean.Algebra.QuantumGroup.PBW.FiniteTypeSpan

/-!
# Finite-type quantum PBW bases

## Main results

* `card_pbwMonomialDegree_fiber`: natural-degree fibers of actual ordered root-vector
  monomials have the Kostant cardinality.
* `span_pbwMonomialDegree_fiber`: those monomials span the corresponding quantum weight space.
* `finiteTypePBWBasis`: the actual ordered monomials form a basis of `U⁺`, over any field at
  any nonzero parameter which is not a root of unity.
* `exists_finiteTypePBWBasis`: such a basis exists, without assuming a chosen reduced word.

The natural-degree comparison and counting use only a nonzero non-root-of-unity parameter.
The degreewise spanning theorems `span_pbwMonomialDegree_fiber` and
`span_pbwMonomial_of_isFiniteCartan` are proved here by a dimension count which requires
characteristic zero and a parameter transcendental over `ℚ`. The basis `finiteTypePBWBasis`
instead uses the straightening proof of spanning `span_pbwMonomial_longest_of_isFiniteCartan`
(`PBW.FiniteTypeSpan`), which needs neither.

## References

Reconstructed dimension argument: combine the longest-word root enumeration and Kostant
counting from `PBW.KostantCounting`, the quantum graded dimensions from `PBW.KostantDimension`,
and actual ordered-monomial independence from `PBW.Independence`.
-/

noncomputable section
open Module Matrix.Realization.KacMoodyAlgebra
namespace QuantumGroup
variable {I Y k K H : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)
  [Field k] {v : k} [hv0 : NeZero v]
  [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  (P : Matrix.Realization D.cartanMatrix K H) (hD : D.cartanMatrix.IsFiniteCartan)
  (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

include hv hv0

/-- Natural PBW degrees retain exactly the signed integer prefix degrees. -/
theorem pbwMonomialDegree_cast_apply {ω : List I}
    (hω : (P.coxeterSystem hD.isGeneralizedCartan).IsReduced ω)
    (c : Fin ω.length → ℕ) (i : I) :
    (pbwMonomialDegree (R := R) ω c i : ℤ) =
      (∑ n : Fin ω.length, c n • rootVectorDegree (R := R) ω n n.isLt) i := by
  have hcast (n : Fin ω.length) :
      (positiveRootVectorDegree (R := R) ω n n.isLt i : ℤ) =
        rootVectorDegree (R := R) ω n n.isLt i :=
    Int.toNat_of_nonneg (rootVectorDegree_nonneg_of_isFiniteCartan (R := R) hD hv hω n n.isLt i)
  simp [pbwMonomialDegree, List.sum_ofFn, hcast]

/-- The existing natural PBW degree realizes to the exact Kostant exponent weight. -/
theorem pbwMonomialDegree_realization {ω : List I}
    (hω : (P.coxeterSystem hD.isGeneralizedCartan).IsReduced ω)
    (c : Fin ω.length → ℕ) :
    P.rootOf (fun i ↦ (pbwMonomialDegree (R := R) ω c i : ℤ)) =
      prefixExponentWeight P hD ω c := by
  simp_rw [pbwMonomialDegree_cast_apply R P hD hv hω]
  exact realize_sum_rootVectorDegree R P hD ω c

/-- Injectivity of the realization identifies natural-degree and realized-weight fibers. -/
theorem pbwMonomialDegree_eq_iff {ω : List I}
    (hω : (P.coxeterSystem hD.isGeneralizedCartan).IsReduced ω)
    (c : Fin ω.length → ℕ) (ν : I →₀ ℕ) :
    pbwMonomialDegree (R := R) ω c = ν ↔
      prefixExponentWeight P hD ω c = P.rootOf (fun i ↦ (ν i : ℤ)) := by
  rw [← pbwMonomialDegree_realization R P hD hv hω]
  constructor
  · rintro rfl; rfl
  · intro h
    have he := P.rootOf_injective h
    ext i
    exact_mod_cast congrFun he i

/-- The actual natural-degree monomial fibers have Kostant cardinality. -/
theorem card_pbwMonomialDegree_fiber {ω : List I}
    (hω : (P.coxeterSystem hD.isGeneralizedCartan).IsReduced ω)
    (hw : (P.coxeterSystem hD.isGeneralizedCartan).wordProd ω = finiteTypeLongest P hD)
    (ν : I →₀ ℕ) :
    Nat.card {c : Fin ω.length → ℕ // pbwMonomialDegree (R := R) ω c = ν} =
      kostantPartition P (P.rootOf (fun i ↦ (ν i : ℤ))) := by
  have e : {c : Fin ω.length → ℕ // pbwMonomialDegree (R := R) ω c = ν} ≃
      {c : Fin ω.length → ℕ //
        prefixExponentWeight P hD ω c = P.rootOf (fun i ↦ (ν i : ℤ))} :=
    Equiv.subtypeEquivRight (fun c ↦ pbwMonomialDegree_eq_iff R P hD hv hω c ν)
  exact (Nat.card_congr e).trans (card_prefixExponentFiber P hD hω hw _)

/-- Each homogeneous piece is spanned by exactly its ordered PBW monomials,
at a transcendental parameter in characteristic zero. -/
theorem span_pbwMonomialDegree_fiber [CharZero k] (htrans : Transcendental ℚ v)
    {ω : List I} (hω : (P.coxeterSystem hD.isGeneralizedCartan).IsReduced ω)
    (hw : (P.coxeterSystem hD.isGeneralizedCartan).wordProd ω = finiteTypeLongest P hD)
    (ν : I →₀ ℕ) :
    Submodule.span k (Set.range (fun c :
      {c : Fin ω.length → ℕ // pbwMonomialDegree (R := R) ω c = ν} ↦
        CoxeterSystem.pbwMonomial (braidEquivOfNotRoot R hv) (E R v) ω c.1)) =
      plusWeightSpace R v ν := by
  let e := (Equiv.subtypeEquivRight
    (fun c ↦ pbwMonomialDegree_eq_iff R P hD hv hω c ν)).trans
      (prefixExponentFiberEquiv P hD hω hw (P.rootOf fun i ↦ (ν i : ℤ)))
  have : Finite {s : NegRootIndex P →₀ ℕ // negRootWt P s =
      P.rootOf (fun i ↦ (ν i : ℤ))} :=
    (finite_setOf_negRootWt_eq P _).to_subtype
  have : Finite {c : Fin ω.length → ℕ // pbwMonomialDegree (R := R) ω c = ν} :=
    Finite.of_injective e e.injective
  let := Fintype.ofFinite {c : Fin ω.length → ℕ // pbwMonomialDegree (R := R) ω c = ν}
  apply (linearIndependent_iff_span_eq_plusWeightSpace htrans P ν _ ?_ ?_).mp
  · exact (linearIndependent_pbwMonomial_of_isFiniteCartan (R := R) hv hD hω).comp
      _ Subtype.val_injective
  · intro c
    simpa only [c.property] using
      pbwMonomial_mem_plusWeightSpace_of_isFiniteCartan (R := R) hD hv hω c.1
  · rw [← Nat.card_eq_fintype_card]
    exact card_pbwMonomialDegree_fiber R P hD hv hω hw ν

/-- Ordered PBW monomials for a longest reduced word span the whole positive quantum
subalgebra. The dimension argument retains characteristic zero and transcendence. -/
theorem span_pbwMonomial_of_isFiniteCartan [CharZero k] (htrans : Transcendental ℚ v)
    {ω : List I} (hω : (P.coxeterSystem hD.isGeneralizedCartan).IsReduced ω)
    (hw : (P.coxeterSystem hD.isGeneralizedCartan).wordProd ω = finiteTypeLongest P hD) :
    Submodule.span k (Set.range
      (CoxeterSystem.pbwMonomial (braidEquivOfNotRoot R hv) (E R v) ω)) =
      (Algebra.adjoin k (Set.range (E R v))).toSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    rw [← iSup_plusWeightSpace]
    exact Submodule.mem_iSup_of_mem (pbwMonomialDegree (R := R) ω c)
      (pbwMonomial_mem_plusWeightSpace_of_isFiniteCartan (R := R) hD hv hω c)
  · rw [← iSup_plusWeightSpace]
    apply iSup_le
    intro ν
    rw [← span_pbwMonomialDegree_fiber R P hD hv htrans hω hw ν]
    apply Submodule.span_mono
    rintro _ ⟨c, rfl⟩
    exact ⟨c.1, rfl⟩

/-- **The PBW basis of `U⁺` in finite type** ([Jan] Thm. 8.24, opposite multiplication order;
[Lus] Cor. 40.2.2, over `ℚ(v)`): for every Cartan
datum of finite type, over any field, at any nonzero parameter which is not a root of unity, the
ordered monomials in the root vectors along a reduced word of the longest element form a basis
of `U⁺`. Spanning is `span_pbwMonomial_longest_of_isFiniteCartan`, independence
`linearIndependent_pbwMonomial_of_isFiniteCartan`. -/
def finiteTypePBWBasis
    {ω : List I} (hω : (P.coxeterSystem hD.isGeneralizedCartan).IsReduced ω)
    (hw : (P.coxeterSystem hD.isGeneralizedCartan).wordProd ω = finiteTypeLongest P hD) :
    Basis (Fin ω.length → ℕ) k (Algebra.adjoin k (Set.range (E R v))) :=
  (Basis.span (linearIndependent_pbwMonomial_of_isFiniteCartan (R := R) hv hD hω)).map
    (LinearEquiv.ofEq _ _ (by
      have := P.finite_weylGroup hD
      exact span_pbwMonomial_longest_of_isFiniteCartan R v hv hD
        (P.coxeterSystem hD.isGeneralizedCartan) hω hw))

/-- The basis has exactly the promised ordered monomials, without a change of vectors. -/
theorem finiteTypePBWBasis_apply
    {ω : List I} (hω : (P.coxeterSystem hD.isGeneralizedCartan).IsReduced ω)
    (hw : (P.coxeterSystem hD.isGeneralizedCartan).wordProd ω = finiteTypeLongest P hD)
    (c : Fin ω.length → ℕ) :
    (finiteTypePBWBasis R P hD hv hω hw c : QuantumGroup R v) =
      CoxeterSystem.pbwMonomial (braidEquivOfNotRoot R hv) (E R v) ω c := by
  simp only [finiteTypePBWBasis, Basis.map_apply, Basis.span_apply]
  rfl

/-- A longest reduced word and its genuine ordered-monomial basis exist in finite type, over any
field at any nonzero parameter which is not a root of unity; no supplied basis or
root-enumeration hypothesis is required. -/
theorem exists_finiteTypePBWBasis :
    ∃ ω : List I, (P.coxeterSystem hD.isGeneralizedCartan).IsReduced ω ∧
      (P.coxeterSystem hD.isGeneralizedCartan).wordProd ω = finiteTypeLongest P hD ∧
      ∃ b : Basis (Fin ω.length → ℕ) k
      (Algebra.adjoin k (Set.range (E R v))),
      ∀ c, (b c : QuantumGroup R v) =
        CoxeterSystem.pbwMonomial (braidEquivOfNotRoot R hv) (E R v) ω c := by
  obtain ⟨ω, hω, hw⟩ :=
    (P.coxeterSystem hD.isGeneralizedCartan).exists_isReduced (finiteTypeLongest P hD)
  exact ⟨ω, hω, hw.symm, finiteTypePBWBasis R P hD hv hω hw.symm,
    finiteTypePBWBasis_apply R P hD hv hω hw.symm⟩

end QuantumGroup
