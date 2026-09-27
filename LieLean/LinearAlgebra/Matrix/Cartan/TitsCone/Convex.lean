/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import LieLean.LinearAlgebra.Matrix.Cartan.TitsCone
import LieLean.LinearAlgebra.Matrix.Cartan.TitsCone.Coroots

/-!
# The Tits cone is a convex cone

Let `A` be a generalized Cartan matrix with realization `(𝔥, Π, Π^∨)` over a linearly ordered
field `K`, `W` its Weyl group acting on `𝔥*`, `C ⊂ 𝔥*` the dominant chamber and
`X = ⋃_{w ∈ W} w(C)` the Tits cone. We prove ([Kac] Prop. 3.12 (c) (check)) that

  `X = {λ ∈ 𝔥* | ⟨λ, β^∨⟩ < 0 for only finitely many positive real coroots β^∨}`,

and deduce that `X` is a convex cone. [Kac] works in `𝔥_ℝ`, with all positive roots `α ∈ Δ₊`; we
work dually in `𝔥*` and with the positive *real* coroots only, which keeps the statement
independent of the Lie algebra. (We do not prove here that using all positive coroots, i.e. the
positive roots of `𝔤(Aᵀ)`, gives the same set.)

The proof is Kac's: if `λ = w μ` with `μ ∈ C` and `w ∈ W`, then `⟨λ, β^∨⟩ = ⟨μ, u β^∨⟩` for the
contragredient `u ∈ W^∨` of `w`, which is `≥ 0` unless `u β^∨ < 0`, and there are only finitely
many such `β^∨` (`Matrix.Realization.finite_inversionSet_coweylGroup`). Conversely, if the set
`N(λ)` of positive real coroots on which `λ` is negative is finite and `λ ∉ C`, pick `i` with
`⟨λ, αᵢ^∨⟩ < 0`; since `rᵢ^∨` permutes the positive real coroots other than `αᵢ^∨`,
`N(rᵢ λ) = rᵢ^∨ (N(λ) \ {αᵢ^∨})` is smaller, and we conclude by induction.

## Main definitions

* `Matrix.Realization.titsPointedCone`: the Tits cone as a `PointedCone`.

## Main results

* `Matrix.Realization.mem_titsCone_iff`: the description of `X` above.
* `Matrix.Realization.add_mem_titsCone`, `Matrix.Realization.smul_mem_titsCone`,
  `Matrix.Realization.convex_titsCone`: `X` is a convex cone.
* `Matrix.Realization.titsPointedCone`: `X` as a `PointedCone`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Prop. 3.12.
-/

open Module

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsGeneralizedCartan)

lemma apply_corootOf_nonneg {μ : Dual K H} (hμ : μ ∈ P.dominantChamber) {k : ι → ℤ}
    (hk : 0 ≤ k) : 0 ≤ μ (P.corootOf k) := by
  rw [apply_corootOf]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (by simpa using hk i) (hμ i)

/-- A point of the Tits cone is negative on only finitely many positive real coroots
([Kac] Prop. 3.12 (c) (check), dually). -/
theorem finite_of_mem_titsCone {μ : Dual K H} (hμ : μ ∈ P.titsCone hA) :
    {h | h ∈ P.posRealCoroots hA ∧ μ h < 0}.Finite := by
  obtain ⟨w, hw, ν, hν, rfl⟩ := hμ
  obtain ⟨u, hu, hwu⟩ := P.exists_coweylGroup_apply_apply hA hw
  refine (P.finite_inversionSet_coweylGroup hA hu).subset ?_
  rintro h ⟨hh, hlt⟩
  refine ⟨hh, fun ⟨_, k, hk, hkh⟩ ↦ ?_⟩
  rw [hwu, ← hkh] at hlt
  exact (P.apply_corootOf_nonneg hν hk).not_gt hlt

/-- A point of `𝔥*` which is negative on only finitely many positive real coroots lies in the
Tits cone ([Kac] Prop. 3.12 (c) (check), dually). -/
theorem mem_titsCone_of_finite {μ : Dual K H}
    (hμ : {h | h ∈ P.posRealCoroots hA ∧ μ h < 0}.Finite) : μ ∈ P.titsCone hA := by
  generalize hn : {h | h ∈ P.posRealCoroots hA ∧ μ h < 0}.ncard = n
  induction n using Nat.strong_induction_on generalizing μ with
  | _ n ih =>
  by_cases hC : μ ∈ P.dominantChamber
  · exact P.dominantChamber_subset_titsCone hA hC
  simp only [mem_dominantChamber, not_forall, not_le] at hC
  obtain ⟨i, hi⟩ := hC
  set S := {h | h ∈ P.posRealCoroots hA ∧ μ h < 0}
  have hsub : {h | h ∈ P.posRealCoroots hA ∧ P.reflection hA i μ h < 0} ⊆
      P.coreflection hA i '' (S \ {P.coroot i}) := by
    rintro h ⟨hh, hlt⟩
    rw [reflection_apply_apply] at hlt
    have hne : h ≠ P.coroot i := by
      rintro rfl
      rw [coreflection_coroot_self, map_neg] at hlt
      linarith
    refine ⟨P.coreflection hA i h,
      ⟨⟨P.coreflection_mem_posRealCoroots hA hh hne, hlt⟩, fun heq ↦ ?_⟩, by simp⟩
    refine P.neg_notMem_posRealCoroots hA (P.coroot_mem_posRealCoroots hA i) ?_
    rw [Set.mem_singleton_iff] at heq
    rw [← coreflection_coroot_self P hA i, ← heq, coreflection_coreflection]
    exact hh
  have hfin : (P.coreflection hA i '' (S \ {P.coroot i})).Finite := (hμ.sdiff).image _
  have hlt : {h | h ∈ P.posRealCoroots hA ∧ P.reflection hA i μ h < 0}.ncard < n :=
    hn ▸ (Set.ncard_le_ncard hsub hfin).trans_lt ((Set.ncard_image_le hμ.sdiff).trans_lt
      (Set.ncard_sdiff_singleton_lt_of_mem ⟨P.coroot_mem_posRealCoroots hA i, hi⟩ hμ))
  have := P.apply_mem_titsCone hA (P.reflection_mem_weylGroup hA i)
    (ih _ hlt (hfin.subset hsub) rfl)
  rwa [reflection_reflection] at this

/-- **The Tits cone** ([Kac] Prop. 3.12 (c) (check), for the action on `𝔥*`):
`X = {λ | ⟨λ, β^∨⟩ < 0 for only finitely many positive real coroots β^∨}`. -/
theorem mem_titsCone_iff {μ : Dual K H} :
    μ ∈ P.titsCone hA ↔ {h | h ∈ P.posRealCoroots hA ∧ μ h < 0}.Finite :=
  ⟨P.finite_of_mem_titsCone hA, P.mem_titsCone_of_finite hA⟩

omit [IsStrictOrderedRing K] in
lemma zero_mem_titsCone : 0 ∈ P.titsCone hA :=
  P.dominantChamber_subset_titsCone hA fun i ↦ by simp

/-- The Tits cone is stable under multiplication by nonnegative scalars. -/
theorem smul_mem_titsCone {c : K} (hc : 0 ≤ c) {μ : Dual K H} (hμ : μ ∈ P.titsCone hA) :
    c • μ ∈ P.titsCone hA := by
  obtain ⟨w, hw, ν, hν, rfl⟩ := hμ
  exact ⟨w, hw, c • ν, fun i ↦ by simpa using mul_nonneg hc (hν i), map_smul w c ν⟩

/-- The Tits cone is stable under addition ([Kac] Prop. 3.12 (c) (check), dually). -/
theorem add_mem_titsCone {μ ν : Dual K H} (hμ : μ ∈ P.titsCone hA) (hν : ν ∈ P.titsCone hA) :
    μ + ν ∈ P.titsCone hA := by
  rw [mem_titsCone_iff] at hμ hν ⊢
  refine (hμ.union hν).subset ?_
  rintro h ⟨hh, hlt⟩
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_lt] at hn
  rw [LinearMap.add_apply] at hlt
  linarith [hn.1 hh, hn.2 hh]

/-- **The Tits cone is convex** ([Kac] Prop. 3.12 (c) (check), dually). -/
theorem convex_titsCone : Convex K (P.titsCone hA) :=
  fun _ hμ _ hν _ _ ha hb _ ↦
    P.add_mem_titsCone hA (P.smul_mem_titsCone hA ha hμ) (P.smul_mem_titsCone hA hb hν)

/-- The Tits cone `X ⊂ 𝔥*` as a pointed convex cone. -/
def titsPointedCone : PointedCone K (Dual K H) where
  carrier := P.titsCone hA
  add_mem' := P.add_mem_titsCone hA
  zero_mem' := P.zero_mem_titsCone hA
  smul_mem' c _ hμ := P.smul_mem_titsCone hA c.2 hμ

@[simp] lemma coe_titsPointedCone : (P.titsPointedCone hA : Set (Dual K H)) = P.titsCone hA :=
  rfl

end Matrix.Realization
