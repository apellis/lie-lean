/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaEmbedding
import LieLean.Algebra.Lie.KacMoody.VermaHomFiniteType
import LieLean.Algebra.Lie.KacMoody.UpperClosureNonintegral
import LieLean.Algebra.Lie.KacMoody.BGG.Character
import LieLean.GroupTheory.Coxeter.Longest

/-!
# Strong linkage and the BGG theorem

Humphreys, GSM 94, §5.1. A weight `μ` is *strongly linked* to `λ` if there is a chain
`μ = μ_r ↑ ⋯ ↑ μ_1 ↑ μ_0 = λ` in which each step is a dot reflection `μ_{k+1} = s_β · μ_k` in a
positive root `β` with `⟨μ_k + ρ, β^∨⟩ ∈ ℤ_{>0}`, so that `μ_{k+1} < μ_k`.

## Main definitions

* `Matrix.Realization.StrongLinkStep`: one step `λ ↦ λ - n β` of strong linkage, for a positive
  real root `β = v αᵢ` and `⟨λ + ρ, β^∨⟩ = n ∈ ℤ_{>0}`.
* `Matrix.Realization.IsStronglyLinked`: the reflexive-transitive closure.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_injective_of_isStronglyLinked`,
  `VermaModule.multiplicity_ne_zero_of_isStronglyLinked`: **Humphreys, GSM 94, Theorem 5.1 (a)**
  (Verma): a strong linkage `μ ↑ λ` gives an embedding `M(μ) ↪ M(λ)`, hence `[M(λ) : L(μ)] ≠ 0`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.isStronglyLinked_of_multiplicity_ne_zero`:
  **Humphreys, GSM 94, Theorem 5.1 (b)** (BGG): a composition factor `L(μ)` of `M(λ)` has
  `μ ↑ λ`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.multiplicity_weylDot_ne_zero_iff_bruhatLE`:
  **Humphreys, GSM 94, Corollary 5.2**: for `λ` integral, antidominant and regular,
  `[M(w·λ) : L(w'·λ)] ≠ 0` iff `w' ≤ w` in the Bruhat order.

## Proof

Part (a) iterates Theorem 4.6 (`VermaModule.exists_injective_reflectionOf`), as in Humphreys.
For part (b), Humphreys develops the Jantzen filtration and sum formula (§5.3–§5.7). The library
has the Kac–Kazhdan criterion (`VermaModule.multiplicity_ne_zero_iff_reflTransGen`), proved from
the Jantzen filtration and the Shapovalov determinant: `[M(λ) : L(μ)] ≠ 0` iff there is a chain of
Kac–Kazhdan steps `λ ↦ λ - n α`, `2 (λ + ρ | α) = n (α | α)`. In finite type every root is real
(`roots_eq_realRoots`), and such a step is a strong linkage step
(`StrongLinkStep.of_kacKazhdanStep`).

For Corollary 5.2 we write `λ = w₀·Λ` with `Λ` dominant integral and work with `Λ`, where the
library has Verma's theorem in the form `x ≤ y ⇒ M(y·Λ) ↪ M(x·Λ)`
(`VermaModule.exists_injective_of_bruhatLE`). As in Humphreys, a strong linkage step
`z·Λ ↦ s_β z·Λ` is `z·Λ ↦ (z s_{β'})·Λ` with `β' = z⁻¹β > 0` and `z < z s_{β'}`
(`StrongLinkStep.bruhatLE_weylDot`); right multiplication by `w₀` reverses the Bruhat order.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §5.1.
-/

noncomputable section

open Module

namespace Matrix.Realization

section Defs

variable {ι K H : Type*} [Fintype ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)

/-- One step of **strong linkage** (Humphreys, GSM 94, §5.1): `μ = s_β · λ = λ - n β` for a
positive real root `β = v αᵢ` with `⟨λ + ρ, β^∨⟩ = n ∈ ℤ_{>0}`. -/
def StrongLinkStep (lam μ : Dual K H) : Prop :=
  ∃ (v : P.weylGroup hA) (i : ι) (n : ℕ), P.IsPosRoot hA v i ∧ 0 < n ∧
    P.corootPairing hA (lam + P.rho) v i = n ∧
      μ = lam - n • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i)

/-- `μ` is **strongly linked** to `λ` (`μ ↑ λ`, Humphreys, GSM 94, §5.1): `μ = λ`, or `μ` is
reached from `λ` by finitely many strong linkage steps. -/
def IsStronglyLinked (μ lam : Dual K H) : Prop :=
  Relation.ReflTransGen (P.StrongLinkStep hA) lam μ

end Defs

namespace KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsFiniteCartan)

/-- In finite type, a Kac–Kazhdan step is a strong linkage step: the root `α` is real,
`α = v αᵢ` with `v αᵢ > 0`, and `2 (λ + ρ | α) = n (α | α)` says `⟨λ + ρ, α^∨⟩ = n`. -/
theorem _root_.Matrix.Realization.StrongLinkStep.of_kacKazhdanStep
    (S : A.Symmetrization) {lam μ : Dual K H}
    (h : KacKazhdanStep P S lam μ) : P.StrongLinkStep hA.isGeneralizedCartan lam μ := by
  obtain ⟨α, hα, hroot, n, hn, rfl, hKK⟩ := h
  have hα0 : α ≠ 0 := fun h0 ↦ P.zero_notMem_posWeights (h0 ▸ hα)
  have hreal : α ∈ P.realRoots hA.isGeneralizedCartan := by
    rw [← roots_eq_realRoots P hA]
    exact ⟨hα0, hroot⟩
  obtain ⟨u, hu, i, rfl⟩ := hreal
  let w : P.weylGroup hA.isGeneralizedCartan := ⟨u, hu⟩
  have hpair : u.symm (lam + P.rho) (P.coroot i) = (n : K) := by
    apply (VermaModule.two_mul_dualBilinForm_root_eq_iff P hA.isGeneralizedCartan S _ i n).mp
    have h₁ := P.dualBilinForm_weylGroup hA.isGeneralizedCartan S hu
      (u.symm (lam + P.rho)) (P.root i)
    have h₂ := P.dualBilinForm_weylGroup hA.isGeneralizedCartan S hu (P.root i) (P.root i)
    simp only [LinearEquiv.apply_symm_apply] at h₁
    simpa only [h₁, h₂] using hKK
  exact ⟨w, i, n, isPosRoot_iff_mem_posWeights.mpr hα, hn, hpair, rfl⟩

namespace VermaModule

/-- **Humphreys, GSM 94, Theorem 5.1 (a)** (Verma). A strong linkage `μ ↑ λ` yields an
embedding of `M(μ)` into `M(λ)`. Finite type and characteristic zero; Humphreys works over `ℂ`. -/
theorem exists_injective_of_isStronglyLinked {lam μ : Dual K H}
    (h : P.IsStronglyLinked hA.isGeneralizedCartan μ lam) :
    ∃ φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P lam, Function.Injective φ := by
  induction h with
  | refl => exact ⟨LieModuleHom.id, Function.injective_id⟩
  | tail _ hstep ih =>
    obtain ⟨φ, hφ⟩ := ih
    obtain ⟨v, i, n, hv, -, hn, rfl⟩ := hstep
    obtain ⟨ψ, hψ⟩ := exists_injective_reflectionOf P hA hv hn
    exact ⟨φ.comp ψ, hφ.comp hψ⟩

/-- **Humphreys, GSM 94, Theorem 5.1 (a)**, second assertion: if `μ` is strongly linked to `λ`,
then `[M(λ) : L(μ)] ≠ 0`. -/
theorem multiplicity_ne_zero_of_isStronglyLinked {lam μ : Dual K H}
    (h : P.IsStronglyLinked hA.isGeneralizedCartan μ lam) :
    (isCategoryO P lam).multiplicity μ ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_injective_of_isStronglyLinked P hA h
  refine multiplicity_ne_zero_of_hom_ne_zero P (φ := φ) fun h0 ↦ hwv_ne_zero P μ (hφ ?_)
  rw [h0, map_zero, _root_.zero_apply]

/-- **Humphreys, GSM 94, Theorem 5.1 (b)** (Bernstein–Gelfand–Gelfand). Whenever `L(μ)` is a
composition factor of `M(λ)`, we have `μ ↑ λ`. Finite type, algebraically closed field of
characteristic zero (Humphreys works over `ℂ`); via the Kac–Kazhdan criterion instead of
Humphreys' direct use of the Jantzen sum formula. -/
theorem isStronglyLinked_of_multiplicity_ne_zero [IsAlgClosed K] {lam μ : Dual K H}
    (h : (isCategoryO P lam).multiplicity μ ≠ 0) :
    P.IsStronglyLinked hA.isGeneralizedCartan μ lam := by
  obtain ⟨d, hdpos, hposDef⟩ := hA.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hposDef.isHermitian
  set S := Symmetrization.ofDiagonal d hdpos hsymm
  have hc := (multiplicity_ne_zero_iff_reflTransGen P S hA.isGeneralizedCartan lam μ).mp h
  clear h
  induction hc with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (StrongLinkStep.of_kacKazhdanStep P hA S hstep)

section Bruhat

variable {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
include hΛ

omit [FiniteDimensional K H] in
/-- A strong linkage step from `z·Λ`, `Λ` dominant integral, goes to `z'·Λ` with `z ≤ z'` in the
Bruhat order (the computation of Humphreys, GSM 94, §5.2). -/
theorem _root_.Matrix.Realization.StrongLinkStep.exists_bruhatLE_weylDot
    {z : P.weylGroup hA.isGeneralizedCartan}
    {μ : Dual K H} (h : P.StrongLinkStep hA.isGeneralizedCartan
      (P.weylDot hA.isGeneralizedCartan z Λ) μ) :
    ∃ z', (P.coxeterSystem hA.isGeneralizedCartan).BruhatLE z z' ∧
      μ = P.weylDot hA.isGeneralizedCartan z' Λ := by
  have hA' := hA.isGeneralizedCartan
  set cs := P.coxeterSystem hA'
  obtain ⟨v, i, n, hv, hn0, hn, rfl⟩ := h
  have hΛρ : P.IsDominantIntegral (Λ + P.rho) := fun j ↦ by
    obtain ⟨m, hm⟩ := hΛ j
    exact ⟨m + 1, by rw [LinearMap.add_apply, hm, rho_coroot]; push_cast; rfl⟩
  set u := z⁻¹ * v
  have hzΛ : P.weylDot hA' z Λ + P.rho = (z : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) :=
    weylDot_add_rho P hA' z Λ
  have hpair : P.corootPairing hA' (Λ + P.rho) u i = n := by
    rw [← hn, hzΛ, corootPairing_apply]
  have hu : P.IsPosRoot hA' u i := by
    refine (isPosRoot_or u i).resolve_right fun hneg ↦ ?_
    have hneg' : ¬cs.IsLeftDescent (u * cs.simple i)⁻¹ i := by
      rw [CoxeterSystem.isLeftDescent_inv_iff]
      exact isPosRoot_iff_not_isRightDescent.mp hneg
    obtain ⟨m, hm⟩ := P.exists_apply_coroot_nat_of_not_isLeftDescent hA' hΛρ hneg'
    have h1 : P.corootPairing hA' (Λ + P.rho) (u * cs.simple i) i = m := hm
    rw [corootPairing_mul_simple, hpair] at h1
    have : ((n + m : ℕ) : K) = 0 := by push_cast; linear_combination -h1
    have := (Nat.add_eq_zero_iff.mp (by exact_mod_cast this)).1
    omega
  have hzu : z * u = v := by simp [u]
  have hlen : cs.length z < cs.length (z * P.reflectionOf hA' u i) := by
    have hneg : ¬P.IsPosRoot hA' (z * P.reflectionOf hA' u i * u) i := by
      rw [mul_assoc, reflectionOf_mul_self_eq, ← mul_assoc, hzu]
      exact fun h ↦ not_isPosRoot_and hv h
    have := length_mul_reflectionOf_lt hu hneg
    rwa [mul_assoc, reflectionOf_mul_self, mul_one] at this
  refine ⟨z * P.reflectionOf hA' u i, CoxeterSystem.BruhatStep.bruhatLE ⟨?_, hlen⟩, ?_⟩
  · have hs : (⟨P.reflection hA' i, P.reflection_mem_weylGroup hA' i⟩ : P.weylGroup hA') =
        cs.simple i := Subtype.ext (P.coxeterSystem_simple hA' i).symm
    exact ⟨u, i, by rw [← mul_assoc, inv_mul_cancel, one_mul, reflectionOf, hs]⟩
  · rw [show u = z⁻¹ * v from rfl, ← reflectionOf_mul, weylDot_mul]
    conv_rhs => rw [weylDot, reflectionOf_apply', hn]
    rw [← Nat.cast_smul_eq_nsmul K]
    abel

omit [FiniteDimensional K H] in
/-- Strong linkage from `x·Λ`, `Λ` dominant integral, only reaches weights `z·Λ` with
`x ≤ z`. -/
theorem _root_.Matrix.Realization.IsStronglyLinked.exists_bruhatLE_weylDot
    {x : P.weylGroup hA.isGeneralizedCartan}
    {μ : Dual K H}
    (h : P.IsStronglyLinked hA.isGeneralizedCartan μ (P.weylDot hA.isGeneralizedCartan x Λ)) :
    ∃ z, (P.coxeterSystem hA.isGeneralizedCartan).BruhatLE x z ∧
      μ = P.weylDot hA.isGeneralizedCartan z Λ := by
  induction h with
  | refl => exact ⟨x, CoxeterSystem.bruhatLE_refl _ x, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨z, hxz, rfl⟩ := ih
    obtain ⟨z', hzz', rfl⟩ := StrongLinkStep.exists_bruhatLE_weylDot P hA hΛ hstep
    exact ⟨z', hxz.trans hzz', rfl⟩

/-- For `Λ` dominant integral, `[M(x·Λ) : L(y·Λ)] ≠ 0` iff `x ≤ y` in the Bruhat order
(Humphreys, GSM 94, §5.2, in the dominant normalization). -/
theorem multiplicity_weylDot_ne_zero_iff_of_isDominantIntegral [IsAlgClosed K]
    {x y : P.weylGroup hA.isGeneralizedCartan} :
    (isCategoryO P (P.weylDot hA.isGeneralizedCartan x Λ)).multiplicity
        (P.weylDot hA.isGeneralizedCartan y Λ) ≠ 0 ↔
      (P.coxeterSystem hA.isGeneralizedCartan).BruhatLE x y := by
  constructor
  · intro h
    obtain ⟨z, hxz, hz⟩ := IsStronglyLinked.exists_bruhatLE_weylDot P hA hΛ
      (isStronglyLinked_of_multiplicity_ne_zero P hA h)
    rwa [weylDot_injective P hA.isGeneralizedCartan hΛ hz]
  · intro h
    obtain ⟨φ, hφ⟩ := exists_injective_of_bruhatLE hA.isGeneralizedCartan hΛ h
    refine multiplicity_ne_zero_of_hom_ne_zero P (φ := φ) fun h0 ↦ hwv_ne_zero P _ (hφ ?_)
    rw [h0, map_zero, _root_.zero_apply]

end Bruhat

/-- **Humphreys, GSM 94, Corollary 5.2.** Let `λ` be integral, antidominant and regular. For
`w, w' ∈ W`, the multiplicity `[M(w·λ) : L(w'·λ)]` is nonzero exactly when `w' ≤ w` (Bruhat). Finite
type, algebraically closed field of characteristic zero (Humphreys works over `ℂ`). -/
theorem multiplicity_weylDot_ne_zero_iff_bruhatLE [IsAlgClosed K] {lam : Dual K H}
    (hint : ∀ j, ∃ z : ℤ, lam (P.coroot j) = z)
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hreg : ∀ v i, P.corootPairing hA.isGeneralizedCartan (lam + P.rho) v i ≠ 0)
    (w w' : P.weylGroup hA.isGeneralizedCartan) :
    (isCategoryO P (P.weylDot hA.isGeneralizedCartan w lam)).multiplicity
        (P.weylDot hA.isGeneralizedCartan w' lam) ≠ 0 ↔
      (P.coxeterSystem hA.isGeneralizedCartan).BruhatLE w' w := by
  classical
  have hA' := hA.isGeneralizedCartan
  have := P.finite_weylGroup hA
  set cs := P.coxeterSystem hA'
  -- `λ = u·Λ` with `Λ` dominant integral
  obtain ⟨w₁, hw₁⟩ := P.exists_dominantIntegral_weylGroup hA' (ν := lam + P.rho) fun j ↦ by
    obtain ⟨z, hz⟩ := hint j
    exact ⟨z + 1, by rw [LinearMap.add_apply, hz, rho_coroot]; push_cast; rfl⟩
  set Λ := w₁.val (lam + P.rho) - P.rho with hΛdef
  have hΛ : P.IsDominantIntegral Λ := by
    intro j
    obtain ⟨m, hm⟩ := hw₁ j
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hreg w₁⁻¹ j
      rw [corootPairing, inv_inv]
      exact_mod_cast hm
    refine ⟨m - 1, ?_⟩
    rw [hΛdef, LinearMap.sub_apply, hm, rho_coroot,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm0), Nat.cast_one]
  set u := w₁⁻¹
  have hu : P.weylDot hA' u Λ = lam := by
    rw [weylDot, hΛdef, sub_add_cancel, inv_apply_apply, add_sub_cancel_right]
  -- antidominance forces `u = w₀`
  have hu₀ : u = cs.longestElement := by
    refine cs.eq_longestElement_iff_forall_isRightDescent.mpr fun i ↦ ?_
    by_contra hi
    have hpos : P.IsPosRoot hA' u i := isPosRoot_iff_not_isRightDescent.mpr hi
    obtain ⟨m, hm⟩ := hΛ i
    have hpair : P.corootPairing hA' (lam + P.rho) u i = ((m + 1 : ℕ) : ℤ) := by
      rw [← hu, weylDot_add_rho, corootPairing_apply, inv_mul_cancel]
      simp [corootPairing, hm]
    have := hlam u i hpos _ hpair
    omega
  have hw : ∀ x : P.weylGroup hA', P.weylDot hA' x lam = P.weylDot hA' (x * u) Λ := fun x ↦ by
    rw [weylDot_mul, hu]
  rw [hw, hw, multiplicity_weylDot_ne_zero_iff_of_isDominantIntegral P hA hΛ, hu₀,
    CoxeterSystem.mul_longestElement_bruhatLE_mul_longestElement_iff]

end VermaModule

end KacMoodyAlgebra

end Matrix.Realization
