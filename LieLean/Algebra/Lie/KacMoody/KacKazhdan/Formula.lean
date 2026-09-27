/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Exponents

/-!
# The Kac–Kazhdan determinant formula

Let `A` be a symmetrizable generalized Cartan matrix, `𝔤 = 𝔤(A)` over an algebraically closed
field `K` of characteristic zero, and `D_β(λ)` the determinant of the Shapovalov form on the weight
space `M(λ)_{λ-β}` of the Verma module, with respect to the PBW basis (which does not depend on
`λ`; `VermaModule.shapovalovDet`). The **Kac–Kazhdan determinant formula** ([KK] Thm. 1 (check);
[Kac] §9 (check)) states that, up to a nonzero constant,

`D_β(λ) = ∏_{α ∈ Δ₊} ∏_{n ≥ 1} ((λ + ρ | α) - n (α | α)/2)^{mult α · P(β - n α)}`,

where `P` is Kostant's partition function. Here the product runs over the index set `x` of a
basis of `𝔫₋` consisting of root vectors, in which each positive root `α` occurs `mult α` times
(`VermaModule.shapovalovDet_eq`).

As a corollary we obtain the **Kac–Kazhdan criterion**: `M(λ)` has a proper submodule meeting
`M(λ)_{λ-β}` (equivalently, the Shapovalov form is degenerate on `M(λ)_{λ-β}`) iff
`2 (λ + ρ | α) = n (α | α)` for some positive root `α` and `n ≥ 1` with `P(β - n α) ≠ 0`
(`VermaModule.maxSubmodule_inf_weightSpace_ne_bot_iff`).

## Proof

We first prove the formula in the form (`VermaModule.exists_shapovalovDet_eq_prod_kkIdx`)

`D_η(λ) = c ∏_{0 < γ ≤ η} (2 (λ + ρ | γ) - (γ | γ))^{d(γ) P(η - γ)}`,

with `d(γ)` the number of pairs `(x, n)`, `n ≥ 1`, with `n α_x = γ` (`kkMult`). By
`VermaModule.exists_eq_C_mul_prod_kkPoly`, `D_β = c_β ∏_γ ψ_γ^{e_β(γ)}` for `β ≤ η`. For
non-isotropic `γ` the hyperplanes `ψ_{γ'} = 0` with `γ'` on the line `K γ` are pairwise distinct,
`e_β(γ) = e_γ(γ) P(β - γ)` (`VermaModule.exponent_eq_mul_of_isotropic_ne_zero`), and the equality
of the sums of the exponents along the line `K γ` (`VermaModule.sum_exponent_parallel_eq`) for
`β = γ` gives `e_γ(γ) = d(γ)` by induction on the height of `γ`
(`VermaModule.exponent_self_eq_kkMult`). For isotropic `γ` all the `ψ_{γ'}`, `γ' ∈ K γ`, define
the same hyperplane, and the sum of their exponents is again given by
`VermaModule.sum_exponent_parallel_eq`. A product of affine polynomials is determined up to a
scalar by these multiplicities (`Module.Dual.exists_prod_pow_eq_C_mul_prod_pow`). Regrouping the
factors `ψ_{n α_x} = 2 n ((λ + ρ | α_x) - n (α_x | α_x)/2)` gives the formula.

This is the argument of [KK] §3 (check) in the form given by Jantzen for finite-dimensional `𝔤`
(via the Jantzen filtration and a comparison of leading terms); we reconstructed the details
ourselves. We work over an algebraically closed field (Kac and Kazhdan work over `ℂ`); this is used
only to see that the zeros of `D_β` lying on finitely many hyperplanes forces `D_β` to be a
product of their equations.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_shapovalovDet_eq_prod_kkIdx`,
  `Matrix.Realization.KacMoodyAlgebra.VermaModule.shapovalovDet_eq`: **the Kac–Kazhdan
  determinant formula**.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.maxSubmodule_inf_weightSpace_ne_bot_iff`:
  **the Kac–Kazhdan criterion**.

## References

* [KK] V. G. Kac, D. A. Kazhdan, *Structure of representations with highest weight of
  infinite-dimensional Lie algebras*, Adv. Math. 34 (1979), 97–108, Thm. 1 (check).
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9 (check).
* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, §5.8 (check) (Shapovalov's formula, finite type).
-/

open Module LieModule Module.Dual Polynomial

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (S : A.Symmetrization) (hA : A.IsGeneralizedCartan)

namespace VermaModule

include S in
/-- The Shapovalov determinant `D_β` is a nonzero polynomial function of `λ`. -/
theorem exists_poly_shapovalovDet (β : Dual K H) :
    ∃ F : MvPolynomial (PolyIdx K H) K, F ≠ 0 ∧ evalPoly K H F = shapovalovDet P β := by
  classical
  obtain ⟨c, hc, p, -, htop, hp⟩ := hasTop_det_pbwWeightBasis_kkExponent P S β
  refine ⟨p, fun h0 ↦ ?_, hp⟩
  rw [h0, map_zero] at htop
  have hprod : ∏ᶠ x : NegRootIndex P, linPoly K H ((P.toDual S).symm x.root) ^
      kkExponent P β x ≠ 0 := by
    rw [finprod_def]
    split_ifs
    · refine Finset.prod_ne_zero_iff.mpr fun x _ ↦ pow_ne_zero _ (linPoly_ne_zero ?_)
      rw [Ne, LinearEquiv.map_eq_zero_iff]
      exact x.root_ne_zero
    · exact one_ne_zero
  exact mul_ne_zero (by rwa [Ne, MvPolynomial.C_eq_zero]) hprod htop.symm

include hA in
/-- **The exponent of a non-isotropic `ψ_γ` in `D_γ`** is `d(γ)`, the number of pairs `(x, n)`,
`n ≥ 1`, with `n α_x = γ`. -/
theorem exponent_self_eq_kkMult {η : ι → ℤ} (F : (ι → ℤ) → MvPolynomial (PolyIdx K H) K)
    (hF : ∀ β, evalPoly K H (F β) = shapovalovDet P (P.rootOf β)) (c : (ι → ℤ) → K)
    (hc : ∀ β, β ≤ η → c β ≠ 0) (e : (ι → ℤ) → (ι → ℤ) → ℕ)
    (hFe : ∀ β, β ≤ η →
      F β = MvPolynomial.C (c β) * ∏ k ∈ kkIdx η, kkPoly P S (P.rootOf k) ^ e β k)
    {k : ι → ℤ} (hk : k ∈ kkIdx η)
    (hiso : P.dualBilinForm S (P.rootOf k) (P.rootOf k) ≠ 0) :
    e k k = kkMult P η k := by
  classical
  induction hn : (∑ i, k i).toNat using Nat.strong_induction_on generalizing k with
  | _ n ih =>
  obtain ⟨hk0, hkη, hkne⟩ := mem_kkIdx.mp hk
  have hγ : P.rootOf k ≠ 0 := P.rootOf_ne_zero hkne
  have hsum := sum_exponent_parallel_eq P S hkη (hF k) (hc k hkη) (hFe k hkη) hγ
  set T := (kkIdx η).filter fun k' ↦ ∃ u : K, P.rootOf k' = u • P.rootOf k
  have hkT : k ∈ T := Finset.mem_filter.mpr ⟨hk, 1, (one_smul _ _).symm⟩
  have hterm : ∀ k' ∈ T.erase k,
      e k k' = kkMult P η k' * kostantPartition P (P.rootOf k - P.rootOf k') := by
    intro k' hk'
    obtain ⟨hne, hk'T⟩ := Finset.mem_erase.mp hk'
    obtain ⟨hk'Γ, u, hu⟩ := Finset.mem_filter.mp hk'T
    obtain ⟨hk'0, hk'η, hk'ne⟩ := mem_kkIdx.mp hk'Γ
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hu
      exact P.rootOf_ne_zero hk'ne hu
    have hiso' : P.dualBilinForm S (P.rootOf k') (P.rootOf k') ≠ 0 := by
      rw [hu, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
      exact mul_ne_zero hu0 (mul_ne_zero hu0 hiso)
    rw [exponent_eq_mul_of_isotropic_ne_zero P S hA hkη hk'Γ hiso' (hF k) (hF k')
      (hc k hkη) (hc k' hk'η) (hFe k hkη) (hFe k' hk'η)]
    by_cases hP : kostantPartition P (P.rootOf k - P.rootOf k') = 0
    · rw [hP, mul_zero, mul_zero]
    congr 1
    obtain ⟨m, hm, hme⟩ := exists_rootOf_of_kostantPartition_ne_zero P hP
    have hkm : k = k' + m := P.rootOf_injective (by rw [map_add, ← hme]; abel)
    refine ih _ ?_ hk'Γ hiso' rfl
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hne (by rw [hkm, add_zero])
    have hpos := sum_pos_of_mem_posCone ⟨hm, hm0⟩
    have hk'pos := sum_pos_of_mem_posCone ⟨hk'0, hk'ne⟩
    have hsplit : ∑ i, k i = ∑ i, k' i + ∑ i, m i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hkm, Pi.add_apply]
    omega
  rw [← Finset.add_sum_erase _ _ hkT, ← Finset.add_sum_erase _ _ hkT,
    Finset.sum_congr rfl hterm, sub_self, kostantPartition_zero, mul_one] at hsum
  omega

include hA in
/-- **The Kac–Kazhdan determinant formula**, grouped by weights ([KK] Thm. 1 (check)). Over an
algebraically closed field of characteristic zero, for `η ∈ Q` there is `c ≠ 0` with
`D_η(λ) = c ∏_{0 < γ ≤ η} (2 (λ + ρ | γ) - (γ | γ))^{d(γ) P(η - γ)}` for all `λ`, where
`d(γ) = kkMult η γ` is the number of pairs `(x, n)`, `n ≥ 1`, with `n α_x = γ`. -/
theorem exists_shapovalovDet_eq_prod_kkIdx [IsAlgClosed K] (η : ι → ℤ) :
    ∃ c : K, c ≠ 0 ∧ ∀ Λ : Dual K H, shapovalovDet P (P.rootOf η) Λ =
      c * ∏ k ∈ kkIdx η, (2 * P.dualBilinForm S (Λ + P.rho) (P.rootOf k) -
        P.dualBilinForm S (P.rootOf k) (P.rootOf k)) ^
          (kkMult P η k * kostantPartition P (P.rootOf η - P.rootOf k)) := by
  classical
  choose F hF0 hF using fun β : ι → ℤ ↦ exists_poly_shapovalovDet P S (P.rootOf β)
  have hfac (β : ι → ℤ) (hβ : β ≤ η) := exists_eq_C_mul_prod_kkPoly P S hA hβ (hF β) (hF0 β)
  choose! c hc e hFe using hfac
  have hvec (k : ι → ℤ) (hk : k ∈ kkIdx η) : kkVec P S (P.rootOf k) ≠ 0 :=
    kkVec_ne_zero P S (P.rootOf_ne_zero (mem_kkIdx.mp hk).2.2)
  obtain ⟨u, hu, hprod⟩ := exists_prod_pow_eq_C_mul_prod_pow (kkIdx η)
    (a := fun k ↦ kkVec P S (P.rootOf k)) (fun k ↦ kkConst P S (P.rootOf k)) hvec (e η)
    (fun k ↦ kkMult P η k * kostantPartition P (P.rootOf η - P.rootOf k)) (fun k₀ hk₀ ↦ by
      obtain ⟨hk₀0, hk₀η, hk₀ne⟩ := mem_kkIdx.mp hk₀
      by_cases hiso : P.dualBilinForm S (P.rootOf k₀) (P.rootOf k₀) = 0
      · -- isotropic: the hyperplanes on the line `K γ₀` coincide
        have hfilt : (kkIdx η).filter (fun k ↦ AffProportional (kkVec P S (P.rootOf k))
            (kkConst P S (P.rootOf k)) (kkVec P S (P.rootOf k₀)) (kkConst P S (P.rootOf k₀))) =
            (kkIdx η).filter (fun k ↦ ∃ u : K, P.rootOf k = u • P.rootOf k₀) := by
          refine Finset.filter_congr fun k _ ↦ ⟨fun h ↦ ?_, fun ⟨u, hu⟩ ↦
            affProportional_kkPoly_of_isotropic P S hiso hu⟩
          obtain ⟨u, hu, -⟩ := (affProportional_kkVec_iff P S _ _ _ _).mp h
          exact ⟨u, hu⟩
        rw [hfilt]
        exact sum_exponent_parallel_eq P S le_rfl (hF η) (hc η le_rfl) (hFe η le_rfl)
          (P.rootOf_ne_zero hk₀ne)
      · -- non-isotropic: the hyperplane of `γ₀` occurs only once
        have hfilt : (kkIdx η).filter (fun k ↦ AffProportional (kkVec P S (P.rootOf k))
            (kkConst P S (P.rootOf k)) (kkVec P S (P.rootOf k₀)) (kkConst P S (P.rootOf k₀))) =
            {k₀} := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_singleton]
          refine ⟨fun ⟨hk, h⟩ ↦ P.rootOf_injective (eq_of_affProportional_kkPoly P S
            (P.rootOf_ne_zero (mem_kkIdx.mp hk).2.2) hiso h), fun h ↦ ?_⟩
          subst h
          exact ⟨hk₀, AffProportional.refl _ _⟩
        rw [hfilt, Finset.sum_singleton, Finset.sum_singleton,
          exponent_eq_mul_of_isotropic_ne_zero P S hA le_rfl hk₀ hiso (hF η) (hF k₀)
            (hc η le_rfl) (hc k₀ hk₀η) (hFe η le_rfl) (hFe k₀ hk₀η),
          exponent_self_eq_kkMult P S hA F hF c hc e hFe hk₀ hiso])
  refine ⟨c η * u, mul_ne_zero (hc η le_rfl) hu, fun Λ ↦ ?_⟩
  rw [← congrFun (hF η) Λ, hFe η le_rfl]
  simp only [kkPoly]
  rw [hprod, map_mul, map_mul, map_prod]
  simp only [Pi.mul_apply, Finset.prod_apply, evalPoly_C, map_pow, Pi.pow_apply,
    evalPoly_affPoly, apply_kkVec_add_kkConst]
  ring

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
