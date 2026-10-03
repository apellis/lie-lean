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
`λ`; `VermaModule.shapovalovDet`). The **Kac–Kazhdan determinant formula** ([KK]; see
[Kum] Thm. 2.3.4) states that, up to a nonzero constant,

`D_β(λ) = ∏_{α ∈ Δ₊} ∏_{n ≥ 1} ((λ + ρ | α) - n (α | α)/2)^{mult α · P(β - n α)}`,

where `P` is Kostant's partition function. Here the product runs over the index set `x` of a
basis of `𝔫₋` consisting of root vectors, in which each positive root `α` occurs `mult α` times
(`VermaModule.shapovalovDet_eq`).

As a corollary we obtain the **Kac–Kazhdan criterion**: `M(λ)` has a proper submodule meeting
`M(λ)_{λ-β}` (equivalently, the Shapovalov form is degenerate on `M(λ)_{λ-β}`) iff
`2 (λ + ρ | α) = n (α | α)` for some positive root `α` and `n ≥ 1` with `n α ≤ β`
(`VermaModule.maxSubmodule_inf_weightSpace_ne_bot_iff`; this uses `P(γ) ≠ 0 ↔ γ ∈ Q₊`,
`VermaModule.kostantPartition_ne_zero_iff`).

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

This is the argument of [KK], as presented in [Kum] Thm. 2.3.4 (proof), in the form given by
Jantzen for finite-dimensional `𝔤` (via the Jantzen filtration and a comparison of leading terms);
we reconstructed the details ourselves. We work over an algebraically closed field (Kac and Kazhdan
work over `ℂ`); this is used only to see that the zeros of `D_β` lying on finitely many hyperplanes
forces `D_β` to be a product of their equations.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.shapovalovDet_eq`: **the Kac–Kazhdan
  determinant formula**; also in the forms
  `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_shapovalovDet_eq_prod_kkPairs` (finite
  product over pairs `(x, n)`) and
  `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_shapovalovDet_eq_prod_kkIdx` (grouped by
  `γ = n α`).
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.maxSubmodule_inf_weightSpace_ne_bot_iff`:
  **the Kac–Kazhdan criterion**.

## References

* [KK] V. G. Kac, D. A. Kazhdan, *Structure of representations with highest weight of
  infinite-dimensional Lie algebras*, Adv. Math. 34 (1979), 97–108.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, Prop. 2.3.2, Thm. 2.3.4.
* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, §5.8 (Shapovalov's formula, finite type).
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
/-- **The Kac–Kazhdan determinant formula**, grouped by weights ([KK]; cf. [Kum]
Thm. 2.3.4). Over an algebraically closed field of characteristic zero, for `η ∈ Q` there is `c ≠ 0`
with `D_η(λ) = c ∏_{0 < γ ≤ η} (2 (λ + ρ | γ) - (γ | γ))^{d(γ) P(η - γ)}` for all `λ`, where
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

/-! ### The formula as a product over positive roots -/

/-- The index of the simple root vector `f_i` in the root vector basis of `𝔫₋`. -/
def simpleIdx (i : ι) : NegRootIndex P :=
  ⟨⟨P.root i, (Pi.single i (1 : ℤ) : ι → ℤ), ⟨Pi.single_nonneg.mpr zero_le_one,
    fun h ↦ (one_ne_zero : (1 : ℤ) ≠ 0) (by simpa using congrFun h i)⟩, P.rootOf_single i⟩,
    ⟨0, by simp [finrank_rootSpace_neg_root]⟩⟩

omit [FiniteDimensional K H] in
@[simp] lemma simpleIdx_root (i : ι) : (simpleIdx P i).root = P.root i := rfl

omit [FiniteDimensional K H] in
/-- `P(γ) ≠ 0` iff `γ ∈ Q₊`. -/
theorem kostantPartition_ne_zero_iff {γ : Dual K H} :
    kostantPartition P γ ≠ 0 ↔ ∃ m : ι → ℤ, 0 ≤ m ∧ γ = P.rootOf m := by
  refine ⟨exists_rootOf_of_kostantPartition_ne_zero P, ?_⟩
  rintro ⟨m, hm, rfl⟩
  set s : NegRootIndex P →₀ ℕ := ∑ i, Finsupp.single (simpleIdx P i) (m i).toNat
  have hs : negRootWt P s = P.rootOf m := by
    rw [show negRootWt P s = AddMonoidHom.mk' (negRootWt P) (negRootWt_add P) s from rfl,
      map_sum, rootOf_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [AddMonoidHom.mk'_apply, negRootWt_single, simpleIdx_root, ← Nat.cast_smul_eq_nsmul K]
    congr 1
    exact_mod_cast Int.toNat_of_nonneg (hm i)
  rw [kostantPartition_eq_card]
  exact Finset.card_ne_zero.mpr ⟨s, (mem_partitions P).mpr hs⟩

include hA in
/-- **The Kac–Kazhdan determinant formula** as a finite product over pairs `(x, n)`, `n ≥ 1`,
with `n α_x ≤ η`: for some `c ≠ 0`,
`D_η(λ) = c ∏_{(x, n)} ((λ + ρ | α_x) - n (α_x | α_x)/2)^{P(η - n α_x)}`. -/
theorem exists_shapovalovDet_eq_prod_kkPairs [IsAlgClosed K] (η : ι → ℤ) :
    ∃ c : K, c ≠ 0 ∧ ∀ Λ : Dual K H, shapovalovDet P (P.rootOf η) Λ =
      c * ∏ z ∈ kkPairs P η, (P.dualBilinForm S (Λ + P.rho) z.1.root -
        ((z.2 : K) + 1) / 2 * P.dualBilinForm S z.1.root z.1.root) ^
          kostantPartition P (P.rootOf η - (z.2 + 1) • z.1.root) := by
  classical
  obtain ⟨c, hc, h⟩ := exists_shapovalovDet_eq_prod_kkIdx P S hA η
  set Z := kkPairs P η
  refine ⟨c * ∏ z ∈ Z, (2 * ((z.2 : K) + 1)) ^
      kostantPartition P (P.rootOf η - (z.2 + 1) • z.1.root),
    mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun z _ ↦
      pow_ne_zero _ (mul_ne_zero two_ne_zero (Nat.cast_add_one_ne_zero _))), fun Λ ↦ ?_⟩
  rw [h Λ, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_fiberwise_of_maps_to (g := kkPairCoeff P) (t := kkIdx η)
    fun z hz ↦ kkPairCoeff_mem P hz]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [mul_comm (kkMult P η k), pow_mul, kkMult, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun z hz ↦ ?_
  obtain ⟨-, hzk⟩ := Finset.mem_filter.mp hz
  have hroot : P.rootOf k = ((z.2 : K) + 1) • z.1.root := by
    rw [← hzk, rootOf_kkPairCoeff, ← Nat.cast_smul_eq_nsmul K]
    push_cast
    rfl
  rw [← mul_pow, ← rootOf_kkPairCoeff P z, hzk]
  congr 1
  rw [hroot]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp

include hA in
/-- **The Kac–Kazhdan determinant formula** ([KK]; [Kum] Thm. 2.3.4). Let `A` be
a symmetrizable generalized Cartan matrix and `K` algebraically closed of characteristic zero.
For every `β ∈ 𝔥*` there is `c ≠ 0` such that for all `λ ∈ 𝔥*` the determinant of the Shapovalov
form on `M(λ)_{λ-β}` with respect to the PBW basis is

`D_β(λ) = c ∏_x ∏_{n ≥ 1} ((λ + ρ | α_x) - n (α_x | α_x)/2)^{P(β - n α_x)}`,

where `x` runs over a basis of `𝔫₋` of root vectors (so that each positive root `α` occurs
`mult α` times, and this is `c ∏_{α > 0} ∏_{n ≥ 1} ((λ + ρ | α) - n (α | α)/2)^{mult α ·
P(β - n α)}`) and `P` is Kostant's partition function. All but finitely many factors are `1`. -/
theorem shapovalovDet_eq [IsAlgClosed K] (β : Dual K H) :
    ∃ c : K, c ≠ 0 ∧ ∀ Λ : Dual K H, shapovalovDet P β Λ =
      c * ∏ᶠ (x : NegRootIndex P) (n : ℕ), (P.dualBilinForm S (Λ + P.rho) x.root -
        ((n : K) + 1) / 2 * P.dualBilinForm S x.root x.root) ^
          kostantPartition P (β - (n + 1) • x.root) := by
  classical
  by_cases hβ : ∃ η, β = P.rootOf η
  · obtain ⟨η, rfl⟩ := hβ
    obtain ⟨c, hc, h⟩ := exists_shapovalovDet_eq_prod_kkPairs P S hA η
    refine ⟨c, hc, fun Λ ↦ ?_⟩
    rw [h Λ]
    congr 1
    set f : NegRootIndex P × ℕ → K := fun z ↦ (P.dualBilinForm S (Λ + P.rho) z.1.root -
      ((z.2 : K) + 1) / 2 * P.dualBilinForm S z.1.root z.1.root) ^
        kostantPartition P (P.rootOf η - (z.2 + 1) • z.1.root)
    have hsupp : Function.mulSupport f ⊆ ↑(kkPairs P η) := fun z hz ↦ by
      by_contra hzZ
      apply hz
      have h0 : kostantPartition P (P.rootOf η - (z.2 + 1) • z.1.root) = 0 := by
        by_contra hne
        exact hzZ (mem_kkPairs_of_kostantPartition_ne_zero P le_rfl hne)
      simp only [f, h0, pow_zero]
    rw [← finprod_eq_prod_of_mulSupport_subset f hsupp,
      finprod_curry f ((kkPairs P η).finite_toSet.subset hsupp)]
  · refine ⟨1, one_ne_zero, fun Λ ↦ ?_⟩
    have hempty : partitions P β = ∅ := Finset.eq_empty_of_forall_notMem fun s hs ↦ by
      obtain ⟨m, -, hm⟩ := exists_negRootWt_eq_rootOf P s
      exact hβ ⟨m, ((mem_partitions P).mp hs).symm.trans hm⟩
    have : IsEmpty (partitions P β) := Finset.isEmpty_coe_sort.mpr hempty
    have hP (x : NegRootIndex P) (n : ℕ) : kostantPartition P (β - (n + 1) • x.root) = 0 := by
      by_contra hne
      obtain ⟨m, -, hm⟩ := exists_rootOf_of_kostantPartition_ne_zero P hne
      refine hβ ⟨m + (n + 1) • x.coeff, ?_⟩
      rw [map_add, map_nsmul, NegRootIndex.rootOf_coeff, ← hm, sub_add_cancel]
    rw [shapovalovDet, Matrix.det_isEmpty, one_mul]
    simp only [hP, pow_zero, finprod_one]

include hA in
/-- **The Kac–Kazhdan criterion** ([KK]; via [Kum] Thm. 2.3.4 and Prop. 2.3.2). Let `A` be a
symmetrizable generalized Cartan matrix and `K` algebraically closed of characteristic zero. The
maximal proper submodule `M'(λ)` of `M(λ)` has a nonzero vector of weight `λ - η` (equivalently, the
Shapovalov form on `M(λ)_{λ-η}` is degenerate) iff `2 (λ + ρ | α) = n (α | α)` for some positive
root `α` and `n ≥ 1` with `n α ≤ η`. Here `α = α_x` for an index `x` of the root vector basis of
`𝔫₋`, and `x.coeff` are the coordinates of `α_x` in the basis of simple roots. -/
theorem maxSubmodule_inf_weightSpace_ne_bot_iff [IsAlgClosed K] (Λ : Dual K H) (η : ι → ℤ) :
    (maxSubmodule P Λ).toSubmodule ⊓ weightSpace P Λ (Λ - P.rootOf η) ≠ ⊥ ↔
      ∃ x : NegRootIndex P, ∃ n : ℕ, (n + 1) • x.coeff ≤ η ∧
        2 * P.dualBilinForm S (Λ + P.rho) x.root =
          ((n : K) + 1) * P.dualBilinForm S x.root x.root := by
  classical
  rw [Ne, ← det_toMatrix_weightSpaceForm_ne_zero_iff P Λ _ (pbwWeightBasis P Λ (P.rootOf η)),
    not_not]
  change shapovalovDet P (P.rootOf η) Λ = 0 ↔ _
  obtain ⟨c, hc, h⟩ := exists_shapovalovDet_eq_prod_kkPairs P S hA η
  rw [h Λ, mul_eq_zero, or_iff_right hc, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨z, hz, h0⟩
    obtain ⟨h1, -⟩ := pow_eq_zero_iff'.mp h0
    exact ⟨z.1, z.2, (mem_kkPairs P).mp hz, by linear_combination 2 * h1⟩
  · rintro ⟨x, n, hle, heq⟩
    refine ⟨(x, n), (mem_kkPairs P).mpr hle,
      pow_eq_zero_iff'.mpr ⟨by linear_combination heq / 2, ?_⟩⟩
    rw [kostantPartition_ne_zero_iff]
    refine ⟨η - (n + 1) • x.coeff, sub_nonneg.mpr hle, ?_⟩
    rw [map_sub, map_nsmul, NegRootIndex.rootOf_coeff]

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
