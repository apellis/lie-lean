/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Determinant
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Factorization
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Generic

/-!
# The exponents in the Kac–Kazhdan determinant formula

Let `A` be a symmetrizable generalized Cartan matrix and `D_β(λ)` the Shapovalov determinant on
`M(λ)_{λ-β}` in the PBW basis (`VermaModule.shapovalovDet`). For `γ ∈ Q₊ \ {0}` let
`ψ_γ(λ) = 2 (λ + ρ | γ) - (γ | γ)` (`kkPoly`), and fix `η ∈ Q₊`. This file establishes the
facts about the exponents of the `ψ_γ` in `D_β` (`β ≤ η`) from which the determinant formula is
assembled in `KacKazhdan/Formula.lean`:

* **Factorization** (`VermaModule.exists_eq_C_mul_prod_kkPoly`): over an algebraically
  closed field, `D_β = c ∏_{0 < γ ≤ η} ψ_γ^{e_β(γ)}` for some `c ≠ 0` and exponents `e_β(γ)`. The
  zeros of `D_β` lie on the hyperplanes `ψ_γ = 0`
  (`VermaModule.det_toMatrix_weightSpaceForm_ne_zero_of_forall`, via the Casimir operator), and a
  polynomial with this property is a product of their equations
  (`Module.Dual.exists_eq_C_mul_prod_affPoly_pow`).
* **Non-isotropic hyperplanes** (`VermaModule.exponent_eq_mul_of_isotropic_ne_zero`): if
  `(γ | γ) ≠ 0`, then `e_β(γ) = e_γ(γ) P(β - γ)`, by the Jantzen filtration at a generic point of
  `ψ_γ = 0` (`VermaModule.natTrailingDegree_eq_mul_of_generic`).
* **Directions** (`VermaModule.sum_exponent_parallel_eq`): comparing the leading term
  `c ∏_x (λ | α_x)^{∑_{n ≥ 1} P(β - n α_x)}` (`VermaModule.hasTop_det_pbwWeightBasis_kkExponent`)
  with the leading term `c ∏_γ (2 (λ | γ))^{e_β(γ)}` of the factorization, for every line `ℓ`
  through `0`: `∑_{γ ∈ ℓ} e_β(γ) = ∑_{α_x ∈ ℓ} ∑_{n ≥ 1} P(β - n α_x)
  = ∑_{γ ∈ ℓ} d(γ) P(β - γ)`, where `d(γ)` is the number of pairs `(x, n)` with `n α_x = γ`
  (`kkMult`), i.e. `d(γ) = ∑_{n ≥ 1, γ/n ∈ Δ₊} mult(γ/n)`.

These arguments were reconstructed by us (cf. [KK] §3 (check), [Kac] §9 (check)).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.kkPairs`, `Matrix.Realization.KacMoodyAlgebra.kkMult`: the
  pairs `(x, n)` with `n α_x ≤ η`, and their number on a given `γ`.
* `Matrix.Realization.KacMoodyAlgebra.kkPoly`: `ψ_γ(λ) = 2 (λ + ρ | γ) - (γ | γ)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_eq_C_mul_prod_kkPoly`,
  `Matrix.Realization.KacMoodyAlgebra.VermaModule.exponent_eq_mul_of_isotropic_ne_zero`,
  `Matrix.Realization.KacMoodyAlgebra.VermaModule.sum_exponent_parallel_eq`: the three facts above.

## References

* [KK] V. G. Kac, D. A. Kazhdan, *Structure of representations with highest weight of
  infinite-dimensional Lie algebras*, Adv. Math. **34** (1979), 97–108.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9 (check).
-/

open Module LieModule Module.Dual Polynomial

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-! ### Root coefficients of indices -/

/-- The coefficients `k ∈ Q₊ \ {0}` of the positive root `α_x = ∑ kᵢ αᵢ` of an index `x`. -/
def NegRootIndex.coeff {P : Realization A K H} (x : NegRootIndex P) : ι → ℤ := x.1.2.choose

lemma NegRootIndex.coeff_mem {P : Realization A K H} (x : NegRootIndex P) :
    x.coeff ∈ posCone ι :=
  x.1.2.choose_spec.1

lemma NegRootIndex.rootOf_coeff {P : Realization A K H} (x : NegRootIndex P) :
    P.rootOf x.coeff = x.root :=
  x.1.2.choose_spec.2

variable [CharZero K]

lemma NegRootIndex.root_ne_zero {P : Realization A K H} (x : NegRootIndex P) : x.root ≠ 0 := by
  rw [← x.rootOf_coeff]
  exact P.rootOf_ne_zero x.coeff_mem.2

/-- A nonzero Kostant partition function forces the argument to lie in `Q₊`. -/
lemma exists_rootOf_of_kostantPartition_ne_zero {γ : Dual K H} (h : kostantPartition P γ ≠ 0) :
    ∃ m : ι → ℤ, 0 ≤ m ∧ γ = P.rootOf m := by
  rw [kostantPartition_eq_card] at h
  obtain ⟨s, hs⟩ := Finset.card_ne_zero.mp h
  obtain ⟨m, hm, hms⟩ := exists_negRootWt_eq_rootOf P s
  exact ⟨m, hm, ((mem_partitions P).mp hs).symm.trans hms⟩

lemma kostantPartition_zero : kostantPartition P 0 = 1 := by
  rw [← VermaModule.finrank_weightSpace_sub P 0 0, sub_zero]
  exact VermaModule.finrank_weightSpace_self P 0

/-! ### Finite index sets -/

/-- The finite set `Γ_η = {γ ∈ Q₊ \ {0} | γ ≤ η}`. -/
def kkIdx (η : ι → ℤ) : Finset (ι → ℤ) :=
  (Fintype.piFinset fun i ↦ Finset.Icc 0 (η i)).filter (· ≠ 0)

@[simp] lemma mem_kkIdx {η k : ι → ℤ} : k ∈ kkIdx η ↔ 0 ≤ k ∧ k ≤ η ∧ k ≠ 0 := by
  classical
  simp only [kkIdx, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  exact ⟨fun ⟨h, h0⟩ ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2, h0⟩,
    fun ⟨h1, h2, h0⟩ ↦ ⟨fun i ↦ ⟨h1 i, h2 i⟩, h0⟩⟩

omit [DecidableEq ι] in
lemma sum_pos_of_mem_posCone {k : ι → ℤ} (hk : k ∈ posCone ι) : 0 < ∑ i, k i := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk.2
  exact Finset.sum_pos' (fun j _ ↦ hk.1 j) ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hk.1 i)
    (Ne.symm hi)⟩

/-- A finite set of indices containing every `x` with `α_x ≤ η`. -/
def kkRoots (η : ι → ℤ) : Finset (NegRootIndex P) :=
  (kkIdx η).biUnion fun k ↦ (partitions P (P.rootOf k)).biUnion Finsupp.support

lemma mem_kkRoots {η : ι → ℤ} {x : NegRootIndex P} (hx : x.coeff ≤ η) : x ∈ kkRoots P η := by
  classical
  simp only [kkRoots, Finset.mem_biUnion]
  refine ⟨x.coeff, mem_kkIdx.mpr ⟨x.coeff_mem.1, hx, x.coeff_mem.2⟩, Finsupp.single x 1, ?_, ?_⟩
  · rw [mem_partitions, negRootWt_single, one_smul, NegRootIndex.rootOf_coeff]
  · simp

/-- The finite set of pairs `(x, n)` with `(n + 1) α_x ≤ η`. -/
def kkPairs (η : ι → ℤ) : Finset (NegRootIndex P × ℕ) :=
  (kkRoots P η ×ˢ Finset.range (∑ i, η i).toNat).filter fun z ↦ (z.2 + 1) • z.1.coeff ≤ η

lemma mem_kkPairs {η : ι → ℤ} {z : NegRootIndex P × ℕ} :
    z ∈ kkPairs P η ↔ (z.2 + 1) • z.1.coeff ≤ η := by
  refine ⟨fun h ↦ (Finset.mem_filter.mp h).2, fun h ↦ Finset.mem_filter.mpr ⟨?_, h⟩⟩
  have hpos := sum_pos_of_mem_posCone z.1.coeff_mem
  have hle : (z.2 + 1) • z.1.coeff ≤ η := h
  have h1 : z.1.coeff ≤ η := le_trans (le_smul_of_one_le_left z.1.coeff_mem.1 (by omega)) hle
  have hsum : ((z.2 + 1 : ℕ) : ℤ) * ∑ i, z.1.coeff i ≤ ∑ i, η i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ by simpa [nsmul_eq_mul] using hle i
  refine Finset.mem_product.mpr ⟨mem_kkRoots P h1, Finset.mem_range.mpr ?_⟩
  have : (z.2 : ℤ) + 1 ≤ ∑ i, η i := by
    push_cast at hsum
    nlinarith
  omega

/-- The index `k` of `(n + 1) α_x = ∑ kᵢ αᵢ`. -/
def kkPairCoeff (z : NegRootIndex P × ℕ) : ι → ℤ := (z.2 + 1) • z.1.coeff

omit [CharZero K] in
lemma rootOf_kkPairCoeff (z : NegRootIndex P × ℕ) :
    P.rootOf (kkPairCoeff P z) = (z.2 + 1) • z.1.root := by
  rw [kkPairCoeff, map_nsmul, NegRootIndex.rootOf_coeff]

lemma kkPairCoeff_mem {η : ι → ℤ} {z : NegRootIndex P × ℕ} (hz : z ∈ kkPairs P η) :
    kkPairCoeff P z ∈ kkIdx η := by
  refine mem_kkIdx.mpr ⟨nsmul_nonneg z.1.coeff_mem.1 _, (mem_kkPairs P).mp hz, ?_⟩
  intro h
  refine z.1.coeff_mem.2 (funext fun i ↦ ?_)
  have := congrFun h i
  simp only [kkPairCoeff, Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at this
  rcases mul_eq_zero.mp this with h' | h'
  · push_cast at h'
    omega
  · exact h'

/-- `d(k)`: the number of pairs `(x, n)` with `(n + 1) α_x = ∑ kᵢ αᵢ`. For a root `α` of
multiplicity `mult α` this counts `∑_{n ≥ 1, γ = n α} mult α`. -/
def kkMult (η k : ι → ℤ) : ℕ := ((kkPairs P η).filter fun z ↦ kkPairCoeff P z = k).card

/-- If `P(β - (n + 1) α_x) ≠ 0` with `β ≤ η`, then `(x, n) ∈ kkPairs η`. -/
lemma mem_kkPairs_of_kostantPartition_ne_zero {η β : ι → ℤ} (hβ : β ≤ η)
    {z : NegRootIndex P × ℕ} (hz : kostantPartition P (P.rootOf β - (z.2 + 1) • z.1.root) ≠ 0) :
    z ∈ kkPairs P η := by
  obtain ⟨m, hm, hβm⟩ := exists_rootOf_of_kostantPartition_ne_zero P hz
  rw [← rootOf_kkPairCoeff, sub_eq_iff_eq_add, ← map_add] at hβm
  rw [mem_kkPairs]
  have := P.rootOf_injective hβm
  exact le_trans (by rw [this]; exact le_add_of_nonneg_left hm) hβ

/-- `∑_{n ≥ 1} P(β - n α_x)` as a finite sum. -/
lemma kkExponent_eq_sum {η β : ι → ℤ} (hβ : β ≤ η) (x : NegRootIndex P) :
    VermaModule.kkExponent P (P.rootOf β) x = ∑ n ∈ Finset.range (∑ i, η i).toNat,
      if (x, n) ∈ kkPairs P η then kostantPartition P (P.rootOf β - (n + 1) • x.root) else 0 := by
  classical
  rw [VermaModule.kkExponent, finsum_eq_sum_of_support_subset _ (s := Finset.range (∑ i, η i).toNat)
    fun n hn ↦ ?_]
  · refine Finset.sum_congr rfl fun n _ ↦ ?_
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (mem_kkPairs_of_kostantPartition_ne_zero P hβ (z := (x, n)) hne)
  · have := mem_kkPairs_of_kostantPartition_ne_zero P hβ (z := (x, n)) hn
    exact Finset.mem_coe.mpr (Finset.mem_product.mp (Finset.mem_filter.mp this).1).2

lemma kkExponent_eq_zero {η β : ι → ℤ} (hβ : β ≤ η) {x : NegRootIndex P}
    (hx : x ∉ kkRoots P η) : VermaModule.kkExponent P (P.rootOf β) x = 0 := by
  rw [kkExponent_eq_sum P hβ]
  refine Finset.sum_eq_zero fun n _ ↦ ?_
  split_ifs with h
  · exact absurd (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1 hx
  · rfl

open Classical in
/-- **Regrouping the exponents along a line.** For `β ≤ η` and `γ₀ ∈ 𝔥*`,
`∑_{α_x ∈ K γ₀} ∑_{n ≥ 1} P(β - n α_x) = ∑_{γ ∈ Γ_η ∩ K γ₀} d(γ) P(β - γ)`. -/
theorem sum_kkExponent_parallel_eq {η β : ι → ℤ} (hβ : β ≤ η) (γ₀ : Dual K H) :
    ∑ x ∈ (kkRoots P η).filter (fun x ↦ ∃ u : K, x.root = u • γ₀),
        VermaModule.kkExponent P (P.rootOf β) x =
      ∑ k ∈ (kkIdx η).filter (fun k ↦ ∃ u : K, P.rootOf k = u • γ₀),
        kkMult P η k * kostantPartition P (P.rootOf β - P.rootOf k) := by
  classical
  set N := (∑ i, η i).toNat
  set par : NegRootIndex P → Prop := fun x ↦ ∃ u : K, x.root = u • γ₀
  have hpar (z : NegRootIndex P × ℕ) :
      (∃ u : K, P.rootOf (kkPairCoeff P z) = u • γ₀) ↔ par z.1 := by
    rw [rootOf_kkPairCoeff]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨((z.2 : K) + 1)⁻¹ * u, ?_⟩
      rw [mul_smul, ← hu, ← Nat.cast_smul_eq_nsmul K, smul_smul, Nat.cast_add, Nat.cast_one,
        inv_mul_cancel₀ (Nat.cast_add_one_ne_zero z.2), one_smul]
    · rintro ⟨u, hu⟩
      refine ⟨((z.2 : K) + 1) * u, ?_⟩
      rw [hu, ← Nat.cast_smul_eq_nsmul K, smul_smul, Nat.cast_add, Nat.cast_one]
  -- expand the left side as a sum over pairs
  have hL : ∑ x ∈ (kkRoots P η).filter par, VermaModule.kkExponent P (P.rootOf β) x =
      ∑ z ∈ (kkPairs P η).filter (fun z ↦ par z.1),
        kostantPartition P (P.rootOf β - (z.2 + 1) • z.1.root) := by
    simp_rw [kkExponent_eq_sum P hβ]
    rw [← Finset.sum_product', ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun z _ ↦ rfl
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.eta]
    constructor
    · rintro ⟨⟨⟨-, hp⟩, -⟩, hz⟩
      exact ⟨hz, hp⟩
    · rintro ⟨hz, hp⟩
      have := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
      exact ⟨⟨⟨this.1, hp⟩, this.2⟩, hz⟩
  rw [hL, ← Finset.sum_fiberwise_of_maps_to (g := kkPairCoeff P)
    (t := (kkIdx η).filter fun k ↦ ∃ u : K, P.rootOf k = u • γ₀) fun z hz ↦ by
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨kkPairCoeff_mem P hz.1, (hpar z).mpr hz.2⟩]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [kkMult, ← smul_eq_mul, ← Finset.sum_const]
  rw [Finset.filter_filter]
  refine Finset.sum_congr ?_ fun z hz ↦ ?_
  · ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨h1, (hpar z).mp ?_, h3⟩
      rw [h3]
      exact (Finset.mem_filter.mp hk).2
  · rw [Finset.mem_filter] at hz
    rw [← rootOf_kkPairCoeff, hz.2]

/-! ### The Kac–Kazhdan hyperplanes -/

section Hyperplanes

omit [DecidableEq ι]

variable [FiniteDimensional K H] (S : A.Symmetrization)

/-- `ν⁻¹(2 γ)`, so that `λ(kkVec γ) = 2 (λ | γ)`. -/
def kkVec : Dual K H →ₗ[K] H := (2 : K) • ((P.toDual S).symm : Dual K H →ₗ[K] H)

lemma apply_kkVec (Λ γ : Dual K H) : Λ (kkVec P S γ) = 2 * P.dualBilinForm S Λ γ := by
  simp [kkVec, dualBilinForm_apply_eq]

lemma kkVec_injective : Function.Injective (kkVec P S) := by
  intro γ γ' h
  simp only [kkVec, LinearMap.smul_apply, LinearEquiv.coe_coe] at h
  exact (P.toDual S).symm.injective (smul_right_injective H two_ne_zero h)

lemma kkVec_ne_zero {γ : Dual K H} (hγ : γ ≠ 0) : kkVec P S γ ≠ 0 := by
  rwa [Ne, ← map_zero (kkVec P S), (kkVec_injective P S).eq_iff]

/-- `2 (ρ | γ) - (γ | γ)`. -/
def kkConst (γ : Dual K H) : K := 2 * P.dualBilinForm S P.rho γ - P.dualBilinForm S γ γ

lemma apply_kkVec_add_kkConst (Λ γ : Dual K H) :
    Λ (kkVec P S γ) + kkConst P S γ =
      2 * P.dualBilinForm S (Λ + P.rho) γ - P.dualBilinForm S γ γ := by
  rw [apply_kkVec, kkConst, map_add, LinearMap.add_apply]
  ring

/-- The Kac–Kazhdan polynomial `ψ_γ(λ) = 2 (λ + ρ | γ) - (γ | γ)`. -/
def kkPoly (γ : Dual K H) : MvPolynomial (PolyIdx K H) K :=
  affPoly K H (kkVec P S γ) (kkConst P S γ)

@[simp] lemma evalPoly_kkPoly (γ Λ : Dual K H) :
    evalPoly K H (kkPoly P S γ) Λ =
      2 * P.dualBilinForm S (Λ + P.rho) γ - P.dualBilinForm S γ γ := by
  rw [kkPoly, evalPoly_affPoly, apply_kkVec_add_kkConst]

/-- The shifted polynomial `λ ↦ 2 (λ - γ₀ + ρ | γ) - (γ | γ)`. -/
def kkShiftPoly (γ₀ γ : Dual K H) : MvPolynomial (PolyIdx K H) K :=
  affPoly K H (kkVec P S γ) (kkConst P S γ - 2 * P.dualBilinForm S γ₀ γ)

@[simp] lemma evalPoly_kkShiftPoly (γ₀ γ Λ : Dual K H) :
    evalPoly K H (kkShiftPoly P S γ₀ γ) Λ =
      2 * P.dualBilinForm S (Λ - γ₀ + P.rho) γ - P.dualBilinForm S γ γ := by
  rw [kkShiftPoly, evalPoly_affPoly, add_sub, apply_kkVec_add_kkConst, sub_add_eq_add_sub,
    map_sub, LinearMap.sub_apply]
  ring

lemma affProportional_kkVec_iff (γ γ₀ : Dual K H) (c c₀ : K) :
    AffProportional (kkVec P S γ) c (kkVec P S γ₀) c₀ ↔ ∃ u : K, γ = u • γ₀ ∧ c = u * c₀ := by
  constructor
  · rintro ⟨u, hu, hc⟩
    exact ⟨u, kkVec_injective P S (by rw [hu, map_smul]), hc⟩
  · rintro ⟨u, rfl, hc⟩
    exact ⟨u, map_smul _ _ _, hc⟩

lemma kkConst_smul (u : K) (γ : Dual K H) :
    kkConst P S (u • γ) = u * (2 * P.dualBilinForm S P.rho γ) - u ^ 2 * P.dualBilinForm S γ γ := by
  simp only [kkConst, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- For non-isotropic `γ₀`, `ψ_γ` is proportional to `ψ_{γ₀}` only for `γ = γ₀`. -/
lemma eq_of_affProportional_kkPoly {γ γ₀ : Dual K H} (hγ : γ ≠ 0)
    (hiso : P.dualBilinForm S γ₀ γ₀ ≠ 0)
    (h : AffProportional (kkVec P S γ) (kkConst P S γ) (kkVec P S γ₀) (kkConst P S γ₀)) :
    γ = γ₀ := by
  obtain ⟨u, rfl, hc⟩ := (affProportional_kkVec_iff P S _ _ _ _).mp h
  have hu : u ≠ 0 := by rintro rfl; exact hγ (zero_smul _ _)
  rw [kkConst_smul, kkConst] at hc
  have : u * (u - 1) * P.dualBilinForm S γ₀ γ₀ = 0 := by linear_combination -hc
  rcases mul_eq_zero.mp this with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hu
    · rw [sub_eq_zero.mp h2, one_smul]
  · exact absurd h1 hiso

/-- For isotropic `γ₀`, `ψ_{u γ₀} = u ψ_{γ₀}`. -/
lemma affProportional_kkPoly_of_isotropic {γ γ₀ : Dual K H}
    (hiso : P.dualBilinForm S γ₀ γ₀ = 0) {u : K} (h : γ = u • γ₀) :
    AffProportional (kkVec P S γ) (kkConst P S γ) (kkVec P S γ₀) (kkConst P S γ₀) := by
  subst h
  refine (affProportional_kkVec_iff P S _ _ _ _).mpr ⟨u, rfl, ?_⟩
  rw [kkConst_smul, kkConst, hiso]
  ring

/-- The shifted polynomials `2 (λ - γ₀ + ρ | γ) - (γ | γ)` (`γ ∈ Q₊ \ {0}`) are not proportional
to `ψ_{γ₀}` for non-isotropic `γ₀ ∈ Q₊ \ {0}`. -/
lemma not_affProportional_kkShiftPoly {k k₀ : ι → ℤ} (hk : k ∈ posCone ι)
    (hk₀ : k₀ ∈ posCone ι) (hiso : P.dualBilinForm S (P.rootOf k₀) (P.rootOf k₀) ≠ 0) :
    ¬ AffProportional (kkVec P S (P.rootOf k))
      (kkConst P S (P.rootOf k) - 2 * P.dualBilinForm S (P.rootOf k₀) (P.rootOf k))
      (kkVec P S (P.rootOf k₀)) (kkConst P S (P.rootOf k₀)) := by
  intro h
  obtain ⟨u, hu, hc⟩ := (affProportional_kkVec_iff P S _ _ _ _).mp h
  rw [hu, kkConst_smul, kkConst, map_smul, smul_eq_mul] at hc
  have : u * (u + 1) * P.dualBilinForm S (P.rootOf k₀) (P.rootOf k₀) = 0 := by
    linear_combination -hc
  rcases mul_eq_zero.mp this with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · rw [h2, zero_smul] at hu
      exact P.rootOf_ne_zero hk.2 hu
    · have h0 : P.rootOf (k + k₀) = P.rootOf 0 := by
        rw [map_add, map_zero, hu]
        calc u • P.rootOf k₀ + P.rootOf k₀ = (u + 1) • P.rootOf k₀ := by rw [add_smul, one_smul]
          _ = 0 := by rw [h2, zero_smul]
      have hkk := P.rootOf_injective h0
      refine hk.2 (funext fun i ↦ ?_)
      have := congrFun hkk i
      have := hk.1 i
      have := hk₀.1 i
      simp only [Pi.add_apply, Pi.zero_apply] at *
      omega
  · exact hiso h1

end Hyperplanes

namespace VermaModule

variable [FiniteDimensional K H] (S : A.Symmetrization) (hA : A.IsGeneralizedCartan)

/-- The Shapovalov determinant `D_β(λ)`: the determinant of the Shapovalov form on `M(λ)_{λ-β}`
in the PBW basis. -/
abbrev shapovalovDet (β Λ : Dual K H) : K :=
  (LinearMap.BilinForm.toMatrix (pbwWeightBasis P Λ β) (weightSpaceForm P Λ (Λ - β))).det

include hA in
/-- **Factorization of the Shapovalov determinant** (over an algebraically closed field): for
`β ≤ η`, a polynomial `F` representing `D_β` is `c ∏_{0 < γ ≤ η} ψ_γ^{e(γ)}` with `c ≠ 0`. -/
theorem exists_eq_C_mul_prod_kkPoly [IsAlgClosed K] {η β : ι → ℤ} (hβ : β ≤ η)
    {F : MvPolynomial (PolyIdx K H) K} (hF : evalPoly K H F = shapovalovDet P (P.rootOf β))
    (hF0 : F ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∃ e : (ι → ℤ) → ℕ,
      F = MvPolynomial.C c * ∏ k ∈ kkIdx η, kkPoly P S (P.rootOf k) ^ e k := by
  refine exists_eq_C_mul_prod_affPoly_pow hF0 (kkIdx η) _ _
    (fun k hk ↦ kkVec_ne_zero P S (P.rootOf_ne_zero (mem_kkIdx.mp hk).2.2)) fun Λ hΛ ↦ ?_
  rw [hF] at hΛ
  by_contra! hne
  refine det_toMatrix_weightSpaceForm_ne_zero_of_forall P S hA (pbwWeightBasis P Λ (P.rootOf β))
    (fun γ hγ0 hγne hγβ heq ↦ hne γ (mem_kkIdx.mpr ⟨hγ0, hγβ.trans hβ, hγne⟩) ?_) hΛ
  rw [apply_kkVec_add_kkConst, heq, sub_self]

open Classical in
/-- **The exponents along a line through `0`.** If `F = c ∏_{0 < γ ≤ η} ψ_γ^{e(γ)}` represents
`D_β` (`β ≤ η`), then for every `γ₀ ≠ 0`,
`∑_{γ ∈ K γ₀} e(γ) = ∑_{γ ∈ K γ₀} d(γ) P(β - γ)`. This compares the leading terms of the two
descriptions of `D_β`. -/
theorem sum_exponent_parallel_eq {η β : ι → ℤ} (hβ : β ≤ η)
    {F : MvPolynomial (PolyIdx K H) K} (hF : evalPoly K H F = shapovalovDet P (P.rootOf β))
    {c : K} (hc : c ≠ 0) {e : (ι → ℤ) → ℕ}
    (hFe : F = MvPolynomial.C c * ∏ k ∈ kkIdx η, kkPoly P S (P.rootOf k) ^ e k)
    {γ₀ : Dual K H} (hγ₀ : γ₀ ≠ 0) :
    ∑ k ∈ (kkIdx η).filter (fun k ↦ ∃ u : K, P.rootOf k = u • γ₀), e k =
      ∑ k ∈ (kkIdx η).filter (fun k ↦ ∃ u : K, P.rootOf k = u • γ₀),
        kkMult P η k * kostantPartition P (P.rootOf β - P.rootOf k) := by
  classical
  rw [← sum_kkExponent_parallel_eq P hβ γ₀]
  obtain ⟨c', hc', htop⟩ := hasTop_det_pbwWeightBasis_kkExponent P S (P.rootOf β)
  -- the leading term from the Kostant partitions, as a finite product
  set X := kkRoots P η
  have hfin : ∏ᶠ x : NegRootIndex P, linPoly K H ((P.toDual S).symm x.root) ^
      kkExponent P (P.rootOf β) x = ∏ x ∈ X, linPoly K H ((P.toDual S).symm x.root) ^
      kkExponent P (P.rootOf β) x := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun x hx ↦ ?_
    by_contra hxX
    apply hx
    beta_reduce
    rw [kkExponent_eq_zero P hβ hxX, pow_zero]
  rw [hfin] at htop
  have hsum : ∑ᶠ x : NegRootIndex P, kkExponent P (P.rootOf β) x =
      ∑ x ∈ X, kkExponent P (P.rootOf β) x := by
    refine finsum_eq_sum_of_support_subset _ fun x hx ↦ ?_
    by_contra hxX
    exact hx (kkExponent_eq_zero P hβ hxX)
  rw [hsum] at htop
  have hroot (x : NegRootIndex P) : (P.toDual S).symm x.root ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]
    exact x.root_ne_zero
  have hvec (k : ι → ℤ) (hk : k ∈ kkIdx η) : kkVec P S (P.rootOf k) ≠ 0 :=
    kkVec_ne_zero P S (P.rootOf_ne_zero (mem_kkIdx.mp hk).2.2)
  -- the leading term from the factorization
  have hfac := hasTop_C_mul_prod_affPoly_pow (kkIdx η) (fun k ↦ kkVec P S (P.rootOf k))
    (fun k ↦ kkConst P S (P.rootOf k)) e c
  rw [show (MvPolynomial.C c * ∏ k ∈ kkIdx η, affPoly K H (kkVec P S (P.rootOf k))
    (kkConst P S (P.rootOf k)) ^ e k) = F from hFe.symm, hF] at hfac
  have hne1 : MvPolynomial.C c' * ∏ x ∈ X, linPoly K H ((P.toDual S).symm x.root) ^
      kkExponent P (P.rootOf β) x ≠ 0 :=
    mul_ne_zero (by rwa [Ne, MvPolynomial.C_eq_zero]) (Finset.prod_ne_zero_iff.mpr fun x _ ↦
      pow_ne_zero _ (linPoly_ne_zero (hroot x)))
  have hne2 : MvPolynomial.C c * ∏ k ∈ kkIdx η, linPoly K H (kkVec P S (P.rootOf k)) ^ e k ≠ 0 :=
    mul_ne_zero (by rwa [Ne, MvPolynomial.C_eq_zero]) (Finset.prod_ne_zero_iff.mpr fun k hk ↦
      pow_ne_zero _ (linPoly_ne_zero (hvec k hk)))
  obtain ⟨p₁, hp₁, hp₁e⟩ := htop.exists_totalDegree_eq hne1
  obtain ⟨p₂, hp₂, hp₂e⟩ := hfac.exists_totalDegree_eq hne2
  have hdeg : ∑ x ∈ X, kkExponent P (P.rootOf β) x = ∑ k ∈ kkIdx η, e k := by
    rw [← hp₁, ← hp₂, evalPoly_injective (hp₁e.trans hp₂e.symm)]
  rw [hdeg] at htop
  have heq := htop.unique hfac
  -- compare the multiplicities of the hyperplane `(λ | γ₀) = 0`
  simp only [← affPoly_zero] at heq
  have := sum_filter_eq_of_C_mul_prod_eq (fun x _ ↦ hroot x) (fun k hk ↦ hvec k hk) _ _ hc' hc
    heq (a₀ := (P.toDual S).symm γ₀) (by rwa [Ne, LinearEquiv.map_eq_zero_iff]) 0
  convert this.symm using 2
  · ext k
    simp only [Finset.mem_filter, affProportional_zero_iff]
    refine and_congr_right fun _ ↦ ⟨fun ⟨u, hu⟩ ↦ ⟨2 * u, ?_⟩, fun ⟨u, hu⟩ ↦ ⟨u / 2, ?_⟩⟩
    · rw [hu, map_smul]
      simp only [kkVec, LinearMap.smul_apply, LinearEquiv.coe_coe, smul_smul, mul_comm]
    · apply (P.toDual S).symm.injective
      have h2 : (2 : K) • (P.toDual S).symm (P.rootOf k) = u • (P.toDual S).symm γ₀ := by
        simpa [kkVec] using hu
      rw [map_smul, ← smul_right_inj (two_ne_zero (α := K)), h2, smul_smul]
      congr 1
      field_simp
  · ext x
    simp only [Finset.mem_filter, affProportional_zero_iff]
    refine and_congr_right fun _ ↦ ⟨fun ⟨u, hu⟩ ↦ ⟨u, by rw [hu, map_smul]⟩,
      fun ⟨u, hu⟩ ↦ ⟨u, (P.toDual S).symm.injective (by rw [hu, map_smul])⟩⟩

include hA in
/-- **The exponent of a non-isotropic hyperplane.** Let `γ₀ = ∑ k₀ᵢ αᵢ` with `0 < k₀ ≤ η` and
`(γ₀ | γ₀) ≠ 0`. If `D_β = c ∏_{0 < γ ≤ η} ψ_γ^{e(γ)}` and `D_{γ₀} = c₀ ∏ ψ_γ^{e₀(γ)}`
(`β ≤ η`), then `e(γ₀) = e₀(γ₀) P(β - γ₀)`. This uses the Jantzen filtration at a generic point
of the hyperplane `ψ_{γ₀} = 0` (`natTrailingDegree_eq_mul_of_generic`). -/
theorem exponent_eq_mul_of_isotropic_ne_zero {η β k₀ : ι → ℤ} (hβ : β ≤ η)
    (hk₀ : k₀ ∈ kkIdx η)
    (hiso : P.dualBilinForm S (P.rootOf k₀) (P.rootOf k₀) ≠ 0)
    {F F₀ : MvPolynomial (PolyIdx K H) K}
    (hF : evalPoly K H F = shapovalovDet P (P.rootOf β))
    (hF₀ : evalPoly K H F₀ = shapovalovDet P (P.rootOf k₀)) {c c₀ : K} (hc : c ≠ 0)
    (hc₀ : c₀ ≠ 0) {e e₀ : (ι → ℤ) → ℕ}
    (hFe : F = MvPolynomial.C c * ∏ k ∈ kkIdx η, kkPoly P S (P.rootOf k) ^ e k)
    (hF₀e : F₀ = MvPolynomial.C c₀ * ∏ k ∈ kkIdx η, kkPoly P S (P.rootOf k) ^ e₀ k) :
    e k₀ = e₀ k₀ * kostantPartition P (P.rootOf β - P.rootOf k₀) := by
  classical
  set γ₀ := P.rootOf k₀
  obtain ⟨hk₀0, hk₀η, hk₀ne⟩ := mem_kkIdx.mp hk₀
  have hvec (k : ι → ℤ) (hk : k ∈ kkIdx η) : kkVec P S (P.rootOf k) ≠ 0 :=
    kkVec_ne_zero P S (P.rootOf_ne_zero (mem_kkIdx.mp hk).2.2)
  -- a generic point `λ₀` of the hyperplane `ψ_{γ₀} = 0`
  obtain ⟨Λ₀, hΛ₀, hgenΛ⟩ := exists_forall_evalPoly_ne_zero_of_hyperplane (hvec k₀ hk₀)
    (kkConst P S γ₀) (((kkIdx η).erase k₀).disjSum (kkIdx η))
    (Sum.elim (fun k ↦ kkPoly P S (P.rootOf k)) fun k ↦ kkShiftPoly P S γ₀ (P.rootOf k)) (by
      rintro (k | k) hk
      · rw [Finset.inl_mem_disjSum, Finset.mem_erase] at hk
        refine exists_eval_ne_zero_of_not_dvd (hvec k₀ hk₀) _ fun hd ↦ hk.1 ?_
        have := eq_of_affProportional_kkPoly P S (P.rootOf_ne_zero (mem_kkIdx.mp hk.2).2.2) hiso
          (affProportional_of_affPoly_dvd (hvec k₀ hk₀) (hvec k hk.2) hd)
        exact P.rootOf_injective this
      · rw [Finset.inr_mem_disjSum] at hk
        obtain ⟨hk0, -, hkne⟩ := mem_kkIdx.mp hk
        exact exists_eval_ne_zero_of_not_dvd (hvec k₀ hk₀) _ fun hd ↦
          not_affProportional_kkShiftPoly P S ⟨hk0, hkne⟩ ⟨hk₀0, hk₀ne⟩ hiso
            (affProportional_of_affPoly_dvd (hvec k₀ hk₀) (hvec k hk) hd))
  obtain ⟨δ, hδ⟩ := exists_dual_apply_ne_zero (K := K) (hvec k₀ hk₀)
  -- at `λ₀`, only `ψ_{γ₀}` vanishes
  have hzero (k : ι → ℤ) (hk : k ∈ kkIdx η) :
      Λ₀ (kkVec P S (P.rootOf k)) + kkConst P S (P.rootOf k) = 0 ↔ k = k₀ := by
    refine ⟨fun h0 ↦ by_contra fun hne ↦ ?_, fun h ↦ h ▸ hΛ₀⟩
    have := hgenΛ (.inl k) (Finset.inl_mem_disjSum.mpr (Finset.mem_erase.mpr ⟨hne, hk⟩))
    simp only [Sum.elim_inl, kkPoly, evalPoly_affPoly] at this
    exact this h0
  have hδ' (k : ι → ℤ) (hk : k ∈ kkIdx η) :
      Λ₀ (kkVec P S (P.rootOf k)) + kkConst P S (P.rootOf k) = 0 →
        δ (kkVec P S (P.rootOf k)) ≠ 0 := fun h0 ↦ by
    rw [(hzero k hk).mp h0]
    exact hδ
  have hord {G : MvPolynomial (PolyIdx K H) K} {c' : K} (hc' : c' ≠ 0) {e' : (ι → ℤ) → ℕ}
      (hG : G = MvPolynomial.C c' * ∏ k ∈ kkIdx η, kkPoly P S (P.rootOf k) ^ e' k) :
      linePoly K H Λ₀ δ G ≠ 0 ∧ (linePoly K H Λ₀ δ G).natTrailingDegree = e' k₀ := by
    subst hG
    refine ⟨linePoly_C_mul_prod_ne_zero _ _ _ e' hc' hδ', ?_⟩
    simp only [kkPoly]
    rw [natTrailingDegree_linePoly_prod _ _ _ e' hc' hδ',
      Finset.filter_congr hzero, Finset.filter_eq' (kkIdx η) k₀]
    simp only [hk₀, ↓reduceIte, Finset.sum_singleton]
  obtain ⟨hd, hdt⟩ := hord hc hFe
  obtain ⟨hd₀, hd₀t⟩ := hord hc₀ hF₀e
  rw [← hdt, ← hd₀t]
  refine natTrailingDegree_eq_mul_of_generic P S hA (Λ₀ := Λ₀) (δ := δ) hk₀0 hk₀η
    (fun γ hγ0 hγne hγη heq ↦ ?_) (fun γ hγ0 hγne hγη heq ↦ ?_) hβ hd hd₀ (fun t ↦ ?_)
    (fun t ↦ ?_)
  · refine (hzero γ (mem_kkIdx.mpr ⟨hγ0, hγη, hγne⟩)).mp ?_
    rw [apply_kkVec_add_kkConst, heq, sub_self]
  · have := hgenΛ (.inr γ) (Finset.inr_mem_disjSum.mpr (mem_kkIdx.mpr ⟨hγ0, hγη, hγne⟩))
    simp only [Sum.elim_inr, evalPoly_kkShiftPoly] at this
    exact this (by rw [heq, sub_self])
  · rw [eval_linePoly, hF]
  · rw [eval_linePoly, hF₀]

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
