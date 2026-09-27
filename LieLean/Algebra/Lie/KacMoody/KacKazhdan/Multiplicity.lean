/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Jantzen.SumFormula

/-!
# Composition factors of Verma modules: the Kac–Kazhdan theorem

Let `A` be a symmetrizable generalized Cartan matrix, `𝔤 = 𝔤(A)` over an algebraically closed
field `K` of characteristic zero, and `M(λ)` the Verma module of highest weight `λ ∈ 𝔥*`. Call
`λ → λ - n α` a **Kac–Kazhdan step** (`KacKazhdanStep`) if `α` is a positive root (`α ∈ Q₊ \ {0}`
with `𝔤_α ≠ 0`, real or imaginary) and `n ≥ 1` is an integer with `2 (λ + ρ | α) = n (α | α)`.
The **Kac–Kazhdan theorem** ([KK] Thm. 2 (check); [Kac] §9 (check)) states that `L(μ)` is a
composition factor of `M(λ)`, `[M(λ) : L(μ)] ≠ 0`, iff `μ` is reached from `λ` by a finite chain of
Kac–Kazhdan steps (`VermaModule.multiplicity_ne_zero_iff_reflTransGen`). As a corollary, `M(λ)` is
irreducible iff no Kac–Kazhdan step starts at `λ`
(`VermaModule.maxSubmodule_eq_bot_iff_kacKazhdan`), e.g. if `(λ + ρ | α) ∉ ℚ` for all positive
roots `α`
(`VermaModule.maxSubmodule_eq_bot_of_forall_notMem_range_ratCast`).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.KacKazhdanStep`: one step `λ → λ - n α` of a Kac–Kazhdan
  chain.
* `Matrix.Realization.KacMoodyAlgebra.coneWindow`: the finite set of weights `ν` with
  `ξ ≤ ν ≤ λ`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.eq_of_forall_sum_coneWindow_eq`: unitriangularity of the
  irreducible characters, on a finite window of weights.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.finsum_multiplicity_jantzen`: **the Jantzen sum
  formula for multiplicities**, `∑_{i ≥ 1} [M(λ)^i : L(μ)] = ∑_{(α, n)} [M(λ - n α) : L(μ)]`,
  the sum over Kac–Kazhdan steps (roots counted with multiplicity), for any line `λ + t δ`
  transversal to the Kac–Kazhdan hyperplanes.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.multiplicity_ne_zero_of_kacKazhdanStep`,
  `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_kacKazhdanStep_of_multiplicity_ne_zero`:
  the two halves of the induction step.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.multiplicity_ne_zero_iff_reflTransGen`:
  **the Kac–Kazhdan theorem** ([KK] Thm. 2 (check)).
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.multiplicity_sub_nsmul_ne_zero`: a single step,
  `[M(λ) : L(λ - n α)] ≠ 0` if `2 (λ + ρ | α) = n (α | α)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.maxSubmodule_eq_bot_iff_kacKazhdan`,
  `VermaModule.maxSubmodule_eq_bot_of_forall_notMem_range_ratCast`: irreducibility of Verma
  modules.

## Proof

*The Jantzen sum formula for multiplicities.* Fix `η ∈ Q₊` and a direction `δ` transversal to the
Kac–Kazhdan hyperplanes through `λ`. The Jantzen sum formula
(`VermaModule.finsum_finrank_jantzen_inf_weightSpace_eq_sum_verma`) gives, for every `0 ≤ γ ≤ η`,
`∑_{i ≥ 1} dim M(λ)^i_{λ-γ} = ∑_{(x, n)} dim M(λ - n α_x)_{λ-γ}`. The Jantzen spaces vanish in the
weight `λ - γ` from some index on, since the Shapovalov determinant along the line is a nonzero
polynomial in `t` by the Kac–Kazhdan determinant formula; so only finitely many `i` occur. Expanding
every term by `dim V_ξ = ∑_ν [V : L(ν)] dim L(ν)_ξ` (`IsCategoryO.finrank_weightSpace_eq_finsum`),
where only `λ - η ≤ ξ ≤ ν ≤ λ` contribute, both sides become `∑_ν c_ν dim L(ν)_{λ-γ}` over the
finite window `λ - η ≤ ν ≤ λ`. Since `dim L(ν)_ν = 1` and `L(ν)_ξ = 0` unless `ξ ≤ ν`, the
coefficients are determined by these sums, by induction on the height of `λ - ν`
(`eq_of_forall_sum_coneWindow_eq`). This gives
`∑_{i ≥ 1} [M(λ)^i : L(λ - η)] = ∑_{(x, n)} [M(λ - n α_x) : L(λ - η)]`.

We use the direction `δ₀ = ν(ρ^∨)`, for which `(δ₀ | α) = ht α ≠ 0` for every positive root, so
`δ₀` is transversal to all Kac–Kazhdan hyperplanes.

*"⇐".* If `λ → λ' = λ - n α` is a Kac–Kazhdan step and `[M(λ') : L(μ)] ≠ 0`, then the right side of
the multiplicity sum formula (all of whose terms are `≥ 0`) is nonzero, hence
`[M(λ)^i : L(μ)] ≠ 0` for some `i ≥ 1`, hence `[M(λ) : L(μ)] ≠ 0` by additivity of multiplicities
(`IsCategoryO.multiplicity_eq_add`). Induction along the chain (starting from
`[M(μ) : L(μ)] = 1`) gives "⇐". In particular no separate argument is needed for imaginary (e.g.
isotropic, `(α | α) = 0`) roots, and the transitivity of "is a composition factor of a Verma
module" is not used.

*"⇒".* If `μ ≠ λ` and `[M(λ) : L(μ)] ≠ 0`, then `[M'(λ) : L(μ)] ≠ 0` because
`M(λ)/M'(λ) = L(λ)` and `[L(λ) : L(μ)] = 0`; and `M'(λ) = M(λ)^1` (`VermaModule.jantzen_one`). So
the left side of the multiplicity sum formula is nonzero, and some `[M(λ - n α) : L(μ)] ≠ 0` for a
Kac–Kazhdan step `λ → λ - n α`. Since `μ ≤ λ - n α < λ`, induction on the height of `λ - μ` gives
the chain.

*Irreducibility.* `M'(λ)` is the sum of its weight spaces, and `M'(λ)_{λ-η} ≠ 0` iff a
Kac–Kazhdan step `λ → λ - n α` with `n α ≤ η` exists (the Kac–Kazhdan criterion,
`VermaModule.maxSubmodule_inf_weightSpace_ne_bot_iff`). If `(λ + ρ | α) ∉ ℚ`, then
`2 (λ + ρ | α) ≠ n (α | α) ∈ ℚ`.

This is the standard deformation argument (Jantzen's for finite-dimensional `𝔤`, [HumO] §5.3–5.7
(check)); we reconstructed the details ourselves and did not check them against [KK] §4 (check),
whose proof may differ.

## References

* [KK] V. G. Kac, D. A. Kazhdan, *Structure of representations with highest weight of
  infinite-dimensional Lie algebras*, Adv. Math. 34 (1979), 97–108, Thm. 2 (check).
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9 (check).
* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, §5.3–5.7 (check).
-/

open Module LieModule Polynomial

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

/-! ### Unitriangularity on a window of weights -/

omit [DecidableEq ι] in
/-- The finite set `{ν | ξ ≤ ν ≤ Λ}` of weights between `ξ` and `Λ` for the dominance order. -/
def coneWindow (Λ ξ : Dual K H) : Finset (Dual K H) :=
  (finite_setOf_mem_cone_and_mem_cone P Λ ξ).toFinset

omit [DecidableEq ι] in
lemma mem_coneWindow {Λ ξ ν : Dual K H} :
    ν ∈ coneWindow P Λ ξ ↔ ν ∈ cone P Λ ∧ ξ ∈ cone P ν := by
  simp [coneWindow]

/-- If the composition factors of a module `V` in `𝒪` have highest weights `≤ Λ`, then
`dim V_ξ = ∑_{ξ ≤ ν ≤ Λ} [V : L(ν)] dim L(ν)_ξ`. -/
theorem IsCategoryO.finrank_weightSpace_eq_sum_coneWindow {V : Type*} [AddCommGroup V]
    [Module K V] [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
    (hV : IsCategoryO P V) {Λ : Dual K H} (hsupp : ∀ ν, hV.multiplicity ν ≠ 0 → ν ∈ cone P Λ)
    (ξ : Dual K H) :
    finrank K (weightSpace P V ξ) = ∑ ν ∈ coneWindow P Λ ξ,
      hV.multiplicity ν * finrank K (weightSpace P (IrreducibleModule P ν) ξ) := by
  rw [hV.finrank_weightSpace_eq_finsum ξ]
  refine finsum_eq_sum_of_support_subset _ fun ν hν ↦ ?_
  rw [Finset.mem_coe, mem_coneWindow]
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hν
  exact ⟨hsupp ν h1, IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero h2⟩

/-- **Unitriangularity of the irreducible characters on a window**: if
`∑_ν a_ν dim L(ν)_ξ = ∑_ν b_ν dim L(ν)_ξ` for all weights `ξ = Λ - γ` with `0 ≤ γ ≤ η` (the sums
over `ξ ≤ ν ≤ Λ`), then `a_{Λ - γ} = b_{Λ - γ}` for all these `γ`. -/
theorem eq_of_forall_sum_coneWindow_eq {Λ : Dual K H} {η : ι → ℤ} (a b : Dual K H → ℕ)
    (h : ∀ γ : ι → ℤ, 0 ≤ γ → γ ≤ η →
      ∑ ν ∈ coneWindow P Λ (Λ - P.rootOf γ),
          a ν * finrank K (weightSpace P (IrreducibleModule P ν) (Λ - P.rootOf γ)) =
        ∑ ν ∈ coneWindow P Λ (Λ - P.rootOf γ),
          b ν * finrank K (weightSpace P (IrreducibleModule P ν) (Λ - P.rootOf γ)))
    {γ : ι → ℤ} (hγ0 : 0 ≤ γ) (hγη : γ ≤ η) : a (Λ - P.rootOf γ) = b (Λ - P.rootOf γ) := by
  classical
  induction hn : (height γ).toNat using Nat.strong_induction_on generalizing γ with
  | _ n ih =>
  set ξ := Λ - P.rootOf γ with hξdef
  have hξ : ξ ∈ coneWindow P Λ ξ := (mem_coneWindow P).mpr ⟨⟨γ, hγ0, rfl⟩, mem_cone_self ξ⟩
  have hrest : ∀ ν ∈ (coneWindow P Λ ξ).erase ξ,
      a ν * finrank K (weightSpace P (IrreducibleModule P ν) ξ) =
        b ν * finrank K (weightSpace P (IrreducibleModule P ν) ξ) := by
    intro ν hν
    obtain ⟨hνξ, hν⟩ := Finset.mem_erase.mp hν
    obtain ⟨⟨γ', hγ'0, rfl⟩, ⟨k, hk0, hk⟩⟩ := (mem_coneWindow P).mp hν
    rw [hξdef] at hk
    have hγ : γ = γ' + k := P.rootOf_injective (by
      rw [map_add]
      linear_combination (norm := abel_nf) -hk)
    have hkne : k ≠ 0 := by
      rintro rfl
      rw [map_zero, sub_zero] at hk
      exact hνξ (hk.symm.trans hξdef.symm)
    have hkpos : 0 < height k := sum_pos_of_mem_posCone ⟨hk0, hkne⟩
    have hγ'pos : 0 ≤ height γ' := Finset.sum_nonneg fun i _ ↦ hγ'0 i
    have hlt : (height γ').toNat < n := by
      rw [← hn, hγ, show height (γ' + k) = height γ' + height k by
        simp [height, Finset.sum_add_distrib]]
      omega
    rw [ih _ hlt hγ'0 (le_trans (by rw [hγ]; exact le_add_of_nonneg_right hk0) hγη) rfl]
  have := h γ hγ0 hγη
  rw [← hξdef, ← Finset.add_sum_erase _ _ hξ, ← Finset.add_sum_erase _ _ hξ,
    Finset.sum_congr rfl hrest, IrreducibleModule.finrank_weightSpace_self, mul_one,
    mul_one] at this
  exact Nat.add_right_cancel this

/-! ### The Jantzen sum formula for multiplicities -/

variable [FiniteDimensional K H] (S : A.Symmetrization) (hA : A.IsGeneralizedCartan)

namespace VermaModule

include hA in
/-- Along a line `λ₀ + t δ` satisfying the transversality hypothesis of the Jantzen sum formula,
the Jantzen filtration of `M(λ₀)` vanishes in the weight `λ₀ - η` from some index on. -/
theorem exists_finrank_jantzen_inf_weightSpace_eq_zero [IsAlgClosed K] (Λ₀ δ : Dual K H)
    (η : ι → ℤ)
    (hδ : ∀ x : NegRootIndex P, ∀ n : ℕ, (n + 1) • x.coeff ≤ η →
      2 * P.dualBilinForm S (Λ₀ + P.rho) x.root =
        ((n : K) + 1) * P.dualBilinForm S x.root x.root →
      P.dualBilinForm S δ x.root ≠ 0) :
    ∃ R : ℕ, ∀ i, R < i → finrank K ((jantzen P Λ₀ δ i).toSubmodule ⊓
        weightSpace P Λ₀ (Λ₀ - P.rootOf η) : Submodule K _) = 0 := by
  obtain ⟨c, hc, h⟩ := exists_shapovalovDet_eq_prod_kkPairs P S hA η
  set f : NegRootIndex P × ℕ → K := fun z ↦ P.dualBilinForm S (Λ₀ + P.rho) z.1.root -
    ((z.2 : K) + 1) / 2 * P.dualBilinForm S z.1.root z.1.root
  set g : NegRootIndex P × ℕ → K := fun z ↦ P.dualBilinForm S δ z.1.root
  set e : NegRootIndex P × ℕ → ℕ := fun z ↦
    kostantPartition P (P.rootOf η - (z.2 + 1) • z.1.root)
  set d : K[X] := C c * ∏ z ∈ kkPairs P η, (C (f z) + C (g z) * X) ^ e z
  have hd0 : d ≠ 0 := by
    refine mul_ne_zero (C_ne_zero.mpr hc) (Finset.prod_ne_zero_iff.mpr fun z hz ↦
      pow_ne_zero _ fun h0 ↦ ?_)
    have h0' := congrArg (coeff · 0) h0
    have h1' := congrArg (coeff · 1) h0
    simp only [coeff_add, coeff_C_mul_X, coeff_C, coeff_zero] at h0' h1'
    simp only [↓reduceIte, one_ne_zero, zero_ne_one, add_zero, zero_add] at h0' h1'
    refine hδ z.1 z.2 ((mem_kkPairs P).mp hz) ?_ h1'
    simp only [f] at h0'
    linear_combination 2 * h0'
  have hdet (t : K) : d.eval t = shapovalovDet P (P.rootOf η) (Λ₀ + t • δ) := by
    rw [h]
    simp only [d, eval_mul, eval_C, eval_prod, eval_pow, eval_add, eval_X]
    congr 1
    refine Finset.prod_congr rfl fun z _ ↦ ?_
    congr 1
    simp only [f, g, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  exact ⟨d.natTrailingDegree, fun i hi ↦
    finrank_jantzen_inf_weightSpace_eq_zero S Λ₀ δ _ d hd0 hdet hi⟩

include hA in
/-- A uniform version of `exists_finrank_jantzen_inf_weightSpace_eq_zero` for all weights
`λ₀ - γ`, `0 ≤ γ ≤ η`. -/
theorem exists_forall_finrank_jantzen_inf_weightSpace_eq_zero [IsAlgClosed K] (Λ₀ δ : Dual K H)
    (η : ι → ℤ)
    (hδ : ∀ x : NegRootIndex P, ∀ n : ℕ, (n + 1) • x.coeff ≤ η →
      2 * P.dualBilinForm S (Λ₀ + P.rho) x.root =
        ((n : K) + 1) * P.dualBilinForm S x.root x.root →
      P.dualBilinForm S δ x.root ≠ 0) :
    ∃ R : ℕ, ∀ γ : ι → ℤ, 0 ≤ γ → γ ≤ η → ∀ i, R < i → finrank K ((jantzen P Λ₀ δ i).toSubmodule ⊓
        weightSpace P Λ₀ (Λ₀ - P.rootOf γ) : Submodule K _) = 0 := by
  have hγ : ∀ γ : ι → ℤ, ∃ R : ℕ, γ ≤ η → ∀ i, R < i → finrank K
      ((jantzen P Λ₀ δ i).toSubmodule ⊓ weightSpace P Λ₀ (Λ₀ - P.rootOf γ) : Submodule K _) =
        0 := fun γ ↦ by
    by_cases hγη : γ ≤ η
    · obtain ⟨R, hR⟩ := exists_finrank_jantzen_inf_weightSpace_eq_zero P S hA Λ₀ δ γ
        fun x n hxn ↦ hδ x n (hxn.trans hγη)
      exact ⟨R, fun _ ↦ hR⟩
    · exact ⟨0, fun h ↦ absurd h hγη⟩
  choose R hR using hγ
  refine ⟨(Fintype.piFinset fun j ↦ Finset.Icc 0 (η j)).sup R, fun γ hγ0 hγη i hi ↦
    hR γ hγη i (lt_of_le_of_lt (Finset.le_sup (Fintype.mem_piFinset.mpr fun j ↦
      Finset.mem_Icc.mpr ⟨hγ0 j, hγη j⟩)) hi)⟩

omit [FiniteDimensional K H] [CharZero K] in
/-- `λ₀ - (n + 1) α_x ≤ λ₀`. -/
lemma sub_nsmul_root_mem_cone (Λ₀ : Dual K H) (z : NegRootIndex P × ℕ) :
    Λ₀ - (z.2 + 1) • z.1.root ∈ cone P Λ₀ :=
  ⟨kkPairCoeff P z, nsmul_nonneg z.1.coeff_mem.1 _, by rw [rootOf_kkPairCoeff]⟩

include hA in
open Classical in
/-- **The Jantzen sum formula for multiplicities.** Let `A` be a symmetrizable generalized Cartan
matrix, `K` algebraically closed of characteristic zero, `η ∈ Q₊`, and `λ₀, δ ∈ 𝔥*` with
`(δ | α_x) ≠ 0` whenever `2 (λ₀ + ρ | α_x) = n (α_x | α_x)` with `n α_x ≤ η`. Then
`∑_{i ≥ 1} [M(λ₀)^i : L(λ₀ - η)] = ∑_{(x, n)} [M(λ₀ - n α_x) : L(λ₀ - η)]`,
the sum on the right over the pairs `(x, n)`, `n ≥ 1`, with `n α_x ≤ η` and
`2 (λ₀ + ρ | α_x) = n (α_x | α_x)` (cf. [HumO] §5.3 (check), [Jantzen] (check)). -/
theorem finsum_multiplicity_jantzen [IsAlgClosed K] (Λ₀ δ : Dual K H) {η : ι → ℤ} (hη : 0 ≤ η)
    (hδ : ∀ x : NegRootIndex P, ∀ n : ℕ, (n + 1) • x.coeff ≤ η →
      2 * P.dualBilinForm S (Λ₀ + P.rho) x.root =
        ((n : K) + 1) * P.dualBilinForm S x.root x.root →
      P.dualBilinForm S δ x.root ≠ 0) :
    ∑ᶠ i : ℕ, ((isCategoryO P Λ₀).lieSubmodule (jantzen P Λ₀ δ (i + 1))).multiplicity
        (Λ₀ - P.rootOf η) =
      ∑ z ∈ (kkPairs P η).filter (fun z ↦ 2 * P.dualBilinForm S (Λ₀ + P.rho) z.1.root =
          ((z.2 : K) + 1) * P.dualBilinForm S z.1.root z.1.root),
        (isCategoryO P (Λ₀ - (z.2 + 1) • z.1.root)).multiplicity (Λ₀ - P.rootOf η) := by
  obtain ⟨R, hR⟩ := exists_forall_finrank_jantzen_inf_weightSpace_eq_zero P S hA Λ₀ δ η hδ
  set Z := (kkPairs P η).filter (fun z ↦ 2 * P.dualBilinForm S (Λ₀ + P.rho) z.1.root =
    ((z.2 : K) + 1) * P.dualBilinForm S z.1.root z.1.root)
  set a : Dual K H → ℕ := fun ν ↦ ∑ i ∈ Finset.range R,
    ((isCategoryO P Λ₀).lieSubmodule (jantzen P Λ₀ δ (i + 1))).multiplicity ν
  set b : Dual K H → ℕ := fun ν ↦ ∑ z ∈ Z,
    (isCategoryO P (Λ₀ - (z.2 + 1) • z.1.root)).multiplicity ν
  have hsuppN (i : ℕ) (ν : Dual K H)
      (hν : ((isCategoryO P Λ₀).lieSubmodule (jantzen P Λ₀ δ (i + 1))).multiplicity ν ≠ 0) :
      ν ∈ cone P Λ₀ := by
    refine mem_cone_of_multiplicity_ne_zero ?_
    rw [(isCategoryO P Λ₀).multiplicity_eq_add (jantzen P Λ₀ δ (i + 1)) ν]
    omega
  have hsuppV (z : NegRootIndex P × ℕ) (ν : Dual K H)
      (hν : (isCategoryO P (Λ₀ - (z.2 + 1) • z.1.root)).multiplicity ν ≠ 0) :
      ν ∈ cone P Λ₀ :=
    mem_cone_trans (mem_cone_of_multiplicity_ne_zero hν) (sub_nsmul_root_mem_cone P Λ₀ z)
  have hab : ∀ γ : ι → ℤ, 0 ≤ γ → γ ≤ η →
      ∑ ν ∈ coneWindow P Λ₀ (Λ₀ - P.rootOf γ),
          a ν * finrank K (KacMoodyAlgebra.weightSpace P (IrreducibleModule P ν)
            (Λ₀ - P.rootOf γ)) =
        ∑ ν ∈ coneWindow P Λ₀ (Λ₀ - P.rootOf γ),
          b ν * finrank K (KacMoodyAlgebra.weightSpace P (IrreducibleModule P ν)
            (Λ₀ - P.rootOf γ)) := by
    intro γ hγ0 hγη
    have hsf := finsum_finrank_jantzen_inf_weightSpace_eq_sum_verma P S hA Λ₀ δ γ
      fun x n hxn ↦ hδ x n (hxn.trans hγη)
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range R) fun i hi ↦ ?_] at hsf
    swap
    · by_contra hiR
      rw [Finset.coe_range, Set.mem_Iio, not_lt] at hiR
      exact hi (hR γ hγ0 hγη (i + 1) (by omega))
    have hL : ∑ ν ∈ coneWindow P Λ₀ (Λ₀ - P.rootOf γ),
        a ν * finrank K (KacMoodyAlgebra.weightSpace P (IrreducibleModule P ν)
          (Λ₀ - P.rootOf γ)) = ∑ i ∈ Finset.range R, finrank K
            ((jantzen P Λ₀ δ (i + 1)).toSubmodule ⊓ weightSpace P Λ₀ (Λ₀ - P.rootOf γ) :
              Submodule K _) := by
      simp only [a, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← finrank_weightSpaceOfMap_lieSubmodule,
        ((isCategoryO P Λ₀).lieSubmodule _).finrank_weightSpace_eq_sum_coneWindow P (hsuppN i)]
    have hR' : ∑ ν ∈ coneWindow P Λ₀ (Λ₀ - P.rootOf γ),
        b ν * finrank K (KacMoodyAlgebra.weightSpace P (IrreducibleModule P ν)
          (Λ₀ - P.rootOf γ)) = ∑ z ∈ Z, finrank K
            (weightSpace P (Λ₀ - (z.2 + 1) • z.1.root) (Λ₀ - P.rootOf γ)) := by
      simp only [b, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [(isCategoryO P _).finrank_weightSpace_eq_sum_coneWindow P (hsuppV z)]
    rw [hL, hR', hsf]
    refine Finset.sum_subset (Finset.filter_subset_filter _ fun z hz ↦
      (mem_kkPairs P).mpr (((mem_kkPairs P).mp hz).trans hγη)) fun z hz hzγ ↦ ?_
    have hzγ' : ¬ 0 ≤ γ - kkPairCoeff P z := fun h ↦ hzγ (Finset.mem_filter.mpr
      ⟨(mem_kkPairs P).mpr (sub_nonneg.mp h), (Finset.mem_filter.mp hz).2⟩)
    have hw : Λ₀ - P.rootOf γ = Λ₀ - (z.2 + 1) • z.1.root - P.rootOf (γ - kkPairCoeff P z) := by
      rw [map_sub, rootOf_kkPairCoeff]
      abel
    rw [hw, weightSpace_sub_rootOf_eq_bot P _ hzγ', finrank_bot]
  have key := eq_of_forall_sum_coneWindow_eq P a b hab hη le_rfl
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range R) fun i hi ↦ ?_]
  · exact key
  · by_contra hiR
    rw [Finset.coe_range, Set.mem_Iio, not_lt] at hiR
    have := ((isCategoryO P Λ₀).lieSubmodule (jantzen P Λ₀ δ (i + 1))).multiplicity_le_finrank
      (Λ₀ - P.rootOf η)
    rw [finrank_weightSpaceOfMap_lieSubmodule, hR η hη le_rfl (i + 1) (by omega)] at this
    exact hi (Nat.le_zero.mp this)

include hA in
/-- The Jantzen filtration contributes only finitely many terms to the multiplicity sum
formula. -/
theorem finite_support_multiplicity_jantzen [IsAlgClosed K] (Λ₀ δ : Dual K H) (η : ι → ℤ)
    (hδ : ∀ x : NegRootIndex P, ∀ n : ℕ, (n + 1) • x.coeff ≤ η →
      2 * P.dualBilinForm S (Λ₀ + P.rho) x.root =
        ((n : K) + 1) * P.dualBilinForm S x.root x.root →
      P.dualBilinForm S δ x.root ≠ 0) :
    (Function.support fun i : ℕ ↦ ((isCategoryO P Λ₀).lieSubmodule
      (jantzen P Λ₀ δ (i + 1))).multiplicity (Λ₀ - P.rootOf η)).Finite := by
  obtain ⟨R, hR⟩ := exists_finrank_jantzen_inf_weightSpace_eq_zero P S hA Λ₀ δ η hδ
  refine (Set.finite_Iio R).subset fun i hi ↦ ?_
  by_contra hiR
  rw [Set.mem_Iio, not_lt] at hiR
  have := ((isCategoryO P Λ₀).lieSubmodule (jantzen P Λ₀ δ (i + 1))).multiplicity_le_finrank
    (Λ₀ - P.rootOf η)
  rw [finrank_weightSpaceOfMap_lieSubmodule, hR (i + 1) (by omega)] at this
  exact hi (Nat.le_zero.mp this)

end VermaModule

/-! ### Kac–Kazhdan chains -/

omit [DecidableEq ι] in
/-- The direction `δ₀ = ν(ρ^∨)`: `(δ₀ | α) = ht α ≠ 0` for every positive root `α`, so the line
`λ₀ + t δ₀` is transversal to all Kac–Kazhdan hyperplanes. -/
lemma dualBilinForm_toDual_rhoCheck (k : ι → ℤ) :
    P.dualBilinForm S (P.toDual S P.rhoCheck) (P.rootOf k) = ((height k : ℤ) : K) := by
  rw [(P.isSymm_dualBilinForm S).eq, dualBilinForm_apply_eq, LinearEquiv.symm_apply_apply,
    rootOf_rhoCheck]

lemma dualBilinForm_toDual_rhoCheck_ne_zero (x : NegRootIndex P) :
    P.dualBilinForm S (P.toDual S P.rhoCheck) x.root ≠ 0 := by
  rw [← x.rootOf_coeff, dualBilinForm_toDual_rhoCheck]
  exact Int.cast_ne_zero.mpr (sum_pos_of_mem_posCone x.coeff_mem).ne'

omit [FiniteDimensional K H] in
lemma NegRootIndex.rootSpace_root_ne_bot (x : NegRootIndex P) : rootSpace P x.root ≠ ⊥ := by
  intro h0
  have hx : x.root ∈ P.posWeights := x.1.2
  have h := x.2.pos
  have := finiteDimensional_rootSpace P hx
  change 0 < finrank K (rootSpace P (-x.root)) at h
  rw [finrank_rootSpace_neg_eq P hx, h0, finrank_bot] at h
  exact lt_irrefl 0 h

omit [FiniteDimensional K H] in
/-- Every positive root is the root of an index of the root vector basis of `𝔫₋`. -/
lemma exists_negRootIndex_root_eq {α : Dual K H} (hα : α ∈ P.posWeights)
    (h : rootSpace P α ≠ ⊥) : ∃ x : NegRootIndex P, x.root = α := by
  have := finiteDimensional_rootSpace P hα
  have hpos : 0 < finrank K (rootSpace P (-(⟨α, hα⟩ : P.posWeights) : Dual K H)) := by
    rw [finrank_rootSpace_neg_eq P hα]
    exact Nat.pos_of_ne_zero fun h0 ↦ h (Submodule.finrank_eq_zero.mp h0)
  exact ⟨⟨⟨α, hα⟩, ⟨0, hpos⟩⟩, rfl⟩

/-- One step of a **Kac–Kazhdan chain** ([KK] Thm. 2 (check)): `μ = λ - n α` for a positive root
`α` (i.e. `α ∈ Q₊ \ {0}` with `𝔤_α ≠ 0`) and an integer `n ≥ 1` with
`2 (λ + ρ | α) = n (α | α)`. -/
def KacKazhdanStep (Λ μ : Dual K H) : Prop :=
  ∃ α ∈ P.posWeights, rootSpace P α ≠ ⊥ ∧ ∃ n : ℕ, 0 < n ∧ μ = Λ - n • α ∧
    2 * P.dualBilinForm S (Λ + P.rho) α = n * P.dualBilinForm S α α

namespace VermaModule

include hA in
open Classical in
/-- If `μ` is obtained from `λ` by a Kac–Kazhdan step, every composition factor of `M(μ)` is a
composition factor of `M(λ)` (in fact of `M'(λ)`): this is the step "⇐" of [KK] Thm. 2 (check),
via the Jantzen sum formula. -/
theorem multiplicity_ne_zero_of_kacKazhdanStep [IsAlgClosed K] {Λ Λ' μ : Dual K H}
    (hstep : KacKazhdanStep P S Λ Λ') (h : (isCategoryO P Λ').multiplicity μ ≠ 0) :
    (isCategoryO P Λ).multiplicity μ ≠ 0 := by
  obtain ⟨α, hα, hαne, n, hn, rfl, hKK⟩ := hstep
  obtain ⟨x, rfl⟩ := exists_negRootIndex_root_eq P hα hαne
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k, hk, rfl⟩ := mem_cone_of_multiplicity_ne_zero h
  set η := (m + 1) • x.coeff + k
  have hη : 0 ≤ η := add_nonneg (nsmul_nonneg x.coeff_mem.1 _) hk
  have hμ : Λ - (m + 1) • x.root - P.rootOf k = Λ - P.rootOf η := by
    rw [map_add, map_nsmul, x.rootOf_coeff]
    abel
  rw [hμ] at h ⊢
  set δ₀ := P.toDual S P.rhoCheck
  have hsum := finsum_multiplicity_jantzen P S hA Λ δ₀ hη
    fun x' _ _ _ ↦ dualBilinForm_toDual_rhoCheck_ne_zero P S x'
  have hz : (x, m) ∈ (kkPairs P η).filter (fun z ↦ 2 * P.dualBilinForm S (Λ + P.rho) z.1.root =
      ((z.2 : K) + 1) * P.dualBilinForm S z.1.root z.1.root) := by
    refine Finset.mem_filter.mpr ⟨(mem_kkPairs P).mpr (le_add_of_nonneg_right hk), ?_⟩
    rw [hKK]
    push_cast
    ring
  have hne : ∑ᶠ i : ℕ, ((isCategoryO P Λ).lieSubmodule (jantzen P Λ δ₀ (i + 1))).multiplicity
      (Λ - P.rootOf η) ≠ 0 := by
    rw [hsum]
    intro h0
    have h0' := (Finset.sum_eq_zero_iff.mp h0) (x, m) hz
    exact h h0'
  obtain ⟨i, hi⟩ : ∃ i : ℕ, ((isCategoryO P Λ).lieSubmodule
      (jantzen P Λ δ₀ (i + 1))).multiplicity (Λ - P.rootOf η) ≠ 0 := by
    by_contra! h0
    exact hne (finsum_eq_zero_of_forall_eq_zero h0)
  rw [(isCategoryO P Λ).multiplicity_eq_add (jantzen P Λ δ₀ (i + 1))]
  omega

include hA in
open Classical in
/-- Every composition factor `L(μ)`, `μ ≠ λ`, of `M(λ)` is a composition factor of `M(λ - n α)`
for some Kac–Kazhdan step `λ → λ - n α`: the step "⇒" of [KK] Thm. 2 (check), via the Jantzen
sum formula. -/
theorem exists_kacKazhdanStep_of_multiplicity_ne_zero [IsAlgClosed K] {Λ μ : Dual K H}
    (hμ : μ ≠ Λ) (h : (isCategoryO P Λ).multiplicity μ ≠ 0) :
    ∃ Λ', KacKazhdanStep P S Λ Λ' ∧ (isCategoryO P Λ').multiplicity μ ≠ 0 := by
  obtain ⟨η, hη, rfl⟩ := mem_cone_of_multiplicity_ne_zero h
  set δ₀ := P.toDual S P.rhoCheck
  have hδ : ∀ x : NegRootIndex P, ∀ n : ℕ, (n + 1) • x.coeff ≤ η →
      2 * P.dualBilinForm S (Λ + P.rho) x.root =
        ((n : K) + 1) * P.dualBilinForm S x.root x.root →
      P.dualBilinForm S δ₀ x.root ≠ 0 := fun x _ _ _ ↦ dualBilinForm_toDual_rhoCheck_ne_zero P S x
  -- `[M(λ) : L(μ)] = [M'(λ) : L(μ)] = [M(λ)^1 : L(μ)]`
  have hadd := (isCategoryO P Λ).multiplicity_eq_add (maxSubmodule P Λ) (Λ - P.rootOf η)
  have hL := IrreducibleModule.multiplicity_eq (P := P) Λ (Λ - P.rootOf η)
  rw [ite_eq_right_iff.mpr fun h ↦ absurd h hμ] at hL
  have h1 : ((isCategoryO P Λ).lieSubmodule (jantzen P Λ δ₀ (0 + 1))).multiplicity
      (Λ - P.rootOf η) ≠ 0 := by
    rw [zero_add, jantzen_one P S Λ δ₀]
    change _ = _ + (IrreducibleModule.isCategoryO P Λ).multiplicity _ at hadd
    omega
  have hle := single_le_finsum 0 (finite_support_multiplicity_jantzen P S hA Λ δ₀ η hδ)
    fun _ ↦ Nat.zero_le _
  rw [finsum_multiplicity_jantzen P S hA Λ δ₀ hη hδ] at hle
  obtain ⟨z, hz, hz0⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (Nat.pos_of_ne_zero h1) hle))
  obtain ⟨-, hKK⟩ := Finset.mem_filter.mp hz
  refine ⟨_, ⟨z.1.root, (z.1.1.2 : z.1.root ∈ P.posWeights), z.1.rootSpace_root_ne_bot, z.2 + 1,
    Nat.succ_pos _, rfl, ?_⟩, hz0⟩
  rw [hKK]
  push_cast
  ring

include hA in
/-- **The Kac–Kazhdan theorem on composition factors of Verma modules** ([KK] Thm. 2 (check);
[Kac] §9 (check)). Let `A` be a symmetrizable generalized Cartan matrix and `K` algebraically
closed of characteristic zero. Then `L(μ)` is a composition factor of `M(λ)`, i.e.
`[M(λ) : L(μ)] ≠ 0`, iff there is a chain `λ = λ₀, λ₁, …, λ_k = μ` with
`λ_{j+1} = λ_j - n_j β_j` for positive roots `β_j` and integers `n_j ≥ 1` such that
`2 (λ_j + ρ | β_j) = n_j (β_j | β_j)` (`KacKazhdanStep`). -/
theorem multiplicity_ne_zero_iff_reflTransGen [IsAlgClosed K] (Λ μ : Dual K H) :
    (isCategoryO P Λ).multiplicity μ ≠ 0 ↔ Relation.ReflTransGen (KacKazhdanStep P S) Λ μ := by
  constructor
  · intro hΛμ
    obtain ⟨η, hη, rfl⟩ := mem_cone_of_multiplicity_ne_zero hΛμ
    induction hn : (height η).toNat using Nat.strong_induction_on generalizing Λ η with
    | _ n ih =>
    by_cases hμ : Λ - P.rootOf η = Λ
    · rw [hμ]
    obtain ⟨Λ', hstep, h'⟩ := exists_kacKazhdanStep_of_multiplicity_ne_zero P S hA hμ hΛμ
    obtain ⟨η', hη', hη'eq⟩ := mem_cone_of_multiplicity_ne_zero h'
    obtain ⟨α, hα, -, m, hm, rfl, -⟩ := id hstep
    obtain ⟨c, hc, rfl⟩ := hα
    have hηeq : η = m • c + η' := P.rootOf_injective (by
      rw [map_add, map_nsmul]
      linear_combination (norm := abel_nf) -hη'eq)
    have hlt : (height η').toNat < n := by
      have h1 := sum_pos_of_mem_posCone hc
      have h2 : 0 ≤ height η' := Finset.sum_nonneg fun i _ ↦ hη' i
      have h3 : 0 < (m : ℤ) * height c := mul_pos (by exact_mod_cast hm) h1
      rw [← hn, hηeq, show height (m • c + η') = m * height c + height η' by
        simp [height, Finset.sum_add_distrib, Finset.mul_sum]]
      omega
    rw [hη'eq] at h' ⊢
    exact .head hstep (ih _ hlt _ η' hη' h' rfl)
  · intro hchain
    induction hchain using Relation.ReflTransGen.head_induction_on with
    | refl => rw [multiplicity_self]; exact one_ne_zero
    | head hstep _ ih => exact multiplicity_ne_zero_of_kacKazhdanStep P S hA hstep ih

include hA in
/-- If `2 (λ + ρ | α) = n (α | α)` for a positive root `α` and an integer `n ≥ 1`, then `L(λ - n α)`
is a composition factor of `M(λ)` ([KK] Thm. 2 (check)). -/
theorem multiplicity_sub_nsmul_ne_zero [IsAlgClosed K] {Λ α : Dual K H} (hα : α ∈ P.posWeights)
    (hαne : rootSpace P α ≠ ⊥) {n : ℕ} (hn : 0 < n)
    (hK : 2 * P.dualBilinForm S (Λ + P.rho) α = n * P.dualBilinForm S α α) :
    (isCategoryO P Λ).multiplicity (Λ - n • α) ≠ 0 :=
  (multiplicity_ne_zero_iff_reflTransGen P S hA Λ _).mpr (.single ⟨α, hα, hαne, n, hn, rfl, hK⟩)

include hA in
/-- **The Kac–Kazhdan irreducibility criterion** ([KK] (check); [Kac] §9 (check)): for `A`
symmetrizable and `K` algebraically closed of characteristic zero, the Verma module `M(λ)` is
irreducible, i.e. `M'(λ) = 0`, iff `2 (λ + ρ | α) ≠ n (α | α)` for all positive roots `α` and all
integers `n ≥ 1`. -/
theorem maxSubmodule_eq_bot_iff_kacKazhdan [IsAlgClosed K] (Λ : Dual K H) :
    maxSubmodule P Λ = ⊥ ↔ ∀ α ∈ P.posWeights, rootSpace P α ≠ ⊥ → ∀ n : ℕ, 0 < n →
      2 * P.dualBilinForm S (Λ + P.rho) α ≠ n * P.dualBilinForm S α α := by
  constructor
  · intro hbot α hα hαne n hn hK
    obtain ⟨x, rfl⟩ := exists_negRootIndex_root_eq P hα hαne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have := (maxSubmodule_inf_weightSpace_ne_bot_iff P S hA Λ ((m + 1) • x.coeff)).mpr
      ⟨x, m, le_rfl, by rw [hK]; push_cast; ring⟩
    rw [hbot] at this
    simp at this
  · intro hK
    by_contra hne
    have hO := (isCategoryO P Λ).lieSubmodule (maxSubmodule P Λ)
    obtain ⟨ξ, hξ⟩ : ∃ ξ, weightSpaceOfMap (maxSubmodule P Λ) (h P) ξ ≠ ⊥ := by
      by_contra! hall
      have htop := hO.iSup_weightSpaceOfMap_eq_top
      simp only [hall, iSup_bot] at htop
      refine hne ((LieSubmodule.eq_bot_iff _).mpr fun m hm ↦ ?_)
      have : (⟨m, hm⟩ : maxSubmodule P Λ) ∈ (⊥ : Submodule K (maxSubmodule P Λ)) :=
        htop ▸ Submodule.mem_top
      simpa using this
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hξ
    have hv' : (v : VermaModule P Λ) ∈ weightSpaceOfMap (VermaModule P Λ) (h P) ξ :=
      mem_weightSpaceOfMap_lieSubmodule_iff.mp hv
    have hv0' : (v : VermaModule P Λ) ≠ 0 := fun h0 ↦ hv0 (Subtype.ext h0)
    obtain ⟨η, -, rfl⟩ := exists_eq_sub_of_mem_weightSpace P Λ LieModuleHom.id
      Function.surjective_id hv' hv0'
    have hne' : (maxSubmodule P Λ).toSubmodule ⊓ weightSpace P Λ (Λ - P.rootOf η) ≠ ⊥ := by
      intro h0
      have hmem : (v : VermaModule P Λ) ∈
          (maxSubmodule P Λ).toSubmodule ⊓ weightSpace P Λ (Λ - P.rootOf η) := ⟨v.2, hv'⟩
      rw [h0] at hmem
      exact hv0' ((Submodule.mem_bot K).mp hmem)
    obtain ⟨x, n, -, hxn⟩ := (maxSubmodule_inf_weightSpace_ne_bot_iff P S hA Λ η).mp hne'
    exact hK x.root (x.1.2 : x.root ∈ P.posWeights) x.rootSpace_root_ne_bot (n + 1) (Nat.succ_pos n)
      (by rw [hxn]; push_cast; ring)

omit [DecidableEq ι] in
/-- `(α | β)` is rational for `α, β` in the root lattice. -/
lemma dualBilinForm_rootOf_rootOf (c c' : ι → ℤ) :
    P.dualBilinForm S (P.rootOf c) (P.rootOf c') =
      ((∑ i, ∑ j, (c i * c' j : ℚ) * S.matrix i j : ℚ) : K) := by
  simp only [rootOf_apply, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, dualBilinForm_root_root, Finset.mul_sum]
  push_cast
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring)

include hA in
/-- **Verma modules with generic highest weight are irreducible** (a consequence of the
Kac–Kazhdan criterion, [KK] (check)): if `(λ + ρ | α) ∉ ℚ` for every positive root `α`, then
`M(λ)` is irreducible. -/
theorem maxSubmodule_eq_bot_of_forall_notMem_range_ratCast [IsAlgClosed K] {Λ : Dual K H}
    (hΛ : ∀ α ∈ P.posWeights, rootSpace P α ≠ ⊥ →
      P.dualBilinForm S (Λ + P.rho) α ∉ Set.range ((↑) : ℚ → K)) :
    maxSubmodule P Λ = ⊥ := by
  refine (maxSubmodule_eq_bot_iff_kacKazhdan P S hA Λ).mpr fun α hα hαne n _ hK ↦
    hΛ α hα hαne ?_
  obtain ⟨c, -, rfl⟩ := hα
  refine ⟨n * (∑ i, ∑ j, (c i * c j : ℚ) * S.matrix i j) / 2, ?_⟩
  rw [Rat.cast_div, Rat.cast_mul, ← dualBilinForm_rootOf_rootOf P S, Rat.cast_natCast,
    Rat.cast_ofNat]
  linear_combination -hK / 2

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
