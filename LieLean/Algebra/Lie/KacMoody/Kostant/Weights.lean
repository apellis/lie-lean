/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Kostant.GarlandLepowsky
import LieLean.Algebra.Lie.KacMoody.GabberKac
import LieLean.Algebra.Lie.KacMoody.WeylLength
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroupExchange

/-!
# Kostant's lemma on the weights of `⋀𝔫₋ ⊗ L(Λ)`

Let `A` be a symmetrizable generalized Cartan matrix, `𝔤 = 𝔤(A)` over a field `K` of
characteristic zero, `Λ` a dominant integral weight and `λ = Λ + ρ`. The weights of the chains
`C_k(𝔫₋, L(Λ)) = ⋀ᵏ𝔫₋ ⊗ L(Λ)` are the `ν - ⟨m⟩`, where `ν` is a weight of `L(Λ)` and `m` is a
multiset of `k` positive roots in which each root `α` occurs at most `dim 𝔤_{-α}` times
(`IsRootMultiset`), `⟨m⟩` being the sum of `m`. **Kostant's lemma** states that if such a weight
`μ = ν - ⟨m⟩` satisfies `(μ + ρ | μ + ρ) = (λ | λ)`, then `μ + ρ = w λ` for some `w ∈ W` with
`ℓ(w) = k`. Together with the Casimir argument (Kostant's `dδ + δd` identity), this identifies the
weights of `H_k(𝔫₋, L(Λ))`.

## Proof

We could not consult [Kum] and reconstructed the following argument, which avoids positivity of
the (in general indefinite) form. Write `φ = ν + ρ - ⟨m⟩`; then `λ - φ ∈ Q₊` and we argue by
induction on its height. The key point is that for a simple reflection `rᵢ` the pair `(ν, m)` can
be replaced by `(rᵢ ν, rᵢ ⋆ m)`, where `rᵢ ⋆ m` removes `αᵢ` from `m`, applies `rᵢ` to the other
roots (which `rᵢ` permutes, with multiplicities, [Kac] Lemma 3.7) and adds `αᵢ` if it did not
occur (`reflectMset`); then `ρ - ⟨rᵢ ⋆ m⟩ = rᵢ (ρ - ⟨m⟩)`, so the new `φ` is `rᵢ φ`.
* If `⟨φ, αⱼ^∨⟩ ≥ 0` for all `j`, write `λ - φ = β = ∑ cⱼ αⱼ`; then
  `(λ|λ) - (φ|φ) = (λ + φ | β) = ∑ cⱼ ⟨λ + φ, αⱼ^∨⟩ / εⱼ`, a sum of nonnegative rationals which
  are positive unless `cⱼ = 0`. Hence `φ = λ`, and then `ν = Λ`, `m = 0`, and `w = 1` works.
* Otherwise `⟨φ, αᵢ^∨⟩ < 0` for some `i`, and `rᵢ φ = φ - ⟨φ, αᵢ^∨⟩ αᵢ` is closer to `λ`. By
  induction `rᵢ φ = w' λ` with `ℓ(w') = |rᵢ ⋆ m|`, and moreover every root `α` of `rᵢ ⋆ m`
  satisfies `w'⁻¹ α < 0`. Since `⟨w' λ, αᵢ^∨⟩ > 0` and `λ` is regular dominant, `w'⁻¹ αᵢ > 0`
  (`inv_apply_root_mem_posWeights`), so `αᵢ` does not occur in `rᵢ ⋆ m`, i.e. `αᵢ` occurs in `m`,
  and `|m| = |rᵢ ⋆ m| + 1`; also `ℓ(rᵢ w') = ℓ(w') + 1` by [Kac] Lemma 3.11. Thus `w = rᵢ w'`
  works, and the invariant (`w⁻¹ α < 0` for the roots `α` of `m`) is inherited.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.msetWt`: the sum `⟨m⟩` of a multiset of weights.
* `Matrix.Realization.KacMoodyAlgebra.IsRootMultiset`: multisets of positive roots within the
  root multiplicities.
* `Matrix.Realization.KacMoodyAlgebra.reflectMset`: the multiset `rᵢ ⋆ m`.
* `Matrix.Realization.KacMoodyAlgebra.finsetMset`: the multiset of roots of a set of root vectors.

## Main results

* `Matrix.Realization.dualBilinForm_weylGroup`: `W` preserves the form on `𝔥*`.
* `Matrix.Realization.KacMoodyAlgebra.exists_weylGroup_of_dualBilinForm_eq`: Kostant's lemma.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.
  exists_weylGroup_of_homologyWeightSpace_ne_bot_of_eq`: if `H_k(𝔫₋, L(Λ))_μ ≠ 0` and
  `(μ + ρ | μ + ρ) = (Λ + ρ | Λ + ρ)`, then `μ = w(Λ + ρ) - ρ` with
  `ℓ(w) = k`.

## References

* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §3.2 (check).
* [GL] H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent.
  Math. **34** (1976), 37–76, §5 (check).
* B. Kostant, *Lie algebra cohomology and the generalized Borel–Weil theorem*, Ann. of Math.
  **74** (1961), 329–387, §5 (check) (finite type, via positivity).
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §3.7, §3.11.
-/

open Module

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsGeneralizedCartan) (S : A.Symmetrization)

/-! ### `W`-invariance of the form on `𝔥*` -/

omit [DecidableEq ι] in
/-- The fundamental reflections preserve the form: `(rᵢ μ | rᵢ μ') = (μ | μ')`. -/
theorem dualBilinForm_reflection (i : ι) (μ μ' : Dual K H) :
    P.dualBilinForm S (P.reflection hA i μ) (P.reflection hA i μ') =
      P.dualBilinForm S μ μ' := by
  have h1 := P.dualBilinForm_root_right S μ i
  have h2 : P.dualBilinForm S (P.root i) μ' = μ' (P.coroot i) / S.ε i := by
    rw [(P.isSymm_dualBilinForm S).eq]
    exact P.dualBilinForm_root_right S μ' i
  have h3 := P.dualBilinForm_root_right S (P.root i) i
  rw [P.root_coroot, hA.diag] at h3
  have hε : (S.ε i : K) ≠ 0 := by exact_mod_cast S.ε_ne_zero i
  simp only [reflection_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, h1, h2, h3]
  push_cast
  field_simp
  ring

omit [DecidableEq ι] in
/-- The Weyl group preserves the form: `(w μ | w μ') = (μ | μ')` ([Kac] §3.8 (check)). -/
theorem dualBilinForm_weylGroup {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    (μ μ' : Dual K H) : P.dualBilinForm S (w μ) (w μ') = P.dualBilinForm S μ μ' := by
  refine P.weylGroup_induction hA (p := fun w ↦ ∀ μ μ',
    P.dualBilinForm S (w μ) (w μ') = P.dualBilinForm S μ μ') (fun _ _ ↦ rfl)
    (fun i w ih μ μ' ↦ ?_) hw μ μ'
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, dualBilinForm_reflection, ih]


/-! ### Multisets of positive roots -/

namespace KacMoodyAlgebra

/-- The weight `⟨m⟩ = ∑_α m(α) α` of a finitely supported family `m` of multiplicities. -/
def msetWt (m : Dual K H →₀ ℕ) : Dual K H := m.sum fun α n ↦ n • α

omit [Fintype ι] [DecidableEq ι] [CharZero K] [FiniteDimensional K H] in
@[simp] lemma msetWt_zero : msetWt (0 : Dual K H →₀ ℕ) = 0 := Finsupp.sum_zero_index

omit [Fintype ι] [DecidableEq ι] [CharZero K] [FiniteDimensional K H] in
lemma msetWt_add (m m' : Dual K H →₀ ℕ) : msetWt (m + m') = msetWt m + msetWt m' :=
  Finsupp.sum_add_index' (fun _ ↦ zero_smul _ _) fun _ _ _ ↦ add_smul _ _ _

omit [Fintype ι] [DecidableEq ι] [CharZero K] [FiniteDimensional K H] in
@[simp] lemma msetWt_single (α : Dual K H) (n : ℕ) : msetWt (Finsupp.single α n) = n • α :=
  Finsupp.sum_single_index (zero_smul _ _)

omit [Fintype ι] [DecidableEq ι] [CharZero K] [FiniteDimensional K H] in
lemma msetWt_mapDomain (f : Dual K H ≃ₗ[K] Dual K H) (m : Dual K H →₀ ℕ) :
    msetWt (m.mapDomain f) = f (msetWt m) := by
  rw [msetWt, Finsupp.sum_mapDomain_index (h := fun α (n : ℕ) ↦ n • α) (fun _ ↦ zero_smul _ _)
    fun _ _ _ ↦ add_smul _ _ _, msetWt, map_finsuppSum]
  simp only [map_nsmul]

/-- `m` is a multiset of positive roots of `𝔤(A)` in which each `α` occurs at most
`dim 𝔤_{-α}` times: the multisets of weights of the wedge monomials of a basis of root vectors
of `𝔫₋`. -/
def IsRootMultiset (m : Dual K H →₀ ℕ) : Prop :=
  (∀ α ∈ m.support, α ∈ P.posWeights) ∧ ∀ α, m α ≤ finrank K (rootSpace P (-α))

omit [DecidableEq ι] [CharZero K] [FiniteDimensional K H] in
lemma sum_nsmul_mem_posWeights (s : Finset (Dual K H)) (f : Dual K H → ℕ)
    (hs : ∀ α ∈ s, α ∈ P.posWeights ∧ f α ≠ 0) (hne : s.Nonempty) :
    ∑ α ∈ s, f α • α ∈ P.posWeights := by
  classical
  have hn (α : Dual K H) (hα : α ∈ P.posWeights) (n : ℕ) (hn : n ≠ 0) : n • α ∈ P.posWeights := by
    induction n with
    | zero => exact absurd rfl hn
    | succ n ih =>
      rcases eq_or_ne n 0 with rfl | hn'
      · simpa using hα
      · rw [succ_nsmul]; exact P.posWeights_add (ih hn') hα
  induction hne using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hn a (hs a (by simp)).1 _ (hs a (by simp)).2
  | cons a s ha hs' ih =>
    rw [Finset.sum_cons]
    exact P.posWeights_add (hn a (hs a (by simp)).1 _ (hs a (by simp)).2)
      (ih fun α hα ↦ hs α (by simp [hα]))

omit [DecidableEq ι] [CharZero K] [FiniteDimensional K H] in
lemma msetWt_mem_posWeights {m : Dual K H →₀ ℕ} (hm : ∀ α ∈ m.support, α ∈ P.posWeights)
    (hne : m ≠ 0) : msetWt m ∈ P.posWeights :=
  sum_nsmul_mem_posWeights P _ _ (fun α hα ↦ ⟨hm α hα, Finsupp.mem_support_iff.mp hα⟩)
    (Finsupp.support_nonempty_iff.mpr hne)

omit [DecidableEq ι] [FiniteDimensional K H] in
lemma eq_zero_of_msetWt_eq_zero {m : Dual K H →₀ ℕ} (hm : ∀ α ∈ m.support, α ∈ P.posWeights)
    (h0 : msetWt m = 0) : m = 0 := by
  by_contra hne
  exact P.zero_notMem_posWeights (h0 ▸ msetWt_mem_posWeights P hm hne)

omit [DecidableEq ι] [CharZero K] [FiniteDimensional K H] in
lemma exists_msetWt_eq_rootOf {m : Dual K H →₀ ℕ} (hm : ∀ α ∈ m.support, α ∈ P.posWeights) :
    ∃ k : ι → ℤ, 0 ≤ k ∧ msetWt m = P.rootOf k := by
  rcases eq_or_ne m 0 with rfl | hne
  · exact ⟨0, le_rfl, by simp⟩
  · obtain ⟨k, hk, h⟩ := msetWt_mem_posWeights P hm hne
    exact ⟨k, hk.1, h.symm⟩


/-! ### Reflecting multisets of positive roots -/

section Reflect

omit [FiniteDimensional K H]

omit [DecidableEq ι] in
/-- The multiset `rᵢ ⋆ m`: remove the copies of `αᵢ` from `m`, apply `rᵢ` to the remaining roots
(which permutes `Δ₊ \ {αᵢ}`), and add `αᵢ` once if it did not occur in `m`. When `m(αᵢ) ≤ 1`,
`ρ - ⟨rᵢ ⋆ m⟩ = rᵢ (ρ - ⟨m⟩)` (`msetWt_reflectMset`). -/
def reflectMset (i : ι) (m : Dual K H →₀ ℕ) : Dual K H →₀ ℕ :=
  (m.erase (P.root i)).mapDomain (P.reflection hA i) + Finsupp.single (P.root i) (1 - m (P.root i))

variable {P}

omit [DecidableEq ι] in
lemma neg_root_notMem_posWeights (i : ι) : -P.root i ∉ P.posWeights := fun h ↦
  Set.disjoint_left.mp P.disjoint_posWeights_negWeights h (P.neg_root_mem_negWeights i)

omit [DecidableEq ι] in
lemma neg_root_ne_root (i : ι) : -P.root i ≠ P.root i := by
  intro h
  have h2 : (2 : K) • P.root i = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel _
  exact P.linearIndependent_root.ne_zero i ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

omit [DecidableEq ι] in
lemma reflectMset_apply_root {m : Dual K H →₀ ℕ} (hm : ∀ α ∈ m.support, α ∈ P.posWeights)
    (i : ι) : reflectMset P hA i m (P.root i) = 1 - m (P.root i) := by
  have h1 : (m.erase (P.root i)).mapDomain (P.reflection hA i) (P.root i) = 0 := by
    have := Finsupp.mapDomain_apply_of_injective (P.reflection hA i).injective
      (m.erase (P.root i)) (-P.root i)
    rw [map_neg, reflection_root_self, neg_neg] at this
    rw [this, Finsupp.erase_ne (neg_root_ne_root i)]
    by_contra h
    exact neg_root_notMem_posWeights i (hm _ (Finsupp.mem_support_iff.mpr h))
  rw [reflectMset, Finsupp.add_apply, h1, zero_add, Finsupp.single_eq_same]

omit [DecidableEq ι] in
lemma reflectMset_apply_neg_root (m : Dual K H →₀ ℕ) (i : ι) :
    reflectMset P hA i m (-P.root i) = 0 := by
  rw [reflectMset, Finsupp.add_apply, Finsupp.single_eq_of_ne (neg_root_ne_root i), add_zero,
    show -P.root i = P.reflection hA i (P.root i) by simp,
    Finsupp.mapDomain_apply_of_injective (P.reflection hA i).injective, Finsupp.erase_same]

omit [DecidableEq ι] [CharZero K] in
lemma reflectMset_apply {β : Dual K H} (i : ι) (m : Dual K H →₀ ℕ) (h1 : β ≠ P.root i)
    (h2 : β ≠ -P.root i) : reflectMset P hA i m β = m (P.reflection hA i β) := by
  have h3 : P.reflection hA i β ≠ P.root i := fun h ↦ h2 (by
    rw [← P.reflection_reflection hA i β, h, reflection_root_self])
  rw [reflectMset, Finsupp.add_apply, Finsupp.single_eq_of_ne h1, add_zero]
  conv_lhs => rw [← P.reflection_reflection hA i β]
  rw [Finsupp.mapDomain_apply_of_injective (P.reflection hA i).injective, Finsupp.erase_ne h3]

omit [Fintype ι] [DecidableEq ι] [CharZero K] in
lemma msetWt_eq_erase_add (m : Dual K H →₀ ℕ) (α : Dual K H) :
    msetWt m = msetWt (m.erase α) + m α • α := by
  conv_lhs => rw [← Finsupp.erase_add_single α m]
  rw [msetWt_add, msetWt_single]

omit [DecidableEq ι] [CharZero K] in
lemma msetWt_reflectMset (i : ι) (m : Dual K H →₀ ℕ) :
    msetWt (reflectMset P hA i m) =
      P.reflection hA i (msetWt (m.erase (P.root i))) + (1 - m (P.root i)) • P.root i := by
  rw [reflectMset, msetWt_add, msetWt_mapDomain, msetWt_single]

omit [Fintype ι] [DecidableEq ι] [CharZero K] in
lemma degree_erase_add (m : Dual K H →₀ ℕ) (α : Dual K H) :
    (m.erase α).degree + m α = m.degree := by
  conv_rhs => rw [← Finsupp.erase_add_single α m]
  rw [map_add, Finsupp.degree_single]

omit [DecidableEq ι] [CharZero K] in
lemma degree_reflectMset (i : ι) (m : Dual K H →₀ ℕ) :
    (reflectMset P hA i m).degree + m (P.root i) = m.degree + (1 - m (P.root i)) := by
  rw [reflectMset, map_add, Finsupp.degree_mapDomain, Finsupp.degree_single, add_right_comm,
    degree_erase_add]

/-- `rᵢ ⋆ m` is again a multiset of positive roots within the root multiplicities. -/
theorem IsRootMultiset.reflectMset {m : Dual K H →₀ ℕ} (hm : IsRootMultiset P m) (i : ι) :
    IsRootMultiset P (reflectMset P hA i m) := by
  have hmult (β : Dual K H) :
      finrank K (rootSpace P (-P.reflection hA i β)) = finrank K (rootSpace P (-β)) := by
    have := rank_rootSpace_weylGroup P hA (P.reflection_mem_weylGroup hA i) (-β)
    rw [map_neg] at this
    unfold Module.finrank
    rw [this]
  refine ⟨fun β hβ ↦ ?_, fun β ↦ ?_⟩
  · rw [Finsupp.mem_support_iff] at hβ
    by_cases h1 : β = P.root i
    · exact h1 ▸ P.root_mem_posWeights i
    by_cases h2 : β = -P.root i
    · exact absurd (h2 ▸ reflectMset_apply_neg_root hA m i) hβ
    rw [reflectMset_apply hA i m h1 h2] at hβ
    have hpos := hm.1 _ (Finsupp.mem_support_iff.mpr hβ)
    have hroot : P.reflection hA i β ∈ roots P := by
      refine ⟨fun h0 ↦ P.zero_notMem_posWeights (h0 ▸ hpos), fun hbot ↦ hβ ?_⟩
      have := hm.2 (P.reflection hA i β)
      rw [finrank_rootSpace_neg_eq P hpos, hbot, finrank_bot] at this
      omega
    have hne : P.reflection hA i β ≠ P.root i := fun h ↦ h2 (by
      rw [← P.reflection_reflection hA i β, h, reflection_root_self])
    simpa using reflection_mem_posWeights P hA hroot hpos hne
  · by_cases h1 : β = P.root i
    · subst h1
      rw [reflectMset_apply_root hA hm.1, finrank_rootSpace_neg_root]
      omega
    by_cases h2 : β = -P.root i
    · rw [h2, reflectMset_apply_neg_root]
      exact Nat.zero_le _
    rw [reflectMset_apply hA i m h1 h2, ← hmult]
    exact hm.2 _

end Reflect

/-! ### Kostant's lemma -/

section Kostant

variable {P}

omit [DecidableEq ι] in
include S in
/-- If `λ` is regular dominant integral (`⟨λ, αⱼ^∨⟩ ∈ ℤ_{>0}`), `w ∈ W` and `⟨wλ, αᵢ^∨⟩ > 0`,
then `w⁻¹ αᵢ > 0`. -/
lemma inv_apply_root_mem_posWeights {lam : Dual K H}
    (hlam : ∀ j, ∃ n : ℕ, lam (P.coroot j) = n + 1) (w : P.weylGroup hA) (i : ι) {p : ℤ}
    (hp : 0 < p) (hwp : (w : Dual K H ≃ₗ[K] Dual K H) lam (P.coroot i) = p) :
    ((w⁻¹ : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∈ P.posWeights := by
  choose n hn using hlam
  have key : P.dualBilinForm S lam (((w⁻¹ : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H)
      (P.root i)) = ((p / S.ε i : ℚ) : K) := by
    rw [← dualBilinForm_weylGroup P hA S w.2, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul,
      mul_inv_cancel, Subgroup.coe_one, LinearEquiv.coe_one, id, dualBilinForm_root_right, hwp]
    push_cast
    rfl
  rcases P.apply_root_nonneg_or_nonpos hA (w⁻¹).2 i with ⟨k, hk, hwk⟩ | ⟨k, hk, hwk⟩
  · refine ⟨k, ⟨hk, ?_⟩, hwk.symm⟩
    rintro rfl
    rw [map_zero, LinearEquiv.map_eq_zero_iff] at hwk
    exact P.linearIndependent_root.ne_zero i hwk
  · exfalso
    rw [hwk, map_neg, dualBilinForm_rootOf_right] at key
    simp only [hn] at key
    have hq : (-(∑ j, (k j : ℚ) * ((n j + 1 : ℚ) / S.ε j)) : ℚ) = p / S.ε i := by
      exact_mod_cast (show (((-(∑ j, (k j : ℚ) * ((n j + 1 : ℚ) / S.ε j)) : ℚ) : K)) =
        ((p / S.ε i : ℚ) : K) by rw [← key]; push_cast; rfl)
    have h1 : 0 ≤ ∑ j, (k j : ℚ) * ((n j + 1 : ℚ) / S.ε j) :=
      Finset.sum_nonneg fun j _ ↦ mul_nonneg (by exact_mod_cast hk j)
        (div_nonneg (by positivity) (S.ε_pos j).le)
    have h2 : (0 : ℚ) < p / S.ε i := div_pos (by exact_mod_cast hp) (S.ε_pos i)
    linarith

variable {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ) (Pw : Set (Dual K H))
  (hrefl : ∀ ν ∈ Pw, ∀ i, P.reflection hA i ν ∈ Pw)
  (hle : ∀ ν ∈ Pw, ∃ k : ι → ℤ, 0 ≤ k ∧ ν = Λ - P.rootOf k)

omit [DecidableEq ι] in
omit [CharZero K] [FiniteDimensional K H] in
include hle in
lemma exists_rootOf_of_mem {ν : Dual K H} (hν : ν ∈ Pw) {m : Dual K H →₀ ℕ}
    (hm : ∀ α ∈ m.support, α ∈ P.posWeights) :
    ∃ c : ι → ℤ, 0 ≤ c ∧ Λ + P.rho - (ν + P.rho - msetWt m) = P.rootOf c := by
  obtain ⟨k, hk, rfl⟩ := hle ν hν
  obtain ⟨k', hk', hmk⟩ := exists_msetWt_eq_rootOf P hm
  exact ⟨k + k', add_nonneg hk hk', by rw [map_add, ← hmk]; abel⟩

include S hΛ hrefl hle in
/-- The inductive step of Kostant's lemma, by induction on the height of `λ - φ`. -/
theorem exists_weylGroup_of_dualBilinForm_eq_aux (N : ℕ) :
    ∀ ν ∈ Pw, ∀ m : Dual K H →₀ ℕ, IsRootMultiset P m → ∀ c : ι → ℤ, 0 ≤ c → ∑ j, c j = N →
      Λ + P.rho - (ν + P.rho - msetWt m) = P.rootOf c →
      P.dualBilinForm S (ν + P.rho - msetWt m) (ν + P.rho - msetWt m) =
        P.dualBilinForm S (Λ + P.rho) (Λ + P.rho) →
      ∃ w : P.weylGroup hA, (w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) = ν + P.rho - msetWt m ∧
        (P.coxeterSystem hA).length w = m.degree ∧
        ∀ α ∈ m.support, ((w⁻¹ : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H) α ∈ P.negWeights := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro ν hν m hm c hc hcN hφ hform
  set φ := ν + P.rho - msetWt m with hφdef
  have hlam : ∀ j, ∃ n : ℕ, (Λ + P.rho) (P.coroot j) = n + 1 := fun j ↦ by
    obtain ⟨n, hn⟩ := hΛ j
    exact ⟨n, by rw [LinearMap.add_apply, hn, rho_coroot]⟩
  choose nn hnn using hlam
  have hφl : φ = Λ + P.rho - P.rootOf c := by rw [← hφ]; abel
  have hφcor (j : ι) : φ (P.coroot j) = ((nn j + 1 - (A *ᵥ c) j : ℤ) : K) := by
    rw [hφl, LinearMap.sub_apply, hnn, rootOf_apply_coroot]
    push_cast
    ring
  by_cases hdom : ∀ j, 0 ≤ (nn j + 1 - (A *ᵥ c) j : ℤ)
  · -- `φ` is dominant: then `φ = λ` and `m = 0`
    have hdiff : P.dualBilinForm S (Λ + P.rho) (Λ + P.rho) - P.dualBilinForm S φ φ =
        P.dualBilinForm S (Λ + P.rho + φ) (P.rootOf c) := by
      have hl : Λ + P.rho = φ + P.rootOf c := by rw [hφl]; abel
      rw [hl]
      simp only [map_add, LinearMap.add_apply]
      rw [(P.isSymm_dualBilinForm S).eq (P.rootOf c) φ]
      ring
    rw [hform, sub_self, dualBilinForm_rootOf_right] at hdiff
    have hq : ∑ j, (c j : ℚ) * ((2 * (nn j + 1) - (A *ᵥ c) j : ℤ) / S.ε j) = 0 := by
      have : ((∑ j, (c j : ℚ) * ((2 * (nn j + 1) - (A *ᵥ c) j : ℤ) / S.ε j) : ℚ) : K) = 0 := by
        rw [hdiff]
        push_cast
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [LinearMap.add_apply, hnn, hφcor]
        push_cast
        ring
      exact_mod_cast this
    have hterm (j : ι) : 0 ≤ (c j : ℚ) * ((2 * (nn j + 1) - (A *ᵥ c) j : ℤ) / S.ε j) := by
      have h : (0 : ℤ) < 2 * (nn j + 1) - (A *ᵥ c) j := by have := hdom j; omega
      exact mul_nonneg (by exact_mod_cast hc j)
        (div_nonneg (Int.cast_pos.mpr h).le (S.ε_pos j).le)
    have hc0 : c = 0 := by
      funext j
      have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hterm j).mp hq j (Finset.mem_univ j)
      have hpos : (0 : ℚ) < ((2 * (nn j + 1) - (A *ᵥ c) j : ℤ) / S.ε j) := by
        have h : (0 : ℤ) < 2 * (nn j + 1) - (A *ᵥ c) j := by have := hdom j; omega
        exact div_pos (Int.cast_pos.mpr h) (S.ε_pos j)
      exact_mod_cast (mul_eq_zero.mp hj).resolve_right hpos.ne'
    subst hc0
    have hφΛ : φ = Λ + P.rho := by rw [hφl, map_zero, sub_zero]
    have hm0 : m = 0 := by
      obtain ⟨k, hk, hνk⟩ := hle ν hν
      obtain ⟨k', hk', hmk⟩ := exists_msetWt_eq_rootOf P hm.1
      have h1 : Λ + P.rho - φ = 0 := hφ.trans (map_zero _)
      have h0 : P.rootOf (k + k') = 0 := by
        rw [map_add, ← hmk, ← h1, hφdef, hνk]
        abel
      rw [← map_zero P.rootOf] at h0
      have hkk := P.rootOf_injective h0
      have hk'0 : k' = 0 := funext fun j ↦ by
        have h1 := congrFun hkk j; have h2 := hk j; have h3 := hk' j
        simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 h3 ⊢
        omega
      exact eq_zero_of_msetWt_eq_zero P hm.1 (by rw [hmk, hk'0, map_zero])
    subst hm0
    exact ⟨1, by simpa using hφΛ.symm, by simp, by simp⟩
  · -- `⟨φ, αᵢ^∨⟩ < 0` for some `i`: reflect
    push Not at hdom
    obtain ⟨i, hi⟩ := hdom
    set p : ℤ := nn i + 1 - (A *ᵥ c) i with hp
    have hmi : m (P.root i) ≤ 1 := by
      have := hm.2 (P.root i)
      rwa [finrank_rootSpace_neg_root] at this
    set m' := reflectMset P hA i m with hm'
    have hrρ : P.reflection hA i P.rho = P.rho - P.root i := by
      rw [reflection_apply, rho_coroot, one_smul]
    have hφ' : P.reflection hA i ν + P.rho - msetWt m' = P.reflection hA i φ := by
      rw [hm', msetWt_reflectMset, hφdef, msetWt_eq_erase_add m (P.root i), map_sub, map_add,
        map_add, hrρ, map_nsmul, reflection_root_self]
      obtain h | h : m (P.root i) = 0 ∨ m (P.root i) = 1 := by omega
      · rw [h]; simp only [tsub_zero, one_smul, zero_smul, add_zero]; abel
      · rw [h]; simp only [tsub_self, zero_smul, one_smul, add_zero]; abel
    have hrφ : P.reflection hA i φ = φ - (p : K) • P.root i := by
      rw [reflection_apply, hφcor]
    have hc' : Λ + P.rho - (P.reflection hA i ν + P.rho - msetWt m') =
        P.rootOf (c + p • Pi.single i 1) := by
      rw [hφ', hrφ, map_add, map_zsmul, rootOf_single, ← Int.cast_smul_eq_zsmul K, hφl]
      abel
    obtain ⟨c'', hc''0, hc''⟩ := exists_rootOf_of_mem Pw hle (hrefl ν hν i)
      (hm.reflectMset hA i).1
    rw [← hm', hc'] at hc''
    have hc'0 : 0 ≤ c + p • Pi.single i 1 := (P.rootOf_injective hc'').symm ▸ hc''0
    have hsum : ∑ j, (c + p • Pi.single i 1 : ι → ℤ) j = N + p := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, hcN]
      simp [Pi.single_apply]
    have hsum0 : 0 ≤ ∑ j, (c + p • Pi.single i 1 : ι → ℤ) j :=
      Finset.sum_nonneg fun j _ ↦ hc'0 j
    have hlt : (N + p).toNat < N := by omega
    have hform' : P.dualBilinForm S (P.reflection hA i ν + P.rho - msetWt m')
        (P.reflection hA i ν + P.rho - msetWt m') = P.dualBilinForm S (Λ + P.rho) (Λ + P.rho) := by
      rw [hφ', dualBilinForm_reflection, hform]
    obtain ⟨w', hw'l, hw'len, hw'inv⟩ := ih _ hlt _ (hrefl ν hν i) m'
      (hm.reflectMset hA i) _ hc'0 (by rw [hsum]; omega) hc' hform'
    -- `w'⁻¹ αᵢ > 0`
    have hpos : ((w'⁻¹ : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∈
        P.posWeights := by
      refine inv_apply_root_mem_posWeights hA S (fun j ↦ ⟨nn j, hnn j⟩) w' i (p := -p)
        (by omega) ?_
      rw [hw'l, hφ', hrφ, LinearMap.sub_apply, hφcor, LinearMap.smul_apply,
        P.root_coroot_self hA i, hp]
      push_cast
      ring
    have hm'i : m' (P.root i) = 0 := by
      by_contra h
      exact Set.disjoint_left.mp P.disjoint_posWeights_negWeights hpos
        (hw'inv _ (Finsupp.mem_support_iff.mpr h))
    rw [hm', reflectMset_apply_root hA hm.1] at hm'i
    have hmi1 : m (P.root i) = 1 := by omega
    have hdeg := degree_reflectMset (P := P) hA i m
    rw [← hm', hmi1] at hdeg
    refine ⟨(P.coxeterSystem hA).simple i * w', ?_, ?_, fun α hα ↦ ?_⟩
    · rw [Subgroup.coe_mul, coxeterSystem_simple, LinearEquiv.mul_apply, hw'l, hφ',
        reflection_reflection]
    · have hnd : ¬(P.coxeterSystem hA).IsRightDescent w'⁻¹ i :=
        (apply_root_mem_posWeights_iff P hA).mp hpos
      rw [(P.coxeterSystem hA).not_isRightDescent_iff] at hnd
      rw [← (P.coxeterSystem hA).length_inv, _root_.mul_inv_rev, (P.coxeterSystem hA).inv_simple,
        hnd, (P.coxeterSystem hA).length_inv, hw'len]
      omega
    · rw [_root_.mul_inv_rev, (P.coxeterSystem hA).inv_simple, Subgroup.coe_mul,
        coxeterSystem_simple, LinearEquiv.mul_apply]
      have hαpos := hm.1 α hα
      by_cases hαi : α = P.root i
      · subst hαi
        rw [reflection_root_self, map_neg]
        exact (neg_mem_negWeights_iff P).mpr hpos
      have hαi' : α ≠ -P.root i := fun h ↦ neg_root_notMem_posWeights i (h ▸ hαpos)
      have h1 : P.reflection hA i α ≠ P.root i := fun h ↦ hαi' (by
        rw [← P.reflection_reflection hA i α, h, reflection_root_self])
      have h2 : P.reflection hA i α ≠ -P.root i := fun h ↦ hαi (by
        rw [← P.reflection_reflection hA i α, h, map_neg, reflection_root_self, neg_neg])
      refine hw'inv _ (Finsupp.mem_support_iff.mpr ?_)
      rw [hm', reflectMset_apply hA i m h1 h2, reflection_reflection]
      exact Finsupp.mem_support_iff.mp hα

include S hΛ hrefl hle in
/-- **Kostant's lemma** (combinatorial form; [Kum] Lemma 3.2.? (check), Kostant 1961 §5 (check)
in finite type; reconstructed for Kac–Moody algebras): let `Λ` be dominant integral, `Pw` a
`W`-invariant set of weights `≤ Λ` (e.g. the weights of `L(Λ)`), `ν ∈ Pw` and `m` a multiset of
positive roots within the root multiplicities. If `φ = ν + ρ - ⟨m⟩` satisfies
`(φ | φ) = (Λ + ρ | Λ + ρ)`, then `φ = w(Λ + ρ)` for some `w ∈ W` with `ℓ(w) = |m|`. -/
theorem exists_weylGroup_of_dualBilinForm_eq {ν : Dual K H} (hν : ν ∈ Pw)
    {m : Dual K H →₀ ℕ} (hm : IsRootMultiset P m)
    (hform : P.dualBilinForm S (ν + P.rho - msetWt m) (ν + P.rho - msetWt m) =
      P.dualBilinForm S (Λ + P.rho) (Λ + P.rho)) :
    ∃ w : P.weylGroup hA, (w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) = ν + P.rho - msetWt m ∧
      (P.coxeterSystem hA).length w = m.degree := by
  obtain ⟨c, hc, hφ⟩ := exists_rootOf_of_mem Pw hle hν hm.1
  obtain ⟨w, hw, hlen, -⟩ := exists_weylGroup_of_dualBilinForm_eq_aux hA S hΛ Pw hrefl hle
    (∑ j, c j).toNat ν hν m hm c hc (Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ ↦ hc j)).symm
    hφ hform
  exact ⟨w, hw, hlen⟩

end Kostant

/-! ### Multisets of roots of wedge monomials -/

section Finset

omit [FiniteDimensional K H]

omit [Fintype ι] [DecidableEq ι] [CharZero K] in
lemma msetWt_sum {κ : Type*} (s : Finset κ) (f : κ → Dual K H →₀ ℕ) :
    msetWt (∑ x ∈ s, f x) = ∑ x ∈ s, msetWt (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, msetWt_add, ih]

omit [CharZero K] in
/-- The multiset of roots `{x.root | x ∈ S}` of a set `S` of indices of the root vector basis
of `𝔫₋`. -/
def finsetMset (S : Finset (NegRootIndex P)) : Dual K H →₀ ℕ :=
  ∑ x ∈ S, Finsupp.single x.root 1

variable {P}

omit [CharZero K] in
@[simp] lemma msetWt_finsetMset (S : Finset (NegRootIndex P)) :
    msetWt (finsetMset P S) = finsetWt P S := by
  simp [finsetMset, msetWt_sum, finsetWt]

omit [CharZero K] in
@[simp] lemma degree_finsetMset (S : Finset (NegRootIndex P)) :
    (finsetMset P S).degree = S.card := by
  simp [finsetMset, map_sum]

omit [CharZero K] in
open Classical in
lemma finsetMset_apply (S : Finset (NegRootIndex P)) (α : Dual K H) :
    finsetMset P S α = (S.filter fun x : NegRootIndex P ↦ x.root = α).card := by
  classical
  simp only [finsetMset, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.card_filter]

omit [CharZero K] in
open Classical in
lemma card_filter_root_le (S : Finset (NegRootIndex P)) (α : Dual K H) :
    (S.filter fun x : NegRootIndex P ↦ x.root = α).card ≤ finrank K (rootSpace P (-α)) := by
  classical
  rw [← Finset.card_range (finrank K (rootSpace P (-α)))]
  refine Finset.card_le_card_of_injOn (fun x ↦ (x.2 : ℕ)) (fun x hx ↦ ?_) fun x hx y hy hxy ↦ ?_
  · obtain ⟨-, hx⟩ := Finset.mem_filter.mp hx
    have := x.2.2
    simp only [Finset.coe_range, Set.mem_Iio]
    rwa [← hx]
  · obtain ⟨-, hx⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    obtain ⟨-, hy⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
    have h1 : x.1 = y.1 := Subtype.ext (hx.trans hy.symm)
    exact Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).mpr hxy)

omit [CharZero K] in
/-- The roots of a wedge monomial of root vectors form a multiset of roots. -/
theorem isRootMultiset_finsetMset (S : Finset (NegRootIndex P)) :
    IsRootMultiset P (finsetMset P S) := by
  classical
  refine ⟨fun α hα ↦ ?_, fun α ↦ (finsetMset_apply S α).trans_le (card_filter_root_le S α)⟩
  rw [Finsupp.mem_support_iff, finsetMset_apply, Ne, Finset.card_eq_zero] at hα
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hα
  rw [← (Finset.mem_filter.mp hx).2]
  exact x.1.2

end Finset

/-! ### The weights of `L(Λ)` and of its `𝔫₋`-homology -/

namespace IrreducibleModule

variable {P} {Λ : Dual K H}

omit [FiniteDimensional K H] in
include hA in
/-- The weights of `L(Λ)`, `Λ` dominant integral, are permuted by `W` ([Kac] Prop. 3.7
(check)). -/
lemma reflection_mem_weights (hΛ : P.IsDominantIntegral Λ) {ν : Dual K H}
    (hν : weightSpace P (IrreducibleModule P Λ) ν ≠ ⊥) (i : ι) :
    weightSpace P (IrreducibleModule P Λ) (P.reflection hA i ν) ≠ ⊥ := by
  have hV := (isIntegrable_iff P hA).mpr hΛ
  have := rank_weightSpace_weylGroup hA hV (P.reflection_mem_weylGroup hA i) ν
  rw [Ne, ← Submodule.rank_eq_zero, this, Submodule.rank_eq_zero]
  exact hν

omit [CharZero K] [FiniteDimensional K H] in
/-- The weights of `L(Λ)` are `≤ Λ`. -/
lemma exists_eq_sub_of_weightSpace_ne_bot {ν : Dual K H}
    (hν : weightSpace P (IrreducibleModule P Λ) ν ≠ ⊥) :
    ∃ k : ι → ℤ, 0 ≤ k ∧ ν = Λ - P.rootOf k := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hν
  exact VermaModule.exists_eq_sub_of_mem_weightSpace P Λ (LieSubmodule.Quotient.mk' _)
    (LieSubmodule.Quotient.surjective_mk' _) hx hx0

/-- **Kostant's lemma for `𝔫₋`-homology** ([Kum] Lemma 3.2.? (check); Kostant 1961, §5
(check), in finite type): if `H_k(𝔫₋, L(Λ))_μ ≠ 0`, `Λ` dominant integral, and
`(μ + ρ | μ + ρ) = (Λ + ρ | Λ + ρ)`, then `μ = w(Λ + ρ) - ρ` for some `w ∈ W` of length `k`.
(The weights of `C_k(𝔫₋, L(Λ))` are `ν - (β₁ + ⋯ + β_k)` with `ν` a weight of `L(Λ)` and the `βⱼ`
roots of distinct elements of a basis of root vectors of `𝔫₋`;
`exists_weylGroup_of_dualBilinForm_eq` applies.) -/
theorem exists_weylGroup_of_homologyWeightSpace_ne_bot_of_eq (hΛ : P.IsDominantIntegral Λ)
    {k : ℕ} {μ : Dual K H}
    (h : (nNegDerivAction P (IrreducibleModule P Λ)).homologyWeightSpace k μ ≠ ⊥)
    (hform : P.dualBilinForm S (μ + P.rho) (μ + P.rho) =
      P.dualBilinForm S (Λ + P.rho) (Λ + P.rho)) :
    ∃ w : P.weylGroup hA, (P.coxeterSystem hA).length w = k ∧
      (w : Dual K H ≃ₗ[K] Dual K H) (Λ + P.rho) - P.rho = μ := by
  obtain ⟨T, hT, hne⟩ := (isCategoryO P Λ).exists_of_homologyWeightSpace_ne_bot h
  have hφ : μ + finsetWt P T + P.rho - msetWt (finsetMset P T) = μ + P.rho := by
    rw [msetWt_finsetMset]; abel
  obtain ⟨w, hw, hlen⟩ := exists_weylGroup_of_dualBilinForm_eq hA S hΛ
    {ν | weightSpace P (IrreducibleModule P Λ) ν ≠ ⊥}
    (fun ν hν i ↦ reflection_mem_weights hA hΛ hν i)
    (fun ν hν ↦ exists_eq_sub_of_weightSpace_ne_bot hν) hne (isRootMultiset_finsetMset T)
    (by rw [hφ, hform])
  refine ⟨w, by rw [hlen, degree_finsetMset, hT], ?_⟩
  rw [hw, hφ, add_sub_cancel_right]

end IrreducibleModule

end KacMoodyAlgebra

end Matrix.Realization
