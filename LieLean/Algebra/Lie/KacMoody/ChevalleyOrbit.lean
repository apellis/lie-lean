/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TracePower
import LieLean.Algebra.Lie.KacMoody.VermaHomFiniteType

/-!
# Finite dominance inversion for distinct Weyl orbits

## Main results
Finite dominance inversion and invariant homogeneous extensions of orbit powers.

## References
Etingof, MIT 18.757 (Fall 2023), Lecture 10, equation (6) and Theorem 10.1(ii).
The finite cone bound and finite-poset induction below reconstruct the inversion step.
-/

noncomputable section
open Module

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

/-- The Weyl-saturated lower cone of a highest weight. -/
def orbitLowerCone (Λ : Dual K H) : Set (Dual K H) :=
  {μ | ∀ w : P.weylGroup hA.isGeneralizedCartan, w.val μ ∈ cone P Λ}

omit [FiniteDimensional K H] in
/-- Every Weyl translate of a dominant integral weight lies below it. -/
theorem dominant_mem_orbitLowerCone {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ) :
    Λ ∈ orbitLowerCone P hA Λ := by
  intro w
  obtain ⟨k, hk, he⟩ := P.exists_sub_apply_eq_rootOf hA.isGeneralizedCartan hΛ w
  exact ⟨k, hk, by rw [← he]; abel⟩

/-- The saturated lower cone is finite, by summing its root coefficients over the finite
Weyl group. This supplies the actual finite induction domain, not a finiteness premise. -/
theorem finite_orbitLowerCone (Λ : Dual K H) (hΛ : P.IsDominantIntegral Λ) :
    (orbitLowerCone P hA Λ).Finite := by
  classical
  have := P.finite_weylGroup hA
  let : Fintype (P.weylGroup hA.isGeneralizedCartan) := Fintype.ofFinite _
  have key : ∀ μ ∈ orbitLowerCone P hA Λ, ∃ k κ : ι → ℤ, 0 ≤ k ∧
      k ≤ κ ∧ μ = Λ - P.rootOf k ∧
      P.rootOf κ = Fintype.card (P.weylGroup hA.isGeneralizedCartan) • Λ := by
    intro μ hμ
    choose k hk0 hk using hμ
    refine ⟨k 1, ∑ w, k w, hk0 1,
      Finset.single_le_sum (fun w _ ↦ hk0 w) (Finset.mem_univ 1),
      by simpa using hk 1, ?_⟩
    have hs : ∑ w, P.rootOf (k w) =
        ∑ w : P.weylGroup hA.isGeneralizedCartan, (Λ - w.val μ) :=
      Finset.sum_congr rfl fun w _ ↦ by rw [hk w]; abel
    rw [map_sum, hs, Finset.sum_sub_distrib, sum_weylGroup_apply_eq_zero hA,
      sub_zero, Finset.sum_const, Finset.card_univ]
  obtain ⟨_, κ, _, _, _, hκ⟩ := key Λ (dominant_mem_orbitLowerCone P hA hΛ)
  have hf : (Set.univ.pi fun i ↦ Set.Icc (0 : ℤ) (κ i)).Finite :=
    Set.Finite.pi fun _ ↦ Set.finite_Icc _ _
  refine (hf.image fun k ↦ Λ - P.rootOf k).subset ?_
  intro μ hμ
  obtain ⟨k, κ', hk0, hkk, he, hκ'⟩ := key μ hμ
  have : κ' = κ := P.rootOf_injective (hκ'.trans hκ.symm)
  subst κ'
  exact ⟨k, Set.mem_univ_pi.mpr fun i ↦ ⟨hk0 i, hkk i⟩, he.symm⟩

/-- Actual multiplicities, viewed in the coefficient field. -/
def orbitCharacter (Λ μ : Dual K H) : K :=
  (finrank K (weightSpace P (IrreducibleModule P Λ) μ) : K)

omit [FiniteDimensional K H] in
/-- Actual character multiplicities are Weyl invariant. -/
theorem orbitCharacter_weyl {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
    (w : P.weylGroup hA.isGeneralizedCartan) (μ : Dual K H) :
    orbitCharacter P Λ (w.val μ) = orbitCharacter P Λ μ := by
  have he := IrreducibleModule.isWeylInvariant_character hA.isGeneralizedCartan hΛ
    w.val w.property μ
  simp only [IsCategoryO.coeffAt_character, Nat.cast_inj] at he
  exact congrArg (Nat.cast : ℕ → K) he

omit [FiniteDimensional K H] in
/-- Lower-cone support of the actual character. -/
theorem orbitCharacter_mem_cone {Λ μ : Dual K H} (hμ : orbitCharacter P Λ μ ≠ 0) :
    μ ∈ cone P Λ :=
  IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero
    (by simpa only [orbitCharacter, Nat.cast_ne_zero] using hμ)

omit [FiniteDimensional K H] in
/-- Characters below a dominant highest weight have support in its saturated lower cone. -/
theorem orbitCharacter_support {Λ μ ν : Dual K H} (hμ : P.IsDominantIntegral μ)
    (hm : μ ∈ cone P Λ) (hν : orbitCharacter P μ ν ≠ 0) :
    ν ∈ orbitLowerCone P hA Λ := by
  intro w
  exact mem_cone_trans (orbitCharacter_mem_cone P
    (by rwa [orbitCharacter_weyl P hA hμ w])) hm

omit [DecidableEq ι] [CharZero K] [FiniteDimensional K H] in
/-- A lower-cone weight of an integral dominant weight is integral. -/
theorem integral_of_mem_cone {Λ μ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
    (hμ : μ ∈ cone P Λ) : ∀ i, ∃ z : ℤ, μ (P.coroot i) = z := by
  obtain ⟨k, _, rfl⟩ := hμ
  intro i
  obtain ⟨n, hn⟩ := hΛ i
  refine ⟨(n : ℤ) - (A *ᵥ k) i, ?_⟩
  simp only [LinearMap.sub_apply, hn, P.rootOf_apply_coroot, Int.cast_sub, Int.cast_natCast]

end Matrix.Realization.KacMoodyAlgebra

namespace FiniteDominance

variable {J K : Type*} [Finite J] [PartialOrder J] [Field K]

/-- Unitriangular finite-poset families are independent. The proof is well-founded
induction on the genuine finite partial order; no triangular inversion is assumed. -/
theorem independent (m : J → J → K) (hd : ∀ i, m i i = 1)
    (ht : ∀ i j, m i j ≠ 0 → i ≤ j) : LinearIndependent K m := by
  classical
  let := Fintype.ofFinite J
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hh : ∀ j, c j = 0 := by
    intro j
    induction j using (Finite.wellFounded_of_trans_of_irrefl
      (fun a b : J ↦ a < b)).induction with
    | h j ih =>
      have he := congrFun hc j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
      rw [Finset.sum_eq_single j] at he
      · simpa only [hd, mul_one] using he
      · intro i _ hij
        by_cases hm : m i j = 0
        · simp [hm]
        · rw [ih i (lt_of_le_of_ne (ht i j hm) hij), zero_mul]
      · simp
  exact hh

variable [Fintype J]

/-- Finite unitriangular inversion over a ring, including the empty index type.
Descending finite-poset induction expresses each coordinate vector using the given
rows. In particular this construction preserves integer coefficients. -/
theorem exists_coefficients {R : Type*} [CommRing R]
    (m : J → J → R) (hd : ∀ i, m i i = 1)
    (ht : ∀ i j, m i j ≠ 0 → i ≤ j) (f : J → R) :
    ∃ c : J → R, ∀ j, f j = ∑ i, c i * m i j := by
  classical
  let U := Submodule.span R (Set.range m)
  have hsingle : ∀ i, Pi.single i (1 : R) ∈ U := by
    intro i
    induction i using (Finite.wellFounded_of_trans_of_irrefl
      (fun a b : J ↦ b < a)).induction with
    | h i ih =>
      have he : Pi.single i (1 : R) = m i -
          ∑ j ∈ Finset.univ.erase i, m i j • Pi.single j (1 : R) := by
        ext j
        simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
        by_cases hij : i = j
        · subst j
          rw [Pi.single_eq_same, hd]
          have hz : (∑ x ∈ Finset.univ.erase i,
              m i x * (Pi.single x (1 : R) : J → R) i) = 0 := by
            apply Finset.sum_eq_zero
            intro x hx
            simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hx).symm]
          simp only [smul_eq_mul, hz, sub_zero]
        · rw [Pi.single_eq_of_ne (Ne.symm hij)]
          rw [Finset.sum_eq_single j]
          · simp
          · intro x _ hxj
            simp [Pi.single_eq_of_ne hxj.symm]
          · simp [Ne.symm hij]
      rw [he]
      apply U.sub_mem (Submodule.subset_span (Set.mem_range_self i))
      apply Submodule.sum_mem
      intro j hj
      by_cases hm : m i j = 0
      · simp [hm]
      · exact U.smul_mem _ (ih j (lt_of_le_of_ne (ht i j hm)
          (Finset.ne_of_mem_erase hj).symm))
  have hf : f ∈ U := by
    have he : f = ∑ i, f i • Pi.single i (1 : R) := by
      ext j
      simp [Pi.single_apply]
    rw [he]
    exact U.sum_mem fun i _ ↦ U.smul_mem _ (hsingle i)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hf
  exact ⟨c, fun j ↦ by simpa using (congrFun hc j).symm⟩

end FiniteDominance

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

/-- Distinct orbit weights, not a list indexed by all Weyl group elements. -/
def distinctWeylOrbit (Λ : Dual K H) : Finset (Dual K H) := by
  classical
  have := P.finite_weylGroup hA
  exact (Set.finite_range fun w : P.weylGroup hA.isGeneralizedCartan ↦ w.val Λ).toFinset

omit [FiniteDimensional K H] in
/-- Membership in the distinct orbit. -/
theorem mem_distinctWeylOrbit (Λ ν : Dual K H) :
    ν ∈ distinctWeylOrbit P hA Λ ↔
      ∃ w : P.weylGroup hA.isGeneralizedCartan, w.val Λ = ν := by
  classical
  simp [distinctWeylOrbit]

omit [FiniteDimensional K H] in
/-- The orbit set is Weyl stable. -/
theorem mem_distinctWeylOrbit_weyl (Λ ν : Dual K H)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    w.val ν ∈ distinctWeylOrbit P hA Λ ↔ ν ∈ distinctWeylOrbit P hA Λ := by
  rw [mem_distinctWeylOrbit, mem_distinctWeylOrbit]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨w⁻¹ * v, by change w.val.symm (v.val Λ) = ν; rw [hv]; simp⟩
  · rintro ⟨v, rfl⟩
    exact ⟨w * v, rfl⟩

omit [FiniteDimensional K H] in
/-- The orbit lies in the finite saturated lower cone. -/
theorem distinctWeylOrbit_subset {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ) :
    ↑(distinctWeylOrbit P hA Λ) ⊆ orbitLowerCone P hA Λ := by
  intro ν hν
  obtain ⟨v, rfl⟩ := (mem_distinctWeylOrbit P hA Λ ν).mp hν
  intro w
  exact dominant_mem_orbitLowerCone P hA hΛ (w * v)

include hA in
/-- The finite set of dominant weights below a dominant integral weight. -/
theorem finite_dominantBelow (Λ : Dual K H) (hΛ : P.IsDominantIntegral Λ) :
    {μ | P.IsDominantIntegral μ ∧ μ ∈ cone P Λ}.Finite := by
  classical
  refine (finite_orbitLowerCone P hA Λ hΛ).subset ?_
  intro μ hμ w
  exact mem_cone_trans (dominant_mem_orbitLowerCone P hA hμ.1 w) hμ.2

omit [FiniteDimensional K H] in
/-- Dominant representatives of a distinct orbit are unique, including singular weights. -/
theorem eq_of_dominant_mem_distinctWeylOrbit {μ ν : Dual K H}
    (hμ : P.IsDominantIntegral μ) (hν : P.IsDominantIntegral ν)
    (hm : ν ∈ distinctWeylOrbit P hA μ) : ν = μ := by
  obtain ⟨w, rfl⟩ := (mem_distinctWeylOrbit P hA μ ν).mp hm
  exact P.apply_eq_self_of_dominant hA.isGeneralizedCartan hμ w.property hν

open Classical in
/-- The finite dominance-triangular expansion into distinct orbit indicators.
Its coefficient at the highest orbit is the actual highest multiplicity, equal to one;
all other representatives lie strictly below it in dominance order. -/
theorem character_eq_sum_distinctOrbit (Λ : Dual K H) (hΛ : P.IsDominantIntegral Λ)
    (ν : Dual K H) :
    orbitCharacter P Λ ν =
      ∑ μ ∈ (finite_dominantBelow P hA Λ hΛ).toFinset,
        orbitCharacter P Λ μ * (if ν ∈ distinctWeylOrbit P hA μ then (1 : K) else 0) := by
  classical
  have := P.finite_weylGroup hA
  by_cases hn : ν ∈ orbitLowerCone P hA Λ
  · obtain ⟨w, hw⟩ := P.exists_dominantIntegral_weylGroup hA.isGeneralizedCartan
      (integral_of_mem_cone P hΛ (by simpa using hn 1))
    have hm : w.val ν ∈ (finite_dominantBelow P hA Λ hΛ).toFinset := by
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨hw, hn w⟩
    rw [Finset.sum_eq_single (w.val ν)]
    · have ho : ν ∈ distinctWeylOrbit P hA (w.val ν) :=
        (mem_distinctWeylOrbit P hA _ _).mpr ⟨w⁻¹, by simp⟩
      simp only [ho, ite_true, mul_one, orbitCharacter_weyl P hA hΛ w ν]
    · intro μ hμ hne
      have hμ' := (Set.Finite.mem_toFinset _).mp hμ
      have ho : ν ∉ distinctWeylOrbit P hA μ := by
        intro ho
        have he := eq_of_dominant_mem_distinctWeylOrbit P hA hμ'.1 hw
          ((mem_distinctWeylOrbit_weyl P hA μ ν w).mpr ho)
        exact hne he.symm
      simp [ho]
    · exact fun hnot ↦ (hnot hm).elim
  · have hz : orbitCharacter P Λ ν = 0 := by
      by_contra hz
      exact hn (orbitCharacter_support P hA hΛ (mem_cone_self Λ) hz)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro μ hμ
    have hμ' := (Set.Finite.mem_toFinset _).mp hμ
    have ho : ν ∉ distinctWeylOrbit P hA μ := by
      intro ho
      exact hn (fun w ↦ mem_cone_trans (distinctWeylOrbit_subset P hA hμ'.1 ho w) hμ'.2)
    simp [ho]

omit [FiniteDimensional K H] in
/-- The diagonal of the character/orbit transition matrix is exactly one. -/
theorem orbitCharacter_self (Λ : Dual K H) : orbitCharacter P Λ Λ = 1 := by
  simp [orbitCharacter, IrreducibleModule.finrank_weightSpace_self]

omit [FiniteDimensional K H] in
/-- Every off-diagonal nonzero multiplicity lies strictly lower in dominance.
`WeightOrd` is the production reverse-dominance order. -/
theorem orbitCharacter_strict {Λ μ : Dual K H} (hne : μ ≠ Λ)
    (hm : orbitCharacter P Λ μ ≠ 0) :
    WeightOrd.toWeightOrd P Λ < WeightOrd.toWeightOrd P μ := by
  apply lt_of_le_of_ne
  · exact (WeightOrd.toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr
      (orbitCharacter_mem_cone P hm)
  · exact fun he ↦ hne ((WeightOrd.toWeightOrd P).injective he).symm

open Classical in
/-- Equation (6) at the level of actual multiplicity functions: the distinct orbit
indicator is a finite linear combination of characters of actual dominant `L(μ)`,
with every `μ` below `Λ`. Finiteness, unit diagonal and dominance triangularity are proved.
The finite-poset induction above constructs the inverse; it is not an input assumption. -/
theorem exists_distinctOrbit_character_inversion (Λ : Dual K H)
    (hΛ : P.IsDominantIntegral Λ) :
    ∃ (S : Finset (Dual K H)) (c : Dual K H → ℤ),
      (∀ μ ∈ S, P.IsDominantIntegral μ ∧ μ ∈ cone P Λ) ∧
      ∀ ν, (if ν ∈ distinctWeylOrbit P hA Λ then (1 : K) else 0) =
        ∑ μ ∈ S, (c μ : K) * orbitCharacter P μ ν := by
  classical
  have := P.finite_weylGroup hA
  let D := {μ : Dual K H // P.IsDominantIntegral μ ∧ μ ∈ cone P Λ}
  have : Finite D := finite_dominantBelow P hA Λ hΛ
  let : Fintype D := Fintype.ofFinite D
  let : PartialOrder D := PartialOrder.lift
    (fun μ ↦ WeightOrd.toWeightOrd P μ.val)
    (fun _ _ he ↦ Subtype.ext ((WeightOrd.toWeightOrd P).injective he))
  obtain ⟨c, hcZ⟩ := FiniteDominance.exists_coefficients
    (fun μ ν : D ↦ (finrank K (weightSpace P (IrreducibleModule P μ.val) ν.val) : ℤ))
    (fun μ ↦ by simp [IrreducibleModule.finrank_weightSpace_self])
    (fun μ ν hn ↦
      (WeightOrd.toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr
        (IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero (by exact_mod_cast hn)))
    (fun ν : D ↦ if ν.val ∈ distinctWeylOrbit P hA Λ then (1 : ℤ) else 0)
  have hc (ν : D) : (if ν.val ∈ distinctWeylOrbit P hA Λ then (1 : K) else 0) =
      ∑ μ : D, (c μ : K) * orbitCharacter P μ.val ν.val := by
    have he := congrArg (Int.cast : ℤ → K) (hcZ ν)
    simpa only [Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_sum, Int.cast_mul,
      Int.cast_natCast, orbitCharacter] using he
  let S := (finite_dominantBelow P hA Λ hΛ).toFinset
  let c' : Dual K H → ℤ := fun μ ↦ if hm : μ ∈ S then c ⟨μ, by simpa [S] using hm⟩ else 0
  have hs (ν : Dual K H) :
      (∑ μ ∈ S, (c' μ : K) * orbitCharacter P μ ν) =
        ∑ μ : D, (c μ : K) * orbitCharacter P μ.val ν := by
    symm
    apply Finset.sum_bij (fun μ _ ↦ μ.val)
    · intro μ _
      simp [S]
    · intro μ _ μ' _ he
      exact Subtype.ext he
    · intro μ hm
      exact ⟨⟨μ, by simpa [S] using hm⟩, Finset.mem_univ _, rfl⟩
    · intro μ _
      simp only [c', show μ.val ∈ S by simp [S], dite_true]
      rfl
  refine ⟨S, c', fun μ hm ↦ by simpa [S] using hm, fun ν ↦ ?_⟩
  rw [hs]
  by_cases hn : ν ∈ orbitLowerCone P hA Λ
  · have hi : ∀ i, ∃ z : ℤ, ν (P.coroot i) = z :=
      integral_of_mem_cone P hΛ (by simpa using hn 1)
    obtain ⟨w, hw⟩ := P.exists_dominantIntegral_weylGroup hA.isGeneralizedCartan hi
    have he := hc ⟨w.val ν, hw, hn w⟩
    simp only [mem_distinctWeylOrbit_weyl P hA Λ ν w] at he
    exact he.trans (Finset.sum_congr rfl fun μ _ ↦
      congrArg ((c μ : K) * ·) (orbitCharacter_weyl P hA μ.property.1 w ν))
  · have ho : ν ∉ distinctWeylOrbit P hA Λ :=
      fun hv ↦ hn (distinctWeylOrbit_subset P hA hΛ hv)
    rw [ite_eq_right_iff.mpr fun hv ↦ (ho hv).elim]
    symm
    apply Finset.sum_eq_zero
    intro μ _
    have hz : orbitCharacter P μ.val ν = 0 := by
      by_contra hz
      exact hn (orbitCharacter_support P hA μ.property.1 μ.property.2 hz)
    rw [hz, mul_zero]


open Classical in
/-- The inverse is unitriangular as well: the highest character occurs with integer
coefficient one, and all remaining indices are strictly below it. -/
theorem exists_normalized_distinctOrbit_character_inversion (Λ : Dual K H)
    (hΛ : P.IsDominantIntegral Λ) :
    ∃ (S : Finset (Dual K H)) (c : Dual K H → ℤ),
      Λ ∈ S ∧ c Λ = 1 ∧
      (∀ μ ∈ S, P.IsDominantIntegral μ ∧ μ ∈ cone P Λ) ∧
      (∀ μ ∈ S, μ ≠ Λ →
        WeightOrd.toWeightOrd P Λ < WeightOrd.toWeightOrd P μ) ∧
      ∀ ν, (if ν ∈ distinctWeylOrbit P hA Λ then (1 : K) else 0) =
        ∑ μ ∈ S, (c μ : K) * orbitCharacter P μ ν := by
  classical
  obtain ⟨S, c, hS, hc⟩ := exists_distinctOrbit_character_inversion P hA Λ hΛ
  have hz (μ : Dual K H) (hm : μ ∈ S) (hne : μ ≠ Λ) :
      orbitCharacter P μ Λ = 0 := by
    by_contra hn
    have hle := (WeightOrd.toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr
      (hS μ hm).2
    have hle' := (WeightOrd.toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr
      (orbitCharacter_mem_cone P hn)
    exact hne ((WeightOrd.toWeightOrd P).injective (le_antisymm hle' hle))
  have ho : Λ ∈ distinctWeylOrbit P hA Λ :=
    (mem_distinctWeylOrbit P hA Λ Λ).mpr ⟨1, rfl⟩
  have he := hc Λ
  simp only [ho, ite_true] at he
  have hmem : Λ ∈ S := by
    by_contra hn
    have hzero : (∑ μ ∈ S, (c μ : K) * orbitCharacter P μ Λ) = 0 :=
      Finset.sum_eq_zero fun μ hm ↦ by rw [hz μ hm (fun heq ↦ hn (heq ▸ hm)), mul_zero]
    exact one_ne_zero (he.trans hzero)
  have hcΛ : c Λ = 1 := by
    rw [Finset.sum_eq_single Λ] at he
    · rw [orbitCharacter_self, mul_one] at he
      exact_mod_cast he.symm
    · intro μ hm hne
      rw [hz μ hm hne, mul_zero]
    · exact fun hn ↦ (hn hmem).elim
  refine ⟨S, c, hmem, hcΛ, hS, ?_, hc⟩
  intro μ hm hne
  apply lt_of_le_of_ne
  · exact (WeightOrd.toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).mpr (hS μ hm).2
  · exact fun heq ↦ hne ((WeightOrd.toWeightOrd P).injective heq).symm

/-- Power sum over distinct weights in the Weyl orbit. Degree zero counts the orbit. -/
def distinctOrbitPower (Λ : Dual K H) (n : ℕ) : SymmetricAlgebra K (Dual K H) :=
  ∑ ν ∈ distinctWeylOrbit P hA Λ, SymmetricAlgebra.ι K (Dual K H) ν ^ n

/-- Power sum of the genuine character of `L(Λ)`, using actual weight-space dimensions. -/
def characterPower (Λ : Dual K H) (n : ℕ) : SymmetricAlgebra K (Dual K H) :=
  ∑ᶠ ν : Dual K H, orbitCharacter P Λ ν • SymmetricAlgebra.ι K (Dual K H) ν ^ n

/-- Character powers can be summed over the proved finite saturated cone. -/
theorem characterPower_eq_sum {Λ μ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
    (hμ : P.IsDominantIntegral μ) (hm : μ ∈ cone P Λ) (n : ℕ) :
    characterPower P μ n = ∑ ν ∈ (finite_orbitLowerCone P hA Λ hΛ).toFinset,
      orbitCharacter P μ ν • SymmetricAlgebra.ι K (Dual K H) ν ^ n := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro ν hν
  apply (Set.Finite.mem_toFinset _).mpr
  apply orbitCharacter_support P hA hμ hm
  intro hz
  simp [Function.mem_support, hz] at hν

/-- Polynomial image of Etingof Lecture 10, equation (6), simultaneously in every degree.
The coefficients have finite dominant lower-cone support and are independent of the degree. -/
theorem exists_distinctOrbitPower_inversion (Λ : Dual K H) (hΛ : P.IsDominantIntegral Λ) :
    ∃ (S : Finset (Dual K H)) (c : Dual K H → ℤ),
      (∀ μ ∈ S, P.IsDominantIntegral μ ∧ μ ∈ cone P Λ) ∧
      ∀ n, distinctOrbitPower P hA Λ n = ∑ μ ∈ S, (c μ : K) • characterPower P μ n := by
  classical
  obtain ⟨S, c, hS, hc⟩ := exists_distinctOrbit_character_inversion P hA Λ hΛ
  refine ⟨S, c, hS, fun n ↦ ?_⟩
  let F := (finite_orbitLowerCone P hA Λ hΛ).toFinset
  have ho : distinctWeylOrbit P hA Λ ⊆ F := fun ν hν ↦
    (Set.Finite.mem_toFinset _).mpr (distinctWeylOrbit_subset P hA hΛ hν)
  have he : distinctOrbitPower P hA Λ n = ∑ ν ∈ F,
      (if ν ∈ distinctWeylOrbit P hA Λ then (1 : K) else 0) •
        SymmetricAlgebra.ι K (Dual K H) ν ^ n := by
    rw [distinctOrbitPower]
    calc
      _ = ∑ ν ∈ distinctWeylOrbit P hA Λ,
          (if ν ∈ distinctWeylOrbit P hA Λ then (1 : K) else 0) •
            SymmetricAlgebra.ι K (Dual K H) ν ^ n := by
        apply Finset.sum_congr rfl
        intro ν hν
        simp [hν]
      _ = _ := Finset.sum_subset ho (fun ν _ hn ↦ by simp [hn])
  rw [he]
  simp_rw [hc, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ hm
  rw [characterPower_eq_sum P hA hΛ (hS μ hm).1 (hS μ hm).2, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  exact mul_smul _ _ _

/-- Genuine invariant homogeneous extension of each distinct Weyl-orbit power sum.
This consumes the production trace-power theorem for actual finite-dimensional `L(μ)`.
No Chevalley extension premise, spanning premise, or HC completion wrapper is used. -/
theorem exists_distinctOrbitPower_extension (Λ : Dual K H) (hΛ : P.IsDominantIntegral Λ)
    (n : ℕ) :
    ∃ F : SymmetricAlgebra K (Dual K P.KacMoodyAlgebra),
      F ∈ SymmetricAlgebra.homogeneousSubmodule n ∧
      (∀ x : P.KacMoodyAlgebra,
        SymmetricAlgebra.derivation (LieModule.toEnd K P.KacMoodyAlgebra
          (Dual K P.KacMoodyAlgebra) x) F = 0) ∧
      coordinateCartanRestriction P F = distinctOrbitPower P hA Λ n := by
  classical
  obtain ⟨S, c, hS, hc⟩ := exists_distinctOrbitPower_inversion P hA Λ hΛ
  have he : ∀ μ : {μ // μ ∈ S},
      ∃ F : SymmetricAlgebra K (Dual K P.KacMoodyAlgebra),
        F ∈ SymmetricAlgebra.homogeneousSubmodule n ∧
        (∀ x : P.KacMoodyAlgebra,
          SymmetricAlgebra.derivation (LieModule.toEnd K P.KacMoodyAlgebra
            (Dual K P.KacMoodyAlgebra) x) F = 0) ∧
        coordinateCartanRestriction P F = characterPower P μ.val n := fun μ ↦
    exists_dominant_tracePower_extension P hA μ.val (hS μ.val μ.property).1 n
  choose F hF using he
  refine ⟨∑ μ : {μ // μ ∈ S}, (c μ.val : K) • F μ,
    Submodule.sum_mem _ (fun μ _ ↦ Submodule.smul_mem _ _ (hF μ).1), ?_, ?_⟩
  · intro x
    simp only [map_sum, Derivation.map_smul, (hF _).2.1 x, smul_zero,
      Finset.sum_const_zero]
  · simp only [map_sum, map_smul, (hF _).2.2]
    rw [hc n]
    exact Finset.sum_coe_sort S (fun μ ↦ (c μ : K) • characterPower P μ n)


/-- The precise stabilizer multiplicity separating full Weyl sums from distinct orbit sums. -/
def orbitStabilizerCard (Λ : Dual K H) : ℕ :=
  Nat.card {w : P.weylGroup hA.isGeneralizedCartan // w.val Λ = Λ}

omit [FiniteDimensional K H] in
/-- Every nonempty orbit fiber is a translate of the stabilizer, with equal cardinality. -/
theorem orbit_fiber_card (Λ ν : Dual K H) (hν : ν ∈ distinctWeylOrbit P hA Λ) :
    Nat.card {w : P.weylGroup hA.isGeneralizedCartan // w.val Λ = ν} =
      orbitStabilizerCard P hA Λ := by
  obtain ⟨v, rfl⟩ := (mem_distinctWeylOrbit P hA Λ ν).mp hν
  apply Nat.card_congr
  refine
    { toFun := fun w ↦ ⟨v⁻¹ * w.val, ?_⟩
      invFun := fun w ↦ ⟨v * w.val, ?_⟩
      left_inv := fun w ↦ Subtype.ext (by simp)
      right_inv := fun w ↦ Subtype.ext (by simp) }
  · change v.val.symm (w.val.val Λ) = Λ
    rw [w.property]
    simp
  · change v.val (w.val.val Λ) = v.val Λ
    rw [w.property]

omit [FiniteDimensional K H] in
/-- The full Weyl sum repeats every distinct orbit weight exactly as many times as the
stabilizer order. No division or regular-weight hypothesis is hidden here. -/
theorem fullWeylPower_eq_stabilizer_smul
    [Fintype (P.weylGroup hA.isGeneralizedCartan)] (Λ : Dual K H) (n : ℕ) :
    (∑ w : P.weylGroup hA.isGeneralizedCartan,
      SymmetricAlgebra.ι K (Dual K H) (w.val Λ) ^ n) =
        (orbitStabilizerCard P hA Λ : K) • distinctOrbitPower P hA Λ n := by
  classical
  rw [distinctOrbitPower, Finset.smul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to' (fun w (_ : w ∈ Finset.univ) ↦
    (mem_distinctWeylOrbit P hA Λ _).mpr ⟨w, rfl⟩)
    (fun ν ↦ SymmetricAlgebra.ι K (Dual K H) ν ^ n)]
  apply Finset.sum_congr rfl
  intro ν hν
  have hf : (Finset.univ.filter
      (fun w : P.weylGroup hA.isGeneralizedCartan ↦ w.val Λ = ν)).card =
      orbitStabilizerCard P hA Λ := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact orbit_fiber_card P hA Λ ν hν
  simp only [Finset.sum_const, hf, Nat.cast_smul_eq_nsmul]

omit [FiniteDimensional K H] in
/-- In degree zero the distinct orbit power is the orbit cardinal, not the Weyl order. -/
theorem distinctOrbitPower_zero (Λ : Dual K H) :
    distinctOrbitPower P hA Λ 0 = (distinctWeylOrbit P hA Λ).card := by
  simp [distinctOrbitPower]


/-- The empty simple-root index case is included: only the constant degree-zero power
survives. This is derived from the actual finite-type Cartan dimension theorem. -/
theorem distinctOrbitPower_of_isEmpty [IsEmpty ι] (Λ : Dual K H) (n : ℕ) :
    distinctOrbitPower P hA Λ n = if n = 0 then 1 else 0 := by
  classical
  have hspan := P.linearIndependent_coroot.span_eq_top_of_card_eq_finrank'
    (P.finrank_eq_card_of_isFiniteCartan hA).symm
  have hΛ : Λ = 0 := LinearMap.ext_on_range hspan fun i ↦ isEmptyElim i
  subst Λ
  have ho : distinctWeylOrbit P hA (0 : Dual K H) = {0} := by
    ext ν
    rw [mem_distinctWeylOrbit]
    simp [eq_comm]
  simp [distinctOrbitPower, ho, zero_pow_eq]

end Matrix.Realization.KacMoodyAlgebra
