/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Uniqueness
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.DirectSumExistence

/-!
# Primitive vectors of `L(λ)` and crystal lattices of direct sums

Let `V(λ) = L_q(λ)` with its crystal base `(L(λ), B(λ))` ([HK] Thm. 5.1.1).

* **[HK] Lemma 5.2.2 (1)**: a vector `u ∈ L(λ)` with `ẽᵢ u ∈ ϖ L(λ)` for all `i` is congruent to a
  multiple of `v_λ` modulo `ϖ L(λ)` (`GrandLoop.exists_sub_smul_hwv_mem_smul_lat`, i.e.
  `U(λ) = F v_λ`), and a vector `v ∈ V(λ)` with `ẽᵢ v ∈ L(λ)` for all `i` lies in `k v_λ + L(λ)`
  (`GrandLoop.exists_sub_smul_hwv_mem_lat`, i.e. `W(λ) = F(q) v_λ + L(λ)`). Both come from the
  weight-vector forms `GrandLoop.mem_smul_lat_of_eK_of_ne` and `GrandLoop.mem_lat_of_eK_of_ne`
  (weights `μ ≠ λ`), which are [HK] Lemma 5.3.18 at all depths.
* **[HK] Lemma 5.2.4**, for `M = ⊕ⱼ V(λⱼ)` with the crystal lattice `L = ⊕ⱼ L(λⱼ)`
  (`GrandLoop.dsSum`): (1) the analogues of `U(λ)`, `W(λ)`, componentwise
  (`GrandLoop.exists_sub_smul_hwv_mem_smul_dsSum`, `GrandLoop.exists_sub_smul_hwv_mem_dsSum`);
  (2) a graded `A`-submodule `L' ⊆ M` stable under the `ẽᵢ`, `f̃ᵢ`, containing the highest weight
  vectors of the summands and whose vectors of weight `λⱼ` have `j`-th component in `L(λⱼ)`, is
  `⊕ⱼ L(λⱼ)` (`GrandLoop.eq_dsSum`). The last condition is a local form of the hypothesis
  `L'_λ = L_λ` of [HK].

[HK] state Lemma 5.2.4 for `M ≅ V(λ)^{⊕ν}` (with `ν` finite) and leave its proof as an exercise;
here the family `(λⱼ)` and its index type are arbitrary, and the freeness of `L'` assumed in
(2) is not needed. The membership criterion behind (2) is also proved relative to a subset of the
summands (`GrandLoop.mem_lat_of_kashiwaraE_stable`), for later use in the uniqueness theorem
([HK] Thm. 5.2.1).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.2.
-/

open Pointwise

noncomputable section

namespace LieLean.QuantumGroup

/-! ### Weight components -/

section Weight

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  (hM : IsIntegrable R v M)

/-- `ẽᵢ` maps the weight-`μ` component of `m` to the weight-`(μ + αᵢ)` component of `ẽᵢ m`. -/
lemma kashiwaraE_weightSetProj (i : I) (μ : Y →+ ℤ) (m : M) :
    kashiwaraE R v M hv hM i (weightSetProj hv hM {μ} m) =
      weightSetProj hv hM {μ + R.root i} (kashiwaraE R v M hv hM i m) := by
  classical
  have h : kashiwaraE R v M hv hM i ∘ₗ weightSetProj hv hM {μ} =
      weightSetProj hv hM {μ + R.root i} ∘ₗ kashiwaraE R v M hv hM i := by
    refine ext_weightSpace hM fun ν x hx ↦ ?_
    have hex := kashiwaraE_mem_weightSpace hv hM i hx
    simp only [LinearMap.comp_apply, weightSetProj_of_mem hv hM _ hx,
      weightSetProj_of_mem hv hM _ hex, Set.mem_singleton_iff, add_left_inj]
    split_ifs <;> simp
  exact LinearMap.congr_fun h m

/-- If all weight components of `m` other than the one of weight `λ` lie in an `A`-submodule `P`,
then `m` minus its weight-`λ` component lies in `P`. -/
lemma sub_weightSetProj_mem {A : Type*} [CommRing A] [Module A M] (P : Submodule A M)
    (Λ : Y →+ ℤ) (m : M) (h : ∀ μ, μ ≠ Λ → weightSetProj hv hM {μ} m ∈ P) :
    m - weightSetProj hv hM {Λ} m ∈ P := by
  classical
  obtain ⟨s, hs⟩ := GrandLoop.exists_finset_eq_sum_weightSetProj hv hM
    (m - weightSetProj hv hM {Λ} m)
  rw [hs]
  refine Submodule.sum_mem _ fun μ _ ↦ ?_
  have hmem := weightSetProj_singleton_mem hv hM Λ m
  rw [map_sub]
  by_cases hμ : μ = Λ
  · subst hμ
    rw [weightSetProj_singleton_of_mem hv hM hmem, sub_self]
    exact zero_mem _
  · have hΛμ : Λ ∉ ({μ} : Set (Y →+ ℤ)) := by simpa [eq_comm] using hμ
    rw [weightSetProj_of_mem hv hM _ hmem]
    simp only [hΛμ, ↓reduceIte, sub_zero]
    exact h μ hμ

end Weight

/-! ### Direct sums of lattices -/

section Lattice

variable {ι A : Type*} [CommRing A] {M : ι → Type*} [∀ j, AddCommGroup (M j)]
  [∀ j, Module A (M j)] {L : ∀ j, Submodule A (M j)}

/-- `c (⊕ⱼ Lⱼ) = ⊕ⱼ c Lⱼ`. -/
lemma mem_smul_dfinsuppLattice (c : A) {m : Π₀ j, M j} :
    m ∈ c • dfinsuppLattice L ↔ ∀ j, m j ∈ c • L j := by
  classical
  constructor
  · intro hm j
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hm
    exact Submodule.smul_mem_pointwise_smul _ c _ (mem_dfinsuppLattice.1 hy j)
  · induction m using DFinsupp.induction with
    | h0 => exact fun _ ↦ zero_mem _
    | ha i b f hf _ ih =>
      intro hm
      have hb : b ∈ c • L i := by simpa [hf] using hm i
      have hf' : ∀ j, f j ∈ c • L j := fun j ↦ by
        by_cases hj : j = i
        · subst hj; rw [hf]; exact zero_mem _
        · simpa [DFinsupp.single_apply, Ne.symm hj] using hm j
      refine add_mem ?_ (ih hf')
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hb
      rw [DFinsupp.single_smul]
      exact Submodule.smul_mem_pointwise_smul _ c _ (single_mem_dfinsuppLattice hy)

end Lattice

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

/-! ### The highest weight space of `L(λ)` -/

include hvt hR in
/-- `V(λ)_λ = k v_λ`. -/
lemma exists_eq_smul_hwv_of_mem_weightSpace (Λ : Dom R)
    {x : IrreducibleModule R v Λ.1} (hx : x ∈ weightSpace R v (IrreducibleModule R v Λ.1) Λ.1) :
    ∃ c : k, x = c • IrreducibleModule.hwv R v Λ.1 := by
  classical
  have hv' := pow_ne_one_of_transcendental' hvt
  have hP : ∀ y ∈ Submodule.span k (Set.range (fW hvt hR Λ)),
      weightSetProj hv' (isInt hvt hR Λ) {Λ.1 - R.rootSum 0} y ∈
        k ∙ IrreducibleModule.hwv R v Λ.1 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      rw [weightSetProj_fW (hvt := hvt) (hR := hR)]
      split_ifs with hw
      · rw [eq_nil_of_wordWeight_eq_zero hw]
        exact Submodule.mem_span_singleton_self _
      · exact zero_mem _
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have h := hP x (by rw [IrreducibleModule.span_fWord]; trivial)
  rw [R.rootSum_zero, sub_zero, weightSetProj_singleton_of_mem hv' _ hx] at h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
  exact ⟨c, hc.symm⟩

/-! ### Direct sums of the `V(λⱼ)` -/

section DSDefs

variable {J : Type*} (Λ : J → Dom R)

variable (hvt hR) in
include hvt hR in
/-- `⊕ⱼ V(λⱼ)` is integrable. -/
lemma isIntDS : IsIntegrable R v (Π₀ j, IrreducibleModule R v (Λ j).1) :=
  isIntegrable_dfinsupp fun j ↦ isInt hvt hR (Λ j)

variable (hvt hR) in
/-- `ẽᵢ` on `⊕ⱼ V(λⱼ)`. -/
abbrev eDS (i : I) : Module.End k (Π₀ j, IrreducibleModule R v (Λ j).1) :=
  kashiwaraE R v _ (pow_ne_one_of_transcendental' hvt) (isIntDS hvt hR Λ) i

variable (hvt hR) in
/-- `f̃ᵢ` on `⊕ⱼ V(λⱼ)`. -/
abbrev fDS (i : I) : Module.End k (Π₀ j, IrreducibleModule R v (Λ j).1) :=
  kashiwaraF R v _ (pow_ne_one_of_transcendental' hvt) (isIntDS hvt hR Λ) i

lemma eDS_apply (i : I) (x : Π₀ j, IrreducibleModule R v (Λ j).1) (j : J) :
    eDS hvt hR Λ i x j = eK hvt hR (Λ j) i (x j) :=
  kashiwaraE_dfinsupp_apply (hM := fun j ↦ isInt hvt hR (Λ j)) i x j

lemma fDS_apply (i : I) (x : Π₀ j, IrreducibleModule R v (Λ j).1) (j : J) :
    fDS hvt hR Λ i x j = fK hvt hR (Λ j) i (x j) :=
  kashiwaraF_dfinsupp_apply (hM := fun j ↦ isInt hvt hR (Λ j)) i x j

lemma mem_dsSum {x : Π₀ j, IrreducibleModule R v (Λ j).1} :
    x ∈ dsSum hvt hR A Λ ↔ ∀ j, x j ∈ lat hvt hR A (Λ j) :=
  mem_dfinsuppLattice

lemma mem_smul_dsSum {x : Π₀ j, IrreducibleModule R v (Λ j).1} :
    x ∈ ϖ • dsSum hvt hR A Λ ↔ ∀ j, x j ∈ ϖ • lat hvt hR A (Λ j) :=
  mem_smul_dfinsuppLattice ϖ

/-- `f̃_w (v_{λⱼ})` in the `j`-th summand is `f̃_w` applied to the `j`-th highest weight vector. -/
lemma single_fW (j : J) (w : List I) [DecidableEq J] :
    DFinsupp.single j (fW hvt hR (Λ j) w) =
      w.foldr (fun i x ↦ fDS hvt hR Λ i x) (DFinsupp.single j (IrreducibleModule.hwv R v (Λ j).1))
      := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [List.foldr_cons, ← ih]
    exact map_kashiwaraF (pow_ne_one_of_transcendental' hvt) (isInt hvt hR (Λ j)) i
      (isIntDS hvt hR Λ)
      (DFinsupp.lsingle (R := QuantumGroup R v) (M := fun j ↦ IrreducibleModule R v (Λ j).1) j) _

/-- An `A`-submodule of `⊕ⱼ V(λⱼ)` stable under the `f̃ᵢ` and containing `v_{λⱼ}` in the `j`-th
summand contains `L(λⱼ)` in the `j`-th summand. -/
lemma single_mem_of_kashiwaraF_stable [DecidableEq J]
    (L' : Submodule A (Π₀ j, IrreducibleModule R v (Λ j).1))
    (hF : ∀ i, ∀ x ∈ L', fDS hvt hR Λ i x ∈ L') {j : J}
    (hj : DFinsupp.single j (IrreducibleModule.hwv R v (Λ j).1) ∈ L')
    {y : IrreducibleModule R v (Λ j).1} (hy : y ∈ lat hvt hR A (Λ j)) :
    DFinsupp.single j y ∈ L' := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    change DFinsupp.single j (fW hvt hR (Λ j) w) ∈ L'
    rw [single_fW]
    induction w with
    | nil => exact hj
    | cons i w ih => exact hF i _ ih
  | zero => rw [DFinsupp.single_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [DFinsupp.single_add]; exact add_mem ha hb
  | smul c a _ ha => rw [DFinsupp.single_smul]; exact Submodule.smul_mem _ c ha

end DSDefs

/-! ### Vectors killed by the `ẽᵢ` ([HK] Lemma 5.2.2 (1)) -/

omit [CharZero k] [NeZero v] [DecidableEq I] in
include hR in
lemma sub_rootSum_ne {Λ : Y →+ ℤ} {ν : I →₀ ℕ} (hν : ν ≠ 0) : Λ - R.rootSum ν ≠ Λ := by
  intro h
  refine hν (LusztigCartanDatum.RootDatum.rootSum_injective hR ?_)
  rw [R.rootSum_zero]
  simpa using h

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

/-- A vector of `V(λ)` of weight `μ ≠ λ` with `ẽᵢ v ∈ L(λ)` for all `i` lies in `L(λ)` (the second
equality of [HK] Lemma 5.2.2 (1) on weight vectors; [HK] Lemma 5.3.18 (2) in all depths). -/
theorem mem_lat_of_eK_of_ne (Λ : Dom R) {μ : Y →+ ℤ} (hμ : μ ≠ Λ.1)
    {x : IrreducibleModule R v Λ.1} (hxw : x ∈ weightSpace R v _ μ)
    (he : ∀ i, eK hvt hR Λ i x ∈ lat hvt hR A Λ) : x ∈ lat hvt hR A Λ := by
  by_cases hx0 : x = 0
  · rw [hx0]; exact zero_mem _
  obtain ⟨ν, rfl⟩ :=
    IrreducibleModule.exists_eq_sub_rootSum (pow_ne_one_of_transcendental' hvt) hxw hx0
  have hν : ν ≠ 0 := by rintro rfl; simp at hμ
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_one_of_ne_zero
    (mt (Finsupp.degree_eq_zero_iff ν).1 hν)
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  exact mem_lat_of_eK hϖv hk (fun s _ ↦ (hall s).1) (hall (r + 1)).2.1 (hall (r + 1)).2.2.1
    (hall r).2.2.2.1 hr hxw he

/-- A vector of `L(λ)` of weight `μ ≠ λ` with `ẽᵢ u ∈ ϖ L(λ)` for all `i` lies in `ϖ L(λ)` (the
first equality of [HK] Lemma 5.2.2 (1) on weight vectors; [HK] Lemma 5.3.18 (1) in all depths). -/
theorem mem_smul_lat_of_eK_of_ne (Λ : Dom R) {μ : Y →+ ℤ} (hμ : μ ≠ Λ.1)
    {x : IrreducibleModule R v Λ.1} (hx : x ∈ lat hvt hR A Λ) (hxw : x ∈ weightSpace R v _ μ)
    (he : ∀ i, eK hvt hR Λ i x ∈ ϖ • lat hvt hR A Λ) : x ∈ ϖ • lat hvt hR A Λ := by
  by_cases hx0 : x = 0
  · rw [hx0]; exact zero_mem _
  obtain ⟨ν, rfl⟩ :=
    IrreducibleModule.exists_eq_sub_rootSum (pow_ne_one_of_transcendental' hvt) hxw hx0
  have hν : ν ≠ 0 := by rintro rfl; simp at hμ
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_one_of_ne_zero
    (mt (Finsupp.degree_eq_zero_iff ν).1 hν)
  have hall := allProp (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
  exact mem_smul_lat_of_eK hϖv (fun s _ ↦ (hall s).1) (hall (r + 1)).2.1 (hall (r + 1)).2.2.1
    (hall r).2.2.2.1 hr hx hxw he

/-- **[HK] Lemma 5.2.2 (1)**, `U(λ) = F v_λ`: if `u ∈ L(λ)` and `ẽᵢ u ∈ ϖ L(λ)` for all `i`, then
`u ≡ a v_λ` modulo `ϖ L(λ)` for some `a ∈ A`. -/
theorem exists_sub_smul_hwv_mem_smul_lat (Λ : Dom R) {u : IrreducibleModule R v Λ.1}
    (hu : u ∈ lat hvt hR A Λ) (he : ∀ i, eK hvt hR Λ i u ∈ ϖ • lat hvt hR A Λ) :
    ∃ a : A, u - a • IrreducibleModule.hwv R v Λ.1 ∈ ϖ • lat hvt hR A Λ := by
  have hv' := pow_ne_one_of_transcendental' hvt
  have h1 := sub_weightSetProj_mem hv' (isInt hvt hR Λ) (ϖ • lat hvt hR A Λ) Λ.1 u
    fun μ hμ ↦ mem_smul_lat_of_eK_of_ne hinj hϖ hϖv hk hfund Λ hμ
      (weightSetProj_mem_lat hvt hR A Λ _ hu) (weightSetProj_singleton_mem hv' _ μ u)
      fun i ↦ by
        rw [kashiwaraE_weightSetProj]
        exact weightSetProj_mem_smul_lat hvt hR A ϖ Λ _ (he i)
  obtain ⟨a, ha⟩ := exists_eq_smul_hwv (weightSetProj_mem_lat hvt hR A Λ _ hu)
    (show _ ∈ wsp Λ 0 by
      rw [wsp, R.rootSum_zero, sub_zero]; exact weightSetProj_singleton_mem hv' _ Λ.1 u)
  exact ⟨a, ha ▸ h1⟩

/-- **[HK] Lemma 5.2.2 (1)**, `W(λ) = F(q) v_λ + L(λ)`: if `ẽᵢ v ∈ L(λ)` for all `i`, then
`v ∈ k v_λ + L(λ)`. -/
theorem exists_sub_smul_hwv_mem_lat (Λ : Dom R) {x : IrreducibleModule R v Λ.1}
    (he : ∀ i, eK hvt hR Λ i x ∈ lat hvt hR A Λ) :
    ∃ c : k, x - c • IrreducibleModule.hwv R v Λ.1 ∈ lat hvt hR A Λ := by
  have hv' := pow_ne_one_of_transcendental' hvt
  have h1 := sub_weightSetProj_mem hv' (isInt hvt hR Λ) (lat hvt hR A Λ) Λ.1 x
    fun μ hμ ↦ mem_lat_of_eK_of_ne hinj hϖ hϖv hk hfund Λ hμ
      (weightSetProj_singleton_mem hv' _ μ x) fun i ↦ by
        rw [kashiwaraE_weightSetProj]
        exact weightSetProj_mem_lat hvt hR A Λ _ (he i)
  obtain ⟨c, hc⟩ := exists_eq_smul_hwv_of_mem_weightSpace (hvt := hvt) (hR := hR) Λ
    (weightSetProj_singleton_mem hv' _ Λ.1 x)
  exact ⟨c, hc ▸ h1⟩

/-! ### Direct sums ([HK] Lemma 5.2.4) -/

section DirectSum

variable {J : Type*} (Λ : J → Dom R)

/-- **[HK] Lemma 5.2.4 (1)**, `U(λ)` for direct sums: if `x ∈ ⊕ⱼ L(λⱼ)` and `ẽᵢ x ∈ ϖ ⊕ⱼ L(λⱼ)`
for all `i`, then every component `xⱼ` is congruent to a multiple of `v_{λⱼ}` modulo `ϖ L(λⱼ)`. -/
theorem exists_sub_smul_hwv_mem_smul_dsSum {x : Π₀ j, IrreducibleModule R v (Λ j).1}
    (hx : x ∈ dsSum hvt hR A Λ) (he : ∀ i, eDS hvt hR Λ i x ∈ ϖ • dsSum hvt hR A Λ) (j : J) :
    ∃ a : A, x j - a • IrreducibleModule.hwv R v (Λ j).1 ∈ ϖ • lat hvt hR A (Λ j) :=
  exists_sub_smul_hwv_mem_smul_lat hinj hϖ hϖv hk hfund (Λ j) ((mem_dsSum Λ).1 hx j)
    fun i ↦ eDS_apply Λ i x j ▸ (mem_smul_dsSum Λ).1 (he i) j

/-- **[HK] Lemma 5.2.4 (1)**, `W(λ)` for direct sums: if `ẽᵢ x ∈ ⊕ⱼ L(λⱼ)` for all `i`, then
every component `xⱼ` lies in `k v_{λⱼ} + L(λⱼ)`. -/
theorem exists_sub_smul_hwv_mem_dsSum {x : Π₀ j, IrreducibleModule R v (Λ j).1}
    (he : ∀ i, eDS hvt hR Λ i x ∈ dsSum hvt hR A Λ) (j : J) :
    ∃ c : k, x j - c • IrreducibleModule.hwv R v (Λ j).1 ∈ lat hvt hR A (Λ j) :=
  exists_sub_smul_hwv_mem_lat hinj hϖ hϖv hk hfund (Λ j)
    fun i ↦ eDS_apply Λ i x j ▸ (mem_dsSum Λ).1 (he i) j

/-- Let `L'` be an `A`-submodule of `⊕ⱼ V(λⱼ)` stable under the `ẽᵢ`, and `T` a set of indices such
that for `j ∈ T` the vectors of `L'` of weight `λⱼ` have `j`-th component in `L(λⱼ)`. Then every
weight vector of `L'` has its components at `T` in the `L(λⱼ)` (cf. [HK] Lemma 5.2.2 (2), whose
proof this is). -/
theorem mem_lat_of_kashiwaraE_stable (T : Set J) (L' : Submodule A (Π₀ j, IrreducibleModule R v
    (Λ j).1)) (hE : ∀ i, ∀ x ∈ L', eDS hvt hR Λ i x ∈ L')
    (htop : ∀ x ∈ L', ∀ j ∈ T, x ∈ weightSpace R v _ (Λ j).1 → x j ∈ lat hvt hR A (Λ j))
    {μ : Y →+ ℤ} {x : Π₀ j, IrreducibleModule R v (Λ j).1} (hx : x ∈ L')
    (hxw : x ∈ weightSpace R v _ μ) {j : J} (hj : j ∈ T) : x j ∈ lat hvt hR A (Λ j) := by
  have hv' := pow_ne_one_of_transcendental' hvt
  have key : ∀ r (ν : I →₀ ℕ), ν.degree = r → ∀ x ∈ L',
      x ∈ weightSpace R v _ ((Λ j).1 - R.rootSum ν) → x j ∈ lat hvt hR A (Λ j) := by
    intro r
    induction r with
    | zero =>
      intro ν hν x hx hxw
      rw [(Finsupp.degree_eq_zero_iff ν).1 hν, R.rootSum_zero, sub_zero] at hxw
      exact htop x hx j hj hxw
    | succ r ih =>
      intro ν hν x hx hxw
      have hν0 : ν ≠ 0 := by rintro rfl; simp at hν
      refine mem_lat_of_eK_of_ne hinj hϖ hϖv hk hfund (Λ j) (sub_rootSum_ne (hR := hR) hν0)
        (map_mem_weightSpace (DFinsupp.lapply j) hxw) fun i ↦ ?_
      rw [← eDS_apply]
      by_cases h0 : eDS hvt hR Λ i x j = 0
      · rw [h0]; exact zero_mem _
      have hew := kashiwaraE_mem_weightSpace hv' (isIntDS hvt hR Λ) i hxw
      have hewj := map_mem_weightSpace (DFinsupp.lapply (R := QuantumGroup R v) j) hew
      obtain ⟨ν', hν'⟩ := exists_eq_add_single hR hv' (Λ j) (i := i) (j := 1) (ν := ν)
        (by rw [one_smul]; exact hewj) h0
      refine ih ν' (by rw [hν', map_add, Finsupp.degree_single] at hν; omega) _ (hE i x hx) ?_
      convert hew using 2
      rw [hν', R.rootSum_add, R.rootSum_single, one_nsmul]; abel
  by_cases hx0 : x j = 0
  · rw [hx0]; exact zero_mem _
  obtain ⟨ν, rfl⟩ := IrreducibleModule.exists_eq_sub_rootSum hv'
    (map_mem_weightSpace (DFinsupp.lapply (R := QuantumGroup R v) j) hxw) hx0
  exact key _ ν rfl x hx hxw

/-- **[HK] Lemma 5.2.4 (2)**: let `L'` be an `A`-submodule of `⊕ⱼ V(λⱼ)` stable under the weight
projections and the `ẽᵢ`, `f̃ᵢ`, containing the highest weight vector of every summand, and such
that the vectors of `L'` of weight `λⱼ` have `j`-th component in `L(λⱼ)`. Then `L' = ⊕ⱼ L(λⱼ)`.
[HK] state this for `V(λ)^{⊕ν}` with `L'` free and `L'_λ = L_λ`. -/
theorem eq_dsSum [DecidableEq J] (L' : Submodule A (Π₀ j, IrreducibleModule R v (Λ j).1))
    (hP : ∀ S, ∀ x ∈ L', weightSetProj (pow_ne_one_of_transcendental' hvt) (isIntDS hvt hR Λ) S x
      ∈ L')
    (hE : ∀ i, ∀ x ∈ L', eDS hvt hR Λ i x ∈ L') (hF : ∀ i, ∀ x ∈ L', fDS hvt hR Λ i x ∈ L')
    (hv : ∀ j, DFinsupp.single j (IrreducibleModule.hwv R v (Λ j).1) ∈ L')
    (htop : ∀ x ∈ L', ∀ j, x ∈ weightSpace R v _ (Λ j).1 → x j ∈ lat hvt hR A (Λ j)) :
    L' = dsSum hvt hR A Λ := by
  have hv' := pow_ne_one_of_transcendental' hvt
  refine le_antisymm (fun x hx ↦ (mem_dsSum Λ).2 fun j ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨s, hs⟩ := exists_finset_eq_sum_weightSetProj hv' (isIntDS hvt hR Λ) x
    rw [hs, DFinsupp.finsetSum_apply]
    exact Submodule.sum_mem _ fun μ _ ↦ mem_lat_of_kashiwaraE_stable hinj hϖ hϖv hk hfund Λ
      Set.univ L' hE (fun x hx j _ ↦ htop x hx j) (hP _ x hx)
      (weightSetProj_singleton_mem hv' _ μ x) (Set.mem_univ j)
  · induction x using DFinsupp.induction with
    | h0 => exact zero_mem _
    | ha j b f hf _ ih =>
      have hx' := (mem_dsSum Λ).1 hx
      have hb : b ∈ lat hvt hR A (Λ j) := by simpa [hf] using hx' j
      refine add_mem (single_mem_of_kashiwaraF_stable Λ L' hF (hv j) hb) (ih ?_)
      refine (mem_dsSum Λ).2 fun l ↦ ?_
      by_cases hl : l = j
      · subst hl; rw [hf]; exact zero_mem _
      · simpa [DFinsupp.single_apply, Ne.symm hl] using hx' l

end DirectSum

end GrandLoop

end LieLean.QuantumGroup
