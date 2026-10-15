/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.HighestWeightMaps

/-!
# The category `𝒪_int` of `U_q(𝔤)`-modules

Let `U = U_q(𝔤)` (`QuantumGroup R v`). The category `𝒪_int` ([HK] Def. 3.2.3) consists of the
integrable `U`-modules with finite-dimensional weight spaces whose weights lie in a finite union of
cones `μ - Q₊` (`QuantumGroup.IsCategoryOInt`).

## Main results

* `QuantumGroup.IsCategoryOInt.exists_maximal`: a nonzero module in `𝒪_int` has a maximal weight
  `Λ`, i.e. `Λ + αᵢ` is not a weight for any `i`.
* `QuantumGroup.dominant_of_primitive`: a primitive weight vector of an integrable module has
  dominant weight.
* `QuantumGroup.nonempty_equiv_irreducibleModule_of_span` ([HK] Cor. 3.4.8 (1)): an integrable
  highest weight module of highest weight `Λ` has `Λ` dominant and is isomorphic to `L_q(Λ)`.
* `QuantumGroup.IsCategoryOInt.exists_nonempty_equiv_of_isSimpleModule` ([HK] Cor. 3.4.8 (2)):
  every simple module in `𝒪_int` is isomorphic to `L_q(Λ)` for a dominant `Λ`.

The results about highest weight modules assume `v` transcendental over `ℚ`, `k` of characteristic
zero, finitely many simple roots and an `X`-regular root datum, the hypotheses under which
`L̃_q(Λ) ≅ L_q(Λ)` is proved (`QuantumGroup.FPowQuotient.equivIrreducibleModule`); [HK] work over
`ℚ(q)`. Their proof of Cor. 3.4.8 (1) goes through the classical limit; here it is the universal
property of `L_q(Λ)` (`QuantumGroup.IrreducibleModule.lift`) and simplicity of `L_q(Λ)`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §3.2, §3.4.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

variable (R v M) in
/-- The category `𝒪_int` ([HK] Def. 3.2.3): `M` is integrable (the sum of its weight spaces, with
`Eᵢ`, `Fᵢ` locally nilpotent), its weight spaces are finite-dimensional, and its weights lie in
`⋃_{μ ∈ s} (μ - Q₊)` for a finite set `s`. -/
structure IsCategoryOInt : Prop where
  isIntegrable : IsIntegrable R v M
  finiteDimensional_weightSpace : ∀ Λ, FiniteDimensional k (weightSpace R v M Λ)
  exists_finset : ∃ s : Finset (Y →+ ℤ), ∀ Λ, weightSpace R v M Λ ≠ ⊥ →
    ∃ μ ∈ s, ∃ ν : I →₀ ℕ, Λ = μ - R.rootSum ν

/-- A nonzero module in `𝒪_int` has a maximal weight: a weight `Λ` such that no `Λ + αᵢ` is a
weight. -/
theorem IsCategoryOInt.exists_maximal (hR : R.IsXRegular) (hM : IsCategoryOInt R v M)
    {Λ₀ : Y →+ ℤ} (h0 : weightSpace R v M Λ₀ ≠ ⊥) :
    ∃ Λ, weightSpace R v M Λ ≠ ⊥ ∧ ∀ i, weightSpace R v M (Λ + R.root i) = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := hM.exists_finset
  have hinj : Function.Injective R.rootSum := fun ν ν' h ↦ by
    by_contra hne
    obtain ⟨μ, hμ⟩ := R.exists_rootSum_ne hR hne
    exact hμ (by rw [h])
  set S : Set ℕ :=
    {n | ∃ ν : I →₀ ℕ, weightSpace R v M (Λ₀ + R.rootSum ν) ≠ ⊥ ∧ ν.degree = n}
  have hbdd : BddAbove S := by
    refine ⟨∑ μ ∈ s, (if h : ∃ ρ, R.rootSum ρ = μ - Λ₀ then h.choose.degree else 0), ?_⟩
    rintro n ⟨ν, hν, rfl⟩
    obtain ⟨μ, hμs, ν', hν'⟩ := hs _ hν
    have hρ : R.rootSum (ν + ν') = μ - Λ₀ := by
      calc R.rootSum (ν + ν') = (Λ₀ + R.rootSum ν) + R.rootSum ν' - Λ₀ := by
            rw [R.rootSum_add]; abel
        _ = μ - Λ₀ := by rw [hν']; abel
    have hex : ∃ ρ, R.rootSum ρ = μ - Λ₀ := ⟨_, hρ⟩
    have hch : hex.choose = ν + ν' := hinj (hex.choose_spec.trans hρ.symm)
    calc ν.degree ≤ (ν + ν').degree := by rw [map_add]; exact Nat.le_add_right _ _
      _ = (if h : ∃ ρ, R.rootSum ρ = μ - Λ₀ then h.choose.degree else 0) := by
            simp only [hex, ↓reduceDIte, hch]
      _ ≤ _ := Finset.single_le_sum
            (f := fun μ ↦ if h : ∃ ρ, R.rootSum ρ = μ - Λ₀ then h.choose.degree else 0)
            (fun _ _ ↦ Nat.zero_le _) hμs
  have hne : S.Nonempty := ⟨0, 0, by simpa using h0, by simp⟩
  obtain ⟨ν, hν, hdeg⟩ := Nat.sSup_mem hne hbdd
  refine ⟨Λ₀ + R.rootSum ν, hν, fun i ↦ ?_⟩
  by_contra hi
  have hmem : (ν + Finsupp.single i 1).degree ∈ S :=
    ⟨_, by rwa [R.rootSum_add, R.rootSum_single, one_smul, ← add_assoc], rfl⟩
  have := le_csSup hbdd hmem
  rw [map_add, hdeg, Finsupp.degree_single] at this
  omega

variable [NeZero v] (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

include hv' in
/-- A primitive weight vector (`Eᵢ w = 0` for all `i`) of an integrable module has dominant
weight. -/
theorem dominant_of_primitive (hM : IsIntegrable R v M) {Λ : Y →+ ℤ} {w : M}
    (hw : w ∈ weightSpace R v M Λ) (hw0 : w ≠ 0) (hE : ∀ i, E R v i • w = 0) (i : I) :
    0 ≤ Λ (R.coroot i) := by
  by_contra h
  exact hw0 (IntegrableSl2.eq_zero_of_primitive_of_neg (V := nodeSl2 R v M hv' hM i)
    (pow_d_ne_zero i) (pow_d_ne_one hv' i) (mem_nodeWt_of_mem hw) (hE i) (by omega))

variable [Finite I] [CharZero k] (hvt : Transcendental ℚ v) (hR : R.IsXRegular)

include hv' hvt hR in
/-- **[HK] Cor. 3.4.8 (1).** An integrable highest weight module `M = U w` of highest weight `Λ`
(`w ∈ M^Λ` nonzero, `Eᵢ w = 0`) has `Λ` dominant and is isomorphic to `L_q(Λ)`. -/
theorem nonempty_equiv_irreducibleModule_of_span (hM : IsIntegrable R v M) {Λ : Y →+ ℤ} {w : M}
    (hw : w ∈ weightSpace R v M Λ) (hw0 : w ≠ 0) (hE : ∀ i, E R v i • w = 0)
    (hspan : Submodule.span (QuantumGroup R v) {w} = ⊤) :
    (∀ i, 0 ≤ Λ (R.coroot i)) ∧
      Nonempty (IrreducibleModule R v Λ ≃ₗ[QuantumGroup R v] M) := by
  have hΛ := dominant_of_primitive hv' hM hw hw0 hE
  refine ⟨hΛ, ⟨LinearEquiv.ofBijective (IrreducibleModule.lift hvt hR hv' hΛ hM w hw hE)
    ⟨?_, ?_⟩⟩⟩
  · have := IrreducibleModule.isSimpleModule hR hv' Λ
    rcases IsSimpleOrder.eq_bot_or_eq_top
      (LinearMap.ker (IrreducibleModule.lift hvt hR hv' hΛ hM w hw hE)) with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exfalso
      have : IrreducibleModule.hwv R v Λ ∈
          LinearMap.ker (IrreducibleModule.lift hvt hR hv' hΛ hM w hw hE) := h ▸ trivial
      rw [LinearMap.mem_ker, IrreducibleModule.lift_hwv] at this
      exact hw0 this
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le,
      Set.singleton_subset_iff]
    exact ⟨_, IrreducibleModule.lift_hwv hvt hR hv' hΛ hM w hw hE⟩

include hv' hvt hR in
/-- **[HK] Cor. 3.4.8 (2).** Every simple module in `𝒪_int` is isomorphic to `L_q(Λ)` for some
dominant `Λ`. -/
theorem IsCategoryOInt.exists_nonempty_equiv_of_isSimpleModule (hM : IsCategoryOInt R v M)
    [IsSimpleModule (QuantumGroup R v) M] :
    ∃ Λ : Y →+ ℤ, (∀ i, 0 ≤ Λ (R.coroot i)) ∧
      Nonempty (IrreducibleModule R v Λ ≃ₗ[QuantumGroup R v] M) := by
  have hnt : Nontrivial M := IsSimpleModule.nontrivial (QuantumGroup R v) M
  obtain ⟨Λ₀, h0⟩ : ∃ Λ₀, weightSpace R v M Λ₀ ≠ ⊥ := by
    by_contra! h
    have htop := hM.isIntegrable.iSup_weightSpace_eq_top
    simp only [h, iSup_bot] at htop
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact hx ((Submodule.mem_bot k).1 (htop ▸ Submodule.mem_top))
  obtain ⟨Λ, hΛ, hmax⟩ := hM.exists_maximal hR h0
  obtain ⟨w, hw, hw0⟩ := Submodule.ne_bot_iff _ |>.1 hΛ
  have hE : ∀ i, E R v i • w = 0 := fun i ↦ by
    have := E_smul_mem_weightSpace hw i
    rwa [hmax i, Submodule.mem_bot] at this
  have hspan : Submodule.span (QuantumGroup R v) {w} = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (Submodule.span (QuantumGroup R v) {w}) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.1 h) hw0
    · exact h
  obtain ⟨hdom, he⟩ :=
    nonempty_equiv_irreducibleModule_of_span hv' hvt hR hM.isIntegrable hw hw0 hE hspan
  exact ⟨Λ, hdom, he⟩

end LieLean.QuantumGroup
