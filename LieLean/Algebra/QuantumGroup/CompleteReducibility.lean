/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.HighestWeightSplitting

/-!
# Complete reducibility of `𝒪_int`

Every module in the category `𝒪_int` of `U_q(𝔤)`-modules is a direct sum of irreducible highest
weight modules `L_q(Λ)` with `Λ` dominant ([HK] Thm. 3.5.4).

## Proof

As in [HK]: every vector of `M` lies in a finite-dimensional subspace `W` stable under the `Eᵢ`
and the `K_μ` (`QuantumGroup.IsCategoryOInt.exists_finiteDimensional`), and `U W` is semisimple,
by induction on `dim W`. A weight `Λ` of `W` maximal among the weights of `W` is a maximal weight of
`U W = U⁻ W`, so for a nonzero `w ∈ W ∩ M^Λ`, `U w ≅ L_q(Λ)` has a complement `N` in `U W`
(Lemma 3.5.3, `QuantumGroup.exists_isCompl_span_of_maximal`). The projection `U W → N` along
`U w` is surjective and kills `w`, so `N = U W'` for the image `W'` of `W`, of smaller dimension.

## Main results

* `QuantumGroup.mem_iSup_inf_weightSpace`: a `K`-stable subspace of an integrable module is the
  sum of its intersections with the weight spaces.
* `QuantumGroup.IsCategoryOInt.submodule`: `𝒪_int` is closed under submodules.
* `QuantumGroup.IsCategoryOInt.isSemisimpleModule`: modules in `𝒪_int` are semisimple.
* `QuantumGroup.IsCategoryOInt.exists_linearEquiv_dfinsupp` ([HK] Thm. 3.5.4): every module in
  `𝒪_int` is isomorphic to a direct sum `⊕ⱼ L_q(Λⱼ)` with all `Λⱼ` dominant.

The results assume `v` transcendental over `ℚ`, `k` of characteristic zero, finitely many simple
roots and an `X`-regular root datum, as in `QuantumGroup.exists_isCompl_span_of_maximal`; [HK]
work over `ℚ(q)`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §3.5.
-/

open LieLean Finset

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

/-! ### Weight decomposition of `K`-stable subspaces -/

section Weights

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

include hv' in
/-- A weight is separated from finitely many other weights by an element of `U⁰ = k[Y]`. -/
theorem exists_charHom_eq_one_forall_eq_zero {Λ : Y →+ ℤ} {t : Finset (Y →+ ℤ)} (hΛ : Λ ∉ t) :
    ∃ g, charHom v Λ g = 1 ∧ ∀ Λ' ∈ t, charHom v Λ' g = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, map_one _, by simp⟩
  | insert a t _ ih =>
    rw [Finset.mem_insert, not_or] at hΛ
    obtain ⟨g, hg1, hg⟩ := ih hΛ.2
    obtain ⟨g', hg'1, hg'⟩ := exists_charHom_eq_one_eq_zero hv' hΛ.1
    refine ⟨g * g', by rw [map_mul, hg1, hg'1, one_mul], fun Λ' hΛ' ↦ ?_⟩
    rcases Finset.mem_insert.1 hΛ' with rfl | h
    · rw [map_mul, hg', mul_zero]
    · rw [map_mul, hg Λ' h, zero_mul]

omit [NeZero v] in
/-- A subspace stable under the `K_μ` is stable under `U⁰`. -/
lemma zeroHom_smul_mem {W : Submodule k M} (hW : ∀ μ, ∀ x ∈ W, K R v μ • x ∈ W)
    (g : AddMonoidAlgebra k Y) {x : M} (hx : x ∈ W) : zeroHom R v g • x ∈ W := by
  induction g using AddMonoidAlgebra.induction_on with
  | of μ =>
    change zeroHom R v (AddMonoidAlgebra.single μ 1) • x ∈ W
    rw [zeroHom_single]
    exact hW μ x hx
  | add f g hf hg => rw [map_add, add_smul]; exact W.add_mem hf hg
  | smul c f hf => rw [map_smul, smul_assoc]; exact W.smul_mem c hf

variable (hM : IsIntegrable R v M)

include hv' hM in
/-- The projection of a vector onto a weight space is given by the action of an element of `U⁰`. -/
lemma exists_zeroHom_smul_eq_weightSetProj (x : M) (μ : Y →+ ℤ) :
    ∃ g, zeroHom R v g • x = weightSetProj hv' hM {μ} x := by
  classical
  have hx : x ∈ ⨆ Λ, weightSpace R v M Λ := hM.iSup_weightSpace_eq_top ▸ Submodule.mem_top
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  obtain ⟨g, hg1, hg0⟩ := exists_charHom_eq_one_forall_eq_zero hv' (Finset.notMem_erase μ s)
  refine ⟨g, ?_⟩
  have key : ⨆ Λ ∈ s, weightSpace R v M Λ ≤ LinearMap.eqLocus
      (Algebra.lsmul k k M (zeroHom R v g)) (weightSetProj hv' hM {μ}) := by
    refine iSup₂_le fun Λ hΛ m hm ↦ ?_
    rw [LinearMap.mem_eqLocus, Algebra.lsmul_apply, zeroHom_smul_of_mem_weightSpace hm,
      weightSetProj_of_mem hv' hM _ hm]
    by_cases h : Λ = μ
    · subst h
      simp [hg1]
    · rw [hg0 Λ (Finset.mem_erase.2 ⟨h, hΛ⟩), zero_smul]
      simp [h]
  exact key hs

include hv' hM in
/-- A subspace of an integrable module stable under the `K_μ` is the sum of its intersections with
the weight spaces. -/
theorem mem_iSup_inf_weightSpace {W : Submodule k M} (hW : ∀ μ, ∀ x ∈ W, K R v μ • x ∈ W)
    {x : M} (hx : x ∈ W) : x ∈ ⨆ μ, W ⊓ weightSpace R v M μ := by
  classical
  have hx' : x ∈ ⨆ Λ, weightSpace R v M Λ := hM.iSup_weightSpace_eq_top ▸ Submodule.mem_top
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx'
  have key : ⨆ Λ ∈ s, weightSpace R v M Λ ≤
      LinearMap.eqLocus (∑ μ ∈ s, weightSetProj hv' hM {μ}) LinearMap.id := by
    refine iSup₂_le fun Λ hΛ m hm ↦ ?_
    rw [LinearMap.mem_eqLocus, LinearMap.sum_apply, LinearMap.id_apply]
    simp [weightSetProj_of_mem hv' hM _ hm, hΛ]
  have hsum := key hs
  rw [LinearMap.mem_eqLocus, LinearMap.sum_apply, LinearMap.id_apply] at hsum
  rw [← hsum]
  refine Submodule.sum_mem _ fun μ _ ↦ Submodule.mem_iSup_of_mem μ
    ⟨?_, weightSetProj_singleton_mem hv' hM μ x⟩
  obtain ⟨g, hg⟩ := exists_zeroHom_smul_eq_weightSetProj hv' hM x μ
  rw [← hg]
  exact zeroHom_smul_mem hW g hx

omit [NeZero v] in
lemma mem_weightSpace_submodule {N : Submodule (QuantumGroup R v) M} {Λ : Y →+ ℤ} {x : N} :
    x ∈ weightSpace R v N Λ ↔ (x : M) ∈ weightSpace R v M Λ := by
  simp only [mem_weightSpace, Subtype.ext_iff, Submodule.coe_smul, Submodule.coe_smul_of_tower]

include hv' hM in
/-- Submodules of integrable modules are integrable. -/
theorem IsIntegrable.submodule (N : Submodule (QuantumGroup R v) M) : IsIntegrable R v N where
  iSup_weightSpace_eq_top := by
    rw [eq_top_iff]
    rintro x -
    have hx := mem_iSup_inf_weightSpace hv' hM (W := N.restrictScalars k)
      (fun μ y hy ↦ N.smul_mem _ hy) x.2
    have hle : ⨆ μ, N.restrictScalars k ⊓ weightSpace R v M μ ≤
        (⨆ μ, weightSpace R v N μ).map (N.subtype.restrictScalars k) := by
      rw [Submodule.map_iSup]
      exact iSup_mono fun μ y hy ↦ ⟨⟨y, hy.1⟩, mem_weightSpace_submodule.2 hy.2, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hle hx
    rwa [show z = x from Subtype.ext hzx] at hz
  exists_E_pow_smul_eq_zero i x := by
    obtain ⟨n, hn⟩ := hM.exists_E_pow_smul_eq_zero i x
    exact ⟨n, Subtype.ext hn⟩
  exists_F_pow_smul_eq_zero i x := by
    obtain ⟨n, hn⟩ := hM.exists_F_pow_smul_eq_zero i x
    exact ⟨n, Subtype.ext hn⟩

end Weights

/-- `𝒪_int` is closed under submodules. -/
theorem IsCategoryOInt.submodule (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsCategoryOInt R v M)
    (N : Submodule (QuantumGroup R v) M) : IsCategoryOInt R v N where
  isIntegrable := hM.isIntegrable.submodule hv' N
  finiteDimensional_weightSpace Λ := by
    have := hM.finiteDimensional_weightSpace Λ
    let f : weightSpace R v N Λ →ₗ[k] weightSpace R v M Λ :=
      { toFun := fun x ↦ ⟨x.1, mem_weightSpace_submodule.1 x.2⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    exact Module.Finite.of_injective f fun x y h ↦
      Subtype.ext (Subtype.ext (congrArg (fun z : weightSpace R v M Λ ↦ (z : M)) h))
  exists_finset := by
    obtain ⟨s, hs⟩ := hM.exists_finset
    refine ⟨s, fun Λ hΛ ↦ hs Λ ?_⟩
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hΛ
    exact (Submodule.ne_bot_iff _).2
      ⟨x, mem_weightSpace_submodule.1 hx, fun h ↦ hx0 (Subtype.ext h)⟩

omit [NeZero v] in
/-- In a module in `𝒪_int`, a property `P` of weights which holds for some weight holds for a
weight `Λ` such that it fails for every `Λ + ν`, `ν ∈ Q₊ \ 0`. -/
theorem IsCategoryOInt.exists_maximal_of_le (hR : R.IsXRegular) (hM : IsCategoryOInt R v M)
    {P : (Y →+ ℤ) → Prop} (hP : ∀ Λ, P Λ → weightSpace R v M Λ ≠ ⊥) {Λ₀ : Y →+ ℤ}
    (h0 : P Λ₀) : ∃ Λ, P Λ ∧ ∀ ν : I →₀ ℕ, ν ≠ 0 → ¬ P (Λ + R.rootSum ν) := by
  classical
  obtain ⟨s, hs⟩ := hM.exists_finset
  have hinj : Function.Injective R.rootSum := fun ν ν' h ↦ by
    by_contra hne
    obtain ⟨μ, hμ⟩ := R.exists_rootSum_ne hR hne
    exact hμ (by rw [h])
  set S : Set ℕ := {n | ∃ ν : I →₀ ℕ, P (Λ₀ + R.rootSum ν) ∧ ν.degree = n}
  have hbdd : BddAbove S := by
    refine ⟨∑ μ ∈ s, (if h : ∃ ρ, R.rootSum ρ = μ - Λ₀ then h.choose.degree else 0), ?_⟩
    rintro n ⟨ν, hν, rfl⟩
    obtain ⟨μ, hμs, ν', hν'⟩ := hs _ (hP _ hν)
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
  refine ⟨Λ₀ + R.rootSum ν, hν, fun ν' hν' hP' ↦ ?_⟩
  have hmem : (ν + ν').degree ∈ S := ⟨_, by rwa [R.rootSum_add, ← add_assoc], rfl⟩
  have hle := le_csSup hbdd hmem
  rw [map_add, hdeg] at hle
  have : ν'.degree ≠ 0 := fun h ↦ hν' ((Finsupp.degree_eq_zero_iff ν').1 h)
  omega

/-! ### The submodule generated by an `E`-stable subspace -/

section Span

variable {W : Submodule k M}

/-- If `W` is stable under the `Eᵢ` and is the sum of its weight components, then the weights of
`U W` lie below the weights of `W`. -/
theorem span_le_iSup_weightSpace (hE : ∀ i, ∀ x ∈ W, E R v i • x ∈ W)
    (hW : W ≤ ⨆ μ, W ⊓ weightSpace R v M μ) {m : M}
    (hm : m ∈ Submodule.span (QuantumGroup R v) (W : Set M)) :
    m ∈ ⨆ (μ) (_ : W ⊓ weightSpace R v M μ ≠ ⊥) (ν : I →₀ ℕ),
      weightSpace R v M (μ - R.rootSum ν) := by
  set P : Submodule k M := ⨆ (μ) (_ : W ⊓ weightSpace R v M μ ≠ ⊥) (ν : I →₀ ℕ),
    weightSpace R v M (μ - R.rootSum ν) with hPdef
  have hPF : ∀ i, ∀ m ∈ P, F R v i • m ∈ P := by
    intro i
    suffices P ≤ P.comap (Algebra.lsmul k k M (F R v i)) from fun m hm ↦ this hm
    refine iSup_le fun μ ↦ iSup_le fun hμ ↦ iSup_le fun ν m hm ↦ ?_
    rw [Submodule.mem_comap, Algebra.lsmul_apply]
    refine Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ
      (Submodule.mem_iSup_of_mem (ν + Finsupp.single i 1) ?_))
    have := F_smul_mem_weightSpace hm i
    rwa [R.rootSum_add, R.rootSum_single, one_smul, ← sub_sub]
  have hPK : ∀ μ', ∀ m ∈ P, K R v μ' • m ∈ P := by
    intro μ'
    suffices P ≤ P.comap (Algebra.lsmul k k M (K R v μ')) from fun m hm ↦ this hm
    refine iSup_le fun μ ↦ iSup_le fun hμ ↦ iSup_le fun ν m hm ↦ ?_
    rw [Submodule.mem_comap, Algebra.lsmul_apply]
    exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ
      (Submodule.mem_iSup_of_mem ν (K_smul_mem_weightSpace hm μ')))
  have hWP : W ≤ P := hW.trans (iSup_le fun μ ↦ by
    by_cases hμ : W ⊓ weightSpace R v M μ = ⊥
    · rw [hμ]; exact bot_le
    · intro m hm
      refine Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ
        (Submodule.mem_iSup_of_mem 0 ?_))
      rw [R.rootSum_zero, sub_zero]
      exact hm.2)
  have hplus : ∀ x : LusztigF k I, ∀ m ∈ W, plusHom R v x • m ∈ W := by
    intro x
    induction x using FreeAlgebra.induction with
    | grade0 c => intro m hm; rw [AlgHom.commutes, algebraMap_smul]; exact W.smul_mem c hm
    | grade1 i => intro m hm; rw [plusHom_θ]; exact hE i m hm
    | mul a b ha hb => intro m hm; rw [map_mul, mul_smul]; exact ha _ (hb m hm)
    | add a b ha hb => intro m hm; rw [map_add, add_smul]; exact W.add_mem (ha m hm) (hb m hm)
  have hminus : ∀ y : LusztigF k I, ∀ m ∈ P, minusHom R v y • m ∈ P := by
    intro y
    induction y using FreeAlgebra.induction with
    | grade0 c => intro m hm; rw [AlgHom.commutes, algebraMap_smul]; exact P.smul_mem c hm
    | grade1 i => intro m hm; rw [minusHom_θ]; exact hPF i m hm
    | mul a b ha hb => intro m hm; rw [map_mul, mul_smul]; exact ha _ (hb m hm)
    | add a b ha hb => intro m hm; rw [map_add, add_smul]; exact P.add_mem (ha m hm) (hb m hm)
  have hU : ∀ u : QuantumGroup R v, ∀ m ∈ W, u • m ∈ P := by
    intro u m hm
    have hu : u ∈ Submodule.span k (triangularSet R v) := by
      change u ∈ triangularSpan R v
      rw [span_triangular (NeZero.ne v)]
      trivial
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨w, μ, w', rfl⟩ := hu
      rw [mul_smul, mul_smul]
      exact hminus _ _ (hPK μ _ (hWP (hplus _ m hm)))
    | zero => rw [zero_smul]; exact P.zero_mem
    | add u u' _ _ h h' => rw [add_smul]; exact P.add_mem h h'
    | smul c u _ h => rw [smul_assoc]; exact P.smul_mem c h
  let Q : Submodule (QuantumGroup R v) M :=
    { carrier := {m | ∀ u : QuantumGroup R v, u • m ∈ P}
      add_mem' := fun ha hb u ↦ by rw [smul_add]; exact P.add_mem (ha u) (hb u)
      zero_mem' := fun u ↦ by rw [smul_zero]; exact P.zero_mem
      smul_mem' := fun c m hm u ↦ by rw [smul_smul]; exact hm _ }
  have hWQ : Submodule.span (QuantumGroup R v) (W : Set M) ≤ Q :=
    Submodule.span_le.2 fun m hm u ↦ hU u m hm
  simpa using (hWQ hm : ∀ u : QuantumGroup R v, u • m ∈ P) 1

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

include hv' in
/-- If `Λ` is not of the form `μ - ν`, `ν ∈ Q₊`, for a weight `μ` of `W`, then `Λ` is not a weight
of `U W`. -/
theorem eq_zero_of_mem_span_of_mem_weightSpace (hE : ∀ i, ∀ x ∈ W, E R v i • x ∈ W)
    (hW : W ≤ ⨆ μ, W ⊓ weightSpace R v M μ) {Λ : Y →+ ℤ}
    (hΛ : ∀ μ, W ⊓ weightSpace R v M μ ≠ ⊥ → ∀ ν : I →₀ ℕ, μ - R.rootSum ν ≠ Λ) {m : M}
    (hm : m ∈ Submodule.span (QuantumGroup R v) (W : Set M))
    (hmΛ : m ∈ weightSpace R v M Λ) : m = 0 := by
  have h1 := span_le_iSup_weightSpace hE hW hm
  have h2 : (⨆ (μ) (_ : W ⊓ weightSpace R v M μ ≠ ⊥) (ν : I →₀ ℕ),
      weightSpace R v M (μ - R.rootSum ν)) ≤ ⨆ (j) (_ : j ≠ Λ), weightSpace R v M j :=
    iSup_le fun μ ↦ iSup_le fun hμ ↦ iSup_le fun ν ↦
      le_iSup₂_of_le (f := fun j (_ : j ≠ Λ) ↦ weightSpace R v M j) _ (hΛ μ hμ ν) le_rfl
  exact Submodule.disjoint_def.1 (iSupIndep_weightSpace hv' Λ) m hmΛ (h2 h1)

end Span

/-! ### Finite-dimensional `E`-stable subspaces -/

/-- Every vector of a module in `𝒪_int` lies in a finite-dimensional subspace stable under the `Eᵢ`
and the `K_μ`. -/
theorem IsCategoryOInt.exists_finiteDimensional (hR : R.IsXRegular) (hM : IsCategoryOInt R v M)
    (x : M) : ∃ W : Submodule k M, x ∈ W ∧ FiniteDimensional k W ∧
      (∀ i, ∀ y ∈ W, E R v i • y ∈ W) ∧ ∀ μ, ∀ y ∈ W, K R v μ • y ∈ W := by
  classical
  obtain ⟨s, hs⟩ := hM.exists_finset
  have hinj : Function.Injective R.rootSum := fun ν ν' h ↦ by
    by_contra hne
    obtain ⟨μ, hμ⟩ := R.exists_rootSum_ne hR hne
    exact hμ (by rw [h])
  have hx : x ∈ ⨆ Λ, weightSpace R v M Λ :=
    hM.isIntegrable.iSup_weightSpace_eq_top ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  have hfin : ∀ μ : Y →+ ℤ, {ν : I →₀ ℕ | weightSpace R v M (μ + R.rootSum ν) ≠ ⊥}.Finite := by
    intro μ
    refine ((s : Set (Y →+ ℤ)).toFinite.biUnion fun μ' _ ↦
      ((antidiagonal (if h : ∃ ρ, R.rootSum ρ = μ' - μ then h.choose else 0)).image
        Prod.fst).finite_toSet).subset ?_
    intro ν hν
    obtain ⟨μ', hμ', ρ, hρ⟩ := hs _ hν
    have hσ : R.rootSum (ν + ρ) = μ' - μ := by
      rw [R.rootSum_add]
      calc R.rootSum ν + R.rootSum ρ = (μ + R.rootSum ν) + R.rootSum ρ - μ := by abel
        _ = μ' - μ := by rw [hρ]; abel
    have hex : ∃ σ, R.rootSum σ = μ' - μ := ⟨_, hσ⟩
    refine Set.mem_biUnion (Finset.mem_coe.2 hμ') ?_
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(ν, ρ), mem_antidiagonal.2 ?_, rfl⟩)
    simp only [hex, ↓reduceDIte]
    exact (hinj (hex.choose_spec.trans hσ.symm)).symm
  have hfd : ∀ Λ, FiniteDimensional k (weightSpace R v M Λ) := hM.finiteDimensional_weightSpace
  set W : Submodule k M := ⨆ μ ∈ t, ⨆ ν : I →₀ ℕ, weightSpace R v M (μ + R.rootSum ν)
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · have hle : ⨆ μ ∈ t, weightSpace R v M μ ≤ W := iSup₂_mono fun μ _ ↦ by
      refine le_trans ?_ (le_iSup _ (0 : I →₀ ℕ))
      rw [R.rootSum_zero, add_zero]
    exact hle ht
  · have hle : W ≤ ⨆ (μ : t) (ν : (hfin μ).toFinset), weightSpace R v M (μ + R.rootSum ν) := by
      refine iSup₂_le fun μ hμ ↦ iSup_le fun ν ↦ ?_
      by_cases h : weightSpace R v M (μ + R.rootSum ν) = ⊥
      · rw [h]; exact bot_le
      · exact le_iSup_of_le ⟨μ, hμ⟩ (le_iSup_of_le ⟨ν, (hfin μ).mem_toFinset.2 h⟩ le_rfl)
    exact Submodule.finiteDimensional_of_le hle
  · intro i
    suffices W ≤ W.comap (Algebra.lsmul k k M (E R v i)) from fun y hy ↦ this hy
    refine iSup₂_le fun μ hμ ↦ iSup_le fun ν y hy ↦ ?_
    rw [Submodule.mem_comap, Algebra.lsmul_apply]
    refine Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ
      (Submodule.mem_iSup_of_mem (ν + Finsupp.single i 1) ?_))
    have := E_smul_mem_weightSpace hy i
    rwa [R.rootSum_add, R.rootSum_single, one_smul, ← add_assoc]
  · intro μ'
    suffices W ≤ W.comap (Algebra.lsmul k k M (K R v μ')) from fun y hy ↦ this hy
    refine iSup₂_le fun μ hμ ↦ iSup_le fun ν y hy ↦ ?_
    rw [Submodule.mem_comap, Algebra.lsmul_apply]
    exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ
      (Submodule.mem_iSup_of_mem ν (K_smul_mem_weightSpace hy μ')))

/-! ### Complete reducibility -/

section CompleteReducibility

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) [Finite I] [CharZero k]
  (hvt : Transcendental ℚ v) (hR : R.IsXRegular)

include hv' hvt hR in
/-- For a finite-dimensional subspace `W` of a module in `𝒪_int`, stable under the `Eᵢ` and the
`K_μ`, the submodule `U W` is semisimple (the induction in the proof of [HK] Thm. 3.5.4). -/
theorem IsCategoryOInt.isSemisimpleModule_span (hM : IsCategoryOInt R v M) (n : ℕ) :
    ∀ W : Submodule k M, Module.finrank k W = n → FiniteDimensional k W →
      (∀ i, ∀ y ∈ W, E R v i • y ∈ W) → (∀ μ, ∀ y ∈ W, K R v μ • y ∈ W) →
      IsSemisimpleModule (QuantumGroup R v) (Submodule.span (QuantumGroup R v) (W : Set M)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hWn hWfd hE hK
  by_cases hW0 : W = ⊥
  · subst hW0
    have h : Submodule.span (QuantumGroup R v) ((⊥ : Submodule k M) : Set M) = ⊥ := by simp
    rw [h]
    exact IsSemisimpleModule.of_sSup_simples_eq_top (Subsingleton.elim _ _)
  have hgr : W ≤ ⨆ μ, W ⊓ weightSpace R v M μ := fun y hy ↦
    mem_iSup_inf_weightSpace hv' hM.isIntegrable hK hy
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀, W ⊓ weightSpace R v M Λ₀ ≠ ⊥ := by
    by_contra! h
    simp only [h, iSup_bot, le_bot_iff] at hgr
    exact hW0 hgr
  obtain ⟨Λ, hΛ, hmax⟩ := hM.exists_maximal_of_le hR
    (P := fun Λ ↦ W ⊓ weightSpace R v M Λ ≠ ⊥) (fun Λ h h' ↦ h (by rw [h', inf_bot_eq])) hΛ₀
  obtain ⟨w, hwmem, hw0⟩ := (Submodule.ne_bot_iff _).1 hΛ
  have hwW : w ∈ W := hwmem.1
  set S := Submodule.span (QuantumGroup R v) (W : Set M) with hS
  have hSint : IsIntegrable R v S := hM.isIntegrable.submodule hv' S
  have hSmax : ∀ i, weightSpace R v S (Λ + R.root i) = ⊥ := by
    intro i
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_bot]
    refine Subtype.ext (eq_zero_of_mem_span_of_mem_weightSpace hv' hE hgr ?_ y.2
      (mem_weightSpace_submodule.1 hy))
    intro μ hμ ν he
    have hν : ν + Finsupp.single i 1 ≠ 0 := fun h ↦ by
      have := congrArg (fun f : I →₀ ℕ ↦ f i) h
      simp at this
    refine hmax _ hν ?_
    have : Λ + R.rootSum (ν + Finsupp.single i 1) = μ := by
      rw [sub_eq_iff_eq_add] at he
      rw [R.rootSum_add, R.rootSum_single, one_smul, he]
      abel
    rwa [this]
  set w' : S := ⟨w, Submodule.subset_span hwW⟩
  have hw' : w' ∈ weightSpace R v S Λ := mem_weightSpace_submodule.2 hwmem.2
  have hw'0 : w' ≠ 0 := fun h ↦ hw0 (congrArg Subtype.val h)
  obtain ⟨-, ⟨e⟩, N, hc⟩ := exists_isCompl_span_of_maximal hv' hvt hR hSint hSmax hw' hw'0
  have hL : IsSemisimpleModule (QuantumGroup R v) (Submodule.span (QuantumGroup R v) {w'}) := by
    have := IrreducibleModule.isSimpleModule hR hv' Λ
    exact IsSemisimpleModule.congr e.symm
  let p := Submodule.projectionOnto N (Submodule.span (QuantumGroup R v) {w'}) hc.symm
  let ψ : S →ₗ[QuantumGroup R v] M := S.subtype ∘ₗ N.subtype ∘ₗ p
  have hψN : ∀ y : N, ψ y = ((y : S) : M) := fun y ↦ by
    simp [ψ, p, Submodule.projectionOnto_apply_left]
  have hψw : ψ w' = 0 := by
    have : p w' = 0 :=
      Submodule.projectionOnto_apply_right hc.symm ⟨w', Submodule.mem_span_singleton_self w'⟩
    simp [ψ, this]
  let ι : W →ₗ[k] S :=
    { toFun := fun y ↦ ⟨y, Submodule.subset_span y.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let g : W →ₗ[k] M := ψ.restrictScalars k ∘ₗ ι
  set W' := LinearMap.range g
  have hW'lt : Module.finrank k W' < n := by
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    have h2 : Module.finrank k (LinearMap.ker g) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro h
      have hker : (⟨w, hwW⟩ : W) ∈ LinearMap.ker g := by
        rw [LinearMap.mem_ker]
        exact hψw
      rw [h, Submodule.mem_bot] at hker
      exact hw0 (congrArg Subtype.val hker)
    change Module.finrank k W' + _ = _ at h1
    omega
  have hE' : ∀ i, ∀ y ∈ W', E R v i • y ∈ W' := by
    rintro i _ ⟨y, rfl⟩
    refine ⟨⟨E R v i • (y : M), hE i y y.2⟩, ?_⟩
    change ψ (ι _) = E R v i • ψ (ι y)
    rw [← map_smul]
    exact congrArg ψ (Subtype.ext rfl)
  have hK' : ∀ μ, ∀ y ∈ W', K R v μ • y ∈ W' := by
    rintro μ _ ⟨y, rfl⟩
    refine ⟨⟨K R v μ • (y : M), hK μ y y.2⟩, ?_⟩
    change ψ (ι _) = K R v μ • ψ (ι y)
    rw [← map_smul]
    exact congrArg ψ (Subtype.ext rfl)
  have hIH := ih _ hW'lt W' rfl inferInstance hE' hK'
  have hrange : ∀ m : S, ψ m ∈ Submodule.span (QuantumGroup R v) (W' : Set M) := by
    intro m
    have hm : m ∈ Submodule.span (QuantumGroup R v) (((↑) : S → M) ⁻¹' (W : Set M)) := by
      rw [Submodule.span_span_coe_preimage]
      trivial
    induction hm using Submodule.span_induction with
    | mem m hm => exact Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul u a _ ha => rw [map_smul]; exact Submodule.smul_mem _ u ha
  let χ : N →ₗ[QuantumGroup R v] Submodule.span (QuantumGroup R v) (W' : Set M) :=
    (ψ ∘ₗ N.subtype).codRestrict _ fun y ↦ hrange y
  have hχ : Function.Injective χ := by
    intro a b hab
    have h : ψ a = ψ b := by
      have := congrArg (fun z : Submodule.span (QuantumGroup R v) (W' : Set M) ↦ (z : M)) hab
      exact this
    rw [hψN, hψN] at h
    exact Subtype.ext (Subtype.ext h)
  have hN : IsSemisimpleModule (QuantumGroup R v) N := .of_injective χ hχ
  have hsup := IsSemisimpleModule.sup hL hN
  rw [hc.sup_eq_top] at hsup
  exact IsSemisimpleModule.congr Submodule.topEquiv.symm

include hv' hvt hR in
/-- Every module in `𝒪_int` is semisimple. -/
theorem IsCategoryOInt.isSemisimpleModule (hM : IsCategoryOInt R v M) :
    IsSemisimpleModule (QuantumGroup R v) M := by
  choose W hxW hfd hE hK using hM.exists_finiteDimensional hR
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun x ↦ Submodule.span (QuantumGroup R v) (W x : Set M))
    (fun x ↦ hM.isSemisimpleModule_span hv' hvt hR _ (W x) rfl (hfd x) (hE x) (hK x)) ?_
  rw [eq_top_iff]
  intro x _
  exact Submodule.mem_iSup_of_mem x (Submodule.subset_span (hxW x))

include hv' hvt hR in
/-- **[HK] Thm. 3.5.4.** Every module `M` in `𝒪_int` is isomorphic to a direct sum `⊕ⱼ L_q(Λⱼ)`
of irreducible highest weight modules with dominant highest weights. The summands are indexed by a
set of submodules of `M`. -/
theorem IsCategoryOInt.exists_linearEquiv_dfinsupp (hM : IsCategoryOInt R v M) :
    ∃ (s : Set (Submodule (QuantumGroup R v) M)) (Λ : s → Y →+ ℤ),
      (∀ j i, 0 ≤ Λ j (R.coroot i)) ∧
        Nonempty ((Π₀ j : s, IrreducibleModule R v (Λ j)) ≃ₗ[QuantumGroup R v] M) := by
  have := hM.isSemisimpleModule hv' hvt hR
  obtain ⟨s, e, -, hsimple⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp (QuantumGroup R v) M
  have key : ∀ m : s, ∃ Λ : Y →+ ℤ, (∀ i, 0 ≤ Λ (R.coroot i)) ∧
      Nonempty (IrreducibleModule R v Λ ≃ₗ[QuantumGroup R v] m.1) := fun m ↦ by
    have := hsimple m
    exact (hM.submodule hv' m.1).exists_nonempty_equiv_of_isSimpleModule hv' hvt hR
  choose Λ hΛ he using key
  exact ⟨s, Λ, hΛ, ⟨(DFinsupp.mapRange.linearEquiv fun m ↦ (he m).some).trans e.symm⟩⟩

end CompleteReducibility

end LieLean.QuantumGroup
