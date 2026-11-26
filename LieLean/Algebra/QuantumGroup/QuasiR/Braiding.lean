/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.QuasiR.TensorInvolution

/-!
# The braiding of modules with weights below a highest weight

Let `M₁`, `M₂` be `U`-modules over `ℚ(v)` whose weights lie in `λ₁ - ℕ[I]` and `λ₂ - ℕ[I]`
respectively (for example highest weight modules of highest weights `λ₁`, `λ₂`), with `M₂` as
in [Lus] 3.4.7. For `m ∈ M₁^{λ₁ - ν}`, `m' ∈ M₂^{λ₂ - ν'}` put
`e(ν, ν') = ν · ν' - Σᵢ νᵢ ⟨dᵢ i, λ₂⟩ - Σᵢ ν'ᵢ ⟨dᵢ i, λ₁⟩`; this is `(μ, μ') - (λ₁, λ₂)` for the
weights `μ = λ₁ - ν`, `μ' = λ₂ - ν'` and any symmetric bilinear form on weights with
`(i', μ) = ⟨dᵢ i, μ⟩`, but needs no such form on all of `X`. The map
`σ(m ⊗ m') = v^{e(ν, ν')} s(Θ̄ (m ⊗ m'))`, `s` the flip, is an isomorphism of `U`-modules
`M₁ ⊗ M₂ → M₂ ⊗ M₁` (`braidingEquiv`). If `m'` is a highest weight vector then
`σ(m ⊗ m') = v^{e(ν, 0)} m' ⊗ m` (`braiding_tmul_of_highest`). Up to the scalar `v^{(λ₁, λ₂)}`,
when the pairing `(λ₁, λ₂)` is defined, this is the braiding of B. Webster, *Knot invariants and
higher representation theory*, arXiv:1309.3796v3, (1.1), which on `m ⊗ m'` with `m'` highest
weight is `v^{(μ, λ₂)} m' ⊗ m`: Webster's coproduct `Δ(Eᵢ) = Eᵢ ⊗ 1 + K̃ᵢ ⊗ Eᵢ`,
`Δ(Fᵢ) = Fᵢ ⊗ K̃₋ᵢ + 1 ⊗ Fᵢ` is the coproduct `comul` used here.

A `U`-linear map out of `M₁ ⊗ M₂` is determined by its values on `M₁ ⊗ S`, for `S` a set
generating `M₂` as a `U`-module (`ext_tmul_of_span`): this is the uniqueness used in
Webster's proof of Corollary 6.11 (v2: Corollary 6.10).

## Main definitions and results

* `QuantumGroup.quasiRBarAct`: the operator `Θ̄` on `M₁ ⊗ M₂`, inverse to `Θ`
  (`quasiRAct_quasiRBarAct`, `quasiRBarAct_quasiRAct`, [Lus] 4.1.3), with
  `Θ̄ Δ(u) = Δ̄(u) Θ̄` (`quasiRBarAct_act`).
* `QuantumGroup.depthTwist`: `m ⊗ m' ↦ v^{e(ν, ν')} m' ⊗ m` for weight vectors of depths `ν`, `ν'`.
* `QuantumGroup.braiding`, `QuantumGroup.braidingEquiv`: the `U`-linear isomorphism `σ`.
* `QuantumGroup.braiding_tmul_of_highest`, `QuantumGroup.ext_tmul_of_span`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 3.4.7, 4.1.2, 4.1.3.
* B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, (1.1),
  Corollary 6.11.
-/

open LieLean LusztigF TensorProduct DirectSum Finset.HasAntidiagonal

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

section Inverse

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module 𝕂 M₁] [Module (QuantumGroup R 𝕧) M₁]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₁]
  [AddCommGroup M₂] [Module 𝕂 M₂] [Module (QuantumGroup R 𝕧) M₂]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂] [Finite I]

local notation "act₂" => TensorModule.actPair R 𝕧 M₁ M₂

lemma barTensor_quasiR_mem_plusPart (ν : I →₀ ℕ) :
    barTensor R (quasiR R ν) ∈ plusPart R ν :=
  barTensor_mem_plusPart (quasiR_mem_plusPart ν)

/-- The operator `Θ̄ = Σ_ν Θ̄_ν` on `M₁ ⊗ M₂`, for `M₂` with the property of [Lus] 3.4.7. -/
def quasiRBarAct (h : IsPlusLocallyNilpotent R M₂) : M₁ ⊗[𝕂] M₂ →ₗ[𝕂] M₁ ⊗[𝕂] M₂ where
  toFun z := ∑ᶠ ν, act₂ (barTensor R (quasiR R ν)) z
  map_add' a b := by
    simp only [map_add]
    exact finsum_add_distrib (support_actPair_finite h barTensor_quasiR_mem_plusPart a)
      (support_actPair_finite h barTensor_quasiR_mem_plusPart b)
  map_smul' c z := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum c _).symm

theorem quasiRBarAct_apply (h : IsPlusLocallyNilpotent R M₂) (z : M₁ ⊗[𝕂] M₂) :
    quasiRBarAct h z = ∑ᶠ ν, act₂ (barTensor R (quasiR R ν)) z := rfl

/-- The composite of two operators `Σ_ν S_ν`, `Σ_ν T_ν` with `S_ν, T_ν ∈ U ⊗ U⁺_ν` is the
operator `Σ_ν Σ_{ν' + ν'' = ν} S_{ν'} T_{ν''}`. -/
lemma finsum_actPair_finsum (h : IsPlusLocallyNilpotent R M₂)
    {S T : (I →₀ ℕ) → QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧}
    (hS : ∀ ν, S ν ∈ plusPart R ν) (hT : ∀ ν, T ν ∈ plusPart R ν) (z : M₁ ⊗[𝕂] M₂) :
    ∑ᶠ ν, act₂ (S ν) (∑ᶠ ν', act₂ (T ν') z) =
      ∑ᶠ ν, act₂ (∑ p ∈ antidiagonal ν, S p.1 * T p.2) z := by
  have hST : ∀ ν, (∑ p ∈ antidiagonal ν, S p.1 * T p.2) ∈ plusPart R ν := fun ν ↦
    Submodule.sum_mem _ fun p hp ↦ by
      rw [mem_antidiagonal] at hp
      exact hp ▸ mul_mem_plusPart (hS p.1) (hT p.2)
  induction z using TensorProduct.inductionOn with
  | add a b ha hb =>
    simp only [map_add]
    rw [finsum_add_distrib (support_actPair_finite h hT a) (support_actPair_finite h hT b)]
    simp only [map_add]
    rw [finsum_add_distrib (support_actPair_finite h hS _) (support_actPair_finite h hS _),
      finsum_add_distrib (support_actPair_finite h hST a) (support_actPair_finite h hST b),
      ha, hb]
  | tmul x y =>
    obtain ⟨N, hN⟩ := plusHom_smul_eq_zero h y
    set F := (Finsupp.finite_of_degree_lt (σ := I) (N + 1)).toFinset
    have hF (ν : I →₀ ℕ) : ν ∈ F ↔ ν.degree < N + 1 := by simp [F]
    have hvan {ν' ν'' : I →₀ ℕ} (hd : N ≤ ν'.degree + ν''.degree) :
        act₂ (S ν' * T ν'') (x ⊗ₜ y) = 0 :=
      actPair_eq_zero_of_mem_plusPart (mul_mem_plusPart (hS ν') (hT ν''))
        (hN _ (by rwa [_root_.map_add])) x
    set a : (I →₀ ℕ) × (I →₀ ℕ) → M₁ ⊗[𝕂] M₂ := fun p ↦ act₂ (S p.1 * T p.2) (x ⊗ₜ y)
    have h1 : ∑ᶠ ν', act₂ (T ν') (x ⊗ₜ y) = ∑ ν' ∈ F, act₂ (T ν') (x ⊗ₜ y) := by
      refine finsum_eq_sum_of_support_subset _ fun ν hν ↦ ?_
      rw [Finset.mem_coe, hF]
      by_contra hc
      exact hν (actPair_eq_zero_of_mem_plusPart (hT ν) (hN ν (by omega)) x)
    have h2 : ∑ᶠ ν, act₂ (S ν) (∑ ν' ∈ F, act₂ (T ν') (x ⊗ₜ y)) =
        ∑ ν ∈ F, ∑ ν' ∈ F, a (ν, ν') := by
      refine (finsum_eq_sum_of_support_subset _ fun ν hν ↦ ?_).trans
        (Finset.sum_congr rfl fun ν _ ↦ ?_)
      · rw [Finset.mem_coe, hF]
        by_contra hc
        refine hν ?_
        beta_reduce
        rw [map_sum]
        exact Finset.sum_eq_zero fun ν' _ ↦ by
          rw [← Module.End.mul_apply, ← _root_.map_mul]
          exact hvan (by omega)
      · rw [map_sum]
        exact Finset.sum_congr rfl fun ν' _ ↦ by
          simp only [a, _root_.map_mul, Module.End.mul_apply]
    have h3 : ∑ ν ∈ F, ∑ ν' ∈ F, a (ν, ν') =
        ∑ ν ∈ F, ∑ p ∈ antidiagonal ν, a p := by
      rw [← Finset.sum_product' (f := fun ν ν' ↦ a (ν, ν'))]
      set T' := (F ×ˢ F).filter fun p ↦ p.1 + p.2 ∈ F
      have e1 : ∑ p ∈ F ×ˢ F, a p = ∑ p ∈ T', a p := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) fun p hp hpT ↦ ?_).symm
        simp only [Finset.mem_filter, not_and, hF] at hpT
        exact hvan (by have := hpT hp; rw [_root_.map_add] at this; omega)
      rw [e1, Finset.sum_sigma']
      refine Finset.sum_nbij' (fun p ↦ ⟨p.1 + p.2, p⟩) (fun q ↦ q.2) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        simp only [T', Finset.mem_filter] at hp
        simp [Finset.mem_sigma, hp.2]
      · rintro ⟨ν, p⟩ hq
        simp only [Finset.mem_sigma, mem_antidiagonal] at hq
        obtain ⟨hν, rfl⟩ := hq
        simp only [T', Finset.mem_filter, Finset.mem_product, hF] at hν ⊢
        rw [_root_.map_add] at hν
        exact ⟨⟨by omega, by omega⟩, by rw [_root_.map_add]; omega⟩
      · intro p _; rfl
      · rintro ⟨ν, p⟩ hq
        simp only [Finset.mem_sigma, mem_antidiagonal] at hq
        obtain ⟨_, rfl⟩ := hq
        rfl
      · intro p _; rfl
    have h4 : ∑ᶠ ν, act₂ (∑ p ∈ antidiagonal ν, S p.1 * T p.2) (x ⊗ₜ y) =
        ∑ ν ∈ F, ∑ p ∈ antidiagonal ν, a p := by
      refine (finsum_eq_sum_of_support_subset _ fun ν hν ↦ ?_).trans
        (Finset.sum_congr rfl fun ν _ ↦ ?_)
      · rw [Finset.mem_coe, hF]
        by_contra hc
        exact hν (actPair_eq_zero_of_mem_plusPart (hST ν) (hN ν (by omega)) x)
      · rw [map_sum, LinearMap.sum_apply]
    rw [h1, h2, h3, h4]

/-- `Θ Θ̄ = 1` on `M₁ ⊗ M₂` ([Lus] 4.1.3). -/
theorem quasiRAct_quasiRBarAct (h : IsPlusLocallyNilpotent R M₂) (z : M₁ ⊗[𝕂] M₂) :
    quasiRAct h (quasiRBarAct h z) = z :=
  quasiRAct_finsum_barTensor h z

/-- `Θ̄ Θ = 1` on `M₁ ⊗ M₂` ([Lus] 4.1.3). -/
theorem quasiRBarAct_quasiRAct (h : IsPlusLocallyNilpotent R M₂) (z : M₁ ⊗[𝕂] M₂) :
    quasiRBarAct h (quasiRAct h z) = z := by
  rw [quasiRBarAct_apply, quasiRAct_apply,
    finsum_actPair_finsum h barTensor_quasiR_mem_plusPart quasiR_mem_plusPart z]
  simp_rw [sum_barTensor_mul_quasiR]
  rw [finsum_eq_single _ 0 fun ν hν ↦ by simp [hν]]
  simp

/-- `Θ̄ Δ(u) = Δ̄(u) Θ̄` on `M₁ ⊗ M₂`, from [Lus] 4.1.2 (a) and 4.1.3. -/
theorem quasiRBarAct_act (h : IsPlusLocallyNilpotent R M₂) (u : QuantumGroup R 𝕧)
    (z : M₁ ⊗[𝕂] M₂) :
    quasiRBarAct h (TensorModule.act R 𝕧 M₁ M₂ u z) =
      act₂ (barComul R u) (quasiRBarAct h z) := by
  conv_lhs => rw [← quasiRAct_quasiRBarAct h z]
  rw [act_quasiRAct, quasiRBarAct_quasiRAct]

/-- `Θ̄ (x ⊗ y) = x ⊗ y` when `y` is killed by `U⁺_ν` for every `ν ≠ 0`. -/
theorem quasiRBarAct_tmul_of_highest (h : IsPlusLocallyNilpotent R M₂) (x : M₁) {y : M₂}
    (hy : ∀ ν : I →₀ ℕ, ν ≠ 0 → ∀ x' ∈ LusztigF.weightSpace 𝕂 ν, plusHom R 𝕧 x' • y = 0) :
    quasiRBarAct h (x ⊗ₜ y) = x ⊗ₜ y := by
  rw [quasiRBarAct_apply, finsum_eq_single _ 0 fun ν hν ↦
    actPair_eq_zero_of_mem_plusPart (barTensor_quasiR_mem_plusPart ν) (hy ν hν) x,
    quasiR_zero, barTensor_one, _root_.map_one, Module.End.one_apply]

end Inverse

/-! ### Weight spaces of a given depth -/

section Depth

variable (R) in
/-- The weight space `M^{Λ - ν}` of depth `ν ∈ ℕ[I]` below `Λ`. -/
abbrev depthSpace (M : Type*) [AddCommGroup M] [Module 𝕂 M] [Module (QuantumGroup R 𝕧) M]
    [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M] (Λ : Y →+ ℤ) (ν : I →₀ ℕ) : Submodule 𝕂 M :=
  weightSpace R 𝕧 M (Λ - R.rootSum ν)

omit [DecidableEq I] in
private lemma rootSum_injective (hR : R.IsXRegular) : Function.Injective R.rootSum := by
  intro ν ν' h
  by_contra hne
  obtain ⟨μ, hμ⟩ := R.exists_rootSum_ne hR hne
  exact hμ (by rw [h])

variable {M : Type*} [AddCommGroup M] [Module 𝕂 M] [Module (QuantumGroup R 𝕧) M]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M] {Λ : Y →+ ℤ}

lemma iSupIndep_depthSpace (hR : R.IsXRegular) : iSupIndep (depthSpace R M Λ) :=
  iSupIndep.comp (t := weightSpace R 𝕧 M)
    (iSupIndep_weightSpace (R := R) (M := M) fun _ hn ↦ ratFunc_X_pow_ne_one hn)
    fun _ _ h ↦ rootSum_injective hR (sub_right_injective h)

lemma isInternal_depthSpace (hR : R.IsXRegular) (hM : ⨆ ν, depthSpace R M Λ ν = ⊤) :
    DirectSum.IsInternal (depthSpace R M Λ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_depthSpace hR) hM

/-- A weight off the grid `Λ - ℕ[I]` has zero weight space. -/
lemma weightSpace_eq_bot_of_depth (hM : ⨆ ν, depthSpace R M Λ ν = ⊤) {Λ' : Y →+ ℤ}
    (h : ∀ ν, Λ' ≠ Λ - R.rootSum ν) : weightSpace R 𝕧 M Λ' = ⊥ := by
  have hle : ⨆ ν, depthSpace R M Λ ν ≤ ⨆ Λ'', ⨆ (_ : Λ'' ≠ Λ'), weightSpace R 𝕧 M Λ'' :=
    iSup_le fun ν ↦ le_iSup₂_of_le (Λ - R.rootSum ν) (Ne.symm (h ν)) le_rfl
  have := (iSupIndep_weightSpace (R := R) (M := M) (fun _ hn ↦ ratFunc_X_pow_ne_one hn)
    Λ').mono_right (hM.symm.le.trans hle)
  exact disjoint_top.1 this

/-- `Eᵢ` lowers the depth by `i`, or kills the vector. -/
lemma E_smul_mem_depthSpace (hR : R.IsXRegular) (hM : ⨆ ν, depthSpace R M Λ ν = ⊤)
    {ν : I →₀ ℕ} {m : M} (hm : m ∈ depthSpace R M Λ ν) (i : I) :
    (∃ ν₀, ν = ν₀ + Finsupp.single i 1 ∧ E R 𝕧 i • m ∈ depthSpace R M Λ ν₀) ∨
      E R 𝕧 i • m = 0 := by
  have hE := E_smul_mem_weightSpace hm i
  by_cases h : ∃ ν₀, ν = ν₀ + Finsupp.single i 1
  · obtain ⟨ν₀, rfl⟩ := h
    refine Or.inl ⟨ν₀, rfl, ?_⟩
    convert hE using 2
    rw [R.rootSum_add, R.rootSum_single, one_smul]
    abel
  · refine Or.inr ?_
    have hbot : weightSpace R 𝕧 M (Λ - R.rootSum ν + R.root i) = ⊥ := by
      refine weightSpace_eq_bot_of_depth hM fun ν'' he ↦ h ⟨ν'', rootSum_injective hR ?_⟩
      rw [R.rootSum_add, R.rootSum_single, one_smul, ← sub_eq_zero, ← neg_eq_zero]
      rw [← sub_eq_zero] at he
      convert he using 1
      abel
    rw [hbot] at hE
    exact (Submodule.mem_bot _).1 hE

/-- `Fᵢ` raises the depth by `i`. -/
lemma F_smul_mem_depthSpace {ν : I →₀ ℕ} {m : M} (hm : m ∈ depthSpace R M Λ ν) (i : I) :
    F R 𝕧 i • m ∈ depthSpace R M Λ (ν + Finsupp.single i 1) := by
  have hF := F_smul_mem_weightSpace hm i
  convert hF using 2
  rw [R.rootSum_add, R.rootSum_single, one_smul]
  abel

end Depth

/-! ### The twist `m ⊗ m' ↦ v^{e(ν, ν')} m' ⊗ m` -/

section Twist

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module 𝕂 M₁] [Module (QuantumGroup R 𝕧) M₁]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₁]
  [AddCommGroup M₂] [Module 𝕂 M₂] [Module (QuantumGroup R 𝕧) M₂]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂] {Λ₁ Λ₂ : Y →+ ℤ}

lemma isInternal_symm_apply {M : Type*} [AddCommGroup M] [Module 𝕂 M] {A : (I →₀ ℕ) → Submodule 𝕂 M}
    (h : DirectSum.IsInternal A) {ν : I →₀ ℕ} {m : M} (hm : m ∈ A ν) :
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm m =
      DirectSum.lof 𝕂 (I →₀ ℕ) (fun ν ↦ A ν) ν ⟨m, hm⟩ := by
  rw [LinearEquiv.symm_apply_eq]
  exact (DirectSum.coeLinearMap_of (A := A) ν ⟨m, hm⟩).symm

variable (R M₁ M₂ Λ₁ Λ₂) in
/-- The `𝕂`-linear map `M₁ ⊗ M₂ → M₂ ⊗ M₁`, `m ⊗ m' ↦ v^{e(ν, ν')} m' ⊗ m` for `m`, `m'` of
depths `ν`, `ν'` below `Λ₁`, `Λ₂`. -/
def depthTwist (h₁ : DirectSum.IsInternal (depthSpace R M₁ Λ₁))
    (h₂ : DirectSum.IsInternal (depthSpace R M₂ Λ₂)) (e : (I →₀ ℕ) → (I →₀ ℕ) → ℤ) :
    M₁ ⊗[𝕂] M₂ →ₗ[𝕂] M₂ ⊗[𝕂] M₁ :=
  (DirectSum.toModule 𝕂 ((I →₀ ℕ) × (I →₀ ℕ)) (M₂ ⊗[𝕂] M₁) fun p ↦
      (𝕧 ^ e p.1 p.2) • ((TensorProduct.comm 𝕂 M₁ M₂).toLinearMap ∘ₗ
        TensorProduct.map (depthSpace R M₁ Λ₁ p.1).subtype (depthSpace R M₂ Λ₂ p.2).subtype)) ∘ₗ
    (TensorProduct.directSum 𝕂 𝕂 (fun ν ↦ depthSpace R M₁ Λ₁ ν)
      (fun ν ↦ depthSpace R M₂ Λ₂ ν)).toLinearMap ∘ₗ
    TensorProduct.map (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) h₁).symm.toLinearMap
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) h₂).symm.toLinearMap

theorem depthTwist_tmul (h₁ : DirectSum.IsInternal (depthSpace R M₁ Λ₁))
    (h₂ : DirectSum.IsInternal (depthSpace R M₂ Λ₂)) (e : (I →₀ ℕ) → (I →₀ ℕ) → ℤ)
    {ν ν' : I →₀ ℕ} {m : M₁} (hm : m ∈ depthSpace R M₁ Λ₁ ν) {m' : M₂}
    (hm' : m' ∈ depthSpace R M₂ Λ₂ ν') :
    depthTwist R M₁ M₂ Λ₁ Λ₂ h₁ h₂ e (m ⊗ₜ m') = 𝕧 ^ e ν ν' • (m' ⊗ₜ m) := by
  simp only [depthTwist, LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    isInternal_symm_apply h₁ hm, isInternal_symm_apply h₂ hm',
    TensorProduct.directSum_lof_tmul_lof, DirectSum.toModule_lof, LinearMap.smul_apply]
  rfl

/-- The pure tensors of weight vectors of given depths span `M₁ ⊗ M₂`. -/
theorem span_tmul_depth (hM₁ : ⨆ ν, depthSpace R M₁ Λ₁ ν = ⊤)
    (hM₂ : ⨆ ν, depthSpace R M₂ Λ₂ ν = ⊤) :
    Submodule.span 𝕂 {z : M₁ ⊗[𝕂] M₂ | ∃ ν ν' m m', m ∈ depthSpace R M₁ Λ₁ ν ∧
      m' ∈ depthSpace R M₂ Λ₂ ν' ∧ z = m ⊗ₜ m'} = ⊤ := by
  set S := Submodule.span 𝕂 {z : M₁ ⊗[𝕂] M₂ | ∃ ν ν' m m', m ∈ depthSpace R M₁ Λ₁ ν ∧
      m' ∈ depthSpace R M₂ Λ₂ ν' ∧ z = m ⊗ₜ m'}
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => exact add_mem ha hb
  | tmul x y =>
    have hx : x ∈ ⨆ ν, depthSpace R M₁ Λ₁ ν := by rw [hM₁]; trivial
    have hy : y ∈ ⨆ ν, depthSpace R M₂ Λ₂ ν := by rw [hM₂]; trivial
    induction hx using Submodule.iSup_induction' with
    | zero => rw [zero_tmul]; exact zero_mem _
    | add x x' _ _ hx hx' => rw [add_tmul]; exact add_mem hx hx'
    | mem ν x hx =>
      induction hy using Submodule.iSup_induction' with
      | zero => rw [tmul_zero]; exact zero_mem _
      | add y y' _ _ hy hy' => rw [tmul_add]; exact add_mem hy hy'
      | mem ν' y hy => exact Submodule.subset_span ⟨ν, ν', x, y, hx, hy, rfl⟩

end Twist

/-! ### The exponent `e(ν, ν')` -/

section Exponent

variable (R) in
/-- `Σᵢ νᵢ ⟨dᵢ i, Λ⟩`, the pairing `(ν, Λ)` of `ν ∈ ℕ[I]` with `Λ ∈ X`. -/
def pairDepth (Λ : Y →+ ℤ) (ν : I →₀ ℕ) : ℤ := ν.sum fun i n ↦ n * Λ (ktilde R i)

omit [DecidableEq I] in
lemma pairDepth_add_single (Λ : Y →+ ℤ) (ν : I →₀ ℕ) (i : I) :
    pairDepth R Λ (ν + Finsupp.single i 1) = pairDepth R Λ ν + Λ (ktilde R i) := by
  rw [pairDepth, Finsupp.sum_add_index' (fun _ ↦ by simp) (fun _ _ _ ↦ by push_cast; ring),
    Finsupp.sum_single_index (by simp)]
  simp [pairDepth]

variable (R) in
/-- The exponent `e(ν, ν') = ν · ν' - (ν, Λ₂) - (ν', Λ₁)` of the braiding on vectors of depths
`ν`, `ν'` below `Λ₁`, `Λ₂`. -/
def braidExp (Λ₁ Λ₂ : Y →+ ℤ) (ν ν' : I →₀ ℕ) : ℤ :=
  D.weightDot ν ν' - pairDepth R Λ₂ ν - pairDepth R Λ₁ ν'

omit [DecidableEq I] in
private lemma rootSum_ktilde' (ν : I →₀ ℕ) (i : I) :
    R.rootSum ν (ktilde R i) = D.weightDot (Finsupp.single i 1) ν := by
  rw [LusztigCartanDatum.weightDot, Finsupp.sum_single_index (by simp)]
  simp only [LusztigCartanDatum.RootDatum.rootSum, Finsupp.sum, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.nsmul_apply, root_ktilde_eq_dot, nsmul_eq_mul, Nat.cast_one, one_mul]

omit [DecidableEq I] in
lemma braidExp_add_single_left (Λ₁ Λ₂ : Y →+ ℤ) (ν ν' : I →₀ ℕ) (i : I) :
    braidExp R Λ₁ Λ₂ (ν + Finsupp.single i 1) ν' =
      braidExp R Λ₁ Λ₂ ν ν' + R.rootSum ν' (ktilde R i) - Λ₂ (ktilde R i) := by
  rw [braidExp, braidExp, D.weightDot_add_left, pairDepth_add_single, rootSum_ktilde']
  ring

omit [DecidableEq I] in
lemma braidExp_add_single_right (Λ₁ Λ₂ : Y →+ ℤ) (ν ν' : I →₀ ℕ) (i : I) :
    braidExp R Λ₁ Λ₂ ν (ν' + Finsupp.single i 1) =
      braidExp R Λ₁ Λ₂ ν ν' + R.rootSum ν (ktilde R i) - Λ₁ (ktilde R i) := by
  rw [braidExp, braidExp, D.weightDot_add_right, pairDepth_add_single, rootSum_ktilde',
    D.weightDot_comm (Finsupp.single i 1)]
  ring

omit [DecidableEq I] in
@[simp] lemma braidExp_zero_right (Λ₁ Λ₂ : Y →+ ℤ) (ν : I →₀ ℕ) :
    braidExp R Λ₁ Λ₂ ν 0 = -pairDepth R Λ₂ ν := by
  simp [braidExp, pairDepth]

end Exponent

/-! ### The braiding -/

section Braiding

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module 𝕂 M₁] [Module (QuantumGroup R 𝕧) M₁]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₁]
  [AddCommGroup M₂] [Module 𝕂 M₂] [Module (QuantumGroup R 𝕧) M₂]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂] {Λ₁ Λ₂ : Y →+ ℤ}
  (hR : R.IsXRegular) (hM₁ : ⨆ ν, depthSpace R M₁ Λ₁ ν = ⊤)
  (hM₂ : ⨆ ν, depthSpace R M₂ Λ₂ ν = ⊤)

local notation "act₂" => TensorModule.actPair R 𝕧 M₁ M₂
local notation "τ" => depthTwist R M₁ M₂ Λ₁ Λ₂ (isInternal_depthSpace hR hM₁)
  (isInternal_depthSpace hR hM₂) (braidExp R Λ₁ Λ₂)

include hR hM₁ hM₂ in
/-- The twist intertwines `Δ̄` on `M₁ ⊗ M₂` with `Δ` on `M₂ ⊗ M₁`. -/
theorem depthTwist_actPair_barComul (u : QuantumGroup R 𝕧) (z : M₁ ⊗[𝕂] M₂) :
    τ (act₂ (barComul R u) z) = TensorModule.act R 𝕧 M₂ M₁ u (τ z) := by
  have hτ (ν ν' : I →₀ ℕ) {m : M₁} (hm : m ∈ depthSpace R M₁ Λ₁ ν) {m' : M₂}
      (hm' : m' ∈ depthSpace R M₂ Λ₂ ν') :=
    depthTwist_tmul (isInternal_depthSpace hR hM₁) (isInternal_depthSpace hR hM₂)
      (braidExp R Λ₁ Λ₂) hm hm'
  have hv (a b : ℤ) : (𝕧 ^ a * 𝕧 ^ b : 𝕂) = 𝕧 ^ (a + b) :=
    (zpow_add₀ RatFunc.X_ne_zero a b).symm
  have hx (a b : ℤ) (w : M₂ ⊗[𝕂] M₁) (hab : a = b) : 𝕧 ^ a • w = 𝕧 ^ b • w := by rw [hab]
  suffices h : τ ∘ₗ act₂ (barComul R u) = TensorModule.act R 𝕧 M₂ M₁ u ∘ₗ τ from
    LinearMap.congr_fun h z
  induction u using QuantumGroup.induction_on with
  | algebraMap c =>
    refine LinearMap.ext fun z ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, barComul_algebraMap, AlgHom.commutes,
      AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hx, hy]
  | mul x y hx hy =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← LinearMap.comp_assoc, hx, LinearMap.comp_assoc, hy, LinearMap.comp_assoc]
  | E i =>
    refine LinearMap.ext_on (span_tmul_depth hM₁ hM₂) ?_
    rintro _ ⟨ν, ν', m, m', hm, hm', rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, barComul_E, map_add, LinearMap.add_apply,
      TensorModule.act_tmul, TensorModule.act_tmul, one_smul, map_add, hτ ν ν' hm hm', map_smul,
      TensorModule.act, AlgHom.comp_apply, comul_E, map_add, LinearMap.add_apply,
      TensorModule.act_tmul, TensorModule.act_tmul, one_smul, smul_add]
    have hA : τ ((E R 𝕧 i • m) ⊗ₜ m') =
        𝕧 ^ braidExp R Λ₁ Λ₂ ν ν' • ((Kt R 𝕧 i • m') ⊗ₜ (E R 𝕧 i • m)) := by
      rcases E_smul_mem_depthSpace hR hM₁ hm i with ⟨ν₀, rfl, hE⟩ | hE
      · rw [hτ ν₀ ν' hE hm', Kt, hm' (ktilde R i), ← smul_tmul' (𝕧 ^ _ : 𝕂), smul_smul, hv]
        refine hx _ _ _ ?_
        rw [braidExp_add_single_left]
        simp only [AddMonoidHom.sub_apply]
        ring
      · rw [hE, zero_tmul, map_zero, tmul_zero, smul_zero]
    have hB : τ ((K R 𝕧 (-ktilde R i) • m) ⊗ₜ (E R 𝕧 i • m')) =
        𝕧 ^ braidExp R Λ₁ Λ₂ ν ν' • ((E R 𝕧 i • m') ⊗ₜ m) := by
      rw [hm (-ktilde R i), ← smul_tmul' (𝕧 ^ _ : 𝕂) m, map_smul]
      rcases E_smul_mem_depthSpace hR hM₂ hm' i with ⟨ν₀, rfl, hE⟩ | hE
      · rw [hτ ν ν₀ hm hE, smul_smul, hv]
        refine hx _ _ _ ?_
        rw [braidExp_add_single_right]
        simp only [map_neg, AddMonoidHom.sub_apply]
        ring
      · rw [hE, tmul_zero, map_zero, zero_tmul, smul_zero, smul_zero]
    rw [hA, hB, add_comm]
  | F i =>
    refine LinearMap.ext_on (span_tmul_depth hM₁ hM₂) ?_
    rintro _ ⟨ν, ν', m, m', hm, hm', rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, barComul_F, map_add, LinearMap.add_apply,
      TensorModule.act_tmul, TensorModule.act_tmul, one_smul, map_add, hτ ν ν' hm hm', map_smul,
      TensorModule.act, AlgHom.comp_apply, comul_F, map_add, LinearMap.add_apply,
      TensorModule.act_tmul, TensorModule.act_tmul, one_smul, smul_add]
    have hC : τ ((F R 𝕧 i • m) ⊗ₜ (K R 𝕧 (ktilde R i) • m')) =
        𝕧 ^ braidExp R Λ₁ Λ₂ ν ν' • (m' ⊗ₜ (F R 𝕧 i • m)) := by
      rw [hm' (ktilde R i), tmul_smul (𝕧 ^ _ : 𝕂), map_smul,
        hτ _ ν' (F_smul_mem_depthSpace hm i) hm', smul_smul, hv]
      refine hx _ _ _ ?_
      rw [braidExp_add_single_left]
      simp only [AddMonoidHom.sub_apply]
      ring
    have hD : τ (m ⊗ₜ (F R 𝕧 i • m')) =
        𝕧 ^ braidExp R Λ₁ Λ₂ ν ν' • ((F R 𝕧 i • m') ⊗ₜ (K R 𝕧 (-ktilde R i) • m)) := by
      rw [hτ ν _ hm (F_smul_mem_depthSpace hm' i), hm (-ktilde R i), tmul_smul (𝕧 ^ _ : 𝕂),
        smul_smul, hv]
      refine hx _ _ _ ?_
      rw [braidExp_add_single_right]
      simp only [map_neg, AddMonoidHom.sub_apply]
      ring
    rw [hC, hD, add_comm]
  | K μ =>
    refine LinearMap.ext_on (span_tmul_depth hM₁ hM₂) ?_
    rintro _ ⟨ν, ν', m, m', hm, hm', rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, barComul_K, TensorModule.act_tmul,
      hτ ν ν' hm hm', map_smul, TensorModule.act, AlgHom.comp_apply, comul_K,
      TensorModule.act_tmul, hm μ, hm' μ, ← smul_tmul' (𝕧 ^ (Λ₁ - R.rootSum ν) μ : 𝕂),
      tmul_smul (𝕧 ^ (Λ₂ - R.rootSum ν') μ : 𝕂), ← smul_tmul' (𝕧 ^ (Λ₂ - R.rootSum ν') μ : 𝕂),
      tmul_smul (𝕧 ^ (Λ₁ - R.rootSum ν) μ : 𝕂), map_smul, map_smul, hτ ν ν' hm hm']
    simp only [smul_smul]
    congr 1
    ring

variable [Finite I] (h : IsPlusLocallyNilpotent R M₂)

/-- The braiding `σ = v^{e} s Θ̄ : M₁ ⊗ M₂ → M₂ ⊗ M₁` as a `U`-linear map. -/
def braiding : TensorModule 𝕂 M₁ M₂ →ₗ[QuantumGroup R 𝕧] TensorModule 𝕂 M₂ M₁ where
  toFun z := TensorModule.mk M₂ M₁ (τ (quasiRBarAct h ((TensorModule.mk M₁ M₂).symm z)))
  map_add' a b := by simp only [map_add]
  map_smul' u z := by
    obtain ⟨z, rfl⟩ := (TensorModule.mk M₁ M₂).surjective z
    rw [TensorModule.smul_mk, RingHom.id_apply, TensorModule.smul_mk]
    simp only [LinearEquiv.symm_apply_apply]
    rw [quasiRBarAct_act, depthTwist_actPair_barComul hR hM₁ hM₂]

theorem braiding_mk (z : M₁ ⊗[𝕂] M₂) :
    braiding hR hM₁ hM₂ h (TensorModule.mk M₁ M₂ z) =
      TensorModule.mk M₂ M₁ (τ (quasiRBarAct h z)) := rfl

/-- `σ(m ⊗ m') = v^{-(ν, Λ₂)} m' ⊗ m` for `m` of depth `ν` and `m'` a highest weight vector of
weight `Λ₂`; compare Webster, arXiv:1309.3796v3, (1.1). -/
theorem braiding_tmul_of_highest {ν : I →₀ ℕ} {m : M₁} (hm : m ∈ depthSpace R M₁ Λ₁ ν)
    {m' : M₂} (hm' : m' ∈ weightSpace R 𝕧 M₂ Λ₂)
    (hy : ∀ ν : I →₀ ℕ, ν ≠ 0 → ∀ x' ∈ LusztigF.weightSpace 𝕂 ν, plusHom R 𝕧 x' • m' = 0) :
    braiding hR hM₁ hM₂ h (TensorModule.mk M₁ M₂ (m ⊗ₜ m')) =
      TensorModule.mk M₂ M₁ (𝕧 ^ (-pairDepth R Λ₂ ν) • (m' ⊗ₜ m)) := by
  have hm'0 : m' ∈ depthSpace R M₂ Λ₂ 0 := by simpa [depthSpace] using hm'
  rw [braiding_mk, quasiRBarAct_tmul_of_highest h m hy,
    depthTwist_tmul _ _ _ hm hm'0, braidExp_zero_right]

local notation "τ'" => depthTwist R M₂ M₁ Λ₂ Λ₁ (isInternal_depthSpace hR hM₂)
  (isInternal_depthSpace hR hM₁) (fun ν' ν ↦ -braidExp R Λ₁ Λ₂ ν ν')

omit [Finite I] in
include hR hM₁ hM₂ in
private lemma depthTwist_inv_left (z : M₁ ⊗[𝕂] M₂) : τ' (τ z) = z := by
  suffices h : τ' ∘ₗ τ = LinearMap.id from LinearMap.congr_fun h z
  refine LinearMap.ext_on (span_tmul_depth hM₁ hM₂) ?_
  rintro _ ⟨ν, ν', m, m', hm, hm', rfl⟩
  rw [LinearMap.comp_apply, depthTwist_tmul _ _ _ hm hm', map_smul, depthTwist_tmul _ _ _ hm' hm,
    smul_smul, ← zpow_add₀ RatFunc.X_ne_zero, add_neg_cancel, zpow_zero, one_smul,
    LinearMap.id_apply]

omit [Finite I] in
include hR hM₁ hM₂ in
private lemma depthTwist_inv_right (z : M₂ ⊗[𝕂] M₁) : τ (τ' z) = z := by
  suffices h : τ ∘ₗ τ' = LinearMap.id from LinearMap.congr_fun h z
  refine LinearMap.ext_on (span_tmul_depth hM₂ hM₁) ?_
  rintro _ ⟨ν', ν, m', m, hm', hm, rfl⟩
  rw [LinearMap.comp_apply, depthTwist_tmul _ _ _ hm' hm, map_smul, depthTwist_tmul _ _ _ hm hm',
    smul_smul, ← zpow_add₀ RatFunc.X_ne_zero, neg_add_cancel, zpow_zero, one_smul,
    LinearMap.id_apply]

/-- The braiding `σ : M₁ ⊗ M₂ ≅ M₂ ⊗ M₁` as an isomorphism of `U`-modules. -/
def braidingEquiv : TensorModule 𝕂 M₁ M₂ ≃ₗ[QuantumGroup R 𝕧] TensorModule 𝕂 M₂ M₁ :=
  { braiding hR hM₁ hM₂ h with
    invFun := fun w ↦ TensorModule.mk M₁ M₂ (quasiRAct h (τ' ((TensorModule.mk M₂ M₁).symm w)))
    left_inv := fun z ↦ by
      obtain ⟨z, rfl⟩ := (TensorModule.mk M₁ M₂).surjective z
      change TensorModule.mk M₁ M₂ (quasiRAct h (τ' (τ (quasiRBarAct h z)))) = _
      rw [depthTwist_inv_left hR hM₁ hM₂, quasiRAct_quasiRBarAct]
    right_inv := fun w ↦ by
      obtain ⟨w, rfl⟩ := (TensorModule.mk M₂ M₁).surjective w
      change TensorModule.mk M₂ M₁ (τ (quasiRBarAct h (quasiRAct h (τ' w)))) = _
      rw [quasiRBarAct_quasiRAct, depthTwist_inv_right hR hM₁ hM₂] }

theorem braidingEquiv_apply (z : TensorModule 𝕂 M₁ M₂) :
    braidingEquiv hR hM₁ hM₂ h z = braiding hR hM₁ hM₂ h z := rfl

end Braiding

/-! ### Uniqueness -/

section Ext

variable {M₁ M₂ N : Type*} [AddCommGroup M₁] [Module 𝕂 M₁] [Module (QuantumGroup R 𝕧) M₁]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₁]
  [AddCommGroup M₂] [Module 𝕂 M₂] [Module (QuantumGroup R 𝕧) M₂]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂]
  [AddCommGroup N] [Module (QuantumGroup R 𝕧) N]

/-- Two `U`-linear maps out of `M₁ ⊗ M₂` agreeing on `M₁ ⊗ S`, for a set `S` generating `M₂`
as a `U`-module, are equal. -/
theorem ext_tmul_of_span {f g : TensorModule 𝕂 M₁ M₂ →ₗ[QuantumGroup R 𝕧] N} {S : Set M₂}
    (hS : Submodule.span (QuantumGroup R 𝕧) S = ⊤)
    (hfg : ∀ x, ∀ y ∈ S,
      f (TensorModule.mk M₁ M₂ (x ⊗ₜ[𝕂] y)) = g (TensorModule.mk M₁ M₂ (x ⊗ₜ[𝕂] y))) :
    f = g := by
  let P : Set M₂ := {y | ∀ x, f (TensorModule.mk M₁ M₂ (x ⊗ₜ[𝕂] y)) =
    g (TensorModule.mk M₁ M₂ (x ⊗ₜ[𝕂] y))}
  have hadd {y y' : M₂} (hy : y ∈ P) (hy' : y' ∈ P) : y + y' ∈ P := fun x ↦ by
    rw [tmul_add, map_add, map_add, map_add, hy x, hy' x]
  have hzero : (0 : M₂) ∈ P := fun x ↦ by rw [tmul_zero, map_zero, map_zero, map_zero]
  have hsmul (c : 𝕂) {y : M₂} (hy : y ∈ P) : c • y ∈ P := fun x ↦ by
    rw [tmul_smul, (TensorModule.mk M₁ M₂).map_smul c,
      ← algebraMap_smul (QuantumGroup R 𝕧) c (TensorModule.mk M₁ M₂ (x ⊗ₜ[𝕂] y)), f.map_smul,
      g.map_smul, hy x]
  -- `U` preserves `P`.
  have hK (μ : Y) {y : M₂} (hy : y ∈ P) : K R 𝕧 μ • y ∈ P := fun x ↦ by
    have e : TensorModule.mk M₁ M₂ (x ⊗ₜ[𝕂] (K R 𝕧 μ • y)) =
        K R 𝕧 μ • TensorModule.mk M₁ M₂ ((K R 𝕧 (-μ) • x) ⊗ₜ[𝕂] y) := by
      rw [TensorModule.K_smul_tmul, ← mul_smul, K_mul_K_neg, one_smul]
    rw [e, map_smul, map_smul, hy (K R 𝕧 (-μ) • x)]
  have hE (i : I) {y : M₂} (hy : y ∈ P) : E R 𝕧 i • y ∈ P := fun x ↦ by
    have e : TensorModule.mk M₁ M₂ (x ⊗ₜ[𝕂] (E R 𝕧 i • y)) =
        E R 𝕧 i • TensorModule.mk M₁ M₂ ((K R 𝕧 (-ktilde R i) • x) ⊗ₜ[𝕂] y) -
          TensorModule.mk M₁ M₂ ((E R 𝕧 i • K R 𝕧 (-ktilde R i) • x) ⊗ₜ[𝕂] y) := by
      rw [TensorModule.E_smul_tmul, map_add, add_sub_cancel_left, Kt, ← mul_smul, K_mul_K_neg,
        one_smul]
    rw [e, map_sub, map_sub, map_smul, map_smul, hy (K R 𝕧 (-ktilde R i) • x),
      hy (E R 𝕧 i • K R 𝕧 (-ktilde R i) • x)]
  have hF (i : I) {y : M₂} (hy : y ∈ P) : F R 𝕧 i • y ∈ P := fun x ↦ by
    have e : TensorModule.mk M₁ M₂ (x ⊗ₜ[𝕂] (F R 𝕧 i • y)) =
        F R 𝕧 i • TensorModule.mk M₁ M₂ (x ⊗ₜ[𝕂] y) -
          TensorModule.mk M₁ M₂ ((F R 𝕧 i • x) ⊗ₜ[𝕂] (K R 𝕧 (-ktilde R i) • y)) := by
      rw [TensorModule.F_smul_tmul, map_add, add_sub_cancel_left]
    rw [e, map_sub, map_sub, map_smul, map_smul, hy x, hK _ hy (F R 𝕧 i • x)]
  have hU (u : QuantumGroup R 𝕧) : ∀ y ∈ P, u • y ∈ P := by
    induction u using QuantumGroup.induction_on with
    | algebraMap c => intro y hy; rw [algebraMap_smul]; exact hsmul c hy
    | E i => exact fun y hy ↦ hE i hy
    | F i => exact fun y hy ↦ hF i hy
    | K μ => exact fun y hy ↦ hK μ hy
    | add a b ha hb => intro y hy; rw [add_smul]; exact hadd (ha y hy) (hb y hy)
    | mul a b ha hb => intro y hy; rw [mul_smul]; exact ha _ (hb y hy)
  let PS : Submodule (QuantumGroup R 𝕧) M₂ :=
    { carrier := P, add_mem' := hadd, zero_mem' := hzero, smul_mem' := fun u y hy ↦ hU u y hy }
  have hall : ∀ y, y ∈ P := fun y ↦ by
    have : y ∈ PS := by
      rw [show PS = ⊤ from eq_top_iff.2 (hS ▸ Submodule.span_le.2 fun y hy x ↦ hfg x y hy)]
      trivial
    exact this
  ext z
  obtain ⟨z, rfl⟩ := (TensorModule.mk M₁ M₂).surjective z
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | tmul x y => exact hall y x

end Ext

end LieLean.QuantumGroup
