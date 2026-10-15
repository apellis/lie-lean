/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.QuasiR.TensorAction

/-!
# The involution `Ψ = Θ ∘ (¯ ⊗ ¯)`

Let `M₁`, `M₂` be `U`-modules over `ℚ(v)` with `M₂` as in [Lus] 3.4.7, and let `ψ₁`, `ψ₂` be
involutions of `M₁`, `M₂` compatible with the bar involution of `U`. Then
`Ψ = Θ ∘ (ψ₁ ⊗ ψ₂)` is an involution of `M₁ ⊗ M₂` (`quasiRAct_barPair_involutive`); in [Lus] 24.3.2
this is deduced from 24.1.2 and 4.1.3, as here: `(ψ₁ ⊗ ψ₂) Θ = Θ̄ (ψ₁ ⊗ ψ₂)` and `Θ Θ̄ = 1`
(`sum_quasiR_mul_barTensor`).

## Main definitions and results

* `QuantumGroup.plusPart`: the span of the `a ⊗ x⁺`, `x ∈ 'f_ν`; it contains `Θ_ν` and `Θ̄_ν`.
* `QuantumGroup.quasiRAct_barPair_involutive`: `Ψ² = 1` ([Lus] 24.3.2).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 4.1.3, 24.1, 24.3.2.
-/

open LieLean LusztigF TensorProduct Finset

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y)

/-! ### Elements of `U ⊗ U⁺_ν` -/

/-- The span of the `a ⊗ x⁺`, `a ∈ U`, `x ∈ 'f_ν`. -/
def plusPart (ν : I →₀ ℕ) : Submodule 𝕂 (QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧) :=
  Submodule.span 𝕂 {t | ∃ a, ∃ x ∈ LusztigF.weightSpace 𝕂 ν, t = a ⊗ₜ[𝕂] plusHom R 𝕧 x}

variable {R}

lemma tmul_mem_plusPart (a : QuantumGroup R 𝕧) {ν : I →₀ ℕ} {x : LusztigF 𝕂 I}
    (hx : x ∈ LusztigF.weightSpace 𝕂 ν) : a ⊗ₜ[𝕂] plusHom R 𝕧 x ∈ plusPart R ν :=
  Submodule.subset_span ⟨a, x, hx, rfl⟩

lemma barTensor_mem_plusPart {ν : I →₀ ℕ} {t : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧}
    (ht : t ∈ plusPart R ν) : barTensor R t ∈ plusPart R ν := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, x, hx, rfl⟩ := ht
    rw [barTensor_tmul, barHom_plusHom]
    exact tmul_mem_plusPart _ (LusztigF.bar_mem_weightSpace hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add s t _ _ hs ht => rw [map_add]; exact add_mem hs ht
  | smul c t _ ht => rw [barTensor_smul]; exact Submodule.smul_mem _ _ ht

lemma mul_mem_plusPart {ν μ : I →₀ ℕ} {s t : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧}
    (hs : s ∈ plusPart R ν) (ht : t ∈ plusPart R μ) : s * t ∈ plusPart R (ν + μ) := by
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, x, hx, rfl⟩ := hs
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨b, y, hy, rfl⟩ := ht
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]
      exact tmul_mem_plusPart _ (LusztigF.mul_mem_weightSpace hx hy)
    | zero => rw [mul_zero]; exact zero_mem _
    | add t t' _ _ ht ht' => rw [mul_add]; exact add_mem ht ht'
    | smul c t _ ht => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ht
  | zero => rw [zero_mul]; exact zero_mem _
  | add s s' _ _ hs hs' => rw [add_mul]; exact add_mem hs hs'
  | smul c s _ hs => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hs

lemma quasiR_mem_plusPart [Finite I] (ν : I →₀ ℕ) : quasiR R ν ∈ plusPart R ν := by
  obtain ⟨s, hs⟩ := quasiR_mem_range R ν
  rw [← hs]
  clear hs
  induction s using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul a b =>
    obtain ⟨x, hx, e⟩ := Submodule.mem_map.1 b.2
    rw [map_tmul, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.coe_subtype, ← e]
    exact tmul_mem_plusPart _ hx

/-! ### Vanishing on `M₁ ⊗ M₂` -/

section Module

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module 𝕂 M₁] [Module (QuantumGroup R 𝕧) M₁]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₁]
  [AddCommGroup M₂] [Module 𝕂 M₂] [Module (QuantumGroup R 𝕧) M₂]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂]

local notation "act₂" => TensorModule.actPair R 𝕧 M₁ M₂

lemma actPair_eq_zero_of_mem_plusPart {ν : I →₀ ℕ} {t : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧}
    (ht : t ∈ plusPart R ν) {y : M₂}
    (hy : ∀ x ∈ LusztigF.weightSpace 𝕂 ν, plusHom R 𝕧 x • y = 0) (x : M₁) :
    act₂ t (x ⊗ₜ y) = 0 := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, x', hx', rfl⟩ := ht
    rw [TensorModule.act_tmul, hy x' hx', tmul_zero]
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add s t _ _ hs ht => rw [map_add, LinearMap.add_apply, hs, ht, add_zero]
  | smul c t _ ht => rw [map_smul, LinearMap.smul_apply, ht, smul_zero]

variable [Finite I]

omit [Module 𝕂 M₂] [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂] in
lemma plusHom_smul_eq_zero (h : IsPlusLocallyNilpotent R M₂) (y : M₂) :
    ∃ N : ℕ, ∀ ν : I →₀ ℕ, N ≤ ν.degree →
      ∀ x ∈ LusztigF.weightSpace 𝕂 ν, plusHom R 𝕧 x • y = 0 := by
  obtain ⟨N, hN⟩ := h y
  exact ⟨N, fun ν hν x hx ↦ hN ν hν _ (Submodule.mem_map_of_mem hx)⟩

lemma support_actPair_finite (h : IsPlusLocallyNilpotent R M₂)
    {T : (I →₀ ℕ) → QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧} (hT : ∀ ν, T ν ∈ plusPart R ν)
    (z : M₁ ⊗[𝕂] M₂) : (Function.support fun ν ↦ act₂ (T ν) z).Finite := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb =>
    refine (ha.union hb).subset fun ν hν ↦ ?_
    simp only [Function.mem_support, map_add] at hν
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
    exact hν (by rw [hc.1, hc.2, add_zero])
  | tmul x y =>
    obtain ⟨N, hN⟩ := plusHom_smul_eq_zero h y
    refine (Finsupp.finite_of_degree_lt (σ := I) N).subset fun ν hν ↦ ?_
    by_contra hc
    exact hν (actPair_eq_zero_of_mem_plusPart (hT ν) (hN ν (not_lt.1 hc)) x)

/-- `Θ Θ̄ = 1` on `M₁ ⊗ M₂` ([Lus] 4.1.3). -/
theorem quasiRAct_finsum_barTensor (h : IsPlusLocallyNilpotent R M₂) (z : M₁ ⊗[𝕂] M₂) :
    quasiRAct h (∑ᶠ ν, act₂ (barTensor R (quasiR R ν)) z) = z := by
  have hT : ∀ ν, barTensor R (quasiR R ν) ∈ plusPart R ν :=
    fun ν ↦ barTensor_mem_plusPart (quasiR_mem_plusPart ν)
  induction z using TensorProduct.inductionOn with
  | add a b ha hb =>
    simp only [map_add]
    rw [finsum_add_distrib (support_actPair_finite h hT a) (support_actPair_finite h hT b),
      map_add, ha, hb]
  | tmul x y =>
    obtain ⟨N, hN⟩ := plusHom_smul_eq_zero h y
    set S := (Finsupp.finite_of_degree_lt (σ := I) (N + 1)).toFinset
    have hS (ν : I →₀ ℕ) : ν ∈ S ↔ ν.degree < N + 1 := by simp [S]
    -- the terms vanish once the total degree is at least `N`
    have hvan {ν' ν'' : I →₀ ℕ} (hd : N ≤ ν'.degree + ν''.degree) :
        act₂ (quasiR R ν' * barTensor R (quasiR R ν'')) (x ⊗ₜ y) = 0 :=
      actPair_eq_zero_of_mem_plusPart (mul_mem_plusPart (quasiR_mem_plusPart ν') (hT ν''))
        (hN _ (by rwa [_root_.map_add])) x
    set a : (I →₀ ℕ) × (I →₀ ℕ) → M₁ ⊗[𝕂] M₂ :=
      fun p ↦ act₂ (quasiR R p.1 * barTensor R (quasiR R p.2)) (x ⊗ₜ y)
    have h1 : ∑ᶠ ν, act₂ (barTensor R (quasiR R ν)) (x ⊗ₜ y) =
        ∑ ν'' ∈ S, act₂ (barTensor R (quasiR R ν'')) (x ⊗ₜ y) := by
      refine finsum_eq_sum_of_support_subset _ fun ν hν ↦ ?_
      rw [Finset.mem_coe, hS]
      by_contra hc
      exact hν (actPair_eq_zero_of_mem_plusPart (hT ν) (hN ν (by omega)) x)
    have h2 (ν'' : I →₀ ℕ) : quasiRAct h (act₂ (barTensor R (quasiR R ν'')) (x ⊗ₜ y)) =
        ∑ ν' ∈ S, a (ν', ν'') := by
      rw [quasiRAct_apply]
      refine (finsum_eq_sum_of_support_subset _ fun ν' hν' ↦ ?_).trans
        (Finset.sum_congr rfl fun ν' _ ↦ ?_)
      · rw [Finset.mem_coe, hS]
        by_contra hc
        refine hν' ?_
        beta_reduce
        rw [← Module.End.mul_apply, ← _root_.map_mul]
        exact hvan (by omega)
      · simp only [a, map_mul, Module.End.mul_apply]
    rw [h1, map_sum, Finset.sum_congr rfl fun ν'' _ ↦ h2 ν'', Finset.sum_comm,
      ← Finset.sum_product' (f := fun ν' ν'' ↦ a (ν', ν''))]
    -- regroup the sum by `ν = ν' + ν''`
    have h3 : ∑ p ∈ S ×ˢ S, a p = ∑ ν ∈ S, ∑ p ∈ antidiagonal ν, a p := by
      set T := (S ×ˢ S).filter fun p ↦ p.1 + p.2 ∈ S
      have e1 : ∑ p ∈ S ×ˢ S, a p = ∑ p ∈ T, a p := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) fun p hp hpT ↦ ?_).symm
        simp only [Finset.mem_filter, not_and, hS] at hpT
        exact hvan (by have := hpT hp; rw [_root_.map_add] at this; omega)
      rw [e1, Finset.sum_sigma']
      refine Finset.sum_nbij' (fun p ↦ ⟨p.1 + p.2, p⟩) (fun q ↦ q.2) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        simp only [T, Finset.mem_filter] at hp
        simp [Finset.mem_sigma, hp.2]
      · rintro ⟨ν, p⟩ hq
        simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at hq
        obtain ⟨hν, rfl⟩ := hq
        simp only [T, Finset.mem_filter, Finset.mem_product, hS] at hν ⊢
        rw [_root_.map_add] at hν
        exact ⟨⟨by omega, by omega⟩, by rw [_root_.map_add]; omega⟩
      · intro p _; rfl
      · rintro ⟨ν, p⟩ hq
        simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at hq
        obtain ⟨_, rfl⟩ := hq
        rfl
      · intro p _; rfl
    rw [h3, Finset.sum_eq_single_of_mem 0 ((hS 0).2 (by simp))]
    · simp only [a]
      rw [← LinearMap.sum_apply, ← _root_.map_sum, sum_quasiR_mul_barTensor]
      simp
    · intro ν _ hν
      simp only [a]
      rw [← LinearMap.sum_apply, ← _root_.map_sum, sum_quasiR_mul_barTensor]
      simp [hν]

section Bar

variable (ψ₁ : M₁ →+ M₁) (ψ₂ : M₂ →+ M₂)
  (hψ₁ : ∀ (u : QuantumGroup R 𝕧) (m : M₁), ψ₁ (u • m) = barHom R u • ψ₁ m)
  (hψ₂ : ∀ (u : QuantumGroup R 𝕧) (m : M₂), ψ₂ (u • m) = barHom R u • ψ₂ m)

omit [Finite I] in
lemma barPair_barPair (hψ₁' : ∀ m, ψ₁ (ψ₁ m) = m) (hψ₂' : ∀ m, ψ₂ (ψ₂ m) = m)
    (z : M₁ ⊗[𝕂] M₂) : barPair ψ₁ ψ₂ hψ₁ hψ₂ (barPair ψ₁ ψ₂ hψ₁ hψ₂ z) = z := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul x y => rw [barPair_tmul, barPair_tmul, hψ₁', hψ₂']

/-- `(ψ₁ ⊗ ψ₂) Θ = Θ̄ (ψ₁ ⊗ ψ₂)` on `M₁ ⊗ M₂` ([Lus] 24.1.2). -/
lemma barPair_quasiRAct (h : IsPlusLocallyNilpotent R M₂) (z : M₁ ⊗[𝕂] M₂) :
    barPair ψ₁ ψ₂ hψ₁ hψ₂ (quasiRAct h z) =
      ∑ᶠ ν, act₂ (barTensor R (quasiR R ν)) (barPair ψ₁ ψ₂ hψ₁ hψ₂ z) := by
  rw [quasiRAct_apply, map_finsum _ (support_quasiR_finite h z)]
  exact finsum_congr fun ν ↦ barPair_actPair ψ₁ ψ₂ hψ₁ hψ₂ _ z

/-- [Lus] 24.3.2: for involutions `ψ₁`, `ψ₂` compatible with the bar involution of `U`, the map
`Ψ = Θ ∘ (ψ₁ ⊗ ψ₂)` of `M₁ ⊗ M₂` satisfies `Ψ² = 1`. -/
theorem quasiRAct_barPair_involutive (h : IsPlusLocallyNilpotent R M₂)
    (hψ₁' : ∀ m, ψ₁ (ψ₁ m) = m) (hψ₂' : ∀ m, ψ₂ (ψ₂ m) = m) (z : M₁ ⊗[𝕂] M₂) :
    quasiRAct h (barPair ψ₁ ψ₂ hψ₁ hψ₂ (quasiRAct h (barPair ψ₁ ψ₂ hψ₁ hψ₂ z))) = z := by
  rw [barPair_quasiRAct, barPair_barPair ψ₁ ψ₂ hψ₁ hψ₂ hψ₁' hψ₂', quasiRAct_finsum_barTensor]

end Bar

end Module

end LieLean.QuantumGroup
