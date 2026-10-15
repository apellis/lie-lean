/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.QuasiR.Inverse
import LieLean.Algebra.QuantumGroup.TensorModule

/-!
# The quasi-R-matrix acting on tensor products

Let `M`, `M'` be `U`-modules over `ℚ(v)` such that `M'` has Lusztig's finiteness property of the
category `𝒞^{hi}` ([Lus] 3.4.7): every `m' ∈ M'` is killed by `x⁺` for all `x ∈ f_ν` with
`tr ν` large (`IsPlusLocallyNilpotent`). Then `Θ = Σ_ν Θ_ν` acts on `M ⊗ M'`, since for each
vector only finitely many terms are nonzero ([Lus] 24.1.1; `quasiRAct`).

## Main definitions and results

* `QuantumGroup.IsPlusLocallyNilpotent`: the property of [Lus] 3.4.7.
* `QuantumGroup.quasiRAct`: the operator `Θ` on `M ⊗ M'` ([Lus] 24.1.1).
* `QuantumGroup.barComul`: `Δ̄(u) = \overline{Δ(ū)}`, as a ring homomorphism `U → U ⊗ U`.
* `QuantumGroup.act_quasiRAct`: [Lus] Lemma 24.1.2 (a), `Δ(u) Θ = Θ Δ̄(u)` on `M ⊗ M'`.
* `QuantumGroup.act_quasiRAct_barPair`: [Lus] Lemma 24.1.2 (b) and 24.1.3: for semilinear maps
  `¯ : M → M`, `¯ : M' → M'` compatible with the bar involution of `U`, the composite
  `Ξ = Θ ∘ (¯ ⊗ ¯)` satisfies `u Ξ(z) = Ξ(ū z)`.

Lusztig allows instead that `ʷM` has the property of 3.4.7; only the case of `M'` is treated.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 3.4.7, 4.1.2, 24.1.
-/

open LieLean LusztigF TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y)

/-! ### The bar involution of `U ⊗ U` and `Δ̄` -/

theorem barTensor_smul (c : 𝕂) (t : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧) :
    barTensor R (c • t) = RatFunc.bar c • barTensor R t := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
  | tmul x y => rw [smul_tmul', barTensor_tmul, barTensor_tmul, barHom_smul, smul_tmul']

theorem barTensor_algebraMap (c : 𝕂) :
    barTensor R (algebraMap 𝕂 _ c) = algebraMap 𝕂 _ (RatFunc.bar c) := by
  rw [Algebra.algebraMap_eq_smul_one, barTensor_smul, barTensor_one,
    ← Algebra.algebraMap_eq_smul_one]

/-- `Δ̄(u) = \overline{Δ(ū)}` ([Lus] 4.1.1), a ring homomorphism `U → U ⊗ U`. -/
def barComul : QuantumGroup R 𝕧 →+* QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧 where
  toFun u := barTensor R (comul R 𝕧 (barHom R u))
  map_one' := by simp
  map_mul' a b := by simp [barTensor_mul]
  map_zero' := by simp
  map_add' a b := by simp

theorem barComul_apply (u : QuantumGroup R 𝕧) :
    barComul R u = barTensor R (comul R 𝕧 (barHom R u)) := rfl

theorem barComul_algebraMap (c : 𝕂) : barComul R (algebraMap 𝕂 _ c) = algebraMap 𝕂 _ c := by
  rw [barComul_apply, barHom_algebraMap, AlgHom.commutes, barTensor_algebraMap,
    RatFunc.bar_bar]

theorem barComul_E (i : I) :
    barComul R (E R 𝕧 i) = E R 𝕧 i ⊗ₜ 1 + K R 𝕧 (-ktilde R i) ⊗ₜ E R 𝕧 i := by
  simp [barComul_apply, Kt]

theorem barComul_F (i : I) :
    barComul R (F R 𝕧 i) = F R 𝕧 i ⊗ₜ K R 𝕧 (ktilde R i) + 1 ⊗ₜ F R 𝕧 i := by
  simp [barComul_apply]

theorem barComul_K (μ : Y) : barComul R (K R 𝕧 μ) = K R 𝕧 μ ⊗ₜ K R 𝕧 μ := by
  simp [barComul_apply]

theorem barTensor_barComul (u : QuantumGroup R 𝕧) :
    barTensor R (barComul R u) = comul R 𝕧 (barHom R u) := by
  rw [barComul_apply, barTensor_barTensor]

/-! ### The finiteness property of `𝒞^{hi}` -/

section Module

variable [Finite I]

variable (M : Type*) [AddCommGroup M] [Module 𝕂 M] [Module (QuantumGroup R 𝕧) M]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M]

/-- The finiteness property defining Lusztig's category `𝒞^{hi}` ([Lus] 3.4.7): every vector is
killed by `x⁺` for all `x ∈ f_ν` with `tr ν` large enough. -/
def IsPlusLocallyNilpotent : Prop :=
  ∀ m : M, ∃ N : ℕ, ∀ ν : I →₀ ℕ, N ≤ ν.degree → ∀ x ∈ quotientWeightSpace D ν,
    quotientPlus R x • m = 0

variable {R}
variable (M₁ M₂ : Type*) [AddCommGroup M₁] [Module 𝕂 M₁] [Module (QuantumGroup R 𝕧) M₁]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₁]
  [AddCommGroup M₂] [Module 𝕂 M₂] [Module (QuantumGroup R 𝕧) M₂]
  [IsScalarTower 𝕂 (QuantumGroup R 𝕧) M₂]

/-- The action of `U ⊗ U` on `M₁ ⊗ M₂`. -/
local notation "act₂" => TensorModule.actPair R 𝕧 M₁ M₂

variable {M₁ M₂}

lemma actPair_quasiR_tmul_eq_zero {ν : I →₀ ℕ} {y : M₂}
    (hy : ∀ x ∈ quotientWeightSpace D ν, quotientPlus R x • y = 0) (x : M₁) :
    act₂ (quasiR R ν) (x ⊗ₜ y) = 0 := by
  obtain ⟨s, hs⟩ := quasiR_mem_range R ν
  rw [← hs]
  clear hs
  induction s using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, ha, hb, add_zero]
  | tmul a b =>
    simp only [map_tmul, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      AlgHom.toLinearMap_apply, TensorModule.act_tmul, hy b.1 b.2, tmul_zero]

lemma support_quasiR_finite (h : IsPlusLocallyNilpotent R M₂) (z : M₁ ⊗[𝕂] M₂) :
    (Function.support fun ν ↦ act₂ (quasiR R ν) z).Finite := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb =>
    refine (ha.union hb).subset fun ν hν ↦ ?_
    simp only [Function.mem_support, map_add] at hν
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
    exact hν (by rw [hc.1, hc.2, add_zero])
  | tmul x y =>
    obtain ⟨N, hN⟩ := h y
    refine (Finsupp.finite_of_degree_lt (σ := I) N).subset fun ν hν ↦ ?_
    by_contra hc
    exact hν (actPair_quasiR_tmul_eq_zero (hN ν (not_lt.1 hc)) x)

/-- The operator `Θ = Σ_ν Θ_ν` on `M₁ ⊗ M₂` ([Lus] 24.1.1), for `M₂` with the property of
[Lus] 3.4.7: for each vector only finitely many terms of the sum are nonzero. -/
def quasiRAct (h : IsPlusLocallyNilpotent R M₂) : M₁ ⊗[𝕂] M₂ →ₗ[𝕂] M₁ ⊗[𝕂] M₂ where
  toFun z := ∑ᶠ ν, act₂ (quasiR R ν) z
  map_add' a b := by
    simp only [map_add]
    exact finsum_add_distrib (support_quasiR_finite h a) (support_quasiR_finite h b)
  map_smul' c z := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum c _).symm

theorem quasiRAct_apply (h : IsPlusLocallyNilpotent R M₂) (z : M₁ ⊗[𝕂] M₂) :
    quasiRAct h z = ∑ᶠ ν, act₂ (quasiR R ν) z := rfl

omit [DecidableEq I] [Finite I] in
/-- Splitting a finite sum over `ℕ^I` according to whether the `i`-th coordinate vanishes. -/
lemma finsum_eq_add_shift {T : Type*} [AddCommMonoid T] (i : I) {φ : (I →₀ ℕ) → T}
    (hφ : (Function.support φ).Finite) :
    ∑ᶠ ν, φ ν = ∑ᶠ ν, (if ν i = 0 then φ ν else 0) + ∑ᶠ μ, φ (μ + Finsupp.single i 1) := by
  classical
  set s := hφ.toFinset
  have hinj : Set.InjOn (· + Finsupp.single i 1) ((· + Finsupp.single i 1) ⁻¹' ↑s) :=
    fun a _ b _ hab ↦ add_right_cancel hab
  rw [finsum_eq_sum_of_support_subset φ (s := s) (by simp [s]),
    finsum_eq_sum_of_support_subset _ (s := s) (fun ν hν ↦ by
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hν
      simpa [s] using hν.2),
    finsum_eq_sum_of_support_subset _ (s := s.preimage _ hinj) (fun μ hμ ↦ by
      simpa [s] using hμ)]
  have hg : ∑ μ ∈ s.preimage _ hinj, φ (μ + Finsupp.single i 1) =
      ∑ ν ∈ s, if ν i = 0 then 0 else φ ν := by
    rw [← Finset.sum_preimage (· + Finsupp.single i 1) s hinj
      (fun ν ↦ if ν i = 0 then 0 else φ ν)]
    · refine Finset.sum_congr rfl fun μ _ ↦ ?_
      simp
    · intro ν _ hν
      split_ifs with hc
      · rfl
      refine absurd ⟨ν - Finsupp.single i 1, tsub_add_cancel_of_le fun j ↦ ?_⟩ hν
      rcases eq_or_ne j i with rfl | hj
      · simp only [Finsupp.single_eq_same]; omega
      · simp [Finsupp.single_eq_of_ne hj]
  rw [hg, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ ↦ ?_
  split_ifs <;> simp

/-- The identities of [Lus] 4.1.2 (a) for one generator give the intertwining property of
`Θ` on `M₁ ⊗ M₂`. -/
lemma actPair_quasiRAct_of (h : IsPlusLocallyNilpotent R M₂) (i : I)
    {a b a' b' : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧}
    (h₀ : ∀ ν : I →₀ ℕ, ν i = 0 → a * quasiR R ν = quasiR R ν * a')
    (h₁ : ∀ μ : I →₀ ℕ, a * quasiR R (μ + Finsupp.single i 1) + b * quasiR R μ =
      quasiR R (μ + Finsupp.single i 1) * a' + quasiR R μ * b')
    (z : M₁ ⊗[𝕂] M₂) :
    act₂ (a + b) (quasiRAct h z) = quasiRAct h (act₂ (a' + b') z) := by
  have hfin := support_quasiR_finite h z
  have hfin' := support_quasiR_finite h (act₂ a' z)
  have hfin'' := support_quasiR_finite h (act₂ b' z)
  have hA : (Function.support fun ν ↦ act₂ a (act₂ (quasiR R ν) z)).Finite :=
    hfin.subset (Function.support_comp_subset (map_zero _) _)
  have hB : (Function.support fun ν ↦ act₂ b (act₂ (quasiR R ν) z)).Finite :=
    hfin.subset (Function.support_comp_subset (map_zero _) _)
  have hshift {φ : (I →₀ ℕ) → M₁ ⊗[𝕂] M₂} (hφ : (Function.support φ).Finite) :
      (Function.support fun μ ↦ φ (μ + Finsupp.single i 1)).Finite :=
    hφ.preimage fun _ _ _ _ h ↦ add_right_cancel h
  simp only [map_add, LinearMap.add_apply, quasiRAct_apply]
  rw [map_finsum _ hfin, map_finsum _ hfin, finsum_eq_add_shift i hA,
    finsum_eq_add_shift i hfin', add_assoc, add_assoc, ← finsum_add_distrib (hshift hA) hB,
    ← finsum_add_distrib (hshift hfin') hfin'']
  congr 1
  · refine finsum_congr fun ν ↦ ?_
    split_ifs with hν
    · rw [← Module.End.mul_apply, ← map_mul, h₀ ν hν, map_mul, Module.End.mul_apply]
    · rfl
  · refine finsum_congr fun μ ↦ ?_
    simpa only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply] using
      congrArg (fun t ↦ act₂ t z) (h₁ μ)

/-- If `a` commutes with every `Θ_ν`, then `a` commutes with `Θ` on `M₁ ⊗ M₂`. -/
lemma actPair_quasiRAct_of_commute (h : IsPlusLocallyNilpotent R M₂)
    {a : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧}
    (ha : ∀ ν : I →₀ ℕ, a * quasiR R ν = quasiR R ν * a) (z : M₁ ⊗[𝕂] M₂) :
    act₂ a (quasiRAct h z) = quasiRAct h (act₂ a z) := by
  rw [quasiRAct_apply, quasiRAct_apply, map_finsum _ (support_quasiR_finite h z)]
  refine finsum_congr fun ν ↦ ?_
  rw [← Module.End.mul_apply, ← map_mul, ha ν, map_mul, Module.End.mul_apply]

/-- [Lus] Lemma 24.1.2 (a): `Δ(u) Θ(z) = Θ(Δ̄(u) z)` for `z ∈ M₁ ⊗ M₂`. -/
theorem act_quasiRAct (h : IsPlusLocallyNilpotent R M₂) (u : QuantumGroup R 𝕧)
    (z : M₁ ⊗[𝕂] M₂) :
    TensorModule.act R 𝕧 M₁ M₂ u (quasiRAct h z) = quasiRAct h (act₂ (barComul R u) z) := by
  induction u using QuantumGroup.induction_on generalizing z with
  | algebraMap c =>
    rw [AlgHom.commutes, barComul_algebraMap, AlgHom.commutes, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul]
  | E i =>
    rw [TensorModule.act, AlgHom.comp_apply, comul_E, barComul_E]
    exact actPair_quasiRAct_of h i (fun ν hν ↦ quasiR_E_of_eq_zero R i hν) (quasiR_E R i) z
  | F i =>
    rw [TensorModule.act, AlgHom.comp_apply, comul_F, barComul_F,
      add_comm (F R 𝕧 i ⊗ₜ[𝕂] K R 𝕧 (-ktilde R i)),
      add_comm (F R 𝕧 i ⊗ₜ[𝕂] K R 𝕧 (ktilde R i))]
    exact actPair_quasiRAct_of h i (fun ν hν ↦ quasiR_F_of_eq_zero R i hν) (quasiR_F R i) z
  | K μ =>
    rw [TensorModule.act, AlgHom.comp_apply, comul_K, barComul_K]
    exact actPair_quasiRAct_of_commute h (fun ν ↦ quasiR_K R μ ν) z
  | add x y hx hy =>
    rw [map_add, LinearMap.add_apply, hx, hy, map_add, map_add, LinearMap.add_apply, map_add]
  | mul x y hx hy =>
    rw [map_mul, Module.End.mul_apply, hy, hx, map_mul, map_mul, Module.End.mul_apply]

/-! ### Compatibility with bar involutions of the factors -/

section Bar

variable (ψ₁ : M₁ →+ M₁) (ψ₂ : M₂ →+ M₂)
  (hψ₁ : ∀ (u : QuantumGroup R 𝕧) (m : M₁), ψ₁ (u • m) = barHom R u • ψ₁ m)
  (hψ₂ : ∀ (u : QuantumGroup R 𝕧) (m : M₂), ψ₂ (u • m) = barHom R u • ψ₂ m)

omit [Finite I] in
include hψ₁ in
lemma map_smul_of_barHom (c : 𝕂) (m : M₁) : ψ₁ (c • m) = RatFunc.bar c • ψ₁ m := by
  rw [← algebraMap_smul (QuantumGroup R 𝕧), hψ₁, barHom_algebraMap, algebraMap_smul]

/-- The map `x ⊗ y ↦ ψ₁ x ⊗ ψ₂ y` on `M₁ ⊗ M₂` for maps `ψ₁`, `ψ₂` compatible with the bar
involution of `U` (`¯ ⊗ ¯` in [Lus] 24.1.2 (b)). -/
def barPair : M₁ ⊗[𝕂] M₂ →+ M₁ ⊗[𝕂] M₂ :=
  liftAddHom
    (AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (fun y ↦ ψ₁ x ⊗ₜ[𝕂] ψ₂ y)
      fun a b ↦ by simp [tmul_add]) fun a b ↦ by ext; simp [add_tmul])
    fun c x y ↦ by
      simp [map_smul_of_barHom ψ₁ hψ₁, map_smul_of_barHom ψ₂ hψ₂, smul_tmul]

omit [Finite I] in
@[simp] theorem barPair_tmul (x : M₁) (y : M₂) :
    barPair ψ₁ ψ₂ hψ₁ hψ₂ (x ⊗ₜ[𝕂] y) = ψ₁ x ⊗ₜ[𝕂] ψ₂ y := rfl

omit [Finite I] in
theorem barPair_actPair (t : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧) (z : M₁ ⊗[𝕂] M₂) :
    barPair ψ₁ ψ₂ hψ₁ hψ₂ (act₂ t z) = act₂ (barTensor R t) (barPair ψ₁ ψ₂ hψ₁ hψ₂ z) := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, LinearMap.add_apply, map_add, ha, hb, map_add, map_add,
      LinearMap.add_apply]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]
    | tmul x y => simp [TensorModule.act_tmul, hψ₁, hψ₂]

/-- [Lus] Lemma 24.1.2 (b), in the form of 24.1.3: for `ψ₁`, `ψ₂` compatible with the bar
involution of `U`, the map `Ξ = Θ ∘ (ψ₁ ⊗ ψ₂)` on `M₁ ⊗ M₂` satisfies `u Ξ(z) = Ξ(ū z)`. -/
theorem act_quasiRAct_barPair (h : IsPlusLocallyNilpotent R M₂) (u : QuantumGroup R 𝕧)
    (z : M₁ ⊗[𝕂] M₂) :
    TensorModule.act R 𝕧 M₁ M₂ u (quasiRAct h (barPair ψ₁ ψ₂ hψ₁ hψ₂ z)) =
      quasiRAct h (barPair ψ₁ ψ₂ hψ₁ hψ₂ (TensorModule.act R 𝕧 M₁ M₂ (barHom R u) z)) := by
  rw [act_quasiRAct, TensorModule.act, AlgHom.comp_apply, barPair_actPair, ← barComul_apply]

end Bar

end Module

end LieLean.QuantumGroup
