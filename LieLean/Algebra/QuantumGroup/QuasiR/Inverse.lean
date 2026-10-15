/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.QuasiR.Uniqueness
import LieLean.Algebra.QuantumGroup.BarInvolution
import LieLean.Algebra.QuantumGroup.LusztigF.BarQuotient

/-!
# The quasi-R-matrix is inverse to its conjugate

Let `Θ = Σ_ν Θ_ν` be Lusztig's quasi-R-matrix (`quasiR`) and `Θ̄ = Σ_ν Θ̄_ν` its image under the
bar involution `¯ ⊗ ¯` of `U ⊗ U`. Then `Θ Θ̄ = Θ̄ Θ = 1 ⊗ 1` ([Lus] 4.1.3). Since the completion
of `U ⊗ U` is not formalized, we state this component by component:
`Σ_{ν' + ν'' = ν} Θ_{ν'} Θ̄_{ν''}` is `1 ⊗ 1` for `ν = 0` and `0` otherwise.

## Main definitions and results

* `QuantumGroup.barTensor`: the bar involution `x ⊗ y ↦ x̄ ⊗ ȳ` of `U ⊗ U`.
* `QuantumGroup.sum_quasiR_mul_barTensor`: `Σ_{ν' + ν'' = ν} Θ_{ν'} Θ̄_{ν''} = δ_{ν,0}`.
* `QuantumGroup.sum_barTensor_mul_quasiR`: `Σ_{ν' + ν'' = ν} Θ̄_{ν'} Θ_{ν''} = δ_{ν,0}`.

## Proof

As in [Lus] 4.1.3, the components `Ω_ν` of `Θ Θ̄` commute with `Δ(Eᵢ)`, because `Θ` intertwines
`Δ` and `Δ̄` (`quasiR_E`) and `Θ̄` intertwines `Δ̄` and `Δ`. By induction on `ν`, `Ω_ν` then
commutes with `Eᵢ ⊗ 1` for `ν ≠ 0`, and an element of `U⁻_ν ⊗ U⁺_ν` with this property is zero
(`eq_zero_of_forall_E_commute`, from the proof of [Lus] 4.1.2). The identity for `Θ̄ Θ` is the
image of the one for `Θ Θ̄` under the bar involution.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 4.1.2, 4.1.3.
-/

open LieLean LusztigF TensorProduct Finset

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y)

/-! ### The bar involution of `U ⊗ U` -/

/-- The bar involution of `U ⊗ U`, `x ⊗ y ↦ x̄ ⊗ ȳ`. -/
def barTensor : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧 →+ QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧 :=
  liftAddHom
    (AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (fun y ↦ barHom R x ⊗ₜ[𝕂] barHom R y)
      fun a b ↦ by simp [tmul_add]) fun a b ↦ by ext; simp [add_tmul])
    fun c x y ↦ by simp [barHom_smul, smul_tmul]

@[simp] theorem barTensor_tmul (x y : QuantumGroup R 𝕧) :
    barTensor R (x ⊗ₜ[𝕂] y) = barHom R x ⊗ₜ[𝕂] barHom R y := rfl

@[simp] theorem barTensor_one : barTensor R 1 = 1 := by
  simp [Algebra.TensorProduct.one_def]

theorem barTensor_mul (s t : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧) :
    barTensor R (s * t) = barTensor R s * barTensor R t := by
  induction s using TensorProduct.inductionOn with
  | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, add_mul]
  | tmul x y =>
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => rw [mul_add, map_add, ha, hb, map_add, mul_add]
    | tmul x' y' => simp

@[simp] theorem barTensor_barTensor (t : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧) :
    barTensor R (barTensor R t) = t := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul x y => simp

/-! ### Weight spaces -/

variable [Finite I]

lemma quotientBar_mem {ν : I →₀ ℕ} {x : Quotient D 𝕧} (hx : x ∈ quotientWeightSpace D ν) :
    quotientBar D x ∈ quotientWeightSpace D ν := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨LusztigF.bar a, LusztigF.bar_mem_weightSpace ha, rfl⟩

omit [Finite I] in
lemma mul_mem_quotientWeightSpace {ν μ : I →₀ ℕ} {x y : Quotient D 𝕧}
    (hx : x ∈ quotientWeightSpace D ν) (hy : y ∈ quotientWeightSpace D μ) :
    x * y ∈ quotientWeightSpace D (ν + μ) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a * b, LusztigF.mul_mem_weightSpace ha hb, by simp⟩

theorem barHom_quotientMinus (x : Quotient D 𝕧) :
    barHom R (quotientMinus R x) = quotientMinus R (quotientBar D x) := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  rw [quotientMinus_toQuotient, barHom_minusHom, quotientBar_toQuotient,
    quotientMinus_toQuotient]

theorem barHom_quotientPlus (x : Quotient D 𝕧) :
    barHom R (quotientPlus R x) = quotientPlus R (quotientBar D x) := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  rw [quotientPlus_toQuotient, barHom_plusHom, quotientBar_toQuotient,
    quotientPlus_toQuotient]

/-- `U⁻_ν ⊗ U⁺_ν`, as the range of `f_ν ⊗ f_ν`. -/
abbrev weightTensor (ν : I →₀ ℕ) : Submodule 𝕂 (QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧) :=
  LinearMap.range (map ((quotientMinus R).toLinearMap ∘ₗ (quotientWeightSpace D ν).subtype)
    ((quotientPlus R).toLinearMap ∘ₗ (quotientWeightSpace D ν).subtype))

theorem barTensor_mem_weightTensor {ν : I →₀ ℕ} {t : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧}
    (ht : t ∈ weightTensor R ν) : barTensor R t ∈ weightTensor R ν := by
  obtain ⟨s, rfl⟩ := ht
  induction s using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
  | tmul x y =>
    refine ⟨⟨quotientBar D x, quotientBar_mem x.2⟩ ⊗ₜ ⟨quotientBar D y, quotientBar_mem y.2⟩, ?_⟩
    simp [barHom_quotientMinus, barHom_quotientPlus]

theorem mul_mem_weightTensor {ν μ : I →₀ ℕ} {s t : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧}
    (hs : s ∈ weightTensor R ν) (ht : t ∈ weightTensor R μ) : s * t ∈ weightTensor R (ν + μ) := by
  obtain ⟨s, rfl⟩ := hs
  obtain ⟨t, rfl⟩ := ht
  induction s using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, add_mul]; exact add_mem ha hb
  | tmul x y =>
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, mul_add]; exact add_mem ha hb
    | tmul x' y' =>
      refine ⟨⟨x * x', mul_mem_quotientWeightSpace x.2 x'.2⟩ ⊗ₜ
        ⟨y * y', mul_mem_quotientWeightSpace y.2 y'.2⟩, ?_⟩
      simp

/-! ### The components of `Θ Θ̄` -/

/-- The component `Ω_ν = Σ_{ν' + ν'' = ν} Θ_{ν'} Θ̄_{ν''}` of `Θ Θ̄`. -/
def quasiRBarProd (ν : I →₀ ℕ) : QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧 :=
  ∑ p ∈ antidiagonal ν, quasiR R p.1 * barTensor R (quasiR R p.2)

theorem quasiRBarProd_mem (ν : I →₀ ℕ) : quasiRBarProd R ν ∈ weightTensor R ν := by
  refine Submodule.sum_mem _ fun p hp ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp]
  exact mul_mem_weightTensor R (quasiR_mem_range R p.1)
    (barTensor_mem_weightTensor R (quasiR_mem_range R p.2))

theorem quasiRBarProd_zero : quasiRBarProd R 0 = 1 := by
  simp [quasiRBarProd]

omit [Finite I] in
/-- Reindexing a sum over `ν' + ν'' = ν` along `ν' ↦ ν' - i`. -/
lemma sum_antidiagonal_sub_single {T : Type*} [AddCommMonoid T] (i : I) (ν : I →₀ ℕ)
    (f : (I →₀ ℕ) → (I →₀ ℕ) → T) :
    ∑ p ∈ antidiagonal ν, (if p.1 i = 0 then 0 else f (p.1 - Finsupp.single i 1) p.2) =
      if ν i = 0 then 0 else
        ∑ p ∈ antidiagonal (ν - Finsupp.single i 1), f p.1 p.2 := by
  split_ifs with hν
  · refine Finset.sum_eq_zero fun p hp ↦ ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    have : p.1 i = 0 := by
      have := congrArg (· i) hp
      simp only [Finsupp.add_apply] at this
      omega
    simp [this]
  · have e : ∀ p : (I →₀ ℕ) × (I →₀ ℕ),
        (if p.1 i = 0 then 0 else f (p.1 - Finsupp.single i 1) p.2) =
          if p.1 i ≠ 0 then f (p.1 - Finsupp.single i 1) p.2 else 0 := fun p ↦ by
      split_ifs <;> simp_all
    simp_rw [e]
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (fun p ↦ (p.1 - Finsupp.single i 1, p.2))
      (fun q ↦ (q.1 + Finsupp.single i 1, q.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, HasAntidiagonal.mem_antidiagonal] at hp ⊢
      obtain ⟨hp, hpi⟩ := hp
      ext j
      have := congrArg (· j) hp
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply] at this ⊢
      split_ifs at * with h <;> (try subst h) <;> omega
    · intro q hq
      simp only [Finset.mem_filter, HasAntidiagonal.mem_antidiagonal] at hq ⊢
      refine ⟨?_, by simp⟩
      ext j
      have := congrArg (· j) hq
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply] at this ⊢
      split_ifs at * with h <;> (try subst h) <;> omega
    · intro p hp
      simp only [Finset.mem_filter] at hp
      refine Prod.ext ?_ rfl
      ext j
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs at * with h <;> (try subst h) <;> omega
    · intro q _
      simp
    · intro p _
      rfl

omit [Finite I] in
lemma sum_antidiagonal_sub_single' {T : Type*} [AddCommMonoid T] (i : I) (ν : I →₀ ℕ)
    (f : (I →₀ ℕ) → (I →₀ ℕ) → T) :
    ∑ p ∈ antidiagonal ν, (if p.2 i = 0 then 0 else f p.1 (p.2 - Finsupp.single i 1)) =
      if ν i = 0 then 0 else
        ∑ p ∈ antidiagonal (ν - Finsupp.single i 1), f p.1 p.2 := by
  rw [Finsupp.sum_antidiagonal_swap ν
    (fun a b ↦ if b i = 0 then 0 else f a (b - Finsupp.single i 1)),
    sum_antidiagonal_sub_single i ν (fun a b ↦ f b a)]
  split_ifs
  · rfl
  · rw [Finsupp.sum_antidiagonal_swap]

variable (i : I)

/-- `(Eᵢ ⊗ 1) Θ_a - Θ_a (Eᵢ ⊗ 1)`, from [Lus] 4.1.2 (a). -/
lemma quasiR_E_sub (a : I →₀ ℕ) :
    (E R 𝕧 i ⊗ₜ[𝕂] 1) * quasiR R a - quasiR R a * (E R 𝕧 i ⊗ₜ[𝕂] 1) =
      if a i = 0 then 0 else
        quasiR R (a - Finsupp.single i 1) * (K R 𝕧 (-ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i) -
          (K R 𝕧 (ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i) * quasiR R (a - Finsupp.single i 1) := by
  split_ifs with ha
  · rw [quasiR_E_of_eq_zero R i ha, sub_self]
  · have h := quasiR_E R i (a - Finsupp.single i 1)
    rw [tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by omega))] at h
    rw [sub_eq_sub_iff_add_eq_add, h, add_comm]

/-- `(Eᵢ ⊗ 1) Θ̄_b - Θ̄_b (Eᵢ ⊗ 1)`, the bar of [Lus] 4.1.2 (a). -/
lemma barTensor_quasiR_E_sub (b : I →₀ ℕ) :
    (E R 𝕧 i ⊗ₜ[𝕂] 1) * barTensor R (quasiR R b) - barTensor R (quasiR R b) * (E R 𝕧 i ⊗ₜ[𝕂] 1) =
      if b i = 0 then 0 else
        barTensor R (quasiR R (b - Finsupp.single i 1)) * (K R 𝕧 (ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i) -
          (K R 𝕧 (-ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i) *
            barTensor R (quasiR R (b - Finsupp.single i 1)) := by
  have h := congrArg (barTensor R) (quasiR_E_sub R i b)
  rw [map_sub, barTensor_mul, barTensor_mul, barTensor_tmul, barHom_E, map_one] at h
  rw [h]
  split_ifs
  · simp
  · rw [map_sub, barTensor_mul, barTensor_mul, barTensor_tmul, barTensor_tmul, barHom_K,
      barHom_K, barHom_E, neg_neg]

/-- `Ω_ν` commutes with `Δ(Eᵢ)`: the commutator with `Eᵢ ⊗ 1` is given by `Ω_{ν-i}`. -/
theorem quasiRBarProd_E_sub (ν : I →₀ ℕ) :
    (E R 𝕧 i ⊗ₜ[𝕂] 1) * quasiRBarProd R ν - quasiRBarProd R ν * (E R 𝕧 i ⊗ₜ[𝕂] 1) =
      if ν i = 0 then 0 else
        quasiRBarProd R (ν - Finsupp.single i 1) * (K R 𝕧 (ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i) -
          (K R 𝕧 (ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i) * quasiRBarProd R (ν - Finsupp.single i 1) := by
  set e := E R 𝕧 i ⊗ₜ[𝕂] (1 : QuantumGroup R 𝕧)
  set kp := K R 𝕧 (ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i
  set km := K R 𝕧 (-ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i
  have key : ∀ a b : I →₀ ℕ, e * (quasiR R a * barTensor R (quasiR R b)) -
      quasiR R a * barTensor R (quasiR R b) * e =
      (if a i = 0 then 0 else
        quasiR R (a - Finsupp.single i 1) * km * barTensor R (quasiR R b) -
          kp * quasiR R (a - Finsupp.single i 1) * barTensor R (quasiR R b)) +
      (if b i = 0 then 0 else
        quasiR R a * barTensor R (quasiR R (b - Finsupp.single i 1)) * kp -
          quasiR R a * km * barTensor R (quasiR R (b - Finsupp.single i 1))) := by
    intro a b
    have h1 := quasiR_E_sub R i a
    have h2 := barTensor_quasiR_E_sub R i b
    have : e * (quasiR R a * barTensor R (quasiR R b)) -
        quasiR R a * barTensor R (quasiR R b) * e =
        (e * quasiR R a - quasiR R a * e) * barTensor R (quasiR R b) +
          quasiR R a * (e * barTensor R (quasiR R b) - barTensor R (quasiR R b) * e) := by
      noncomm_ring
    rw [this, h1, h2]
    congr 1
    · split_ifs
      · simp
      · rw [sub_mul, mul_assoc]
    · split_ifs
      · simp
      · rw [mul_sub, mul_assoc, mul_assoc]
  rw [quasiRBarProd, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp_rw [key, Finset.sum_add_distrib]
  rw [sum_antidiagonal_sub_single i ν
      (fun a b ↦ quasiR R a * km * barTensor R (quasiR R b) -
        kp * quasiR R a * barTensor R (quasiR R b)),
    sum_antidiagonal_sub_single' i ν
      (fun a b ↦ quasiR R a * barTensor R (quasiR R b) * kp -
        quasiR R a * km * barTensor R (quasiR R b))]
  split_ifs
  · simp
  · rw [← Finset.sum_add_distrib, quasiRBarProd, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp only [mul_assoc]
    abel

/-- [Lus] 4.1.3, componentwise: `Σ_{ν' + ν'' = ν} Θ_{ν'} Θ̄_{ν''}` is `1 ⊗ 1` for `ν = 0` and
`0` otherwise, i.e. `Θ Θ̄ = 1 ⊗ 1`. -/
theorem sum_quasiR_mul_barTensor (ν : I →₀ ℕ) :
    ∑ p ∈ antidiagonal ν, quasiR R p.1 * barTensor R (quasiR R p.2) =
      if ν = 0 then 1 else 0 := by
  change quasiRBarProd R ν = _
  induction h : ν.degree using Nat.strong_induction_on generalizing ν with
  | _ n ih =>
  split_ifs with hν
  · rw [hν, quasiRBarProd_zero]
  obtain ⟨t, ht⟩ := quasiRBarProd_mem R ν
  rw [← ht]
  suffices t = 0 by rw [this, map_zero]
  refine eq_zero_of_forall_E_commute R hν t fun i ↦ ?_
  rw [ht, ← sub_eq_zero, quasiRBarProd_E_sub]
  split_ifs with hνi
  · rfl
  · have hlt : (ν - Finsupp.single i 1).degree < n := by
      rw [← h]
      have hle : Finsupp.single i 1 ≤ ν := Finsupp.single_le_iff.2 (by omega)
      conv_rhs => rw [← tsub_add_cancel_of_le hle]
      rw [map_add, Finsupp.degree_single]
      omega
    rw [ih _ hlt _ rfl]
    split_ifs <;> simp

/-- [Lus] 4.1.3, componentwise: `Σ_{ν' + ν'' = ν} Θ̄_{ν'} Θ_{ν''}` is `1 ⊗ 1` for `ν = 0` and
`0` otherwise, i.e. `Θ̄ Θ = 1 ⊗ 1`. -/
theorem sum_barTensor_mul_quasiR (ν : I →₀ ℕ) :
    ∑ p ∈ antidiagonal ν, barTensor R (quasiR R p.1) * quasiR R p.2 =
      if ν = 0 then 1 else 0 := by
  have h := congrArg (barTensor R) (sum_quasiR_mul_barTensor R ν)
  simp only [map_sum, barTensor_mul, barTensor_barTensor] at h
  rw [h]
  split_ifs <;> simp

end LieLean.QuantumGroup
