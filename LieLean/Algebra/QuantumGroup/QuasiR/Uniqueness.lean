/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.QuasiR.Theorem

/-!
# Uniqueness of the quasi-R-matrix

The components `Θ_ν ∈ U⁻_ν ⊗ U⁺_ν` of Lusztig's quasi-R-matrix are determined by `Θ_0 = 1 ⊗ 1`
and the identities `Δ(Eᵢ) Θ = Θ Δ̄(Eᵢ)`, read component by component ([Lus] 4.1.2 (a),
uniqueness). The argument follows [Lus] 4.1.2: if `z ∈ U⁻_ν ⊗ U⁺_ν`, `ν ≠ 0`, commutes with
every `Eᵢ ⊗ 1`, then [Lus] 3.1.6 and the independence of the `K_μ` force `rᵢ` to vanish on the
first tensor factor of `z` for all `i`, and then [Lus] 1.2.15 gives `z = 0`.

## Main results

* `mem_serreIdeal_of_minusHom_mul_K_add`: `y⁻ K_μ + y'⁻ K_ν = 0` with `μ ≠ ν` forces `y⁻ = 0`
  (triangular decomposition, any field, `v` not a root of unity).
* `eq_zero_of_forall_E_commute`: an element of `U⁻_ν ⊗ U⁺_ν`, `ν ≠ 0`, commuting with all
  `Eᵢ ⊗ 1` is zero.
* `quasiR_unique`: [Lus] 4.1.2 (a), uniqueness: a family `Θ'_ν ∈ U⁻_ν ⊗ U⁺_ν` with
  `Θ'_0 = 1 ⊗ 1` satisfying the `Eᵢ`-identities of `quasiR_E`, `quasiR_E_of_eq_zero` is
  `quasiR`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.2.15, 3.1.6, 4.1.2.
-/

open LieLean TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

open LusztigF

/-! ### Independence of `U⁻ K_μ` for distinct `μ` -/

section Independence

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k) [NeZero v] (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

include hv' in
/-- If `y⁻ K_μ + y'⁻ K_ν = 0` with `μ ≠ ν`, then `y` lies in the Serre ideal, i.e. `y⁻ = 0`
(triangular decomposition). Requires `v` not a root of unity. -/
theorem mem_serreIdeal_of_minusHom_mul_K_add {μ ν : Y} (h : μ ≠ ν) {y y' : LusztigF k I}
    (hy : minusHom R v y * K R v μ + minusHom R v y' * K R v ν = 0) : y ∈ serreIdeal D v := by
  have hz : y ⊗ₜ (AddMonoidAlgebra.single μ (1 : k) ⊗ₜ (1 : LusztigF k I)) +
      y' ⊗ₜ (AddMonoidAlgebra.single ν (1 : k) ⊗ₜ (1 : LusztigF k I)) ∈
        serreTriSubmodule Y D v :=
    mem_serreTriSubmodule_of_triMap_eq_zero R v hv' (by simpa using hy)
  let π : TriSpace k I Y →ₗ[k] LusztigF k I ⧸ serreSubmodule D v :=
    (TensorProduct.rid k _).toLinearMap ∘ₗ TensorProduct.map (serreSubmodule D v).mkQ
      ((TensorProduct.lid k k).toLinearMap ∘ₗ
        TensorProduct.map (Finsupp.lapply μ ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap)
          (LusztigF.counit (k := k) (I := I)).toLinearMap)
  have hπ : ∀ y' (g : AddMonoidAlgebra k Y) x, π (y' ⊗ₜ (g ⊗ₜ x)) =
      (g.coeff μ • LusztigF.counit x) • Submodule.Quotient.mk (p := serreSubmodule D v) y' :=
    fun _ _ _ ↦ rfl
  have hW : serreTriSubmodule Y D v ≤ LinearMap.ker π := by
    rw [serreTriSubmodule, Submodule.span_le]
    rintro _ ⟨y', g, x, rfl, h | h⟩
    · have : Submodule.Quotient.mk (p := serreSubmodule D v) y' = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (mem_serreSubmodule.2 h)
      simp [hπ, this]
    · simp [hπ, counit_eq_zero_of_mem_serreIdeal h]
  have := hW hz
  rw [LinearMap.mem_ker, map_add, hπ, hπ] at this
  simp only [map_one, smul_eq_mul, mul_one] at this
  classical
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_true, h.symm, ite_false,
    zero_smul, add_zero, one_smul, Submodule.Quotient.mk_eq_zero] at this
  exact mem_serreSubmodule.1 this

end Independence

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}

/-! ### [Lus] 1.2.15 on `f` -/

/-- [Lus] 1.2.15 on `f`: an element of `f_ν`, `ν ≠ 0`, killed by all `rᵢ` is zero. -/
theorem eq_zero_of_forall_quotientRDeriv_eq_zero {ν : I →₀ ℕ} (hν : ν ≠ 0)
    {y : Quotient D 𝕧} (hy : y ∈ quotientWeightSpace D ν)
    (h : ∀ i, quotientRDeriv D i y = 0) : y = 0 := by
  obtain ⟨a, rfl⟩ := toQuotient_surjective D 𝕧 y
  rw [toQuotient_eq_zero_iff]
  refine mem_radical_of_rDeriv_mem D 𝕧 ?_ fun i ↦ ?_
  · have := quotientForm_eq_zero_of_ne D hν hy (one_mem_quotientWeightSpace_zero)
    rwa [← map_one (toQuotient D 𝕧), quotientForm_toQuotient, form_one_right] at this
  · rw [← toQuotient_eq_zero_iff, ← quotientRDeriv_toQuotient]
    exact h i

variable (R : D.RootDatum Y)

/-- `y⁻ K_μ + y'⁻ K_ν = 0` with `μ ≠ ν` forces `y = 0` in `f`. -/
theorem quotientMinus_mul_K_add_eq_zero {μ ν : Y} (h : μ ≠ ν) {a b : Quotient D 𝕧}
    (hab : quotientMinus R a * K R 𝕧 μ + quotientMinus R b * K R 𝕧 ν = 0) : a = 0 := by
  obtain ⟨a, rfl⟩ := toQuotient_surjective D 𝕧 a
  obtain ⟨b, rfl⟩ := toQuotient_surjective D 𝕧 b
  rw [toQuotient_eq_zero_iff, radical_eq_serreIdeal_ratFunc]
  exact mem_serreIdeal_of_minusHom_mul_K_add R 𝕧 ratFunc_X_not_root h hab

omit [Finite I] [DecidableEq I] in
lemma ktilde_ne_neg (i : I) : ktilde R i ≠ -ktilde R i := by
  intro h
  have h' := congrArg (R.root i) h
  rw [map_neg, root_ktilde_eq_dot] at h'
  have := D.dot_self_pos i
  omega

omit [Finite I] [DecidableEq I] in
lemma sub_inv_ratFunc_ne_zero (i : I) : 𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹ ≠ 0 := by
  intro h
  have h0 : (𝕧 ^ D.d i : 𝕂) ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  have h1 : (𝕧 ^ D.d i) * 𝕧 ^ D.d i = 1 := by
    rw [sub_eq_zero] at h
    nth_rewrite 2 [h]
    exact mul_inv_cancel₀ h0
  refine ratFunc_X_not_root (D.d i * 2) (by have := D.d_pos i; omega) ?_
  rw [pow_mul, sq, h1]

/-- The map `f × f → U`, `(a, b) ↦ a⁻ K_μ + b⁻ K_ν`; injective for `μ ≠ ν`. -/
private def pairMap (μ ν : Y) : Quotient D 𝕧 × Quotient D 𝕧 →ₗ[𝕂] QuantumGroup R 𝕧 :=
  LinearMap.mulRight 𝕂 (K R 𝕧 μ) ∘ₗ (quotientMinus R).toLinearMap ∘ₗ LinearMap.fst 𝕂 _ _ +
    LinearMap.mulRight 𝕂 (K R 𝕧 ν) ∘ₗ (quotientMinus R).toLinearMap ∘ₗ LinearMap.snd 𝕂 _ _

private lemma pairMap_injective {μ ν : Y} (h : μ ≠ ν) : Function.Injective (pairMap R μ ν) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, b⟩ hab
  simp only [pairMap, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, AlgHom.toLinearMap_apply, LinearMap.mulRight_apply] at hab
  have ha := quotientMinus_mul_K_add_eq_zero R h hab
  have hb := quotientMinus_mul_K_add_eq_zero R h.symm (by rw [add_comm]; exact hab)
  simp [ha, hb]

/-! ### Elements of `U⁻_ν ⊗ U⁺_ν` commuting with the `Eᵢ ⊗ 1` -/

/-- If `map (y ↦ y⁻) g t` commutes with `Eᵢ ⊗ 1`, `g` injective, then `rᵢ` vanishes on the
first factor of `t` ([Lus] 3.1.6 and the independence of `K_{±i}`). -/
theorem rTensor_quotientRDeriv_eq_zero_of_commute {ν : I →₀ ℕ} (i : I) {W : Type*}
    [AddCommGroup W] [Module 𝕂 W] (g : W →ₗ[𝕂] QuantumGroup R 𝕧) (hg : Function.Injective g)
    (t : quotientWeightSpace D ν ⊗[𝕂] W)
    (h : (E R 𝕧 i ⊗ₜ[𝕂] 1) *
        map ((quotientMinus R).toLinearMap ∘ₗ (quotientWeightSpace D ν).subtype) g t =
      map ((quotientMinus R).toLinearMap ∘ₗ (quotientWeightSpace D ν).subtype) g t *
        (E R 𝕧 i ⊗ₜ[𝕂] 1)) :
    (quotientRDeriv D i ∘ₗ (quotientWeightSpace D ν).subtype).rTensor W t = 0 := by
  by_cases hνi : ν i = 0
  · have : quotientRDeriv D i ∘ₗ (quotientWeightSpace D ν).subtype = 0 :=
      LinearMap.ext fun y ↦ quotientRDeriv_eq_zero i hνi y.2
    rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply]
  obtain ⟨μ, rfl⟩ : ∃ μ, ν = μ + Finsupp.single i 1 :=
    ⟨ν - Finsupp.single i 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.2
      (Nat.one_le_iff_ne_zero.2 hνi))).symm⟩
  set S := (quotientWeightSpace D (μ + Finsupp.single i 1)).subtype
  set γ : 𝕂 := (𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹)⁻¹
  set c : 𝕂 := 𝕧 ^ R.rootSum μ (-ktilde R i)
  set P := LinearMap.prod (c • (quotientLDeriv D i ∘ₗ S)) (-(quotientRDeriv D i ∘ₗ S))
  have key : LinearMap.mulLeft 𝕂 (E R 𝕧 i) ∘ₗ (quotientMinus R).toLinearMap ∘ₗ S -
      LinearMap.mulRight 𝕂 (E R 𝕧 i) ∘ₗ (quotientMinus R).toLinearMap ∘ₗ S =
        γ • (pairMap R (ktilde R i) (-ktilde R i) ∘ₗ P) := by
    ext y
    have hK := K_mul_quotientMinus_of_mem R (ktilde R i) (quotientLDeriv_mem i y.2)
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply, pairMap, P,
      LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.prod_apply,
      Function.prod, E_mul_quotientMinus_sub]
    simp only [S, Submodule.subtype_apply, LinearMap.neg_apply,
      LinearMap.comp_apply, map_smul, map_neg, hK, c, γ, smul_mul_assoc, neg_mul,
      sub_eq_add_neg]
  rw [tmul_mul_map, map_mul_tmul, LinearMap.mulLeft_one, LinearMap.mulRight_one,
    LinearMap.id_comp, ← sub_eq_zero, ← LinearMap.sub_apply, ← map_sub_left', key,
    map_smul_left, LinearMap.smul_apply,
    smul_eq_zero, or_iff_right (inv_ne_zero (sub_inv_ratFunc_ne_zero i)),
    ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, LinearMap.rTensor_comp,
    LinearMap.comp_apply] at h
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap g hg
    (h.trans (map_zero _).symm)
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap _
    (pairMap_injective R (ktilde_ne_neg R i)) (h1.trans (map_zero _).symm)
  have h3 := congrArg ((LinearMap.snd 𝕂 (Quotient D 𝕧) (Quotient D 𝕧)).rTensor W) h2
  rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp] at h3
  simpa only [P, LinearMap.snd_prod, LinearMap.rTensor_neg, LinearMap.neg_apply,
    neg_eq_zero] using h3

/-- An element of `U⁻_ν ⊗ U⁺_ν`, `ν ≠ 0`, commuting with every `Eᵢ ⊗ 1` is zero
(proof of [Lus] 4.1.2 (a), uniqueness). -/
theorem eq_zero_of_forall_E_commute {ν : I →₀ ℕ} (hν : ν ≠ 0)
    (t : quotientWeightSpace D ν ⊗[𝕂] quotientWeightSpace D ν)
    (hE : ∀ i, (E R 𝕧 i ⊗ₜ[𝕂] 1) *
        map ((quotientMinus R).toLinearMap ∘ₗ (quotientWeightSpace D ν).subtype)
          ((quotientPlus R).toLinearMap ∘ₗ (quotientWeightSpace D ν).subtype) t =
      map ((quotientMinus R).toLinearMap ∘ₗ (quotientWeightSpace D ν).subtype)
          ((quotientPlus R).toLinearMap ∘ₗ (quotientWeightSpace D ν).subtype) t *
        (E R 𝕧 i ⊗ₜ[𝕂] 1)) : t = 0 := by
  have := Fintype.ofFinite I
  have hg : Function.Injective
      ((quotientPlus R).toLinearMap ∘ₗ (quotientWeightSpace D ν).subtype) :=
    (quotientPlus_injective R).comp (Submodule.injective_subtype _)
  have hr : ∀ i, (quotientRDeriv D i ∘ₗ (quotientWeightSpace D ν).subtype).rTensor
      (quotientWeightSpace D ν) t = 0 := fun i ↦
    rTensor_quotientRDeriv_eq_zero_of_commute R i _ hg t (hE i)
  let L : quotientWeightSpace D ν →ₗ[𝕂] (I → Quotient D 𝕧) :=
    LinearMap.pi fun i ↦ quotientRDeriv D i ∘ₗ (quotientWeightSpace D ν).subtype
  have hL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact Subtype.ext (eq_zero_of_forall_quotientRDeriv_eq_zero hν y.2
      fun i ↦ congrFun hy i)
  have hLsum : L = ∑ i, LinearMap.single 𝕂 (fun _ ↦ Quotient D 𝕧) i ∘ₗ
      (quotientRDeriv D i ∘ₗ (quotientWeightSpace D ν).subtype) := by
    ext y j
    simp [L, Pi.single_apply]
  refine Module.Flat.rTensor_preserves_injective_linearMap L hL ?_
  have hsum := map_sum (LinearMap.rTensorHom (M := quotientWeightSpace D ν))
    (fun i ↦ LinearMap.single 𝕂 (fun _ ↦ Quotient D 𝕧) i ∘ₗ
      (quotientRDeriv D i ∘ₗ (quotientWeightSpace D ν).subtype)) Finset.univ
  rw [map_zero, hLsum]
  refine (congrFun (congrArg DFunLike.coe hsum) t).trans ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  change LinearMap.rTensor _ (_ ∘ₗ _) t = 0
  rw [LinearMap.rTensor_comp, LinearMap.comp_apply, hr i, map_zero]

/-! ### Uniqueness -/

/-- [Lus] 4.1.2 (a), uniqueness: a family `Θ'_ν ∈ U⁻_ν ⊗ U⁺_ν` with `Θ'_0 = 1 ⊗ 1` and
`(Eᵢ ⊗ 1) Θ'_ν + (K̃ᵢ ⊗ Eᵢ) Θ'_μ = Θ'_ν (Eᵢ ⊗ 1) + Θ'_μ (K̃₋ᵢ ⊗ Eᵢ)` for `ν = μ + i`,
`(Eᵢ ⊗ 1) Θ'_ν = Θ'_ν (Eᵢ ⊗ 1)` for `νᵢ = 0` (the `Eᵢ`-components of
`Δ(Eᵢ) Θ = Θ Δ̄(Eᵢ)`) is the quasi-R-matrix `quasiR`. As in [Lus], only the identities for
the `Eᵢ` are used. -/
theorem quasiR_unique (Θ' : (I →₀ ℕ) → QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧)
    (h0 : Θ' 0 = 1)
    (hmem : ∀ ν, Θ' ν ∈ LinearMap.range (map
      ((quotientMinus R).toLinearMap ∘ₗ (quotientWeightSpace D ν).subtype)
      ((quotientPlus R).toLinearMap ∘ₗ (quotientWeightSpace D ν).subtype)))
    (hE : ∀ i μ, (E R 𝕧 i ⊗ₜ[𝕂] 1) * Θ' (μ + Finsupp.single i 1) +
        (K R 𝕧 (ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i) * Θ' μ =
      Θ' (μ + Finsupp.single i 1) * (E R 𝕧 i ⊗ₜ[𝕂] 1) +
        Θ' μ * (K R 𝕧 (-ktilde R i) ⊗ₜ[𝕂] E R 𝕧 i))
    (hE0 : ∀ i ν, ν i = 0 → (E R 𝕧 i ⊗ₜ[𝕂] 1) * Θ' ν = Θ' ν * (E R 𝕧 i ⊗ₜ[𝕂] 1)) :
    Θ' = quasiR R := by
  funext ν
  induction ν using WellFoundedLT.induction with
  | _ ν ih =>
  by_cases hν : ν = 0
  · subst hν; rw [h0, quasiR_zero]
  obtain ⟨t, ht⟩ := Submodule.sub_mem _ (hmem ν) (quasiR_mem_range R ν)
  suffices t = 0 by rw [← sub_eq_zero, ← ht, this, map_zero]
  refine eq_zero_of_forall_E_commute R hν t fun i ↦ ?_
  rw [ht, mul_sub, sub_mul, sub_eq_sub_iff_add_eq_add]
  by_cases hνi : ν i = 0
  · rw [hE0 i ν hνi, quasiR_E_of_eq_zero R i hνi, add_comm]
  obtain ⟨μ, rfl⟩ : ∃ μ, ν = μ + Finsupp.single i 1 :=
    ⟨ν - Finsupp.single i 1, (tsub_add_cancel_of_le (Finsupp.single_le_iff.2
      (Nat.one_le_iff_ne_zero.2 hνi))).symm⟩
  have hμ : Θ' μ = quasiR R μ :=
    ih μ (lt_add_of_pos_right μ (pos_iff_ne_zero.2 (Finsupp.single_ne_zero.2 one_ne_zero)))
  have h1 := hE i μ
  have h2 := quasiR_E R i μ
  rw [hμ] at h1
  rw [eq_sub_of_add_eq h1, eq_sub_of_add_eq h2]
  abel

end LieLean.QuantumGroup
