/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.RootVectors
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Symmetries

/-!
# `T'_{i,1}` and `T''_{i,-1}` on `U̇` and the rest of [Lus] 41.1.3

* `Modified.braidPrime hv i`: Lusztig's `T'_{i,1}` on `U̇` ([Lus] 41.1.1), induced by
  `T'_{i,1} = braidPrimeEquiv` on `U` (`braidPrime_elt`, `braidPrime_mul`,
  `braidPrime_one`: `T'_{i,1}(1_λ) = 1_{sᵢλ}`); its inverse `(braidPrime hv i).symm` is
  `T''_{i,-1}` on `U̇` (`braidPrime_symm_elt`).
* Over `ℚ(v)`: `T'_{i,1} = ω Tᵢ ω` on `U̇` (`braidPrime_eq_map_omega`), so `T'_{i,1}` and
  `T''_{i,-1}` preserve `𝒜U̇` ([Lus] 41.1.2, last assertion: `braidPrime_mem_aForm`,
  `braidPrime_symm_mem_aForm`).
* **[Lus] 41.1.3 (a) for `e = -1`** (`Modified.list_braidPrime_symm_qDivPow_E_mem_aPlus`:
  `T''_{i₁,-1} ⋯ T''_{iₙ₋₁,-1}(E_{iₙ}^{(t)}) ∈ 𝒜U⁺`) and **(b) for `e = 1`**
  (`Modified.list_braidPrime_qDivPow_E_mem_aPlus`: `T'_{i₁,1} ⋯ T'_{iₙ₋₁,1}(E_{iₙ}^{(t)}) ∈ 𝒜U⁺`),
  for `s_{i₁} ⋯ s_{iₙ}` reduced. By [Lus] 37.2.4 these elements are `±v^m` times the elements of
  (b) for `e = -1` and (a) for `e = 1` (`exists_list_braidPrime_symm_qDivPow_E`,
  `exists_list_braidPrime_qDivPow_E`), which are `Modified.list_braid_symm_qDivPow_E_mem_aPlus`,
  `Modified.list_braid_qDivPow_E_mem_aPlus`. (Lusztig proves the four cases alike, from 40.1.3 and
  41.1.2.)

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 37.2.4, 41.1.1–41.1.3.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

namespace Modified

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}

section General

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-- `(T'_{i,1}, sᵢ) ∈ torusAut`. -/
def braidPrimeAut (i : I) : torusAut R v :=
  ⟨(braidPrimeEquiv R hv i, reflAut R i), fun μ ↦ braidPrimeEquiv_K hv i μ⟩

/-- **Lusztig's `T'_{i,1}` on `U̇`** ([Lus] 41.1.1): the automorphism with
`T'_{i,1}(π_{λ',λ''}(u)) = π_{sᵢλ', sᵢλ''}(T'_{i,1} u)` (`braidPrime_elt`); it is multiplicative
(`braidPrime_mul`), and its inverse is Lusztig's `T''_{i,-1}` on `U̇` (`braidPrime_symm_elt`). -/
def braidPrime (i : I) : Modified R v ≃ₗ[k] Modified R v := mapHom R v (braidPrimeAut hv i)

lemma braidPrime_elt (i : I) (l₁ l₂ : Y →+ ℤ) {u : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v (l₁ - l₂))
    (hu' : braidPrimeEquiv R hv i u ∈
      adWeightSpace R v (l₁.comp (reflY R i) - l₂.comp (reflY R i))) :
    braidPrime hv i (elt l₁ l₂ u hu) =
      elt (l₁.comp (reflY R i)) (l₂.comp (reflY R i)) (braidPrimeEquiv R hv i u) hu' := by
  change map (braidPrimeAut hv i) _ = _
  rw [map_elt]
  exact elt_index (by ext μ; simp [braidPrimeAut]) (by ext μ; simp [braidPrimeAut]) rfl _ _

lemma braidPrime_mul (i : I) (x y : Modified R v) :
    braidPrime hv i (x * y) = braidPrime hv i x * braidPrime hv i y :=
  mapHom_mul _ x y

/-- `T'_{i,1}(1_λ) = 1_{sᵢλ}` ([Lus] 41.1.1). -/
lemma braidPrime_one (i : I) (l : Y →+ ℤ) :
    braidPrime (R := R) hv i (one l) = one (l.comp (reflY R i)) := by
  rw [one, braidPrime_elt hv i l l _
    (by rw [_root_.map_one, sub_self]; exact one_mem_adWeightSpace), one]
  exact elt_congr (_root_.map_one _) _ _

/-- The inverse of `T'_{i,1}` on `U̇` is induced by `T''_{i,-1}` ([Lus] 41.1.1). -/
lemma braidPrime_symm_elt (i : I) (l₁ l₂ : Y →+ ℤ) {u : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v (l₁ - l₂))
    (hu' : (braidPrimeEquiv R hv i).symm u ∈
      adWeightSpace R v (l₁.comp (reflY R i) - l₂.comp (reflY R i))) :
    (braidPrime hv i).symm (elt l₁ l₂ u hu) =
      elt (l₁.comp (reflY R i)) (l₂.comp (reflY R i)) ((braidPrimeEquiv R hv i).symm u) hu' := by
  have hc : ∀ l : Y →+ ℤ, (l.comp (reflY R i)).comp (reflY R i) = l := fun l ↦ by
    ext μ; simp
  rw [LinearEquiv.symm_apply_eq, braidPrime_elt hv i _ _ hu' (by
    rw [hc, hc, AlgEquiv.apply_symm_apply]; exact hu)]
  exact elt_index (hc l₁).symm (hc l₂).symm (AlgEquiv.apply_symm_apply _ _).symm _ _

end General

section RatFunc

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)

attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

/-- `T'_{i,1} = ω Tᵢ ω` on `U̇` ([Lus] 37.2.4). -/
lemma braidPrime_eq_map_omega (i : I) (x : Modified R 𝕧) :
    braidPrime ratFunc_X_not_root i x =
      map (omegaAut R) (braid ratFunc_X_not_root i (map (omegaAut R) x)) := by
  have h : braidPrimeAut (R := R) ratFunc_X_not_root i =
      omegaAut R * braidAut ratFunc_X_not_root i * omegaAut R :=
    torusAut_ext ratFunc_X_not_root (by ext u; rfl)
  change map _ x = map _ (map _ (map _ x))
  rw [map_map, map_map, h, mul_assoc]

/-- `T'_{i,1}` preserves `𝒜U̇` ([Lus] 41.1.2). -/
theorem braidPrime_mem_aForm (i : I) {x : Modified R 𝕧} (hx : x ∈ aForm R) :
    braidPrime ratFunc_X_not_root i x ∈ aForm R := by
  rw [braidPrime_eq_map_omega]
  exact map_omega_mem_aForm (braid_mem_aForm i (map_omega_mem_aForm hx))

/-- `T''_{i,-1} = (T'_{i,1})⁻¹` preserves `𝒜U̇` ([Lus] 41.1.2). -/
theorem braidPrime_symm_mem_aForm (i : I) {x : Modified R 𝕧} (hx : x ∈ aForm R) :
    (braidPrime ratFunc_X_not_root i).symm x ∈ aForm R := by
  have e : (braidPrime (R := R) ratFunc_X_not_root i).symm x =
      map (omegaAut R) ((braid ratFunc_X_not_root i).symm (map (omegaAut R) x)) := by
    rw [LinearEquiv.symm_apply_eq, braidPrime_eq_map_omega, map_omega_map_omega,
      LinearEquiv.apply_symm_apply, map_omega_map_omega]
  rw [e]
  exact map_omega_mem_aForm (braid_symm_mem_aForm i (map_omega_mem_aForm hx))

lemma isLaurent_sign_pow (e m : ℤ) (t : ℕ) : IsLaurent (((-1 : 𝕂) ^ e * 𝕧 ^ m) ^ t) := by
  refine IsLaurent.pow (IsLaurent.mul ?_ (isLaurent_zpow m)) t
  rcases Int.even_or_odd e with he | he
  · rw [he.neg_one_zpow]; exact isLaurent_one
  · rw [he.neg_one_zpow]; exact isLaurent_neg_one

/-- **[Lus] 41.1.3 (b)** for `e = 1`: if `s_{i₁} ⋯ s_{iₙ₋₁} s_i` is a reduced expression, then
`T'_{i₁,1} ⋯ T'_{iₙ₋₁,1}(E_i^{(t)}) ∈ 𝒜U⁺`. -/
theorem list_braidPrime_qDivPow_E_mem_aPlus
    {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}
    {ω : List I} {i : I} (hω : cs.IsReduced (ω ++ [i])) (t : ℕ) :
    (ω.map (braidPrimeEquiv R ratFunc_X_not_root)).prod (qDivPow (𝕧 ^ D.d i) t (E R 𝕧 i)) ∈
      aPlus R := by
  obtain ⟨e, m, h⟩ := exists_list_braidPrime_qDivPow_E (R := R) ratFunc_X_not_root ω i
  rw [h]
  exact smul_mem_aPlus (isLaurent_sign_pow e m t) (list_braid_qDivPow_E_mem_aPlus hω t)

/-- **[Lus] 41.1.3 (a)** for `e = -1`: if `s_{i₁} ⋯ s_{iₙ₋₁} s_i` is a reduced expression, then
`T''_{i₁,-1} ⋯ T''_{iₙ₋₁,-1}(E_i^{(t)}) ∈ 𝒜U⁺`. -/
theorem list_braidPrime_symm_qDivPow_E_mem_aPlus
    {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}
    {ω : List I} {i : I} (hω : cs.IsReduced (ω ++ [i])) (t : ℕ) :
    (ω.map fun j ↦ (braidPrimeEquiv R ratFunc_X_not_root j).symm).prod
      (qDivPow (𝕧 ^ D.d i) t (E R 𝕧 i)) ∈ aPlus R := by
  obtain ⟨e, m, h⟩ := exists_list_braidPrime_symm_qDivPow_E (R := R) ratFunc_X_not_root ω i
  rw [h]
  exact smul_mem_aPlus (isLaurent_sign_pow e m t) (list_braid_symm_qDivPow_E_mem_aPlus hω t)

end RatFunc

end Modified

end LieLean.QuantumGroup
