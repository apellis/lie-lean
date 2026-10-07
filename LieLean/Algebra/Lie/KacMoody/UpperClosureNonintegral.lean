/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.UpperClosure
import LieLean.LinearAlgebra.Matrix.Cartan.IntegralWeylGroupFacet

/-!
# Upper closures of facets for arbitrary weights (finite type)

The combinatorial input to Humphreys, GSM 94, Theorem 7.9, for weights that need not be integral.
Fix `a = λ + ρ`, `b = μ + ρ` with `a - b` integral and `λ`, `μ` antidominant
(`⟨a, β^∨⟩, ⟨b, β^∨⟩ ∉ ℤ_{>0}` for the positive roots `β`), such that every positive root
orthogonal to `a` is orthogonal to `b`. The definitions `Matrix.Realization.MemUpperClosure` and
`Matrix.Realization.UpperClosureCondition` of `UpperClosure.lean` only involve the roots `β` with
`⟨x + ρ, β^∨⟩ ∈ ℤ`, i.e. the roots integral for `λ`, so they are the conditions of Humphreys,
GSM 94, §7.3–7.4, relative to the integral root system `Φ_[λ]`.

## Main results

* `Matrix.Realization.memUpperClosure_weylDot_iff_of_isAntidominant`: for `w ∈ W`, `w·μ` lies in
  the upper closure of the facet of `w·λ` iff no positive root `β` with `⟨w b, β^∨⟩ = 0` has
  `⟨w a, β^∨⟩ > 0`.
* `Matrix.Realization.exists_apply_sub_eq_rootOf_of_upperClosureCondition_of_integral`
  (minimality): if this condition holds at `w` and `w' b = w b`, then `w' a - w a ∈ Q₊`.
* `Matrix.Realization.exists_upperClosureCondition_of_integral` (descent): for `w ∈ W_[λ]`, a
  chain of reflections in positive roots orthogonal to `w b` leads from `w a` to some `w'' a`
  with `w'' ∈ W_[λ]`, `w'' b = w b`, at which the condition holds.

The proofs follow the integral case (`UpperClosure.lean`), with the stabilizer of `b` (generated
by the reflections in the roots orthogonal to `b`, which are integral) in place of the standard
parabolic subgroup on the simple walls of `b`; see
`Matrix.Realization.exists_mul_eq_isPosRoot_of_orth`,
`Matrix.Realization.apply_sub_mem_orthPosRootCone` and
`Matrix.Realization.apply_eq_self_of_apply_eq_of_orth`. Reconstructed.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.3, §7.4, Theorem 7.9.
-/

noncomputable section

open Module

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  (hF : A.IsFiniteCartan)

omit [DecidableEq ι] [CharZero K] in
lemma symm_apply_coroot_eq_corootPairing {hA : A.IsGeneralizedCartan} (v : P.weylGroup hA)
    (x : Dual K H) (i : ι) :
    (v : Dual K H ≃ₗ[K] Dual K H).symm x (P.coroot i) = P.corootPairing hA x v i :=
  rfl

omit [DecidableEq ι] in
lemma isPosRoot_iff_mem_posWeights {hA : A.IsGeneralizedCartan} {v : P.weylGroup hA} {i : ι} :
    P.IsPosRoot hA v i ↔ (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∈ P.posWeights := by
  classical
  rw [isPosRoot_iff_not_isRightDescent, P.apply_root_mem_posWeights_iff hA]

/-! ### Minimality -/

/-- **Minimality.** Let `a - b` be integral and `⟨a, β^∨⟩ ∉ ℤ_{>0}` for all positive roots `β`.
If no positive root `β` with `⟨w b, β^∨⟩ = 0` has `⟨w a, β^∨⟩ > 0` and `w' b = w b`, then
`w' a - w a ∈ Q₊`. -/
theorem exists_apply_sub_eq_rootOf_of_upperClosureCondition_of_integral [FiniteDimensional K H]
    {a b : Dual K H} (hab : ∀ j, ∃ n : ℤ, (a - b) (P.coroot j) = n)
    (ha : ∀ v i, P.IsPosRoot hF.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hF.isGeneralizedCartan a v i = n → n ≤ 0)
    {w w' : P.weylGroup hF.isGeneralizedCartan}
    (hU : P.UpperClosureCondition hF.isGeneralizedCartan (w.val a) (w.val b))
    (hb' : w'.val b = w.val b) :
    ∃ c : ι → ℤ, 0 ≤ c ∧ w'.val a - w.val a = P.rootOf c := by
  classical
  have hort : ∀ v i, P.IsPosRoot hF.isGeneralizedCartan v i →
      P.corootPairing hF.isGeneralizedCartan b v i = 0 →
        ∃ n : ℤ, n ≤ 0 ∧ P.corootPairing hF.isGeneralizedCartan a v i = n := by
    intro v i hv hb0
    obtain ⟨n, hn⟩ := (P.isIntegralRoot_congr _ hab v i).mpr
      ⟨0, by rw [Int.cast_zero]; exact hb0⟩
    exact ⟨n, ha v i hv n hn, hn⟩
  obtain ⟨w₁, u₁, rfl, hu₁b, hpos⟩ := exists_mul_eq_isPosRoot_of_orth (P := P) b w
  have hu₁a : (u₁ : Dual K H ≃ₗ[K] Dual K H) a = a := by
    refine apply_eq_self_of_apply_eq_of_orth hF hab hort hu₁b fun v i hv hb0 ↦ ?_
    have hpw : ((w₁ * v : P.weylGroup _) : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∈
        P.posWeights := isPosRoot_iff_mem_posWeights.mp (hpos v i hv hb0)
    have hwb : ((w₁ * v : P.weylGroup _) : Dual K H ≃ₗ[K] Dual K H).symm
        ((w₁ * u₁ : P.weylGroup _).val b) (P.coroot i) = 0 := by
      rw [symm_apply_coroot_eq_corootPairing]
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hu₁b, corootPairing_apply, ← mul_assoc,
        _root_.inv_mul_cancel, one_mul]
      exact hb0
    obtain ⟨n, hn⟩ := hU _ (w₁ * v).2 i hpw hwb
    rw [symm_apply_coroot_eq_corootPairing] at hn
    change P.corootPairing _ (((w₁ * u₁ : P.weylGroup _) : Dual K H ≃ₗ[K] Dual K H) a) _ i = _
      at hn
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, corootPairing_apply, ← mul_assoc,
      _root_.inv_mul_cancel, one_mul] at hn
    exact ⟨-(n : ℤ), by omega, by rw [hn]; push_cast; ring⟩
  have hvb : ((w₁⁻¹ * w' : P.weylGroup _) : Dual K H ≃ₗ[K] Dual K H) b = b := by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
    change ((w₁⁻¹ : P.weylGroup _) : Dual K H ≃ₗ[K] Dual K H) (w'.val b) = b
    rw [hb', Subgroup.coe_mul, LinearEquiv.mul_apply, inv_apply_apply, hu₁b]
  have hx := apply_sub_mem_orthPosRootCone hF hort hvb
  -- `w₁` maps the cone of the positive roots orthogonal to `b` into `Q₊`
  have hmap : ∀ x ∈ P.orthPosRootCone hF.isGeneralizedCartan b, ∃ c : ι → ℤ, 0 ≤ c ∧
      (w₁ : Dual K H ≃ₗ[K] Dual K H) x = P.rootOf c := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨v, i, ⟨hv, hb0⟩, rfl⟩ := hx
      obtain ⟨k, hk, hk'⟩ := hpos v i hv hb0
      exact ⟨k, hk, by rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul]; exact hk'⟩
    | zero => exact ⟨0, le_rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c₁, h₁, e₁⟩ := hx
      obtain ⟨c₂, h₂, e₂⟩ := hy
      exact ⟨c₁ + c₂, add_nonneg h₁ h₂, by rw [map_add, e₁, e₂, map_add]⟩
  obtain ⟨c, hc, hce⟩ := hmap _ hx
  refine ⟨c, hc, ?_⟩
  rw [← hce]
  simp only [map_sub, Subgroup.coe_mul, LinearEquiv.mul_apply, apply_inv_apply, hu₁a]

/-! ### Descent -/

/-- **Descent.** Let `a - b` be integral and `⟨a, β^∨⟩ ∉ ℤ_{>0}` for all positive roots `β`. For
every `w ∈ W_[a]` there is `w'' ∈ W_[a]` with `w'' b = w b` such that no positive root `β` with
`⟨w b, β^∨⟩ = 0` has `⟨w'' a, β^∨⟩ > 0`, and `w'' a` is reached from `w a` by a chain of
reflections `ξ ↦ ξ - ⟨ξ, β^∨⟩ β` in positive roots `β` orthogonal to `w b` with
`⟨ξ, β^∨⟩ > 0`. Induction on the height of `w a - a ∈ Q₊`
(`Matrix.Realization.exists_nonneg_apply_sub_eq_rootOf`). -/
theorem exists_upperClosureCondition_of_integral {a b : Dual K H}
    (hab : ∀ j, ∃ n : ℤ, (a - b) (P.coroot j) = n)
    (ha : ∀ v i, P.IsPosRoot hF.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hF.isGeneralizedCartan a v i = n → n ≤ 0)
    {w : P.weylGroup hF.isGeneralizedCartan}
    (hw : w ∈ P.integralWeylGroup hF.isGeneralizedCartan a) :
    ∃ w'' : P.weylGroup hF.isGeneralizedCartan,
      w'' ∈ P.integralWeylGroup hF.isGeneralizedCartan a ∧ w''.val b = w.val b ∧
      P.UpperClosureCondition hF.isGeneralizedCartan (w''.val a) (w.val b) ∧
      Relation.ReflTransGen (P.WallStep hF.isGeneralizedCartan (w.val b)) (w.val a)
        (w''.val a) := by
  classical
  suffices H : ∀ N : ℕ, ∀ w ∈ P.integralWeylGroup hF.isGeneralizedCartan a, ∀ c : ι → ℤ,
      0 ≤ c → (w : Dual K H ≃ₗ[K] Dual K H) a - a = P.rootOf c → (∑ j, c j).toNat = N →
      ∃ w'' : P.weylGroup hF.isGeneralizedCartan,
        w'' ∈ P.integralWeylGroup hF.isGeneralizedCartan a ∧ w''.val b = w.val b ∧
        P.UpperClosureCondition hF.isGeneralizedCartan (w''.val a) (w.val b) ∧
        Relation.ReflTransGen (P.WallStep hF.isGeneralizedCartan (w.val b)) (w.val a)
          (w''.val a) by
    obtain ⟨c, hc, hce⟩ := exists_nonneg_apply_sub_eq_rootOf hF ha hw
    exact H _ w hw c hc hce rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro w hw c hc hce hN
  by_cases hU : P.UpperClosureCondition hF.isGeneralizedCartan (w.val a) (w.val b)
  · exact ⟨w, hw, rfl, hU, .refl⟩
  unfold UpperClosureCondition at hU
  push Not at hU
  obtain ⟨v, hv, i, hpos, hvb, hva⟩ := hU
  set u : P.weylGroup hF.isGeneralizedCartan := ⟨v, hv⟩ with hu
  -- the pairing `⟨w a, β^∨⟩` is an integer, hence a positive one
  have hint : ∃ z : ℤ, P.corootPairing hF.isGeneralizedCartan (w.val a) u i = z := by
    have h1 : P.IsIntegralRoot hF.isGeneralizedCartan b (w⁻¹ * u) i := ⟨0, by
      change P.corootPairing _ b (w⁻¹ * u) i = _
      rw [← corootPairing_apply, Int.cast_zero]
      exact hvb⟩
    obtain ⟨z, hz⟩ := (P.isIntegralRoot_congr _ hab _ i).mpr h1
    refine ⟨z, ?_⟩
    rw [corootPairing_apply]
    exact hz
  obtain ⟨z, hz⟩ := hint
  have hz0 : 0 < z := by
    by_contra hle
    push Not at hle
    apply hva (-z).toNat
    rw [symm_apply_coroot_eq_corootPairing (v := u), hz]
    have h' : (((-z).toNat : ℕ) : K) = ((-z : ℤ) : K) := by
      exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ -z by omega)
    rw [h']
    push_cast
    ring
  set n := z.toNat with hn
  have hnz : (n : K) = z := by exact_mod_cast Int.toNat_of_nonneg hz0.le
  have hn0 : 0 < n := by omega
  set s := P.reflectionOf hF.isGeneralizedCartan u i
  have hsb : (s * w).val b = w.val b := by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, reflectionOf_apply',
      ← symm_apply_coroot_eq_corootPairing (v := u)]
    change (w : Dual K H ≃ₗ[K] Dual K H) b - v.symm (w.val b) (P.coroot i) • _ = _
    rw [hvb, zero_smul, sub_zero]
  have hsa : (s * w).val a = w.val a - n • v (P.root i) := by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, reflectionOf_apply', hz, ← hnz,
      Nat.cast_smul_eq_nsmul]
  have hstep : P.WallStep hF.isGeneralizedCartan (w.val b) (w.val a) ((s * w).val a) :=
    ⟨v, hv, i, n, hpos, hn0, hvb, by rw [symm_apply_coroot_eq_corootPairing (v := u), hz, ← hnz],
      hsa⟩
  -- `s w ∈ W_[a]`
  have hWa : P.integralWeylGroup hF.isGeneralizedCartan (w.val a) =
      P.integralWeylGroup hF.isGeneralizedCartan a := by
    refine P.integralWeylGroup_eq_of_integral _ fun j ↦ ?_
    rw [show w.val a = (w : Dual K H ≃ₗ[K] Dual K H) a from rfl, hce]
    exact P.exists_int_of_mem_rootLattice (P.rootOf_mem_rootLattice c) j
  have hsw : s * w ∈ P.integralWeylGroup hF.isGeneralizedCartan a := by
    refine mul_mem ?_ hw
    rw [← hWa]
    exact (P.reflectionOf_mem_integralWeylGroup_iff _ u i).mpr ⟨z, hz⟩
  obtain ⟨c', hc', hce'⟩ := exists_nonneg_apply_sub_eq_rootOf hF ha hsw
  obtain ⟨k₁, hk₁, hk₁e⟩ := hpos
  have hcc' : c' = c - n • k₁ := P.rootOf_injective (by
    rw [map_sub, map_nsmul, ← hce, ← hce']
    rw [show ((s * w : P.weylGroup _) : Dual K H ≃ₗ[K] Dual K H) a = (s * w).val a from rfl, hsa,
      hk₁e]
    abel)
  have hlt : (∑ j, c' j).toNat < N := by
    have h1 := KacMoodyAlgebra.sum_pos_of_mem_posCone hk₁
    have h2 : 0 ≤ ∑ j, c' j := Finset.sum_nonneg fun j _ ↦ hc' j
    have h3 : 0 < (n : ℤ) * ∑ j, k₁ j := mul_pos (by exact_mod_cast hn0) h1
    have h4 : ∑ j, c' j = ∑ j, c j - (n : ℤ) * ∑ j, k₁ j := by
      rw [hcc', Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by simp
    omega
  obtain ⟨w'', hw'', hw''b, hw''U, hchain⟩ := ih _ hlt (s * w) hsw c' hc' hce' rfl
  rw [hsb] at hw''b hw''U hchain
  exact ⟨w'', hw'', hw''b, hw''U, .head hstep hchain⟩

/-! ### The upper closure and the reduced condition -/

omit [DecidableEq ι] [CharZero K] in
private lemma natCast_toNat' {z : ℤ} (hz : 0 ≤ z) : ((z.toNat : ℕ) : K) = (z : K) := by
  rw [← Int.cast_natCast (R := K), Int.toNat_of_nonneg hz]

/-- For `a = λ + ρ`, `b = μ + ρ` with `λ`, `μ` antidominant, `a - b` integral and every positive
root orthogonal to `a` orthogonal to `b`, and `w ∈ W`: `w·μ` lies in the upper closure of the
facet of `w·λ` iff no positive root `β` with `⟨w b, β^∨⟩ = 0` has `⟨w a, β^∨⟩ > 0`. -/
theorem memUpperClosure_weylDot_iff_of_isAntidominant {lam μ : Dual K H}
    (hlam : P.IsAntidominant hF.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hF.isGeneralizedCartan μ)
    (hab : ∀ j, ∃ n : ℤ, ((lam + P.rho) - (μ + P.rho)) (P.coroot j) = n)
    (hfacet : ∀ v i, P.IsPosRoot hF.isGeneralizedCartan v i →
      P.corootPairing hF.isGeneralizedCartan (lam + P.rho) v i = 0 →
        P.corootPairing hF.isGeneralizedCartan (μ + P.rho) v i = 0)
    (w : P.weylGroup hF.isGeneralizedCartan) :
    P.MemUpperClosure hF.isGeneralizedCartan (P.weylDot hF.isGeneralizedCartan w lam)
        (P.weylDot hF.isGeneralizedCartan w μ) ↔
      P.UpperClosureCondition hF.isGeneralizedCartan (w.val (lam + P.rho))
        (w.val (μ + P.rho)) := by
  classical
  set a := lam + P.rho
  set b := μ + P.rho
  -- the two pairings for a positive root `v αᵢ`
  have key : ∀ v ∈ P.weylGroup hF.isGeneralizedCartan, ∀ i,
      ((¬∃ z : ℤ, v.symm (w.val a) (P.coroot i) = z) ∧
        (¬∃ z : ℤ, v.symm (w.val b) (P.coroot i) = z)) ∨
      ∃ sa sb : ℤ, 0 ≤ sa ∧ 0 ≤ sb ∧ (sa = 0 → sb = 0) ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        v.symm (w.val a) (P.coroot i) = ((-ε * sa : ℤ) : K) ∧
        v.symm (w.val b) (P.coroot i) = ((-ε * sb : ℤ) : K) := by
    intro v hv i
    set u : P.weylGroup hF.isGeneralizedCartan := w⁻¹ * ⟨v, hv⟩
    have hA' : ∀ x : Dual K H, v.symm (w.val x) (P.coroot i) =
        P.corootPairing hF.isGeneralizedCartan x u i := fun x ↦ by
      rw [symm_apply_coroot_eq_corootPairing (v := ⟨v, hv⟩)]
      exact corootPairing_apply w _ x i
    simp only [hA']
    by_cases hbint : ∃ z : ℤ, P.corootPairing hF.isGeneralizedCartan b u i = z
    · obtain ⟨zb, hzb⟩ := hbint
      obtain ⟨za, hza⟩ := (P.isIntegralRoot_congr _ hab u i).mpr ⟨zb, hzb⟩
      change P.corootPairing _ a u i = _ at hza
      right
      rcases isPosRoot_or u i with hp | hp
      · have h1 := hlam u i hp za hza
        have h2 := hμ u i hp zb hzb
        have hfz : za = 0 → zb = 0 := fun h0 ↦ by
          have := hfacet u i hp (by rw [hza, h0, Int.cast_zero])
          rw [hzb] at this
          exact_mod_cast this
        refine ⟨-za, -zb, by omega, by omega, fun h0 ↦ by have := hfz (by omega); omega, 1,
          Or.inl rfl, ?_, ?_⟩
        · rw [hza]; push_cast; ring
        · rw [hzb]; push_cast; ring
      · have hma := corootPairing_mul_simple a u i
        have hmb := corootPairing_mul_simple b u i
        rw [hza] at hma
        rw [hzb] at hmb
        have h1 := hlam _ i hp (-za) (by rw [hma]; push_cast; ring)
        have h2 := hμ _ i hp (-zb) (by rw [hmb]; push_cast; ring)
        have hfz : za = 0 → zb = 0 := fun h0 ↦ by
          have := hfacet _ i hp (by rw [hma, h0]; push_cast; ring)
          rw [hmb] at this
          have h' : ((zb : ℤ) : K) = 0 := by linear_combination -this
          exact_mod_cast h'
        refine ⟨za, zb, by omega, by omega, hfz, -1, Or.inr rfl, ?_, ?_⟩
        · rw [hza]; push_cast; ring
        · rw [hzb]; push_cast; ring
    · left
      refine ⟨fun ⟨za, hza⟩ ↦ hbint ?_, hbint⟩
      have hab' : ∀ j, ∃ n : ℤ, (b - a) (P.coroot j) = n := fun j ↦ by
        obtain ⟨n, hn⟩ := hab j
        exact ⟨-n, by rw [← neg_sub, LinearMap.neg_apply, hn, Int.cast_neg]⟩
      exact (P.isIntegralRoot_congr _ hab' u i).mpr ⟨za, hza⟩
  simp only [MemUpperClosure, UpperClosureCondition, weylDot_add_rho]
  constructor
  · intro hU v hv i hpos hb0
    rcases key v hv i with ⟨-, hbn⟩ | ⟨sa, sb, hsa, hsb, hab0, ε, hε, h1, h2⟩
    · exact absurd ⟨0, by rw [hb0, Int.cast_zero]⟩ hbn
    obtain ⟨-, hU2, -⟩ := hU v hv i hpos
    rw [h2] at hb0
    have hb0' : -ε * sb = 0 := by exact_mod_cast hb0
    rcases hε with rfl | rfl
    · exact ⟨sa.toNat, by rw [h1, natCast_toNat' hsa]; push_cast; ring⟩
    · by_cases hsa0 : sa = 0
      · exact ⟨0, by rw [h1, hsa0]; simp⟩
      · obtain ⟨m, hm, hm'⟩ := hU2 ⟨sa.toNat, by omega, by
          rw [h1, natCast_toNat' hsa]; push_cast; ring⟩
        rw [h2] at hm'
        have : - -1 * sb = (m : ℤ) := by exact_mod_cast hm'
        exfalso
        omega
  · intro hC v hv i hpos
    rcases key v hv i with ⟨han, hbn⟩ | ⟨sa, sb, hsa, hsb, hab0, ε, hε, h1, h2⟩
    · refine ⟨fun h0 ↦ absurd ⟨0, by rw [h0, Int.cast_zero]⟩ han, ?_, ?_⟩
      · rintro ⟨n, -, hn⟩
        exact absurd ⟨n, by rw [hn, Int.cast_natCast]⟩ han
      · rintro ⟨n, -, hn⟩
        exact absurd ⟨-(n : ℤ), by rw [hn]; push_cast; ring⟩ han
    have hC' := hC v hv i hpos
    refine ⟨fun h0 ↦ ?_, ?_, ?_⟩
    · rw [h1] at h0
      have h0' : -ε * sa = 0 := by exact_mod_cast h0
      have : sa = 0 := by rcases hε with rfl | rfl <;> omega
      rw [h2, hab0 this, mul_zero, Int.cast_zero]
    · rintro ⟨n, hn, hn'⟩
      rw [h1] at hn'
      have hn'' : -ε * sa = (n : ℤ) := by exact_mod_cast hn'
      rcases hε with rfl | rfl
      · exfalso
        omega
      · have hsb0 : sb ≠ 0 := fun h0 ↦ by
          obtain ⟨q, hq⟩ := hC' (by rw [h2, h0, mul_zero, Int.cast_zero])
          rw [h1] at hq
          have : - -1 * sa = -(q : ℤ) := by exact_mod_cast hq
          omega
        exact ⟨sb.toNat, by omega, by rw [h2, natCast_toNat' hsb]; push_cast; ring⟩
    · rintro ⟨n, hn, hn'⟩
      rw [h1] at hn'
      have hn'' : -ε * sa = -(n : ℤ) := by exact_mod_cast hn'
      rcases hε with rfl | rfl
      · exact ⟨sb.toNat, by rw [h2, natCast_toNat' hsb]; push_cast; ring⟩
      · exfalso
        omega

end Matrix.Realization
