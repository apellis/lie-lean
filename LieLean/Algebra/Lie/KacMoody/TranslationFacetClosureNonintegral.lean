/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationFacetClosure
import LieLean.Algebra.Lie.KacMoody.TranslationNonintegral

/-!
# Translation out of a facet closure for arbitrary weights

Humphreys, GSM 94, Theorem 7.12 for arbitrary, not necessarily integral, weights. Let `A` be of
finite type, `λ`, `μ` antidominant (`Matrix.Realization.IsAntidominant`: `⟨λ + ρ, β^∨⟩ ∉ ℤ_{>0}`
for every positive root `β`), and `ν = z (λ - μ)` (`z ∈ W`) dominant integral. Then for every
`w ∈ W`, `T_μ^λ M(w·μ)` (the `χ_λ`-block of `M(w·μ) ⊗ L(ν)`) has a standard filtration whose Verma
modules are the `M((w w')·λ)`, `w'` running over the stabilizer `W_μ°` of `μ` modulo that of `λ`,
each exactly once.

## Main results

* `Matrix.Realization.exists_apply_eq_of_add_eq_apply_of_antidominant`: the root-datum core.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.`
  `exists_weylDot_eq_of_add_eq_weylDot_of_isAntidominant`: if `ν'` is a weight of `L(ν)` and
  `w·μ + ν' = y·λ`, then `y·λ = (w w')·λ` with `w'·μ = μ`.
* `Matrix.Realization.KacMoodyAlgebra.exists_translation_verma_filtration_of_isAntidominant`,
  `Matrix.Realization.KacMoodyAlgebra.character_translation_verma_of_isAntidominant`: Humphreys,
  Theorem 7.12, as a filtration statement and on characters.

Humphreys states the theorem for `w ∈ W_[λ]`, with `μ♮` in the closure of the facet of `λ♮`; the
statements here hold for all `w ∈ W` and do not need the facet condition.

## Proof

Write `a = λ + ρ`, `b = μ + ρ` and suppose `b + ν₁ = x a` with `ν₁` a weight of `L(ν)`, `x ∈ W`.
Then `x ∈ W_[a]`, and `x a - a` lies in the cone spanned by the positive roots integral for `a`, on
which `( · | b)` is `≤ 0`. The norm comparison `|x a - b| = |ν₁| ≤ |ν| = |a - b|` forces
`(x a - a | b) = 0`. Choose `g` in the stabilizer of `b` for which `c = g⁻¹ x a` has `c - a ∈ Q₊`
of minimal height; then `c` is antidominant on the positive roots orthogonal to `b`, and `c - a`
lies in the cone of those roots, so `(c - a | a), (c - a | c) ≤ 0` with sum `0`. Hence
`|c - a|² = 0` and `x a = g a`. The argument is our own; all comparisons are between rationals.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.12.
-/

noncomputable section

open Module

namespace Matrix.Realization

section RootDatum

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ} {P : Realization A K H}
  (hF : A.IsFiniteCartan)

/-- On the cone of the positive roots integral for `a`, the form `( · | b)` takes values in
`ℚ_{≤ 0}` when `a - b` is integral and `⟨b, β^∨⟩ ≤ 0` for the positive integral roots; an element
of the cone with `(x | b) = 0` lies in the cone of the positive roots orthogonal to `b`. -/
lemma exists_bilinForm_eq_of_mem_integralPosRootCone (S : A.Symmetrization) {a b : Dual K H}
    (hab : ∀ j, ∃ n : ℤ, (a - b) (P.coroot j) = n)
    (hb : ∀ v i, P.IsPosRoot hF.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hF.isGeneralizedCartan b v i = n → n ≤ 0)
    {x : Dual K H} (hx : x ∈ P.integralPosRootCone hF.isGeneralizedCartan a) :
    ∃ q : ℚ, q ≤ 0 ∧ P.dualBilinForm S x b = q ∧
      (q = 0 → x ∈ P.orthPosRootCone hF.isGeneralizedCartan b) := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨v, i, hv, hint, rfl⟩ := hx
    obtain ⟨n, hn⟩ := (P.isIntegralRoot_congr _ hab v i).mp hint
    change P.corootPairing _ b v i = n at hn
    have hform : ∀ y : Dual K H, P.dualBilinForm S y ((v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) =
        P.corootPairing hF.isGeneralizedCartan y v i / S.ε i := by
      intro y
      rw [← P.dualBilinForm_weylGroup hF.isGeneralizedCartan S (v⁻¹).2, inv_apply_apply,
        dualBilinForm_root_right]
      rfl
    refine ⟨n / S.ε i, div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hb v i hv n hn)
      (S.ε_pos i).le, ?_, fun h0 ↦ ?_⟩
    · rw [(P.isSymm_dualBilinForm S).eq, hform, hn]
      push_cast
      rfl
    · have hn0 : n = 0 := by
        rw [div_eq_zero_iff] at h0
        exact_mod_cast h0.resolve_right (S.ε_ne_zero i)
      exact AddSubmonoid.subset_closure ⟨v, i, ⟨hv, by rw [hn, hn0, Int.cast_zero]⟩, rfl⟩
  | zero => exact ⟨0, le_rfl, by simp, fun _ ↦ zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨q₁, hq₁, hx₁, hx₂⟩ := hx
    obtain ⟨q₂, hq₂, hy₁, hy₂⟩ := hy
    refine ⟨q₁ + q₂, add_nonpos hq₁ hq₂, ?_,
      fun h0 ↦ add_mem (hx₂ (by linarith)) (hy₂ (by linarith))⟩
    rw [map_add, LinearMap.add_apply, hx₁, hy₁]
    push_cast
    rfl

/-- **The surviving weights, root-datum form, arbitrary weights.** Let `A` be of finite type,
`a - b` integral, and `⟨a, β^∨⟩, ⟨b, β^∨⟩ ∉ ℤ_{>0}` for every positive root `β`. Let
`ν = z (a - b)` be dominant integral (`z ∈ W`) and `ν₁ = u ν₂` with `u ∈ W`, `ν₂` dominant
integral and `ν - ν₂ ∈ Q₊`. If `b + ν₁ = x a` with `x ∈ W`, then `x a = g a` for some `g ∈ W`
with `g b = b`. -/
theorem exists_apply_eq_of_add_eq_apply_of_antidominant {a b : Dual K H}
    (hab : ∀ j, ∃ n : ℤ, (a - b) (P.coroot j) = n)
    (ha : ∀ v i, P.IsPosRoot hF.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hF.isGeneralizedCartan a v i = n → n ≤ 0)
    (hb : ∀ v i, P.IsPosRoot hF.isGeneralizedCartan v i → ∀ n : ℤ,
      P.corootPairing hF.isGeneralizedCartan b v i = n → n ≤ 0)
    {z u x : P.weylGroup hF.isGeneralizedCartan}
    (hν : ∀ i, ∃ n : ℕ, (z : Dual K H ≃ₗ[K] Dual K H) (a - b) (P.coroot i) = n)
    {ν₂ : Dual K H} (hν₂ : ∀ i, ∃ n : ℕ, ν₂ (P.coroot i) = n) {c : ι → ℤ} (hc : 0 ≤ c)
    (hνc : (z : Dual K H ≃ₗ[K] Dual K H) (a - b) - ν₂ = P.rootOf c)
    (h : b + (u : Dual K H ≃ₗ[K] Dual K H) ν₂ = (x : Dual K H ≃ₗ[K] Dual K H) a) :
    ∃ g : P.weylGroup hF.isGeneralizedCartan, (g : Dual K H ≃ₗ[K] Dual K H) b = b ∧
      (g : Dual K H ≃ₗ[K] Dual K H) a = (x : Dual K H ≃ₗ[K] Dual K H) a := by
  classical
  have := P.finite_weylGroup hF
  obtain ⟨d, hdpos, hpos⟩ := hF.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hpos.isHermitian
  set S := Symmetrization.ofDiagonal d hdpos hsymm
  set B := P.dualBilinForm S
  have hB (k : ι → ℤ) (y : Dual K H) := P.dualBilinForm_ofDiagonal_rootOf d hdpos hsymm k y
  have hW (w : P.weylGroup hF.isGeneralizedCartan) (y y' : Dual K H) :
      B ((w : Dual K H ≃ₗ[K] Dual K H) y) ((w : Dual K H ≃ₗ[K] Dual K H) y') = B y y' :=
    P.dualBilinForm_weylGroup hF.isGeneralizedCartan S w.2 y y'
  have hBsymm (y y' : Dual K H) : B y y' = B y' y := (P.isSymm_dualBilinForm S).eq y y'
  have hν₂int : ∀ j, ∃ n : ℤ, ν₂ (P.coroot j) = n := fun j ↦ by
    obtain ⟨n, hn⟩ := hν₂ j
    exact ⟨n, by rw [hn, Int.cast_natCast]⟩
  -- the stabilizer of `b` lies in `W_[a]`, and so does `x`
  have hstab : ∀ g : P.weylGroup hF.isGeneralizedCartan, (g : Dual K H ≃ₗ[K] Dual K H) b = b →
      g ∈ P.integralWeylGroup hF.isGeneralizedCartan a := by
    intro g hg
    rw [mem_integralWeylGroup]
    have e : (g : Dual K H ≃ₗ[K] Dual K H) a - a =
        (g : Dual K H ≃ₗ[K] Dual K H) (a - b) - (a - b) := by
      rw [map_sub, hg]
      abel
    rw [e]
    exact P.apply_sub_mem_rootLattice_of_integral hF.isGeneralizedCartan g.2 hab
  have hx : x ∈ P.integralWeylGroup hF.isGeneralizedCartan a := by
    rw [mem_integralWeylGroup, ← h]
    have e : b + (u : Dual K H ≃ₗ[K] Dual K H) ν₂ - a =
        ((u : Dual K H ≃ₗ[K] Dual K H) ν₂ - ν₂) - P.rootOf c +
          ((z : Dual K H ≃ₗ[K] Dual K H) (a - b) - (a - b)) := by
      rw [← hνc]
      abel
    rw [e]
    exact add_mem (sub_mem (P.apply_sub_mem_rootLattice_of_integral _ u.2 hν₂int)
      (P.rootOf_mem_rootLattice c)) (P.apply_sub_mem_rootLattice_of_integral _ z.2 hab)
  -- `(x a - a | b) = q ≤ 0`
  obtain ⟨q, hq, hxq, -⟩ := exists_bilinForm_eq_of_mem_integralPosRootCone hF S hab hb
    (apply_sub_mem_integralPosRootCone hF ha hx)
  -- the norm comparison: `R₁ = |ν|² - |ν₂|² ≥ 0` and `R₁ = 2 q`
  choose n2 hn2 using hν₂
  choose nν hnν using hν
  set R₁ : ℤ := ∑ i, c i * d i * ((nν i : ℤ) + n2 i) with hR₁
  have hR₁nonneg : 0 ≤ R₁ := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (hc i) (hdpos i).le) (by positivity)
  have hR₁eq : B ((z : Dual K H ≃ₗ[K] Dual K H) (a - b)) ((z : Dual K H ≃ₗ[K] Dual K H) (a - b))
      - B ν₂ ν₂ = R₁ := by
    have hsplit : (z : Dual K H ≃ₗ[K] Dual K H) (a - b) = ν₂ + P.rootOf c := by
      rw [← hνc]; abel
    calc _ = B (P.rootOf c) ((z : Dual K H ≃ₗ[K] Dual K H) (a - b) + ν₂) := by
          rw [hsplit]
          simp only [map_add, LinearMap.add_apply]
          rw [hBsymm ν₂ (P.rootOf c)]
          ring
      _ = R₁ := by
          rw [hB, hR₁]
          push_cast
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [LinearMap.add_apply, hnν, hn2]
  have hR₂ : B (a - b) (a - b) - B ((x : Dual K H ≃ₗ[K] Dual K H) a - b)
      ((x : Dual K H ≃ₗ[K] Dual K H) a - b) = 2 * q := by
    have h1 : B ((x : Dual K H ≃ₗ[K] Dual K H) a) ((x : Dual K H ≃ₗ[K] Dual K H) a) = B a a :=
      hW x a a
    have h2 := hxq
    simp only [map_sub, LinearMap.sub_apply] at h2 ⊢
    rw [hBsymm b a, hBsymm b ((x : Dual K H ≃ₗ[K] Dual K H) a)]
    linear_combination (-1 : K) * h1 + 2 * h2
  have hR : (R₁ : K) = 2 * q := by
    have h3 : (x : Dual K H ≃ₗ[K] Dual K H) a - b = (u : Dual K H ≃ₗ[K] Dual K H) ν₂ := by
      rw [← h]; abel
    rw [← hR₁eq, ← hR₂, hW z, h3, hW u]
  have hq0 : q = 0 := by
    have : ((R₁ : ℚ) : K) = ((2 * q : ℚ) : K) := by push_cast; exact hR
    have h' : (R₁ : ℚ) = 2 * q := by exact_mod_cast this
    have : (0 : ℚ) ≤ R₁ := by exact_mod_cast hR₁nonneg
    linarith
  have hBxb : B ((x : Dual K H ≃ₗ[K] Dual K H) a - a) b = 0 := by
    rw [hxq, hq0, Rat.cast_zero]
  -- minimize the height of `g⁻¹ x a - a ∈ Q₊` over the stabilizer of `b`
  have hmem : ∀ g : {g : P.weylGroup hF.isGeneralizedCartan //
      (g : Dual K H ≃ₗ[K] Dual K H) b = b},
      g.1⁻¹ * x ∈ P.integralWeylGroup hF.isGeneralizedCartan a :=
    fun g ↦ mul_mem (inv_mem (hstab g.1 g.2)) hx
  choose m hm hmeq using fun g ↦ exists_nonneg_apply_sub_eq_rootOf hF ha (hmem g)
  have : Nonempty {g : P.weylGroup hF.isGeneralizedCartan //
      (g : Dual K H ≃ₗ[K] Dual K H) b = b} := ⟨⟨1, rfl⟩⟩
  obtain ⟨g, hgmin⟩ := Finite.exists_min (fun g : {g : P.weylGroup hF.isGeneralizedCartan //
      (g : Dual K H ≃ₗ[K] Dual K H) b = b} ↦ ∑ i, m g i)
  obtain ⟨c', hc'⟩ : ∃ c', ((g.1⁻¹ * x : P.weylGroup hF.isGeneralizedCartan) :
      Dual K H ≃ₗ[K] Dual K H) a = c' := ⟨_, rfl⟩
  have hmg : c' - a = P.rootOf (m g) := hc' ▸ hmeq g
  -- `c'` is antidominant on the positive roots orthogonal to `b`
  have hga : ∀ v i, P.IsPosRoot hF.isGeneralizedCartan v i →
      P.corootPairing hF.isGeneralizedCartan b v i = 0 →
        ∃ n : ℤ, n ≤ 0 ∧ P.corootPairing hF.isGeneralizedCartan c' v i = n := by
    intro v i hv hb0
    obtain ⟨na, hna⟩ := (P.isIntegralRoot_congr _ hab v i).mpr ⟨0, by rw [Int.cast_zero]; exact hb0⟩
    change P.corootPairing _ a v i = na at hna
    obtain ⟨nd, hnd⟩ := exists_int_corootPairing_of_mem_rootLattice
      (hA := hF.isGeneralizedCartan) (P.rootOf_mem_rootLattice (m g)) v i
    have hc'pair : P.corootPairing hF.isGeneralizedCartan c' v i = ((na + nd : ℤ) : K) := by
      rw [show c' = a + P.rootOf (m g) by rw [← hmg]; abel, corootPairing_add, hna, hnd]
      push_cast
      rfl
    refine ⟨na + nd, ?_, hc'pair⟩
    by_contra hposn
    push Not at hposn
    set s := P.reflectionOf hF.isGeneralizedCartan v i with hs
    have hsb : (s : Dual K H ≃ₗ[K] Dual K H) b = b := by
      rw [hs, reflectionOf_apply', hb0, zero_smul, sub_zero]
    have hgs : ((g.1 * s : P.weylGroup hF.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H) b =
        b := by
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hsb, g.2]
    obtain ⟨l, hl, hvl⟩ := hv
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [map_zero, LinearEquiv.map_eq_zero_iff] at hvl
      exact P.linearIndependent_root.ne_zero i hvl
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left (reflectionOf_mul_self v i)
    have hcs : (((g.1 * s)⁻¹ * x : P.weylGroup hF.isGeneralizedCartan) :
        Dual K H ≃ₗ[K] Dual K H) a = (s : Dual K H ≃ₗ[K] Dual K H) c' := by
      rw [_root_.mul_inv_rev, hsinv, mul_assoc, ← hc']
      rfl
    have h1 := hmeq ⟨g.1 * s, hgs⟩
    dsimp only at h1
    rw [hcs] at h1
    have hnew : P.rootOf (m ⟨g.1 * s, hgs⟩) = P.rootOf (m g - (na + nd) • l) := by
      rw [← h1, hs, reflectionOf_apply', hc'pair, map_sub, map_zsmul, ← hmg, ← hvl,
        ← Int.cast_smul_eq_zsmul K]
      abel
    have hmnew := P.rootOf_injective hnew
    have hsum : ∑ j, m ⟨g.1 * s, hgs⟩ j = ∑ j, m g j - (na + nd) * ∑ j, l j := by
      rw [hmnew]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        Finset.mul_sum]
    have hlpos : 0 < ∑ j, l j := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hl0
      exact lt_of_lt_of_le (lt_of_le_of_ne (hl j) (Ne.symm hj))
        (Finset.single_le_sum (fun k _ ↦ hl k) (Finset.mem_univ j))
    have hlt := hgmin ⟨g.1 * s, hgs⟩
    have := mul_pos hposn hlpos
    linarith
  -- `c' - a` lies in the cone of the positive roots orthogonal to `b`
  have hd : c' - a ∈ P.orthPosRootCone hF.isGeneralizedCartan b := by
    obtain ⟨q', -, hq', hq'0⟩ := exists_bilinForm_eq_of_mem_integralPosRootCone hF S hab hb
      (hc' ▸ apply_sub_mem_integralPosRootCone hF ha (hmem g))
    refine hq'0 ?_
    have e1 : B c' b = B ((x : Dual K H ≃ₗ[K] Dual K H) a) b := by
      rw [← hW g.1 c' b, g.2, ← hc', Subgroup.coe_mul, LinearEquiv.mul_apply, apply_inv_apply]
    have e2 : B (c' - a) b = 0 := by
      rw [map_sub, LinearMap.sub_apply, e1, ← LinearMap.sub_apply, ← map_sub, hBxb]
    have : ((q' : ℚ) : K) = 0 := hq'.symm.trans e2
    exact_mod_cast this
  -- the norm argument on that cone: `c' = a`
  have hG1 : ∀ v i, (P.IsPosRoot hF.isGeneralizedCartan v i ∧
      P.corootPairing hF.isGeneralizedCartan b v i = 0) → ∃ n : ℤ, n ≤ 0 ∧
        P.corootPairing hF.isGeneralizedCartan a v i = n ∧
          (n = 0 → P.corootPairing hF.isGeneralizedCartan a v i = 0) := fun v i ⟨hv, hb0⟩ ↦ by
    obtain ⟨n, hn⟩ := (P.isIntegralRoot_congr _ hab v i).mpr ⟨0, by rw [Int.cast_zero]; exact hb0⟩
    change P.corootPairing _ a v i = n at hn
    exact ⟨n, ha v i hv n hn, hn, fun h0 ↦ by rw [hn, h0, Int.cast_zero]⟩
  have hG2 : ∀ v i, (P.IsPosRoot hF.isGeneralizedCartan v i ∧
      P.corootPairing hF.isGeneralizedCartan b v i = 0) → ∃ n : ℤ, n ≤ 0 ∧
        P.corootPairing hF.isGeneralizedCartan c' v i = n ∧
          (n = 0 → P.corootPairing hF.isGeneralizedCartan c' v i = 0) := fun v i ⟨hv, hb0⟩ ↦ by
    obtain ⟨n, hn, hn'⟩ := hga v i hv hb0
    exact ⟨n, hn, hn', fun h0 ↦ by rw [hn', h0, Int.cast_zero]⟩
  obtain ⟨q₁, hq₁, h₁, -⟩ := bilinForm_mem_closure_nonpos S hG1 hd
  obtain ⟨q₂, hq₂, h₂, -⟩ := bilinForm_mem_closure_nonpos S hG2 hd
  have hWc : B c' c' = B a a := by rw [← hc']; exact hW _ a a
  have hsum : ((q₁ + q₂ : ℚ) : K) = 0 := by
    push_cast
    rw [← h₁, ← h₂]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hBsymm a c']
    linear_combination hWc
  have hq : q₁ + q₂ = 0 := by exact_mod_cast hsum
  have hq₁0 : q₁ = 0 := by linarith
  have hq₂0 : q₂ = 0 := by linarith
  have hxx : B (c' - a) (c' - a) = 0 := by
    rw [map_sub (B (c' - a)), h₁, h₂, hq₁0, hq₂0]
    simp
  have hk0 : m g = 0 := by
    by_contra hne
    have hqd := hpos.dotProduct_mulVec_pos hne
    rw [hmg, hB] at hxx
    have hcast : ((m g ⬝ᵥ (diagonal d * A) *ᵥ m g : ℤ) : K) = 0 := by
      rw [← hxx, ← mulVec_mulVec, dotProduct]
      simp only [mulVec_diagonal]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [rootOf_apply_coroot]
      ring
    simp only [star_trivial] at hqd
    exact hqd.ne' (by exact_mod_cast hcast)
  have hca : c' = a := by
    rw [← sub_eq_zero, hmg, hk0, map_zero]
  refine ⟨g.1, g.2, ?_⟩
  calc (g.1 : Dual K H ≃ₗ[K] Dual K H) a = (g.1 : Dual K H ≃ₗ[K] Dual K H) c' := by rw [hca]
    _ = _ := by rw [← hc', Subgroup.coe_mul, LinearEquiv.mul_apply, apply_inv_apply]

end RootDatum

namespace KacMoodyAlgebra

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H} (hA : A.IsFiniteCartan)

namespace IrreducibleModule

include hA

/-- **The surviving weights, arbitrary weights** (finite type; cf. Humphreys, GSM 94, 7.12).
Let `λ`, `μ` be antidominant and `ν = z (λ - μ)`, `z ∈ W`, dominant integral. If `ν'` is a weight
of `L(ν)` and `w·μ + ν' = y·λ` for `w, y ∈ W`, then `y·λ = (w w')·λ` for some `w' ∈ W` fixing `μ`
(for the dot action). -/
theorem exists_weylDot_eq_of_add_eq_weylDot_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    {ν' : Dual K H} (hν' : weightSpace P (IrreducibleModule P ν) ν' ≠ ⊥)
    {w y : P.weylGroup hA.isGeneralizedCartan}
    (h : P.weylDot hA.isGeneralizedCartan w μ + ν' = P.weylDot hA.isGeneralizedCartan y lam) :
    ∃ w' : P.weylGroup hA.isGeneralizedCartan, P.weylDot hA.isGeneralizedCartan w' μ = μ ∧
      P.weylDot hA.isGeneralizedCartan y lam = P.weylDot hA.isGeneralizedCartan (w * w') lam := by
  classical
  have hA' := hA.isGeneralizedCartan
  have := P.finite_weylGroup hA
  have hνint : ∀ i, ∃ n : ℤ, ν (P.coroot i) = n := fun i ↦ by
    obtain ⟨n, hn⟩ := hν i; exact ⟨n, by rw [hn, Int.cast_natCast]⟩
  -- `λ - μ = z⁻¹ ν` is integral
  have hab : ∀ j, ∃ n : ℤ, ((lam + P.rho) - (μ + P.rho)) (P.coroot j) = n := by
    intro j
    obtain ⟨k, hk⟩ := P.exists_apply_eq_add_rootOf hA' (inv_mem hz) hνint
    obtain ⟨n, hn⟩ := hνint j
    have e : (lam + P.rho) - (μ + P.rho) = z⁻¹ ν := by
      rw [add_sub_add_right_eq_sub, ← hzν]
      exact (z.symm_apply_apply _).symm
    refine ⟨n + (A *ᵥ k) j, ?_⟩
    rw [e, hk, LinearMap.add_apply, hn, rootOf_apply_coroot]
    push_cast
    ring
  set ν₁ := (w⁻¹ : P.weylGroup hA').val ν' with hν₁def
  have hν₁ : weightSpace P (IrreducibleModule P ν) ν₁ ≠ ⊥ :=
    weightSpace_apply_ne_bot hA' hν (w⁻¹).property hν'
  have hν₁int : ∀ i, ∃ n : ℤ, ν₁ (P.coroot i) = n := by
    obtain ⟨k, -, hk⟩ := exists_eq_sub_of_weightSpace_ne_bot hν₁
    intro i
    obtain ⟨n, hn⟩ := hν i
    refine ⟨n - (A *ᵥ k) i, ?_⟩
    rw [hk, LinearMap.sub_apply, hn, rootOf_apply_coroot]
    push_cast
    ring
  obtain ⟨u', hu'⟩ := P.exists_dominantIntegral_weylGroup hA' hν₁int
  have hν₂ : weightSpace P (IrreducibleModule P ν) (u'.val ν₁) ≠ ⊥ :=
    weightSpace_apply_ne_bot hA' hν u'.property hν₁
  obtain ⟨c, hc, hck⟩ := exists_eq_sub_of_weightSpace_ne_bot hν₂
  have hνc : z ((lam + P.rho) - (μ + P.rho)) - u'.val ν₁ = P.rootOf c := by
    rw [add_sub_add_right_eq_sub, hzν, hck]
    abel
  have hu : (u'⁻¹ : P.weylGroup hA').val (u'.val ν₁) = ν₁ := by
    change u'.val.symm (u'.val ν₁) = ν₁
    exact u'.val.symm_apply_apply ν₁
  have hwy : y.val (lam + P.rho) = w.val (μ + P.rho) + ν' := by
    have h' := h
    simp only [weylDot] at h'
    rw [sub_add_eq_add_sub, sub_left_inj] at h'
    exact h'.symm
  have hx : (μ + P.rho) + (u'⁻¹ : P.weylGroup hA').val (u'.val ν₁) =
      (w⁻¹ * y : P.weylGroup hA').val (lam + P.rho) := by
    rw [hu, hν₁def]
    change μ + P.rho + w.val.symm ν' = w.val.symm (y.val (lam + P.rho))
    rw [hwy, map_add, LinearEquiv.symm_apply_apply]
  obtain ⟨g, hgb, hga⟩ := exists_apply_eq_of_add_eq_apply_of_antidominant hA hab hlam hμ
    (z := ⟨z, hz⟩) (u := u'⁻¹) (x := w⁻¹ * y)
    (by rw [add_sub_add_right_eq_sub, hzν]; exact hν) hu' hc hνc hx
  refine ⟨g, ?_, ?_⟩
  · simp only [weylDot, hgb, add_sub_cancel_right]
  · simp only [weylDot]
    congr 1
    change y.val (lam + P.rho) = w.val (g.val (lam + P.rho))
    rw [hga]
    change y.val (lam + P.rho) = w.val (w.val.symm (y.val (lam + P.rho)))
    rw [LinearEquiv.apply_symm_apply]

end IrreducibleModule

open VermaModule TensorProduct

local notation "𝔤" => KacMoodyAlgebra P

variable [IsAlgClosed K]

include hA in
/-- **Translation out of a facet closure, arbitrary weights** (finite type; Humphreys, GSM 94,
Theorem 7.12, in the form of standard filtrations). Let `λ`, `μ` be antidominant and
`ν = z (λ - μ)`, `z ∈ W`, dominant integral. For `w ∈ W`, the `χ_λ`-block of `M(w·μ) ⊗ L(ν)`
(that is, `T_μ^λ M(w·μ)`) has a filtration `0 = F₀ ≤ ⋯ ≤ Fₙ` whose successive quotients are `0`
or Verma modules, and the Verma modules occurring are the `M((w w')·λ)`, `w'` running over the
stabilizer `W_μ°` of `μ` modulo that of `λ`, each exactly once. Humphreys assumes `w ∈ W_[λ]` and
that `μ♮` lies in the closure of the facet of `λ♮`; neither is needed. -/
theorem exists_translation_verma_filtration_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    ∃ (n : ℕ) (F : Fin (n + 1) → LieSubmodule K 𝔤
        (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ) ⊗[K] IrreducibleModule P ν))
      (x : Fin n → Dual K H) (S : Set (Fin n)),
      Monotone F ∧ F 0 = ⊥ ∧
      F (Fin.last n) = centralBlock P (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ) ⊗[K]
        IrreducibleModule P ν) (centralCharacter P lam) ∧
      (∀ j ∈ S, Nonempty (VermaModule P (x j) ≃ₗ⁅K,𝔤⁆
        (F j.succ).map (LieSubmodule.Quotient.mk' (F j.castSucc)))) ∧
      (∀ j ∉ S, (F j.succ).map (LieSubmodule.Quotient.mk' (F j.castSucc)) = ⊥) ∧
      Set.BijOn x S {y | ∃ w' : P.weylGroup hA.isGeneralizedCartan,
        P.weylDot hA.isGeneralizedCartan w' μ = μ ∧
          y = P.weylDot hA.isGeneralizedCartan (w * w') lam} :=
  exists_translation_verma_filtration_of_forall hA hν hz hzν w fun _ hν' _ h ↦
    IrreducibleModule.exists_weylDot_eq_of_add_eq_weylDot_of_isAntidominant hA hlam hμ hν hz hzν
      hν' h

include hA in
/-- **Translation out of a facet closure on characters, arbitrary weights** (finite type;
Humphreys, GSM 94, Theorem 7.12 (1)). Under the hypotheses of
`exists_translation_verma_filtration_of_isAntidominant`, `ch T_μ^λ M(w·μ) = Σ_y ch M(y)`, `y`
running over the weights `(w w')·λ` with `w'·μ = μ`, each counted once (i.e. over
`w' ∈ W_μ°/W_λ°`). -/
theorem character_translation_verma_of_isAntidominant {lam μ ν : Dual K H}
    (hlam : P.IsAntidominant hA.isGeneralizedCartan lam)
    (hμ : P.IsAntidominant hA.isGeneralizedCartan μ)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    ∃ T : Finset (Dual K H), (T : Set (Dual K H)) = {y | ∃ w' : P.weylGroup hA.isGeneralizedCartan,
        P.weylDot hA.isGeneralizedCartan w' μ = μ ∧
          y = P.weylDot hA.isGeneralizedCartan (w * w') lam} ∧
      (((VermaModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan w μ)).tensorProduct
          (IrreducibleModule.isCategoryO P ν)).lieSubmodule
          (centralBlock P _ (centralCharacter P lam))).character =
        ∑ y ∈ T, (VermaModule.isCategoryO P y).character :=
  character_translation_verma_of_forall hA hν hz hzν w fun _ hν' _ h ↦
    IrreducibleModule.exists_weylDot_eq_of_add_eq_weylDot_of_isAntidominant hA hlam hμ hν hz hzν
      hν' h

end KacMoodyAlgebra

end Matrix.Realization
