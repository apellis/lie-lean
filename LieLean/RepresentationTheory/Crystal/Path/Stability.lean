/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.LS
import LieLean.RepresentationTheory.Crystal.Path.Realization
import LieLean.LinearAlgebra.Matrix.Cartan.TitsCone
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroupDominant
import LieLean.GroupTheory.Coxeter.Parabolic
import LieLean.GroupTheory.Coxeter.Bruhat

/-!
# Littelmann's stability theorem for realizations

Let `A` be a generalized Cartan matrix with a realization over a conditionally complete ordered
field `K` (i.e. over `ℝ`), and `λ` a dominant integral weight. We verify the axioms of
`LittelmannPath.LSData` for the orbit `W λ`, with the Bruhat order of minimal coset
representatives (`Matrix.Realization.lsData`), and deduce Littelmann's theorem: the crystal
`B(λ)` (the connected component of `π_λ`) is the set of paths `f_{i₁} ⋯ f_{iₖ} π_λ`, it consists
of Lakshmibai–Seshadri paths, and hence (by `Matrix.Realization.exists_wt_eq_pathCrystal` and
`Matrix.Realization.finite_wt_pathCrystal`) its weights lie in `λ - Q₊` and have finite
multiplicities.

## The Bruhat-order input

For `x ∈ W λ` let `m_x` be a minimal-length `w ∈ W` with `w λ = x` (`Matrix.Realization.IsMinRep`).
A step `x → y` means `m_y ≤ m_x` in the Bruhat order, `ℓ(m_y) + 1 = ℓ(m_x)` and
`m_y = u rⱼ u⁻¹ m_x`, with coroot `u αⱼ^∨`. The axioms reduce to:

* `⟨w λ, αᵢ^∨⟩ ≥ 0` if `rᵢ w > w`, since `λ - (w⁻¹ rᵢ w) λ = ⟨w λ, αᵢ^∨⟩ w⁻¹ αᵢ ∈ Q₊`
  (`Matrix.Realization.apply_coroot_nonneg_of_not_isLeftDescent`); for minimal representatives,
  `rᵢ m < m ↔ ⟨m λ, αᵢ^∨⟩ < 0` (`Matrix.Realization.IsMinRep.isLeftDescent_iff`), and
  `ℓ(m_{rᵢ x}) = ℓ(m_x) ± 1` according to the sign.
* the lifting property of the Bruhat order (`CoxeterSystem.BruhatLE.lifting_left`) gives
  Deodhar's lemma: a step from `⟨·, αᵢ^∨⟩ < 0` to `> 0` is `x → rᵢ x`, and no step goes from
  `< 0` to `= 0`; for a step from `= 0` to `> 0` one also uses that the stabilizer of `λ` is the
  parabolic subgroup `W_J` ([Kac] Prop. 3.12 (a)) and length additivity for `W^J × W_J`, which
  make `m_x⁻¹ rᵢ m_x` a simple reflection.
* a reflection `u rⱼ u⁻¹ = rᵢ` has coroot `± αᵢ^∨` (`Matrix.Realization.eval_comp_eq_or_eq_neg`).

The arguments are our reconstruction of the standard facts on parabolic Bruhat orders
([BB] §2.5, Deodhar) in the form needed by Littelmann.

## Main definitions

* `Matrix.Realization.IsMinRep`: minimal representatives of `W / W_λ`.
* `Matrix.Realization.lsData`: the LS data of the orbit `W λ`.

## Main results

* `Matrix.Realization.component_straightLine_eq_fOrbit`: `B(λ) = {f_{i₁} ⋯ f_{iₖ} π_λ}`, and all
  paths in `B(λ)` are Lakshmibai–Seshadri paths.
* `Matrix.Realization.fOrbitStable`: Littelmann's stability theorem (the hypothesis
  `Matrix.Realization.FOrbitStable` of `LieLean.RepresentationTheory.Crystal.Path.Realization`).
* `Matrix.Realization.exists_wt_eq_sub_rootOf_pathCrystal`,
  `Matrix.Realization.finite_setOf_wt_pathCrystal`: the weights of `B(λ)` lie in `λ - Q₊` and have
  finite multiplicities.

## References

* [Lit94] P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*,
  Invent. Math. **116** (1994), 329–346.
* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
* [BB] A. Björner, F. Brenti, *Combinatorics of Coxeter groups*, GTM 231, Springer 2005.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990.
-/

open Module Set

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [ConditionallyCompleteLinearOrder K]
  [IsStrictOrderedRing K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)

/-! ### The orbit `Wλ` and minimal representatives -/

section Orbit

/-- `m ∈ W` has minimal length among the elements `w ∈ W` with `w λ = m λ` (i.e. `m` is the
minimal representative of the coset `m W_λ`). -/
def IsMinRep (Λ : Dual K H) (m : P.weylGroup hA) : Prop :=
  ∀ w : P.weylGroup hA, w.1 Λ = m.1 Λ → (P.coxeterSystem hA).length m ≤
    (P.coxeterSystem hA).length w

variable {P hA}

lemma exists_isMinRep (Λ : Dual K H) (w : P.weylGroup hA) :
    ∃ m, P.IsMinRep hA Λ m ∧ m.1 Λ = w.1 Λ := by
  classical
  have hex : ∃ n, ∃ v : P.weylGroup hA, v.1 Λ = w.1 Λ ∧ (P.coxeterSystem hA).length v = n :=
    ⟨_, w, rfl, rfl⟩
  obtain ⟨v, hv, hvn⟩ := Nat.find_spec hex
  refine ⟨v, fun u hu ↦ ?_, hv⟩
  rw [hvn]
  exact Nat.find_min' hex ⟨u, hu.trans hv, rfl⟩

lemma coe_simple_mul_apply (i : ι) (w : P.weylGroup hA) (μ : Dual K H) :
    ((P.coxeterSystem hA).simple i * w).1 μ = P.reflection hA i (w.1 μ) := by
  rw [Subgroup.coe_mul, coxeterSystem_simple, LinearEquiv.mul_apply]

omit [DecidableEq ι] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K] in
lemma exists_int_apply_coroot {Λ : Dual K H} (hΛ : ∀ j, ∃ z : ℤ, Λ (P.coroot j) = z)
    (w : P.weylGroup hA) (i : ι) : ∃ n : ℤ, w.1 Λ (P.coroot i) = n := by
  obtain ⟨k, hk⟩ := P.exists_apply_eq_add_rootOf hA w.2 hΛ
  obtain ⟨z, hz⟩ := hΛ i
  exact ⟨z + (A *ᵥ k) i, by rw [hk, LinearMap.add_apply, hz, rootOf_apply_coroot]; push_cast; rfl⟩

variable {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
include hΛ

omit [DecidableEq ι] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K] in
lemma IsDominantIntegral.exists_int (j : ι) : ∃ z : ℤ, Λ (P.coroot j) = z := by
  obtain ⟨n, hn⟩ := hΛ j
  exact ⟨n, by rw [hn]; norm_cast⟩

/-- If `sᵢ` is not a left descent of `w`, then `⟨w λ, αᵢ^∨⟩ ≥ 0` (for `λ` dominant integral):
`λ - (w⁻¹ rᵢ w) λ = ⟨w λ, αᵢ^∨⟩ w⁻¹ αᵢ` lies in `Q₊`, and `w⁻¹ αᵢ > 0`. -/
theorem apply_coroot_nonneg_of_not_isLeftDescent {w : P.weylGroup hA} {i : ι}
    (hw : ¬(P.coxeterSystem hA).IsLeftDescent w i) : 0 ≤ w.1 Λ (P.coroot i) := by
  classical
  set cs := P.coxeterSystem hA
  have h1 : ¬cs.IsRightDescent w⁻¹ i := by rwa [cs.isRightDescent_inv_iff]
  obtain ⟨k, hk, hwk⟩ := (P.not_isRightDescent_coxeterSystem_iff hA).mp h1
  obtain ⟨n, hn⟩ := exists_int_apply_coroot hΛ.exists_int w i
  obtain ⟨k', hk', hk'e⟩ := P.exists_sub_apply_eq_rootOf hA hΛ (w⁻¹ * cs.simple i * w)
  have hcalc : Λ - (w⁻¹ * cs.simple i * w).1 Λ = (n : K) • (w⁻¹).1 (P.root i) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coxeterSystem_simple, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, reflection_apply, hn, map_sub, map_smul]
    have : (w⁻¹).1 (w.1 Λ) = Λ := by
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
      rfl
    rw [this]
    abel
  rw [hcalc, hwk] at hk'e
  have hkk : n • k = k' := P.rootOf_injective (by
    rw [map_zsmul, ← hk'e]; exact (Int.cast_smul_eq_zsmul K n _).symm)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero, LinearEquiv.map_eq_zero_iff] at hwk
    exact P.linearIndependent_root.ne_zero i hwk
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hk0
  have hkj : 0 < k j := lt_of_le_of_ne (hk j) (Ne.symm hj)
  have h2 := congr_fun hkk j
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  have h3 : 0 ≤ n * k j := by rw [h2]; exact hk' j
  have : 0 ≤ n := nonneg_of_mul_nonneg_left h3 hkj
  rw [hn]
  exact_mod_cast this

theorem apply_coroot_nonpos_of_isLeftDescent {w : P.weylGroup hA} {i : ι}
    (hw : (P.coxeterSystem hA).IsLeftDescent w i) : w.1 Λ (P.coroot i) ≤ 0 := by
  have h := apply_coroot_nonneg_of_not_isLeftDescent hΛ (w := (P.coxeterSystem hA).simple i * w)
    (i := i) (by
      exact (P.coxeterSystem hA).isLeftDescent_iff_not_isLeftDescent_mul.mp hw)
  rw [coe_simple_mul_apply, reflection_apply] at h
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, P.root_coroot_self hA, smul_eq_mul] at h
  linarith

variable {m : P.weylGroup hA} {i : ι}

/-- For a minimal representative `m`, `sᵢ` is a left descent of `m` iff `⟨m λ, αᵢ^∨⟩ < 0`. -/
theorem IsMinRep.isLeftDescent_iff (hm : P.IsMinRep hA Λ m) :
    (P.coxeterSystem hA).IsLeftDescent m i ↔ m.1 Λ (P.coroot i) < 0 := by
  constructor
  · intro hd
    rcases (apply_coroot_nonpos_of_isLeftDescent hΛ hd).lt_or_eq with h | h
    · exact h
    · exfalso
      have heq : ((P.coxeterSystem hA).simple i * m).1 Λ = m.1 Λ := by
        rw [coe_simple_mul_apply, reflection_apply, h, zero_smul, sub_zero]
      exact absurd (hm _ heq) (not_le.mpr hd)
  · intro h
    by_contra hd
    exact absurd (apply_coroot_nonneg_of_not_isLeftDescent hΛ hd) (not_le.mpr h)

/-- If `⟨m λ, αᵢ^∨⟩ > 0` for a minimal representative `m`, then `sᵢ m` is the minimal
representative of `rᵢ (m λ)`, of length `ℓ(m) + 1`. -/
theorem IsMinRep.simple_mul_of_pos (hm : P.IsMinRep hA Λ m) (h : 0 < m.1 Λ (P.coroot i)) :
    P.IsMinRep hA Λ ((P.coxeterSystem hA).simple i * m) ∧
      (P.coxeterSystem hA).length ((P.coxeterSystem hA).simple i * m) =
        (P.coxeterSystem hA).length m + 1 := by
  have hnd : ¬(P.coxeterSystem hA).IsLeftDescent m i := fun hd ↦
    absurd ((hm.isLeftDescent_iff hΛ).mp hd) (not_lt.mpr h.le)
  have hl : (P.coxeterSystem hA).length ((P.coxeterSystem hA).simple i * m) =
      (P.coxeterSystem hA).length m + 1 :=
    (P.coxeterSystem hA).not_isLeftDescent_iff.mp hnd
  refine ⟨fun w hw ↦ ?_, hl⟩
  rw [coe_simple_mul_apply] at hw
  have hwd : (P.coxeterSystem hA).IsLeftDescent w i := by
    by_contra hwd
    have := apply_coroot_nonneg_of_not_isLeftDescent hΛ hwd
    rw [hw, reflection_apply_coroot_self] at this
    linarith
  have h1 := (P.coxeterSystem hA).isLeftDescent_iff.mp hwd
  have h2 := hm ((P.coxeterSystem hA).simple i * w)
    (by rw [coe_simple_mul_apply, hw, reflection_reflection])
  omega

/-- If `⟨m λ, αᵢ^∨⟩ < 0` for a minimal representative `m`, then `sᵢ m` is the minimal
representative of `rᵢ (m λ)`, of length `ℓ(m) - 1`. -/
theorem IsMinRep.simple_mul_of_neg (hm : P.IsMinRep hA Λ m) (h : m.1 Λ (P.coroot i) < 0) :
    P.IsMinRep hA Λ ((P.coxeterSystem hA).simple i * m) ∧
      (P.coxeterSystem hA).length ((P.coxeterSystem hA).simple i * m) + 1 =
        (P.coxeterSystem hA).length m := by
  have hl : (P.coxeterSystem hA).length ((P.coxeterSystem hA).simple i * m) + 1 =
      (P.coxeterSystem hA).length m :=
    (P.coxeterSystem hA).isLeftDescent_iff.mp ((hm.isLeftDescent_iff hΛ).mpr h)
  refine ⟨fun w hw ↦ ?_, hl⟩
  rw [coe_simple_mul_apply] at hw
  have h2 := hm ((P.coxeterSystem hA).simple i * w)
    (by rw [coe_simple_mul_apply, hw, reflection_reflection])
  rcases (P.coxeterSystem hA).length_simple_mul w i with h3 | h3 <;> omega

end Orbit

/-! ### Reflections determine their roots -/

section Roots

variable {P hA}

omit [DecidableEq ι] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K] in
/-- If `∑ kₗ αₗ = a αᵢ` then `a = kᵢ`. -/
lemma eq_of_rootOf_eq_smul_root {k : ι → ℤ} {a : K} {i : ι} (h : P.rootOf k = a • P.root i) :
    a = k i := by
  classical
  have := Fintype.linearIndependent_iff.mp P.linearIndependent_root
    (fun l ↦ (k l : K) - if l = i then a else 0) (by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      rw [← rootOf_apply, h, sub_self]) i
  simp only [↓reduceIte, sub_eq_zero] at this
  exact this.symm

/-- If `u rⱼ u⁻¹ = rᵢ` in `W`, then the coroot `u αⱼ^∨` of the reflection is `± αᵢ^∨`: the linear
form `λ ↦ ⟨u⁻¹ λ, αⱼ^∨⟩` is `± ⟨·, αᵢ^∨⟩`. -/
theorem eval_comp_eq_or_eq_neg {u : P.weylGroup hA} {i j : ι}
    (h : u * (P.coxeterSystem hA).simple j * u⁻¹ = (P.coxeterSystem hA).simple i) :
    Dual.eval K H (P.coroot j) ∘ₗ (u⁻¹).1.toLinearMap = Dual.eval K H (P.coroot i) ∨
      Dual.eval K H (P.coroot j) ∘ₗ (u⁻¹).1.toLinearMap = -Dual.eval K H (P.coroot i) := by
  classical
  set c := Dual.eval K H (P.coroot j) ∘ₗ (u⁻¹).1.toLinearMap
  set γ := u.1 (P.root j)
  have huu : ∀ μ, u.1 ((u⁻¹).1 μ) = μ := fun μ ↦ by
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]; rfl
  have huu' : ∀ μ, (u⁻¹).1 (u.1 μ) = μ := fun μ ↦ by
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]; rfl
  have key : ∀ μ, c μ • γ = μ (P.coroot i) • P.root i := fun μ ↦ by
    have := congrArg (fun w : P.weylGroup hA ↦ w.1 μ) h
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, coxeterSystem_simple, reflection_apply,
      map_sub, map_smul, huu] at this
    have h' : μ - c μ • γ = μ - μ (P.coroot i) • P.root i := this
    exact sub_right_injective h'
  have hri : P.root i ≠ 0 := P.linearIndependent_root.ne_zero i
  have hc0 : c (P.root i) ≠ 0 := fun h0 ↦ by
    have := key (P.root i)
    rw [h0, zero_smul, P.root_coroot_self hA] at this
    exact hri (by simpa using this.symm)
  set a := 2 / c (P.root i) with ha
  have hγ : γ = a • P.root i := by
    have := key (P.root i)
    rw [P.root_coroot_self hA] at this
    rw [ha, div_eq_mul_inv, mul_comm, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have ha0 : a ≠ 0 := div_ne_zero two_ne_zero hc0
  have hcμ : ∀ μ, c μ = a⁻¹ * μ (P.coroot i) := fun μ ↦ by
    have := key μ
    rw [hγ, smul_smul] at this
    have := smul_left_injective K hri this
    field_simp
    linarith [this]
  -- `a` and `a⁻¹` are integers
  obtain ⟨k₁, hk₁⟩ := P.exists_apply_rootOf_eq_rootOf hA u.2 (Pi.single j 1)
  rw [rootOf_single] at hk₁
  have ha1 : a = k₁ i := eq_of_rootOf_eq_smul_root (hk₁.symm.trans hγ)
  obtain ⟨k₂, hk₂⟩ := P.exists_apply_rootOf_eq_rootOf hA (u⁻¹).2 (Pi.single i 1)
  rw [rootOf_single] at hk₂
  have hui : (u⁻¹).1 (P.root i) = a⁻¹ • P.root j := by
    have := congrArg (u⁻¹).1 hγ
    rw [huu', map_smul] at this
    rw [this, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  have ha2 : a⁻¹ = k₂ j := eq_of_rootOf_eq_smul_root (hk₂.symm.trans hui)
  have hint : k₁ i * k₂ j = 1 := by
    have : (k₁ i : K) * k₂ j = 1 := by rw [← ha1, ← ha2, mul_inv_cancel₀ ha0]
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hint with h1 | h1
  · left
    ext μ
    rw [hcμ, ha1, h1]
    simp
  · right
    ext μ
    rw [hcμ, ha1, h1]
    simp

end Roots

/-! ### The Bruhat-order data of `W λ` -/

section Data

variable {P hA}

omit [DecidableEq ι] in
lemma coroot_cartanDatum_pos_iff {i : ι} {x : P.integralWeights} :
    0 < (P.cartanDatum hA).coroot i x ↔ 0 < (x : Dual K H) (P.coroot i) := by
  rw [← coroot_cartanDatum_cast P hA]
  exact Int.cast_pos.symm

omit [DecidableEq ι] in
lemma coroot_cartanDatum_neg_iff {i : ι} {x : P.integralWeights} :
    (P.cartanDatum hA).coroot i x < 0 ↔ (x : Dual K H) (P.coroot i) < 0 := by
  rw [← coroot_cartanDatum_cast P hA]
  exact Int.cast_lt_zero.symm

omit [DecidableEq ι] in
lemma coroot_cartanDatum_eq_zero_iff {i : ι} {x : P.integralWeights} :
    (P.cartanDatum hA).coroot i x = 0 ↔ (x : Dual K H) (P.coroot i) = 0 := by
  rw [← coroot_cartanDatum_cast P hA]
  exact Int.cast_eq_zero.symm

omit [DecidableEq ι] in
lemma pathSpace_reflection (i : ι) (μ : Dual K H) :
    (P.pathSpace hA).reflection i μ = P.reflection hA i μ := by
  rw [CartanDatum.PathSpace.reflection_apply, reflection_apply, pathSpace_coroot,
    CartanDatum.PathSpace.root, pathSpace_embed, coe_root_cartanDatum]

/-- Elements of `W` lying in the subgroup of `GL(𝔥*)` generated by the `rⱼ`, `j ∈ J`, lie in
the standard parabolic subgroup `W_J` of the Coxeter system. -/
lemma mem_parabolicSubgroup_of_mem_closure {J : Set ι} {w : P.weylGroup hA}
    (hw : w.1 ∈ Subgroup.closure (P.reflection hA '' J)) :
    w ∈ (P.coxeterSystem hA).parabolicSubgroup J := by
  have hmap : ((P.coxeterSystem hA).parabolicSubgroup J).map (P.weylGroup hA).subtype =
      Subgroup.closure (P.reflection hA '' J) := by
    rw [CoxeterSystem.parabolicSubgroup, MonoidHom.map_closure, ← Set.image_comp]
    congr 1
  rw [← hmap] at hw
  obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp hw
  rwa [show y = w from Subtype.ext hyw] at hy

variable {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
include hΛ

omit [DecidableEq ι] in
lemma IsDominantIntegral.mem_dominantChamber : Λ ∈ P.dominantChamber :=
  P.mem_dominantChamber.mpr fun i ↦ by obtain ⟨n, hn⟩ := hΛ i; rw [hn]; positivity

omit hΛ in
/-- A minimal representative has no right descent `sⱼ` with `⟨λ, αⱼ^∨⟩ = 0`. -/
lemma IsMinRep.mem_minCosetReps {m : P.weylGroup hA} (hm : P.IsMinRep hA Λ m) :
    m ∈ (P.coxeterSystem hA).minCosetReps {j | Λ (P.coroot j) = 0} := fun j hj hd ↦ by
  have := hm (m * (P.coxeterSystem hA).simple j) (by
    rw [Subgroup.coe_mul, coxeterSystem_simple, LinearEquiv.mul_apply, reflection_apply,
      show Λ (P.coroot j) = 0 from hj, zero_smul, sub_zero])
  exact absurd hd (not_lt.mpr this)

variable (P hA) in
/-- The Bruhat-order data (`LittelmannPath.LSData`) of the orbit `W λ` of a dominant integral
weight: `x → y` is a step if the minimal representatives `m, n ∈ W` of `x = m λ` and `y = n λ`
satisfy `n ≤ m` in the Bruhat order, `ℓ(n) + 1 = ℓ(m)` and `n = u rⱼ u⁻¹ m` for a reflection
`u rⱼ u⁻¹` with coroot `c = u αⱼ^∨` (the linear form `μ ↦ ⟨u⁻¹ μ, αⱼ^∨⟩`). The axioms are
Deodhar's lemma and the lifting property of the Bruhat order ([BB] Prop. 2.2.7, 2.5.1 (check)),
in the forms needed for Littelmann's argument. -/
noncomputable def lsData : LittelmannPath.LSData (P.pathSpace hA) where
  O := {x | ∃ w : P.weylGroup hA, (x : Dual K H) = w.1 Λ}
  Step x y c := ∃ m n : P.weylGroup hA, P.IsMinRep hA Λ m ∧ P.IsMinRep hA Λ n ∧
    (x : Dual K H) = m.1 Λ ∧ (y : Dual K H) = n.1 Λ ∧ (P.coxeterSystem hA).BruhatLE n m ∧
    (P.coxeterSystem hA).length n + 1 = (P.coxeterSystem hA).length m ∧
    ∃ (u : P.weylGroup hA) (j : ι), n = u * (P.coxeterSystem hA).simple j * u⁻¹ * m ∧
      c = Dual.eval K H (P.coroot j) ∘ₗ (u⁻¹).1.toLinearMap
  reflection_mem i x := by
    rintro ⟨w, hw⟩
    exact ⟨(P.coxeterSystem hA).simple i * w, by
      rw [coe_reflection_cartanDatum, hw, coe_simple_mul_apply]⟩
  step_mem x y c := by
    rintro ⟨m, n, -, -, hx, hy, -⟩
    exact ⟨⟨m, hx⟩, ⟨n, hy⟩⟩
  exists_int x y c := by
    rintro ⟨m, n, -, -, -, -, -, -, u, j, -, rfl⟩ μ
    exact exists_int_apply_coroot μ.2 u⁻¹ j
  step_reflection_pos i x y c := by
    rintro ⟨m, n, hm, hn, hx, hy, hnm, hl, u, j, hnu, rfl⟩ hxp hyp
    rw [coroot_cartanDatum_pos_iff, hx] at hxp
    rw [coroot_cartanDatum_pos_iff, hy] at hyp
    obtain ⟨hm', hlm⟩ := hm.simple_mul_of_pos hΛ hxp
    obtain ⟨hn', hln⟩ := hn.simple_mul_of_pos hΛ hyp
    have hmd : ¬(P.coxeterSystem hA).IsLeftDescent m i := fun h ↦
      absurd ((hm.isLeftDescent_iff hΛ).mp h) (not_lt.mpr hxp.le)
    have hnd : ¬(P.coxeterSystem hA).IsLeftDescent n i := fun h ↦
      absurd ((hn.isLeftDescent_iff hΛ).mp h) (not_lt.mpr hyp.le)
    have h1 : (P.coxeterSystem hA).IsLeftDescent ((P.coxeterSystem hA).simple i * n) i := by
      rwa [(P.coxeterSystem hA).isLeftDescent_iff_not_isLeftDescent_mul,
        CoxeterSystem.simple_mul_simple_cancel_left]
    have h2 : (P.coxeterSystem hA).IsLeftDescent ((P.coxeterSystem hA).simple i * m) i := by
      rwa [(P.coxeterSystem hA).isLeftDescent_iff_not_isLeftDescent_mul,
        CoxeterSystem.simple_mul_simple_cancel_left]
    refine ⟨_, _, hm', hn', by rw [coe_reflection_cartanDatum, hx, coe_simple_mul_apply],
      by rw [coe_reflection_cartanDatum, hy, coe_simple_mul_apply],
      ((P.coxeterSystem hA).simple_mul_bruhatLE_simple_mul_iff h1 h2).mp
        (by simpa [CoxeterSystem.simple_mul_simple_cancel_left] using hnm), by omega,
      (P.coxeterSystem hA).simple i * u, j, by rw [hnu]; group, ?_⟩
    ext μ
    simp [CoxeterSystem.inv_simple, coxeterSystem_simple, pathSpace_reflection]
  step_reflection_neg i x y c := by
    rintro ⟨m, n, hm, hn, hx, hy, hnm, hl, u, j, hnu, rfl⟩ hxn hyn
    rw [coroot_cartanDatum_neg_iff, hx] at hxn
    rw [coroot_cartanDatum_neg_iff, hy] at hyn
    obtain ⟨hm', hlm⟩ := hm.simple_mul_of_neg hΛ hxn
    obtain ⟨hn', hln⟩ := hn.simple_mul_of_neg hΛ hyn
    refine ⟨_, _, hm', hn', by rw [coe_reflection_cartanDatum, hx, coe_simple_mul_apply],
      by rw [coe_reflection_cartanDatum, hy, coe_simple_mul_apply],
      ((P.coxeterSystem hA).simple_mul_bruhatLE_simple_mul_iff
        ((hn.isLeftDescent_iff hΛ).mpr hyn) ((hm.isLeftDescent_iff hΛ).mpr hxn)).mpr hnm,
      by omega, (P.coxeterSystem hA).simple i * u, j, by rw [hnu]; group, ?_⟩
    ext μ
    simp [CoxeterSystem.inv_simple, coxeterSystem_simple, pathSpace_reflection]
  step_simple i x := by
    rintro ⟨w, hw⟩ hxp
    obtain ⟨m, hm, hmw⟩ := exists_isMinRep Λ w
    rw [coroot_cartanDatum_pos_iff, hw, ← hmw] at hxp
    obtain ⟨hm', hlm⟩ := hm.simple_mul_of_pos hΛ hxp
    have hmd : ¬(P.coxeterSystem hA).IsLeftDescent m i := fun h ↦
      absurd ((hm.isLeftDescent_iff hΛ).mp h) (not_lt.mpr hxp.le)
    refine ⟨_, m, hm', hm, by rw [coe_reflection_cartanDatum, hw, ← hmw, coe_simple_mul_apply],
      by rw [hw, hmw], (P.coxeterSystem hA).bruhatLE_simple_mul hmd, by omega, 1, i,
      by rw [one_mul, inv_one, mul_one, CoxeterSystem.simple_mul_simple_cancel_left], ?_⟩
    ext μ
    simp
  step_neg_pos i x y c := by
    rintro ⟨m, n, hm, hn, hx, hy, hnm, hl, u, j, hnu, rfl⟩ hxn hyp
    rw [coroot_cartanDatum_neg_iff, hx] at hxn
    rw [coroot_cartanDatum_pos_iff, hy] at hyp
    have hmd := (hm.isLeftDescent_iff hΛ).mpr hxn
    have hnd : ¬(P.coxeterSystem hA).IsLeftDescent n i := fun h ↦
      absurd ((hn.isLeftDescent_iff hΛ).mp h) (not_lt.mpr hyp.le)
    have hl' := (P.coxeterSystem hA).isLeftDescent_iff.mp hmd
    have hn_eq : n = (P.coxeterSystem hA).simple i * m :=
      (hnm.lifting_left hmd hnd).1.eq_of_length_le (by omega)
    refine ⟨Subtype.ext ?_, ?_⟩
    · rw [coe_reflection_cartanDatum, hy, hn_eq, coe_simple_mul_apply, hx]
    · have hu : u * (P.coxeterSystem hA).simple j * u⁻¹ = (P.coxeterSystem hA).simple i := by
        rw [hn_eq] at hnu
        exact (mul_right_cancel hnu).symm
      rcases eval_comp_eq_or_eq_neg hu with h | h
      · exact Or.inl h
      · exact Or.inr h
  coroot_nonpos_of_step i x y c := by
    rintro ⟨m, n, hm, hn, hx, hy, hnm, hl, u, j, hnu, rfl⟩ hx0
    by_contra hyp
    rw [not_le, coroot_cartanDatum_pos_iff, hy] at hyp
    rw [coroot_cartanDatum_eq_zero_iff, hx] at hx0
    have hmd : ¬(P.coxeterSystem hA).IsLeftDescent m i := fun h ↦
      absurd ((hm.isLeftDescent_iff hΛ).mp h) (by rw [hx0]; exact lt_irrefl 0)
    have hnd : ¬(P.coxeterSystem hA).IsLeftDescent n i := fun h ↦
      absurd ((hn.isLeftDescent_iff hΛ).mp h) (not_lt.mpr hyp.le)
    obtain ⟨hn', hln⟩ := hn.simple_mul_of_pos hΛ hyp
    set cs := P.coxeterSystem hA
    have hlm : cs.length (cs.simple i * m) = cs.length m + 1 := cs.not_isLeftDescent_iff.mp hmd
    have h1 : cs.IsLeftDescent (cs.simple i * n) i := by
      rwa [cs.isLeftDescent_iff_not_isLeftDescent_mul, CoxeterSystem.simple_mul_simple_cancel_left]
    have h2 : cs.IsLeftDescent (cs.simple i * m) i := by
      rwa [cs.isLeftDescent_iff_not_isLeftDescent_mul, CoxeterSystem.simple_mul_simple_cancel_left]
    have hb : cs.BruhatLE (cs.simple i * n) (cs.simple i * m) :=
      (cs.simple_mul_bruhatLE_simple_mul_iff h1 h2).mp
        (by simpa [CoxeterSystem.simple_mul_simple_cancel_left] using hnm)
    -- `t = m⁻¹ sᵢ m` fixes `λ`, so it lies in `W_J`, and it has length one
    set t := m⁻¹ * cs.simple i * m with ht
    have hfix : ∀ μ : Dual K H, μ (P.coroot i) = 0 → P.reflection hA i μ = μ := fun μ hμ ↦ by
      rw [reflection_apply, hμ, zero_smul, sub_zero]
    have hmm : ∀ μ, (m⁻¹).1 (m.1 μ) = μ := fun μ ↦ by
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]; rfl
    have htΛ : t.1 Λ = Λ := by
      rw [ht, Subgroup.coe_mul, Subgroup.coe_mul, coxeterSystem_simple, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply, hfix _ hx0, hmm]
    have htJ : t ∈ cs.parabolicSubgroup {j | Λ (P.coroot j) = 0} :=
      mem_parabolicSubgroup_of_mem_closure (P.mem_closure_reflection_of_apply_eq_self hA
        hΛ.mem_dominantChamber t.2 htΛ)
    have hmt : m * t = cs.simple i * m := by rw [ht]; group
    have hlt := cs.length_mul_of_mem_minCosetReps hm.mem_minCosetReps htJ
    rw [hmt, hlm] at hlt
    obtain ⟨k, hk⟩ := cs.length_eq_one_iff.mp (by omega : cs.length t = 1)
    rw [hk] at hmt htΛ
    have hsk : ∀ w : P.weylGroup hA, (w * cs.simple k).1 Λ = w.1 Λ := fun w ↦ by
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, htΛ]
    have hdesc : cs.IsRightDescent (m * cs.simple k) k := by
      rw [CoxeterSystem.IsRightDescent, CoxeterSystem.simple_mul_simple_cancel_right, hmt, hlm]
      omega
    have hndesc : ¬cs.IsRightDescent (cs.simple i * n) k := fun h ↦
      absurd (hn' _ (hsk _)) (not_le.mpr h)
    rw [← hmt] at hb
    have hb' := (hb.lifting hdesc hndesc).1
    rw [CoxeterSystem.simple_mul_simple_cancel_right] at hb'
    have hnm' : cs.simple i * n = m := hb'.eq_of_length_le (by omega)
    have hx0' : (cs.simple i * n).1 Λ (P.coroot i) = 0 := by rw [hnm']; exact hx0
    rw [coe_simple_mul_apply, reflection_apply_coroot_self, neg_eq_zero] at hx0'
    have hn_eq : n.1 Λ = m.1 Λ := by rw [← hnm', coe_simple_mul_apply, hfix _ hx0']
    have h3 : cs.length m ≤ cs.length n := hm n hn_eq
    omega
  coroot_ne_zero_of_step i x y c := by
    rintro ⟨m, n, hm, hn, hx, hy, hnm, hl, u, j, hnu, rfl⟩ hxn hy0
    rw [coroot_cartanDatum_neg_iff, hx] at hxn
    rw [coroot_cartanDatum_eq_zero_iff, hy] at hy0
    have hmd := (hm.isLeftDescent_iff hΛ).mpr hxn
    have hnd : ¬(P.coxeterSystem hA).IsLeftDescent n i := fun h ↦
      absurd ((hn.isLeftDescent_iff hΛ).mp h) (by rw [hy0]; exact lt_irrefl 0)
    have hl' := (P.coxeterSystem hA).isLeftDescent_iff.mp hmd
    have hn_eq : n = (P.coxeterSystem hA).simple i * m :=
      (hnm.lifting_left hmd hnd).1.eq_of_length_le (by omega)
    rw [hn_eq, coe_simple_mul_apply, reflection_apply_coroot_self] at hy0
    linarith

end Data

/-! ### Littelmann's theorem for `B(λ)` -/

section Main

variable {P hA}

omit [DecidableEq ι] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K] in
/-- A linear form on `𝔥*` taking the value `1` on every simple root (a "height" function). -/
lemma exists_linearMap_root_eq_one : ∃ g : Dual K H →ₗ[K] K, ∀ i, g (P.root i) = 1 := by
  classical
  have hli := P.linearIndependent_root
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((Finsupp.linearCombination K fun _ : ι ↦ (1 : K)) ∘ₗ hli.repr)
  refine ⟨g, fun i ↦ ?_⟩
  have h := congrArg (fun φ ↦ φ ⟨P.root i, Submodule.subset_span ⟨i, rfl⟩⟩) hg
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
  rw [h, hli.repr_eq_single i _ rfl, Finsupp.linearCombination_single, one_smul]

variable [TopologicalSpace K] [OrderTopology K] [FloorRing K] {Λ : Dual K H}
  (hΛ : P.IsDominantIntegral Λ)

/-- **Littelmann's theorem** ([Lit94] §4–5, [Lit95] §4–5 (check)): for a dominant integral
weight `λ`, the connected component `B(λ)` of `π_λ` in the crystal of paths is the set of paths
`f_{i₁} ⋯ f_{iₖ} π_λ`, and it consists of Lakshmibai–Seshadri paths of shape `λ`
(`Matrix.Realization.lsData`). -/
theorem component_straightLine_eq_fOrbit :
    (LittelmannPath.straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component =
      (LittelmannPath.straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).fOrbit ∧
    ∀ η ∈ (LittelmannPath.straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component,
      LittelmannPath.IsLS (P.lsData hA hΛ) η := by
  classical
  obtain ⟨g, hg⟩ := exists_linearMap_root_eq_one (P := P)
  have hone : ((1 : P.weylGroup hA).1) Λ = Λ := rfl
  refine LittelmannPath.component_straightLine_eq_fOrbit (P.lsData hA hΛ) ⟨1, hone.symm⟩
    (fun x ⟨w, hw⟩ hx ↦ Subtype.ext ?_) (fun y c ⟨m, n, hm, _, hx, _, _, hl, _⟩ ↦ ?_) g
    (fun i ↦ by simpa [CartanDatum.PathSpace.root] using hg i) (fun x ⟨w, hw⟩ ↦ ?_)
  · rw [hw]
    refine P.apply_eq_self_of_dominant hA hΛ w.2 fun i ↦
      ⟨((P.cartanDatum hA).coroot i x).toNat, ?_⟩
    rw [← hw, ← coroot_cartanDatum_cast P hA]
    exact_mod_cast (Int.toNat_of_nonneg (hx i)).symm
  · have := hm 1 (by rw [hone]; exact hx)
    simp only [CoxeterSystem.length_one] at this
    omega
  · obtain ⟨k, hk, hwk⟩ := P.exists_sub_apply_eq_rootOf hA hΛ w
    simp only [pathSpace_embed]
    rw [hw]
    have : g Λ - g (w.1 Λ) = ∑ i, (k i : K) := by
      rw [← map_sub, hwk, rootOf_apply, map_sum]
      simp [hg]
    have h0 : (0 : K) ≤ ∑ i, (k i : K) := Finset.sum_nonneg fun i _ ↦ by exact_mod_cast hk i
    linarith

omit [DecidableEq ι] in
/-- **Littelmann's stability theorem** ([Lit95] §5–7 (check), [Lit94]): the set of paths
`f_{i₁} ⋯ f_{iₖ} π_λ` is stable under all root operators `eⱼ`. -/
theorem fOrbitStable : FOrbitStable hA hΛ := by
  classical
  intro π' hπ' j π'' he
  have h := (component_straightLine_eq_fOrbit (hA := hA) hΛ).1
  rw [← h] at hπ' ⊢
  exact LittelmannPath.isStable_component _ |>.e_mem j π' π'' hπ' he

omit [DecidableEq ι] in
/-- The weights of `B(λ)` lie in `λ - Q₊` ([Lit95] (check)). -/
theorem exists_wt_eq_sub_rootOf_pathCrystal
    (b : (LittelmannPath.straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    ∃ k : ι → ℤ, 0 ≤ k ∧ ((P.pathCrystal hA hΛ).wt b : Dual K H) = Λ - P.rootOf k :=
  exists_wt_eq_pathCrystal hA hΛ (fOrbitStable (hA := hA) hΛ) b

omit [DecidableEq ι] in
/-- Every weight occurs only finitely often in `B(λ)`. -/
theorem finite_setOf_wt_pathCrystal (μ : P.integralWeights) :
    {π ∈ (LittelmannPath.straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component |
      π.wt = μ}.Finite :=
  finite_wt_pathCrystal hA hΛ (fOrbitStable (hA := hA) hΛ) μ

end Main

end Matrix.Realization
