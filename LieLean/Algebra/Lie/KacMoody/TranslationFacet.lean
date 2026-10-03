/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaHomFiniteType

/-!
# Facet exclusion for translation functors (integral weights, finite type)

Let `A` be of finite type, `λ, μ` integral weights with `λ + ρ`, `μ + ρ` antidominant, and `μ`
in the closure of the facet of `λ` (every simple wall containing `λ + ρ` contains `μ + ρ`). Let
`ν` be the dominant integral weight in `W (μ - λ)`. Then, for `w ∈ W`, the only weight of the
form `w·λ + ν'`, `ν'` a weight of `L(ν)`, lying in the dot orbit `W·μ` is `w·μ`, which does
occur (`ν' = w (μ - λ)`). This is the combinatorial input to the translation of Verma modules
`T_λ^μ M(w·λ) ≅ M(w·μ)`.

## Main definitions

* `Matrix.Symmetrization.ofDiagonal`: the symmetrization `εᵢ = 1 / dᵢ` of a matrix with
  `diag(d) A` symmetric.

## Main results

* `Matrix.Realization.apply_eq_of_add_eq_apply`: the root-datum form of facet exclusion,
  for a weight `ν₁` conjugate to a dominant integral weight below `ν`.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.weylDot_add_eq_weylDot`: if
  `w·λ + ν' = x·μ` with `ν'` a weight of `L(ν)`, then `w·λ + ν' = w·μ`.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.weightSpace_weylDot_sub_ne_bot`:
  `w·μ - w·λ` is a weight of `L(ν)`.

## Proof

Write `a = λ + ρ`, `b = μ + ρ`, and suppose `a + ν₁ = y b` with `ν₁` a weight of `L(ν)`. Use
the `W`-invariant form attached to a positive definite symmetrization `diag(d) A`. Since `ν₁`
is conjugate to a dominant `ν₂ ≤ ν`, `|ν|² - |ν₁|² = (ν - ν₂ | ν + ν₂) ≥ 0`; also
`|ν|² = |b - a|²`, and `|b - a|² - |y b - a|² = 2 (y b - b | a) ≤ 0` because `y b - b ∈ Q₊`
(`b` antidominant) and `a` is antidominant. So `(y b - b | a) = 0`; the simple roots in the
support of `y b - b` are orthogonal to `a`, hence (facet hypothesis) to `b`, so
`|y b|² = |b|² + |y b - b|²` forces `y b = b` by positive definiteness. This norm argument is
our own, with all comparisons made in `ℤ`, so that no order on the field `K` is needed;
Humphreys, GSM 94, Lemma 7.5 states the result and proves it by induction on chamber distance.

## References

* Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  Lemma 7.5 and Theorem 7.6. Humphreys treats arbitrary `λ` with `W_[λ]`; here all weights
  are integral, so `W_[λ] = W`.
-/

noncomputable section

open Module

namespace Matrix.Symmetrization

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ}

/-- The symmetrization `εᵢ = 1 / dᵢ` attached to positive integers `dᵢ` with `diag(d) A`
symmetric; its symmetric matrix is `diag(d) A`. -/
def ofDiagonal (d : ι → ℤ) (hd : ∀ i, 0 < d i) (hsymm : (diagonal d * A).IsSymm) :
    A.Symmetrization where
  ε i := 1 / d i
  ε_pos i := by have := hd i; positivity
  ε_mul_comm i j := by
    have h := congrFun (congrFun hsymm i) j
    simp only [transpose_apply, diagonal_mul] at h
    have hi : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
    have hj : (d j : ℚ) ≠ 0 := by exact_mod_cast (hd j).ne'
    have h' : (d j * A j i : ℚ) = d i * A i j := by exact_mod_cast h
    field_simp
    linarith

end Matrix.Symmetrization

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- For the symmetrization `εᵢ = 1 / dᵢ`, `(∑ kᵢ αᵢ | x) = ∑ kᵢ dᵢ ⟨x, αᵢ^∨⟩`. -/
theorem dualBilinForm_ofDiagonal_rootOf (d : ι → ℤ) (hd : ∀ i, 0 < d i)
    (hsymm : (diagonal d * A).IsSymm) (k : ι → ℤ) (x : Dual K H) :
    P.dualBilinForm (Symmetrization.ofDiagonal d hd hsymm) (P.rootOf k) x =
      ∑ i, ((k i * d i : ℤ) : K) * x (P.coroot i) := by
  rw [P.rootOf_apply, map_sum (P.dualBilinForm (Symmetrization.ofDiagonal d hd hsymm)),
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, (P.isSymm_dualBilinForm _).eq, dualBilinForm_root_right,
    smul_eq_mul]
  simp only [Symmetrization.ofDiagonal]
  push_cast
  have hi : (d i : K) ≠ 0 := by exact_mod_cast (hd i).ne'
  field_simp

/-- **Facet exclusion, root-datum form.** Let `A` be of finite type, `a`, `b` antidominant
integral weights with every simple wall of `a` a wall of `b`, `ν = z (b - a)` for some `z ∈ W`,
and `ν₁ = u ν₂` with `u ∈ W` and `ν₂` dominant integral, `ν - ν₂ ∈ Q₊`. If `a + ν₁ = y b` with
`y ∈ W`, then `y b = b`. Reconstructed norm argument; cf. Humphreys, GSM 94, Lemma 7.5. -/
theorem apply_eq_of_add_eq_apply (hA : A.IsFiniteCartan) {a b : Dual K H}
    (ha : ∀ i, ∃ n : ℕ, a (P.coroot i) = -n) (hb : ∀ i, ∃ n : ℕ, b (P.coroot i) = -n)
    (hfacet : ∀ i, a (P.coroot i) = 0 → b (P.coroot i) = 0)
    {z u y : Dual K H ≃ₗ[K] Dual K H} (hz : z ∈ P.weylGroup hA.isGeneralizedCartan)
    (hu : u ∈ P.weylGroup hA.isGeneralizedCartan) (hy : y ∈ P.weylGroup hA.isGeneralizedCartan)
    (hν : P.IsDominantIntegral (z (b - a)))
    {ν₂ : Dual K H} (hν₂ : P.IsDominantIntegral ν₂) {c : ι → ℤ} (hc : 0 ≤ c)
    (hνc : z (b - a) - ν₂ = P.rootOf c) (h : a + u ν₂ = y b) : y b = b := by
  classical
  have hA' := hA.isGeneralizedCartan
  obtain ⟨d, hdpos, hpos⟩ := hA.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hpos.isHermitian
  set S := Symmetrization.ofDiagonal d hdpos hsymm
  set B := P.dualBilinForm S
  have hB (k : ι → ℤ) (x : Dual K H) := P.dualBilinForm_ofDiagonal_rootOf d hdpos hsymm k x
  have hW {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA') (x x' : Dual K H) :
      B (w x) (w x') = B x x' := P.dualBilinForm_weylGroup hA' S hw x x'
  have hBsymm (x x' : Dual K H) : B x x' = B x' x := (P.isSymm_dualBilinForm S).eq x x'
  -- `y b - b ∈ Q₊`.
  obtain ⟨e, he, hye⟩ : ∃ e : ι → ℤ, 0 ≤ e ∧ y b - b = P.rootOf e := by
    obtain ⟨e, he, hee⟩ := P.exists_sub_apply_eq_rootOf hA' (μ := -b)
      (fun i => by obtain ⟨n, hn⟩ := hb i; exact ⟨n, by simp [hn]⟩) ⟨y, hy⟩
    refine ⟨e, he, ?_⟩
    rw [← hee, map_neg]
    abel
  choose na hna using ha
  choose nb hnb using hb
  choose n2 hn2 using hν₂
  choose nν hnν using hν
  -- `R₁ := |ν|² - |ν₂|² = (ν - ν₂ | ν + ν₂)`, an integer `≥ 0`.
  set R₁ : ℤ := ∑ i, c i * d i * ((nν i : ℤ) + n2 i) with hR₁
  have hR₁nonneg : 0 ≤ R₁ := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (hc i) (hdpos i).le) (by positivity)
  have hR₁eq : B (z (b - a)) (z (b - a)) - B ν₂ ν₂ = R₁ := by
    have hsplit : z (b - a) = ν₂ + P.rootOf c := by rw [← hνc]; abel
    calc B (z (b - a)) (z (b - a)) - B ν₂ ν₂ = B (P.rootOf c) (z (b - a) + ν₂) := by
          rw [hsplit]
          simp only [map_add, LinearMap.add_apply]
          rw [hBsymm ν₂ (P.rootOf c)]
          ring
      _ = R₁ := by
          rw [hB, hR₁]
          push_cast
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [LinearMap.add_apply, hnν, hn2]
  -- `R₂ := |b - a|² - |y b - a|² = 2 (y b - b | a)`, an integer `≤ 0`.
  set R₂ : ℤ := ∑ i, 2 * (e i * d i * (-(na i : ℤ))) with hR₂
  have hR₂nonpos : R₂ ≤ 0 := Finset.sum_nonpos fun i _ => by
    have := mul_nonneg (he i) (hdpos i).le
    have : (0 : ℤ) ≤ na i := by positivity
    nlinarith
  have hR₂eq : B (b - a) (b - a) - B (y b - a) (y b - a) = R₂ := by
    have h1 : B (y b) (y b) = B b b := hW hy _ _
    have hyb : y b = b + P.rootOf e := by rw [← hye]; abel
    have hBea : 2 * B (P.rootOf e) a = R₂ := by
      rw [hB, hR₂]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hna]
    rw [hyb] at h1 ⊢
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at h1 ⊢
    rw [hBsymm b a, hBsymm b (P.rootOf e), hBsymm a (P.rootOf e)] at *
    linear_combination (-1 : K) * h1 + hBea
  have hR : R₁ = R₂ := by
    have h1 : B (z (b - a)) (z (b - a)) = B (b - a) (b - a) := hW hz _ _
    have h2 : B (u ν₂) (u ν₂) = B ν₂ ν₂ := hW hu _ _
    have h3 : y b - a = u ν₂ := by rw [← h]; abel
    have : (R₁ : K) = R₂ := by rw [← hR₁eq, ← hR₂eq, h1, h3, h2]
    exact_mod_cast this
  have hR₂0 : R₂ = 0 := le_antisymm hR₂nonpos (hR ▸ hR₁nonneg)
  -- Each simple root in the support of `e` is orthogonal to `a`, hence to `b`.
  have hsupp (i : ι) : e i = 0 ∨ nb i = 0 := by
    have hterms := (Finset.sum_eq_zero_iff_of_nonpos fun j _ => by
      have := mul_nonneg (he j) (hdpos j).le
      have : (0 : ℤ) ≤ na j := by positivity
      nlinarith).mp hR₂0 i (Finset.mem_univ i)
    have hd : d i ≠ 0 := (hdpos i).ne'
    rcases mul_eq_zero.mp hterms with h2 | h2
    · norm_num at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact Or.inl h4
      · exact absurd h4 hd
    · right
      have h4 : na i = 0 := by omega
      have hna0 : a (P.coroot i) = 0 := by rw [hna i, h4]; simp
      have := hfacet i hna0
      rw [hnb i] at this
      exact_mod_cast neg_eq_zero.mp this
  have hBeb : B (P.rootOf e) b = 0 := by
    rw [hB]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases hsupp i with h0 | h0
    · simp [h0]
    · simp [hnb i, h0]
  -- Then `|y b - b|² = 0`, so `y b = b`.
  have hee : B (P.rootOf e) (P.rootOf e) = 0 := by
    have h1 : B (y b) (y b) = B b b := hW hy _ _
    have hyb : y b = b + P.rootOf e := by rw [← hye]; abel
    rw [hyb] at h1
    simp only [map_add, LinearMap.add_apply] at h1
    rw [hBsymm b (P.rootOf e), hBeb] at h1
    linear_combination h1
  have he0 : e = 0 := by
    by_contra hne
    have hq := hpos.dotProduct_mulVec_pos hne
    rw [hB] at hee
    have hcast : ((e ⬝ᵥ (diagonal d * A) *ᵥ e : ℤ) : K) = 0 := by
      rw [← hee, ← mulVec_mulVec, dotProduct]
      simp only [mulVec_diagonal]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [rootOf_apply_coroot]
      ring
    simp only [star_trivial] at hq
    exact hq.ne' (by exact_mod_cast hcast)
  rw [← sub_eq_zero, hye, he0, map_zero]

namespace KacMoodyAlgebra.IrreducibleModule

variable {P}

omit [FiniteDimensional K H] in
/-- The weights of `L(ν)`, `ν` dominant integral, are stable under the whole Weyl group. -/
theorem weightSpace_apply_ne_bot (hA : A.IsGeneralizedCartan) {ν : Dual K H}
    (hν : P.IsDominantIntegral ν) {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    {ν' : Dual K H} (hν' : weightSpace P (IrreducibleModule P ν) ν' ≠ ⊥) :
    weightSpace P (IrreducibleModule P ν) (w ν') ≠ ⊥ := by
  have hV := (isIntegrable_iff P hA).mpr hν
  have := rank_weightSpace_weylGroup hA hV hw ν'
  rw [Ne, ← Submodule.rank_eq_zero, this, Submodule.rank_eq_zero]
  exact hν'

omit [FiniteDimensional K H] in
/-- The highest weight `ν` is a weight of `L(ν)`. -/
theorem weightSpace_self_ne_bot (ν : Dual K H) :
    weightSpace P (IrreducibleModule P ν) ν ≠ ⊥ := by
  intro h
  have := finrank_weightSpace_self P ν
  rw [h, finrank_bot] at this
  exact zero_ne_one this

variable (hA : A.IsFiniteCartan)
include hA

/-- **Facet exclusion** (integral weights, finite type; Humphreys, GSM 94, Lemma 7.5).
Let `λ + ρ` and `μ + ρ` be antidominant integral, with every simple wall of `λ + ρ` a wall of
`μ + ρ` (`μ` lies in the closure of the facet of `λ`), and let `ν = z (μ - λ)`, `z ∈ W`, be
dominant. If `ν'` is a weight of `L(ν)` and `w·λ + ν' = x·μ` for `w, x ∈ W`, then
`w·λ + ν' = w·μ`. Antidominance and
the facet condition are stated on simple coroots; for antidominant integral weights this is
equivalent to the conditions on all positive coroots used in the source. -/
theorem weylDot_add_eq_weylDot {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    {ν' : Dual K H} (hν' : weightSpace P (IrreducibleModule P ν) ν' ≠ ⊥)
    {w x : P.weylGroup hA.isGeneralizedCartan}
    (h : P.weylDot hA.isGeneralizedCartan w lam + ν' = P.weylDot hA.isGeneralizedCartan x μ) :
    P.weylDot hA.isGeneralizedCartan w lam + ν' = P.weylDot hA.isGeneralizedCartan w μ := by
  classical
  have hA' := hA.isGeneralizedCartan
  have := P.finite_weylGroup hA
  -- The weight `ν₁ = w⁻¹ ν'` and a dominant conjugate `ν₂ = u' ν₁`.
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
  have hνc : z ((μ + P.rho) - (lam + P.rho)) - u'.val ν₁ = P.rootOf c := by
    rw [add_sub_add_right_eq_sub, hzν, hck]
    abel
  have hu : (u'⁻¹ : P.weylGroup hA').val (u'.val ν₁) = ν₁ := by
    change u'.val.symm (u'.val ν₁) = ν₁
    exact u'.val.symm_apply_apply ν₁
  -- Transport `h` by `w⁻¹`.
  have hwx : x.val (μ + P.rho) = w.val (lam + P.rho) + ν' := by
    have h' := h
    simp only [weylDot] at h'
    rw [sub_add_eq_add_sub, sub_left_inj] at h'
    exact h'.symm
  have hy : (lam + P.rho) + (u'⁻¹ : P.weylGroup hA').val (u'.val ν₁) =
      (w⁻¹ * x : P.weylGroup hA').val (μ + P.rho) := by
    rw [hu, hν₁def]
    change lam + P.rho + w.val.symm ν' = w.val.symm (x.val (μ + P.rho))
    rw [hwx, map_add, LinearEquiv.symm_apply_apply]
  have hfix := P.apply_eq_of_add_eq_apply hA hlam hμ hfacet hz (u'⁻¹).property
    (w⁻¹ * x).property (by rw [add_sub_add_right_eq_sub, hzν]; exact hν) hu' hc hνc hy
  have hxw : x.val (μ + P.rho) = w.val (μ + P.rho) := by
    have := congrArg w.val hfix
    change w.val (w.val.symm (x.val (μ + P.rho))) = _ at this
    rwa [LinearEquiv.apply_symm_apply] at this
  rw [h]
  simp only [weylDot, hxw]

omit [FiniteDimensional K H] in
/-- The weight `w·μ - w·λ = w (μ - λ)` does occur in `L(ν)`, `ν = z (μ - λ)` dominant. -/
theorem weightSpace_weylDot_sub_ne_bot {lam μ ν : Dual K H}
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    weightSpace P (IrreducibleModule P ν)
      (P.weylDot hA.isGeneralizedCartan w μ - P.weylDot hA.isGeneralizedCartan w lam) ≠ ⊥ := by
  have hA' := hA.isGeneralizedCartan
  have he : P.weylDot hA' w μ - P.weylDot hA' w lam = (w.val * z.symm) ν := by
    rw [LinearEquiv.mul_apply, ← hzν, LinearEquiv.symm_apply_apply]
    simp only [weylDot, map_sub, map_add]
    abel
  rw [he]
  exact weightSpace_apply_ne_bot hA' hν (mul_mem w.property (inv_mem hz))
    (weightSpace_self_ne_bot ν)

end KacMoodyAlgebra.IrreducibleModule

end Matrix.Realization
