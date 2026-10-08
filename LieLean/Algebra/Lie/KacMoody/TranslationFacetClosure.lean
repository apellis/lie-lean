/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationVerma

/-!
# Translation out of a facet closure (integral weights, finite type)

Let `A` be of finite type, `λ, μ` integral weights with `λ + ρ`, `μ + ρ` antidominant, and
`ν` the dominant weight in `W (λ - μ)`. The translation functor `T_μ^λ = pr_{χ_λ}(- ⊗ L(ν))`
applied to `M(w·μ)` has a standard filtration by the Verma modules `M(w·μ + ν')`, `ν'` running over
the weights of `L(ν)` with `w·μ + ν' ∈ W·λ`. We determine these weights: they are exactly the
`w w' (λ - μ) = (w w')·λ - w·μ` with `w'` in the stabilizer `W_μ°` of `μ` for the dot action, and
they are extremal, of multiplicity one. This gives Humphreys' Theorem 7.12.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.exists_weylDot_eq_of_add_eq_weylDot`: if
  `w·μ + ν' = y·λ` for a weight `ν'` of `L(ν)`, then `y·λ = (w w')·λ` with `w'·μ = μ`.
* `Matrix.Realization.KacMoodyAlgebra.exists_translation_verma_filtration`: `T_μ^λ M(w·μ)` has a
  filtration whose nonzero steps are the Verma modules `M((w w')·λ)`, `w' ∈ W_μ°/W_λ°`, each
  exactly once.
* `Matrix.Realization.KacMoodyAlgebra.character_translation_verma`:
  `ch T_μ^λ M(w·μ) = Σ_{w' ∈ W_μ°/W_λ°} ch M((w w')·λ)` (Humphreys, Theorem 7.12).
* `Matrix.Realization.KacMoodyAlgebra.finrank_inf_weightSpaceOfMap_eq_sum`: weight
  multiplicities are additive along finite filtrations of modules in `𝒪`.

Humphreys assumes a facet-closure condition relating `μ` to `λ` and argues by adjunction; the
statements here do not need that condition. Our proof determines the weights
of the filtration directly, the approach Humphreys attributes to Jantzen.

## Proof

Write `a = λ + ρ`, `b = μ + ρ`, and suppose `b + ν₁ = x a` with `ν₁` conjugate to a dominant
`ν₂ ≤ ν`. With the `W`-invariant form `( | )` of a positive definite symmetrization,
`|x a - b|² - |a - b|² = -2 (x a - a | b) ≥ 0` (`x a - a ∈ Q₊` as `a` is antidominant, and `b` is
antidominant), while `|x a - b|² = |ν₂|² ≤ |ν|² = |a - b|²`. So `(x a - a | b) = 0`. Among the
`g ∈ W` fixing `b`, choose one for which `c = g⁻¹ x a` has `c - a ∈ Q₊` of minimal height; then
`(c - a | b) = 0`, so `c - a` is supported on the simple walls of `b`, and minimality makes `c`
antidominant on these walls, hence antidominant. So `c = a` and `x a = g a`. The argument is our
own, with all comparisons in `ℤ`.

## References

* Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94, §7.12.
* J. C. Jantzen, *Moduln mit einem höchsten Gewicht*, LNM 750.
-/

noncomputable section

open Module

namespace Matrix.Realization

section RootDatum

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- **The surviving weights, root-datum form.** Let `A` be of finite type, `a`, `b` antidominant
integral weights, `ν = z (a - b)` dominant (`z ∈ W`), and `ν₁ = u ν₂` with `u ∈ W` and `ν₂`
dominant integral, `ν - ν₂ ∈ Q₊`. If `b + ν₁ = x a` with `x ∈ W`, then `x a = g a` for some
`g ∈ W` with `g b = b`. -/
theorem exists_apply_eq_of_add_eq_apply (hA : A.IsFiniteCartan) {a b : Dual K H}
    (ha : ∀ i, ∃ n : ℕ, a (P.coroot i) = -n) (hb : ∀ i, ∃ n : ℕ, b (P.coroot i) = -n)
    {z u x : Dual K H ≃ₗ[K] Dual K H} (hz : z ∈ P.weylGroup hA.isGeneralizedCartan)
    (hu : u ∈ P.weylGroup hA.isGeneralizedCartan) (hx : x ∈ P.weylGroup hA.isGeneralizedCartan)
    (hν : P.IsDominantIntegral (z (a - b)))
    {ν₂ : Dual K H} (hν₂ : P.IsDominantIntegral ν₂) {c : ι → ℤ} (hc : 0 ≤ c)
    (hνc : z (a - b) - ν₂ = P.rootOf c) (h : b + u ν₂ = x a) :
    ∃ g ∈ P.weylGroup hA.isGeneralizedCartan, g b = b ∧ g a = x a := by
  classical
  have hA' := hA.isGeneralizedCartan
  have := P.finite_weylGroup hA
  obtain ⟨d, hdpos, hpos⟩ := hA.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hpos.isHermitian
  set S := Symmetrization.ofDiagonal d hdpos hsymm
  set B := P.dualBilinForm S
  have hB (k : ι → ℤ) (y : Dual K H) := P.dualBilinForm_ofDiagonal_rootOf d hdpos hsymm k y
  have hW {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA') (y y' : Dual K H) :
      B (w y) (w y') = B y y' := P.dualBilinForm_weylGroup hA' S hw y y'
  have hBsymm (y y' : Dual K H) : B y y' = B y' y := (P.isSymm_dualBilinForm S).eq y y'
  have hnegA : ∀ i, ∃ n : ℕ, (-a) (P.coroot i) = n := fun i ↦ by
    obtain ⟨n, hn⟩ := ha i; exact ⟨n, by simp [hn]⟩
  -- `w a - a ∈ Q₊` for every `w ∈ W`.
  have hpos_sub : ∀ w : P.weylGroup hA', ∃ e : ι → ℤ, 0 ≤ e ∧ w.val a - a = P.rootOf e := by
    intro w
    obtain ⟨e, he, hee⟩ := P.exists_sub_apply_eq_rootOf hA' hnegA w
    refine ⟨e, he, ?_⟩
    rw [← hee, map_neg]
    abel
  choose nb hnb using hb
  choose n2 hn2 using hν₂
  choose nν hnν using hν
  -- `(x a - a | b) = 0`.
  obtain ⟨e, he, hxe⟩ := hpos_sub ⟨x, hx⟩
  have hBeb : B (P.rootOf e) b = 0 := by
    set R₁ : ℤ := ∑ i, c i * d i * ((nν i : ℤ) + n2 i) with hR₁
    have hR₁nonneg : 0 ≤ R₁ := Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (hc i) (hdpos i).le) (by positivity)
    have hR₁eq : B (z (a - b)) (z (a - b)) - B ν₂ ν₂ = R₁ := by
      have hsplit : z (a - b) = ν₂ + P.rootOf c := by rw [← hνc]; abel
      calc B (z (a - b)) (z (a - b)) - B ν₂ ν₂ = B (P.rootOf c) (z (a - b) + ν₂) := by
            rw [hsplit]
            simp only [map_add, LinearMap.add_apply]
            rw [hBsymm ν₂ (P.rootOf c)]
            ring
        _ = R₁ := by
            rw [hB, hR₁]
            push_cast
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [LinearMap.add_apply, hnν, hn2]
    set R₃ : ℤ := ∑ i, 2 * (e i * d i * (nb i : ℤ)) with hR₃
    have hR₃nonneg : 0 ≤ R₃ := Finset.sum_nonneg fun i _ => by
      have := mul_nonneg (he i) (hdpos i).le
      have : (0 : ℤ) ≤ nb i := by positivity
      positivity
    have hR₃eq : B (x a - b) (x a - b) - B (a - b) (a - b) = R₃ := by
      have h1 : B (x a) (x a) = B a a := hW hx _ _
      have hxa : x a = a + P.rootOf e := by rw [← hxe]; abel
      have hBe : 2 * B (P.rootOf e) b = -R₃ := by
        rw [hB, hR₃]
        push_cast
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hnb]
        ring
      rw [hxa] at h1 ⊢
      simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at h1 ⊢
      rw [hBsymm b a, hBsymm b (P.rootOf e), hBsymm a (P.rootOf e)] at *
      linear_combination (1 : K) * h1 - hBe
    have hR : R₃ = -R₁ := by
      have h1 : B (z (a - b)) (z (a - b)) = B (a - b) (a - b) := hW hz _ _
      have h2 : B (u ν₂) (u ν₂) = B ν₂ ν₂ := hW hu _ _
      have h3 : x a - b = u ν₂ := by rw [← h]; abel
      have : (R₃ : K) = -R₁ := by
        rw [← hR₃eq, ← hR₁eq, h1, h3, h2]
        ring
      exact_mod_cast this
    have hR₃0 : R₃ = 0 := by omega
    rw [hB]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => by
      have := mul_nonneg (he j) (hdpos j).le
      have : (0 : ℤ) ≤ nb j := by positivity
      positivity).mp hR₃0 i (Finset.mem_univ i)
    rw [hnb i]
    have : ((e i * d i : ℤ) : K) * (nb i : K) = 0 := by
      have := congrArg (fun t : ℤ ↦ (t : K)) hterm
      push_cast at this ⊢
      linear_combination (1 / 2 : K) * this
    linear_combination -this
  -- Minimize the height of `g⁻¹ x a - a` over the stabilizer of `b`.
  choose m hm hmeq using fun g : P.weylGroup hA' ↦ hpos_sub (g⁻¹ * ⟨x, hx⟩)
  have : Nonempty {g : P.weylGroup hA' // g.val b = b} := ⟨⟨1, rfl⟩⟩
  obtain ⟨⟨g, hgb⟩, hgmin⟩ :=
    Finite.exists_min (fun g : {g : P.weylGroup hA' // g.val b = b} ↦ ∑ i, m g.1 i)
  set c := (g⁻¹ * ⟨x, hx⟩ : P.weylGroup hA').val a with hcdef
  have hc_eq : c = a + P.rootOf (m g) := by rw [← hmeq g]; abel
  have hginv : (g⁻¹ : P.weylGroup hA').val b = b := by
    change g.val.symm b = b
    conv_lhs => rw [← hgb]
    exact g.val.symm_apply_apply b
  -- (i) `g⁻¹ x a - a` is supported on the walls of `b`.
  have hsupp : ∀ i, m g i = 0 ∨ nb i = 0 := by
    have hB0 : B (P.rootOf (m g)) b = 0 := by
      have h1 : B c b = B (x a) b := by
        rw [hcdef]
        change B ((g⁻¹ : P.weylGroup hA').val (x a)) b = B (x a) b
        conv_lhs => rw [← hginv]
        exact hW (g⁻¹).property _ _
      have h2 : B (x a) b = B a b := by
        have hxa : x a = a + P.rootOf e := by rw [← hxe]; abel
        rw [hxa, map_add, LinearMap.add_apply, hBeb, add_zero]
      rw [hc_eq, map_add, LinearMap.add_apply] at h1
      linear_combination h1 + h2
    rw [hB] at hB0
    have hterms : ∀ i, m g i * d i * (nb i : ℤ) = 0 := by
      have hsum : ∑ i, m g i * d i * (nb i : ℤ) = 0 := by
        have : ((∑ i, m g i * d i * (nb i : ℤ) : ℤ) : K) = 0 := by
          push_cast
          rw [← neg_eq_zero, ← Finset.sum_neg_distrib, ← hB0]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hnb i]
          push_cast
          ring
        exact_mod_cast this
      exact fun i ↦ (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ by
        have := mul_nonneg (hm g j) (hdpos j).le
        have : (0 : ℤ) ≤ nb j := by positivity
        positivity).mp hsum i (Finset.mem_univ i)
    intro i
    rcases mul_eq_zero.mp (hterms i) with h3 | h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact Or.inl h4
      · exact absurd h4 (hdpos i).ne'
    · exact Or.inr (by exact_mod_cast h3)
  -- the pairings of `c` are integers
  choose na hna using ha
  have hcpair : ∀ i, c (P.coroot i) = ((-(na i : ℤ) + (A *ᵥ m g) i : ℤ) : K) := by
    intro i
    rw [hc_eq, LinearMap.add_apply, hna i, P.rootOf_apply_coroot]
    push_cast
    ring
  -- (ii) `c` is antidominant on the walls of `b`, by minimality.
  have hwall : ∀ j, nb j = 0 → -(na j : ℤ) + (A *ᵥ m g) j ≤ 0 := by
    intro j hj
    by_contra hpos
    push Not at hpos
    set k := -(na j : ℤ) + (A *ᵥ m g) j with hk
    set sj : P.weylGroup hA' := ⟨P.reflection hA' j, P.reflection_mem_weylGroup hA' j⟩
    have hsjb : sj.val b = b := by
      change P.reflection hA' j b = b
      rw [reflection_apply, hnb j, hj]
      simp
    have hgs : (g * sj).val b = b := by
      change g.val (sj.val b) = b
      rw [hsjb, hgb]
    have hnew : P.rootOf (m (g * sj)) = P.rootOf (m g - k • Pi.single j 1) := by
      rw [← hmeq, map_sub, map_zsmul, rootOf_single, ← hmeq]
      have hsjinv : sj⁻¹ = sj := by
        refine inv_eq_of_mul_eq_one_left (Subtype.ext ?_)
        exact P.reflection_mul_self hA' j
      have : ((g * sj)⁻¹ * ⟨x, hx⟩ : P.weylGroup hA').val a = sj.val c := by
        rw [hcdef, show (g * sj)⁻¹ * ⟨x, hx⟩ = sj * (g⁻¹ * ⟨x, hx⟩) by
          simp only [_root_.mul_inv_rev, hsjinv, mul_assoc]]
        rfl
      rw [this]
      change P.reflection hA' j c - a = c - a - k • P.root j
      rw [reflection_apply, hcpair j, ← Int.cast_smul_eq_zsmul K]
      abel
    have hmnew := P.rootOf_injective hnew
    have hsum : ∑ i, m (g * sj) i = ∑ i, m g i - k := by
      rw [hmnew]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_pi_single', Finset.mem_univ, ite_true, mul_one]
    have hlt : ∑ i, m g i ≤ ∑ i, m (g * sj) i := hgmin ⟨g * sj, hgs⟩
    omega
  -- (iii) hence `c` is antidominant, so `c = a`.
  have hcanti : ∀ i, ∃ n : ℕ, (-c) (P.coroot i) = n := by
    intro i
    have hle : -(na i : ℤ) + (A *ᵥ m g) i ≤ 0 := by
      rcases hsupp i with h0 | h0
      · have : (A *ᵥ m g) i ≤ 0 := by
          simp only [mulVec, dotProduct]
          refine Finset.sum_nonpos fun l _ ↦ ?_
          by_cases hl : l = i
          · subst hl; rw [h0, mul_zero]
          · exact mul_nonpos_of_nonpos_of_nonneg (hA'.offDiag_nonpos i l (Ne.symm hl))
              (hm g l)
        omega
      · exact hwall i h0
    set t := -(-(na i : ℤ) + (A *ᵥ m g) i) with ht
    refine ⟨t.toNat, ?_⟩
    rw [LinearMap.neg_apply, hcpair i]
    have h1 : ((t.toNat : ℤ)) = t := Int.toNat_of_nonneg (by omega)
    have h2 : ((t.toNat : ℕ) : K) = ((t : ℤ) : K) := by exact_mod_cast h1
    rw [h2, ht]
    push_cast
    ring
  have hfix := P.apply_eq_self_of_dominant hA' (μ := -a) hnegA
    (g⁻¹ * ⟨x, hx⟩ : P.weylGroup hA').property (by
      intro i
      obtain ⟨n, hn⟩ := hcanti i
      exact ⟨n, by rw [map_neg, ← hcdef]; exact hn⟩)
  have hca : c = a := by
    rw [hcdef]
    have := congrArg Neg.neg hfix
    simpa [map_neg] using this
  refine ⟨g.val, g.property, hgb, ?_⟩
  have : g.val c = x a := by
    rw [hcdef]
    change g.val (g.val.symm (x a)) = x a
    exact g.val.apply_symm_apply _
  rw [← this, hca]

end RootDatum

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H}

namespace KacMoodyAlgebra.IrreducibleModule

variable (hA : A.IsFiniteCartan)
include hA

/-- **The surviving weights** (integral weights, finite type; cf. Humphreys, GSM 94, 7.12).
Let `λ + ρ` and `μ + ρ` be antidominant integral and `ν = z (λ - μ)`, `z ∈ W`, dominant. If `ν'` is
a weight of `L(ν)` and `w·μ + ν' = y·λ` for `w, y ∈ W`, then `y·λ = (w w')·λ` for some `w' ∈ W`
fixing `μ` (for the dot action). -/
theorem exists_weylDot_eq_of_add_eq_weylDot {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
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
  obtain ⟨g, hg, hgb, hga⟩ := P.exists_apply_eq_of_add_eq_apply hA hlam hμ hz (u'⁻¹).property
    (w⁻¹ * y).property (by rw [add_sub_add_right_eq_sub, hzν]; exact hν) hu' hc hνc hx
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · simp only [weylDot, hgb, add_sub_cancel_right]
  · simp only [weylDot]
    congr 1
    change y.val (lam + P.rho) = w.val (g (lam + P.rho))
    rw [hga]
    change y.val (lam + P.rho) = w.val (w.val.symm (y.val (lam + P.rho)))
    rw [LinearEquiv.apply_symm_apply]

omit [FiniteDimensional K H] in
/-- For `w'` fixing `μ`, the weight `(w w')·λ - w·μ = w w' (λ - μ)` of `L(ν)`, `ν = z (λ - μ)`
dominant, is extremal: it has multiplicity one. -/
theorem finrank_weightSpace_weylDot_sub_weylDot {lam μ ν : Dual K H}
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    (w w' : P.weylGroup hA.isGeneralizedCartan)
    (hw' : P.weylDot hA.isGeneralizedCartan w' μ = μ) :
    finrank K (weightSpace P (IrreducibleModule P ν)
      (P.weylDot hA.isGeneralizedCartan (w * w') lam -
        P.weylDot hA.isGeneralizedCartan w μ)) = 1 := by
  have hA' := hA.isGeneralizedCartan
  have hfix : w'.val (μ + P.rho) = μ + P.rho := by
    have := congrArg (· + P.rho) hw'
    simpa [weylDot] using this
  have he : P.weylDot hA' (w * w') lam - P.weylDot hA' w μ = ((w * w').val * z.symm) ν := by
    rw [LinearEquiv.mul_apply, ← hzν, LinearEquiv.symm_apply_apply]
    simp only [weylDot]
    conv_lhs => rw [show w.val (μ + P.rho) = (w * w').val (μ + P.rho) by
      change _ = w.val (w'.val (μ + P.rho)); rw [hfix]]
    simp only [map_sub, map_add]
    abel
  rw [he]
  have hV := (isIntegrable_iff P hA').mpr hν
  have hr := rank_weightSpace_weylGroup hA' hV (mul_mem (w * w').property (inv_mem hz)) ν
  unfold Module.finrank
  rw [show ((w * w').val * z.symm) = ((w * w').val * z⁻¹) from rfl, hr]
  exact finrank_weightSpace_self P ν

end KacMoodyAlgebra.IrreducibleModule

namespace KacMoodyAlgebra

open VermaModule TensorProduct

local notation "𝔤" => KacMoodyAlgebra P

section Steps

open LieModule

variable {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

omit [CharZero K] [FiniteDimensional K H] in
/-- For submodules `N ≤ M` of a module `V` in `𝒪`, `dim (M ∩ V_μ) = dim (N ∩ V_μ) + dim (M/N)_μ`,
with `M/N` realized as the image of `M` in `V/N`. -/
theorem finrank_inf_weightSpaceOfMap_eq_add (hV : IsCategoryO P V)
    {N M : LieSubmodule K P.KacMoodyAlgebra V} (hNM : N ≤ M) (μ : Dual K H) :
    finrank K ↥(M.toSubmodule ⊓ weightSpaceOfMap V (h P) μ) =
      finrank K ↥(N.toSubmodule ⊓ weightSpaceOfMap V (h P) μ) +
        finrank K ↥((M.map (LieSubmodule.Quotient.mk' N)).toSubmodule ⊓
          weightSpaceOfMap (V ⧸ N) (h P) μ) := by
  have := hV.finiteDimensional_weightSpaceOfMap μ
  have hle (ν : Dual K H) : (M.toSubmodule ⊓ weightSpaceOfMap V (h P) ν).map (quotMk P N) ≤
      weightSpaceOfMap (V ⧸ N) (h P) ν := by
    rintro _ ⟨v, hv, rfl⟩
    exact map_mem_weightSpaceOfMap P (LieSubmodule.Quotient.mk' N) hv.2
  have hMsup : ⨆ ν, (M.toSubmodule ⊓ weightSpaceOfMap V (h P) ν) = M.toSubmodule := by
    simp_rw [← map_weightSpaceOfMap_lieSubmodule P M, ← Submodule.map_iSup,
      (hV.lieSubmodule M).iSup_weightSpaceOfMap_eq_top, Submodule.map_top,
      Submodule.range_subtype]
  have hrange : (M.toSubmodule ⊓ weightSpaceOfMap V (h P) μ).map (quotMk P N) =
      (M.map (LieSubmodule.Quotient.mk' N)).toSubmodule ⊓ weightSpaceOfMap (V ⧸ N) (h P) μ := by
    refine le_antisymm (le_inf ?_ (hle μ)) fun x ⟨hxM, hxμ⟩ ↦ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact (LieSubmodule.mem_map _).mpr ⟨v, hv.1, rfl⟩
    refine mem_of_mem_iSup_of_le (h P) _ hle hxμ ?_
    rw [← Submodule.map_iSup, hMsup]
    obtain ⟨m, hm, rfl⟩ := (LieSubmodule.mem_map _).mp hxM
    exact Submodule.mem_map_of_mem hm
  have := LinearMap.finrank_range_add_finrank_ker
    (quotMk P N ∘ₗ (M.toSubmodule ⊓ weightSpaceOfMap V (h P) μ).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, hrange, LinearMap.ker_comp, ker_quotMk,
    ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype] at this
  have hinf : M.toSubmodule ⊓ weightSpaceOfMap V (h P) μ ⊓ N.toSubmodule =
      N.toSubmodule ⊓ weightSpaceOfMap V (h P) μ := by
    rw [inf_right_comm, inf_eq_right.mpr (show N.toSubmodule ≤ M.toSubmodule from hNM)]
  rw [hinf] at this
  omega

omit [CharZero K] [FiniteDimensional K H] in
/-- Weight multiplicities are additive along a finite filtration `0 = F₀ ≤ ⋯ ≤ Fₙ` of a module
in `𝒪`: `dim (Fₙ ∩ V_μ) = Σⱼ dim (Fⱼ₊₁/Fⱼ)_μ`. -/
theorem finrank_inf_weightSpaceOfMap_eq_sum (hV : IsCategoryO P V) {n : ℕ}
    (F : Fin (n + 1) → LieSubmodule K P.KacMoodyAlgebra V) (hF : Monotone F) (hF0 : F 0 = ⊥)
    (μ : Dual K H) :
    finrank K ↥((F (Fin.last n)).toSubmodule ⊓ weightSpaceOfMap V (h P) μ) =
      ∑ j : Fin n, finrank K (weightSpaceOfMap
        ((F j.succ).map (LieSubmodule.Quotient.mk' (F j.castSucc))) (h P) μ) := by
  induction n with
  | zero =>
    rw [Fin.last_zero, hF0]
    simp
  | succ n ih =>
    have ih' := ih (F ∘ Fin.castSucc) (hF.comp Fin.strictMono_castSucc.monotone) hF0
    rw [Fin.sum_univ_castSucc, ← Fin.succ_last,
      finrank_inf_weightSpaceOfMap_eq_add hV (hF (Fin.castSucc_le_succ (Fin.last n))) μ]
    exact congrArg₂ (· + ·) ih' (finrank_weightSpaceOfMap_lieSubmodule P _ μ).symm

end Steps

variable [IsAlgClosed K] (hA : A.IsFiniteCartan)

include hA in
/-- **Translation out of a facet closure, general form.** Let `ν = z (λ - μ)`, `z ∈ W`, be
dominant integral and `w ∈ W`, and suppose that the weights `ν'` of `L(ν)` with `w·μ + ν'` linked
to `λ` are among the `(w w')·λ - w·μ`, `w'·μ = μ` (hypothesis `hkey`). Then the `χ_λ`-block of
`M(w·μ) ⊗ L(ν)` has a filtration whose nonzero steps are the Verma modules `M((w w')·λ)`, each
exactly once. `hkey` is supplied by
`KacMoodyAlgebra.IrreducibleModule.exists_weylDot_eq_of_add_eq_weylDot` for antidominant integral
weights, and by its non-integral counterpart. -/
theorem exists_translation_verma_filtration_of_forall {lam μ ν : Dual K H}
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan)
    (hkey : ∀ ν' : Dual K H, weightSpace P (IrreducibleModule P ν) ν' ≠ ⊥ →
      ∀ y : P.weylGroup hA.isGeneralizedCartan,
        P.weylDot hA.isGeneralizedCartan w μ + ν' = P.weylDot hA.isGeneralizedCartan y lam →
        ∃ w' : P.weylGroup hA.isGeneralizedCartan, P.weylDot hA.isGeneralizedCartan w' μ = μ ∧
          P.weylDot hA.isGeneralizedCartan y lam =
            P.weylDot hA.isGeneralizedCartan (w * w') lam) :
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
          y = P.weylDot hA.isGeneralizedCartan (w * w') lam} := by
  classical
  have hA' := hA.isGeneralizedCartan
  set Λ := P.weylDot hA' w μ with hΛdef
  have : FiniteDimensional K (IrreducibleModule P ν) :=
    IrreducibleModule.finiteDimensional (P := P) hA hν
  have hZ : IsHDiagonalizable P (IrreducibleModule P ν) :=
    (IrreducibleModule.isCategoryO P ν).iSup_weightSpaceOfMap_eq_top
  obtain ⟨N, wt, -, -, -, -, hcount, hFmono, hF0, hFlast, -, hFstep, hret⟩ :=
    exists_centralTensorVermaFiltration P hZ Λ (centralCharacter P lam)
  set C := centralBlock P (VermaModule P Λ ⊗[K] IrreducibleModule P ν) (centralCharacter P lam)
  set S : Set (Fin (finrank K (IrreducibleModule P ν))) :=
    {j | centralCharacter P (Λ + wt j) = centralCharacter P lam}
  refine ⟨_, fun k ↦ N k ⊓ C, fun j ↦ Λ + wt j, S, hFmono, hF0, hFlast,
    fun j hj ↦ (hFstep j).1 hj, fun j hj ↦ (hFstep j).2 hj, ?_, ?_, ?_⟩
  · -- maps to
    intro j hj
    have hwtj : weightSpace P (IrreducibleModule P ν) (wt j) ≠ ⊥ := by
      intro hbot
      have hc := hcount (wt j)
      rw [hbot, finrank_bot] at hc
      have : Nonempty {j' // wt j' = wt j} := ⟨⟨j, rfl⟩⟩
      exact (Nat.card_pos (α := {j' // wt j' = wt j})).ne' hc
    obtain ⟨y, hy, hye⟩ := (VermaModule.centralCharacter_eq_iff P hA lam (Λ + wt j)).mp hj.symm
    have h : P.weylDot hA' w μ + wt j = P.weylDot hA' ⟨y, hy⟩ lam := by
      simp only [weylDot]
      rw [hye, hΛdef]
      simp only [weylDot]
      abel
    obtain ⟨w', hw', he⟩ :=
      hkey _ hwtj _ h
    exact ⟨w', hw', h.trans he⟩
  · -- injective
    intro j hj j' hj' hjj'
    simp only at hjj'
    have hwt : wt j = wt j' := add_left_cancel hjj'
    obtain ⟨y, hy, hye⟩ := (VermaModule.centralCharacter_eq_iff P hA lam (Λ + wt j)).mp hj.symm
    have hwtj : weightSpace P (IrreducibleModule P ν) (wt j) ≠ ⊥ := by
      intro hbot
      have hc := hcount (wt j)
      rw [hbot, finrank_bot] at hc
      have : Nonempty {j' // wt j' = wt j} := ⟨⟨j, rfl⟩⟩
      exact (Nat.card_pos (α := {j' // wt j' = wt j})).ne' hc
    have h : P.weylDot hA' w μ + wt j = P.weylDot hA' ⟨y, hy⟩ lam := by
      simp only [weylDot]
      rw [hye, hΛdef]
      simp only [weylDot]
      abel
    obtain ⟨w', hw', he⟩ :=
      hkey _ hwtj _ h
    have hmult : finrank K (weightSpace P (IrreducibleModule P ν) (wt j)) = 1 := by
      have hwtj' : wt j = P.weylDot hA' (w * w') lam - P.weylDot hA' w μ := by
        rw [← he, ← h]; abel
      rw [hwtj']
      exact IrreducibleModule.finrank_weightSpace_weylDot_sub_weylDot hA hν hz hzν w w' hw'
    have hone := hret (wt j)
    rw [ite_eq_left (show centralCharacter P (Λ + wt j) = centralCharacter P lam from hj),
      hmult] at hone
    obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp hone
    have := hsub.elim ⟨j, rfl, hj⟩ ⟨j', hwt.symm, hj'⟩
    exact congrArg Subtype.val this
  · -- surjective
    rintro _ ⟨w', hw', rfl⟩
    set μ₀ := P.weylDot hA' (w * w') lam - Λ
    have hχ : centralCharacter P (Λ + μ₀) = centralCharacter P lam := by
      rw [add_sub_cancel]
      exact VermaModule.centralCharacter_weyl P hA' (w * w').property lam
    have hmult : finrank K (weightSpace P (IrreducibleModule P ν) μ₀) = 1 :=
      IrreducibleModule.finrank_weightSpace_weylDot_sub_weylDot hA hν hz hzν w w' hw'
    have hone := hret μ₀
    rw [ite_eq_left hχ, hmult] at hone
    obtain ⟨-, ⟨j, hjwt, hjχ⟩⟩ := Nat.card_eq_one_iff_unique.mp hone
    refine ⟨j, hjχ, ?_⟩
    simp only
    rw [hjwt, add_sub_cancel]

include hA in
/-- **Translation out of a facet closure on characters, general form**: the character version of
`exists_translation_verma_filtration_of_forall`, under the same hypothesis `hkey`. -/
theorem character_translation_verma_of_forall {lam μ ν : Dual K H}
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (lam - μ) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan)
    (hkey : ∀ ν' : Dual K H, weightSpace P (IrreducibleModule P ν) ν' ≠ ⊥ →
      ∀ y : P.weylGroup hA.isGeneralizedCartan,
        P.weylDot hA.isGeneralizedCartan w μ + ν' = P.weylDot hA.isGeneralizedCartan y lam →
        ∃ w' : P.weylGroup hA.isGeneralizedCartan, P.weylDot hA.isGeneralizedCartan w' μ = μ ∧
          P.weylDot hA.isGeneralizedCartan y lam =
            P.weylDot hA.isGeneralizedCartan (w * w') lam) :
    ∃ T : Finset (Dual K H), (T : Set (Dual K H)) = {y | ∃ w' : P.weylGroup hA.isGeneralizedCartan,
        P.weylDot hA.isGeneralizedCartan w' μ = μ ∧
          y = P.weylDot hA.isGeneralizedCartan (w * w') lam} ∧
      (((VermaModule.isCategoryO P (P.weylDot hA.isGeneralizedCartan w μ)).tensorProduct
          (IrreducibleModule.isCategoryO P ν)).lieSubmodule
          (centralBlock P _ (centralCharacter P lam))).character =
        ∑ y ∈ T, (VermaModule.isCategoryO P y).character := by
  classical
  obtain ⟨n, F, x, S, hmono, hF0, hFlast, hiso, hzero, hbij⟩ :=
    exists_translation_verma_filtration_of_forall hA hν hz hzν w hkey
  set S' : Finset (Fin n) := Finset.univ.filter (· ∈ S)
  have hS' : (S' : Set (Fin n)) = S := by ext; simp [S']
  refine ⟨S'.image x, by rw [Finset.coe_image, hS', hbij.image_eq], ?_⟩
  rw [Finset.sum_image fun a ha b hb ↦ hbij.injOn (hS' ▸ ha) (hS' ▸ hb)]
  ext β
  rw [IsCategoryO.coeffAt_character, CharacterRing.coeffAt, HahnSeries.coeff_sum]
  simp only [← CharacterRing.coeffAt.eq_1, IsCategoryO.coeffAt_character]
  rw [finrank_weightSpaceOfMap_lieSubmodule, ← hFlast,
    finrank_inf_weightSpaceOfMap_eq_sum (VermaModule.isCategoryO P _ |>.tensorProduct
      (IrreducibleModule.isCategoryO P ν)) F hmono hF0 β, Nat.cast_sum,
    show S' = Finset.univ.filter (· ∈ S) from rfl, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split_ifs with hj
  · obtain ⟨e⟩ := hiso j hj
    rw [finrank_weightSpaceOfMap_equiv P e]
  · rw [hzero j hj, finrank_weightSpaceOfMap_lieSubmodule]
    simp

include hA in
/-- **Translation out of a facet closure** (integral weights, finite type; Humphreys, GSM 94,
Theorem 7.12, in the form of standard filtrations). Let `λ + ρ`, `μ + ρ` be antidominant integral
and `ν = z (λ - μ)`, `z ∈ W`, dominant. For `w ∈ W`, the `χ_λ`-block of `M(w·μ) ⊗ L(ν)` (that
is, `T_μ^λ M(w·μ)`) has a filtration `0 = F₀ ≤ ⋯ ≤ Fₙ` whose successive quotients are `0` or
Verma modules, and the Verma modules occurring are the `M((w w')·λ)`, `w'` running over the
stabilizer `W_μ°` of `μ` modulo that of `λ`, each exactly once: the map `j ↦ xⱼ` from the nonzero
steps to the weights `(w w')·λ` is a bijection. The character form is
`character_translation_verma`. The facet condition of the source is not needed. -/
theorem exists_translation_verma_filtration {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
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
    IrreducibleModule.exists_weylDot_eq_of_add_eq_weylDot hA hlam hμ hν hz hzν hν' h

include hA in
/-- **Translation out of a facet closure, on characters** (integral weights, finite type;
Humphreys, GSM 94, Theorem 7.12). Under the hypotheses of `exists_translation_verma_filtration`,
`ch T_μ^λ M(w·μ) = Σ_y ch M(y)`, `y` running over the finitely many weights `(w w')·λ` with `w'` in
the stabilizer `W_μ°` of `μ`, each counted once (i.e. over `w' ∈ W_μ°/W_λ°`). The facet condition
of the source is not needed. -/
theorem character_translation_verma {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
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
    IrreducibleModule.exists_weylDot_eq_of_add_eq_weylDot hA hlam hμ hν hz hzν hν' h

end KacMoodyAlgebra

end Matrix.Realization
