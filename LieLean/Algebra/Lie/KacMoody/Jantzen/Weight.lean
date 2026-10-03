/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Jantzen

/-!
# The Jantzen filtration and the Shapovalov determinant

Let `A` be symmetrizable and `M(λ₀)^i` the Jantzen filtration of `M(λ₀)` along the line
`λ(t) = λ₀ + t δ` (`KacMoody/Jantzen.lean`). Let `D_β(λ)` be the determinant of the Shapovalov
form on `M(λ)_{λ-β}` in the PBW basis, and suppose `t ↦ D_β(λ(t))` is not identically zero. Then
([HumO] §5.6–5.7; [Jan79] 5.1, 5.3)

`∑_{i ≥ 1} dim M(λ₀)^i_{λ₀-β} = ord_{t=0} D_β(λ₀ + t δ)`

(`Matrix.Realization.KacMoodyAlgebra.VermaModule.sum_finrank_jantzen_inf_weightSpace`). In
coordinates, `M(λ₀)^i_{λ₀-β}` is the `i`-th Jantzen space of the Gram matrix of the Shapovalov
form along the line, a matrix of polynomials in `t`, and the formula is
`Matrix.sum_finrank_jantzenSpace`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.finrank_jantzen_inf_weightSpace`: the dimension
  of `M(λ₀)^i_{λ₀-β}` is that of the `i`-th Jantzen space of the Gram matrix.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.sum_finrank_jantzen_inf_weightSpace`,
  `Matrix.Realization.KacMoodyAlgebra.VermaModule.finrank_jantzen_inf_weightSpace_eq_zero`: **the
  order formula**.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, §5.6–5.7.
* [Jan79] J. C. Jantzen, *Moduln mit einem höchsten Gewicht*, Lecture Notes in Math. 750,
  Springer 1979, 5.1, 5.3 (numbering as cited in [HumO] §5.6–5.7).
-/

open Module LieModule Module.Dual Polynomial UniversalEnvelopingAlgebra

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝒰⁻" => UniversalEnvelopingAlgebra K (nNeg P)

namespace VermaModule

/-- The PBW basis of `U(𝔫₋)`. -/
local notation "𝐞" => pbwBasis (nNegBasis P)

variable {P}

/-- The coordinates of a polynomial family along a line are polynomial functions of `t`. -/
lemma exists_eval_eq_repr {f : K → 𝒰⁻} (hf : f ∈ lineFam P) (s : NegRootIndex P →₀ ℕ) :
    ∃ q : K[X], ∀ t, q.eval t = (𝐞).repr (f t) s := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, u, rfl⟩ := hf
    exact ⟨X ^ n * C ((𝐞).repr u s), fun t ↦ by simp; ring⟩
  | zero => exact ⟨0, fun t ↦ by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨p, hp⟩ := hf
    obtain ⟨q, hq⟩ := hg
    exact ⟨p + q, fun t ↦ by simp [hp, hq]⟩
  | smul a f _ hf =>
    obtain ⟨p, hp⟩ := hf
    exact ⟨C a * p, fun t ↦ by simp [hp]⟩

lemma pairAt_pbw_eq_zero (Λ : Dual K H) {s s' : NegRootIndex P →₀ ℕ}
    (h : negRootWt P s ≠ negRootWt P s') : pairAt P Λ (𝐞 s) (𝐞 s') = 0 :=
  contravariantForm_eq_zero_of_ne P Λ (pbwBasisVerma_mem_weightSpace P Λ s)
    (pbwBasisVerma_mem_weightSpace P Λ s') (fun h' ↦ h (sub_right_injective h'))

lemma pairAt_left_eq_sum (Λ β : Dual K H) (u : 𝒰⁻) {s' : NegRootIndex P →₀ ℕ}
    (hs' : s' ∈ partitions P β) :
    pairAt P Λ u (𝐞 s') = ∑ s ∈ partitions P β, (𝐞).repr u s * pairAt P Λ (𝐞 s) (𝐞 s') := by
  classical
  have hlin : ∀ u : 𝒰⁻, pairAt P Λ u (𝐞 s') =
      ((contravariantForm P Λ).flip (equivEnvNNeg P Λ (𝐞 s')) ∘ₗ
        (equivEnvNNeg P Λ).toLinearMap) u := fun _ ↦ rfl
  conv_lhs => rw [← (𝐞).linearCombination_repr u, hlin, Finsupp.linearCombination_apply,
    map_finsuppSum]
  simp only [map_smul, smul_eq_mul, Finsupp.sum]
  rw [Finset.sum_subset (s₂ := ((𝐞).repr u).support ∪ partitions P β) Finset.subset_union_left
      fun s _ hs ↦ by simp [Finsupp.notMem_support_iff.mp hs],
    Finset.sum_subset (s₁ := partitions P β) Finset.subset_union_right fun s _ hs ↦ by
      rw [pairAt_pbw_eq_zero Λ fun h ↦ hs ((mem_partitions P).mpr
        (h.trans ((mem_partitions P).mp hs'))), mul_zero]]
  exact Finset.sum_congr rfl fun s _ ↦ by rw [← hlin]

variable [FiniteDimensional K H] (S : A.Symmetrization)

variable (P) in
/-- The Gram matrix of the Shapovalov form on `M(λ(t))_{λ(t)-β}` along the line
`λ(t) = λ₀ + t δ`, as a matrix of polynomials in `t`. -/
def gramPoly (Λ₀ δ β : Dual K H) : Matrix (partitions P β) (partitions P β) K[X] :=
  fun s s' ↦ (exists_eval_eq_pairAt S Λ₀ δ (𝐞 s) (𝐞 s')).choose

lemma eval_gramPoly (Λ₀ δ β : Dual K H) (s s' : partitions P β) (t : K) :
    (gramPoly P S Λ₀ δ β s s').eval t = pairAt P (Λ₀ + t • δ) (𝐞 s) (𝐞 s') :=
  (exists_eval_eq_pairAt S Λ₀ δ (𝐞 s) (𝐞 s')).choose_spec t

/-- The determinant of the Gram matrix along the line is the Shapovalov determinant. -/
lemma eval_det_gramPoly (Λ₀ δ β : Dual K H) (t : K) :
    (gramPoly P S Λ₀ δ β).det.eval t = (LinearMap.BilinForm.toMatrix
      (pbwWeightBasis P (Λ₀ + t • δ) β) (weightSpaceForm P (Λ₀ + t • δ) (Λ₀ + t • δ - β))).det := by
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext s s'
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, coe_evalRingHom, eval_gramPoly,
    LinearMap.BilinForm.toMatrix_apply]
  simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
    weightBasisOf_apply]
  rfl

omit [FiniteDimensional K H] in
variable (P) in
/-- The coordinate map `Kᵀ → M(λ₀)`, `v ↦ ∑ v_s e_s v_{λ₀}`. -/
def coordMap (Λ₀ β : Dual K H) : (partitions P β → K) →ₗ[K] VermaModule P Λ₀ :=
  (equivEnvNNeg P Λ₀).toLinearMap ∘ₗ Fintype.linearCombination K fun s ↦ 𝐞 s

omit [FiniteDimensional K H] in
lemma coordMap_injective (Λ₀ β : Dual K H) : Function.Injective (coordMap P Λ₀ β) :=
  (equivEnvNNeg P Λ₀).injective.comp (linearIndependent_iff_injective_fintypeLinearCombination.mp
    ((𝐞).linearIndependent.comp _ Subtype.val_injective))

omit [FiniteDimensional K H] in
lemma coordMap_apply (Λ₀ β : Dual K H) (v : partitions P β → K) :
    coordMap P Λ₀ β v = equivEnvNNeg P Λ₀ (∑ s, v s • 𝐞 s) := by
  simp [coordMap, Fintype.linearCombination_apply]

omit [FiniteDimensional K H] in
lemma pairAt_right_eq_sum (Λ : Dual K H) (u w : 𝒰⁻) :
    pairAt P Λ u w = ∑ s' ∈ ((𝐞).repr w).support, (𝐞).repr w s' * pairAt P Λ u (𝐞 s') := by
  have hlin : ∀ w : 𝒰⁻, pairAt P Λ u w =
      (contravariantForm P Λ (equivEnvNNeg P Λ u) ∘ₗ (equivEnvNNeg P Λ).toLinearMap) w :=
    fun _ ↦ rfl
  conv_lhs => rw [← (𝐞).linearCombination_repr w, hlin, Finsupp.linearCombination_apply,
    map_finsuppSum]
  simp only [map_smul, smul_eq_mul, Finsupp.sum]
  exact Finset.sum_congr rfl fun s _ ↦ by rw [← hlin]

omit [FiniteDimensional K H] in
/-- A vector of `M(λ₀)_{λ₀-β}` is a combination of the PBW vectors of weight `λ₀ - β`. -/
lemma symm_eq_sum_of_mem_weightSpace {Λ₀ β : Dual K H} {m : VermaModule P Λ₀}
    (hm : m ∈ weightSpace P Λ₀ (Λ₀ - β)) :
    (equivEnvNNeg P Λ₀).symm m = ∑ s : partitions P β, (𝐞).repr ((equivEnvNNeg P Λ₀).symm m) s •
      𝐞 s := by
  classical
  rw [weightSpace_eq_span_pbwOf P Λ₀ (nNegBasis_mem P), Basis.mem_span_image] at hm
  have hrepr : (pbwOf P Λ₀ (nNegBasis P)).repr m = (𝐞).repr ((equivEnvNNeg P Λ₀).symm m) := by
    rw [pbwOf, Basis.map_repr, LinearEquiv.trans_apply]
  rw [hrepr] at hm
  conv_lhs => rw [← (𝐞).linearCombination_repr ((equivEnvNNeg P Λ₀).symm m),
    Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Finset.sum_coe_sort (partitions P β) (fun s ↦ (𝐞).repr _ s • 𝐞 s)]
  refine Finset.sum_subset (fun s hs ↦ (mem_partitions P).mpr ?_) fun s _ hs ↦ ?_
  · have := hm hs
    simpa using this
  · rw [Finsupp.notMem_support_iff.mp hs, zero_smul]

/-- **The Jantzen filtration in coordinates**: under the PBW coordinates of `M(λ₀)_{λ₀-β}`, the
`i`-th Jantzen space of the Gram matrix along the line is `M(λ₀)^i ∩ M(λ₀)_{λ₀-β}`. -/
theorem map_coordMap_jantzenSpace (Λ₀ δ β : Dual K H) (i : ℕ) :
    ((gramPoly P S Λ₀ δ β).jantzenSpace i).map (coordMap P Λ₀ β) =
      (jantzen P Λ₀ δ i).toSubmodule ⊓ weightSpace P Λ₀ (Λ₀ - β) := by
  classical
  apply le_antisymm
  · rintro _ ⟨v, ⟨w, rfl, hw⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · change coordMap P Λ₀ β _ ∈ jantzen P Λ₀ δ i
      rw [mem_jantzen, coordMap_apply, LinearEquiv.symm_apply_apply]
      set f : K → 𝒰⁻ := fun t ↦ ∑ s, (w s).eval t • 𝐞 s
      have hf : f ∈ lineFam P := by
        have : f = ∑ s, fun t : K ↦ (w s).eval t • 𝐞 s := by
          funext t; simp only [f, Finset.sum_apply]
        rw [this]
        exact Submodule.sum_mem _ fun s _ ↦ polyEval_smul_mem_lineFam _ _
      refine ⟨f, hf, rfl, fun u ↦ ?_⟩
      simp_rw [pairAt_right_eq_sum _ (f _) u]
      refine DvdXPow.sum _ fun s' _ ↦ ?_
      by_cases hs' : s' ∈ partitions P β
      · obtain ⟨q, hq⟩ := hw ⟨s', hs'⟩
        refine ⟨C ((𝐞).repr u s') * q, fun t ↦ ?_⟩
        beta_reduce
        have e1 : pairAt P (Λ₀ + t • δ) (f t) (𝐞 s') =
            ((w ᵥ* gramPoly P S Λ₀ δ β) ⟨s', hs'⟩).eval t := by
          rw [pairAt_left_eq_sum _ β _ hs']
          simp only [f, vecMul, dotProduct, eval_finsetSum, eval_mul, eval_gramPoly]
          rw [← Finset.sum_coe_sort (partitions P β)]
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          congr 1
          rw [map_sum, Finset.sum_apply']
          simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
            smul_eq_mul, mul_ite, mul_one, mul_zero]
          rw [Finset.sum_eq_single s (fun b _ hb ↦ by
            simp only [Subtype.val_inj]; exact ite_eq_right_iff.mpr fun h ↦ absurd h hb)
            (fun h ↦ absurd (Finset.mem_univ s) h)]
          simp
        rw [e1, hq]
        simp only [eval_mul, eval_pow, eval_X, eval_C]
        ring
      · refine ⟨0, fun t ↦ ?_⟩
        have : pairAt P (Λ₀ + t • δ) (f t) (𝐞 s') = 0 := by
          simp only [f, pairAt, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
          refine Finset.sum_eq_zero fun s _ ↦ ?_
          rw [smul_eq_mul, ← pairAt, pairAt_pbw_eq_zero _ fun h ↦ hs' ((mem_partitions P).mpr
            (h.symm.trans ((mem_partitions P).mp s.2))), mul_zero]
        beta_reduce
        rw [this]
        simp
    · rw [coordMap_apply, map_sum]
      refine Submodule.sum_mem _ fun s _ ↦ ?_
      rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      have := pbwBasisVerma_mem_weightSpace P Λ₀ s
      rwa [(mem_partitions P).mp s.2] at this
  · rintro m ⟨hmJ, hmW⟩
    change m ∈ jantzen P Λ₀ δ i at hmJ
    rw [mem_jantzen] at hmJ
    obtain ⟨f, hf, hf0, hfw⟩ := hmJ
    choose w hw using fun s : partitions P β ↦ exists_eval_eq_repr hf s
    refine ⟨fun s ↦ (𝐞).repr ((equivEnvNNeg P Λ₀).symm m) s, ⟨w, ?_, fun s' ↦ ?_⟩, ?_⟩
    · ext s
      rw [hw, hf0]
    · obtain ⟨q, hq⟩ := hfw (𝐞 s')
      refine ⟨q, Polynomial.funext fun t ↦ ?_⟩
      have : pairAt P (Λ₀ + t • δ) (f t) (𝐞 s') = t ^ i * q.eval t := hq t
      rw [pairAt_left_eq_sum _ β _ s'.2] at this
      rw [eval_mul, eval_pow, eval_X, ← this]
      simp only [vecMul, dotProduct, eval_finsetSum, eval_mul, hw, eval_gramPoly]
      exact (Finset.sum_coe_sort (partitions P β)
        (fun s ↦ (𝐞).repr (f t) s * pairAt P (Λ₀ + t • δ) (𝐞 s) (𝐞 s')))
    · rw [coordMap_apply, ← symm_eq_sum_of_mem_weightSpace hmW, LinearEquiv.apply_symm_apply]

theorem finrank_jantzen_inf_weightSpace (Λ₀ δ β : Dual K H) (i : ℕ) :
    finrank K ((jantzen P Λ₀ δ i).toSubmodule ⊓ weightSpace P Λ₀ (Λ₀ - β) : Submodule K _) =
      finrank K ((gramPoly P S Λ₀ δ β).jantzenSpace i) := by
  rw [← map_coordMap_jantzenSpace S]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (coordMap_injective Λ₀ β) _)).symm

include S in
/-- **The Jantzen order formula** ([HumO] §5.6–5.7; [Jan79] 5.1, 5.3): if `d(t) = D_β(λ₀ + t δ)` is
a nonzero polynomial in `t` (`D_β` the Shapovalov determinant on `M(λ)_{λ-β}` in the PBW basis) with
order of vanishing `N` at `t = 0`, then `∑_{i = 1}^{N} dim M(λ₀)^i_{λ₀-β} = N` (and
`M(λ₀)^i_{λ₀-β} = 0` for `i > N`, see `finrank_jantzen_inf_weightSpace_eq_zero`). -/
theorem sum_finrank_jantzen_inf_weightSpace (Λ₀ δ β : Dual K H) (d : K[X]) (hd : d ≠ 0)
    (hdet : ∀ t, d.eval t = (LinearMap.BilinForm.toMatrix (pbwWeightBasis P (Λ₀ + t • δ) β)
      (weightSpaceForm P (Λ₀ + t • δ) (Λ₀ + t • δ - β))).det) :
    ∑ i ∈ Finset.range d.natTrailingDegree,
      finrank K ((jantzen P Λ₀ δ (i + 1)).toSubmodule ⊓ weightSpace P Λ₀ (Λ₀ - β) :
        Submodule K _) = d.natTrailingDegree := by
  have hG : (gramPoly P S Λ₀ δ β).det = d :=
    Polynomial.funext fun t ↦ by rw [eval_det_gramPoly, hdet]
  simp_rw [finrank_jantzen_inf_weightSpace S]
  rw [← hG]
  exact Matrix.sum_finrank_jantzenSpace _ (hG ▸ hd)

include S in
/-- With the notation of `sum_finrank_jantzen_inf_weightSpace`, `M(λ₀)^i_{λ₀-β} = 0` for `i > N`,
`N` the order of vanishing of `D_β(λ₀ + t δ)` at `t = 0`. -/
theorem finrank_jantzen_inf_weightSpace_eq_zero (Λ₀ δ β : Dual K H) (d : K[X]) (hd : d ≠ 0)
    (hdet : ∀ t, d.eval t = (LinearMap.BilinForm.toMatrix (pbwWeightBasis P (Λ₀ + t • δ) β)
      (weightSpaceForm P (Λ₀ + t • δ) (Λ₀ + t • δ - β))).det) {i : ℕ}
    (hi : d.natTrailingDegree < i) :
    finrank K ((jantzen P Λ₀ δ i).toSubmodule ⊓ weightSpace P Λ₀ (Λ₀ - β) :
      Submodule K _) = 0 := by
  have hG : (gramPoly P S Λ₀ δ β).det = d :=
    Polynomial.funext fun t ↦ by rw [eval_det_gramPoly, hdet]
  rw [finrank_jantzen_inf_weightSpace S, Matrix.jantzenSpace_eq_bot _ (hG ▸ hd) (hG ▸ hi),
    finrank_bot]

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
