/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Jantzen's order formula for a matrix of polynomials

Let `G` be a square matrix with entries in the polynomial ring `K[X]` over a field, with
`det G ≠ 0`. For `i ∈ ℕ` let `Vⁱ ⊆ Kⁿ` be the space of values at `0` of the vectors `w ∈ K[X]ⁿ`
with `w G ≡ 0 mod Xⁱ` (`Matrix.jantzenSpace`). Then `V⁰ ⊇ V¹ ⊇ ⋯` and
`∑_{i ≥ 1} dim Vⁱ = ord_X det G`, the order of vanishing of `det G` at `0`
(`Matrix.sum_finrank_jantzenSpace`). Applied to the Gram matrix of a contravariant form on a
one-parameter family of modules this is the basic identity behind the Jantzen filtration and the
Jantzen sum formula ([HumO] §5.6 (check); [Jantzen, *Moduln mit einem höchsten Gewicht*, Lemma
5.1] (check)).

The proof uses the Smith normal form over the principal ideal domain `K[X]`: with bases `(bⱼ)`,
`(cⱼ)` of `K[X]ⁿ` such that `cⱼ G = aⱼ bⱼ`, one has `Vⁱ = span {cⱼ(0) | ord aⱼ ≥ i}` and
`ord det G = ∑ⱼ ord aⱼ`.

## Main definitions

* `Matrix.jantzenSpace`: the space `Vⁱ`.

## Main results

* `Matrix.sum_finrank_jantzenSpace`: `∑_{i = 1}^{N} dim Vⁱ = N = ord_X det G`.
* `Matrix.jantzenSpace_eq_bot`: `Vⁱ = 0` for `i > ord_X det G`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, §5.6 (check).
-/

open Polynomial Module

noncomputable section

namespace Matrix

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The `i`-th Jantzen space of a square matrix `G` of polynomials: the values at `0` of the
vectors `w` of polynomials with `w G ≡ 0 mod Xⁱ`. -/
def jantzenSpace (G : Matrix n n K[X]) (i : ℕ) : Submodule K (n → K) where
  carrier := {v | ∃ w : n → K[X], (fun s ↦ (w s).eval 0) = v ∧ ∀ s, X ^ i ∣ (w ᵥ* G) s}
  add_mem' := by
    rintro _ _ ⟨w, rfl, hw⟩ ⟨w', rfl, hw'⟩
    refine ⟨w + w', by ext; simp, fun s ↦ ?_⟩
    rw [add_vecMul]
    exact dvd_add (hw s) (hw' s)
  zero_mem' := ⟨0, by ext; simp, fun s ↦ by simp⟩
  smul_mem' := by
    rintro c _ ⟨w, rfl, hw⟩
    refine ⟨C c • w, by ext; simp, fun s ↦ ?_⟩
    rw [smul_vecMul, Pi.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_right (hw s) _

lemma natTrailingDegree_eq_zero_of_isUnit {p : K[X]} (hp : IsUnit p) : p.natTrailingDegree = 0 := by
  obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.mp hp
  exact natTrailingDegree_C r

lemma natTrailingDegree_prod {ι : Type*} (s : Finset ι) (f : ι → K[X]) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).natTrailingDegree = ∑ i ∈ s, (f i).natTrailingDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      natTrailingDegree_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

lemma X_pow_dvd_iff_le_natTrailingDegree {p : K[X]} (hp : p ≠ 0) {i : ℕ} :
    X ^ i ∣ p ↔ i ≤ p.natTrailingDegree := by
  rw [X_pow_dvd_iff]
  exact ⟨fun h ↦ le_natTrailingDegree hp h,
    fun h d hd ↦ coeff_eq_zero_of_lt_natTrailingDegree (hd.trans_le h)⟩

/-- **Jantzen's order formula** (Smith normal form description): if `det G ≠ 0`, there are bases
`(cⱼ)` of `K[X]ⁿ` and nonzero `aⱼ` with `ord det G = ∑ ord aⱼ` and
`Vⁱ = span {cⱼ(0) | ord aⱼ ≥ i}`, the `cⱼ(0)` being linearly independent. -/
theorem exists_jantzenSpace_eq_span (G : Matrix n n K[X]) (hG : G.det ≠ 0) :
    ∃ (v : n → n → K) (a : n → K[X]), LinearIndependent K v ∧ (∀ j, a j ≠ 0) ∧
      G.det.natTrailingDegree = ∑ j, (a j).natTrailingDegree ∧
      ∀ i, G.jantzenSpace i = Submodule.span K (v '' {j | i ≤ (a j).natTrailingDegree}) := by
  classical
  set φ := G.vecMulLinear
  have hinj : Function.Injective φ :=
    Matrix.vecMul_injective_iff.mpr (linearIndependent_rows_of_det_ne_zero hG)
  have hrank : finrank K[X] (LinearMap.range φ) = finrank K[X] (n → K[X]) :=
    LinearMap.finrank_range_of_inj hinj
  obtain ⟨bM, a, bN, hsnf⟩ :=
    (LinearMap.range φ).exists_smith_normal_form_of_rank_eq (Pi.basisFun K[X] n) hrank
  set e := LinearEquiv.ofInjective φ hinj
  set c := bN.map e.symm
  have hc : ∀ j, c j ᵥ* G = a j • bM j := fun j ↦ by
    rw [← hsnf]
    have : e (c j) = bN j := by simp [c]
    rw [← this]
    rfl
  have ha : ∀ j, a j ≠ 0 := fun j h ↦ bN.ne_zero j (Subtype.ext (by rw [hsnf, h, zero_smul]; rfl))
  -- the matrices of the bases `c` and `bM`
  set Cm : Matrix n n K[X] := (Pi.basisFun K[X] n).toMatrix c
  set Bm : Matrix n n K[X] := (Pi.basisFun K[X] n).toMatrix bM
  have hCm : IsUnit Cm.det := by
    have := Basis.invertibleToMatrix (Pi.basisFun K[X] n) c
    exact isUnit_det_of_invertible Cm
  have hBm : IsUnit Bm.det := by
    have := Basis.invertibleToMatrix (Pi.basisFun K[X] n) bM
    exact isUnit_det_of_invertible Bm
  have hmat : Cmᵀ * G = diagonal a * Bmᵀ := by
    refine Matrix.ext fun j s ↦ ?_
    have := congrFun (hc j) s
    simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [diagonal_mul]
    simp only [mul_apply, transpose_apply, Basis.toMatrix_apply, Pi.basisFun_repr, Cm, Bm]
    exact this
  have hdet : Cm.det * G.det = (∏ j, a j) * Bm.det := by
    have := congrArg det hmat
    rwa [det_mul, det_transpose, det_mul, det_diagonal, det_transpose] at this
  refine ⟨fun j s ↦ (c j s).eval 0, a, ?_, ha, ?_, fun i ↦ ?_⟩
  · -- the values at `0` of the basis `c` are linearly independent
    have hdet0 : (Cm.map (eval 0)).det ≠ 0 := by
      have := RingHom.map_det (Polynomial.evalRingHom (0 : K)) Cm
      rw [RingHom.mapMatrix_apply, coe_evalRingHom] at this
      rw [← this]
      obtain ⟨r, hr, hrC⟩ := Polynomial.isUnit_iff.mp hCm
      rw [← hrC, eval_C]
      exact hr.ne_zero
    have := linearIndependent_cols_of_det_ne_zero hdet0
    convert this using 1
    ext j s
    simp [Cm, Basis.toMatrix_apply]
  · have h1 := congrArg natTrailingDegree hdet
    rw [natTrailingDegree_mul hCm.ne_zero hG, natTrailingDegree_eq_zero_of_isUnit hCm,
      zero_add, natTrailingDegree_mul (Finset.prod_ne_zero_iff.mpr fun j _ ↦ ha j)
        hBm.ne_zero, natTrailingDegree_eq_zero_of_isUnit hBm, add_zero,
      natTrailingDegree_prod _ _ fun j _ ↦ ha j] at h1
    exact h1
  · apply le_antisymm
    · rintro _ ⟨w, rfl, hw⟩
      -- expand `w` in the basis `c`
      set γ := c.repr w
      have hw' : w = ∑ j, γ j • c j := (c.sum_repr w).symm
      have hwG : w ᵥ* G = ∑ j, (γ j * a j) • bM j := by
        rw [hw', sum_vecMul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [smul_vecMul, hc, smul_smul]
      -- all coordinates of `w G` are divisible by `Xⁱ`
      choose u hu using hw
      have hrepr : ∀ j, X ^ i ∣ γ j * a j := fun j ↦ by
        have h1 : w ᵥ* G = (X : K[X]) ^ i • u := by funext s; rw [hu s]; rfl
        have h3 : bM.repr (w ᵥ* G) j = γ j * a j := by
          rw [hwG, map_sum]
          simp [Finsupp.single_apply]
        have h4 : bM.repr ((X : K[X]) ^ i • u) j = X ^ i * bM.repr u j := by
          rw [map_smul]; rfl
        exact ⟨bM.repr u j, by rw [← h3, h1, h4]⟩
      have hγ : ∀ j, (a j).natTrailingDegree < i → (γ j).eval 0 = 0 := fun j hj ↦ by
        by_contra h0
        have hγ0 : γ j ≠ 0 := fun h ↦ h0 (by rw [h, eval_zero])
        have := (X_pow_dvd_iff_le_natTrailingDegree (mul_ne_zero hγ0 (ha j))).mp (hrepr j)
        rw [natTrailingDegree_mul hγ0 (ha j)] at this
        have hγt : (γ j).natTrailingDegree = 0 :=
          natTrailingDegree_eq_zero.mpr (.inr (by rwa [coeff_zero_eq_eval_zero]))
        omega
      have hval : (fun s ↦ (w s).eval 0) = ∑ j, (γ j).eval 0 • fun s ↦ (c j s).eval 0 := by
        ext s
        rw [hw']
        simp [eval_finsetSum]
      rw [hval]
      refine Submodule.sum_mem _ fun j _ ↦ ?_
      by_cases hj : i ≤ (a j).natTrailingDegree
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
      · rw [hγ j (not_le.mp hj), zero_smul]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      refine ⟨c j, rfl, fun s ↦ ?_⟩
      rw [hc, Pi.smul_apply, smul_eq_mul]
      exact dvd_mul_of_dvd_left ((X_pow_dvd_iff_le_natTrailingDegree (ha j)).mpr hj) _

/-- **Jantzen's order formula**: if `det G ≠ 0` and `N` is the order of vanishing of `det G` at `0`,
then `∑_{i = 1}^{N} dim Vⁱ = N`. -/
theorem sum_finrank_jantzenSpace (G : Matrix n n K[X]) (hG : G.det ≠ 0) :
    ∑ i ∈ Finset.range G.det.natTrailingDegree, finrank K (G.jantzenSpace (i + 1)) =
      G.det.natTrailingDegree := by
  classical
  obtain ⟨v, a, hv, ha, hdet, hspace⟩ := exists_jantzenSpace_eq_span G hG
  have hdim : ∀ i, finrank K (G.jantzenSpace i) =
      (Finset.univ.filter fun j ↦ i ≤ (a j).natTrailingDegree).card := fun i ↦ by
    have : v '' {j | i ≤ (a j).natTrailingDegree} =
        Set.range (v ∘ Subtype.val : {j // i ≤ (a j).natTrailingDegree} → n → K) := by
      rw [Set.range_comp, Subtype.range_coe_subtype]
    rw [hspace, this, finrank_span_eq_card (hv.comp _ Subtype.val_injective), Fintype.card_subtype]
  simp_rw [hdim]
  -- `∑_{i < N} #{j | i + 1 ≤ ord aⱼ} = ∑ⱼ ord aⱼ`
  have hle : ∀ j, (a j).natTrailingDegree ≤ G.det.natTrailingDegree := fun j ↦ by
    rw [hdet]
    exact Finset.single_le_sum (f := fun j ↦ (a j).natTrailingDegree)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  conv_rhs => rw [hdet]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have : (Finset.range G.det.natTrailingDegree).filter (fun i ↦ i + 1 ≤ (a j).natTrailingDegree) =
      Finset.range (a j).natTrailingDegree := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; have := hle j; omega
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one, this, Finset.card_range]

/-- `Vⁱ = 0` for `i` larger than the order of vanishing of `det G` at `0`. -/
theorem jantzenSpace_eq_bot (G : Matrix n n K[X]) (hG : G.det ≠ 0) {i : ℕ}
    (hi : G.det.natTrailingDegree < i) : G.jantzenSpace i = ⊥ := by
  obtain ⟨v, a, -, -, hdet, hspace⟩ := exists_jantzenSpace_eq_span G hG
  rw [hspace, Submodule.span_eq_bot]
  rintro _ ⟨j, hj, rfl⟩
  exfalso
  have : (a j).natTrailingDegree ≤ G.det.natTrailingDegree := by
    rw [hdet]
    exact Finset.single_le_sum (f := fun j ↦ (a j).natTrailingDegree)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  exact absurd hj (by simp only [Set.mem_ofPred_eq, not_le]; omega)

end Matrix
