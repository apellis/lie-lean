/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Hecke.KazhdanLusztig.ParabolicRecursion.Mu

/-!
# Arbitrary-J spherical/index Deodhar multiplication recursion

## Main results

* `CoxeterSystem.index_boundary_exchange`: if `sd` is not minimal, `sd = dj` for some `j ∈ J`.
* `IwahoriHeckeAlgebra.index_T_smul_basis_boundary`: the standard boundary action is `q`.
* `IwahoriHeckeAlgebra.index_normalized_action`: normalized coordinates on arbitrary vectors.
* `IwahoriHeckeAlgebra.index_klBasis_simple_smul`: all three canonical multiplication branches.

The ascent formula follows from normalized negativity, the genuine parabolic μ coefficient,
and canonical uniqueness. Descent and boundary eigenvalues follow from maximal-support
uniqueness applied to the eigenvalue defect. No finiteness of J or W_J is used.

## References

V. Deodhar, *On some geometric aspects of Bruhat orderings II. The parabolic analogue of
Kazhdan–Lusztig polynomials*, J. Algebra 111 (1987), 483–506. The argument here is
our own, in the normalization q = v² and C'_s = v⁻¹(T_s + 1).
-/
open LaurentPolynomial CoxeterSystem
namespace CoxeterSystem
variable {B W : Type*} [Group W] {M : CoxeterMatrix B} {cs : CoxeterSystem M W}
variable {J : Set B}

/-- Boundary exchange, reconstructed from the Coxeter square/exchange lemma. -/
theorem index_boundary_exchange (i : B) (d : cs.minCosetReps J)
    (hsd : cs.simple i * d ∉ cs.minCosetReps J) :
    ∃ j ∈ J, cs.simple i * d = d * cs.simple j := by
  classical
  simp only [minCosetReps, Set.mem_ofPred_eq, not_forall, not_not] at hsd
  obtain ⟨j, hj, hdj⟩ := hsd
  refine ⟨j, hj, ?_⟩
  have h1 := cs.length_mul_simple (d : W) j
  have h2 := cs.length_simple_mul (d : W) i
  have h3 := cs.length_simple_mul ((d : W) * cs.simple j) i
  have h4 := cs.length_mul_simple (cs.simple i * d) j
  have h0 := d.property j hj
  change ¬ cs.length (d * cs.simple j) < cs.length d at h0
  change cs.length (cs.simple i * d * cs.simple j) < cs.length (cs.simple i * d) at hdj
  rw [← mul_assoc] at h3
  exact cs.simple_mul_eq_mul_simple (by omega) (by omega)

/-- Leaving the minimal representatives always increases length. -/
theorem index_boundary_ascent (i : B) (d : cs.minCosetReps J)
    (hsd : cs.simple i * d ∉ cs.minCosetReps J) :
    cs.length d < cs.length (cs.simple i * d) := by
  obtain ⟨j, hj, he⟩ := index_boundary_exchange i d hsd
  rw [he, length_mul_of_mem_minCosetReps d.property (simple_mem_parabolicSubgroup hj),
    cs.length_simple]
  omega

/-- A left descent of a minimal representative remains minimal. -/
theorem index_descent_minimal (i : B) (d : cs.minCosetReps J)
    (h : cs.length (cs.simple i * d) < cs.length d) :
    cs.simple i * d ∈ cs.minCosetReps J := by
  by_contra hn
  have := index_boundary_ascent i d hn
  omega
end CoxeterSystem

namespace IwahoriHeckeAlgebra
attribute [local instance] Classical.propDecidable
variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {J : Set B}
local notation "q" => (LaurentPolynomial.T 2 : ℤ[T;T⁻¹])
local notation "χ" => ind (cs.parabolicCoxeterSystem J) q

/-- Standard-basis ascent action, valid for arbitrary J. -/
theorem index_T_smul_basis_ascent (i : B) (d : cs.minCosetReps J)
    (h : cs.length d < cs.length (cs.simple i * d))
    (hsd : cs.simple i * d ∈ cs.minCosetReps J) :
    T cs q (cs.simple i) • inducedBasis χ d = inducedBasis χ ⟨cs.simple i * d, hsd⟩ := by
  rw [inducedBasis_apply, inducedBasis_apply, ← Submodule.Quotient.mk_smul]
  change Submodule.Quotient.mk (T cs q (cs.simple i) * T cs q d) = _
  rw [T_simple_mul_T_of_lt cs q h]

/-- Standard-basis descent action, valid for arbitrary J. -/
theorem index_T_smul_basis_descent (i : B) (d : cs.minCosetReps J)
    (h : cs.length (cs.simple i * d) < cs.length d) :
    T cs q (cs.simple i) • inducedBasis χ d =
      (q - 1) • inducedBasis χ d +
        q • inducedBasis χ ⟨cs.simple i * d, index_descent_minimal i d h⟩ := by
  rw [inducedBasis_apply, inducedBasis_apply, ← Submodule.Quotient.mk_smul]
  change Submodule.Quotient.mk (T cs q (cs.simple i) * T cs q d) = _
  rw [T_simple_mul_T_of_lt' cs q h, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]

/-- Standard-basis boundary action: the index character contributes q, not -1. -/
theorem index_T_smul_basis_boundary (i : B) (d : cs.minCosetReps J)
    (hsd : cs.simple i * d ∉ cs.minCosetReps J) :
    T cs q (cs.simple i) • inducedBasis χ d = q • inducedBasis χ d := by
  obtain ⟨j, hj, he⟩ := index_boundary_exchange i d hsd
  have ht : T cs q (cs.simple i) * T cs q d =
      T cs q d * parabolicHom cs q J (T (cs.parabolicCoxeterSystem J) q
        ((cs.parabolicCoxeterSystem J).simple ⟨j, hj⟩)) := by
    rw [T_simple_mul_T_of_lt cs q (index_boundary_ascent i d hsd),
      parabolicHom_T, coe_parabolicCoxeterSystem_simple,
      T_mul_T_of_mem_minCosetReps cs q d.property (simple_mem_parabolicSubgroup hj), he]
  apply (inducedModuleEquiv χ).injective
  rw [inducedBasis_apply, ← Submodule.Quotient.mk_smul]
  change inducedModuleEquiv χ (Submodule.Quotient.mk
    (T cs q (cs.simple i) * T cs q d)) = _
  rw [ht, inducedModuleEquiv_mk, inducedCoeff_mul_parabolicHom, ind_T_simple]
  rw [map_smul, inducedModuleEquiv_mk]

local notation "N" => normalizedBasis cs χ

/-- Normalized-basis ascent action by C'_s. -/
theorem index_klSimple_smul_normalized_ascent (i : B) (d : cs.minCosetReps J)
    (h : cs.length d < cs.length (cs.simple i * d))
    (hsd : cs.simple i * d ∈ cs.minCosetReps J) :
    klSimple cs i • N d = N ⟨cs.simple i * d, hsd⟩ +
      (LaurentPolynomial.T (-1) : ℤ[T;T⁻¹]) • N d := by
  have hl := cs.length_simple_mul (d : W) i
  have he : -(cs.length (cs.simple i * d) : ℤ) = -1 + -(cs.length d : ℤ) := by
    rcases hl with hl | hl <;> omega
  rw [klSimple, normalizedBasis_apply, smul_assoc, add_smul, one_smul,
    smul_comm (T cs q (cs.simple i)), index_T_smul_basis_ascent cs i d h hsd,
    smul_add, smul_smul, normalizedBasis_apply, he, T_add]


/-- Normalized-basis descent action by C'_s. -/
theorem index_klSimple_smul_normalized_descent (i : B) (d : cs.minCosetReps J)
    (h : cs.length (cs.simple i * d) < cs.length d) :
    klSimple cs i • N d = N ⟨cs.simple i * d, index_descent_minimal i d h⟩ +
      (LaurentPolynomial.T 1 : ℤ[T;T⁻¹]) • N d := by
  have hl := cs.length_simple_mul (d : W) i
  have he : -(cs.length (cs.simple i * d) : ℤ) = 1 + -(cs.length d : ℤ) := by
    rcases hl with hl | hl <;> omega
  rw [klSimple, smul_assoc, add_smul, one_smul, normalizedBasis_apply,
    smul_comm (T cs q (cs.simple i)), index_T_smul_basis_descent cs i d h]
  simp only [smul_add, smul_smul, normalizedBasis_apply]
  rw [he, T_add]
  have hp : (LaurentPolynomial.T (-1) : ℤ[T;T⁻¹]) *
      (LaurentPolynomial.T (-(cs.length d : ℤ)) * (q - 1)) +
      LaurentPolynomial.T (-1) * LaurentPolynomial.T (-(cs.length d : ℤ)) =
      LaurentPolynomial.T 1 * LaurentPolynomial.T (-(cs.length d : ℤ)) := by
    calc
      _ = LaurentPolynomial.T (-1) * q * LaurentPolynomial.T (-(cs.length d : ℤ)) := by ring
      _ = _ := by rw [← T_add]; rfl
  have hq : (LaurentPolynomial.T (-1) : ℤ[T;T⁻¹]) *
      (LaurentPolynomial.T (-(cs.length d : ℤ)) * q) =
      LaurentPolynomial.T 1 * LaurentPolynomial.T (-(cs.length d : ℤ)) := by
    calc
      _ = LaurentPolynomial.T (-1) * q * LaurentPolynomial.T (-(cs.length d : ℤ)) := by ring
      _ = _ := by rw [← T_add]; rfl
  rw [hq]
  rw [add_right_comm, ← add_smul, hp, add_comm]

/-- Boundary normalized-basis action is v+v⁻¹. -/
theorem index_klSimple_smul_normalized_boundary (i : B) (d : cs.minCosetReps J)
    (hsd : cs.simple i * d ∉ cs.minCosetReps J) :
    klSimple cs i • N d =
      (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : ℤ[T;T⁻¹]) • N d := by
  rw [klSimple, smul_assoc, add_smul, one_smul, normalizedBasis_apply,
    smul_comm (T cs q (cs.simple i)), index_T_smul_basis_boundary cs i d hsd]
  simp only [smul_add, smul_smul]
  rw [← add_smul]
  congr 1
  calc
    _ = (LaurentPolynomial.T (-1) * q + LaurentPolynomial.T (-1)) *
        LaurentPolynomial.T (-(cs.length d : ℤ)) := by ring
    _ = _ := by rw [← T_add]; rfl

/-- Combined normalized-basis action, with the boundary separated from descents. -/
theorem index_klSimple_smul_normalized (i : B) (d : cs.minCosetReps J) :
    klSimple cs i • N d =
      if hsd : cs.simple i * d ∈ cs.minCosetReps J then
        N ⟨cs.simple i * d, hsd⟩ +
          (LaurentPolynomial.T (if cs.length (cs.simple i * d) < cs.length d
            then 1 else -1) : ℤ[T;T⁻¹]) • N d
      else (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : ℤ[T;T⁻¹]) • N d := by
  classical
  split_ifs with hsd hd
  · exact index_klSimple_smul_normalized_descent cs i d hd
  · apply index_klSimple_smul_normalized_ascent cs i d _ hsd
    have := cs.length_simple_mul (d : W) i
    omega
  · exact index_klSimple_smul_normalized_boundary cs i d hsd

/-- Matrix coefficient of the normalized standard action. -/
theorem index_normalized_action_basis (i : B) (d x : cs.minCosetReps J) :
    (N).repr (klSimple cs i • N d) x =
      if hx : cs.simple i * x ∈ cs.minCosetReps J then
        (N).repr (N d) ⟨cs.simple i * x, hx⟩ +
          LaurentPolynomial.T (if cs.length (cs.simple i * x) < cs.length x then 1 else -1) *
            (N).repr (N d) x
      else (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) * (N).repr (N d) x := by
  classical
  rw [index_klSimple_smul_normalized]
  by_cases hdx : d = x
  · subst d
    by_cases hx : cs.simple i * x ∈ cs.minCosetReps J
    · simp [hx, Finsupp.single_apply, eq_comm]
    · simp [hx]
  · by_cases hd : cs.simple i * d ∈ cs.minCosetReps J
    · rw [dite_eq_left hd]
      simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
        Module.Basis.repr_self, Finsupp.single_apply, hdx, ite_false,
        smul_eq_mul, mul_zero, add_zero]
      by_cases hx : cs.simple i * x ∈ cs.minCosetReps J
      · rw [dite_eq_left hx]
        have he : (⟨cs.simple i * d, hd⟩ : cs.minCosetReps J) = x ↔
            d = (⟨cs.simple i * x, hx⟩ : cs.minCosetReps J) := by
          constructor <;> intro h <;> apply Subtype.ext
          · have h := congrArg (fun y : W ↦ cs.simple i * y) (congrArg Subtype.val h)
            simpa only [simple_mul_simple_cancel_left] using h
          · have h := congrArg (fun y : W ↦ cs.simple i * y) (congrArg Subtype.val h)
            simpa only [simple_mul_simple_cancel_left] using h
        simp only [he]
      · rw [dite_eq_right hx]
        have hn : (⟨cs.simple i * d, hd⟩ : cs.minCosetReps J) ≠ x := by
          intro h
          apply hx
          rw [← h]
          simpa only [simple_mul_simple_cancel_left] using d.property
        simp [hn]
    · rw [dite_eq_right hd]
      simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
        Finsupp.single_apply, hdx, ite_false, smul_eq_mul, mul_zero]
      by_cases hx : cs.simple i * x ∈ cs.minCosetReps J
      · rw [dite_eq_left hx]
        have hn : d ≠ (⟨cs.simple i * x, hx⟩ : cs.minCosetReps J) := by
          intro h
          apply hd
          rw [h]
          simpa only [simple_mul_simple_cancel_left] using x.property
        simp [hn]
      · simp [hx]

/-- Normalized coordinates of C'_s on every vector of the arbitrary-J index module. -/
theorem index_normalized_action (i : B) (m : InducedModule χ) (x : cs.minCosetReps J) :
    (N).repr (klSimple cs i • m) x =
      if hx : cs.simple i * x ∈ cs.minCosetReps J then
        (N).repr m ⟨cs.simple i * x, hx⟩ +
          LaurentPolynomial.T (if cs.length (cs.simple i * x) < cs.length x then 1 else -1) *
            (N).repr m x
      else (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) * (N).repr m x := by
  classical
  induction (N).mem_span m using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨d, rfl⟩ := hy
    exact index_normalized_action_basis cs i d x
  | zero => simp
  | add a b ha hb iha ihb =>
    simp only [smul_add, map_add, Finsupp.add_apply]
    rw [iha, ihb]
    split_ifs <;> ring
  | smul a m hm ih =>
    rw [smul_comm (klSimple cs i) a]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [ih]
    split_ifs <;> ring

end IwahoriHeckeAlgebra

namespace IwahoriHeckeAlgebra.IndexCanonical

attribute [local instance] Classical.propDecidable CoxeterSystem.minCosetRepsPartialOrder

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} {cs : CoxeterSystem M W}
variable {J : Set B} {χ : IwahoriHeckeAlgebra (cs.parabolicCoxeterSystem J)
  (LaurentPolynomial.T 2 : ℤ[T;T⁻¹]) →ₐ[ℤ[T;T⁻¹]] ℤ[T;T⁻¹]}
variable (hχ : IsBarCompatible (cs.parabolicCoxeterSystem J) χ)

local notation "N" => normalizedBasis cs χ
local notation "C" => parabolicKLBasis hχ

/-- Nonnegative normalized coefficients of a canonical element are its diagonal constant. -/
theorem coeff_canonical_nonneg (w x : cs.minCosetReps J) (n : ℤ) (hn : 0 ≤ n) :
    ((normalizedBasis cs χ).repr (C w) x).coeff n = if x = w ∧ n = 0 then 1 else 0 := by
  classical
  by_cases hx : x = w
  · subst x
    change (((normalizedBasis cs χ).repr ((isBarTriangular hχ).canonical w)) w).coeff n = _
    rw [(isBarTriangular hχ).repr_canonical_self]
    change (Finsupp.single (0 : ℤ) (1 : ℤ)) n = _
    simp only [Finsupp.single_apply, true_and, eq_comm]
  · rw [ite_eq_right (by simp [hx])]
    exact (isBarTriangular hχ).isNeg_repr_canonical hx n hn

/-- Bar-invariant vectors are determined by all nonnegative normalized coefficients. -/
theorem eq_of_nonneg_coeff_eq {a b : InducedModule χ}
    (ha : parabolicBar hχ a = a) (hb : parabolicBar hχ b = b)
    (hc : ∀ x (n : ℤ), 0 ≤ n →
      ((normalizedBasis cs χ).repr a x).coeff n = ((normalizedBasis cs χ).repr b x).coeff n) :
    a = b := by
  apply sub_eq_zero.mp
  apply (isBarTriangular hχ).eq_zero_of_apply_eq_self
  · change parabolicBar hχ (a - b) = a - b
    rw [map_sub, ha, hb]
  · intro x n hn
    simpa only [map_sub, Finsupp.sub_apply, AddMonoidAlgebra.coeff_sub,
      sub_eq_zero] using hc x n hn

/-- Canonical expansion from constant coefficients when all positive coefficients vanish.
This is the uniqueness argument, not an assumption of any multiplication formula. -/
theorem eq_sum_canonical_of_nonneg_coeff {a : InducedModule χ}
    (ha : parabolicBar hχ a = a) (S : Finset (cs.minCosetReps J))
    (c : cs.minCosetReps J → ℤ)
    (hc : ∀ x (n : ℤ), 0 ≤ n →
      ((normalizedBasis cs χ).repr a x).coeff n = if x ∈ S ∧ n = 0 then c x else 0) :
    a = ∑ z ∈ S, c z • C z := by
  classical
  apply eq_of_nonneg_coeff_eq hχ ha
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [map_zsmul, parabolicBar_parabolicKLBasis]
  · intro x n hn
    rw [hc x n hn, map_sum, Finsupp.finsetSum_apply]
    simp_rw [map_zsmul, Finsupp.smul_apply]
    rw [show (∑ z ∈ S, c z • (normalizedBasis cs χ).repr (C z) x).coeff n =
        ∑ z ∈ S, c z * ((normalizedBasis cs χ).repr (C z) x).coeff n by
      simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
        AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply]
      simp only [zsmul_eq_mul, Int.cast_id]]
    simp_rw [coeff_canonical_nonneg hχ _ _ n hn]
    by_cases hn0 : n = 0
    · subst n
      simp
    · simp [hn0]

/-- Shift down never creates a nonnegative coefficient of a canonical coordinate. -/
theorem coeff_shift_down (w x : cs.minCosetReps J) (n : ℤ) (hn : 0 ≤ n) :
    (LaurentPolynomial.T (-1) * (normalizedBasis cs χ).repr (C w) x).coeff n = 0 := by
  rw [coeff_T_mul, coeff_canonical_nonneg hχ w x (n - -1) (by omega)]
  simp only [show n - -1 ≠ 0 by omega, and_false, ite_false]

/-- Shift up of an off-diagonal coordinate exposes exactly μ in degree zero. -/
theorem coeff_shift_up (w x : cs.minCosetReps J) (hx : x ≠ w)
    (n : ℤ) (hn : 0 ≤ n) :
    (LaurentPolynomial.T 1 * (normalizedBasis cs χ).repr (C w) x).coeff n =
      if n = 0 then parabolicKLMu hχ x w else 0 := by
  rw [coeff_T_mul]
  by_cases hn0 : n = 0
  · subst n
    simp only [ite_true, zero_sub, parabolicKLMu_eq_coeff_neg_one]
  · rw [ite_eq_right hn0]
    exact (isBarTriangular hχ).isNeg_repr_canonical hx (n - 1) (by omega)

/-- Effective descents for the index (spherical) character, including the boundary. -/
def effectiveDescent (i : B) (x : cs.minCosetReps J) : Prop :=
  cs.length (cs.simple i * x) < cs.length x ∨
    cs.simple i * x ∉ cs.minCosetReps J

/-- Nonnegative coefficients of an ascent product, under an explicit normalized-action
hypothesis. This hypothesis states standard-coordinate action on arbitrary vectors;
it does not assume canonical recursion. Reconstructed from canonical negativity. -/
theorem coeff_ascent_of_normalized_action (i : B)
    (ha : ∀ (m : InducedModule χ) (x : cs.minCosetReps J),
      (normalizedBasis cs χ).repr (klSimple cs i • m) x =
        if hx : cs.simple i * x ∈ cs.minCosetReps J then
          (normalizedBasis cs χ).repr m ⟨cs.simple i * x, hx⟩ +
            LaurentPolynomial.T (if cs.length (cs.simple i * x) < cs.length x
              then 1 else -1) * (normalizedBasis cs χ).repr m x
        else (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) *
          (normalizedBasis cs χ).repr m x)
    (w : cs.minCosetReps J)
    (hw : cs.length w < cs.length (cs.simple i * w))
    (hsw : cs.simple i * w ∈ cs.minCosetReps J)
    (x : cs.minCosetReps J) (n : ℤ) (hn : 0 ≤ n) :
    ((normalizedBasis cs χ).repr (klSimple cs i • C w) x).coeff n =
      (if x = (⟨cs.simple i * w, hsw⟩ : cs.minCosetReps J) ∧ n = 0 then 1 else 0) +
      (if effectiveDescent i x ∧ n = 0 then parabolicKLMu hχ x w else 0) := by
  classical
  rw [ha]
  by_cases hx : cs.simple i * x ∈ cs.minCosetReps J
  · rw [dite_eq_left hx, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      coeff_canonical_nonneg hχ w _ n hn]
    have heq : (⟨cs.simple i * x, hx⟩ : cs.minCosetReps J) = w ↔
        x = (⟨cs.simple i * w, hsw⟩ : cs.minCosetReps J) := by
      constructor
      · intro h
        apply Subtype.ext
        have hh := congrArg (fun z : W ↦ cs.simple i * z) (congrArg Subtype.val h)
        simpa only [CoxeterSystem.simple_mul_simple_cancel_left] using hh
      · intro h
        apply Subtype.ext
        have hh := congrArg (fun z : W ↦ cs.simple i * z) (congrArg Subtype.val h)
        simpa only [CoxeterSystem.simple_mul_simple_cancel_left] using hh
    simp only [heq]
    by_cases hd : cs.length (cs.simple i * x) < cs.length x
    · have hxw : x ≠ w := by intro e; subst x; omega
      rw [ite_eq_left hd, coeff_shift_up hχ w x hxw n hn]
      simp only [effectiveDescent, hd, true_or, true_and]
    · rw [ite_eq_right hd, coeff_shift_down hχ w x n hn]
      simp only [effectiveDescent, hd, hx, not_true_eq_false, or_self, false_and,
        ite_false, add_zero]
  · rw [dite_eq_right hx]
    have hxw : x ≠ w := by intro e; subst x; exact hx hsw
    have hxsw : x ≠ (⟨cs.simple i * w, hsw⟩ : cs.minCosetReps J) := by
      intro e
      apply hx
      rw [e]
      simpa only [CoxeterSystem.simple_mul_simple_cancel_left] using w.property
    rw [add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      coeff_shift_up hχ w x hxw n hn, coeff_shift_down hχ w x n hn]
    simp only [hxsw, false_and, ite_false, effectiveDescent, hx, not_false_eq_true,
      or_true, true_and, add_zero, zero_add]

/-- The finite effective-descent part of the Bruhat interval below w. -/
noncomputable def effectiveDescentsBelow (i : B) (w : cs.minCosetReps J) :
    Finset (cs.minCosetReps J) :=
  ((cs.finite_setOf_bruhatLE (w : W)).preimage
    (show Set.InjOn (Subtype.val : cs.minCosetReps J → W)
      (Subtype.val ⁻¹' {z | cs.BruhatLE z w}) from Subtype.val_injective.injOn)).toFinset.filter
    (effectiveDescent i)

@[simp] theorem mem_effectiveDescentsBelow (i : B) (w x : cs.minCosetReps J) :
    x ∈ effectiveDescentsBelow i w ↔ cs.BruhatLE x w ∧ effectiveDescent i x := by
  simp [effectiveDescentsBelow]

/-- Canonical ascent recursion from normalized standard action.
The displayed action hypothesis is discharged by `index_normalized_action` for `ind`.
Canonical uniqueness, μ identification, and the finite correction sum are proved here. -/
theorem ascent_of_normalized_action (i : B)
    (ha : ∀ (m : InducedModule χ) (x : cs.minCosetReps J),
      (normalizedBasis cs χ).repr (klSimple cs i • m) x =
        if hx : cs.simple i * x ∈ cs.minCosetReps J then
          (normalizedBasis cs χ).repr m ⟨cs.simple i * x, hx⟩ +
            LaurentPolynomial.T (if cs.length (cs.simple i * x) < cs.length x
              then 1 else -1) * (normalizedBasis cs χ).repr m x
        else (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) *
          (normalizedBasis cs χ).repr m x)
    (w : cs.minCosetReps J)
    (hw : cs.length w < cs.length (cs.simple i * w))
    (hsw : cs.simple i * w ∈ cs.minCosetReps J) :
    klSimple cs i • C w = C ⟨cs.simple i * w, hsw⟩ +
      ∑ z ∈ effectiveDescentsBelow i w, parabolicKLMu hχ z w • C z := by
  classical
  apply sub_eq_iff_eq_add'.mp
  apply eq_sum_canonical_of_nonneg_coeff hχ
  · rw [map_sub, parabolicBar_smul_hecke, barL_klSimple,
      parabolicBar_parabolicKLBasis, parabolicBar_parabolicKLBasis]
  · intro x n hn
    rw [map_sub, Finsupp.sub_apply, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      coeff_ascent_of_normalized_action hχ i ha w hw hsw x n hn,
      coeff_canonical_nonneg hχ _ x n hn, add_sub_cancel_left]
    by_cases hx : cs.BruhatLE x w
    · simp only [mem_effectiveDescentsBelow, hx, true_and]
    · simp only [mem_effectiveDescentsBelow, hx, false_and,
        parabolicKLMu_eq_zero_of_not_bruhatLE hχ hx, ite_self]


end IwahoriHeckeAlgebra.IndexCanonical

namespace IwahoriHeckeAlgebra
open IndexCanonical
attribute [local instance] Classical.propDecidable CoxeterSystem.minCosetRepsPartialOrder
variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable {J : Set B}
local notation "hχ" => isBarCompatible_ind (cs.parabolicCoxeterSystem J)

/-- Arbitrary-J spherical/index C'_s ascent recursion. No finiteness or recursion hypothesis.
The proof uses the standard boundary action, normalized coordinates and canonical uniqueness.
Our own proof, in Deodhar's normalization. -/
theorem index_klBasis_simple_smul_ascent (i : B) (w : cs.minCosetReps J)
    (hw : cs.length w < cs.length (cs.simple i * w))
    (hsw : cs.simple i * w ∈ cs.minCosetReps J) :
    klBasis cs (cs.simple i) • parabolicKLBasis hχ w =
      parabolicKLBasis hχ ⟨cs.simple i * w, hsw⟩ +
      ∑ z ∈ effectiveDescentsBelow i w, parabolicKLMu hχ z w • parabolicKLBasis hχ z := by
  rw [klBasis_simple]
  exact ascent_of_normalized_action hχ i (index_normalized_action cs i) w hw hsw

/-- The coordinates of the failure of the eigenvalue identity are paired along s-edges. -/
theorem index_eigen_defect_pair (i : B)
    (m : InducedModule (ind (cs.parabolicCoxeterSystem J) (LaurentPolynomial.T 2)))
    (x : cs.minCosetReps J)
    (hx : cs.simple i * x ∈ cs.minCosetReps J)
    (hlt : cs.length x < cs.length (cs.simple i * x)) :
    let N := normalizedBasis cs (ind (cs.parabolicCoxeterSystem J) (LaurentPolynomial.T 2))
    let a : ℤ[T;T⁻¹] := LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)
    N.repr (klSimple cs i • m - a • m) x =
      -LaurentPolynomial.T 1 * N.repr (klSimple cs i • m - a • m)
        ⟨cs.simple i * x, hx⟩ := by
  dsimp only
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [index_normalized_action, index_normalized_action, dite_eq_left hx]
  have hsx : cs.simple i * (cs.simple i * x) ∈ cs.minCosetReps J := by
    simpa only [simple_mul_simple_cancel_left] using x.property
  rw [dite_eq_left hsx]
  simp only [simple_mul_simple_cancel_left]
  rw [ite_eq_right (by omega : ¬ cs.length (cs.simple i * x) < cs.length x), ite_eq_left hlt]
  have hv : (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1) : ℤ[T;T⁻¹]) = 1 := by
    rw [← T_add, show (1 : ℤ) + -1 = 0 from rfl, T_zero]
  linear_combination -((normalizedBasis cs
    (ind (cs.parabolicCoxeterSystem J) (LaurentPolynomial.T 2))).repr m
      ⟨cs.simple i * x, hx⟩) * hv

local notation "χind" => ind (cs.parabolicCoxeterSystem J) (LaurentPolynomial.T 2)
local notation "Nind" => normalizedBasis cs χind
local notation "aind" => (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : ℤ[T;T⁻¹])

/-- The eigenvalue defect has strictly negative coordinates at effective descents. -/
theorem index_eigen_defect_negative (i : B) (w x : cs.minCosetReps J)
    (hw : effectiveDescent i w) (hx : effectiveDescent i x) :
    ((Nind).repr (klSimple cs i • parabolicKLBasis hχ w -
      aind • parabolicKLBasis hχ w) x).IsNeg := by
  classical
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [index_normalized_action]
  by_cases hxmin : cs.simple i * x ∈ cs.minCosetReps J
  · rw [dite_eq_left hxmin]
    have hxd : cs.length (cs.simple i * x) < cs.length x := hx.resolve_right (not_not.mpr hxmin)
    rw [ite_eq_left hxd]
    have he : (Nind).repr (parabolicKLBasis hχ w) ⟨cs.simple i * x, hxmin⟩ +
        LaurentPolynomial.T 1 * (Nind).repr (parabolicKLBasis hχ w) x -
        aind * (Nind).repr (parabolicKLBasis hχ w) x =
        (Nind).repr (parabolicKLBasis hχ w) ⟨cs.simple i * x, hxmin⟩ -
          LaurentPolynomial.T (-1) * (Nind).repr (parabolicKLBasis hχ w) x := by ring
    rw [he]
    apply LaurentPolynomial.IsNeg.sub
    · apply (isBarTriangular hχ).isNeg_repr_canonical
      intro h
      have hnot : ¬ effectiveDescent i (⟨cs.simple i * x, hxmin⟩ : cs.minCosetReps J) := by
        simp only [effectiveDescent, simple_mul_simple_cancel_left, x.property,
          not_true_eq_false, or_false]
        omega
      exact hnot (h.symm ▸ hw)
    · intro n hn
      exact coeff_shift_down hχ w x n hn
  · rw [dite_eq_right hxmin, sub_self]
    exact isNeg_zero

/-- Descent and boundary eigenvalue recursion for arbitrary J, by maximal-support uniqueness. -/
theorem index_klBasis_simple_smul_effective (i : B) (w : cs.minCosetReps J)
    (hw : effectiveDescent i w) :
    klBasis cs (cs.simple i) • parabolicKLBasis hχ w =
      aind • parabolicKLBasis hχ w := by
  classical
  rw [klBasis_simple]
  apply sub_eq_zero.mp
  let D := klSimple cs i • parabolicKLBasis hχ w - aind • parabolicKLBasis hχ w
  change D = 0
  have hbar : parabolicBar hχ D = D := by
    dsimp [D]
    rw [map_sub, parabolicBar_smul_hecke, barL_klSimple,
      parabolicBar_parabolicKLBasis, parabolicBar_smul, parabolicBar_parabolicKLBasis]
    simp only [map_add, invert_T, neg_neg]
    rw [add_comm (LaurentPolynomial.T (-1))]
  by_contra hne
  have hsupp : ((Nind).repr D).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact fun e ↦ hne ((Nind).repr.map_eq_zero_iff.mp e)
  obtain ⟨x, hx⟩ := ((Nind).repr D).support.exists_maximal hsupp
  have hxe : effectiveDescent i x := by
    by_contra hn
    have hxmin : cs.simple i * x ∈ cs.minCosetReps J := by
      by_contra h
      exact hn (Or.inr h)
    have hxd : ¬ cs.length (cs.simple i * x) < cs.length x := fun h ↦ hn (Or.inl h)
    have hlt : cs.length x < cs.length (cs.simple i * x) := by
      have := cs.length_simple_mul (x : W) i
      omega
    have hsupp' : (⟨cs.simple i * x, hxmin⟩ : cs.minCosetReps J) ∈
        ((Nind).repr D).support := by
      rw [Finsupp.mem_support_iff]
      intro hz
      apply Finsupp.mem_support_iff.mp hx.1
      have hp := index_eigen_defect_pair cs i (parabolicKLBasis hχ w) x hxmin hlt
      change (Nind).repr D x = -LaurentPolynomial.T 1 *
        (Nind).repr D ⟨cs.simple i * x, hxmin⟩ at hp
      rw [hz, mul_zero] at hp
      exact hp
    have hle : x ≤ (⟨cs.simple i * x, hxmin⟩ : cs.minCosetReps J) :=
      cs.bruhatLE_simple_mul hxd
    have hle' : cs.BruhatLE (cs.simple i * x) x := hx.2 hsupp' hle
    have := hle'.length_le
    omega
  have key : (Nind).repr (parabolicBar hχ D) x = invert ((Nind).repr D x) := by
    change (Nind).repr ((parabolicBar hχ).toAddMonoidHom D) x = _
    rw [(isBarTriangular hχ).repr_apply, Finsupp.sum,
      Finset.sum_eq_single_of_mem x hx.1, (isBarTriangular hχ).repr_self, mul_one]
    intro y hy hyx
    by_cases hr : (Nind).repr ((parabolicBar hχ).toAddMonoidHom ((Nind) y)) x = 0
    · rw [hr, mul_zero]
    · exact absurd (le_antisymm (hx.2 hy ((isBarTriangular hχ).le_of_repr_ne_zero hr))
        ((isBarTriangular hχ).le_of_repr_ne_zero hr)) hyx
  rw [hbar] at key
  exact Finsupp.mem_support_iff.mp hx.1
    ((index_eigen_defect_negative cs i w x hw hxe).eq_zero_of_invert_eq key.symm)

/-- The correction interval is strictly below w in an ascent branch. -/
theorem index_mem_effectiveDescentsBelow_ascent (i : B) (w x : cs.minCosetReps J)
    (hw : cs.length w < cs.length (cs.simple i * w))
    (hsw : cs.simple i * w ∈ cs.minCosetReps J) :
    x ∈ effectiveDescentsBelow i w ↔ cs.BruhatLE x w ∧ x ≠ w ∧ effectiveDescent i x := by
  rw [mem_effectiveDescentsBelow]
  constructor
  · rintro ⟨hle, he⟩
    refine ⟨hle, ?_, he⟩
    intro h
    subst x
    rcases he with he | he
    · omega
    · exact he hsw
  · rintro ⟨hle, _, he⟩
    exact ⟨hle, he⟩

/-- Arbitrary-J index canonical descent action. -/
theorem index_klBasis_simple_smul_descent (i : B) (w : cs.minCosetReps J)
    (hw : cs.length (cs.simple i * w) < cs.length w) :
    klBasis cs (cs.simple i) • parabolicKLBasis hχ w =
      aind • parabolicKLBasis hχ w :=
  index_klBasis_simple_smul_effective cs i w (Or.inl hw)

/-- Arbitrary-J index canonical boundary action. -/
theorem index_klBasis_simple_smul_boundary (i : B) (w : cs.minCosetReps J)
    (hw : cs.simple i * w ∉ cs.minCosetReps J) :
    klBasis cs (cs.simple i) • parabolicKLBasis hχ w =
      aind • parabolicKLBasis hχ w :=
  index_klBasis_simple_smul_effective cs i w (Or.inr hw)

/-- Full arbitrary-J spherical/index Deodhar C'_s multiplication recursion.
The ascent correction uses μ^{J,q}, with effective descents (including boundaries)
strictly below w; the other two branches have eigenvalue v+v⁻¹. -/
theorem index_klBasis_simple_smul (i : B) (w : cs.minCosetReps J) :
    klBasis cs (cs.simple i) • parabolicKLBasis hχ w =
      if hsw : cs.simple i * w ∈ cs.minCosetReps J then
        if cs.length w < cs.length (cs.simple i * w) then
          parabolicKLBasis hχ ⟨cs.simple i * w, hsw⟩ +
            ∑ z ∈ effectiveDescentsBelow i w, parabolicKLMu hχ z w • parabolicKLBasis hχ z
        else aind • parabolicKLBasis hχ w
      else aind • parabolicKLBasis hχ w := by
  split_ifs with hsw hw
  · exact index_klBasis_simple_smul_ascent cs i w hw hsw
  · apply index_klBasis_simple_smul_descent cs i w
    have := cs.length_simple_mul (w : W) i
    omega
  · exact index_klBasis_simple_smul_boundary cs i w hsw

end IwahoriHeckeAlgebra
