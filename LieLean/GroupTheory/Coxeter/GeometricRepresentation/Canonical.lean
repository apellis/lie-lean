/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.GeometricRepresentation.RootChoice
import LieLean.GroupTheory.Coxeter.Matsumoto
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Faithfulness of the canonical real geometric representation

## Main definitions / results

* `representation` and `representationUnits` are the actual real canonical action.
* `coeff_complex` and `embed_representation` identify the explicit exponential
  specialization with its real form; no opaque primitive-root choice is identified.
* `parabolic_ascent_two_nonnegative` supplies the finite and infinite dihedral cone step.
* `nonnegative_of_length_lt` and `nonpositive_of_length_lt` prove the root/length signs.
* `representationUnits_injective` and `representation_injective` prove faithfulness.
* `canonicalComplex_injective` transfers the result to the explicit complex specialization.

## Scope and proof

The source assumes finitely many simple generators (§5.1, p. 106), not a finite group.
The statements here prove the stronger arbitrary-rank version on the finitely supported
real root space. No finiteness, positive-definiteness, or faithful-action hypothesis is used.
The positive-root induction follows §5.4: a shorter minimal coset representative and a
rank-two alternating factor. Existing independently proved combinatorial parabolic lemmas
replace the source's minimal-length construction. The sine recurrence below expands the
source's finite-dihedral direct calculation; its infinite analogue is q(n) = n.

## References

Humphreys, *Reflection Groups and Coxeter Groups* (1990), §5.3, pp. 108–110,
§5.4 Theorem and Corollary, pp. 111–113.
The convention at infinity is B(αᵢ, αⱼ) = -1, with 0 encoding infinity here.
-/

namespace CanonicalGeometric

/-- Humphreys' cosine coefficient, with natural-number zero denoting infinity. -/
noncomputable def coeff (m : ℕ) : ℝ := Real.cos (Real.pi / m)

/-- The actual standard exponential, not an opaque primitive-root choice. -/
noncomputable def rootChoice : GeometricParametric.RootChoice ℂ where
  root m := Complex.exp (2 * Real.pi * Complex.I / (2 * m))
  root_zero := by simp
  order_root := by
    intro m hm
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Complex.isPrimitiveRoot_exp (2 * m) (by omega)).eq_orderOf.symm

/-- The canonical root equals exp(iπ/m), including the zero convention. -/
theorem rootChoice_root (m : ℕ) :
    rootChoice.root m = Complex.exp ((Real.pi / m : ℝ) * Complex.I) := by
  change Complex.exp (2 * Real.pi * Complex.I / (2 * m)) = _
  congr 1
  push_cast
  ring

/-- Exact identification of the parametric coefficients with real cosine coefficients. -/
theorem coeff_complex (m : ℕ) :
    GeometricParametric.coeff rootChoice m = (coeff m : ℂ) := by
  by_cases hm : m = 0
  · subst m
    simp [GeometricParametric.coeff, coeff]
  · rw [GeometricParametric.coeff, ite_eq_right (by exact hm), rootChoice_root,
      ← Complex.exp_neg]
    rw [show -((Real.pi / m : ℝ) * Complex.I) =
      ((-(Real.pi / m) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, coeff]
    ring

/-- The infinity coefficient is one, so the bilinear form entry is minus one. -/
@[simp] theorem coeff_zero : coeff 0 = 1 := by simp [coeff]

/-- Diagonal normalization. -/
@[simp] theorem coeff_one : coeff 1 = -1 := by simp [coeff]

variable {B : Type*} (M : CoxeterMatrix B)

/-- The real row of Humphreys' canonical bilinear form. -/
noncomputable def form (i : B) : (B →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ fun j ↦ -coeff (M i j)

/-- The canonical real reflection from Humphreys §5.3. -/
noncomputable def reflection (i : B) : Module.End ℝ (B →₀ ℝ) :=
  LinearMap.id - (form M i).smulRight (Finsupp.single i 2)

/-- Evaluation of the form on a basis vector. -/
theorem form_single (i j : B) (a : ℝ) :
    form M i (Finsupp.single j a) = a * -coeff (M i j) := by
  simp [form, Finsupp.linearCombination_single]

/-- Diagonal form evaluation. -/
theorem form_single_self (i : B) (a : ℝ) : form M i (Finsupp.single i a) = a := by
  rw [form_single, M.diagonal, coeff_one]
  ring

/-- Defining action of the real reflection. -/
theorem reflection_apply (i : B) (v : B →₀ ℝ) :
    reflection M i v = v - form M i v • Finsupp.single i 2 := rfl

/-- Basis action of the real reflection. -/
theorem reflection_single (i j : B) :
    reflection M i (Finsupp.single j 1) =
      Finsupp.single j 1 + (2 * coeff (M i j)) • Finsupp.single i 1 := by
  rw [reflection_apply, form_single, ← Finsupp.smul_single_one i (2 : ℝ)]
  module

/-- A real simple reflection negates its simple root. -/
theorem reflection_single_self (i : B) :
    reflection M i (Finsupp.single i 1) = -Finsupp.single i 1 := by
  rw [reflection_single, M.diagonal, coeff_one]
  module

/-- The real reflections are involutions. -/
theorem reflection_mul_self (i : B) : reflection M i * reflection M i = 1 := by
  refine LinearMap.ext fun v ↦ ?_
  have h : form M i (reflection M i v) = -form M i v := by
    rw [reflection_apply, map_sub, map_smul, form_single_self, smul_eq_mul]
    ring
  rw [Module.End.mul_apply, Module.End.one_apply, reflection_apply M i (reflection M i v),
    h, reflection_apply]
  module

/-- Coordinatewise inclusion of the real root space in its complexification. -/
noncomputable def embed : (B →₀ ℝ) →ₗ[ℝ] (B →₀ ℂ) :=
  Finsupp.mapRange.linearMap Complex.ofRealCLM.toLinearMap

/-- Complexification is injective, for arbitrary rank. -/
theorem embed_injective : Function.Injective (embed (B := B)) :=
  Finsupp.mapRange_injective _ (map_zero _) Complex.ofReal_injective

/-- Inclusion on basis vectors. -/
@[simp] theorem embed_single (i : B) (a : ℝ) :
    embed (Finsupp.single i a) = Finsupp.single i (a : ℂ) := by
  simp [embed]

/-- Exact generator-level transfer, using the proved cosine identification. -/
theorem embed_reflection (i : B) (v : B →₀ ℝ) :
    embed (reflection M i v) = GeometricParametric.reflection rootChoice M i (embed v) := by
  have h : (embed (B := B)).comp (reflection M i) =
      ((GeometricParametric.reflection rootChoice M i).restrictScalars ℝ).comp embed := by
    apply Finsupp.lhom_ext
    intro j a
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      reflection_apply, GeometricParametric.reflection_apply, map_sub, map_smul,
      embed_single, form_single, GeometricParametric.form_single, coeff_complex]
    ext k
    simp [Complex.real_smul, mul_assoc]
  exact LinearMap.congr_fun h v

/-- The complexification intertwines arbitrary powers of a pair of real reflections. -/
theorem embed_pair_pow (i j : B) (n : ℕ) (v : B →₀ ℝ) :
    embed (((reflection M i * reflection M j) ^ n) v) =
      ((GeometricParametric.reflection rootChoice M i *
        GeometricParametric.reflection rootChoice M j) ^ n) (embed v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, Module.End.mul_apply, ih, embed_reflection]

/-- All Coxeter relations hold on the actual real space, by injective complexification. -/
theorem reflection_liftable : M.IsLiftable (reflection M) := by
  intro i j
  apply LinearMap.ext
  intro v
  apply embed_injective
  rw [embed_pair_pow, GeometricParametric.reflection_liftable rootChoice M i j]
  rfl

variable {W : Type*} [Group W] (cs : CoxeterSystem M W)

/-- Humphreys' canonical real representation (§5.3), with no faithfulness assumed. -/
noncomputable def representation : W →* Module.End ℝ (B →₀ ℝ) :=
  cs.lift ⟨reflection M, reflection_liftable M⟩

/-- The canonical real lift has exactly the source reflection formula on generators. -/
theorem representation_simple (i : B) :
    representation M cs (cs.simple i) = reflection M i := cs.lift_apply_simple _ i

/-- The full real representation intertwines with the canonical complex parametric lift. -/
theorem embed_representation (w : W) (v : B →₀ ℝ) :
    embed (representation M cs w v) =
      GeometricParametric.representation rootChoice M cs w (embed v) := by
  induction w using cs.induction_mul_simple generalizing v with
  | one => simp
  | mul_simple w i _ ih =>
    simp only [map_mul, representation_simple, GeometricParametric.representation_simple,
      Module.End.mul_apply, ih, embed_reflection]

/-- The same representation into the genuine group of invertible endomorphisms. -/
noncomputable def representationUnits : W →* (Module.End ℝ (B →₀ ℝ))ˣ :=
  (representation M cs).toHomUnits

/-- Passing to units does not change the underlying real action. -/
theorem representationUnits_val (w : W) :
    (representationUnits M cs w : Module.End ℝ (B →₀ ℝ)) = representation M cs w := rfl

/-- Dihedral sine coefficients used in the positive-root proof of Humphreys §5.4.
The infinite-edge case is the limiting arithmetic progression. -/
noncomputable def dihedralCoeff (m n : ℕ) : ℝ :=
  if m = 0 then n else Real.sin (n * (Real.pi / m)) / Real.sin (Real.pi / m)

/-- The finite dihedral angle lies strictly between zero and pi. -/
theorem angle_bounds {m : ℕ} (hm : 1 < m) :
    0 < Real.pi / m ∧ Real.pi / m < Real.pi := by
  have hm' : (1 : ℝ) < m := by exact_mod_cast hm
  constructor
  · positivity
  · exact (div_lt_iff₀ (by positivity)).mpr (by nlinarith [Real.pi_pos])

/-- The denominator of the finite dihedral sine formula is positive. -/
theorem sin_angle_pos {m : ℕ} (hm : 1 < m) : 0 < Real.sin (Real.pi / m) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_bounds hm).1 (angle_bounds hm).2

/-- Initial dihedral coefficient. -/
@[simp] theorem dihedralCoeff_zero (m : ℕ) : dihedralCoeff m 0 = 0 := by
  simp [dihedralCoeff]

/-- The second dihedral coefficient, for every possible off-diagonal exponent. -/
theorem dihedralCoeff_one {m : ℕ} (hm : m = 0 ∨ 1 < m) : dihedralCoeff m 1 = 1 := by
  rcases hm with rfl | hm
  · simp [dihedralCoeff]
  · simp [dihedralCoeff, ne_of_gt (sin_angle_pos hm)]

/-- The sine addition formulas give the dihedral recurrence; this supplies the
explicit calculation in Humphreys §5.4, pp. 112–113. -/
theorem dihedralCoeff_recurrence (m n : ℕ) :
    dihedralCoeff m (n + 2) =
      2 * coeff m * dihedralCoeff m (n + 1) - dihedralCoeff m n := by
  by_cases hm : m = 0
  · subst m
    simp only [dihedralCoeff, ite_true, coeff_zero, Nat.cast_add, Nat.cast_ofNat]
    ring
  · simp only [dihedralCoeff, hm, ite_false, coeff, Nat.cast_add, Nat.cast_ofNat]
    have hs : Real.sin (((n : ℝ) + 2) * (Real.pi / m)) =
        2 * Real.cos (Real.pi / m) * Real.sin (((n : ℝ) + 1) * (Real.pi / m)) -
          Real.sin ((n : ℝ) * (Real.pi / m)) := by
      have h₁ := Real.sin_add (((n : ℝ) + 1) * (Real.pi / m)) (Real.pi / m)
      have h₂ := Real.sin_sub (((n : ℝ) + 1) * (Real.pi / m)) (Real.pi / m)
      rw [show ((n : ℝ) + 1) * (Real.pi / m) + Real.pi / m =
        ((n : ℝ) + 2) * (Real.pi / m) by ring] at h₁
      rw [show ((n : ℝ) + 1) * (Real.pi / m) - Real.pi / m =
        (n : ℝ) * (Real.pi / m) by ring] at h₂
      linear_combination h₁ + h₂
    rw [hs]
    ring_nf

/-- Precisely the sign range needed for reduced dihedral words. -/
theorem dihedralCoeff_nonneg {m n : ℕ} (hm : m = 0 ∨ 1 < m)
    (hn : m = 0 ∨ n ≤ m) : 0 ≤ dihedralCoeff m n := by
  rcases hm with rfl | hm
  · simp [dihedralCoeff]
  · have hm0 : m ≠ 0 := by omega
    have hn' : (n : ℝ) ≤ m := by exact_mod_cast (hn.resolve_left hm0)
    have hm' : (0 : ℝ) < m := by positivity
    rw [dihedralCoeff, ite_eq_right hm0]
    apply div_nonneg _ (sin_angle_pos hm).le
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · calc
        (n : ℝ) * (Real.pi / m) ≤ m * (Real.pi / m) :=
          mul_le_mul_of_nonneg_right hn' (angle_bounds hm).1.le
        _ = Real.pi := by field_simp

/-- Exact rank-two formula for an even alternating product.  This is the
calculation underlying the positive cone step of Humphreys §5.4. -/
theorem pair_pow_single {i j : B} (hij : i ≠ j) (k : ℕ) :
    ((reflection M i * reflection M j) ^ k) (Finsupp.single i 1) =
      dihedralCoeff (M i j) (2 * k + 1) • Finsupp.single i 1 +
        dihedralCoeff (M i j) (2 * k) • Finsupp.single j 1 := by
  have hm : M i j = 0 ∨ 1 < M i j := by
    have := M.off_diagonal i j hij
    omega
  induction k with
  | zero => simp [dihedralCoeff_one hm]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, map_smul,
      Module.End.mul_apply, Module.End.mul_apply, reflection_single M j i,
      reflection_single_self, map_add, map_smul, map_neg, reflection_single_self,
      reflection_single, M.symmetric j i]
    rw [show 2 * (k + 1) = 2 * k + 2 by omega,
      show 2 * k + 2 + 1 = (2 * k + 1) + 2 by omega,
      dihedralCoeff_recurrence, show 2 * k + 1 + 1 = 2 * k + 2 by omega,
      dihedralCoeff_recurrence]
    module

/-- Exact rank-two formula for an odd alternating product ending on the right in j. -/
theorem reflection_pair_pow_single {i j : B} (hij : i ≠ j) (k : ℕ) :
    (reflection M j * (reflection M i * reflection M j) ^ k) (Finsupp.single i 1) =
      dihedralCoeff (M i j) (2 * k + 1) • Finsupp.single i 1 +
        dihedralCoeff (M i j) (2 * k + 2) • Finsupp.single j 1 := by
  rw [Module.End.mul_apply, pair_pow_single M hij, map_add, map_smul, map_smul,
    reflection_single M j i, reflection_single_self, M.symmetric j i,
    dihedralCoeff_recurrence]
  module

/-- Nonnegative-coordinate cone, including zero; roots themselves will be nonzero. -/
def Nonnegative (v : B →₀ ℝ) : Prop := ∀ i, 0 ≤ v i

/-- A nonnegative linear combination of two simple roots belongs to the positive cone. -/
theorem nonnegative_two_simple {i j : B} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Nonnegative (a • Finsupp.single i 1 + b • Finsupp.single j 1) := by
  intro t
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (by
    classical
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num))
    (mul_nonneg hb (by
      classical
      simp only [Finsupp.single_apply]
      split_ifs <;> norm_num))

/-- Positive-cone part of Humphreys §5.4 for every finite or infinite rank-two
alternating product of even length below its braid bound. -/
theorem pair_pow_nonnegative {i j : B} (hij : i ≠ j) {k : ℕ}
    (hk : M i j = 0 ∨ 2 * k < M i j) :
    Nonnegative (((reflection M i * reflection M j) ^ k) (Finsupp.single i 1)) := by
  have hm : M i j = 0 ∨ 1 < M i j := by
    have := M.off_diagonal i j hij
    omega
  rw [pair_pow_single M hij]
  apply nonnegative_two_simple
  · exact dihedralCoeff_nonneg hm (by omega)
  · exact dihedralCoeff_nonneg hm (by omega)

/-- The odd-length case of the same dihedral positive-cone calculation. -/
theorem reflection_pair_pow_nonnegative {i j : B} (hij : i ≠ j) {k : ℕ}
    (hk : M i j = 0 ∨ 2 * k + 1 < M i j) :
    Nonnegative ((reflection M j * (reflection M i * reflection M j) ^ k)
      (Finsupp.single i 1)) := by
  have hm : M i j = 0 ∨ 1 < M i j := by
    have := M.off_diagonal i j hij
    omega
  rw [reflection_pair_pow_single M hij]
  apply nonnegative_two_simple
  · exact dihedralCoeff_nonneg hm (by omega)
  · exact dihedralCoeff_nonneg hm (by omega)

/-- A rank-two parabolic element with a right ascent at i has an alternating
expression ending in j, strictly shorter than the finite braid bound. This is the
combinatorial input used in Humphreys §5.4. -/
theorem exists_alternating_of_parabolic_ascent {i j : B} {v : W}
    (hv : v ∈ cs.parabolicSubgroup {i, j})
    (hi : cs.length v < cs.length (v * cs.simple i)) :
    ∃ n, v = cs.wordProd (CoxeterSystem.alternatingWord i j n) ∧
      (M i j = 0 ∨ n < M i j) := by
  obtain ⟨ω, hω, hmem, rfl⟩ := cs.exists_isReduced_of_mem_parabolicSubgroup hv
  have hlen : cs.length (cs.wordProd ω * cs.simple i) = ω.length + 1 := by
    have := cs.length_mul_simple (cs.wordProd ω) i
    rw [hω.eq] at this hi
    omega
  have hred : cs.IsReduced (ω ++ [i]) := by
    simp [CoxeterSystem.IsReduced, cs.wordProd_append, hlen]
  have halt := hred.reverse.eq_reverse_alternatingWord (a := i) (b := j)
    (fun c hc ↦ by
      have hc' : c ∈ ω ++ [i] := List.mem_reverse.mp hc
      rcases List.mem_append.mp hc' with hc' | hc'
      · simpa using hmem c hc'
      · simp only [List.mem_singleton] at hc'
        exact Or.inl hc') (by simp)
  have halt' : ω ++ [i] = CoxeterSystem.alternatingWord j i (ω.length + 1) := by
    simpa using congrArg List.reverse halt
  have heq : ω = CoxeterSystem.alternatingWord i j ω.length := by
    rw [CoxeterSystem.alternatingWord_succ, List.concat_eq_append] at halt'
    exact List.append_cancel_right halt'
  refine ⟨ω.length, congrArg cs.wordProd heq, ?_⟩
  by_cases hm : M i j = 0
  · exact Or.inl hm
  · apply Or.inr
    by_contra h
    apply cs.not_isReduced_alternatingWord j i (m := ω.length + 1)
      (by rwa [M.symmetric j i])
      (by rw [M.symmetric j i]; omega)
    rwa [← halt']

/-- The dihedral step of Humphreys §5.4, in precisely the form needed to combine
with two positive root images under a shorter minimal coset representative. -/
theorem parabolic_ascent_two_nonnegative {i j : B} (hij : i ≠ j) {v : W}
    (hv : v ∈ cs.parabolicSubgroup {i, j})
    (hi : cs.length v < cs.length (v * cs.simple i)) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ representation M cs v (Finsupp.single i 1) =
      a • Finsupp.single i 1 + b • Finsupp.single j 1 := by
  obtain ⟨n, rfl, hn⟩ := exists_alternating_of_parabolic_ascent M cs hv hi
  have hm : M i j = 0 ∨ 1 < M i j := by
    have := M.off_diagonal i j hij
    omega
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hn' : n = 2 * k := by omega
    clear hk
    subst n
    refine ⟨dihedralCoeff (M i j) (2 * k + 1), dihedralCoeff (M i j) (2 * k),
      dihedralCoeff_nonneg hm (by omega), dihedralCoeff_nonneg hm (by omega), ?_⟩
    simpa [cs.prod_alternatingWord_eq_mul_pow, representation_simple] using
      pair_pow_single M hij k
  · subst n
    refine ⟨dihedralCoeff (M i j) (2 * k + 1), dihedralCoeff (M i j) (2 * k + 2),
      dihedralCoeff_nonneg hm (by omega), dihedralCoeff_nonneg hm (by omega), ?_⟩
    simpa [cs.prod_alternatingWord_eq_mul_pow, representation_simple,
      show (2 * k + 1) / 2 = k by omega] using reflection_pair_pow_single M hij k

/-- Humphreys §5.4, Theorem (positive half): a right ascent gives a positive
root. The proof uses his shorter minimal-coset-representative / dihedral-cone
induction; the already-proved combinatorial parabolic API supplies the decomposition. -/
theorem nonnegative_of_length_lt {w : W} {i : B}
    (hi : cs.length w < cs.length (w * cs.simple i)) :
    Nonnegative (representation M cs w (Finsupp.single i 1)) := by
  induction hn : cs.length w using Nat.strong_induction_on generalizing w i with
  | h n ih =>
    by_cases hw : w = 1
    · subst w
      intro t
      classical
      simp only [map_one, Module.End.one_apply, Finsupp.single_apply]
      split_ifs <;> norm_num
    obtain ⟨j, hj⟩ := cs.exists_rightDescent_of_ne_one hw
    have hij : i ≠ j := by
      intro heq
      subst j
      exact (not_lt_of_gt hi) hj
    obtain ⟨u, hu, v, hv, huv⟩ := cs.exists_mem_minCosetReps_mul_eq {i, j} w
    have hlen : cs.length w = cs.length u + cs.length v := by
      rw [← huv]
      exact cs.length_mul_of_mem_minCosetReps hu hv
    have hu_ascent : ∀ t ∈ ({i, j} : Set B), cs.length u < cs.length (u * cs.simple t) := by
      intro t ht
      have hnot := hu t ht
      have hne := cs.length_mul_simple_ne u t
      change ¬ cs.length (u * cs.simple t) < cs.length u at hnot
      omega
    have hv_ne : v ≠ 1 := by
      intro heq
      have huw : u = w := by simpa [heq] using huv
      have := hu_ascent j (by simp)
      rw [huw] at this
      exact (not_lt_of_gt this) hj
    have hu_lt : cs.length u < n := by
      have : cs.length v ≠ 0 := fun h ↦ hv_ne (cs.length_eq_zero_iff.mp h)
      omega
    have hv_i : v * cs.simple i ∈ cs.parabolicSubgroup {i, j} :=
      Subgroup.mul_mem _ hv (cs.simple_mem_parabolicSubgroup (by simp))
    have hlen_i : cs.length (w * cs.simple i) =
        cs.length u + cs.length (v * cs.simple i) := by
      rw [← huv, mul_assoc]
      exact cs.length_mul_of_mem_minCosetReps hu hv_i
    have hvi : cs.length v < cs.length (v * cs.simple i) := by omega
    obtain ⟨a, b, ha, hb, hab⟩ := parabolic_ascent_two_nonnegative M cs hij hv hvi
    have hui := ih (cs.length u) hu_lt (hu_ascent i (by simp)) rfl
    have huj := ih (cs.length u) hu_lt (hu_ascent j (by simp)) rfl
    rw [← huv, map_mul, Module.End.mul_apply, hab, map_add, map_smul, map_smul]
    intro t
    exact add_nonneg (mul_nonneg ha (hui t)) (mul_nonneg hb (huj t))

/-- Humphreys §5.4, Theorem (negative half): a right descent gives a negative
root. It follows from the positive half by applying it to ws. -/
theorem nonpositive_of_length_lt {w : W} {i : B}
    (hi : cs.length (w * cs.simple i) < cs.length w) :
    ∀ t, (representation M cs w (Finsupp.single i 1)) t ≤ 0 := by
  have hpos := nonnegative_of_length_lt M cs (w := w * cs.simple i) (i := i)
    (by simpa using hi)
  rw [map_mul, representation_simple, Module.End.mul_apply, reflection_single_self,
    map_neg] at hpos
  intro t
  exact neg_nonneg.mp (hpos t)

/-- Humphreys §5.4, Corollary: the canonical real action has trivial kernel. -/
theorem representation_eq_one_iff (w : W) : representation M cs w = 1 ↔ w = 1 := by
  constructor
  · intro h
    by_contra hw
    obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hw
    have hneg := nonpositive_of_length_lt M cs hi i
    rw [h, Module.End.one_apply, Finsupp.single_eq_same] at hneg
    norm_num at hneg
  · rintro rfl
    exact map_one _

/-- Faithfulness into the genuine group of invertible real endomorphisms;
Humphreys §5.4, Corollary, with no finiteness assumption on the Coxeter system. -/
theorem representationUnits_injective : Function.Injective (representationUnits M cs) := by
  intro w v h
  have hker : representationUnits M cs (w⁻¹ * v) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hker' : representation M cs (w⁻¹ * v) = 1 := by
    exact congrArg Units.val hker
  have := (representation_eq_one_iff M cs _).mp hker'
  exact inv_mul_eq_one.mp this

/-- The endomorphism-valued canonical real representation is injective as well. -/
theorem representation_injective : Function.Injective (representation M cs) := by
  intro w v h
  apply representationUnits_injective M cs
  exact Units.ext h

/-- Root images are nonzero, so the two coordinate cones give the source's
positive/negative distinction, not merely a weak sign assertion about zero. -/
theorem root_image_ne_zero (w : W) (i : B) :
    representation M cs w (Finsupp.single i 1) ≠ 0 := by
  intro hzero
  have h := congrArg (representation M cs w⁻¹) hzero
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply, map_zero] at h
  have hi := congrArg (fun v : B →₀ ℝ ↦ v i) h
  simp at hi

/-- The proved real theorem transfers to the explicit exponential specialization
of the parametric complex construction. It says nothing about the opaque choice. -/
theorem canonicalComplex_injective :
    Function.Injective (GeometricParametric.representation rootChoice M cs) := by
  intro w v h
  apply representation_injective M cs
  apply LinearMap.ext
  intro x
  apply embed_injective
  rw [embed_representation, embed_representation, h]

end CanonicalGeometric
